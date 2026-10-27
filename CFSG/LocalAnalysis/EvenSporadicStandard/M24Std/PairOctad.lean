module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairTransport
public import Certificates.Certificate24850
public import Certificates.Certificate24851
public import Certificates.Certificate24852

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Schreier CFSG.Certificates

variable {G : Type} [Group G]

theorem m24_eq_one_of_fix {g : Equiv.Perm (Fin 24)}
    (hg : g ∈ NativeSporadic.M24) (hfix : ∀ j : Fin 24, j.val < 7 → g j = j) : g = 1 := by
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  have hbase : ∀ b ∈ m24Certificate.base.toList.take m24Certificate.baseCount, b.val < 7 := by
    decide
  have hmem : g ∈ m24Certificate.levelSubgroup m24Certificate.baseCount :=
    (m24Certificate.mem_levelSubgroup_iff hQ _ le_rfl g).2
      ⟨by rw [m24Certificate_originalSubgroup]; exact hg, fun b hb => hfix b (hbase b hb)⟩
  rw [m24Certificate.levelSubgroup_terminal_eq_bot hQ] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem s24_mul_apply (x y : S24) (i : Fin 24) :
    ((x * y : S24) : Equiv.Perm (Fin 24)) i =
      (x : Equiv.Perm (Fin 24)) ((y : Equiv.Perm (Fin 24)) i) := rfl

theorem m24B0_centralizer
    {p : S24} (hp : ∀ b ∈ m24B0l, p * b = b * p) :
    p ∈ m24B0l := by
  obtain ⟨-, -, -, -, hsq, hcomm⟩ := Certificates.certificate24850
  obtain ⟨⟨hC1, hC2, hC3⟩, -, -⟩ := Certificates.certificate24851
  have hp' : ∀ b ∈ m24B0l, ∀ i, (p : Equiv.Perm (Fin 24)) ((b : Equiv.Perm (Fin 24)) i) =
      (b : Equiv.Perm (Fin 24)) ((p : Equiv.Perm (Fin 24)) i) := by
    intro b hb i
    rw [← s24_mul_apply, ← s24_mul_apply, hp b hb]
  obtain ⟨b, hb, hb0⟩ : ∃ b ∈ m24B0l,
      (b : Equiv.Perm (Fin 24)) 0 = (p : Equiv.Perm (Fin 24)) 0 := by
    rcases hC1 ((p : Equiv.Perm (Fin 24)) 0) with hfix | hex
    · exfalso
      obtain ⟨b₁, hb₁, hne⟩ := hC2
      apply hne
      apply (p : Equiv.Perm (Fin 24)).injective
      rw [hp' b₁ hb₁ 0, hfix b₁ hb₁]
    · exact hex
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  have hqcomm : ∀ b' ∈ m24B0l, b⁻¹ * p * b' = b' * (b⁻¹ * p) := by
    intro b' hb'
    rw [hbinv, mul_assoc, hp b' hb', ← mul_assoc, hcomm b hb b' hb', mul_assoc]
  have hq0 : ((b⁻¹ * p : S24) : Equiv.Perm (Fin 24)) 0 = 0 := by
    rw [s24_mul_apply, ← hb0, ← s24_mul_apply, inv_mul_cancel]
    rfl
  have hqfix : ∀ b' ∈ m24B0l, ((b⁻¹ * p : S24) : Equiv.Perm (Fin 24))
      ((b' : Equiv.Perm (Fin 24)) 0) = (b' : Equiv.Perm (Fin 24)) 0 := by
    intro b' hb'
    rw [← s24_mul_apply, hqcomm b' hb', s24_mul_apply, hq0]
  have hr : ((pairC⁻¹ * (b⁻¹ * p) * pairC : S24) : Equiv.Perm (Fin 24)) = 1 := by
    refine m24_eq_one_of_fix (pairC⁻¹ * (b⁻¹ * p) * pairC).2 (fun j hj => ?_)
    obtain ⟨b', hb', hcj⟩ := hC3 j hj
    rw [s24_mul_apply, s24_mul_apply, hcj, hqfix b' hb', ← hcj, ← s24_mul_apply,
      inv_mul_cancel]
    rfl
  have hr' : pairC⁻¹ * (b⁻¹ * p) * pairC = 1 := Subtype.ext hr
  have hpb : p = b := by
    calc p = b * (pairC * (pairC⁻¹ * (b⁻¹ * p) * pairC) * pairC⁻¹) := by group
      _ = b := by rw [hr']; group
  exact hpb ▸ hb

theorem pinV_conj {L : Subgroup G} (e : L ≃* NativeSporadic.M24) (a b : S24) :
    pinV e a * pinV e b * (pinV e a)⁻¹ = pinV e (a * b * a⁻¹) := by
  rw [map_mul, map_mul, map_inv]

namespace ListImage

variable {L B : Subgroup G} {e : L ≃* NativeSporadic.M24}

theorem octad_cent
    (hB : ListImage L e B m24B0l) :
    ∀ l ∈ L, (∀ b ∈ B, l * b = b * l) → l ∈ B := by
  intro l hl hcomm
  obtain ⟨p, rfl⟩ := exists_pinV_eq e hl
  rw [hB.pinV_mem_iff]
  refine m24B0_centralizer fun b hb => pinV_injective e ?_
  rw [map_mul, map_mul]
  exact hcomm _ ((hB.pinV_mem_iff b).2 hb)

theorem octad_exists_conj (hB : ListImage L e B m24B0l)
    {x : G} (hx : x ∈ B) (hx1 : x ≠ 1) :
    ∃ g ∈ pairTransL, pinV e (g * pairX0 * g⁻¹) = x := by
  obtain ⟨-, -, -, htr⟩ := (Certificates.certificate24851).2.1
  obtain ⟨q, hq, rfl⟩ := hB.exists_eq hx
  rcases htr q hq with h1 | ⟨g, hg, hgq⟩
  · exact absurd (by rw [h1, map_one]) hx1
  · exact ⟨g, hg, by rw [hgq]⟩

theorem octad_trans (hB : ListImage L e B m24B0l) :
    ∀ x ∈ B, ∀ y ∈ B, x ≠ 1 → y ≠ 1 → ∃ n ∈ egNL L B, n * x * n⁻¹ = y := by
  obtain ⟨-, -, hnorm, -⟩ := (Certificates.certificate24851).2.1
  intro x hx y hy hx1 hy1
  obtain ⟨g, hg, rfl⟩ := hB.octad_exists_conj hx hx1
  obtain ⟨g', hg', rfl⟩ := hB.octad_exists_conj hy hy1
  refine ⟨pinV e g' * (pinV e g)⁻¹, (egNL L B).mul_mem (hB.pinV_mem_egNL (hnorm g' hg'))
    ((egNL L B).inv_mem (hB.pinV_mem_egNL (hnorm g hg))), ?_⟩
  simp only [map_mul, map_inv]
  group

theorem octad_fix (hB : ListImage L e B m24B0l) :
    ∀ x ∈ B, x ≠ 1 → ∀ w ∈ B,
      (∀ n ∈ egNL L B, n * x * n⁻¹ = x → n * w * n⁻¹ = w) → w = 1 ∨ w = x := by
  obtain ⟨-, -, hnorm, -⟩ := (Certificates.certificate24851).2.1
  obtain ⟨hsn, hsx, hsw⟩ := (Certificates.certificate24851).2.2
  intro x hx hx1 w hw hyp
  obtain ⟨g, hg, rfl⟩ := hB.octad_exists_conj hx hx1
  obtain ⟨qw, hqw, rfl⟩ := hB.exists_eq hw
  have hr : g⁻¹ * qw * g ∈ m24B0l := conj_inv_mem_list (hnorm g hg) qw hqw
  have hfixr : ∀ s ∈ pairFixL, s * (g⁻¹ * qw * g) * s⁻¹ = g⁻¹ * qw * g := by
    intro s hs
    have hg' := hB.pinV_mem_egNL (hnorm g hg)
    have hs' := hB.pinV_mem_egNL (hsn s hs)
    have hn : pinV e (g * s * g⁻¹) ∈ egNL L B := by
      rw [map_mul, map_mul, map_inv]
      exact (egNL L B).mul_mem ((egNL L B).mul_mem hg' hs') ((egNL L B).inv_mem hg')
    have hconj : (g * s * g⁻¹) * (g * pairX0 * g⁻¹) * (g * s * g⁻¹)⁻¹ = g * pairX0 * g⁻¹ := by
      calc (g * s * g⁻¹) * (g * pairX0 * g⁻¹) * (g * s * g⁻¹)⁻¹ =
          g * (s * pairX0 * s⁻¹) * g⁻¹ := by group
        _ = g * pairX0 * g⁻¹ := by rw [hsx s hs]
    have h1 := hyp _ hn (by rw [pinV_conj, hconj])
    rw [pinV_conj] at h1
    have h2 := pinV_injective e h1
    calc s * (g⁻¹ * qw * g) * s⁻¹ = g⁻¹ * ((g * s * g⁻¹) * qw * (g * s * g⁻¹)⁻¹) * g := by
          group
      _ = g⁻¹ * qw * g := by rw [h2]
  rcases hsw _ hr hfixr with h | h
  · left
    have hq : qw = 1 := by
      calc qw = g * (g⁻¹ * qw * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [hq, map_one]
  · right
    congr 1
    calc qw = g * (g⁻¹ * qw * g) * g⁻¹ := by group
      _ = g * pairX0 * g⁻¹ := by rw [h]

theorem octad_big_N (hB : ListImage L e B m24B0l) :
    20160 < Nat.card (egNL L B) := by
  obtain ⟨hlen, hnd, h1, hmul, hnorm, h3, h5, h7⟩ := Certificates.certificate24852
  obtain ⟨H, hH⟩ := exists_listImage e h1 hmul
  have hHle : H ≤ egNL L B := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := hH.exists_eq hg
    exact hB.pinV_mem_egNL (hnorm q hq)
  have h256 : 256 ∣ Nat.card (egNL L B) := by
    rw [← hlen, ← hH.card hnd]
    exact Subgroup.card_dvd_of_le hHle
  have hdvd : ∀ (p : S24) (r : ℕ), r.Prime → OrdNormB0 p r → r ∣ Nat.card (egNL L B) := by
    rintro p r hr ⟨hpow, hne, hpn⟩
    have : Fact r.Prime := ⟨hr⟩
    have hdv := orderOf_dvd_natCard (⟨pinV e p, hB.pinV_mem_egNL hpn⟩ : egNL L B)
    rwa [Subgroup.orderOf_mk, orderOf_pinV, orderOf_eq_prime hpow hne] at hdv
  have h3 := hdvd _ 3 (by norm_num) h3
  have h5 := hdvd _ 5 (by norm_num) h5
  have h7 := hdvd _ 7 (by norm_num) h7
  have h15 : 15 ∣ Nat.card (egNL L B) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 3 5) h3 h5
  have h105 : 105 ∣ Nat.card (egNL L B) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 15 7) h15 h7
  have hall : 26880 ∣ Nat.card (egNL L B) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 256 105) h256 h105
  have : Finite L := finite_of_mulEquiv e
  have : Finite (egNL L B) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_right : egNL L B ≤ L))
      (Subgroup.inclusion_injective _)
  exact lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd Nat.card_pos hall)

theorem octadBasics
    (hB : ListImage L e B m24B0l) : OctadBasics L B := by
  obtain ⟨hlen, hnd, -, -, hsq, hcomm⟩ := Certificates.certificate24850
  exact ⟨hB.elemAb hcomm hsq, (hB.card hnd).trans hlen, hB.octad_big_N, hB.octad_cent,
    hB.octad_trans, hB.octad_fix⟩

end ListImage

theorem octadBasics_of_type
    {L B : Subgroup G}
    (h : OctadType L B) : OctadBasics L B := by
  obtain ⟨e, hB⟩ := h.exists_listImage
  exact hB.octadBasics

end CFSG.EvenSporadicStandard.M24Std
