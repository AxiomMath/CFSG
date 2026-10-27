module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.FixedFive
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueCenFive
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.InvertingInvolution
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.PartOneAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.ThreeLocal

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

section Inverting

variable {G : Type} [Group G]

private theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G}
    (h₁ : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h₂ : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h₁ x, fun hx => ?_⟩
  simpa [mul_assoc] using h₂ _ hx

private theorem inv_conj_eq_inv {r g : G} (hg : g * r * g⁻¹ = r⁻¹) : g⁻¹ * r * g = r⁻¹ := by
  have h : g * r⁻¹ * g⁻¹ = r := by
    calc g * r⁻¹ * g⁻¹ = (g * r * g⁻¹)⁻¹ := by group
      _ = r := by rw [hg, inv_inv]
  calc g⁻¹ * r * g = g⁻¹ * (g * r⁻¹ * g⁻¹) * g := by rw [h]
    _ = r⁻¹ := by group

private theorem conj_mem_centralizer_of_inv {r g : G} (hg : g * r * g⁻¹ = r⁻¹) {n : G}
    (hn : n ∈ centralizer ({r} : Set G)) : g * n * g⁻¹ ∈ centralizer ({r} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hn ⊢
  have h : g * r⁻¹ * g⁻¹ = r := by
    calc g * r⁻¹ * g⁻¹ = (g * r * g⁻¹)⁻¹ := by group
      _ = r := by rw [hg, inv_inv]
  have hn' : n * r⁻¹ = r⁻¹ * n := (show Commute n r from hn).inv_right.eq
  calc g * n * g⁻¹ * r = g * n * (g⁻¹ * r * g) * g⁻¹ := by group
    _ = g * (n * r⁻¹) * g⁻¹ := by rw [inv_conj_eq_inv hg]; group
    _ = g * (r⁻¹ * n) * g⁻¹ := by rw [hn']
    _ = (g * r⁻¹ * g⁻¹) * (g * n * g⁻¹) := by group
    _ = r * (g * n * g⁻¹) := by rw [h]

theorem mem_normalizer_centralizer_of_inv {r g : G} (hg : g * r * g⁻¹ = r⁻¹) :
    g ∈ normalizer (centralizer ({r} : Set G) : Set G) :=
  mem_normalizer_of_conj_mem (fun _ hn => conj_mem_centralizer_of_inv hg hn) fun n hn => by
    simpa using
      conj_mem_centralizer_of_inv (g := g⁻¹) (by rw [inv_inv]; exact inv_conj_eq_inv hg) hn

theorem exists_involutory_aut_of_inv {r e : G} (hee : e * e = 1) (her : e * r * e⁻¹ = r⁻¹) :
    ∃ α : MulAut (CenG r), α * α = 1 ∧ ∀ x : CenG r, ((α x : CenG r) : G) = e * (x : G) * e⁻¹ := by
  have heN : e ∈ normalizer (centralizer ({r} : Set G) : Set G) :=
    mem_normalizer_centralizer_of_inv her
  refine ⟨(centralizer ({r} : Set G)).normalizerMonoidHom ⟨e, heN⟩, ?_, fun x => rfl⟩
  rw [← map_mul,
    show (⟨e, heN⟩ : normalizer (centralizer ({r} : Set G) : Set G)) * ⟨e, heN⟩ = 1 from
      Subtype.ext hee, map_one]

theorem mem_normalizer_oddCoreCen_of_inv [Finite G] {r g : G} (hg : g * r * g⁻¹ = r⁻¹) :
    g ∈ normalizer (oddCoreCen r : Set G) := by
  have key : ∀ g : G, g * r * g⁻¹ = r⁻¹ → ∀ n ∈ oddCoreCen r, g * n * g⁻¹ ∈ oddCoreCen r := by
    intro g hg n hn
    have hg' : g⁻¹ * r * g⁻¹⁻¹ = r⁻¹ := by rw [inv_inv]; exact inv_conj_eq_inv hg
    have hle : (oddCoreCen r).map (MulAut.conj g).toMonoidHom ≤ oddCoreCen r := by
      refine le_oddCoreCen ?_ ?_ ?_
      · rintro _ ⟨m, hm, rfl⟩
        exact conj_mem_centralizer_of_inv hg (oddCoreCen_le r hm)
      · rintro y hy _ ⟨m, hm, rfl⟩
        have hy' : g⁻¹ * y * g ∈ centralizer ({r} : Set G) := by
          simpa using conj_mem_centralizer_of_inv hg' hy
        refine ⟨(g⁻¹ * y * g) * m * (g⁻¹ * y * g)⁻¹, oddCoreCen_norm r hy' hm, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
        exact odd_card_oddCoreCen r
    exact hle ⟨n, hn, rfl⟩
  exact mem_normalizer_of_conj_mem (key g hg) fun n hn => by
    simpa using key g⁻¹ (by rw [inv_inv]; exact inv_conj_eq_inv hg) n hn

end Inverting

section Five

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem exists_involution_centralizing_five (d : PartThreeData G L t) (h3 : RuThreeFacts L)
    (h5 : RuFiveFacts L) (h5O : 5 ∣ Nat.card (oddCoreCen d.r)) :
    ∃ e ∈ centralizer ({d.f} : Set G), orderOf e = 2 ∧ e * d.r * e⁻¹ = d.r⁻¹ ∧
      ∃ h ∈ oddCoreCen d.r, orderOf h = 5 ∧ e * h = h * e := by
  have hc := d.config
  obtain ⟨δ₀, hδ₀f, hδ₀2, hδ₀1, hδ₀r⟩ := exists_inv_involution h5 ⟨d.f, d.f_mem⟩
    ⟨d.r, d.r_mem⟩ (by rw [Subgroup.orderOf_mk]; exact d.f_ord)
    (by rw [Subgroup.orderOf_mk]; exact d.r_ord) (Subtype.ext d.fr_comm) d.f_typeA
  set δ : G := (δ₀ : G) with hδdef
  have hδL : δ ∈ L := δ₀.2
  have hδ2 : δ * δ = 1 := congrArg Subtype.val hδ₀2
  have hδ1 : δ ≠ 1 := fun h => hδ₀1 (Subtype.ext h)
  have hδr : δ * d.r * δ = d.r⁻¹ := congrArg Subtype.val hδ₀r
  have hδf : δ * d.f = d.f * δ := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hδ₀f)
  have hδinv : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
  have hδr' : δ * d.r * δ⁻¹ = d.r⁻¹ := by rw [hδinv]; exact hδr
  have htδ : δ * t = t * δ := hc.comm δ hδL
  have htr : t * d.r * t⁻¹ = d.r := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hc.comm d.r d.r_mem).symm
  have hV2 : ∀ x ∈ zpowers t ⊔ zpowers δ, x * x = 1 :=
    sq_one_sup (A := zpowers t) (B := zpowers δ)
      (by rw [zpowers_le]; exact mem_centralizer_iff.2 fun z hz => (comm_zpowers hc hδL hz).symm)
      (sq_one_zpowers hc.z_sq) (sq_one_zpowers hδ2)
  have hVp : IsPGroup 2 ↥(zpowers t ⊔ zpowers δ) := fun x =>
    ⟨1, Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two]
      exact hV2 x x.2)⟩
  have htc : t ∈ centralizer ({d.r} : Set G) :=
    mem_centralizer_singleton_iff.2 (hc.comm d.r d.r_mem).symm
  have htN : t ∈ normalizer (oddCoreCen d.r : Set G) :=
    mem_normalizer_of_conj_mem (fun n hn => oddCoreCen_norm d.r htc hn) fun n hn => by
      simpa using oddCoreCen_norm d.r (inv_mem htc) hn
  have hδN : δ ∈ normalizer (oddCoreCen d.r : Set G) := mem_normalizer_oddCoreCen_of_inv hδr'
  have hVO : zpowers t ⊔ zpowers δ ≤ normalizer (oddCoreCen d.r : Set G) :=
    sup_le (zpowers_le.2 htN) (zpowers_le.2 hδN)
  have hC : ∀ x ∈ oddCoreCen d.r, t * x = x * t → x ^ 3 = 1 := by
    intro x hx hxt
    have hmem := cen_odd_le hc h3 d.r_mem d.r_ord (oddCoreCen_le d.r)
      (fun y hy n hn => oddCoreCen_norm d.r hy hn) (odd_card_oddCoreCen d.r) hx hxt.symm
    have h1 : orderOf x ∣ orderOf d.r := orderOf_dvd_of_mem_zpowers hmem
    rw [d.r_ord] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  obtain ⟨e, he, h, hhO, hh5, heh⟩ := exists_fixed_five (oddCoreCen d.r) (zpowers t ⊔ zpowers δ)
    t δ hVp hVO (odd_card_oddCoreCen d.r) (mem_sup_left (mem_zpowers t))
    (mem_sup_right (mem_zpowers δ)) hc.z_sq hδ2 hC h5O
  refine ⟨e, ?_, ?_, ?_, h, hhO, hh5, heh⟩ <;> rcases he with rfl | rfl
  · exact mem_centralizer_singleton_iff.2 hδf
  · exact mul_mem (mem_centralizer_singleton_iff.2 (hc.comm d.f d.f_mem).symm)
      (mem_centralizer_singleton_iff.2 hδf)
  · exact orderOf_eq_prime (by rw [pow_two]; exact hδ2) hδ1
  · refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      calc t * δ * (t * δ) = t * (δ * t) * δ := by group
        _ = t * (t * δ) * δ := by rw [htδ]
        _ = (t * t) * (δ * δ) := by group
        _ = 1 := by rw [hc.z_sq, hδ2, one_mul]
    · intro h1
      apply hc.z_not_mem
      have : t = δ⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact L.inv_mem hδL
  · exact hδr'
  · calc t * δ * d.r * (t * δ)⁻¹ = t * (δ * d.r * δ⁻¹) * t⁻¹ := by group
      _ = t * d.r⁻¹ * t⁻¹ := by rw [hδr']
      _ = (t * d.r * t⁻¹)⁻¹ := by group
      _ = d.r⁻¹ := by rw [htr]

theorem noFive_of (d : PartThreeData G L t) (h3 : RuThreeFacts L) (h5 : RuFiveFacts L)
    (hinv : InvConj G d.f t) : NoFiveField (CenG d.r) := by
  intro Q hQ hfix h5O
  have h5O' : 5 ∣ Nat.card (oddCoreCen d.r) := by
    rwa [oddCoreCen, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  obtain ⟨e, hef, he2, her, h, hhO, hh5, heh⟩ :=
    exists_involution_centralizing_five d h3 h5 h5O'
  have hee : e * e = 1 := by
    have : e ^ 2 = 1 := by rw [← he2]; exact pow_orderOf_eq_one e
    rwa [pow_two] at this
  obtain ⟨α, hαα, hα⟩ := exists_involutory_aut_of_inv hee her
  set P : Subgroup (CenG d.r) := Q ⊓ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _) with hP
  have hcardP : Nat.card P = Nat.card {q : CenG d.r // q ∈ Q ∧ α q = q} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun q => Iff.rfl)
  have hdvd : Nat.card P ∣
      Nat.card ↥(centralizer ({e} : Set G) ⊓ centralizer ({h} : Set G)) := by
    have hψ : ∀ q : P, (((q : CenG d.r)) : G) ∈
        centralizer ({e} : Set G) ⊓ centralizer ({h} : Set G) := by
      intro q
      obtain ⟨hqQ, hqα⟩ := q.2
      refine mem_inf.2 ⟨?_, ?_⟩
      · rw [mem_centralizer_singleton_iff]
        have h1 := hα (q : CenG d.r)
        have h2 : ((α (q : CenG d.r) : CenG d.r) : G) = ((q : CenG d.r) : G) :=
          congrArg Subtype.val hqα
        exact (mul_inv_eq_iff_eq_mul.1 (h1.symm.trans h2)).symm
      · rw [mem_centralizer_singleton_iff]
        obtain ⟨y, hy, rfl⟩ := hhO
        exact (congrArg Subtype.val (mem_centralizer_iff.1 (hQ hqQ) y hy)).symm
    refine Subgroup.card_dvd_of_injective
      (((centralizer ({d.r} : Set G)).subtype.comp P.subtype).codRestrict _ hψ) ?_
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have h9 : 9 ∣ Nat.card ↥(centralizer ({e} : Set G) ⊓ centralizer ({h} : Set G)) :=
    (hcardP ▸ hfix α hαα).trans hdvd
  rcases card_cen_conj_five d.config h5 (hinv e hef he2) heh.symm hh5 with hK | hK <;>
    rw [hK] at h9 <;> omega

end Five

end CFSG.EvenSporadicStandard.RuStd.S2.Glue
