module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Hom

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem elemAb_sup_zpowers {Vt : Subgroup G} {q : G} (hq2 : q * q = 1)
    (hV2 : ∀ v ∈ Vt, v * v = 1) (hVc : ∀ a ∈ Vt, ∀ b ∈ Vt, a * b = b * a)
    (hqV : ∀ v ∈ Vt, v * q = q * v) :
    (∀ a ∈ Vt ⊔ zpowers q, ∀ b ∈ Vt ⊔ zpowers q, a * b = b * a) ∧
      ∀ a ∈ Vt ⊔ zpowers q, a * a = 1 := by
  have hle : Vt ≤ centralizer (zpowers q : Set G) := fun v hv => by
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute q v from (hqV v hv).symm) i).eq
  have hq1 : ∀ x ∈ zpowers q, x = 1 ∨ x = q := fun x hx => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have h2 : q ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hq2
    have hk : q ^ k = q ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [hk, h]; simp
    · right; rw [hk, h]; simp
  have hform : ∀ x ∈ Vt ⊔ zpowers q, ∃ v ∈ Vt, x = v ∨ x = v * q := by
    intro x hx
    obtain ⟨v, hv, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hx
    rcases hq1 y hy with rfl | rfl
    · exact ⟨v, hv, Or.inl (mul_one v)⟩
    · exact ⟨v, hv, Or.inr rfl⟩
  have hmul : ∀ v ∈ Vt, ∀ w ∈ Vt, v * q * w = v * w * q := fun v hv w hw => by
    have hwq := hqV w hw
    calc v * q * w = v * (q * w) := by group
      _ = v * (w * q) := by rw [← hwq]
      _ = v * w * q := by group
  have hmul2 : ∀ v ∈ Vt, ∀ w ∈ Vt, v * q * (w * q) = v * w := fun v hv w hw => by
    calc v * q * (w * q) = (v * q * w) * q := by group
      _ = v * w * q * q := by rw [hmul v hv w hw]
      _ = v * w * (q * q) := by group
      _ = v * w := by rw [hq2, mul_one]
  constructor
  · intro a ha b hb
    obtain ⟨v, hv, hva⟩ := hform a ha
    obtain ⟨w, hw, hwb⟩ := hform b hb
    have hvw := hVc v hv w hw
    rcases hva with hva | hva <;> rcases hwb with hwb | hwb <;> rw [hva, hwb]
    · exact hvw
    · calc v * (w * q) = v * w * q := by group
        _ = w * v * q := by rw [hvw]
        _ = w * q * v := (hmul w hw v hv).symm
    · calc v * q * w = v * w * q := hmul v hv w hw
        _ = w * v * q := by rw [hvw]
        _ = w * (v * q) := by group
    · rw [hmul2 v hv w hw, hmul2 w hw v hv, hvw]
  · intro a ha
    obtain ⟨v, hv, hva⟩ := hform a ha
    rcases hva with hva | hva <;> rw [hva]
    · exact hV2 v hv
    · rw [hmul2 v hv v hv]
      exact hV2 v hv

namespace Cfg

variable {d : Datum A} {α : ℕ} (K : Cfg d α)

include K

theorem card_elemAb_le_eight {E : Subgroup G} (hEA : E ≤ A)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1) : Nat.card E ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa [pow_two] using hsq g g.2)⟩
  obtain ⟨P, hP, hEP⟩ := exists_isSylowOf_of_le hp hEA
  obtain ⟨k, -, hk⟩ := d.S_sylow.exists_mem_conj hP
  have hE'S : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ d.S := by
    rintro _ ⟨x, hx, rfl⟩
    have := (hk x).1 (hEP hx)
    simpa [MulAut.conj_apply] using this
  have hcomm' : ∀ a ∈ E.map (MulAut.conj k⁻¹).toMonoidHom,
      ∀ b ∈ E.map (MulAut.conj k⁻¹).toMonoidHom, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k⁻¹ * x * k⁻¹⁻¹ * (k⁻¹ * y * k⁻¹⁻¹) = k⁻¹ * (x * y) * k⁻¹⁻¹ := by group
      _ = k⁻¹ * (y * x) * k⁻¹⁻¹ := by rw [hcomm x hx y hy]
      _ = k⁻¹ * y * k⁻¹⁻¹ * (k⁻¹ * x * k⁻¹⁻¹) := by group
  have hsq' : ∀ a ∈ E.map (MulAut.conj k⁻¹).toMonoidHom, a * a = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k⁻¹ * x * k⁻¹⁻¹ * (k⁻¹ * x * k⁻¹⁻¹) = k⁻¹ * (x * x) * k⁻¹⁻¹ := by group
      _ = 1 := by rw [hsq x hx]; group
  have := K.sf.elemAb_le _ hE'S hcomm' hsq'
  rwa [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective] at this

end Cfg

namespace Cfg

variable {d : Datum A} (K : Cfg d 0)

include K

theorem false_of_isConj_q_z (hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t) {n z : G}
    (hnN : n ∈ normalizer (K.c.V : Set G))
    (hord : orderOf (K.c.V.normalizerMonoidHom ⟨n, hnN⟩) = 7)
    (hzP : z ∈ centralizer (K.c.V : Set G)) (hzW : z ∉ K.c.W)
    (hnz : n * z * n⁻¹ = z) (hzq : IsConj d.q z) : False := by
  obtain ⟨g₀, hg₀, hgX⟩ := d.exists_conj_config K.h hzq
  have hzg : g₀ * z * g₀⁻¹ = d.q := by rw [← hg₀]; group
  have hVS : K.c.V ≤ d.S := K.c.V_le_S K.h
  have hVz : ∀ v ∈ K.c.V, v * z = z * v := fun v hv => mem_centralizer_iff.1 hzP v hv
  have hñq : (g₀ * n * g₀⁻¹) * d.q * (g₀ * n * g₀⁻¹)⁻¹ = d.q := by
    calc (g₀ * n * g₀⁻¹) * d.q * (g₀ * n * g₀⁻¹)⁻¹
        = g₀ * (n * (g₀⁻¹ * d.q * g₀) * n⁻¹) * g₀⁻¹ := by group
      _ = g₀ * (n * z * n⁻¹) * g₀⁻¹ := by rw [hg₀]
      _ = g₀ * z * g₀⁻¹ := by rw [hnz]
      _ = d.q := hzg
  have hñN : g₀ * n * g₀⁻¹ ∈ normalizer (A : Set G) := by
    rw [← d.centralizer_q K.h, mem_centralizer_singleton_iff]
    calc (g₀ * n * g₀⁻¹) * d.q
        = ((g₀ * n * g₀⁻¹) * d.q * (g₀ * n * g₀⁻¹)⁻¹) * (g₀ * n * g₀⁻¹) := by group
      _ = d.q * (g₀ * n * g₀⁻¹) := by rw [hñq]
  set Vt : Subgroup G := K.c.V.map (MulAut.conj g₀).toMonoidHom with hVt
  have hVtmem : ∀ x, x ∈ Vt ↔ ∃ v ∈ K.c.V, g₀ * v * g₀⁻¹ = x := fun x => by
    simp [hVt, Subgroup.mem_map, MulAut.conj_apply]
  have hVtX : ∀ x ∈ Vt, x ∈ d.X := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := (hVtmem x).1 hx
    exact hgX v (d.S_le_X (hVS hv)) (hVz v hv)
  have hVtN : ∀ x ∈ Vt, x ∈ normalizer (A : Set G) := fun x hx => d.X_sylow.le (hVtX x hx)
  have hVt2 : ∀ x ∈ Vt, x * x = 1 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := (hVtmem x).1 hx
    calc g₀ * v * g₀⁻¹ * (g₀ * v * g₀⁻¹) = g₀ * (v * v) * g₀⁻¹ := by group
      _ = 1 := by rw [K.sf.V_sq v hv]; group
  have hVtc : ∀ a ∈ Vt, ∀ b ∈ Vt, a * b = b * a := by
    intro a ha b hb
    obtain ⟨v, hv, rfl⟩ := (hVtmem a).1 ha
    obtain ⟨w, hw, rfl⟩ := (hVtmem b).1 hb
    calc g₀ * v * g₀⁻¹ * (g₀ * w * g₀⁻¹) = g₀ * (v * w) * g₀⁻¹ := by group
      _ = g₀ * (w * v) * g₀⁻¹ := by rw [K.sf.V_comm v hv w hw]
      _ = g₀ * w * g₀⁻¹ * (g₀ * v * g₀⁻¹) := by group
  have hVtcard : Nat.card Vt = 8 := by
    rw [hVt, Subgroup.card_map_of_injective (MulAut.conj g₀).injective, K.sf.card_V]
  have hVcard : 4 < Nat.card K.c.V := by rw [K.sf.card_V]; norm_num
  obtain ⟨v₀, hv₀, hv₀1, hv₀QS⟩ := K.exists_conj_mem_QS hVcard fun v hv =>
    hgX v (d.S_le_X (hVS hv)) (hVz v hv)
  have hQSS : d.QS ≤ d.S := sup_le (fun u hu => (K.Q_le_W hQt hu).1) le_rfl
  have hv₀A : g₀ * v₀ * g₀⁻¹ ∈ A := d.S_le_A (hQSS hv₀QS)
  have horb : ∀ y ∈ Vt, y ≠ 1 →
      ∃ j : ℕ, (g₀ * n * g₀⁻¹) ^ j * (g₀ * v₀ * g₀⁻¹) * ((g₀ * n * g₀⁻¹) ^ j)⁻¹ = y := by
    intro y hy hy1
    obtain ⟨w, hw, rfl⟩ := (hVtmem y).1 hy
    have hw1 : w ≠ 1 := fun h => hy1 (by rw [h]; group)
    obtain ⟨j, hj⟩ := K.exists_pow_conj_of_order_seven hnN hord hv₀ hw hv₀1 hw1
    refine ⟨j, ?_⟩
    calc (g₀ * n * g₀⁻¹) ^ j * (g₀ * v₀ * g₀⁻¹) * ((g₀ * n * g₀⁻¹) ^ j)⁻¹
        = g₀ * (n ^ j * v₀ * (n ^ j)⁻¹) * g₀⁻¹ := by rw [conj_pow]; group
      _ = g₀ * w * g₀⁻¹ := by rw [hj]
  have hVtA : Vt ≤ A := le_of_mem_inf_of_transitive hñN hv₀A horb
  have hqq : d.q * d.q = 1 := Sec1.q_mul_self d
  have hqV : ∀ v ∈ Vt, v * d.q = d.q * v := fun v hv => mem_centralizer_iff.1 d.q_cent v (hVtA hv)
  obtain ⟨hEc, hE2⟩ := elemAb_sup_zpowers hqq hVt2 hVtc hqV
  have hEA : Vt ⊔ zpowers d.q ≤ A := sup_le hVtA (zpowers_le.2 d.q_mem)
  have hle8 := K.card_elemAb_le_eight hEA hEc hE2
  have hqnV : d.q ∉ Vt := fun hq => by
    obtain ⟨v, hv, hve⟩ := (hVtmem d.q).1 hq
    have hvz : v = z := by
      have : v = g₀⁻¹ * d.q * g₀ := by rw [← hve]; group
      rw [this, hg₀]
    apply hzW
    rw [← hvz]
    exact K.c.mem_W_of_comm (hVS hv) (fun v' hv' => K.sf.V_comm v hv v' hv')
  have h1 := Subgroup.relIndex_mul_card Vt (Vt ⊔ zpowers d.q)
  rw [inf_eq_left.2 le_sup_left, hVtcard] at h1
  have hne : Vt.relIndex (Vt ⊔ zpowers d.q) ≠ 1 := fun h =>
    hqnV (Subgroup.relIndex_eq_one.1 h (mem_sup_right (mem_zpowers _)))
  have hpos : 0 < Nat.card (Vt ⊔ zpowers d.q : Subgroup G) := Nat.card_pos
  omega

end Cfg

end CFSG.OddStandard.ChengHeld.Excl2
