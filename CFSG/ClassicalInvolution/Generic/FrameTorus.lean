module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.Generic.QuadraticNorm

public section

namespace CFSG.ClassicalInvolution.Generic

open scoped MatrixGroups
open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {F : Type*} [Field F] {G : Type*} [Group G]

theorem sg_eq_pm (h2 : (2 : F) ≠ 0) {g S Si : Matrix (Fin 2) (Fin 2) F} {c : F} (hc0 : c ≠ 0)
    (hgg : g * g = c • (1 : Matrix (Fin 2) (Fin 2) F)) (htr : g.trace = 0)
    (hSSi : S * Si = 1) (hSiS : Si * S = 1) {x y x' y' : F} (hy : y ≠ 0)
    (hrel : S * (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • g) =
      (x' • (1 : Matrix (Fin 2) (Fin 2) F) + y' • g) * S) :
    S * g = g * S ∨ S * g = -(g * S) := by
  have h1 : y • (S * g) = (x' - x) • S + y' • (g * S) := by
    have := hrel
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul] at this
    linear_combination (norm := module) this
  have h2' : S * g = ((x' - x) / y) • S + (y' / y) • (g * S) := by
    have h3 : S * g = y⁻¹ • (y • (S * g)) := by rw [smul_smul, inv_mul_cancel₀ hy, one_smul]
    rw [h3, h1, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
  set p : F := (x' - x) / y with hp
  set q : F := y' / y with hq
  have h3 : S * g * Si = p • (1 : Matrix (Fin 2) (Fin 2) F) + q • g := by
    rw [h2', add_mul, smul_mul_assoc, smul_mul_assoc, hSSi, Matrix.mul_assoc, hSSi, mul_one]
  have h4 : p = 0 := by
    have htr' : (S * g * Si).trace = g.trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc g Si S, hSiS, mul_one]
    rw [h3, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htr, Matrix.trace_one] at htr'
    simp at htr'
    rcases htr' with h | h
    · exact h
    · exact absurd h (by simpa using h2)
  have h5 : S * g = q • (g * S) := by rw [h2', h4]; simp
  have h6 : (c - q * q * c) • S = 0 := by
    have e1 : S * (g * g) = c • S := by rw [hgg, mul_smul_comm, mul_one]
    have e2 : S * (g * g) = (q * q * c) • S := by
      calc S * (g * g) = (S * g) * g := by rw [Matrix.mul_assoc]
        _ = (q • (g * S)) * g := by rw [h5]
        _ = q • (g * (S * g)) := by rw [smul_mul_assoc, Matrix.mul_assoc]
        _ = q • (g * (q • (g * S))) := by rw [h5]
        _ = (q * q) • ((g * g) * S) := by
          rw [mul_smul_comm, smul_smul, ← Matrix.mul_assoc]
        _ = (q * q * c) • S := by rw [hgg, smul_mul_assoc, one_mul, smul_smul]
    rw [sub_smul, ← e1, ← e2, sub_self]
  have h7 : c - q * q * c = 0 := by
    have := congrArg (fun M => M * Si) h6
    simp only [smul_mul_assoc, hSSi, zero_mul] at this
    have h00 := congrFun (congrFun this 0) 0
    simpa using h00
  have h8 : q * q = 1 := by
    have : c * (1 - q * q) = 0 := by linear_combination h7
    have := (mul_eq_zero.mp this).resolve_left hc0
    linear_combination -this
  rcases mul_self_eq_one_iff.mp h8 with hq1 | hq1
  · left
    rw [h5, hq1, one_smul]
  · right
    rw [h5, hq1, neg_smul, one_smul]

namespace Witness

variable {φ : SL(2, F) →* G} {E : Subgroup G} (W : Witness φ E)

theorem centSub_eq_fixSub (hD : DiagData φ E) : centSub φ E = fixSub W.g := by
  ext s
  rw [W.mem_centSub_iff hD s]
  exact Iff.rfl

end Witness

namespace DiagData

variable {φ : SL(2, F) →* G} {E : Subgroup G}

theorem isCyclic_and_card_centSub [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F)) :
    IsCyclic (centSub φ E) ∧
      ∃ η : ℤ, (η = 1 ∨ η = -1) ∧ (Nat.card (centSub φ E) : ℤ) = Nat.card F - η := by
  obtain ⟨W⟩ := hD.nonempty_witness
  let e : centSub φ E ≃* fixSub W.g := MulEquiv.subgroupCongr (W.centSub_eq_fixSub hD)
  obtain ⟨hcyc, η, hη, hcard⟩ := W.inv.isCyclic_and_card_fixSub hodd
  refine ⟨e.isCyclic.mpr hcyc, η, hη, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact hcard

theorem normSub_le_normalizer [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F)) :
    normSub φ E ≤ Subgroup.normalizer (centSub φ E : Set SL(2, F)) := by
  intro s hs
  by_cases hsH : s ∈ centSub φ E
  · exact Subgroup.le_normalizer hsH
  · rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [hD.mul_inv_mul_inv hodd hs hsH hk]
      exact (centSub φ E).inv_mem hk
    · intro hk
      have hs' : s⁻¹ ∈ normSub φ E := (normSub φ E).inv_mem hs
      have hs'' : s⁻¹ ∉ centSub φ E := fun h => hsH (by simpa using (centSub φ E).inv_mem h)
      have h1 := hD.mul_inv_mul_inv hodd hs' hs'' hk
      have h3 : s⁻¹ * (s * k * s⁻¹) * s⁻¹⁻¹ = k := by group
      rw [h3] at h1
      rw [h1]
      exact (centSub φ E).inv_mem hk

theorem sl2_eq_pm_one_of_smul_one {h : SL(2, F)} {x : F}
    (hx : (h : Matrix (Fin 2) (Fin 2) F) = x • (1 : Matrix (Fin 2) (Fin 2) F)) :
    h = 1 ∨ h = -1 := by
  have hdet := h.2
  rw [hx, Matrix.det_fin_two] at hdet
  simp at hdet
  have hx2 : x * x = 1 := hdet
  rcases mul_self_eq_one_iff.mp hx2 with h1 | h1
  · left
    apply sl_ext
    rw [hx, h1, one_smul, Matrix.SpecialLinearGroup.coe_one]
  · right
    apply sl_ext
    rw [hx, h1, neg_smul, one_smul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]

theorem normalizer_centSub_le [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) :
    Subgroup.normalizer (centSub φ E : Set SL(2, F)) ≤ normSub φ E := by
  intro s hs
  obtain ⟨W⟩ := hD.nonempty_witness
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  rw [W.mem_normSub_iff hD h2]
  obtain ⟨-, η, hη, hcard⟩ := hD.isCyclic_and_card_centSub hodd
  have hex : ∃ h ∈ centSub φ E, h ≠ 1 ∧ h ≠ -1 := by
    by_contra hcon
    push Not at hcon
    have hle : centSub φ E ≤ Subgroup.zpowers (-1 : SL(2, F)) := by
      intro h hh
      by_cases h1 : h = 1
      · rw [h1]
        exact one_mem _
      · rw [hcon h hh h1]
        exact Subgroup.mem_zpowers _
    have hc2 : Nat.card (centSub φ E) ≤ 2 := by
      have := Subgroup.card_le_of_le hle
      rwa [Nat.card_zpowers, sl2_orderOf_neg_one hodd] at this
    omega
  obtain ⟨h, hh, hh1, hh2⟩ := hex
  obtain ⟨a, b, e, c, hc0, hAmat, hac, hAA⟩ := W.inv.entries
  have hhH := (W.mem_centSub_iff hD h).mp hh
  obtain ⟨x, y, hxy⟩ := W.inv.exists_comm_eq h2 _ ((slConj_eq_iff W.g h h).mp hhH)
  have hy : y ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hxy
    rcases sl2_eq_pm_one_of_smul_one hxy with h1 | h1
    · exact hh1 h1
    · exact hh2 h1
  have htH : s * h * s⁻¹ ∈ centSub φ E := (Subgroup.mem_normalizer_iff.mp hs h).mp hh
  have htα := (W.mem_centSub_iff hD _).mp htH
  obtain ⟨x', y', hxy'⟩ := W.inv.exists_comm_eq h2 _ ((slConj_eq_iff W.g _ _).mp htα)
  have hrel : (s : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F) =
      ((s * h * s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (s : Matrix (Fin 2) (Fin 2) F) := by
    have e : s * h * s⁻¹ * s = s * h := by group
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, e]
  rw [hxy, hxy'] at hrel
  have hgg : W.g.val * W.g.val = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hAA, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have htr : (W.g.val).trace = 0 := by
    rw [hAmat]
    simp [Matrix.trace_fin_two]
  have hSSi : (s : Matrix (Fin 2) (Fin 2) F) * ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hSiS : ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (s : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rcases sg_eq_pm h2 hc0 hgg htr hSSi hSiS hy hrel with h1 | h1
  · left
    exact (slConj_eq_iff W.g s s).mpr h1.symm
  · right
    refine (slConj_eq_iff W.g s (s * (-1))).mpr ?_
    rw [coe_mul_neg_one, neg_mul, h1, neg_neg]

theorem normSub_eq_normalizer_centSub [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) : normSub φ E = Subgroup.normalizer (centSub φ E : Set SL(2, F)) :=
  le_antisymm (hD.normSub_le_normalizer hodd) (hD.normalizer_centSub_le hodd h5)

end DiagData

theorem mem_normalizer_map_iff {φ : SL(2, F) →* G} (hφ : Function.Injective φ)
    (H : Subgroup SL(2, F)) (s : SL(2, F)) :
    φ s ∈ Subgroup.normalizer ((H.map φ : Subgroup G) : Set G) ↔
      s ∈ Subgroup.normalizer (H : Set SL(2, F)) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff] at h ⊢
    intro k
    have := h (φ k)
    rw [Subgroup.mem_map_iff_mem hφ, ← map_inv, ← map_mul, ← map_mul,
      Subgroup.mem_map_iff_mem hφ] at this
    exact this
  · intro h
    rw [Subgroup.mem_normalizer_iff] at h ⊢
    intro y
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨s * k * s⁻¹, (h k).mp hk, ?_⟩
      simp
    · rintro ⟨k', hk', hk'y⟩
      have hy : y = φ (s⁻¹ * k' * s) := by
        rw [map_mul, map_mul, map_inv, hk'y]
        group
      have hmem : s⁻¹ * k' * s ∈ H := by
        refine (h (s⁻¹ * k' * s)).mpr ?_
        simpa [mul_assoc] using hk'
      rw [hy]
      exact ⟨_, hmem, rfl⟩

namespace InSigma

variable [Finite F] {E K : Subgroup G}

theorem isCyclic_and_card_centPart (hK : InSigma F E K) (hodd : Odd (Nat.card F)) :
    IsCyclic (centPart K E) ∧
      ∃ η : ℤ, (η = 1 ∨ η = -1) ∧ (Nat.card (centPart K E) : ℤ) = Nat.card F - η := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨hcyc, η, hη, hcard⟩ := hD.isCyclic_and_card_centSub hodd
  rw [centPart_range]
  let e := (centSub φ E).equivMapOfInjective φ hD.inj
  refine ⟨e.isCyclic.mp hcyc, η, hη, ?_⟩
  rw [← Nat.card_congr e.toEquiv]
  exact hcard

theorem mem_normalizer_centPart_iff (hK : InSigma F E K) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {x : G} (hx : x ∈ K) :
    x ∈ Subgroup.normalizer (centPart K E : Set G) ↔ x ∈ Subgroup.normalizer (E : Set G) := by
  obtain ⟨φ, rfl, hD⟩ := hK
  obtain ⟨s, rfl⟩ := hx
  rw [centPart_range, mem_normalizer_map_iff hD.inj]
  have := hD.normSub_eq_normalizer_centSub hodd h5
  constructor
  · intro h
    have h' : s ∈ normSub φ E := by rw [this]; exact h
    exact h'
  · intro h
    have h' : s ∈ normSub φ E := h
    rw [this] at h'
    exact h'

theorem normPart_eq (hK : InSigma F E K) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    normPart K E = K ⊓ Subgroup.normalizer (centPart K E : Set G) := by
  ext x
  rw [mem_normPart_iff, Subgroup.mem_inf]
  constructor
  · rintro ⟨hxK, hxN⟩
    exact ⟨hxK, (hK.mem_normalizer_centPart_iff hodd h5 hxK).mpr hxN⟩
  · rintro ⟨hxK, hxN⟩
    exact ⟨hxK, (hK.mem_normalizer_centPart_iff hodd h5 hxK).mp hxN⟩

end InSigma

theorem four_dvd_iff_modEq {n q : ℕ} {η : ℤ} (h : (n : ℤ) = q - η) :
    4 ∣ n ↔ (q : ℤ) ≡ η [ZMOD 4] := by
  rw [Int.modEq_iff_dvd]
  constructor <;> intro hh <;> omega

namespace InSigma

variable [Finite F] {E K : Subgroup G}

omit [Field F] [Finite F] in
theorem eq_one_or_eq_of_two_power {z : G} (hz : IsUniqueInvolution K z) {η : ℤ}
    (h : (Nat.card (centPart K E) : ℤ) = Nat.card F - η)
    (hmod : ¬ (Nat.card F : ℤ) ≡ η [ZMOD 4]) {x : G} (hx : x ∈ centPart K E) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) : x = 1 ∨ x = z := by
  have h4 : ¬ 4 ∣ Nat.card (centPart K E) := fun h4 =>
    hmod ((four_dvd_iff_modEq h).mp h4)
  have h1 : orderOf x ∣ Nat.card (centPart K E) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : centPart K E)
    rwa [← Subgroup.orderOf_coe] at this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxk)
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    apply h4
    refine dvd_trans ?_ h1
    rw [hj]
    exact (pow_dvd_pow 2 hj2 : 2 ^ 2 ∣ 2 ^ j)
  have hsq : x * x = 1 := by
    rw [← pow_two]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hj]
    simpa using (pow_dvd_pow 2 hj1 : 2 ^ j ∣ 2 ^ 1)
  exact hz.unique x (centPart_le_left _ _ hx) hsq

end InSigma

end CFSG.ClassicalInvolution.Generic
