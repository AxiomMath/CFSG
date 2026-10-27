module

public import CFSG.GH74.Uniqueness.Bender.UnitaryTransfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelUnitaryTorus

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Algebra

def multiplierSubfield {E : Type} [Field E] [Finite E] (A : AddSubgroup E) : Subfield E where
  carrier := {x | ∀ y ∈ A, x * y ∈ A}
  zero_mem' := fun y _ => by simp
  one_mem' := fun y hy => by simpa using hy
  add_mem' := fun {x x'} hx hx' y hy => by rw [add_mul]; exact A.add_mem (hx y hy) (hx' y hy)
  neg_mem' := fun {x} hx y hy => by rw [neg_mul]; exact A.neg_mem (hx y hy)
  mul_mem' := fun {x x'} hx hx' y hy => by rw [mul_assoc]; exact hx _ (hx' y hy)
  inv_mem' := fun x hx => by
    classical
    have : Fintype E := Fintype.ofFinite E
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      intro y _
      simp
    · have hpow : ∀ m : ℕ, ∀ y ∈ A, x ^ m * y ∈ A := by
        intro m
        induction m with
        | zero => intro y hy; simpa using hy
        | succ m ih => intro y hy; rw [pow_succ, mul_assoc]; exact ih _ (hx y hy)
      have h1 : x ^ (Fintype.card E - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx0
      have hc : 2 ≤ Fintype.card E := Fintype.one_lt_card
      have h2 : x⁻¹ = x ^ (Fintype.card E - 2) := by
        apply eq_inv_of_mul_eq_one_right ?_ |>.symm
        rw [← pow_succ', show Fintype.card E - 2 + 1 = Fintype.card E - 1 by omega, h1]
      rw [h2]
      exact hpow _

theorem addSubgroup_eq_top_of_scalar_stable {E : Type} [Field E] [Finite E] {q : ℕ}
    (hE : Nat.card E = q ^ 2) (hq : 2 ≤ q) (A : AddSubgroup E) {a : E} (haA : a ∈ A) (ha : a ≠ 0)
    (S : Subgroup Eˣ) (hS : ∀ u ∈ S, ∀ y ∈ A, (u : E) * y ∈ A) (hcard : q < Nat.card S + 1) :
    A = ⊤ := by
  classical
  set T := multiplierSubfield A with hT
  have hST : ∀ u ∈ S, (u : E) ∈ T := fun u hu y hy => hS u hu y hy
  have hTcard : q < Nat.card T := by
    let f : Option S → T := fun o =>
      Option.elim o ⟨0, T.zero_mem⟩ (fun u => ⟨((u : Eˣ) : E), hST _ u.2⟩)
    have hinj : Function.Injective f := by
      rintro (_ | u) (_ | u') h
      · rfl
      · exact (Units.ne_zero _ (congrArg Subtype.val h).symm).elim
      · exact (Units.ne_zero _ (congrArg Subtype.val h)).elim
      · exact congrArg some (Subtype.ext (Units.ext (congrArg Subtype.val h)))
    have := Nat.card_le_card_of_injective f hinj
    rw [Finite.card_option] at this
    omega
  have hrank := Module.natCard_eq_pow_finrank (K := T) (V := E)
  have hrank1 : Module.finrank T E = 1 := by
    have hpos : 0 < Module.finrank T E := Module.finrank_pos
    by_contra hne
    have h2 : 2 ≤ Module.finrank T E := by omega
    have : Nat.card T ^ 2 ≤ Nat.card T ^ Module.finrank T E :=
      Nat.pow_le_pow_right (by omega) h2
    rw [← hrank, hE] at this
    nlinarith
  have hcT : Nat.card T = Nat.card E := by rw [hrank1, pow_one] at hrank; exact hrank.symm
  have hTtop : ∀ x : E, x ∈ T := by
    have hsub : (T : Set E) ⊆ Set.univ := Set.subset_univ _
    have := Set.eq_of_subset_of_ncard_le hsub (by
      rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
      exact hcT.ge) Set.finite_univ
    intro x
    have hx : x ∈ (Set.univ : Set E) := Set.mem_univ x
    rw [← this] at hx
    exact hx
  rw [eq_top_iff]
  intro y _
  have := hTtop (y / a) a haA
  rwa [div_mul_cancel₀ y ha] at this

end Algebra

section Model

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.TheoremC

variable {E : Type} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

include hJ in
def firstCoordAddSubgroup (W : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : AddSubgroup E where
  carrier := {x | ∃ z : hermitianUnipotentCoord J, hermitianUnipotentPSU J hJ z ∈ W ∧ z.1.1 = x}
  add_mem' := by
    rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    exact ⟨z * z', by rw [map_mul]; exact W.mul_mem hz hz', rfl⟩
  zero_mem' := ⟨1, by rw [map_one]; exact W.one_mem, rfl⟩
  neg_mem' := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z⁻¹, by rw [map_inv]; exact W.inv_mem hz, ?_⟩
    simp

theorem mem_rootCenter_unitaryCoverRoot_iff (f : ℕ) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f)
    {w : ProjectiveSpecialUnitaryMatrixGroup J} :
    w ∈ rootCenter (unitaryCoverRoot J hJ) ↔
      ∃ z : hermitianUnipotentCoord J, z.1.1 = 0 ∧ hermitianUnipotentPSU J hJ z = w := by
  rw [← inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ]
  constructor
  · intro h
    exact ⟨h.1, fun q hq => (mem_rootCenter_iff.mp h).2 q hq⟩
  · intro h
    exact mem_rootCenter_iff.mpr ⟨h.1, fun q hq => (h.2 q hq).eq⟩

omit [CharP E 2] in
include hJ in
theorem unitary_scalarImage_card_gt (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f) :
    2 ^ f < Nat.card (unitaryCoverScalarImage J) + 1 := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rw [unitaryCoverScalarImage_card J (2 ^ f) hcard hfixed hJ]
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq] at hq4 ⊢
  have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hgpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h1 : q ≤ (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
    rw [Nat.le_div_iff_mul_le hgpos]
    have h3 : 3 * q + 1 ≤ q ^ 2 := by nlinarith
    have h4 : q * Nat.gcd 3 (q + 1) ≤ 3 * q := by nlinarith
    omega
  omega

include hJ in
theorem unitary_root_irreducible (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f)
    (W : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hZW : rootCenter (unitaryCoverRoot J hJ) ≤ W) (hWR : W ≤ unitaryCoverRoot J hJ)
    (hinv : ∀ d ∈ unitaryCoverTorus J hJ, ∀ w ∈ W, d * w * d⁻¹ ∈ W) :
    W = rootCenter (unitaryCoverRoot J hJ) ∨ W = unitaryCoverRoot J hJ := by
  classical
  by_cases hWZ : W ≤ rootCenter (unitaryCoverRoot J hJ)
  · exact Or.inl (le_antisymm hWZ hZW)
  right
  obtain ⟨w, hwW, hwZ⟩ := Set.not_subset.mp hWZ
  obtain ⟨z, rfl⟩ := hWR hwW
  have ha : z.1.1 ≠ 0 := fun h0 =>
    hwZ ((mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed).mpr ⟨z, h0, rfl⟩)
  have hA : ∀ k : Eˣ, ∀ y ∈ firstCoordAddSubgroup J hJ W,
      ((unitaryCoverScalar J k : Eˣ) : E) * y ∈ firstCoordAddSubgroup J hJ W := by
    rintro k _ ⟨z', hz', rfl⟩
    refine ⟨hermitianTorusAction J k z', ?_, hermitianTorusAction_fst_eq_scalar J k z'⟩
    rw [← unitaryCoverTorus_conj_root J hJ k z']
    exact hinv _ ⟨k, rfl⟩ _ hz'
  have hS : ∀ u ∈ unitaryCoverScalarImage J, ∀ y ∈ firstCoordAddSubgroup J hJ W,
      (u : E) * y ∈ firstCoordAddSubgroup J hJ W := by
    rintro u ⟨k, rfl⟩ y hy
    exact hA k y hy
  have hAtop := addSubgroup_eq_top_of_scalar_stable hcard
    (by have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hf; omega)
    (firstCoordAddSubgroup J hJ W) ⟨z, hwW, rfl⟩ ha (unitaryCoverScalarImage J) hS
    (unitary_scalarImage_card_gt J hJ f hf hcard hfixed)
  refine le_antisymm hWR ?_
  rintro _ ⟨y, rfl⟩
  have hy : y.1.1 ∈ firstCoordAddSubgroup J hJ W := by rw [hAtop]; exact AddSubgroup.mem_top _
  obtain ⟨y', hy'W, hy'⟩ := hy
  have hinv : ∀ z : hermitianUnipotentCoord J, (z⁻¹).1.1 = -z.1.1 := fun z => by
    simp
  have hz0 : (y'⁻¹ * y).1.1 = 0 := by
    show (y'⁻¹).1.1 + y.1.1 = 0
    rw [hinv, hy']
    ring
  have hcen := (mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed).mpr ⟨y'⁻¹ * y, hz0, rfl⟩
  have hsplit : hermitianUnipotentPSU J hJ y = hermitianUnipotentPSU J hJ y' *
      hermitianUnipotentPSU J hJ (y'⁻¹ * y) := by
    rw [← map_mul]
    congr 1
    group
  rw [hsplit]
  exact W.mul_mem hy'W (hZW hcen)

include hJ in
theorem unitary_torus_fixedPointFree (f : ℕ) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f) {d : ProjectiveSpecialUnitaryMatrixGroup J}
    (hd : d ∈ unitaryCoverTorus J hJ) (hd1 : d ≠ 1) {x : ProjectiveSpecialUnitaryMatrixGroup J}
    (hx : x ∈ unitaryCoverRoot J hJ)
    (hdx : d * x * d⁻¹ * x⁻¹ ∈ rootCenter (unitaryCoverRoot J hJ)) :
    x ∈ rootCenter (unitaryCoverRoot J hJ) := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨z, rfl⟩ := hx
  have hinv : ∀ z : hermitianUnipotentCoord J, (z⁻¹).1.1 = -z.1.1 := fun z => by
    simp
  have hconj := unitaryCoverTorus_conj_root J hJ k z
  have hcomm : hermitianTorusPSU J hJ k * hermitianUnipotentPSU J hJ z *
      (hermitianTorusPSU J hJ k)⁻¹ * (hermitianUnipotentPSU J hJ z)⁻¹ =
        hermitianUnipotentPSU J hJ (hermitianTorusAction J k z * z⁻¹) := by
    rw [hconj, map_mul, map_inv]
  rw [hcomm, mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed] at hdx
  obtain ⟨z₂, hz₂, hz₂eq⟩ := hdx
  have hz₂' : z₂ = hermitianTorusAction J k z * z⁻¹ := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ hz₂eq
  have h0 : (hermitianTorusAction J k z * z⁻¹).1.1 = 0 := by rw [← hz₂']; exact hz₂
  have h1 : (hermitianTorusAction J k z * z⁻¹).1.1 =
      ((unitaryCoverScalar J k : Eˣ) : E) * z.1.1 - z.1.1 := by
    show (hermitianTorusAction J k z).1.1 + (z⁻¹).1.1 = _
    rw [hermitianTorusAction_fst_eq_scalar, hinv]
    ring
  by_cases ha : z.1.1 = 0
  · exact (mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed).mpr ⟨z, ha, rfl⟩
  · exfalso
    apply hd1
    have hs : ((unitaryCoverScalar J k : Eˣ) : E) = 1 := by
      have : (((unitaryCoverScalar J k : Eˣ) : E) - 1) * z.1.1 = 0 := by
        rw [sub_mul, one_mul, ← h1, h0]
      rcases mul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact (ha h).elim
    have hk : k ∈ (unitaryCoverScalar J).ker := by
      rw [MonoidHom.mem_ker]
      exact Units.ext hs
    rw [unitaryCoverScalar_ker_eq_torus_ker J hJ, MonoidHom.mem_ker] at hk
    exact hk

end Model

section BenderLevel

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem BenderType.irreducible_unitary {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K}
    (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) (W : Subgroup K)
    (hZW : rootCenter (Q : Subgroup K) ≤ W) (hWQ : W ≤ (Q : Subgroup K))
    (hinv : ∀ d ∈ cartan (Q : Subgroup K) t, ∀ w ∈ W, d * w * d⁻¹ ∈ W) :
    W = rootCenter (Q : Subgroup K) ∨ W = (Q : Subgroup K) := by
  obtain ⟨hn, -⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, φ, hφQ, hφD⟩ := h.exists_standard_iso_unitary Q ht htQ
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have hZ : rootCenter (unitaryCoverRoot J hJ) = (rootCenter (Q : Subgroup K)).map φ.toMonoidHom := by
    rw [← hφQ, rootCenter_map]
  have key := unitary_root_irreducible J hJ n hn hcard hfixed (W.map φ.toMonoidHom)
    (by rw [hZ]; exact Subgroup.map_mono hZW) (by rw [← hφQ]; exact Subgroup.map_mono hWQ)
    (fun d' hd' w' hw' => by
      rw [← hφD] at hd'
      obtain ⟨d, hd, rfl⟩ := hd'
      obtain ⟨w, hw, rfl⟩ := hw'
      exact ⟨d * w * d⁻¹, hinv d hd w hw, by simp⟩)
  rcases key with hk | hk
  · left
    rw [hZ] at hk
    exact Subgroup.map_injective φ.injective hk
  · right
    rw [← hφQ] at hk
    exact Subgroup.map_injective φ.injective hk

omit [Finite K] in
theorem BenderType.fixedPointFree_unitary {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K)
    {t : K} (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) {d : K}
    (hd : d ∈ cartan (Q : Subgroup K) t) (hd1 : d ≠ 1) {x : K} (hx : x ∈ (Q : Subgroup K))
    (hdx : d * x * d⁻¹ * x⁻¹ ∈ rootCenter (Q : Subgroup K)) : x ∈ rootCenter (Q : Subgroup K) := by
  obtain ⟨hn, -⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, φ, hφQ, hφD⟩ := h.exists_standard_iso_unitary Q ht htQ
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have hZ : rootCenter (unitaryCoverRoot J hJ) = (rootCenter (Q : Subgroup K)).map φ.toMonoidHom := by
    rw [← hφQ, rootCenter_map]
  have hdH : φ d ∈ unitaryCoverTorus J hJ := by
    rw [← hφD]
    exact ⟨d, hd, rfl⟩
  have hxR : φ x ∈ unitaryCoverRoot J hJ := by
    rw [← hφQ]
    exact ⟨x, hx, rfl⟩
  have hdx' : φ d * φ x * (φ d)⁻¹ * (φ x)⁻¹ ∈ rootCenter (unitaryCoverRoot J hJ) := by
    rw [hZ]
    exact ⟨_, hdx, by simp⟩
  have := unitary_torus_fixedPointFree J hJ n hcard hfixed hdH
    (fun h1 => hd1 (φ.injective (by rw [h1, map_one]))) hxR hdx'
  rw [hZ] at this
  obtain ⟨y, hy, hyx⟩ := this
  have : y = x := φ.injective hyx
  rwa [← this]

end BenderLevel

end CFSG.GH74.Uniqueness.Bender
