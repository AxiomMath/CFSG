module

public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus
public import CFSG.LieType.Chevalley.EvenRootCommutatorG2
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.LieType.Chevalley.G2FieldFour

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ExceptionalCover
open scoped commutatorElement

@[expose] def rootA : Fin Tag.G2.rank → ℤ := ![1, 0]

@[expose] def rootR : Fin Tag.G2.rank → ℤ := ![0, 1]

@[expose] def rootU : Fin Tag.G2.rank → ℤ := ![1, 1]

@[expose] def rootV : Fin Tag.G2.rank → ℤ := ![1, 2]

@[expose] def rootB : Fin Tag.G2.rank → ℤ := ![1, 3]

@[expose] def rootC : Fin Tag.G2.rank → ℤ := ![2, 3]

@[expose] def posRoots : Finset (Fin Tag.G2.rank → ℤ) :=
  {rootA, rootR, rootU, rootV, rootB, rootC}

theorem filter_height_pos_rootFinset :
    (rootFinset .G2).filter (fun β => 0 < height β) = posRoots := by
  decide +kernel

theorem mem_posRoots {d : Fin Tag.G2.rank → ℤ} :
    d ∈ posRoots ↔ IsRoot .G2 d ∧ 0 < height d := by
  rw [← filter_height_pos_rootFinset, Finset.mem_filter, mem_rootFinset]

theorem ncard_posRoots
    : {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α}.ncard = 6 := by
  have h : {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α} = (posRoots : Set _) := by
    ext d
    rw [Set.mem_ofPred_eq, Finset.mem_coe, mem_posRoots]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem rootA_mem : rootA ∈ posRoots := by decide +kernel
theorem rootR_mem : rootR ∈ posRoots := by decide +kernel
theorem rootU_mem : rootU ∈ posRoots := by decide +kernel
theorem rootV_mem : rootV ∈ posRoots := by decide +kernel
theorem rootB_mem : rootB ∈ posRoots := by decide +kernel
theorem rootC_mem : rootC ∈ posRoots := by decide +kernel

variable {K : Type} [Field K]

@[expose] def rootX
    (d : Fin Tag.G2.rank → ℤ) (c : K) : adjointGroup Tag.G2 K :=
  ⟨pinnedX .G2 K d c, pinnedX_mem_adjointGroup d c⟩

@[expose] def torusX
    (t : Fin Tag.G2.rank → Kˣ) : adjointGroup Tag.G2 K :=
  ⟨torusVec .G2 K t, torusVec_mem_adjointGroup t⟩

theorem coe_rootX
    (d : Fin Tag.G2.rank → ℤ) (c : K) :
    (rootX d c : ModGL Tag.G2 K) = pinnedX .G2 K d c :=
  rfl

theorem rootX_add
    (d : Fin Tag.G2.rank → ℤ) (c c' : K) :
    rootX d (c + c') = rootX d c * rootX d c' :=
  Subtype.ext (pinnedX_add .G2 K d c c')

theorem rootX_zero
    (d : Fin Tag.G2.rank → ℤ) : rootX d (0 : K) = 1 :=
  Subtype.ext (pinnedX_zero .G2 K d)

theorem rootX_injective
    (d : Fin Tag.G2.rank → ℤ) : Function.Injective (rootX (K := K) d) :=
  fun _ _ h => pinnedX_injective .G2 K d (congrArg Subtype.val h)

theorem torusX_conj_rootX
    {d : Fin Tag.G2.rank → ℤ} (hd : IsRoot .G2 d)
    (t : Fin Tag.G2.rank → Kˣ) (c : K) :
    torusX t * rootX d c * (torusX t)⁻¹ = rootX d ((rootChar K d t : K) * c) :=
  Subtype.ext (torusVec_conj_pinnedX hd t c)

theorem torusX_mul_comm
    (t t' : Fin Tag.G2.rank → Kˣ) :
    torusX (K := K) t * torusX t' = torusX t' * torusX t :=
  Subtype.ext (by
    change torusVec .G2 K t * torusVec .G2 K t' = torusVec .G2 K t' * torusVec .G2 K t
    rw [← map_mul, ← map_mul, mul_comm])

@[expose] def torusPow (ω : Kˣ) (e : Fin Tag.G2.rank → ℤ) : Fin Tag.G2.rank → Kˣ :=
  fun k => ω ^ e k

theorem zpow_sum_eq_prod {G : Type*} [CommGroup G] (g : G) {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) : g ^ (∑ i ∈ s, f i) = ∏ i ∈ s, g ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem rootChar_torusPow (ω : Kˣ) (d e : Fin Tag.G2.rank → ℤ) :
    rootChar K d (torusPow ω e) = ω ^ (∑ k, e k * cartanCoord d k) := by
  rw [rootChar_apply, zpow_sum_eq_prod]
  simp only [torusPow, zpow_mul]

variable {ω : Kˣ}

theorem rootChar_torusPow_eq (hω : orderOf ω = 3) {d d' e : Fin Tag.G2.rank → ℤ}
    (h : (∑ k, e k * cartanCoord d k) ≡ ∑ k, e k * cartanCoord d' k [ZMOD 3]) :
    rootChar K d (torusPow ω e) = rootChar K d' (torusPow ω e) := by
  rw [rootChar_torusPow, rootChar_torusPow, zpow_eq_zpow_iff_modEq, hω]
  exact_mod_cast h

theorem rootChar_torusPow_eq_one (hω : orderOf ω = 3) {d e : Fin Tag.G2.rank → ℤ}
    (h : (3 : ℤ) ∣ ∑ k, e k * cartanCoord d k) : rootChar K d (torusPow ω e) = 1 := by
  rw [rootChar_torusPow, ← orderOf_dvd_iff_zpow_eq_one, hω]
  exact_mod_cast h

theorem rootChar_torusPow_ne_one (hω : orderOf ω = 3) {d e : Fin Tag.G2.rank → ℤ}
    (h : ¬ (3 : ℤ) ∣ ∑ k, e k * cartanCoord d k) : (rootChar K d (torusPow ω e) : K) ≠ 1 := by
  rw [ne_eq, Units.val_eq_one, rootChar_torusPow, ← orderOf_dvd_iff_zpow_eq_one, hω]
  exact_mod_cast h

theorem rootChar_torusPow_eq_sq (hω : orderOf ω = 3) {d d' e : Fin Tag.G2.rank → ℤ}
    (h : (∑ k, e k * cartanCoord d' k) ≡ 2 * ∑ k, e k * cartanCoord d k [ZMOD 3]) :
    (rootChar K d' (torusPow ω e) : K) = (rootChar K d (torusPow ω e) : K) ^ 2 := by
  rw [← Units.val_pow_eq_pow_val]
  congr 1
  rw [rootChar_torusPow, rootChar_torusPow, ← zpow_natCast, ← zpow_mul, zpow_eq_zpow_iff_modEq,
    hω]
  push_cast
  rw [mul_comm]
  exact h

theorem exists_rootChar_ne_one (hω : orderOf ω = 3) {d : Fin Tag.G2.rank → ℤ}
    (hd : d ∈ posRoots) : ∃ t : Fin Tag.G2.rank → Kˣ, (rootChar K d t : K) ≠ 1 := by
  have key : ∀ d ∈ posRoots,
      ¬ (3 : ℤ) ∣ ∑ k, (![1, 0] : Fin Tag.G2.rank → ℤ) k * cartanCoord d k ∨
        ¬ (3 : ℤ) ∣ ∑ k, (![0, 1] : Fin Tag.G2.rank → ℤ) k * cartanCoord d k := by
    decide +kernel
  rcases key d hd with h | h
  · exact ⟨_, rootChar_torusPow_ne_one hω h⟩
  · exact ⟨_, rootChar_torusPow_ne_one hω h⟩

section Table

variable [CharP K 2] (x y : K)

theorem commutator_rootX_ar :
    ⁅rootX rootA x, rootX rootR y⁆ =
      rootX rootU (x * y) * rootX rootV (x * y ^ 2) * rootX rootB (x * y ^ 3) *
        rootX rootC (x ^ 2 * y ^ 3) :=
  Subtype.ext (g2_even_root_commutator_table x y).1

theorem commutator_rootX_ru :
    ⁅rootX rootR x, rootX rootU y⁆ = rootX rootC (x * y ^ 2) * rootX rootB (x ^ 2 * y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.1

theorem commutator_rootX_rv
    : ⁅rootX rootR x, rootX rootV y⁆ = rootX rootB (x * y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.1

theorem commutator_rootX_ab
    : ⁅rootX rootA x, rootX rootB y⁆ = rootX rootC (x * y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.1

theorem commutator_rootX_uv
    : ⁅rootX rootU x, rootX rootV y⁆ = rootX rootC (x * y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.1

theorem commute_rootX_au
    : Commute (rootX rootA x) (rootX rootU y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.1

theorem commute_rootX_av
    : Commute (rootX rootA x) (rootX rootV y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.1

theorem commute_rootX_ac
    : Commute (rootX rootA x) (rootX rootC y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.1

theorem commute_rootX_rb
    : Commute (rootX rootR x) (rootX rootB y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.1

theorem commute_rootX_rc
    : Commute (rootX rootR x) (rootX rootC y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.1

theorem commute_rootX_ub
    : Commute (rootX rootU x) (rootX rootB y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.1

theorem commute_rootX_uc
    : Commute (rootX rootU x) (rootX rootC y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem commute_rootX_vb
    : Commute (rootX rootV x) (rootX rootB y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem commute_rootX_vc
    : Commute (rootX rootV x) (rootX rootC y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem commute_rootX_bc
    : Commute (rootX rootB x) (rootX rootC y) :=
  Subtype.ext (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Table

end CFSG.LieType.Chevalley.G2FieldFour
