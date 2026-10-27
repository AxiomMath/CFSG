module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type*} [Field K]

section Tori

@[expose] def blockTorusParam (I : Finset (Fin n)) : Subgroup (Fin n → Kˣ) where
  carrier := {c | ∏ i, c i = 1 ∧ ∀ i ∈ I, ∀ j ∈ I, c i = c j}
  one_mem' := ⟨by simp, fun _ _ _ _ => rfl⟩
  mul_mem' := fun {c d} hc hd => ⟨by
      simp only [Pi.mul_apply, Finset.prod_mul_distrib, hc.1, hd.1, mul_one],
    fun i hi j hj => by simp only [Pi.mul_apply, hc.2 i hi j hj, hd.2 i hi j hj]⟩
  inv_mem' := fun {c} hc => ⟨by simp only [Pi.inv_apply, Finset.prod_inv_distrib, hc.1, inv_one],
    fun i hi j hj => by simp only [Pi.inv_apply, hc.2 i hi j hj]⟩

theorem mem_blockTorusParam {I : Finset (Fin n)} {c : Fin n → Kˣ} :
    c ∈ blockTorusParam I ↔ ∏ i, c i = 1 ∧ ∀ i ∈ I, ∀ j ∈ I, c i = c j :=
  Iff.rfl

theorem blockTorusParam_anti {I I' : Finset (Fin n)} (h : I ⊆ I') :
    blockTorusParam (K := K) I' ≤ blockTorusParam I :=
  fun _ hc => ⟨hc.1, fun i hi j hj => hc.2 i (h hi) j (h hj)⟩

theorem blockTorusParam_le_empty (I : Finset (Fin n)) :
    blockTorusParam (K := K) I ≤ blockTorusParam ∅ :=
  blockTorusParam_anti (Finset.empty_subset I)

@[expose] noncomputable def torusDiagSL :
    blockTorusParam (K := K) (∅ : Finset (Fin n)) →* SpecialLinearGroup (Fin n) K where
  toFun c := ⟨diagonal fun i => ((c.1 i : Kˣ) : K), by
    rw [det_diagonal, ← Units.coe_prod, c.2.1, Units.val_one]⟩
  map_one' := Subtype.ext (by
    change diagonal (fun i => (((1 : Fin n → Kˣ) i : Kˣ) : K)) = 1
    simp)
  map_mul' c d := Subtype.ext (by
    change diagonal (fun i => (((c.1 * d.1) i : Kˣ) : K)) =
      diagonal (fun i => ((c.1 i : Kˣ) : K)) * diagonal (fun i => ((d.1 i : Kˣ) : K))
    rw [diagonal_mul_diagonal]
    simp)

theorem coe_torusDiagSL (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) :
    ((torusDiagSL c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => ((c.1 i : Kˣ) : K) :=
  rfl

theorem torusDiagSL_apply_of_ne (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) {i j : Fin n}
    (hij : i ≠ j) :
    ((torusDiagSL c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
  rw [coe_torusDiagSL, diagonal_apply_ne _ hij]

theorem torusDiagSL_apply_self (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) (i : Fin n) :
    ((torusDiagSL c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
      ((c.1 i : Kˣ) : K) := by
  rw [coe_torusDiagSL, diagonal_apply_eq]

@[expose] noncomputable def blockTorus (I : Finset (Fin n)) :
    Subgroup (LinearFlag.projectiveSL n K) :=
  (((blockTorusParam I).subgroupOf (blockTorusParam ∅)).map torusDiagSL).map (LinearFlag.proj n K)

theorem mem_blockTorus {I : Finset (Fin n)} {x : LinearFlag.projectiveSL n K} :
    x ∈ blockTorus I ↔ ∃ c : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      c.1 ∈ blockTorusParam I ∧ LinearFlag.proj n K (torusDiagSL c) = x := by
  simp only [blockTorus, mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩

theorem proj_torusDiagSL_mem_blockTorus {I : Finset (Fin n)}
    {c : blockTorusParam (K := K) (∅ : Finset (Fin n))} (hc : c.1 ∈ blockTorusParam I) :
    LinearFlag.proj n K (torusDiagSL c) ∈ blockTorus I :=
  mem_blockTorus.2 ⟨c, hc, rfl⟩

theorem blockTorus_anti {I I' : Finset (Fin n)} (h : I ⊆ I') :
    blockTorus (K := K) I' ≤ blockTorus I := by
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  exact ⟨_, ⟨c, blockTorusParam_anti h hc, rfl⟩, rfl⟩

theorem torusDiagSL_mul_eq_mul_torusDiagSL {I : Finset (Fin n)}
    {c : blockTorusParam (K := K) (∅ : Finset (Fin n))} (hc : c.1 ∈ blockTorusParam I)
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ blockSpecialLinear I) :
    torusDiagSL c * A = A * torusDiagSL c := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_torusDiagSL]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : i ∈ I ∧ j ∈ I
  · rw [hc.2 i hij.1 j hij.2, mul_comm]
  · rw [(mem_blockSpecialLinear.mp hA) i j (not_and_or.mp hij)]
    by_cases h : i = j
    · subst h
      rw [one_apply_eq, mul_one, one_mul]
    · rw [one_apply_ne h, mul_zero, zero_mul]

theorem blockSL_le_centralizer_blockTorus (I : Finset (Fin n)) :
    blockSL (K := K) I ≤
      centralizer (blockTorus (K := K) I : Set (LinearFlag.projectiveSL n K)) := by
  rintro _ ⟨A, hA, rfl⟩
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨c, hc, rfl⟩ := mem_blockTorus.1 hx
  rw [← map_mul, ← map_mul, torusDiagSL_mul_eq_mul_torusDiagSL hc hA]

end Tori

section Levi

@[expose] def levTorusParam (a : Fin n) (c : Kˣ) : Fin n → Kˣ :=
  fun i => if i = a then c⁻¹ ^ (n - 1) else c

theorem coe_levTorusParam (a : Fin n) (c : Kˣ) :
    (fun i => ((levTorusParam a c i : Kˣ) : K)) = levDiag a c := by
  funext i
  simp only [levTorusParam, levDiag]
  split_ifs <;> rfl

theorem levTorusParam_mem (a : Fin n) (c : Kˣ) :
    levTorusParam a c ∈ blockTorusParam (K := K) ({a}ᶜ : Finset (Fin n)) := by
  refine ⟨?_, fun i hi j hj => ?_⟩
  · apply Units.ext
    rw [Units.coe_prod, Units.val_one]
    have := prod_levDiag (K := K) a c
    rwa [← coe_levTorusParam] at this
  · have hia : i ≠ a := by simpa using hi
    have hja : j ≠ a := by simpa using hj
    simp only [levTorusParam, hia, hja, ite_false]

theorem levTorusHom_eq_torusDiagSL (a : Fin n) (c : Kˣ) :
    levTorusHom a c = torusDiagSL (K := K)
      ⟨levTorusParam a c, blockTorusParam_le_empty _ (levTorusParam_mem a c)⟩ := by
  apply Subtype.ext
  rw [coe_torusDiagSL, coe_levTorusHom]
  change diagonal (levDiag a c) = diagonal (fun i => ((levTorusParam a c i : Kˣ) : K))
  rw [coe_levTorusParam]

theorem levTorus_le_blockTorus {a : Fin n} {I : Finset (Fin n)} (ha : a ∉ I) :
    levTorus (K := K) a ≤ blockTorus I := by
  rintro _ ⟨c, rfl⟩
  rw [MonoidHom.comp_apply, levTorusHom_eq_torusDiagSL]
  refine proj_torusDiagSL_mem_blockTorus (blockTorusParam_anti ?_ (levTorusParam_mem a c))
  intro i hi
  simpa using fun h : i = a => ha (h ▸ hi)

theorem eq_levTorusParam_of_mem {a : Fin n} {c : Fin n → Kˣ}
    (hc : c ∈ blockTorusParam ({a}ᶜ : Finset (Fin n))) {μ : Kˣ} (hμ : ∀ i, i ≠ a → c i = μ) :
    c = levTorusParam a μ := by
  funext i
  by_cases hi : i = a
  · subst hi
    simp only [levTorusParam, ite_true]
    have hprod := hc.1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      Finset.prod_congr rfl fun j hj => hμ j (Finset.ne_of_mem_erase hj), Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at hprod
    rw [inv_pow, eq_inv_iff_mul_eq_one, hprod]
  · simp only [levTorusParam, hi, ite_false]
    exact hμ i hi

theorem blockTorus_compl_singleton (a : Fin n) :
    blockTorus (K := K) ({a}ᶜ : Finset (Fin n)) = levTorus a := by
  refine le_antisymm ?_ (levTorus_le_blockTorus (by simp))
  intro x hx
  obtain ⟨c, hc, rfl⟩ := mem_blockTorus.1 hx
  obtain ⟨μ, hμ⟩ : ∃ μ : Kˣ, ∀ i, i ≠ a → c.1 i = μ := by
    by_cases h : ∃ b : Fin n, b ≠ a
    · obtain ⟨b, hb⟩ := h
      exact ⟨c.1 b, fun i hi => hc.2 i (by simpa using hi) b (by simpa using hb)⟩
    · push Not at h
      exact ⟨1, fun i hi => absurd (h i) hi⟩
  refine ⟨μ, ?_⟩
  rw [MonoidHom.comp_apply, levTorusHom_eq_torusDiagSL]
  congr 2
  exact Subtype.ext (eq_levTorusParam_of_mem hc hμ).symm

end Levi

section Root

@[expose] def rootTorusParam (a b : Fin n) (κ : Kˣ) : Fin n → Kˣ :=
  fun i => if i = a then κ else if i = b then κ⁻¹ else 1

theorem rootTorusParam_apply_left (a b : Fin n) (κ : Kˣ) : rootTorusParam a b κ a = κ := by
  simp [rootTorusParam]

theorem rootTorusParam_apply_right {a b : Fin n} (hab : a ≠ b) (κ : Kˣ) :
    rootTorusParam a b κ b = κ⁻¹ := by
  simp [rootTorusParam, hab.symm]

theorem rootTorusParam_apply_of_ne {a b i : Fin n} (hia : i ≠ a) (hib : i ≠ b) (κ : Kˣ) :
    rootTorusParam a b κ i = 1 := by
  simp [rootTorusParam, hia, hib]

theorem rootTorusParam_mem {a b : Fin n} (hab : a ≠ b) (κ : Kˣ) :
    rootTorusParam a b κ ∈ blockTorusParam (K := K) (∅ : Finset (Fin n)) := by
  refine ⟨?_, fun i hi => by simp at hi⟩
  rw [Finset.prod_eq_mul_of_mem a b (Finset.mem_univ _) (Finset.mem_univ _) hab]
  · simp [rootTorusParam, hab.symm]
  · intro c _ hc
    simp [rootTorusParam, hc.1, hc.2]

theorem rootTorusParam_mem_blockTorusParam {a b : Fin n} (hab : a ≠ b) {I : Finset (Fin n)}
    (ha : a ∉ I) (hb : b ∉ I) (κ : Kˣ) : rootTorusParam a b κ ∈ blockTorusParam (K := K) I :=
  ⟨(rootTorusParam_mem hab κ).1, fun i hi j hj => by
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    have hib : i ≠ b := fun h => hb (h ▸ hi)
    have hja : j ≠ a := fun h => ha (h ▸ hj)
    have hjb : j ≠ b := fun h => hb (h ▸ hj)
    rw [rootTorusParam_apply_of_ne hia hib, rootTorusParam_apply_of_ne hja hjb]⟩

@[expose] noncomputable def rootTorusHom {a b : Fin n} (hab : a ≠ b) :
    Kˣ →* blockTorusParam (K := K) (∅ : Finset (Fin n)) where
  toFun κ := ⟨rootTorusParam a b κ, rootTorusParam_mem hab κ⟩
  map_one' := Subtype.ext (funext fun i => by simp [rootTorusParam])
  map_mul' κ μ := Subtype.ext (funext fun i => by
    change rootTorusParam a b (κ * μ) i = rootTorusParam a b κ i * rootTorusParam a b μ i
    simp only [rootTorusParam]
    split_ifs <;> simp [mul_comm])

theorem coe_rootTorusHom {a b : Fin n} (hab : a ≠ b) (κ : Kˣ) :
    ((rootTorusHom (K := K) hab κ : blockTorusParam (K := K) (∅ : Finset (Fin n))) :
      Fin n → Kˣ) = rootTorusParam a b κ :=
  rfl

theorem coe_torusDiagSL_rootTorusHom {a b : Fin n} (hab : a ≠ b) (κ : Kˣ) :
    ((torusDiagSL (rootTorusHom (K := K) hab κ) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = diagonal fun i => ((rootTorusParam a b κ i : Kˣ) : K) :=
  rfl

@[expose] noncomputable def rootTorus {a b : Fin n} (hab : a ≠ b) :
    Subgroup (LinearFlag.projectiveSL n K) :=
  ((LinearFlag.proj n K).comp (torusDiagSL.comp (rootTorusHom hab))).range

theorem mem_rootTorus {a b : Fin n} (hab : a ≠ b) {x : LinearFlag.projectiveSL n K} :
    x ∈ rootTorus hab ↔ ∃ κ : Kˣ, LinearFlag.proj n K (torusDiagSL (rootTorusHom hab κ)) = x :=
  Iff.rfl

theorem proj_torusDiagSL_rootTorusHom_mem {a b : Fin n} (hab : a ≠ b) (κ : Kˣ) :
    LinearFlag.proj n K (torusDiagSL (rootTorusHom hab κ)) ∈ rootTorus hab :=
  ⟨κ, rfl⟩

theorem rootTorus_le_rootSL2 {a b : Fin n} (hab : a ≠ b) :
    rootTorus (K := K) hab ≤ rootSL2 a b := by
  rintro _ ⟨κ, rfl⟩
  refine ⟨_, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_blockSpecialLinear]
  intro i j hij
  change (diagonal fun i => ((rootTorusParam a b κ i : Kˣ) : K)) i j = _
  by_cases h : i = j
  · subst h
    have hi : i ≠ a ∧ i ≠ b := by
      rcases hij with h1 | h1 <;> simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using h1
    simp [rootTorusParam, hi.1, hi.2]
  · rw [diagonal_apply_ne _ h, one_apply_ne h]

theorem rootTorus_le_blockTorus {a b : Fin n} (hab : a ≠ b) {I : Finset (Fin n)} (ha : a ∉ I)
    (hb : b ∉ I) : rootTorus (K := K) hab ≤ blockTorus I := by
  rintro _ ⟨κ, rfl⟩
  exact proj_torusDiagSL_mem_blockTorus (rootTorusParam_mem_blockTorusParam hab ha hb κ)

theorem blockSL_compl_le_centralizer_rootTorus {a b : Fin n} (hab : a ≠ b) :
    blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)) ≤
      centralizer (rootTorus (K := K) hab : Set (LinearFlag.projectiveSL n K)) :=
  (blockSL_le_centralizer_blockTorus _).trans
    (centralizer_le (rootTorus_le_blockTorus hab (by simp) (by simp)))

end Root

inductive Neighbour (n : ℕ) where
  | root (a b : Fin n) (hab : a ≠ b)
  | levi (a : Fin n)

namespace Neighbour

variable (K) in
@[expose] noncomputable def torus : Neighbour n → Subgroup (LinearFlag.projectiveSL n K)
  | root _ _ hab => rootTorus hab
  | levi a => levTorus a

@[expose] def index : Neighbour n → Finset (Fin n)
  | root a b _ => {a, b}ᶜ
  | levi a => {a}ᶜ

theorem torus_root {a b : Fin n} (hab : a ≠ b) : (root a b hab).torus K = rootTorus hab :=
  rfl

theorem torus_levi (a : Fin n) : (levi a).torus K = levTorus a :=
  rfl

theorem index_root {a b : Fin n} (hab : a ≠ b) : (root a b hab).index = {a, b}ᶜ :=
  rfl

theorem index_levi (a : Fin n) : (levi a).index = {a}ᶜ :=
  rfl

theorem torus_le_blockTorus (N : Neighbour n) {I : Finset (Fin n)} (hI : I ⊆ N.index) :
    N.torus K ≤ blockTorus I := by
  cases N with
  | root a b hab =>
    refine rootTorus_le_blockTorus hab (fun h => ?_) (fun h => ?_)
    · have := hI h
      simp [index] at this
    · have := hI h
      simp [index] at this
  | levi a =>
    refine levTorus_le_blockTorus fun h => ?_
    have := hI h
    simp [index] at this

theorem blockSL_index_le_centralizer_torus (N : Neighbour n) :
    blockSL (K := K) N.index ≤
      centralizer (N.torus K : Set (LinearFlag.projectiveSL n K)) :=
  (blockSL_le_centralizer_blockTorus N.index).trans
    (centralizer_le (N.torus_le_blockTorus subset_rfl))

theorem torus_levi_eq_blockTorus (a : Fin n) :
    (levi a).torus K = blockTorus (levi a).index :=
  (blockTorus_compl_singleton a).symm

end Neighbour

section Separation

theorem exists_mem_blockTorusParam_ne {I : Finset (Fin n)} (hI : 2 ≤ Iᶜ.card) {κ : Kˣ}
    (hκ1 : κ ≠ 1) (hκ2 : κ * κ ≠ 1) {i j : Fin n} (hij : i ≠ j) (hIJ : i ∉ I ∨ j ∉ I) :
    ∃ c ∈ blockTorusParam (K := K) I, c i ≠ c j := by
  have hκinv : κ ≠ κ⁻¹ := fun h => hκ2 (by rw [← mul_inv_cancel κ]; exact congrArg (κ * ·) h)
  have hother : ∀ a : Fin n, ∃ a' : Fin n, a' ∉ I ∧ a' ≠ a := by
    intro a
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hsub : Iᶜ ⊆ {a} := fun x hx => Finset.mem_singleton.mpr (hcon x (Finset.mem_compl.mp hx))
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  by_cases hi : i ∈ I
  · have hj : j ∉ I := hIJ.resolve_left (not_not.mpr hi)
    obtain ⟨j', hj', hjj'⟩ := hother j
    refine ⟨rootTorusParam j j' κ, rootTorusParam_mem_blockTorusParam hjj'.symm hj hj' κ, ?_⟩
    have hij' : i ≠ j' := fun h => hj' (h ▸ hi)
    rw [rootTorusParam_apply_of_ne hij hij', rootTorusParam_apply_left]
    exact fun h => hκ1 h.symm
  · by_cases hj : j ∈ I
    · obtain ⟨i', hi', hii'⟩ := hother i
      refine ⟨rootTorusParam i i' κ, rootTorusParam_mem_blockTorusParam hii'.symm hi hi' κ, ?_⟩
      have hji' : j ≠ i' := fun h => hi' (h ▸ hj)
      rw [rootTorusParam_apply_left, rootTorusParam_apply_of_ne (Ne.symm hij) hji']
      exact hκ1
    · refine ⟨rootTorusParam i j κ, rootTorusParam_mem_blockTorusParam hij hi hj κ, ?_⟩
      rw [rootTorusParam_apply_left, rootTorusParam_apply_right hij]
      exact hκinv

theorem exists_mem_blockTorusParam_ne_of_notMem {I N : Finset (Fin n)} (hIN : I ⊆ N) {k : Fin n}
    (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1) {i j : Fin n} (hi : i ∈ N) (hj : j ∈ N) (hij : i ≠ j)
    (hIJ : i ∉ I ∨ j ∉ I) : ∃ c ∈ blockTorusParam (K := K) I, c i ≠ c j := by
  have hkI : k ∉ I := fun h => hk (hIN h)
  have hik : i ≠ k := fun h => hk (h ▸ hi)
  have hjk : j ≠ k := fun h => hk (h ▸ hj)
  by_cases hiI : i ∈ I
  · have hjI : j ∉ I := hIJ.resolve_left (not_not.mpr hiI)
    refine ⟨rootTorusParam j k κ, rootTorusParam_mem_blockTorusParam hjk hjI hkI κ, ?_⟩
    rw [rootTorusParam_apply_of_ne hij hik, rootTorusParam_apply_left]
    exact fun h => hκ h.symm
  · refine ⟨rootTorusParam i k κ, rootTorusParam_mem_blockTorusParam hik hiI hkI κ, ?_⟩
    rw [rootTorusParam_apply_left, rootTorusParam_apply_of_ne (Ne.symm hij) hjk]
    exact hκ

end Separation

section Lifts

theorem exists_eq_mul_of_proj_torusDiagSL_eq
    {c d : blockTorusParam (K := K) (∅ : Finset (Fin n))}
    (h : LinearFlag.proj n K (torusDiagSL c) = LinearFlag.proj n K (torusDiagSL d)) :
    ∃ s : Kˣ, ∀ i, d.1 i = s * c.1 i := by
  rw [LinearFlag.proj_eq_proj_iff] at h
  obtain ⟨s, -, hs⟩ := LinearFlag.mem_scalars.1 h
  refine ⟨s, fun i => ?_⟩
  have hi := congrFun (congrFun hs i) i
  rw [← map_inv, ← map_mul, torusDiagSL_apply_self, scalar_apply, diagonal_apply_eq] at hi
  have hi' : (c⁻¹ * d).1 i = s := Units.ext hi
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply, inv_mul_eq_iff_eq_mul] at hi'
  rw [hi', mul_comm]

@[expose] noncomputable def blockTorusLift {I : Finset (Fin n)} (d : blockTorus (K := K) I) :
    blockTorusParam (K := K) (∅ : Finset (Fin n)) :=
  (mem_blockTorus.1 d.2).choose

theorem blockTorusLift_mem {I : Finset (Fin n)} (d : blockTorus (K := K) I) :
    (blockTorusLift d).1 ∈ blockTorusParam I :=
  (mem_blockTorus.1 d.2).choose_spec.1

theorem proj_torusDiagSL_blockTorusLift {I : Finset (Fin n)} (d : blockTorus (K := K) I) :
    LinearFlag.proj n K (torusDiagSL (blockTorusLift d)) = d :=
  (mem_blockTorus.1 d.2).choose_spec.2

theorem exists_blockTorusLift_ne {I : Finset (Fin n)} {c : Fin n → Kˣ}
    (hc : c ∈ blockTorusParam I) {i j : Fin n} (hcij : c i ≠ c j) :
    ∃ d : blockTorus (K := K) I, (blockTorusLift d).1 i ≠ (blockTorusLift d).1 j := by
  set c₀ : blockTorusParam (K := K) (∅ : Finset (Fin n)) := ⟨c, blockTorusParam_le_empty I hc⟩
  set d : blockTorus (K := K) I := ⟨LinearFlag.proj n K (torusDiagSL c₀),
    proj_torusDiagSL_mem_blockTorus (c := c₀) hc⟩
  refine ⟨d, ?_⟩
  obtain ⟨s, hs⟩ := exists_eq_mul_of_proj_torusDiagSL_eq (c := c₀) (d := blockTorusLift d)
    (proj_torusDiagSL_blockTorusLift d).symm
  rw [hs i, hs j]
  exact fun h => hcij (mul_left_cancel h)

end Lifts

section Monomial

private theorem permMatrix_mul_diagonal' (σ : Equiv.Perm (Fin n)) (d : Fin n → K) :
    σ.permMatrix K * diagonal d = diagonal (d ∘ σ) * σ.permMatrix K := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.comp_apply]
  split_ifs with h
  · rw [h, one_mul, mul_one]
  · rw [zero_mul, mul_zero]

private theorem diagonal_mul_diagonal_comm (d e : Fin n → K) :
    diagonal d * diagonal e = diagonal e * diagonal d := by
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem exists_monomial (ρ : Equiv.Perm (Fin n)) :
    ∃ g : SpecialLinearGroup (Fin n) K,
      (∀ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) * diagonal d =
        diagonal (d ∘ ρ.symm) * (g : Matrix (Fin n) (Fin n) K)) ∧
      ∀ I : Finset (Fin n), blockComplProj (I.map ρ.toEmbedding) *
        (g : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) * blockComplProj I := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, fun d => ?_, fun I => ?_⟩
    · ext i
      exact i.elim0
    · ext i
      exact i.elim0
  · set τ : Equiv.Perm (Fin n) := ρ.symm
    set D : Matrix (Fin n) (Fin n) K :=
      diagonal (Function.update 1 (⟨0, hn⟩ : Fin n) ((Equiv.Perm.sign τ : ℤ) : K)) with hD
    have hdet : (τ.permMatrix K * D).det = 1 := by
      rw [det_mul, det_permutation, hD, det_diagonal,
        Finset.prod_update_of_mem (Finset.mem_univ _)]
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
    refine ⟨⟨τ.permMatrix K * D, hdet⟩, fun d => ?_, fun I => ?_⟩
    · change τ.permMatrix K * D * diagonal d = diagonal (d ∘ τ) * (τ.permMatrix K * D)
      rw [Matrix.mul_assoc, hD, diagonal_mul_diagonal_comm, ← Matrix.mul_assoc,
        permMatrix_mul_diagonal', Matrix.mul_assoc]
    · change blockComplProj (I.map ρ.toEmbedding) * (τ.permMatrix K * D) =
        τ.permMatrix K * D * blockComplProj I
      have h := blockComplProj_mul_permMatrix (K := K) τ I
      rw [show τ.symm = ρ from Equiv.symm_symm ρ] at h
      rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hD, blockComplProj, diagonal_mul_diagonal_comm,
        ← Matrix.mul_assoc]

theorem comp_symm_mem_blockTorusParam_iff (ρ : Equiv.Perm (Fin n)) {I : Finset (Fin n)}
    {c : Fin n → Kˣ} :
    c ∘ ρ.symm ∈ blockTorusParam (K := K) (I.map ρ.toEmbedding) ↔ c ∈ blockTorusParam I := by
  rw [mem_blockTorusParam, mem_blockTorusParam, Function.comp_def,
    Equiv.prod_comp ρ.symm (fun i => c i)]
  refine and_congr_right fun _ => ⟨fun h i hi j hj => ?_, fun h i hi j hj => ?_⟩
  · have := h (ρ i) (Finset.mem_map_equiv.2 (by simpa using hi))
      (ρ j) (Finset.mem_map_equiv.2 (by simpa using hj))
    simpa using this
  · exact h _ (Finset.mem_map_equiv.1 hi) _ (Finset.mem_map_equiv.1 hj)

@[expose] def permParam (ρ : Equiv.Perm (Fin n))
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) :
    blockTorusParam (K := K) (∅ : Finset (Fin n)) :=
  ⟨c.1 ∘ ρ.symm, by simpa using (comp_symm_mem_blockTorusParam_iff ρ (I := ∅) (c := c.1)).2 c.2⟩

theorem coe_permParam (ρ : Equiv.Perm (Fin n))
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) : (permParam ρ c).1 = c.1 ∘ ρ.symm :=
  rfl

theorem levTorusParam_comp_symm (ρ : Equiv.Perm (Fin n)) (a : Fin n) (c : Kˣ) :
    levTorusParam a c ∘ ρ.symm = levTorusParam (ρ a) c := by
  funext i
  simp only [Function.comp_apply, levTorusParam, Equiv.symm_apply_eq]

theorem rootTorusParam_comp_symm (ρ : Equiv.Perm (Fin n)) (a b : Fin n) (κ : Kˣ) :
    rootTorusParam a b κ ∘ ρ.symm = rootTorusParam (ρ a) (ρ b) κ := by
  funext i
  simp only [Function.comp_apply, rootTorusParam, Equiv.symm_apply_eq]

variable {ρ : Equiv.Perm (Fin n)} {g : SpecialLinearGroup (Fin n) K}

theorem conj_torusDiagSL_of_monomial
    (hg : ∀ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) * diagonal d =
      diagonal (d ∘ ρ.symm) * (g : Matrix (Fin n) (Fin n) K))
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) :
    g * torusDiagSL c * g⁻¹ = torusDiagSL (permParam ρ c) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_torusDiagSL, coe_torusDiagSL,
    hg]
  rfl

theorem conj_proj_torusDiagSL_of_monomial
    (hg : ∀ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) * diagonal d =
      diagonal (d ∘ ρ.symm) * (g : Matrix (Fin n) (Fin n) K))
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) :
    MulAut.conj (LinearFlag.proj n K g) (LinearFlag.proj n K (torusDiagSL c)) =
      LinearFlag.proj n K (torusDiagSL (permParam ρ c)) := by
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, conj_torusDiagSL_of_monomial hg]

theorem map_conj_blockTorus_of_monomial
    (hg : ∀ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) * diagonal d =
      diagonal (d ∘ ρ.symm) * (g : Matrix (Fin n) (Fin n) K))
    (I : Finset (Fin n)) :
    (blockTorus (K := K) I).map (MulAut.conj (LinearFlag.proj n K g)).toMonoidHom =
      blockTorus (I.map ρ.toEmbedding) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, rfl⟩ := mem_blockTorus.1 hx
    rw [MulEquiv.coe_toMonoidHom, conj_proj_torusDiagSL_of_monomial hg]
    exact proj_torusDiagSL_mem_blockTorus ((comp_symm_mem_blockTorusParam_iff ρ).2 hc)
  · intro x hx
    obtain ⟨c', hc', rfl⟩ := mem_blockTorus.1 hx
    have hc : c'.1 ∘ ρ ∈ blockTorusParam (K := K) I := by
      rw [← comp_symm_mem_blockTorusParam_iff ρ]
      simpa [Function.comp_def] using hc'
    set c : blockTorusParam (K := K) (∅ : Finset (Fin n)) :=
      ⟨c'.1 ∘ ρ, blockTorusParam_le_empty I hc⟩
    have hcc' : permParam ρ c = c' := Subtype.ext (by funext i; simp [permParam, c])
    refine ⟨LinearFlag.proj n K (torusDiagSL c), proj_torusDiagSL_mem_blockTorus hc, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, conj_proj_torusDiagSL_of_monomial hg, hcc']

theorem map_conj_rootTorus_of_monomial
    (hg : ∀ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) * diagonal d =
      diagonal (d ∘ ρ.symm) * (g : Matrix (Fin n) (Fin n) K))
    {a b : Fin n} (hab : a ≠ b) :
    (rootTorus (K := K) hab).map (MulAut.conj (LinearFlag.proj n K g)).toMonoidHom =
      rootTorus (ρ.injective.ne hab) := by
  rw [rootTorus, rootTorus, ← MonoidHom.range_comp]
  congr 1
  refine MonoidHom.ext fun κ => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [conj_proj_torusDiagSL_of_monomial hg]
  congr 2
  exact Subtype.ext (rootTorusParam_comp_symm ρ a b κ)

theorem map_conj_levTorus_of_monomial
    (hg : ∀ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) * diagonal d =
      diagonal (d ∘ ρ.symm) * (g : Matrix (Fin n) (Fin n) K))
    (a : Fin n) :
    (levTorus (K := K) a).map (MulAut.conj (LinearFlag.proj n K g)).toMonoidHom =
      levTorus (ρ a) := by
  rw [levTorus, levTorus, ← MonoidHom.range_comp]
  congr 1
  refine MonoidHom.ext fun c => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [levTorusHom_eq_torusDiagSL, levTorusHom_eq_torusDiagSL, conj_proj_torusDiagSL_of_monomial hg]
  congr 2
  exact Subtype.ext (levTorusParam_comp_symm ρ a c)

private theorem map_compl_toEmbedding (ρ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    sᶜ.map ρ.toEmbedding = (s.map ρ.toEmbedding)ᶜ := by
  ext x
  simp [Finset.mem_map_equiv]

namespace Neighbour

@[expose] def map (ρ : Equiv.Perm (Fin n)) : Neighbour n → Neighbour n
  | root a b hab => root (ρ a) (ρ b) (ρ.injective.ne hab)
  | levi a => levi (ρ a)

theorem index_map (ρ : Equiv.Perm (Fin n)) (N : Neighbour n) :
    (N.map ρ).index = N.index.map ρ.toEmbedding := by
  cases N with
  | root a b hab =>
    change ({ρ a, ρ b}ᶜ : Finset (Fin n)) = ({a, b}ᶜ : Finset (Fin n)).map ρ.toEmbedding
    rw [map_compl_toEmbedding, Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding]
  | levi a =>
    change ({ρ a}ᶜ : Finset (Fin n)) = ({a}ᶜ : Finset (Fin n)).map ρ.toEmbedding
    rw [map_compl_toEmbedding, Finset.map_singleton, Equiv.coe_toEmbedding]

theorem map_conj_torus_of_monomial
    (hg : ∀ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) * diagonal d =
      diagonal (d ∘ ρ.symm) * (g : Matrix (Fin n) (Fin n) K))
    (N : Neighbour n) :
    (N.torus K).map (MulAut.conj (LinearFlag.proj n K g)).toMonoidHom = (N.map ρ).torus K := by
  cases N with
  | root a b hab => exact map_conj_rootTorus_of_monomial hg hab
  | levi a => exact map_conj_levTorus_of_monomial hg a

end Neighbour

theorem exists_conj_blockTorus (ρ : Equiv.Perm (Fin n)) :
    ∃ g : LinearFlag.projectiveSL n K,
      (∀ I : Finset (Fin n),
        (blockTorus I).map (MulAut.conj g).toMonoidHom = blockTorus (I.map ρ.toEmbedding) ∧
        (blockSL I).map (MulAut.conj g).toMonoidHom = blockSL (I.map ρ.toEmbedding)) ∧
      ∀ N : Neighbour n, (N.torus K).map (MulAut.conj g).toMonoidHom = (N.map ρ).torus K := by
  obtain ⟨g, hgd, hgP⟩ := exists_monomial (K := K) ρ
  exact ⟨LinearFlag.proj n K g, fun I => ⟨map_conj_blockTorus_of_monomial hgd I,
    map_conj_blockSL_of_mul_eq g (hgP I)⟩, Neighbour.map_conj_torus_of_monomial hgd⟩

end Monomial

end CFSG.SeitzReduction.LinearPilot
