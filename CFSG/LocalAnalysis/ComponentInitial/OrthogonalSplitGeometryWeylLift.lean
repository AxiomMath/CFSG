module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryMonomial
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryWeyl

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix SymplecticTorusWeyl CFSG.LieType.Universal.SpecialLinear CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type*} [Field K]

section Reflection

variable {a b : Fin r ⊕ Fin r}

theorem coordWt_swap_mul_swap (h : coordIdx a ≠ coordIdx b) (x : Fin r ⊕ Fin r) :
    coordWt ((Equiv.swap a b * Equiv.swap a.swap b.swap) x) =
      coordWt x - (coordWt x ⬝ᵥ (coordWt a - coordWt b)) • (coordWt a - coordWt b) := by
  have hab := ne_of_coordIdx_ne h
  have hab' := ne_swap_of_coordIdx_ne h
  have hba' := ne_swap_of_coordIdx_ne (Ne.symm h)
  rw [Equiv.Perm.mul_apply, dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct]
  by_cases hxa : x = a
  · subst x
    rw [Equiv.swap_apply_of_ne_of_ne (swap_ne_self a).symm hab', Equiv.swap_apply_left,
      ite_eq_left rfl, ite_eq_right hab, ite_eq_right hab']
    module
  by_cases hxb : x = b
  · subst x
    rw [Equiv.swap_apply_of_ne_of_ne hba' (swap_ne_self b).symm, Equiv.swap_apply_right,
      ite_eq_right (Ne.symm hab), ite_eq_right hba', ite_eq_left rfl]
    module
  by_cases hxa' : x = a.swap
  · subst x
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hab') (swap_ne_self b),
      ite_eq_right (swap_ne_self a), ite_eq_left rfl, ite_eq_right (Ne.symm hba'),
      ite_eq_right (swap_ne_swap_of_ne hab), coordWt_swap, coordWt_swap]
    module
  by_cases hxb' : x = b.swap
  · subst x
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (swap_ne_self a) (Ne.symm hba'),
      ite_eq_right (Ne.symm hab'), ite_eq_right (swap_ne_swap_of_ne (Ne.symm hab)),
      ite_eq_right (swap_ne_self b), ite_eq_left rfl, coordWt_swap, coordWt_swap]
    module
  · rw [Equiv.swap_apply_of_ne_of_ne hxa' hxb', Equiv.swap_apply_of_ne_of_ne hxa hxb,
      ite_eq_right hxa, ite_eq_right hxa', ite_eq_right hxb, ite_eq_right hxb']
    simp

theorem swap_mul_swap_mem_signedPermGroup (h : coordIdx a ≠ coordIdx b) :
    Equiv.swap a b * Equiv.swap a.swap b.swap ∈ signedPermGroup r := by
  intro x
  apply coordWt_injective
  rw [coordWt_swap_mul_swap h, coordWt_swap, coordWt_swap, coordWt_swap_mul_swap h, neg_dotProduct,
    neg_smul, sub_neg_eq_add, neg_sub]
  abel

theorem rpBlock_w (h : coordIdx a ≠ coordIdx b) :
    rpBlock a b !![0, 1; -1, (0 : K)] =
      signedPerm (Equiv.swap a b * Equiv.swap a.swap b.swap)
        fun s => if s = a ∨ s = a.swap then -1 else 1 := by
  have hadj : (adjugate !![(0 : K), 1; -1, 0])ᵀ = !![0, 1; -1, 0] := by
    rw [adjugate_fin_two_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [rpBlock, hadj, pairMat_w_inv (ne_of_coordIdx_ne h),
    pairMat_w_inv (swap_ne_swap_of_coordIdx_ne h), signedPerm_mul_signedPerm]
  congr 1
  funext s
  have hab' := ne_swap_of_coordIdx_ne h
  by_cases hsa : s = a
  · subst s
    rw [Equiv.swap_apply_of_ne_of_ne (swap_ne_self a).symm hab', ite_eq_left rfl,
      ite_eq_right (swap_ne_self a).symm, ite_eq_left (Or.inl rfl), mul_one]
  by_cases hsa' : s = a.swap
  · subst s
    rw [Equiv.swap_apply_left, ite_eq_right (Ne.symm hab'), ite_eq_left rfl,
      ite_eq_left (Or.inr rfl), one_mul]
  rw [ite_eq_right hsa', ite_eq_right (not_or.2 ⟨hsa, hsa'⟩), mul_one, ite_eq_right]
  intro he
  by_cases hsb' : s = b.swap
  · subst s
    rw [Equiv.swap_apply_right] at he
    exact swap_ne_self a he
  · rw [Equiv.swap_apply_of_ne_of_ne hsa' hsb'] at he
    exact hsa he

end Reflection

section SimpleRefl

theorem eps_dotProduct_eps (i j : Fin r) : eps r i ⬝ᵥ eps r j = if i = j then 1 else 0 := by
  have := coordWt_dotProduct (Sum.inl i : Fin r ⊕ Fin r) (Sum.inl j)
  simpa using this

theorem simpleRefl_eps_eq (hr : 2 ≤ r) (i j : Fin r) :
    simpleRefl r i (eps r j) = eps r j - (eps r j ⬝ᵥ simpleRoot r i) • simpleRoot r i := by
  by_cases h : i.val + 1 < r
  · have hii : i ≠ ⟨i.val + 1, h⟩ := by simp [Fin.ext_iff]
    rw [simpleRefl_of_lt h, signedPermAut_eps, simpleRoot_of_lt h, Pi.one_apply, Units.val_one,
      one_smul, one_smul, neg_one_smul, dotProduct_add, dotProduct_neg, eps_dotProduct_eps,
      eps_dotProduct_eps]
    by_cases hji : j = i
    · subst j
      rw [Equiv.swap_apply_left, ite_eq_left rfl, ite_eq_right hii]
      module
    by_cases hji' : j = ⟨i.val + 1, h⟩
    · subst j
      rw [Equiv.swap_apply_right, ite_eq_right (Ne.symm hii), ite_eq_left rfl]
      module
    · rw [Equiv.swap_apply_of_ne_of_ne hji hji', ite_eq_right hji, ite_eq_right hji']
      simp
  · have hi : i.val = r - 1 := by have := i.isLt; omega
    have hpi : (⟨r - 2, by omega⟩ : Fin r) ≠ i := by
      rw [Ne, Fin.ext_iff]
      simp only
      omega
    rw [simpleRefl_of_not_lt h, signedPermAut_eps, simpleRoot_of_not_lt h, one_smul, one_smul,
      dotProduct_add, eps_dotProduct_eps, eps_dotProduct_eps]
    by_cases hjp : j = ⟨r - 2, by omega⟩
    · subst j
      rw [Equiv.swap_apply_left, ite_eq_left rfl, ite_eq_right hpi]
      have hs : (lastSigns r i ⟨r - 2, by omega⟩ : ℤ) = -1 := by
        simp [lastSigns]
        omega
      rw [hs]
      module
    by_cases hji : j = i
    · subst j
      rw [Equiv.swap_apply_right, ite_eq_right (Ne.symm hpi), ite_eq_left rfl]
      have hs : (lastSigns r i i : ℤ) = -1 := by simp [lastSigns]
      rw [hs]
      module
    · have hs : (lastSigns r i j : ℤ) = 1 := by
        have hj2 : j.val + 2 ≠ r := fun h' => hjp (Fin.ext (by simp only; omega))
        simp [lastSigns, hji, hj2]
      rw [Equiv.swap_apply_of_ne_of_ne hjp hji, ite_eq_right hjp, ite_eq_right hji, hs]
      simp

end SimpleRefl

section Monomial

theorem autMat_weylElt_eq_rpBlock {i : Fin r} {a b : Fin r ⊕ Fin r}
    (hab : coordIdx a ≠ coordIdx b)
    (h1 : ∀ t : K, autMat (rootElt r K (simpleRoot r i) t) = rpBlock a b !![1, t; 0, 1])
    (h2 : ∀ t : K, autMat (rootElt r K (-simpleRoot r i) t) = rpBlock a b !![1, 0; t, 1]) :
    autMat (weylElt r K i) = rpBlock a b !![0, 1; -1, 0] := by
  have := autMat_rootN hab h1 h2 (one_ne_zero (α := K))
  rwa [rootN, inv_one, ← weylElt] at this

theorem units_ite_swap (a : Fin r ⊕ Fin r) (c : Fin r ⊕ Fin r) :
    (fun s => if s = a ∨ s = a.swap then (-1 : Kˣ) else 1) c.swap =
      ((fun s => if s = a ∨ s = a.swap then (-1 : Kˣ) else 1) c)⁻¹ := by
  simp only
  by_cases hc : c = a ∨ c = a.swap
  · have : c.swap = a ∨ c.swap = a.swap := by
      rcases hc with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (Sum.swap_swap _)
    rw [ite_eq_left this, ite_eq_left hc, inv_neg, inv_one]
  · have : ¬(c.swap = a ∨ c.swap = a.swap) := by
      rintro (h | h)
      · exact hc (Or.inr (by rw [← h, Sum.swap_swap]))
      · exact hc (Or.inl (by simpa using congrArg Sum.swap h))
    rw [ite_eq_right this, ite_eq_right hc, inv_one]

theorem exists_weylElt_autMat (hr : 2 ≤ r) (i : Fin r) :
    ∃ a b : Fin r ⊕ Fin r, coordIdx a ≠ coordIdx b ∧ coordWt a - coordWt b = simpleRoot r i ∧
      autMat (weylElt r K i) = signedPerm (Equiv.swap a b * Equiv.swap a.swap b.swap)
        fun s => (((if s = a ∨ s = a.swap then (-1 : Kˣ) else 1 : Kˣ)) : K) := by
  obtain ⟨a, b, hab, hw, h1, h2⟩ := exists_autMat_rootElt_eq_rpBlock (K := K)
    (posRoots_subset_roots (simpleRoot_mem_posRoots hr i))
  refine ⟨a, b, hab, hw, ?_⟩
  rw [autMat_weylElt_eq_rpBlock hab h1 h2, rpBlock_w hab]
  congr 1
  funext s
  split_ifs <;> simp

theorem weylElt_mem_monoAut (hr : 2 ≤ r) (i : Fin r) : weylElt r K i ∈ monoAut r K := by
  obtain ⟨a, b, hab, -, h⟩ := exists_weylElt_autMat (K := K) hr i
  exact ⟨_, swap_mul_swap_mem_signedPermGroup hab, _, units_ite_swap a, h⟩

theorem torusWeyl_le_monoAut (hr : 2 ≤ r) : torusWeyl r K ≤ monoAut r K := by
  rw [torusWeyl, Subgroup.closure_le]
  rintro _ (⟨-, d, rfl⟩ | ⟨i, rfl⟩)
  · exact torusElt_mem_monoAut d
  · exact weylElt_mem_monoAut hr i

end Monomial

section Nu

variable (hr : 2 ≤ r)
include hr

theorem monoPermFun_weylElt (i : Fin r) {a b : Fin r ⊕ Fin r} {μ : Fin r ⊕ Fin r → K}
    (h : autMat (weylElt r K i) = signedPerm (Equiv.swap a b * Equiv.swap a.swap b.swap) μ) :
    monoPermFun (⟨weylElt r K i, weylElt_mem_monoAut hr i⟩ : monoAut r K) =
      Equiv.swap a b * Equiv.swap a.swap b.swap :=
  monoPermFun_eq h

theorem nuMono_weylElt (i : Fin r) :
    nuMono r K ⟨weylElt r K i, weylElt_mem_monoAut hr i⟩ = simpleRefl r i := by
  obtain ⟨a, b, hab, hw, h⟩ := exists_weylElt_autMat (K := K) hr i
  refine LinearEquiv.toLinearMap_injective (linearMap_ext_eps fun j => ?_)
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, ← coordWt_inl, nuMono_coordWt,
    monoPermFun_weylElt hr i h, coordWt_swap_mul_swap hab, hw, coordWt_inl, simpleRefl_eps_eq hr]

omit hr in
theorem nuMono_torusElt (d : Fin r → Kˣ) :
    nuMono r K ⟨torusElt r K d, torusElt_mem_monoAut d⟩ = 1 := by
  have h1 : monoPermFun (⟨torusElt r K d, torusElt_mem_monoAut d⟩ : monoAut r K) = 1 :=
    monoPermFun_eq (μ := fun x => ((Sum.elim d d⁻¹ x : Kˣ) : K))
      (by rw [autMat_torusElt, signedPerm_one])
  have h2 : monoPerm r K ⟨torusElt r K d, torusElt_mem_monoAut d⟩ = 1 := Subtype.ext h1
  rw [nuMono, MonoidHom.comp_apply, h2, map_one]

theorem nuMono_mem_weylGroup {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ torusWeyl r K) :
    nuMono r K ⟨g, torusWeyl_le_monoAut hr hg⟩ ∈ weylGroup r := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨-, d, rfl⟩ | ⟨i, rfl⟩
    · rw [nuMono_torusElt d]
      exact one_mem _
    · rw [nuMono_weylElt hr i]
      exact simpleRefl_mem hr i
  | one =>
    have : (⟨1, torusWeyl_le_monoAut hr (one_mem _)⟩ : monoAut r K) = 1 := rfl
    rw [this, map_one]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    have : (⟨x * y, torusWeyl_le_monoAut hr (mul_mem hx hy)⟩ : monoAut r K) =
        ⟨x, torusWeyl_le_monoAut hr hx⟩ * ⟨y, torusWeyl_le_monoAut hr hy⟩ := rfl
    rw [this, map_mul]
    exact mul_mem ihx ihy
  | inv x hx ihx =>
    have : (⟨x⁻¹, torusWeyl_le_monoAut hr (inv_mem hx)⟩ : monoAut r K) =
        (⟨x, torusWeyl_le_monoAut hr hx⟩)⁻¹ := rfl
    rw [this, map_inv]
    exact inv_mem ihx

variable (r K) in
@[expose] noncomputable def torusWeylNu : torusWeyl r K →* weylGroup r :=
  ((nuMono r K).comp (Subgroup.inclusion (torusWeyl_le_monoAut hr))).codRestrict (weylGroup r)
    fun n => nuMono_mem_weylGroup hr n.2

theorem coe_torusWeylNu (n : torusWeyl r K) :
    ((torusWeylNu r K hr n : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) =
      nuMono r K ⟨n, torusWeyl_le_monoAut hr n.2⟩ :=
  rfl

theorem apply_single_torusWeylNu (n : torusWeyl r K) (c : Fin r ⊕ Fin r) :
    ∃ (μ : Kˣ) (c' : Fin r ⊕ Fin r),
      (n : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single c 1) =
          (μ : K) • Pi.single c' 1 ∧
        coordWt c' = ((torusWeylNu r K hr n : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] _) (coordWt c) := by
  obtain ⟨μ, -, hμ⟩ := exists_autMat_eq_monoPermFun
    (⟨n, torusWeyl_le_monoAut hr n.2⟩ : monoAut r K)
  exact ⟨μ c, _, apply_single_of_autMat hμ c, by rw [coe_torusWeylNu, nuMono_coordWt]⟩

theorem torusWeylNu_weylElt (i : Fin r) :
    torusWeylNu r K hr ⟨weylElt r K i, weylElt_mem_torusWeyl i⟩ =
      ⟨simpleRefl r i, simpleRefl_mem hr i⟩ :=
  Subtype.ext (nuMono_weylElt hr i)

theorem torusWeylNu_surjective (hr3 : 3 ≤ r) : Function.Surjective (torusWeylNu r K hr) := by
  have key : ∀ w ∈ Subgroup.closure (Set.range (simpleRefl r)), ∃ n : torusWeyl r K,
      ((torusWeylNu r K hr n : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨_, congrArg Subtype.val (torusWeylNu_weylElt hr i)⟩
    | one => exact ⟨1, by rw [map_one]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨n, hn⟩ := ihx
      obtain ⟨m, hm⟩ := ihy
      exact ⟨n * m, by rw [map_mul, Subgroup.coe_mul, hn, hm]⟩
    | inv x _ ihx =>
      obtain ⟨n, hn⟩ := ihx
      exact ⟨n⁻¹, by rw [map_inv, Subgroup.coe_inv, hn]⟩
  rintro ⟨w, hw⟩
  obtain ⟨n, hn⟩ := key w (by rwa [closure_simpleRefl hr3])
  exact ⟨n, Subtype.ext hn⟩

theorem torusWeylNu_ker : (torusWeylNu r K hr).ker = (torus r K).subgroupOf (torusWeyl r K) := by
  ext ⟨n, hn⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    have h2 : nuMono r K ⟨n, torusWeyl_le_monoAut hr hn⟩ = 1 := congrArg Subtype.val h1
    rw [nuMono, MonoidHom.comp_apply, ← map_one wtHom] at h2
    have h3 := congrArg Subtype.val (wtHom_injective h2)
    rw [coe_monoPerm, OneMemClass.coe_one] at h3
    obtain ⟨μ, hμ, hmat⟩ := exists_autMat_eq_monoPermFun
      (⟨n, torusWeyl_le_monoAut hr hn⟩ : monoAut r K)
    rw [h3, signedPerm_one] at hmat
    refine ⟨torusWeyl_le hn, fun i => μ (Sum.inl i), autMat_injective ?_⟩
    rw [autMat_torusElt]
    change _ = autMat n
    rw [hmat]
    congr 1
    funext x
    rcases x with i | i
    · rfl
    · change (((μ (Sum.inl i))⁻¹ : Kˣ) : K) = μ (Sum.inr i)
      rw [← hμ (Sum.inl i)]
      rfl
  · rintro ⟨-, d, rfl⟩
    exact Subtype.ext (nuMono_torusElt d)

theorem map_conj_rootSubgroup_torusWeyl (n : torusWeyl r K) {α : Fin r → ℤ} (hα : α ∈ roots r) :
    (rootSubgroup r K α).map
        (MulAut.conj (n : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))).toMonoidHom =
      rootSubgroup r K (((torusWeylNu r K hr n : weylGroup r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) α) :=
  map_conj_rootSubgroup (⟨n, torusWeyl_le_monoAut hr n.2⟩ : monoAut r K) hα

end Nu

theorem image_eq_self_of_mapsTo {α : Type*} {σ : Equiv.Perm α} (hσ : σ * σ = 1) {S : Set α}
    (h : ∀ c ∈ S, σ c ∈ S) : σ '' S = S := by
  refine Set.Subset.antisymm (Set.image_subset_iff.2 h) fun c hc => ⟨σ c, h c hc, ?_⟩
  rw [← Equiv.Perm.mul_apply, hσ, Equiv.Perm.one_apply]

theorem image_ne_self_of_mem {α : Type*} {σ : Equiv.Perm α} {S : Set α} {c : α} (hc : c ∈ S)
    (h : σ c ∉ S) : σ '' S ≠ S :=
  fun he => h (he ▸ ⟨c, hc, rfl⟩)

theorem mem_Xstar_coords (hr0 : 0 < r) {c : Fin r ⊕ Fin r} :
    c ∈ (Sum.inl '' {j : Fin r | (j : ℕ) < r - 1} ∪ {Sum.inr ⟨r - 1, by omega⟩} :
      Set (Fin r ⊕ Fin r)) ↔
      (∃ k : Fin r, k.val < r - 1 ∧ c = Sum.inl k) ∨ c = Sum.inr ⟨r - 1, by omega⟩ := by
  simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨k, hk, rfl⟩ | h)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr h
  · rintro (⟨k, hk, rfl⟩ | h)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr h

section Action

variable (hr : 2 ≤ r)
include hr

noncomputable abbrev weylPerm (i : Fin r) : Equiv.Perm (Fin r ⊕ Fin r) :=
  monoPermFun (⟨weylElt r K i, weylElt_mem_monoAut hr i⟩ : monoAut r K)

theorem coordWt_weylPerm (i : Fin r) (c : Fin r ⊕ Fin r) :
    coordWt (weylPerm (K := K) hr i c) = simpleRefl r i (coordWt c) := by
  rw [← nuMono_coordWt, nuMono_weylElt hr]

theorem weylPerm_mul_self (i : Fin r) : weylPerm (K := K) hr i * weylPerm (K := K) hr i = 1 := by
  refine Equiv.ext fun c => coordWt_injective ?_
  rw [Equiv.Perm.mul_apply, coordWt_weylPerm, coordWt_weylPerm, ← LinearEquiv.mul_apply,
    simpleRefl_mul_self hr]
  rfl

theorem weylPerm_swap (i : Fin r) (c : Fin r ⊕ Fin r) :
    weylPerm (K := K) hr i c.swap = (weylPerm (K := K) hr i c).swap :=
  monoPermFun_mem _ c

theorem weylPerm_inl_of_lt {i : Fin r} (h : i.val + 1 < r) (k : Fin r) :
    weylPerm (K := K) hr i (Sum.inl k) = Sum.inl (Equiv.swap i ⟨i.val + 1, h⟩ k) := by
  apply coordWt_injective
  rw [coordWt_weylPerm, coordWt_inl, coordWt_inl, simpleRefl_of_lt h, signedPermAut_eps,
    Pi.one_apply, Units.val_one, one_smul]

theorem weylPerm_inl_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) (k : Fin r) :
    weylPerm (K := K) hr i (Sum.inl k) =
      if k = ⟨r - 2, by omega⟩ ∨ k = i then Sum.inr (Equiv.swap ⟨r - 2, by omega⟩ i k)
      else Sum.inl k := by
  apply coordWt_injective
  rw [coordWt_weylPerm, coordWt_inl, simpleRefl_of_not_lt h, signedPermAut_eps]
  have hi : i.val = r - 1 := by have := i.isLt; omega
  by_cases hk : k = ⟨r - 2, by omega⟩ ∨ k = i
  · rw [ite_eq_left hk, coordWt_inr]
    have hs : (lastSigns r i k : ℤ) = -1 := by
      rcases hk with rfl | rfl
      · simp [lastSigns]
        omega
      · simp [lastSigns]
    rw [hs, neg_one_smul]
  · rw [ite_eq_right hk, coordWt_inl]
    have hk1 : k ≠ ⟨r - 2, by omega⟩ := fun h' => hk (Or.inl h')
    have hk2 : k ≠ i := fun h' => hk (Or.inr h')
    have hs : (lastSigns r i k : ℤ) = 1 := by
      have hk3 : k.val + 2 ≠ r := fun h' => hk1 (Fin.ext (by simp only; omega))
      simp [lastSigns, hk2, hk3]
    rw [hs, one_smul, Equiv.swap_apply_of_ne_of_ne hk1 hk2]

theorem weylElt_smul_coordSpan_eq_iff (i : Fin r) (S : Set (Fin r ⊕ Fin r)) :
    weylElt r K i • coordSpan K S = coordSpan K S ↔ weylPerm (K := K) hr i '' S = S := by
  obtain ⟨μ, -, hμ⟩ := exists_autMat_eq_monoPermFun
    (⟨weylElt r K i, weylElt_mem_monoAut hr i⟩ : monoAut r K)
  exact smul_coordSpan_eq_iff (fun c => (μ c).ne_zero) hμ S

end Action

section Flags

variable (hr : 3 ≤ r)
include hr

theorem weylElt_smul_flag_of_ne {i : ℕ} (_hi1 : 1 ≤ i) (hi2 : i ≤ r - 2) {j : Fin r}
    (hj : j.val + 1 ≠ i) : weylElt r K j • flag r K i = flag r K i := by
  have hr2 : 2 ≤ r := by omega
  rw [flag_eq_coordSpan, weylElt_smul_coordSpan_eq_iff hr2]
  refine image_eq_self_of_mapsTo (weylPerm_mul_self hr2 j) ?_
  rintro _ ⟨k, hk, rfl⟩
  simp only [Set.mem_ofPred_eq] at hk
  by_cases hjr : j.val + 1 < r
  · rw [weylPerm_inl_of_lt hr2 hjr]
    refine ⟨_, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq]
    by_cases hkj : k = j
    · subst k
      rw [Equiv.swap_apply_left]
      simp only
      omega
    by_cases hkj' : k = ⟨j.val + 1, hjr⟩
    · subst k
      rw [Equiv.swap_apply_right]
      simp only at hk
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hkj hkj']
      exact hk
  · have hj' : j.val = r - 1 := by have := j.isLt; omega
    have hk' : ¬(k = ⟨r - 2, by omega⟩ ∨ k = j) := by
      rintro (h | h)
      · have : k.val = r - 2 := congrArg Fin.val h
        omega
      · have : k.val = j.val := congrArg Fin.val h
        omega
    rw [weylPerm_inl_of_not_lt hr2 hjr, ite_eq_right hk']
    exact ⟨k, hk, rfl⟩

theorem weylElt_smul_flag_ne {j : Fin r} (hj : j.val + 1 ≤ r - 2) :
    weylElt r K j • flag r K (j.val + 1) ≠ flag r K (j.val + 1) := by
  have hr2 : 2 ≤ r := by omega
  have hjr : j.val + 1 < r := by omega
  rw [flag_eq_coordSpan, Ne, weylElt_smul_coordSpan_eq_iff hr2]
  refine image_ne_self_of_mem (c := Sum.inl j) ⟨j, by simp, rfl⟩ ?_
  rw [weylPerm_inl_of_lt hr2 hjr, Equiv.swap_apply_left]
  rintro ⟨k, hk, he⟩
  simp only [Set.mem_ofPred_eq] at hk
  rw [Sum.inl.injEq] at he
  subst he
  simp only at hk
  omega

theorem weylElt_last_smul :
    weylElt r K ⟨r - 1, by omega⟩ • flag r K r ≠ flag r K r ∧
      weylElt r K ⟨r - 1, by omega⟩ • Xstar r K (by omega) = Xstar r K (by omega) := by
  have hr2 : 2 ≤ r := by omega
  have hlt : ¬((⟨r - 1, by omega⟩ : Fin r).val + 1 < r) := by simp only; omega
  set p : Fin r := ⟨r - 2, by omega⟩ with hp
  set q : Fin r := ⟨r - 1, by omega⟩ with hq
  have hpq : p ≠ q := by simp [hp, hq, Fin.ext_iff]; omega
  have hσp : weylPerm (K := K) hr2 q (Sum.inl p) = Sum.inr q := by
    rw [weylPerm_inl_of_not_lt hr2 hlt, ite_eq_left (Or.inl rfl), Equiv.swap_apply_left]
  have hσq : weylPerm (K := K) hr2 q (Sum.inr q) = Sum.inl p := by
    rw [show (Sum.inr q : Fin r ⊕ Fin r) = (Sum.inl q).swap from rfl, weylPerm_swap,
      weylPerm_inl_of_not_lt hr2 hlt, ite_eq_left (Or.inr rfl), Equiv.swap_apply_right]
    rfl
  refine ⟨?_, ?_⟩
  · rw [flag_eq_coordSpan, Ne, weylElt_smul_coordSpan_eq_iff hr2]
    refine image_ne_self_of_mem (c := Sum.inl p) ⟨p, by simp [hp], rfl⟩ ?_
    rw [hσp]
    rintro ⟨k, -, he⟩
    exact Sum.inl_ne_inr he
  · rw [Xstar_eq_coordSpan, weylElt_smul_coordSpan_eq_iff hr2]
    refine image_eq_self_of_mapsTo (weylPerm_mul_self hr2 q) fun c hc => ?_
    rw [mem_Xstar_coords (by omega)] at hc ⊢
    rcases hc with ⟨k, hk, rfl⟩ | rfl
    · by_cases hkp : k = p
      · subst k
        rw [hσp]
        exact Or.inr rfl
      · have hkq : k ≠ q := by
          rintro rfl
          simp [hq] at hk
        rw [weylPerm_inl_of_not_lt hr2 hlt, ite_eq_right (not_or.2 ⟨hkp, hkq⟩)]
        exact Or.inl ⟨k, hk, rfl⟩
    · rw [hσq]
      exact Or.inl ⟨p, by simp [hp]; omega, rfl⟩

theorem weylElt_penult_smul :
    weylElt r K ⟨r - 2, by omega⟩ • Xstar r K (by omega) ≠ Xstar r K (by omega) ∧
      weylElt r K ⟨r - 2, by omega⟩ • flag r K r = flag r K r := by
  have hr2 : 2 ≤ r := by omega
  have hlt : (⟨r - 2, by omega⟩ : Fin r).val + 1 < r := by simp only; omega
  refine ⟨?_, ?_⟩
  · rw [Xstar_eq_coordSpan, Ne, weylElt_smul_coordSpan_eq_iff hr2]
    refine image_ne_self_of_mem (c := Sum.inl ⟨r - 2, by omega⟩)
      ((mem_Xstar_coords (by omega)).2 (Or.inl ⟨_, by simp only; omega, rfl⟩)) ?_
    rw [weylPerm_inl_of_lt hr2 hlt, Equiv.swap_apply_left, mem_Xstar_coords (by omega)]
    rintro (⟨k, hk, he⟩ | he)
    · rw [Sum.inl.injEq] at he
      subst he
      simp only at hk
      omega
    · exact Sum.inl_ne_inr he
  · rw [flag_eq_coordSpan, weylElt_smul_coordSpan_eq_iff hr2]
    refine image_eq_self_of_mapsTo (weylPerm_mul_self hr2 _) ?_
    rintro _ ⟨k, -, rfl⟩
    rw [weylPerm_inl_of_lt hr2 hlt]
    exact ⟨_, (Equiv.swap _ _ k).isLt, rfl⟩

theorem weylElt_smul_flag_top_and_Xstar {j : Fin r} (hj : j.val + 1 ≤ r - 2) :
    weylElt r K j • flag r K r = flag r K r ∧
      weylElt r K j • Xstar r K (by omega) = Xstar r K (by omega) := by
  have hr2 : 2 ≤ r := by omega
  have hjr : j.val + 1 < r := by omega
  have hq1 : (⟨r - 1, by omega⟩ : Fin r) ≠ j := Fin.ne_of_val_ne (show r - 1 ≠ j.val by omega)
  have hq2 : (⟨r - 1, by omega⟩ : Fin r) ≠ ⟨j.val + 1, hjr⟩ :=
    Fin.ne_of_val_ne (show r - 1 ≠ j.val + 1 by omega)
  refine ⟨?_, ?_⟩
  · rw [flag_eq_coordSpan, weylElt_smul_coordSpan_eq_iff hr2]
    refine image_eq_self_of_mapsTo (weylPerm_mul_self hr2 _) ?_
    rintro _ ⟨k, -, rfl⟩
    rw [weylPerm_inl_of_lt hr2 hjr]
    exact ⟨_, (Equiv.swap _ _ k).isLt, rfl⟩
  · rw [Xstar_eq_coordSpan, weylElt_smul_coordSpan_eq_iff hr2]
    refine image_eq_self_of_mapsTo (weylPerm_mul_self hr2 _) fun c hc => ?_
    rw [mem_Xstar_coords (by omega)] at hc ⊢
    rcases hc with ⟨k, hk, rfl⟩ | rfl
    · rw [weylPerm_inl_of_lt hr2 hjr]
      refine Or.inl ⟨_, ?_, rfl⟩
      by_cases hkj : k = j
      · subst k
        rw [Equiv.swap_apply_left]
        simp only
        omega
      by_cases hkj' : k = ⟨j.val + 1, hjr⟩
      · subst k
        rw [Equiv.swap_apply_right]
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne hkj hkj']
        exact hk
    · rw [show (Sum.inr ⟨r - 1, by omega⟩ : Fin r ⊕ Fin r) = (Sum.inl ⟨r - 1, by omega⟩).swap
        from rfl, weylPerm_swap, weylPerm_inl_of_lt hr2 hjr,
        Equiv.swap_apply_of_ne_of_ne hq1 hq2]
      exact Or.inr rfl

end Flags

theorem orthogonal_geometry_split_Weyl_lifts {K : Type*} [Field K] {r : ℕ} (hr : 3 ≤ r) :
    ∃ ν : torusWeyl r K →* weylGroup r,
      (∀ (n : torusWeyl r K) (c : Fin r ⊕ Fin r), ∃ (μ : Kˣ) (c' : Fin r ⊕ Fin r),
        (n : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single c 1) =
            (μ : K) • Pi.single c' 1 ∧
          coordWt c' = ((ν n : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (coordWt c)) ∧
      Function.Surjective ν ∧
      ν.ker = (torus r K).subgroupOf (torusWeyl r K) ∧
      (∀ i : Fin r, ((ν ⟨weylElt r K i, weylElt_mem_torusWeyl i⟩ : weylGroup r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) = simpleRefl r i) ∧
      (∀ (n : torusWeyl r K) (α : Fin r → ℤ), α ∈ roots r →
        (rootSubgroup r K α).map
            (MulAut.conj (n : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))).toMonoidHom =
          rootSubgroup r K (((ν n : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) α)) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ r - 2 → ∀ j : Fin r, j.val + 1 ≠ i →
        weylElt r K j • flag r K i = flag r K i) ∧
      (∀ j : Fin r, j.val + 1 ≤ r - 2 →
        weylElt r K j • flag r K (j.val + 1) ≠ flag r K (j.val + 1)) ∧
      (weylElt r K ⟨r - 1, by omega⟩ • flag r K r ≠ flag r K r ∧
        weylElt r K ⟨r - 1, by omega⟩ • Xstar r K (by omega) = Xstar r K (by omega)) ∧
      (weylElt r K ⟨r - 2, by omega⟩ • Xstar r K (by omega) ≠ Xstar r K (by omega) ∧
        weylElt r K ⟨r - 2, by omega⟩ • flag r K r = flag r K r) ∧
      ∀ j : Fin r, j.val + 1 ≤ r - 2 →
        weylElt r K j • flag r K r = flag r K r ∧
          weylElt r K j • Xstar r K (by omega) = Xstar r K (by omega) := by
  have hr2 : 2 ≤ r := by omega
  exact ⟨torusWeylNu r K hr2, apply_single_torusWeylNu hr2, torusWeylNu_surjective hr2 hr,
    torusWeylNu_ker hr2, fun i => congrArg Subtype.val (torusWeylNu_weylElt hr2 i),
    fun n α hα => map_conj_rootSubgroup_torusWeyl hr2 n hα,
    fun i hi1 hi2 j hj => weylElt_smul_flag_of_ne hr hi1 hi2 hj,
    fun j hj => weylElt_smul_flag_ne hr hj, weylElt_last_smul hr, weylElt_penult_smul hr,
    fun j hj => weylElt_smul_flag_top_and_Xstar hr hj⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
