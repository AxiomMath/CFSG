module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups (rootCharHom)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

namespace KacData

private theorem eqvGen_perm_iff {X : Type*} {r : X → X → Prop} (σ : Equiv.Perm X)
    (h : ∀ a b, r (σ a) (σ b) ↔ r a b) (a b : X) :
    Relation.EqvGen r (σ a) (σ b) ↔ Relation.EqvGen r a b := by
  constructor
  · intro hh
    have h' : ∀ u v, Relation.EqvGen r u v → Relation.EqvGen r (σ.symm u) (σ.symm v) := by
      intro u v huv
      induction huv with
      | rel x y hxy =>
        exact Relation.EqvGen.rel _ _ ((h (σ.symm x) (σ.symm y)).1 (by simpa using hxy))
      | refl x => exact Relation.EqvGen.refl _
      | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    simpa using h' (σ a) (σ b) hh
  · intro hh
    induction hh with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ ((h x y).2 hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

variable {τ : Tag} (K : KacData τ)

theorem extRoot_mem_rootsOf_comp {p : ℕ} {μ : Fin τ.rank → ℤ} {x : Option (Fin τ.rank)}
    (hx : K.IsZ p μ x) : K.extRoot x ∈ K.rootsOf (K.comp p μ x) := by
  classical
  refine ⟨K.isRoot_extRoot x, fun y => if y = x then 1 else 0, ?_, Or.inl ?_⟩
  · intro y hy
    by_cases h : y = x
    · rw [h]
      exact K.mem_comp_self hx
    · simp [h] at hy
  · rw [combo, Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
    simp

theorem comp_eq_of_extRoot_mem {p : ℕ} {μ : Fin τ.rank → ℤ} {x y : Option (Fin τ.rank)}
    (hx : K.IsZ p μ x) (hxy : K.extRoot x ∈ K.rootsOf (K.comp p μ y)) :
    K.comp p μ x = K.comp p μ y := by
  classical
  obtain ⟨hroot, n, hn_supp, hcombo⟩ := hxy
  have hn_ne : n ≠ 0 := by
    intro h
    have h0 : K.combo n = 0 := by
      rw [h]
      simp [combo]
    rcases hcombo with e | e
    · rw [e, h0] at hroot
      exact hroot.ne_zero rfl
    · rw [e, h0, neg_zero] at hroot
      exact hroot.ne_zero rfl
  by_cases hmem : x ∈ K.comp p μ y
  · exact K.comp_eq_of_mem hmem
  · have hy : K.IsZ p μ y := by
      have hz : ∃ z, n z ≠ 0 := by
        by_contra h
        push Not at h
        exact hn_ne (funext fun z => h z)
      obtain ⟨z, hz⟩ := hz
      have hzC : z ∈ K.comp p μ y := hn_supp z hz
      exact (K.isZ_iff_of_eqvGen hzC.2).2 hzC.1
    have hyx : y ∉ K.comp p μ x := by
      intro h
      exact hmem ⟨hx, h.2.symm⟩
    have hsep := K.comp_separated hy hyx
    have hsupp₁ : ∀ z, (if z = x then 1 else 0 : ℕ) ≠ 0 → z ∈ K.comp p μ x := by
      intro z hz
      by_cases h : z = x
      · rw [h]
        exact K.mem_comp_self hx
      · simp [h] at hz
    have hzero := K.iform_combo_eq_zero hsep hsupp₁ hn_supp
    have hcombo1 : K.combo (fun z => if z = x then 1 else 0) = K.extRoot x := by
      rw [combo, Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
      simp
    rw [hcombo1] at hzero
    have hzero_self : iform (K.extRoot x) (K.extRoot x) = 0 := by
      rcases hcombo with e | e
      · rw [e] at hzero
        rw [e]
        exact hzero
      · rw [e]
        rw [e] at hzero
        rw [show -K.combo n = (-1 : ℤ) • K.combo n by rw [neg_one_smul]] at hzero
        rw [show -K.combo n = (-1 : ℤ) • K.combo n by rw [neg_one_smul]]
        rw [iform_smul_right]
        rw [hzero, mul_zero]
    have hext_zero : K.extRoot x = 0 := eq_zero_of_iform_self hzero_self
    exfalso
    exact (K.isRoot_extRoot x).ne_zero hext_zero

theorem rootsOf_comp_eq_span (hK : K.Facts) {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ}
    (hμ : K.IsNormal p μ) (x : Option (Fin τ.rank)) :
    K.rootsOf (K.comp p μ x) =
      {v | IsRoot τ v ∧ v ∈ Submodule.span ℤ (K.extRoot '' K.comp p μ x)} := by
  classical
  have hcombo_mem : ∀ n, (∀ y, n y ≠ 0 → y ∈ K.comp p μ x) →
      K.combo n ∈ Submodule.span ℤ (K.extRoot '' K.comp p μ x) := by
    intro n hn
    rw [combo]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases h : n y = 0
    · rw [h, Nat.cast_zero, zero_smul]
      exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨y, hn y h, rfl⟩
  ext v
  constructor
  · rintro ⟨hv, n, hn, hcombo⟩
    refine ⟨hv, ?_⟩
    rcases hcombo with e | e
    · rw [e]
      exact hcombo_mem n hn
    · rw [e]
      exact Submodule.neg_mem _ (hcombo_mem n hn)
  · rintro ⟨hv, hvspan⟩
    have hdiv : (p : ℤ) ∣ v ⬝ᵥ μ := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hvspan
      · rintro _ ⟨y, hy, rfl⟩
        exact K.extRoot_dvd hy.1
      · rw [zero_dotProduct]
        exact dvd_zero _
      · intro u w _ _ ihu ihw
        rw [add_dotProduct]
        exact Dvd.dvd.add ihu ihw
      · intro c u _ ihu
        rw [smul_dotProduct]
        exact Dvd.dvd.mul_left ihu c
    obtain ⟨n, hn, hcombo⟩ := K.exists_combo_of_dvd hK hp hμ hv hdiv
    obtain ⟨y, hny, hiy⟩ := K.exists_iform_ne_zero hv hcombo
    have hy : K.IsZ p μ y := hn y hny
    have hmem := K.mem_rootsOf_comp hK hv hn hcombo hny hiy
    by_cases hyx : y ∈ K.comp p μ x
    · rw [K.comp_eq_of_mem hyx] at hmem
      exact hmem
    · exfalso
      obtain ⟨-, n₁, hn₁, hv_n₁⟩ := hmem
      have hsep := K.comp_separated hy hyx
      have horth : ∀ w ∈ Submodule.span ℤ (K.extRoot '' K.comp p μ x),
          iform w (K.combo n₁) = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨a, ha, rfl⟩ := hu
          rw [iform_comm, iform_combo_left]
          refine Finset.sum_eq_zero fun b _ => ?_
          by_cases hb : n₁ b = 0
          · rw [hb, Nat.cast_zero, zero_mul]
          · have hbC : b ∈ K.comp p μ y := hn₁ b hb
            obtain ⟨hne, hnotadj⟩ := hsep a ha b hbC
            have hzero : iform (K.extRoot b) (K.extRoot a) = 0 := by
              rw [iform_comm]
              by_contra h
              exact hnotadj ⟨hne, h⟩
            rw [hzero, mul_zero]
        | zero => simp [iform]
        | add u w _ _ ihu ihw =>
          rw [iform_add_left, ihu, ihw, add_zero]
        | smul c u _ ihu =>
          rw [iform_smul_left, ihu, mul_zero]
      have hzero_v : iform v (K.combo n₁) = 0 := horth v hvspan
      have hzero_self : iform v v = 0 := by
        rcases hv_n₁ with e | e
        · rw [e] at hzero_v
          rw [e]
          exact hzero_v
        · rw [e]
          rw [e] at hzero_v
          rw [show -K.combo n₁ = (-1 : ℤ) • K.combo n₁ by rw [neg_one_smul]] at hzero_v
          rw [show -K.combo n₁ = (-1 : ℤ) • K.combo n₁ by rw [neg_one_smul]]
          rw [iform_smul_right]
          rw [hzero_v, mul_zero]
      have hv_zero : v = 0 := eq_zero_of_iform_self hzero_self
      exact hv.ne_zero hv_zero

section Classes

variable {M : Type*} [CommGroup M]

theorem componentRoots_mk_extRoot (hK : K.Facts) {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ}
    (hμ : K.IsNormal p μ) {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hχ : ∀ γ, IsRoot τ γ → (χ (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ))
    {x : Option (Fin τ.rank)} (hx : K.IsZ p μ x) :
    componentRoots χ ⟦⟨K.extRoot x, K.extRoot_mem_kernelRoots hχ hx⟩⟧ =
      K.rootsOf (K.comp p μ x) := by
  obtain ⟨x', hx', hcomp⟩ := K.componentRoots_eq_rootsOf hK hp hμ hχ
    ⟦⟨K.extRoot x, K.extRoot_mem_kernelRoots hχ hx⟩⟧
  have hmem : K.extRoot x ∈ K.rootsOf (K.comp p μ x') := by
    rw [← hcomp]
    exact ⟨K.extRoot_mem_kernelRoots hχ hx, rfl⟩
  have hceq : K.comp p μ x = K.comp p μ x' := K.comp_eq_of_extRoot_mem hx hmem
  rw [hcomp, hceq]

theorem mk_extRoot_eq_iff (hK : K.Facts) {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ}
    (hμ : K.IsNormal p μ) {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hχ : ∀ γ, IsRoot τ γ → (χ (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ))
    {x y : Option (Fin τ.rank)} (hx : K.IsZ p μ x) (hy : K.IsZ p μ y) :
    (⟦⟨K.extRoot x, K.extRoot_mem_kernelRoots hχ hx⟩⟧ : KernelComponent χ) =
        ⟦⟨K.extRoot y, K.extRoot_mem_kernelRoots hχ hy⟩⟧ ↔
      Relation.EqvGen (K.ZRel p μ) x y := by
  constructor
  · intro h
    have hcomp := congrArg (componentRoots χ) h
    rw [K.componentRoots_mk_extRoot hK hp hμ hχ hx,
        K.componentRoots_mk_extRoot hK hp hμ hχ hy] at hcomp
    have hmem : K.extRoot x ∈ K.rootsOf (K.comp p μ y) := by
      rw [← hcomp]
      exact K.extRoot_mem_rootsOf_comp hx
    have hceq : K.comp p μ x = K.comp p μ y := K.comp_eq_of_extRoot_mem hx hmem
    have hyx : y ∈ K.comp p μ x := by
      rw [hceq]
      exact K.mem_comp_self hy
    exact hyx.2
  · intro h
    have h' := K.mk_extRoot_eq hχ hx h
    have hsub : (⟨K.extRoot y, K.extRoot_mem_kernelRoots hχ ((K.isZ_iff_of_eqvGen h).1 hx)⟩ : kernelRoots χ) =
        ⟨K.extRoot y, K.extRoot_mem_kernelRoots hχ hy⟩ := Subtype.ext rfl
    rw [hsub] at h'
    exact h'

theorem exists_mk_extRoot (hK : K.Facts) {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ}
    (hμ : K.IsNormal p μ) {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hχ : ∀ γ, IsRoot τ γ → (χ (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ))
    (i : KernelComponent χ) :
    ∃ (x : Option (Fin τ.rank)) (hx : K.IsZ p μ x),
      i = ⟦⟨K.extRoot x, K.extRoot_mem_kernelRoots hχ hx⟩⟧ := by
  obtain ⟨x, hx, hcomp⟩ := K.componentRoots_eq_rootsOf hK hp hμ hχ i
  refine ⟨x, hx, ?_⟩
  have hmem : K.extRoot x ∈ componentRoots χ i := by
    rw [hcomp]
    exact K.extRoot_mem_rootsOf_comp hx
  obtain ⟨hxroot, hxeq⟩ := hmem
  rw [← hxeq]

end Classes

theorem image_comp {p : ℕ} {μ : Fin τ.rank → ℤ} (σ : Equiv.Perm (Option (Fin τ.rank)))
    (hZ : ∀ x, K.IsZ p μ (σ x) ↔ K.IsZ p μ x) (hA : ∀ x y, K.Adj (σ x) (σ y) ↔ K.Adj x y)
    (x : Option (Fin τ.rank)) : σ '' K.comp p μ x = K.comp p μ (σ x) := by
  have hZrel : ∀ a b, K.ZRel p μ (σ a) (σ b) ↔ K.ZRel p μ a b := by
    intro a b
    simp only [ZRel, hZ a, hZ b, hA a b]
  have hEqv : ∀ a b, Relation.EqvGen (K.ZRel p μ) (σ a) (σ b) ↔
      Relation.EqvGen (K.ZRel p μ) a b :=
    eqvGen_perm_iff σ hZrel
  have hcomp : ∀ y, y ∈ K.comp p μ x ↔ σ y ∈ K.comp p μ (σ x) := by
    intro y
    constructor
    · rintro ⟨hyZ, hyE⟩
      exact ⟨(hZ y).2 hyZ, (hEqv x y).2 hyE⟩
    · rintro ⟨hyZ, hyE⟩
      exact ⟨(hZ y).1 hyZ, (hEqv x y).1 hyE⟩
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hcomp y).1 hy
  · intro hz
    refine ⟨σ.symm z, ?_, σ.apply_symm_apply z⟩
    exact (hcomp (σ.symm z)).2 (by simpa using hz)

end KacData

end CFSG.HardMathSupport.Timmesfeld.CrossChar

end
