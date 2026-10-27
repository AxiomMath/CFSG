module

public import CFSG.HardMathSupport.Kantor79.CommutingLongRoot

public section

namespace CFSG.HardMathSupport.Kantor79

open CFSG.HardMathSupport.GuralnickMalle QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

omit [CharP K 2] in
theorem sub_mem_movedSpace (s : V ≃ₗ[K] V) (x : V) : s x - x ∈ movedSpace s :=
  ⟨x, by simp⟩

omit [CharP K 2] in
theorem mem_movedSpace_iff {s : V ≃ₗ[K] V} {y : V} : y ∈ movedSpace s ↔ ∃ x, s x - x = y := by
  simp [movedSpace]

theorem IsLongRootElement.isometry {s : V ≃ₗ[K] V} (hs : IsLongRootElement Qf s) (v : V) :
    Qf (s v) = Qf v :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hs.mem_orthogonalGroup v

theorem IsLongRootElement.qf_eq_zero_of_mem_movedSpace {s : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) {w : V} (hw : w ∈ movedSpace s) : Qf w = 0 := by
  obtain ⟨a, b, ha, hb, hab, -, -, -, hform⟩ := hs
  have hxeq : s = rootEquiv Qf a b ha hb hab := by
    ext v
    rw [rootEquiv_apply, hform]
  rw [hxeq, movedSpace_rootEquiv] at hw
  exact Qf_eq_zero_on_span_singular_pair ha hb hab (range_rootEnd_le_span Qf a b hw)

theorem IsLongRootElement.exists_eq_siegelEquiv {s : V ≃ₗ[K] V} (hs : IsLongRootElement Qf s) :
    ∃ (a b : V) (ha : Qf a = 0) (hb : Qf b = 0) (hab : polarBilin Qf a b = 0),
      LinearIndependent K ![a, b] ∧ s = siegelEquiv Qf a b ha hb hab 1 := by
  obtain ⟨a, b, ha, hb, hab, -, -, hli, hform⟩ := hs
  have hab' : polarBilin Qf a b = 0 := hab
  refine ⟨a, b, ha, hb, hab', hli, ?_⟩
  ext v
  rw [siegelEquiv_apply, siegelLin_apply, hform]
  simp only [one_smul, polarBilin_apply_apply]

theorem IsLongRootElement.mul_self {s : V ≃ₗ[K] V} (hs : IsLongRootElement Qf s) : s * s = 1 := by
  obtain ⟨a, b, ha, hb, hab, -, hxeq⟩ := hs.exists_eq_siegelEquiv
  rw [hxeq]
  exact siegelEquiv_mul_self Qf a b ha hb hab 1

theorem IsLongRootElement.sub_one_mul_self {s : V ≃ₗ[K] V} (hs : IsLongRootElement Qf s) :
    ((s : V →ₗ[K] V) - 1) * ((s : V →ₗ[K] V) - 1) = 0 := by
  obtain ⟨a, b, ha, hb, hab, h⟩ := hs.sub_one_eq_rootEnd
  rw [h]
  exact rootEnd_sq_eq_zero Qf a b ha hb hab

theorem IsLongRootElement.apply_eq_self_of_mem_movedSpace {s : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) {x : V} (hx : x ∈ movedSpace s) : s x = x := by
  obtain ⟨y, rfl⟩ := mem_movedSpace_iff.mp hx
  have h := congrArg (fun f : V →ₗ[K] V => f y) hs.sub_one_mul_self
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearEquiv.coe_coe, LinearMap.zero_apply] at h
  exact sub_eq_zero.mp h

theorem IsLongRootElement.finrank_movedSpace
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {s : V ≃ₗ[K] V} (hs : IsLongRootElement Qf s) : finrank K (movedSpace s) = 2 := by
  obtain ⟨a, b, ha, hb, hab, hli, hxeq⟩ := hs.exists_eq_siegelEquiv
  have hrange : movedSpace s = Submodule.span K ({a, b} : Set V) := by
    rw [hxeq]
    change LinearMap.range (siegelLin Qf a b 1 - 1) = _
    exact siegelLin_sub_one_range Qf a b hnd hli 1 one_ne_zero
  rw [hrange]
  have h := finrank_span_eq_card hli
  rw [show Set.range ![a, b] = ({a, b} : Set V) by
    ext x; simp [eq_comm, or_comm]] at h
  simpa using h

end CFSG.HardMathSupport.Kantor79

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 CFSG.HardMathSupport.GuralnickMalle QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

omit [CharP K 2] in
theorem mem_orthogonal_iff_polar {A : Submodule K V} {y : V} :
    y ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf) A ↔ ∀ x ∈ A, polar Qf x y = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [polarBilin_apply_apply]

theorem polar_self_eq_zero (x : V) : polar Qf x x = 0 := by
  rw [polar_self, CharTwo.two_nsmul]

omit [CharP K 2] in
theorem polar_apply_apply_of_isometry {f : V →ₗ[K] V} (hf : ∀ v, Qf (f v) = Qf v) (x y : V) :
    polar Qf (f x) (f y) = polar Qf x y := by
  have h := QuadraticMap.map_add Qf (f x) (f y)
  rw [← map_add, hf, hf, hf, QuadraticMap.map_add Qf x y] at h
  exact (add_left_cancel h).symm

omit [CharP K 2] in
theorem polar_eq_zero_of_totallySingular {A : Submodule K V} (hA : ∀ w ∈ A, Qf w = 0)
    {x y : V} (hx : x ∈ A) (hy : y ∈ A) : polar Qf x y = 0 := by
  have h := QuadraticMap.map_add Qf x y
  rw [hA _ (A.add_mem hx hy), hA x hx, hA y hy, zero_add, zero_add] at h
  exact h.symm

omit [CharP K 2] in
theorem le_orthogonal_of_totallySingular {A : Submodule K V} (hA : ∀ w ∈ A, Qf w = 0) :
    A ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) A := fun _ hy =>
  mem_orthogonal_iff_polar.mpr fun _ hx => polar_eq_zero_of_totallySingular hA hx hy

omit [CharP K 2] in
theorem nondegenerate_polarBilin (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) :
    (polarBilin Qf).Nondegenerate :=
  ⟨fun x hx => hnd x fun y => hx y, fun y hy => hnd y fun x => by rw [polar_comm]; exact hy x⟩

omit [CharP K 2] in
theorem finrank_orthogonal_polar [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) (A : Submodule K V) :
    finrank K (LinearMap.BilinForm.orthogonal (polarBilin Qf) A) = finrank K V - finrank K A :=
  LinearMap.BilinForm.finrank_orthogonal (nondegenerate_polarBilin hnd) A

theorem exists_polar_pair (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {a b : V}
    (hli : LinearIndependent K ![a, b]) (α β : K) :
    ∃ x : V, polar Qf x a = α ∧ polar Qf x b = β :=
  exists_polarBilin_pair Qf a b hnd hli α β

omit [CharP K 2] in
theorem exists_basis_of_finrank_eq_two {A : Submodule K V} (hA : finrank K A = 2) :
    ∃ a₁ a₂ : V, a₁ ∈ A ∧ a₂ ∈ A ∧ LinearIndependent K ![a₁, a₂] ∧
      Submodule.span K ({a₁, a₂} : Set V) = A := by
  have : Module.Finite K A := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq K A hA
  refine ⟨(b 0 : V), (b 1 : V), (b 0).2, (b 1).2, ?_, ?_⟩
  · have h := b.linearIndependent.map' A.subtype A.ker_subtype
    convert h using 1
    ext i
    fin_cases i <;> rfl
  · have h := congrArg (Submodule.map A.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top] at h
    convert h using 2
    ext x
    simp [Fin.exists_fin_two, eq_comm]

omit [CharP K 2] in
theorem span_pair_eq_of_finrank_eq_two {A : Submodule K V} (hA : finrank K A = 2) {a₁ a₂ : V}
    (h₁ : a₁ ∈ A) (h₂ : a₂ ∈ A) (hli : LinearIndependent K ![a₁, a₂]) :
    Submodule.span K ({a₁, a₂} : Set V) = A := by
  have : Module.Finite K A := Module.finite_of_finrank_pos (by omega)
  have hle : Submodule.span K ({a₁, a₂} : Set V) ≤ A := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    exacts [h₁, h₂]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [hA]
  have h := finrank_span_eq_card hli
  rw [show Set.range ![a₁, a₂] = ({a₁, a₂} : Set V) by
    ext x; simp [eq_comm, or_comm]] at h
  simpa using h

omit [CharP K 2] in
theorem ker_sub_one_eq_orthogonal_movedSpace
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {s : V ≃ₗ[K] V} (hs : ∀ v, Qf (s v) = Qf v) :
    LinearMap.ker ((s : V →ₗ[K] V) - 1) =
      LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s) := by
  have hpol : ∀ x y, polar Qf (s x) (s y) = polar Qf x y :=
    polar_apply_apply_of_isometry (f := (s : V →ₗ[K] V)) hs
  ext z
  rw [LinearMap.mem_ker, mem_orthogonal_iff_polar]
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, sub_eq_zero]
  constructor
  · intro hz y hy
    obtain ⟨x, rfl⟩ := mem_movedSpace_iff.mp hy
    have h1 := hpol x z
    rw [hz] at h1
    rw [polar_sub_left, h1, sub_self]
  · intro h
    have h0 : s z - z = 0 := by
      refine hnd _ fun y => ?_
      obtain ⟨x, rfl⟩ := s.surjective y
      have h1 := h _ (sub_mem_movedSpace s x)
      rw [polar_sub_left] at h1 ⊢
      rw [hpol, polar_comm Qf z x, polar_comm Qf z (s x)]
      linear_combination -h1
    exact sub_eq_zero.mp h0

theorem exists_siegel_scalar
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {s : V ≃ₗ[K] V} (hs : ∀ v, Qf (s v) = Qf v) {a₁ a₂ : V}
    (hli : LinearIndependent K ![a₁, a₂])
    (hspan : Submodule.span K ({a₁, a₂} : Set V) = movedSpace s)
    (hsing : ∀ w ∈ movedSpace s, Qf w = 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ v, s v = v + c • (polar Qf v a₁ • a₂ + polar Qf v a₂ • a₁) := by
  have ha₁ : a₁ ∈ movedSpace s := hspan ▸ Submodule.subset_span (by simp)
  have ha₁0 : a₁ ≠ 0 := by simpa using hli.ne_zero (0 : Fin 2)
  have hφmem : ∀ x, s x - x ∈ Submodule.span K ({a₁, a₂} : Set V) := fun x => by
    rw [hspan]; exact sub_mem_movedSpace s x
  have halt : ∀ x, polar Qf x (s x - x) = 0 := by
    intro x
    have h := QuadraticMap.map_add Qf x (s x - x)
    rw [add_sub_cancel, hs x, hsing _ (sub_mem_movedSpace s x)] at h
    linear_combination -h
  have hfix : ∀ z, polar Qf a₁ z = 0 → polar Qf a₂ z = 0 → s z = z := by
    intro z h₁ h₂
    have hz : z ∈ LinearMap.ker ((s : V →ₗ[K] V) - 1) := by
      rw [ker_sub_one_eq_orthogonal_movedSpace hnd hs, mem_orthogonal_iff_polar, ← hspan]
      intro y hy
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hy
      rw [polar_add_left, polar_smul_left, polar_smul_left, h₁, h₂]
      simp
    simpa [sub_eq_zero] using hz
  obtain ⟨u₁, hu₁₁, hu₁₂⟩ := exists_polar_pair hnd hli 1 0
  obtain ⟨u₂, hu₂₁, hu₂₂⟩ := exists_polar_pair hnd hli 0 1
  have hdec : ∀ x, s x - x = polar Qf x a₁ • (s u₁ - u₁) + polar Qf x a₂ • (s u₂ - u₂) := by
    intro x
    have h := hfix (x - polar Qf x a₁ • u₁ - polar Qf x a₂ • u₂) ?_ ?_
    · simp only [map_sub, map_smul] at h
      linear_combination (norm := module) h
    · rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right,
        polar_comm Qf a₁ x, polar_comm Qf a₁ u₁, polar_comm Qf a₁ u₂, hu₁₁, hu₂₁]
      simp
    · rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right,
        polar_comm Qf a₂ x, polar_comm Qf a₂ u₁, polar_comm Qf a₂ u₂, hu₁₂, hu₂₂]
      simp
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp (hφmem u₁)
  obtain ⟨r, t, hrt⟩ := Submodule.mem_span_pair.mp (hφmem u₂)
  have hp : p = 0 := by
    have h := halt u₁
    rw [← hpq, polar_add_right, polar_smul_right, polar_smul_right, hu₁₁, hu₁₂] at h
    simpa using h
  have ht : t = 0 := by
    have h := halt u₂
    rw [← hrt, polar_add_right, polar_smul_right, polar_smul_right, hu₂₁, hu₂₂] at h
    simpa using h
  have hrq : r = q := by
    have h := halt (u₁ + u₂)
    have e : s (u₁ + u₂) - (u₁ + u₂) = (s u₁ - u₁) + (s u₂ - u₂) := by
      rw [map_add]; abel
    rw [e, ← hpq, ← hrt] at h
    simp only [polar_add_left, polar_add_right, polar_smul_right, hu₁₁, hu₁₂, hu₂₁, hu₂₂,
      smul_eq_mul] at h
    have h' : r + q = 0 := by linear_combination h - hp - ht
    exact CharTwo.add_eq_zero.mp h'
  subst hp
  subst ht
  refine ⟨q, ?_, fun v => ?_⟩
  · intro hq0
    subst hq0
    obtain ⟨x, hx⟩ := mem_movedSpace_iff.mp ha₁
    rw [hdec x, ← hpq, ← hrt, hrq] at hx
    simp at hx
    exact ha₁0 hx.symm
  · have h := hdec v
    rw [← hpq, ← hrt, hrq] at h
    rw [sub_eq_iff_eq_add'] at h
    rw [h]
    module

theorem exists_eq_siegelEquiv
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {s : V ≃ₗ[K] V} (hs : ∀ v, Qf (s v) = Qf v) {a₁ a₂ : V}
    (hli : LinearIndependent K ![a₁, a₂])
    (hspan : Submodule.span K ({a₁, a₂} : Set V) = movedSpace s)
    (hsing : ∀ w ∈ movedSpace s, Qf w = 0)
    (h₁ : Qf a₁ = 0) (h₂ : Qf a₂ = 0) (h₁₂ : polarBilin Qf a₁ a₂ = 0) :
    ∃ c : K, c ≠ 0 ∧ s = siegelEquiv Qf a₁ a₂ h₁ h₂ h₁₂ c := by
  obtain ⟨c, hc0, hc⟩ := exists_siegel_scalar hnd hs hli hspan hsing
  refine ⟨c, hc0, ?_⟩
  ext v
  rw [hc v, siegelEquiv_apply, siegelLin_apply]
  simp only [polarBilin_apply_apply]
  module

theorem isLongRootElement_of_totallySingular_movedSpace
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {s : V ≃ₗ[K] V} (hs : ∀ v, Qf (s v) = Qf v)
    (hfin : finrank K (movedSpace s) = 2) (hsing : ∀ w ∈ movedSpace s, Qf w = 0) :
    IsLongRootElement Qf s := by
  obtain ⟨a₁, a₂, ha₁, ha₂, hli, hspan⟩ := exists_basis_of_finrank_eq_two hfin
  have h₁ : Qf a₁ = 0 := hsing a₁ ha₁
  have h₂ : Qf a₂ = 0 := hsing a₂ ha₂
  have h₁₂ : polarBilin Qf a₁ a₂ = 0 := polar_eq_zero_of_totallySingular hsing ha₁ ha₂
  obtain ⟨c, hc0, hceq⟩ := exists_eq_siegelEquiv hnd hs hli hspan hsing h₁ h₂ h₁₂
  rw [hceq]
  exact (isLongRootElement_siegelEquiv Qf a₁ a₂ h₁ h₂ h₁₂ hnd hli hc0).1

theorem isLongRootElement_iff
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s : V ≃ₗ[K] V} :
    IsLongRootElement Qf s ↔
      (∀ v, Qf (s v) = Qf v) ∧ finrank K (movedSpace s) = 2 ∧ ∀ w ∈ movedSpace s, Qf w = 0 :=
  ⟨fun hs => ⟨hs.isometry, hs.finrank_movedSpace hnd,
      fun _ hw => hs.qf_eq_zero_of_mem_movedSpace hw⟩,
    fun ⟨hs, hfin, hsing⟩ => isLongRootElement_of_totallySingular_movedSpace hnd hs hfin hsing⟩

omit [CharP K 2] in
private theorem mul_polar_eq_zero_of_sub_eq_smul {g : V →ₗ[K] V} {u w : V} {c : K}
    (hw : Qf w = 0) (hgQ : Qf (g u) = Qf u) (hc : g u - u = c • w) :
    c * polar Qf u w = 0 := by
  have hgu : g u = u + c • w := by
    rw [← hc]
    abel
  have h := QuadraticMap.map_add Qf u (c • w)
  rw [QuadraticMap.map_smul, hw, smul_zero, add_zero, QuadraticMap.polar_smul_right,
    smul_eq_mul, ← hgu, hgQ] at h
  linear_combination -h

omit [CharP K 2] in
theorem apply_eq_self_of_sub_mem_span_singular {U : Submodule K V}
    (hU : ∀ x ∈ U, (∀ y ∈ U, polar Qf x y = 0) → x = 0) {g : V →ₗ[K] V}
    (hgQ : ∀ u ∈ U, Qf (g u) = Qf u) {w : V} (hwU : w ∈ U) (hw : Qf w = 0)
    (hmem : ∀ u ∈ U, g u - u ∈ Submodule.span K ({w} : Set V)) : ∀ u ∈ U, g u = u := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₁, hu₁, hne⟩ := hcon
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp (hmem u₁ hu₁)
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    apply hne
    rw [zero_smul] at hc₁
    exact sub_eq_zero.mp hc₁.symm
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hne
    rw [smul_zero] at hc₁
    exact sub_eq_zero.mp hc₁.symm
  have hpol₁ : polar Qf u₁ w = 0 := by
    have h := mul_polar_eq_zero_of_sub_eq_smul hw (hgQ u₁ hu₁) hc₁.symm
    exact (mul_eq_zero.mp h).resolve_left hc₁0
  obtain ⟨u₂, hu₂, hpol₂⟩ : ∃ u₂ ∈ U, polar Qf u₂ w ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hw0
    apply hU w hwU
    intro y hy
    rw [QuadraticMap.polar_comm]
    exact hall y hy
  have hg₂ : g u₂ = u₂ := by
    obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp (hmem u₂ hu₂)
    have h := mul_polar_eq_zero_of_sub_eq_smul hw (hgQ u₂ hu₂) hc₂.symm
    have hc₂0 : c₂ = 0 := (mul_eq_zero.mp h).resolve_right hpol₂
    rw [hc₂0, zero_smul] at hc₂
    exact sub_eq_zero.mp hc₂.symm
  have hu : u₁ + u₂ ∈ U := U.add_mem hu₁ hu₂
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hmem (u₁ + u₂) hu)
  have hmoved : g (u₁ + u₂) - (u₁ + u₂) = c₁ • w := by
    rw [map_add, hg₂, hc₁]
    abel
  have hcc : c = c₁ := by
    have h0 : (c - c₁) • w = 0 := by
      rw [sub_smul, hc, hmoved, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  have hcne : c ≠ 0 := by
    rw [hcc]
    exact hc₁0
  have hsum := mul_polar_eq_zero_of_sub_eq_smul hw (hgQ (u₁ + u₂) hu) hc.symm
  have hsum0 : polar Qf (u₁ + u₂) w = 0 := (mul_eq_zero.mp hsum).resolve_left hcne
  rw [QuadraticMap.polar_add_left, hpol₁, zero_add] at hsum0
  exact hpol₂ hsum0

omit [CharP K 2] in
theorem eq_one_of_movedSpace_le_span_singular
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {g : V ≃ₗ[K] V}
    (hg : ∀ v, Qf (g v) = Qf v) {w : V} (hw : Qf w = 0)
    (hle : movedSpace g ≤ Submodule.span K ({w} : Set V)) : g = 1 := by
  have hU : ∀ x ∈ (⊤ : Submodule K V),
      (∀ y ∈ (⊤ : Submodule K V), polar Qf x y = 0) → x = 0 :=
    fun x _ h => hnd x fun y => h y Submodule.mem_top
  have hmem : ∀ u ∈ (⊤ : Submodule K V),
      (g : V →ₗ[K] V) u - u ∈ Submodule.span K ({w} : Set V) := by
    intro u _
    have hmoved : (g : V →ₗ[K] V) u - u ∈ movedSpace g :=
      LinearMap.mem_range.mpr ⟨u, by simp⟩
    exact hle hmoved
  have key := apply_eq_self_of_sub_mem_span_singular (g := (g : V →ₗ[K] V)) hU
    (fun u _ => hg u) Submodule.mem_top hw hmem
  apply LinearEquiv.ext
  intro u
  exact key u Submodule.mem_top

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
