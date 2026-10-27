module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.GF2Type.Smith1979.Case2

open Module

private theorem forall_eq_zero_of_sorted {ι R : Type*} [LinearOrder ι] [Zero R]
    (d : ι → ι → ι → R) (h12 : ∀ i j k, d i j k = d j i k) (h23 : ∀ i j k, d i j k = d i k j)
    (hii : ∀ i k, d i i k = 0) (hs : ∀ i j k, i < j → j < k → d i j k = 0) :
    ∀ i j k, d i j k = 0 := by
  intro i j k
  rcases lt_trichotomy i j with hij | rfl | hji
  · rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact hs i j k hij hjk
    · rw [h12, h23]
      exact hii _ _
    · rcases lt_trichotomy i k with hik | rfl | hki
      · rw [h23]
        exact hs i k j hik hkj
      · rw [h23]
        exact hii _ _
      · rw [h23, h12]
        exact hs k i j hki hij
  · exact hii _ _
  · rcases lt_trichotomy i k with hik | rfl | hki
    · rw [h12]
      exact hs j i k hji hik
    · rw [h23]
      exact hii _ _
    · rcases lt_trichotomy j k with hjk | rfl | hkj
      · rw [h12, h23]
        exact hs j k i hjk hki
      · rw [h12, h23]
        exact hii _ _
      · rw [h23, h12, h23]
        exact hs k j i hkj hji

private theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b
  decide

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def rad (T : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (x : W) :
    Submodule (ZMod 2) W :=
  LinearMap.ker (T x)

theorem mem_rad {T : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2} {x y : W} :
    y ∈ rad T x ↔ ∀ z, T x y z = 0 := by
  simp [rad, LinearMap.mem_ker, LinearMap.ext_iff]

theorem trilinear_swap_right (T : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (h2 : ∀ x y, T x y y = 0) (x y z : W) : T x y z = T x z y := by
  have h := h2 x (y + z)
  simp only [map_add, LinearMap.add_apply, h2 x y, h2 x z, zero_add, add_zero] at h
  exact (zmod2_eq_of_add_eq_zero h).symm

private structure Frame (ψ : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (α₀ : Module.Dual (ZMod 2) W)
    (x₀ e₁ f₁ e₂ f₂ : W) : Prop where
  α₀_e₁ : α₀ e₁ = 0
  α₀_f₁ : α₀ f₁ = 0
  α₀_e₂ : α₀ e₂ = 0
  α₀_f₂ : α₀ f₂ = 0
  ψ_e₁f₁ : ψ e₁ f₁ = 1
  ψ_e₂f₂ : ψ e₂ f₂ = 1
  ψ_e₁e₂ : ψ e₁ e₂ = 0
  ψ_e₁f₂ : ψ e₁ f₂ = 0
  ψ_f₁e₂ : ψ f₁ e₂ = 0
  ψ_f₁f₂ : ψ f₁ f₂ = 0
  span_eq : Submodule.span (ZMod 2) (Set.range ![x₀, e₁, f₁, e₂, f₂]) = ⊤

private theorem three_le_finrank_ker_prod [FiniteDimensional (ZMod 2) W]
    (hW : finrank (ZMod 2) W = 5) (f g : Module.Dual (ZMod 2) W) :
    3 ≤ finrank (ZMod 2) (LinearMap.ker (f.prod g)) := by
  have hr : finrank (ZMod 2) (LinearMap.range (f.prod g)) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range (f.prod g))
    rwa [Module.finrank_prod, finrank_self] at this
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.prod g)
  omega

private theorem apply_eq_zero_of_ker_eq_span (ψ : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) {x₀ : W}
    (hker : LinearMap.ker ψ = Submodule.span (ZMod 2) {x₀}) (y : W) : ψ x₀ y = 0 := by
  have h : x₀ ∈ LinearMap.ker ψ := hker ▸ Submodule.mem_span_singleton_self x₀
  rw [LinearMap.mem_ker] at h
  rw [h]
  rfl

private theorem exists_gram [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 5)
    (ψ : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (hsymm : ∀ x y, ψ x y = ψ y x)
    (halt : ∀ x, ψ x x = 0) {x₀ : W} (hx0 : x₀ ≠ 0)
    (hker : LinearMap.ker ψ = Submodule.span (ZMod 2) {x₀}) :
    ∃ e₁ f₁ e₂ f₂ : W, ψ e₁ f₁ = 1 ∧ ψ e₂ f₂ = 1 ∧ ψ e₁ e₂ = 0 ∧ ψ e₁ f₂ = 0 ∧ ψ f₁ e₂ = 0 ∧
      ψ f₁ f₂ = 0 := by
  have hspan1 : finrank (ZMod 2) (Submodule.span (ZMod 2) {x₀}) = 1 := finrank_span_singleton hx0
  have hpartner : ∀ v, v ∉ Submodule.span (ZMod 2) {x₀} → ∃ u, ψ v u = 1 := by
    intro v hv
    by_contra hcon
    push Not at hcon
    refine hv ?_
    rw [← hker, LinearMap.mem_ker]
    refine LinearMap.ext fun u => ?_
    show ψ v u = 0
    have := hcon u
    revert this
    generalize ψ v u = c
    revert c
    decide
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : W, e₁ ∉ Submodule.span (ZMod 2) {x₀} := by
    by_contra h
    push Not at h
    have htop : Submodule.span (ZMod 2) {x₀} = ⊤ := eq_top_iff.mpr fun v _ => h v
    rw [htop, finrank_top, hW] at hspan1
    omega
  obtain ⟨f₁, hf₁⟩ := hpartner e₁ he₁
  obtain ⟨e₂, he₂N, he₂⟩ : ∃ e₂ ∈ LinearMap.ker ((ψ e₁).prod (ψ f₁)),
      e₂ ∉ Submodule.span (ZMod 2) {x₀} := by
    by_contra h
    push Not at h
    have hle : LinearMap.ker ((ψ e₁).prod (ψ f₁)) ≤ Submodule.span (ZMod 2) {x₀} := h
    have h1 := Submodule.finrank_mono hle
    have h2 := three_le_finrank_ker_prod hW (ψ e₁) (ψ f₁)
    omega
  have hN := LinearMap.mem_ker.mp he₂N
  have h1e₂ : ψ e₁ e₂ = 0 := congrArg Prod.fst hN
  have h2e₂ : ψ f₁ e₂ = 0 := congrArg Prod.snd hN
  obtain ⟨y, hy⟩ := hpartner e₂ he₂
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : W, f₂ = y - ψ f₁ y • e₁ - ψ e₁ y • f₁ := ⟨_, rfl⟩
  have hf₁e₁ : ψ f₁ e₁ = 1 := by rw [hsymm]; exact hf₁
  have he₂e₁ : ψ e₂ e₁ = 0 := by rw [hsymm]; exact h1e₂
  have he₂f₁ : ψ e₂ f₁ = 0 := by rw [hsymm]; exact h2e₂
  refine ⟨e₁, f₁, e₂, f₂, hf₁, ?_, h1e₂, ?_, h2e₂, ?_⟩ <;> rw [hf₂] <;>
    simp only [map_sub, map_smul, smul_eq_mul]
  · rw [hy, he₂e₁, he₂f₁]
    ring
  · rw [halt e₁, hf₁]
    ring
  · rw [hf₁e₁, halt f₁]
    ring

private theorem span_of_gram [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 5)
    (ψ : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (hsymm : ∀ x y, ψ x y = ψ y x)
    (halt : ∀ x, ψ x x = 0) {x₀ e₁ f₁ e₂ f₂ : W} (hx0 : x₀ ≠ 0)
    (hker : LinearMap.ker ψ = Submodule.span (ZMod 2) {x₀})
    (g1 : ψ e₁ f₁ = 1) (g2 : ψ e₂ f₂ = 1) (g3 : ψ e₁ e₂ = 0) (g4 : ψ e₁ f₂ = 0)
    (g5 : ψ f₁ e₂ = 0) (g6 : ψ f₁ f₂ = 0) :
    Submodule.span (ZMod 2) (Set.range ![x₀, e₁, f₁, e₂, f₂]) = ⊤ := by
  have hx₀ψ : ∀ y, ψ x₀ y = 0 := apply_eq_zero_of_ker_eq_span ψ hker
  have hspan1 : finrank (ZMod 2) (Submodule.span (ZMod 2) {x₀}) = 1 := finrank_span_singleton hx0
  have hf₁e₁ : ψ f₁ e₁ = 1 := by rw [hsymm]; exact g1
  have he₂e₁ : ψ e₂ e₁ = 0 := by rw [hsymm]; exact g3
  have he₂f₁ : ψ e₂ f₁ = 0 := by rw [hsymm]; exact g5
  have hf₂e₁ : ψ f₂ e₁ = 0 := by rw [hsymm]; exact g4
  have hf₂f₁ : ψ f₂ f₁ = 0 := by rw [hsymm]; exact g6
  have hf₂e₂ : ψ f₂ e₂ = 1 := by rw [hsymm]; exact g2
  let Φ : W →ₗ[ZMod 2] ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 :=
    (ψ e₁).prod ((ψ f₁).prod ((ψ e₂).prod (ψ f₂)))
  have hΦ : ∀ w, Φ w = (ψ e₁ w, ψ f₁ w, ψ e₂ w, ψ f₂ w) := fun w => rfl
  have hΦσ : ∀ p q r s : ZMod 2, Φ (p • f₁ + q • e₁ + r • f₂ + s • e₂) = (p, q, r, s) := by
    intro p q r s
    rw [hΦ]
    simp only [map_add, map_smul, smul_eq_mul, halt, g1, g3, g4, hf₁e₁, g5, g6, he₂e₁, he₂f₁,
      g2, hf₂e₁, hf₂f₁, hf₂e₂, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  have hrange : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨p, q, r, s⟩ -
    exact ⟨p • f₁ + q • e₁ + r • f₂ + s • e₂, hΦσ p q r s⟩
  have hrk : finrank (ZMod 2) (LinearMap.ker Φ) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hrange, finrank_top] at h
    simp only [Module.finrank_prod, finrank_self] at h
    omega
  have hker2 : LinearMap.ker Φ = Submodule.span (ZMod 2) {x₀} := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hspan1, hrk])
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, hΦ]
    simp only [hsymm _ x₀, hx₀ψ]
    rfl
  rw [eq_top_iff]
  intro w _
  have hw : w - (ψ e₁ w • f₁ + ψ f₁ w • e₁ + ψ e₂ w • f₂ + ψ f₂ w • e₂) ∈ LinearMap.ker Φ := by
    rw [LinearMap.mem_ker, map_sub, hΦσ, hΦ, sub_self]
  rw [hker2, Submodule.mem_span_singleton] at hw
  obtain ⟨c, hc⟩ := hw
  have hrep : w = c • x₀ + (ψ e₁ w • f₁ + ψ f₁ w • e₁ + ψ e₂ w • f₂ + ψ f₂ w • e₂) := by
    rw [hc]
    abel
  rw [hrep]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (add_mem (add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩)))

private theorem exists_frame [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 5)
    (ψ : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (hsymm : ∀ x y, ψ x y = ψ y x)
    (halt : ∀ x, ψ x x = 0) {x₀ : W} (hker : LinearMap.ker ψ = Submodule.span (ZMod 2) {x₀})
    (α₀ : Module.Dual (ZMod 2) W) (hα₀ : α₀ x₀ = 1) :
    ∃ e₁ f₁ e₂ f₂ : W, Frame ψ α₀ x₀ e₁ f₁ e₂ f₂ := by
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hα₀
    exact zero_ne_one hα₀
  have hx₀ψ : ∀ y, ψ x₀ y = 0 := apply_eq_zero_of_ker_eq_span ψ hker
  obtain ⟨e₁, f₁, e₂, f₂, g1, g2, g3, g4, g5, g6⟩ := exists_gram hW ψ hsymm halt hx0 hker
  have hspan := span_of_gram hW ψ hsymm halt hx0 hker g1 g2 g3 g4 g5 g6
  have hψ' : ∀ (v u : W) (a b : ZMod 2), ψ (v - a • x₀) (u - b • x₀) = ψ v u := by
    intro v u a b
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hx₀ψ, hsymm v x₀,
      smul_zero, sub_zero, zero_sub, neg_zero, smul_eq_mul, mul_zero, zero_add, add_zero]
  have hα' : ∀ v : W, α₀ (v - α₀ v • x₀) = 0 := fun v => by
    rw [map_sub, map_smul, hα₀, smul_eq_mul, mul_one, sub_self]
  refine ⟨e₁ - α₀ e₁ • x₀, f₁ - α₀ f₁ • x₀, e₂ - α₀ e₂ • x₀, f₂ - α₀ f₂ • x₀,
    hα' _, hα' _, hα' _, hα' _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hψ', g1]
  · rw [hψ', g2]
  · rw [hψ', g3]
  · rw [hψ', g4]
  · rw [hψ', g5]
  · rw [hψ', g6]
  · rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hx : x₀ ∈ Submodule.span (ZMod 2) (Set.range ![x₀, e₁ - α₀ e₁ • x₀, f₁ - α₀ f₁ • x₀,
        e₂ - α₀ e₂ • x₀, f₂ - α₀ f₂ • x₀]) := Submodule.subset_span ⟨0, rfl⟩
    have hv : ∀ v : W, v - α₀ v • x₀ ∈ Submodule.span (ZMod 2) (Set.range ![x₀,
        e₁ - α₀ e₁ • x₀, f₁ - α₀ f₁ • x₀, e₂ - α₀ e₂ • x₀, f₂ - α₀ f₂ • x₀]) →
        v ∈ Submodule.span (ZMod 2) (Set.range ![x₀, e₁ - α₀ e₁ • x₀, f₁ - α₀ f₁ • x₀,
          e₂ - α₀ e₂ • x₀, f₂ - α₀ f₂ • x₀]) := fun v h => by
      have : v = (v - α₀ v • x₀) + α₀ v • x₀ := by abel
      rw [this]
      exact add_mem h (Submodule.smul_mem _ _ hx)
    fin_cases i
    · exact hx
    · exact hv _ (Submodule.subset_span ⟨1, rfl⟩)
    · exact hv _ (Submodule.subset_span ⟨2, rfl⟩)
    · exact hv _ (Submodule.subset_span ⟨3, rfl⟩)
    · exact hv _ (Submodule.subset_span ⟨4, rfl⟩)

private def wedge (ψ : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (α : Module.Dual (ZMod 2) W) :
    W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun x y => ψ x y • α + α x • ψ y + α y • ψ.flip x)
    (fun x x' y => by
      simp only [map_add, LinearMap.add_apply, LinearMap.flip_apply, add_smul, smul_add]
      abel)
    (fun c x y => by
      simp only [map_smul, LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul, smul_add,
        smul_smul, mul_comm])
    (fun x y y' => by
      simp only [map_add, LinearMap.add_apply, LinearMap.flip_apply, add_smul, smul_add]
      abel)
    (fun c x y => by
      simp only [map_smul, LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul, smul_add,
        smul_smul, mul_comm])

private theorem wedge_apply (ψ : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (α : Module.Dual (ZMod 2) W)
    (x y z : W) : wedge ψ α x y z = ψ x y * α z + α x * ψ y z + α y * ψ z x := by
  simp [wedge]

private def tau (T : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (e₁ f₁ e₂ f₂ : W) :
    Module.Dual (ZMod 2) W where
  toFun x := T x e₁ f₁ + T x e₂ f₂
  map_add' x y := by simp only [map_add, LinearMap.add_apply]; abel
  map_smul' c x := by simp [mul_add]

private theorem T_eq_wedge (T : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (h1 : ∀ x z, T x x z = 0) (h2 : ∀ x y, T x y y = 0) (h3 : ∀ x y z, T x y z = T y x z)
    {x₀ e₁ f₁ e₂ f₂ : W} {α₀ : Module.Dual (ZMod 2) W} (hα₀ : α₀ x₀ = 1)
    (F : Frame (T x₀) α₀ x₀ e₁ f₁ e₂ f₂) :
    T = wedge (T x₀) (α₀ + tau T e₁ f₁ e₂ f₂) := by
  have hsymm : ∀ x y, T x₀ x y = T x₀ y x := fun x y => trilinear_swap_right T h2 x₀ x y
  have hcyc : ∀ x y z, T x y z = T y z x := fun x y z => by
    rw [h3 x y z, trilinear_swap_right T h2 y x z]
  have hαv : ∀ x, (α₀ + tau T e₁ f₁ e₂ f₂) x = α₀ x + (T x e₁ f₁ + T x e₂ f₂) := fun x => rfl
  have hαx₀ : (α₀ + tau T e₁ f₁ e₂ f₂) x₀ = 1 := by
    rw [hαv, hα₀, F.ψ_e₁f₁, F.ψ_e₂f₂]
    decide
  have hαe₁ : (α₀ + tau T e₁ f₁ e₂ f₂) e₁ = T e₁ e₂ f₂ := by
    rw [hαv, F.α₀_e₁, h1 e₁ f₁, zero_add, zero_add]
  have hαf₁ : (α₀ + tau T e₁ f₁ e₂ f₂) f₁ = T f₁ e₂ f₂ := by
    rw [hαv, F.α₀_f₁, trilinear_swap_right T h2 f₁ e₁ f₁, h1 f₁ e₁, zero_add, zero_add]
  have hαe₂ : (α₀ + tau T e₁ f₁ e₂ f₂) e₂ = T e₁ f₁ e₂ := by
    rw [hαv, F.α₀_e₂, h1 e₂ f₂, hcyc e₂ e₁ f₁, add_zero, zero_add]
  have hαf₂ : (α₀ + tau T e₁ f₁ e₂ f₂) f₂ = T e₁ f₁ f₂ := by
    rw [hαv, F.α₀_f₂, trilinear_swap_right T h2 f₂ e₂ f₂, h1 f₂ e₂, hcyc f₂ e₁ f₁, add_zero,
      zero_add]
  set α := α₀ + tau T e₁ f₁ e₂ f₂
  have hM12 : ∀ x y z, wedge (T x₀) α x y z = wedge (T x₀) α y x z := by
    intro x y z
    simp only [wedge_apply, hsymm y x, hsymm z y, hsymm x z]
    ring
  have hM23 : ∀ x y z, wedge (T x₀) α x y z = wedge (T x₀) α x z y := by
    intro x y z
    simp only [wedge_apply, hsymm x z, hsymm z y, hsymm y x]
    ring
  have hMxx : ∀ x z, wedge (T x₀) α x x z = 0 := by
    intro x z
    simp only [wedge_apply, h2 x₀ x, hsymm z x, zero_mul, zero_add]
    exact zmod2_add_self _
  have hM0 : ∀ y z, wedge (T x₀) α x₀ y z = T x₀ y z := by
    intro y z
    simp only [wedge_apply, h1 x₀ y, hαx₀, trilinear_swap_right T h2 x₀ z x₀, h1 x₀ z]
    ring
  have hs0 : ∀ y z, T x₀ y z - wedge (T x₀) α x₀ y z = 0 := fun y z => by
    rw [hM0, sub_self]
  have hs123 : T e₁ f₁ e₂ - wedge (T x₀) α e₁ f₁ e₂ = 0 := by
    rw [wedge_apply, F.ψ_e₁f₁, F.ψ_f₁e₂, hsymm e₂ e₁, F.ψ_e₁e₂, hαe₂]
    ring
  have hs124 : T e₁ f₁ f₂ - wedge (T x₀) α e₁ f₁ f₂ = 0 := by
    rw [wedge_apply, F.ψ_e₁f₁, F.ψ_f₁f₂, hsymm f₂ e₁, F.ψ_e₁f₂, hαf₂]
    ring
  have hs134 : T e₁ e₂ f₂ - wedge (T x₀) α e₁ e₂ f₂ = 0 := by
    rw [wedge_apply, F.ψ_e₁e₂, F.ψ_e₂f₂, hsymm f₂ e₁, F.ψ_e₁f₂, hαe₁]
    ring
  have hs234 : T f₁ e₂ f₂ - wedge (T x₀) α f₁ e₂ f₂ = 0 := by
    rw [wedge_apply, F.ψ_f₁e₂, F.ψ_e₂f₂, hsymm f₂ f₁, F.ψ_f₁f₂, hαf₁]
    ring
  have hsorted : ∀ i j k : Fin 5, i < j → j < k → i = 0 ∨ (i = 1 ∧ j = 2 ∧ k = 3) ∨
      (i = 1 ∧ j = 2 ∧ k = 4) ∨ (i = 1 ∧ j = 3 ∧ k = 4) ∨ (i = 2 ∧ j = 3 ∧ k = 4) := by
    decide
  let v : Fin 5 → W := ![x₀, e₁, f₁, e₂, f₂]
  have hd : ∀ i j k : Fin 5, T (v i) (v j) (v k) = wedge (T x₀) α (v i) (v j) (v k) := by
    intro i j k
    refine sub_eq_zero.mp (forall_eq_zero_of_sorted
      (fun i j k => T (v i) (v j) (v k) - wedge (T x₀) α (v i) (v j) (v k)) ?_ ?_ ?_ ?_ i j k)
    · intro i j k
      rw [h3, hM12]
    · intro i j k
      rw [trilinear_swap_right T h2 _ _ _, hM23]
    · intro i k
      rw [h1, hMxx, sub_zero]
    · intro i j k hij hjk
      rcases hsorted i j k hij hjk with rfl | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact hs0 _ _
      · exact hs123
      · exact hs124
      · exact hs134
      · exact hs234
  refine LinearMap.ext_on F.span_eq (fun x hx => ?_)
  refine LinearMap.ext_on F.span_eq (fun y hy => ?_)
  refine LinearMap.ext_on F.span_eq (fun z hz => ?_)
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  obtain ⟨k, rfl⟩ := hz
  exact hd i j k

private theorem alpha_x₀ (T : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    {x₀ e₁ f₁ e₂ f₂ : W} {α₀ : Module.Dual (ZMod 2) W} (hα₀ : α₀ x₀ = 1)
    (F : Frame (T x₀) α₀ x₀ e₁ f₁ e₂ f₂) : (α₀ + tau T e₁ f₁ e₂ f₂) x₀ = 1 := by
  change α₀ x₀ + (T x₀ e₁ f₁ + T x₀ e₂ f₂) = 1
  rw [hα₀, F.ψ_e₁f₁, F.ψ_e₂f₂]
  decide

private theorem three_le_finrank_rad [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 5)
    (T : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) {x₀ : W} (α : Module.Dual (ZMod 2) W)
    (hT : ∀ x y z, T x y z = T x₀ x y * α z + α x * T x₀ y z + α y * T x₀ z x) {x : W}
    (hx : α x = 0) : 3 ≤ finrank (ZMod 2) (rad T x) := by
  have hK : LinearMap.ker (LinearMap.prod α (T x₀ x)) ≤ rad T x := by
    intro y hy
    rw [LinearMap.ker_prod, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [mem_rad]
    intro z
    rw [hT, hx, hy1, hy2]
    simp
  have h3 := three_le_finrank_ker_prod hW α (T x₀ x)
  have := Submodule.finrank_mono hK
  omega

private theorem finrank_rad_eq_one [FiniteDimensional (ZMod 2) W]
    (T : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) {x₀ : W} (α : Module.Dual (ZMod 2) W)
    (hT : ∀ x y z, T x y z = T x₀ x y * α z + α x * T x₀ y z + α y * T x₀ z x)
    (h1 : ∀ x z, T x x z = 0) (h2 : ∀ x y, T x y y = 0)
    (hker : LinearMap.ker (T x₀) = Submodule.span (ZMod 2) {x₀}) (hαx₀ : α x₀ = 1) {x : W}
    (hx : α x = 1) : finrank (ZMod 2) (rad T x) = 1 := by
  apply le_antisymm
  · have hinj : Function.Injective (α.domRestrict (rad T x)) := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      have hy0 : α (y : W) = 0 := hy
      have hyrad : ∀ z, T x y z = 0 := mem_rad.mp y.2
      have hz' : ∀ z, α z = 0 → T x₀ y z = 0 := by
        intro z hz
        have h := hyrad z
        rw [hT, hx, hy0, hz] at h
        simpa using h
      have hall : ∀ z, T x₀ y z = 0 := by
        intro z
        have h3 : T x₀ y z = α z * T x₀ y x₀ + T x₀ y (z - α z • x₀) := by
          have : z = α z • x₀ + (z - α z • x₀) := by abel
          conv_lhs => rw [this]
          rw [map_add, map_smul, smul_eq_mul]
        have h4 : T x₀ y x₀ = 0 := by rw [trilinear_swap_right T h2, h1]
        have h5 : α (z - α z • x₀) = 0 := by
          rw [map_sub, map_smul, hαx₀, smul_eq_mul, mul_one, sub_self]
        rw [h3, h4, mul_zero, zero_add]
        exact hz' _ h5
      have hmem : (y : W) ∈ LinearMap.ker (T x₀) := LinearMap.mem_ker.mpr (LinearMap.ext hall)
      rw [hker, Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      rw [← hc, map_smul, hαx₀, smul_eq_mul, mul_one] at hy0
      apply Subtype.ext
      rw [← hc, hy0, zero_smul]
      rfl
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  · rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro hbot
    have hxrad : x ∈ rad T x := mem_rad.mpr (h1 x)
    rw [hbot, Submodule.mem_bot] at hxrad
    rw [hxrad, map_zero] at hx
    exact zero_ne_one hx

theorem exists_hyperplane_of_trilinear {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 5)
    (T : W →ₗ[ZMod 2] W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (h1 : ∀ x z, T x x z = 0) (h2 : ∀ x y, T x y y = 0) (h3 : ∀ x y z, T x y z = T y x z)
    {x₀ : W} (h0 : finrank (ZMod 2) (rad T x₀) = 1) :
    ∃ α : Module.Dual (ZMod 2) W, α x₀ = 1 ∧ ∀ x, (α x = 0 → 3 ≤ finrank (ZMod 2) (rad T x)) ∧
      (α x = 1 → finrank (ZMod 2) (rad T x) = 1) := by
  have hx₀ : x₀ ≠ 0 := by
    rintro rfl
    rw [rad, map_zero, LinearMap.ker_zero, finrank_top, hW] at h0
    omega
  have hker : LinearMap.ker (T x₀) = Submodule.span (ZMod 2) {x₀} := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact LinearMap.ext (h1 x₀)
    · rw [finrank_span_singleton hx₀]
      exact h0.symm
  obtain ⟨α₀, hα₀⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hx₀
  obtain ⟨e₁, f₁, e₂, f₂, F⟩ := exists_frame hW (T x₀) (fun x y => trilinear_swap_right T h2 x₀ x y)
    (fun x => h2 x₀ x) hker α₀ hα₀
  have hT := T_eq_wedge T h1 h2 h3 hα₀ F
  have hαx₀ := alpha_x₀ T hα₀ F
  have hTapp : ∀ x y z, T x y z = T x₀ x y * (α₀ + tau T e₁ f₁ e₂ f₂) z +
      (α₀ + tau T e₁ f₁ e₂ f₂) x * T x₀ y z + (α₀ + tau T e₁ f₁ e₂ f₂) y * T x₀ z x :=
    fun x y z => by rw [← wedge_apply, ← hT]
  exact ⟨α₀ + tau T e₁ f₁ e₂ f₂, hαx₀, fun x =>
    ⟨fun hx => three_le_finrank_rad hW T _ hTapp hx,
      fun hx => finrank_rad_eq_one T _ hTapp h1 h2 hker hαx₀ hx⟩⟩

end CFSG.GF2Type.Smith1979.Case2
