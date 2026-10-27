module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructLin
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

abbrev eig (g : V ≃ₗ[K] V) (μ : K) : Submodule K V :=
  Module.End.eigenspace (g : V →ₗ[K] V) μ

theorem mem_eig_iff {g : V ≃ₗ[K] V} {μ : K} {v : V} : v ∈ eig g μ ↔ g v = μ • v :=
  Module.End.mem_eigenspace_iff

theorem pow_three_apply {g : V ≃ₗ[K] V} {μ : K} {v : V} (hv : g v = μ • v) :
    (g ^ 3) v = μ ^ 3 • v := by
  rw [LinearEquiv.pow_apply]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  simp only [hv, map_smul, smul_smul, pow_three']

theorem exists_omega [Finite K] (hK : Nat.card K = 4) {g h : V ≃ₗ[K] V}
    (hs : ⁅g, h⁆ ∈ scalars K V) (hne : g * h ≠ h * g) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ∀ v, g (h v) = ω • h (g v) := by
  obtain ⟨c, hc⟩ := mem_scalars_iff.1 hs
  refine ⟨(c : K), ?_, ?_, ?_⟩
  · have h2 := congrArg (fun u : Kˣ => (u : K)) (units_pow_three hK c)
    simpa using h2
  · intro h1
    apply hne
    apply commutatorElement_eq_one_iff_mul_comm.1
    refine LinearEquiv.ext fun v => ?_
    rw [hc v, h1, one_smul]
    rfl
  · intro v
    have e : g * h = ⁅g, h⁆ * (h * g) := by rw [commutatorElement_def]; group
    have := congrArg (fun e : V ≃ₗ[K] V => e v) e
    simp only [LinearEquiv.mul_apply] at this
    rw [this, hc]

theorem h_mem_eig {g h : V ≃ₗ[K] V} {ω : K} (hω : ∀ v, g (h v) = ω • h (g v)) {μ : K} {v : V}
    (hv : v ∈ eig g μ) : h v ∈ eig g (ω * μ) := by
  rw [mem_eig_iff] at hv ⊢
  rw [hω, hv, map_smul, smul_smul]

theorem hsymm_mem_eig {g h : V ≃ₗ[K] V} {ω : K} (hω : ∀ v, g (h v) = ω • h (g v)) (hω0 : ω ≠ 0)
    {μ : K} {v : V} (hv : v ∈ eig g (ω * μ)) : h.symm v ∈ eig g μ := by
  rw [mem_eig_iff] at hv ⊢
  have h1 := hω (h.symm v)
  rw [LinearEquiv.apply_symm_apply, hv] at h1
  have h2 : h (g (h.symm v)) = μ • v := by
    have h3 : ω • h (g (h.symm v)) = ω • (μ • v) := by rw [← h1, smul_smul]
    exact smul_right_injective V hω0 h3
  calc g (h.symm v) = h.symm (h (g (h.symm v))) := by simp
    _ = h.symm (μ • v) := by rw [h2]
    _ = μ • h.symm v := map_smul _ _ _

theorem isPrimitiveRoot_of_pow_three {ω : K} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    IsPrimitiveRoot ω 3 := by
  have := IsPrimitiveRoot.orderOf ω
  rwa [orderOf_eq_prime h3 h1] at this

theorem omega_facts {ω : K} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    ω ≠ 0 ∧ ω ^ 2 ≠ 1 ∧ ω ≠ ω ^ 2 := by
  have h0 : ω ≠ 0 := by
    rintro rfl
    simp at h3
  refine ⟨h0, ?_, ?_⟩
  · intro h
    apply h1
    have : ω ^ 3 = ω ^ 2 * ω := pow_succ ω 2
    rw [h3, h, one_mul] at this
    exact this.symm
  · intro h
    apply h1
    have h2 : ω * ω = ω * 1 := by rw [mul_one, ← sq]; exact h.symm
    exact mul_left_cancel₀ h0 h2

theorem exists_eig_decomp {g : V ≃ₗ[K] V} (hg3 : g ^ 3 = 1) {ω : K} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (w : V) :
    ∃ a b d : V, a ∈ eig g 1 ∧ b ∈ eig g ω ∧ d ∈ eig g (ω ^ 2) ∧ w = a + b + d := by
  have hprim : IsPrimitiveRoot ω 3 := isPrimitiveRoot_of_pow_three hω3 hω1
  have hf : (g : V →ₗ[K] V) ^ 3 = 1 := by
    ext v
    have := congrArg (fun e : V ≃ₗ[K] V => e v) hg3
    simpa [LinearEquiv.pow_apply, Module.End.pow_apply] using this
  have htop := CFSG.RankThree.PartOne.iSup_eigenspace_eq_top_of_pow_eq_one hprim hf
  have hle : (⨆ μ, Module.End.eigenspace (g : V →ₗ[K] V) μ) ≤
      eig g 1 ⊔ eig g ω ⊔ eig g (ω ^ 2) := by
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ^ 3 = 1
    · obtain ⟨i, hi, rfl⟩ := hprim.eq_pow_of_pow_eq_one hμ
      interval_cases i
      · rw [pow_zero]; exact le_sup_of_le_left le_sup_left
      · rw [pow_one]; exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · intro v hv
      have hv' : g v = μ • v := mem_eig_iff.1 hv
      have h3 : (g ^ 3) v = v := by rw [hg3]; rfl
      rw [pow_three_apply hv'] at h3
      have h4 : (μ ^ 3 - 1) • v = 0 := by rw [sub_smul, h3, one_smul, sub_self]
      rcases smul_eq_zero.1 h4 with h | h
      · exact absurd (sub_eq_zero.1 h) hμ
      · rw [h]; exact Submodule.zero_mem _
  have hw : w ∈ eig g 1 ⊔ eig g ω ⊔ eig g (ω ^ 2) := hle (htop ▸ Submodule.mem_top)
  obtain ⟨x, hx, d, hd, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  exact ⟨a, b, d, ha, hb, hd, rfl⟩

theorem three_mul_finrank_eig_le [FiniteDimensional K V] {g h : V ≃ₗ[K] V} {ω : K}
    (hω : ∀ v, g (h v) = ω • h (g v)) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    3 * Module.finrank K (eig g 1) ≤ Module.finrank K V := by
  classical
  obtain ⟨hω0, hω21, hωω2⟩ := omega_facts hω3 hω1
  let Φ : (eig g 1) × ((eig g 1) × (eig g 1)) →ₗ[K] V :=
    (eig g 1).subtype.coprod (((h : V →ₗ[K] V).comp (eig g 1).subtype).coprod
      (((h ^ 2 : V ≃ₗ[K] V) : V →ₗ[K] V).comp (eig g 1).subtype))
  have hΦ : ∀ x : (eig g 1) × ((eig g 1) × (eig g 1)),
      Φ x = (x.1 : V) + h (x.2.1 : V) + h (h (x.2.2 : V)) := by
    intro x
    simp [Φ, pow_two, add_assoc]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b, d⟩ hz
    rw [hΦ] at hz
    simp only at hz
    have hind := Module.End.eigenspaces_iSupIndep (g : V →ₗ[K] V)
    rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hind
    have hb' : h (b : V) ∈ eig g ω := by
      have := h_mem_eig hω (show (b : V) ∈ eig g 1 from b.2)
      rwa [mul_one] at this
    have hd' : h (h (d : V)) ∈ eig g (ω ^ 2) := by
      have := h_mem_eig hω (h_mem_eig hω (show (d : V) ∈ eig g 1 from d.2))
      rwa [mul_one, ← sq] at this
    have key := hind {1, ω, ω ^ 2}
      (fun μ => if μ = 1 then (a : V) else if μ = ω then h (b : V) else h (h (d : V)))
      (by
        intro μ hμ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hμ
        rcases hμ with rfl | rfl | rfl
        · simp only [if_true]; exact a.2
        · simp only [hω1, if_false, if_true]; exact hb'
        · simp only [hω21, hωω2.symm, if_false]; exact hd')
      (by
        rw [Finset.sum_insert (by simp [hω1.symm, hω21.symm]),
          Finset.sum_insert (by simp [hωω2]), Finset.sum_singleton]
        simp only [if_true, hω1, if_false, hω21, hωω2.symm]
        rw [← add_assoc]
        exact hz)
    have h1 := key 1 (by simp)
    have h2 := key ω (by simp)
    have h3 := key (ω ^ 2) (by simp)
    simp only [if_true, hω1, if_false, hω21, hωω2.symm] at h1 h2 h3
    have hb0 : (b : V) = 0 := by
      have : h.symm (h (b : V)) = h.symm 0 := by rw [h2]
      simpa using this
    have hd0 : (d : V) = 0 := by
      have : h.symm (h.symm (h (h (d : V)))) = h.symm (h.symm 0) := by rw [h3]
      simpa using this
    ext <;> simp [h1, hb0, hd0]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, Module.finrank_prod] at this
  omega

theorem eq_one_of_fix_eig {g h c : V ≃ₗ[K] V} {ω : K} (hg3 : g ^ 3 = 1)
    (hω : ∀ v, g (h v) = ω • h (g v)) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hch : c * h = h * c) (hfix : ∀ u ∈ eig g 1, c u = u) : c = 1 := by
  obtain ⟨hω0, -, -⟩ := omega_facts hω3 hω1
  refine LinearEquiv.ext fun w => ?_
  obtain ⟨a, b, d, ha, hb, hd, rfl⟩ := exists_eig_decomp hg3 hω3 hω1 w
  have hc : ∀ v, c (h v) = h (c v) := fun v => by
    have := congrArg (fun e : V ≃ₗ[K] V => e v) hch
    simpa using this
  have hb1 : h.symm b ∈ eig g 1 := hsymm_mem_eig hω hω0 (by rwa [mul_one])
  have hd1 : h.symm d ∈ eig g ω := hsymm_mem_eig hω hω0 (by rwa [← sq])
  have hd2 : h.symm (h.symm d) ∈ eig g 1 := hsymm_mem_eig hω hω0 (by rwa [mul_one])
  have hcb : c b = b := by
    have := hc (h.symm b)
    rwa [LinearEquiv.apply_symm_apply, hfix _ hb1, LinearEquiv.apply_symm_apply] at this
  have hcd : c d = d := by
    have h1 := hc (h.symm d)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 := hc (h.symm (h.symm d))
    rw [LinearEquiv.apply_symm_apply, hfix _ hd2, LinearEquiv.apply_symm_apply] at h2
    rw [h1, h2]
    simp
  show c (a + b + d) = a + b + d
  simp only [map_add, hfix a ha, hcb, hcd]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

end
