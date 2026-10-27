module

public import CFSG.LieType.SeitzGeneration.OrthGenLinear
public import CFSG.LieType.SeitzGeneration.OrthCommutator

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem eichler_sub_self {x z m : V} (hx : Q x = 0) (hxz : polar Q x z = 0) :
    eichler Q x z m - m = polar Q m x • z - (polar Q m z + Q z * polar Q m x) • x := by
  rw [eichler_apply hx hxz]
  abel

omit [Finite K] [FiniteDimensional K V] in
theorem smul_mem_of_hyperbolic {A : Submodule K V} (M : AddSubgroup V)
    (hinv : ∀ x ∈ A, ∀ z ∈ A, Q x = 0 → polar Q x z = 0 → ∀ m ∈ M, m ∈ A → eichler Q x z m ∈ M)
    {e f z₀ z₁ : V} (heA : e ∈ A) (hfA : f ∈ A) (heM : e ∈ M) (hfQ : Q f = 0)
    (hef : polar Q e f = 1) (hz₀A : z₀ ∈ A) (hz₁A : z₁ ∈ A) (hz₀e : polar Q e z₀ = 0)
    (hz₀f : polar Q f z₀ = 0) (hz₁e : polar Q e z₁ = 0) (hz₁f : polar Q f z₁ = 0)
    (hm : polar Q z₀ z₁ ≠ 0) (c : K) : c • f ∈ M := by
  have hμ : ∀ z ∈ A, polar Q e z = 0 → polar Q f z = 0 → z - Q z • f ∈ M := by
    intro z hzA hze hzf
    have h1 := M.sub_mem (hinv f hfA z hzA hfQ hzf e heM heA) heM
    have h2 := eichler_sub_self (m := e) hfQ hzf
    rw [h2, hef, hze, one_smul] at h1
    simpa using h1
  have hc := M.sub_mem (M.sub_mem (hμ ((c / polar Q z₀ z₁) • z₀ + z₁)
    (A.add_mem (A.smul_mem _ hz₀A) hz₁A)
    (by rw [polar_add_right, polar_smul_right_eq, hz₀e, hz₁e]; ring)
    (by rw [polar_add_right, polar_smul_right_eq, hz₀f, hz₁f]; ring))
    (hμ ((c / polar Q z₀ z₁) • z₀) (A.smul_mem _ hz₀A)
      (by rw [polar_smul_right_eq, hz₀e]; ring) (by rw [polar_smul_right_eq, hz₀f]; ring)))
    (hμ z₁ hz₁A hz₁e hz₁f)
  have hcalc : ((c / polar Q z₀ z₁) • z₀ + z₁ - Q ((c / polar Q z₀ z₁) • z₀ + z₁) • f) -
      ((c / polar Q z₀ z₁) • z₀ - Q ((c / polar Q z₀ z₁) • z₀) • f) - (z₁ - Q z₁ • f) =
      (-c) • f := by
    rw [QuadraticMap.map_add Q, polar_smul_left_eq]
    have : (c / polar Q z₀ z₁) * polar Q z₀ z₁ = c := div_mul_cancel₀ c hm
    rw [this]
    module
  rw [hcalc] at hc
  simpa using M.neg_mem hc

omit [Finite K] in
theorem exists_orth_pair {A : Submodule K V} (hA : PolarNondegOn Q A) (h3 : 3 ≤ finrank K A)
    {e f : V} (heA : e ∈ A) (hfA : f ∈ A) (hee : Q e = 0) (hff : Q f = 0)
    (hef : polar Q e f = 1) : ∃ z₀ z₁, z₀ ∈ A ∧ z₁ ∈ A ∧ polar Q e z₀ = 0 ∧ polar Q f z₀ = 0 ∧
      polar Q e z₁ = 0 ∧ polar Q f z₁ = 0 ∧ polar Q z₀ z₁ ≠ 0 := by
  classical
  obtain ⟨z₀, hz₀A, hz₀0, hz₀e, hz₀f⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.exists_mem_orth_two Q h3 e f
  obtain ⟨a, haA, ha⟩ := hA.exists_polar_ne_zero hz₀A hz₀0
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  have hee' : polar Q e e = 0 := polar_self_eq_zero hee
  have hff' : polar Q f f = 0 := polar_self_eq_zero hff
  refine ⟨z₀, a - polar Q a f • e - polar Q a e • f, hz₀A, A.sub_mem (A.sub_mem haA
    (A.smul_mem _ heA)) (A.smul_mem _ hfA), hz₀e, hz₀f, ?_, ?_, ?_⟩
  · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hee', hef,
      polar_comm Q e a]
    ring
  · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hfe, hff',
      polar_comm Q f a]
    ring
  · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q z₀ e, polar_comm Q z₀ f, hz₀e, hz₀f]
    simpa using ha

theorem mem_of_invariant_of_ne_zero {A : Submodule K V} (hA : PolarNondegOn Q A)
    (h4 : 4 ≤ finrank K A) (M : AddSubgroup V)
    (hinv : ∀ x ∈ A, ∀ z ∈ A, Q x = 0 → polar Q x z = 0 → ∀ m ∈ M, m ∈ A → eichler Q x z m ∈ M)
    {y : V} (hyM : y ∈ M) (hyA : y ∈ A) (hy0 : y ≠ 0) : ∀ a ∈ A, a ∈ M := by
  classical
  obtain ⟨x, hxA, hxM, hx0, hxQ⟩ : ∃ x ∈ A, x ∈ M ∧ x ≠ 0 ∧ Q x = 0 := by
    by_cases hQy : Q y = 0
    · exact ⟨y, hyA, hyM, hy0, hQy⟩
    obtain ⟨x, hxA, hx0, hxQ, hxF⟩ := exists_singular_in_kernel_fin (Q := Q) (n := 1) (S := A)
      (by omega) ![(polarBilin Q).flip y]
    have hxy : polar Q x y = 0 := by simpa [polarBilin_apply_apply] using hxF 0
    have hind : ∀ c : K, y ≠ c • x := by
      intro c hc
      apply hQy
      rw [hc, map_smul_eq_sq, hxQ, mul_zero]
    obtain ⟨z, hzA, hzx, hzy⟩ := exists_perp_not_perp hA hyA hxA hind
    have hyx : polar Q y x = 0 := by rw [polar_comm, hxy]
    obtain ⟨c, hc⟩ : ∃ c : K, c = -(polar Q z y)⁻¹ := ⟨_, rfl⟩
    have hcz : c * polar Q z y = -1 := by
      rw [hc, neg_mul, inv_mul_cancel₀ hzy]
    have hxz : polar Q x (c • z) = 0 := by
      rw [polar_smul_right_eq, polar_comm Q x z, hzx, mul_zero]
    have h1 := M.sub_mem (hinv x hxA (c • z) (A.smul_mem _ hzA) hxQ hxz y hyM hyA) hyM
    have key : eichler Q x (c • z) y - y = x := by
      rw [eichler_sub_self hxQ hxz, hyx, polar_smul_right_eq, polar_comm Q y z, hcz]
      module
    rw [key] at h1
    exact ⟨x, hxA, h1, hx0, hxQ⟩
  obtain ⟨f, hfA, hfQ, hxf⟩ := exists_partner_of_polarNondegOn hA hxA hxQ hx0
  have hfx : polar Q f x = 1 := by rw [polar_comm, hxf]
  have hxx : polar Q x x = 0 := polar_self_eq_zero hxQ
  have hff : polar Q f f = 0 := polar_self_eq_zero hfQ
  obtain ⟨z₀, z₁, hz₀A, hz₁A, hz₀x, hz₀f, hz₁x, hz₁f, hm⟩ :=
    exists_orth_pair hA (by omega) hxA hfA hxQ hfQ hxf
  have hKf : ∀ c : K, c • f ∈ M :=
    smul_mem_of_hyperbolic M hinv hxA hfA hxM hfQ hxf hz₀A hz₁A hz₀x hz₀f hz₁x hz₁f hm
  have hfM : f ∈ M := by simpa using hKf 1
  have hKx : ∀ c : K, c • x ∈ M :=
    smul_mem_of_hyperbolic M hinv hfA hxA hfM hxQ hfx hz₀A hz₁A hz₀f hz₀x hz₁f hz₁x hm
  intro a haA
  obtain ⟨z, hz⟩ : ∃ z : V, z = a - polar Q a f • x - polar Q a x • f := ⟨_, rfl⟩
  have hzA : z ∈ A := by
    rw [hz]
    exact A.sub_mem (A.sub_mem haA (A.smul_mem _ hxA)) (A.smul_mem _ hfA)
  have hzx : polar Q x z = 0 := by
    rw [hz, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hxx, hxf,
      polar_comm Q x a]
    ring
  have hzf : polar Q f z = 0 := by
    rw [hz, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hfx, hff,
      polar_comm Q f a]
    ring
  have hzM : z ∈ M := by
    have h1 := M.sub_mem (hinv f hfA z hzA hfQ hzf x hxM hxA) hxM
    rw [eichler_sub_self hfQ hzf, hxf, hzx] at h1
    have h2 := M.add_mem h1 (hKf (Q z))
    simpa using h2
  have hdec : a = polar Q a f • x + polar Q a x • f + z := by
    rw [hz]
    abel
  rw [hdec]
  exact M.add_mem (M.add_mem (hKx _) (hKf _)) hzM

end CFSG.LieType.SeitzGeneration.OrthBlk
