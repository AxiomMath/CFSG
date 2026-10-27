module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Star
public import CFSG.ClassicalInvolution.RouteD.TWEB6Bridge
public import CFSG.ClassicalInvolution.RouteD.GapsFrBEigen
public import CFSG.ClassicalInvolution.RouteD.GapsFrSpin

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.ModelFacts (plusSp minusSp isCompl_plusSp_minusSp mem_plusSp)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Sign

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem sign_of_commute (h2 : (2 : K) ≠ 0) {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}
    (hL : IsFundamental Q L i) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hcomm : ∀ l ∈ L, g * l = l * g) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ x ∈ negSpace i, g x = ε • x := by
  rcases negSpace_le_eigenspace_of_commute h2 hL hgO hg2 hcomm with h | h
  · refine ⟨1, Or.inl rfl, fun x hx => ?_⟩
    have := h hx
    rw [Module.End.mem_eigenspace_iff] at this
    exact this
  · refine ⟨-1, Or.inr rfl, fun x hx => ?_⟩
    have := h hx
    rw [Module.End.mem_eigenspace_iff] at this
    exact this

theorem sign_mul_eq_one {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {a b : K} {x y : V} (hx : g x = a • x) (hy : g y = b • y) (hxy : polar Q x y ≠ 0) :
    a * b = 1 := by
  have h := polar_map_of_mem hgO x y
  rw [hx, hy, polar_smul_left_eq, polar_smul_right_eq] at h
  have h' : (a * b - 1) * polar Q x y = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h1
  · linear_combination h1
  · exact absurd h1 hxy

theorem exists_polar_ne_of_not_commutes (h2 : (2 : K) ≠ 0) {L L' : Subgroup (V ≃ₗ[K] V)}
    {i i' : V ≃ₗ[K] V} (hL : IsFundamental Q L i) (hL' : IsFundamental Q L' i')
    (h : ¬ Commutes L L') : ∃ x ∈ negSpace i, ∃ y ∈ negSpace i', polar Q x y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨F, rfl, rfl⟩ := hL
  obtain ⟨F', rfl, rfl⟩ := hL'
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at hcon
  exact h (commutes_of_span_orth F F' hcon)

theorem negSpace_ne_of_not_commutes (hodd : Odd (Nat.card K)) {S₁ S₂ : Subgroup (V ≃ₗ[K] V)}
    {s₁ s₂ : V ≃ₗ[K] V} (h₁ : IsFundamental Q S₁ s₁) (h₂ : IsFundamental Q S₂ s₂)
    (hne : S₁ ≠ S₂) (hnc : ¬ Commutes S₁ S₂) : negSpace s₁ ≠ negSpace s₂ := by
  intro h
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hs : s₂ = s₁ := by
    obtain ⟨F₁, -, rfl⟩ := h₁
    obtain ⟨F₂, -, rfl⟩ := h₂
    rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at h
    exact Frame.La_neg_one_eq_of_span_eq h.symm
  subst hs
  obtain ⟨L', -, -, hcomm, huniq⟩ := IsFundamental.exists_twin hodd h₁
  rcases huniq S₂ h₂ with h3 | h3
  · exact hne h3.symm
  · exact hnc (fun x hx y hy => hcomm x hx y (h3 ▸ hy))

theorem polar_zero_of_mem_sup {A B₁ B₂ : Submodule K V}
    (h1 : ∀ x ∈ A, ∀ y ∈ B₁, polar Q x y = 0) (h2 : ∀ x ∈ A, ∀ y ∈ B₂, polar Q x y = 0) :
    ∀ x ∈ A, ∀ y ∈ B₁ ⊔ B₂, polar Q x y = 0 := by
  intro x hx y hy
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hy
  rw [polar_add_right, h1 x hx b₁ hb₁, h2 x hx b₂ hb₂, add_zero]

theorem orth_of_commutes_two (hodd : Odd (Nat.card K)) {pr : ℕ → HypPair Q}
    (horth : ∀ a b, a < 3 → b < 3 → a ≠ b → (pr a).Orth (pr b))
    {L₀ L₁ S : Subgroup (V ≃ₗ[K] V)} {i₀ i₁ s : V ≃ₗ[K] V} (h₀ : IsFundamental Q L₀ i₀)
    (h₁ : IsFundamental Q L₁ i₁) (hS : IsFundamental Q S s)
    (n₀ : negSpace i₀ = hypPlane (pr 0) ⊔ hypPlane (pr 1))
    (n₁ : negSpace i₁ = hypPlane (pr 1) ⊔ hypPlane (pr 2))
    (c₀ : Commutes S L₀) (c₁ : Commutes S L₁) :
    (∀ x ∈ negSpace s, ∀ y ∈ negSpace i₀, polar Q x y = 0) ∧
      ∀ x ∈ negSpace s, ∀ y ∈ negSpace i₁, polar Q x y = 0 := by
  have o01 : (pr 0).Orth (pr 1) := horth 0 1 (by norm_num) (by norm_num) (by norm_num)
  have o02 : (pr 0).Orth (pr 2) := horth 0 2 (by norm_num) (by norm_num) (by norm_num)
  have e1A : (pr 1).e ∈ negSpace i₀ := n₀ ▸ Submodule.mem_sup_right (e_mem_hypPlane (pr 1))
  have f1A : (pr 1).f ∈ negSpace i₀ := n₀ ▸ Submodule.mem_sup_right (f_mem_hypPlane (pr 1))
  have e1B : (pr 1).e ∈ negSpace i₁ := n₁ ▸ Submodule.mem_sup_left (e_mem_hypPlane (pr 1))
  have f1B : (pr 1).f ∈ negSpace i₁ := n₁ ▸ Submodule.mem_sup_left (f_mem_hypPlane (pr 1))
  have e0A : (pr 0).e ∈ negSpace i₀ := n₀ ▸ Submodule.mem_sup_left (e_mem_hypPlane (pr 0))
  have f0A : (pr 0).f ∈ negSpace i₀ := n₀ ▸ Submodule.mem_sup_left (f_mem_hypPlane (pr 0))
  have hne1 : polar Q (pr 1).e (pr 1).f ≠ 0 := by rw [(pr 1).polar_ef]; exact one_ne_zero
  have hne0 : polar Q (pr 0).e (pr 0).f ≠ 0 := by rw [(pr 0).polar_ef]; exact one_ne_zero
  have e0perp : ∀ y ∈ negSpace i₁, polar Q (pr 0).e y = 0 := by
    intro y hy
    rw [n₁] at hy
    exact polar_zero_of_mem_sup (A := hypPlane (pr 0)) (fun x hx y hy => polar_hypPlane_of_orth
      o01 x hx y hy) (fun x hx y hy => polar_hypPlane_of_orth o02 x hx y hy) _ (e_mem_hypPlane _)
      y hy
  rcases orth_or_twin hodd hS h₀ c₀ with o₀ | t₀ <;> rcases orth_or_twin hodd hS h₁ c₁ with o₁ | t₁
  · exact ⟨o₀, o₁⟩
  · exfalso
    have hs : negSpace s = negSpace i₁ := by rw [t₁]
    exact hne1 (o₀ _ (hs ▸ e1B) _ f1A)
  · exfalso
    have hs : negSpace s = negSpace i₀ := by rw [t₀]
    exact hne1 (o₁ _ (hs ▸ e1A) _ f1B)
  · exfalso
    have h01 : i₀ = i₁ := t₀.trans t₁.symm
    exact hne0 (e0perp _ (h01 ▸ f0A))

end Sign

section Perp

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem commute_of_scalar_on_perp (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {g₀ h : V ≃ₗ[K] V} (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {ε : K} (hε : ε * ε = 1)
    (hperp : ∀ y ∈ P.perp, g₀ y = ε • y) (hfix : ∀ q ∈ hypPlane P, h q = q) :
    g₀ * h = h * g₀ := by
  have hε0 : ε ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hε
    exact zero_ne_one hε
  have hpq : ∀ q ∈ hypPlane P, ∀ y ∈ P.perp, polar Q q y = 0 := by
    intro q hq y hy
    obtain ⟨a, b, rfl⟩ := (mem_hypPlane_iff P).mp hq
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, (HypPair.mem_perp.mp hy).1,
      (HypPair.mem_perp.mp hy).2]
    ring
  have hgq : ∀ q ∈ hypPlane P, g₀ q ∈ hypPlane P := by
    intro q hq
    have hgperp : ∀ y' ∈ P.perp, polar Q (g₀ q) y' = 0 := by
      intro y' hy'
      have e1 := polar_map_of_mem hg₀O q y'
      rw [hperp y' hy', polar_smul_right_eq, hpq q hq y' hy'] at e1
      exact (mul_eq_zero.mp e1).resolve_left hε0
    have hw : P.proj (g₀ q) = 0 := by
      apply eq_zero_of_polar_eq_zero hQ
      intro x
      have hw' := HypPair.mem_perp.mp (P.proj_mem_perp (g₀ q))
      have hpy : polar Q (P.proj (g₀ q)) (P.proj x) = 0 := by
        rw [HypPair.proj, polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq,
          hgperp _ (P.proj_mem_perp x), (HypPair.mem_perp.mp (P.proj_mem_perp x)).1,
          (HypPair.mem_perp.mp (P.proj_mem_perp x)).2]
        ring
      have key : polar Q (P.proj (g₀ q)) x = polar Q (P.proj (g₀ q))
          (polar Q x P.f • P.e + polar Q x P.e • P.f + P.proj x) :=
        congrArg (polar Q (P.proj (g₀ q))) (P.eq_add_proj x)
      rw [key, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm Q (P.proj (g₀ q)) P.e, polar_comm Q (P.proj (g₀ q)) P.f, hw'.1, hw'.2, hpy]
      ring
    have hdec := P.eq_add_proj (g₀ q)
    rw [hw, add_zero] at hdec
    exact (mem_hypPlane_iff P).mpr ⟨_, _, hdec⟩
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨q, y, hqmem, hymem, hv⟩ : ∃ q y : V, q ∈ hypPlane P ∧ y ∈ P.perp ∧ v = q + y :=
    ⟨polar Q v P.f • P.e + polar Q v P.e • P.f, P.proj v, (mem_hypPlane_iff P).mpr ⟨_, _, rfl⟩,
      P.proj_mem_perp v, P.eq_add_proj v⟩
  subst hv
  have hhy : h y ∈ P.perp := by
    have e1 := polar_map_of_mem hhO P.e y
    have e2 := polar_map_of_mem hhO P.f y
    rw [hfix _ (e_mem_hypPlane P)] at e1
    rw [hfix _ (f_mem_hypPlane P)] at e2
    rw [HypPair.mem_perp] at hymem ⊢
    exact ⟨e1.trans hymem.1, e2.trans hymem.2⟩
  calc (g₀ * h) (q + y) = g₀ q + ε • h y := by
        rw [LinearEquiv.mul_apply, map_add, hfix q hqmem, map_add, hperp _ hhy]
    _ = h (g₀ q) + h (ε • y) := by rw [hfix _ (hgq q hqmem), map_smul]
    _ = (h * g₀) (q + y) := by
        rw [LinearEquiv.mul_apply, map_add, map_add, hperp y hymem]

end Perp

section Helpers

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem sign_eq {a b : K} (hb : b = 1 ∨ b = -1) (h : a * b = 1) : a = b := by
  rcases hb with rfl | rfl
  · simpa using h
  · linear_combination -h

theorem polar_eigen_orth (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a : K} (ha : a * a = 1) {x y : V}
    (hx : g x = a • x) (hy : g y = (-a) • y) : polar Q x y = 0 := by
  have h := polar_map_of_mem hgO x y
  rw [hx, hy, polar_smul_left_eq, polar_smul_right_eq] at h
  have h' : (2 : K) * polar Q x y = 0 := by
    linear_combination (-1 : K) * h - polar Q x y * ha
  exact (mul_eq_zero.mp h').resolve_left h2

theorem exists_eigen_decomp (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V} (hg2 : g * g = 1) {a : K}
    (ha : a * a = 1) (v : V) :
    ∃ e n : V, g e = a • e ∧ g n = (-a) • n ∧ v = e + n := by
  have hgg : ∀ x, g (g x) = x := fun x => by
    have := LinearEquiv.congr_fun hg2 x
    simpa using this
  have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  refine ⟨(2 : K)⁻¹ • (v + a • g v), (2 : K)⁻¹ • (v - a • g v), ?_, ?_, ?_⟩
  · have e1 : g ((2 : K)⁻¹ • (v + a • g v)) = (2 : K)⁻¹ • (g v + a • v) := by
      simp only [map_smul, map_add, hgg]
    rw [e1]
    match_scalars <;> first | ring1 | linear_combination (-(2 : K)⁻¹) * ha
  · have e1 : g ((2 : K)⁻¹ • (v - a • g v)) = (2 : K)⁻¹ • (g v - a • v) := by
      simp only [map_smul, map_sub, hgg]
    rw [e1]
    match_scalars <;> first | ring1 | linear_combination (-(2 : K)⁻¹) * ha
  · rw [← smul_add]
    have : v + a • g v + (v - a • g v) = (2 : K) • v := by module
    rw [this, smul_smul, h22, one_smul]

theorem polar_zero_sup_of_perp {P₁ P₂ : HypPair Q} {z : V} (h₁ : z ∈ P₁.perp) (h₂ : z ∈ P₂.perp) :
    ∀ y ∈ hypPlane P₁ ⊔ hypPlane P₂, polar Q z y = 0 := by
  have key : ∀ (P : HypPair Q), z ∈ P.perp → ∀ y ∈ hypPlane P, polar Q z y = 0 := by
    intro P hz y hy
    obtain ⟨a, b, rfl⟩ := (mem_hypPlane_iff P).mp hy
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_comm Q z P.e,
      polar_comm Q z P.f, (HypPair.mem_perp.mp hz).1, (HypPair.mem_perp.mp hz).2]
    ring
  intro y hy
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hy
  rw [polar_add_right, key P₁ h₁ b₁ hb₁, key P₂ h₂ b₂ hb₂, add_zero]

theorem exists_aniso (h2 : (2 : K) ≠ 0) {C : Submodule K V} (hC : C ≠ ⊥)
    (hnd : PolarNondegOn Q C) : ∃ c ∈ C, polar Q c c ≠ 0 := by
  obtain ⟨c₀, hc₀C, hc₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC
  obtain ⟨y, hyC, hy⟩ := hnd.exists_polar_ne_zero hc₀C hc₀
  by_cases h1 : polar Q c₀ c₀ = 0
  · by_cases h3 : polar Q y y = 0
    · refine ⟨c₀ + y, C.add_mem hc₀C hyC, ?_⟩
      rw [polar_add_left, polar_add_right, polar_add_right, h1, h3, polar_comm Q y c₀]
      intro h
      apply hy
      have : (2 : K) * polar Q c₀ y = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left h2
    · exact ⟨y, hyC, h3⟩
  · exact ⟨c₀, hc₀C, h1⟩

theorem polar_plane_perp (P : HypPair Q) :
    ∀ q ∈ hypPlane P, ∀ y ∈ P.perp, polar Q q y = 0 := by
  intro q hq y hy
  obtain ⟨a, b, rfl⟩ := (mem_hypPlane_iff P).mp hq
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, (HypPair.mem_perp.mp hy).1,
    (HypPair.mem_perp.mp hy).2]
  ring

end Helpers


section Main

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem g0_scalar (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 13) (pr : ℕ → HypPair Q)
    (horth : ∀ a b, a < 6 → b < 6 → a ≠ b → (pr a).Orth (pr b))
    {L₀ L₁ L₂ LM S₁ S₂ : Subgroup (V ≃ₗ[K] V)} {i₀ i₁ i₂ iM s₁ s₂ : V ≃ₗ[K] V}
    (h₀ : IsFundamental Q L₀ i₀) (h₁ : IsFundamental Q L₁ i₁) (h₂' : IsFundamental Q L₂ i₂)
    (hM : IsFundamental Q LM iM) (hS₁ : IsFundamental Q S₁ s₁) (hS₂ : IsFundamental Q S₂ s₂)
    (n₀ : negSpace i₀ = hypPlane (pr 0) ⊔ hypPlane (pr 1))
    (n₁ : negSpace i₁ = hypPlane (pr 1) ⊔ hypPlane (pr 2))
    (n₂ : negSpace i₂ = hypPlane (pr 2) ⊔ hypPlane (pr 3))
    (nM : negSpace iM = hypPlane (pr 4) ⊔ hypPlane (pr 5))
    (c₁ : Commutes S₁ L₀) (c₁' : Commutes S₁ L₁) (c₂ : Commutes S₂ L₀) (c₂' : Commutes S₂ L₁)
    (d₁ : ¬ Commutes S₁ L₂) (d₂ : ¬ Commutes S₂ L₂) (hne : negSpace s₁ ≠ negSpace s₂)
    {g₀ : V ≃ₗ[K] V} (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg₀2 : g₀ * g₀ = 1)
    (f₁ : ∀ l ∈ L₁, g₀ * l = l * g₀) (f₂ : ∀ l ∈ L₂, g₀ * l = l * g₀)
    (fM : ∀ l ∈ LM, g₀ * l = l * g₀) (fS₁ : ∀ l ∈ S₁, g₀ * l = l * g₀)
    (fS₂ : ∀ l ∈ S₂, g₀ * l = l * g₀)
    {g' : V ≃ₗ[K] V} (hg'O : g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg'2 : g' * g' = 1)
    (hS₁g' : ∀ l ∈ S₁, g' * l = l * g') (hS₂g' : ∀ l ∈ S₂, g' * l = l * g')
    (hg'fix : ∀ x, (∀ y ∈ negSpace iM, polar Q x y = 0) → g' x = x)
    (hg'dim : Module.finrank K (negSpace g') = 2) (hg'le : negSpace g' ≤ negSpace iM)
    (hg'pos : ∃ v ∈ negSpace iM, v ≠ 0 ∧ g' v = v) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ y ∈ (pr 0).perp, g₀ y = ε • y := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hgg : ∀ x, g₀ (g₀ x) = x := fun x => by simpa using LinearEquiv.congr_fun hg₀2 x
  obtain ⟨ε₁, hε₁, e₁⟩ := sign_of_commute h2 h₁ hg₀O hg₀2 f₁
  obtain ⟨ε₂, hε₂, e₂⟩ := sign_of_commute h2 h₂' hg₀O hg₀2 f₂
  obtain ⟨εM, hεM, eM⟩ := sign_of_commute h2 hM hg₀O hg₀2 fM
  obtain ⟨εa, hεa, ea⟩ := sign_of_commute h2 hS₁ hg₀O hg₀2 fS₁
  obtain ⟨εb, hεb, eb⟩ := sign_of_commute h2 hS₂ hg₀O hg₀2 fS₂
  have hεε : ε₂ * ε₂ = 1 := by rcases hε₂ with rfl | rfl <;> norm_num
  have pl : ∀ (P : HypPair Q) (W : Submodule K V), hypPlane P ≤ W → P.e ∈ W ∧ P.f ∈ W :=
    fun P W h => ⟨h (e_mem_hypPlane P), h (f_mem_hypPlane P)⟩
  have m0 := pl (pr 0) (negSpace i₀) (by rw [n₀]; exact le_sup_left)
  have m1a := pl (pr 1) (negSpace i₀) (by rw [n₀]; exact le_sup_right)
  have m1b := pl (pr 1) (negSpace i₁) (by rw [n₁]; exact le_sup_left)
  have m2b := pl (pr 2) (negSpace i₁) (by rw [n₁]; exact le_sup_right)
  have m2c := pl (pr 2) (negSpace i₂) (by rw [n₂]; exact le_sup_left)
  have m3 := pl (pr 3) (negSpace i₂) (by rw [n₂]; exact le_sup_right)
  have m4 := pl (pr 4) (negSpace iM) (by rw [nM]; exact le_sup_left)
  have m5 := pl (pr 5) (negSpace iM) (by rw [nM]; exact le_sup_right)
  have hε12 : ε₁ = ε₂ := by
    have : ε₁ • (pr 2).e = ε₂ • (pr 2).e := (e₁ _ m2b.1).symm.trans (e₂ _ m2c.1)
    exact smul_left_injective K (pr 2).e_ne_zero this
  have hεa₂ : εa = ε₂ := by
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_polar_ne_of_not_commutes h2 hS₁ h₂' d₁
    exact sign_eq hε₂ (sign_mul_eq_one hg₀O (ea x hx) (e₂ y hy) hxy)
  have hεb₂ : εb = ε₂ := by
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_polar_ne_of_not_commutes h2 hS₂ h₂' d₂
    exact sign_eq hε₂ (sign_mul_eq_one hg₀O (eb x hx) (e₂ y hy) hxy)
  obtain ⟨C₃, hC₃, hC₃nd, hC₃dim⟩ := fam_perp hQ pr 3
    (fun a b ha hb hab => horth a b (by omega) (by omega) hab)
  have hW_C3 : ∀ {i : V ≃ₗ[K] V}, (∀ x ∈ negSpace i, ∀ y ∈ negSpace i₀, polar Q x y = 0) →
      (∀ x ∈ negSpace i, ∀ y ∈ negSpace i₁, polar Q x y = 0) → negSpace i ≤ C₃ := by
    intro i o₀ o₁ x hx
    rw [hC₃]
    intro a ha
    rw [HypPair.mem_perp]
    interval_cases a
    · exact ⟨by rw [polar_comm]; exact o₀ x hx _ m0.1, by rw [polar_comm]; exact o₀ x hx _ m0.2⟩
    · exact ⟨by rw [polar_comm]; exact o₀ x hx _ m1a.1, by rw [polar_comm]; exact o₀ x hx _ m1a.2⟩
    · exact ⟨by rw [polar_comm]; exact o₁ x hx _ m2b.1, by rw [polar_comm]; exact o₁ x hx _ m2b.2⟩
  obtain ⟨oa₀, oa₁⟩ := orth_of_commutes_two hodd (fun a b ha hb hab => horth a b (by omega)
    (by omega) hab) h₀ h₁ hS₁ n₀ n₁ c₁ c₁'
  obtain ⟨ob₀, ob₁⟩ := orth_of_commutes_two hodd (fun a b ha hb hab => horth a b (by omega)
    (by omega) hab) h₀ h₁ hS₂ n₀ n₁ c₂ c₂'
  have hMC : negSpace iM ≤ C₃ := by
    intro x hx
    rw [hC₃]
    intro a ha
    rw [HypPair.mem_perp]
    rw [nM] at hx
    have hz : ∀ P : HypPair Q, P.Orth (pr 4) → P.Orth (pr 5) →
        polar Q P.e x = 0 ∧ polar Q P.f x = 0 := fun P h4 h5 =>
      ⟨polar_zero_of_mem_sup (A := hypPlane P) (fun x hx y hy => polar_hypPlane_of_orth h4 x hx y
        hy) (fun x hx y hy => polar_hypPlane_of_orth h5 x hx y hy) _ (e_mem_hypPlane P) x hx,
       polar_zero_of_mem_sup (A := hypPlane P) (fun x hx y hy => polar_hypPlane_of_orth h4 x hx y
        hy) (fun x hx y hy => polar_hypPlane_of_orth h5 x hx y hy) _ (f_mem_hypPlane P) x hx⟩
    exact hz (pr a) (horth a 4 (by omega) (by omega) (by omega))
      (horth a 5 (by omega) (by omega) (by omega))
  have hii := isCompl_plusSp_minusSp h2 hg'2
  have hdp := Submodule.finrank_add_eq_of_isCompl hii
  have hplus : ∀ {S : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}, IsFundamental Q S i →
      (∀ l ∈ S, g' * l = l * g') → negSpace i ≤ plusSp g' := by
    intro S i hS hcomm x hx
    obtain ⟨ε', hε', e'⟩ := sign_of_commute h2 hS hg'O hg'2 hcomm
    rcases hε' with rfl | rfl
    · have := e' x hx
      rw [one_smul] at this
      exact mem_plusSp.mpr this
    · exfalso
      have hle : negSpace i ≤ negSpace g' := fun y hy => by
        have := e' y hy
        rw [neg_one_smul] at this
        exact Module.End.mem_eigenspace_iff.mpr (by simpa using this)
      have := Submodule.finrank_mono hle
      rw [finrank_negSpace hodd hS, hg'dim] at this
      omega
  set E : Submodule K V := Module.End.eigenspace (g₀ : Module.End K V) ε₂ with hE
  have hmemE : ∀ x, g₀ x = ε₂ • x → x ∈ E := fun x hx => Module.End.mem_eigenspace_iff.mpr hx
  set U : Submodule K V := C₃ ⊓ plusSp g' with hU
  have hsup : C₃ ⊔ plusSp g' = ⊤ := by
    rw [eq_top_iff, ← hii.sup_eq_top]
    exact sup_le le_sup_right ((hg'le.trans hMC).trans le_sup_left)
  have hdimU : Module.finrank K U ≤ 5 := by
    rw [hU]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq C₃ (plusSp g')
    rw [hsup, finrank_top, hdim] at h1
    have hp : Module.finrank K (plusSp g') = 11 := by
      rw [hdim] at hdp
      have h' : Module.finrank K (minusSp g') = 2 := hg'dim
      omega
    omega
  have hWU : ∀ {S : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}, IsFundamental Q S i →
      (∀ l ∈ S, g' * l = l * g') →
      (∀ x ∈ negSpace i, ∀ y ∈ negSpace i₀, polar Q x y = 0) →
      (∀ x ∈ negSpace i, ∀ y ∈ negSpace i₁, polar Q x y = 0) →
      (∀ x ∈ negSpace i, g₀ x = ε₂ • x) → negSpace i ≤ U ⊓ E := by
    intro S i hS hg' o₀ o₁ hsg x hx
    exact ⟨⟨hW_C3 o₀ o₁ hx, hplus hS hg' hx⟩, hmemE x (hsg x hx)⟩
  have hUE : U ≤ E := le_of_two_distinct hdimU
    (hWU hS₁ hS₁g' oa₀ oa₁ (fun x hx => hεa₂ ▸ ea x hx))
    (hWU hS₂ hS₂g' ob₀ ob₁ (fun x hx => hεb₂ ▸ eb x hx))
    (finrank_negSpace hodd hS₁) (finrank_negSpace hodd hS₂) hne
  obtain ⟨C₆, hC₆, hC₆nd, hC₆dim⟩ := fam_perp hQ pr 6 horth
  have hC₆ne : C₆ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hC₆dim
    omega
  obtain ⟨z', hz'C, hz'⟩ := exists_aniso h2 hC₆ne hC₆nd
  have hz'perp : ∀ a < 6, z' ∈ (pr a).perp := (hC₆ z').mp hz'C
  have hz'U : z' ∈ U := by
    refine ⟨(hC₃ z').mpr fun a ha => hz'perp a (by omega),
      mem_plusSp.mpr (hg'fix z' fun y hy => ?_)⟩
    rw [nM] at hy
    exact polar_zero_sup_of_perp (hz'perp 4 (by norm_num)) (hz'perp 5 (by norm_num)) y hy
  have hz'E : g₀ z' = ε₂ • z' := Module.End.mem_eigenspace_iff.mp (hUE hz'U)
  have hεM2 : εM = ε₂ := by
    obtain ⟨v, hv, hv0, hgv⟩ := hg'pos
    have hvU : v ∈ U := ⟨hMC hv, mem_plusSp.mpr hgv⟩
    have h1 : g₀ v = ε₂ • v := Module.End.mem_eigenspace_iff.mp (hUE hvU)
    have : εM • v = ε₂ • v := (eM v hv).symm.trans h1
    exact smul_left_injective K hv0 this
  have hplane : ∀ k, 1 ≤ k → k ≤ 5 →
      g₀ (pr k).e = ε₂ • (pr k).e ∧ g₀ (pr k).f = ε₂ • (pr k).f := by
    intro k hk1 hk5
    interval_cases k
    · exact ⟨by rw [← hε12]; exact e₁ _ m1b.1, by rw [← hε12]; exact e₁ _ m1b.2⟩
    · exact ⟨by rw [← hε12]; exact e₁ _ m2b.1, by rw [← hε12]; exact e₁ _ m2b.2⟩
    · exact ⟨e₂ _ m3.1, e₂ _ m3.2⟩
    · exact ⟨by rw [← hεM2]; exact eM _ m4.1, by rw [← hεM2]; exact eM _ m4.2⟩
    · exact ⟨by rw [← hεM2]; exact eM _ m5.1, by rw [← hεM2]; exact eM _ m5.2⟩
  have hN : ∀ n, g₀ n = (-ε₂) • n → n ∈ hypPlane (pr 0) := by
    intro n hn
    have horthN : ∀ x, g₀ x = ε₂ • x → polar Q x n = 0 := fun x hx =>
      polar_eigen_orth h2 hg₀O hεε hx hn
    obtain ⟨C₅, hC₅, hC₅nd, hC₅dim⟩ := fam_perp hQ (fun a => pr (a + 1)) 5
      (fun a b ha hb hab => horth (a + 1) (b + 1) (by omega) (by omega) (by omega))
    have hnC₅ : n ∈ C₅ := by
      rw [hC₅]
      intro a ha
      rw [HypPair.mem_perp]
      obtain ⟨he, hf⟩ := hplane (a + 1) (by omega) (by omega)
      exact ⟨horthN _ he, horthN _ hf⟩
    set D : Submodule K V := C₅ ⊓ LinearMap.ker (polarBilin Q z') with hD
    have hnD : n ∈ D := ⟨hnC₅, by
      show polar Q z' n = 0
      exact horthN _ hz'E⟩
    have hz'C₅ : z' ∈ C₅ := (hC₅ z').mpr fun a ha => hz'perp (a + 1) (by omega)
    have hDlt : D < C₅ := by
      refine lt_of_le_of_ne inf_le_left fun h => ?_
      have : z' ∈ D := h ▸ hz'C₅
      exact hz' this.2
    have hD2 : Module.finrank K D ≤ 2 := by
      have := Submodule.finrank_lt_finrank_of_lt hDlt
      omega
    have hle : hypPlane (pr 0) ≤ D := by
      intro q hq
      refine ⟨(hC₅ q).mpr fun a ha => ?_, ?_⟩
      · rw [HypPair.mem_perp]
        have ho := horth (a + 1) 0 (by omega) (by omega) (by omega)
        exact ⟨polar_hypPlane_of_orth ho _ (e_mem_hypPlane _) q hq,
          polar_hypPlane_of_orth ho _ (f_mem_hypPlane _) q hq⟩
      · show polar Q z' q = 0
        rw [polar_comm]
        exact polar_plane_perp (pr 0) q hq z' (hz'perp 0 (by norm_num))
    have heq : hypPlane (pr 0) = D :=
      Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_hypPlane]; exact hD2)
    rw [heq]
    exact hnD
  refine ⟨ε₂, hε₂, fun y hy => ?_⟩
  set d : V := g₀ y - ε₂ • y with hd
  have hdN : g₀ d = (-ε₂) • d := by
    rw [hd, map_sub, map_smul, hgg, smul_sub, smul_smul, neg_mul, mul_comm, hεε]
    module
  have hdperp : ∀ v, polar Q d v = 0 := by
    intro v
    obtain ⟨e, n, he, hn, rfl⟩ := exists_eigen_decomp h2 hg₀2 hεε v
    rw [polar_add_right]
    have h1 : polar Q d e = 0 := by
      rw [polar_comm]
      exact polar_eigen_orth h2 hg₀O hεε he hdN
    have hyn : polar Q y n = 0 := by
      rw [polar_comm]
      exact polar_plane_perp (pr 0) n (hN n hn) y hy
    have h2' : polar Q d n = 0 := by
      have e1 := polar_map_of_mem hg₀O y (g₀ n)
      rw [hgg n, hn, polar_smul_right_eq, hyn, mul_zero] at e1
      rw [hd, polar_sub_left, polar_smul_left_eq, hyn, e1]
      ring
    rw [h1, h2', add_zero]
  have hd0 : d = 0 := eq_zero_of_polar_eq_zero hQ hdperp
  exact sub_eq_zero.mp hd0

end Main

end CFSG.ClassicalInvolution.RouteD.TWE.B6
