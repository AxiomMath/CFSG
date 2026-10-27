module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Sign

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.ModelFacts (plusSp minusSp isCompl_plusSp_minusSp mem_plusSp)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Main

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem chain_sign_gen (h2 : (2 : K) ≠ 0) {s : ℕ} (hs : 1 ≤ s) {pr : ℕ → HypPair Q}
    {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}
    (hL : ∀ a ≤ s, IsFundamental Q (L a) (i a))
    (nL : ∀ a ≤ s, negSpace (i a) = hypPlane (pr a) ⊔ hypPlane (pr (a + 1)))
    {g₀ : V ≃ₗ[K] V} (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg₀2 : g₀ * g₀ = 1)
    (f : ∀ a, 1 ≤ a → a ≤ s → ∀ l ∈ L a, g₀ * l = l * g₀) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a, 1 ≤ a → a ≤ s → ∀ x ∈ negSpace (i a), g₀ x = ε • x := by
  obtain ⟨ε₂, hε₂, e₂⟩ := sign_of_commute h2 (hL s le_rfl) hg₀O hg₀2 (f s hs le_rfl)
  refine ⟨ε₂, hε₂, ?_⟩
  have key : ∀ k a, a + k = s → 1 ≤ a → ∀ x ∈ negSpace (i a), g₀ x = ε₂ • x := by
    intro k
    induction k with
    | zero =>
      intro a ha _ x hx
      obtain rfl : a = s := by omega
      exact e₂ x hx
    | succ k ih =>
      intro a ha ha1 x hx
      obtain ⟨εa, hεa, ea⟩ := sign_of_commute h2 (hL a (by omega)) hg₀O hg₀2 (f a ha1 (by omega))
      have hmem1 : (pr (a + 1)).e ∈ negSpace (i a) := by
        rw [nL a (by omega)]
        exact Submodule.mem_sup_right (e_mem_hypPlane _)
      have hmem2 : (pr (a + 1)).e ∈ negSpace (i (a + 1)) := by
        rw [nL (a + 1) (by omega)]
        exact Submodule.mem_sup_left (e_mem_hypPlane _)
      have h1 : εa • (pr (a + 1)).e = ε₂ • (pr (a + 1)).e :=
        (ea _ hmem1).symm.trans (ih (a + 1) (by omega) (by omega) _ hmem2)
      have h3 : εa = ε₂ := smul_left_injective K (pr (a + 1)).e_ne_zero h1
      rw [ea x hx, h3]
  exact fun a ha1 has => key (s - a) a (by omega) ha1

theorem g0_scalar_gen (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate) {s : ℕ}
    (hs : 1 ≤ s) (hdim : Module.finrank K V = 2 * s + 9) (pr : ℕ → HypPair Q)
    (horth : ∀ a b, a < s + 4 → b < s + 4 → a ≠ b → (pr a).Orth (pr b))
    {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}
    {LM S₁ S₂ : Subgroup (V ≃ₗ[K] V)} {iM s₁ s₂ : V ≃ₗ[K] V}
    (hL : ∀ a ≤ s, IsFundamental Q (L a) (i a)) (hM : IsFundamental Q LM iM)
    (hS₁ : IsFundamental Q S₁ s₁) (hS₂ : IsFundamental Q S₂ s₂)
    (nL : ∀ a ≤ s, negSpace (i a) = hypPlane (pr a) ⊔ hypPlane (pr (a + 1)))
    (nM : negSpace iM = hypPlane (pr (s + 2)) ⊔ hypPlane (pr (s + 3)))
    (oS₁ : ∀ a < s, ∀ x ∈ negSpace s₁, ∀ y ∈ negSpace (i a), polar Q x y = 0)
    (oS₂ : ∀ a < s, ∀ x ∈ negSpace s₂, ∀ y ∈ negSpace (i a), polar Q x y = 0)
    (d₁ : ¬ Commutes S₁ (L s)) (d₂ : ¬ Commutes S₂ (L s)) (hne : negSpace s₁ ≠ negSpace s₂)
    {g₀ : V ≃ₗ[K] V} (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg₀2 : g₀ * g₀ = 1)
    (f : ∀ a, 1 ≤ a → a ≤ s → ∀ l ∈ L a, g₀ * l = l * g₀)
    (fM : ∀ l ∈ LM, g₀ * l = l * g₀) (fS₁ : ∀ l ∈ S₁, g₀ * l = l * g₀)
    (fS₂ : ∀ l ∈ S₂, g₀ * l = l * g₀)
    {g' : V ≃ₗ[K] V} (hg'O : g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg'2 : g' * g' = 1)
    (hS₁g' : ∀ l ∈ S₁, g' * l = l * g') (hS₂g' : ∀ l ∈ S₂, g' * l = l * g')
    (hg'fix : ∀ x, (∀ y ∈ negSpace iM, polar Q x y = 0) → g' x = x)
    (hg'dim : Module.finrank K (negSpace g') = 2) (hg'le : negSpace g' ≤ negSpace iM) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ y ∈ (pr 0).perp, g₀ y = ε • y := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hgg : ∀ x, g₀ (g₀ x) = x := fun x => by simpa using LinearEquiv.congr_fun hg₀2 x
  obtain ⟨ε₂, hε₂, hchain⟩ := chain_sign_gen h2 hs hL nL hg₀O hg₀2 f
  obtain ⟨εM, hεM, eM⟩ := sign_of_commute h2 hM hg₀O hg₀2 fM
  obtain ⟨εa, hεa, ea⟩ := sign_of_commute h2 hS₁ hg₀O hg₀2 fS₁
  obtain ⟨εb, hεb, eb⟩ := sign_of_commute h2 hS₂ hg₀O hg₀2 fS₂
  have hεε : ε₂ * ε₂ = 1 := by rcases hε₂ with rfl | rfl <;> norm_num
  have pl : ∀ (P : HypPair Q) (W : Submodule K V), hypPlane P ≤ W → P.e ∈ W ∧ P.f ∈ W :=
    fun P W h => ⟨h (e_mem_hypPlane P), h (f_mem_hypPlane P)⟩
  have m1 : ∀ a ≤ s, (pr a).e ∈ negSpace (i a) ∧ (pr a).f ∈ negSpace (i a) := fun a ha =>
    pl (pr a) _ (by rw [nL a ha]; exact le_sup_left)
  have m2 : ∀ a ≤ s, (pr (a + 1)).e ∈ negSpace (i a) ∧ (pr (a + 1)).f ∈ negSpace (i a) :=
    fun a ha => pl (pr (a + 1)) _ (by rw [nL a ha]; exact le_sup_right)
  have m4 := pl (pr (s + 2)) (negSpace iM) (by rw [nM]; exact le_sup_left)
  have m5 := pl (pr (s + 3)) (negSpace iM) (by rw [nM]; exact le_sup_right)
  have hεa₂ : εa = ε₂ := by
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_polar_ne_of_not_commutes h2 hS₁ (hL s le_rfl) d₁
    exact sign_eq hε₂ (sign_mul_eq_one hg₀O (ea x hx) (hchain s hs le_rfl y hy) hxy)
  have hεb₂ : εb = ε₂ := by
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_polar_ne_of_not_commutes h2 hS₂ (hL s le_rfl) d₂
    exact sign_eq hε₂ (sign_mul_eq_one hg₀O (eb x hx) (hchain s hs le_rfl y hy) hxy)
  obtain ⟨C, hC, hCnd, hCdim⟩ := fam_perp hQ pr (s + 1)
    (fun a b ha hb hab => horth a b (by omega) (by omega) hab)
  have hC7 : Module.finrank K C = 7 := by omega
  have hW_C : ∀ {i' : V ≃ₗ[K] V}, (∀ a < s, ∀ x ∈ negSpace i', ∀ y ∈ negSpace (i a),
      polar Q x y = 0) → negSpace i' ≤ C := by
    intro i' o x hx
    rw [hC]
    intro a ha
    rw [HypPair.mem_perp]
    by_cases has : a < s
    · exact ⟨by rw [polar_comm]; exact o a has x hx _ (m1 a has.le).1,
        by rw [polar_comm]; exact o a has x hx _ (m1 a has.le).2⟩
    · have has' : a = s := by omega
      obtain ⟨b, hb⟩ : ∃ b, s = b + 1 := ⟨s - 1, by omega⟩
      have hm := m2 b (by omega)
      rw [← hb] at hm
      rw [has']
      exact ⟨by rw [polar_comm]; exact o b (by omega) x hx _ hm.1,
        by rw [polar_comm]; exact o b (by omega) x hx _ hm.2⟩
  have hMC : negSpace iM ≤ C := by
    intro x hx
    rw [hC]
    intro a ha
    rw [HypPair.mem_perp]
    rw [nM] at hx
    have hz : ∀ P : HypPair Q, P.Orth (pr (s + 2)) → P.Orth (pr (s + 3)) →
        polar Q P.e x = 0 ∧ polar Q P.f x = 0 := fun P h4 h5 =>
      ⟨polar_zero_of_mem_sup (A := hypPlane P) (fun x hx y hy => polar_hypPlane_of_orth h4 x hx y
        hy) (fun x hx y hy => polar_hypPlane_of_orth h5 x hx y hy) _ (e_mem_hypPlane P) x hx,
       polar_zero_of_mem_sup (A := hypPlane P) (fun x hx y hy => polar_hypPlane_of_orth h4 x hx y
        hy) (fun x hx y hy => polar_hypPlane_of_orth h5 x hx y hy) _ (f_mem_hypPlane P) x hx⟩
    exact hz (pr a) (horth a (s + 2) (by omega) (by omega) (by omega))
      (horth a (s + 3) (by omega) (by omega) (by omega))
  have hii := isCompl_plusSp_minusSp h2 hg'2
  have hdp := Submodule.finrank_add_eq_of_isCompl hii
  have hplus : ∀ {S : Subgroup (V ≃ₗ[K] V)} {i' : V ≃ₗ[K] V}, IsFundamental Q S i' →
      (∀ l ∈ S, g' * l = l * g') → negSpace i' ≤ plusSp g' := by
    intro S i' hS hcomm x hx
    obtain ⟨ε', hε', e'⟩ := sign_of_commute h2 hS hg'O hg'2 hcomm
    rcases hε' with rfl | rfl
    · have := e' x hx
      rw [one_smul] at this
      exact mem_plusSp.mpr this
    · exfalso
      have hle : negSpace i' ≤ negSpace g' := fun y hy => by
        have := e' y hy
        rw [neg_one_smul] at this
        exact Module.End.mem_eigenspace_iff.mpr (by simpa using this)
      have := Submodule.finrank_mono hle
      rw [finrank_negSpace hodd hS, hg'dim] at this
      omega
  have hp : Module.finrank K (plusSp g') = 2 * s + 7 := by
    rw [hdim] at hdp
    have h' : Module.finrank K (minusSp g') = 2 := hg'dim
    omega
  set E : Submodule K V := Module.End.eigenspace (g₀ : Module.End K V) ε₂ with hE
  have hmemE : ∀ x, g₀ x = ε₂ • x → x ∈ E := fun x hx => Module.End.mem_eigenspace_iff.mpr hx
  set U : Submodule K V := C ⊓ plusSp g' with hU
  have hsup : C ⊔ plusSp g' = ⊤ := by
    rw [eq_top_iff, ← hii.sup_eq_top]
    exact sup_le le_sup_right ((hg'le.trans hMC).trans le_sup_left)
  have hdimU : Module.finrank K U ≤ 5 := by
    rw [hU]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq C (plusSp g')
    rw [hsup, finrank_top, hdim] at h1
    omega
  have hWU : ∀ {S : Subgroup (V ≃ₗ[K] V)} {i' : V ≃ₗ[K] V}, IsFundamental Q S i' →
      (∀ l ∈ S, g' * l = l * g') →
      (∀ a < s, ∀ x ∈ negSpace i', ∀ y ∈ negSpace (i a), polar Q x y = 0) →
      (∀ x ∈ negSpace i', g₀ x = ε₂ • x) → negSpace i' ≤ U ⊓ E := by
    intro S i' hS hg' o hsg x hx
    exact ⟨⟨hW_C o hx, hplus hS hg' hx⟩, hmemE x (hsg x hx)⟩
  have hUE : U ≤ E := le_of_two_distinct hdimU
    (hWU hS₁ hS₁g' oS₁ (fun x hx => hεa₂ ▸ ea x hx))
    (hWU hS₂ hS₂g' oS₂ (fun x hx => hεb₂ ▸ eb x hx))
    (finrank_negSpace hodd hS₁) (finrank_negSpace hodd hS₂) hne
  obtain ⟨C₆, hC₆, hC₆nd, hC₆dim⟩ := fam_perp hQ pr (s + 4) horth
  have hC₆ne : C₆ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hC₆dim
    omega
  obtain ⟨z', hz'C, hz'⟩ := exists_aniso h2 hC₆ne hC₆nd
  have hz'perp : ∀ a < s + 4, z' ∈ (pr a).perp := (hC₆ z').mp hz'C
  have hz'U : z' ∈ U := by
    refine ⟨(hC z').mpr fun a ha => hz'perp a (by omega),
      mem_plusSp.mpr (hg'fix z' fun y hy => ?_)⟩
    rw [nM] at hy
    exact polar_zero_sup_of_perp (hz'perp (s + 2) (by omega)) (hz'perp (s + 3) (by omega)) y hy
  have hz'E : g₀ z' = ε₂ • z' := Module.End.mem_eigenspace_iff.mp (hUE hz'U)
  have hg'pos : ∃ v ∈ negSpace iM, v ≠ 0 ∧ g' v = v := by
    have hs4 : negSpace iM ⊔ plusSp g' = ⊤ := by
      rw [eq_top_iff, ← hii.sup_eq_top]
      exact sup_le le_sup_right (hg'le.trans le_sup_left)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (negSpace iM) (plusSp g')
    rw [hs4, finrank_top, hdim, finrank_negSpace hodd hM, hp] at h1
    have hne0 : negSpace iM ⊓ plusSp g' ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at h1
      omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne0
    exact ⟨v, hv.1, hv0, mem_plusSp.mp hv.2⟩
  have hεM2 : εM = ε₂ := by
    obtain ⟨v, hv, hv0, hgv⟩ := hg'pos
    have hvU : v ∈ U := ⟨hMC hv, mem_plusSp.mpr hgv⟩
    have h1 : g₀ v = ε₂ • v := Module.End.mem_eigenspace_iff.mp (hUE hvU)
    have : εM • v = ε₂ • v := (eM v hv).symm.trans h1
    exact smul_left_injective K hv0 this
  have hplane : ∀ k, 1 ≤ k → k ≤ s + 3 →
      g₀ (pr k).e = ε₂ • (pr k).e ∧ g₀ (pr k).f = ε₂ • (pr k).f := by
    intro k hk1 hk3
    by_cases hks : k ≤ s
    · exact ⟨hchain k hk1 hks _ (m1 k hks).1, hchain k hk1 hks _ (m1 k hks).2⟩
    · by_cases hk1' : k = s + 1
      · subst hk1'
        exact ⟨hchain s hs le_rfl _ (m2 s le_rfl).1, hchain s hs le_rfl _ (m2 s le_rfl).2⟩
      · by_cases hk2' : k = s + 2
        · subst hk2'
          exact ⟨by rw [← hεM2]; exact eM _ m4.1, by rw [← hεM2]; exact eM _ m4.2⟩
        · obtain rfl : k = s + 3 := by omega
          exact ⟨by rw [← hεM2]; exact eM _ m5.1, by rw [← hεM2]; exact eM _ m5.2⟩
  have hN : ∀ n, g₀ n = (-ε₂) • n → n ∈ hypPlane (pr 0) := by
    intro n hn
    have horthN : ∀ x, g₀ x = ε₂ • x → polar Q x n = 0 := fun x hx =>
      polar_eigen_orth h2 hg₀O hεε hx hn
    obtain ⟨C₅, hC₅, hC₅nd, hC₅dim⟩ := fam_perp hQ (fun a => pr (a + 1)) (s + 3)
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
        exact polar_plane_perp (pr 0) q hq z' (hz'perp 0 (by omega))
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

end CFSG.ClassicalInvolution.Q3.Q3TWY
