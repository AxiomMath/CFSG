module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2Cos
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrQ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrSM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrSP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3Gen

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

private lemma fzc_sy3_inv_mul_mem {Wp M₂ : Subgroup G}
    (hnrm : ∀ q ∈ M₂, ∀ w ∈ Wp, q * w * q⁻¹ ∈ Wp) {g : G}
    (hg : g ∈ M₂) {s : G} (h : g * s⁻¹ ∈ Wp) : g⁻¹ * s ∈ Wp := by
  have h1 : s * g⁻¹ ∈ Wp := by
    have := Wp.inv_mem h
    rwa [mul_inv_rev, inv_inv] at this
  have h2 := hnrm g⁻¹ (M₂.inv_mem hg) (s * g⁻¹) h1
  simpa [mul_assoc] using h2

private theorem fzc_sy3_rank_M₂_hard (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U)
    {X : Subgroup G} (hX : X ≤ M₂) {x y : G}
    (hxX : x ∈ X) (hxWp : x ∉ Wp) (hyX : y ∈ X) (hyWp : y ∉ Wp) (hyx : y * x⁻¹ ∉ Wp) :
    ∃ s : Finset G, s.card ≤ 3 ∧ closure (s : Set G) = X := by
  classical
  obtain ⟨hWpF, hFP, hPU, hFM₂, hM₂U, hFM₃, hM₃U⟩ := hs.chain
  have hWpM₂ : Wp ≤ M₂ := hWpF.trans hFM₂
  have hnrmM₂ : ∀ q ∈ M₂, ∀ w ∈ Wp, q * w * q⁻¹ ∈ Wp :=
    fun q hq w hw => hs.nrm q (hM₂U hq) w hw
  have hfour := fzc_sy2_four_cosets hWpM₂ hs.card_P_M₂.2 hnrmM₂ hs.M₂_elem.1 hs.M₂_elem.2
    (hX hxX) hxWp (hX hyX) hyWp hyx
  have haF : a ∈ F := hs.F_eq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have haM₂ : a ∈ M₂ := hFM₂ haF
  have hcM₂ : c ∈ M₂ := by
    rw [hs.M₂_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hcWp : c ∉ Wp := fun h => hs.c_notin (hFP (hWpF h))
  have hac : a * c⁻¹ ∉ Wp := by
    intro hac
    have hcF : c ∈ F := by
      have hc_eq : c = (a * c⁻¹)⁻¹ * a := by group
      rw [hc_eq]
      exact F.mul_mem (F.inv_mem (hWpF hac)) haF
    exact hs.c_notin (hFP hcF)
  obtain ⟨x', hx'X, hax'⟩ : ∃ x' ∈ X, a⁻¹ * x' ∈ Wp := by
    rcases hfour a haM₂ with h1 | h1 | h1 | h1
    · exact absurd h1 hs.a_notin
    · exact ⟨x, hxX, fzc_sy3_inv_mul_mem hnrmM₂ haM₂ h1⟩
    · exact ⟨y, hyX, fzc_sy3_inv_mul_mem hnrmM₂ haM₂ h1⟩
    · exact ⟨x * y, X.mul_mem hxX hyX, fzc_sy3_inv_mul_mem hnrmM₂ haM₂ h1⟩
  obtain ⟨y', hy'X, hcy'⟩ : ∃ y' ∈ X, c⁻¹ * y' ∈ Wp := by
    rcases hfour c hcM₂ with h1 | h1 | h1 | h1
    · exact absurd h1 hcWp
    · exact ⟨x, hxX, fzc_sy3_inv_mul_mem hnrmM₂ hcM₂ h1⟩
    · exact ⟨y, hyX, fzc_sy3_inv_mul_mem hnrmM₂ hcM₂ h1⟩
    · exact ⟨x * y, X.mul_mem hxX hyX, fzc_sy3_inv_mul_mem hnrmM₂ hcM₂ h1⟩
  obtain ⟨k, hk⟩ := hs.SM x' y' hax' hcy'
  obtain ⟨hc1, hc2⟩ := hs.c_act.2
  obtain ⟨e, heA, heshift⟩ := fzc_sy3_shift (c := c) hs.comm hs.ord₁ hs.ord₂ hs.inf hc1 hc2
    (A := X ⊓ baseGrp x₁ x₂) inf_le_right k
  have heWp : e ∈ Wp := hs.E_le_Wp heA.2
  set y'' : G := y' * e with hy''def
  have hy''X : y'' ∈ X := by rw [hy''def]; exact X.mul_mem hy'X heA.1
  have hcU : c ∈ U := hM₂U hcM₂
  have hcec : c⁻¹ * e * c ∈ Wp := by
    have h := hs.nrm c⁻¹ (U.inv_mem hcU) e heWp
    simpa using h
  have hr : c⁻¹ * e * c * e ∈ Wp := Wp.mul_mem hcec heWp
  have hce : y'⁻¹ * e * y' = c⁻¹ * e * c := hs.c_act.1 y' hcy' e heA.2
  have hy''sq : y'' ^ 2 = y' ^ 2 * (c⁻¹ * e * c * e) := by
    calc y'' ^ 2 = (y' * e) * (y' * e) := by rw [hy''def, pow_two]
      _ = y' * e * y' * e := by group
      _ = y' ^ 2 * (y'⁻¹ * e * y') * e := by group
      _ = y' ^ 2 * (c⁻¹ * e * c) * e := by rw [hce]
      _ = y' ^ 2 * (c⁻¹ * e * c * e) := by group
  have hx'2Wp : x' ^ 2 ∈ Wp := hs.M₂_elem.1 x' (hX hx'X)
  have hy'2Wp : y' ^ 2 ∈ Wp := hs.M₂_elem.1 y' (hX hy'X)
  have hx'Wp : x' ∉ Wp := by
    intro h
    apply hs.a_notin
    have : a = x' * (a⁻¹ * x')⁻¹ := by group
    rw [this]
    exact Wp.mul_mem h (Wp.inv_mem hax')
  have hy'Wp : y' ∉ Wp := by
    intro h
    apply hcWp
    have : c = y' * (c⁻¹ * y')⁻¹ := by group
    rw [this]
    exact Wp.mul_mem h (Wp.inv_mem hcy')
  have hprod : x' ^ 2 * (y'' ^ 2)⁻¹ =
      x₂ ^ 2 * (x₁ * x₂) ^ k * (c⁻¹ * e * c * e)⁻¹ := by
    have hcomm : (c⁻¹ * e * c * e)⁻¹ * (y' ^ 2)⁻¹ =
        (y' ^ 2)⁻¹ * (c⁻¹ * e * c * e)⁻¹ :=
      hs.Wp_comm _ (Wp.inv_mem hr) _ (Wp.inv_mem hy'2Wp)
    calc x' ^ 2 * (y'' ^ 2)⁻¹
        = x' ^ 2 * (y' ^ 2 * (c⁻¹ * e * c * e))⁻¹ := by rw [hy''sq]
      _ = x' ^ 2 * ((c⁻¹ * e * c * e)⁻¹ * (y' ^ 2)⁻¹) := by rw [mul_inv_rev]
      _ = x' ^ 2 * ((y' ^ 2)⁻¹ * (c⁻¹ * e * c * e)⁻¹) := by rw [hcomm]
      _ = (x' ^ 2 * (y' ^ 2)⁻¹) * (c⁻¹ * e * c * e)⁻¹ := by rw [← mul_assoc]
      _ = (x₂ ^ 2 * (x₁ * x₂) ^ k) * (c⁻¹ * e * c * e)⁻¹ := by rw [hk]
  have hw : ∀ e' ∈ X ⊓ baseGrp x₁ x₂, e' ^ 2 ≠ x' ^ 2 * (y'' ^ 2)⁻¹ := by
    intro e' he'
    rw [hprod]
    exact heshift e' he'
  have hcy'' : c⁻¹ * y'' ∈ Wp := by
    rw [hy''def, ← mul_assoc]
    exact Wp.mul_mem hcy' heWp
  have hx'y'' : x' * y''⁻¹ ∉ Wp := by
    intro h
    apply hac
    have hax'2 : a * x'⁻¹ ∈ Wp := by
      have hx'inv : x'⁻¹ = (a⁻¹ * x')⁻¹ * a⁻¹ := by group
      rw [hx'inv]
      simpa only [mul_assoc] using hnrmM₂ a haM₂ _ (Wp.inv_mem hax')
    have hy''c : y'' * c⁻¹ ∈ Wp := by
      have hy''eq : y'' = c * (c⁻¹ * y'') := by group
      rw [hy''eq]
      exact hnrmM₂ c hcM₂ _ hcy''
    have heq : a * c⁻¹ = (a * x'⁻¹) * (x' * y''⁻¹) * (y'' * c⁻¹) := by group
    rw [heq]
    exact Wp.mul_mem (Wp.mul_mem hax'2 h) hy''c
  have hy''Wp : y'' ∉ Wp := by
    intro h
    apply hy'Wp
    rw [hy''def] at h
    have : y' = (y' * e) * e⁻¹ := by group
    rw [this]
    exact Wp.mul_mem h (Wp.inv_mem heWp)
  have hx'M₂ : x' ∈ M₂ := hX hx'X
  have hy''M₂ : y'' ∈ M₂ := hX hy''X
  have hy''x' : y'' * x'⁻¹ ∉ Wp := by
    intro h
    exact hx'y'' (by simpa [mul_inv_rev] using Wp.inv_mem h)
  have hcov : ∀ g ∈ X, g ∈ Wp ∨ g * x'⁻¹ ∈ Wp ∨ g * y''⁻¹ ∈ Wp ∨
      g * (x' * y'')⁻¹ ∈ Wp := by
    intro g hg
    exact fzc_sy2_four_cosets hWpM₂ hs.card_P_M₂.2 hnrmM₂ hs.M₂_elem.1 hs.M₂_elem.2
      hx'M₂ hx'Wp hy''M₂ hy''Wp hy''x' g (hX hg)
  have hx'2E : x' ^ 2 ∉ baseGrp x₁ x₂ := hs.sq_notE x' (hM₂U hx'M₂) hx'Wp hx'2Wp
  have hy''2Wp : y'' ^ 2 ∈ Wp := hs.M₂_elem.1 y'' hy''M₂
  have hy''2E : y'' ^ 2 ∉ baseGrp x₁ x₂ := hs.sq_notE y'' (hM₂U hy''M₂) hy''Wp hy''2Wp
  obtain ⟨u, hu⟩ := fzc_sy3_klein (N := Wp) (E := baseGrp x₁ x₂) (X := X)
    hs.E_comm hs.E_exp hs.E_rank hs.E_le_Wp hs.Wp_E hx'X hy''X hx'2Wp hx'2E hy''2Wp
    hy''2E hcov hw
  exact ⟨{x', y'', u}, Finset.card_le_three, by simpa using hu⟩

theorem fzc_sy3_rank_M₂ (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    S4A.RankLE M₂ 3 := by
  classical
  intro X hX
  by_cases hXWp : X ≤ Wp
  · exact hs.Wp_rank X hXWp
  obtain ⟨x, hxX, hxWp⟩ := SetLike.not_le_iff_exists.mp hXWp
  by_cases h2 : ∃ y ∈ X, y ∉ Wp ∧ y * x⁻¹ ∉ Wp
  · obtain ⟨y, hyX, hyWp, hyx⟩ := h2
    exact fzc_sy3_rank_M₂_hard hs hX hxX hxWp hyX hyWp hyx
  · have h2' : ∀ g ∈ X, g ∈ Wp ∨ g * x⁻¹ ∈ Wp := by
      intro g hg
      by_contra hcon
      rw [not_or] at hcon
      exact h2 ⟨g, hg, hcon.1, hcon.2⟩
    have hM₂U : M₂ ≤ U := hs.chain.2.2.2.2.1
    have hx2Wp : x ^ 2 ∈ Wp := hs.M₂_elem.1 x (hX hxX)
    have hx2E : x ^ 2 ∉ baseGrp x₁ x₂ := hs.sq_notE x (hM₂U (hX hxX)) hxWp hx2Wp
    have hsq : ∀ a ∈ Wp, a ^ 2 ∈ baseGrp x₁ x₂ := fun a ha => hs.Z_le_E (hs.Wp_sq a ha)
    obtain ⟨s, hscard, hsc⟩ := fzc_sy3_cyc (N := Wp) (E := baseGrp x₁ x₂) (X := X)
      hs.Wp_comm hs.Wp_exp hs.Wp_rank hsq hxX hx2Wp hx2E (by
        intro g hg
        rcases h2' g hg with hgW | hgx
        · exact ⟨0, by simpa using hgW⟩
        · exact ⟨1, by simpa using hgx⟩)
    exact ⟨s, hscard, hsc⟩

end CFSG.OddStandard.SmallF3.FritzII
