module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilBlocks
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilNFArith
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilBasis

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3PencilCoords

variable {G : Type} [Group G] [Finite G] {L T R₂ U₁ : Subgroup G} {t : G} {f : ℕ} {E : Type}
  [Field E] [Fintype E] [CharP E 2] {σ : E →+* E} {u w : G → E} {d : G} {μ : E}
  {a χ₁ χ₂ : G → E}

omit [Finite G] [CharP E 2] in
theorem eq_zero_of_additive_weight (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂)
    (hf : 2 ≤ f) {b : G → E} (hb_add : ∀ x ∈ U₁, ∀ y ∈ U₁, b (x * y) = b x + b y)
    (hb_d : ∀ x ∈ U₁, b (d * x * d⁻¹) = μ * b x)
    (hinj : ∀ x ∈ U₁, a x = 0 → b x = 0 → x ∈ R₂)
    (hsurj : ∀ α β : E, ∃ x ∈ U₁, a x = α ∧ b x = β) (hRU : R₂ ≤ U₁) {D : G → E}
    (hD_mul : ∀ x ∈ U₁, ∀ y ∈ U₁, D (x * y) = D x + D y) (hD_R : ∀ r ∈ R₂, D r = 0)
    (hD_d : ∀ x ∈ U₁, D (d * x * d⁻¹) = μ ^ (2 ^ f + 1) * D x) {x : G} (hx : x ∈ U₁) :
    D x = 0 := by
  classical
  have hKE : Fintype.card E = (2 ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hP.semilinear.card]
  have hdU : ∀ x ∈ U₁, d * x * d⁻¹ ∈ U₁ := fun x hx =>
    (mem_normalizer_iff.mp hP.d_mem_normalizer_U₁ x).mp hx
  have hb1 : b 1 = 0 := by
    have := hb_add 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    linear_combination -this
  have hbinv : ∀ x ∈ U₁, b x⁻¹ = -b x := by
    intro x hx
    have h1 := hb_add x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, hb1] at h1
    linear_combination -h1
  have hcoord : ∀ x ∈ U₁, ∀ y ∈ U₁, a x = a y → b x = b y → D y = D x := by
    intro x hx y hy hab hbb
    have hr : x⁻¹ * y ∈ R₂ := hinj _ (mul_mem (inv_mem hx) hy)
      (by rw [hP.a_mul _ (inv_mem hx) _ hy, hP.a_inv hx, hab, neg_add_cancel])
      (by rw [hb_add _ (inv_mem hx) _ hy, hbinv x hx, hbb, neg_add_cancel])
    have e : y = x * (x⁻¹ * y) := by group
    rw [e, hD_mul _ hx _ (hRU hr), hD_R _ hr, add_zero]
  choose s hsU hsa hsb using hsurj
  have h₀ : ∀ β, D (s 0 β) = 0 := pencilNF_eq_zero_of_additive_weight hf hKE (fun β => D (s 0 β))
    (fun β β' => show D (s 0 (β + β')) = D (s 0 β) + D (s 0 β') by
      rw [← hD_mul _ (hsU _ _) _ (hsU _ _)]
      exact hcoord (s 0 β * s 0 β') (mul_mem (hsU _ _) (hsU _ _)) (s 0 (β + β')) (hsU _ _)
        (by rw [hP.a_mul _ (hsU _ _) _ (hsU _ _), hsa, hsa, hsa, add_zero])
        (by rw [hb_add _ (hsU _ _) _ (hsU _ _), hsb, hsb, hsb]))
    hP.mu_ne_zero hP.orderOf_mu (fun β => show D (s 0 (μ * β)) = _ * D (s 0 β) by
      rw [← hD_d _ (hsU _ _)]
      exact hcoord (d * s 0 β * d⁻¹) (hdU _ (hsU _ _)) (s 0 (μ * β)) (hsU _ _)
        (by rw [hP.a_conj_d (hsU _ _), hsa, hsa, mul_zero])
        (by rw [hb_d _ (hsU _ _), hsb, hsb]))
  have h₁ : ∀ α, D (s α 0) = 0 := pencilNF_eq_zero_of_additive_weight hf hKE (fun α => D (s α 0))
    (fun α α' => show D (s (α + α') 0) = D (s α 0) + D (s α' 0) by
      rw [← hD_mul _ (hsU _ _) _ (hsU _ _)]
      exact hcoord (s α 0 * s α' 0) (mul_mem (hsU _ _) (hsU _ _)) (s (α + α') 0) (hsU _ _)
        (by rw [hP.a_mul _ (hsU _ _) _ (hsU _ _), hsa, hsa, hsa])
        (by rw [hb_add _ (hsU _ _) _ (hsU _ _), hsb, hsb, hsb, add_zero]))
    hP.mu_ne_zero hP.orderOf_mu (fun α => show D (s (μ * α) 0) = _ * D (s α 0) by
      rw [← hD_d _ (hsU _ _)]
      exact hcoord (d * s α 0 * d⁻¹) (hdU _ (hsU _ _)) (s (μ * α) 0) (hsU _ _)
        (by rw [hP.a_conj_d (hsU _ _), hsa, hsa])
        (by rw [hb_d _ (hsU _ _), hsb, hsb, mul_zero]))
  have hm := mul_mem (hsU 0 (b x)) (hsU (a x) 0)
  rw [hcoord _ hm x hx (by rw [hP.a_mul _ (hsU _ _) _ (hsU _ _), hsa, hsa, zero_add])
    (by rw [hb_add _ (hsU _ _) _ (hsU _ _), hsb, hsb, add_zero]),
    hD_mul _ (hsU _ _) _ (hsU _ _), h₀, h₁, add_zero]

theorem exists_normalForm (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂)
    (hf : 2 ≤ f) (hR : U3R2 G L (szT₁ L T) R₂ t f) (hU : U3U1Data G L f t T R₂ U₁) {b : G → E}
    (hb_add : ∀ x ∈ U₁, ∀ y ∈ U₁, b (x * y) = b x + b y)
    (hb_T : ∀ y ∈ szT₁ L T, ∀ r ∈ R₂, b (y * r) = u y)
    (hb_d : ∀ x ∈ U₁, b (d * x * d⁻¹) = μ * b x)
    (hb_t : ∀ x ∈ U₁, b (t * x * t⁻¹) = a x + b x)
    (hinj : ∀ x ∈ U₁, a x = 0 → b x = 0 → x ∈ R₂)
    (hsurj : ∀ α β : E, ∃ x ∈ U₁, a x = α ∧ b x = β) :
    ∃ g δ : E, σ δ = δ ∧
      (∀ x ∈ U₁, ∀ y ∈ U₁,
        χ₁ ⁅x, y⁆ = TraceForm.form σ (b x + σ g * a x) (a y) +
          TraceForm.form σ (a x) (b y + σ g * a y) + TraceForm.form σ (a x) (a y) ∧
        χ₂ ⁅x, y⁆ = TraceForm.form σ (b x + σ g * a x) (b y + σ g * a y) +
          δ * TraceForm.form σ (a x) (a y)) ∧
      ∀ x ∈ U₁, χ₁ (x ^ 2) = TraceForm.form σ (b x + σ g * a x) (a x) + a x * σ (a x) ∧
        χ₂ (x ^ 2) = (b x + σ g * a x) * σ (b x + σ g * a x) + δ * (a x * σ (a x)) := by
  classical
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hS := hP.semilinear
  have hc := hS.coords
  have hσ := hS.sigma
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hσσ : ∀ x, σ (σ x) = x := TraceForm.sigma_sigma hσ hS.card
  obtain ⟨β₀, hβ₀⟩ := pencilNF_exists_sigma_ne hq hS.card hS.card_fixed
  have hRU : R₂ ≤ U₁ := le_sup_right.trans hU.le
  have hTU : szT₁ L T ≤ U₁ := le_sup_left.trans hU.le
  have hUR : ∀ x ∈ U₁, ∀ r ∈ R₂, x * r = r * x := fun x hx r hr =>
    (mem_centralizer_iff.mp (hU.le_centralizer hx) r hr).symm
  have hcomR : ∀ x ∈ U₁, ∀ y ∈ U₁, ⁅x, y⁆ ∈ R₂ := fun x hx y hy => by
    rw [commutatorElement_def]
    exact hU.comm_mem x hx y hy
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  have htU' : ∀ x ∈ U₁, t * x * t⁻¹ ∈ U₁ := fun x hx => (mem_normalizer_iff.mp htU x).mp hx
  have hconj : ∀ g x y : G, g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := fun g x y => by
    simp only [commutatorElement_def]
    group
  obtain ⟨γ₀₀, γ₀₀', γ₀₁, γ₀₁', γ₁₀, γ₁₀', γ₁₁, γ₁₁', hχ₁⟩ := hP.exists_commutator_form hf hR hU
    hb_add hb_T hb_d hinj hsurj χ₁ hP.chi₁_mul hP.chi₁_conj
  obtain ⟨ε₀₀, ε₀₀', ε₀₁, ε₀₁', ε₁₀, ε₁₀', ε₁₁, ε₁₁', hχ₂⟩ := hP.exists_commutator_form hf hR hU
    hb_add hb_T hb_d hinj hsurj χ₂ hP.chi₂_mul hP.chi₂_conj
  simp only [← hσ] at hχ₁ hχ₂
  choose s hsU hsa hsb using hsurj
  have hgen₁ : ∀ x ∈ U₁, ∀ y ∈ U₁, χ₁ ⁅x, y⁆ = χ₁ ⁅s (a x) (b x), s (a y) (b y)⁆ :=
    fun x hx y hy => by rw [hχ₁ x hx y hy, hχ₁ _ (hsU _ _) _ (hsU _ _), hsa, hsa, hsb, hsb]
  have hgen₂ : ∀ x ∈ U₁, ∀ y ∈ U₁, χ₂ ⁅x, y⁆ = χ₂ ⁅s (a x) (b x), s (a y) (b y)⁆ :=
    fun x hx y hy => by rw [hχ₂ x hx y hy, hχ₂ _ (hsU _ _) _ (hsU _ _), hsa, hsa, hsb, hsb]
  have hP₁ : ∀ X₀ X₁ Y₀ Y₁, χ₁ ⁅s X₁ X₀, s Y₁ Y₀⁆ =
      (γ₀₀ * (X₀ * σ Y₀) + γ₀₀' * (σ X₀ * Y₀)) + (γ₀₁ * (X₀ * σ Y₁) + γ₀₁' * (σ X₀ * Y₁)) +
        (γ₁₀ * (X₁ * σ Y₀) + γ₁₀' * (σ X₁ * Y₀)) + (γ₁₁ * (X₁ * σ Y₁) + γ₁₁' * (σ X₁ * Y₁)) :=
    fun X₀ X₁ Y₀ Y₁ => by rw [hχ₁ _ (hsU _ _) _ (hsU _ _), hsa, hsa, hsb, hsb]
  have hP₂ : ∀ X₀ X₁ Y₀ Y₁, χ₂ ⁅s X₁ X₀, s Y₁ Y₀⁆ =
      (ε₀₀ * (X₀ * σ Y₀) + ε₀₀' * (σ X₀ * Y₀)) + (ε₀₁ * (X₀ * σ Y₁) + ε₀₁' * (σ X₀ * Y₁)) +
        (ε₁₀ * (X₁ * σ Y₀) + ε₁₀' * (σ X₁ * Y₀)) + (ε₁₁ * (X₁ * σ Y₁) + ε₁₁' * (σ X₁ * Y₁)) :=
    fun X₀ X₁ Y₀ Y₁ => by rw [hχ₂ _ (hsU _ _) _ (hsU _ _), hsa, hsa, hsb, hsb]
  have ht₁ : ∀ X₀ X₁ Y₀ Y₁, χ₁ ⁅s X₁ (X₀ + X₁), s Y₁ (Y₀ + Y₁)⁆ = χ₁ ⁅s X₁ X₀, s Y₁ Y₀⁆ := by
    intro X₀ X₁ Y₀ Y₁
    have hx := hsU X₁ X₀
    have hy := hsU Y₁ Y₀
    have e := hgen₁ _ (htU' _ hx) _ (htU' _ hy)
    rw [← hconj, hP.chi₁_conj_t _ (hcomR _ hx _ hy), hP.a_conj_t _ hx, hP.a_conj_t _ hy,
      hb_t _ hx, hb_t _ hy, hsa, hsa, hsb, hsb] at e
    rw [add_comm X₀ X₁, add_comm Y₀ Y₁]
    exact e.symm
  have ht₂ : ∀ X₀ X₁ Y₀ Y₁, χ₂ ⁅s X₁ (X₀ + X₁), s Y₁ (Y₀ + Y₁)⁆ =
      χ₁ ⁅s X₁ X₀, s Y₁ Y₀⁆ + χ₂ ⁅s X₁ X₀, s Y₁ Y₀⁆ := by
    intro X₀ X₁ Y₀ Y₁
    have hx := hsU X₁ X₀
    have hy := hsU Y₁ Y₀
    have e := hgen₂ _ (htU' _ hx) _ (htU' _ hy)
    rw [← hconj, hP.chi₂_conj_t _ (hcomR _ hx _ hy), hP.a_conj_t _ hx, hP.a_conj_t _ hy,
      hb_t _ hx, hb_t _ hy, hsa, hsa, hsb, hsb] at e
    rw [add_comm X₀ X₁, add_comm Y₀ Y₁]
    exact e.symm
  have hTa : ∀ y ∈ szT₁ L T, a y = 0 := fun y hy => (hP.a_eq_zero_iff _ (hTU hy)).mpr (by
    rw [show t * y * t⁻¹ = y by rw [← hR.t_comm _ hy, mul_inv_cancel_right], ← sq]
    exact hU.sq_mem _ (hTU hy))
  have hTb : ∀ y ∈ szT₁ L T, b y = u y := fun y hy => by
    have := hb_T y hy 1 (one_mem _)
    rwa [mul_one] at this
  have hTcomm : ∀ y ∈ szT₁ L T, ∀ y' ∈ szT₁ L T, ⁅y, y'⁆ ∈ szA₁ (szT₁ L T) := by
    intro y hy y' hy'
    have hmem : ⁅y, y'⁆ ∈ szT₁ L T := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hy hy') (inv_mem hy)) (inv_mem hy')
    exact (hS.mem_szA₁_iff _ hmem).mpr (hc.u_commutator hy hy')
  have hT₁ : ∀ X₀ Y₀, χ₁ ⁅s 0 X₀, s 0 Y₀⁆ = 0 := by
    intro X₀ Y₀
    obtain ⟨y, hy, rfl⟩ := hc.u_surj X₀
    obtain ⟨y', hy', rfl⟩ := hc.u_surj Y₀
    have e := hgen₁ _ (hTU hy) _ (hTU hy')
    rw [hTa y hy, hTa y' hy', hTb y hy, hTb y' hy'] at e
    rw [← e]
    exact hP.chi₁_of_mem_szA₁ _ (hTcomm y hy y' hy')
  have hT₂ : ∀ X₀ Y₀, χ₂ ⁅s 0 X₀, s 0 Y₀⁆ = TraceForm.form σ X₀ Y₀ := by
    intro X₀ Y₀
    obtain ⟨y, hy, rfl⟩ := hc.u_surj X₀
    obtain ⟨y', hy', rfl⟩ := hc.u_surj Y₀
    have e := hgen₂ _ (hTU hy) _ (hTU hy')
    rw [hTa y hy, hTa y' hy', hTb y hy, hTb y' hy'] at e
    rw [← e, hP.chi₂_of_mem_szA₁ _ (hTcomm y hy y' hy'), hc.v_commutator hy hy',
      TraceForm.form]
    linear_combination (-(u y * σ (u y'))) * h2
  obtain ⟨g, δ, hδ, hform⟩ := pencilNF_normalForm hσσ hβ₀
    (fun X₀ X₁ Y₀ Y₁ => χ₁ ⁅s X₁ X₀, s Y₁ Y₀⁆) (fun X₀ X₁ Y₀ Y₁ => χ₂ ⁅s X₁ X₀, s Y₁ Y₀⁆)
    hP₁ hP₂ (fun X₀ X₁ Y₀ Y₁ => hP.sigma_chi₁ _ (hcomR _ (hsU _ _) _ (hsU _ _)))
    (fun X₀ X₁ Y₀ Y₁ => hP.sigma_chi₂ _ (hcomR _ (hsU _ _) _ (hsU _ _)))
    (fun X₀ X₁ => by rw [commutatorElement_self]; exact hP.chi₂_one) ht₁ ht₂ hT₁ hT₂
  have hform' : ∀ X₀ X₁ Y₀ Y₁,
      χ₁ ⁅s X₁ X₀, s Y₁ Y₀⁆ = TraceForm.form σ (X₀ + σ g * X₁) Y₁ +
        TraceForm.form σ X₁ (Y₀ + σ g * Y₁) + TraceForm.form σ X₁ Y₁ ∧
      χ₂ ⁅s X₁ X₀, s Y₁ Y₀⁆ = TraceForm.form σ (X₀ + σ g * X₁) (Y₀ + σ g * Y₁) +
        δ * TraceForm.form σ X₁ Y₁ := hform
  have hcomm₁ : ∀ x ∈ U₁, ∀ y ∈ U₁, χ₁ ⁅x, y⁆ = TraceForm.form σ (b x + σ g * a x) (a y) +
      TraceForm.form σ (a x) (b y + σ g * a y) + TraceForm.form σ (a x) (a y) :=
    fun x hx y hy => by rw [hgen₁ x hx y hy]; exact (hform' _ _ _ _).1
  have hcomm₂ : ∀ x ∈ U₁, ∀ y ∈ U₁, χ₂ ⁅x, y⁆ =
      TraceForm.form σ (b x + σ g * a x) (b y + σ g * a y) + δ * TraceForm.form σ (a x) (a y) :=
    fun x hx y hy => by rw [hgen₂ x hx y hy]; exact (hform' _ _ _ _).2
  have hsurj' : ∀ α β : E, ∃ x ∈ U₁, a x = α ∧ b x = β := fun α β =>
    ⟨s α β, hsU α β, hsa α β, hsb α β⟩
  have hb1 : b 1 = 0 := by
    have := hb_add 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    linear_combination -this
  have hainv : ∀ x ∈ U₁, a x⁻¹ = a x := fun x hx => by rw [hP.a_inv hx, CharTwo.neg_eq]
  have hbinv : ∀ x ∈ U₁, b x⁻¹ = b x := fun x hx => by
    have h1 := hb_add x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, hb1] at h1
    linear_combination -h1 - b x * h2
  have hbR : ∀ r ∈ R₂, b r = 0 := fun r hr => by
    have := hb_T 1 (one_mem _) r hr
    rwa [one_mul, hc.u_one] at this
  have haR : ∀ r ∈ R₂, a r = 0 := fun r hr => hP.a_eq_zero_of_mem hRU hR.tN hr
  have hsq : ∀ x ∈ U₁, ∀ y ∈ U₁, (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅y⁻¹, x⁻¹⁆ := by
    intro x hx y hy
    have hcy := hUR y hy _ (hcomR _ (inv_mem hy) _ (inv_mem hx))
    calc (x * y) ^ 2 = x ^ 2 * y * (⁅y⁻¹, x⁻¹⁆ * y) := by
          rw [sq (x * y), sq x, commutatorElement_def]; group
      _ = x ^ 2 * y * (y * ⁅y⁻¹, x⁻¹⁆) := by rw [← hcy]
      _ = x ^ 2 * y ^ 2 * ⁅y⁻¹, x⁻¹⁆ := by group
  have hsqd : ∀ x : G, (d * x * d⁻¹) ^ 2 = d * x ^ 2 * d⁻¹ := fun x => by
    rw [sq, sq]; group
  have hNμ : μ ^ (2 ^ f + 1) = μ * σ μ := by rw [hσ, pow_succ']
  have hsqR : ∀ x ∈ U₁, ∀ y ∈ U₁, x ^ 2 * y ^ 2 ∈ R₂ := fun x hx y hy =>
    mul_mem (hU.sq_mem x hx) (hU.sq_mem y hy)
  have hsq₁ : ∀ x ∈ U₁, χ₁ (x ^ 2) - (TraceForm.form σ (b x + σ g * a x) (a x) +
      a x * σ (a x)) = 0 := fun x hx =>
    hP.eq_zero_of_additive_weight hf hb_add hb_d hinj hsurj' hRU
      (D := fun x => χ₁ (x ^ 2) - (TraceForm.form σ (b x + σ g * a x) (a x) + a x * σ (a x)))
      (fun x hx y hy => by
        rw [hsq x hx y hy, hP.chi₁_mul _ (hsqR x hx y hy) _ (hcomR _ (inv_mem hy) _ (inv_mem hx)),
          hP.chi₁_mul _ (hU.sq_mem x hx) _ (hU.sq_mem y hy), hcomm₁ _ (inv_mem hy) _ (inv_mem hx),
          hainv x hx, hainv y hy, hbinv x hx, hbinv y hy, hP.a_mul _ hx _ hy, hb_add _ hx _ hy]
        simp only [TraceForm.form, map_add, map_mul]
        ring)
      (fun r hr => by
        rw [hU.sq_R₂ r hr, hP.chi₁_one, haR r hr, hbR r hr]
        simp [TraceForm.form])
      (fun x hx => by
        rw [hsqd, hP.chi₁_conj _ (hU.sq_mem x hx), hP.a_conj_d hx, hb_d _ hx, hNμ]
        simp only [TraceForm.form, map_add, map_mul]
        ring) hx
  have hsq₂ : ∀ x ∈ U₁, χ₂ (x ^ 2) - ((b x + σ g * a x) * σ (b x + σ g * a x) +
      δ * (a x * σ (a x))) = 0 := fun x hx =>
    hP.eq_zero_of_additive_weight hf hb_add hb_d hinj hsurj' hRU
      (D := fun x => χ₂ (x ^ 2) - ((b x + σ g * a x) * σ (b x + σ g * a x) +
        δ * (a x * σ (a x))))
      (fun x hx y hy => by
        rw [hsq x hx y hy, hP.chi₂_mul _ (hsqR x hx y hy) _ (hcomR _ (inv_mem hy) _ (inv_mem hx)),
          hP.chi₂_mul _ (hU.sq_mem x hx) _ (hU.sq_mem y hy), hcomm₂ _ (inv_mem hy) _ (inv_mem hx),
          hainv x hx, hainv y hy, hbinv x hx, hbinv y hy, hP.a_mul _ hx _ hy, hb_add _ hx _ hy]
        simp only [TraceForm.form, map_add, map_mul]
        ring)
      (fun r hr => by
        rw [hU.sq_R₂ r hr, hP.chi₂_one, haR r hr, hbR r hr]
        simp)
      (fun x hx => by
        rw [hsqd, hP.chi₂_conj _ (hU.sq_mem x hx), hP.a_conj_d hx, hb_d _ hx, hNμ]
        simp only [map_add, map_mul]
        ring) hx
  exact ⟨g, δ, hδ, fun x hx y hy => ⟨hcomm₁ x hx y hy, hcomm₂ x hx y hy⟩, fun x hx =>
    ⟨sub_eq_zero.mp (hsq₁ x hx), sub_eq_zero.mp (hsq₂ x hx)⟩⟩

end U3PencilCoords

end CFSG.SeitzReduction.RankOne
