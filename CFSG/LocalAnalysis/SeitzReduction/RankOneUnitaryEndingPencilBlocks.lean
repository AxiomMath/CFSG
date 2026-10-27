module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilArith
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilCoords

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pencilBl_conj_commutator {G : Type*} [Group G] (g x y : G) :
    g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem exists_block_form {G : Type*} [Group G] {K : Type*} [Field K] [Fintype K] {f : ℕ}
    (hf : 2 ≤ f) (hK : Fintype.card K = (2 ^ f) ^ 2) {U R : Subgroup G}
    (hUR : ∀ x ∈ U, ∀ r ∈ R, x * r = r * x) (hRab : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r)
    (hcom : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ R) (χ : G → K)
    (hχ : ∀ r ∈ R, ∀ r' ∈ R, χ (r * r') = χ r + χ r') {d : G} {μ : K} (hμ0 : μ ≠ 0)
    (hμ : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    (hdχ : ∀ r ∈ R, χ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ r)
    (s s' : K → G) (hs : ∀ α, s α ∈ U) (hs' : ∀ α, s' α ∈ U)
    (hsadd : ∀ α α', (s α * s α')⁻¹ * s (α + α') ∈ R)
    (hs'add : ∀ α α', (s' α * s' α')⁻¹ * s' (α + α') ∈ R)
    (hdU : ∀ x ∈ U, d * x * d⁻¹ ∈ U)
    (hsd : ∀ α, (d * s α * d⁻¹)⁻¹ * s (μ * α) ∈ R)
    (hs'd : ∀ α, (d * s' α * d⁻¹)⁻¹ * s' (μ * α) ∈ R) :
    ∃ γ γ' : K, ∀ α β, χ ⁅s α, s' β⁆ = γ * (α * β ^ 2 ^ f) + γ' * (α ^ 2 ^ f * β) := by
  have hcongL : ∀ x ∈ U, ∀ y ∈ U, ∀ r ∈ R, ⁅x * r, y⁆ = ⁅x, y⁆ := fun x _ y hy r hr =>
    SplitComm.mul_right_of_commute (hUR y hy r hr).symm
  have hcongR : ∀ x ∈ U, ∀ y ∈ U, ∀ r ∈ R, ⁅x, y * r⁆ = ⁅x, y⁆ := fun x hx y _ r hr =>
    SplitComm.mul_right_of_commute' (hUR x hx r hr).symm
  have hsplit : ∀ x y : G, y = x * (x⁻¹ * y) := fun x y => by group
  refine exists_eq_of_biadditive_equivariant' hf hK (fun α β => χ ⁅s α, s' β⁆) ?_ ?_ hμ0 hμ ?_
  · intro α α' β
    have hU2 := mul_mem (hs α) (hs α')
    rw [hsplit (s α * s α') (s (α + α')), hcongL _ hU2 _ (hs' β) _ (hsadd α α'),
      SplitComm.mul_left_eq (hUR _ (hs α) _ (hcom _ (hs α') _ (hs' β))).symm
        (hRab _ (hcom _ (hs α') _ (hs' β)) _ (hcom _ (hs α) _ (hs' β)))]
    exact hχ _ (hcom _ (hs α) _ (hs' β)) _ (hcom _ (hs α') _ (hs' β))
  · intro α β β'
    have hU2 := mul_mem (hs' β) (hs' β')
    rw [hsplit (s' β * s' β') (s' (β + β')), hcongR _ (hs α) _ hU2 _ (hs'add β β'),
      SplitComm.mul_right_eq (hUR _ (hs' β) _ (hcom _ (hs α) _ (hs' β'))).symm]
    exact hχ _ (hcom _ (hs α) _ (hs' β)) _ (hcom _ (hs α) _ (hs' β'))
  · intro α β
    rw [hsplit (d * s α * d⁻¹) (s (μ * α)), hcongL _ (hdU _ (hs α)) _ (hs' (μ * β)) _ (hsd α),
      hsplit (d * s' β * d⁻¹) (s' (μ * β)),
      hcongR _ (hdU _ (hs α)) _ (hdU _ (hs' β)) _ (hs'd β), ← pencilBl_conj_commutator,
      hdχ _ (hcom _ (hs α) _ (hs' β))]

namespace U3PencilCoords

variable {G : Type} [Group G] [Finite G] {L T R₂ U₁ : Subgroup G} {t : G} {f : ℕ} {E : Type}
  [Field E] [Fintype E] {σ : E →+* E} {u w : G → E} {d : G} {μ : E}
  {a χ₁ χ₂ : G → E}

theorem exists_commutator_form (hP : U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂)
    (hf : 2 ≤ f) (hR : U3R2 G L (szT₁ L T) R₂ t f) (hU : U3U1Data G L f t T R₂ U₁) {b : G → E}
    (hb_add : ∀ x ∈ U₁, ∀ y ∈ U₁, b (x * y) = b x + b y)
    (hb_T : ∀ y ∈ szT₁ L T, ∀ r ∈ R₂, b (y * r) = u y)
    (hb_d : ∀ x ∈ U₁, b (d * x * d⁻¹) = μ * b x)
    (hinj : ∀ x ∈ U₁, a x = 0 → b x = 0 → x ∈ R₂)
    (hsurj : ∀ α β : E, ∃ x ∈ U₁, a x = α ∧ b x = β) (χ : G → E)
    (hχ : ∀ r ∈ R₂, ∀ r' ∈ R₂, χ (r * r') = χ r + χ r')
    (hdχ : ∀ r ∈ R₂, χ (d * r * d⁻¹) = μ ^ (2 ^ f + 1) * χ r) :
    ∃ γ₀₀ γ₀₀' γ₀₁ γ₀₁' γ₁₀ γ₁₀' γ₁₁ γ₁₁' : E, ∀ x ∈ U₁, ∀ y ∈ U₁,
      χ ⁅x, y⁆ = (γ₀₀ * (b x * b y ^ 2 ^ f) + γ₀₀' * (b x ^ 2 ^ f * b y)) +
        (γ₀₁ * (b x * a y ^ 2 ^ f) + γ₀₁' * (b x ^ 2 ^ f * a y)) +
        (γ₁₀ * (a x * b y ^ 2 ^ f) + γ₁₀' * (a x ^ 2 ^ f * b y)) +
        (γ₁₁ * (a x * a y ^ 2 ^ f) + γ₁₁' * (a x ^ 2 ^ f * a y)) := by
  classical
  have hKE : Fintype.card E = (2 ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hP.semilinear.card]
  have hc := hP.semilinear.coords
  have hRU : R₂ ≤ U₁ := le_sup_right.trans hU.le
  have hTU : szT₁ L T ≤ U₁ := le_sup_left.trans hU.le
  have hUR : ∀ x ∈ U₁, ∀ r ∈ R₂, x * r = r * x := fun x hx r hr =>
    (mem_centralizer_iff.mp (hU.le_centralizer hx) r hr).symm
  have hcomR : ∀ x ∈ U₁, ∀ y ∈ U₁, ⁅x, y⁆ ∈ R₂ := fun x hx y hy => by
    rw [commutatorElement_def]
    exact hU.comm_mem x hx y hy
  have hdU : ∀ x ∈ U₁, d * x * d⁻¹ ∈ U₁ := fun x hx =>
    (mem_normalizer_iff.mp hP.d_mem_normalizer_U₁ x).mp hx
  have hb1 : b 1 = 0 := by
    have := hb_T 1 (one_mem _) 1 (one_mem _)
    rwa [mul_one, hc.u_one] at this
  have hbinv : ∀ x ∈ U₁, b x⁻¹ = -b x := by
    intro x hx
    have h1 := hb_add x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, hb1] at h1
    linear_combination -h1
  have hmod : ∀ x ∈ U₁, ∀ y ∈ U₁, a x = a y → b x = b y → x⁻¹ * y ∈ R₂ := by
    intro x hx y hy hab hbb
    refine hinj _ (mul_mem (inv_mem hx) hy) ?_ ?_
    · rw [hP.a_mul _ (inv_mem hx) _ hy, hP.a_inv hx, hab, neg_add_cancel]
    · rw [hb_add _ (inv_mem hx) _ hy, hbinv x hx, hbb, neg_add_cancel]
  choose s₀ hs₀T hs₀u using hc.u_surj
  choose s₁ hs₁U hs₁a hs₁b using fun α : E => hsurj α 0
  have hs₀U : ∀ β, s₀ β ∈ U₁ := fun β => hTU (hs₀T β)
  have hs₀a : ∀ β, a (s₀ β) = 0 := fun β => (hP.a_eq_zero_iff _ (hs₀U β)).mpr (by
    rw [show t * s₀ β * t⁻¹ = s₀ β by rw [← hR.t_comm _ (hs₀T β), mul_inv_cancel_right], ← sq]
    exact hU.sq_mem _ (hs₀U β))
  have hs₀b : ∀ β, b (s₀ β) = β := fun β => by
    have := hb_T (s₀ β) (hs₀T β) 1 (one_mem _)
    rwa [mul_one, hs₀u] at this
  have hadd₀ : ∀ β β', (s₀ β * s₀ β')⁻¹ * s₀ (β + β') ∈ R₂ := fun β β' =>
    hmod _ (mul_mem (hs₀U β) (hs₀U β')) _ (hs₀U _)
      (by rw [hP.a_mul _ (hs₀U β) _ (hs₀U β'), hs₀a, hs₀a, hs₀a, add_zero])
      (by rw [hb_add _ (hs₀U β) _ (hs₀U β'), hs₀b, hs₀b, hs₀b])
  have hadd₁ : ∀ α α', (s₁ α * s₁ α')⁻¹ * s₁ (α + α') ∈ R₂ := fun α α' =>
    hmod _ (mul_mem (hs₁U α) (hs₁U α')) _ (hs₁U _)
      (by rw [hP.a_mul _ (hs₁U α) _ (hs₁U α'), hs₁a, hs₁a, hs₁a])
      (by rw [hb_add _ (hs₁U α) _ (hs₁U α'), hs₁b, hs₁b, hs₁b, add_zero])
  have hd₀ : ∀ β, (d * s₀ β * d⁻¹)⁻¹ * s₀ (μ * β) ∈ R₂ := fun β =>
    hmod _ (hdU _ (hs₀U β)) _ (hs₀U _) (by rw [hP.a_conj_d (hs₀U β), hs₀a, hs₀a, mul_zero])
      (by rw [hb_d _ (hs₀U β), hs₀b, hs₀b])
  have hd₁ : ∀ α, (d * s₁ α * d⁻¹)⁻¹ * s₁ (μ * α) ∈ R₂ := fun α =>
    hmod _ (hdU _ (hs₁U α)) _ (hs₁U _) (by rw [hP.a_conj_d (hs₁U α), hs₁a, hs₁a])
      (by rw [hb_d _ (hs₁U α), hs₁b, hs₁b, mul_zero])
  obtain ⟨γ₀₀, γ₀₀', h00⟩ := exists_block_form hf hKE hUR hR.comm hcomR χ hχ hP.mu_ne_zero
    hP.orderOf_mu hdχ s₀ s₀ hs₀U hs₀U hadd₀ hadd₀ hdU hd₀ hd₀
  obtain ⟨γ₀₁, γ₀₁', h01⟩ := exists_block_form hf hKE hUR hR.comm hcomR χ hχ hP.mu_ne_zero
    hP.orderOf_mu hdχ s₀ s₁ hs₀U hs₁U hadd₀ hadd₁ hdU hd₀ hd₁
  obtain ⟨γ₁₀, γ₁₀', h10⟩ := exists_block_form hf hKE hUR hR.comm hcomR χ hχ hP.mu_ne_zero
    hP.orderOf_mu hdχ s₁ s₀ hs₁U hs₀U hadd₁ hadd₀ hdU hd₁ hd₀
  obtain ⟨γ₁₁, γ₁₁', h11⟩ := exists_block_form hf hKE hUR hR.comm hcomR χ hχ hP.mu_ne_zero
    hP.orderOf_mu hdχ s₁ s₁ hs₁U hs₁U hadd₁ hadd₁ hdU hd₁ hd₁
  have hexp : ∀ p ∈ U₁, ∀ q ∈ U₁, ∀ p' ∈ U₁, ∀ q' ∈ U₁,
      χ ⁅p * q, p' * q'⁆ = χ ⁅p, p'⁆ + χ ⁅p, q'⁆ + χ ⁅q, p'⁆ + χ ⁅q, q'⁆ := by
    intro p hp q hq p' hp' q' hq'
    have hpq' := mul_mem hp' hq'
    rw [SplitComm.mul_left_eq (hUR _ hp _ (hcomR _ hq _ hpq')).symm
        (hR.comm _ (hcomR _ hq _ hpq') _ (hcomR _ hp _ hpq')),
      SplitComm.mul_right_eq (hUR _ hp' _ (hcomR _ hp _ hq')).symm,
      SplitComm.mul_right_eq (hUR _ hp' _ (hcomR _ hq _ hq')).symm,
      hχ _ (mul_mem (hcomR _ hp _ hp') (hcomR _ hp _ hq')) _
        (mul_mem (hcomR _ hq _ hp') (hcomR _ hq _ hq')),
      hχ _ (hcomR _ hp _ hp') _ (hcomR _ hp _ hq'), hχ _ (hcomR _ hq _ hp') _ (hcomR _ hq _ hq')]
    ring
  have hdec : ∀ z ∈ U₁, (s₀ (b z) * s₁ (a z))⁻¹ * z ∈ R₂ := fun z hz =>
    hmod _ (mul_mem (hs₀U _) (hs₁U _)) _ hz
      (by rw [hP.a_mul _ (hs₀U _) _ (hs₁U _), hs₀a, hs₁a, zero_add])
      (by rw [hb_add _ (hs₀U _) _ (hs₁U _), hs₀b, hs₁b, add_zero])
  have hsplit : ∀ x y : G, y = x * (x⁻¹ * y) := fun x y => by group
  have hred : ∀ z ∈ U₁, ∀ z' ∈ U₁,
      ⁅z, z'⁆ = ⁅s₀ (b z) * s₁ (a z), s₀ (b z') * s₁ (a z')⁆ := by
    intro z hz z' hz'
    have hm := mul_mem (hs₀U (b z)) (hs₁U (a z))
    have hm' := mul_mem (hs₀U (b z')) (hs₁U (a z'))
    conv_lhs => rw [hsplit (s₀ (b z) * s₁ (a z)) z, hsplit (s₀ (b z') * s₁ (a z')) z']
    rw [SplitComm.mul_right_of_commute (hUR _ (mul_mem hm' (hRU (hdec z' hz'))) _
        (hdec z hz)).symm,
      SplitComm.mul_right_of_commute' (hUR _ hm _ (hdec z' hz')).symm]
  refine ⟨γ₀₀, γ₀₀', γ₀₁, γ₀₁', γ₁₀, γ₁₀', γ₁₁, γ₁₁', fun x hx y hy => ?_⟩
  rw [hred x hx y hy, hexp _ (hs₀U _) _ (hs₁U _) _ (hs₀U _) _ (hs₁U _), h00, h01, h10, h11]

end U3PencilCoords

end CFSG.SeitzReduction.RankOne
