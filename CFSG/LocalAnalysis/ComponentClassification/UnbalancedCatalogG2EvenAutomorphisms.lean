module

public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm
public import CFSG.LieType.Chevalley.G2FieldFourEvenSimplePairs

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem exists_exactNormalAut_zero_eq_of_even_G2 [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {β : MulAut (adjointGroup .G2 K)} (hβ : β ∈ unipotentPairAut .G2 K) :
    ∃ a σ, β = exactNormalAut .G2 K a σ 0 := by
  have hβ' : β ∈ rootPairAut .G2 K := mem_rootPairAut.2 fun i =>
    even_G2_opposite_Sylow_stabilizer_fixes_simple_pairs K hK hβ i
  obtain ⟨p, hp, -⟩ := (ordinary_Chevalley_root_pair_common_field_parameter .G2 K).1 β hβ'
  refine ⟨p.1, p.2, mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_⟩
  · rw [(hp i).1, exactNormalAut_zero_adjX]
  · rw [(hp i).2.1, exactNormalAut_zero_adjY]

theorem even_G2_exact_automorphism_normal_form {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) :
    (∀ α : MulAut (adjointGroup .G2 K), ∃! gσ : adjointGroup .G2 K × (K ≃+* K),
      ∀ h : adjointGroup .G2 K, (α h : ModGL .G2 K) = (gσ.1 : ModGL .G2 K) *
        Units.map (entrywiseHom gσ.2.toRingHom) (h : ModGL .G2 K) * (gσ.1 : ModGL .G2 K)⁻¹) ∧
    ∃ Θ : MulAut (adjointGroup .G2 K) →* (K ≃+* K),
      (∀ (α : MulAut (adjointGroup .G2 K)) (g : adjointGroup .G2 K) (σ : K ≃+* K),
        (∀ h : adjointGroup .G2 K, (α h : ModGL .G2 K) = (g : ModGL .G2 K) *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹) →
        Θ α = σ) ∧
      Function.Surjective Θ ∧
      Θ.ker = (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ∧
      ∀ α : MulAut (adjointGroup .G2 K), α ^ 2 = 1 → Θ α = 1 ∨
        (Even f ∧ (∀ c, Θ α c = c ^ (2 ^ (f / 2))) ∧
          Nat.card (fixSubfield (Θ α)) = 2 ^ (f / 2)) := by
  classical
  have hp : Nat.Prime 2 := Nat.prime_two
  have hf1 : 1 ≤ f := le_trans (by norm_num) hf
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : CharP K 2 := finite_field_prime_power_characteristic hp hf1 hK
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdC : ∀ a : Fin Tag.G2.rank → Kˣ, rootDiagUnit .G2 a ∈ adjointGroup .G2 K := fun a => by
    obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K
    exact (hrest B hB a).2.2.1
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  set E : (K ≃+* K) → MulAut (adjointGroup .G2 K) := fun σ => exactNormalAut .G2 K 1 σ 0
  have hE1 : E 1 = 1 := exactNormalAut_one_one_zero
  have hE : ∀ σ (h : adjointGroup .G2 K),
      (E σ h : ModGL .G2 K) = Units.map (entrywiseHom σ.toRingHom) (h : ModGL .G2 K) :=
    fun σ h => by
      change (exactNormalAut .G2 K 1 σ 0 h : ModGL .G2 K) = _
      rw [coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]
  have hNF : ∀ (α : MulAut (adjointGroup .G2 K)) (g : adjointGroup .G2 K) (σ : K ≃+* K),
      (∀ h : adjointGroup .G2 K, (α h : ModGL .G2 K) = (g : ModGL .G2 K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹) ↔
      α = MulAut.conj g * E σ := by
    intro α g σ
    constructor
    · intro h
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, hE,
        Subgroup.coe_inv]
    · rintro rfl h
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, hE,
        Subgroup.coe_inv]
  have hex : ∀ α : MulAut (adjointGroup .G2 K), ∃ g σ, α = MulAut.conj g * E σ := by
    intro α
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem .G2).length
    obtain ⟨c, β, hU, hV, rfl⟩ :=
      (exceptional_ordinary_Sylow_opposition .G2 K 2 w₀ hw₀).2.2.2.2.2 α
    obtain ⟨a, σ, rfl⟩ := exists_exactNormalAut_zero_eq_of_even_G2 hK4 (β := β) ⟨hU, hV⟩
    refine ⟨c * ⟨rootDiagUnit .G2 a, hdC a⟩, σ, MulEquiv.ext fun h => Subtype.ext ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_mul, coe_exactNormalAut_zero, Subgroup.coe_mul,
      Subgroup.coe_mul, hE, Subgroup.coe_inv, Subgroup.coe_inv, Subgroup.coe_mul]
    group
  have huniq : ∀ (g g' : adjointGroup .G2 K) (σ σ' : K ≃+* K),
      MulAut.conj g * E σ = MulAut.conj g' * E σ' → g = g' ∧ σ = σ' := by
    intro g g' σ σ' h
    have e : E σ' * (E σ)⁻¹ = MulAut.conj (g'⁻¹ * g) := by
      have h' : E σ' = (MulAut.conj g')⁻¹ * MulAut.conj g * E σ := by
        rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h', mul_inv_cancel_right, map_mul, map_inv]
    have hA : MulAut.conj (g'⁻¹ * g) ∈ unipotentPairAut .G2 K := by
      rw [← e]
      exact mul_mem (exactNormalAut_mem _ _ _) (inv_mem (exactNormalAut_mem _ _ _))
    obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hA
    have e2 : exactNormalAut .G2 K (b * 1) σ 0 = exactNormalAut .G2 K 1 σ' 0 := by
      rw [← exactNormalAut_diag_mul, ← hb, ← e, inv_mul_cancel_right]
    obtain ⟨hb1, hσ⟩ := exactNormalAut_zero_injective e2
    rw [mul_one] at hb1
    subst hb1
    refine ⟨?_, hσ⟩
    have h1 : MulAut.conj (g'⁻¹ * g) = 1 := by
      rw [hb]
      exact exactNormalAut_one_one_zero
    have h2 := mulAut_conj_injective_of_center_eq_bot hZ (h1.trans (map_one _).symm)
    exact (inv_mul_eq_one.1 h2).symm
  choose gF σF hF using hex
  have hΘ : ∀ α g σ, α = MulAut.conj g * E σ → σF α = σ := fun α g σ h =>
    (huniq _ _ _ _ ((hF α).symm.trans h)).2
  have hmul : ∀ α β : MulAut (adjointGroup .G2 K), σF (α * β) = σF α * σF β := by
    intro α β
    refine hΘ _ (gF α * E (σF α) (gF β)) _ ?_
    calc α * β = MulAut.conj (gF α) * E (σF α) * (MulAut.conj (gF β) * E (σF β)) := by
          rw [← hF α, ← hF β]
      _ = MulAut.conj (gF α) * (E (σF α) * MulAut.conj (gF β)) * E (σF β) := by
          simp only [mul_assoc]
      _ = MulAut.conj (gF α) * (MulAut.conj (E (σF α) (gF β)) * E (σF α)) * E (σF β) := by
          rw [mulAut_mul_conj]
      _ = MulAut.conj (gF α * E (σF α) (gF β)) * (E (σF α) * E (σF β)) := by
          rw [map_mul]
          simp only [mul_assoc]
      _ = MulAut.conj (gF α * E (σF α) (gF β)) * E (σF α * σF β) := by
          rw [exactNormalAut_one_zero_mul]
  have hone : σF 1 = 1 := hΘ 1 1 1 (by rw [map_one, one_mul, hE1])
  let Θ : MulAut (adjointGroup .G2 K) →* (K ≃+* K) :=
    { toFun := σF
      map_one' := hone
      map_mul' := hmul }
  refine ⟨fun α => ?_, Θ, fun α g σ h => hΘ α g σ ((hNF α g σ).1 h), fun σ => ?_, ?_,
    fun α hα => ?_⟩
  ·
    refine ⟨(gF α, σF α), (hNF α (gF α) (σF α)).2 (hF α), fun q hq => ?_⟩
    obtain ⟨h1, h2⟩ := huniq _ _ _ _ (((hNF α q.1 q.2).1 hq).symm.trans (hF α))
    exact Prod.ext h1 h2
  ·
    exact ⟨E σ, hΘ _ 1 σ (by rw [map_one, one_mul])⟩
  ·
    ext α
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      change σF α = 1 at h1
      have h' := hF α
      rw [h1, hE1, mul_one] at h'
      exact ⟨gF α, h'.symm⟩
    · rintro ⟨g, rfl⟩
      exact hΘ _ g 1 (by rw [hE1, mul_one])
  ·
    have h2 : σF α ^ 2 = 1 := by
      rw [pow_two, ← hmul, ← pow_two, hα, hone]
    by_cases h1 : σF α = 1
    · exact Or.inl h1
    · obtain ⟨hev, hpow, hcard⟩ := ringEquiv_sq_eq_one_facts hp hf1 hK h2 h1
      exact Or.inr ⟨hev, hpow, hcard⟩

end CFSG.ComponentClassification.UnbalancedCatalog
