module

public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem inner_field_automorphism_normal_form_of_params
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f)
    (hA : ∀ β ∈ unipotentPairAut τ K, ∃ (a : Fin τ.rank → Kˣ) (σ : K ≃+* K),
      β = exactNormalAut τ K a σ 0)
    (hdC : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ adjointGroup τ K) :
    (∀ α : MulAut (adjointGroup τ K), ∃! gσ : adjointGroup τ K × (K ≃+* K),
      ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (gσ.1 : ModGL τ K) *
        Units.map (entrywiseHom gσ.2.toRingHom) (h : ModGL τ K) * (gσ.1 : ModGL τ K)⁻¹) ∧
    ∃ Θ : MulAut (adjointGroup τ K) →* (K ≃+* K),
      (∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (σ : K ≃+* K),
        (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) →
        Θ α = σ) ∧
      Function.Surjective Θ ∧
      Θ.ker = (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ∧
      ∀ α : MulAut (adjointGroup τ K), α ^ 2 = 1 → Θ α = 1 ∨
        (Even f ∧ ∀ c, Θ α c = c ^ (p ^ (f / 2))) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  set E : (K ≃+* K) → MulAut (adjointGroup τ K) := fun σ => exactNormalAut τ K 1 σ 0
  have hE1 : E 1 = 1 := exactNormalAut_one_one_zero
  have hE : ∀ σ (h : adjointGroup τ K),
      (E σ h : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) := fun σ h => by
    change (exactNormalAut τ K 1 σ 0 h : ModGL τ K) = _
    rw [coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]
  have hNF : ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (σ : K ≃+* K),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) ↔
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
  have hex : ∀ α : MulAut (adjointGroup τ K), ∃ g σ, α = MulAut.conj g * E σ := by
    intro α
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
    obtain ⟨c, β, hU, hV, rfl⟩ :=
      (exceptional_ordinary_Sylow_opposition τ K p w₀ hw₀).2.2.2.2.2 α
    obtain ⟨a, σ, rfl⟩ := hA β ⟨hU, hV⟩
    refine ⟨c * ⟨rootDiagUnit τ a, hdC a⟩, σ, MulEquiv.ext fun h => Subtype.ext ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_mul, coe_exactNormalAut_zero, Subgroup.coe_mul,
      Subgroup.coe_mul, hE, Subgroup.coe_inv, Subgroup.coe_inv, Subgroup.coe_mul]
    group
  have huniq : ∀ (g g' : adjointGroup τ K) (σ σ' : K ≃+* K),
      MulAut.conj g * E σ = MulAut.conj g' * E σ' → g = g' ∧ σ = σ' := by
    intro g g' σ σ' h
    have e : E σ' * (E σ)⁻¹ = MulAut.conj (g'⁻¹ * g) := by
      have h' : E σ' = (MulAut.conj g')⁻¹ * MulAut.conj g * E σ := by
        rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h', mul_inv_cancel_right, map_mul, map_inv]
    have hA' : MulAut.conj (g'⁻¹ * g) ∈ unipotentPairAut τ K := by
      rw [← e]
      exact mul_mem (exactNormalAut_mem _ _ _) (inv_mem (exactNormalAut_mem _ _ _))
    obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hA'
    have e2 : exactNormalAut τ K (b * 1) σ 0 = exactNormalAut τ K 1 σ' 0 := by
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
  have hmul : ∀ α β : MulAut (adjointGroup τ K), σF (α * β) = σF α * σF β := by
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
  let Θ : MulAut (adjointGroup τ K) →* (K ≃+* K) :=
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
    · obtain ⟨hev, hpow, -⟩ := ringEquiv_sq_eq_one_facts hp hf hK h2 h1
      exact Or.inr ⟨hev, hpow⟩

theorem exists_exactNormalAut_zero_eq_E7_E8
    [Finite K] (hτ : τ = .E7 ∨ τ = .E8)
    {β : MulAut (adjointGroup τ K)} (hβ : β ∈ unipotentPairAut τ K) :
    ∃ (a : Fin τ.rank → Kˣ) (σ : K ≃+* K), β = exactNormalAut τ K a σ 0 := by
  obtain ⟨a, σ, ε, rfl⟩ := exists_exactNormalAut_eq (Or.inr hτ) hβ
  have hE : exactE τ = 1 := by
    rcases hτ with rfl | rfl <;> rfl
  have hε : (ε : ℕ) = 0 := by
    have := ε.isLt
    omega
  exact ⟨a, σ, by rw [hε]⟩

theorem rootDiagUnit_mem_adjointGroup_E7_E8
    [Finite K] (hτ : τ = .E7 ∨ τ = .E8)
    (hK : ringChar K = 2) (a : Fin τ.rank → Kˣ) : rootDiagUnit τ a ∈ adjointGroup τ K := by
  have hT := (even_power_two_Cartan_root_diagonals_inner τ
    (Or.inr (Or.inr (Or.inr hτ))) K hK).1 a
  have hle : torusGroup τ K ≤ adjointGroup τ K :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  exact hle hT

theorem even_E7_E8_exact_inner_field_automorphism_normal_form
    {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f) (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) :
    (∀ α : MulAut (adjointGroup τ K), ∃! gσ : adjointGroup τ K × (K ≃+* K),
      ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (gσ.1 : ModGL τ K) *
        Units.map (entrywiseHom gσ.2.toRingHom) (h : ModGL τ K) * (gσ.1 : ModGL τ K)⁻¹) ∧
    ∃ Θ : MulAut (adjointGroup τ K) →* (K ≃+* K),
      (∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (σ : K ≃+* K),
        (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) →
        Θ α = σ) ∧
      Function.Surjective Θ ∧
      Θ.ker = (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ∧
      ∀ α : MulAut (adjointGroup τ K), α ^ 2 = 1 → Θ α = 1 ∨
        (Even f ∧ ∀ c, Θ α c = c ^ (2 ^ (f / 2))) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hchar : ringChar K = 2 := ringChar.eq K 2
  exact inner_field_automorphism_normal_form_of_params Nat.prime_two hf hK
    (fun β hβ => exists_exactNormalAut_zero_eq_E7_E8 hτ hβ)
    (rootDiagUnit_mem_adjointGroup_E7_E8 hτ hchar)

end CFSG.LieType.Chevalley
