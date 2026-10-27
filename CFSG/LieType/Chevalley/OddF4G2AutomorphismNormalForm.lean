module

public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LieType.Chevalley.OddRootPairPermutation
public import CFSG.LieType.Chevalley.RootDiagonalTorusWords
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem exactNormalAut_zero_adjX
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (i : Fin τ.rank) (c : K) :
    exactNormalAut τ K a σ 0 (adjX τ K i c) = adjX τ K i ((a i : K) * σ c) := by
  rw [exactNormalAut_adjX, exactPerm_zero, Equiv.Perm.one_apply]

theorem exactNormalAut_zero_adjY
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (i : Fin τ.rank) (c : K) :
    exactNormalAut τ K a σ 0 (adjY τ K i c) = adjY τ K i ((((a i)⁻¹ : Kˣ) : K) * σ c) := by
  rw [exactNormalAut_adjY, exactPerm_zero, Equiv.Perm.one_apply]

theorem coe_exactNormalAut_zero
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (h : adjointGroup τ K) :
    (exactNormalAut τ K a σ 0 h : ModGL τ K) =
      rootDiagUnit τ a * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
        (rootDiagUnit τ a)⁻¹ := by
  rw [coe_exactNormalAut, exactQ_zero, mul_one, inv_one, mul_one]

theorem exactNormalAut_zero_injective
    {a a' : Fin τ.rank → Kˣ} {σ σ' : K ≃+* K}
    (h : exactNormalAut τ K a σ 0 = exactNormalAut τ K a' σ' 0) : a = a' ∧ σ = σ' := by
  have e : ∀ j c, (a j : K) * σ c = a' j * σ' c := fun j c => by
    have := congrArg (fun φ : MulAut (adjointGroup τ K) => φ (adjX τ K j c)) h
    simp only [exactNormalAut_zero_adjX] at this
    exact adjX_injective _ this
  have ha : a = a' := funext fun j => Units.ext (by simpa using e j 1)
  subst ha
  exact ⟨rfl, RingEquiv.ext fun c => mul_left_cancel₀ (a ⟨0, τ.rank_pos⟩).ne_zero (e _ c)⟩

theorem exactNormalAut_one_zero_mul
    (σ σ' : K ≃+* K) :
    exactNormalAut τ K 1 σ 0 * exactNormalAut τ K 1 σ' 0 = exactNormalAut τ K 1 (σ * σ') 0 := by
  rw [exactNormalAut_mul]
  congr 1
  funext j
  simp

theorem exactNormalAut_one_one_zero
    : exactNormalAut τ K 1 (1 : K ≃+* K) 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one, MulAut.one_apply]
    exact Units.ext (entrywise_id _))

theorem exists_exactNormalAut_zero_eq
    [Finite K] (hK : ringChar K ≠ 2)
    (hτ : τ = .F4 ∨ (τ = .G2 ∧ ringChar K ≠ 3)) {β : MulAut (adjointGroup τ K)}
    (hβ : β ∈ unipotentPairAut τ K) : ∃ a σ, β = exactNormalAut τ K a σ 0 := by
  obtain ⟨⟨π, hπ, -⟩, hrest⟩ := odd_root_pair_permutation_torus_compatibility τ K hK hβ
  obtain ⟨-, -, -, hF4, hG2⟩ := hrest π hπ
  have hπ1 : π = 1 := by
    rcases hτ with rfl | ⟨rfl, h3⟩
    · exact hF4 rfl
    · exact hG2 rfl h3
  subst hπ1
  have hβ' : β ∈ rootPairAut τ K := mem_rootPairAut.2 fun i => ⟨(hπ i).1, (hπ i).2⟩
  obtain ⟨p, hp, -⟩ := (ordinary_Chevalley_root_pair_common_field_parameter τ K).1 β hβ'
  refine ⟨p.1, p.2, mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_⟩
  · rw [(hp i).1, exactNormalAut_zero_adjX]
  · rw [(hp i).2.1, exactNormalAut_zero_adjY]


theorem odd_F4_and_nonexceptional_G2_automorphism_normal_form
    {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = p ^ f) (τ : Tag)
    (hτ : τ = .F4 ∨ (τ = .G2 ∧ p ≠ 3)) :
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
        (Even f ∧ (∀ c, Θ α c = c ^ (p ^ (f / 2))) ∧
          Nat.card (fixSubfield (Θ α)) = p ^ (f / 2)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have : Fact p.Prime := ⟨hp⟩
  have hchar : ringChar K = p := ringChar.eq K p
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  have hτ' : τ = .F4 ∨ (τ = .G2 ∧ ringChar K ≠ 3) := by
    rcases hτ with h | ⟨h, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, hchar ▸ h3⟩
  have hFG : τ = .G2 ∨ τ = .F4 := by
    rcases hτ with h | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  have hdC : ∀ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ adjointGroup τ K := fun a => by
    obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner τ hFG K
    exact (hrest B hB a).2.2.1
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
    obtain ⟨a, σ, rfl⟩ := exists_exactNormalAut_zero_eq hK2 hτ' (β := β) ⟨hU, hV⟩
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
    have hA : MulAut.conj (g'⁻¹ * g) ∈ unipotentPairAut τ K := by
      rw [← e]
      exact mul_mem (exactNormalAut_mem _ _ _) (inv_mem (exactNormalAut_mem _ _ _))
    obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hA
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
    · obtain ⟨hev, hpow, hcard⟩ := ringEquiv_sq_eq_one_facts hp hf hK h2 h1
      exact Or.inr ⟨hev, hpow, hcard⟩

end CFSG.LieType.Chevalley
