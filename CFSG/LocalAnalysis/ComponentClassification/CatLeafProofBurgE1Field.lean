module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Glue
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Comp
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
public import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
public import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.RankThree.Chevalley.SteinbergBT (canonical_field_centralizer_of_normalForm_all)

theorem pPrimeCore_eq_bot_of_isSimpleGroup
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : pPrimeCore 2 Q = ⊥ := by
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hQ
  have := le_center_of_odd_normal_of_isQuasisimple hq (pPrimeCore 2 Q) pPrimeCore_coprime_card
  rwa [hZ, le_bot_iff] at this

theorem exists_card_eq_pow_of_charP {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime]
    [CharP k p] : ∃ f : ℕ, 1 ≤ f ∧ Nat.card k = p ^ f := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem map_fixedSubgroup_entrywiseAdjointAut
    (τ : Tag) {K : Type} [Field K] [Finite K] (δ : K ≃+* K) :
    (fixedSubgroup (entrywiseAdjointAut τ δ)).map (adjointGroup τ K).subtype =
      entrywiseFixedGroup τ δ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    change Units.map (entrywiseHom δ.toRingHom) (x : ModGL τ K) = x
    rw [← coe_entrywiseAdjointAut τ δ x]
    exact congrArg Subtype.val hx
  · intro hy
    obtain ⟨hyC, hyF⟩ := Subgroup.mem_inf.1 hy
    refine ⟨⟨y, hyC⟩, Subtype.ext ?_, rfl⟩
    change (entrywiseAdjointAut τ δ ⟨y, hyC⟩ : ModGL τ K) = y
    rw [coe_entrywiseAdjointAut]
    exact hyF

theorem burgOddCoreFor_entrywise
    (τ : Tag) (hdet : τ.cartan.transpose.det = 1) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) (δ : K ≃+* K)
    (hstab : ∀ γ : MulAut (adjointGroup τ K), Odd (orderOf γ) →
      entrywiseAdjointAut τ δ * γ = γ * entrywiseAdjointAut τ δ →
      (∀ x ∈ fixedSubgroup (entrywiseAdjointAut τ δ), γ x = x) → γ = 1) :
    BurgOddCoreFor (entrywiseAdjointAut τ δ) := by
  have hfixJ : (fixedSubgroup (entrywiseAdjointAut τ δ)).map (adjointGroup τ K).subtype =
      fixedFieldImage τ δ := by
    rw [map_fixedSubgroup_entrywiseAdjointAut,
      RankThree.entrywiseFixedGroup_eq_fixedFieldImage_of_det_one hdet δ]
  refine ⟨?_, fun γ hγ hcomm hfix => hstab γ hγ hcomm hfix⟩
  have hk2 := ringChar_fixSubfield_ne_two hK2 δ
  obtain ⟨hsimp, hnab, -⟩ := odd_pinned_Chevalley_p_components τ (fixSubfield δ) hk2
  let e₁ : fixedSubgroup (entrywiseAdjointAut τ δ) ≃* fixedFieldImage τ δ :=
    ((fixedSubgroup _).equivMapOfInjective _ (adjointGroup τ K).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  let e₂ : adjointGroup τ (fixSubfield δ) ≃* fixedFieldImage τ δ :=
    (adjointGroup τ (fixSubfield δ)).equivMapOfInjective _ (baseChangeGL_injective _)
  have : Finite (ModGL τ (fixSubfield δ)) := finite_modGL
  have h0 := pPrimeCore_eq_bot_of_isSimpleGroup (Q := adjointGroup τ (fixSubfield δ)) hnab
  have h1 := pPrimeCore_map_iso 2 (e₁.trans e₂.symm).symm
  rw [h0, Subgroup.map_bot] at h1
  exact h1.symm

theorem burgOddCoreFor_of_quadratic
    (τ : Tag) {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : orderOf α = 2) (h : BurgOddCoreFor (entrywiseAdjointAut τ δ)) : BurgOddCoreFor α := by
  have hαα : α * α = 1 := by rw [← sq, ← hα, pow_orderOf_eq_one]
  obtain ⟨hcoset, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
  obtain ⟨β, -, hβg⟩ := hcoset τ
  obtain ⟨-, hconj⟩ := hβg g a
  obtain ⟨ψ, hψ, -⟩ := hconj α hαg hαα
  have hψα : ψ * α * ψ⁻¹ = entrywiseAdjointAut τ δ :=
    MulEquiv.ext fun u => Subtype.ext ((hψ u).trans (coe_entrywiseAdjointAut τ δ u).symm)
  refine burgOddCoreFor_of_conj ψ α ?_
  rwa [hψα]

theorem burgOddCoreFor_quadratic_field
    (τ : Tag) (hdet : τ.cartan.transpose.det = 1) {K : Type} [Field K] [Finite K] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hKe : Nat.card K = (p ^ e) ^ 2)
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    (hNF : ∀ (k : Type) [Field k] [Finite k], (∃ f' : ℕ, 1 ≤ f' ∧ Nat.card k = p ^ f') →
      ∀ α : MulAut (adjointGroup τ k), ∃! gφ : adjointGroup τ k × (k ≃+* k),
        ∀ h : adjointGroup τ k, (α h : ModGL τ k) = (gφ.1 : ModGL τ k) *
          Units.map (entrywiseHom gφ.2.toRingHom) (h : ModGL τ k) * (gφ.1 : ModGL τ k)⁻¹)
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : orderOf α = 2) : BurgOddCoreFor α := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hKe' : Nat.card K = p ^ (2 * e) := by rw [hKe, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hKe'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have : CharP (fixSubfield δ) p := Subfield.charP _ p
  refine burgOddCoreFor_of_quadratic τ hp he hKe δ hδ hαg hα ?_
  set δs := entrywiseAdjointAut τ δ with hδs
  have hδ2 : δs * δs = 1 := by
    have hαα : α * α = 1 := by rw [← sq, ← hα, pow_orderOf_eq_one]
    obtain ⟨hcoset, -⟩ :=
      exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
    obtain ⟨β, -, hβg⟩ := hcoset τ
    obtain ⟨-, hconj⟩ := hβg g a
    obtain ⟨ψ, hψ, -⟩ := hconj α hαg hαα
    have hψα : ψ * α * ψ⁻¹ = δs :=
      MulEquiv.ext fun u => Subtype.ext ((hψ u).trans (coe_entrywiseAdjointAut τ δ u).symm)
    rw [← hψα]
    calc ψ * α * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (α * α) * ψ⁻¹ := by group
      _ = 1 := by rw [hαα, mul_one, mul_inv_cancel]
  obtain ⟨-, hfixJ, -, -, -, -, -, hpw⟩ :=
    canonical_field_centralizer_of_normalForm_all δ (hNF K ⟨2 * e, by omega, hKe'⟩)
      (hNF (fixSubfield δ) exists_card_eq_pow_of_charP)
      (RankThree.entrywiseFixedGroup_eq_fixedFieldImage_of_det_one hdet δ)
  refine burgOddCoreFor_entrywise τ hdet hK2 δ fun γ hγ hcomm hfix => ?_
  have hmem : γ ∈ Subgroup.centralizer {δs} ⊓ Subgroup.centralizer
      ((((fixedFieldImage τ δ).subgroupOf (adjointGroup τ K)).map MulAut.conj :
        Subgroup (MulAut (adjointGroup τ K))) : Set (MulAut (adjointGroup τ K))) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    have hjfix : j ∈ fixedSubgroup δs := by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, ← hfixJ] at hj
      obtain ⟨j', hj', hjj'⟩ := hj
      rwa [show j = j' from Subtype.ext hjj'.symm]
    have hγj := hfix j hjfix
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hγj]
  rw [hpw] at hmem
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h2 : (δs ^ n) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hδ2, one_zpow]
  have hdvd : orderOf (δs ^ n) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · rw [h1] at hγ
    exact absurd hγ (by decide)

end CFSG.ComponentClassification.CatLeafProof
