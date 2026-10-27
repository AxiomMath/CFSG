module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCore
public import CFSG.RankThree.PartTwo.KFacts.K72Moving
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Rank

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoIn_inf_of_isSubnormal {P H K : Subgroup G} (hP : IsSylowTwoIn P H)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsSubnormal) : IsSylowTwoIn (P ⊓ K) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPH, P₀, hP₀⟩ := hP
  obtain ⟨P₁, hP₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P₀ hK
  let e : (K.subgroupOf H) ≃* K := subgroupOfEquivOfLe hKH
  have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  refine ⟨inf_le_right, P₁.mapSurjective he, ?_⟩
  apply map_injective K.subtype_injective
  rw [Sylow.coe_mapSurjective, map_map]
  have hcomp : K.subtype.comp e.toMonoidHom = H.subtype.comp (K.subgroupOf H).subtype := by
    ext x
    rfl
  rw [hcomp, ← map_map, hP₁, map_inf_eq _ _ H.subtype H.subtype_injective, hP₀,
    subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hPH,
    inf_eq_left.mpr hKH, inf_assoc, inf_idem]

theorem card_le_of_isSylowTwoIn_top {S R : Subgroup G} (hS : IsSylowTwoIn S ⊤)
    (hR : IsPGroup 2 R) : Nat.card R ≤ Nat.card S := by
  obtain ⟨g, -, hg⟩ := exists_conjugate_le_of_isSylowTwoIn hS le_top hR
  calc Nat.card R = Nat.card (conjugate R g) := by
        rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective]
    _ ≤ Nat.card S := card_le_of_le hg

theorem sixtyFour_le_card_of_isSylowTwoIn {P K : Subgroup G} (hP : IsSylowTwoIn P K)
    (h64 : 64 ∣ Nat.card K) : 64 ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPK, P₀, hP₀⟩ := hP
  have h1 : 2 ^ 6 ∣ Nat.card (P₀ : Subgroup K) :=
    P₀.pow_dvd_card_of_pow_dvd_card (by simpa using h64)
  rw [hP₀, Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv] at h1
  exact Nat.le_of_dvd Nat.card_pos (by simpa using h1)

theorem card_le_eight_of_unitary (hUnit : L34UnbalancingUnitaryStep)
    (hUC : L34UnitaryCentralizerFact) {u t : G} {K R : Subgroup G}
    (hT : GSUnbalancingTriple u t K) (htype : IsL34Type (K ⧸ Open.fusionZStar K)) (hRK : R ≤ K)
    (hRt : R ≤ centralizer ({t} : Set G)) (hR2 : IsPGroup 2 R) : Nat.card R ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUt := hUnit G u t K hT htype
  have htN : t ∈ normalizer (K : Set G) := hUt.1
  obtain ⟨-, hto, -, hKu, hKp, -, -⟩ := hT
  have hperf : ⁅K, K⁆ = K := GSThmB.commutator_eq_self_of_isPComponent hKu hKp
  have htz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto, pow_one])
  have htR : zpowers t ≤ normalizer (R : Set G) := zpowers_le.mpr
    (mem_normalizer_of_commute fun y hy => (mem_centralizer_singleton_iff.mp (hRt hy)).symm)
  have hB2 : IsPGroup 2 ↥(R ⊔ zpowers t) := hR2.to_sup_of_normal_left' htz htR
  have hBN : R ⊔ zpowers t ≤ normalizer (K : Set G) :=
    sup_le (hRK.trans le_normalizer) (zpowers_le.mpr htN)
  obtain ⟨Q₁, hQ₁⟩ := RankThree.PartTwo.KFacts.exists_sylow_le_normalizer hB2 hBN
  set P : Subgroup G := (Q₁ : Subgroup ↥K).map K.subtype with hP
  have hPsyl : IsSylowTwoIn P K :=
    ⟨map_subtype_le _, Q₁, (comap_map_eq_self_of_injective K.subtype_injective _).symm⟩
  have hRP : R ≤ P := by
    have hRN : R ≤ normalizer (P : Set G) := le_sup_left.trans hQ₁
    have h2 : IsPGroup 2 ↥(P ⊔ R) :=
      (IsSylowTwoIn.isPGroup hPsyl).to_sup_of_normal_left' hR2 hRN
    have heq := IsSylowTwoIn.eq_of_le hPsyl le_sup_left (sup_le hPsyl.1 hRK) h2
    calc R ≤ P ⊔ R := le_sup_right
      _ = P := heq
  have htP : t ∈ normalizer (P : Set G) := hQ₁ (mem_sup_right (mem_zpowers t))
  obtain ⟨-, h8, -⟩ := hUC G K P t hperf htype hUt hPsyl htP
  calc Nat.card R ≤ Nat.card ↥(P ⊓ centralizer ({t} : Set G)) := card_le_of_le (le_inf hRP hRt)
    _ = 8 := h8

omit [Finite G] in
theorem conjugate_centralizer_singleton (u g : G) :
    conjugate (centralizer ({u} : Set G)) g = centralizer ({g⁻¹ * u * g} : Set G) := by
  ext y
  simp only [conjugate, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    calc g⁻¹ * c * g * (g⁻¹ * u * g) = g⁻¹ * (c * u) * g := by group
      _ = g⁻¹ * (u * c) * g := by rw [hc]
      _ = g⁻¹ * u * g * (g⁻¹ * c * g) := by group
  · intro hy
    refine ⟨g * y * g⁻¹, ?_, by group⟩
    calc g * y * g⁻¹ * u = g * (y * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * y) * g⁻¹ := by rw [hy]
      _ = u * (g * y * g⁻¹) := by group

omit [Finite G] in
theorem types_conjugate {K : Subgroup G} (g : G)
    (h : IsL2Type 5 (K ⧸ pPrimeCore 2 K) ∨ IsL2Type 7 (K ⧸ pPrimeCore 2 K) ∨
      IsL34Type (K ⧸ Open.fusionZStar K)) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        Blueprint.LieModel (conjugate K g ⧸ pPrimeCore 2 (conjugate K g)) .PSL 2 p f) ∨
      IsL34Type (conjugate K g ⧸ Open.fusionZStar (conjugate K g)) := by
  let e : ↥K ≃* ↥(conjugate K g) :=
    K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  let eO : K ⧸ pPrimeCore 2 K ≃* conjugate K g ⧸ pPrimeCore 2 (conjugate K g) :=
    QuotientGroup.congr _ _ e (CFSG.pPrimeCore_map_iso 2 e)
  rcases h with h | h | h
  · exact Or.inl ⟨5, 1, by norm_num, by norm_num, le_rfl,
      LieType.CurtisTits.lieModel_of_mulEquiv eO h⟩
  · exact Or.inl ⟨7, 1, by norm_num, by norm_num, le_rfl,
      LieType.CurtisTits.lieModel_of_mulEquiv eO h⟩
  · exact Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv
      (FooteLit.nonempty_quotient_fusionZStar_equiv e).some h)

omit [Finite G] in
theorem isL34Type_of_conjugate {K : Subgroup G} (g : G)
    (h : IsL34Type (conjugate K g ⧸ Open.fusionZStar (conjugate K g))) :
    IsL34Type (K ⧸ Open.fusionZStar K) := by
  let e : ↥K ≃* ↥(conjugate K g) :=
    K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    (FooteLit.nonempty_quotient_fusionZStar_equiv e).some.symm h

omit [Finite G] in
theorem relIndex_mul_card_of_le {H K : Subgroup G} (h : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  rw [Subgroup.relIndex, ← Nat.card_congr (subgroupOfEquivOfLe h).toEquiv]
  exact Subgroup.index_mul_card _

theorem relIndex_inf_le_of_le {A B K : Subgroup G} (hAB : A ≤ B) :
    (A ⊓ K).relIndex (B ⊓ K) ≤ A.relIndex B := by
  have h1 : (A ⊓ K).relIndex (B ⊓ K) = A.relIndex (B ⊓ K) := by
    rw [← Subgroup.inf_relIndex_right (H := A) (K := B ⊓ K),
      show A ⊓ (B ⊓ K) = A ⊓ K by
        rw [← inf_assoc, inf_eq_left.mpr hAB]]
  rw [h1]
  exact Subgroup.relIndex_le_of_le_right inf_le_left (Subgroup.index_ne_zero_of_finite)

end CFSG.ComponentClassification.GrSLit.GrS5
