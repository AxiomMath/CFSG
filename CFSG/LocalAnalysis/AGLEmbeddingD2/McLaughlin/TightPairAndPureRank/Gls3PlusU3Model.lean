module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model CFSG.AGLEmbedding

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hJ hK hfix

theorem normalizer_rootGroup_eq_stabilizer (hq : 2 < p ^ f) :
    Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
  have h2 := isMultiplyPretransitive_two J hJ (p ^ f) hK hfix
  have : MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : Nontrivial (IsoPoint J) := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_isoPoint J hJ (p ^ f) hK hfix]
    have : 0 < (p ^ f) ^ 3 := pow_pos (by omega) _
    omega
  have hprim := MulAction.isPreprimitive_of_is_two_pretransitive h2
  have hco := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)
  have hle := stabilizer_pinf_le_normalizer_rootGroup J hJ (p ^ f) hK hfix
  have hN := (CFSG.AGLEmbedding.UnitaryModel.isCoatom_normalizer_rootGroup J hJ hK hfix hq).1
  rcases hco.le_iff.mp hle with h | h
  · exact absurd h hN
  · exact h

theorem rootGroup_ti (hq : 2 < p ^ f) {r g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hr : r ∈ rootGroup J hJ) (hr1 : r ≠ 1) (hg : g * r * g⁻¹ ∈ rootGroup J hJ) :
    g ∈ Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  rw [normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq]
  have hfixR : ∀ x ∈ rootGroup J hJ, x • pinf J hJ = pinf J hJ := fun x hx =>
    rootGroup_le_stabilizer J hJ hx
  have hrfix : ∀ β : IsoPoint J, β ≠ pinf J hJ → r • β = β → False := by
    intro β hβ hrβ
    obtain ⟨r0, -, huniq⟩ := rootGroup_regular J hJ β β hβ hβ
    have h1 := huniq ⟨r, hr⟩ hrβ
    have h2 := huniq 1 (one_smul _ _)
    exact hr1 (congrArg Subtype.val (h1.trans h2.symm))
  by_contra hne
  have hne' : g⁻¹ • pinf J hJ ≠ pinf J hJ := by
    intro h
    apply hne
    rw [MulAction.mem_stabilizer_iff]
    exact inv_smul_eq_iff.mp h |>.symm
  apply hrfix (g⁻¹ • pinf J hJ) hne'
  have h1 : (g * r * g⁻¹) • pinf J hJ = pinf J hJ := hfixR _ hg
  calc r • g⁻¹ • pinf J hJ = (g⁻¹ * (g * r * g⁻¹)) • pinf J hJ := by
        rw [← smul_smul, ← smul_smul]
        simp [mul_assoc, smul_smul]
    _ = g⁻¹ • (g * r * g⁻¹) • pinf J hJ := by rw [smul_smul]
    _ = g⁻¹ • pinf J hJ := by rw [h1]

theorem index_normalizer_rootGroup (hq : 2 < p ^ f) :
    (Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))).index = (p ^ f) ^ 3 + 1 := by
  rw [normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq]
  have h2 := isMultiplyPretransitive_two J hJ (p ^ f) hK hfix
  have : MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  rw [MulAction.index_stabilizer_of_transitive, card_isoPoint J hJ (p ^ f) hK hfix]

theorem normalizer_rootGroup_eq_sup (hq : 2 < p ^ f) :
    Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      rootGroup J hJ ⊔ torusGroup J hJ ∧ IsCyclic (torusGroup J hJ) := by
  refine ⟨?_, isCyclic_torusGroup J hJ (p ^ f) hK hfix⟩
  rw [normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq,
    rootGroup_sup_torusGroup J hJ (p ^ f) hK hfix]

end Model

section Transport

theorem unitary_rankOne_data {L : Type} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (h : Nonempty (L ≃* CatGroup d))
    (U : Sylow p L) :
    (∀ t ∈ (U : Subgroup L), t ≠ 1 → ∀ k : L, k * t * k⁻¹ ∈ (U : Subgroup L) →
      k ∈ Subgroup.normalizer ((U : Subgroup L) : Set L)) ∧
    IsCoatom (Subgroup.normalizer ((U : Subgroup L) : Set L)) ∧
    (Subgroup.normalizer ((U : Subgroup L) : Set L)).index = (p ^ d.1.fieldExponent) ^ 3 + 1 ∧
    ∃ J : Subgroup L, IsCyclic J ∧
      Subgroup.normalizer ((U : Subgroup L) : Set L) = (U : Subgroup L) ⊔ J := by
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  have hN' : Subgroup.normalizer ((U : Subgroup L) : Set L) =
      (Subgroup.normalizer (rootGroup J hJ : Set _)).comap e'.toMonoidHom := by
    rw [← hN, Subgroup.comap_map_eq_self_of_injective e'.injective]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht ht1 k hk
    have ht' : e' t ∈ rootGroup J hJ := by
      rw [← hU]; exact (UnitaryModel.mem_map_iff e' _ t).2 ht
    have hk' : e' k * e' t * (e' k)⁻¹ ∈ rootGroup J hJ := by
      rw [← map_mul, ← map_inv, ← map_mul, ← hU]
      exact (UnitaryModel.mem_map_iff e' _ _).2 hk
    have ht1' : e' t ≠ 1 := fun h1 => ht1 (e'.injective (by rw [h1, map_one]))
    have := rootGroup_ti J hJ hK hfix hq ht' ht1' hk'
    rw [hN']
    exact this
  · rw [hN']
    exact (Subgroup.isCoatom_comap e').2
      (UnitaryModel.isCoatom_normalizer_rootGroup J hJ hK hfix hq)
  · exact (Subgroup.index_map_equiv _ e').symm.trans
      ((congrArg Subgroup.index hN).trans (index_normalizer_rootGroup J hJ hK hfix hq))
  · obtain ⟨hsup, hcyc⟩ := normalizer_rootGroup_eq_sup J hJ hK hfix hq
    refine ⟨(torusGroup J hJ).map e'.symm.toMonoidHom, ?_, ?_⟩
    · have : IsCyclic (torusGroup J hJ) := hcyc
      let φ := Subgroup.equivMapOfInjective (torusGroup J hJ) e'.symm.toMonoidHom e'.symm.injective
      exact isCyclic_of_surjective φ.toMonoidHom φ.surjective
    · apply Subgroup.map_injective (f := e'.toMonoidHom) e'.injective
      rw [hN, hsup, Subgroup.map_sup, hU, Subgroup.map_map]
      congr 1
      ext x
      simp

end Transport

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
