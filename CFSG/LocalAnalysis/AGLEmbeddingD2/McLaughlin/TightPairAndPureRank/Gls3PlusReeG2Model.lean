module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.LieType.Ree

section Native

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem ree_native_rankOne_data (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (∀ t ∈ ReeModel.stdU a K, t ≠ 1 → ∀ k : ↥(ReeTag.G2.reeGamma K a),
      k * t * k⁻¹ ∈ ReeModel.stdU a K →
        k ∈ Subgroup.normalizer ((ReeModel.stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
          Set ↥(ReeTag.G2.reeGamma K a))) ∧
    IsCoatom (Subgroup.normalizer ((ReeModel.stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a))) ∧
    (Subgroup.normalizer ((ReeModel.stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a))).index = (3 ^ (2 * a + 1)) ^ 3 + 1 ∧
    ∃ J : Subgroup ↥(ReeTag.G2.reeGamma K a), IsCyclic J ∧
      Subgroup.normalizer ((ReeModel.stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
        Set ↥(ReeTag.G2.reeGamma K a)) = ReeModel.stdU a K ⊔ J := by
  obtain ⟨-, hNU, hco, -⟩ := ReeModel.std_facts hK
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, -, hcardΩ, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  refine ⟨?_, hNU ▸ hco, ?_, ?_⟩
  · intro t ht ht1 k hk
    rw [hNU]
    by_contra hkB
    have h1 : k * t * k⁻¹ ∈ ReeModel.stdU a K ⊓ (ReeModel.stdU a K).map (MulAut.conj k).toMonoidHom :=
      ⟨hk, ⟨t, ht, by simp [MulAut.conj_apply]⟩⟩
    rw [ReeModel.inf_map_conj_eq_bot hK hkB, Subgroup.mem_bot] at h1
    apply ht1
    calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  · rw [hNU]
    exact hcardΩ
  · have hHΓ : ReeTag.G2.reeFixedTorus K a ≤ ReeTag.G2.reeGamma K a :=
      ReeTag.reeFixedTorus_le_reeFixedBorel.trans ReeTag.reeFixedBorel_le_reeGamma
    have hUΓ : ReeTag.G2.reeFixedPosUnipotent K a ≤ ReeTag.G2.reeGamma K a :=
      ReeTag.reeFixedPosUnipotent_le_reeGamma
    refine ⟨(ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a), ?_, ?_⟩
    · obtain ⟨⟨φ, -⟩, -⟩ := small_Ree_positive_torus_action a K hK
      have e : Kˣ ≃* ↥((ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a)) :=
        φ.trans (Subgroup.subgroupOfEquivOfLe hHΓ).symm
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    · rw [hNU, ReeModel.stdB, ReeTag.reeFixedBorel_eq_sup, Subgroup.subgroupOf_sup hHΓ hUΓ,
        sup_comm]
      rfl

theorem ree_native_elemAbelian (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∃ E : Subgroup ↥(ReeTag.G2.reeGamma K a), E ≤ ReeModel.stdU a K ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (2 * a + 1) :=
  ⟨(ReeModel.xHom hK).range, (ReeModel.xHom_range hK).le.trans inf_le_left,
    ReeModel.isElemAbelian_xHom_range hK, ReeModel.card_xHom_range hK⟩

end Native

section Transport

theorem ree_rankOne_data {L : Type} [Group L] [Finite L]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d) (h : Nonempty (L ≃* CatGroup d))
    (U : Sylow 3 L) :
    (∀ t ∈ (U : Subgroup L), t ≠ 1 → ∀ k : L, k * t * k⁻¹ ∈ (U : Subgroup L) →
      k ∈ Subgroup.normalizer ((U : Subgroup L) : Set L)) ∧
    IsCoatom (Subgroup.normalizer ((U : Subgroup L) : Set L)) ∧
    (Subgroup.normalizer ((U : Subgroup L) : Set L)).index = (3 ^ d.1.fieldExponent) ^ 3 + 1 ∧
    (∃ J : Subgroup L, IsCyclic J ∧
      Subgroup.normalizer ((U : Subgroup L) : Set L) = (U : Subgroup L) ⊔ J) ∧
    ∃ E : Subgroup L, E ≤ (U : Subgroup L) ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ d.1.fieldExponent := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨⟨P, hP⟩, -, -, -⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e U P
  have hU : (U : Subgroup L).map e'.toMonoidHom = ReeModel.stdU a (GaloisField 3 (2 * a + 1)) :=
    he'.trans hP
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer ((ReeModel.stdU a (GaloisField 3 (2 * a + 1)) : Subgroup _) : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  have hN' : Subgroup.normalizer ((U : Subgroup L) : Set L) =
      (Subgroup.normalizer ((ReeModel.stdU a (GaloisField 3 (2 * a + 1)) : Subgroup _) :
        Set _)).comap e'.toMonoidHom := by
    rw [← hN, Subgroup.comap_map_eq_self_of_injective e'.injective]
  obtain ⟨hti, hco, hidx, J, hJc, hNJ⟩ := ree_native_rankOne_data hK
  rw [hfe]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht ht1 k hk
    have ht' : e' t ∈ ReeModel.stdU a (GaloisField 3 (2 * a + 1)) := by
      rw [← hU]; exact (ReeModel.mem_map_iff e' _ t).2 ht
    have hk' : e' k * e' t * (e' k)⁻¹ ∈ ReeModel.stdU a (GaloisField 3 (2 * a + 1)) := by
      rw [← map_mul, ← map_inv, ← map_mul, ← hU]
      exact (ReeModel.mem_map_iff e' _ _).2 hk
    have ht1' : e' t ≠ 1 := fun h1 => ht1 (e'.injective (by rw [h1, map_one]))
    rw [hN']
    exact hti _ ht' ht1' _ hk'
  · rw [hN']
    exact (Subgroup.isCoatom_comap e').2 hco
  · exact (Subgroup.index_map_equiv _ e').symm.trans ((congrArg Subgroup.index hN).trans hidx)
  · refine ⟨J.map e'.symm.toMonoidHom, ?_, ?_⟩
    · let φ := Subgroup.equivMapOfInjective J e'.symm.toMonoidHom e'.symm.injective
      exact isCyclic_of_surjective φ.toMonoidHom φ.surjective
    · apply Subgroup.map_injective (f := e'.toMonoidHom) e'.injective
      rw [hN, hNJ, Subgroup.map_sup, hU, Subgroup.map_map]
      congr 1
      ext x
      simp
  · obtain ⟨E, hEU, hEel, hEcard⟩ := ree_native_elemAbelian hK
    refine ⟨E.map e'.symm.toMonoidHom, ?_, ?_, ?_⟩
    · rw [← Subgroup.map_le_map_iff_of_injective (f := e'.toMonoidHom) e'.injective, hU,
        Subgroup.map_map]
      convert hEU
      ext x
      simp
    · exact (ReeModel.isElemAbelian_map_iff e'.symm E).2 hEel
    · rw [Subgroup.card_map_of_injective e'.symm.injective, hEcard]

end Transport

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
