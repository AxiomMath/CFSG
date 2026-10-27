module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.ReeThreePair
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Sec66T (fixSub)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.RankThree.PartOne.SEITZ2 (exists_conj_mem_of_plane_of_cyclic_outer)

open CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc (reeG2_fixed_data isCyclic_outer_reeG2)


namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316

section Certs


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K G2.prime]

theorem fieldAutData_reeG2_three (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    FieldAutData (G2.reeGamma K a) 3 := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hfin : Finite (G2.reeGamma K a) := Subtype.finite
  have hcycOut := isCyclic_outer_reeG2 ha hK
  obtain ⟨-, -, -, -, -, hcycAut, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality 3 (2 * a + 1)
      Nat.prime_three (by omega) K hK
  let : CommGroup (K ≃+* K) := hcycAut.commGroup
  refine fieldAutData_of_standard (⊤ : Subgroup (MulAut (G2.reeGamma K a)))
    {g | ∃ β : K ≃+* K, orderOf β = 3 ∧ g = G2.reeGammaFieldAut K a β} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_conj_mem_of_plane_of_cyclic_outer hp hcycOut E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ 3 = 1 := hord ▸ pow_orderOf_eq_one α
    obtain ⟨-, δ, σ, hσord, hδ, -⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK hp
        (by norm_num) α hαp (fun ⟨g, hg⟩ => hout g hg.symm)
    refine ⟨δ⁻¹, Subgroup.mem_top _, G2.reeGammaFieldAut K a σ, ⟨σ, hσord, rfl⟩, ?_⟩
    rw [inv_inv, ← hδ]
    group
  · rintro _ ⟨β, hβ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    have hzp := zpowers_ringEquiv_eq_of_orderOf Nat.prime_three (by omega : 1 ≤ 2 * a + 1) hK hβ hτ
    exact fixedSubgroup_eq_of_zpowers_eq (G2.reeGammaFieldAutHom K a) hzp
  · rintro _ ⟨β, hβ, rfl⟩ _ x hx hc
    obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ := reeG2_fixed_data hK hp (by norm_num) hβ
    have hz : eC ⟨x, hx⟩ ∈ Subgroup.center (G2.reeGamma (fixSubfield β) b) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, hy⟩ : ∃ y : ↥(fixSub (G2.reeGammaFieldAut K a β)), eC y = g :=
        ⟨eC.symm g, by simp⟩
      rw [← hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc y.1 y.2).symm
    have hcen := (small_Ree_fixed_group_center_trivial b (fixSubfield β) hbcard).1
    rw [hcen, Subgroup.mem_bot] at hz
    have h1 : (⟨x, hx⟩ : ↥(fixSub (G2.reeGammaFieldAut K a β))) = 1 :=
      eC.injective (by rw [hz, map_one])
    exact congrArg Subtype.val h1
  · rintro _ ⟨β, hβ, rfl⟩ d - hne
    obtain ⟨x, τ, hd⟩ :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.smallReeOuterIsField a ha K hK d
    set R := fixedSubgroup (G2.reeGammaFieldAut K a β) with hR
    have hcomm : G2.reeGammaFieldAut K a τ * G2.reeGammaFieldAut K a β *
        (G2.reeGammaFieldAut K a τ)⁻¹ = G2.reeGammaFieldAut K a β := by
      have h := congrArg (G2.reeGammaFieldAutHom K a)
        (show τ * β * τ⁻¹ = β by rw [mul_comm τ β, mul_assoc, mul_inv_cancel, mul_one])
      rw [map_mul, map_mul, map_inv] at h
      simpa only [ReeTag.reeGammaFieldAutHom_apply] using h
    have hτR : R.map (G2.reeGammaFieldAut K a τ).toMonoidHom = R := by
      rw [hR, ← fixedSubgroup_conj, hcomm]
    have hmap : R.map d.toMonoidHom = R.map (MulAut.conj x).toMonoidHom := by
      rw [hd]
      calc R.map (MulAut.conj x * G2.reeGammaFieldAut K a τ).toMonoidHom
          = (R.map (G2.reeGammaFieldAut K a τ).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
            rw [Subgroup.map_map]; rfl
        _ = R.map (MulAut.conj x).toMonoidHom := by rw [hτR]
    rw [hmap] at hne ⊢
    exact Or.inl (CFSG.LocalAnalysis.SubfieldPairReeG2.subfieldPairReeG2_three ha hK hβ x hne)

theorem planesGenerate_of_isReeGTwoIndex {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsReeGTwoIndex 3 d) :
    PlanesGenerate 3 (CFSG.AGLEmbedding.CatGroup d) := by
  intro E hE hEc hnot
  obtain ⟨a, ha, -, ⟨e⟩⟩ := CFSG.AGLEmbedding.ReeModel.exists_equiv_reeGamma hd
    ⟨MulEquiv.refl (CFSG.AGLEmbedding.CatGroup d)⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  have hFAD := fieldAutData_reeG2_three (K := GaloisField 3 (2 * a + 1)) ha hX
  have hFAD' : FieldAutData (CFSG.AGLEmbedding.CatGroup d) 3 := hFAD.of_mulEquiv e Nat.prime_three
  have := (CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple ha
    (GaloisField 3 (2 * a + 1)) hX).2.1
  have hsimple : IsSimpleGroup (CFSG.AGLEmbedding.CatGroup d) := MulEquiv.isSimpleGroup e
  have hfin : Finite (CFSG.AGLEmbedding.CatGroup d) := Finite.of_equiv _ e.symm.toEquiv
  have hel : CFSG.IsElementaryAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).mpr hE
  have hnab := CFSG.LieType.SeitzGeneration.exists_noncommuting_of_isElementaryAbelian_aut hel hEc
  exact (CFSG.LieType.SeitzGeneration.planeGen_iff_closure_fixUnion E).mpr
    (closure_fixUnion_eq_top_of_fieldAutData hnab Nat.prime_three hFAD' E hEc
      (fun hall => hnot fun φ hφ => (hall φ hφ).elim fun g hg => ⟨g, hg.symm⟩))

end Certs

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316
