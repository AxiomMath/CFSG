module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Model
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4M12
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Ord

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.M12Cover
  CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor CFSG.GH74.GLS.IVK
open scoped commutatorElement

theorem m12_inv_cases :
    ∀ t ∈ blockGroup, orderOf t = 2 →
      (∃ g ∈ autModel, t = g * blockHom (permZ, permZ) * g⁻¹) ∨
        Nat.card ↥(centralizerIn blockGroup t) = 192 := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hout⟩ := Certificates.certificate5150
  simp only [m12OuterOK, Bool.and_eq_true] at hout
  obtain ⟨⟨-, hoA⟩, -⟩ := hout
  have hσrep : Rep 24 m12ST m12Sigma := rep_toTable hn _
  have hσA : m12Sigma * m12A1 = m12A1 * m12Sigma :=
    (commTT_iff hσrep (rep_toTable hn _)).1 hoA
  have hcardW : Nat.card autModel = 2 * Nat.card blockGroup := card_autModel_eq
  have hautM := m12_smallAutModel
  have hnormW : ∀ x ∈ autModel, ∀ p ∈ blockGroup, x * p * x⁻¹ ∈ blockGroup := hautM.conj_mem
  have hnormW' : ∀ x ∈ autModel, ∀ p ∈ blockGroup, x⁻¹ * p * x ∈ blockGroup := fun x hx p hp => by
    simpa using hnormW x⁻¹ (autModel.inv_mem hx) p hp
  have hcentA : Nat.card ↥(centralizerIn blockGroup m12A1) = 192 := by
    have h384 : Nat.card ↥(centralizerIn autModel m12A1) = 384 := by
      have h := q2Q_spec
      rw [← h.1]
      exact h.2.1
    have := card_centralizerIn_of_outer blockGroup_le_autModel hcardW sigma_mem_autModel
      sigma_not_mem_blockGroup hσA
    omega
  intro t htD ht2
  obtain ⟨r, hr, c, hc, hδ⟩ := autModel_involution_cover (blockGroup_le_autModel htD) ht2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · right
    rw [hδ, GHInv.card_centralizerIn_conj_of_norm (hnormW c hc) (hnormW' c hc)]
    exact hcentA
  · exact Or.inl ⟨c, hc, hδ⟩
  · exfalso
    apply sigma_not_mem_blockGroup
    have := hnormW' c hc t htD
    rw [hδ] at this
    simpa [mul_assoc] using this

theorem ivk95_m12 :
    Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .M12) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.M12 := e
  let θ : J ≃* ↥blockGroup := e'.trans m12EquivD
  rcases m12_inv_cases ((θ z : ↥blockGroup) : Equiv.Perm (Fin 24)) (θ z).2
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hz.ord) with ⟨g, hg, hgt⟩ | h192
  · exact hz.false_of_model_class m12_model θ hg hgt
  · have hcard : Nat.card ↥(centralizer ({z} : Set J)) = 192 := by
      rw [GHInv.card_centralizer_eq_centralizerIn blockGroup θ z]
      exact h192
    exact hz.false_of_card_cent_dvd (N := 192) (by rw [hcard]) (fun q hq => not_sl2_dvd_192 q hq)

end CFSG.GH74.GLS.IVK.Proofs2
