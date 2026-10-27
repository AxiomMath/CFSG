module

public import Certificates.Certificate211002
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import Certificates.Data.U62Rank.Data

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi22.Native U62Rank
  CFSG.Yardstones.Md0ec50421ce4 TauCeti CFSG.Sporadic.Th

namespace U62RankSound

theorem card_le_81_T46
    {E : Subgroup CFSG.Fischer.T46} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 81 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQT, hQcard, hQab⟩ := Certificates.certificate211002
  let Q₀ : Subgroup CFSG.Fischer.T46 := Q.subgroupOf CFSG.Fischer.T46
  have hQ₀card : Nat.card Q₀ = 3 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv, hQcard]
    norm_num
  have hindex : ¬ 3 ∣ Q₀.index := by
    have h1 := Subgroup.card_mul_index Q₀
    rw [hQ₀card, card_T46] at h1
    have h2 : Q₀.index = 12615680 := by omega
    rw [h2]
    decide
  let Q₀S : Sylow 3 CFSG.Fischer.T46 := (IsPGroup.of_card hQ₀card).toSylow hindex
  obtain ⟨P, hEP⟩ := (isPGroup_of_isElemAbelian hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (CFSG.Fischer.T46) P Q₀S
  have hconj : ∀ x ∈ E, MulAut.conj g x ∈ Q₀ := by
    intro x hx
    have hxP : x ∈ (P : Set CFSG.Fischer.T46) := hEP hx
    have h1 : MulAut.conj g x ∈ ((g • P : Sylow 3 CFSG.Fischer.T46) : Set CFSG.Fischer.T46) := by
      rw [Sylow.coe_smul]
      exact Set.smul_mem_smul_set hxP
    rw [hg] at h1
    exact (IsPGroup.mem_toSylow (IsPGroup.of_card hQ₀card) hindex).1 (SetLike.mem_coe.1 h1)
  let E' : Subgroup CFSG.Fischer.T46 := E.map (MulAut.conj g).toMonoidHom
  have hE'Q₀ : E' ≤ Q₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hconj x hx
  let F : Subgroup (Equiv.Perm (Fin 693)) := E'.map CFSG.Fischer.T46.subtype
  have hFQ : F ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hE'Q₀ hy)
  have hFab : IsElemAbelian 3 F := (hE.map (MulAut.conj g).toMonoidHom).map CFSG.Fischer.T46.subtype
  have hF_card : Nat.card F = Nat.card E := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))]
  rw [← hF_card]
  exact hQab F hFQ hFab

theorem lieIndex_isU6two {S : Type} [Group S] (h : catalogIs S S9.isU6two) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 5 q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.twistedA 5 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem bridge_u6two_T46
    {S : Type} [Group S] (h : catalogIs S S9.isU6two) : Nonempty (S ≃* CFSG.Fischer.T46) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isU6two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  have hm := lieModel_twistedA' 5 q hv e
  rw [h1, h2] at hm
  exact CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 (hm.toBlueprint (by decide))

theorem card_le_81_of_catalogIs
    {S : Type} [Group S] (h : catalogIs S S9.isU6two) {F : Subgroup S}
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 81 := by
  obtain ⟨e⟩ := bridge_u6two_T46 h
  have hE : IsElemAbelian 3 (F.map e.toMonoidHom) := hF.map e.toMonoidHom
  have hcard : Nat.card (F.map e.toMonoidHom) = Nat.card F :=
    Subgroup.card_map_of_injective e.injective
  rw [← hcard]
  exact card_le_81_T46 hE

end U62RankSound

end CFSG.LocalAnalysis.GLTheoremA.CatB
