module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.Walter.AStar.Subnormal
public import Certificates.Certificate2021
public import Certificates.Certificate2022
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ClassicalInvolution.Balance

theorem fusionZStar_eq_center_of_pPrimeCore_eq_bot {K : Type*} [Group K]
    (hK : pPrimeCore 2 K = ⊥) : Open.fusionZStar K = center K := by
  ext l
  rw [GSThmB.OddQuot.mem_fusionZStar_iff, hK, mem_center_iff]
  simp only [mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact ⟨fun h m => (h m).symm, fun h m => (h m).symm⟩

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_eq_bot_of_isSubnormal {X : Type*} [Group X] [Finite X]
    (hX : pPrimeCore 2 X = ⊥) {K : Subgroup X} (hK : K.IsSubnormal) : pPrimeCore 2 K = ⊥ := by
  have hsub : ((pPrimeCore 2 K).map K.subtype).IsSubnormal := by
    refine Subgroup.IsSubnormal.step _ K (map_subtype_le _) hK ?_
    have h : ((pPrimeCore 2 K).map K.subtype).subgroupOf K = pPrimeCore 2 K :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [h]
    infer_instance
  have h := CFSG.Walter.eq_bot_of_isSubnormal_of_odd hX hsub (odd_card_map_pPrimeCore K)
  exact (map_eq_bot_iff_of_injective _ K.subtype_injective).mp h

theorem nonempty_image_center_quotient_equiv {a : G} {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G)))) :
    Nonempty (↥((J.subgroupOf (centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G))))) ⧸
      center ↥((J.subgroupOf (centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G))))) ≃*
      ↥J ⧸ Open.fusionZStar ↥J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({a} : Set G) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  set JC : Subgroup C := J.subgroupOf C with hJC
  obtain ⟨K', hK', -, hJK', -⟩ := hJ
  have hKO : pPrimeCore 2 ↥(JC.map π) = ⊥ := by
    rw [hJK']
    exact pPrimeCore_eq_bot_of_isSubnormal (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hK'.2
  obtain ⟨e1⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective
    (subgroupOfEquivOfLe hJa).symm.toMonoidHom (subgroupOfEquivOfLe hJa).symm.surjective
    (by
      rw [show (subgroupOfEquivOfLe hJa).symm.toMonoidHom.ker = ⊥ from
        MonoidHom.ker_eq_bot_iff _ |>.mpr (subgroupOfEquivOfLe hJa).symm.injective, card_bot]
      norm_num)
  have hker : ¬ 2 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    intro h
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr h)
  obtain ⟨e2⟩ := GSThmB.OddQuot.nonempty_quotient_fusionZStar_equiv π hker JC
  have e3 := QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_center_of_pPrimeCore_eq_bot hKO)
  exact ⟨e3.symm.trans (e2.symm.trans e1.symm)⟩

theorem wGroup_eq_iInf_of_four {E : Subgroup G} (hE4 : Nat.card E = 4)
    (hE2 : ∀ e ∈ E, e * e = 1) :
    wGroup E = ⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
      (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype := by
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hBE => iSup_le fun hB4 => iSup_le fun _ => ?_
    have hBeq : B = E :=
      Subgroup.eq_of_le_of_card_ge hBE (by rw [hE4]; exact hB4)
    rw [hBeq]
  · exact le_iSup_of_le E (le_iSup_of_le le_rfl (le_iSup_of_le (by rw [hE4])
      (le_iSup_of_le hE2 le_rfl)))

theorem commutator_deltaCore_le_of_psl34 {a : G} {J E : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hmodel : Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2)
    (hE : E ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G)) (hE4 : Nat.card E = 4)
    (hE2 : ∀ e ∈ E, e * e = 1) :
    ⁅J, (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1), (pPrimeCore 2 (centralizer ({e} : Set G))).map
        (centralizer ({e} : Set G)).subtype) ⊓ centralizer ({a} : Set G)⁆ ≤
      (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype := by
  obtain ⟨e⟩ := nonempty_image_center_quotient_equiv hJa hJ
  refine commutator_deltaCore_le_of_isLocallyTwoBalanced hJa hJ rfl ?_ hE hE4 hE2
  obtain ⟨K', hK', -, hJK', -⟩ := hJ
  have hq : IsQuasisimple ↥((J.subgroupOf (centralizer ({a} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({a} : Set G))))) := by
    rw [hJK']
    exact hK'.1
  obtain ⟨-, hs, hnab⟩ := hq
  exact isLocallyTwoBalanced_of_psl34 hnab (LieType.CurtisTits.lieModel_of_mulEquiv e.symm hmodel)

theorem commutator_wGroup_le_of_psl34 {a : G} {J E : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hmodel : Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2)
    (hE : E ≤ normalizer (J : Set G) ⊓ centralizer ({a} : Set G))
    (hE4 : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ⁅J, wGroup E ⊓ centralizer ({a} : Set G)⁆ ≤
      (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype := by
  obtain ⟨φ⟩ := hE4
  have h4 : Nat.card E = 4 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
    rfl
  have h2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have hm : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * y = 1 := by decide
    have : (⟨e, he⟩ : E) * ⟨e, he⟩ = 1 := φ.injective (by rw [map_mul, map_one, hm])
    exact congrArg Subtype.val this
  rw [wGroup_eq_iInf_of_four h4 h2]
  exact commutator_deltaCore_le_of_psl34 hJa hJ hmodel
    (fun x hx => mem_inf.mpr ⟨(mem_inf.mp (hE hx)).2, (mem_inf.mp (hE hx)).1⟩) h4 h2

end CFSG.ComponentClassification.GrSLit
