module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactReeL28Core
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactReeL28Cent
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactReeL28Sub
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSSection
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.LieType.Ree.SmallReeModelSchreier

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup CFSG.Blueprint CFSG.LieType.Ree
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)

namespace ReeL28

theorem exists_reeG2 {d : TauCeti.LieTypeIndex} (h : IsReeIndex d) : ∃ a, d = .reeG2 a := by
  cases d <;> first | exact ⟨_, rfl⟩ | exact False.elim h

theorem exists_mul_ne_of_card_504 {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h : Nat.card X = 504) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push_neg at hcon
  letI : CommGroup X := { (inferInstance : Group X) with mul_comm := hcon }
  have hprime := IsSimpleGroup.prime_card (α := X)
  rw [h] at hprime
  norm_num at hprime

end ReeL28

theorem kFactReeL28_holds :
    KFactReeL28 := by
  intro A _ _ L T z hL hT hzL hz7 hzT
  obtain ⟨i, hi, ⟨e⟩⟩ := hL
  cases i with
  | lie d =>
    obtain ⟨d', hv⟩ := d
    obtain ⟨m, rfl⟩ := ReeL28.exists_reeG2 (show IsReeIndex d' from hi)
    have hm := CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩
    obtain ⟨-, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier ↥L 3 (2 * m + 1) hm
    obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hm
    have ha' : a' = a := by omega
    subst ha'
    have : CharP K ReeTag.G2.prime :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_three (by omega) hK
    obtain ⟨e'⟩ := hiso a' K hfa hK hw
    have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
    haveI : Finite (ReeTag.G2.reeGamma K a') := Finite.of_equiv ↥L e'.toEquiv
    obtain ⟨hC, h8⟩ := ReeL28.reeL28_cent ha hK'
    have hdata : ReeL28.ReeL28Data ↥(ReeTag.G2.reeGamma K a') := ⟨hC, h8, ReeL28.reeL28_sub h8⟩
    have hdataL : ReeL28.ReeL28Data ↥L := ReeL28.ReeL28Data.of_mulEquiv e'.symm hdata
    obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
    set z' : ↥L := ⟨z, hzL⟩ with hz'
    have hz'N : z' ∈ normalizer (((Q : Subgroup ↥L)) : Set ↥L) := by
      rw [hQ, ← Subgroup.subgroupOf_normalizer_eq (CFSG.ABGLocalTools.IsSylowOf.le hT)]
      exact hzT
    have hz'7 : orderOf z' = 7 := by
      rw [hz', Subgroup.orderOf_mk, hz7]
    obtain ⟨H, hHs, hH504, -, hz'H, hHeq⟩ := ReeL28.exists_sub504 hdataL Q hz'N hz'7
    let HA : Subgroup A := H.map L.subtype
    have hHAs : IsSimpleGroup HA :=
      (H.equivMapOfInjective L.subtype L.subtype_injective).isSimpleGroup_congr.mp hHs
    have hHAcard : Nat.card HA = 504 := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hH504]
    have hzHA : z ∈ HA := ⟨z', hz'H, rfl⟩
    have hz1 : z ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hz7
      omega
    refine ⟨HA, ⊥, ?_, ?_, hzHA, ?_, ?_⟩
    ·
      have hTmap : (Q : Subgroup ↥L).map L.subtype = T := by
        rw [hQ, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr (CFSG.ABGLocalTools.IsSylowOf.le hT)]
      have hHmap : HA = ((normalizer (zpowers z' : Set ↥L) ⊓ H).map L.subtype) ⊔ T := by
        rw [← hTmap, ← Subgroup.map_sup, ← hHeq]
      rw [hHmap]
      refine sup_le_sup_right ?_ T
      rintro _ ⟨n, ⟨hnN, -⟩, rfl⟩
      refine ⟨?_, n.2⟩
      have hmap : (zpowers z').map L.subtype = zpowers z := by
        rw [MonoidHom.map_zpowers]
        rfl
      have := Subgroup.le_normalizer_map L.subtype (Subgroup.mem_map_of_mem L.subtype hnN)
      rwa [hmap] at this
    ·
      haveI := hHAs
      have hsec := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNS.s622IsSimpleSection_comap
        (MonoidHom.id A) Function.surjective_id hHAs
        (ReeL28.exists_mul_ne_of_card_504 hHAcard)
      rwa [Subgroup.comap_id, MonoidHom.ker_id] at hsec
    · exact fun h => hz1 (Subgroup.mem_bot.mp h)
    · rw [Subgroup.relIndex_bot_left, hHAcard]
      norm_num
  | cyclic q hq => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
