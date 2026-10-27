module

public import CFSG.Dihedral.FourgroupFixedOrder
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenOddSubgroupOrderBound
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerOddPart
public import CFSG.GroupTheory.CentralizerMap
public import CFSG.Milestones.OO_odd_order_solvable
import all CFSG.Dihedral.BlueprintDefs
public import CFSG.Dihedral.OriginalOddCore

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_inter_card_eq_of_normalizer (J : Subgroup G) (x a : G)
    (hx : x ∈ Subgroup.normalizer (J : Set G)) :
    Nat.card (J ⊓ Subgroup.centralizer ({x * a * x⁻¹} : Set G) : Subgroup G) =
      Nat.card (J ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) := by
  let e : G ≃* G := MulAut.conj x
  have hmap := centralizer_inter_map e J a
  have hJ : J.map e.toMonoidHom = J := Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  rw [hJ] at hmap
  change (J ⊓ Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom =
    J ⊓ Subgroup.centralizer ({x * a * x⁻¹} : Set G) at hmap
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

theorem odd_normal_subgroup_centralizes_cycling_fourgroup_of_aSeven_model
    (e : G ≃* alternatingGroup (Fin 7)) (H V J : Subgroup G)
    (hV : IsKleinFour V) (hVH : V ≤ H) (hc : Cycles H V)
    (hJH : J ≤ H) (hnormal : (J.subgroupOf H).Normal)
    (hodd : Odd (Nat.card J)) : J ≤ Subgroup.centralizer (V : Set G) := by
  classical
  let : IsKleinFour V := hV
  have hnormH : NormalizedBy J H :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mp hnormal
  have hnormV : NormalizedBy J V := hVH.trans hnormH
  obtain ⟨x, hxH, hxN, hxmove⟩ := hc
  let phi : MulAut V := V.normalizerMonoidHom ⟨x, hxN⟩
  have hmove (v : V) (hv : v ≠ 1) : phi v ≠ v := by
    intro h
    exact hxmove v v.property (fun h => hv (Subtype.ext h)) (congrArg Subtype.val h)
  have hVbot : V ≠ ⊥ := by
    intro h
    have hcard := hV.card_four
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVbot
  let b : V := phi a
  have hb : b ≠ 1 := by
    intro h
    apply ha
    apply phi.injective
    change phi a = 1 at h
    simpa only [map_one] using h
  have hab : a ≠ b := (hmove a ha).symm
  have hthird : phi b = a * b := by
    have hneone : phi b ≠ 1 := fun h => hb (phi.injective (by simpa using h))
    have hneb : phi b ≠ b := hmove b hb
    have hnea : phi b ≠ a := by
      intro heq
      have hprod : a * b ≠ 1 := by
        intro h
        exact hab (by simpa only [IsKleinFour.inv_eq_self] using mul_eq_one_iff_eq_inv.mp h)
      have hfix : phi (a * b) = a * b := by
        rw [map_mul, heq]
        exact IsKleinFour.isMulCommutative.is_comm.comm _ _
      exact hmove (a * b) hprod hfix
    exact IsKleinFour.eq_mul_of_ne_all ha hb hab hneone hnea hneb
  have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hbG : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
  have habG : (a : G) ≠ (b : G) := fun h => hab (Subtype.ext h)
  have hconja : x * (a : G) * x⁻¹ = (b : G) :=
    (Subgroup.normalizerMonoidHom_apply_apply_coe V ⟨x, hxN⟩ a).symm
  have hconjb : x * (b : G) * x⁻¹ = (a : G) * (b : G) := by
    rw [← Subgroup.normalizerMonoidHom_apply_apply_coe V ⟨x, hxN⟩ b]
    exact congrArg Subtype.val hthird
  have hcardb := centralizer_inter_card_eq_of_normalizer J x a (hnormH hxH)
  have hcardab := centralizer_inter_card_eq_of_normalizer J x b (hnormH hxH)
  rw [hconja] at hcardb
  rw [hconjb, hcardb] at hcardab
  let F : Subgroup G := J ⊓ Subgroup.centralizer (V : Set G)
  let A : Subgroup G := J ⊓ Subgroup.centralizer ({(a : G)} : Set G)
  have hFA : F ≤ A := inf_le_inf_left J (Subgroup.centralizer_le (by
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    exact hv ▸ a.property))
  have hFdiv : Nat.card F ∣ Nat.card A := Subgroup.card_dvd_of_le hFA
  have hAodd : Odd (Nat.card A) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hAbound : Nat.card A ≤ 3 := by
    have ht : BenderSuzuki.PFAppendixIII.IsInvolution (e (a : G)) := by
      refine ⟨fun h => haG (e.injective (by simpa using h)), ?_⟩
      have hpow : (a : G) ^ 2 = 1 := by
        simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
          congrArg Subtype.val (IsKleinFour.mul_self a)
      simpa only [map_pow, map_one] using congrArg e hpow
    have hmapodd : Odd (Nat.card (A.map e.toMonoidHom)) := by
      rwa [Subgroup.card_map_of_injective e.injective]
    have hmapcent : A.map e.toMonoidHom ≤
        Subgroup.centralizer ({e (a : G)} : Set (alternatingGroup (Fin 7))) := by
      change (J ⊓ Subgroup.centralizer ({(a : G)} : Set G)).map e.toMonoidHom ≤ _
      rw [centralizer_inter_map]
      exact inf_le_right
    have h := aSeven_odd_subgroup_centralizing_involution_card_le_three hmapodd ht hmapcent
    rwa [Subgroup.card_map_of_injective e.injective] at h
  have hJbound : Nat.card J ≤ 21 := by
    have h := aSeven_odd_subgroup_card_le_21 (J.map e.toMonoidHom) (by
      rwa [Subgroup.card_map_of_injective e.injective])
    rwa [Subgroup.card_map_of_injective e.injective] at h
  have hsolv : Group.IsSolvable J := CFSG.Milestones.odd_order_solvable hodd
  have hprod := ambient_fourgroup_fixed_order_identity V J hV hodd hsolv hnormV
    a b a.property b.property haG hbG habG
  rw [hcardb, hcardab] at hprod
  change Nat.card J * Nat.card F ^ 2 = Nat.card A * Nat.card A * Nat.card A at hprod
  have hcard : Nat.card J = Nat.card F := by
    have hApos := Nat.card_pos (α := A)
    have hAcases : Nat.card A = 1 ∨ Nat.card A = 3 := by
      have hoddmod := hAodd.not_two_dvd_nat
      omega
    rcases hAcases with hA | hA
    · have hF : Nat.card F = 1 := Nat.eq_one_of_dvd_one (hA ▸ hFdiv)
      rw [hA, hF] at hprod
      simpa only [one_pow, mul_one, hF] using hprod
    · have hFcases : Nat.card F = 1 ∨ Nat.card F = 3 :=
        (Nat.dvd_prime Nat.prime_three).mp (hA ▸ hFdiv)
      rcases hFcases with hF | hF
      · rw [hA, hF] at hprod
        norm_num at hprod
        omega
      · rw [hA, hF] at hprod
        norm_num at hprod
        omega
  have heq : F = J := Subgroup.eq_of_le_of_card_ge inf_le_left hcard.le
  rw [← heq]
  exact inf_le_right

theorem oddCoreOf_centralizes_cycling_fourgroup_of_aSeven_model
    (e : G ≃* alternatingGroup (Fin 7)) (H V : Subgroup G)
    (hV : IsKleinFour V) (hVH : V ≤ H) (hc : Cycles H V) :
    oddCoreOf H ≤ Subgroup.centralizer (V : Set G) :=
  odd_normal_subgroup_centralizes_cycling_fourgroup_of_aSeven_model e H V
    (oddCoreOf H) hV hVH hc (oddCoreOf_le H) (oddCoreOf_normal H) (oddCoreOf_odd H)

end CFSG.DihedralBlueprint
