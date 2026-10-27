module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem le_twoPrimeRes_of_isQuasisimple [Finite G] {X : Subgroup G} (hX : IsQuasisimple X) :
    X ≤ twoPrimeRes X := by
  let Y := ↥X
  haveI : Finite Y := Subtype.finite
  let s : Set Y := {y | ∃ k : ℕ, orderOf y = 2 ^ k}
  let M : Subgroup Y := Subgroup.closure s
  have hMnormal : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    refine Subgroup.closure_induction (fun x hx => ?_) ?_
      (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) hn
    · rcases hx with ⟨k, hk⟩
      exact Subgroup.subset_closure
        ⟨k, by rw [← MulAut.conj_apply, (MulAut.conj g).orderOf_eq x, hk]⟩
    · simpa using Subgroup.one_mem M
    · rw [← conj_mul]
      exact M.mul_mem ihx ihy
    · rw [← conj_inv]
      exact M.inv_mem ihx
  have hMtop : M = ⊤ := by
    haveI : M.Normal := hMnormal
    haveI : Group.IsPerfect Y := hX.1
    refine QuotientGroup.subgroup_eq_top_of_subsingleton M ?_
    have hodd_order : ∀ x : Y ⧸ M, Odd (orderOf x) := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective M x
      obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
      have hpow2 : orderOf (y ^ m) ∣ 2 ^ k := by
        rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpow2
      have hmem : y ^ m ∈ M := Subgroup.subset_closure ⟨j, hj⟩
      have hqm : (QuotientGroup.mk' M y) ^ m = 1 := by
        rw [← map_pow]
        simpa using (QuotientGroup.eq_one_iff (y ^ m)).mpr hmem
      exact hm.of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hqm)
    by_contra hsub
    haveI : Nontrivial (Y ⧸ M) := not_subsingleton_iff_nontrivial.mp hsub
    have hodd_card : Odd (Nat.card (Y ⧸ M)) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y ⧸ M) 2
        (even_iff_two_dvd.mp heven)
      obtain ⟨j, hj⟩ := hodd_order x
      rw [hx] at hj
      omega
    exact Group.IsPerfect.not_isSolvable (Y ⧸ M) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd_card)
  have hmap : M.map X.subtype ≤ twoPrimeRes X := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨k, hk⟩
    exact Subgroup.subset_closure ⟨y.2, ⟨k, (Subgroup.orderOf_coe y).trans hk⟩⟩
  intro x hx
  exact hmap (Subgroup.mem_map.mpr
    ⟨⟨x, hx⟩, by rw [hMtop]; exact Subgroup.mem_top _, rfl⟩)

theorem IsComponentIn.le_layerCent [Finite G] {X L : Subgroup G} {s : G}
    (h : IsComponentIn X (L ⊓ centralizer ({s} : Set G))) : X ≤ layerCent L s := by
  let K : Subgroup G := L ⊓ centralizer ({s} : Set G)
  have hle : X.subgroupOf K ≤ CFSG.layer K := CFSG.LocalCores.component_le_layer h.2
  calc X = (X.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le h.1).symm
    _ ≤ (CFSG.layer K).map K.subtype := Subgroup.map_mono hle
    _ = layerCent L s := rfl

theorem isComponentIn_pair_layerCent [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G}
    {z : G} (hctx : Sec7Ctx G t L S z) {s : G}
    (h : IsOmega5 (layerCent L s) ∨ IsL29 (layerCent L s) ∨ IsU33 (layerCent L s) ∨
      IsL3Eps3 (layerCent L s)) :
    IsComponentIn (layerCent L s) (centralizer ({t} : Set G) ⊓ centralizer ({s} : Set G)) := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  exact IsComponentIn.of_normal_inf_centralizer hS.component.le
    (conjugate_eq_self_of_lemma36 h36 hS) (isComponentIn_layerCent h)

end CFSG.OddStandard.SmallF3.Omega
