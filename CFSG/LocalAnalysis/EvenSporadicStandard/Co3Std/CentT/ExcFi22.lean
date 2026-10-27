module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ExcQuot
public import CFSG.Sporadic.FischerOddCore.Fi22GenFitting
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22

public noncomputable section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Certified


theorem card_fi22P_inf_centralizer_z :
    Nat.card ↥(fi22P ⊓ Subgroup.centralizer ({fi22OuterZ} : Set (Equiv.Perm (Fin 3510)))) =
      18393661440 := by
  rw [Nat.card_congr fi22CPzEquiv.toEquiv,
    ← CFSG.Sporadic.FischerOddCore.card_centralizer_of_isConj isConj_fi22OuterZP_fi22Ya,
    card_centralizer_fi22Ya]

theorem card_fi22P_inf_centralizer_ext {k : ℕ} (hk : k < 6) :
    Nat.card ↥(fi22P ⊓ Subgroup.centralizer ({fi22ExtRep k} : Set (Equiv.Perm (Fin 3510)))) =
      [1769472, 53084160, 18393661440, 3317760, 1045094400, 2903040].getD k 0 := by
  obtain ⟨h0, h1, h3, h4, h5, hord⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  have hH : ∀ c < 5, Nat.card ↥(fi22H c) =
      [1769472, 53084160, 3317760, 1045094400, 2903040].getD c 0 :=
    fun c hc => by rw [← hord]; simp [List.getD_eq_getElem?_getD, hc]
  interval_cases k
  · rw [h0, hH 0 (by norm_num)]; rfl
  · rw [h1, hH 1 (by norm_num)]; rfl
  · rw [fi22ExtRep_two, card_fi22P_inf_centralizer_z]; rfl
  · rw [h3, hH 2 (by norm_num)]; rfl
  · rw [h4, hH 3 (by norm_num)]; rfl
  · rw [h5, hH 4 (by norm_num)]; rfl

theorem fi22_involution_card_inf_centralizer {τ : Equiv.Perm (Fin 3510)} (hτ : τ ∈ fi22R)
    (ho : orderOf τ = 2) :
    ∃ k < 6, (τ ∈ fi22P → k < 3) ∧
      Nat.card ↥(fi22P ⊓ Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 3510)))) =
        Nat.card ↥(fi22P ⊓ Subgroup.centralizer
          ({fi22ExtRep k} : Set (Equiv.Perm (Fin 3510)))) := by
  obtain ⟨k, hk, r, hr, hrτ⟩ := fi22R_involution_conj hτ ho
  have hrn := fi22R_le_normalizer hr
  refine ⟨k, hk, fun hτP => ?_, ?_⟩
  · have hkP : fi22ExtRep k ∈ fi22P := by
      rw [← hrτ]
      exact (Subgroup.mem_normalizer_iff.1 hrn _).1 hτP
    by_contra h
    obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
    exact (CTUC_Fi22_all_extension_involutions_covered.2.1 j (by omega)).2 hkP
  · have e := (fi22CP_conj_equiv hrn τ).trans (MulEquiv.subgroupCongr (by rw [hrτ]))
    exact Nat.card_congr e.toEquiv

theorem excQuot_fi22P : ExcQuot fi22P where
  center_eq_bot := center_fi22P
  card_mulAut_dvd := by
    rw [← Nat.card_congr fi22RAut.toEquiv, card_fi22R, card_fi22P]
    norm_num
  fixLarge := by
    intro β hβ
    obtain ⟨r, rfl⟩ := fi22RAut.surjective β
    have hr2 : r * r = 1 := fi22RAut.injective (by rw [map_mul, hβ, map_one])
    have hfix : Nat.card ↥(fixedSubgroup (fi22RAut r)) = Nat.card ↥(fi22P ⊓
        Subgroup.centralizer ({(r : Equiv.Perm (Fin 3510))} : Set (Equiv.Perm (Fin 3510)))) :=
      Nat.card_congr (fixSubRAutEquiv r).toEquiv
    rw [hfix]
    by_cases hr1 : r = 1
    · subst hr1
      have htop : Subgroup.centralizer ({((1 : fi22R) : Equiv.Perm (Fin 3510))} :
          Set (Equiv.Perm (Fin 3510))) = ⊤ := by
        ext x
        simp [Subgroup.mem_centralizer_singleton_iff]
      rw [htop, inf_top_eq, card_fi22P]
      norm_num
    · have hτ2 : (r : Equiv.Perm (Fin 3510)) * r = 1 := congrArg Subtype.val hr2
      have hτ1 : (r : Equiv.Perm (Fin 3510)) ≠ 1 := fun h => hr1 (Subtype.ext h)
      have ho : orderOf (r : Equiv.Perm (Fin 3510)) = 2 :=
        orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
      obtain ⟨k, hk, -, hcard⟩ := fi22_involution_card_inf_centralizer r.2 ho
      rw [hcard, card_fi22P_inf_centralizer_ext hk]
      interval_cases k <;> norm_num
  two_pow_dvd := by
    rw [card_fi22P]
    norm_num
  involution_centralizer := by
    intro q hq2 hq1
    left
    have hτP : (q : Equiv.Perm (Fin 3510)) ∈ fi22P := q.2
    have hτ2 : (q : Equiv.Perm (Fin 3510)) * q = 1 := congrArg Subtype.val hq2
    have hτ1 : (q : Equiv.Perm (Fin 3510)) ≠ 1 := fun h => hq1 (Subtype.ext h)
    have ho : orderOf (q : Equiv.Perm (Fin 3510)) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
    obtain ⟨k, hk, hk3, hcard⟩ := fi22_involution_card_inf_centralizer (fi22P_le_R hτP) ho
    rw [card_centralizer_subtype_eq_card_inf fi22P q, hcard,
      card_fi22P_inf_centralizer_ext hk]
    have hk3' := hk3 hτP
    interval_cases k <;> norm_num

theorem excQuot_fi22 {Q : Type} [Group Q] (h : NativeSporadic.IsSporadic Q .Fi22) :
    ExcQuot Q := by
  obtain ⟨e⟩ := h
  exact ExcQuot.of_mulEquiv (e.trans fi22PermEquiv).symm excQuot_fi22P

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
