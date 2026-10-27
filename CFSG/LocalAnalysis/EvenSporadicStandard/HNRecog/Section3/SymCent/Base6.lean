module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open Equiv

private def pr : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

private def idx : Fin 4 → Fin 4 → Fin 6 :=
  ![![0,0,1,2], ![0,1,3,4], ![1,3,2,5], ![2,4,5,3]]

private def actFun (g : Sym 4) (i : Fin 6) : Fin 6 :=
  idx (g (pr i).1) (g (pr i).2)

private theorem actFun_inv : ∀ (g : Sym 4) (i : Fin 6),
    actFun g⁻¹ (actFun g i) = i := by decide +kernel

private theorem actFun_inv' : ∀ (g : Sym 4) (i : Fin 6),
    actFun g (actFun g⁻¹ i) = i := by decide +kernel

private def act (g : Sym 4) : Sym 6 where
  toFun := actFun g
  invFun := actFun g⁻¹
  left_inv := fun i => actFun_inv g i
  right_inv := fun i => actFun_inv' g i

private theorem act_one : act 1 = 1 := by decide +kernel

private theorem act_mul : ∀ g h : Sym 4, act (g * h) = act g * act h := by
  decide +kernel

private def actHom : Sym 4 →* Sym 6 where
  toFun := act
  map_one' := act_one
  map_mul' := act_mul

private def tauVal (ε : Z 2) : Sym 6 := if ε = 1 then 1 else Fin.revPerm

private theorem tauVal_mul : ∀ a b : Z 2, tauVal (a * b) = tauVal a * tauVal b := by
  decide +kernel

private theorem tauVal_one : tauVal 1 = 1 := by simp [tauVal]

private def tauPow : Z 2 →* Sym 6 where
  toFun := tauVal
  map_one' := tauVal_one
  map_mul' := tauVal_mul

private theorem comm_tau_act_all :
    ∀ a : Z 2, ∀ b : Sym 4, tauPow a * actHom b = actHom b * tauPow a := by
  decide +kernel

private theorem comm_tau_act (a : Z 2) (b : Sym 4) : Commute (tauPow a) (actHom b) :=
  comm_tau_act_all a b

private def F : Z 2 × Sym 4 →* Sym 6 :=
  MonoidHom.noncommCoprod tauPow actHom comm_tau_act

private theorem F_eq_one : ∀ x : Z 2 × Sym 4, F x = 1 → x = 1 := by
  decide +kernel

private theorem F_injective : Function.Injective F :=
  (injective_iff_map_eq_one F).mpr F_eq_one

private theorem F_comm_rev : ∀ x : Z 2 × Sym 4, F x * Fin.revPerm = Fin.revPerm * F x := by
  decide +kernel

private theorem F_mem (x : Z 2 × Sym 4) :
    F x ∈ Subgroup.centralizer ({Fin.revPerm} : Set (Sym 6)) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (F_comm_rev x)

private theorem revPerm_pow_two : (Fin.revPerm : Sym 6) ^ 2 = 1 := by
  rw [pow_two]; ext i; simp [Fin.revPerm_apply]

private theorem revPerm_cycleType_rep :
    (Fin.revPerm : Sym 6).cycleType = Multiset.replicate 3 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one revPerm_pow_two
  have hsum : (Fin.revPerm : Sym 6).cycleType.sum = 6 := by
    rw [Equiv.Perm.sum_cycleType]
    have huniv : (Fin.revPerm : Sym 6).support = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro i
      rw [Equiv.Perm.mem_support]
      simpa [Fin.revPerm_apply] using (by decide : ∀ i : Fin 6, Fin.rev i ≠ i) i
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  have hcard3 : (Fin.revPerm : Sym 6).cycleType.card = 3 := by
    have h1 : (Fin.revPerm : Sym 6).cycleType.sum =
        2 * (Fin.revPerm : Sym 6).cycleType.card := by
      rw [hct, Multiset.sum_replicate, Multiset.card_replicate, nsmul_eq_mul, Nat.cast_id]
      ring
    omega
  rw [hct, hcard3]

private theorem revPerm_cycleType :
    (Fin.revPerm : Sym 6).cycleType = ({2, 2, 2} : Multiset ℕ) := by
  rw [revPerm_cycleType_rep]
  decide

private theorem revPerm_nat_card :
    Nat.card ↥(Subgroup.centralizer ({(Fin.revPerm : Sym 6)} : Set (Sym 6))) = 48 := by
  rw [Equiv.Perm.nat_card_centralizer, revPerm_cycleType_rep]
  simp only [Multiset.sum_replicate, Multiset.card_replicate, Multiset.prod_replicate,
    Multiset.toFinset_replicate, Multiset.count_replicate]
  norm_num [Nat.factorial]

private theorem card_eq :
    Nat.card (Z 2 × Sym 4) =
      Nat.card ↥(Subgroup.centralizer ({(Fin.revPerm : Sym 6)} : Set (Sym 6))) := by
  rw [revPerm_nat_card]
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  simp [Z, Fintype.card_multiplicative, ZMod.card, Nat.factorial]

private theorem isConj_revPerm {τ : Sym 6} (hτ : τ.cycleType = {2, 2, 2}) :
    IsConj τ Fin.revPerm := by
  rw [Equiv.Perm.isConj_iff_cycleType_eq, hτ, revPerm_cycleType]

theorem symCent_base_six {τ : Sym 6} (hτ : τ.cycleType = {2, 2, 2}) :
    Nonempty (↥(Subgroup.centralizer ({τ} : Set (Sym 6))) ≃* Z 2 × Sym 4) := by
  obtain ⟨e⟩ := symCent_mulEquiv_of_isConj (isConj_revPerm hτ)
  obtain ⟨f⟩ := symCent_mulEquiv_of_injective F F_injective F_mem card_eq
  exact ⟨e.trans f⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
