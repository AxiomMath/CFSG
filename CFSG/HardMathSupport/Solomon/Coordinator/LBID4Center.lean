module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit
public import CFSG.Open.GriessAllModelsStatement

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (griessHopfMultiplier GriessAllModelsStatement)
open CFSG.Blueprint.Multiplier CFSG.LieType.Steinberg.CentralExt.CoprimeSplit
open scoped commutatorElement

theorem lbi_card_table_D4 (p f : ℕ) :
    Finite (generic .POmegaPlus 4 p f × exceptional .POmegaPlus 4 p f) ∧
      Nat.card (generic .POmegaPlus 4 p f × exceptional .POmegaPlus 4 p f) ∣ 16 := by
  have h4 : Even 4 := by decide
  have hg : genericOrders .POmegaPlus 4 p f = (if Even (p ^ f) then (1, 1) else (2, 2)) := by
    simp [genericOrders, h4]
  have he : exceptionalOrders .POmegaPlus 4 p f = (if p = 2 ∧ f = 1 then (2, 2) else (1, 1)) := by
    unfold exceptionalOrders
    split_ifs <;> simp_all
  have hgd : (genericOrders .POmegaPlus 4 p f).1 ≠ 0 ∧ (genericOrders .POmegaPlus 4 p f).2 ≠ 0 ∧
      (genericOrders .POmegaPlus 4 p f).1 * (genericOrders .POmegaPlus 4 p f).2 ∣ 4 := by
    rw [hg]; split_ifs <;> simp
  have hed : (exceptionalOrders .POmegaPlus 4 p f).1 ≠ 0 ∧
      (exceptionalOrders .POmegaPlus 4 p f).2 ≠ 0 ∧
      (exceptionalOrders .POmegaPlus 4 p f).1 * (exceptionalOrders .POmegaPlus 4 p f).2 ∣ 4 := by
    rw [he]; split_ifs <;> simp
  have hc := lbi_card_gen_exc .POmegaPlus 4 p f hgd.1 hgd.2.1 hed.1 hed.2.1
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hc]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero hgd.1 hgd.2.1) (Nat.mul_ne_zero hed.1 hed.2.1)
  · rw [hc]
    exact (mul_dvd_mul hgd.2.2 hed.2.2).trans (by norm_num)

theorem lbiD4_center (hG : GriessAllModelsStatement) {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hD : LocalBalance.Lemma27Ns.IsD4Type X) :
    ∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ 3 ^ k = 1 → z = 1 := by
  classical
  obtain ⟨p, f, hp3, hmodel⟩ := hD
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hLie : CFSG.Models.LieModel (X ⧸ Subgroup.center X) .POmegaPlus 4 p f :=
    ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e⟩⟩⟩
  obtain ⟨-, ⟨eH⟩⟩ := hG _ .POmegaPlus 4 p f hLie
  obtain ⟨hfin, hdvd⟩ := lbi_card_table_D4 p f
  have : Finite (generic .POmegaPlus 4 p f × exceptional .POmegaPlus 4 p f) := hfin
  let C := Subgroup.center X
  let N := copPart 3 C le_rfl
  have hNC : N ≤ C := fun c hc => hc.1
  let ψ : X ⧸ N →* X ⧸ C := QuotientGroup.map N C (MonoidHom.id X) hNC
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hkerψ : ∀ w : X ⧸ N, w ∈ ψ.ker → ∃ x ∈ C, w = QuotientGroup.mk x := by
    intro w hw
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    refine ⟨x, ?_, rfl⟩
    exact (QuotientGroup.eq_one_iff x).1 hw
  have hcen : ψ.ker ≤ Subgroup.center (X ⧸ N) := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hkerψ w hw
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.1 hx y)]
  have hperf : commutator (X ⧸ N) = ⊤ := by
    have : Group.IsPerfect X := ⟨hq.1⟩
    have : Group.IsPerfect (X ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    exact this.commutator_eq_top
  have hp : IsPGroup 3 ψ.ker := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [IsPGroup.iff_orderOf]
    intro w
    obtain ⟨x, hx, hw⟩ := hkerψ w w.2
    obtain ⟨a, ha⟩ := exists_pow_prime_pow_mem_copPart (p := 3) (C := C) le_rfl hx
    have hpow : w ^ 3 ^ a = 1 := by
      apply Subtype.ext
      show (w : X ⧸ N) ^ 3 ^ a = 1
      rw [hw, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ha
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hpow)
    exact ⟨k, hk⟩
  have hcard : Nat.card ψ.ker ∣ 16 :=
    (lbi_card_ker_dvd ψ hψ hcen hperf eH).trans hdvd
  have hone : Nat.card ψ.ker = 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
    rw [hk] at hcard ⊢
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rfl
    · exfalso
      have h3 : 3 ∣ 16 := (dvd_pow_self 3 hk0.ne').trans hcard
      omega
  have hbot : ψ.ker = ⊥ := by
    have : Subsingleton ψ.ker := (Nat.card_eq_one_iff_unique.1 hone).1
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    exact congrArg Subtype.val (Subsingleton.elim (⟨y, hy⟩ : ψ.ker) 1)
  intro z hz k hzk
  have hzN : z ∈ N := by
    have hmem : (QuotientGroup.mk z : X ⧸ N) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff z).2 hz
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff z).1 hmem
  have hcop : Nat.Coprime 3 (orderOf z) := hzN.2
  have hd : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have h1 : orderOf z = 1 := Nat.Coprime.eq_one_of_dvd (hcop.symm.pow_right k) hd
  exact orderOf_eq_one_iff.1 h1

end CFSG.HardMathSupport.Solomon.Coordinator
