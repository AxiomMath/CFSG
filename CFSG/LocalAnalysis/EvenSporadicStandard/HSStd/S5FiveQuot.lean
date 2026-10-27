module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Equiv

@[expose] def zmodPowHom {G : Type*} [Group G] (n : ℕ) [NeZero n] (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G where
  toFun k := g ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hg]

section ZModPow

variable {G : Type*} [Group G] {n : ℕ} [NeZero n] {g : G} (hg : g ^ n = 1)

theorem zmodPowHom_apply (k : Multiplicative (ZMod n)) :
    zmodPowHom n g hg k = g ^ (Multiplicative.toAdd k).val := rfl

theorem zmodPowHom_ofAdd_natCast (m : ℕ) :
    zmodPowHom n g hg (Multiplicative.ofAdd (m : ZMod n)) = g ^ m := by
  rw [zmodPowHom_apply, toAdd_ofAdd, ZMod.val_natCast, ← pow_eq_pow_mod _ hg]

theorem zmodPowHom_injective (hord : orderOf g = n) : Function.Injective (zmodPowHom n g hg) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  rw [zmodPowHom_apply] at hk
  have h1 : orderOf g ∣ (Multiplicative.toAdd k).val := orderOf_dvd_iff_pow_eq_one.2 hk
  rw [hord] at h1
  have h2 : (Multiplicative.toAdd k).val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
  exact toAdd_eq_zero.1 ((ZMod.val_eq_zero _).1 h2)

end ZModPow

theorem center_prod_two_perm_five :
    ∀ c ∈ center (Multiplicative (ZMod 2) × Perm (Fin 5)), c.2 = 1 := fun _ hc =>
  CFSG.perm_eq_one_of_forall_commute (by simp) fun σ =>
    (congr_arg Prod.snd (mem_center_iff.1 hc (1, σ))).symm

theorem eq_one_of_pow_odd_of_sq_eq_one {H : Type*} [Group H] {x : H} {n : ℕ} (hn : Odd n)
    (hx : x ^ n = 1) (hx2 : x ^ 2 = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rwa [pow_succ, pow_mul, hx2, one_pow, one_mul] at hx

theorem sq_eq_one_multiplicative_zmod_two (x : Multiplicative (ZMod 2)) : x ^ 2 = 1 := by
  revert x
  decide

theorem exists_pow_eq_multiplicative_zmod_five {g : Multiplicative (ZMod 5)} (hg : g ≠ 1)
    (b : Multiplicative (ZMod 5)) : ∃ k : ℕ, g ^ k = b := by
  have key : ∀ g b : Multiplicative (ZMod 5), g ≠ 1 → ∃ k : Fin 5, g ^ (k : ℕ) = b := by decide
  obtain ⟨k, hk⟩ := key g b hg
  exact ⟨k, hk⟩

theorem eq_bot_of_normal_odd_perm_five (N : Subgroup (Perm (Fin 5))) [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  have hle : N ≤ alternatingGroup (Fin 5) := by
    intro σ hσ
    rw [Equiv.Perm.mem_alternatingGroup]
    have hpow : σ ^ Nat.card N = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (N.orderOf_dvd_natCard hσ)
    exact eq_one_of_pow_odd_of_sq_eq_one hN (by rw [← map_pow, hpow, map_one]) (Int.units_sq _)
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5))) with
    h | h
  · exact (subgroupOf_eq_bot.1 h).eq_bot_of_le hle
  · exfalso
    have h60 := card_dvd_of_le (subgroupOf_eq_top.1 h)
    rw [nat_card_alternatingGroup] at h60
    obtain ⟨k, hk⟩ := hN
    obtain ⟨j, hj⟩ := h60
    simp [Nat.factorial] at hj
    omega

theorem normal_odd_le_prod_five
    {M : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Perm (Fin 5))}
    [M.Normal] (hM : Odd (Nat.card M)) : ∀ m ∈ M, m.1 = 1 ∧ m.2.2 = 1 := by
  let p : (Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Perm (Fin 5)) →*
      Perm (Fin 5) := (MonoidHom.snd _ _).comp (MonoidHom.snd _ _)
  have hp : Function.Surjective p := fun σ => ⟨(1, 1, σ), rfl⟩
  have : (M.map p).Normal := Subgroup.Normal.map ‹M.Normal› p hp
  have hbot : M.map p = ⊥ :=
    eq_bot_of_normal_odd_perm_five _ (hM.of_dvd_nat (card_map_dvd M p))
  intro m hm
  refine ⟨?_, ?_⟩
  · have hpow : m ^ Nat.card M = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (M.orderOf_dvd_natCard hm)
    exact eq_one_of_pow_odd_of_sq_eq_one hM (congr_arg Prod.fst hpow)
      (sq_eq_one_multiplicative_zmod_two _)
  · have hmem : m.2.2 ∈ M.map p := ⟨m, hm, rfl⟩
    rwa [hbot, mem_bot] at hmem

theorem exists_mulEquiv_quotient_prod_five {A : Type*} [Group A]
    (e : A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Perm (Fin 5))
    {r : A} (hr : r ∈ center A) (hr5 : orderOf r = 5) [(zpowers r).Normal] :
    Nonempty (A ⧸ zpowers r ≃* Multiplicative (ZMod 2) × Perm (Fin 5)) := by
  let π : (Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Perm (Fin 5)) →*
      Multiplicative (ZMod 2) × Perm (Fin 5) :=
    (MonoidHom.fst _ _).prod ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))
  have hπ : Function.Surjective π := fun x => ⟨(x.1, 1, x.2), rfl⟩
  let φ : A →* Multiplicative (ZMod 2) × Perm (Fin 5) := π.comp e.toMonoidHom
  have hφ : Function.Surjective φ := hπ.comp e.surjective
  set f := e r with hf
  have hfc : ∀ x, x * f = f * x := fun x => by
    apply e.symm.injective
    simp only [map_mul, hf, MulEquiv.symm_apply_apply]
    exact mem_center_iff.1 hr (e.symm x)
  have hf3 : f.2.2 = 1 := CFSG.perm_eq_one_of_forall_commute (by simp) fun σ =>
    (congr_arg (fun y => y.2.2) (hfc (1, 1, σ))).symm
  have hr5' : r ^ 5 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hr5)
  have hf5 : f ^ 5 = 1 := by
    rw [hf, ← map_pow, hr5', map_one]
  have hf1 : f.1 = 1 :=
    eq_one_of_pow_odd_of_sq_eq_one (n := 5) (by decide) (congr_arg Prod.fst hf5)
      (sq_eq_one_multiplicative_zmod_two _)
  have hf2 : f.2.1 ≠ 1 := fun h2 => by
    have : f = 1 := Prod.ext hf1 (Prod.ext h2 hf3)
    rw [hf, map_eq_one_iff _ e.injective] at this
    rw [this, orderOf_one] at hr5
    exact absurd hr5 (by decide)
  have hker : φ.ker = zpowers r := by
    refine le_antisymm (fun x hx => ?_) ((zpowers_le).2 ?_)
    · have hx' : φ x = 1 := hx
      have hx1 : (e x).1 = 1 := congr_arg Prod.fst hx'
      have hx3 : (e x).2.2 = 1 := congr_arg Prod.snd hx'
      obtain ⟨k, hk⟩ := exists_pow_eq_multiplicative_zmod_five hf2 (e x).2.1
      refine mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [zpow_natCast]
      apply e.injective
      rw [map_pow, ← hf]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · rw [Prod.pow_fst, hf1, one_pow, hx1]
      · rw [Prod.pow_snd, Prod.pow_fst, hk]
      · rw [Prod.pow_snd, Prod.pow_snd, hf3, one_pow, hx3]
    · show φ r = 1
      exact Prod.ext hf1 hf3
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end CFSG.EvenSporadicStandard.HSStd
