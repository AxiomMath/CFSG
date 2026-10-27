module

public import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.Fischer.Classification.Recognition.SymO

open CFSG.Open
open scoped Nat commutatorElement

variable {X : Type*} [Group X]

theorem IsSubnormal.le {A B : Subgroup X} (h : IsSubnormal A B) : A ≤ B :=
  CFSG.Open.IsSubnormal.le h

theorem IsSubnormal.inf_eq_bot_or_le {A C S : Subgroup X} (h : IsSubnormal A C) (hSC : S ≤ C)
    (hS : IsSimpleGroup S) : A ⊓ S = ⊥ ∨ S ≤ A := by
  induction h with
  | refl => exact Or.inr hSC
  | @step A M C hAM hn _ ih =>
    rcases ih hSC with h | h
    · exact Or.inl (eq_bot_iff.mpr ((inf_le_inf_right S hAM).trans h.le))
    · rw [Subgroup.normal_subgroupOf_iff hAM] at hn
      have hN : (A.subgroupOf S).Normal := by
        refine ⟨fun x hx g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        simpa using hn _ _ hx (h g.2)
      rcases hS.eq_bot_or_eq_top_of_normal (A.subgroupOf S) with h' | h'
      · exact Or.inl (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h'))
      · exact Or.inr (Subgroup.subgroupOf_eq_top.mp h')

theorem IsSubnormal.map_eq_bot_or_eq_top {A C : Subgroup X} (h : IsSubnormal A C) {S : Type*}
    [Group S] (hS : IsSimpleGroup S) (ρ : C →* S) (hρ : Function.Surjective ρ) :
    (A.subgroupOf C).map ρ = ⊥ ∨ (A.subgroupOf C).map ρ = ⊤ := by
  induction h with
  | refl =>
    refine Or.inr ?_
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hρ
  | @step A M C hAM hn _ ih =>
    rcases ih ρ hρ with h | h
    · refine Or.inl (eq_bot_iff.mpr (le_trans ?_ h.le))
      exact Subgroup.map_mono fun x hx => hAM hx
    · rw [Subgroup.normal_subgroupOf_iff hAM] at hn
      have hN : ((A.subgroupOf C).map ρ).Normal := by
        refine ⟨?_⟩
        rintro _ ⟨x, hx, rfl⟩ s
        obtain ⟨y, hy, rfl⟩ : s ∈ (M.subgroupOf C).map ρ := h ▸ Subgroup.mem_top s
        refine ⟨y * x * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
        simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx hy ⊢
        simpa using hn _ _ hx hy
      exact hS.eq_bot_or_eq_top_of_normal _

variable {Y : Type*} [Group Y]

theorem center_ne_top (hY : Open.IsQuasisimple Y) : Subgroup.center Y ≠ ⊤ := by
  intro h
  have := hY.2
  obtain ⟨p, q, hpq⟩ := exists_pair_ne (Y ⧸ Subgroup.center Y)
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  exact hpq (QuotientGroup.eq.mpr (h ▸ Subgroup.mem_top _))

theorem le_center_of_normal (hY : Open.IsQuasisimple Y) {N : Subgroup Y} (hN : N.Normal)
    (hc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : N ≤ Subgroup.center Y := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (localCores_isQuasisimple hY) hN with h | h
  · subst h
    refine absurd (eq_top_iff.mpr fun y _ => Subgroup.mem_center_iff.mpr fun z => ?_)
      (center_ne_top hY)
    exact hc z (Subgroup.mem_top z) y (Subgroup.mem_top y)
  · exact h

theorem card_quotient_center_le [Finite Y] {S : Type*} [Group S] [Finite S]
    (hY : Open.IsQuasisimple Y) (f : Y →* S) (hf : ∀ a ∈ f.ker, ∀ b ∈ f.ker, a * b = b * a) :
    Nat.card (Y ⧸ Subgroup.center Y) ≤ Nat.card S := by
  have hle := le_center_of_normal hY f.normal_ker hf
  calc Nat.card (Y ⧸ Subgroup.center Y) = (Subgroup.center Y).index := rfl
    _ ≤ f.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero f.ker.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hle)
    _ = Nat.card f.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    _ ≤ Nat.card S := Subgroup.card_le_card_group _

theorem card_quotient_center_eq {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (hY : Open.IsQuasisimple Y) (f : Y →* S) (hsurj : Function.Surjective f)
    (hf : ∀ a ∈ f.ker, ∀ b ∈ f.ker, a * b = b * a) :
    Nat.card (Y ⧸ Subgroup.center Y) = Nat.card S := by
  have hle := le_center_of_normal hY f.normal_ker hf
  have hZS : Subgroup.center S = ⊥ := by
    refine (hS.eq_bot_or_eq_top_of_normal (Subgroup.center S)).resolve_right fun h => ?_
    have hcomm : commutator Y ≤ Subgroup.center Y := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      apply hle
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (f b)) (f a)
    exact center_ne_top hY (eq_top_iff.mpr (hY.1 ▸ hcomm))
  have hge : Subgroup.center Y ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← hZS, Subgroup.mem_center_iff]
    intro s
    obtain ⟨y, rfl⟩ := hsurj s
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [← le_antisymm hle hge]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv

theorem mem_fischerComponentOrders_iff {N : ℕ} :
    N ∈ fischerComponentOrders ↔
      N = 9196830720 ∨ N = 64561751654400 ∨ N = 4089470473293004800 := by
  simp only [fischerComponentOrders, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem notMem_of_lt {N : ℕ} (h : N < 9196830720) : N ∉ fischerComponentOrders := by
  rw [mem_fischerComponentOrders_iff]
  omega

theorem factorial_div_two_notMem (n : ℕ) : n ! / 2 ∉ fischerComponentOrders := by
  have h13 : 13 ! = 6227020800 := by decide
  have h14 : 14 ! = 87178291200 := by decide
  have h16 : 16 ! = 20922789888000 := by decide
  have h17 : 17 ! = 355687428096000 := by decide
  have h20 : 20 ! = 2432902008176640000 := by decide
  have h21 : 21 ! = 51090942171709440000 := by decide
  have mono : ∀ k, (n ≤ k → n ! ≤ k !) ∧ (k ≤ n → k ! ≤ n !) := fun k =>
    ⟨Nat.factorial_le, Nat.factorial_le⟩
  rw [mem_fischerComponentOrders_iff]
  rcases Nat.lt_or_ge n 14 with h | h
  · have := (mono 13).1 (by omega)
    omega
  rcases Nat.lt_or_ge n 17 with h' | h'
  · have := (mono 16).1 (by omega)
    have := (mono 14).2 h
    omega
  rcases Nat.lt_or_ge n 21 with h'' | h''
  · have := (mono 20).1 (by omega)
    have := (mono 17).2 h'
    omega
  · have := (mono 21).2 h''
    omega

theorem eq_of_two_pow_mul_eq {a b r s : ℕ} (hr : Odd r) (hs : Odd s)
    (h : 2 ^ a * r = 2 ^ b * s) : a = b := by
  have h2 := congrArg (padicValNat 2) h
  rw [padicValNat.mul (by positivity) hr.pos.ne', padicValNat.mul (by positivity) hs.pos.ne',
    padicValNat.prime_pow, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hr)),
    padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hs))] at h2
  omega

theorem two_pow_mul_notMem (k : ℕ) {r : ℕ} (hr : Odd r) :
    2 ^ (k ^ 2) * r ∉ fischerComponentOrders := by
  have hk : ∀ e, e = 15 ∨ e = 17 ∨ e = 18 → k ^ 2 ≠ e := by
    rintro e he rfl
    have : k ≤ 4 := by
      by_contra hk
      have : 5 * 5 ≤ k ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases k <;> omega
  rw [mem_fischerComponentOrders_iff]
  rintro (h | h | h)
  · exact hk 15 (by omega)
      (eq_of_two_pow_mul_eq hr (s := 280665) (by decide) (h.trans (by norm_num)))
  · exact hk 17 (by omega)
      (eq_of_two_pow_mul_eq hr (s := 492567075) (by decide) (h.trans (by norm_num)))
  · exact hk 18 (by omega)
      (eq_of_two_pow_mul_eq hr (s := 15600091832325) (by decide) (h.trans (by norm_num)))

theorem odd_prod_two_pow_sub_one (k : ℕ) : Odd (∏ j ∈ Finset.Icc 1 k, (2 ^ (2 * j) - 1)) := by
  refine Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun j hj => ?_
  have hj : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one

end CFSG.Fischer.Classification.Recognition.SymO
