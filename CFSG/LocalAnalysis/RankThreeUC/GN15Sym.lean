module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.GroupAction.Jordan
import CFSG.CGT.PushingUpLit.BHSSym.PermSylow
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open Equiv Equiv.Perm
open scoped Pointwise

theorem closure_threeCycles_eq_alternating {n : ℕ} (hn : 5 ≤ n) (c : Fin n)
    (pairs : Finset (Finset (Fin n))) (hcard : ∀ p ∈ pairs, p.card = 2)
    (_hdisj : (pairs : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hcover : ∀ x : Fin n, x ≠ c → ∃ p ∈ pairs, x ∈ p) (hc : ∀ p ∈ pairs, c ∉ p) :
    Subgroup.closure {σ : Equiv.Perm (Fin n) | ∃ p ∈ pairs, ∃ a ∈ p, ∃ b ∈ p, a ≠ b ∧
      σ = Equiv.swap a b * Equiv.swap b c} = alternatingGroup (Fin n) := by
  classical
  set S : Set (Perm (Fin n)) := {σ | ∃ p ∈ pairs, ∃ a ∈ p, ∃ b ∈ p, a ≠ b ∧
      σ = swap a b * swap b c} with hS
  set G : Subgroup (Perm (Fin n)) := Subgroup.closure S with hG
  have hne : ∀ {p}, p ∈ pairs → ∀ {a}, a ∈ p → a ≠ c := by
    intro p hp a ha h
    exact hc _ hp (h ▸ ha)
  have hS3 : ∀ σ ∈ S, σ.IsThreeCycle := by
    rintro σ ⟨p, hp, a, ha, b, hb, hab, rfl⟩
    rw [swap_comm a b]
    exact isThreeCycle_swap_mul_swap_same hab.symm (hne hp hb) (hne hp ha)
  have hGA : G ≤ alternatingGroup (Fin n) :=
    (Subgroup.closure_le _).2 fun σ hσ => (hS3 σ hσ).mem_alternatingGroup
  have hgen : ∀ {p x y}, p ∈ pairs → x ∈ p → y ∈ p → x ≠ y → swap x y * swap y c ∈ G := by
    intro p x y hp hx hy hxy
    exact Subgroup.subset_closure ⟨_, hp, _, hx, _, hy, hxy, rfl⟩
  have hpartner : ∀ {x}, x ≠ c → ∃ p ∈ pairs, ∃ y ∈ p, x ∈ p ∧ x ≠ y := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hcover x hx
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 (hcard p hp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxp
    rcases hxp with rfl | rfl
    · exact ⟨_, hp, v, by simp, by simp, huv⟩
    · exact ⟨_, hp, u, by simp, by simp, huv.symm⟩
  have hc_apply : ∀ x y : Fin n, (swap x y * swap y c) c = swap x y y := by
    intro x y
    simp [Perm.mul_apply, swap_apply_right]
  have horb : ∀ x : Fin n, ∃ g ∈ G, g c = x := by
    intro x
    by_cases hx : x = c
    · exact ⟨1, G.one_mem, by simp [hx]⟩
    · obtain ⟨p, hp, y, hy, hxp, hxy⟩ := hpartner hx
      refine ⟨swap x y * swap y c, hgen hp hxp hy hxy, ?_⟩
      rw [hc_apply x y, swap_apply_right]
  have hpre : MulAction.IsPretransitive G (Fin n) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨gx, hgx, hx⟩ := horb x
    obtain ⟨gy, hgy, hy⟩ := horb y
    refine ⟨⟨gy * gx⁻¹, G.mul_mem hgy (G.inv_mem hgx)⟩, ?_⟩
    show (gy * gx⁻¹) x = y
    rw [← hx]
    simp [Perm.mul_apply, hy]
  have hprim : MulAction.IsPreprimitive G (Fin n) := by
    haveI := hpre
    refine MulAction.IsPreprimitive.of_isTrivialBlock_base (G := G) (X := Fin n) c ?_
    intro B hcB hB
    rw [MulAction.isBlock_iff_smul_eq_of_mem] at hB
    have key : ∀ σ : Perm (Fin n), σ ∈ G → ∀ a ∈ B, σ a ∈ B → ∀ z ∈ B, σ z ∈ B := by
      intro σ hσ a ha hσa z hz
      have h1 : (⟨σ, hσ⟩ : G) • B = B := hB ha hσa
      have h2 : (⟨σ, hσ⟩ : G) • z ∈ (⟨σ, hσ⟩ : G) • B := Set.smul_mem_smul_set hz
      rw [h1] at h2
      exact h2
    by_cases hB1 : ∀ x ∈ B, x = c
    · left
      intro x hx y hy
      rw [hB1 x hx, hB1 y hy]
    · right
      push Not at hB1
      obtain ⟨x₀, hx₀B, hx₀c⟩ := hB1
      have claim1 : ∀ {p x y}, p ∈ pairs → x ∈ p → y ∈ p → x ≠ y → x ∈ B → y ∈ B := by
        intro p x y hp hx hy hxy hxB
        have hxc := hne hp hx
        have hcx : (swap x y * swap y c) c = x := by rw [hc_apply x y, swap_apply_right]
        have hxy' : (swap x y * swap y c) x = y := by
          simp [Perm.mul_apply, swap_apply_of_ne_of_ne hxy hxc]
        have := key _ (hgen hp hx hy hxy) c hcB (by rw [hcx]; exact hxB) x hxB
        rwa [hxy'] at this
      have claim2 : ∀ {p}, p ∈ pairs → ∀ u ∈ p, u ∈ B := by
        intro p hp u hu
        by_contra huB
        obtain ⟨p', hp', v, hv, hup', huv⟩ := hpartner (hne hp hu)
        have hvB : v ∉ B := fun hvB => huB (claim1 hp' hv hup' huv.symm hvB)
        have hσx : (swap u v * swap v c) x₀ = x₀ := by
          have h1 : x₀ ≠ u := fun h => huB (h ▸ hx₀B)
          have h2 : x₀ ≠ v := fun h => hvB (h ▸ hx₀B)
          simp [Perm.mul_apply, swap_apply_of_ne_of_ne h2 hx₀c, swap_apply_of_ne_of_ne h1 h2]
        have hcu : (swap u v * swap v c) c = u := by rw [hc_apply u v, swap_apply_right]
        exact huB (hcu ▸ key _ (hgen hp' hup' hv huv) x₀ hx₀B (by rw [hσx]; exact hx₀B) c hcB)
      rw [Set.eq_univ_iff_forall]
      intro z
      by_cases hz : z = c
      · rw [hz]; exact hcB
      · obtain ⟨p, hp, hzp⟩ := hcover z hz
        exact claim2 hp z hzp
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨x, hx⟩ := exists_ne c
  obtain ⟨p, hp, y, hy, hxp, hxy⟩ := hpartner hx
  have hge : alternatingGroup (Fin n) ≤ G :=
    alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
      (hS3 _ (⟨p, hp, x, hxp, y, hy, hxy, rfl⟩ : swap x y * swap y c ∈ S))
      (hgen hp hxp hy hxy)
  exact le_antisymm hGA hge

variable {n : ℕ} {T : Subgroup (Perm (Fin n))}

private theorem card_eq_two_pow_padicValNat (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) :
    Nat.card T = 2 ^ padicValNat 2 n.factorial := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (hT2.toSylow hTidx).card_eq_multiplicity
  rw [IsPGroup.toSylow_coe] at h
  rw [h, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.factorization_def _ Nat.prime_two]

private theorem card_stabilizer_dvd_factorial {c x : Fin n} (hcx : c ≠ x)
    (hc : ∀ t ∈ T, t c = c) : Nat.card (MulAction.stabilizer T x) ∣ (n - 2).factorial := by
  classical
  set s : Finset (Fin n) := (Finset.univ.erase c).erase x with hs
  have hmem : ∀ y, y ∈ s ↔ y ≠ x ∧ y ≠ c := by
    intro y
    simp [hs, Finset.mem_erase]
  have hscard : s.card = n - 2 := by
    rw [hs, Finset.card_erase_of_mem (by simpa using hcx.symm),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  let φ : Perm {y // y ∈ s} →* Perm (Fin n) := Perm.ofSubtype
  have hle : (MulAction.stabilizer T x).map T.subtype ≤ φ.range := by
    rintro _ ⟨⟨t, ht⟩, hts, rfl⟩
    have htx : t x = x := hts
    have htc : t c = c := hc t ht
    have h1 : ∀ y, y ∈ s ↔ t y ∈ s := by
      intro y
      rw [hmem, hmem]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h1 (t.injective (h.trans htx.symm)),
          fun h => h2 (t.injective (h.trans htc.symm))⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h1 (h ▸ htx), fun h => h2 (h ▸ htc)⟩
    refine ⟨t.subtypePerm (fun y => (h1 y).symm), ?_⟩
    exact Perm.ofSubtype_subtypePerm (fun y => (h1 y).symm) (fun y hy => by
      by_contra hys
      rw [hmem] at hys
      push Not at hys
      by_cases hyx : y = x
      · exact hy (hyx ▸ htx)
      · exact hy (by rw [hys hyx]; exact htc))
  have hdvd : Nat.card ((MulAction.stabilizer T x).map T.subtype) ∣ Nat.card φ.range :=
    Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective T.subtype_injective] at hdvd
  have hcardφ : Nat.card φ.range = Nat.card (Perm {y // y ∈ s}) :=
    (Nat.card_congr (MonoidHom.ofInjective (f := φ) Perm.ofSubtype_injective).toEquiv).symm
  rw [hcardφ, Nat.card_perm, Nat.card_eq_finsetCard, hscard] at hdvd
  exact hdvd

private theorem padicValNat_factorial_eq (hn : Odd n) (hn2 : 2 ≤ n) :
    padicValNat 2 n.factorial = padicValNat 2 (n - 2).factorial + padicValNat 2 (n - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have h2 : ¬ 2 ∣ j + 2 := by
    rcases hn with ⟨k, hk⟩
    omega
  rw [Nat.factorial_succ, Nat.factorial_succ, padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity), padicValNat.eq_zero_of_not_dvd h2]
  simp only [Nat.add_sub_cancel, zero_add]
  rw [show j + 2 - 1 = j + 1 by omega, add_comm]

theorem existsUnique_fixed_of_sylowTwo (hn : Odd n) (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) :
    ∃! c : Fin n, ∀ t ∈ T, t c = c := by
  obtain ⟨c, hc⟩ := CFSG.CGT.PushingUpLit.BHSSym.exists_isFixed hn hT2
  exact ⟨c, hc, fun c' hc' => CFSG.CGT.PushingUpLit.BHSSym.eq_of_isFixed hT2 hTidx hc' hc⟩

theorem two_pow_padicValNat_le_ncard_orbit (hn : Odd n) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) {c x : Fin n} (hc : ∀ t ∈ T, t c = c) (hx : x ≠ c) :
    2 ^ padicValNat 2 (n - 1) ≤ (MulAction.orbit T x).ncard := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 2 ≤ n := by
    have h1 := Fin.val_ne_of_ne hx
    have h2 := x.isLt
    have h3 := c.isLt
    omega
  have hfac := padicValNat_factorial_eq hn hn2
  have hcard := card_eq_two_pow_padicValNat hT2 hTidx
  obtain ⟨s, hs⟩ : ∃ s, Nat.card (MulAction.stabilizer T x) = 2 ^ s :=
    IsPGroup.iff_card.mp (hT2.to_subgroup _)
  have hsle : s ≤ padicValNat 2 (n - 2).factorial :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).1
      (hs ▸ card_stabilizer_dvd_factorial (T := T) hx.symm hc)
  have horb : Nat.card (MulAction.stabilizer T x) * (MulAction.orbit T x).ncard = Nat.card T := by
    rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]
  rw [hs, hcard, hfac] at horb
  have hN : (MulAction.orbit T x).ncard = 2 ^ (padicValNat 2 (n - 2).factorial +
      padicValNat 2 (n - 1) - s) := by
    have h2 : 2 ^ (padicValNat 2 (n - 2).factorial + padicValNat 2 (n - 1)) =
        2 ^ s * 2 ^ (padicValNat 2 (n - 2).factorial + padicValNat 2 (n - 1) - s) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h2] at horb
    exact Nat.eq_of_mul_eq_mul_left (by positivity) horb
  rw [hN]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem exists_apply_eq_of_sylowTwo_two_pow_succ {m : ℕ} (hm : 1 ≤ m)
    {T : Subgroup (Perm (Fin (2 ^ m + 1)))} (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    {c x y : Fin (2 ^ m + 1)} (hc : ∀ t ∈ T, t c = c) (hx : x ≠ c) (hy : y ≠ c) :
    ∃ t ∈ T, t x = y := by
  have hodd : Odd (2 ^ m + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have h1 := two_pow_padicValNat_le_ncard_orbit hodd hT2 hTidx hc hx
  have hn1 : 2 ^ m + 1 - 1 = 2 ^ m := by omega
  rw [hn1, padicValNat.prime_pow] at h1
  have hsub : MulAction.orbit T x ⊆ {z | z ≠ c} := by
    rintro _ ⟨⟨t, ht⟩, rfl⟩
    show t x ≠ c
    intro h
    apply hx
    apply t.injective
    rw [h, hc t ht]
  have hcard : ({z : Fin (2 ^ m + 1) | z ≠ c} : Set (Fin (2 ^ m + 1))).ncard = 2 ^ m := by
    have h2 := Set.ncard_diff_singleton_add_one (s := (Set.univ : Set (Fin (2 ^ m + 1))))
      (Set.mem_univ c)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
    have h3 : ({z : Fin (2 ^ m + 1) | z ≠ c} : Set (Fin (2 ^ m + 1))) = Set.univ \ {c} := by
      ext z
      simp
    rw [h3]
    omega
  have heq : MulAction.orbit T x = {z | z ≠ c} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact h1) (Set.toFinite _)
  have hyo : y ∈ MulAction.orbit T x := by
    rw [heq]
    exact hy
  obtain ⟨⟨t, ht⟩, hty⟩ := hyo
  exact ⟨t, ht, hty⟩

theorem exists_apply_swap_eq_of_sylowTwo_two_pow_succ {m : ℕ} (hm : 1 ≤ m)
    {T : Subgroup (Perm (Fin (2 ^ m + 1)))} (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    {a b a' b' : Fin (2 ^ m + 1)} (hab : a ≠ b) (hab' : a' ≠ b')
    (h : swap a b ∈ T) (h' : swap a' b' ∈ T) : ∃ t ∈ T, t a = a' ∧ t b = b' := by
  have hodd : Odd (2 ^ m + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  obtain ⟨c, hc, -⟩ := existsUnique_fixed_of_sylowTwo hodd hT2 hTidx
  have hfix : ∀ {a b : Fin (2 ^ m + 1)}, a ≠ b → swap a b ∈ T → a ≠ c := by
    intro a b hab h hac
    have := hc _ h
    rw [hac, swap_apply_left] at this
    exact hab (hac.trans this.symm)
  obtain ⟨t, ht, hta⟩ := exists_apply_eq_of_sylowTwo_two_pow_succ hm hT2 hTidx hc (hfix hab h)
    (hfix hab' h')
  refine ⟨t, ht, hta, ?_⟩
  have h1 : swap a' (t b) ∈ T := by
    have := T.mul_mem (T.mul_mem ht h) (T.inv_mem ht)
    rwa [← swap_apply_apply, hta] at this
  exact CFSG.CGT.PushingUpLit.BHSSym.eq_of_swap_mem hT2 (fun e => hab (t.injective (hta.trans e)))
    hab' h1 h'

theorem exists_conj_swap_eq_of_sylowTwo_two_pow_succ {m : ℕ} (hm : 1 ≤ m)
    {T : Subgroup (Perm (Fin (2 ^ m + 1)))} (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    {a b a' b' : Fin (2 ^ m + 1)} (hab : a ≠ b) (hab' : a' ≠ b')
    (h : swap a b ∈ T) (h' : swap a' b' ∈ T) : ∃ t ∈ T, t * swap a b * t⁻¹ = swap a' b' := by
  obtain ⟨t, ht, hta, htb⟩ :=
    exists_apply_swap_eq_of_sylowTwo_two_pow_succ hm hT2 hTidx hab hab' h h'
  exact ⟨t, ht, by rw [← swap_apply_apply, hta, htb]⟩

theorem closure_swap_mul_swap_eq_alternating_of_sylowTwo (hn : 5 ≤ n) (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) {c : Fin n} (hc : ∀ t ∈ T, t c = c) :
    Subgroup.closure {σ : Perm (Fin n) | ∃ a b : Fin n, a ≠ b ∧ swap a b ∈ T ∧
      σ = swap a b * swap b c} = alternatingGroup (Fin n) := by
  classical
  let pairs : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun p => ∃ a b : Fin n, a ≠ b ∧ p = {a, b} ∧ swap a b ∈ T
  have hmem : ∀ p, p ∈ pairs ↔ ∃ a b : Fin n, a ≠ b ∧ p = {a, b} ∧ swap a b ∈ T := by
    intro p
    simp [pairs]
  have hfix : ∀ {a b : Fin n}, a ≠ b → swap a b ∈ T → a ≠ c ∧ b ≠ c := by
    intro a b hab h
    refine ⟨fun hac => ?_, fun hbc => ?_⟩
    · have := hc _ h
      rw [hac, swap_apply_left] at this
      exact hab (hac.trans this.symm)
    · have := hc _ h
      rw [hbc, swap_apply_right] at this
      exact hab (this.trans hbc.symm)
  have hcard : ∀ p ∈ pairs, p.card = 2 := by
    intro p hp
    obtain ⟨a, b, hab, rfl, -⟩ := (hmem p).1 hp
    exact Finset.card_pair hab
  have hdisj : (pairs : Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro p hp q hq hpq
    obtain ⟨a, b, hab, rfl, h1⟩ := (hmem p).1 hp
    obtain ⟨a', b', hab', rfl, h2⟩ := (hmem q).1 hq
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    apply hpq
    simp only [id, Finset.mem_insert, Finset.mem_singleton] at hx hx'
    have e : ∀ {a b c : Fin n}, a ≠ b → a ≠ c → swap a b ∈ T → swap a c ∈ T → b = c :=
      fun hab hac h1 h2 => CFSG.CGT.PushingUpLit.BHSSym.eq_of_swap_mem hT2 hab hac h1 h2
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · rw [e hab hab' h1 h2]
    · rw [swap_comm] at h2
      rw [e hab hab'.symm h1 h2, Finset.pair_comm]
    · rw [swap_comm] at h1
      rw [e hab.symm hab' h1 h2, Finset.pair_comm]
    · rw [swap_comm] at h1 h2
      rw [e hab.symm hab'.symm h1 h2]
  have hcover : ∀ x : Fin n, x ≠ c → ∃ p ∈ pairs, x ∈ p := by
    intro x hx
    obtain ⟨b, hxb, h⟩ := CFSG.CGT.PushingUpLit.BHSSym.exists_edge hT2 hTidx hc hx
    exact ⟨{x, b}, (hmem _).2 ⟨x, b, hxb, rfl, h⟩, by simp⟩
  have hcp : ∀ p ∈ pairs, c ∉ p := by
    intro p hp
    obtain ⟨a, b, hab, rfl, h⟩ := (hmem p).1 hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e => (hfix hab h).1 e.symm, fun e => (hfix hab h).2 e.symm⟩
  have hset : {σ : Perm (Fin n) | ∃ p ∈ pairs, ∃ a ∈ p, ∃ b ∈ p, a ≠ b ∧
      σ = swap a b * swap b c} =
      {σ : Perm (Fin n) | ∃ a b : Fin n, a ≠ b ∧ swap a b ∈ T ∧ σ = swap a b * swap b c} := by
    ext σ
    constructor
    · rintro ⟨p, hp, a, ha, b, hb, hab, rfl⟩
      obtain ⟨a₀, b₀, hab₀, rfl, h₀⟩ := (hmem p).1 hp
      refine ⟨a, b, hab, ?_, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact h₀
      · rw [swap_comm]
        exact h₀
      · exact absurd rfl hab
    · rintro ⟨a, b, hab, h, rfl⟩
      exact ⟨{a, b}, (hmem _).2 ⟨a, b, hab, rfl, h⟩, a, by simp, b, by simp, hab, rfl⟩
  rw [← hset]
  exact closure_threeCycles_eq_alternating hn c pairs hcard hdisj hcover hcp

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
