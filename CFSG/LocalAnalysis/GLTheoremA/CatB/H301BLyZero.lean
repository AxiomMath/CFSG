module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyConfig

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

open Equiv Equiv.Perm MulAction Subgroup

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem not_isThreeCycle_of_mem {W : Subgroup (Perm X)} (hW : IsPGroup 2 W) {g : Perm X}
    (hg : g ∈ W) : ¬ g.IsThreeCycle := by
  intro h3
  obtain ⟨n, hn⟩ := hW ⟨g, hg⟩
  have : g ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hd : 3 ∣ 2 ^ n := h3.orderOf ▸ orderOf_dvd_of_pow_eq_one this
  exact absurd (Nat.prime_three.dvd_of_dvd_pow hd) (by norm_num)

theorem false_of_swap_mem {E W : Subgroup (Perm X)} (c : Config E) (hW : IsPGroup 2 W)
    (hEW : E ≤ normalizer W) {i : Fin 3} {x y : X} (hx : x ∈ (c.a i).support)
    (hy : y ∈ (c.a i).support) (hxy : x ≠ y) (hs : Equiv.swap x y ∈ W) : False := by
  set a := c.a i with ha
  have hcub : a ^ 3 = 1 := c.a_cube i
  have hsup := c.support_eq i hx
  have h1 : a x ≠ x := c.ne_of_mem hx
  have h2 : a (a x) ≠ a x := fun h => h1 (a.injective h)
  have h4 : a (a (a x)) = x := by
    have := congrArg (fun g : Perm X => g x) hcub
    simpa [pow_succ] using this
  have h3 : a (a x) ≠ x := fun h => h1 ((congrArg a h).symm.trans h4)
  have hconj : Equiv.swap (a x) (a y) ∈ W := by
    rw [Equiv.swap_apply_apply]
    exact (Subgroup.mem_normalizer_iff.1 (hEW (c.a_mem i)) _).1 hs
  rw [hsup] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with hy0 | hy1 | hy2
  · exact hxy hy0.symm
  · subst hy1
    refine not_isThreeCycle_of_mem hW (W.mul_mem hs hconj) ?_
    rw [Equiv.swap_comm x]
    exact isThreeCycle_swap_mul_swap_same h1 h2.symm h3.symm
  · subst hy2
    refine not_isThreeCycle_of_mem hW (W.mul_mem hs hconj) ?_
    rw [h4, Equiv.swap_comm (a x) x]
    exact isThreeCycle_swap_mul_swap_same hxy h1.symm h2

theorem swap_mem_of_orbit_two {E W : Subgroup (Perm X)} (c : Config E) (hE : IsPGroup 3 E)
    (hW : IsPGroup 2 W) (hEW : E ≤ normalizer W) (hp : ∀ w ∈ W, w c.p = c.p)
    (hq : ∀ w ∈ W, w c.q = c.q) {i : Fin 3} {x y : X} (hx : x ∈ (c.a i).support)
    (hy : y ∈ (c.a i).support) (hxy : x ≠ y) {w : Perm X} (hw : w ∈ W) (hwx : w x = y)
    (h2 : ∀ w' ∈ W, w' x = x ∨ w' x = y) : Equiv.swap x y ∈ W := by
  obtain ⟨w0, hw0, hw0x, hcomm⟩ := exists_comm_elt hE hW hEW ⟨w, hw, hwx⟩
  have hout : ∀ z, z ∉ (c.a i).support → w0 z = z := by
    intro z hz
    by_cases hzp : z = c.p
    · rw [hzp]; exact hp w0 hw0
    by_cases hzq : z = c.q
    · rw [hzq]; exact hq w0 hw0
    obtain ⟨j, hj⟩ := c.cover z hzp hzq
    have hji : j ≠ i := fun h => hz (h ▸ hj)
    have hcx : c.a j x = x := c.fix_of_notMem fun h => hji (c.mem_inj h hx)
    have hcy : c.a j y = y := c.fix_of_notMem fun h => hji (c.mem_inj h hy)
    exact fix_of_comm hW hw0 (c.a_cube j) (c.supp_card j) (hcomm _ (c.a_mem j) hcx hcy).symm
      (c.ne_of_mem hj)
  have hw0y : w0 y = x := by
    have h1 : w0 y = (w0 * w) x := by rw [Perm.mul_apply, hwx]
    rcases h2 (w0 * w) (W.mul_mem hw0 hw) with h | h
    · rw [h1, h]
    · exact absurd (w0.injective ((h1.trans h).trans hw0x.symm)) hxy.symm
  have hsw : w0 = Equiv.swap x y := by
    ext u
    by_cases hux : u = x
    · rw [hux, hw0x, Equiv.swap_apply_left]
    by_cases huy : u = y
    · rw [huy, hw0y, Equiv.swap_apply_right]
    rw [Equiv.swap_apply_of_ne_of_ne hux huy]
    by_cases hu : u ∈ (c.a i).support
    · have hmem : w0 u ∈ (c.a i).support := by
        by_contra hn
        have h2' : w0 u = u := w0.injective (hout _ hn)
        exact hn (by rw [h2']; exact hu)
      have hsub : (c.a i).support = {x, y, u} := by
        refine (Finset.eq_of_subset_of_card_le (s := ({x, y, u} : Finset X)) ?_ ?_).symm
        · intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl <;> assumption
        · rw [c.supp_card i, Finset.card_eq_three.2 ⟨x, y, u, hxy, Ne.symm hux, Ne.symm huy, rfl⟩]
      rw [hsub] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact absurd (w0.injective (h.trans hw0y.symm)) huy
      · exact absurd (w0.injective (h.trans hw0x.symm)) hux
      · exact h
    · exact hout u hu
  rw [← hsw]
  exact hw0

theorem eq_bot_of_fix {E W : Subgroup (Perm X)} (c : Config E) (hE : IsPGroup 3 E)
    (hW : IsPGroup 2 W) (hEW : E ≤ normalizer W) (hp : ∀ w ∈ W, w c.p = c.p)
    (hq : ∀ w ∈ W, w c.q = c.q) : W = ⊥ := by
  by_contra hne
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨x, hx⟩ : ∃ x, w x ≠ x := by
    by_contra h
    exact hw1 (Subtype.ext (Equiv.ext fun x => by_contra fun h' => h ⟨x, h'⟩))
  have hxp : x ≠ c.p := by rintro rfl; exact hx (hp w hw)
  have hxq : x ≠ c.q := by rintro rfl; exact hx (hq w hw)
  obtain ⟨i, hi⟩ := c.cover x hxp hxq
  obtain ⟨k, hk⟩ := exists_card_orbit_eq hW x
  have hxΩ : x ∈ (orbit W x : Set X) := mem_orbit_self x
  have hyΩ : w x ∈ (orbit W x : Set X) := mem_orbit_iff.2 ⟨⟨w, hw⟩, rfl⟩
  have hΩY : ∀ z ∈ (orbit W x : Set X), z ≠ c.p ∧ z ≠ c.q := by
    intro z hz
    obtain ⟨⟨v, hv⟩, rfl⟩ := mem_orbit_iff.1 hz
    exact ⟨fun h => hxp (v.injective (h.trans (hp v hv).symm)),
      fun h => hxq (v.injective (h.trans (hq v hv).symm))⟩
  have hk' : (orbit W x : Set X).ncard = 2 ^ k := by rw [← Nat.card_coe_set_eq]; exact hk
  by_cases hA : ∃ m, ∀ z ∈ (orbit W x : Set X), z ∈ (c.a m).support
  · obtain ⟨m, hm⟩ := hA
    have hmi : m = i := c.mem_inj (hm x hxΩ) hi
    rw [hmi] at hm
    have hle : (orbit W x : Set X).ncard ≤ 3 :=
      (Set.ncard_le_ncard (t := ((c.a i).support : Set X)) (fun z hz => hm z hz)
        (Finset.finite_toSet _)).trans (by rw [Set.ncard_coe_finset, c.supp_card])
    have hge : 1 < (orbit W x : Set X).ncard :=
      (Set.one_lt_ncard_iff (Set.toFinite _)).2 ⟨x, w x, hxΩ, hyΩ, hx.symm⟩
    have hcard2 : (orbit W x : Set X).ncard = 2 := by
      rcases k with _ | _ | k
      · rw [pow_zero] at hk'; omega
      · simpa using hk'
      · have : 4 ≤ 2 ^ (k + 1 + 1) := by
          rw [pow_succ, pow_succ]; have := Nat.one_le_two_pow (n := k); omega
        omega
    have h2 : ∀ w' ∈ W, w' x = x ∨ w' x = w x := by
      intro w' hw'
      by_contra h
      have hne' : w' x ≠ x ∧ w' x ≠ w x := not_or.1 h
      have : 2 < (orbit W x : Set X).ncard := (Set.two_lt_ncard_iff (Set.toFinite _)).2
        ⟨x, w x, w' x, hxΩ, hyΩ, mem_orbit_iff.2 ⟨⟨w', hw'⟩, rfl⟩, hx.symm, hne'.1.symm,
          hne'.2.symm⟩
      omega
    exact false_of_swap_mem c hW hEW hi (hm _ hyΩ) hx.symm
      (swap_mem_of_orbit_two c hE hW hEW hp hq hi (hm _ hyΩ) hx.symm hw rfl h2)
  · have hB : ∀ m, ∃ z ∈ (orbit W x : Set X), z ∉ (c.a m).support := fun m => by
      by_contra h
      exact hA ⟨m, fun z hz => by_contra fun hn => h ⟨z, hz, hn⟩⟩
    let F : Subgroup (Perm X) := E ⊓ setStab (orbit W x : Set X)
    have hF : IsPGroup 3 F := hE.to_le inf_le_left
    have haF : ∀ m, c.a m ∈ F := fun m => by
      obtain ⟨z, hzΩ, hz⟩ := hB m
      exact ⟨c.a_mem m, mem_setStab_orbit hEW hzΩ (c.a_mem m) (c.fix_of_notMem hz)⟩
    have hmod := card_modEq_fix hF (orbit W x : Set X)
      (fun f hf z hz => (mem_setStab.1 hf.2 z).2 hz)
    have hempty : IsEmpty {z : X // z ∈ (orbit W x : Set X) ∧ ∀ f ∈ F, f z = z} :=
      ⟨fun ⟨z, hz, hf⟩ => by
        obtain ⟨hzp, hzq⟩ := hΩY z hz
        obtain ⟨m, hm⟩ := c.cover z hzp hzq
        exact c.ne_of_mem hm (hf _ (haF m))⟩
    have h0 : Nat.card {z : X // z ∈ (orbit W x : Set X) ∧ ∀ f ∈ F, f z = z} = 0 :=
      Nat.card_of_isEmpty
    rw [h0] at hmod
    have h3 : 3 ∣ Nat.card (orbit W x : Set X) := (Nat.modEq_zero_iff_dvd).1 hmod
    rw [hk] at h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

end
