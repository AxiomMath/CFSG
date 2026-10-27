module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAMA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ} {s t : Equiv.Perm (Fin n)}

@[expose] def OffOrb (s t : Equiv.Perm (Fin n)) (a c : Fin n) : Prop :=
  c ≠ a ∧ c ≠ s a ∧ c ≠ t a ∧ c ≠ s (t a)

theorem orbVec_apply_of_offOrb {a i : Fin n} (h : OffOrb s t a i) : orbVec s t a i = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [orbVec, pairVec_apply, h1, h2, h3, h4]

theorem mem_orbit_of_not_offOrb {a i : Fin n} (h : ¬ OffOrb s t a i) :
    i = a ∨ i = s a ∨ i = t a ∨ i = s (t a) := by
  by_contra h'
  push Not at h'
  exact h h'

theorem regular_orbit (hs2 : s * s = 1) (ht2 : t * t = 1) (hst : s * t = t * s) {a : Fin n}
    (hsa : s a ≠ a) (hta : t a ≠ a) (hsta : s (t a) ≠ a) {x : Fin n}
    (hx : x = a ∨ x = s a ∨ x = t a ∨ x = s (t a)) : s x ≠ x ∧ t x ≠ x ∧ s (t x) ≠ x := by
  have hss := apply_apply_of_mul_self hs2
  have htt := apply_apply_of_mul_self ht2
  have hts : ∀ i, t (s i) = s (t i) := fun i => by
    rw [← Equiv.Perm.mul_apply, ← hst, Equiv.Perm.mul_apply]
  have e5 : t a ≠ s a := fun h => hsta (by rw [h, hss])
  have e6 : s (t a) ≠ s a := fun h => hta (s.injective h)
  have e7 : s (t a) ≠ t a := fun h => hsa (t.injective (by rw [hts, h]))
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨hsa, hta, hsta⟩
  · refine ⟨by rw [hss]; exact Ne.symm hsa, by rw [hts]; exact e6, ?_⟩
    rw [hts, hss]
    exact e5
  · refine ⟨e7, by rw [htt]; exact Ne.symm hta, ?_⟩
    rw [htt]
    exact Ne.symm e5
  · refine ⟨by rw [hss]; exact Ne.symm e7, by rw [hts, htt]; exact Ne.symm e6, ?_⟩
    rw [hts, htt, hss]
    exact Ne.symm hsta

theorem orbVec_apply_of_not_offOrb (hs2 : s * s = 1) (hst : s * t = t * s) {a : Fin n}
    (hsa : s a ≠ a) (hta : t a ≠ a) (hsta : s (t a) ≠ a) {i : Fin n} (h : ¬ OffOrb s t a i) :
    orbVec s t a i = 1 := by
  have hss := apply_apply_of_mul_self hs2
  have hts : ∀ i, t (s i) = s (t i) := fun i => by
    rw [← Equiv.Perm.mul_apply, ← hst, Equiv.Perm.mul_apply]
  have e5 : t a ≠ s a := fun h => hsta (by rw [h, hss])
  have e7 : s (t a) ≠ t a := fun h => hsa (t.injective (by rw [hts, h]))
  rcases mem_orbit_of_not_offOrb h with rfl | rfl | rfl | rfl
  · simp [orbVec, pairVec_apply, Ne.symm hsa, Ne.symm hta, Ne.symm hsta]
  · simp [orbVec, pairVec_apply, hsa, Ne.symm e5, Ne.symm hta]
  · simp [orbVec, pairVec_apply, hta, e5, Ne.symm e7]
  · simp [orbVec, pairVec_apply, hsta, e7, hta]

theorem offOrb_s (hs2 : s * s = 1) {a c : Fin n} (h : OffOrb s t a c) : OffOrb s t a (s c) := by
  have hss := apply_apply_of_mul_self hs2
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun e => h2 (by rw [← e, hss]), fun e => h1 (s.injective e),
    fun e => h4 (by rw [← e, hss]), fun e => h3 (s.injective e)⟩

theorem offOrb_t (ht2 : t * t = 1) (hst : s * t = t * s) {a c : Fin n} (h : OffOrb s t a c) :
    OffOrb s t a (t c) := by
  have htt := apply_apply_of_mul_self ht2
  have hts : ∀ i, t (s i) = s (t i) := fun i => by
    rw [← Equiv.Perm.mul_apply, ← hst, Equiv.Perm.mul_apply]
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun e => h3 (by rw [← e, htt]), fun e => h4 (by rw [← hts, ← e, htt]),
    fun e => h1 (t.injective e), fun e => h2 (by rw [← htt c, e, ← hts, htt])⟩

theorem offOrb_symm (hs2 : s * s = 1) (ht2 : t * t = 1) (hst : s * t = t * s) {a c : Fin n}
    (h : OffOrb s t a c) : OffOrb s t c a := by
  have hss := apply_apply_of_mul_self hs2
  have htt := apply_apply_of_mul_self ht2
  have hts : ∀ i, t (s i) = s (t i) := fun i => by
    rw [← Equiv.Perm.mul_apply, ← hst, Equiv.Perm.mul_apply]
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨Ne.symm h1, fun e => h2 (by rw [e, hss]), fun e => h3 (by rw [e, htt]),
    fun e => h4 (by rw [e, hts, htt, hss])⟩

theorem false_of_regular_offOrb (hs2 : s * s = 1) (ht2 : t * t = 1) (hst : s * t = t * s)
    {u : Fin n → ZMod 2} (hu : ¬ ModPi u 0)
    (hP : ∀ a c, a ≠ c → PairCond s t u (pairVec a c)) {a c : Fin n} (hsa : s a ≠ a)
    (hta : t a ≠ a) (hsta : s (t a) ≠ a) (hc : OffOrb s t a c) (hsc : s c ≠ c) (htc : t c ≠ c)
    (hstc : s (t c) ≠ c) : False := by
  have hac := modPi_of_pairCond hs2 ht2 hst hsa hta hsta hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    (hP a c (Ne.symm hc.1))
  have hcc : ¬ OffOrb s t c c := fun h => h.1 rfl
  by_cases hd : ∃ d, OffOrb s t a d ∧ OffOrb s t c d
  · obtain ⟨d, hda, hdc⟩ := hd
    have had := modPi_of_pairCond hs2 ht2 hst hsa hta hsta hda.1 hda.2.1 hda.2.2.1 hda.2.2.2
      (hP a d (Ne.symm hda.1))
    refine not_modPi (i := c) (j := a) ?_ ?_ (modPi_trans (modPi_symm hac) had)
    · rw [Pi.add_apply, Pi.add_apply, orbVec_apply_of_offOrb hc,
        orbVec_apply_of_not_offOrb hs2 hst hsc htc hstc hcc,
        orbVec_apply_of_offOrb (offOrb_symm hs2 ht2 hst hdc)]
      decide
    · rw [Pi.add_apply, Pi.add_apply, orbVec_apply_of_offOrb (offOrb_symm hs2 ht2 hst hc),
        orbVec_apply_of_offOrb (offOrb_symm hs2 ht2 hst hda)]
  · push Not at hd
    have hca := offOrb_symm hs2 ht2 hst hc
    have hone : orbVec s t a + orbVec s t c = 1 := by
      funext i
      rw [Pi.add_apply, Pi.one_apply]
      by_cases hi : OffOrb s t a i
      · rw [orbVec_apply_of_offOrb hi, orbVec_apply_of_not_offOrb hs2 hst hsc htc hstc
          (hd i hi), zero_add]
      · have hci : OffOrb s t c i := by
          rcases mem_orbit_of_not_offOrb hi with h | h | h | h <;> rw [h]
          · exact hca
          · exact offOrb_s hs2 hca
          · exact offOrb_t ht2 hst hca
          · exact offOrb_s hs2 (offOrb_t ht2 hst hca)
        rw [orbVec_apply_of_not_offOrb hs2 hst hsa hta hsta hi, orbVec_apply_of_offOrb hci,
          add_zero]
    rw [hone] at hac
    exact hu (modPi_trans hac (Or.inr (zero_add 1).symm))

theorem modPi_orbVec (hn : 5 ≤ n) (hs2 : s * s = 1) (ht2 : t * t = 1) (hst : s * t = t * s)
    {u : Fin n → ZMod 2} (hu : ¬ ModPi u 0)
    (hP : ∀ a c, a ≠ c → PairCond s t u (pairVec a c)) {a : Fin n} (hsa : s a ≠ a)
    (hta : t a ≠ a) (hsta : s (t a) ≠ a) : ModPi u (orbVec s t a) := by
  obtain ⟨c, hc⟩ : ∃ c, OffOrb s t a c := exists_ne_four hn a (s a) (t a) (s (t a))
  by_cases hreg : s c ≠ c ∧ t c ≠ c ∧ s (t c) ≠ c
  · exact (false_of_regular_offOrb hs2 ht2 hst hu hP hsa hta hsta hc hreg.1 hreg.2.1
      hreg.2.2).elim
  · have hac := modPi_of_pairCond hs2 ht2 hst hsa hta hsta hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      (hP a c (Ne.symm hc.1))
    rw [orbVec_eq_zero hs2 hst hreg, add_zero] at hac
    exact hac

theorem exists_regular_modPi (hn : 5 ≤ n) (hs2 : s * s = 1) (ht2 : t * t = 1)
    (hst : s * t = t * s) (hs1 : s ≠ 1) (hsign : Equiv.Perm.sign s = 1) {u : Fin n → ZMod 2}
    (hu : ¬ ModPi u 0) (hP : ∀ a c, a ≠ c → PairCond s t u (pairVec a c)) :
    ∃ a, s a ≠ a ∧ t a ≠ a ∧ s (t a) ≠ a ∧ ModPi u (orbVec s t a) := by
  obtain ⟨a, hsa, hta, hsta⟩ := exists_regular hn hs2 hst hs1 hsign hu hP
  exact ⟨a, hsa, hta, hsta, modPi_orbVec hn hs2 ht2 hst hu hP hsa hta hsta⟩

end CFSG.ClassicalInvolution.Q3.TL4
