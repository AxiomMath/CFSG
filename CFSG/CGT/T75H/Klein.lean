module

public import CFSG.CGT.Timmesfeld75.Involutions
public import CFSG.CGT.Timmesfeld75.Sec3TwelveIrr

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem exists_basis_of_ne_one {a b : G} (hT : ∀ t ∈ T, t = 1 ∨ t = a ∨ t = b ∨ t = b * a)
    (haT : a ∈ T) (hbT : b ∈ T) (hab : a * b = b * a) (haa : a * a = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) {f : G} (hf : f ∈ T) (hf1 : f ≠ 1) :
    ∃ x ∈ T, x ≠ 1 ∧ x ≠ f ∧ ∀ t ∈ T, t = 1 ∨ t = f ∨ t = x ∨ t = x * f := by
  rcases hT f hf with h | h | h | h
  · exact absurd h hf1
  ·
    refine ⟨b, hbT, hb1, by rw [h]; exact hne.symm, fun t ht => ?_⟩
    rcases hT t ht with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (h'.trans h.symm))
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (by rw [h', h])))
  ·
    refine ⟨a, haT, ha1, by rw [h]; exact hne, fun t ht => ?_⟩
    rcases hT t ht with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inl (h'.trans h.symm))
    · exact Or.inr (Or.inr (Or.inr (by rw [h', h, hab])))
  ·
    have hax : a ≠ b * a := fun h' => hb1 (by
      have : (1 : G) * a = b * a := by rw [one_mul]; exact h'
      exact (mul_right_cancel this).symm)
    refine ⟨a, haT, ha1, by rw [h]; exact hax, fun t ht => ?_⟩
    rcases hT t ht with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [h', h]
      calc b = b * (a * a) := by rw [haa, mul_one]
        _ = (b * a) * a := by rw [mul_assoc]
        _ = (a * b) * a := by rw [hab]
        _ = a * (b * a) := by rw [mul_assoc]
    · exact Or.inr (Or.inl (h'.trans h.symm))

theorem conj_eq_mul_of_fixed {f x : G} (hxT : x ∈ T) (hx1 : x ≠ 1) (hxf : x ≠ f)
    (hbasis : ∀ t ∈ T, t = 1 ∨ t = f ∨ t = x ∨ t = x * f) {w : G}
    (hwN : ∀ t ∈ T, w * t * w⁻¹ ∈ T) (hwf : w * f * w⁻¹ = f)
    (hnc : ¬ ∀ t ∈ T, w * t = t * w) : w * x * w⁻¹ = x * f := by
  rcases hbasis _ (hwN x hxT) with h | h | h | h
  · exfalso
    apply hx1
    calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply hxf
    calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
      _ = w⁻¹ * (w * f * w⁻¹) * w := by rw [h, hwf]
      _ = f := by group
  · exfalso
    apply hnc
    intro t ht
    have hwx : w * x = x * w := mul_inv_eq_iff_eq_mul.1 h
    have hwf' : w * f = f * w := mul_inv_eq_iff_eq_mul.1 hwf
    rcases hbasis t ht with h' | h' | h' | h'
    · rw [h']; simp
    · rw [h']; exact hwf'
    · rw [h']; exact hwx
    · rw [h']
      calc w * (x * f) = (w * x) * f := by group
        _ = (x * w) * f := by rw [hwx]
        _ = x * (w * f) := by group
        _ = x * (f * w) := by rw [hwf']
        _ = (x * f) * w := by group
  · exact h

theorem eq_of_comm_of_conj {f x : G} (hf1 : f ≠ 1)
    (hbasis : ∀ t ∈ T, t = 1 ∨ t = f ∨ t = x ∨ t = x * f) (hff : f * f = 1) {w : G}
    (hwf : w * f * w⁻¹ = f) (hwx : w * x * w⁻¹ = x * f) {t : G} (ht : t ∈ T)
    (hwt : w * t = t * w) : t = 1 ∨ t = f := by
  have hwx' : w * x = x * f * w := mul_inv_eq_iff_eq_mul.1 hwx
  have hwf' : w * f = f * w := mul_inv_eq_iff_eq_mul.1 hwf
  have hfw : ∀ h2 : x * w = x * (f * w), False := fun h2 => hf1 (by
    have h3 : w = f * w := mul_left_cancel h2
    calc f = (f * w) * w⁻¹ := by group
      _ = w * w⁻¹ := by rw [← h3]
      _ = 1 := by group)
  rcases hbasis t ht with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [h] at hwt
    exact hfw (by rw [← hwt, hwx', mul_assoc])
  · exfalso
    rw [h] at hwt
    have e1 : w * (x * f) = x * w := by
      calc w * (x * f) = (w * x) * f := by group
        _ = (x * f * w) * f := by rw [hwx']
        _ = x * f * (w * f) := by group
        _ = x * f * (f * w) := by rw [hwf']
        _ = x * (f * f) * w := by group
        _ = x * w := by rw [hff, mul_one]
    exact hfw (by rw [← mul_assoc]; exact e1.symm.trans hwt)

theorem mul_cent_of_fixed {f x : G} (hxT : x ∈ T) (hx1 : x ≠ 1) (hxf : x ≠ f)
    (hbasis : ∀ t ∈ T, t = 1 ∨ t = f ∨ t = x ∨ t = x * f) (hff : f * f = 1) {w w' : G}
    (hwN : ∀ t ∈ T, w * t * w⁻¹ ∈ T)
    (hw'N : ∀ t ∈ T, w' * t * w'⁻¹ ∈ T) (hwf : w * f * w⁻¹ = f) (hw'f : w' * f * w'⁻¹ = f)
    (hnc : ¬ ∀ t ∈ T, w * t = t * w) (hnc' : ¬ ∀ t ∈ T, w' * t = t * w') :
    ∀ t ∈ T, t * (w * w') = (w * w') * t := by
  have hwx := conj_eq_mul_of_fixed hxT hx1 hxf hbasis hwN hwf hnc
  have hw'x := conj_eq_mul_of_fixed hxT hx1 hxf hbasis hw'N hw'f hnc'
  have hwx' : w * x = x * f * w := mul_inv_eq_iff_eq_mul.1 hwx
  have hw'x' : w' * x = x * f * w' := mul_inv_eq_iff_eq_mul.1 hw'x
  have hwf' : w * f = f * w := mul_inv_eq_iff_eq_mul.1 hwf
  have hw'f' : w' * f = f * w' := mul_inv_eq_iff_eq_mul.1 hw'f
  have hcf : (w * w') * f = f * (w * w') := by
    calc (w * w') * f = w * (w' * f) := by group
      _ = w * (f * w') := by rw [hw'f']
      _ = (w * f) * w' := by group
      _ = (f * w) * w' := by rw [hwf']
      _ = f * (w * w') := by group
  have hcx : (w * w') * x = x * (w * w') := by
    calc (w * w') * x = w * (w' * x) := by group
      _ = w * (x * f * w') := by rw [hw'x']
      _ = (w * x) * f * w' := by group
      _ = (x * f * w) * f * w' := by rw [hwx']
      _ = x * f * (w * f) * w' := by group
      _ = x * f * (f * w) * w' := by rw [hwf']
      _ = x * (f * f) * (w * w') := by group
      _ = x * (w * w') := by rw [hff, mul_one]
  intro t ht
  rcases hbasis t ht with h | h | h | h
  · rw [h]; simp
  · rw [h]; exact hcf.symm
  · rw [h]; exact hcx.symm
  · rw [h]
    calc (x * f) * (w * w') = x * (f * (w * w')) := by group
      _ = x * ((w * w') * f) := by rw [hcf]
      _ = (x * (w * w')) * f := by group
      _ = ((w * w') * x) * f := by rw [hcx]
      _ = (w * w') * (x * f) := by group

theorem eq_one_of_mul_self_eq_one_of_odd {N : Subgroup G} (hNodd : Odd (Nat.card N)) {n : G}
    (hn : n ∈ N) (h : n * n = 1) : n = 1 := by
  have h5 : orderOf n ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨n, hn⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have hodd : Odd (orderOf n) := Odd.of_dvd_nat hNodd h5
  have hd : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h' | h'
  · exact orderOf_eq_one_iff.1 h'
  · rw [h'] at hodd
    exact absurd hodd (by decide)

theorem eq_mul_of_fixed {H N : Subgroup G} (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hNodd : Odd (Nat.card N)) (hTN : T ⊓ N = ⊥) (hNc : N ≤ Subgroup.centralizer (T : Set G))
    (hdec : ∀ c ∈ Subgroup.centralizer (T : Set G) ⊓ H, ∃ t ∈ T, ∃ n ∈ N, c = t * n)
    (htt : ∀ t ∈ T, t * t = 1) {f x : G} (hxT : x ∈ T) (hx1 : x ≠ 1) (hxf : x ≠ f)
    (hbasis : ∀ t ∈ T, t = 1 ∨ t = f ∨ t = x ∨ t = x * f) (hff : f * f = 1) {g q : G}
    (hgH : g ∈ H) (hqH : q ∈ H) (hgg : g * g = 1) (hqq : q * q = 1)
    (hNg : ∀ n ∈ N, n * g = g * n) (hgf : g * f * g⁻¹ = f) (hqf : q * f * q⁻¹ = f)
    (hgnc : ¬ ∀ t ∈ T, g * t = t * g) (hqnc : ¬ ∀ t ∈ T, q * t = t * q) :
    ∃ t ∈ T, g * t = t * g ∧ q = t * g := by
  have hgN : ∀ t ∈ T, g * t * g⁻¹ ∈ T := fun t ht => conj_mem_of_mem_normalizer (hHN hgH) ht
  have hqN : ∀ t ∈ T, q * t * q⁻¹ ∈ T := fun t ht => conj_mem_of_mem_normalizer (hHN hqH) ht
  have hcT := mul_cent_of_fixed hxT hx1 hxf hbasis hff hqN hgN hqf hgf hqnc hgnc
  have hcH : q * g ∈ H := H.mul_mem hqH hgH
  obtain ⟨t, ht, n, hn, hcn⟩ := hdec (q * g) ⟨Subgroup.mem_centralizer_iff.2 hcT, hcH⟩
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right hqq
  have hinv : g * (t * n) * g⁻¹ = (t * n)⁻¹ := by
    rw [← hcn]
    calc g * (q * g) * g⁻¹ = g * q := by group
      _ = (q * g)⁻¹ := by rw [mul_inv_rev, hg', hq']
  have hgtT : g * t * g⁻¹ ∈ T := hgN t ht
  have hgn : g * n * g⁻¹ = n := mul_inv_eq_iff_eq_mul.2 (hNg n hn).symm
  have htt' := htt t ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt'
  have hnt : ∀ s ∈ T, ∀ m ∈ N, s * m = m * s := fun s hs m hm =>
    Subgroup.mem_centralizer_iff.1 (hNc hm) s hs
  have h1 : (g * t * g⁻¹) * n = n⁻¹ * t := by
    calc (g * t * g⁻¹) * n = (g * t * g⁻¹) * (g * n * g⁻¹) := by rw [hgn]
      _ = g * (t * n) * g⁻¹ := by group
      _ = (t * n)⁻¹ := hinv
      _ = n⁻¹ * t⁻¹ := mul_inv_rev t n
      _ = n⁻¹ * t := by rw [htinv]
  have h2 : (t * (g * t * g⁻¹)) * n = n⁻¹ := by
    calc (t * (g * t * g⁻¹)) * n = t * ((g * t * g⁻¹) * n) := by group
      _ = t * (n⁻¹ * t) := by rw [h1]
      _ = (t * n⁻¹) * t := by group
      _ = (n⁻¹ * t) * t := by rw [hnt t ht n⁻¹ (N.inv_mem hn)]
      _ = n⁻¹ * (t * t) := by group
      _ = n⁻¹ := by rw [htt', mul_one]
  have h3 : t * (g * t * g⁻¹) = n⁻¹ * n⁻¹ := by
    calc t * (g * t * g⁻¹) = ((t * (g * t * g⁻¹)) * n) * n⁻¹ := by group
      _ = n⁻¹ * n⁻¹ := by rw [h2]
  have hmem : t * (g * t * g⁻¹) ∈ T ⊓ N := by
    refine ⟨T.mul_mem ht hgtT, ?_⟩
    rw [h3]
    exact N.mul_mem (N.inv_mem hn) (N.inv_mem hn)
  rw [hTN, Subgroup.mem_bot] at hmem
  have hgt : g * t * g⁻¹ = t := by
    have : g * t * g⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right hmem
    rw [this, htinv]
  have hn1 : n = 1 := by
    apply eq_one_of_mul_self_eq_one_of_odd hNodd hn
    rw [hmem] at h3
    have h4 : (n * n)⁻¹ = 1 := by rw [mul_inv_rev]; exact h3.symm
    exact inv_eq_one.1 h4
  refine ⟨t, ht, mul_inv_eq_iff_eq_mul.1 hgt, ?_⟩
  calc q = (q * g) * g⁻¹ := by group
    _ = t * 1 * g⁻¹ := by rw [hcn, hn1]
    _ = t * g := by rw [hg', mul_one]

end CFSG.CGT.T75H
