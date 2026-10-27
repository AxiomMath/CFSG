module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open CFSG.Open Subgroup

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

theorem pow_conj_eq_zpow {y c : G} {m : ℤ} (h : y * c * y⁻¹ = c ^ m) (j : ℕ) :
    y ^ j * c * (y ^ j)⁻¹ = c ^ (m ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : y * c ^ (m ^ j) * y⁻¹ = (y * c * y⁻¹) ^ (m ^ j) := by
      rw [← conj_zpow]
    calc y ^ (j + 1) * c * (y ^ (j + 1))⁻¹ = y * (y ^ j * c * (y ^ j)⁻¹) * y⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          group
      _ = c ^ (m ^ (j + 1)) := by
          rw [ih, h1, h, ← zpow_mul, pow_succ, mul_comm]

theorem commute_of_normalizes_prime_order [Finite G] {y c : G} (hy : IsPGroup p (zpowers y))
    (hc : orderOf c = p) (hyc : y * c * y⁻¹ ∈ zpowers c) : y * c = c * y := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hyc
  obtain ⟨k, hk⟩ := hy.exists_card_eq
  have hyk : y ^ (p ^ k) = 1 := by
    rw [← hk, Nat.card_zpowers]
    exact pow_orderOf_eq_one y
  have h1 := pow_conj_eq_zpow hm.symm (p ^ k)
  rw [hyk] at h1
  simp only [one_mul, inv_one, mul_one] at h1
  have h2 : c ^ (m ^ (p ^ k) - 1) = 1 := by
    rw [zpow_sub, zpow_one, ← h1]
    simp
  have h2' : (orderOf c : ℤ) ∣ m ^ (p ^ k) - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [hc] at h2'
  have h3 : ((m ^ (p ^ k) - 1 : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h2'
  have h4 : ((m : ZMod p)) ^ (p ^ k) = 1 := by
    push_cast at h3
    exact sub_eq_zero.mp h3
  rw [ZMod.pow_card_pow] at h4
  have h5 : (p : ℤ) ∣ m - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h4, sub_self]
  have h6 : c ^ m = c := by
    obtain ⟨t, ht⟩ := h5
    have : m = 1 + p * t := by linarith
    rw [this, zpow_add, zpow_one, zpow_mul]
    have : c ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hc]
      exact pow_orderOf_eq_one c
    rw [this, one_zpow, mul_one]
  rw [h6] at hm
  calc y * c = (y * c * y⁻¹) * y := by group
    _ = c * y := by rw [← hm]


@[expose] def omegaCenter (p : ℕ) (Q : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ Q ∧ (∀ q ∈ Q, q * z = z * q) ∧ z ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haQ, hac, hap⟩ ⟨hbQ, hbc, hbp⟩
    refine ⟨mul_mem haQ hbQ, fun q hq => ?_, ?_⟩
    · rw [← mul_assoc, hac q hq, mul_assoc, hbc q hq, mul_assoc]
    · rw [(show Commute a b from hbc a haQ).mul_pow, hap, hbp, mul_one]
  one_mem' := ⟨one_mem Q, fun q _ => by simp, one_pow p⟩
  inv_mem' := by
    rintro a ⟨haQ, hac, hap⟩
    refine ⟨inv_mem haQ, fun q hq => ?_, by rw [inv_pow, hap, inv_one]⟩
    have := (Commute.inv_right (show Commute q a from hac q hq))
    exact this

theorem mem_omegaCenter {p : ℕ} {Q : Subgroup G} {z : G} :
    z ∈ omegaCenter p Q ↔ z ∈ Q ∧ (∀ q ∈ Q, q * z = z * q) ∧ z ^ p = 1 := Iff.rfl

theorem omegaCenter_le (p : ℕ) (Q : Subgroup G) : omegaCenter p Q ≤ Q := fun _ h => h.1

theorem isElemAbelian_omegaCenter (p : ℕ) (Q : Subgroup G) :
    IsElemAbelian p (omegaCenter p Q) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => hz.2.2⟩
  apply Subtype.ext
  exact b.2.2.1 a a.2.1

theorem conj_mem_omegaCenter {p : ℕ} {Q : Subgroup G} {g z : G} (hg : g ∈ normalizer (Q : Set G))
    (hz : z ∈ omegaCenter p Q) : g * z * g⁻¹ ∈ omegaCenter p Q := by
  obtain ⟨hzQ, hzc, hzp⟩ := hz
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzQ, fun q hq => ?_, ?_⟩
  · have hq' : g⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) q).mp hq
      simpa using this
    have := hzc _ hq'
    calc q * (g * z * g⁻¹) = g * ((g⁻¹ * q * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * q * g)) * g⁻¹ := by rw [this]
      _ = g * z * g⁻¹ * q := by group
  · rw [conj_pow, hzp]; simp

theorem mem_normalizer_omegaCenter {p : ℕ} {Q : Subgroup G} {g : G}
    (hg : g ∈ normalizer (Q : Set G)) :
    g ∈ normalizer ((omegaCenter p Q : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => conj_mem_omegaCenter hg hz, fun hz => ?_⟩
  have := conj_mem_omegaCenter (inv_mem hg) hz
  rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this

theorem conj_zpowers_ne [Finite G] {x y : G} (hx : orderOf x = p) (hy : IsPGroup p (zpowers y))
    (hyx : y * x ≠ x * y) {i j : ℕ} (hij : i < j) (hjp : j < p) :
    (zpowers x).map (MulAut.conj (y ^ i)).toMonoidHom ≠
      (zpowers x).map (MulAut.conj (y ^ j)).toMonoidHom := by
  have hp : p.Prime := Fact.out
  intro heq
  set d := j - i with hd
  have hdp : 0 < d ∧ d < p := ⟨by omega, by omega⟩
  have hyj : y ^ j * x * (y ^ j)⁻¹ ∈ (zpowers x).map (MulAut.conj (y ^ i)).toMonoidHom := by
    rw [heq]
    exact ⟨x, mem_zpowers x, rfl⟩
  obtain ⟨t, ht, hti⟩ := hyj
  have hw : y ^ d * x * (y ^ d)⁻¹ ∈ zpowers x := by
    have h1 : t = y ^ d * x * (y ^ d)⁻¹ := by
      have h2 : y ^ i * t * (y ^ i)⁻¹ = y ^ j * x * (y ^ j)⁻¹ := hti
      have h3 : y ^ j = y ^ i * y ^ d := by rw [← pow_add]; congr 1; omega
      rw [h3] at h2
      have h4 : MulAut.conj (y ^ i) t = MulAut.conj (y ^ i) (y ^ d * x * (y ^ d)⁻¹) := by
        simp only [MulAut.conj_apply]
        rw [h2]
        group
      exact (MulAut.conj (y ^ i)).injective h4
    rw [← h1]
    exact ht
  have hwp : IsPGroup p (zpowers (y ^ d)) :=
    hy.to_le (zpowers_le.mpr (pow_mem (mem_zpowers y) d))
  have hcomm : Commute (y ^ d) x := commute_of_normalizes_prime_order hwp hx hw
  obtain ⟨k, hk⟩ := hy.exists_card_eq
  rw [Nat.card_zpowers] at hk
  have hcop : Nat.Coprime d (orderOf y) := by
    rw [hk]
    exact Nat.Coprime.pow_right _
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hdp.1 hdp.2)).symm
  obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime hcop
  apply hyx
  have h5 : Commute ((y ^ d) ^ e) x := hcomm.pow_left e
  rw [he] at h5
  exact h5

theorem exists_lines_of_invariant_plane [Finite G] {D : Subgroup G} {x y : G} (hx : orderOf x = p)
    (hxD : x ∈ D) (hyD : ∀ i : ℕ, y ^ i ∈ normalizer (D : Set G)) (hy : IsPGroup p (zpowers y))
    (hyx : y * x ≠ x * y) :
    ∃ S : Finset (Subgroup G), S.card = p ∧ ∀ L ∈ S, L ≤ D ∧ Nat.card L = p ∧
      ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom := by
  classical
  refine ⟨(Finset.range p).image fun i => (zpowers x).map (MulAut.conj (y ^ i)).toMonoidHom,
    ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact conj_zpowers_ne hx hy hyx h hj hij
    · exact conj_zpowers_ne hx hy hyx h hi hij.symm
  · intro L hL
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hL
    refine ⟨?_, ?_, y ^ i, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      have htD : t ∈ D := zpowers_le.mpr hxD ht
      exact (Subgroup.mem_normalizer_iff.mp (hyD i) t).mp htD
    · rw [Subgroup.card_map_of_injective (MulAut.conj (y ^ i)).injective, Nat.card_zpowers, hx]

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
