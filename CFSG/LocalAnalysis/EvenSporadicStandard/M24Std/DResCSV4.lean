module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResE81
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open

variable {Y : Type} [Group Y]

theorem exists_dihedral_data [Finite Y] {O : Subgroup Y} [O.Normal] (hO : Odd (Nat.card O))
    {t g : Y} (ht : t * t = 1) (hg : g * g = 1)
    (hπ : (QuotientGroup.mk' O (t * g)) ^ 2 ≠ 1) (hπ4 : (QuotientGroup.mk' O (t * g)) ^ 4 = 1) :
    ∃ x h : Y, x * x = 1 ∧ x ≠ 1 ∧ x * t = t * x ∧ h * x = x * h ∧ h⁻¹ * t * h = t * x ∧
      QuotientGroup.mk' O x = QuotientGroup.mk' O ((t * g) ^ 2) ∧ x ∈ zpowers ((t * g) ^ 2) := by
  set r : Y := t * g with hr
  have htr : t * r * t⁻¹ = r⁻¹ := by
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
    rw [hr, ht', mul_inv_rev, hg', ht']
    calc t * (t * g) * t = (t * t) * g * t := by group
      _ = g * t := by rw [ht, one_mul]
  have htrk : ∀ k : ℕ, t * r ^ k * t⁻¹ = (r ^ k)⁻¹ := by
    intro k
    rw [← conj_pow, htr, inv_pow]
  obtain ⟨j, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf (r ^ 2))
    (orderOf_pos_iff.2 (isOfFinOrder_of_finite _)).ne'
  set x : Y := r ^ (2 * m) with hx
  set h : Y := r ^ m with hh
  set π := QuotientGroup.mk' O with hπdef
  have hv2 : (π r ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hπ4
  obtain ⟨k, hk⟩ := hm
  have hπx : π x = π r ^ 2 := by
    have : π x = (π r ^ 2) ^ m := by rw [hx, map_pow, pow_mul]
    rw [this, hk, pow_succ, pow_mul, hv2, one_pow, one_mul]
  have hx2 : x * x = 1 := by
    have hxO : x ^ 2 ∈ O := by
      have : π (x ^ 2) = 1 := by rw [map_pow, hπx, hv2]
      exact (QuotientGroup.eq_one_iff _).1 this
    have hodd : Odd (orderOf (x ^ 2)) :=
      Odd.of_dvd_nat hO (Subgroup.orderOf_dvd_natCard O hxO)
    have h2 : ∃ k : ℕ, (x ^ 2) ^ (2 ^ k) = 1 := by
      refine ⟨j, ?_⟩
      have h1 : (r ^ 2) ^ (2 ^ j * m) = 1 := by
        rw [← hn]
        exact pow_orderOf_eq_one _
      calc (x ^ 2) ^ (2 ^ j) = ((r ^ 2) ^ (2 ^ j * m)) ^ 2 := by
            rw [hx]
            simp only [← pow_mul]
            congr 1
            ring
        _ = 1 := by rw [h1, one_pow]
    have := E81Data.eq_one_of_pow_two_of_odd h2 hodd
    rwa [sq] at this
  have hx1 : x ≠ 1 := fun h1 => hπ (by rw [← hπx, h1, map_one])
  have htx : x * t = t * x := by
    have h1 : t * x * t⁻¹ = x⁻¹ := by rw [hx]; exact htrk _
    have h2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [h2] at h1
    calc x * t = (t * x * t⁻¹) * t := by rw [h1]
      _ = t * x := by group
  have hhx : h * x = x * h := by
    rw [hh, hx, ← pow_add, ← pow_add, add_comm]
  have hth : h⁻¹ * t * h = t * x := by
    have h1 : t * h = h⁻¹ * t := by
      have := htrk m
      calc t * h = (t * r ^ m * t⁻¹) * t := by rw [hh]; group
        _ = (r ^ m)⁻¹ * t := by rw [this]
    have h2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    calc h⁻¹ * t * h = h⁻¹ * (t * h) := by group
      _ = h⁻¹ * (h⁻¹ * t) := by rw [h1]
      _ = (h * h)⁻¹ * t := by group
      _ = x⁻¹ * t := by rw [hh, hx, ← pow_add, ← two_mul]
      _ = x * t := by rw [h2]
      _ = t * x := htx
  exact ⟨x, h, hx2, hx1, htx, hhx, hth, hπx,
    mem_zpowers_iff.2 ⟨m, by rw [zpow_natCast, hx, pow_mul]⟩⟩

theorem mem_zpowers_involution {t a : Y} (ht : t * t = 1) (ht1 : t ≠ 1) (ha : a ∈ zpowers t) :
    a = 1 ∨ a = t := by
  have ho : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht) ht1
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  rw [← zpow_mod_orderOf, ho, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exact Or.inl (by rw [h, zpow_zero])
  · exact Or.inr (by rw [h, zpow_one])

theorem centralizes_odd_of_v4 [Finite Y] {O : Subgroup Y} [O.Normal] (hO : Odd (Nat.card O))
    {t x h : Y} (ht : t * t = 1) (hx : x * x = 1) (htx : x * t = t * x) (hhx : h * x = x * h)
    (hth : h⁻¹ * t * h = t * x) (hx1 : x ≠ 1) (ht1 : t ≠ 1) (htx' : t ≠ x)
    (hCO : ∀ o ∈ O, o * t = t * o → x * o = o * x) : ∀ o ∈ O, x * o = o * x := by
  have hc : ∀ a ∈ zpowers t, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    exact ((Commute.zpow_zpow (show Commute t x from htx.symm) m n)).eq
  set A : Subgroup Y := commProd (zpowers t) (zpowers x) hc with hA
  have hint : ∀ a ∈ zpowers t, a ∈ zpowers x → a = 1 := by
    intro a hat hax
    rcases mem_zpowers_involution ht ht1 hat with h1 | h1
    · exact h1
    · rcases mem_zpowers_involution hx hx1 hax with h2 | h2
      · rw [h1] at h2; exact absurd h2 ht1
      · exact absurd (h1.symm.trans h2) htx'
  have hord : ∀ y : Y, y * y = 1 → y ≠ 1 → orderOf y = 2 := fun y hy hy1 =>
    orderOf_eq_prime (by rw [sq]; exact hy) hy1
  have hcard : Nat.card A = 2 ^ 2 := by
    rw [hA, card_commProd hc hint, Nat.card_zpowers, Nat.card_zpowers, hord t ht ht1,
      hord x hx hx1]
    norm_num
  have hpower : ∀ member : A, member ^ 2 = 1 := by
    rintro ⟨v, hv⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_commProd.1 hv
    have h1 : a * a = 1 := by
      rcases mem_zpowers_involution ht ht1 ha with h | h
      · rw [h, one_mul]
      · rw [h, ht]
    have h2 : b * b = 1 := by
      rcases mem_zpowers_involution hx hx1 hb with h | h
      · rw [h, one_mul]
      · rw [h, hx]
    apply Subtype.ext
    show (a * b) ^ 2 = 1
    rw [sq, show a * b * (a * b) = a * (b * a) * b by group, ← hc a ha b hb,
      show a * (a * b) * b = (a * a) * (b * b) by group, h1, h2, one_mul]
  have hnorm : A ≤ normalizer (O : Set Y) := fun a _ =>
    mem_normalizer_iff.2 fun o => ⟨fun ho => Normal.conj_mem inferInstance o ho a, fun ho => by
      have := Normal.conj_mem inferInstance _ ho a⁻¹
      rwa [show a⁻¹ * (a * o * a⁻¹) * a⁻¹⁻¹ = o by group] at this⟩
  have hodd2 : ¬ 2 ∣ Nat.card O := fun hd => (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 hd)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two A O hpower hcard hodd2 hnorm
  have hle : O ≤ centralizer ({x} : Set Y) := by
    calc O = ⨆ (member : A) (_ : member ≠ 1), O ⊓ centralizer ({(member : Y)} : Set Y) := hgen
      _ ≤ centralizer ({x} : Set Y) := by
        refine iSup_le fun v => iSup_le fun hv => ?_
        obtain ⟨v, hvA⟩ := v
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_commProd.1 hvA
        intro o ho
        rw [mem_centralizer_singleton_iff]
        have hoO : o ∈ O := ho.1
        have hoC : o * (a * b) = (a * b) * o := mem_centralizer_singleton_iff.1 ho.2
        rcases mem_zpowers_involution ht ht1 ha with h1 | h1 <;>
          rcases mem_zpowers_involution hx hx1 hb with h2 | h2 <;> rw [h1, h2] at hoC
        · exact absurd (Subtype.ext (by show a * b = 1; rw [h1, h2]; simp)) hv
        · simpa using hoC
        · exact (hCO o hoO (by simpa using hoC)).symm
        · have hoO' : h * o * h⁻¹ ∈ O := Normal.conj_mem inferInstance o hoO h
          have h1 : (h * o * h⁻¹) * t = t * (h * o * h⁻¹) := by
            calc (h * o * h⁻¹) * t = h * (o * (h⁻¹ * t * h)) * h⁻¹ := by group
              _ = h * (o * (t * x)) * h⁻¹ := by rw [hth]
              _ = h * ((t * x) * o) * h⁻¹ := by rw [hoC]
              _ = h * ((h⁻¹ * t * h) * o) * h⁻¹ := by rw [hth]
              _ = t * (h * o * h⁻¹) := by group
          have h2 := hCO _ hoO' h1
          have hx' : h⁻¹ * x * h = x := by
            calc h⁻¹ * x * h = h⁻¹ * (x * h) := by group
              _ = h⁻¹ * (h * x) := by rw [hhx]
              _ = x := by group
          calc o * x = o * (h⁻¹ * x * h) := by rw [hx']
            _ = h⁻¹ * ((h * o * h⁻¹) * x) * h := by group
            _ = h⁻¹ * (x * (h * o * h⁻¹)) * h := by rw [h2]
            _ = (h⁻¹ * x * h) * o := by group
            _ = x * o := by rw [hx']
  intro o ho
  exact (mem_centralizer_singleton_iff.1 (hle ho)).symm

end CFSG.EvenSporadicStandard.M24Std.DRes
