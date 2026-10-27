module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25Datum
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25Extend
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

open Subgroup

variable {G : Type*} [Group G] [Finite G] {x : G}

omit [Finite G] in
theorem isConj_conj {z u : G} (g : G) (hu : IsConj z u) : IsConj z (g * u * g⁻¹) :=
  hu.trans (isConj_iff.mpr ⟨g, rfl⟩)

theorem fixLeTwo_dsub (hx : orderOf x = 4) (hwc : WeaklyClosedInNormalizer (zpowers x))
    {e : ℕ} {w t : G} (hd : Datum {u | IsConj (x ^ 2) u} e w t) {s : G}
    (hs : IsConj (x ^ 2) s) (hsD : s ∉ dsub w t) : FixLeTwo s (dsub w t) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 : s * s = 1 := sq_eq_one_of_isConj hx hs
  set D : Subgroup G := dsub w t with hDdef
  set P : Subgroup G := D ⊓ centralizer ({s} : Set G) with hPdef
  have hPp : IsPGroup 2 P := hd.isPGroup.to_le inf_le_left
  obtain ⟨y, hxy, hy2, hPy⟩ := exists_datum hx hwc hs hPp inf_le_right
  have hyo : orderOf y = 4 := by rw [orderOf_eq_of_isConj hxy, hx]
  have hcomm_trivial : ∀ p ∈ P, p * y * p⁻¹ = y → p = 1 := by
    intro p hp hpy
    by_contra hp1
    have hcomm : p * y = y * p := by
      calc p * y = (p * y * p⁻¹) * p := by group
        _ = y * p := by rw [hpy]
    have hpord : ∃ k : ℕ, orderOf (⟨p, hp⟩ : P) = 2 ^ k := (IsPGroup.iff_orderOf.mp hPp) ⟨p, hp⟩
    obtain ⟨k, hk⟩ := hpord
    have hk1 : k ≠ 0 := by
      rintro rfl
      apply hp1
      have : orderOf (⟨p, hp⟩ : P) = 1 := by simpa using hk
      have := orderOf_eq_one_iff.mp this
      exact congrArg Subtype.val this
    have hdvd : 2 ∣ Nat.card (zpowers p) := by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_mk p hp, hk]
      exact dvd_pow_self 2 hk1
    obtain ⟨q', hq'⟩ := exists_prime_orderOf_dvd_card' (G := zpowers p) 2 hdvd
    set q : G := (q' : G) with hq
    have hqp : q ∈ zpowers p := q'.2
    have hqP : q ∈ P := zpowers_le.mpr hp hqp
    have hq2 : q * q = 1 := by
      have : q ^ 2 = 1 := by
        have h := pow_orderOf_eq_one q'
        rw [hq'] at h
        exact congrArg Subtype.val h
      rwa [sq] at this
    have hq1 : q ≠ 1 := by
      intro h
      have : q' = 1 := Subtype.ext h
      rw [this, orderOf_one] at hq'
      omega
    have hq𝒞 : IsConj (x ^ 2) q := hd.inv_mem q hqP.1 hq2 hq1
    have hqy : q * y = y * q := by
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hqp
      rw [← hj]
      exact ((Commute.zpow_left (show Commute p y from hcomm) j)).eq
    have := eq_sq_of_commute_conj hx hwc hxy hq𝒞 hqy
    rw [hy2] at this
    exact hsD (this ▸ hqP.1)
  have hinj : ∀ p ∈ P, ∀ q ∈ P, p * y * p⁻¹ = q * y * q⁻¹ → p = q := by
    intro p hp q hq h
    have h1 : (q⁻¹ * p) * y * (q⁻¹ * p)⁻¹ = y := by
      calc (q⁻¹ * p) * y * (q⁻¹ * p)⁻¹ = q⁻¹ * (p * y * p⁻¹) * q := by group
        _ = q⁻¹ * (q * y * q⁻¹) * q := by rw [h]
        _ = y := by group
    have := hcomm_trivial (q⁻¹ * p) (mul_mem (inv_mem hq) hp) h1
    exact (inv_mul_eq_one.mp this).symm
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hPof : ∀ d ∈ D, s * d * s = d → d ∈ P := by
    intro d hdD hfix
    refine Subgroup.mem_inf.mpr ⟨hdD, ?_⟩
    rw [mem_centralizer_singleton_iff]
    calc d * s = (s * d * s) * s := by rw [hfix]
      _ = s * d := by rw [mul_assoc, hs2, mul_one]
  unfold FixLeTwo
  intro a ha b hb c hc ha' hb' hc'
  have hPa := hPof a ha ha'
  have hPb := hPof b hb hb'
  have hPc := hPof c hc hc'
  rcases conj_eq_or_eq_inv_of_mem_normalizer hyo (hPy hPa) with h1 | h1 <;>
  rcases conj_eq_or_eq_inv_of_mem_normalizer hyo (hPy hPb) with h2 | h2 <;>
  rcases conj_eq_or_eq_inv_of_mem_normalizer hyo (hPy hPc) with h3 | h3
  · exact Or.inl (hinj a hPa b hPb (h1.trans h2.symm))
  · exact Or.inl (hinj a hPa b hPb (h1.trans h2.symm))
  · exact Or.inr (Or.inl (hinj a hPa c hPc (h1.trans h3.symm)))
  · exact Or.inr (Or.inr (hinj b hPb c hPc (h2.trans h3.symm)))
  · exact Or.inr (Or.inr (hinj b hPb c hPc (h2.trans h3.symm)))
  · exact Or.inr (Or.inl (hinj a hPa c hPc (h1.trans h3.symm)))
  · exact Or.inl (hinj a hPa b hPb (h1.trans h2.symm))
  · exact Or.inl (hinj a hPa b hPb (h1.trans h2.symm))

omit [Finite G] in
theorem zpow_eq_one_or_self {z : G} (hz2 : z * z = 1) (i : ℤ) : z ^ i = 1 ∨ z ^ i = z := by
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem datum_zero (hx : orderOf x = 4) (hwc : WeaklyClosedInNormalizer (zpowers x)) {t₀ : G}
    (ht₀ : IsConj (x ^ 2) t₀) (hne : x ^ 2 ≠ t₀) (hcomm : x ^ 2 * t₀ = t₀ * x ^ 2) :
    Datum {u | IsConj (x ^ 2) u} 0 (x ^ 2) t₀ := by
  have hz : IsConj (x ^ 2) (x ^ 2) := IsConj.refl _
  have hz2 := sq_eq_one_of_isConj hx hz
  have hz1 := ne_one_of_isConj hx hz
  have ht2 := sq_eq_one_of_isConj hx ht₀
  have ht1 := ne_one_of_isConj hx ht₀
  have hb := bareDatum_zero hz2 hz1 ht2 ht1 hne hcomm
  refine ⟨hb, ?_⟩
  intro g hg hg2 hg1
  rcases hb.eq_center_or_refl hg hg2 hg1 with rfl | ⟨i, rfl⟩
  · simpa using hz
  · rcases zpow_eq_one_or_self hz2 i with h | h
    · rw [h, one_mul]; exact ht₀
    · rw [h]; exact mul_isConj_of_commute hx hwc hz ht₀ hne hcomm

theorem exists_datum_zero {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 4)
    (hwc : WeaklyClosedInNormalizer (zpowers x)) (hnz : ¬ InZStar (x ^ 2)) :
    ∃ w t : G, Datum {u | IsConj (x ^ 2) u} 0 w t := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hz : IsConj (x ^ 2) (x ^ 2) := IsConj.refl _
  have hz2 := sq_eq_one_of_isConj hx hz
  have hz1 := ne_one_of_isConj hx hz
  have hex : ∃ g : G, (g * x ^ 2 * g⁻¹) * x ^ 2 = x ^ 2 * (g * x ^ 2 * g⁻¹) ∧
      g * x ^ 2 * g⁻¹ ≠ x ^ 2 := by
    by_contra hcon
    refine hnz (CFSG.ZStar.glauberman_zStar G (x ^ 2) hz1 hz2 fun g hcomm => ?_)
    by_contra hne
    exact hcon ⟨g, hcomm, hne⟩
  obtain ⟨g, hcomm, hne⟩ := hex
  exact ⟨x ^ 2, g * x ^ 2 * g⁻¹, datum_zero hx hwc (isConj_conj g hz) hne.symm hcomm.symm⟩

theorem exists_sic_datum (hx : orderOf x = 4) (hwc : WeaklyClosedInNormalizer (zpowers x))
    (h0 : ∃ w t : G, Datum {u | IsConj (x ^ 2) u} 0 w t) :
    ∃ (e : ℕ) (w t : G), Datum {u | IsConj (x ^ 2) u} e w t ∧
      ∀ s ∈ normalizer ((dsub w t : Subgroup G) : Set G), IsConj (x ^ 2) s → s ∈ dsub w t := by
  classical
  let E : Set ℕ := {e | ∃ w t : G, Datum {u | IsConj (x ^ 2) u} e w t}
  have hne : E.Nonempty := by
    obtain ⟨w, t, h⟩ := h0
    exact ⟨0, w, t, h⟩
  have hbdd : BddAbove E := by
    refine ⟨Nat.card G, ?_⟩
    rintro e ⟨w, t, hd⟩
    have h1 : 2 ^ (e + 1) ≤ Nat.card G := by
      rw [← hd.order_w]
      exact Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard w)
    have h2 : e + 1 < 2 ^ (e + 1) := Nat.lt_two_pow_self
    omega
  obtain ⟨w, t, hd⟩ := Nat.sSup_mem hne hbdd
  refine ⟨sSup E, w, t, hd, ?_⟩
  intro s hsN hs
  by_contra hsD
  have hs2 : s * s = 1 := sq_eq_one_of_isConj hx hs
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hsn : ∀ d ∈ dsub w t, s * d * s ∈ dsub w t := by
    intro d hdD
    have := (mem_normalizer_iff.mp hsN d).mp hdD
    rwa [hsi] at this
  have hfix := fixLeTwo_dsub hx hwc hd hs hsD
  obtain ⟨w', t', hd'⟩ := exists_datum_succ (fun g u hu => isConj_conj g hu) hd hs hs2 hsn hfix
  have : sSup E + 1 ≤ sSup E := le_csSup hbdd ⟨w', t', hd'⟩
  omega

theorem normalClosure_dsub {G : Type*} [Group G] {z : G} {e : ℕ} {w t : G}
    (hd : Datum {u | IsConj z u} e w t) :
    normalClosure ((dsub w t : Subgroup G) : Set G) = normalClosure {z} := by
  have htD : t ∈ dsub w t := mem_sup_right (mem_zpowers t)
  have hwD : w ∈ dsub w t := mem_sup_left (mem_zpowers w)
  have ht𝒞 : IsConj z t := hd.inv_mem t htD hd.t_sq (fun h => hd.t_not_mem (h ▸ one_mem _))
  have hwt𝒞 : IsConj z (w * t) := by
    have hmem : w * t ∈ dsub w t := mul_mem hwD htD
    have := hd.refl_sq 1
    simp only [zpow_one] at this
    exact hd.inv_mem _ hmem this (by simpa using hd.refl_ne_one 1)
  have hconj : ∀ u, IsConj z u → u ∈ normalClosure {z} := by
    intro u hu
    obtain ⟨c, rfl⟩ := isConj_iff.mp hu
    exact (normalClosure_normal (s := {z})).conj_mem z (subset_normalClosure rfl) c
  apply le_antisymm
  · apply normalClosure_le_normal
    intro u hu
    have hu' : u ∈ dsub w t := hu
    have : dsub w t ≤ normalClosure {z} := by
      apply sup_le
      · rw [zpowers_le]
        have h1 := hconj _ hwt𝒞
        have h2 := hconj _ ht𝒞
        have : w = (w * t) * t⁻¹ := by group
        rw [this]
        exact mul_mem h1 (inv_mem h2)
      · rw [zpowers_le]
        exact hconj _ ht𝒞
    exact this hu'
  · apply normalClosure_le_normal
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    rw [hu]
    obtain ⟨c, hc⟩ := isConj_iff.mp ht𝒞
    have : z = c⁻¹ * t * c := by rw [← hc]; group
    rw [this]
    have h := (normalClosure_normal (s := ((dsub w t : Subgroup G) : Set G))).conj_mem t
      (subset_normalClosure htD) c⁻¹
    rwa [inv_inv] at h

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof
