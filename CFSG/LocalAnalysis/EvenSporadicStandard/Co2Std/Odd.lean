module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Sq
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.Co2Std

open Subgroup

structure TwoCentralSetting (G : Type) [Group G] (L : Subgroup G) (z t : G)
    (SL : Subgroup G) : Prop where
  z_ne : z ≠ 1
  z_sq : z * z = 1
  centralizer_z : centralizer ({z} : Set G) = L ⊔ zpowers z
  disjoint : Disjoint L (zpowers z)
  t_mem : t ∈ L
  t_ne : t ≠ 1
  t_sq : t * t = 1
  sq_of_invol : ∀ v ∈ L, v * v = 1 → v ≠ 1 → ∃ w ∈ L, w * w = v
  le : SL ≤ L
  pgroup : IsPGroup 2 SL
  maximal : ∀ R : Subgroup G, R ≤ L → IsPGroup 2 R → SL ≤ R → R = SL
  t_mem_SL : t ∈ SL
  t_comm : ∀ s ∈ SL, s * t = t * s
  center_eq : ∀ c ∈ SL, (∀ s ∈ SL, s * c = c * s) → c = 1 ∨ c = t

variable {G : Type} [Group G]

theorem exists_mem_normalizer_not_mem [Finite G] {P S : Subgroup G} (hP : IsPGroup 2 P)
    (hSP : S < P) : ∃ n ∈ P, n ∉ S ∧ ∀ h ∈ P, h ∈ S ↔ n * h * n⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hU : S.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    obtain ⟨x, hxP, hxS⟩ := IsConcreteLE.exists_of_lt hSP
    have : (⟨x, hxP⟩ : P) ∈ S.subgroupOf P := by rw [h]; trivial
    exact hxS this
  have hlt := Group.normalizerCondition_of_isNilpotent (S.subgroupOf P) hU
  obtain ⟨x, hx, hxU⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, fun h => hxU h, fun h hh => ?_⟩
  have := mem_normalizer_iff.1 hx ⟨h, hh⟩
  exact this

theorem isPGroup_sup_zpowers [Finite G] {A : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hA : IsPGroup 2 A) (hc : zpowers z ≤ centralizer (A : Set G)) (hd : Disjoint A (zpowers z)) :
    IsPGroup 2 (A ⊔ zpowers z : Subgroup G) ∧ A.relIndex (A ⊔ zpowers z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hA
  have hcard : Nat.card (A ⊔ zpowers z : Subgroup G) = 2 ^ (n + 1) := by
    rw [← Nat.card_congr (mulEquivProdSup hc hd).toEquiv, Nat.card_prod, hn, Nat.card_zpowers, hz,
      pow_succ]
  refine ⟨IsPGroup.of_card hcard, ?_⟩
  have h1 := Subgroup.card_mul_index (A.subgroupOf (A ⊔ zpowers z))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ zpowers z)).toEquiv, hn,
    hcard, pow_succ] at h1
  have hpos : 0 < 2 ^ n := by positivity
  exact Nat.eq_of_mul_eq_mul_left hpos h1

theorem eq_one_or_eq_of_mem_zpowers {z : G} (hz2 : z * z = 1) {b : G} (hb : b ∈ zpowers z) :
    b = 1 ∨ b = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  have hzp : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz2]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · left
    rw [← Int.emod_add_mul_ediv k 2, h0, zpow_add, zpow_mul, hzp, one_zpow]
    simp
  · right
    rw [← Int.emod_add_mul_ediv k 2, h0, zpow_add, zpow_mul, hzp, one_zpow]
    simp

theorem TwoCentralSetting.odd_index_centralizer [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G} {z t : G} {SL : Subgroup G}
    (h : TwoCentralSetting G L z t SL) :
    Odd (centralizer ({t} : Set G)).index ∧ IsConj z (t * z) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.z_sq) h.z_ne
  have hzL : zpowers z ≤ centralizer (L : Set G) :=
    le_centralizer_zpowers_of_centralizer_eq h.centralizer_z
  have hzSL : zpowers z ≤ centralizer (SL : Set G) :=
    hzL.trans (centralizer_le (fun x hx => h.le hx))
  have hdSL : Disjoint SL (zpowers z) := h.disjoint.mono_left h.le
  obtain ⟨hSp, hSrel⟩ := isPGroup_sup_zpowers hz2 h.pgroup hzSL hdSL
  set S : Subgroup G := SL ⊔ zpowers z with hSdef
  have hSLS : SL ≤ S := le_sup_left
  have hzS : z ∈ S := mem_sup_right (mem_zpowers z)
  have hzSL' : z ∉ SL := fun hz =>
    h.z_ne (mem_bot.1 (h.disjoint.le_bot ⟨h.le hz, mem_zpowers z⟩))
  have hSprod : ∀ x ∈ S, ∃ s ∈ SL, ∃ b ∈ zpowers z, x = s * b :=
    fun x hx => exists_mul_of_mem_sup_of_le_centralizer hzSL hx
  have hbcomm : ∀ b ∈ zpowers z, ∀ w ∈ SL, w * b = b * w := fun b hb w hw =>
    mem_centralizer_iff.1 (hzSL hb) w hw
  have hnc : ∀ v ∈ L, v * v = 1 → v ≠ 1 → ¬ IsConj z v := by
    intro v hv hv2 hv1
    obtain ⟨w, -, hw⟩ := h.sq_of_invol v hv hv2 hv1
    exact not_isConj_of_mem_of_sq h.z_ne h.z_sq h.centralizer_z h.disjoint hw
  have hnotSylow : 2 ∣ S.index := by
    by_contra hodd
    obtain ⟨g, hg⟩ := exists_conj_mem_complement hnonab hSp hodd hSLS hSrel hzS hzSL' hz2
    have hgL : g⁻¹ * z * g ∈ L := h.le hg
    have hg2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
      calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [h.z_sq]; group
    have hg1 : g⁻¹ * z * g ≠ 1 := by
      intro h1
      apply h.z_ne
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    exact hnc _ hgL hg2 hg1 (isConj_iff.2 ⟨g⁻¹, by group⟩)
  obtain ⟨P, hSP⟩ := hSp.exists_le_sylow
  have hSltP : S < (P : Subgroup G) := by
    refine lt_of_le_of_ne hSP fun heq => ?_
    have := Sylow.not_dvd_index P
    rw [← heq] at this
    exact this hnotSylow
  obtain ⟨n, hnP, hnS, hn⟩ := exists_mem_normalizer_not_mem P.isPGroup' hSltP
  have hPcent : ∀ y ∈ (P : Subgroup G), y * z = z * y → y ∈ S := by
    intro y hyP hyz
    have hyC : y ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hyz
    rw [h.centralizer_z] at hyC
    obtain ⟨l, hl, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer hzL hyC
    have hbS : b ∈ S := mem_sup_right hb
    have hlP : l ∈ (P : Subgroup G) := by
      have := mul_mem hyP (inv_mem (hSP hbS))
      simpa using this
    have hR : (P : Subgroup G) ⊓ L = SL := by
      refine h.maximal _ inf_le_right ?_ (le_inf (hSLS.trans hSP) h.le)
      exact P.isPGroup'.to_le inf_le_left
    have hlSL : l ∈ SL := by rw [← hR]; exact ⟨hlP, hl⟩
    exact mul_mem_sup hlSL hb
  have hzP : z ∈ (P : Subgroup G) := hSP hzS
  have hzcomm : ∀ x ∈ S, x * z = z * x := by
    intro x hx
    obtain ⟨s, hs, b, hb, rfl⟩ := hSprod x hx
    have hsz : s * z = z * s := mem_centralizer_singleton_iff.1
      (by rw [h.centralizer_z]; exact mem_sup_left (h.le hs))
    have hbz : b * z = z * b := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_left (Commute.refl z) k).eq
    calc s * b * z = s * (b * z) := by group
      _ = s * (z * b) := by rw [hbz]
      _ = (s * z) * b := by group
      _ = z * s * b := by rw [hsz]
      _ = z * (s * b) := by group
  have hznS : n * z * n⁻¹ ∈ S := (hn z hzP).1 hzS
  have hZc : ∀ u ∈ S, u * (n * z * n⁻¹) = (n * z * n⁻¹) * u := by
    intro u hu
    have hu' : n⁻¹ * u * n ∈ S := by
      have hmem : n⁻¹ * u * n ∈ (P : Subgroup G) :=
        mul_mem (mul_mem (inv_mem hnP) (hSP hu)) hnP
      refine (hn _ hmem).2 ?_
      have : n * (n⁻¹ * u * n) * n⁻¹ = u := by group
      rw [this]; exact hu
    have hc := hzcomm _ hu'
    calc u * (n * z * n⁻¹) = n * ((n⁻¹ * u * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * u * n)) * n⁻¹ := by rw [hc]
      _ = (n * z * n⁻¹) * u := by group
  have hcentral : ∀ c ∈ S, c ≠ 1 → c * c = 1 → (∀ u ∈ S, u * c = c * u) →
      c = z ∨ c = t ∨ c = t * z := by
    intro c hc hc1 hc2 hcc
    obtain ⟨s, hs, b, hb, rfl⟩ := hSprod c hc
    have hsc : ∀ w ∈ SL, w * s = s * w := by
      intro w hw
      have h1 := hcc w (hSLS hw)
      have h2 : w * s * b = s * w * b := by
        calc w * s * b = w * (s * b) := by group
          _ = s * b * w := h1
          _ = s * (b * w) := by group
          _ = s * (w * b) := by rw [hbcomm b hb w hw]
          _ = s * w * b := by group
      exact mul_right_cancel h2
    rcases h.center_eq s hs hsc with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers h.z_sq hb with rfl | rfl
    · exact absurd (by simp) hc1
    · left; simp
    · right; left; simp
    · right; right; rfl
  have hz'1 : n * z * n⁻¹ ≠ 1 := by
    intro h1
    apply h.z_ne
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  have hz'2 : (n * z * n⁻¹) * (n * z * n⁻¹) = 1 := by
    calc (n * z * n⁻¹) * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  have hz'eq : n * z * n⁻¹ = t * z := by
    rcases hcentral _ hznS hz'1 hz'2 hZc with h1 | h1 | h1
    · exfalso
      apply hnS
      exact hPcent n hnP (by
        have : n * z = z * n := by
          calc n * z = (n * z * n⁻¹) * n := by group
            _ = z * n := by rw [h1]
        exact this)
    · exfalso
      refine hnc t h.t_mem h.t_sq h.t_ne ?_
      exact isConj_iff.2 ⟨n, h1⟩
    · exact h1
  have hPnt : Nontrivial (P : Subgroup G) :=
    ⟨⟨⟨z, hzP⟩, 1, fun h1 => h.z_ne (congrArg Subtype.val h1)⟩⟩
  have hZnt : Nontrivial (center (P : Subgroup G)) := P.isPGroup'.center_nontrivial
  have hZp : IsPGroup 2 (center (P : Subgroup G)) := P.isPGroup'.to_subgroup _
  have h2dvd : 2 ∣ Nat.card (center (P : Subgroup G)) := by
    rcases hZp.card_eq_or_dvd with h1 | h1
    · exfalso
      have := Finite.one_lt_card_iff_nontrivial.2 hZnt
      omega
    · exact h1
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center (P : Subgroup G)) 2 h2dvd
  set c' : G := ((c : P) : G) with hc'
  have hc'P : c' ∈ (P : Subgroup G) := (c : P).2
  have hc'cent : ∀ p ∈ (P : Subgroup G), p * c' = c' * p := by
    intro p hp
    have := (Subgroup.mem_center_iff.1 c.2) ⟨p, hp⟩
    exact congrArg Subtype.val this
  have hc'ord : orderOf c' = 2 := by
    rw [hc', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  have hc'2 : c' * c' = 1 := by rw [← pow_two, ← hc'ord, pow_orderOf_eq_one]
  have hc'1 : c' ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hc'ord; exact absurd hc'ord (by decide)
  have hc'S : c' ∈ S := hPcent c' hc'P (hc'cent z hzP).symm
  have ht_cent : t = c' := by
    rcases hcentral c' hc'S hc'1 hc'2 (fun u hu => hc'cent u (hSP hu)) with h1 | h1 | h1
    · exfalso
      have h3 : n * z * n⁻¹ = z := by
        calc n * z * n⁻¹ = n * c' * n⁻¹ := by rw [h1]
          _ = c' := by rw [hc'cent n hnP]; group
          _ = z := h1
      rw [h3] at hz'eq
      have h5 : t * z = 1 * z := by rw [one_mul]; exact hz'eq.symm
      exact h.t_ne (mul_right_cancel h5)
    · exact h1.symm
    · exfalso
      have h3 : n * (t * z) * n⁻¹ = t * z := by
        calc n * (t * z) * n⁻¹ = n * c' * n⁻¹ := by rw [h1]
          _ = c' := by rw [hc'cent n hnP]; group
          _ = t * z := h1
      have h4 : n * (t * z) * n⁻¹ = (n * t * n⁻¹) * (n * z * n⁻¹) := by group
      rw [h4, hz'eq] at h3
      have : n * t * n⁻¹ = 1 := mul_right_cancel (by rw [h3, one_mul])
      apply h.t_ne
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [this]; group
  refine ⟨?_, isConj_iff.2 ⟨n, hz'eq⟩⟩
  have hle : (P : Subgroup G) ≤ centralizer ({t} : Set G) := by
    intro p hp
    rw [mem_centralizer_singleton_iff]
    rw [ht_cent]
    exact hc'cent p hp
  have hdvd := Subgroup.index_dvd_of_le hle
  have hnd : ¬ 2 ∣ (centralizer ({t} : Set G)).index := fun h2 =>
    Sylow.not_dvd_index P (h2.trans hdvd)
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hnd)

end CFSG.EvenSporadicStandard.Co2Std


