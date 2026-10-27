module

public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.SeitzReduction.RankOne.Endings

open Subgroup

section General

variable {G : Type*} [Group G]

theorem exists_mul_eq_of_mem_sup {W T : Subgroup G} (hTW : T ≤ normalizer (W : Set G)) {x : G}
    (hx : x ∈ W ⊔ T) : ∃ w ∈ W, ∃ τ ∈ T, w * τ = x := by
  have hx' : x ∈ ((W ⊔ T : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left W T hTW] at hx'
  obtain ⟨w, hw, τ, hτ, rfl⟩ := hx'
  exact ⟨w, hw, τ, hτ, rfl⟩

theorem eq_one_or_eq_of_mem_zpowers {t z : G} (htt : t * t = 1) (hz : z ∈ zpowers t) :
    1 = z ∨ t = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact htt
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, ht2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

theorem exists_eq_or_eq_mul_of_mem_sup_zpowers {U : Subgroup G} {t v : G} (htt : t * t = 1)
    (htU : zpowers t ≤ normalizer (U : Set G)) (hv : v ∈ U ⊔ zpowers t) :
    ∃ u ∈ U, u = v ∨ u * t = v := by
  obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup htU hv
  rcases eq_one_or_eq_of_mem_zpowers htt hz with rfl | rfl
  · exact ⟨u, hu, Or.inl (mul_one u).symm⟩
  · exact ⟨u, hu, Or.inr rfl⟩

theorem exists_pow_mul_pow_eq {W : Subgroup G} {X : G} (hX : X ∈ normalizer (W : Set G))
    {w : G} (hw : w ∈ W) (j : ℕ) : ∀ m : ℕ, ∃ w' ∈ W, (w * X ^ j) ^ m = w' * X ^ (j * m)
  | 0 => ⟨1, one_mem W, by simp⟩
  | m + 1 => by
    obtain ⟨w', hw', h⟩ := exists_pow_mul_pow_eq hX hw j m
    refine ⟨w' * (X ^ (j * m) * w * (X ^ (j * m))⁻¹), mul_mem hw' ?_, ?_⟩
    · exact (mem_normalizer_iff.mp (pow_mem hX _) w).mp hw
    · rw [pow_succ, h, show j * (m + 1) = j * m + j by ring, pow_add]
      group

theorem orderOf_le_of_ne_one [Finite G] {t y : G} (htt : t * t = 1) (hy : y ≠ 1) :
    orderOf t ≤ orderOf y := by
  have h1 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact htt)
  have h2 : orderOf t ≤ 2 := Nat.le_of_dvd (by norm_num) h1
  have h3 : orderOf y ≠ 1 := fun h => hy (orderOf_eq_one_iff.mp h)
  have h4 : 0 < orderOf y := orderOf_pos y
  omega

theorem not_exists_normal_index_two [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  rintro ⟨N, hN, hidx⟩
  rcases hN.eq_bot_or_eq_top with rfl | rfl
  · rw [index_bot] at hidx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card hidx
    obtain ⟨a, b, hab⟩ := hnonab
    have hc : IsMulCommutative G := inferInstance
    exact hab (hc.is_comm.comm a b)
  · rw [index_top] at hidx
    exact absurd hidx (by norm_num)

theorem relIndex_sup_zpowers_eq_two {W : Subgroup G} {t : G} (htW : t ∉ W)
    (htN : t ∈ normalizer (W : Set G)) (htt : t * t = 1) :
    W.relIndex (W ⊔ zpowers t) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨t, mem_sup_right (mem_zpowers t), fun b hb => ?_⟩
  obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup (zpowers_le.mpr htN) hb
  rcases eq_one_or_eq_of_mem_zpowers htt hz with rfl | rfl
  · rw [mul_one]
    exact Or.inr ⟨hw, fun h => htW (by simpa using mul_mem (inv_mem hw) h)⟩
  · refine Or.inl ⟨?_, fun h => htW (by simpa using mul_mem (inv_mem hw) h)⟩
    rw [mul_assoc, htt, mul_one]
    exact hw

end General

section Transfer

variable {G : Type*} [Group G] [Finite G]

theorem exists_normal_index_two_of_ending {W T U : Subgroup G} {t : G}
    (hSp : IsPGroup 2 (W ⊔ T : Subgroup G)) (hSidx : ¬ 2 ∣ (W ⊔ T).index)
    (hTW : T ≤ normalizer (W : Set G)) (hWT : W ⊓ T = U) (hU2 : ∀ u ∈ U, u * u = 1)
    (htT : t ∈ T) (htW : t ∉ W) (htt : t * t = 1) (hTt : T ≤ centralizer ({t} : Set G))
    [((U ⊔ zpowers t).subgroupOf T).Normal]
    (hcyc : IsCyclic (T ⧸ (U ⊔ zpowers t).subgroupOf T))
    (h1 : ∀ g : G, g⁻¹ * t * g ∉ W)
    (h2 : ∀ u ∈ U, ∃ g : G, g⁻¹ * t * g = u * t)
    (h3 : ∀ y ∈ W ⊔ T, y ∉ W ⊔ zpowers t → y * y = 1 → ∀ g : G, g⁻¹ * t * g ≠ y) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUW : U ≤ W := hWT ▸ inf_le_left
  have hUT : U ≤ T := hWT ▸ inf_le_right
  have hTS : T ≤ W ⊔ T := le_sup_right
  have hWS : W ≤ W ⊔ T := le_sup_left
  have htS : t ∈ W ⊔ T := hTS htT
  have hTp : IsPGroup 2 T := hSp.to_le hTS
  have hTU : T ≤ normalizer (U : Set G) := by
    rw [← hWT]
    exact (le_inf hTW le_normalizer).trans inf_normalizer_le_normalizer_inf
  have htU : zpowers t ≤ normalizer (U : Set G) := zpowers_le.mpr (hTU htT)
  have htc : ∀ τ ∈ T, τ * t = t * τ := fun τ hτ => mem_centralizer_singleton_iff.mp (hTt hτ)
  have hconjU : ∀ τ ∈ T, ∀ u ∈ U, τ * u * τ⁻¹ ∈ U := fun τ hτ u hu =>
    (mem_normalizer_iff.mp (hTU hτ) u).mp hu
  obtain ⟨g₀, hg₀⟩ := hcyc.exists_generator
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g₀
  set X : G := (x : G) with hXdef
  have hXT : X ∈ T := x.2
  have hmkV : ∀ τ : T, (QuotientGroup.mk τ : T ⧸ (U ⊔ zpowers t).subgroupOf T) = 1 ↔
      (τ : G) ∈ U ⊔ zpowers t := fun τ => by
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hdec : ∀ τ ∈ T, ∃ k : ℕ, ∃ v ∈ U ⊔ zpowers t, τ = X ^ k * v := by
    intro τ hτ
    have hmem := hg₀ (QuotientGroup.mk ⟨τ, hτ⟩)
    rw [← mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hk' : (QuotientGroup.mk x : T ⧸ (U ⊔ zpowers t).subgroupOf T) ^ k =
        QuotientGroup.mk ⟨τ, hτ⟩ := hk
    refine ⟨k, (X ^ k)⁻¹ * τ, ?_, by group⟩
    have h1' : (QuotientGroup.mk ((x ^ k)⁻¹ * ⟨τ, hτ⟩) :
        T ⧸ (U ⊔ zpowers t).subgroupOf T) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hk', inv_mul_cancel]
    simpa [hXdef] using (hmkV _).mp h1'
  set d := orderOf (QuotientGroup.mk x : T ⧸ (U ⊔ zpowers t).subgroupOf T) with hd
  have hpowV : ∀ m : ℕ, X ^ m ∈ U ⊔ zpowers t ↔ d ∣ m := by
    intro m
    rw [hd, orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, hmkV]
    simp [hXdef]
  by_cases hTV : T ≤ U ⊔ zpowers t
  ·
    have hSeq : W ⊔ T = W ⊔ zpowers t := le_antisymm
      (sup_le le_sup_left (hTV.trans (sup_le (hUW.trans le_sup_left) le_sup_right)))
      (sup_le le_sup_left ((zpowers_le.mpr htT).trans le_sup_right))
    have hrel : W.relIndex (W ⊔ T) = 2 := by
      rw [hSeq]
      exact relIndex_sup_zpowers_eq_two htW (hTW htT) htt
    exact CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hSp hSidx hWS hrel htS htW
      (fun y _ hy => orderOf_le_of_ne_one htt fun h => hy (by rw [h]; exact one_mem _)) h1
  have hd1 : d ≠ 1 := by
    intro h1'
    apply hTV
    intro τ hτ
    obtain ⟨k, v, hv, rfl⟩ := hdec τ hτ
    exact mul_mem ((hpowV k).mpr (by rw [h1']; exact one_dvd k)) hv
  have hQp : IsPGroup 2 (T ⧸ (U ⊔ zpowers t).subgroupOf T) := hTp.to_quotient _
  obtain ⟨j₀, hj₀⟩ := (IsPGroup.iff_orderOf.mp hQp) (QuotientGroup.mk x)
  rw [← hd] at hj₀
  have hj₀0 : j₀ ≠ 0 := by
    rintro rfl
    exact hd1 (by rw [hj₀, pow_zero])
  have hdeven : 2 ∣ d := by rw [hj₀]; exact dvd_pow_self 2 hj₀0
  have hdpos : 0 < d := orderOf_pos _
  have hXdV : X ^ d ∈ U ⊔ zpowers t := (hpowV d).mpr dvd_rfl
  by_cases hXdU : X ^ d ∈ U
  ·
    have hXN : zpowers X ≤ normalizer (W : Set G) := zpowers_le.mpr (hTW hXT)
    have hMS : W ⊔ zpowers X ≤ W ⊔ T := sup_le le_sup_left ((zpowers_le.mpr hXT).trans le_sup_right)
    have hbM : ∀ w ∈ W, ∀ k : ℕ, ∀ u ∈ U, w * (X ^ k * u) ∈ W ⊔ zpowers X := by
      intro w hw k u hu
      have e : w * (X ^ k * u) = (w * (X ^ k * u * (X ^ k)⁻¹)) * X ^ k := by group
      rw [e]
      exact mul_mem (mem_sup_left (mul_mem hw (hUW (hconjU _ (pow_mem hXT k) u hu))))
        (mem_sup_right (pow_mem (mem_zpowers X) k))
    have htM : t ∉ W ⊔ zpowers X := by
      intro htM
      obtain ⟨w, hw, z, hz, hwz⟩ := exists_mul_eq_of_mem_sup hXN htM
      obtain ⟨i, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hz
      have hwT : w ∈ T := by
        have e : w = t * (X ^ i)⁻¹ := by rw [← hwz]; group
        rw [e]
        exact mul_mem htT (inv_mem (pow_mem hXT i))
      have hwU : w ∈ U := hWT ▸ mem_inf.mpr ⟨hw, hwT⟩
      have hXiV : X ^ i ∈ U ⊔ zpowers t := by
        have e : X ^ i = w⁻¹ * t := by rw [← hwz]; group
        rw [e]
        exact mul_mem (mem_sup_left (inv_mem hwU)) (mem_sup_right (mem_zpowers t))
      obtain ⟨r, hr⟩ := (hpowV i).mp hXiV
      have hXiU : X ^ i ∈ U := by
        rw [hr, pow_mul]
        exact pow_mem hXdU r
      exact htW (hwz ▸ mul_mem hw (hUW hXiU))
    have hrel : (W ⊔ zpowers X).relIndex (W ⊔ T) = 2 := by
      rw [relIndex_eq_two_iff]
      refine ⟨t, htS, fun b hb => ?_⟩
      obtain ⟨w, hw, τ, hτ, rfl⟩ := exists_mul_eq_of_mem_sup hTW hb
      obtain ⟨k, v, hv, rfl⟩ := hdec τ hτ
      obtain ⟨u, hu, rfl | rfl⟩ := exists_eq_or_eq_mul_of_mem_sup_zpowers htt htU hv
      · have hm := hbM w hw k u hu
        refine Or.inr ⟨hm, fun h => htM ?_⟩
        have h' := mul_mem (inv_mem hm) h
        rwa [inv_mul_cancel_left] at h'
      · have hm := hbM w hw k u hu
        have e : w * (X ^ k * (u * t)) * t = w * (X ^ k * u) := by
          rw [show w * (X ^ k * (u * t)) * t = w * (X ^ k * u) * (t * t) by group, htt, mul_one]
        refine Or.inl ⟨e ▸ hm, fun h => htM ?_⟩
        have e' : t = (w * (X ^ k * u))⁻¹ * (w * (X ^ k * (u * t))) := by group
        rw [e']
        exact mul_mem (inv_mem hm) h
    refine CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hSp hSidx hMS hrel htS htM
      (fun y _ hy => orderOf_le_of_ne_one htt fun h => hy (by rw [h]; exact one_mem _)) ?_
    intro g hg
    by_cases hgW : g⁻¹ * t * g ∈ W
    · exact h1 g hgW
    · refine h3 _ (hMS hg) ?_ ?_ g rfl
      · intro hy
        obtain ⟨w, hw, z, hz, hwz⟩ := exists_mul_eq_of_mem_sup (zpowers_le.mpr (hTW htT)) hy
        rcases eq_one_or_eq_of_mem_zpowers htt hz with rfl | rfl
        · exact hgW (by rw [← hwz, mul_one]; exact hw)
        · apply htM
          have e : t = w⁻¹ * (g⁻¹ * t * g) := by rw [← hwz]; group
          rw [e]
          exact mul_mem (mem_sup_left (inv_mem hw)) hg
      · calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
          _ = 1 := by rw [htt]; group
  ·
    obtain ⟨u₀, hu₀, hX⟩ : ∃ u₀ ∈ U, X ^ d = u₀ * t := by
      obtain ⟨u, hu, h | h⟩ := exists_eq_or_eq_mul_of_mem_sup_zpowers htt htU hXdV
      · exact absurd (h ▸ hu) hXdU
      · exact ⟨u, hu, h.symm⟩
    have hu₀t : u₀ * t = t * u₀ := htc u₀ (hUT hu₀)
    have hX2d : X ^ (2 * d) = 1 := by
      rw [mul_comm, pow_mul, hX, sq]
      calc u₀ * t * (u₀ * t) = u₀ * (t * u₀) * t := by group
        _ = u₀ * u₀ * (t * t) := by rw [← hu₀t]; group
        _ = 1 := by rw [hU2 u₀ hu₀, htt, one_mul]
    have hXW : ∀ m : ℕ, X ^ m ∈ W → 2 * d ∣ m := by
      intro m hm
      have hmU : X ^ m ∈ U := hWT ▸ mem_inf.mpr ⟨hm, pow_mem hXT m⟩
      obtain ⟨r, rfl⟩ := (hpowV m).mp (mem_sup_left hmU)
      rcases Nat.even_or_odd r with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · exact ⟨s, by ring⟩
      · exfalso
        have e : X ^ (d * (2 * s + 1)) = u₀ * t := by
          rw [show d * (2 * s + 1) = 2 * d * s + d by ring, pow_add, pow_mul, hX2d, one_pow,
            one_mul, hX]
        rw [e] at hmU
        exact htW (hUW (by simpa using mul_mem (inv_mem hu₀) hmU))
    have hX2N : zpowers (X ^ 2) ≤ normalizer (W : Set G) := zpowers_le.mpr (pow_mem (hTW hXT) 2)
    have hMS : W ⊔ zpowers (X ^ 2) ≤ W ⊔ T :=
      sup_le le_sup_left ((zpowers_le.mpr (pow_mem hXT 2)).trans le_sup_right)
    have hev : ∀ s : ℕ, X ^ (s + s) ∈ zpowers (X ^ 2) := fun s => by
      rw [← two_mul, pow_mul]
      exact pow_mem (mem_zpowers _) s
    have hMdec : ∀ y ∈ W ⊔ zpowers (X ^ 2), ∃ w ∈ W, ∃ i : ℕ, y = w * X ^ (2 * i) := by
      intro y hy
      obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup hX2N hy
      obtain ⟨i, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hz
      exact ⟨w, hw, i, by rw [pow_mul]⟩
    have hSdec : ∀ y ∈ W ⊔ T, ∃ w ∈ W, ∃ j : ℕ, y = w * X ^ j := by
      intro y hy
      obtain ⟨w, hw, τ, hτ, rfl⟩ := exists_mul_eq_of_mem_sup hTW hy
      obtain ⟨k, v, hv, rfl⟩ := hdec τ hτ
      obtain ⟨u, hu, rfl | rfl⟩ := exists_eq_or_eq_mul_of_mem_sup_zpowers htt htU hv
      · refine ⟨w * (X ^ k * u * (X ^ k)⁻¹), mul_mem hw (hUW (hconjU _ (pow_mem hXT k) u hu)), k,
          by group⟩
      · have ht' : t = u₀⁻¹ * X ^ d := by rw [hX]; group
        refine ⟨w * (X ^ k * (u * u₀⁻¹) * (X ^ k)⁻¹),
          mul_mem hw (hUW (hconjU _ (pow_mem hXT k) _ (mul_mem hu (inv_mem hu₀)))), k + d, ?_⟩
        rw [ht', pow_add]
        group
    have hXinv : X ^ (2 * d - 1) = X⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hX2d]
    have hXM : X ∉ W ⊔ zpowers (X ^ 2) := by
      intro hXM
      obtain ⟨w, hw, i, hwi⟩ := hMdec X hXM
      have hw' : w = X * (X ^ (2 * i))⁻¹ := eq_mul_inv_of_mul_eq hwi.symm
      have e : X ^ (1 + 2 * ((2 * d - 1) * i)) = w := by
        rw [pow_add, pow_one, show 2 * ((2 * d - 1) * i) = (2 * d - 1) * (2 * i) by ring, pow_mul,
          hXinv, inv_pow, ← hw']
      have h2d := hXW _ (e ▸ hw)
      have h2 : 2 ∣ 1 + 2 * ((2 * d - 1) * i) := (dvd_mul_right 2 d).trans h2d
      generalize (2 * d - 1) * i = k at h2
      omega
    have hrel : (W ⊔ zpowers (X ^ 2)).relIndex (W ⊔ T) = 2 := by
      rw [relIndex_eq_two_iff]
      refine ⟨X, hTS hXT, fun b hb => ?_⟩
      obtain ⟨w, hw, j, rfl⟩ := hSdec b hb
      rcases Nat.even_or_odd j with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · have hm : w * X ^ (s + s) ∈ W ⊔ zpowers (X ^ 2) :=
          mul_mem (mem_sup_left hw) (mem_sup_right (hev s))
        refine Or.inr ⟨hm, fun h => hXM ?_⟩
        have h' := mul_mem (inv_mem hm) h
        rwa [inv_mul_cancel_left] at h'
      · have hm : w * X ^ (2 * s + 1) * X ∈ W ⊔ zpowers (X ^ 2) := by
          rw [mul_assoc, ← pow_succ, show 2 * s + 1 + 1 = (s + 1) + (s + 1) by ring]
          exact mul_mem (mem_sup_left hw) (mem_sup_right (hev (s + 1)))
        refine Or.inl ⟨hm, fun h => hXM ?_⟩
        have h' := mul_mem (inv_mem h) hm
        rwa [inv_mul_cancel_left] at h'
    have hmin : ∀ y ∈ W ⊔ T, y ∉ W ⊔ zpowers (X ^ 2) → orderOf X ≤ orderOf y := by
      intro y hy hyM
      obtain ⟨w, hw, j, rfl⟩ := hSdec y hy
      have hjodd : Odd j := by
        rcases Nat.even_or_odd j with ⟨s, rfl⟩ | h
        · exact absurd (mul_mem (mem_sup_left hw) (mem_sup_right (hev s))) hyM
        · exact h
      have hXo : orderOf X ≤ 2 * d := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hX2d)
      obtain ⟨w', hw', hpow⟩ := exists_pow_mul_pow_eq (hTW hXT) hw j (orderOf (w * X ^ j))
      rw [pow_orderOf_eq_one] at hpow
      have hmem : X ^ (j * orderOf (w * X ^ j)) ∈ W := by
        rw [eq_inv_of_mul_eq_one_right hpow.symm]
        exact inv_mem hw'
      have hdvd := hXW _ hmem
      have hcop : Nat.Coprime (2 * d) j := by
        rw [hj₀, ← pow_succ']
        exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hjodd)
      exact hXo.trans (Nat.le_of_dvd (orderOf_pos _) (hcop.dvd_of_dvd_mul_left hdvd))
    have hconj : ∀ g : G, g⁻¹ * X * g ∉ W ⊔ zpowers (X ^ 2) := by
      intro g hg
      obtain ⟨w, hw, i, hwi⟩ := hMdec _ hg
      obtain ⟨w', hw', hpow⟩ := exists_pow_mul_pow_eq (hTW hXT) hw (2 * i) d
      rw [← hwi] at hpow
      have hX2id : X ^ (2 * i * d) = 1 := by
        rw [show 2 * i * d = 2 * d * i by ring, pow_mul, hX2d, one_pow]
      rw [hX2id, mul_one] at hpow
      have hc := conj_pow (a := g⁻¹) (b := X) (i := d)
      rw [inv_inv] at hc
      rw [hc, hX] at hpow
      obtain ⟨h, hh⟩ := h2 u₀ hu₀
      apply h1 (h * g)
      rw [show (h * g)⁻¹ * t * (h * g) = g⁻¹ * (h⁻¹ * t * h) * g by group, hh, hpow]
      exact hw'
    exact CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hSp hSidx hMS hrel (hTS hXT)
      hXM hmin hconj

end Transfer

section Squares

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_sq_eq_one_of_isCyclic {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {z₁ z₂ : Q}
    (h₁ : z₁ ^ 2 = 1) (h₂ : z₂ ^ 2 = 1) (h₁1 : z₁ ≠ 1) (h₂1 : z₂ ≠ 1) : z₁ = z₂ := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  by_contra hne
  have hle := IsCyclic.card_pow_eq_one_le (α := Q) (n := 2) (by norm_num)
  have hsub : ({1, z₁, z₂} : Finset Q) ⊆ Finset.univ.filter (fun a : Q => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact h₁
    · exact h₂
  have h3 : ({1, z₁, z₂} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm h₁1, Ne.symm h₂1⟩
  have := Finset.card_le_card hsub
  omega

theorem sq_eq_sq_of_isCyclic_quotient {T V : Subgroup G} [(V.subgroupOf T).Normal] (hcyc : IsCyclic (T ⧸ V.subgroupOf T))
    (hV2 : ∀ v ∈ V, v * v = 1) {a b : G} (ha : a ∈ T) (hb : b ∈ T) (hab : a * b = b * a)
    (ha4 : a ^ 4 = 1) (hb4 : b ^ 4 = 1) (ha2 : a ^ 2 ≠ 1) (hb2 : b ^ 2 ≠ 1) : a ^ 2 = b ^ 2 := by
  set Q := T ⧸ V.subgroupOf T
  have hmk : ∀ τ : T, (QuotientGroup.mk τ : Q) = 1 ↔ (τ : G) ∈ V := fun τ => by
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
  have key : ∀ {a b : G} (ha : a ∈ T) (hb : b ∈ T), a * b = b * a → ∀ e : ℕ,
      (QuotientGroup.mk ⟨a, ha⟩ : Q) ^ e = QuotientGroup.mk ⟨b, hb⟩ → b ^ 2 = a ^ (2 * e) := by
    intro a b ha hb hab e he
    have hv : (a ^ e)⁻¹ * b ∈ V := by
      have h1 : (QuotientGroup.mk ((⟨a, ha⟩ : T) ^ e)⁻¹ * QuotientGroup.mk ⟨b, hb⟩ : Q) = 1 := by
        rw [QuotientGroup.mk_inv, QuotientGroup.mk_pow, he, inv_mul_cancel]
      rw [← QuotientGroup.mk_mul, hmk] at h1
      simpa using h1
    have hc : Commute a b := hab
    have hcv : Commute (a ^ e) ((a ^ e)⁻¹ * b) :=
      (Commute.refl (a ^ e)).inv_right.mul_right (hc.pow_left e)
    have hb' : b = a ^ e * ((a ^ e)⁻¹ * b) := by group
    rw [hb', hcv.mul_pow, sq ((a ^ e)⁻¹ * b), hV2 _ hv, mul_one, ← pow_mul, mul_comm]
  set A : Q := QuotientGroup.mk ⟨a, ha⟩ with hA
  set B : Q := QuotientGroup.mk ⟨b, hb⟩ with hB
  have hnot : ∀ {c : G} (hc : c ∈ T), c ^ 2 ≠ 1 → (QuotientGroup.mk ⟨c, hc⟩ : Q) ≠ 1 := by
    intro c hc hc2 h
    exact hc2 (by rw [sq]; exact hV2 c ((hmk _).mp h))
  have hA1 := hnot ha ha2
  have hB1 := hnot hb hb2
  have hA4 : A ^ 4 = 1 := by
    rw [hA, ← QuotientGroup.mk_pow, show (⟨a, ha⟩ : T) ^ 4 = 1 from Subtype.ext (by simpa using ha4),
      QuotientGroup.mk_one]
  have hB4 : B ^ 4 = 1 := by
    rw [hB, ← QuotientGroup.mk_pow, show (⟨b, hb⟩ : T) ^ 4 = 1 from Subtype.ext (by simpa using hb4),
      QuotientGroup.mk_one]
  have hAB : A * B = B * A := by
    rw [hA, hB, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hab
  have hsq : ∀ z : Q, z ^ 4 = 1 → (z ^ 2) ^ 2 = 1 := fun z hz => by rw [← pow_mul]; exact hz
  by_cases hA2 : A ^ 2 = 1
  · by_cases hB2 : B ^ 2 = 1
    · have heq : A = B := eq_of_sq_eq_one_of_isCyclic hA2 hB2 hA1 hB1
      have := key ha hb hab 1 (by rw [pow_one]; exact heq)
      rw [this, mul_one]
    ·
      exfalso
      have heq : B ^ 2 = A := eq_of_sq_eq_one_of_isCyclic (hsq B hB4) hA2 hB2 hA1
      have := key hb ha hab.symm 2 heq
      rw [show 2 * 2 = 4 by norm_num, hb4] at this
      exact ha2 this
  · by_cases hB2 : B ^ 2 = 1
    · exfalso
      have heq : A ^ 2 = B := eq_of_sq_eq_one_of_isCyclic (hsq A hA4) hB2 hA2 hB1
      have := key ha hb hab 2 heq
      rw [show 2 * 2 = 4 by norm_num, ha4] at this
      exact hb2 this
    · have hAB2 : A ^ 2 = B ^ 2 := eq_of_sq_eq_one_of_isCyclic (hsq A hA4) (hsq B hB4) hA2 hB2
      have hC2 : (A * B⁻¹) ^ 2 = 1 := by
        have hc : Commute A B⁻¹ := (Commute.inv_right hAB)
        rw [hc.mul_pow, hAB2, inv_pow, mul_inv_cancel]
      by_cases hC1 : A * B⁻¹ = 1
      · have heq : A = B := mul_inv_eq_one.mp hC1
        have := key ha hb hab 1 (by rw [pow_one]; exact heq)
        rw [this, mul_one]
      · have heq : A * B⁻¹ = A ^ 2 := eq_of_sq_eq_one_of_isCyclic hC2 (hsq A hA4) hC1 hA2
        have hB3 : A ^ 3 = B := by
          have h1 : B⁻¹ = A := by
            have := congrArg (A⁻¹ * ·) heq
            simp only [inv_mul_cancel_left] at this
            rw [this, sq, inv_mul_cancel_left]
          have h2 : B = A⁻¹ := by rw [← h1, inv_inv]
          rw [h2, eq_inv_iff_mul_eq_one, ← pow_succ, hA4]
        have := key ha hb hab 3 hB3
        rw [this, show 2 * 3 = 4 + 2 by norm_num, pow_add, ha4, one_mul]

theorem sq_eq_sq_of_isSylow {K T : Subgroup G}
    (hT : ∃ P : Sylow 2 K, (P : Subgroup K) = T.subgroupOf K)
    (hK2 : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a → a ^ 4 = 1 → b ^ 4 = 1 → a ^ 2 ≠ 1 → b ^ 2 ≠ 1 →
      a ^ 2 = b ^ 2)
    {a b : G} (ha : a ∈ K) (hb : b ∈ K) (hab : a * b = b * a) (ha4 : a ^ 4 = 1)
    (hb4 : b ^ 4 = 1) (ha2 : a ^ 2 ≠ 1) (hb2 : b ^ 2 ≠ 1) : a ^ 2 = b ^ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hT
  set a' : K := ⟨a, ha⟩
  set b' : K := ⟨b, hb⟩
  have hab' : Commute a' b' := Subtype.ext hab
  set H : Subgroup K := zpowers a' ⊔ zpowers b'
  have hab'N : zpowers b' ≤ normalizer ((zpowers a' : Subgroup K) : Set K) := by
    refine zpowers_le.mpr (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz => ?_))
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact (hab'.zpow_left k).eq
  have hH4 : ∀ h ∈ H, h ^ 4 = 1 := by
    intro h hh
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_eq_of_mem_sup hab'N hh
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx₁
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx₂
    have ha4' : a' ^ 4 = 1 := Subtype.ext ha4
    have hb4' : b' ^ 4 = 1 := Subtype.ext hb4
    rw [(hab'.zpow_zpow i j).mul_pow, ← zpow_natCast, ← zpow_mul, ← zpow_natCast (b' ^ j),
      ← zpow_mul, mul_comm i, mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ha4',
      hb4', one_zpow, one_zpow, one_mul]
  have hHp : IsPGroup 2 H := fun h => ⟨2, Subtype.ext (by simpa using hH4 h h.2)⟩
  obtain ⟨P', hP'⟩ := hHp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K P' P
  have hmem : ∀ z : K, z ∈ H → c * z * c⁻¹ ∈ (P : Subgroup K) := by
    intro z hz
    rw [← hc]
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, mul_assoc] using hP' hz
  have hT' : ∀ z : K, z ∈ H → ((c : G) * z * (c : G)⁻¹) ∈ T := by
    intro z hz
    have h1 := hmem z hz
    rw [hP, mem_subgroupOf] at h1
    simpa using h1
  have ha' := hT' a' (mem_sup_left (mem_zpowers a'))
  have hb' := hT' b' (mem_sup_right (mem_zpowers b'))
  have hconj4 : ∀ x : G, x ^ 4 = 1 → ((c : G) * x * (c : G)⁻¹) ^ 4 = 1 := fun x hx => by
    rw [conj_pow, hx, mul_one, mul_inv_cancel]
  have hconj2 : ∀ x : G, x ^ 2 ≠ 1 → ((c : G) * x * (c : G)⁻¹) ^ 2 ≠ 1 := fun x hx h => by
    rw [conj_pow] at h
    have h' : (c : G) * x ^ 2 = (c : G) * 1 := by
      rw [mul_one]
      exact (mul_inv_eq_one.mp h)
    exact hx (mul_left_cancel h')
  have hcomm : ((c : G) * a * (c : G)⁻¹) * ((c : G) * b * (c : G)⁻¹) =
      ((c : G) * b * (c : G)⁻¹) * ((c : G) * a * (c : G)⁻¹) := by
    calc ((c : G) * a * (c : G)⁻¹) * ((c : G) * b * (c : G)⁻¹) = (c : G) * (a * b) * (c : G)⁻¹ := by
          group
      _ = (c : G) * (b * a) * (c : G)⁻¹ := by rw [hab]
      _ = _ := by group
  have := hK2 _ ha' _ hb' hcomm (hconj4 a ha4) (hconj4 b hb4) (hconj2 a ha2) (hconj2 b hb2)
  rw [conj_pow, conj_pow] at this
  exact mul_left_cancel (mul_right_cancel this)

end Squares

section Homocyclic

variable {G : Type*} [Group G] [Finite G]

theorem exists_sq_ne_of_involution {W U : Subgroup G}
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hUW : U ≤ W) (hU2 : ∀ u ∈ U, u * u = 1)
    (hΩ : ∀ w ∈ W, w * w = 1 → w ∈ U) (h℧ : ∀ u ∈ U, ∃ w ∈ W, w * w = u) {y : G}
    (hyW : ∀ w ∈ W, y * w * y⁻¹ ∈ W) (hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) (hyy : y * y = 1)
    (hcard : Nat.card (U ⊓ centralizer ({y} : Set G) : Subgroup G) ^ 2 ≤ Nat.card U)
    (h16 : 16 ≤ Nat.card U) :
    ∃ a ∈ W, ∃ b ∈ W, y * a = a * y ∧ y * b = b * y ∧ a * b = b * a ∧
      a * a ≠ 1 ∧ b * b ≠ 1 ∧ a * a ≠ b * b ∧ a ^ 4 = 1 ∧ b ^ 4 = 1 := by
  classical
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => hWab a (hUW ha) b (hUW hb)
  set C : Subgroup G := U ⊓ centralizer ({y} : Set G) with hC
  let φ : U →* U :=
    { toFun := fun u => ⟨u * (y * u * y⁻¹), mul_mem u.2 (hyU u u.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by
        show (u : G) * v * (y * (u * v) * y⁻¹) = u * (y * u * y⁻¹) * (v * (y * v * y⁻¹))
        have h1 : y * ((u : G) * v) * y⁻¹ = (y * u * y⁻¹) * (y * v * y⁻¹) := by group
        rw [h1]
        have hc := hUab v v.2 (y * u * y⁻¹) (hyU u u.2)
        calc (u : G) * v * ((y * u * y⁻¹) * (y * v * y⁻¹))
            = u * (v * (y * u * y⁻¹)) * (y * v * y⁻¹) := by group
          _ = u * ((y * u * y⁻¹) * v) * (y * v * y⁻¹) := by rw [hc]
          _ = _ := by group) }
  have hφ : ∀ u : U, (φ u : G) = u * (y * u * y⁻¹) := fun _ => rfl
  have hker : ∀ u : U, φ u = 1 ↔ (u : G) ∈ C := by
    intro u
    constructor
    · intro h
      have h1 : (u : G) * (y * u * y⁻¹) = 1 := by rw [← hφ, h]; rfl
      have h2 : y * u * y⁻¹ = u := by
        have := eq_inv_of_mul_eq_one_right h1
        rwa [inv_eq_of_mul_eq_one_right (hU2 u u.2)] at this
      refine mem_inf.mpr ⟨u.2, mem_centralizer_singleton_iff.mpr ?_⟩
      calc (u : G) * y = y * u * y⁻¹ * y := by rw [h2]
        _ = y * u := by group
    · intro h
      have h2 : y * (u : G) * y⁻¹ = u := by
        rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp h).2]
        group
      exact Subtype.ext (by rw [hφ, h2]; exact hU2 u u.2)
  have himC : ∀ u : U, (φ u : G) ∈ C := by
    intro u
    refine mem_inf.mpr ⟨(φ u).2, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hφ]
    have hyu := hyU u u.2
    have e : y * ((u : G) * (y * u * y⁻¹)) * y⁻¹ = (y * u * y⁻¹) * u := by
      rw [show y * ((u : G) * (y * u * y⁻¹)) * y⁻¹ = (y * u * y⁻¹) * ((y * y) * u * (y⁻¹ * y⁻¹))
        by group, hyy, show y⁻¹ * y⁻¹ = 1 by rw [← mul_inv_rev, hyy, inv_one]]
      group
    have e2 : (y * u * y⁻¹) * (u : G) = u * (y * u * y⁻¹) := hUab _ hyu _ u.2
    calc (u : G) * (y * u * y⁻¹) * y = y * (y⁻¹ * ((u : G) * (y * u * y⁻¹)) * y) := by group
      _ = y * (y * ((u : G) * (y * u * y⁻¹)) * y⁻¹) := by rw [hyinv]
      _ = y * ((u : G) * (y * u * y⁻¹)) := by rw [e, e2]
  have hkerC : Nat.card φ.ker = Nat.card C := by
    refine Nat.card_congr
      { toFun := fun u => ⟨(u.1 : G), (hker u.1).mp u.2⟩
        invFun := fun c => ⟨⟨c, (mem_inf.mp c.2).1⟩, (hker _).mpr c.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrangeC : Nat.card φ.range ≤ Nat.card C := by
    refine Nat.card_le_card_of_injective (fun v => ⟨((v : U) : G), ?_⟩) ?_
    · obtain ⟨u, hu⟩ := v.2
      rw [← hu]
      exact himC u
    · intro v v' h
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      simpa using h'
  have hU : Nat.card U = Nat.card φ.ker * Nat.card φ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
  rw [hkerC] at hU
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hrange_eq : Nat.card φ.range = Nat.card C := by
    refine le_antisymm hrangeC ?_
    by_contra hlt
    push Not at hlt
    have : Nat.card C * Nat.card φ.range < Nat.card C * Nat.card C :=
      Nat.mul_lt_mul_of_pos_left hlt hCpos
    rw [← hU] at this
    rw [sq] at hcard
    omega
  have hsurj : ∀ c ∈ C, ∃ u : U, (φ u : G) = c := by
    intro c hc
    by_contra hno
    push Not at hno
    have hlt : Nat.card φ.range < Nat.card C := by
      have hinj : Function.Injective (fun v : φ.range => (⟨((v : U) : G), by
          obtain ⟨u, hu⟩ := v.2
          rw [← hu]
          exact himC u⟩ : C)) := by
        intro v v' h
        apply Subtype.ext
        apply Subtype.ext
        have h' := congrArg Subtype.val h
        simpa using h'
      refine lt_of_le_of_ne (Nat.card_le_card_of_injective _ hinj) fun heq => ?_
      have hbij := (Function.Injective.bijective_of_nat_card_le hinj heq.ge).2 ⟨c, hc⟩
      obtain ⟨v, hv⟩ := hbij
      obtain ⟨u, hu⟩ := v.2
      exact hno u (by
        have := congrArg Subtype.val hv
        simp only at this
        rw [← this, ← hu])
    omega
  have hC4 : 4 ≤ Nat.card C := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card U ≤ 3 * 3 := by
      rw [hU, hrange_eq]
      exact Nat.mul_le_mul (by omega) (by omega)
    omega
  have hroot : ∀ c ∈ C, ∃ a ∈ W, y * a = a * y ∧ a * a = c := by
    intro c hc
    obtain ⟨hcU, hcy⟩ := mem_inf.mp hc
    obtain ⟨w, hw, hwc⟩ := h℧ c hcU
    have hyw := hyW w hw
    set e := w⁻¹ * (y * w * y⁻¹) with he
    have heW : e ∈ W := mul_mem (inv_mem hw) hyw
    have hycy : y * c * y⁻¹ = c := by
      rw [← mem_centralizer_singleton_iff.mp hcy]
      group
    have hee : e * e = 1 := by
      have hc1 : w⁻¹ * (y * w * y⁻¹) = (y * w * y⁻¹) * w⁻¹ := hWab _ (inv_mem hw) _ hyw
      calc e * e = w⁻¹ * (y * w * y⁻¹) * ((y * w * y⁻¹) * w⁻¹) := by rw [he, hc1]
        _ = w⁻¹ * (y * (w * w) * y⁻¹) * w⁻¹ := by group
        _ = w⁻¹ * c * w⁻¹ := by rw [hwc, hycy]
        _ = w⁻¹ * (w * w) * w⁻¹ := by rw [hwc]
        _ = 1 := by group
    have heU : e ∈ U := hΩ e heW hee
    have heC : e ∈ C := by
      refine mem_inf.mpr ⟨heU, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : y * e * y⁻¹ = (y * w * y⁻¹)⁻¹ * w := by
        rw [he]
        calc y * (w⁻¹ * (y * w * y⁻¹)) * y⁻¹ = (y * w * y⁻¹)⁻¹ * ((y * y) * w * (y⁻¹ * y⁻¹)) := by
              group
          _ = (y * w * y⁻¹)⁻¹ * w := by
              rw [hyy, show y⁻¹ * y⁻¹ = 1 by rw [← mul_inv_rev, hyy, inv_one]]
              group
      have h2 : (y * w * y⁻¹)⁻¹ * w = e⁻¹ := by
        rw [he]
        group
      have h3 : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
      calc e * y = y * (y⁻¹ * e * y) := by group
        _ = y * (y * e * y⁻¹) := by rw [hyinv]
        _ = y * e := by rw [h1, h2, h3]
    obtain ⟨u, hu⟩ := hsurj e heC
    rw [hφ] at hu
    have huW : (u : G) ∈ W := hUW u.2
    have hyuU := hyU u u.2
    refine ⟨w * u, mul_mem hw huW, ?_, ?_⟩
    ·
      have h1 : y * (w * u) * y⁻¹ = w * u := by
        calc y * (w * u) * y⁻¹ = (y * w * y⁻¹) * (y * u * y⁻¹) := by group
          _ = w * e * (y * u * y⁻¹) := by rw [he]; group
          _ = w * u * ((y * u * y⁻¹) * (y * u * y⁻¹)) := by rw [← hu]; group
          _ = w * u := by rw [hU2 _ hyuU, mul_one]
      calc y * (w * u) = y * (w * u) * y⁻¹ * y := by group
        _ = w * u * y := by rw [h1]
    · calc w * u * (w * u) = w * w * (u * u) := by
            rw [show w * u * (w * u) = w * (u * w) * u by group, hWab u huW w hw]
            group
        _ = c := by rw [hwc, hU2 u u.2, mul_one]
  have hC2 : ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ ≠ 1 ∧ c₂ ≠ 1 ∧ c₁ ≠ c₂ := by
    obtain ⟨c₁, hc₁1⟩ : ∃ c : C, c ≠ 1 := by
      by_contra hno
      push Not at hno
      have : Nat.card C ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => (hno a).trans (hno b).symm⟩
      omega
    obtain ⟨c₂, hc₂1, hc₂c₁⟩ : ∃ c : C, c ≠ 1 ∧ c ≠ c₁ := by
      by_contra hno
      push Not at hno
      have hinj : Function.Injective (fun c : C => decide (c = 1)) := by
        intro a b hab
        by_cases ha : a = 1 <;> by_cases hb : b = 1
        · rw [ha, hb]
        · simp [ha, hb] at hab
        · simp [ha, hb] at hab
        · rw [hno a ha, hno b hb]
      have := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
      omega
    refine ⟨c₁, c₁.2, c₂, c₂.2, fun h => hc₁1 (Subtype.ext h), fun h => hc₂1 (Subtype.ext h),
      fun h => hc₂c₁ (Subtype.ext h.symm)⟩
  obtain ⟨c₁, hc₁, c₂, hc₂, hc₁1, hc₂1, hc₁₂⟩ := hC2
  obtain ⟨a, haW, hay, rfl⟩ := hroot c₁ hc₁
  obtain ⟨b, hbW, hby, rfl⟩ := hroot c₂ hc₂
  have h4 : ∀ x : G, x * x ∈ U → x ^ 4 = 1 := fun x hx => by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq]
    rw [sq]
    exact hU2 _ hx
  exact ⟨a, haW, b, hbW, hay, hby, hWab a haW b hbW, hc₁1, hc₂1, hc₁₂,
    h4 a (mem_inf.mp hc₁).1, h4 b (mem_inf.mp hc₂).1⟩


theorem not_isConj_of_fixed_square_pair
    {G : Type*} [Group G] [Finite G]
    {B1 U A T M : Subgroup G} {y t : G}
    (hBcomm : ∀ a ∈ B1, ∀ b ∈ B1, a * b = b * a)
    (hUB : U ≤ B1)
    (hU2 : ∀ u ∈ U, u * u = 1)
    (hOmega : ∀ b ∈ B1, b * b = 1 → b ∈ U)
    (hSquare : ∀ u ∈ U, ∃ b ∈ B1, b * b = u)
    (hyB : ∀ b ∈ B1, y * b * y⁻¹ ∈ B1)
    (hy2 : y * y = 1)
    (hFixed : Nat.card ↥(U ⊓ Subgroup.centralizer ({y} : Set G)) ^ 2 ≤ Nat.card U)
    (h16 : 16 ≤ Nat.card U)
    [(A.subgroupOf T).Normal]
    (hCyclic : IsCyclic (T ⧸ A.subgroupOf T))
    (hA2 : ∀ a ∈ A, a * a = 1)
    (hT : ∃ P : Sylow 2 M, (P : Subgroup M) = T.subgroupOf M)
    (hCentralizer : Subgroup.centralizer ({t} : Set G) ≤ M) :
    ¬ IsConj y t := by
  classical
  have hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
    intro u hu
    apply hOmega _ (hyB u (hUB hu))
    calc (y * u * y⁻¹) * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
      _ = 1 := by rw [hU2 u hu]; group
  rintro hconj
  obtain ⟨a, haB, b, hbB, hya, hyb, hab, ha_ne, hb_ne, hsq_ne, ha4, hb4⟩ :=
    exists_sq_ne_of_involution hBcomm hUB hU2 hOmega hSquare hyB hyU hy2 hFixed h16
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let f : MulAut G := MulAut.conj g
  set a' : G := f a with ha'
  set b' : G := f b with hb'
  have hfa : a' = g * a * g⁻¹ := by rw [ha']; simp [f, MulAut.conj_apply]
  have hfb : b' = g * b * g⁻¹ := by rw [hb']; simp [f, MulAut.conj_apply]
  have hra : a' * t = t * a' := by
    rw [hfa, ← hg]
    calc (g * a * g⁻¹) * (g * y * g⁻¹) = g * (a * y) * g⁻¹ := by group
      _ = g * (y * a) * g⁻¹ := by rw [hya]
      _ = (g * y * g⁻¹) * (g * a * g⁻¹) := by group
  have hrb : b' * t = t * b' := by
    rw [hfb, ← hg]
    calc (g * b * g⁻¹) * (g * y * g⁻¹) = g * (b * y) * g⁻¹ := by group
      _ = g * (y * b) * g⁻¹ := by rw [hyb]
      _ = (g * y * g⁻¹) * (g * b * g⁻¹) := by group
  have ha'M : a' ∈ M := hCentralizer (Subgroup.mem_centralizer_singleton_iff.mpr hra)
  have hb'M : b' ∈ M := hCentralizer (Subgroup.mem_centralizer_singleton_iff.mpr hrb)
  have ha'4 : a' ^ (4 : ℕ) = 1 := by
    rw [ha']
    rw [← map_pow, ha4, map_one]
  have hb'4 : b' ^ (4 : ℕ) = 1 := by
    rw [hb']
    rw [← map_pow, hb4, map_one]
  have ha'2 : a' ^ (2 : ℕ) ≠ 1 := by
    intro h
    apply ha_ne
    have h' : f (a ^ (2 : ℕ)) = f 1 := by
      rw [map_pow, map_one]
      exact h
    simpa [pow_two] using f.injective h'
  have hb'2 : b' ^ (2 : ℕ) ≠ 1 := by
    intro h
    apply hb_ne
    have h' : f (b ^ (2 : ℕ)) = f 1 := by
      rw [map_pow, map_one]
      exact h
    simpa [pow_two] using f.injective h'
  have ha'b' : a' * b' = b' * a' := by
    rw [ha', hb']
    rw [← map_mul, ← map_mul, hab]
  have hsq_ne' : a' ^ (2 : ℕ) ≠ b' ^ (2 : ℕ) := by
    intro h
    apply hsq_ne
    have h' : f (a * a) = f (b * b) := by
      rw [map_mul, map_mul]
      simpa [pow_two] using h
    have h2 : a * a = b * b := f.injective h'
    simpa [pow_two] using h2
  have hK2 : ∀ a ∈ T, ∀ b ∈ T,
      a * b = b * a → a ^ (4 : ℕ) = 1 → b ^ (4 : ℕ) = 1 →
      a ^ (2 : ℕ) ≠ 1 → b ^ (2 : ℕ) ≠ 1 → a ^ (2 : ℕ) = b ^ (2 : ℕ) := by
    intro a ha b hb hab' ha4' hb4' ha2' hb2'
    exact sq_eq_sq_of_isCyclic_quotient hCyclic hA2
      ha hb hab' ha4' hb4' ha2' hb2'
  have hsqeq := sq_eq_sq_of_isSylow hT hK2 ha'M hb'M ha'b' ha'4 hb'4 ha'2 hb'2
  exact hsq_ne' hsqeq

end Homocyclic

end CFSG.SeitzReduction.RankOne.Endings
