module

public import CFSG.Assembly.Defs
public import CFSG.GH74.Uniqueness.Section15HeringEnd1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup MulAction

section Group

variable {G : Type*} [Group G]

@[expose] def AtMostOneCentralInvolution (S : Subgroup G) : Prop :=
  ∀ z₁ ∈ S, ∀ z₂ ∈ S, orderOf z₁ = 2 → orderOf z₂ = 2 → (∀ s ∈ S, z₁ * s = s * z₁) →
    (∀ s ∈ S, z₂ * s = s * z₂) → z₁ = z₂

theorem three_not_dvd_two_pow_sub_one {p : ℕ} (hp : Odd p) : ¬ 3 ∣ 2 ^ p - 1 := by
  obtain ⟨k, rfl⟩ := hp
  have h1 : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h2 : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
  generalize 2 ^ (2 * k + 1) = X at *
  omega

theorem mem_four_cases [Finite G] {V : Subgroup G} (hV4 : Nat.card V = 4) {z u : G}
    (hz : z ∈ V) (hu : u ∈ V) (hz1 : z ≠ 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) {x : G} (hx : x ∈ V) :
    x = 1 ∨ x = z ∨ x = u ∨ x = u * z := by
  have hzz : z * z = 1 := by rw [← pow_two]; exact hV2 z hz
  have huz1 : u * z ≠ 1 := by
    intro h
    apply huz
    calc u = u * z * z := by rw [mul_assoc, hzz, mul_one]
      _ = z := by rw [h, one_mul]
  have huzz : u * z ≠ z := fun h => hu1 (by simpa using h)
  have huzu : u * z ≠ u := fun h => hz1 (by simpa using h)
  by_contra hcon
  push Not at hcon
  obtain ⟨hx1, hxz, hxu, hxuz⟩ := hcon
  have hsub : ({x, 1, z, u, u * z} : Set G) ⊆ (V : Set G) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact hx
    · exact one_mem V
    · exact hz
    · exact hu
    · exact mul_mem hu hz
  have hcard : ({x, 1, z, u, u * z} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [hx1, hxz, hxu, hxuz]),
      Set.ncard_insert_of_notMem (by simp [hz1.symm, hu1.symm, huz1.symm]),
      Set.ncard_insert_of_notMem (by simp [huz.symm, huzz.symm]),
      Set.ncard_pair huzu.symm]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hV4] at this
  omega

theorem thompson_omega {S : Subgroup G} (huniq : AtMostOneCentralInvolution S)
    {z u a : G} (hzS : z ∈ S) (hz2 : orderOf z = 2) (hzc : ∀ s ∈ S, z * s = s * z)
    (huS : u ∈ S) (hu2 : u ^ 2 = 1) (haS : a ∈ S) (hau : a * u * a⁻¹ = u * z)
    (hcases : ∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z)
    {v : G} (hvQ : v ∈ S ⊓ centralizer {u})
    (hvc : ∀ q ∈ S ⊓ centralizer {u}, v * q = q * v) (hv2 : v ^ 2 = 1) :
    v = 1 ∨ v = z ∨ v = u ∨ v = u * z := by
  set Q := S ⊓ centralizer ({u} : Set G) with hQ
  have hmemQ : ∀ q, q ∈ Q ↔ q ∈ S ∧ q * u = u * q := fun q => by
    rw [hQ, mem_inf, mem_centralizer_singleton_iff]
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have huu : u * u = 1 := by rw [← pow_two, hu2]
  have hvv : v * v = 1 := by rw [← pow_two, hv2]
  have hzconj : ∀ g ∈ S, g * z * g⁻¹ = z := fun g hg => by
    rw [← hzc g hg, mul_inv_cancel_right]
  have hzconj' : ∀ g ∈ S, g⁻¹ * z * g = z := fun g hg => by
    simpa using hzconj g⁻¹ (S.inv_mem hg)
  have hau' : a⁻¹ * u * a = u * z := by
    have h1 : u = a⁻¹ * (u * z) * a := by rw [← hau]; group
    have h2 : a⁻¹ * (u * z) * a = (a⁻¹ * u * a) * z := by
      rw [show a⁻¹ * (u * z) * a = (a⁻¹ * u * a) * (a⁻¹ * z * a) by group, hzconj' a haS]
    calc a⁻¹ * u * a = (a⁻¹ * u * a) * z * z := by rw [mul_assoc _ z z, hzz, mul_one]
      _ = u * z := by rw [← h2, ← h1]
  have hsplit : ∀ s ∈ S, s ∈ Q ∨ a⁻¹ * s ∈ Q := by
    intro s hs
    rcases hcases s hs with h | h
    · left
      refine (hmemQ s).mpr ⟨hs, ?_⟩
      calc s * u = s * u * s⁻¹ * s := by group
        _ = u * s := by rw [h]
    · right
      refine (hmemQ _).mpr ⟨S.mul_mem (S.inv_mem haS) hs, ?_⟩
      have : (a⁻¹ * s) * u * (a⁻¹ * s)⁻¹ = u := by
        calc (a⁻¹ * s) * u * (a⁻¹ * s)⁻¹ = a⁻¹ * (s * u * s⁻¹) * a := by group
          _ = a⁻¹ * (u * z) * a := by rw [h]
          _ = (a⁻¹ * u * a) * (a⁻¹ * z * a) := by group
          _ = (u * z) * z := by rw [hau', hzconj' a haS]
          _ = u := by rw [mul_assoc, hzz, mul_one]
      calc a⁻¹ * s * u = (a⁻¹ * s) * u * (a⁻¹ * s)⁻¹ * (a⁻¹ * s) := by group
        _ = u * (a⁻¹ * s) := by rw [this]
  have hcentral : ∀ w ∈ S, w * a = a * w → (∀ q ∈ Q, w * q = q * w) →
      ∀ s ∈ S, w * s = s * w := by
    intro w _ hwa hwq s hs
    rcases hsplit s hs with h | h
    · exact hwq s h
    · have hq := hwq _ h
      calc w * s = w * (a * (a⁻¹ * s)) := by group
        _ = a * (w * (a⁻¹ * s)) := by rw [← mul_assoc, hwa, mul_assoc]
        _ = a * ((a⁻¹ * s) * w) := by rw [hq]
        _ = s * w := by group
  have hone : ∀ w ∈ S, w ^ 2 = 1 → (∀ s ∈ S, w * s = s * w) → w = 1 ∨ w = z := by
    intro w hw hw2 hwc
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (huniq w hw z hzS (orderOf_eq_prime hw2 hw1) hz2 hwc hzc)
  have ha2 : a * a ∈ Q := by
    refine (hmemQ _).mpr ⟨S.mul_mem haS haS, ?_⟩
    have : (a * a) * u * (a * a)⁻¹ = u := by
      calc (a * a) * u * (a * a)⁻¹ = a * (a * u * a⁻¹) * a⁻¹ := by group
        _ = a * (u * z) * a⁻¹ := by rw [hau]
        _ = (a * u * a⁻¹) * (a * z * a⁻¹) := by group
        _ = (u * z) * z := by rw [hau, hzconj a haS]
        _ = u := by rw [mul_assoc, hzz, mul_one]
    calc (a * a) * u = (a * a) * u * (a * a)⁻¹ * (a * a) := by group
      _ = u * (a * a) := by rw [this]
  have hnorm : ∀ q ∈ Q, a * q * a⁻¹ ∈ Q := by
    intro q hq
    obtain ⟨hqS, hqu⟩ := (hmemQ q).mp hq
    refine (hmemQ _).mpr ⟨S.mul_mem (S.mul_mem haS hqS) (S.inv_mem haS), ?_⟩
    have hqz : q * z = z * q := (hzc q hqS).symm
    have : (a * q * a⁻¹) * u * (a * q * a⁻¹)⁻¹ = u := by
      calc (a * q * a⁻¹) * u * (a * q * a⁻¹)⁻¹ = a * (q * (a⁻¹ * u * a) * q⁻¹) * a⁻¹ := by
            group
        _ = a * (q * (u * z) * q⁻¹) * a⁻¹ := by rw [hau']
        _ = a * (u * z) * a⁻¹ := by
            rw [show q * (u * z) * q⁻¹ = (q * u) * z * q⁻¹ by group, hqu,
              show u * q * z * q⁻¹ = u * (q * z) * q⁻¹ by group, hqz]
            group
        _ = (a * u * a⁻¹) * (a * z * a⁻¹) := by group
        _ = (u * z) * z := by rw [hau, hzconj a haS]
        _ = u := by rw [mul_assoc, hzz, mul_one]
    calc (a * q * a⁻¹) * u = (a * q * a⁻¹) * u * (a * q * a⁻¹)⁻¹ * (a * q * a⁻¹) := by group
      _ = u * (a * q * a⁻¹) := by rw [this]
  have hnorm' : ∀ q ∈ Q, a⁻¹ * q * a ∈ Q := by
    intro q hq
    have : a⁻¹ * q * a = (a * a)⁻¹ * (a * q * a⁻¹) * (a * a) := by group
    rw [this]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem ha2) (hnorm q hq)) ha2
  have hv'Q : a * v * a⁻¹ ∈ Q := hnorm v hvQ
  have hv'c : ∀ q ∈ Q, (a * v * a⁻¹) * q = q * (a * v * a⁻¹) := by
    intro q hq
    have := hvc _ (hnorm' q hq)
    calc (a * v * a⁻¹) * q = a * (v * (a⁻¹ * q * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * q * a) * v) * a⁻¹ := by rw [this]
      _ = q * (a * v * a⁻¹) := by group
  have hvv' : v * (a * v * a⁻¹) = (a * v * a⁻¹) * v := hvc _ hv'Q
  have hwQ : v * (a * v * a⁻¹) ∈ Q := Q.mul_mem hvQ hv'Q
  have hwc : ∀ q ∈ Q, (v * (a * v * a⁻¹)) * q = q * (v * (a * v * a⁻¹)) := by
    intro q hq
    rw [mul_assoc, hv'c q hq, ← mul_assoc, hvc q hq, mul_assoc]
  have hwa : (v * (a * v * a⁻¹)) * a = a * (v * (a * v * a⁻¹)) := by
    have h1 : a * (a * v * a⁻¹) * a⁻¹ = v := by
      have := hvc (a * a) ha2
      calc a * (a * v * a⁻¹) * a⁻¹ = (a * a) * v * (a * a)⁻¹ := by group
        _ = v * (a * a) * (a * a)⁻¹ := by rw [← this]
        _ = v := by group
    have : a * (v * (a * v * a⁻¹)) * a⁻¹ = v * (a * v * a⁻¹) := by
      calc a * (v * (a * v * a⁻¹)) * a⁻¹ = (a * v * a⁻¹) * (a * (a * v * a⁻¹) * a⁻¹) := by
            group
        _ = (a * v * a⁻¹) * v := by rw [h1]
        _ = v * (a * v * a⁻¹) := hvv'.symm
    calc (v * (a * v * a⁻¹)) * a = a * (v * (a * v * a⁻¹)) * a⁻¹ * a := by rw [this]
      _ = a * (v * (a * v * a⁻¹)) := by group
  have hw2 : (v * (a * v * a⁻¹)) ^ 2 = 1 := by
    have hv'2 : (a * v * a⁻¹) * (a * v * a⁻¹) = 1 := by
      calc (a * v * a⁻¹) * (a * v * a⁻¹) = a * (v * v) * a⁻¹ := by group
        _ = 1 := by rw [hvv]; group
    rw [pow_two]
    calc v * (a * v * a⁻¹) * (v * (a * v * a⁻¹)) =
        v * ((a * v * a⁻¹) * v) * (a * v * a⁻¹) := by group
      _ = v * (v * (a * v * a⁻¹)) * (a * v * a⁻¹) := by rw [hvv']
      _ = (v * v) * ((a * v * a⁻¹) * (a * v * a⁻¹)) := by group
      _ = 1 := by rw [hvv, hv'2, one_mul]
  have hwS : v * (a * v * a⁻¹) ∈ S := ((hmemQ _).mp hwQ).1
  have hvS : v ∈ S := ((hmemQ v).mp hvQ).1
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  rcases hone _ hwS hw2 (hcentral _ hwS hwa hwc) with hw1 | hwz
  · have hva : v * a = a * v := by
      have hv' : a * v * a⁻¹ = v := by
        calc a * v * a⁻¹ = v⁻¹ * (v * (a * v * a⁻¹)) := by group
          _ = v := by rw [hw1, mul_one, hvinv]
      calc v * a = (a * v * a⁻¹) * a := by rw [hv']
        _ = a * v := by group
    rcases hone v hvS hv2 (hcentral v hvS hva hvc) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hv'z : a * v * a⁻¹ = v * z := by
      calc a * v * a⁻¹ = v⁻¹ * (v * (a * v * a⁻¹)) := by group
        _ = v * z := by rw [hwz, hvinv]
    have huQ : u ∈ Q := (hmemQ u).mpr ⟨huS, rfl⟩
    have hvu : v * u = u * v := hvc u huQ
    have hzu : z * u = u * z := hzc u huS
    have htc : ∀ q ∈ Q, (v * u) * q = q * (v * u) := by
      intro q hq
      have hqu : q * u = u * q := ((hmemQ q).mp hq).2
      rw [mul_assoc, ← hqu, ← mul_assoc, hvc q hq, mul_assoc]
    have hta : (v * u) * a = a * (v * u) := by
      have : a * (v * u) * a⁻¹ = v * u := by
        calc a * (v * u) * a⁻¹ = (a * v * a⁻¹) * (a * u * a⁻¹) := by group
          _ = (v * z) * (u * z) := by rw [hv'z, hau]
          _ = v * u * (z * z) := by
              rw [show v * z * (u * z) = v * (z * u) * z by group, hzu]
              group
          _ = v * u := by rw [hzz, mul_one]
      calc (v * u) * a = a * (v * u) * a⁻¹ * a := by rw [this]
        _ = a * (v * u) := by group
    have ht2 : (v * u) ^ 2 = 1 := by
      rw [pow_two]
      calc v * u * (v * u) = v * (u * v) * u := by group
        _ = v * (v * u) * u := by rw [hvu]
        _ = (v * v) * (u * u) := by group
        _ = 1 := by rw [hvv, huu, one_mul]
    have htS : v * u ∈ S := S.mul_mem hvS huS
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    rcases hone (v * u) htS ht2 (hcentral _ htS hta htc) with h | h
    · right; right; left
      calc v = v * u * u⁻¹ := by group
        _ = u := by rw [h, one_mul, huinv]
    · right; right; right
      calc v = v * u * u⁻¹ := by group
        _ = z * u := by rw [h, huinv]
        _ = u * z := hzu

theorem three_dvd_orderOf_of_cycle {w z u : G} (hz : w * z * w⁻¹ = u)
    (hu : w * u * w⁻¹ = u * z) (hcomm : z * u = u * z) (huu : u * u = 1) (hzu : u ≠ z)
    (huz : u * z ≠ z) : 3 ∣ orderOf w := by
  have h3 : w ^ 3 * z * (w ^ 3)⁻¹ = z := by
    calc w ^ 3 * z * (w ^ 3)⁻¹ = w * (w * (w * z * w⁻¹) * w⁻¹) * w⁻¹ := by
          rw [pow_succ, pow_two]; group
      _ = w * (w * u * w⁻¹) * w⁻¹ := by rw [hz]
      _ = w * (u * z) * w⁻¹ := by rw [hu]
      _ = (w * u * w⁻¹) * (w * z * w⁻¹) := by group
      _ = (u * z) * u := by rw [hu, hz]
      _ = u * (u * z) := by rw [mul_assoc, hcomm]
      _ = z := by rw [← mul_assoc, huu, one_mul]
  have hk : ∀ k : ℕ, (w ^ 3) ^ k * z * ((w ^ 3) ^ k)⁻¹ = z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (w ^ 3) ^ (k + 1) * z * ((w ^ 3) ^ (k + 1))⁻¹ =
          (w ^ 3) ^ k * (w ^ 3 * z * (w ^ 3)⁻¹) * ((w ^ 3) ^ k)⁻¹ := by group
        _ = z := by rw [h3, ih]
  set n := orderOf w with hn
  have hwn : w ^ n = 1 := pow_orderOf_eq_one w
  have hsplit : w ^ (n % 3) * z * (w ^ (n % 3))⁻¹ = z := by
    have hdec : w ^ n = w ^ (n % 3) * (w ^ 3) ^ (n / 3) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    have hy : w ^ (n % 3) = ((w ^ 3) ^ (n / 3))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hdec, hwn]
    have := hk (n / 3)
    rw [hy, inv_inv]
    calc ((w ^ 3) ^ (n / 3))⁻¹ * z * (w ^ 3) ^ (n / 3)
        = ((w ^ 3) ^ (n / 3))⁻¹ * ((w ^ 3) ^ (n / 3) * z * ((w ^ 3) ^ (n / 3))⁻¹) *
            (w ^ 3) ^ (n / 3) := by rw [this]
      _ = z := by group
  have hmod : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases hr : n % 3
  · exact Nat.dvd_of_mod_eq_zero hr
  · exfalso
    rw [pow_one, hz] at hsplit
    exact hzu hsplit
  · exfalso
    have : w ^ 2 * z * (w ^ 2)⁻¹ = u * z := by
      rw [show w ^ 2 * z * (w ^ 2)⁻¹ = w * (w * z * w⁻¹) * w⁻¹ by rw [pow_two]; group, hz, hu]
    rw [this] at hsplit
    exact huz hsplit

theorem mem_smul_sylow_iff {q : ℕ} {S : Sylow q G} {c x : G} :
    x ∈ ((c • S : Sylow q G) : Subgroup G) ↔ c⁻¹ * x * c ∈ (S : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [mul_assoc]

theorem atMostOneCentralInvolution_of_sylow [Finite G] {S : Sylow 2 G}
    (h : AtMostOneCentralInvolution (S : Subgroup G)) (S' : Sylow 2 G) :
    AtMostOneCentralInvolution (S' : Subgroup G) := by
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq G S S'
  intro z₁ hz₁ z₂ hz₂ ho₁ ho₂ hc₁ hc₂
  have hc : ∀ z, (∀ s ∈ ((c • S : Sylow 2 G) : Subgroup G), z * s = s * z) →
      ∀ s ∈ (S : Subgroup G), (c⁻¹ * z * c) * s = s * (c⁻¹ * z * c) := by
    intro z hz s hs
    have hs' : c * s * c⁻¹ ∈ ((c • S : Sylow 2 G) : Subgroup G) := by
      rw [mem_smul_sylow_iff]
      simpa [mul_assoc] using hs
    have := hz _ hs'
    calc c⁻¹ * z * c * s = c⁻¹ * (z * (c * s * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * s * c⁻¹) * z) * c := by rw [this]
      _ = s * (c⁻¹ * z * c) := by group
  have := h _ (mem_smul_sylow_iff.mp hz₁) _ (mem_smul_sylow_iff.mp hz₂)
    (by rw [orderOf_conj', ho₁]) (by rw [orderOf_conj', ho₂]) (hc z₁ hc₁) (hc z₂ hc₂)
  simpa using this

end Group

end CFSG.GH74.Uniqueness.Hering
