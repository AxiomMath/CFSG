module

public import CFSG.ClassicalInvolution.Q3.Sec13End15B
public import CFSG.ClassicalInvolution.Q3.Sec13End15D
import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8
import CFSG.ClassicalInvolution.Q3.TL4SepTwoD

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]


private theorem e15c_comm_of_unique {R : Subgroup G} {t : G} (ht : IsUniqueInvolution R t)
    {r : G} (hr : r ∈ R) : r * t = t * r := by
  have hm : r * t * r⁻¹ ∈ R := R.mul_mem (R.mul_mem hr ht.mem) (R.inv_mem hr)
  have hsq : (r * t * r⁻¹) * (r * t * r⁻¹) = 1 := by
    calc (r * t * r⁻¹) * (r * t * r⁻¹) = r * (t * t) * r⁻¹ := by group
      _ = 1 := by rw [ht.sq]; group
  have hc : r * t * r⁻¹ = t := by
    rcases ht.unique _ hm hsq with h1 | h1
    · exfalso
      apply ht.ne_one
      calc t = r⁻¹ * (r * t * r⁻¹) * r := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  calc r * t = (r * t * r⁻¹) * r := by group
    _ = t * r := by rw [hc]

private theorem e15c_mem_sup {K V : Subgroup G} (hV : V ≤ Subgroup.normalizer (K : Set G))
    {x : G} (hx : x ∈ K ⊔ V) : ∃ k ∈ K, ∃ v ∈ V, x = k * v := by
  let S : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ v ∈ V, x = k * v}
      one_mem' := ⟨1, K.one_mem, 1, V.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k, hk, v, hv, rfl⟩ ⟨k', hk', v', hv', rfl⟩
        exact ⟨k * (v * k' * v⁻¹),
          K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hV hv) k').mp hk'),
          v * v', V.mul_mem hv hv', by group⟩
      inv_mem' := by
        rintro _ ⟨k, hk, v, hv, rfl⟩
        exact ⟨v⁻¹ * k⁻¹ * v⁻¹⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hV (V.inv_mem hv)) k⁻¹).mp (K.inv_mem hk),
          v⁻¹, V.inv_mem hv, by group⟩ }
  have hle : K ⊔ V ≤ S :=
    sup_le (fun k hk => ⟨k, hk, 1, V.one_mem, by simp⟩) (fun v hv => ⟨1, K.one_mem, v, hv, by simp⟩)
  exact hle hx

private theorem e15c_mem_normalizer_of_mem_centralizer {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.centralizer (K : Set G)) : a ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have hc := Subgroup.mem_centralizer_iff.mp ha g hg
    have e : a * g * a⁻¹ = g := by rw [← hc]; group
    rw [e]
    exact hg
  · intro hg
    have hc := Subgroup.mem_centralizer_iff.mp ha (a * g * a⁻¹) hg
    have e1 : g = a⁻¹ * (a * g * a⁻¹) * a := by group
    have e2 : a⁻¹ * (a * g * a⁻¹) * a = a * g * a⁻¹ := by
      calc a⁻¹ * (a * g * a⁻¹) * a = a⁻¹ * ((a * g * a⁻¹) * a) := by group
        _ = a⁻¹ * (a * (a * g * a⁻¹)) := by rw [hc]
        _ = a * g * a⁻¹ := by group
    have hX : a⁻¹ * (a * g * a⁻¹) * a ∈ K := by rw [e2]; exact hg
    rw [e1]
    exact hX

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

private theorem e15c_pow4 {K : Subgroup G} {z i j : G} (hK : IsUniqueInvolution K z) (hi : i ∈ K)
    (hj : j ∈ K) (hii : i * i = z) (hjj : j * j = z) (hji : j * i = z * (i * j))
    (hnf : ∀ x ∈ K, x = 1 ∨ x = z ∨ x = i ∨ x = z * i ∨ x = j ∨ x = z * j ∨ x = i * j ∨
      x = z * (i * j)) : ∀ k ∈ K, k * k * (k * k) = 1 := by
  have hzc : ∀ x ∈ K, z * x = x * z := fun x hx => (e15c_comm_of_unique hK hx).symm
  have hzz : z * z = 1 := hK.sq
  have hij2 : (i * j) * (i * j) = z := by
    calc (i * j) * (i * j) = i * (j * i) * j := by group
      _ = i * (z * (i * j)) * j := by rw [hji]
      _ = (i * z) * (i * j) * j := by group
      _ = (z * i) * (i * j) * j := by rw [← hzc i hi]
      _ = z * (i * i) * (j * j) := by group
      _ = z := by rw [hii, hjj, hzz, one_mul]
  have hsq : ∀ k ∈ K, k * k = 1 ∨ k * k = z := by
    intro k hk
    rcases hnf k hk with h | h | h | h | h | h | h | h <;> rw [h]
    · left; exact one_mul 1
    · left; exact hzz
    · right; exact hii
    · right
      calc z * i * (z * i) = z * (i * z) * i := by group
        _ = z * (z * i) * i := by rw [← hzc i hi]
        _ = (z * z) * (i * i) := by group
        _ = z := by rw [hzz, hii, one_mul]
    · right; exact hjj
    · right
      calc z * j * (z * j) = z * (j * z) * j := by group
        _ = z * (z * j) * j := by rw [← hzc j hj]
        _ = (z * z) * (j * j) := by group
        _ = z := by rw [hzz, hjj, one_mul]
    · right; exact hij2
    · right
      have hX : i * j ∈ K := K.mul_mem hi hj
      calc z * (i * j) * (z * (i * j)) = z * ((i * j) * z) * (i * j) := by group
        _ = z * (z * (i * j)) * (i * j) := by rw [← hzc (i * j) hX]
        _ = (z * z) * ((i * j) * (i * j)) := by group
        _ = z := by rw [hzz, hij2, one_mul]
  intro k hk
  rcases hsq k hk with h1 | h1
  · rw [h1, one_mul]
  · rw [h1, hzz]

private theorem e15c_not_semidihedral {K : Subgroup G} {a : G}
    (hK4 : ∀ k ∈ K, k * k * (k * k) = 1) (haK : a ∈ Subgroup.centralizer (K : Set G))
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hSD : IsSemidihedral (K ⊔ Subgroup.zpowers a)) : False := by
  have hVN : Subgroup.zpowers a ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr (e15c_mem_normalizer_of_mem_centralizer haK)
  have hakc : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp haK k hk).symm
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hP4 : ∀ p ∈ K ⊔ Subgroup.zpowers a, p * p * (p * p) = 1 := by
    intro p hp
    obtain ⟨k, hk, v, hv, rfl⟩ := e15c_mem_sup hVN hp
    have hv' : v = 1 ∨ v = a := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hv
      rw [← hn, ← zpow_mod_orderOf, hord]
      rcases Int.emod_two_eq_zero_or_one n with h1 | h1
      · left
        simp [h1]
      · right
        simp [h1]
    rcases hv' with h1 | h1
    · rw [h1, mul_one]
      exact hK4 k hk
    · have hkk : k * a * (k * a) = k * k := by
        calc k * a * (k * a) = k * (a * k) * a := by group
          _ = k * (k * a) * a := by rw [hakc k hk]
          _ = k * k * (a * a) := by group
          _ = k * k := by rw [ha2, mul_one]
      rw [h1, hkk]
      exact hK4 k hk
  obtain ⟨a', b', ha8, -, -, -, -, hgen⟩ := hSD
  have ha'P : a' ∈ K ⊔ Subgroup.zpowers a := by
    rw [← hgen]
    exact Subgroup.subset_closure (by simp)
  have h4 : a' ^ 4 = 1 := by
    rw [show a' ^ 4 = a' * a' * (a' * a') by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
    exact hP4 a' ha'P
  have hle := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h4)
  omega

private theorem e15c_odd_eq_sq_pow {y : G} (hy : Odd (orderOf y)) :
    y = (y * y) ^ ((orderOf y + 1) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k, (orderOf y + 1) / 2 = k := ⟨_, rfl⟩
  rw [hk]
  have h2 : orderOf y + 1 = 2 * k := by
    obtain ⟨m, hm⟩ := hy
    omega
  calc y = y ^ (orderOf y + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
    _ = (y * y) ^ k := by rw [h2, pow_mul, pow_two]

private theorem e15c_commute_of_sq {y x : G} (hy : Odd (orderOf y)) (h : y * y * x = x * (y * y)) :
    y * x = x * y := by
  have hc : Commute (y * y) x := h
  have hc' : Commute ((y * y) ^ ((orderOf y + 1) / 2)) x := hc.pow_left _
  rw [← e15c_odd_eq_sq_pow hy] at hc'
  exact hc'

private theorem e15c_odd_comm_cyclic {U : Subgroup G} (hcyc : IsCyclic U) (h4 : Nat.card U = 4)
    {y : G} (hy : Odd (orderOf y)) (hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    ∀ u ∈ U, y * u = u * y := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgU : (g : G) ∈ U := g.2
  have hgorder : orderOf (g : G) = 4 := by
    rw [orderOf_submonoid, orderOf_eq_card_of_forall_mem_zpowers hg, h4]
  have hgen : ∀ u ∈ U, ∃ k : ℤ, (g : G) ^ k = u := by
    intro u hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨u, hu⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hg4 : (g : G) ^ 4 = 1 := by rw [← hgorder]; exact pow_orderOf_eq_one _
  obtain ⟨k, hk⟩ := hgen _ (hyU _ hgU)
  have hk4 : y * (g : G) * y⁻¹ = (g : G) ^ (k % 4) := by
    have e4 := zpow_mod_orderOf (g : G) k
    rw [hgorder] at e4
    norm_num at e4
    rw [e4, hk]
  have hcomm : y * (g : G) = (g : G) * y := by
    have hr : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hr with h0 | h1 | h2 | h3
    · exfalso
      rw [h0, zpow_zero] at hk4
      have : (g : G) = 1 := by
        calc (g : G) = y⁻¹ * (y * (g : G) * y⁻¹) * y := by group
          _ = 1 := by rw [hk4]; group
      rw [this, orderOf_one] at hgorder
      norm_num at hgorder
    · rw [h1, zpow_one] at hk4
      calc y * (g : G) = (y * (g : G) * y⁻¹) * y := by group
        _ = (g : G) * y := by rw [hk4]
    · exfalso
      rw [h2, zpow_ofNat] at hk4
      have e : y * (g : G) ^ 2 * y⁻¹ = (y * (g : G) * y⁻¹) ^ 2 := by
        rw [pow_two, pow_two]; group
      have h4' : ((g : G) ^ 2) ^ 2 = 1 := by
        calc ((g : G) ^ 2) ^ 2 = (g : G) ^ 4 := by rw [← pow_mul]
          _ = 1 := hg4
      have hsq : (g : G) ^ 2 = 1 := by
        have h5 : y * (g : G) ^ 2 * y⁻¹ = 1 := by rw [e, hk4, h4']
        calc (g : G) ^ 2 = y⁻¹ * (y * (g : G) ^ 2 * y⁻¹) * y := by group
          _ = 1 := by rw [h5]; group
      have hd := orderOf_dvd_of_pow_eq_one hsq
      rw [hgorder] at hd
      norm_num at hd
    ·
      rw [h3, zpow_ofNat] at hk4
      have hyg : y * (g : G) = (g : G) ^ 3 * y := by
        calc y * (g : G) = (y * (g : G) * y⁻¹) * y := by group
          _ = (g : G) ^ 3 * y := by rw [hk4]
      have hyg3 : y * (g : G) ^ 3 = (g : G) ^ 9 * y := by
        calc y * (g : G) ^ 3 = (y * (g : G)) * (g : G) ^ 2 := by group
          _ = ((g : G) ^ 3 * y) * (g : G) ^ 2 := by rw [hyg]
          _ = (g : G) ^ 3 * (y * (g : G)) * (g : G) := by rw [pow_two]; group
          _ = (g : G) ^ 3 * ((g : G) ^ 3 * y) * (g : G) := by rw [hyg]
          _ = (g : G) ^ 6 * (y * (g : G)) := by group
          _ = (g : G) ^ 6 * ((g : G) ^ 3 * y) := by rw [hyg]
          _ = (g : G) ^ 9 * y := by group
      have h9 : (g : G) ^ 9 = (g : G) := by
        calc (g : G) ^ 9 = ((g : G) ^ 4) ^ 2 * (g : G) := by group
          _ = (g : G) := by rw [hg4, one_pow, one_mul]
      have hyy : y * y * (g : G) = (g : G) * (y * y) := by
        calc y * y * (g : G) = y * (y * (g : G)) := by group
          _ = y * ((g : G) ^ 3 * y) := by rw [hyg]
          _ = (y * (g : G) ^ 3) * y := by group
          _ = ((g : G) ^ 9 * y) * y := by rw [hyg3]
          _ = (g : G) ^ 9 * (y * y) := by group
          _ = (g : G) * (y * y) := by rw [h9]
      have hyc := e15c_commute_of_sq hy hyy
      have hfix : y * (g : G) * y⁻¹ = (g : G) := by
        rw [hyc]; group
      rw [hfix] at hk4
      exfalso
      have hsq : (g : G) ^ 2 = 1 := by
        calc (g : G) ^ 2 = (g : G) ^ 3 * (g : G)⁻¹ := by group
          _ = (g : G) * (g : G)⁻¹ := by rw [← hk4]
          _ = 1 := by group
      have hd := orderOf_dvd_of_pow_eq_one hsq
      rw [hgorder] at hd
      norm_num at hd
  intro u hu
  obtain ⟨j, rfl⟩ := hgen u hu
  exact (Commute.zpow_right (show Commute y (g : G) from hcomm) j).eq

private theorem e15c_odd_normalizes (h : EndHyp Ω) {L L' : Subgroup G} (hL : L ∈ Ω)
    (hLL' : L' ≠ L) (htw : twinSet Ω L = {L, L'}) {y : G} (hy : Odd (orderOf y))
    (hyL : conjSub y L ∈ twinSet Ω L) : y ∈ Subgroup.normalizer (L : Set G) := by
  have hΩc := h.thmD.hyp.conjInvariant
  have hL'tw : L' ∈ twinSet Ω L := by
    rw [htw]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  rw [htw, Set.mem_insert_iff, Set.mem_singleton_iff] at hyL
  rcases hyL with hc | hc
  · exact mem_normalizer_iff_conjSub_eq.mpr hc
  · exfalso
    obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hL
    have hL'z : twinSet Ω L' = twinSet Ω L := Asc77.twinSet_eq_of_mem_twinSet hw hL'tw
    have h1 : conjSub y L' ∈ twinSet Ω L := by
      have := twinSet_conj hΩc hL'tw y
      rw [hc, hL'z] at this
      exact this
    rw [htw, Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    have hne : conjSub y L' ≠ L' := fun e =>
      hLL' (conjSub_injective y (e.trans hc.symm))
    have hL2 : conjSub y L' = L := h1.resolve_right hne
    have hyy : y * y ∈ Subgroup.normalizer (L : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, hc]
      exact hL2
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := by
      rw [e15c_odd_eq_sq_pow hy]
      exact Subgroup.pow_mem _ hyy _
    have := mem_normalizer_iff_conjSub_eq.mp hyN
    rw [this] at hc
    exact hLL' hc.symm

private theorem e15c_q8_ij_sq {M : Subgroup G} {z i j : G} (hQ : Q8Data M z i j) :
    (i * j) * (i * j) = z := by
  obtain ⟨hz, hi, -, hii, hjj, hji, -⟩ := hQ
  have hzi : z * i = i * z := (e15c_comm_of_unique hz hi).symm
  calc (i * j) * (i * j) = i * (j * i) * j := by group
    _ = i * (z * (i * j)) * j := by rw [hji]
    _ = (i * z) * (i * j) * j := by group
    _ = (z * i) * (i * j) * j := by rw [hzi]
    _ = z * (i * i) * (j * j) := by group
    _ = z := by rw [hii, hjj, hz.sq, one_mul]

private theorem e15c_comm_of_class {z : G} (hz1 : z ≠ 1) (hz2 : z * z = 1) {c g : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hodd : Odd (orderOf c))
    (hcg : c * g * c⁻¹ = g ∨ c * g * c⁻¹ = z * g) : c * g = g * c := by
  have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hc z (Set.mem_singleton z)).symm
  rcases hcg with h1 | h1
  · calc c * g = (c * g * c⁻¹) * c := by group
      _ = g * c := by rw [h1]
  · exfalso
    have hczc : c * z * c⁻¹ = z := by rw [hcz]; group
    have e : c * c * g * (c * c)⁻¹ = g := by
      calc c * c * g * (c * c)⁻¹ = c * (c * g * c⁻¹) * c⁻¹ := by group
        _ = c * (z * g) * c⁻¹ := by rw [h1]
        _ = (c * z * c⁻¹) * (c * g * c⁻¹) := by group
        _ = (c * z * c⁻¹) * (z * g) := by rw [h1]
        _ = z * (z * g) := by rw [hczc]
        _ = g := by rw [← mul_assoc, hz2, one_mul]
    have hcc : (c * c) * g = g * (c * c) := by
      calc (c * c) * g = (c * c * g * (c * c)⁻¹) * (c * c) := by group
        _ = g * (c * c) := by rw [e]
    have hcg' : c * g = g * c := e15c_commute_of_sq hodd hcc
    have hfix : c * g * c⁻¹ = g := by rw [hcg']; group
    rw [hfix] at h1
    exact hz1 (mul_right_cancel (by rw [one_mul]; exact h1.symm))

private theorem e15c_q8_class {M : Subgroup G} {z i j : G} (hQ : Q8Data M z i j) {w : G}
    (hw : w ∈ M) (hww : w * w = z) :
    ({w, z * w} : Set G) = {i, z * i} ∨ ({w, z * w} : Set G) = {j, z * j} ∨
      ({w, z * w} : Set G) = {i * j, z * (i * j)} := by
  have hz1 := hQ.inv.ne_one
  have hz2 := hQ.inv.sq
  rcases hQ.nf w hw with h | h | h | h | h | h | h | h
  · exfalso
    apply hz1
    rw [h, one_mul] at hww
    exact hww.symm
  · exfalso
    apply hz1
    rw [h] at hww
    rw [hz2] at hww
    exact hww.symm
  · left
    rw [h]
  · left
    rw [h, ← mul_assoc, hz2, one_mul, Set.pair_comm]
  · right; left
    rw [h]
  · right; left
    rw [h, ← mul_assoc, hz2, one_mul, Set.pair_comm]
  · right; right
    rw [h]
  · right; right
    rw [h, ← mul_assoc z z, hz2, one_mul, Set.pair_comm]

private theorem e15c_class_fix {M : Subgroup G} {z i j : G} (hQ : Q8Data M z i j) {y g : G}
    (hyz : y ∈ Subgroup.centralizer ({z} : Set G)) (hyM : y ∈ Subgroup.normalizer (M : Set G))
    (hg : g ∈ M) (hg2 : g * g = z) :
    ∃ d ∈ ({1, 2, 3} : Finset ℕ), y ^ d * g * (y ^ d)⁻¹ = g ∨ y ^ d * g * (y ^ d)⁻¹ = z * g := by
  classical
  have hz1 := hQ.inv.ne_one
  have hz2 := hQ.inv.sq
  let f : ℕ → Set G := fun m => {y ^ m * g * (y ^ m)⁻¹, z * (y ^ m * g * (y ^ m)⁻¹)}
  let 𝒜 : Finset (Set G) := {{i, z * i}, {j, z * j}, {i * j, z * (i * j)}}
  have hmaps : ∀ m ∈ Finset.range 4, f m ∈ 𝒜 := by
    intro m _
    have hcm : y ^ m ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.pow_mem _ hyz m
    have hwM : y ^ m * g * (y ^ m)⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyM m) g).mp hg
    have hzc : z * y ^ m = y ^ m * z := Subgroup.mem_centralizer_iff.mp hcm z (Set.mem_singleton z)
    have hww : (y ^ m * g * (y ^ m)⁻¹) * (y ^ m * g * (y ^ m)⁻¹) = z := by
      calc (y ^ m * g * (y ^ m)⁻¹) * (y ^ m * g * (y ^ m)⁻¹) = y ^ m * (g * g) * (y ^ m)⁻¹ := by
            group
        _ = y ^ m * z * (y ^ m)⁻¹ := by rw [hg2]
        _ = z := by rw [← hzc]; group
    have hcl := e15c_q8_class hQ hwM hww
    simp only [𝒜, f, Finset.mem_insert, Finset.mem_singleton]
    exact hcl
  have hcard : 𝒜.card < (Finset.range 4).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Finset.card_le_three (by norm_num)
  obtain ⟨a, ha, b, hb, hab, hfab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have step : ∀ a b : ℕ, a < b → b < 4 → f a = f b → ∃ d ∈ ({1, 2, 3} : Finset ℕ),
      y ^ d * g * (y ^ d)⁻¹ = g ∨ y ^ d * g * (y ^ d)⁻¹ = z * g := by
    intro a b hab hb4 hfab
    have hmem : y ^ b * g * (y ^ b)⁻¹ ∈ f b := Set.mem_insert _ _
    rw [← hfab] at hmem
    have hyc : z * y ^ a = y ^ a * z := Subgroup.mem_centralizer_iff.mp
      (Subgroup.pow_mem _ hyz a) z (Set.mem_singleton z)
    have hzc' : (y ^ a)⁻¹ * z * y ^ a = z := by
      calc (y ^ a)⁻¹ * z * y ^ a = (y ^ a)⁻¹ * (z * y ^ a) := by group
        _ = (y ^ a)⁻¹ * (y ^ a * z) := by rw [hyc]
        _ = z := by group
    have hyb : y ^ b = y ^ a * y ^ (b - a) := by
      rw [← pow_add]
      congr 1
      omega
    have key : (y ^ (b - a)) * g * (y ^ (b - a))⁻¹ =
        (y ^ a)⁻¹ * (y ^ b * g * (y ^ b)⁻¹) * y ^ a := by
      rw [hyb]
      group
    refine ⟨b - a, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · rcases Set.mem_insert_iff.mp hmem with h1 | h1
      · left
        rw [key, h1]
        group
      · right
        rw [Set.mem_singleton_iff] at h1
        rw [key, h1]
        calc (y ^ a)⁻¹ * (z * (y ^ a * g * (y ^ a)⁻¹)) * y ^ a
            = ((y ^ a)⁻¹ * z * y ^ a) * ((y ^ a)⁻¹ * (y ^ a * g * (y ^ a)⁻¹) * y ^ a) := by
              group
          _ = z * g := by rw [hzc']; group
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · exact step a b hlt (Finset.mem_range.mp hb) hfab
  · exact step b a hlt (Finset.mem_range.mp ha) hfab.symm

private theorem e15c_axis_comm {M : Subgroup G} {z i j : G} (hQ : Q8Data M z i j) {y g : G}
    (hyz : y ∈ Subgroup.centralizer ({z} : Set G)) (hyM : y ∈ Subgroup.normalizer (M : Set G))
    (hy : Odd (orderOf y)) (hg : g ∈ M) (hg2 : g * g = z) : y ^ 3 * g = g * y ^ 3 := by
  have hz1 := hQ.inv.ne_one
  have hz2 := hQ.inv.sq
  obtain ⟨d, hd, hcase⟩ := e15c_class_fix hQ hyz hyM hg hg2
  have hdodd : ∀ k : ℕ, Odd (orderOf (y ^ k)) := fun k => Odd.of_dvd_nat hy (orderOf_pow_dvd k)
  have hcomm_of : ∀ k : ℕ, y ^ k ∈ Subgroup.centralizer ({z} : Set G) :=
    fun k => Subgroup.pow_mem _ hyz k
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h1 | h1 | h1 <;> subst h1
  · have h1' : y * g = g * y := e15c_comm_of_class hz1 hz2 hyz hy (by simpa using hcase)
    exact (Commute.pow_left h1' 3).eq
  · have h2 : y ^ 2 * g = g * y ^ 2 := e15c_comm_of_class hz1 hz2 (hcomm_of 2) (hdodd 2) hcase
    have h2' : y * y * g = g * (y * y) := by rw [← pow_two]; exact h2
    have h1' : y * g = g * y := e15c_commute_of_sq hy h2'
    exact (Commute.pow_left h1' 3).eq
  · exact e15c_comm_of_class hz1 hz2 (hcomm_of 3) (hdodd 3) hcase

private theorem e15c_pow3_mem_centralizer {M : Subgroup G} {z i j : G} (hQ : Q8Data M z i j)
    {y : G} (hyz : y ∈ Subgroup.centralizer ({z} : Set G))
    (hyM : y ∈ Subgroup.normalizer (M : Set G)) (hy : Odd (orderOf y)) :
    y ^ 3 ∈ Subgroup.centralizer (M : Set G) := by
  have hi3 : y ^ 3 * i = i * y ^ 3 := e15c_axis_comm hQ hyz hyM hy hQ.mem_i hQ.sq_i
  have hj3 : y ^ 3 * j = j * y ^ 3 := e15c_axis_comm hQ hyz hyM hy hQ.mem_j hQ.sq_j
  have hz3 : z * y ^ 3 = y ^ 3 * z :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hyz 3) z (Set.mem_singleton z)
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have hmz : m ∈ M := hm
  rcases hQ.nf m hmz with h | h | h | h | h | h | h | h <;> rw [h]
  · simp
  · exact hz3
  · exact hi3.symm
  · calc z * i * y ^ 3 = z * (i * y ^ 3) := by group
      _ = z * (y ^ 3 * i) := by rw [hi3]
      _ = (z * y ^ 3) * i := by group
      _ = (y ^ 3 * z) * i := by rw [hz3]
      _ = y ^ 3 * (z * i) := by group
  · exact hj3.symm
  · calc z * j * y ^ 3 = z * (j * y ^ 3) := by group
      _ = z * (y ^ 3 * j) := by rw [hj3]
      _ = (z * y ^ 3) * j := by group
      _ = (y ^ 3 * z) * j := by rw [hz3]
      _ = y ^ 3 * (z * j) := by group
  · calc i * j * y ^ 3 = i * (j * y ^ 3) := by group
      _ = i * (y ^ 3 * j) := by rw [hj3]
      _ = (i * y ^ 3) * j := by group
      _ = (y ^ 3 * i) * j := by rw [hi3]
      _ = y ^ 3 * (i * j) := by group
  · calc z * (i * j) * y ^ 3 = z * ((i * j) * y ^ 3) := by group
      _ = z * (y ^ 3 * (i * j)) := by rw [show (i * j) * y ^ 3 = y ^ 3 * (i * j) from
          calc (i * j) * y ^ 3 = i * (j * y ^ 3) := by group
            _ = i * (y ^ 3 * j) := by rw [hj3]
            _ = (i * y ^ 3) * j := by group
            _ = (y ^ 3 * i) * j := by rw [hi3]
            _ = y ^ 3 * (i * j) := by group]
      _ = (z * y ^ 3) * (i * j) := by group
      _ = (y ^ 3 * z) * (i * j) := by rw [hz3]
      _ = y ^ 3 * (z * (i * j)) := by group

private theorem e15c_centralizes_E {A B E : Subgroup G} {z y : G} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hAB : Commutes A B) (hBN : B ≤ Subgroup.normalizer (A : Set G))
    (hEsub : E ≤ A ⊔ B) (hEN : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hwE : ∀ w ∈ B, w ∈ E → w = 1 ∨ w = z)
    (hyz : y ∈ Subgroup.centralizer ({z} : Set G)) (hyA : ∀ a ∈ A, y * a = a * y)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) (hy : Odd (orderOf y)) :
    ∀ e ∈ E, y * e = e * y := by
  intro e he
  have hyAc : y ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun a ha => (hyA a ha).symm)
  have hyAN : y ∈ Subgroup.normalizer (A : Set G) := e15c_mem_normalizer_of_mem_centralizer hyAc
  obtain ⟨a, ha, b, hb, rfl⟩ := e15c_mem_sup hBN (hEsub he)
  obtain ⟨w, hwdef⟩ : ∃ w, w = y * b * y⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hwB : w ∈ B := by
    rw [hwdef]
    exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp hyB b).mp hb) (B.inv_mem hb)
  have hyay : y * a * y⁻¹ = a := by rw [hyA a ha]; group
  have hkey : y * (a * b) * y⁻¹ * (a * b)⁻¹ = w := by
    calc y * (a * b) * y⁻¹ * (a * b)⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) * (a * b)⁻¹ := by group
      _ = a * (y * b * y⁻¹) * (a * b)⁻¹ := by rw [hyay]
      _ = a * ((y * b * y⁻¹) * b⁻¹) * a⁻¹ := by group
      _ = a * w * a⁻¹ := by rw [hwdef]
      _ = w := by rw [hAB a ha w hwB]; group
  have hwE' : w ∈ E := by
    rw [← hkey]
    exact E.mul_mem (hEN y hyAN (a * b) he) (E.inv_mem he)
  have he' : y * (a * b) * y⁻¹ = w * (a * b) := by
    calc y * (a * b) * y⁻¹ = (y * (a * b) * y⁻¹ * (a * b)⁻¹) * (a * b) := by group
      _ = w * (a * b) := by rw [hkey]
  have hw' : w = 1 ∨ w = z := hwE w hwB hwE'
  have hww : w * w = 1 := by
    rcases hw' with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, hz2]
  have hyw : y * w * y⁻¹ = w := by
    rcases hw' with h1 | h1
    · rw [h1]; group
    · rw [h1]
      have hc : z * y = y * z := Subgroup.mem_centralizer_iff.mp hyz z (Set.mem_singleton z)
      rw [← hc]
      group
  have hsq : y * y * (a * b) = (a * b) * (y * y) := by
    have h1 : y * (y * (a * b) * y⁻¹) * y⁻¹ = a * b := by
      calc y * (y * (a * b) * y⁻¹) * y⁻¹ = y * (w * (a * b)) * y⁻¹ := by rw [he']
        _ = (y * w * y⁻¹) * (y * (a * b) * y⁻¹) := by group
        _ = w * (w * (a * b)) := by rw [hyw, he']
        _ = (w * w) * (a * b) := by group
        _ = a * b := by rw [hww, one_mul]
    calc y * y * (a * b) = (y * (y * (a * b) * y⁻¹) * y⁻¹) * (y * y) := by group
      _ = (a * b) * (y * y) := by rw [h1]
  exact e15c_commute_of_sq hy hsq

private theorem e15c_comm_of_pow {M : Subgroup G} {y : G} {s : ℕ} (hs : ¬ 3 ∣ s)
    (h3 : y ^ 3 ∈ Subgroup.centralizer (M : Set G))
    (hs' : y ^ s ∈ Subgroup.centralizer (M : Set G)) :
    y ∈ Subgroup.centralizer (M : Set G) := by
  have hcop : Nat.Coprime 3 s := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hs
  have hbez : (3 : ℤ) * Nat.gcdA 3 s + (s : ℤ) * Nat.gcdB 3 s = 1 := by
    have h := Nat.gcd_eq_gcd_ab 3 s
    have hg1 : Nat.gcd 3 s = 1 := hcop
    rw [hg1] at h
    push_cast at h
    linarith
  rw [Subgroup.mem_centralizer_iff] at h3 hs' ⊢
  intro m hm
  have hc3 : Commute m (y ^ 3) := h3 m hm
  have hcs : Commute m (y ^ s) := hs' m hm
  have e1 : (y ^ 3) ^ (Nat.gcdA 3 s) = y ^ ((3 : ℤ) * Nat.gcdA 3 s) := by
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  have e2 : (y ^ s) ^ (Nat.gcdB 3 s) = y ^ ((s : ℤ) * Nat.gcdB 3 s) := by
    rw [← zpow_natCast, ← zpow_mul]
  have hyexp : y = (y ^ 3) ^ (Nat.gcdA 3 s) * (y ^ s) ^ (Nat.gcdB 3 s) := by
    rw [e1, e2, ← zpow_add, hbez, zpow_one]
  have hcomm : Commute m ((y ^ 3) ^ (Nat.gcdA 3 s) * (y ^ s) ^ (Nat.gcdB 3 s)) :=
    ((hc3.zpow_right _).mul_right (hcs.zpow_right _))
  rw [← hyexp] at hcomm
  exact hcomm.eq

private theorem e15c_fix_small {K : Subgroup G} {z : G} (hK : IsUniqueInvolution K z)
    (hK8 : Nat.card K = 8) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    {a : ℕ} (ha : x ^ 3 ^ a = 1) (hnc : ∃ k ∈ K, x * k ≠ k * x) {k : G} (hk : k ∈ K)
    (hxk : x * k = k * x) : k = 1 ∨ k = z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hx
  letI : MulAction (Subgroup.zpowers x) K :=
    { smul := fun h k => ⟨(h : G) * k * (h : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hH h.2) k).mp k.2⟩
      one_smul := fun k => Subtype.ext (by
        show ((1 : Subgroup.zpowers x) : G) * (k : G) * ((1 : Subgroup.zpowers x) : G)⁻¹ = (k : G)
        simp)
      mul_smul := fun h₁ h₂ k => Subtype.ext (by
        show ((h₁ * h₂ : Subgroup.zpowers x) : G) * (k : G) *
          ((h₁ * h₂ : Subgroup.zpowers x) : G)⁻¹ =
          ((h₁ : G) * ((h₂ : G) * (k : G) * (h₂ : G)⁻¹) * (h₁ : G)⁻¹)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group) }
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one ha)
  have hP : IsPGroup 3 (Subgroup.zpowers x) := IsPGroup.of_card (by rw [Nat.card_zpowers, hb])
  have hmod := hP.card_modEq_card_fixedPoints (α := K)
  have hfix : ∀ k' : K, k' ∈ MulAction.fixedPoints (Subgroup.zpowers x) K ↔
      x * (k' : G) = (k' : G) * x := by
    intro k'
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hf
      have h1 := hf ⟨x, Subgroup.mem_zpowers x⟩
      have h2 : x * (k' : G) * x⁻¹ = (k' : G) := congrArg Subtype.val h1
      calc x * (k' : G) = x * (k' : G) * x⁻¹ * x := by group
        _ = (k' : G) * x := by rw [h2]
    · intro hc h
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h.2
      apply Subtype.ext
      show (h : G) * (k' : G) * (h : G)⁻¹ = (k' : G)
      have hcomm : Commute (k' : G) (h : G) := by
        rw [← hm]
        exact Commute.zpow_right (show Commute (k' : G) x from hc.symm) m
      calc (h : G) * (k' : G) * (h : G)⁻¹ = (k' : G) * (h : G) * (h : G)⁻¹ := by
            rw [hcomm.eq]
        _ = (k' : G) := by group
  let F : Subgroup K :=
    { carrier := {k' | x * (k' : G) = (k' : G) * x}
      mul_mem' := fun {a b} ha hb => by
        show x * ((a : G) * (b : G)) = ((a : G) * (b : G)) * x
        calc x * ((a : G) * (b : G)) = (x * (a : G)) * (b : G) := by group
          _ = ((a : G) * x) * (b : G) := by rw [ha]
          _ = (a : G) * (x * (b : G)) := by group
          _ = (a : G) * ((b : G) * x) := by rw [hb]
          _ = ((a : G) * (b : G)) * x := by group
      one_mem' := by
        show x * ((1 : K) : G) = ((1 : K) : G) * x
        simp
      inv_mem' := fun {a} ha => by
        show x * (a : G)⁻¹ = (a : G)⁻¹ * x
        have ha' : (a : G) * x = x * (a : G) := ha.symm
        calc x * (a : G)⁻¹ = (a : G)⁻¹ * ((a : G) * x) * (a : G)⁻¹ := by group
          _ = (a : G)⁻¹ * (x * (a : G)) * (a : G)⁻¹ := by rw [ha']
          _ = (a : G)⁻¹ * x := by group }
  have hFcard : Nat.card F = Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) K) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun k' => (hfix k').symm)
  have hdvd : Nat.card F ∣ 2 ^ 3 := by
    have := Subgroup.card_subgroup_dvd_card F
    rw [hK8] at this
    simpa using this
  have hmod' : Nat.card F % 3 = 2 := by
    have h8 := hmod
    rw [hK8, ← hFcard] at h8
    unfold Nat.ModEq at h8
    omega
  obtain ⟨c, hc3, hcF⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hzx : x * z = z * x := by
    have := conj_eq_self_of_normalizer hK hx
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [this]
  have hzF : (⟨z, hK.mem⟩ : K) ∈ F := show x * z = z * x from hzx
  interval_cases c
  · norm_num at hcF
    rw [hcF] at hmod'
    norm_num at hmod'
  ·
    norm_num at hcF
    have hzZ : Subgroup.zpowers (⟨z, hK.mem⟩ : K) ≤ F := Subgroup.zpowers_le.mpr hzF
    have hord : orderOf (⟨z, hK.mem⟩ : K) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (by simpa using hK.sq)) (by
        intro e
        apply hK.ne_one
        simpa using congrArg Subtype.val e)
    have hZF : Subgroup.zpowers (⟨z, hK.mem⟩ : K) = F := by
      apply Subgroup.eq_of_le_of_card_ge hzZ
      rw [Nat.card_zpowers, hord, hcF]
    have hkF : (⟨k, hk⟩ : K) ∈ F := show x * k = k * x from hxk
    rw [← hZF] at hkF
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hkF
    have hkn : z ^ n = k := by
      have := congrArg Subtype.val hn
      simpa using this
    have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hK.sq) hK.ne_one
    rw [← hkn, ← zpow_mod_orderOf, hz2]
    rcases Int.emod_two_eq_zero_or_one n with h1 | h1
    · left; simp [h1]
    · right; simp [h1]
  · norm_num at hcF
    rw [hcF] at hmod'
    norm_num at hmod'
  ·
    exfalso
    norm_num at hcF
    have hFtop : F = ⊤ := Subgroup.eq_of_le_of_card_ge le_top (by simp [hK8, hcF])
    obtain ⟨k₀, hk₀, hne⟩ := hnc
    have hmem : (⟨k₀, hk₀⟩ : K) ∈ F := by rw [hFtop]; exact Subgroup.mem_top _
    exact hne (show x * k₀ = k₀ * x from hmem)

private theorem e15c_sq_K {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {w : G}
    (hw : w ∈ K) (hw1 : w ≠ 1) (hwz : w ≠ z) : w * w = z := by
  have hz2 := hQ.inv.sq
  have hzc : ∀ x ∈ K, z * x = x * z := fun x hx => (e15c_comm_of_unique hQ.inv hx).symm
  have hi := hQ.mem_i
  have hj := hQ.mem_j
  have hii := hQ.sq_i
  have hjj := hQ.sq_j
  rcases hQ.nf w hw with h | h | h | h | h | h | h | h
  · exact absurd h hw1
  · exact absurd h hwz
  · rw [h]; exact hii
  · rw [h]
    calc z * i * (z * i) = z * (i * z) * i := by group
      _ = z * (z * i) * i := by rw [← hzc i hi]
      _ = (z * z) * (i * i) := by group
      _ = z := by rw [hz2, hii, one_mul]
  · rw [h]; exact hjj
  · rw [h]
    calc z * j * (z * j) = z * (j * z) * j := by group
      _ = z * (z * j) * j := by rw [← hzc j hj]
      _ = (z * z) * (j * j) := by group
      _ = z := by rw [hz2, hjj, one_mul]
  · rw [h]; exact e15c_q8_ij_sq hQ
  · rw [h]
    have hX : i * j ∈ K := K.mul_mem hi hj
    calc z * (i * j) * (z * (i * j)) = z * ((i * j) * z) * (i * j) := by group
      _ = z * (z * (i * j)) * (i * j) := by rw [← hzc (i * j) hX]
      _ = (z * z) * ((i * j) * (i * j)) := by group
      _ = z := by rw [hz2, e15c_q8_ij_sq hQ, one_mul]

private theorem e15c_center_K {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {a : G}
    (ha : a ∈ K) (hac : ∀ k ∈ K, a * k = k * a) : a = 1 ∨ a = z := by
  have hz1 := hQ.inv.ne_one
  have hz2 := hQ.inv.sq
  have hi := hQ.mem_i
  have hj := hQ.mem_j
  have hii := hQ.sq_i
  have hjj := hQ.sq_j
  have hji := hQ.comm
  have hzc : ∀ x ∈ K, z * x = x * z := fun x hx => (e15c_comm_of_unique hQ.inv hx).symm
  have hnc : i * j ≠ j * i := by
    intro e
    apply hz1
    have h1 : (1 : G) * (i * j) = z * (i * j) := by rw [one_mul, ← hji]; exact e
    exact (mul_right_cancel h1).symm
  have hcomm_i_ij : i * (i * j) ≠ (i * j) * i := by
    intro e
    apply hz1
    have e2 : (i * j) * i = j := by
      calc (i * j) * i = i * (j * i) := by group
        _ = i * (z * (i * j)) := by rw [hji]
        _ = (i * z) * (i * j) := by group
        _ = (z * i) * (i * j) := by rw [← hzc i hi]
        _ = z * (i * (i * j)) := by group
        _ = z * (z * j) := by rw [← mul_assoc i i j, hii]
        _ = j := by rw [← mul_assoc, hz2, one_mul]
    have e3 : i * (i * j) = z * j := by rw [← mul_assoc, hii]
    have h5 : z * j = j := by rw [← e3]; exact e.trans e2
    exact mul_right_cancel (h5.trans (one_mul j).symm)
  rcases hQ.nf a ha with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    apply hnc
    have := hac j hj
    rw [h] at this
    exact this
  · exfalso
    apply hnc
    have := hac j hj
    rw [h] at this
    have h' : z * (i * j) = z * (j * i) := by
      calc z * (i * j) = z * i * j := by group
        _ = j * (z * i) := this
        _ = (j * z) * i := by group
        _ = (z * j) * i := by rw [← hzc j hj]
        _ = z * (j * i) := by group
    exact mul_left_cancel h'
  · exfalso
    apply hnc
    have := hac i hi
    rw [h] at this
    exact this.symm
  · exfalso
    apply hnc
    have := hac i hi
    rw [h] at this
    have h' : z * (j * i) = z * (i * j) := by
      calc z * (j * i) = (z * j) * i := by group
        _ = i * (z * j) := this
        _ = (i * z) * j := by group
        _ = (z * i) * j := by rw [← hzc i hi]
        _ = z * (i * j) := by group
    exact (mul_left_cancel h').symm
  · exfalso
    apply hcomm_i_ij
    have := hac i hi
    rw [h] at this
    exact this.symm
  · exfalso
    apply hcomm_i_ij
    have := hac i hi
    rw [h] at this
    have h' : z * ((i * j) * i) = z * (i * (i * j)) := by
      calc z * ((i * j) * i) = (z * (i * j)) * i := by group
        _ = i * (z * (i * j)) := this
        _ = (i * z) * (i * j) := by group
        _ = (z * i) * (i * j) := by rw [← hzc i hi]
        _ = z * (i * (i * j)) := by group
    exact (mul_left_cancel h').symm

private theorem e15c_P2 {K : Subgroup G} {z : G} (hK : IsUniqueInvolution K z)
    (hK8 : Nat.card K = 8) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    {a : ℕ} (ha : x ^ 3 ^ a = 1) (hnc : ∃ k ∈ K, x * k ≠ k * x) {k : G} (hk : k ∈ K)
    (hk1 : k ≠ 1) (hk2 : k ≠ z) : x * k * x⁻¹ ≠ k ∧ x * k * x⁻¹ ≠ z * k := by
  have hzx : x * z = z * x := by
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [conj_eq_self_of_normalizer hK hx]
  constructor
  · intro e
    have hxk : x * k = k * x := by
      calc x * k = (x * k * x⁻¹) * x := by group
        _ = k * x := by rw [e]
    rcases e15c_fix_small hK hK8 hx ha hnc hk hxk with h | h
    · exact hk1 h
    · exact hk2 h
  · intro e
    have e1 : x * k = z * k * x := by
      calc x * k = (x * k * x⁻¹) * x := by group
        _ = z * k * x := by rw [e]
    have hxx : x * x * k = k * (x * x) := by
      calc x * x * k = x * (x * k) := by group
        _ = x * (z * k * x) := by rw [e1]
        _ = (x * z) * (k * x) := by group
        _ = (z * x) * (k * x) := by rw [hzx]
        _ = z * (x * k) * x := by group
        _ = z * (z * k * x) * x := by rw [e1]
        _ = (z * z) * (k * x * x) := by group
        _ = k * (x * x) := by rw [hK.sq, one_mul]; group
    obtain ⟨c, hc⟩ : Odd (3 ^ a) := Odd.pow (by decide)
    have hm : 2 * ((3 ^ a + 1) / 2) = 3 ^ a + 1 := by omega
    have hxm : (x * x) ^ ((3 ^ a + 1) / 2) = x := by
      rw [← sq, ← pow_mul, hm, pow_succ', ha, mul_one]
    have hcomm1 : Commute ((x * x) ^ ((3 ^ a + 1) / 2)) k :=
      (show Commute (x * x) k from hxx).pow_left _
    rw [hxm] at hcomm1
    rcases e15c_fix_small hK hK8 hx ha hnc hk hcomm1.eq with h | h
    · exact hk1 h
    · exact hk2 h

private theorem e15c_cover_logic {X : Type} (S₁ S₂ S₃ A B C D : Set X)
    (hA : A = S₁ ∨ A = S₂ ∨ A = S₃) (hB : B = S₁ ∨ B = S₂ ∨ B = S₃)
    (hC : C = S₁ ∨ C = S₂ ∨ C = S₃) (hD : D = S₁ ∨ D = S₂ ∨ D = S₃)
    (hBA : B ≠ A) (hCB : C ≠ B) (hCA : C ≠ A) : D = A ∨ D = B ∨ D = C := by
  rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl <;>
    rcases hC with rfl | rfl | rfl <;> rcases hD with rfl | rfl | rfl <;> simp_all

private theorem e15c_E_inj {K K' E : Subgroup G} {z : G} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hAB : Commutes K K') (hzE : z ∈ E)
    (hwE : ∀ w ∈ K', w ∈ E → w = 1 ∨ w = z) {k b k' b' e e' : G} (hk : k ∈ K) (hb : b ∈ K')
    (hk' : k' ∈ K) (hb' : b' ∈ K') (he : e = k * b) (he' : e' = k' * b') (hE : e ∈ E)
    (hE' : e' ∈ E) (hkk : k' = k ∨ k' = z * k) : e' = e ∨ e' = z * e := by
  have hc : k' * k⁻¹ = 1 ∨ k' * k⁻¹ = z := by
    rcases hkk with h | h
    · left; rw [h]; group
    · right; rw [h]; group
  have hw : b' * b⁻¹ ∈ K' := K'.mul_mem hb' (K'.inv_mem hb)
  have hkw : k * (b' * b⁻¹) * k⁻¹ = b' * b⁻¹ := by
    have hc' := hAB k hk (b' * b⁻¹) hw
    calc k * (b' * b⁻¹) * k⁻¹ = (k * (b' * b⁻¹)) * k⁻¹ := rfl
      _ = ((b' * b⁻¹) * k) * k⁻¹ := by rw [hc']
      _ = b' * b⁻¹ := by group
  have hprod : e' * e⁻¹ = (k' * k⁻¹) * (b' * b⁻¹) := by
    rw [he, he']
    calc k' * b' * (k * b)⁻¹ = k' * (b' * b⁻¹) * k⁻¹ := by group
      _ = (k' * k⁻¹) * (k * (b' * b⁻¹) * k⁻¹) := by group
      _ = (k' * k⁻¹) * (b' * b⁻¹) := by rw [hkw]
  have hwE' : b' * b⁻¹ ∈ E := by
    have h1 : (k' * k⁻¹) * (b' * b⁻¹) ∈ E := by
      rw [← hprod]
      exact E.mul_mem hE' (E.inv_mem hE)
    have h2 : k' * k⁻¹ ∈ E := by
      rcases hc with h | h
      · rw [h]; exact E.one_mem
      · rw [h]; exact hzE
    have h3 := E.mul_mem (E.inv_mem h2) h1
    rwa [inv_mul_cancel_left] at h3
  have hw1 := hwE _ hw hwE'
  have hcw : e' * e⁻¹ = 1 ∨ e' * e⁻¹ = z := by
    rcases hc with h | h <;> rcases hw1 with h' | h' <;> simp [hprod, h, h', hz2]
  have he_eq : e' = (e' * e⁻¹) * e := by group
  rcases hcw with h | h
  · left
    rw [he_eq, h, one_mul]
  · right
    rw [he_eq, h]

private theorem e15c_conj_E {K K' E : Subgroup G} {z : G} (hAB : Commutes K K')
    (hKN : K' ≤ Subgroup.normalizer (K : Set G)) (hEsub : E ≤ K ⊔ K')
    (hEN : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hwE' : ∀ w ∈ K, w ∈ E → w = 1 ∨ w = z) {k e : G} (hk : k ∈ K) (he : e ∈ E) :
    k * e * k⁻¹ = e ∨ k * e * k⁻¹ = z * e := by
  obtain ⟨a, ha, b, hb, rfl⟩ := e15c_mem_sup hKN (hEsub he)
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
  have hbk : b * k⁻¹ * b⁻¹ = k⁻¹ := by
    have hbkb : b * k * b⁻¹ = k := by
      rw [← hAB k hk b hb]
      group
    calc b * k⁻¹ * b⁻¹ = (b * k * b⁻¹)⁻¹ := by group
      _ = k⁻¹ := by rw [hbkb]
  obtain ⟨w, hwdef⟩ : ∃ w, w = k * a * k⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have h1 : k * (a * b) * k⁻¹ * (a * b)⁻¹ = w := by
    rw [hwdef]
    calc k * (a * b) * k⁻¹ * (a * b)⁻¹ = k * a * (b * k⁻¹ * b⁻¹) * a⁻¹ := by group
      _ = k * a * k⁻¹ * a⁻¹ := by rw [hbk]
  have hwK : w ∈ K := by
    rw [hwdef]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk ha) (K.inv_mem hk)) (K.inv_mem ha)
  have hwE : w ∈ E := by
    rw [← h1]
    exact E.mul_mem (hEN k hkN (a * b) he) (E.inv_mem he)
  have hkey : k * (a * b) * k⁻¹ = w * (a * b) := by
    calc k * (a * b) * k⁻¹ = (k * (a * b) * k⁻¹ * (a * b)⁻¹) * (a * b) := by group
      _ = w * (a * b) := by rw [h1]
  rcases hwE' w hwK hwE with h | h
  · left
    rw [hkey, h, one_mul]
  · right
    rw [hkey, h]

private theorem e15c_E_noncomm {K K' E : Subgroup G} {z i j : G} (hQ : Q8Data K z i j)
    (hAB : Commutes K K') (hKN : K' ≤ Subgroup.normalizer (K : Set G)) (hEsub : E ≤ K ⊔ K')
    (hwE : ∀ w ∈ K', w ∈ E → w = 1 ∨ w = z) (hzE : z ∈ E) {e : G} (he : e ∈ E)
    (he1 : e ≠ 1) (he2 : e ≠ z) : ∃ k ∈ K, e * k ≠ k * e := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, ha, b, hb, rfl⟩ := e15c_mem_sup hKN (hEsub he)
  have hac : ∀ k ∈ K, a * k = k * a := by
    intro k hk
    have hbkb : b * k * b⁻¹ = k := by
      rw [← hAB k hk b hb]
      group
    calc a * k = a * (b * k * b⁻¹) := by rw [hbkb]
      _ = a * b * k * b⁻¹ := by group
      _ = k * (a * b) * b⁻¹ := by rw [hcon k hk]
      _ = k * a := by group
  have hA := e15c_center_K hQ ha hac
  have haE : a⁻¹ ∈ E := by
    rcases hA with h | h
    · rw [h, inv_one]
      exact E.one_mem
    · rw [h]
      exact E.inv_mem hzE
  have hbE : b ∈ E := by
    have hb' : b = a⁻¹ * (a * b) := by group
    rw [hb']
    exact E.mul_mem haE he
  have hbz := hwE b hb hbE
  rcases hA with h1 | h1 <;> rcases hbz with h2 | h2 <;> simp_all [hQ.inv.sq]

private theorem e15c_conj_one_or_z {K : Subgroup G} {z : G} (hK : IsUniqueInvolution K z)
    {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) {k c : G} (hck : x * k * x⁻¹ = c)
    (hc : c = 1 ∨ c = z) : k = 1 ∨ k = z := by
  have hxz : x * z = z * x := by
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [conj_eq_self_of_normalizer hK hx]
  have hk' : k = x⁻¹ * c * x := by
    rw [← hck]
    group
  rcases hc with h | h
  · left
    rw [hk', h]
    group
  · right
    rw [hk', h]
    calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
      _ = x⁻¹ * (x * z) := by rw [hxz]
      _ = z := by group

private theorem e15c_zG_conj {z f k : G} (hf : ∃ g : G, f = g * z * g⁻¹) :
    ∃ g : G, k * f * k⁻¹ = g * z * g⁻¹ := by
  obtain ⟨g, rfl⟩ := hf
  exact ⟨k * g, by group⟩

private theorem e15c_card_RSet (h : EndHyp Ω) {R : Subgroup G} (hR : R ∈ RSet Ω) :
    Nat.card R = 8 := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJR : J = R := hRJ.2.2 J le_rfl (h.thmD.two J hJ) hRJ.1
  rw [← hJR]
  exact h.card_eq_eight hJ

private theorem e15c_not_wreathed {K V R : Subgroup G} {z a : G} (hK : IsUniqueInvolution K z)
    (hR : IsUniqueInvolution R a) (hVR : V ≤ R) (haV : a ∈ V)
    (haK : a ∈ Subgroup.centralizer (K : Set G)) (hVN : V ≤ Subgroup.normalizer (K : Set G))
    (hV4 : Nat.card V = 4) (hza : a ≠ z) {i j : G} (hi : i ∈ K) (hj : j ∈ K)
    (hij : i * j ≠ j * i) (hW : IsWreathed (K ⊔ V)) : False := by
  have haK' : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp haK k hk).symm
  have hzK : ∀ k ∈ K, z * k = k * z := fun k hk => (e15c_comm_of_unique hK hk).symm
  have hzV : ∀ v ∈ V, z * v = v * z := by
    intro v hv
    have hc := hK.conj v
    rw [mem_normalizer_iff_conjSub_eq.mp (hVN hv)] at hc
    have e : v * z * v⁻¹ = z := (hK.eq hc).symm
    calc z * v = (v * z * v⁻¹) * v := by rw [e]
      _ = v * z := by group
  have haV' : ∀ v ∈ V, a * v = v * a := fun v hv => (e15c_comm_of_unique hR (hVR hv)).symm
  have hv4 : ∀ v ∈ V, v * v * (v * v) = 1 := by
    intro v hv
    have h1 := orderOf_dvd_natCard (⟨v, hv⟩ : ↥V)
    rw [hV4] at h1
    have h2 : (⟨v, hv⟩ : ↥V) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
    calc v * v * (v * v) = v ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h3
  have hsq : ∀ v ∈ V, v ≠ 1 → v ≠ a → v * v = a := by
    intro v hv hv1 hva
    have hvR : v ∈ R := hVR hv
    rcases hR.unique (v * v) (R.mul_mem hvR hvR) (hv4 v hv) with h1 | h1
    · rcases hR.unique v hvR h1 with h2 | h2
      · exact absurd h2 hv1
      · exact absurd h2 hva
    · exact h1
  have hinv : ∀ p ∈ K ⊔ V, p * p = 1 → p = 1 ∨ p = z ∨ p = a ∨ p = z * a := by
    intro p hp hpp
    obtain ⟨k, hk, v, hv, rfl⟩ := e15c_mem_sup hVN hp
    by_cases hv1 : v = 1
    · rw [hv1] at hpp ⊢
      have hkk : k * k = 1 := by simpa using hpp
      rcases hK.unique k hk hkk with h1 | h1
      · left; simp [h1]
      · right; left; simp [h1]
    by_cases hva : v = a
    · rw [hva] at hpp ⊢
      have hkk : k * k = 1 := by
        have e : (k * a) * (k * a) = k * k := by
          calc (k * a) * (k * a) = k * (a * k) * a := by group
            _ = k * (k * a) * a := by rw [haK' k hk]
            _ = k * k * (a * a) := by group
            _ = k * k := by rw [hR.sq]; group
        rw [← e]
        exact hpp
      rcases hK.unique k hk hkk with h1 | h1
      · right; right; left; simp [h1]
      · right; right; right; simp [h1]
    · exfalso
      have hvv := hsq v hv hv1 hva
      have hk' : v * k * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hVN hv) k).mp hk
      have e : (k * v) * (k * v) = (k * (v * k * v⁻¹)) * a := by
        rw [← hvv]; group
      rw [e] at hpp
      have haK2 : a ∈ K := by
        have h2 : a = (k * (v * k * v⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right hpp
        rw [h2]
        exact K.inv_mem (K.mul_mem hk hk')
      rcases hK.unique a haK2 hR.sq with h3 | h3
      · exact hR.ne_one h3
      · exact hza h3
  have hcentP : ∀ p ∈ K ⊔ V, z * p = p * z ∧ a * p = p * a := by
    intro p hp
    obtain ⟨k, hk, v, hv, rfl⟩ := e15c_mem_sup hVN hp
    refine ⟨?_, ?_⟩
    · calc z * (k * v) = (z * k) * v := by group
        _ = (k * z) * v := by rw [hzK k hk]
        _ = k * (z * v) := by group
        _ = k * (v * z) := by rw [hzV v hv]
        _ = k * v * z := by group
    · calc a * (k * v) = (a * k) * v := by group
        _ = (k * a) * v := by rw [haK' k hk]
        _ = k * (a * v) := by group
        _ = k * (v * a) := by rw [haV' v hv]
        _ = k * v * a := by group
  obtain ⟨a', c', b', -, -, hac, -, hb2, hba, hbc, hgen⟩ := hW
  have hgenmem : ∀ x, x ∈ ({a', c', b'} : Set G) → x ∈ K ⊔ V := by
    intro x hx
    rw [← hgen]
    exact Subgroup.subset_closure hx
  have ha'P : a' ∈ K ⊔ V := hgenmem a' (by simp)
  have hb'P : b' ∈ K ⊔ V := hgenmem b' (by simp)
  have hb'cent : ∀ p ∈ K ⊔ V, b' * p = p * b' := by
    intro p hp
    rcases hinv b' hb'P hb2 with h1 | h1 | h1 | h1
    · rw [h1]; group
    · rw [h1]; exact (hcentP p hp).1
    · rw [h1]; exact (hcentP p hp).2
    · rw [h1]
      obtain ⟨hz1, ha1⟩ := hcentP p hp
      calc z * a * p = z * (a * p) := by group
        _ = z * (p * a) := by rw [ha1]
        _ = (z * p) * a := by group
        _ = (p * z) * a := by rw [hz1]
        _ = p * (z * a) := by group
  have hc'a' : c' = a' := by
    have e : b' * a' * b'⁻¹ = a' := by rw [hb'cent a' ha'P]; group
    exact hba.symm.trans e
  have hcentA : ∀ p ∈ K ⊔ V, a' * p = p * a' := by
    intro p hp
    have hle : K ⊔ V ≤ Subgroup.centralizer ({a'} : Set G) := by
      rw [← hgen]
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      rcases hx with h1 | h1 | h1
      · rw [h1]
      · rw [h1, hc'a']
      · rw [h1]; exact (hb'cent a' ha'P).symm
    exact Subgroup.mem_centralizer_iff.mp (hle hp) a' (Set.mem_singleton a')
  have hcommP : ∀ p ∈ K ⊔ V, ∀ q ∈ K ⊔ V, p * q = q * p := by
    intro p hp q hq
    have hle : K ⊔ V ≤ Subgroup.centralizer ({p} : Set G) := by
      rw [← hgen]
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      rcases hx with h1 | h1 | h1
      · rw [h1]; exact (hcentA p hp).symm
      · rw [h1, hc'a']; exact (hcentA p hp).symm
      · rw [h1]; exact (hb'cent p hp).symm
    exact Subgroup.mem_centralizer_iff.mp (hle hq) p (Set.mem_singleton p)
  exact hij (hcommP i (Subgroup.mem_sup_left hi) j (Subgroup.mem_sup_left hj))

theorem eq_of_conj_mem_centralizer (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z) {a : G}
    (ha : ∃ x : G, a = x * z * x⁻¹) (haK : a ∈ Subgroup.centralizer (K : Set G)) : a = z := by
  obtain ⟨x, rfl⟩ := ha
  by_contra hne
  have hΩ := h.thmD.hyp
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hnf⟩ :=
    exists_q8_gen s.isInv (h.isQuatSub_of_mem s.mem) (h.card_eq_eight s.mem)
  have hij : i * j ≠ j * i := by
    intro e
    have h1 : z * (i * j) = i * j := by rw [← hji, e]
    exact s.isInv.ne_one (mul_eq_right.mp h1)
  have ha2 : x * z * x⁻¹ * (x * z * x⁻¹) = 1 := (s.isInv.conj x).sq
  have hR : conjSub x K ∈ Ω := hΩ.conjInvariant x K s.mem
  have hRa : IsUniqueInvolution (conjSub x K) (x * z * x⁻¹) := s.isInv.conj x
  have haN := e15c_mem_normalizer_of_mem_centralizer haK
  have hRtw : conjSub x K ∉ twinSet Ω K := by
    rintro ⟨-, z', hz'K, hz'R⟩
    rw [← s.isInv.eq hz'K] at hz'R
    exact hne (hRa.eq hz'R)
  have haC : x * z * x⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Subgroup.mem_centralizer_iff.mp haK z s.isInv.mem)
  have hZ2 : IsPGroup 2 (Subgroup.zpowers (x * z * x⁻¹)) :=
    (h.thmD.two (conjSub x K) hR).to_le (Subgroup.zpowers_le.mpr hRa.mem)
  obtain ⟨V, hV, hZV⟩ := IsSylow2In.exists_ge hZ2
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hRa.mem, haC⟩))
  have haV : x * z * x⁻¹ ∈ V := hZV (Subgroup.mem_zpowers _)
  have hVR : V ≤ conjSub x K := hV.1.trans inf_le_left
  have ha1 : x * z * x⁻¹ ≠ 1 := hRa.ne_one
  rcases Sec6Gen.l6_2Gen G Ω hΩ K s.mem z s.isInv (conjSub x K) hR hRtw (x * z * x⁻¹) hRa
    V hV haV with ⟨hVt, hne'⟩ | ⟨hVt, -, R', hR'RS, hR'K, -, hSD⟩ |
      ⟨hVU, hVN, R', hR'RS, hR'K, -, hW⟩ | ⟨hVRS, hVK⟩
  ·
    exact hne' (mem_normalizer_iff_conjSub_eq.mp haN)
  · exfalso
    have hR'eq : R' = K := Subgroup.eq_of_le_of_card_ge hR'K (by
      rw [h.card_eq_eight s.mem, e15c_card_RSet h hR'RS])
    rw [hVt, hR'eq] at hSD
    exact e15c_not_semidihedral (e15c_pow4 s.isInv hi hj hii hjj hji hnf) haK ha2 ha1 hSD
  · exfalso
    obtain ⟨R₂, hR₂, -, -, -, -, -, hcard₂, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
    have hV4eq : Nat.card V = 4 := by
      have := e15c_card_RSet h hR₂
      omega
    have hR'eq : R' = K := Subgroup.eq_of_le_of_card_ge hR'K (by
      rw [h.card_eq_eight s.mem, e15c_card_RSet h hR'RS])
    rw [hR'eq] at hW
    exact e15c_not_wreathed s.isInv hRa hVR haV haK hVN hV4eq hne hi hj hij hW
  · exfalso
    have hVRe : V = conjSub x K :=
      ((Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hR hVRS hVR).eq_of_le
        (h.thmD.two (conjSub x K) hR) le_rfl hVR).symm
    rw [hVRe, TL4.oddCoreOf_eq_bot_of_isPGroup (h.thmD.two K s.mem)] at hVK
    have hcom : Commutes K (conjSub x K) := fun a' ha' b hb =>
      (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp
        (hVK (Subgroup.commutator_mem_commutator hb ha')))).symm
    exact hne (h9 K s.mem (conjSub x K) hR hcom z (x * z * x⁻¹) s.isInv hRa).symm

private theorem e15c_le_oTwoCore_of_odd {C U : Subgroup G} (hU2 : IsPGroup 2 U) (hUC : U ≤ C)
    (hodd : ∀ y ∈ C, Odd (orderOf y) → ∀ u ∈ U, y * u = u * y) : U ≤ oTwoCore C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Oset : Set G := {y | y ∈ C ∧ Odd (orderOf y)}
  let N : Subgroup G := Subgroup.closure Oset
  have hNC : N ≤ C := (Subgroup.closure_le _).mpr fun _ hy => hy.1
  have hconjO : ∀ c ∈ C, ∀ y ∈ Oset, c * y * c⁻¹ ∈ Oset := by
    intro c hc y hy
    refine ⟨C.mul_mem (C.mul_mem hc hy.1) (C.inv_mem hc), ?_⟩
    have hord : orderOf (c * y * c⁻¹) = orderOf y :=
      orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y
    rw [hord]
    exact hy.2
  have hNnorm : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    have hsub : N ≤ N.comap (MulAut.conj c).toMonoidHom :=
      (Subgroup.closure_le _).mpr fun y hy =>
        Subgroup.mem_comap.mpr (Subgroup.subset_closure (hconjO c hc y hy))
    exact Subgroup.mem_comap.mp (hsub hn)
  let N' : Subgroup C := N.subgroupOf C
  have hN'mem : ∀ x : C, x ∈ N' ↔ (x : G) ∈ N := fun x => Subgroup.mem_subgroupOf
  haveI hN'normal : N'.Normal := ⟨fun n hn g => by
    rw [hN'mem] at hn ⊢
    have := hNnorm g.1 g.2 n.1 hn
    simpa using this⟩
  have hU2C : IsPGroup 2 (U.subgroupOf C) := hU2.comap_subtype
  obtain ⟨S, hUS⟩ := hU2C.exists_le_sylow
  have hSN : (S : Subgroup C) ≤ Subgroup.normalizer (N' : Set C) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcover : N' ⊔ (S : Subgroup C) = ⊤ := by
    have hpN : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ N'.index := by
      intro p hp hp2
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨Q, -⟩ := (IsPGroup.of_bot (p := p) (G := C)).exists_le_sylow
      have hQN : (Q : Subgroup C) ≤ N' := by
        intro x hx
        obtain ⟨k, hk⟩ := Q.isPGroup' ⟨x, hx⟩
        have hk' : x ^ p ^ k = 1 := by
          have := congrArg Subtype.val hk
          simpa using this
        have hdvd : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
        have hodd' : Odd (orderOf x) :=
          Odd.of_dvd_nat (Odd.pow (hp.odd_of_ne_two hp2)) hdvd
        rw [hN'mem]
        apply Subgroup.subset_closure
        refine ⟨x.2, ?_⟩
        rw [← orderOf_submonoid] at hodd'
        exact hodd'
      exact fun hd => Q.not_dvd_index (dvd_trans hd (Subgroup.index_dvd_of_le hQN))
    by_contra hne
    have hM2 : ¬ 2 ∣ (N' ⊔ (S : Subgroup C)).index := fun hd =>
      S.not_dvd_index (dvd_trans hd (Subgroup.index_dvd_of_le le_sup_right))
    have hMN : (N' ⊔ (S : Subgroup C)).index ∣ N'.index := Subgroup.index_dvd_of_le le_sup_left
    obtain ⟨p, hp, hpM⟩ := Nat.exists_prime_and_dvd
      (fun h1 => hne (Subgroup.index_eq_one.mp h1))
    have hp2 : p ≠ 2 := fun e => hM2 (e ▸ hpM)
    exact hpN p hp hp2 (dvd_trans hpM hMN)
  have hdec : ∀ c : C, ∃ n ∈ N', ∃ s ∈ (S : Subgroup C), c = n * s := by
    intro c
    have hc : c ∈ N' ⊔ (S : Subgroup C) := by
      rw [hcover]
      exact Subgroup.mem_top c
    exact e15c_mem_sup hSN hc
  have hcentral : ∀ c ∈ C, ∀ u ∈ U, ∀ y ∈ Oset, y * (c * u * c⁻¹) = (c * u * c⁻¹) * y := by
    intro c hc u hu y hy
    have hw := hconjO c⁻¹ (C.inv_mem hc) y hy
    rw [inv_inv] at hw
    have hcomm := hodd _ hw.1 hw.2 u hu
    calc y * (c * u * c⁻¹) = c * ((c⁻¹ * y * c) * u) * c⁻¹ := by group
      _ = c * (u * (c⁻¹ * y * c)) * c⁻¹ := by rw [hcomm]
      _ = (c * u * c⁻¹) * y := by group
  have hNcent : ∀ c ∈ C, ∀ u ∈ U, N ≤ Subgroup.centralizer ({c * u * c⁻¹} : Set G) := by
    intro c hc u hu
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (hcentral c hc u hu y hy).symm
  have hconjS : ∀ c : C, ∀ u : C, (u : G) ∈ U → c * u * c⁻¹ ∈ (S : Subgroup C) := by
    intro c u hu
    obtain ⟨n, hn, s, hs, rfl⟩ := hdec c
    have huS : u ∈ (S : Subgroup C) := hUS (Subgroup.mem_subgroupOf.mpr hu)
    have hsus : s * u * s⁻¹ ∈ (S : Subgroup C) := S.mul_mem (S.mul_mem hs huS) (S.inv_mem hs)
    have hcommG : ((s : G) * (u : G) * (s : G)⁻¹) * (n : G) =
        (n : G) * ((s : G) * (u : G) * (s : G)⁻¹) :=
      Subgroup.mem_centralizer_iff.mp
        ((hNcent s.1 s.2 u hu) ((hN'mem n).mp hn)) _ (Set.mem_singleton _)
    have key : (n * s) * u * (n * s)⁻¹ = s * u * s⁻¹ := by
      apply Subtype.ext
      show (n : G) * (s : G) * (u : G) * ((n : G) * (s : G))⁻¹ = (s : G) * (u : G) * (s : G)⁻¹
      have e : (n : G) * (s : G) * (u : G) * ((n : G) * (s : G))⁻¹ =
          (n : G) * ((s : G) * (u : G) * (s : G)⁻¹) * (n : G)⁻¹ := by group
      rw [e, ← hcommG]
      group
    rw [key]
    exact hsus
  let X : Set C := {x | ∃ c : C, ∃ u : C, (u : G) ∈ U ∧ x = c * u * c⁻¹}
  let T : Subgroup C := Subgroup.closure X
  have hTS : T ≤ (S : Subgroup C) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨c, u, hu, rfl⟩
    exact hconjS c u hu
  have hTnorm : ∀ g : C, ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro g x hx
    have hle : T ≤ T.comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨c, u, hu, rfl⟩
      refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨g * c, u, hu, ?_⟩)
      show g * (c * u * c⁻¹) * g⁻¹ = g * c * u * (g * c)⁻¹
      group
    exact Subgroup.mem_comap.mp (hle hx)
  haveI hTN : T.Normal := ⟨fun n hn g => hTnorm g n hn⟩
  have hT2 : IsPGroup 2 T := S.isPGroup'.to_le hTS
  have hTle : T ≤ sSup {N : Subgroup C | N.Normal ∧ IsPGroup 2 N} :=
    le_sSup ⟨hTN, hT2⟩
  intro u hu
  have huC : (⟨u, hUC hu⟩ : C) ∈ T := by
    apply Subgroup.subset_closure
    exact ⟨1, ⟨u, hUC hu⟩, hu, by simp⟩
  exact Subgroup.mem_map.mpr ⟨⟨u, hUC hu⟩, hTle huC, rfl⟩

theorem le_oTwoCore_of_odd_centralizes (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    {J : Subgroup G} {t : G} (hJ : J ∈ omegaStarNbr Ω K) (hJt : J ∉ twinSet Ω K)
    (ht : IsUniqueInvolution J t)
    (hodd : ∀ y ∈ Subgroup.centralizer ({z} : Set G), Odd (orderOf y) → y * t = t * y)
    {U : Subgroup G} (hU : U ∈ USet Ω) (hUJ : U ≤ J) (hUN : U ≤ Subgroup.normalizer (K : Set G)) :
    U ≤ oTwoCore (Subgroup.centralizer ({z} : Set G)) := by
  have hΩ := h.thmD.hyp
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet hΩ hU
  have hUC : U ≤ Subgroup.centralizer ({z} : Set G) := hUN.trans (h.normalizer_twin s).2
  obtain ⟨R₀, hR₀, -, -, -, -, -, hcard₀, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hU4 : Nat.card U = 4 := by
    have := e15c_card_RSet h hR₀
    omega
  have hcyc : IsCyclic U := by
    obtain ⟨-, -, -, -, -, -, hc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
    exact hc
  refine e15c_le_oTwoCore_of_odd hU2 hUC ?_
  intro y hyC hy u hu
  have hyz : y * z * y⁻¹ = z := by
    have hc := Subgroup.mem_centralizer_iff.mp hyC z (Set.mem_singleton z)
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [← hc]
      _ = z := by group
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := by
    refine e15c_odd_normalizes h s.mem s.ne.symm s.twin hy ?_
    have hc := s.isInv.conj y
    rw [hyz] at hc
    exact ⟨hΩ.conjInvariant y K s.mem, z, s.isInv, hc⟩
  have hyt : y * t * y⁻¹ = t := by
    calc y * t * y⁻¹ = t * y * y⁻¹ := by rw [hodd y hyC hy]
      _ = t := by group
  have hyJ : y ∈ Subgroup.normalizer (J : Set G) := by
    obtain ⟨J', hJ'ne, hJtw⟩ := h.twinSet_pair s hJ.1
    refine e15c_odd_normalizes h hJ.1 hJ'ne hJtw hy ?_
    have hc := ht.conj y
    rw [hyt] at hc
    exact ⟨hΩ.conjInvariant y J hJ.1, t, ht, hc⟩
  have hJN : ¬ J ≤ Subgroup.normalizer (K : Set G) := by
    intro hle
    apply hJt
    rw [← h.kPerp_eq_twinSet_of_perp9 h9 s.mem]
    exact Or.inr ⟨hJ.1, hJ.2.1, J, TC.mem_RSet_of_isPGroup hJ.1 (h.thmD.two J hJ.1), le_rfl, hle⟩
  have hXJ : (J ⊓ Subgroup.normalizer (K : Set G)) ≠ J := fun e => hJN (e ▸ inf_le_right)
  have hX8 : Nat.card ↥(J ⊓ Subgroup.normalizer (K : Set G)) ∣ Nat.card J :=
    Subgroup.card_dvd_of_le inf_le_left
  have hJ8 : Nat.card J = 8 := h.card_eq_eight hJ.1
  have hXc : Nat.card ↥(J ⊓ Subgroup.normalizer (K : Set G)) ≠ 8 := by
    intro e8
    apply hXJ
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    omega
  have hXc4 : Nat.card ↥(J ⊓ Subgroup.normalizer (K : Set G)) = 4 := by
    have hle8 : Nat.card ↥(J ⊓ Subgroup.normalizer (K : Set G)) ≤ 8 := by
      rw [← hJ8]
      exact Nat.le_of_dvd (Nat.card_pos) hX8
    have hge4 : 4 ≤ Nat.card ↥(J ⊓ Subgroup.normalizer (K : Set G)) := by
      have := Subgroup.card_le_of_le (le_inf hUJ hUN)
      omega
    rw [hJ8] at hX8
    interval_cases hc : Nat.card ↥(J ⊓ Subgroup.normalizer (K : Set G)) <;> omega
  have hUeq : U = J ⊓ Subgroup.normalizer (K : Set G) :=
    Subgroup.eq_of_le_of_card_ge (le_inf hUJ hUN) (by omega)
  have hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
    intro u hu
    have hmem : y * u * y⁻¹ ∈ J ⊓ Subgroup.normalizer (K : Set G) := by
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hyJ u).mp (hUJ hu) |> fun h' => by
          simpa [mul_assoc] using h'
      · exact (Subgroup.normalizer (K : Set G)).mul_mem
          ((Subgroup.normalizer (K : Set G)).mul_mem hyK (hUN hu))
          ((Subgroup.normalizer (K : Set G)).inv_mem hyK)
    rw [← hUeq] at hmem
    exact hmem
  exact e15c_odd_comm_cyclic hcyc hU4 hy hyU u hu

theorem eGroup_eq_zGroup_inf_sup_of_le (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') :
    Nat.card ↥(eGroup Ω K) = 8 ∧ eGroup Ω K = zGroup Ω ⊓ (K ⊔ K') := by
  have hle : eGroup Ω K ≤ zGroup Ω ⊓ (K ⊔ K') := le_inf (h.eGroup_le_zGroup s.mem) hE
  have hc8 := h.natCard_zGroup_inf_sup_twin h9 s h13
  have hE8 := h.eight_le_card_eGroup h9 s.mem
  have heq : eGroup Ω K = zGroup Ω ⊓ (K ⊔ K') := Subgroup.eq_of_le_of_card_ge hle (by omega)
  exact ⟨by rw [heq, hc8], heq⟩

private theorem e15c_odd_mem_N_K (h : EndHyp Ω) (s : TwinSit Ω K K' z) {y : G}
    (hyC : y ∈ Subgroup.centralizer ({z} : Set G)) (hy : Odd (orderOf y)) :
    y ∈ Subgroup.normalizer (K : Set G) := by
  have hyz : y * z * y⁻¹ = z := by
    have hc : z * y = y * z := Subgroup.mem_centralizer_iff.mp hyC z (Set.mem_singleton z)
    rw [← hc]
    group
  refine e15c_odd_normalizes h s.mem s.ne.symm s.twin hy ?_
  have hc := s.isInv.conj y
  rw [hyz] at hc
  exact ⟨h.thmD.hyp.conjInvariant y K s.mem, z, s.isInv, hc⟩

private theorem e15c_three_full (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') :
    ∃ x : G, x ∈ Subgroup.normalizer (K : Set G) ∧ x ^ 3 ∈ Subgroup.centralizer (K : Set G) ∧
      (∃ a : ℕ, x ^ 3 ^ a = 1) ∧ (∃ k ∈ K, x * k ≠ k * x) ∧ (∃ k ∈ K', x * k ≠ k * x) := by
  have hΩ := h.thmD.hyp
  obtain ⟨W, hW, hzW, hKd, J, hJ, hJd, hJs, hJt, U, hU, hUJ, hUW, hUO⟩ := h.exists_choice h9 s
  have hKJ : K ≠ J := fun e => hJs.2.1 e.symm
  have hsylow : ∀ M ∈ Ω, IsSylow2In M M := fun M hM =>
    ⟨le_rfl, h.thmD.two M hM, fun V' hV' _ hMV' => le_antisymm hV' hMV'⟩
  have hUN : U ≤ Subgroup.normalizer (K : Set G) := fun u hu =>
    (Q3CL.Thompson.inf_W_le_normalizer_of_ne hΩ hW s.mem hJs.1 hKJ hKd hJd
      (hsylow K s.mem) (hsylow J hJs.1)).2 (Subgroup.mem_inf.mpr ⟨hUJ hu, hUW hu⟩)
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJs.1
  obtain ⟨y, hyC, hyodd, hyt⟩ : ∃ y ∈ Subgroup.centralizer ({z} : Set G),
      Odd (orderOf y) ∧ y * t ≠ t * y := by
    by_contra hcon
    push_neg at hcon
    exact hUO (le_oTwoCore_of_odd_centralizes h h9 s hJs hJt ht hcon hU hUJ hUN)
  have hyz : y * z * y⁻¹ = z := by
    have hc : z * y = y * z := Subgroup.mem_centralizer_iff.mp hyC z (Set.mem_singleton z)
    rw [← hc]
    group
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := e15c_odd_mem_N_K h s hyC hyodd
  have hyK' : y ∈ Subgroup.normalizer (K' : Set G) := (h.normalizer_twin s).1 ▸ hyK
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hnf⟩ :=
    exists_q8_gen s.isInv (h.isQuatSub_of_mem s.mem) (h.card_eq_eight s.mem)
  have hQK : Q8Data K z i j := ⟨s.isInv, hi, hj, hii, hjj, hji, hnf⟩
  obtain ⟨i', j', hi', hj', hii', hjj', hji', hnf'⟩ :=
    exists_q8_gen s.mem_twin.2 (h.isQuatSub_of_mem s.mem_twin.1) (h.card_eq_eight s.mem_twin.1)
  have hQK' : Q8Data K' z i' j' := ⟨s.mem_twin.2, hi', hj', hii', hjj', hji', hnf'⟩
  have hyK3 : y ^ 3 ∈ Subgroup.centralizer (K : Set G) :=
    e15c_pow3_mem_centralizer hQK hyC hyK hyodd
  have hyK3' : y ^ 3 ∈ Subgroup.centralizer (K' : Set G) :=
    e15c_pow3_mem_centralizer hQK' hyC hyK' hyodd
  have hz1 : z ≠ 1 := s.isInv.ne_one
  have hz2 : z * z = 1 := s.isInv.sq
  have hAB : Commutes K K' := s.commutes h
  have hEN : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ e ∈ eGroup Ω K,
      g * e * g⁻¹ ∈ eGroup Ω K := by
    intro g hg e he
    have hgK : conjSub g K = K := mem_normalizer_iff_conjSub_eq.mp hg
    have hc := h.eGroup_conj s.mem g
    rw [hgK] at hc
    rw [hc]
    exact conj_mem_conjSub he
  have hwE : ∀ w ∈ K', w ∈ eGroup Ω K → w = 1 ∨ w = z := by
    intro w hw hwE
    have hww := h.zGroup_mul_self h9 w (h.eGroup_le_zGroup s.mem hwE)
    exact s.mem_twin.2.unique w hw hww
  have hwE' : ∀ w ∈ K, w ∈ eGroup Ω K → w = 1 ∨ w = z := by
    intro w hw hwE
    have hww := h.zGroup_mul_self h9 w (h.eGroup_le_zGroup s.mem hwE)
    exact s.isInv.unique w hw hww
  have ht_E : t ∈ eGroup Ω K := h.mem_eGroup_of_mem_omegaStarNbr hJs ht
  have hyEK : ∃ k ∈ K, y * k ≠ k * y := by
    by_contra hcon
    push_neg at hcon
    have hcomm := e15c_centralizes_E (A := K) (B := K') (E := eGroup Ω K) hz1 hz2 hAB
      (Asc77.AscL62.le_normalizer_of_commutes (s.commutes h).symm) hE hEN hwE hyC hcon hyK' hyodd
    exact hyt (hcomm t ht_E)
  have hyEK' : ∃ k ∈ K', y * k ≠ k * y := by
    by_contra hcon
    push_neg at hcon
    have hcomm := e15c_centralizes_E (A := K') (B := K) (E := eGroup Ω K) hz1 hz2
      (fun a ha b hb => ((s.commutes h) b hb a ha).symm)
      (Asc77.AscL62.le_normalizer_of_commutes (s.commutes h)) (by rw [sup_comm]; exact hE)
      (fun g hg e he => hEN g ((h.normalizer_twin s).1 ▸ hg) e he) hwE' hyC hcon hyK hyodd
    exact hyt (hcomm t ht_E)
  have hn0 : orderOf y ≠ 0 := by
    obtain ⟨m, hm⟩ := hyodd
    omega
  obtain ⟨e3, s3, hs3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  have hx3 : (y ^ s3) ^ 3 ∈ Subgroup.centralizer (K : Set G) := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Subgroup.pow_mem _ hyK3 s3
  refine ⟨y ^ s3, Subgroup.pow_mem _ hyK s3, hx3, ⟨e3, ?_⟩, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  · by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk, hkx⟩ := hyEK
    apply hkx
    have hxc : y ^ s3 ∈ Subgroup.centralizer (K : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun k hk => (hcon k hk).symm)
    exact (Subgroup.mem_centralizer_iff.mp (e15c_comm_of_pow hs3 hyK3 hxc) k hk).symm
  · by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk, hkx⟩ := hyEK'
    apply hkx
    have hxc : y ^ s3 ∈ Subgroup.centralizer (K' : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun k hk => (hcon k hk).symm)
    exact (Subgroup.mem_centralizer_iff.mp (e15c_comm_of_pow hs3 hyK3' hxc) k hk).symm

theorem exists_three_element (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') :
    ∃ x : G, x ∈ Subgroup.normalizer (K : Set G) ∧ (∃ a : ℕ, x ^ 3 ^ a = 1) ∧
      (∃ k ∈ K, x * k ≠ k * x) ∧ (∃ k ∈ K', x * k ≠ k * x) := by
  obtain ⟨x, hx1, -, hx2, hx3, hx4⟩ := e15c_three_full h h9 s h13 hE
  exact ⟨x, hx1, hx2, hx3, hx4⟩

theorem exists_conj_of_mem_eGroup_of_le (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') {e : G} (he : e ∈ eGroup Ω K)
    (he1 : e ≠ 1) : ∃ g : G, e = g * z * g⁻¹ := by
  have hΩ := h.thmD.hyp
  have hz1 : z ≠ 1 := s.isInv.ne_one
  have hz2 : z * z = 1 := s.isInv.sq
  have hAB : Commutes K K' := s.commutes h
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) :=
    Asc77.AscL62.le_normalizer_of_commutes (s.commutes h).symm
  have hEN : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ e' ∈ eGroup Ω K,
      g * e' * g⁻¹ ∈ eGroup Ω K := by
    intro g hg e' he'
    have hgK : conjSub g K = K := mem_normalizer_iff_conjSub_eq.mp hg
    have hc := h.eGroup_conj s.mem g
    rw [hgK] at hc
    rw [hc]
    exact conj_mem_conjSub he'
  have hwE : ∀ w ∈ K', w ∈ eGroup Ω K → w = 1 ∨ w = z := by
    intro w hw hwE
    have hww := h.zGroup_mul_self h9 w (h.eGroup_le_zGroup s.mem hwE)
    exact s.mem_twin.2.unique w hw hww
  have hwE' : ∀ w ∈ K, w ∈ eGroup Ω K → w = 1 ∨ w = z := by
    intro w hw hwE
    have hww := h.zGroup_mul_self h9 w (h.eGroup_le_zGroup s.mem hwE)
    exact s.isInv.unique w hw hww
  have hzE : z ∈ eGroup Ω K := h.mem_eGroup_of_isUniqueInvolution s.isInv
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hnf⟩ :=
    exists_q8_gen s.isInv (h.isQuatSub_of_mem s.mem) (h.card_eq_eight s.mem)
  have hQ : Q8Data K z i j := ⟨s.isInv, hi, hj, hii, hjj, hji, hnf⟩
  obtain ⟨x, hxN, hx3, ⟨a3, hxa⟩, hnc, -⟩ := e15c_three_full h h9 s h13 hE
  obtain ⟨W, hW, hzW, hKd, J, hJ, hJd, hJs, hJt, U, hU, hUJ, hUW, hUO⟩ := h.exists_choice h9 s
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJs.1
  have ht_E : t ∈ eGroup Ω K := h.mem_eGroup_of_mem_omegaStarNbr hJs ht
  have htz : t ≠ z := by
    intro e'
    apply hJt
    exact ⟨hJs.1, z, s.isInv, e' ▸ ht⟩
  have ht_zG : ∃ g : G, t = g * z * g⁻¹ := by
    obtain ⟨g, hg⟩ := h.thmD.trans K s.mem J hJs.1
    have hc := s.isInv.conj g
    rw [hg] at hc
    exact ⟨g, ht.eq hc⟩
  obtain ⟨k₀, hk₀, b₀, hb₀, ht_eq⟩ := e15c_mem_sup hKN (hE ht_E)
  have hk₀1 : k₀ ≠ 1 := by
    intro h'
    have htb : t = b₀ := by rw [ht_eq, h', one_mul]
    rw [htb] at ht_E
    rcases hwE b₀ hb₀ ht_E with h'' | h''
    · exact ht.ne_one (htb.trans h'')
    · exact htz (htb.trans h'')
  have hk₀z : k₀ ≠ z := by
    intro h'
    have htb : t = z * b₀ := by rw [ht_eq, h']
    have hzb : z * b₀ ∈ K' := K'.mul_mem s.mem_twin.2.mem hb₀
    have hmem : z * b₀ ∈ eGroup Ω K := by
      rw [← htb]
      exact ht_E
    rcases hwE _ hzb hmem with h'' | h''
    · exact ht.ne_one (htb.trans h'')
    · exact htz (htb.trans h'')
  have hxK' : x ∈ Subgroup.normalizer (K' : Set G) := (h.normalizer_twin s).1 ▸ hxN
  have hxz : x * z = z * x := by
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [conj_eq_self_of_normalizer s.isInv hxN]
  have hK8 : Nat.card K = 8 := h.card_eq_eight s.mem
  obtain ⟨k₁, hk₁def⟩ : ∃ k₁ : G, k₁ = x * k₀ * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂def⟩ : ∃ k₂ : G, k₂ = x * k₁ * x⁻¹ := ⟨_, rfl⟩
  have hk₁K : k₁ ∈ K := by
    rw [hk₁def]
    exact (Subgroup.mem_normalizer_iff.mp hxN k₀).mp hk₀
  have hk₂K : k₂ ∈ K := by
    rw [hk₂def]
    exact (Subgroup.mem_normalizer_iff.mp hxN k₁).mp hk₁K
  have hk₁1 : k₁ ≠ 1 := fun h' => by
    rcases e15c_conj_one_or_z s.isInv hxN hk₁def.symm (Or.inl h') with h'' | h''
    · exact hk₀1 h''
    · exact hk₀z h''
  have hk₁z : k₁ ≠ z := fun h' => by
    rcases e15c_conj_one_or_z s.isInv hxN hk₁def.symm (Or.inr h') with h'' | h''
    · exact hk₀1 h''
    · exact hk₀z h''
  have hk₂1 : k₂ ≠ 1 := fun h' => by
    rcases e15c_conj_one_or_z s.isInv hxN hk₂def.symm (Or.inl h') with h'' | h''
    · exact hk₁1 h''
    · exact hk₁z h''
  have hk₂z : k₂ ≠ z := fun h' => by
    rcases e15c_conj_one_or_z s.isInv hxN hk₂def.symm (Or.inr h') with h'' | h''
    · exact hk₁1 h''
    · exact hk₁z h''
  have hP0 := e15c_P2 s.isInv hK8 hxN hxa hnc hk₀ hk₀1 hk₀z
  rw [← hk₁def] at hP0
  have hP1 := e15c_P2 s.isInv hK8 hxN hxa hnc hk₁K hk₁1 hk₁z
  rw [← hk₂def] at hP1
  have hcube : x * k₂ * x⁻¹ = k₀ := by
    have hc := Subgroup.mem_centralizer_iff.mp hx3 k₀ hk₀
    rw [pow_three] at hc
    rw [hk₂def, hk₁def]
    calc x * (x * (x * k₀ * x⁻¹) * x⁻¹) * x⁻¹ = (x * (x * x)) * k₀ * (x * (x * x))⁻¹ := by
          group
      _ = k₀ := by rw [← hc]; group
  have hk₂k₀ : k₂ ≠ k₀ := fun h' => hP0.1 (by
    rw [hk₁def]
    rw [h'] at hcube
    exact hcube)
  have hk₂zk₀ : k₂ ≠ z * k₀ := fun h' => by
    have e0 : x * (z * k₀) * x⁻¹ = z * k₁ := by
      rw [hk₁def]
      calc x * (z * k₀) * x⁻¹ = (x * z * x⁻¹) * (x * k₀ * x⁻¹) := by group
        _ = z * (x * k₀ * x⁻¹) := by rw [conj_eq_self_of_normalizer s.isInv hxN]
    have e1 : z * k₁ = k₀ := by
      rw [← e0, ← h']
      exact hcube
    exact hP0.2 (by
      calc k₁ = z * (z * k₁) := by rw [← mul_assoc, hz2, one_mul]
        _ = z * k₀ := by rw [e1])
  have hk₀sq := e15c_sq_K hQ hk₀ hk₀1 hk₀z
  have hk₁sq := e15c_sq_K hQ hk₁K hk₁1 hk₁z
  have hk₂sq := e15c_sq_K hQ hk₂K hk₂1 hk₂z
  have hL0 := e15c_q8_class hQ hk₀ hk₀sq
  have hL1 := e15c_q8_class hQ hk₁K hk₁sq
  have hL2 := e15c_q8_class hQ hk₂K hk₂sq
  have hL10 : ({k₁, z * k₁} : Set G) ≠ {k₀, z * k₀} := by
    intro heq
    have hm : k₁ ∈ ({k₀, z * k₀} : Set G) := by
      rw [← heq]
      exact Set.mem_insert _ _
    rcases Set.mem_insert_iff.mp hm with h' | h'
    · exact hP0.1 h'
    · exact hP0.2 (Set.mem_singleton_iff.mp h')
  have hL21 : ({k₂, z * k₂} : Set G) ≠ {k₁, z * k₁} := by
    intro heq
    have hm : k₂ ∈ ({k₁, z * k₁} : Set G) := by
      rw [← heq]
      exact Set.mem_insert _ _
    rcases Set.mem_insert_iff.mp hm with h' | h'
    · exact hP1.1 h'
    · exact hP1.2 (Set.mem_singleton_iff.mp h')
  have hL20 : ({k₂, z * k₂} : Set G) ≠ {k₀, z * k₀} := by
    intro heq
    have hm : k₂ ∈ ({k₀, z * k₀} : Set G) := by
      rw [← heq]
      exact Set.mem_insert _ _
    rcases Set.mem_insert_iff.mp hm with h' | h'
    · exact hk₂k₀ h'
    · exact hk₂zk₀ (Set.mem_singleton_iff.mp h')
  obtain ⟨e₁, he₁def⟩ : ∃ e₁ : G, e₁ = x * t * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨e₂, he₂def⟩ : ∃ e₂ : G, e₂ = x * e₁ * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁def⟩ : ∃ b₁ : G, b₁ = x * b₀ * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂def⟩ : ∃ b₂ : G, b₂ = x * b₁ * x⁻¹ := ⟨_, rfl⟩
  have hb₁K' : b₁ ∈ K' := by
    rw [hb₁def]
    exact (Subgroup.mem_normalizer_iff.mp hxK' b₀).mp hb₀
  have hb₂K' : b₂ ∈ K' := by
    rw [hb₂def]
    exact (Subgroup.mem_normalizer_iff.mp hxK' b₁).mp hb₁K'
  have hE₁ : e₁ ∈ eGroup Ω K := by
    rw [he₁def]
    exact hEN x hxN t ht_E
  have hE₂ : e₂ ∈ eGroup Ω K := by
    rw [he₂def]
    exact hEN x hxN e₁ hE₁
  have hdec₁ : e₁ = k₁ * b₁ := by
    rw [he₁def, ht_eq, hk₁def, hb₁def]
    group
  have hdec₂ : e₂ = k₂ * b₂ := by
    rw [he₂def, hdec₁, hk₂def, hb₂def, hk₁def, hb₁def]
    group
  have hZ1 : ∃ g : G, e₁ = g * z * g⁻¹ := by
    rw [he₁def]
    exact e15c_zG_conj ht_zG
  have hZ2 : ∃ g : G, e₂ = g * z * g⁻¹ := by
    rw [he₂def]
    exact e15c_zG_conj hZ1
  have he₁1 : e₁ ≠ 1 := by
    intro h'
    apply ht.ne_one
    have : t = x⁻¹ * e₁ * x := by rw [he₁def]; group
    rw [this, h']
    group
  have he₁z : e₁ ≠ z := by
    intro h'
    apply htz
    have : t = x⁻¹ * e₁ * x := by rw [he₁def]; group
    rw [this, h']
    calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
      _ = x⁻¹ * (x * z) := by rw [hxz]
      _ = z := by group
  have he₂1 : e₂ ≠ 1 := by
    intro h'
    apply he₁1
    have : e₁ = x⁻¹ * e₂ * x := by rw [he₂def]; group
    rw [this, h']
    group
  have he₂z : e₂ ≠ z := by
    intro h'
    apply he₁z
    have : e₁ = x⁻¹ * e₂ * x := by rw [he₂def]; group
    rw [this, h']
    calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
      _ = x⁻¹ * (x * z) := by rw [hxz]
      _ = z := by group
  by_cases hez : e = z
  · exact ⟨1, by rw [hez]; group⟩
  obtain ⟨ke, hke, be, hbe, he_eq⟩ := e15c_mem_sup hKN (hE he)
  have hke1 : ke ≠ 1 := by
    intro h'
    have hbeE : be ∈ eGroup Ω K := by
      have : e = be := by rw [he_eq, h', one_mul]
      rw [← this]
      exact he
    rcases hwE be hbe hbeE with h'' | h''
    · exact he1 (by rw [he_eq, h', h'', one_mul])
    · exact hez (by rw [he_eq, h', h'', one_mul])
  have hkez : ke ≠ z := by
    intro h'
    have hzbe : z * be ∈ K' := K'.mul_mem s.mem_twin.2.mem hbe
    have hmem : z * be ∈ eGroup Ω K := by
      have : e = z * be := by rw [he_eq, h']
      rw [← this]
      exact he
    rcases hwE _ hzbe hmem with h'' | h''
    · exact he1 (by rw [he_eq, h']; exact h'')
    · exact hez (by rw [he_eq, h']; exact h'')
  have hkesq := e15c_sq_K hQ hke hke1 hkez
  have hLe := e15c_q8_class hQ hke hkesq
  have hcov := e15c_cover_logic ({i, z * i} : Set G) ({j, z * j} : Set G)
    ({i * j, z * (i * j)} : Set G) _ _ _ _ hL0 hL1 hL2 hLe hL10 hL21 hL20
  have hZf : ∀ f ∈ eGroup Ω K, f ≠ 1 → f ≠ z → (∃ g : G, f = g * z * g⁻¹) →
      ∀ f' : G, (f' = f ∨ f' = z * f) → ∃ g : G, f' = g * z * g⁻¹ := by
    intro f hf hf1 hfz hfg f' hf'
    rcases hf' with h1 | h1
    · rw [h1]
      exact hfg
    · obtain ⟨k, hk, hkn⟩ := e15c_E_noncomm hQ hAB hKN hE hwE hzE hf hf1 hfz
      rcases e15c_conj_E hAB hKN hE hEN hwE' hk hf with h2 | h2
      · exfalso
        apply hkn
        calc f * k = (k * f * k⁻¹) * k := by rw [h2]
          _ = k * f := by group
      · rw [h1, ← h2]
        exact e15c_zG_conj hfg
  have hmemL : ∀ w : G, ({ke, z * ke} : Set G) = ({w, z * w} : Set G) →
      ke = w ∨ ke = z * w := by
    intro w hw
    have hm : ke ∈ ({w, z * w} : Set G) := by
      rw [← hw]
      exact Set.mem_insert _ _
    rcases Set.mem_insert_iff.mp hm with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Set.mem_singleton_iff.mp h1)
  rcases hcov with hc | hc | hc
  · exact hZf t ht_E ht.ne_one htz ht_zG e
      (e15c_E_inj hz1 hz2 hAB hzE hwE hk₀ hb₀ hke hbe ht_eq he_eq ht_E he (hmemL k₀ hc))
  · exact hZf e₁ hE₁ he₁1 he₁z hZ1 e
      (e15c_E_inj hz1 hz2 hAB hzE hwE hk₁K hb₁K' hke hbe hdec₁ he_eq hE₁ he (hmemL k₁ hc))
  · exact hZf e₂ hE₂ he₂1 he₂z hZ2 e
      (e15c_E_inj hz1 hz2 hAB hzE hwE hk₂K hb₂K' hke hbe hdec₂ he_eq hE₂ he (hmemL k₂ hc))


end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
