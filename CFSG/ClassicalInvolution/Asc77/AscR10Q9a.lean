module

public import CFSG.ClassicalInvolution.Asc77.AscR10Sg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Fus

variable {G : Type} [Group G]

@[expose] def FusAt (S : Sylow 2 G) (z b : G) : Prop :=
  ∀ s : G, s * s = 1 → s * b = b * s → s ∈ (S : Subgroup G) → (∃ g : G, s = g * z * g⁻¹) →
    ∃ c : G, c * b = b * c ∧ s = c * z * c⁻¹

end Fus

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}




theorem Std20.r9_not_conj_z (d : Std20 p f K K' J S R R' W V z t) {b : G}
    (hb : FieldInv20 S K K' W z t b) (hF : FusAt S z b) (g : G) : g * z * g⁻¹ ≠ b := by
  intro hg
  obtain ⟨c, hcb, hc⟩ := hF b hb.sq rfl hb.mem ⟨g, hg.symm⟩
  have h1 : c⁻¹ * b * c = z := by
    calc c⁻¹ * b * c = c⁻¹ * (c * z * c⁻¹) * c := by rw [← hc]
      _ = z := by group
  have h2 : c⁻¹ * b * c = b := by
    calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
      _ = c⁻¹ * (c * b) := by rw [hcb]
      _ = b := by group
  have hbz : b = z := h2.symm.trans h1
  apply hb.not_mem_X
  rw [hbz]
  exact le_sec20X_left d.viol.hzK.mem

theorem Std20.r9_four_le_relIndex [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    {b : G} (hb : FieldInv20 S K K' W z t b) (hF : FusAt S z b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1)) {x : G}
    (hxS : x⁻¹ * b * x ∈ (S : Subgroup G)) :
    4 ≤ (Subgroup.centralizer ({x⁻¹ * b * x} : Set G)).relIndex (S : Subgroup G) := by
  classical
  have hX1 : (1 : G) ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
    (sec20X (CoreAssembly.conjClass K) z K K').one_mem
  generalize hn : x⁻¹ * b * x = n at hxS ⊢
  have hbn : b = x * n * x⁻¹ := by rw [← hn]; group
  have hn2 : n * n = 1 := by
    have : n * n = x⁻¹ * (b * b) * x := by rw [← hn]; group
    rw [this, hb.sq]; group
  have hn1 : n ≠ 1 := by
    intro h
    apply hb.not_mem_X
    rw [hbn, h, mul_one, mul_inv_cancel]
    exact hX1
  have hniv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn2
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have hz2 : z * z = 1 := d.viol.hzK.sq
  obtain ⟨a, ha⟩ := R10.r_relIndex_eq_pow S.isPGroup' n
  by_contra hlt
  have ha1 : a ≤ 1 := by
    by_contra h
    push Not at h
    apply hlt
    rw [ha]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h
  have hsq : ∀ y ∈ (S : Subgroup G), (y * y) * n = n * (y * y) := by
    intro y hy
    have hyy : y * y ∈ Subgroup.centralizer ({n} : Set G) := by
      interval_cases a
      · have h1 : (Subgroup.centralizer ({n} : Set G)).relIndex (S : Subgroup G) = 1 := by
          rw [ha]; rfl
        have h2 : (S : Subgroup G) ≤ Subgroup.centralizer ({n} : Set G) :=
          Subgroup.relIndex_eq_one.mp h1
        exact (Subgroup.centralizer ({n} : Set G)).mul_mem (h2 hy) (h2 hy)
      · have h1 : ((Subgroup.centralizer ({n} : Set G)).subgroupOf (S : Subgroup G)).index = 2 := by
          have : (Subgroup.centralizer ({n} : Set G)).relIndex (S : Subgroup G) = 2 := by
            rw [ha]; rfl
          exact this
        have h2 := Subgroup.mul_self_mem_of_index_two h1 ⟨y, hy⟩
        exact Subgroup.mem_subgroupOf.mp h2
    exact Subgroup.mem_centralizer_singleton_iff.mp hyy
  have hnN : n ∈ Subgroup.normalizer (K : Set G) :=
    (c9 h8).2.2 n hxS (by rw [hn2]; exact hX1)
  have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hnN
  obtain ⟨v₀, hv₀, hv₀o, hv₀t, huz, hWgen, huv, hdis⟩ := d.v_W_gen hu huo
  have hv₀W : v₀ ∈ W := (hv₀ ▸ Subgroup.mem_zpowers v₀ : v₀ ∈ J ⊓ W).2
  have huW : u ∈ W := (hu ▸ Subgroup.mem_zpowers u : u ∈ K ⊓ W).2
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hnt : n * t * n⁻¹ = t := by
    have h1 : n * (v₀ * v₀) = (v₀ * v₀) * n := (hsq v₀ (d.hWS hv₀W)).symm
    have h2 : n * (v₀ * v₀) ^ 2 ^ k' = (v₀ * v₀) ^ 2 ^ k' * n :=
      ((show Commute n (v₀ * v₀) from h1).pow_right _).eq
    have h3 : t = (v₀ * v₀) ^ 2 ^ k' := by
      rw [← hv₀t, ← pow_two, ← pow_mul, pow_succ']
    calc n * t * n⁻¹ = n * (v₀ * v₀) ^ 2 ^ k' * n⁻¹ := by rw [← h3]
      _ = ((v₀ * v₀) ^ 2 ^ k' * n) * n⁻¹ := by rw [h2]
      _ = t := by rw [← h3]; group
  obtain ⟨l, hl⟩ := d.y_scalar hu huo hxS hnK hnt
  have hdvd : ((2 : ℤ) ^ (k' + 1)) ∣ l - 1 := by
    have e : u ^ l * u ^ l = u * u := by
      calc u ^ l * u ^ l = (n * u * n⁻¹) * (n * u * n⁻¹) := by rw [hl u huW]
        _ = n * (u * u) * n⁻¹ := by group
        _ = (u * u) * n * n⁻¹ := by rw [← hsq u (d.hWS huW)]
        _ = u * u := by group
    have e2 : u ^ (l + l - (1 + 1)) = 1 := by
      rw [zpow_sub, zpow_add, zpow_add, zpow_one, e]
      exact mul_inv_cancel _
    have e3 := (orderOf_dvd_iff_zpow_eq_one (x := u) (i := l + l - (1 + 1))).mpr e2
    rw [huo] at e3
    have e4 : ((2 : ℤ) ^ (k' + 1 + 1)) ∣ 2 * (l - 1) := by
      have : (l + l - (1 + 1) : ℤ) = 2 * (l - 1) := by ring
      rw [this] at e3
      simpa using e3
    rw [pow_succ' (2 : ℤ) (k' + 1)] at e4
    exact (mul_dvd_mul_iff_left (by norm_num)).mp e4
  obtain ⟨m, hm⟩ := hdvd
  have hl' : l = 1 + (2 : ℤ) ^ (k' + 1) * m := by linarith
  have hcast : ∀ e : G, e ^ ((2 : ℤ) ^ (k' + 1)) = e ^ (2 ^ (k' + 1)) := by
    intro e
    have : ((2 : ℤ) ^ (k' + 1)) = ((2 ^ (k' + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast]
  have hWz : ∀ w ∈ W, w ^ ((2 : ℤ) ^ (k' + 1 + 1)) = 1 := by
    intro w hw
    have h1 := d.r_W_exp hu huo w hw
    have : ((2 : ℤ) ^ (k' + 1 + 1)) = ((2 ^ (k' + 1 + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast]
    exact h1
  obtain ⟨m', hm' | hm'⟩ := Int.even_or_odd' m
  ·
    have hcent : ∀ w ∈ W, n * w * n⁻¹ = w := by
      intro w hw
      rw [hl w hw, hl', hm']
      have : (1 + (2 : ℤ) ^ (k' + 1) * (2 * m')) = 1 + (2 : ℤ) ^ (k' + 1 + 1) * m' := by ring
      rw [this, zpow_add, zpow_one, zpow_mul, hWz w hw, one_zpow, mul_one]
    have hcomm : ∀ w ∈ W, n * w = w * n := by
      intro w hw
      have := hcent w hw
      calc n * w = n * w * n⁻¹ * n := by group
        _ = w * n := by rw [this]
    have hnW : n ∈ W := d.y_CSW_le_W c7 hxS hcomm
    rcases d.r_W_invol hu huo n hnW hn2 with h | h | h | h
    · exact hn1 h
    · exact d.r9_not_conj_z hb hF x (by rw [hbn, h])
    · obtain ⟨c, hcb, hct⟩ := hb.fuse
      exact d.r9_not_conj_z hb hF (x * c) (by
        calc x * c * z * (x * c)⁻¹ = x * (c * z * c⁻¹) * x⁻¹ := by group
          _ = x * t * x⁻¹ := by rw [hct]
          _ = b := by rw [hbn, h])
    · obtain ⟨g, -, -, hgz, -⟩ := d.v_hexg
      exact d.r9_not_conj_z hb hF (x * g) (by
        calc x * g * z * (x * g)⁻¹ = x * (g * z * g⁻¹) * x⁻¹ := by group
          _ = x * (z * t) * x⁻¹ := by rw [hgz]
          _ = b := by rw [hbn, h])
  ·
    have hcls : ∀ e ∈ W, e * n * e⁻¹ = n * e ^ (2 ^ (k' + 1)) := by
      intro e he
      have h1 : n * e * n⁻¹ = e ^ l := hl e he
      have h2 : e ^ l = e * e ^ (2 ^ (k' + 1)) := by
        rw [hl', hm']
        have : (1 + (2 : ℤ) ^ (k' + 1) * (2 * m' + 1)) =
            1 + (2 : ℤ) ^ (k' + 1) + (2 : ℤ) ^ (k' + 1 + 1) * m' := by ring
        rw [this, zpow_add, zpow_add, zpow_one, zpow_mul, hWz e he, one_zpow, mul_one, hcast]
      have h3 : e * n * e⁻¹ = n * (n * e * n⁻¹) * e⁻¹ := by
        rw [hniv]
        calc e * n * e⁻¹ = (n * n) * e * n * e⁻¹ := by rw [hn2, one_mul]
          _ = n * (n * e * n) * e⁻¹ := by group
      rw [h3, h1, h2, (Commute.self_pow e (2 ^ (k' + 1))).eq]
      group
    have hFin : ∀ y ∈ ({n, n * z, n * t} : Finset G), ∃ s ∈ (S : Subgroup G), s * n * s⁻¹ = y := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨1, one_mem _, by group⟩
      · exact ⟨u, d.hWS huW, by rw [hcls u huW, ← huz]⟩
      · exact ⟨v₀, d.hWS hv₀W, by rw [hcls v₀ hv₀W, ← hv₀t]⟩
    have h3 := R10.r_card_le_relIndex (S := (S : Subgroup G)) (b := n) hFin
    have hcard : ({n, n * z, n * t} : Finset G).card = 3 := by
      refine Finset.card_eq_three.mpr ⟨n, n * z, n * t, ?_, ?_, ?_, rfl⟩
      · intro h
        apply hz1
        have : n * 1 = n * z := by rw [mul_one]; exact h
        exact (mul_left_cancel this).symm
      · intro h
        apply d.viol.hzJ.ne_one
        have : n * 1 = n * t := by rw [mul_one]; exact h
        exact (mul_left_cancel this).symm
      · intro h
        exact d.late_ne_inv (mul_left_cancel h).symm
    rw [hcard] at h3
    rw [ha] at h3
    have : 2 ^ a ≤ 2 := by
      calc 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) ha1
        _ = 2 := by norm_num
    omega


theorem Std20.r9_exists_conj_into_S [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    {b : G} (hb : FieldInv20 S K K' W z t b) (hF : FusAt S z b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) {s : G} (hs2 : s * s = 1)
    (hsb : s * b = b * s) : ∃ c : G, c * b = b * c ∧ c⁻¹ * s * c ∈ (S : Subgroup G) := by
  have hup := d.r_relIndex_le_four c7 c9 h8 hb hk hu huo hact
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers s) := by
    have h1 : orderOf s ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hs2)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hPC : Subgroup.zpowers s ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hsb)
  obtain ⟨c, hcC, hc⟩ := R10.r_exists_conj_into_sylow (S := S) hb.sq hup
    (fun x hx => d.r9_four_le_relIndex c7 c9 h8 hb hF hk hu huo hx) hP hPC
  exact ⟨c, Subgroup.mem_centralizer_singleton_iff.mp hcC, hc s (Subgroup.mem_zpowers s)⟩

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
