module

public import CFSG.GH74.GLS.IVK.Lifted.TwoGroups
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2

public section

namespace CFSG.GH74.GLS.IVK.Lifted

section SDSq

open CFSG.GH74.GLS.Stage1.Thm3.Sec6 in
theorem sd_sq_not_z : SD_sq_not_z := by
  intro G _ _ P z y hq hz hz2 hz1 hy2 hyP hN ⟨n, hn4, ⟨ι⟩⟩
  obtain ⟨-, -, -, h4⟩ := sd_facts_main P z y hz hz2 hz1 hy2 hyP hN hn4 ι
  exact h4 (quatGroup_not_comm P hq)

end SDSq

section QuatCentr

open Subgroup CFSG QuaternionGroup

theorem quat_cases' {N : ℕ} (g : QuaternionGroup N) : (∃ i, g = a i) ∨ ∃ i, g = xa i := by
  cases g with
  | a i => exact Or.inl ⟨i, rfl⟩
  | xa i => exact Or.inr ⟨i, rfl⟩

theorem natCast_ne_zero_two_mul (N : ℕ) [NeZero N] : ((N : ℕ) : ZMod (2 * N)) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff N (2 * N)).1 h
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have := Nat.le_of_dvd hpos this
  omega

theorem zmod_add_self_eq_zero (N : ℕ) [NeZero N] (j : ZMod (2 * N)) (h : j + j = 0) :
    j = 0 ∨ j = (N : ZMod (2 * N)) := by
  have h1 : ((2 * j.val : ℕ) : ZMod (2 * N)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination h
  have h2 := (ZMod.natCast_eq_zero_iff (2 * j.val) (2 * N)).1 h1
  have h3 : N ∣ j.val := by
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by rw [hc]; ring)⟩
  have hv : j.val < 2 * N := ZMod.val_lt j
  obtain ⟨c, hc⟩ := h3
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc2 : c = 0 ∨ c = 1 := by
    have : c < 2 := by
      by_contra hcon
      push Not at hcon
      have : N * 2 ≤ N * c := Nat.mul_le_mul_left N hcon
      omega
    omega
  rcases hc2 with rfl | rfl
  · left
    have : j.val = 0 := by omega
    rw [← ZMod.natCast_zmod_val j, this]
    simp
  · right
    have : j.val = N := by omega
    rw [← ZMod.natCast_zmod_val j, this]

theorem quat_invol (N : ℕ) [NeZero N] (g : QuaternionGroup N) (hg : g * g = 1) (hg1 : g ≠ 1) :
    g = a (N : ZMod (2 * N)) := by
  cases g with
  | a i =>
    rw [a_mul_a, one_def] at hg
    have h := QuaternionGroup.a.inj hg
    rcases zmod_add_self_eq_zero N i (by simpa using h) with h0 | h0
    · exact absurd (by rw [h0, one_def]) hg1
    · rw [h0]
  | xa i =>
    rw [xa_mul_xa, one_def] at hg
    have h := QuaternionGroup.a.inj hg
    exfalso
    apply natCast_ne_zero_two_mul N
    linear_combination h

theorem quat_centr_C (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) (u' : QuaternionGroup N)
    (hu'sq : u' * u' = a (N : ZMod (2 * N)))
    (hnorm : ∀ p : QuaternionGroup N,
      p * u' * p⁻¹ = u' ∨ p * u' * p⁻¹ = u' * a (N : ZMod (2 * N))) :
    IsCyclic ↥(Subgroup.centralizer ({u'} : Set (QuaternionGroup N))) ∧
      (Subgroup.centralizer ({u'} : Set (QuaternionGroup N))).index = 2 := by
  have hcardG : Nat.card (QuaternionGroup N) = 4 * N := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hN0 := natCast_ne_zero_two_mul N
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rcases quat_cases' u' with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hi : i + i = (N : ZMod (2 * N)) := by
      rw [a_mul_a] at hu'sq
      exact QuaternionGroup.a.inj hu'sq
    have hC : Subgroup.centralizer ({a i} : Set (QuaternionGroup N)) = Subgroup.zpowers (a 1) := by
      apply le_antisymm
      · intro g hg
        rw [Subgroup.mem_centralizer_singleton_iff] at hg
        rcases quat_cases' g with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · refine ⟨(j.val : ℤ), ?_⟩
          simp only [zpow_natCast]
          rw [a_one_pow, ZMod.natCast_zmod_val]
        · exfalso
          rw [xa_mul_a, a_mul_xa] at hg
          have h := QuaternionGroup.xa.inj hg
          apply hN0
          rw [← hi]
          linear_combination h
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff, a_mul_a, a_mul_a, add_comm]
    rw [hC]
    refine ⟨inferInstance, ?_⟩
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers (a 1 : QuaternionGroup N))
    rw [Nat.card_zpowers, orderOf_a_one, hcardG] at h1
    nlinarith [h1]
  · have hN : N = 2 := by
      have h1 := hnorm (a 1)
      have e : a 1 * xa i * (a 1)⁻¹ = xa (i - 2) := by
        rw [a_mul_xa, quat_inv_a, xa_mul_a]
        congr 1
        ring
      rw [e] at h1
      rcases h1 with h | h
      · have h' := QuaternionGroup.xa.inj h
        have h2 : ((2 : ℕ) : ZMod (2 * N)) = 0 := by
          push_cast
          linear_combination -h'
        have h3 := (ZMod.natCast_eq_zero_iff 2 (2 * N)).1 h2
        have := Nat.le_of_dvd (by norm_num) h3
        omega
      · have h' : xa (i - 2) = xa (i + (N : ZMod (2 * N))) := by rw [h, xa_mul_a]
        have h'' := QuaternionGroup.xa.inj h'
        have h2 : ((N + 2 : ℕ) : ZMod (2 * N)) = 0 := by
          push_cast
          linear_combination -h''
        have h3 := (ZMod.natCast_eq_zero_iff (N + 2) (2 * N)).1 h2
        have := Nat.le_of_dvd (by omega) h3
        omega
    have hC : Subgroup.centralizer ({xa i} : Set (QuaternionGroup N)) = Subgroup.zpowers (xa i) := by
      apply le_antisymm
      · intro g hg
        rw [Subgroup.mem_centralizer_singleton_iff] at hg
        rcases quat_cases' g with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · rw [a_mul_xa, xa_mul_a] at hg
          have h := QuaternionGroup.xa.inj hg
          have h2 : j + j = 0 := by linear_combination -h
          rcases zmod_add_self_eq_zero N j h2 with rfl | rfl
          · rw [← one_def]
            exact one_mem _
          · have : (a (N : ZMod (2 * N)) : QuaternionGroup N) = xa i ^ 2 := by
              rw [sq, xa_mul_xa]
              congr 1
              ring
            rw [this]
            exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
        · rw [xa_mul_xa, xa_mul_xa] at hg
          have h := QuaternionGroup.a.inj hg
          have h2 : (i - j) + (i - j) = 0 := by linear_combination h
          rcases zmod_add_self_eq_zero N (i - j) h2 with h0 | h0
          · have : j = i := by linear_combination -h0
            rw [this]
            exact Subgroup.mem_zpowers _
          · have h2N : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self _
            push_cast at h2N
            have hj : j = (N : ZMod (2 * N)) + i := by
              linear_combination (-1 : ZMod (2 * N)) * h0 - h2N
            rw [hj, ← quat_inv_xa]
            exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    rw [hC]
    refine ⟨inferInstance, ?_⟩
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers (xa i : QuaternionGroup N))
    rw [Nat.card_zpowers, orderOf_xa, hcardG] at h1
    omega

theorem quat_centr_core (N : ℕ) [NeZero N] (hN2 : 2 ≤ N) {G : Type} [Group G] (P : Subgroup G)
    (ι : ↥P ≃* QuaternionGroup N) (z u : G) (hz : z ∈ P) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hu : u ∈ P)
    (huz : u * u = z) (hnorm : ∀ p ∈ P, p * u * p⁻¹ = u ∨ p * u * p⁻¹ = u * z) :
    IsCyclic ↥(P ⊓ centralizer ({u} : Set G)) ∧ (P ⊓ centralizer ({u} : Set G)).relIndex P = 2 := by
  set z' : QuaternionGroup N := ι ⟨z, hz⟩ with hz'
  set u' : QuaternionGroup N := ι ⟨u, hu⟩ with hu'
  have hz'sq : z' * z' = 1 := by
    rw [hz', ← map_mul]
    have : (⟨z, hz⟩ * ⟨z, hz⟩ : ↥P) = 1 := Subtype.ext (by simpa using hz2)
    rw [this, map_one]
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    have : (⟨z, hz⟩ : ↥P) = 1 := ι.injective (by rw [← hz', h, map_one])
    simpa using congrArg Subtype.val this
  have hz'a : z' = a (N : ZMod (2 * N)) := quat_invol N z' hz'sq hz'1
  have hu'sq : u' * u' = a (N : ZMod (2 * N)) := by
    rw [← hz'a, hu', hz', ← map_mul]
    congr 1
    exact Subtype.ext huz
  have hnorm' : ∀ p : QuaternionGroup N,
      p * u' * p⁻¹ = u' ∨ p * u' * p⁻¹ = u' * a (N : ZMod (2 * N)) := by
    intro p
    rcases hnorm ((ι.symm p : ↥P) : G) (ι.symm p).2 with h | h
    · left
      have h1 : ι.symm p * ⟨u, hu⟩ * (ι.symm p)⁻¹ = ⟨u, hu⟩ := Subtype.ext (by simpa using h)
      have := congrArg ι h1
      simpa [hu'] using this
    · right
      have h1 : ι.symm p * ⟨u, hu⟩ * (ι.symm p)⁻¹ = ⟨u, hu⟩ * ⟨z, hz⟩ :=
        Subtype.ext (by simpa using h)
      have := congrArg ι h1
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at this
      rw [← hz'a]
      exact this
  obtain ⟨hcyc, hidx⟩ := quat_centr_C N hN2 u' hu'sq hnorm'
  set C : Subgroup (QuaternionGroup N) := Subgroup.centralizer ({u'} : Set (QuaternionGroup N)) with hC
  have hCmap : ((P ⊓ centralizer ({u} : Set G)).subgroupOf P).map ι.toMonoidHom = C := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hC,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      have h1 : ι.symm x * ⟨u, hu⟩ = ⟨u, hu⟩ * ι.symm x := Subtype.ext h
      have := congrArg ι h1
      simpa [hu'] using this
    · intro h
      refine ⟨(ι.symm x).2, ?_⟩
      have h1 : ι.symm x * ⟨u, hu⟩ = ⟨u, hu⟩ * ι.symm x := by
        apply ι.injective
        simpa [hu'] using h
      exact congrArg Subtype.val h1
  refine ⟨?_, ?_⟩
  · have e1 : ↥(P ⊓ centralizer ({u} : Set G)) ≃* ↥C :=
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ centralizer ({u} : Set G) ≤ P)).symm.trans
        ((Subgroup.equivMapOfInjective _ ι.toMonoidHom ι.injective).trans
          (MulEquiv.subgroupCongr hCmap))
    exact e1.isCyclic.2 hcyc
  · show ((P ⊓ centralizer ({u} : Set G)).subgroupOf P).index = 2
    have h5 : (((P ⊓ centralizer ({u} : Set G)).subgroupOf P).map ι.toMonoidHom).index =
        ((P ⊓ centralizer ({u} : Set G)).subgroupOf P).index :=
      Subgroup.index_map_equiv ((P ⊓ centralizer ({u} : Set G)).subgroupOf P) ι
    rw [hCmap] at h5
    rw [← h5]
    exact hidx

open CFSG.GH74.GLS.Stage1.Thm3.Sec6 in
theorem quat_centr : Quat_centr := by
  intro G _ _ P z u n hq hz hz2 hz1 hu huz hnorm
  obtain ⟨hn3, ⟨ι⟩⟩ := hq
  have hNne : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hN2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact quat_centr_core (2 ^ (n - 2)) hN2 P ι z u hz hz2 hz1 hu huz hnorm

end QuatCentr

end CFSG.GH74.GLS.IVK.Lifted
