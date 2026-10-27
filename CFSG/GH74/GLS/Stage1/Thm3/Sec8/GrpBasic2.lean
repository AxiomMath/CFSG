module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

theorem mem_of_pow_card_eq_one {G : Type*} [Group G] [Finite G] {W V : Subgroup G} (hW : IsCyclic ↥W)
    (hV : V ≤ W) {w : G} (hw : w ∈ W) (hwn : w ^ Nat.card ↥V = 1) : w ∈ V := by
  have hVc : IsCyclic ↥V := isCyclic_of_le hV hW
  obtain ⟨a, haV, hagen⟩ := exists_generator_of_cyclic hVc
  have hao : orderOf a = Nat.card ↥V := by rw [hagen, Nat.card_zpowers]
  set d := orderOf w with hd
  have hdvdn : d ∣ Nat.card ↥V := orderOf_dvd_of_pow_eq_one hwn
  have hdvd : d ∣ orderOf a := by rw [hao]; exact hdvdn
  set c := a ^ (orderOf a / d) with hc
  have hco : orderOf c = d := orderOf_pow_orderOf_div (by rw [hao]; exact Nat.card_pos.ne') hdvd
  have hcV : c ∈ V := pow_mem haV _
  have hcW : c ∈ W := hV hcV
  let H : Subgroup ↥W := (Subgroup.zpowers w).subgroupOf W
  let K : Subgroup ↥W := (Subgroup.zpowers c).subgroupOf W
  have hwle : Subgroup.zpowers w ≤ W := by rw [Subgroup.zpowers_le]; exact hw
  have hcle : Subgroup.zpowers c ≤ W := by rw [Subgroup.zpowers_le]; exact hcW
  have hHK : H = K := by
    have := hW
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    have e1 : Nat.card ↥H = Nat.card ↥(Subgroup.zpowers w) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hwle).toEquiv
    have e2 : Nat.card ↥K = Nat.card ↥(Subgroup.zpowers c) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcle).toEquiv
    rw [e1, e2, Nat.card_zpowers, Nat.card_zpowers, hco]
  have hwH : (⟨w, hw⟩ : ↥W) ∈ H := Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers w)
  rw [hHK] at hwH
  have hwK : w ∈ Subgroup.zpowers c := Subgroup.mem_subgroupOf.1 hwH
  exact (Subgroup.zpowers_le.2 hcV) hwK

theorem GQ.exists_noncomm {G : Type*} [Group G] {Q : Subgroup G} {z : G} (hQ : GQ Q z) {y : G}
    (hyQ : y ∈ Q) (hy : 3 ≤ orderOf y) : ∃ x ∈ Q, x * y ≠ y * x := by
  obtain ⟨M, hMQ, hMc, hzM, hM4, hMi, hM⟩ := hQ.ex
  by_contra hcon
  push Not at hcon
  have hne : ∃ x ∈ Q, x ∉ M := by
    by_contra hcon'
    push Not at hcon'
    have h1 : M.relIndex Q = 1 := Subgroup.relIndex_eq_one.2 hcon'
    omega
  obtain ⟨x, hxQ, hxM⟩ := hne
  obtain ⟨hx2, hxinv⟩ := hM x hxQ hxM
  by_cases hyM : y ∈ M
  · have h1 := hxinv y hyM
    have h2 : x * y * x⁻¹ = y := by rw [hcon x hxQ]; group
    rw [h2] at h1
    have h3 : y * y = 1 := by
      calc y * y = y * y⁻¹⁻¹ := by group
        _ = y⁻¹ * y⁻¹⁻¹ := by rw [← h1]
        _ = 1 := by group
    have h4 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using h3)
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  · obtain ⟨hy2, hyinv⟩ := hM y hyQ hyM
    obtain ⟨m, hmM, hmgen⟩ := exists_generator_of_cyclic hMc
    have hmo : orderOf m = Nat.card ↥M := by rw [hmgen, Nat.card_zpowers]
    have hm2 : m * m ≠ 1 := by
      intro h
      have h4 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using h)
      have := Nat.le_of_dvd (by norm_num) h4
      omega
    have h1 := hyinv m hmM
    have h2 : y * m * y⁻¹ = m := by
      have h3 : y * m = m * y := (hcon m (hMQ hmM)).symm
      calc y * m * y⁻¹ = m * y * y⁻¹ := by rw [h3]
        _ = m := by group
    rw [h2] at h1
    apply hm2
    calc m * m = m * m⁻¹⁻¹ := by group
      _ = m⁻¹ * m⁻¹⁻¹ := by rw [← h1]
      _ = 1 := by group

theorem mul_inv_mem_of_relIndex_two {G : Type*} [Group G] {W Q : Subgroup G} (hWi : W.relIndex Q = 2)
    {x q : G} (hx : x ∈ Q) (hq : q ∈ Q) (hxW : x ∉ W) (hqW : q ∉ W) : x * q⁻¹ ∈ W := by
  have hi : (W.subgroupOf Q).index = 2 := hWi
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hi
  have hx' : (⟨x, hx⟩ : ↥Q) ∉ W.subgroupOf Q := hxW
  have hq' : (⟨q, hq⟩ : ↥Q) ∉ W.subgroupOf Q := hqW
  have h1 := (ha ⟨x, hx⟩)
  have h2 := (ha ⟨q, hq⟩)
  have h3 : ⟨x, hx⟩ * a ∈ W.subgroupOf Q := by
    rcases h1 with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hx'
  have h4 : ⟨q, hq⟩ * a ∈ W.subgroupOf Q := by
    rcases h2 with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hq'
  have h5 := mul_mem h3 (inv_mem h4)
  have : (⟨x, hx⟩ : ↥Q) * a * (⟨q, hq⟩ * a)⁻¹ = ⟨x, hx⟩ * ⟨q, hq⟩⁻¹ := by group
  rw [this] at h5
  exact h5

theorem GQ.mem_of_commute {G : Type*} [Group G] {Q : Subgroup G} {z : G} (hQ : GQ Q z)
    {W V : Subgroup G} (hWQ : W ≤ Q) (hWc : IsCyclic ↥W) (hWi : W.relIndex Q = 2) (hVW : V ≤ W)
    (hV : 4 ≤ Nat.card ↥V) {q : G} (hq : q ∈ Q) (hcomm : ∀ v ∈ V, q * v = v * q) : q ∈ W := by
  by_contra hqW
  have hVc : IsCyclic ↥V := isCyclic_of_le hVW hWc
  obtain ⟨g, hgV, hgen⟩ := exists_generator_of_cyclic hVc
  have hgo : orderOf g = Nat.card ↥V := by rw [hgen, Nat.card_zpowers]
  have hgW : g ∈ W := hVW hgV
  obtain ⟨x, hxQ, hx⟩ := hQ.exists_noncomm (hWQ hgW) (by omega : 3 ≤ orderOf g)
  apply hx
  by_cases hxW : x ∈ W
  · exact cyclic_comm hWc x hxW g hgW
  · have h1 := mul_inv_mem_of_relIndex_two hWi hxQ hq hxW hqW
    have h2 : x = (x * q⁻¹) * q := by group
    rw [h2]
    calc x * q⁻¹ * q * g = (x * q⁻¹) * (q * g) := by group
      _ = (x * q⁻¹) * (g * q) := by rw [hcomm g hgV]
      _ = ((x * q⁻¹) * g) * q := by group
      _ = (g * (x * q⁻¹)) * q := by rw [cyclic_comm hWc _ h1 g hgW]
      _ = g * (x * q⁻¹ * q) := by group


theorem GQ.cyclic_unique {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {z : G} (hQ : GQ Q z)
    (h16 : 16 ≤ Nat.card ↥Q) {C D : Subgroup G} (hCQ : C ≤ Q) (hCc : IsCyclic ↥C)
    (hC : 2 * Nat.card ↥C = Nat.card ↥Q) (hDQ : D ≤ Q) (hDc : IsCyclic ↥D)
    (hD : 2 * Nat.card ↥D = Nat.card ↥Q) : C = D := by
  obtain ⟨M, hMQ, hMc, hzM, hM4, hMi, hM⟩ := hQ.ex
  have hMcard : 2 * Nat.card ↥M = Nat.card ↥Q := by
    have := card_mul_relIndex_of_le hMQ
    rw [hMi] at this
    omega
  have key : ∀ C : Subgroup G, C ≤ Q → IsCyclic ↥C → 2 * Nat.card ↥C = Nat.card ↥Q → C = M := by
    intro C hCQ hCc hC
    obtain ⟨g, hgC, hgen⟩ := exists_generator_of_cyclic hCc
    have hgo : orderOf g = Nat.card ↥C := by rw [hgen, Nat.card_zpowers]
    have hgM : g ∈ M := by
      by_contra hgM
      obtain ⟨hg2, -⟩ := hM g (hCQ hgC) hgM
      have h4 : g ^ 4 = 1 := by
        rw [pow_four_eq, hg2, hQ.z_sq]
      have h5 : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one h4
      have h6 := Nat.le_of_dvd (by norm_num) h5
      omega
    have hCM : C ≤ M := by
      rw [hgen, Subgroup.zpowers_le]; exact hgM
    exact Subgroup.eq_of_le_of_card_ge hCM (by omega)
  rw [key C hCQ hCc hC, key D hDQ hDc hD]

theorem pow_card_of_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    x ^ Nat.card ↥H = 1 := by
  have h1 : (⟨x, hx⟩ : ↥H) ^ Nat.card ↥H = 1 := pow_card_eq_one'
  have h3 := congrArg Subtype.val h1
  rw [Subgroup.coe_pow] at h3
  exact h3

theorem exists_involution_of_cyclic {G : Type*} [Group G] {W : Subgroup G} (hW : IsCyclic ↥W) {j : ℕ}
    (hcard : Nat.card ↥W = 2 ^ (j + 1)) : ∃ x ∈ W, x * x = 1 ∧ x ≠ 1 := by
  obtain ⟨g, hgW, hgen⟩ := exists_generator_of_cyclic hW
  have hgo : orderOf g = 2 ^ (j + 1) := by rw [← hcard, hgen, Nat.card_zpowers]
  refine ⟨g ^ (2 ^ j), pow_mem hgW _, ?_, ?_⟩
  · rw [← pow_two, ← pow_mul, show 2 ^ j * 2 = 2 ^ (j + 1) by ring, ← hgo]
    exact pow_orderOf_eq_one g
  · intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hgo] at h1
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem comm_sup_of_comm {G : Type*} [Group G] {A B : Subgroup G}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := mem_sup_of_commute' hAB hx
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := mem_sup_of_commute' hAB hy
  calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
    _ = a₁ * (a₂ * b₁) * b₂ := by rw [← hAB a₂ ha₂ b₁ hb₁]
    _ = (a₁ * a₂) * (b₁ * b₂) := by group
    _ = (a₂ * a₁) * (b₂ * b₁) := by rw [hA a₁ ha₁ a₂ ha₂, hB b₁ hb₁ b₂ hb₂]
    _ = a₂ * (a₁ * b₂) * b₁ := by group
    _ = a₂ * (b₂ * a₁) * b₁ := by rw [hAB a₁ ha₁ b₂ hb₂]
    _ = a₂ * b₂ * (a₁ * b₁) := by group

theorem GQ.z_central {G : Type*} [Group G] {Q : Subgroup G} {z : G} (hQ : GQ Q z) {x : G} (hx : x ∈ Q) :
    x * z = z * x := by
  have hxz : x * z * x⁻¹ ∈ Q := mul_mem (mul_mem hx hQ.z_mem) (inv_mem hx)
  have h2 : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
    calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hQ.z_sq]; group
  rcases hQ.uniq _ hxz h2 with h | h
  · exfalso
    apply hQ.z_ne
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, h]; group
  · calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [h]

theorem GQ.conj_gen_cyclic4 {G : Type*} [Group G] {Q : Subgroup G} {z : G} (hQ : GQ Q z) {C : Subgroup G}
    (hCQ : C ≤ Q) {g : G} (hgC : g ∈ C) (hgen : C = Subgroup.zpowers g) (hg4 : orderOf g = 4) {s : G}
    (hsC : ∀ c ∈ C, s * c * s⁻¹ ∈ C) : s * g * s⁻¹ * g⁻¹ ∈ Subgroup.zpowers z := by
  have h4 : g ^ 4 = 1 := by have := pow_orderOf_eq_one g; rwa [hg4] at this
  have hgQ : g ∈ Q := hCQ hgC
  have hg2ne : g * g ≠ 1 := by
    intro h
    have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hg2 : g * g = z := by
    have h1 : (g * g) * (g * g) = 1 := by rw [← pow_four_eq]; exact h4
    rcases hQ.uniq (g * g) (mul_mem hgQ hgQ) h1 with h | h
    · exact absurd h hg2ne
    · exact h
  have hzC : z ∈ C := by rw [← hg2]; exact mul_mem hgC hgC
  have hszs : s * z * s⁻¹ = z := by
    have hmem : s * z * s⁻¹ ∈ C := hsC z hzC
    have h2 : (s * z * s⁻¹) * (s * z * s⁻¹) = 1 := by
      calc (s * z * s⁻¹) * (s * z * s⁻¹) = s * (z * z) * s⁻¹ := by group
        _ = 1 := by rw [hQ.z_sq]; group
    rcases hQ.uniq _ (hCQ hmem) h2 with h | h
    · exfalso
      apply hQ.z_ne
      have : z = s⁻¹ * (s * z * s⁻¹) * s := by group
      rw [this, h]; group
    · exact h
  have hsg : s * g * s⁻¹ ∈ C := hsC g hgC
  have hsg' := hsg
  rw [hgen] at hsg'
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hsg'
  have hmod : g ^ m = g ^ (m % 4) := by
    have := zpow_mod_orderOf g m
    rw [hg4] at this
    exact_mod_cast this.symm
  have hr0 : 0 ≤ m % 4 := Int.emod_nonneg _ (by norm_num)
  have hr4 : m % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le hr0
  rw [hr] at hmod
  have hsq : (s * g * s⁻¹) * (s * g * s⁻¹) = z := by
    calc (s * g * s⁻¹) * (s * g * s⁻¹) = s * (g * g) * s⁻¹ := by group
      _ = z := by rw [hg2, hszs]
  rw [← hm, hmod] at hsq
  have hrlt : r < 4 := by omega
  interval_cases r
  · exfalso
    simp at hsq
    exact hQ.z_ne hsq.symm
  · have : s * g * s⁻¹ = g := by rw [← hm, hmod]; simp
    rw [this]; simp
  · exfalso
    have : g ^ 2 * g ^ 2 = 1 := by rw [← pow_add]; exact h4
    simp only [zpow_natCast] at hsq
    rw [this] at hsq
    exact hQ.z_ne hsq.symm
  · have : s * g * s⁻¹ = g ^ 3 := by rw [← hm, hmod]; simp
    rw [this]
    have e : g ^ 3 * g⁻¹ = g * g := by rw [pow_three]; group
    rw [e, hg2]
    exact Subgroup.mem_zpowers z

theorem GQ.Q8_comm_mod_z {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {z : G} (hQ : GQ Q z)
    (h8 : Nat.card ↥Q = 8) {C D : Subgroup G} (hCQ : C ≤ Q) (hCc : IsCyclic ↥C) (hC : Nat.card ↥C = 4)
    (hDQ : D ≤ Q) (hDc : IsCyclic ↥D) (hD : Nat.card ↥D = 4) (hCD : C ≠ D) {s : G}
    (hsC : ∀ c ∈ C, s * c * s⁻¹ ∈ C) (hsD : ∀ d ∈ D, s * d * s⁻¹ ∈ D) :
    ∀ p ∈ Q, s * p * s⁻¹ * p⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨g, hgC, hgen⟩ := exists_generator_of_cyclic hCc
  obtain ⟨g', hg'D, hgen'⟩ := exists_generator_of_cyclic hDc
  have hg4 : orderOf g = 4 := by rw [← hC, hgen, Nat.card_zpowers]
  have hg4' : orderOf g' = 4 := by rw [← hD, hgen', Nat.card_zpowers]
  have hs₁ := hQ.conj_gen_cyclic4 hCQ hgC hgen hg4 hsC
  have hs₂ := hQ.conj_gen_cyclic4 hDQ hg'D hgen' hg4' hsD
  let T : Subgroup G :=
    { carrier := {p | p ∈ Q ∧ s * p * s⁻¹ * p⁻¹ ∈ Subgroup.zpowers z}
      mul_mem' := by
        rintro a b ⟨haQ, ha⟩ ⟨hbQ, hb⟩
        refine ⟨mul_mem haQ hbQ, ?_⟩
        have hzb : ∀ w ∈ Subgroup.zpowers z, a * w * a⁻¹ = w := by
          intro w hw
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
          have hc : Commute a z := hQ.z_central haQ
          rw [(Commute.zpow_right hc m).eq]; group
        have e : s * (a * b) * s⁻¹ * (a * b)⁻¹ =
            (s * a * s⁻¹ * a⁻¹) * (a * (s * b * s⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e, hzb _ hb]
        exact mul_mem ha hb
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨haQ, ha⟩
        refine ⟨inv_mem haQ, ?_⟩
        have hzb : ∀ w ∈ Subgroup.zpowers z, a⁻¹ * w * a = w := by
          intro w hw
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
          have hc : Commute a z := hQ.z_central haQ
          rw [(Commute.zpow_right hc m).inv_left.eq]; group
        have e : s * a⁻¹ * s⁻¹ * a⁻¹⁻¹ = a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e, hzb _ (inv_mem ha)]
        exact inv_mem ha }
  have hgT : g ∈ T := ⟨hCQ hgC, hs₁⟩
  have hgT' : g' ∈ T := ⟨hDQ hg'D, hs₂⟩
  have hCT : C ≤ T := by rw [hgen, Subgroup.zpowers_le]; exact hgT
  have hDT : D ≤ T := by rw [hgen', Subgroup.zpowers_le]; exact hgT'
  have hCDQ : C ⊔ D ≤ Q := sup_le hCQ hDQ
  have hCD4 : 4 < Nat.card ↥(C ⊔ D) := by
    have h1 : Nat.card ↥C ≤ Nat.card ↥(C ⊔ D) := Subgroup.card_le_of_le le_sup_left
    by_contra hcon
    have h2 : Nat.card ↥(C ⊔ D) = 4 := by omega
    have h3 : C = C ⊔ D := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    have h4' : D ≤ C := by rw [h3]; exact le_sup_right
    exact hCD (Subgroup.eq_of_le_of_card_ge h4' (by omega)).symm
  have hdvd : Nat.card ↥(C ⊔ D) ∣ Nat.card ↥Q := Subgroup.card_dvd_of_le hCDQ
  have hCDeq : Nat.card ↥(C ⊔ D) = 8 := by
    rw [h8] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hh : Nat.card ↥(C ⊔ D) <;> simp_all
  have hQCD : C ⊔ D = Q := Subgroup.eq_of_le_of_card_ge hCDQ (by omega)
  intro p hp
  have : p ∈ C ⊔ D := by rw [hQCD]; exact hp
  exact (sup_le hCT hDT this).2

theorem GQ.outside_cyclic {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {z : G} (hQ : GQ Q z)
    {j : ℕ} (hj : Nat.card ↥Q = 2 ^ j) {C : Subgroup G} (hCQ : C ≤ Q) (hCc : IsCyclic ↥C)
    (hC : 2 * Nat.card ↥C = Nat.card ↥Q) (h4 : 4 ≤ Nat.card ↥C) {y : G} (hy : y ∈ Q) (hyC : y ∉ C) :
    y * y = z ∧ ∀ c ∈ C, y * c * y⁻¹ = c⁻¹ := by
  obtain ⟨M, hMQ, hMc, hzM, hM4, hMi, hM⟩ := hQ.ex
  have hMcard : 2 * Nat.card ↥M = Nat.card ↥Q := by
    have := card_mul_relIndex_of_le hMQ
    rw [hMi] at this
    omega
  by_cases hCM : C = M
  · subst hCM
    obtain ⟨h1, h2⟩ := hM y hy hyC
    exact ⟨h1, h2⟩
  · have h8 : Nat.card ↥Q = 8 := by
      by_contra hne
      have h16 : 16 ≤ Nat.card ↥Q := by
        have hj3 : 3 ≤ j := by
          by_contra hcon
          have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hj4 : 4 ≤ j := by
          by_contra hcon
          have : j = 3 := by omega
          subst this
          exact hne hj
        have : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj4
        omega
      exact hCM (hQ.cyclic_unique h16 hCQ hCc hC hMQ hMc hMcard)
    have hC4 : Nat.card ↥C = 4 := by omega
    have hM4' : Nat.card ↥M = 4 := by omega
    obtain ⟨g, hgC, hgen⟩ := exists_generator_of_cyclic hCc
    have hg4 : orderOf g = 4 := by rw [← hC4, hgen, Nat.card_zpowers]
    have hCi : C.relIndex Q = 2 := by
      have := card_mul_relIndex_of_le hCQ
      have hpos : 0 < Nat.card ↥C := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (by omega)
    have hN : (C.subgroupOf Q).Normal := Subgroup.normal_of_index_eq_two hCi
    have hsC : ∀ c ∈ C, y * c * y⁻¹ ∈ C := fun c hc => hN.conj_mem ⟨c, hCQ hc⟩ hc ⟨y, hy⟩
    have h1 := hQ.conj_gen_cyclic4 hCQ hgC hgen hg4 hsC
    have h4' : g ^ 4 = 1 := by have := pow_orderOf_eq_one g; rwa [hg4] at this
    have hgQ : g ∈ Q := hCQ hgC
    have hg2ne : g * g ≠ 1 := by
      intro h
      have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using h)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have hg2 : g * g = z := by
      have h1' : (g * g) * (g * g) = 1 := by rw [← pow_four_eq]; exact h4'
      rcases hQ.uniq (g * g) (mul_mem hgQ hgQ) h1' with h | h
      · exact absurd h hg2ne
      · exact h
    have hzC : z ∈ C := by rw [← hg2]; exact mul_mem hgC hgC
    have hy2 : y * y = z := by
      by_cases hyM : y ∈ M
      · have hy4 : y ^ 4 = 1 := by
          have := pow_card_of_mem hyM
          rwa [hM4'] at this
        have h1' : (y * y) * (y * y) = 1 := by rw [← pow_four_eq]; exact hy4
        rcases hQ.uniq (y * y) (mul_mem hy hy) h1' with h | h
        · exfalso
          rcases hQ.uniq y hy h with h' | h'
          · exact hyC (h' ▸ one_mem C)
          · exact hyC (h' ▸ hzC)
        · exact h
      · exact (hM y hy hyM).1
    have hcQ : y * g * y⁻¹ * g⁻¹ ∈ Q := mul_mem (mul_mem (mul_mem hy hgQ) (inv_mem hy)) (inv_mem hgQ)
    have hc2 : (y * g * y⁻¹ * g⁻¹) * (y * g * y⁻¹ * g⁻¹) = 1 := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h1
      rw [← hm, ← zpow_add, show m + m = 2 * m by ring, zpow_mul]
      have : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hQ.z_sq]
      rw [this, one_zpow]
    rcases hQ.uniq _ hcQ hc2 with hc | hc
    · exfalso
      have hyg : y * g = g * y := by
        have : y * g * y⁻¹ = g := by
          have := congrArg (· * g) hc
          simpa using this
        calc y * g = (y * g * y⁻¹) * y := by group
          _ = g * y := by rw [this]
      obtain ⟨x, hxQ, hx⟩ := hQ.exists_noncomm hgQ (by omega : 3 ≤ orderOf g)
      apply hx
      by_cases hxC : x ∈ C
      · rw [hgen] at hxC
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hxC
        rw [← hn]
        exact ((Commute.refl g).zpow_left n).eq
      · have h5 := mul_inv_mem_of_relIndex_two hCi hxQ hy hxC hyC
        rw [hgen] at h5
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h5
        have e : x = g ^ n * y := by rw [hn]; group
        rw [e]
        calc g ^ n * y * g = g ^ n * (y * g) := by group
          _ = g ^ n * (g * y) := by rw [hyg]
          _ = g * (g ^ n * y) := by
            rw [← mul_assoc, ← mul_assoc, ((Commute.refl g).zpow_left n).eq]
    · have hyg : y * g * y⁻¹ = g⁻¹ := by
        have e : y * g * y⁻¹ = z * g := by
          calc y * g * y⁻¹ = (y * g * y⁻¹ * g⁻¹) * g := by group
            _ = z * g := by rw [hc]
        have e3 : g * g * g = g⁻¹ :=
          eq_inv_of_mul_eq_one_left (by rw [← h4', pow_four_eq]; group)
        rw [e, ← hg2, e3]
      refine ⟨hy2, fun c hcC => ?_⟩
      rw [hgen] at hcC
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hcC
      rw [← hn, ← zpow_neg]
      calc y * g ^ n * y⁻¹ = (y * g * y⁻¹) ^ n := by rw [conj_zpow]
        _ = (g⁻¹) ^ n := by rw [hyg]
        _ = g ^ (-n) := by rw [inv_zpow']

theorem comm_of_index_two {D : Type*} [Group D] (R : Subgroup D) (hR : R.index = 2)
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) {y : D} (hy : y ∉ R)
    (hyc : ∀ r ∈ R, y * r = r * y) : ∀ a b : D, a * b = b * a := by
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.1 hR
  have key : ∀ a : D, a ∈ R ∨ ∃ r ∈ R, a = r * y := by
    intro a
    by_cases ha : a ∈ R
    · exact Or.inl ha
    · right
      have h1 : a * c ∈ R := by
        rcases hc a with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h ha
      have h2 : y * c ∈ R := by
        rcases hc y with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h hy
      refine ⟨a * y⁻¹, ?_, by group⟩
      have h3 := mul_mem h1 (inv_mem h2)
      have : a * c * (y * c)⁻¹ = a * y⁻¹ := by group
      rwa [this] at h3
  intro a b
  rcases key a with ha | ⟨r₁, hr₁, rfl⟩ <;> rcases key b with hb | ⟨r₂, hr₂, rfl⟩
  · exact hRc a ha b hb
  · calc a * (r₂ * y) = (a * r₂) * y := by group
      _ = (r₂ * a) * y := by rw [hRc a ha r₂ hr₂]
      _ = r₂ * (a * y) := by group
      _ = r₂ * (y * a) := by rw [← hyc a ha]
      _ = r₂ * y * a := by group
  · calc r₁ * y * b = r₁ * (y * b) := by group
      _ = r₁ * (b * y) := by rw [hyc b hb]
      _ = (r₁ * b) * y := by group
      _ = (b * r₁) * y := by rw [hRc r₁ hr₁ b hb]
      _ = b * (r₁ * y) := by group
  · calc r₁ * y * (r₂ * y) = r₁ * (y * r₂) * y := by group
      _ = r₁ * (r₂ * y) * y := by rw [hyc r₂ hr₂]
      _ = (r₁ * r₂) * (y * y) := by group
      _ = (r₂ * r₁) * (y * y) := by rw [hRc r₁ hr₁ r₂ hr₂]
      _ = r₂ * (r₁ * y) * y := by group
      _ = r₂ * (y * r₁) * y := by rw [← hyc r₁ hr₁]
      _ = r₂ * y * (r₁ * y) := by group

@[expose] def Rimg {G : Type*} [Group G] (S₁ Q V : Subgroup G) [(Q.subgroupOf S₁).Normal] :
    Subgroup (↥S₁ ⧸ Q.subgroupOf S₁) :=
  (V.subgroupOf S₁).map (QuotientGroup.mk' (Q.subgroupOf S₁))

theorem mem_Rimg_iff {G : Type*} [Group G] {S₁ Q V : Subgroup G} [(Q.subgroupOf S₁).Normal]
    (hVS : V ≤ S₁) {x : G} (hx : x ∈ S₁) :
    (QuotientGroup.mk ⟨x, hx⟩ : ↥S₁ ⧸ Q.subgroupOf S₁) ∈ Rimg S₁ Q V ↔
      ∃ v ∈ V, ∃ q ∈ Q, x = v * q := by
  constructor
  · intro h
    obtain ⟨v₀, hv₀, hv⟩ := Subgroup.mem_map.1 h
    have h1 : v₀⁻¹ * ⟨x, hx⟩ ∈ Q.subgroupOf S₁ := QuotientGroup.eq.1 hv
    have h2 : ((v₀ : G))⁻¹ * x ∈ Q := h1
    exact ⟨(v₀ : G), hv₀, (v₀ : G)⁻¹ * x, h2, by group⟩
  · rintro ⟨v, hv, q, hq, rfl⟩
    refine Subgroup.mem_map.2 ⟨⟨v, hVS hv⟩, hv, ?_⟩
    apply QuotientGroup.eq.2
    show ((⟨v, hVS hv⟩ : ↥S₁))⁻¹ * ⟨v * q, hx⟩ ∈ Q.subgroupOf S₁
    show (v⁻¹ * (v * q) : G) ∈ Q
    simpa using hq

theorem Rimg_index {G : Type*} [Group G] [Finite G] {S₁ Q V : Subgroup G}
    [hN : (Q.subgroupOf S₁).Normal] (hQS : Q ≤ S₁) (hVS : V ≤ S₁) (hVQ : V ⊓ Q = ⊥)
    (hcard : Nat.card ↥S₁ = 2 * Nat.card ↥V * Nat.card ↥Q) : (Rimg S₁ Q V).index = 2 := by
  let π : ↥S₁ →* (↥S₁ ⧸ Q.subgroupOf S₁) := QuotientGroup.mk' (Q.subgroupOf S₁)
  let VS : Subgroup ↥S₁ := V.subgroupOf S₁
  have hinj : Function.Injective (π.comp VS.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h0 : π (a : ↥S₁) = 1 := ha
    have h1 : ((a : ↥S₁)) ∈ Q.subgroupOf S₁ := (QuotientGroup.eq_one_iff _).1 h0
    have h2 : (((a : ↥S₁)) : G) ∈ V ⊓ Q := ⟨a.2, h1⟩
    rw [hVQ] at h2
    exact Subtype.ext (Subtype.ext (by simpa using h2))
  have hRcard : Nat.card ↥(Rimg S₁ Q V) = Nat.card ↥V := by
    have h1 : Rimg S₁ Q V = (π.comp VS.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]; rfl
    have h2 : Nat.card ↥(Rimg S₁ Q V) = Nat.card ↥VS := by
      rw [h1]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [h2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv
  have hXcard : Nat.card (↥S₁ ⧸ Q.subgroupOf S₁) * Nat.card ↥Q = Nat.card ↥S₁ := by
    have h1 : Nat.card ↥(Q.subgroupOf S₁) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf S₁)
    rw [h1] at this
    exact this.symm
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have hVpos : 0 < Nat.card ↥V := Nat.card_pos
  have hDcard : Nat.card (↥S₁ ⧸ Q.subgroupOf S₁) = 2 * Nat.card ↥V := by
    have : Nat.card (↥S₁ ⧸ Q.subgroupOf S₁) * Nat.card ↥Q = (2 * Nat.card ↥V) * Nat.card ↥Q := by
      rw [hXcard, hcard]
    exact Nat.eq_of_mul_eq_mul_right hQpos this
  have h1 := Subgroup.index_mul_card (Rimg S₁ Q V)
  rw [hRcard, hDcard] at h1
  exact Nat.eq_of_mul_eq_mul_right hVpos (by omega)

theorem mem_sup_of_centralizes {G : Type*} [Group G] [Finite G] {S₁ Q V : Subgroup G}
    [hN : (Q.subgroupOf S₁).Normal] (hQS : Q ≤ S₁) (hVS : V ≤ S₁) (hVQ : V ⊓ Q = ⊥)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hcard : Nat.card ↥S₁ = 2 * Nat.card ↥V * Nat.card ↥Q)
    (hnab : ∃ a b : ↥S₁ ⧸ Q.subgroupOf S₁, a * b ≠ b * a) {x : G} (hx : x ∈ S₁)
    (hxc : ∀ v ∈ V, x * v = v * x) : ∃ v ∈ V, ∃ q ∈ Q, x = v * q := by
  have hRindex := Rimg_index hQS hVS hVQ hcard
  by_cases hxR : (QuotientGroup.mk ⟨x, hx⟩ : ↥S₁ ⧸ Q.subgroupOf S₁) ∈ Rimg S₁ Q V
  · exact (mem_Rimg_iff hVS hx).1 hxR
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    refine hab (comm_of_index_two (Rimg S₁ Q V) hRindex ?_ hxR ?_ a b)
    · rintro _ ⟨a₀, ha₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hVc _ ha₀ _ hb₀)
    · rintro _ ⟨r₀, hr₀, rfl⟩
      show (QuotientGroup.mk' (Q.subgroupOf S₁)) ⟨x, hx⟩ * (QuotientGroup.mk' (Q.subgroupOf S₁)) r₀ =
        (QuotientGroup.mk' (Q.subgroupOf S₁)) r₀ * (QuotientGroup.mk' (Q.subgroupOf S₁)) ⟨x, hx⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hxc _ hr₀)

theorem conj_mem_sup {G : Type*} [Group G] [Finite G] {S₁ Q V : Subgroup G}
    [hN : (Q.subgroupOf S₁).Normal] (hQS : Q ≤ S₁) (hVS : V ≤ S₁) (hVQ : V ⊓ Q = ⊥)
    (hcard : Nat.card ↥S₁ = 2 * Nat.card ↥V * Nat.card ↥Q) {s v : G} (hs : s ∈ S₁) (hv : v ∈ V) :
    ∃ v' ∈ V, ∃ q ∈ Q, s * v * s⁻¹ = v' * q := by
  have hRindex := Rimg_index hQS hVS hVQ hcard
  have : (Rimg S₁ Q V).Normal := Subgroup.normal_of_index_eq_two hRindex
  have hx : s * v * s⁻¹ ∈ S₁ := mul_mem (mul_mem hs (hVS hv)) (inv_mem hs)
  rw [← mem_Rimg_iff hVS hx]
  have h1 : (QuotientGroup.mk ⟨v, hVS hv⟩ : ↥S₁ ⧸ Q.subgroupOf S₁) ∈ Rimg S₁ Q V :=
    (mem_Rimg_iff hVS (hVS hv)).2 ⟨v, hv, 1, one_mem _, by simp⟩
  have h2 := this.conj_mem _ h1 (QuotientGroup.mk ⟨s, hs⟩)
  have h3 : (QuotientGroup.mk ⟨s, hs⟩ : ↥S₁ ⧸ Q.subgroupOf S₁) * QuotientGroup.mk ⟨v, hVS hv⟩ *
      (QuotientGroup.mk ⟨s, hs⟩)⁻¹ = QuotientGroup.mk ⟨s * v * s⁻¹, hx⟩ := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  rw [h3] at h2
  exact h2

theorem pow_two_pow_mul {G : Type*} [Group G] {q v c : G} {k : ℕ} (hk : 2 ≤ k)
    (hc2 : c * c = 1) (hv : v ^ (2 ^ k) = 1) (hqv : v * q * v⁻¹ = q * c)
    (h1 : Commute (q * q) v) (h2 : Commute c v) (h3 : Commute (q * q) c) :
    (q * v) ^ (2 ^ k) = q ^ (2 ^ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hvq : v * q = q * c * v := by
    have : v * q * v⁻¹ * v = q * c * v := by rw [hqv]
    simpa using this
  have hsq : (q * v) * (q * v) = ((q * q) * c) * (v * v) := by
    calc (q * v) * (q * v) = q * (v * q) * v := by group
      _ = q * (q * c * v) * v := by rw [hvq]
      _ = ((q * q) * c) * (v * v) := by group
  have hpow : (q * v) ^ (2 ^ (j + 2)) = ((q * v) * (q * v)) ^ (2 ^ (j + 1)) := by
    rw [← pow_two, ← pow_mul]
    congr 1
    ring
  rw [hpow, hsq]
  have hcd : Commute c (v * v) := h2.mul_right h2
  have had : Commute (q * q) (v * v) := h1.mul_right h1
  have hacd : Commute ((q * q) * c) (v * v) := had.mul_left hcd
  rw [hacd.mul_pow, h3.mul_pow]
  have hvv : (v * v) ^ (2 ^ (j + 1)) = 1 := by
    rw [← pow_two, ← pow_mul, show 2 * 2 ^ (j + 1) = 2 ^ (j + 2) by ring]
    exact hv
  have hcc : c ^ (2 ^ (j + 1)) = 1 := by
    rw [show 2 ^ (j + 1) = 2 * 2 ^ j by ring, pow_mul, pow_two, hc2, one_pow]
  rw [hvv, hcc, mul_one, mul_one, ← pow_two, ← pow_mul]
  congr 1
  ring

theorem pow_two_pow_mul_gen {G : Type*} [Group G] {q v c : G} {k : ℕ} (hk : 2 ≤ k)
    (hc2 : c * c = 1) (hqv : v * q * v⁻¹ = q * c)
    (h1 : Commute (q * q) v) (h2 : Commute c v) (h3 : Commute (q * q) c) :
    (q * v) ^ (2 ^ k) = q ^ (2 ^ k) * v ^ (2 ^ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hvq : v * q = q * c * v := by
    have : v * q * v⁻¹ * v = q * c * v := by rw [hqv]
    simpa using this
  have hsq : (q * v) * (q * v) = ((q * q) * c) * (v * v) := by
    calc (q * v) * (q * v) = q * (v * q) * v := by group
      _ = q * (q * c * v) * v := by rw [hvq]
      _ = ((q * q) * c) * (v * v) := by group
  have hpow : (q * v) ^ (2 ^ (j + 2)) = ((q * v) * (q * v)) ^ (2 ^ (j + 1)) := by
    rw [← pow_two, ← pow_mul]
    congr 1
    ring
  rw [hpow, hsq]
  have hcd : Commute c (v * v) := h2.mul_right h2
  have had : Commute (q * q) (v * v) := h1.mul_right h1
  have hacd : Commute ((q * q) * c) (v * v) := had.mul_left hcd
  rw [hacd.mul_pow, h3.mul_pow]
  have hcc : c ^ (2 ^ (j + 1)) = 1 := by
    rw [show 2 ^ (j + 1) = 2 * 2 ^ j by ring, pow_mul, pow_two, hc2, one_pow]
  rw [hcc, mul_one, ← pow_two, ← pow_two, ← pow_mul, ← pow_mul]
  congr 2 <;> ring

theorem conj_dichotomy {G : Type*} [Group G] {z q v : G} {W : Subgroup G}
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (huniq : ∀ c ∈ W, c * c = 1 → c = 1 ∨ c = z)
    (hq : q ∈ W) (hvq : v * q * v⁻¹ ∈ W) (hsq : v * (q * q) = (q * q) * v) :
    ∃ c, (c = 1 ∨ c = z) ∧ v * q * v⁻¹ = q * c := by
  refine ⟨q⁻¹ * (v * q * v⁻¹), ?_, by group⟩
  apply huniq _ (mul_mem (inv_mem hq) hvq)
  have hc := hWc (v * q * v⁻¹) hvq q⁻¹ (inv_mem hq)
  have h1 : v * (q * q) * v⁻¹ = q * q := by
    rw [hsq]; group
  calc q⁻¹ * (v * q * v⁻¹) * (q⁻¹ * (v * q * v⁻¹))
      = q⁻¹ * ((v * q * v⁻¹) * q⁻¹) * (v * q * v⁻¹) := by group
    _ = q⁻¹ * (q⁻¹ * (v * q * v⁻¹)) * (v * q * v⁻¹) := by rw [hc]
    _ = (q * q)⁻¹ * (v * (q * q) * v⁻¹) := by group
    _ = 1 := by rw [h1]; group

theorem mem_of_pow_mul_eq_one {G : Type*} [Group G] [Finite G] {z : G} {W V₁ V : Subgroup G} {k : ℕ}
    (hk : 2 ≤ k) (hW : IsCyclic ↥W) (hV₁W : V₁ ≤ W) (hV₁ : Nat.card ↥V₁ = 2 ^ k)
    (hsqV₁ : ∀ w ∈ W, w * w ∈ V₁) (hz : z ∈ V₁) (hz2 : z * z = 1)
    (huniq : ∀ c ∈ W, c * c = 1 → c = 1 ∨ c = z)
    (hVV₁ : ∀ v ∈ V, ∀ a ∈ V₁, v * a = a * v) (hVW : ∀ v ∈ V, ∀ w ∈ W, v * w * v⁻¹ ∈ W)
    (hVk : ∀ v ∈ V, v ^ (2 ^ k) = 1) {q v : G} (hq : q ∈ W) (hv : v ∈ V)
    (hx : (q * v) ^ (2 ^ k) = 1) : q ∈ V₁ := by
  have hWc := cyclic_comm hW
  have hqq : q * q ∈ V₁ := hsqV₁ q hq
  have hsq : v * (q * q) = (q * q) * v := hVV₁ v hv _ hqq
  obtain ⟨c, hc, hqv⟩ := conj_dichotomy hWc huniq hq (hVW v hv q hq) hsq
  have hcV₁ : c ∈ V₁ := by
    rcases hc with rfl | rfl
    · exact one_mem _
    · exact hz
  have hc2 : c * c = 1 := by
    rcases hc with rfl | rfl
    · simp
    · exact hz2
  have h1 : Commute (q * q) v := (hVV₁ v hv _ hqq).symm
  have h2 : Commute c v := (hVV₁ v hv c hcV₁).symm
  have h3 : Commute (q * q) c := hWc _ (hV₁W hqq) c (hV₁W hcV₁)
  have h4 := pow_two_pow_mul hk hc2 (hVk v hv) hqv h1 h2 h3
  rw [h4] at hx
  apply mem_of_pow_card_eq_one hW hV₁W hq
  rw [hV₁]
  exact hx

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
