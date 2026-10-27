module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48TI
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open scoped Pointwise

section Lattice

variable {G : Type*} [Group G] [Finite G]

structure LatData (G : Type*) [Group G] [Finite G] where
  T0 : Subgroup G
  N : Subgroup G
  M1 : Subgroup G
  θ : G ≃* G
  zI : G
  zII : G
  card_T0 : Nat.card T0 = 81
  comm_T0 : ∀ a ∈ T0, ∀ b ∈ T0, a * b = b * a
  exp_T0 : ∀ t ∈ T0, t ^ 9 = 1
  N_eq : N = Subgroup.normalizer (T0 : Set G)
  card_N : Nat.card N = 648
  E_cases : ∀ e ∈ T0, e ^ 3 = 1 → e ≠ 1 →
    (∃ n ∈ N, e = n * zI * n⁻¹) ∨ (∃ n ∈ N, e = n * zII * n⁻¹)
  θ_T0 : ∀ x, x ∈ T0 ↔ θ x ∈ T0
  θ_zI : θ zI = zII
  dich : ∀ H : Subgroup G, N ≤ H →
    (∀ g ∈ H, g * zI = zI * g → g ∈ N) ∨ (∀ g : G, g * zI = zI * g → g ∈ H)
  N_le_M1 : N ≤ M1
  cent_le : ∀ g : G, g * zI = zI * g → g ∈ M1
  gen : ∀ H : Subgroup G, N ≤ H → (∀ g : G, g * zI = zI * g → g ∈ H) → M1 ≤ H
  card_M1 : Nat.card M1 = 508032
  card_G : Nat.card G = 1056706560
  wit : ∃ g : G, g * zII = zII * g ∧ g ∉ M1
  simple : IsSimpleGroup G

namespace LatData

theorem T0_le_N (D : LatData G) : D.T0 ≤ D.N := by
  rw [D.N_eq]
  exact Subgroup.le_normalizer

theorem not_dvd_243 (D : LatData G) : ¬ 243 ∣ Nat.card G := by
  rw [D.card_G]
  decide

theorem isPGroup_T0 (D : LatData G) : IsPGroup 3 D.T0 :=
  IsPGroup.of_card (n := 4) (by rw [D.card_T0]; norm_num)

theorem θ_mem_N (D : LatData G) {n : G} (hn : n ∈ D.N) : D.θ n ∈ D.N := by
  rw [D.N_eq, Subgroup.mem_normalizer_iff] at hn ⊢
  intro h
  have h1 := hn (D.θ.symm h)
  have h2 : D.θ.symm h ∈ D.T0 ↔ h ∈ D.T0 := by
    rw [D.θ_T0 (D.θ.symm h), MulEquiv.apply_symm_apply]
  rw [← h2, h1, D.θ_T0]
  simp

theorem pElem_mem_T0 (D : LatData G) {y : G} (hy : y ∈ D.N) (h3 : ∃ m : ℕ, y ^ (3 ^ m) = 1) :
    y ∈ D.T0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card D.N).factorization 3 = 4 := by
    rw [D.card_N]
    decide +kernel
  have e1 : Nat.card (D.T0.subgroupOf D.N) = 3 ^ (Nat.card D.N).factorization 3 := by
    rw [hfac]
    have : Nat.card (D.T0.subgroupOf D.N) = Nat.card D.T0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.T0_le_N).toEquiv
    rw [this, D.card_T0]
    norm_num
  let P0 : Sylow 3 D.N := Sylow.ofCard (D.T0.subgroupOf D.N) e1
  have : (D.T0.subgroupOf D.N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer D.T0_le_N).2 (by rw [D.N_eq])
  have : P0.Normal := ‹(D.T0.subgroupOf D.N).Normal›
  obtain ⟨m, hm⟩ := h3
  set y' : D.N := ⟨y, hy⟩ with hy'
  have hy'm : y' ^ (3 ^ m) = 1 := Subtype.ext (by simpa using hm)
  have hord : IsPGroup 3 (Subgroup.zpowers y') := by
    have hdvd : orderOf y' ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hy'm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨Q, hQ⟩ := hord.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D.N P0 Q
  have hQP : Q = P0 := by rw [← hg]; exact Sylow.smul_eq_of_normal
  have : y' ∈ (Q : Subgroup D.N) := hQ (Subgroup.mem_zpowers y')
  rw [hQP] at this
  exact (Subgroup.mem_subgroupOf.1 this)

theorem tiStep (D : LatData G) (H M' : Subgroup G) (hNM : D.N ≤ M') (hMH : M' ≤ H)
    (hC : ∀ e ∈ D.T0, e ^ 3 = 1 → e ≠ 1 → ∀ g ∈ H, g * e = e * g → g ∈ M') :
    D.N.relIndex H ≡ D.N.relIndex M' [MOD 81] := by
  have hT0M : D.T0 ≤ M' := D.T0_le_N.trans hNM
  have h := relIndex_modEq_of_ti H D.T0 D.N M' D.T0_le_N hNM hMH D.isPGroup_T0
    (fun y hy h3 => D.pElem_mem_T0 hy h3) ?_
  · rwa [D.card_T0] at h
  intro a haH haM g hg hag
  by_contra hg1
  obtain ⟨e, heT, he3, he1, heg⟩ : ∃ e, e ∈ D.T0 ∧ e ^ 3 = 1 ∧ e ≠ 1 ∧ a⁻¹ * e * a ∈ D.T0 := by
    by_cases h3 : g ^ 3 = 1
    · exact ⟨g, hg, h3, hg1, hag⟩
    · refine ⟨g ^ 3, D.T0.pow_mem hg 3, ?_, h3, ?_⟩
      · rw [← pow_mul]
        exact D.exp_T0 g hg
      · have := conj_pow (a := a⁻¹) (b := g) (i := 3)
        simp only [inv_inv] at this
        rw [← this]
        exact D.T0.pow_mem hag 3
  have hTa : ∀ h : G, a⁻¹ * h * a ∈ D.T0 → h ∈ M' := by
    intro h hh
    have hhH : h ∈ H := by
      have : h = a * (a⁻¹ * h * a) * a⁻¹ := by group
      rw [this]
      exact H.mul_mem (H.mul_mem haH (hMH (hT0M hh))) (H.inv_mem haH)
    refine hC e heT he3 he1 h hhH ?_
    have hc := D.comm_T0 _ hh _ heg
    calc h * e = a * ((a⁻¹ * h * a) * (a⁻¹ * e * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * e * a) * (a⁻¹ * h * a)) * a⁻¹ := by rw [hc]
      _ = e * h := by group
  let T' : Subgroup G := D.T0.map (MulAut.conj a).toMonoidHom
  have hT'mem : ∀ x, x ∈ T' ↔ a⁻¹ * x * a ∈ D.T0 := by
    intro x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have : a⁻¹ * (a * t * a⁻¹) * a = t := by group
      change a⁻¹ * (a * t * a⁻¹) * a ∈ D.T0
      rw [this]
      exact ht
    · intro hx
      exact ⟨a⁻¹ * x * a, hx, by simp [MulAut.conj_apply]; group⟩
  have hT'M : T' ≤ M' := fun x hx => hTa x ((hT'mem x).1 hx)
  have hT'card : Nat.card T' = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, D.card_T0]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ^ 4 ∣ Nat.card M' := by
    have := Subgroup.card_dvd_of_le hT0M
    rwa [D.card_T0, show (81 : ℕ) = 3 ^ 4 by norm_num] at this
  have hndvd : ¬ 3 ^ (4 + 1) ∣ Nat.card M' := fun h =>
    D.not_dvd_243 ((by norm_num : (243 : ℕ) = 3 ^ (4 + 1)) ▸
      h.trans (Subgroup.card_subgroup_dvd_card M'))
  obtain ⟨m, hmM, hm⟩ := exists_conj_of_sylow_in (p := 3) M' hdvd hndvd D.T0 T' hT0M hT'M
    (by rw [D.card_T0]; norm_num) hT'card
  have hn : m⁻¹ * a ∈ D.N := by
    rw [D.N_eq, Subgroup.mem_normalizer_iff]
    intro x
    have h1 := hm (a * x * a⁻¹)
    rw [hT'mem] at h1
    have e1 : a⁻¹ * (a * x * a⁻¹) * a = x := by group
    have e2 : m⁻¹ * (a * x * a⁻¹) * m = (m⁻¹ * a) * x * (m⁻¹ * a)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  have : a = m * (m⁻¹ * a) := by group
  exact haM (this ▸ M'.mul_mem hmM (hNM hn))

theorem θ_symm_mem_N (D : LatData G) {n : G} (hn : n ∈ D.N) : D.θ.symm n ∈ D.N := by
  have hle : D.N.map D.θ.toMonoidHom ≤ D.N := by
    rintro _ ⟨x, hx, rfl⟩
    exact D.θ_mem_N hx
  have hcard : Nat.card (D.N.map D.θ.toMonoidHom) = Nat.card D.N :=
    Subgroup.card_map_of_injective D.θ.injective
  have heq : D.N.map D.θ.toMonoidHom = D.N := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have : n ∈ D.N.map D.θ.toMonoidHom := by rw [heq]; exact hn
  obtain ⟨x, hx, hxn⟩ := this
  have : D.θ.symm n = x := by rw [← hxn]; exact D.θ.symm_apply_apply x
  rw [this]
  exact hx

@[expose] def M2 (D : LatData G) : Subgroup G := D.M1.map D.θ.toMonoidHom

theorem N_le_M2 (D : LatData G) : D.N ≤ D.M2 := fun n hn =>
  ⟨D.θ.symm n, D.N_le_M1 (D.θ_symm_mem_N hn), D.θ.apply_symm_apply n⟩

theorem card_M2 (D : LatData G) : Nat.card D.M2 = 508032 := by
  rw [M2, Subgroup.card_map_of_injective D.θ.injective, D.card_M1]

theorem N_le_comap (D : LatData G) {H : Subgroup G} (hH : D.N ≤ H) :
    D.N ≤ H.comap D.θ.toMonoidHom := fun _ hn => hH (D.θ_mem_N hn)

theorem symm_comm (D : LatData G) {y : G} (hy : y * D.zII = D.zII * y) :
    D.θ.symm y * D.zI = D.zI * D.θ.symm y := by
  apply D.θ.injective
  rw [map_mul, map_mul, D.θ_zI, MulEquiv.apply_symm_apply]
  exact hy

theorem dichII (D : LatData G) (H : Subgroup G) (hH : D.N ≤ H) :
    (∀ g ∈ H, g * D.zII = D.zII * g → g ∈ D.N) ∨ (∀ g : G, g * D.zII = D.zII * g → g ∈ H) := by
  rcases D.dich (H.comap D.θ.toMonoidHom) (D.N_le_comap hH) with h | h
  · left
    intro g hg hgc
    have hc : D.θ.symm g * D.zI = D.zI * D.θ.symm g := by
      apply D.θ.injective
      rw [map_mul, map_mul, D.θ_zI, MulEquiv.apply_symm_apply]
      exact hgc
    have := h (D.θ.symm g) (by simpa using hg) hc
    simpa using D.θ_mem_N this
  · right
    intro g hgc
    have hc : D.θ.symm g * D.zI = D.zI * D.θ.symm g := by
      apply D.θ.injective
      rw [map_mul, map_mul, D.θ_zI, MulEquiv.apply_symm_apply]
      exact hgc
    simpa using h (D.θ.symm g) hc

theorem index_N (D : LatData G) : D.N.index = 1630720 := by
  have := D.N.card_mul_index
  rw [D.card_N, D.card_G] at this
  omega

theorem index_of_card (D : LatData G) (M' : Subgroup G) (h : Nat.card M' = 508032) :
    M'.index = 2080 := by
  have := M'.card_mul_index
  rw [h, D.card_G] at this
  omega

theorem relIndex_N_of_card (D : LatData G) (M' : Subgroup G) (h : Nat.card M' = 508032)
    (hle : D.N ≤ M') : D.N.relIndex M' = 784 := by
  have h1 := Subgroup.relIndex_mul_index hle
  rw [D.index_of_card M' h, D.index_N] at h1
  omega

theorem dichAll (D : LatData G) (H : Subgroup G) (hH : D.N ≤ H)
    (hI : ¬ ∀ g : G, g * D.zI = D.zI * g → g ∈ H)
    (hII : ¬ ∀ g : G, g * D.zII = D.zII * g → g ∈ H) :
    ∀ e ∈ D.T0, e ^ 3 = 1 → e ≠ 1 → ∀ g ∈ H, g * e = e * g → g ∈ D.N := by
  intro e heT he3 he1 g hg hgc
  rcases D.E_cases e heT he3 he1 with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · have hc : (n⁻¹ * g * n) * D.zI = D.zI * (n⁻¹ * g * n) := by
      have : g * (n * D.zI * n⁻¹) = (n * D.zI * n⁻¹) * g := hgc
      calc (n⁻¹ * g * n) * D.zI = n⁻¹ * (g * (n * D.zI * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * D.zI * n⁻¹) * g) * n := by rw [this]
        _ = D.zI * (n⁻¹ * g * n) := by group
    have hgH : n⁻¹ * g * n ∈ H := H.mul_mem (H.mul_mem (H.inv_mem (hH hn)) hg) (hH hn)
    rcases D.dich H hH with h | h
    · have := h _ hgH hc
      have e : g = n * (n⁻¹ * g * n) * n⁻¹ := by group
      rw [e]
      exact D.N.mul_mem (D.N.mul_mem hn this) (D.N.inv_mem hn)
    · exact absurd h hI
  · have hc : (n⁻¹ * g * n) * D.zII = D.zII * (n⁻¹ * g * n) := by
      have : g * (n * D.zII * n⁻¹) = (n * D.zII * n⁻¹) * g := hgc
      calc (n⁻¹ * g * n) * D.zII = n⁻¹ * (g * (n * D.zII * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * D.zII * n⁻¹) * g) * n := by rw [this]
        _ = D.zII * (n⁻¹ * g * n) := by group
    have hgH : n⁻¹ * g * n ∈ H := H.mul_mem (H.mul_mem (H.inv_mem (hH hn)) hg) (hH hn)
    rcases D.dichII H hH with h | h
    · have := h _ hgH hc
      have e : g = n * (n⁻¹ * g * n) * n⁻¹ := by group
      rw [e]
      exact D.N.mul_mem (D.N.mul_mem hn this) (D.N.inv_mem hn)
    · exact absurd h hII

theorem caseN (D : LatData G) (H : Subgroup G) (hH : D.N ≤ H)
    (hC : ∀ e ∈ D.T0, e ^ 3 = 1 → e ≠ 1 → ∀ g ∈ H, g * e = e * g → g ∈ D.N) : H = D.N := by
  have hNM : D.N ≤ D.M1 := D.N_le_M1
  have h784 : D.N.relIndex D.M1 = 784 := D.relIndex_N_of_card D.M1 D.card_M1 hNM
  have hH1 : H ⊓ D.M1 ≤ D.N := by
    have hmod := D.tiStep (H ⊓ D.M1) D.N le_rfl (le_inf hH hNM)
      (fun e he he3 he1 g hg hgc => hC e he he3 he1 g hg.1 hgc)
    rw [Subgroup.relIndex_self] at hmod
    have hdvd : D.N.relIndex (H ⊓ D.M1) ∣ 784 := by
      rw [← h784, ← Subgroup.relIndex_mul_relIndex D.N (H ⊓ D.M1) D.M1 (le_inf hH hNM)
        inf_le_right]
      exact Dvd.intro _ rfl
    have hr : D.N.relIndex (H ⊓ D.M1) = 1 := by
      have hle : D.N.relIndex (H ⊓ D.M1) ≤ 784 := Nat.le_of_dvd (by norm_num) hdvd
      have key : ∀ r : ℕ, r ≤ 784 → r ∣ 784 → r ≡ 1 [MOD 81] → r = 1 := by decide +kernel
      exact key _ hle hdvd hmod
    exact Subgroup.relIndex_eq_one.1 hr
  have hHeq : H ⊓ D.M1 = D.N := le_antisymm hH1 (le_inf hH hNM)
  have hmod := D.tiStep H D.N le_rfl hH hC
  rw [Subgroup.relIndex_self] at hmod
  have hle : D.N.relIndex H ≤ 2080 := by
    have h1 : D.N.relIndex H = D.M1.relIndex H := by
      rw [← hHeq, inf_comm, Subgroup.inf_relIndex_right]
    rw [h1]
    calc D.M1.relIndex H ≤ D.M1.relIndex ⊤ :=
          Subgroup.relIndex_le_of_le_right le_top (by
            rw [Subgroup.relIndex_top_right, D.index_of_card D.M1 D.card_M1]; norm_num)
      _ = 2080 := by rw [Subgroup.relIndex_top_right, D.index_of_card D.M1 D.card_M1]
  have hdvd : D.N.relIndex H ∣ 1630720 := by
    rw [← D.index_N]
    exact Subgroup.relIndex_dvd_index_of_le hH
  have hr : D.N.relIndex H = 1 := by
    have key : ∀ r : ℕ, r ≤ 2080 → r ∣ 1630720 → r ≡ 1 [MOD 81] → r = 1 := by decide +kernel
    exact key _ hle hdvd hmod
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hr) hH

theorem caseM (D : LatData G) (M' H : Subgroup G) (hcard : Nat.card M' = 508032) (hNM : D.N ≤ M')
    (hMH : M' ≤ H)
    (hC : ∀ e ∈ D.T0, e ^ 3 = 1 → e ≠ 1 → ∀ g ∈ H, g * e = e * g → g ∈ M') : H = M' := by
  have h784 : D.N.relIndex M' = 784 := D.relIndex_N_of_card M' hcard hNM
  have hmod := D.tiStep H M' hNM hMH hC
  rw [← Subgroup.relIndex_mul_relIndex D.N M' H hNM hMH, h784] at hmod
  have hr : M'.relIndex H ≡ 1 [MOD 81] := by
    have : 784 * M'.relIndex H ≡ 784 * 1 [MOD 81] := by simpa using hmod
    exact Nat.ModEq.cancel_left_of_coprime (by norm_num) this
  have hdvd : M'.relIndex H ∣ 2080 := by
    rw [← D.index_of_card M' hcard]
    exact Subgroup.relIndex_dvd_index_of_le hMH
  have hone : M'.relIndex H = 1 := by
    have key : ∀ r : ℕ, r ≤ 2080 → r ∣ 2080 → r ≡ 1 [MOD 81] → r = 1 := by decide +kernel
    exact key _ (Nat.le_of_dvd (by norm_num) hdvd) hdvd hr
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hone) hMH

theorem M2_ne_witness (D : LatData G) (hle : D.M1 ≤ D.M2) : False := by
  have hM : D.M1 = D.M2 := Subgroup.eq_of_le_of_card_ge hle (by rw [D.card_M1, D.card_M2])
  obtain ⟨g, hg, hgM⟩ := D.wit
  have hc : D.θ.symm g * D.zI = D.zI * D.θ.symm g := by
    apply D.θ.injective
    rw [map_mul, map_mul, D.θ_zI, MulEquiv.apply_symm_apply]
    exact hg
  have h1 := D.cent_le _ hc
  have h2 : g ∈ D.M2 := ⟨D.θ.symm g, h1, D.θ.apply_symm_apply g⟩
  exact hgM (hM ▸ h2)

theorem inter_eq_N (D : LatData G) : D.M1 ⊓ D.M2 = D.N := by
  have hNW : D.N ≤ D.M1 ⊓ D.M2 := le_inf D.N_le_M1 D.N_le_M2
  refine D.caseN _ hNW ?_
  refine D.dichAll _ hNW ?_ ?_
  · intro hI
    have := D.gen (D.M1 ⊓ D.M2) hNW hI
    exact D.M2_ne_witness (this.trans inf_le_right)
  · intro hII
    obtain ⟨g, hg, hgM⟩ := D.wit
    exact hgM (hII g hg).1

theorem lattice (D : LatData G) (H : Subgroup G) (hH : D.N ≤ H) :
    H = D.N ∨ H = D.M1 ∨ H = D.M2 ∨ H = ⊤ := by
  by_cases hI : ∀ g : G, g * D.zI = D.zI * g → g ∈ H <;>
    by_cases hII : ∀ g : G, g * D.zII = D.zII * g → g ∈ H
  ·
    right; right; right
    have hM1 : D.M1 ≤ H := D.gen H hH hI
    have hM2 : D.M2 ≤ H := by
      have h := D.gen (H.comap D.θ.toMonoidHom) (D.N_le_comap hH) (fun g hg => by
        have : D.θ g * D.zII = D.zII * D.θ g := by
          rw [← D.θ_zI, ← map_mul, ← map_mul, hg]
        exact hII _ this)
      rintro _ ⟨x, hx, rfl⟩
      exact h hx
    have hdvd : D.M1.relIndex H ∣ 2080 := by
      rw [← D.index_of_card D.M1 D.card_M1]
      exact Subgroup.relIndex_dvd_index_of_le hM1
    have hne : D.M1.relIndex H ≠ 0 := by
      intro h0
      rw [h0] at hdvd
      norm_num at hdvd
    have hge : 784 ≤ D.M1.relIndex H := by
      have h1 : D.M1.relIndex D.M2 ≤ D.M1.relIndex H := Subgroup.relIndex_le_of_le_right hM2 hne
      have h2 : D.M1.relIndex D.M2 = 784 := by
        rw [← Subgroup.inf_relIndex_right, D.inter_eq_N]
        exact D.relIndex_N_of_card D.M2 D.card_M2 D.N_le_M2
      omega
    have key : ∀ r : ℕ, r ≤ 2080 → r ∣ 2080 → 784 ≤ r → r = 1040 ∨ r = 2080 := by decide +kernel
    have hmul := Subgroup.relIndex_mul_index hM1
    rw [D.index_of_card D.M1 D.card_M1] at hmul
    rcases key _ (Nat.le_of_dvd (by norm_num) hdvd) hdvd hge with h | h
    · exfalso
      have hidx : H.index = 2 := by rw [h] at hmul; omega
      have : H.Normal := Subgroup.normal_of_index_eq_two hidx
      rcases D.simple.eq_bot_or_eq_top_of_normal H with h0 | h0
      · rw [h0, Subgroup.index_bot, D.card_G] at hidx
        omega
      · rw [h0, Subgroup.index_top] at hidx
        omega
    · rw [← Subgroup.index_eq_one]
      rw [h] at hmul
      omega
  ·
    right; left
    have hM1 : D.M1 ≤ H := D.gen H hH hI
    refine D.caseM D.M1 H D.card_M1 D.N_le_M1 hM1 ?_
    intro e he he3 he1 g hg hgc
    rcases D.E_cases e he he3 he1 with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
    · have hc : (n⁻¹ * g * n) * D.zI = D.zI * (n⁻¹ * g * n) := by
        have : g * (n * D.zI * n⁻¹) = (n * D.zI * n⁻¹) * g := hgc
        calc (n⁻¹ * g * n) * D.zI = n⁻¹ * (g * (n * D.zI * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * D.zI * n⁻¹) * g) * n := by rw [this]
          _ = D.zI * (n⁻¹ * g * n) := by group
      have h1 := D.cent_le _ hc
      have e : g = n * (n⁻¹ * g * n) * n⁻¹ := by group
      rw [e]
      exact D.M1.mul_mem (D.M1.mul_mem (D.N_le_M1 hn) h1) (D.M1.inv_mem (D.N_le_M1 hn))
    · have hc : (n⁻¹ * g * n) * D.zII = D.zII * (n⁻¹ * g * n) := by
        have : g * (n * D.zII * n⁻¹) = (n * D.zII * n⁻¹) * g := hgc
        calc (n⁻¹ * g * n) * D.zII = n⁻¹ * (g * (n * D.zII * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * D.zII * n⁻¹) * g) * n := by rw [this]
          _ = D.zII * (n⁻¹ * g * n) := by group
      have hgH : n⁻¹ * g * n ∈ H := H.mul_mem (H.mul_mem (H.inv_mem (hH hn)) hg) (hH hn)
      rcases D.dichII H hH with h | h
      · have h1 := h _ hgH hc
        have e : g = n * (n⁻¹ * g * n) * n⁻¹ := by group
        rw [e]
        exact D.M1.mul_mem (D.M1.mul_mem (D.N_le_M1 hn) (D.N_le_M1 h1))
          (D.M1.inv_mem (D.N_le_M1 hn))
      · exact absurd h hII
  ·
    right; right; left
    have hM2 : D.M2 ≤ H := by
      have h := D.gen (H.comap D.θ.toMonoidHom) (D.N_le_comap hH) (fun g hg => by
        have : D.θ g * D.zII = D.zII * D.θ g := by
          rw [← D.θ_zI, ← map_mul, ← map_mul, hg]
        exact hII _ this)
      rintro _ ⟨x, hx, rfl⟩
      exact h hx
    refine D.caseM D.M2 H D.card_M2 D.N_le_M2 hM2 ?_
    intro e he he3 he1 g hg hgc
    rcases D.E_cases e he he3 he1 with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
    · have hc : (n⁻¹ * g * n) * D.zI = D.zI * (n⁻¹ * g * n) := by
        have : g * (n * D.zI * n⁻¹) = (n * D.zI * n⁻¹) * g := hgc
        calc (n⁻¹ * g * n) * D.zI = n⁻¹ * (g * (n * D.zI * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * D.zI * n⁻¹) * g) * n := by rw [this]
          _ = D.zI * (n⁻¹ * g * n) := by group
      have hgH : n⁻¹ * g * n ∈ H := H.mul_mem (H.mul_mem (H.inv_mem (hH hn)) hg) (hH hn)
      rcases D.dich H hH with h | h
      · have h1 := h _ hgH hc
        have e : g = n * (n⁻¹ * g * n) * n⁻¹ := by group
        rw [e]
        exact D.M2.mul_mem (D.M2.mul_mem (D.N_le_M2 hn) (D.N_le_M2 h1))
          (D.M2.inv_mem (D.N_le_M2 hn))
      · exact absurd h hI
    · have hc : (n⁻¹ * g * n) * D.zII = D.zII * (n⁻¹ * g * n) := by
        have : g * (n * D.zII * n⁻¹) = (n * D.zII * n⁻¹) * g := hgc
        calc (n⁻¹ * g * n) * D.zII = n⁻¹ * (g * (n * D.zII * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * D.zII * n⁻¹) * g) * n := by rw [this]
          _ = D.zII * (n⁻¹ * g * n) := by group
      have h1 := D.cent_le _ (D.symm_comm hc)
      have h2 : n⁻¹ * g * n ∈ D.M2 := ⟨D.θ.symm (n⁻¹ * g * n), h1, D.θ.apply_symm_apply _⟩
      have e : g = n * (n⁻¹ * g * n) * n⁻¹ := by group
      rw [e]
      exact D.M2.mul_mem (D.M2.mul_mem (D.N_le_M2 hn) h2) (D.M2.inv_mem (D.N_le_M2 hn))
  ·
    left
    exact D.caseN H hH (D.dichAll H hH hI hII)

end LatData

end Lattice

end CFSG.AGLEmbedding.KFactProofs.Sp48
