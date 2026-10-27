module

public import Mathlib
public import CFSG.ClassicalInvolution.AschTight.Sec7L98C

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

set_option hygiene false in
local notation "𝕌𝕍" => (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G)
set_option hygiene false in
local notation "𝕏𝕏" =>
  ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) : Subgroup G)
set_option hygiene false in
local notation "𝕐𝕐" => (pairNormalizers K J z j)
set_option hygiene false in
local notation "ℤℤ" => (Subgroup.closure ({z, j} : Set G) : Subgroup G)

theorem mem_normalizer_sup_of {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  rw [conjSub_sup_eq, hA, hB]

namespace Tor98

variable {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z j u v : G} {R R' T : Subgroup G}
  (t : Tor98 Ω K J K' z j u v R R' T)
include t

theorem U_data [Finite G] :
    IsPGroup 2 (Subgroup.zpowers u) ∧ 4 ≤ Nat.card (Subgroup.zpowers u) := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet t.hΩ t.hU
  exact ⟨Sec6Gen.isPGroup_of_mem_USet t.hΩ t.hU, h4⟩

theorem V_data [Finite G] :
    IsPGroup 2 (Subgroup.zpowers v) ∧ 4 ≤ Nat.card (Subgroup.zpowers v) := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet t.hΩ t.hV
  exact ⟨Sec6Gen.isPGroup_of_mem_USet t.hΩ t.hV, h4⟩

theorem u_sq_ne [Finite G] : u * u ≠ 1 := by
  intro h
  have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h2 := t.U_data.2
  rw [Nat.card_zpowers] at h2
  have := Nat.le_of_dvd two_pos h1
  omega

theorem v_sq_ne [Finite G] : v * v ≠ 1 := by
  intro h
  have h1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h2 := t.V_data.2
  rw [Nat.card_zpowers] at h2
  have := Nat.le_of_dvd two_pos h1
  omega

theorem U_inf_V [Finite G] : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers u ⊓ Subgroup.zpowers v) :=
    t.U_data.1.to_le inf_le_left
  have hcard : 2 ≤ Nat.card ↥(Subgroup.zpowers u ⊓ Subgroup.zpowers v) := by
    have h1 : 1 < Nat.card ↥(Subgroup.zpowers u ⊓ Subgroup.zpowers v) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hb
      apply hx1
      rw [hb] at hx
      exact hx
    omega
  have hzm := t.hz.mem_of_le (inf_le_left.trans t.hUK) h2 hcard
  have hjm := t.hj.mem_of_le (inf_le_right.trans t.hVJ) h2 hcard
  have hz2 := (t.hj.unique z (inf_le_right.trans t.hVJ hzm) t.hz.sq).resolve_left t.hz.ne_one
  exact t.hzj hz2

theorem v_le_C_u : Subgroup.zpowers v ≤ Subgroup.centralizer (Subgroup.zpowers u : Set G) :=
  fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => (t.hcomm x hx y hy)

theorem v_le_N_u :
    Subgroup.zpowers v ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
  t.v_le_C_u.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers u : Set G))

theorem UV_comm : ∀ x ∈ 𝕌𝕍, ∀ y ∈ 𝕌𝕍, x * y = y * x := by
  have hle : 𝕌𝕍 ≤ Subgroup.centralizer (𝕌𝕍 : Set G) := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      have h1 : 𝕌𝕍 ≤ Subgroup.centralizer ({a} : Set G) := by
        refine sup_le ?_ ?_
        · intro b hb
          rw [Subgroup.mem_centralizer_singleton_iff]
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact (Commute.zpow_zpow_self u n m).eq
        · intro b hb
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (t.hcomm a ha b hb).symm
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hb)
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      have h1 : 𝕌𝕍 ≤ Subgroup.centralizer ({a} : Set G) := by
        refine sup_le ?_ ?_
        · intro b hb
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact t.hcomm b hb a ha
        · intro b hb
          rw [Subgroup.mem_centralizer_singleton_iff]
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact (Commute.zpow_zpow_self v n m).eq
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hb)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hy) x hx)

theorem UV_isPGroup [Finite G] : IsPGroup 2 𝕌𝕍 :=
  IsPGroup.to_sup_of_normal_left' t.U_data.1 t.V_data.1 t.v_le_N_u

theorem exists_mul_of_mem_UV {x : G} (hx : x ∈ 𝕌𝕍) :
    ∃ a ∈ Subgroup.zpowers u, ∃ b ∈ Subgroup.zpowers v, x = a * b :=
  Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer t.v_le_N_u hx

theorem z_mem_U [Finite G] : z ∈ Subgroup.zpowers u :=
  t.hz.mem_of_le t.hUK t.U_data.1 (by have := t.U_data.2; omega)

theorem j_mem_V [Finite G] : j ∈ Subgroup.zpowers v :=
  t.hj.mem_of_le t.hVJ t.V_data.1 (by have := t.V_data.2; omega)

theorem Z_le_UV [Finite G] : ℤℤ ≤ 𝕌𝕍 := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.mem_sup_left t.z_mem_U
  · exact Subgroup.mem_sup_right t.j_mem_V

theorem mem_Z_of_sq [Finite G] {x : G} (hx : x ∈ 𝕌𝕍) (hx2 : x * x = 1) : x ∈ ℤℤ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := t.exists_mul_of_mem_UV hx
  have hab : a * b = b * a := t.hcomm a ha b hb
  have h1 : a * a = (b * b)⁻¹ := by
    have : a * a * (b * b) = 1 := by
      calc a * a * (b * b) = a * b * (a * b) := by
            rw [show a * b * (a * b) = a * (b * a) * b by group, ← hab]; group
        _ = 1 := hx2
    exact eq_inv_of_mul_eq_one_left this
  have h2 : a * a ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v :=
    ⟨Subgroup.mul_mem _ ha ha, h1 ▸ Subgroup.inv_mem _ (Subgroup.mul_mem _ hb hb)⟩
  rw [t.U_inf_V, Subgroup.mem_bot] at h2
  have h3 : b * b = 1 := by rw [h2] at h1; exact inv_eq_one.mp h1.symm
  have hz' : a ∈ ℤℤ := by
    rcases t.hz.unique a (t.hUK ha) h2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.subset_closure (by simp)
  have hj' : b ∈ ℤℤ := by
    rcases t.hj.unique b (t.hVJ hb) h3 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.subset_closure (by simp)
  exact Subgroup.mul_mem _ hz' hj'

theorem mem_C_Z_of_comm {g : G} (hgz : g * z = z * g) (hgj : g * j = j * g) :
    g ∈ Subgroup.centralizer (ℤℤ : Set G) := by
  have hle : ℤℤ ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hgz.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hgj.symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

omit t in
theorem comm_of_conj_eq {g x : G} (h : g * x * g⁻¹ = x) : g * x = x * g := by
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h]

omit t in
theorem comm_of_conj_eq_inv {g x : G} (h : x * g = g * x) : g * x * g⁻¹ = x := by
  calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [h]
    _ = x := by group

theorem X_le_C_Z : 𝕏𝕏 ≤ Subgroup.centralizer (ℤℤ : Set G) := by
  refine sup_le ?_ ?_
  · intro g hg
    exact t.mem_C_Z_of_comm (comm_of_conj_eq (t.hz.conj_eq
      (mem_normalizer_iff_conjSub_eq.mp hg.2))) (AscL62.uniqueInvolution_comm t.hj hg.1)
  · intro g hg
    exact t.mem_C_Z_of_comm (AscL62.uniqueInvolution_comm t.hz hg.1)
      (comm_of_conj_eq (t.hj.conj_eq (mem_normalizer_iff_conjSub_eq.mp hg.2)))

theorem card_sylow_eq [Finite G] {M U Q : Subgroup G} (hM : M ∈ Ω) (hU : U ∈ USet Ω) (hUM : U ≤ M)
    (hQ : IsSylow2In Q M) : Nat.card Q = 2 * Nat.card U := by
  obtain ⟨R₀, -, M₀, hM₀, hR₀, hUR₀, -, hcard, h4⟩ := Sec6Gen.exists_data_of_mem_USet t.hΩ hU
  have hMM : M₀ = M := Sec6Gen.eq_of_le_of_le t.hΩ hM₀ hM (Sec6Gen.isPGroup_of_mem_USet t.hΩ hU)
    h4 (hUR₀.trans hR₀.1) hUM
  subst hMM
  rw [← hcard, Sec6Gen.natCard_isSylow2In_eq t.hΩ hM hM hQ hR₀]

theorem exists_r [Finite G] : ∃ r ∈ R, r ∉ Subgroup.zpowers u := by
  by_contra h
  push Not at h
  have h1 := t.card_sylow_eq t.hK t.hU t.hUK t.hR
  have h2 : Nat.card R ≤ Nat.card (Subgroup.zpowers u) := Subgroup.card_le_of_le h
  have h3 := t.U_data.2
  omega

theorem exists_r' [Finite G] : ∃ r' ∈ R', r' ∉ Subgroup.centralizer ({j} : Set G) := by
  obtain ⟨u', hu', hu'U, -⟩ := t.hU'
  by_contra h
  push Not at h
  have hle : R' ≤ Subgroup.zpowers u' := by
    rw [hu']
    exact fun x hx => ⟨hx, h x hx⟩
  have hu'K : Subgroup.zpowers u' ≤ K' := by rw [hu']; exact inf_le_left.trans t.hR'.1
  have h1 := t.card_sylow_eq t.hK' hu'U hu'K t.hR'
  have h2 : Nat.card R' ≤ Nat.card (Subgroup.zpowers u') := Subgroup.card_le_of_le hle
  obtain ⟨-, -, -, -, -, -, -, -, h3⟩ := Sec6Gen.exists_data_of_mem_USet t.hΩ hu'U
  omega

theorem R_le_Y [Finite G] : R ≤ 𝕐𝕐 := t.hRY R t.hR t.huR t.hRN

theorem R'_le_Y [Finite G] : R' ≤ 𝕐𝕐 := t.hR'Y R' t.hR' t.hR'N

theorem UV_le_X [Finite G] : 𝕌𝕍 ≤ 𝕏𝕏 := by
  have h := t.hXeq
  rw [h]
  exact le_sup_right

theorem X_triv [Finite G] {y : G} (hy : y ∈ 𝕏𝕏) (hyN : y ∈ Subgroup.normalizer (𝕌𝕍 : Set G)) :
    ∀ w ∈ 𝕌𝕍, y * w * y⁻¹ = w := by
  have hON : 𝕌𝕍 ≤ Subgroup.normalizer ((oddCoreOf 𝕏𝕏 : Subgroup G) : Set G) := fun w hw =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (t.UV_le_X hw))
  have hy' : y ∈ oddCoreOf 𝕏𝕏 ⊔ 𝕌𝕍 := t.hXeq ▸ hy
  obtain ⟨o, ho, w', hw', rfl⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hON hy'
  have hw'N : w' ∈ Subgroup.normalizer (𝕌𝕍 : Set G) := Subgroup.le_normalizer hw'
  have hoN : o ∈ Subgroup.normalizer (𝕌𝕍 : Set G) := by
    have : o = (o * w') * w'⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ hw'N)
  have hoodd : Odd (orderOf o) := by
    have h1 : orderOf o ∣ Nat.card ↥(oddCoreOf 𝕏𝕏) := by
      rw [← Subgroup.orderOf_mk o ho]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat (oddCoreOf_odd_natCard _) h1
  have hoZ : o ∈ Subgroup.centralizer (ℤℤ : Set G) := t.X_le_C_Z (oddCoreOf_le_self _ ho)
  have hotriv := conj_eq_of_odd t.UV_comm t.UV_isPGroup
    (fun a ha => (Subgroup.mem_normalizer_iff.mp hoN a).mp ha) hoodd (fun a ha ha2 =>
      (comm_of_conj_eq_inv (Subgroup.mem_centralizer_iff.mp hoZ a (t.mem_Z_of_sq ha ha2))))
  intro w hw
  calc o * w' * w * (o * w')⁻¹ = o * (w' * w * w'⁻¹) * o⁻¹ := by group
    _ = o * w * o⁻¹ := by rw [show w' * w * w'⁻¹ = w by rw [t.UV_comm w' hw' w hw]; group]
    _ = w := hotriv w hw

theorem sign [Finite G] {c : G} (hcY : c ∈ 𝕐𝕐) (hcZ : c ∈ Subgroup.centralizer (ℤℤ : Set G))
    (hcN : c ∈ Subgroup.normalizer (𝕌𝕍 : Set G)) :
    (∀ w ∈ 𝕌𝕍, c * w * c⁻¹ = w) ∨ (∀ w ∈ 𝕌𝕍, c * w * c⁻¹ = w⁻¹) := by
  obtain ⟨r, hrR, hru⟩ := t.exists_r
  obtain ⟨r', hr'R', hr'j⟩ := t.exists_r'
  obtain ⟨hinv, hYC⟩ := t.hcent r hrR hru r' hr'R' hr'j
  have hrrY : r * r' ∈ 𝕐𝕐 := Subgroup.mul_mem _ (t.R_le_Y hrR) (t.R'_le_Y hr'R')
  have hrrN : r * r' ∈ Subgroup.normalizer (𝕌𝕍 : Set G) :=
    Subgroup.mul_mem _ (t.hRN hrR) (t.hR'N hr'R')
  have hc : c ∈ 𝕏𝕏 ⊔ Subgroup.zpowers (r * r') := by
    rw [← hYC]
    exact ⟨hcY, hcZ⟩
  have hzN : Subgroup.zpowers (r * r') ≤ Subgroup.normalizer (𝕏𝕏 : Set G) :=
    Subgroup.zpowers_le.mpr (t.hYX hrrY)
  obtain ⟨y, hy, w₁, hw₁, rfl⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hzN hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw₁
  have hkN : (r * r') ^ k ∈ Subgroup.normalizer (𝕌𝕍 : Set G) := Subgroup.zpow_mem _ hrrN k
  have hyN : y ∈ Subgroup.normalizer (𝕌𝕍 : Set G) := by
    have : y = (y * (r * r') ^ k) * ((r * r') ^ k)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ hkN)
  have hytr := t.X_triv hy hyN
  have hsq : ∀ w ∈ 𝕌𝕍, ((r * r') * (r * r')) * w * ((r * r') * (r * r'))⁻¹ = w := by
    intro w hw
    have hw' : (r * r') * w * (r * r')⁻¹ ∈ 𝕌𝕍 := (Subgroup.mem_normalizer_iff.mp hrrN w).mp hw
    calc ((r * r') * (r * r')) * w * ((r * r') * (r * r'))⁻¹
        = (r * r') * ((r * r') * w * (r * r')⁻¹) * (r * r')⁻¹ := by group
      _ = (r * r') * w⁻¹ * (r * r')⁻¹ := by rw [hinv w hw]
      _ = ((r * r') * w * (r * r')⁻¹)⁻¹ := by group
      _ = w := by rw [hinv w hw, inv_inv]
  have hpow : ∀ m : ℕ, ∀ w ∈ 𝕌𝕍,
      ((r * r') * (r * r')) ^ m * w * (((r * r') * (r * r')) ^ m)⁻¹ = w := by
    intro m
    induction m with
    | zero => intro w _; simp
    | succ m ih =>
      intro w hw
      rw [pow_succ]
      calc ((r * r') * (r * r')) ^ m * ((r * r') * (r * r')) * w *
            (((r * r') * (r * r')) ^ m * ((r * r') * (r * r')))⁻¹
          = ((r * r') * (r * r')) ^ m * (((r * r') * (r * r')) * w * ((r * r') * (r * r'))⁻¹) *
              (((r * r') * (r * r')) ^ m)⁻¹ := by group
        _ = w := by rw [hsq w hw, ih w hw]
  have hpowz : ∀ m : ℤ, ∀ w ∈ 𝕌𝕍,
      ((r * r') * (r * r')) ^ m * w * (((r * r') * (r * r')) ^ m)⁻¹ = w := by
    intro m w hw
    rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
    · rw [zpow_natCast]; exact hpow n w hw
    · rw [zpow_neg, zpow_natCast, inv_inv]
      have h := hpow n w hw
      calc (((r * r') * (r * r')) ^ n)⁻¹ * w * ((r * r') * (r * r')) ^ n
          = (((r * r') * (r * r')) ^ n)⁻¹ * (((r * r') * (r * r')) ^ n * w *
              (((r * r') * (r * r')) ^ n)⁻¹) * ((r * r') * (r * r')) ^ n := by rw [h]
        _ = w := by group
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    intro w hw
    have e : (r * r') ^ (m + m) = ((r * r') * (r * r')) ^ m := by
      rw [← two_mul, zpow_mul, zpow_two]
    rw [e]
    calc y * ((r * r') * (r * r')) ^ m * w * (y * ((r * r') * (r * r')) ^ m)⁻¹
        = y * (((r * r') * (r * r')) ^ m * w * (((r * r') * (r * r')) ^ m)⁻¹) * y⁻¹ := by group
      _ = w := by rw [hpowz m w hw, hytr w hw]
  · right
    intro w hw
    have e : (r * r') ^ (2 * m + 1) = ((r * r') * (r * r')) ^ m * (r * r') := by
      rw [zpow_add, zpow_mul, zpow_two, zpow_one]
    rw [e]
    have hw' : (r * r') * w * (r * r')⁻¹ ∈ 𝕌𝕍 := (Subgroup.mem_normalizer_iff.mp hrrN w).mp hw
    calc y * (((r * r') * (r * r')) ^ m * (r * r')) * w *
          (y * (((r * r') * (r * r')) ^ m * (r * r')))⁻¹
        = y * (((r * r') * (r * r')) ^ m * ((r * r') * w * (r * r')⁻¹) *
            (((r * r') * (r * r')) ^ m)⁻¹) * y⁻¹ := by group
      _ = y * ((r * r') * w * (r * r')⁻¹) * y⁻¹ := by rw [hpowz m _ hw']
      _ = (r * r') * w * (r * r')⁻¹ := hytr _ hw'
      _ = w⁻¹ := hinv w hw

end Tor98

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
