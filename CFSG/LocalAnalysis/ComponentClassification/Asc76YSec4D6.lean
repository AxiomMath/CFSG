module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Tools

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace IsDihedralRot

variable {U R : Subgroup G}

theorem two_dvd_card (h : IsDihedralRot U R) : 2 ∣ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (h.isPGroup.to_le h.le).exists_card_eq
  have h4 := h.four_le
  rw [hn] at h4 ⊢
  rcases n with _ | n
  · simp at h4
  · exact Dvd.intro_left _ rfl

theorem exists_sq_of_pow_half_eq_one (h : IsDihedralRot U R) {g : G} (hg : g ∈ U)
    (h1 : g ^ (Nat.card U / 2) = 1) : ∃ v ∈ U, g = v * v := by
  obtain ⟨ρ, hρ, hρo⟩ := h.exists_gen
  rw [← hρ] at hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  obtain ⟨m, hm⟩ := h.two_dvd_card
  have hm0 : Nat.card U / 2 = m := by omega
  rw [hm0, ← zpow_natCast, ← zpow_mul] at h1
  have hdvd : ((orderOf ρ : ℕ) : ℤ) ∣ k * m := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hρo, hm] at hdvd
  have hm1 : (m : ℤ) ≠ 0 := by
    have := h.four_le
    omega
  have h2 : (2 : ℤ) ∣ k := by
    obtain ⟨c, hc⟩ := hdvd
    have : (m : ℤ) * (2 * c) = m * k := by push_cast at hc; linarith [hc]
    have := mul_left_cancel₀ hm1 this
    exact ⟨c, by linarith⟩
  obtain ⟨j, rfl⟩ := h2
  refine ⟨ρ ^ j, hρ ▸ zpow_mem (mem_zpowers ρ) j, ?_⟩
  rw [← zpow_add, two_mul]

theorem not_sq_of_isDihedral (h : IsDihedralRot U R) {t : G} (htt : t * t = 1) (htR : t ∉ R)
    (hinv : ∀ u ∈ U, t * u * t⁻¹ = u⁻¹)
    (hD : IsDihedralTwoGroup (zpowers t ⊔ R)) {s : G} (hsR : s ∈ R) (hsU : s ∉ U) :
    ∀ v ∈ U, (t * s) * (t * s) ≠ v * v := by
  intro v hv heq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hss : s * s = 1 := h.mul_self s hsR hsU
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  set s₀ := v * s with hs₀
  have hs₀R : s₀ ∈ R := R.mul_mem (h.le hv) hsR
  have hs₀U : s₀ ∉ U := fun hs => hsU (by
    have : s = v⁻¹ * s₀ := by rw [hs₀]; group
    rw [this]; exact U.mul_mem (inv_mem hv) hs)
  have htv : t * v * t⁻¹ = v⁻¹ := hinv v hv
  have hts₀ : t * s₀ = s₀ * t := by
    have h1 : t * s * t * s = v * v := by rw [← heq]; group
    have h2 : t * s * t = v * v * s := by
      calc t * s * t = t * s * t * s * s⁻¹ := by group
        _ = v * v * s := by rw [h1, hsinv]
    have h3 : t * s * t⁻¹ = v * v * s := by rw [htinv]; exact h2
    calc t * s₀ = (t * v * t⁻¹) * (t * s * t⁻¹) * t := by rw [hs₀]; group
      _ = v⁻¹ * (v * v * s) * t := by rw [htv, h3]
      _ = s₀ * t := by rw [hs₀]; group
  set c := t * s₀ with hc
  have hc1 : c ≠ 1 := by
    intro h1
    apply htR
    have : t = s₀⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_mem hs₀R
  have hcR : c ∉ R := by
    intro hcR
    apply htR
    have : t = c * s₀⁻¹ := by rw [hc]; group
    rw [this]
    exact R.mul_mem hcR (inv_mem hs₀R)
  have hcR' : ∀ y ∈ R, c * y = y * c := by
    intro y hy
    have key : ∀ u ∈ U, c * u = u * c := by
      intro u hu
      have h1 : s₀ * u * s₀⁻¹ = u⁻¹ := h.conj_eq s₀ hs₀R hs₀U u hu
      have h2 : t * u * t⁻¹ = u⁻¹ := hinv u hu
      calc c * u = t * (s₀ * u * s₀⁻¹) * s₀ := by rw [hc]; group
        _ = t * u⁻¹ * s₀ := by rw [h1]
        _ = (t * u⁻¹ * t⁻¹) * (t * s₀) := by group
        _ = u * c := by
          rw [hc]
          congr 1
          have : t * u⁻¹ * t⁻¹ = (t * u * t⁻¹)⁻¹ := by group
          rw [this, h2, inv_inv]
    have hcs₀ : c * s₀ = s₀ * c := by
      rw [hc, show s₀ * (t * s₀) = (s₀ * t) * s₀ by group, ← hts₀]
    by_cases hyU : y ∈ U
    · exact key y hyU
    · have hy' : s₀ * y ∈ U := h.mul_mem_of_not_mem hs₀R hy hs₀U hyU
      have hs₀s₀ : s₀ * s₀ = 1 := h.mul_self s₀ hs₀R hs₀U
      have hyeq : y = s₀ * (s₀ * y) := by
        rw [← mul_assoc, hs₀s₀, one_mul]
      rw [hyeq, ← mul_assoc, hcs₀, mul_assoc, key _ hy', ← mul_assoc]
  have hct : c * t = t * c := by rw [hc, mul_assoc, ← hts₀]
  set P : Subgroup G := zpowers t ⊔ R with hP
  have hPc : ∀ y ∈ P, c * y = y * c := by
    have hle : P ≤ centralizer ({c} : Set G) := by
      refine sup_le ?_ ?_
      · rw [zpowers_le, mem_centralizer_singleton_iff]
        exact hct.symm
      · intro y hy
        rw [mem_centralizer_singleton_iff]
        exact (hcR' y hy).symm
    intro y hy
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  obtain ⟨z, hzU, hz1, hzz, -, hzR⟩ := h.exists_involution
  have hPz : ∀ y ∈ P, z * y = y * z := by
    have hzt : z * t = t * z := by
      have h1 : t * z * t⁻¹ = z⁻¹ := hinv z hzU
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
      calc z * t = (t * z * t⁻¹)⁻¹ * t := by rw [h1, inv_inv]
        _ = t * z⁻¹ := by group
        _ = t * z := by rw [hzinv]
    have hle : P ≤ centralizer ({z} : Set G) := by
      refine sup_le ?_ ?_
      · rw [zpowers_le, mem_centralizer_singleton_iff]
        exact hzt.symm
      · intro y hy
        rw [mem_centralizer_singleton_iff]
        exact hzR y hy
    intro y hy
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hPnc : ¬ IsMulCommutative P := by
    intro hcomm
    apply h.not_isMulCommutative
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have := hcomm.is_comm.comm ⟨a, (le_sup_right : R ≤ P) a.2⟩ ⟨b, (le_sup_right : R ≤ P) b.2⟩
    simpa using congrArg Subtype.val this
  obtain ⟨UP, hUP⟩ := exists_isDihedralRot hD hPnc
  obtain ⟨zP, -, -, -, hzPuniq, -⟩ := hUP.exists_involution
  have hcP : c ∈ P := P.mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hs₀R)
  have hzP : z ∈ P := mem_sup_right (h.le hzU)
  rcases hUP.eq_of_central hzPuniq hcP hPc with h1 | h1
  · exact hc1 h1
  rcases hUP.eq_of_central hzPuniq hzP hPz with h2 | h2
  · exact hz1 h2
  exact hcR (h1.trans h2.symm ▸ h.le hzU)

end IsDihedralRot

omit [Finite G] in
theorem mem_sup_iff_of_commute {U U' : Subgroup G} (hcomm : ∀ a ∈ U, ∀ b ∈ U', a * b = b * a)
    {x : G} : x ∈ U ⊔ U' ↔ ∃ a ∈ U, ∃ b ∈ U', x = a * b := by
  have hN : U' ≤ normalizer (U : Set G) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← hcomm a ha b hb, mul_inv_cancel_right]
      exact ha
    · intro ha
      have hc := hcomm _ ha b hb
      have h1 : b * a = b * (b * a * b⁻¹) := by
        calc b * a = b * a * b⁻¹ * b := by group
          _ = b * (b * a * b⁻¹) := hc
      have h2 : a = b * a * b⁻¹ := mul_left_cancel h1
      rw [h2]
      exact ha
  constructor
  · intro hx
    have hx' : x ∈ ((U ⊔ U' : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left U U' hN] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem mul_inv_conj_mem_of_inv {U U' U₃ : Subgroup G} {τ : G}
    (hab : ∀ x ∈ U ⊔ U', ∀ y ∈ U ⊔ U', x * y = y * x) (hUU' : U ⊓ U' = ⊥)
    (hτU : ∀ u ∈ U, τ * u * τ⁻¹ ∈ U') (hτU' : ∀ u ∈ U', τ * u * τ⁻¹ ∈ U)
    (hU₃ : U₃ ≤ U ⊔ U') (hU₃c : IsCyclic U₃) (hinv : ∀ w ∈ U₃, τ * w * τ⁻¹ = w⁻¹)
    (hcard : Nat.card U₃ = Nat.card U) :
    ∀ u ∈ U, u * (τ * u * τ⁻¹)⁻¹ ∈ U₃ := by
  have hcomm : ∀ a ∈ U, ∀ b ∈ U', a * b = b * a := fun a ha b hb =>
    hab a (mem_sup_left ha) b (mem_sup_right hb)
  obtain ⟨w, hw⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top U₃).mp hU₃c
  have hwU₃ : w ∈ U₃ := hw ▸ mem_zpowers w
  obtain ⟨a, ha, b, hb, hwab⟩ := (mem_sup_iff_of_commute hcomm).mp (hU₃ hwU₃)
  have ha' := hτU a ha
  have hb' := hτU' b hb
  have h1 : (τ * a * τ⁻¹) * (τ * b * τ⁻¹) = a⁻¹ * b⁻¹ := by
    have := hinv w hwU₃
    rw [hwab] at this
    calc (τ * a * τ⁻¹) * (τ * b * τ⁻¹) = τ * (a * b) * τ⁻¹ := by group
      _ = (a * b)⁻¹ := this
      _ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := (hcomm _ (inv_mem ha) _ (inv_mem hb)).symm
  have h2 : (τ * b * τ⁻¹) * a = (τ * a * τ⁻¹)⁻¹ * b⁻¹ := by
    calc (τ * b * τ⁻¹) * a = (τ * a * τ⁻¹)⁻¹ * ((τ * a * τ⁻¹) * (τ * b * τ⁻¹)) * a := by group
      _ = (τ * a * τ⁻¹)⁻¹ * (a⁻¹ * b⁻¹) * a := by rw [h1]
      _ = (τ * a * τ⁻¹)⁻¹ * (b⁻¹ * a⁻¹) * a := by rw [hcomm _ (inv_mem ha) _ (inv_mem hb)]
      _ = (τ * a * τ⁻¹)⁻¹ * b⁻¹ := by group
  have h3 : (τ * b * τ⁻¹) * a ∈ U ⊓ U' :=
    mem_inf.mpr ⟨mul_mem hb' ha, h2 ▸ mul_mem (inv_mem ha') (inv_mem hb)⟩
  rw [hUU', mem_bot] at h3
  have hbeq : b = (τ * a * τ⁻¹)⁻¹ := by
    have h4 : (τ * a * τ⁻¹)⁻¹ * b⁻¹ = 1 := h2 ▸ h3
    have h5 := mul_eq_one_iff_eq_inv.mp h4
    rw [inv_inv] at h5
    exact h5.symm
  have hca : Commute a (τ * a * τ⁻¹)⁻¹ := hcomm a ha _ (inv_mem ha')
  have hφ : ∀ k : ℤ, a ^ k * (τ * a ^ k * τ⁻¹)⁻¹ = (a * (τ * a * τ⁻¹)⁻¹) ^ k := by
    intro k
    have e : τ * a ^ k * τ⁻¹ = (τ * a * τ⁻¹) ^ k := by
      rw [show τ * a ^ k * τ⁻¹ = (MulAut.conj τ) (a ^ k) by simp [MulAut.conj_apply], map_zpow]
      simp [MulAut.conj_apply]
    rw [e, hca.mul_zpow, inv_zpow]
  have hwφ : w = a * (τ * a * τ⁻¹)⁻¹ := by rw [hwab, hbeq]
  have hord : orderOf w ∣ orderOf a := by
    apply orderOf_dvd_of_pow_eq_one
    have := hφ (orderOf a)
    rw [zpow_natCast, zpow_natCast, pow_orderOf_eq_one, one_mul,
      show τ * 1 * τ⁻¹ = (1 : G) by group, inv_one] at this
    rw [hwφ, ← this]
  have hwo : orderOf w = Nat.card U := by rw [← hcard, ← hw, Nat.card_zpowers]
  have haU : zpowers a = U := by
    apply eq_of_le_of_card_ge ((zpowers_le).mpr ha)
    rw [Nat.card_zpowers, ← hwo]
    exact Nat.le_of_dvd (orderOf_pos a) hord
  intro u hu
  rw [← haU] at hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [hφ k, ← hwφ]
  exact zpow_mem hwU₃ k

end CFSG.ComponentClassification.Asc76.Sec4
