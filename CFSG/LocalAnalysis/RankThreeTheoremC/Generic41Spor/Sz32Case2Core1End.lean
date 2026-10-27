module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Num

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section End

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}

theorem szh1e_exists_exp {C : Subgroup Y} {g y : Y} (hC : C = Subgroup.zpowers g)
    (hy : ∀ u ∈ C, y * u * y⁻¹ ∈ C) : ∃ n : ℤ, ∀ u ∈ C, y * u * y⁻¹ = u ^ n := by
  have hg : g ∈ C := hC ▸ Subgroup.mem_zpowers g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hC ▸ hy g hg)
  refine ⟨n, fun u hu => ?_⟩
  rw [hC] at hu
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  calc y * g ^ m * y⁻¹ = (y * g * y⁻¹) ^ m := conj_zpow.symm
    _ = (g ^ n) ^ m := by rw [hn]
    _ = (g ^ m) ^ n := by rw [← zpow_mul, ← zpow_mul, mul_comm]

theorem szh1e_pow_conj {C : Subgroup Y} {y : Y} {n : ℤ} (hn : ∀ u ∈ C, y * u * y⁻¹ = u ^ n)
    (k : ℕ) {u : Y} (hu : u ∈ C) : y ^ k * u * (y ^ k)⁻¹ = u ^ (n ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : y ^ (k + 1) * u * (y ^ (k + 1))⁻¹ = y * (y ^ k * u * (y ^ k)⁻¹) * y⁻¹ := by
      rw [pow_succ']; group
    rw [e, ih, ← conj_zpow, hn u hu, ← zpow_mul, pow_succ']

theorem szh1e_zmod_eq {n m : ℤ} (h : (25 : ℤ) ∣ n - m) : (n : ZMod 25) = (m : ZMod 25) := by
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub m n 25).mpr (by simpa using h)
  exact this.symm

theorem szh1e_zpow_eq_self {u : Y} (h25 : u ^ 25 = 1) {n : ℤ} (hn : (n : ZMod 25) = 1) :
    u ^ n = u := by
  have h1 : (25 : ℤ) ∣ n - 1 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 n 25).mp (by simpa using hn.symm)
    simpa using this
  obtain ⟨m, hm⟩ := h1
  have : n = 1 + 25 * m := by omega
  rw [this, zpow_add, zpow_one, zpow_mul]
  have h25' : u ^ (25 : ℤ) = 1 := by simpa using h25
  rw [h25', one_zpow, mul_one]

theorem szh1_two_numeric (hY : Sz32Case2Data Pb a c y) {L₁ L₂ : Subgroup Y} {t : Y}
    (h : Szh1Two Pb L₁ L₂ t) (hs : Szh1Cyc Pb a c y L₁ L₂)
    (hnot : t * y * t⁻¹ * y⁻¹ ∉ sz32Q0 a c) : False := by
  obtain ⟨g₁, hg₁o, hP₁⟩ := hs.cyc₁
  obtain ⟨g₂, hg₂o, hP₂⟩ := hs.cyc₂
  have hyP : y ∈ Pb := hY.pres.y_mem
  have hL12 : ⁅L₁, L₂⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h.comp₁ h.comp₂ h.ne
  have hcomm : ∀ u ∈ L₁, ∀ v ∈ L₂, u * v = v * u := by
    intro u hu v hv
    have h1 := Subgroup.commutator_mem_commutator hu hv
    rw [hL12, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hdisj : (Pb ⊓ L₁) ⊓ (Pb ⊓ L₂) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : x ∈ L₁ := hx.1.2
    have hx2 : x ∈ L₂ := hx.2.2
    have hxc : (⟨x, hx1⟩ : L₁) ∈ Subgroup.center L₁ := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (hcomm z.1 z.2 x hx2)
    rw [h.cen₁, Subgroup.mem_bot] at hxc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)
  have hcommP : ∀ u ∈ Pb ⊓ L₁, ∀ v ∈ Pb ⊓ L₂, u * v = v * u :=
    fun u hu v hv => hcomm u hu.2 v hv.2
  have hyP₁ : ∀ u ∈ Pb ⊓ L₁, y * u * y⁻¹ ∈ Pb ⊓ L₁ := by
    intro u hu
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hyP hu.1) (Subgroup.inv_mem _ hyP),
      (Subgroup.mem_normalizer_iff.mp (h.norm₁ y hyP) u).mp hu.2⟩
  have hyP₂ : ∀ u ∈ Pb ⊓ L₂, y * u * y⁻¹ ∈ Pb ⊓ L₂ := by
    intro u hu
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hyP hu.1) (Subgroup.inv_mem _ hyP),
      (Subgroup.mem_normalizer_iff.mp (h.norm₂ y hyP) u).mp hu.2⟩
  obtain ⟨n₁, hn₁⟩ := szh1e_exists_exp hP₁ hyP₁
  obtain ⟨n₂, hn₂⟩ := szh1e_exists_exp hP₂ hyP₂
  have hg₂ : g₂ ∈ Pb ⊓ L₂ := by rw [hP₂]; exact Subgroup.mem_zpowers g₂
  have hg₁ : g₁ ∈ Pb ⊓ L₁ := by rw [hP₁]; exact Subgroup.mem_zpowers g₁
  have htP : ∀ u ∈ Pb, t * u * t⁻¹ ∈ Pb := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp h.t_norm u).mp hu
  have htP' : ∀ u ∈ Pb, t⁻¹ * u * t ∈ Pb := by
    intro u hu
    have h1 := (Subgroup.mem_normalizer_iff.mp h.t_norm (t⁻¹ * u * t)).mpr
    have e : t * (t⁻¹ * u * t) * t⁻¹ = u := by group
    exact h1 (by rw [e]; exact hu)
  have ht₁ : ∀ u ∈ L₁, t * u * t⁻¹ ∈ L₂ := by
    intro u hu
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hu
    rw [h.t₁] at h1
    simpa using h1
  have ht₁' : ∀ v ∈ L₂, t⁻¹ * v * t ∈ L₁ := by
    intro v hv
    rw [← h.t₁] at hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    have e : t⁻¹ * (MulAut.conj t).toMonoidHom u * t = u := by simp [MulAut.conj_apply]; group
    rw [e]; exact hu
  obtain ⟨k, q, hq, hkq⟩ := szh1_Pb_decomp hY (htP y hyP)
  have hQ0 : sz32Q0 a c = (Pb ⊓ L₁) ⊔ (Pb ⊓ L₂) := hs.Q0
  have hact₂ : ∀ v ∈ Pb ⊓ L₂, (t * y * t⁻¹) * v * (t * y * t⁻¹)⁻¹ = v ^ (n₂ ^ k) := by
    intro v hv
    have hvQ : v ∈ sz32Q0 a c := by rw [hQ0]; exact Subgroup.mem_sup_right hv
    have hqv : q * v = v * q := congrArg Subtype.val
      (hY.facts.Q0_comm.is_comm.comm ⟨q, hq⟩ ⟨v, hvQ⟩)
    have hqv' : q * v * q⁻¹ = v := by rw [hqv]; group
    rw [hkq]
    calc y ^ k * q * v * (y ^ k * q)⁻¹ = y ^ k * (q * v * q⁻¹) * (y ^ k)⁻¹ := by group
      _ = y ^ k * v * (y ^ k)⁻¹ := by rw [hqv']
      _ = v ^ (n₂ ^ k) := szh1e_pow_conj hn₂ k hv
  have hact₁ : ∀ u ∈ Pb ⊓ L₁, (t * y * t⁻¹) * (t * u * t⁻¹) * (t * y * t⁻¹)⁻¹ =
      (t * u * t⁻¹) ^ n₁ := by
    intro u hu
    have e : (t * y * t⁻¹) * (t * u * t⁻¹) * (t * y * t⁻¹)⁻¹ = t * (y * u * y⁻¹) * t⁻¹ := by group
    rw [e, hn₁ u hu, conj_zpow]
  have hmod : (n₁ : ZMod 25) = (n₂ : ZMod 25) ^ k := by
    have hu : t⁻¹ * g₂ * t ∈ Pb ⊓ L₁ := ⟨htP' g₂ hg₂.1, ht₁' g₂ hg₂.2⟩
    have hv : t * (t⁻¹ * g₂ * t) * t⁻¹ = g₂ := by group
    have h1 := hact₁ _ hu
    have h2 := hact₂ (t * (t⁻¹ * g₂ * t) * t⁻¹) ⟨htP _ hu.1, ht₁ _ hu.2⟩
    rw [hv] at h1 h2
    have h3 : g₂ ^ n₁ = g₂ ^ (n₂ ^ k) := h1.symm.trans h2
    have h4 : g₂ ^ (n₁ - n₂ ^ k) = 1 := by rw [zpow_sub, h3, mul_inv_cancel]
    have h5 : (orderOf g₂ : ℤ) ∣ n₁ - n₂ ^ k := orderOf_dvd_iff_zpow_eq_one.mpr h4
    rw [hg₂o] at h5
    have h6 := szh1e_zmod_eq (by simpa using h5)
    simpa using h6
  have h5 : (n₂ : ZMod 25) ^ 5 = 1 := by
    have h1 := szh1e_pow_conj hn₂ 5 hg₂
    rw [hY.pres.y5, one_mul, inv_one, mul_one] at h1
    have h2 : g₂ ^ (n₂ ^ 5 - 1) = 1 := by rw [zpow_sub, ← h1, zpow_one, mul_inv_cancel]
    have h3 : (orderOf g₂ : ℤ) ∣ n₂ ^ 5 - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hg₂o] at h3
    have h4 := szh1e_zmod_eq (n := n₂ ^ 5) (m := 1) (by simpa using h3)
    simpa using h4
  have hne : n₁ % 25 ≠ n₂ % 25 := by
    intro heq
    have hZ : (n₁ : ZMod 25) = (n₂ : ZMod 25) :=
      (ZMod.intCast_eq_intCast_iff' n₁ n₂ 25).mpr (by simpa using heq)
    by_cases hn21 : (n₂ : ZMod 25) = 1
    · have hn11 : (n₁ : ZMod 25) = 1 := hZ.trans hn21
      have hya : y * a * y⁻¹ = a := by
        have haQ : a ∈ (Pb ⊓ L₁) ⊔ (Pb ⊓ L₂) := by rw [← hQ0]; exact szh1_a_mem_Q0 a c
        obtain ⟨u₁, hu₁, u₂, hu₂, hau⟩ := szh1n_mem_sup hcommP haQ
        rw [hau]
        have e : y * (u₁ * u₂) * y⁻¹ = (y * u₁ * y⁻¹) * (y * u₂ * y⁻¹) := by group
        rw [e, hn₁ u₁ hu₁, hn₂ u₂ hu₂, szh1e_zpow_eq_self (hY.facts.exp u₁ hu₁.1) hn11,
          szh1e_zpow_eq_self (hY.facts.exp u₂ hu₂.1) hn21]
      obtain ⟨n, hn, -, hn25⟩ := hY.pres.ya
      rw [hn] at hya
      have h1 : a ^ (n - 1) = 1 := by rw [zpow_sub, hya, zpow_one, mul_inv_cancel]
      have h2 : (orderOf a : ℤ) ∣ n - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [hY.pres.ord_a] at h2
      omega
    · have key : ∀ x : ZMod 25, x ^ 5 = 1 → x ≠ 1 → ∀ r : Fin 5, x ^ (r : ℕ) = x → (r : ℕ) = 1 := by
        decide
      have hk : (n₂ : ZMod 25) ^ k = (n₂ : ZMod 25) := hmod.symm.trans hZ
      have hk1 : (n₂ : ZMod 25) ^ (k % 5) = (n₂ : ZMod 25) :=
        (pow_eq_pow_mod k h5).symm.trans hk
      have hk5 : k % 5 = 1 := key _ h5 hn21 ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩ hk1
      apply hnot
      rw [hkq]
      have hyk : y ^ k = y := by
        have e : k = 5 * (k / 5) + 1 := by omega
        rw [e, pow_add, pow_mul, hY.pres.y5, one_pow, one_mul, pow_one]
      rw [hyk]
      exact szh1_y_norm_Q0 hY hq
  have hc : c ∈ (Pb ⊓ L₁) ⊔ (Pb ⊓ L₂) := by rw [← hQ0]; exact szh1_c_mem_Q0 a c
  obtain ⟨ν, hν, -⟩ := hY.pres.yc
  have hfin := szh1_num_final hcommP hdisj (fun u hu => hY.facts.exp u hu.1)
    (fun u hu => hY.facts.exp u hu.1) hn₁ hn₂ hne hc hν
  obtain ⟨S, hS⟩ := hY.sylow
  obtain ⟨N, hser⟩ := hY.series
  rw [← hS] at hser
  rcases hfin with h1 | h2
  · refine szh1_not_le_of_centSeries hY.core S hser h.comp₂ ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hcomm _ h1.2 v hv
  · refine szh1_not_le_of_centSeries hY.core S hser h.comp₁ ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (hcomm v hv _ h2.2).symm

end End

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
