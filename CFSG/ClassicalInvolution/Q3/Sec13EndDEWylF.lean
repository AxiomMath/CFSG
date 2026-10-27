module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEWylD

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem dewF_lab2_add_self (a : Lab2) : a + a = 0 := by
  ext <;> simp [CharTwo.add_self_eq_zero]

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

theorem dewPair_shift (S : TwinShift Ω) {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v)
    (m m' : Lab2) : DewPair Ω (S.shift m K) (S.shift m' L) u v := by
  obtain ⟨hKΩ, z, hKz, hzK⟩ := S.shift_mem m K sp.memK
  obtain ⟨hLΩ, z', hLz, hzL⟩ := S.shift_mem m' L sp.memL
  have e1 : z = u := (sp.invK.eq hKz).symm
  have e2 : z' = v := (sp.invL.eq hLz).symm
  exact ⟨hKΩ, hLΩ, e1 ▸ hzK, e2 ▸ hzL, sp.ne⟩

theorem dewStar_shift (S : TwinShift Ω) {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v)
    (m m' : Lab2) :
    dewStar (S.shift m K) (S.shift m' L) = S.shift (m + m') (dewStar K L) := by
  obtain ⟨q, hq, hKq⟩ := h.exists_pCore_conj_of_mem_twinSet sp.memK (S.shift_mem m K sp.memK)
  obtain ⟨q', hq', hLq⟩ := h.exists_pCore_conj_of_mem_twinSet sp.memL (S.shift_mem m' L sp.memL)
  have hKu : K ∈ dew1V Ω u := ⟨sp.memK, sp.invK⟩
  have hLv : L ∈ dew1V Ω v := ⟨sp.memL, sp.invL⟩
  have hMv : dewStar K L ∈ dew1V Ω (u * v) := h.dewStar_mem_dew1V sp
  have hMΩ : dewStar K L ∈ Ω := hMv.1
  have huD : u ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K, sp.memK, sp.invK⟩)
  have hvD : v ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨L, sp.memL, sp.invL⟩)
  have hlu : S.lam q u = m :=
    S.shift_injective sp.memK ((h.lam_spec S hq hKu).symm.trans hKq)
  have hlv' : S.lam q' v = m' :=
    S.shift_injective sp.memL ((h.lam_spec S hq' hLv).symm.trans hLq)
  obtain ⟨r, hr_def⟩ : ∃ r : G, r = q⁻¹ * q' := ⟨_, rfl⟩
  have hr : r ∈ pCore 2 G := by
    rw [hr_def]
    exact (pCore 2 G).mul_mem ((pCore 2 G).inv_mem hq) hq'
  have hqr : q * r = q' := by rw [hr_def, mul_inv_cancel_left]
  have hrv : r * v * r⁻¹ = v := by
    have hc : r ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
      rw [h.centralizer_zGroup_eq_pCore]
      exact hr
    have hcv := Subgroup.mem_centralizer_iff.mp hc v hvD
    rw [← hcv, mul_inv_cancel_right]
  have hsp : DewPair Ω K (conjSub r L) u v :=
    ⟨sp.memK, S.conj_mem r L sp.memL, sp.invK,
      by have h1 := sp.invL.conj r; rwa [hrv] at h1, sp.ne⟩
  have hlr : S.lam r v = S.lam q v + m' := by
    rw [hr_def, h.lam_mul S ((pCore 2 G).inv_mem hq) hq' v, h.lam_inv S hq v, hlv']
  have hLr : conjSub r L = S.shift (S.lam r v) L := h.lam_spec S hr hLv
  obtain ⟨k, hkK, hkv⟩ := h.exists_not_comm_of_dewPair sp
  have hK1 : dewStar K L = conjSub k L := h.dewStar_eq sp hkK hkv
  have hK2 : dewStar K (conjSub r L) = S.shift (S.lam r v) (dewStar K L) := by
    rw [h.dewStar_eq hsp hkK hkv, hLr, ← S.shift_conj (S.lam r v) k L sp.memL, ← hK1]
  have hK4 : dewStar (S.shift m K) (S.shift m' L) = conjSub q (dewStar K (conjSub r L)) := by
    rw [h.conjSub_dewStar hsp q, hKq, ← conjSub_mul, hqr, hLq]
  have hlq : conjSub q (dewStar K L) = S.shift (S.lam q (u * v)) (dewStar K L) :=
    h.lam_spec S hq hMv
  have hadd : S.lam q (u * v) = S.lam q u + S.lam q v :=
    (h.lam_mem_dual S hq).2.2 u huD v hvD
  calc dewStar (S.shift m K) (S.shift m' L)
      = conjSub q (dewStar K (conjSub r L)) := hK4
    _ = conjSub q (S.shift (S.lam r v) (dewStar K L)) := by rw [hK2]
    _ = S.shift (S.lam r v) (conjSub q (dewStar K L)) :=
        (S.shift_conj (S.lam r v) q (dewStar K L) hMΩ).symm
    _ = S.shift (S.lam r v) (S.shift (S.lam q (u * v)) (dewStar K L)) := by rw [hlq]
    _ = S.shift (S.lam r v + S.lam q (u * v)) (dewStar K L) :=
        (S.shift_add _ _ _ hMΩ).symm
    _ = S.shift (m + m') (dewStar K L) := by
        congr 1
        rw [hlr, hadd, hlu]
        calc S.lam q v + m' + (m + S.lam q v)
            = (S.lam q v + S.lam q v) + (m + m') := by abel
          _ = m + m' := by rw [dewF_lab2_add_self, zero_add]

private theorem dewF_conj_defect (S : TwinShift Ω) {K₀ L₀ : Subgroup G} {u₀ v₀ : G}
    (sp₀ : DewPair Ω K₀ L₀ u₀ v₀) (g : G) {d : Lab2}
    (hΔ : dewStar L₀ K₀ = S.shift d (dewStar K₀ L₀)) :
    dewStar (conjSub g L₀) (conjSub g K₀) = S.shift d (dewStar (conjSub g K₀) (conjSub g L₀)) := by
  rw [← h.conjSub_dewStar sp₀.symm g, hΔ, ← S.shift_conj d g _ (h.dewStar_mem_dew1V sp₀).1,
    h.conjSub_dewStar sp₀ g]

private theorem dewF_shift_defect (S : TwinShift Ω) {K L : Subgroup G} {u v : G}
    (sp : DewPair Ω K L u v) {d : Lab2} (hΔ : dewStar L K = S.shift d (dewStar K L))
    (m m' : Lab2) :
    dewStar (S.shift m' L) (S.shift m K) = S.shift d (dewStar (S.shift m K) (S.shift m' L)) := by
  have hM : dewStar K L ∈ Ω := (h.dewStar_mem_dew1V sp).1
  rw [h.dewStar_shift S sp.symm m' m, hΔ, h.dewStar_shift S sp m m',
    ← S.shift_add (m' + m) d _ hM, ← S.shift_add d (m + m') _ hM]
  congr 1
  abel

theorem exists_defect_const (S : TwinShift Ω) :
    ∃ d₀ : Lab2, ∀ (K L : Subgroup G) (u v : G), DewPair Ω K L u v →
      dewStar L K = S.shift d₀ (dewStar K L) := by
  by_cases hb : ∃ (K L : Subgroup G) (u v : G), DewPair Ω K L u v
  · obtain ⟨K₀, L₀, u₀, v₀, sp₀⟩ := hb
    have hu₀ : u₀ ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K₀, sp₀.memK, sp₀.invK⟩)
    have hv₀ : v₀ ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨L₀, sp₀.memL, sp₀.invL⟩)
    have hM₀ : dewStar K₀ L₀ ∈ dew1V Ω (u₀ * v₀) := h.dewStar_mem_dew1V sp₀
    have hN₀ : dewStar L₀ K₀ ∈ dew1V Ω (v₀ * u₀) := h.dewStar_mem_dew1V sp₀.symm
    have hcomm : v₀ * u₀ = u₀ * v₀ := h.zGroup_comm v₀ hv₀ u₀ hu₀
    have htw : dewStar L₀ K₀ ∈ twinSet Ω (dewStar K₀ L₀) := by
      refine ⟨hN₀.1, u₀ * v₀, hM₀.2, ?_⟩
      rw [← hcomm]
      exact hN₀.2
    obtain ⟨d₀, hd₀, -⟩ := h.exists_unique_shift S hM₀.1 htw
    refine ⟨d₀, fun K L u v sp => ?_⟩
    have hu : u ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K, sp.memK, sp.invK⟩)
    have hv : v ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨L, sp.memL, sp.invL⟩)
    obtain ⟨g, hgu, hgv⟩ := h.exists_conj_pair hu₀ hv₀ hu hv sp₀.invK.ne_one sp₀.invL.ne_one
      sp.invK.ne_one sp.invL.ne_one sp₀.ne sp.ne
    have hK₁ : IsUniqueInvolution (conjSub g K₀) u := by
      have h1 := sp₀.invK.conj g
      rwa [hgu] at h1
    have hL₁ : IsUniqueInvolution (conjSub g L₀) v := by
      have h1 := sp₀.invL.conj g
      rwa [hgv] at h1
    have sp₁ : DewPair Ω (conjSub g K₀) (conjSub g L₀) u v :=
      ⟨S.conj_mem g K₀ sp₀.memK, S.conj_mem g L₀ sp₀.memL, hK₁, hL₁, sp.ne⟩
    obtain ⟨m, hm, -⟩ := h.exists_unique_shift S (S.conj_mem g K₀ sp₀.memK)
      (show K ∈ twinSet Ω (conjSub g K₀) from ⟨sp.memK, u, hK₁, sp.invK⟩)
    obtain ⟨m', hm', -⟩ := h.exists_unique_shift S (S.conj_mem g L₀ sp₀.memL)
      (show L ∈ twinSet Ω (conjSub g L₀) from ⟨sp.memL, v, hL₁, sp.invL⟩)
    have hΔ₁ := dewF_conj_defect h S sp₀ g hd₀.symm
    have key := dewF_shift_defect h S sp₁ hΔ₁ m m'
    rw [hm, hm'] at key
    exact key
  · exact ⟨0, fun K L u v sp => absurd ⟨K, L, u, v, sp⟩ hb⟩

theorem defect_const_eq_zero (S : TwinShift Ω) {d₀ : Lab2}
    (hd₀ : ∀ (K L : Subgroup G) (u v : G), DewPair Ω K L u v →
      dewStar L K = S.shift d₀ (dewStar K L)) : d₀ = 0 := by
  obtain ⟨K₀, hK₀, -⟩ := h.exists_ne
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK₀
  have huD : u ∈ zGroup Ω := h.mem_zGroup_iff.mpr (Or.inr ⟨K₀, hK₀, hu⟩)
  have hu1 : u ≠ 1 := hu.ne_one
  obtain ⟨v, hvD, hv1, hvu⟩ : ∃ v ∈ zGroup Ω, v ≠ 1 ∧ v ≠ u := by
    by_contra hcon
    push Not at hcon
    have hle : zGroup Ω ≤ Subgroup.zpowers u := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · rw [hcon x hx hx1]
        exact Subgroup.mem_zpowers u
    have h8 := Subgroup.card_le_of_le hle
    rw [h.card_zGroup, card_zpowers_of_involution hu.sq hu1] at h8
    norm_num at h8
  obtain ⟨K, hK, hKu⟩ := (h.mem_zGroup_iff.mp huD).resolve_left hu1
  obtain ⟨y, hy3, hyu, hyv⟩ := h.exists_cube huD hvD hu1 hv1 (Ne.symm hvu)
  have hy1 : y * (y * y) = 1 := (pow_three y).symm.trans hy3
  have hL : IsUniqueInvolution (conjSub y K) v := by
    have h1 := hKu.conj y
    rwa [hyu] at h1
  have hpair : DewPair Ω K (conjSub y K) u v :=
    ⟨hK, S.conj_mem y K hK, hKu, hL, Ne.symm hvu⟩
  have hNu : IsUniqueInvolution (conjSub (y * y) K) (u * v) := by
    have h1 := hKu.conj (y * y)
    have e : y * y * u * (y * y)⁻¹ = u * v := by
      calc y * y * u * (y * y)⁻¹ = y * (y * u * y⁻¹) * y⁻¹ := by group
        _ = y * v * y⁻¹ := by rw [hyu]
        _ = u * v := hyv
    rwa [e] at h1
  have hMΩ : dewStar K (conjSub y K) ∈ Ω := (h.dewStar_mem_dew1V hpair).1
  have hMu : IsUniqueInvolution (dewStar K (conjSub y K)) (u * v) :=
    (h.dewStar_mem_dew1V hpair).2
  have hNΩ : conjSub (y * y) K ∈ Ω := S.conj_mem (y * y) K hK
  have hLΩ : conjSub y K ∈ Ω := S.conj_mem y K hK
  obtain ⟨μ, hμ, -⟩ := h.exists_unique_shift S hMΩ
    (show conjSub (y * y) K ∈ twinSet Ω (dewStar K (conjSub y K)) from
      ⟨hNΩ, u * v, hMu, hNu⟩)
  have hMN : dewStar K (conjSub y K) = S.shift μ (conjSub (y * y) K) := by
    rw [← hμ, S.shift_shift_self μ hMΩ]
  have hMd : dewStar K (conjSub y K) = S.shift d₀ (dewStar (conjSub y K) K) := by
    rw [hd₀ K (conjSub y K) u v hpair, S.shift_shift_self d₀ hMΩ]
  have hpairLK : DewPair Ω (conjSub y K) K v u := hpair.symm
  have hLK : dewStar (conjSub y K) K ∈ dew1V Ω (v * u) := h.dewStar_mem_dew1V hpairLK
  have hne1 : v ≠ u * v :=
    fun h' => hu1 (mul_right_cancel (b := v) (by rw [one_mul]; exact h'.symm))
  have hne2 : v ≠ v * u :=
    fun h' => hu1 (mul_left_cancel (a := v) (by rw [mul_one]; exact h')).symm
  have hpairLM : DewPair Ω (conjSub y K) (dewStar K (conjSub y K)) v (u * v) :=
    ⟨hLΩ, hMΩ, hL, hMu, hne1⟩
  have hpairLLK : DewPair Ω (conjSub y K) (dewStar (conjSub y K) K) v (v * u) :=
    ⟨hLΩ, hLK.1, hL, hLK.2, hne2⟩
  have hB := h.dewStar_shift S hpairLM 0 μ
  rw [S.shift_zero _ hLΩ, hμ, zero_add] at hB
  have hC0 := h.dewStar_shift S hpairLLK 0 d₀
  rw [S.shift_zero _ hLΩ, zero_add, h.dewStar_dewStar hpairLK] at hC0
  have hC : dewStar (conjSub y K) (dewStar K (conjSub y K)) = S.shift d₀ K := by
    rw [hMd]
    exact hC0
  have hE : conjSub y (dewStar K (conjSub y K)) = dewStar (conjSub y K) (conjSub (y * y) K) := by
    rw [h.conjSub_dewStar hpair y, ← conjSub_mul]
  have hyN : conjSub y (conjSub (y * y) K) = K := by
    rw [← conjSub_mul, hy1, conjSub_one]
  have hF : conjSub y (dewStar K (conjSub y K)) = S.shift μ K := by
    rw [hMN, ← S.shift_conj μ y (conjSub (y * y) K) hNΩ, hyN]
  have hcalc : S.shift μ K = S.shift (μ + d₀) K := by
    calc S.shift μ K = conjSub y (dewStar K (conjSub y K)) := hF.symm
      _ = dewStar (conjSub y K) (conjSub (y * y) K) := hE
      _ = S.shift μ (dewStar (conjSub y K) (dewStar K (conjSub y K))) := hB
      _ = S.shift μ (S.shift d₀ K) := by rw [hC]
      _ = S.shift (μ + d₀) K := (S.shift_add μ d₀ K hK).symm
  have hμd : μ = μ + d₀ := S.shift_injective hK hcalc
  have h0 : μ + d₀ = μ + 0 := by
    rw [add_zero]
    exact hμd.symm
  exact add_left_cancel h0

theorem dewStar_comm {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v) :
    dewStar K L = dewStar L K := by
  obtain ⟨S⟩ := h.exists_twinShift
  obtain ⟨d₀, hd₀⟩ := h.exists_defect_const S
  have h0 : d₀ = 0 := h.defect_const_eq_zero S hd₀
  rw [hd₀ K L u v sp, h0, S.shift_zero _ (h.dewStar_mem_dew1V sp).1]

end DE4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
