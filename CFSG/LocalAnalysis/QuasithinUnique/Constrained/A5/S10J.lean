module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S10D
public import Certificates.Certificate17027
public import Certificates.Certificate5952

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem zp_sq (C : StdCfg T M H S L) (t : ZMod 2) : C.zp t * C.zp t = 1 := by
  rw [← C.zp_add, zmod2_add_self']
  simp [zp]

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem exists_refl_T
    : ∃ (y₀ : G) (w : V4), y₀ ∈ T ∧ y₀ ∉ S ∧ quadHyp w = 1 ∧
    ∀ x : V4, ((X.rg y₀ : GL (Fin 4) (ZMod 2)) : Mat4).mulVec x = x + Bf x w • w := by
  obtain ⟨x, hxT, hxS⟩ := C.exists_mem_T_sdiff
  have hxM : x ∈ M := C.T_le_M hxT
  have hgO : X.rg x ∈ O4PlusTwo := X.rg_mem_O4 hxM
  have hn : ∀ V ∈ VSL, ∃ V' ∈ VSL, ((X.rg x : GL (Fin 4) (ZMod 2)) : Mat4) * V =
      V' * ((X.rg x : GL (Fin 4) (ZMod 2)) : Mat4) := by
    intro V hV
    obtain ⟨s, hsS, hsV⟩ := X.exists_S_of_VSL hV
    have hsM : s ∈ M := C.S_le_M hsS
    have hxsx : x * s * x⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (C.T_normalizes_S hxT) s).mp hsS
    have hxsxM : x * s * x⁻¹ ∈ M := M.mul_mem (M.mul_mem hxM hsM) (M.inv_mem hxM)
    have h1 : X.rg x * X.rg s = X.rg (x * s) := (X.rg_mul hxM hsM).symm
    have h2 : X.rg (x * s * x⁻¹) * X.rg x = X.rg (x * s) := by
      rw [← X.rg_mul hxsxM hxM]
      congr 1
      group
    refine ⟨_, X.rg_S_mem_VSL hxsx, ?_⟩
    rw [← hsV]
    have h3 : (X.rg x * X.rg s : GL (Fin 4) (ZMod 2)) = X.rg (x * s * x⁻¹) * X.rg x :=
      h1.trans h2.symm
    simpa only [Units.val_mul] using congrArg Units.val h3
  have hnot : ((X.rg x : GL (Fin 4) (ZMod 2)) : Mat4) ∉ VSL := by
    intro hmem
    obtain ⟨s, hsS, hsV⟩ := X.exists_S_of_VSL hmem
    have hsM : s ∈ M := C.S_le_M hsS
    have h1 : X.rg s = X.rg x := Units.ext hsV
    have hP : s⁻¹ * x ∈ borelP M L := by
      refine (X.rg_eq_one_iff (M.mul_mem (M.inv_mem hsM) hxM)).mp ?_
      rw [X.rg_mul (M.inv_mem hsM) hxM, X.rg_inv hsM, h1]
      group
    apply hxS
    have : x = s * (s⁻¹ * x) := by group
    rw [this]
    exact S.mul_mem hsS (X.P_le_S hP)
  obtain ⟨V, hV, w, hw, hx⟩ := normS_cases hgO hn hnot
  obtain ⟨s, hsS, hsV⟩ := X.exists_S_of_VSL hV
  have hsM : s ∈ M := C.S_le_M hsS
  refine ⟨x * s, w, T.mul_mem hxT (C.hcs.le_T hsS), ?_, hw, ?_⟩
  · intro hxs
    apply hxS
    have : x = (x * s) * s⁻¹ := by group
    rw [this]
    exact S.mul_mem hxs (S.inv_mem hsS)
  · intro y
    rw [X.rg_mul hxM hsM, Units.val_mul, hsV]
    exact hx y

theorem exists_adjust
    {y₀ : G} {w : V4} (hw : quadHyp w = 1) (hy0M : y₀ ∈ M)
    (hthy : ∀ p ∈ borelP M L, y₀ * p * y₀⁻¹ ∈ borelP M L ∧
      X.th (y₀ * p * y₀⁻¹) = X.th p + Bf (X.th p) w • w) :
    ∃ a ∈ borelP M L, inPl w (X.th a) ∧
      ∀ q ∈ borelP M L, inPl w (X.th q) → (a * y₀) * q * (a * y₀)⁻¹ = q := by
  have hconj : ∀ q ∈ borelP M L, inPl w (X.th q) →
      ∃ t : ZMod 2, y₀ * q * y₀⁻¹ = q * C.zp t := by
    intro q hq hqpl
    obtain ⟨h1, h2⟩ := hthy q hq
    rw [pl_Bf w _ hqpl, zero_smul, add_zero] at h2
    rcases X.th_fiber h1 hq h2 with h | h
    · exact ⟨0, by rw [h]; simp [StdCfg.zp]⟩
    · exact ⟨1, by rw [h]; simp [StdCfg.zp]⟩
  obtain ⟨a1, a2, ha1, ha2, ha10, ha20, ha12, hall, hsolve⟩ := pl_basis w hw
  obtain ⟨q1, hq1P, hq1th⟩ := X.th_exists a1
  obtain ⟨q2, hq2P, hq2th⟩ := X.th_exists a2
  obtain ⟨t1, ht1⟩ := hconj q1 hq1P (by rw [hq1th]; exact ha1)
  obtain ⟨t2, ht2⟩ := hconj q2 hq2P (by rw [hq2th]; exact ha2)
  obtain ⟨b, hbpl, hb1, hb2⟩ := hsolve t1 t2
  obtain ⟨a, haP, hath⟩ := X.th_exists b
  refine ⟨a, haP, by rw [hath]; exact hbpl, ?_⟩
  have haM : a ∈ M := C.P_le_M haP
  have hy1M : a * y₀ ∈ M := M.mul_mem haM hy0M
  have key : ∀ (q : G), q ∈ borelP M L → ∀ (t : ZMod 2), y₀ * q * y₀⁻¹ = q * C.zp t →
      Bf (X.th a) (X.th q) = t → (a * y₀) * q * (a * y₀)⁻¹ = q := by
    intro q hq t hqt hBt
    have hc := X.comm_th haP hq
    rw [hBt] at hc
    have hqM : q ∈ M := C.P_le_M hq
    have e1 : a * q * a⁻¹ = C.zp t * q := by
      calc a * q * a⁻¹ = (a * q * a⁻¹ * q⁻¹) * q := by group
        _ = C.zp t * q := by rw [hc]
    have e2 : a * C.zp t * a⁻¹ = C.zp t := by
      have := X.zp_comm_M t haM
      calc a * C.zp t * a⁻¹ = (C.zp t * a) * a⁻¹ := by rw [this]
        _ = C.zp t := by group
    calc (a * y₀) * q * (a * y₀)⁻¹ = a * (y₀ * q * y₀⁻¹) * a⁻¹ := by group
      _ = a * (q * C.zp t) * a⁻¹ := by rw [hqt]
      _ = (a * q * a⁻¹) * (a * C.zp t * a⁻¹) := by group
      _ = (C.zp t * q) * C.zp t := by rw [e1, e2]
      _ = (q * C.zp t) * C.zp t := by rw [X.zp_comm_M t hqM]
      _ = q * (C.zp t * C.zp t) := by group
      _ = q := by rw [C.zp_sq, mul_one]
  have hmulc : ∀ q q' : G, (a * y₀) * q * (a * y₀)⁻¹ = q → (a * y₀) * q' * (a * y₀)⁻¹ = q' →
      (a * y₀) * (q * q') * (a * y₀)⁻¹ = q * q' := by
    intro q q' h h'
    calc (a * y₀) * (q * q') * (a * y₀)⁻¹ =
        ((a * y₀) * q * (a * y₀)⁻¹) * ((a * y₀) * q' * (a * y₀)⁻¹) := by group
      _ = q * q' := by rw [h, h']
  have hzc : (a * y₀) * C.zU * (a * y₀)⁻¹ = C.zU := X.zU_conj_M hy1M
  have hc1 : (a * y₀) * q1 * (a * y₀)⁻¹ = q1 := key q1 hq1P t1 ht1 (by rw [hath, hq1th]; exact hb1)
  have hc2 : (a * y₀) * q2 * (a * y₀)⁻¹ = q2 := key q2 hq2P t2 ht2 (by rw [hath, hq2th]; exact hb2)
  intro q hq hqpl
  have hfib : ∀ r : G, r ∈ borelP M L → X.th r = X.th q → (a * y₀) * r * (a * y₀)⁻¹ = r →
      (a * y₀) * q * (a * y₀)⁻¹ = q := by
    intro r hr hth hrc
    rcases X.th_fiber hq hr hth.symm with h | h
    · rw [h]; exact hrc
    · rw [h]; exact hmulc r _ hrc hzc
  rcases hall _ hqpl with h0 | h0 | h0 | h0
  · rcases (X.th_eq_zero_iff hq).mp h0 with rfl | rfl
    · simp
    · exact hzc
  · exact hfib q1 hq1P (by rw [hq1th, h0]) hc1
  · exact hfib q2 hq2P (by rw [hq2th, h0]) hc2
  · exact hfib (q1 * q2) (mul_mem hq1P hq2P) (by rw [X.th_mul hq1P hq2P, hq1th, hq2th, h0])
      (hmulc q1 q2 hc1 hc2)

omit X in
theorem smul_w_eq_zero {w : V4} (hw : quadHyp w = 1) (c : ZMod 2) (h : c • w = 0) : c = 0 := by
  rcases zmod2_cases c with rfl | rfl
  · rfl
  · exfalso
    rw [one_smul] at h
    rw [h] at hw
    exact absurd hw (by decide)

theorem exists_y2
    : ∃ (y₂ : G) (w : V4), y₂ ∈ T ∧ y₂ ∉ S ∧ quadHyp w = 1 ∧
    (∀ q ∈ borelP M L, inPl w (X.th q) → y₂ * q * y₂⁻¹ = q) ∧
    (y₂ * y₂ = 1 ∨ y₂ * y₂ = C.zU) := by
  obtain ⟨y₀, w, hy0T, hy0S, hw, hy⟩ := X.exists_refl_T
  have hy0M : y₀ ∈ M := C.T_le_M hy0T
  have hrg_th : ∀ y : G, y ∈ M → X.rg y = X.rg y₀ → ∀ p ∈ borelP M L,
      y * p * y⁻¹ ∈ borelP M L ∧ X.th (y * p * y⁻¹) = X.th p + Bf (X.th p) w • w := by
    intro y hyM hyr p hp
    obtain ⟨h1, h2⟩ := X.th_conj hyM hp
    rw [hyr, hy] at h2
    exact ⟨h1, h2⟩
  obtain ⟨a, haP, hapl, hcent⟩ := X.exists_adjust hw hy0M (hrg_th y₀ hy0M rfl)
  have haM : a ∈ M := C.P_le_M haP
  have haS : a ∈ S := X.P_le_S haP
  set y₁ : G := a * y₀ with hy1
  have hy1M : y₁ ∈ M := M.mul_mem haM hy0M
  have hy1T : y₁ ∈ T := T.mul_mem (C.hcs.le_T haS) hy0T
  have hy1S : y₁ ∉ S := by
    intro h
    apply hy0S
    have : y₀ = a⁻¹ * y₁ := by rw [hy1]; group
    rw [this]
    exact S.mul_mem (S.inv_mem haS) h
  have hrg1 : X.rg y₁ = X.rg y₀ := by
    rw [hy1, X.rg_mul haM hy0M, (X.rg_eq_one_iff haM).mpr haP, one_mul]
  have hth1 := hrg_th y₁ hy1M hrg1
  have hsq : X.rg y₁ * X.rg y₁ = 1 := by
    rw [hrg1]
    exact Units.ext (by rw [Units.val_mul]; exact refl_sq hy)
  have hsP : y₁ * y₁ ∈ borelP M L :=
    (X.rg_eq_one_iff (M.mul_mem hy1M hy1M)).mp (by rw [X.rg_mul hy1M hy1M]; exact hsq)
  have hscent : ∀ q ∈ borelP M L, inPl w (X.th q) → (y₁ * y₁) * q * (y₁ * y₁)⁻¹ = q := by
    intro q hq hqpl
    have := hcent q hq hqpl
    calc (y₁ * y₁) * q * (y₁ * y₁)⁻¹ = y₁ * (y₁ * q * y₁⁻¹) * y₁⁻¹ := by group
      _ = q := by rw [this, this]
  have hspl' : inPl' w (X.th (y₁ * y₁)) := by
    refine pl_perp w _ hw ?_
    intro a1 ha1
    obtain ⟨q, hqP, hqth⟩ := X.th_exists a1
    have hc := X.comm_th hsP hqP
    have h0 : (y₁ * y₁) * q * (y₁ * y₁)⁻¹ * q⁻¹ = 1 := by
      rw [hscent q hqP (by rw [hqth]; exact ha1)]
      group
    rw [h0, hqth] at hc
    rw [Bf_comm]
    exact (zp_eq_one_iff C _).mp hc.symm
  have hsB : Bf (X.th (y₁ * y₁)) w = 0 := by
    obtain ⟨h1, h2⟩ := hth1 _ hsP
    have : y₁ * (y₁ * y₁) * y₁⁻¹ = y₁ * y₁ := by group
    rw [this] at h2
    have h3 : Bf (X.th (y₁ * y₁)) w • w = 0 := left_eq_add.mp h2
    exact smul_w_eq_zero hw _ h3
  rcases pl'_fix w _ hw hspl' hsB with h0 | h0
  · refine ⟨y₁, w, hy1T, hy1S, hw, fun q hq hqpl => hcent q hq hqpl, ?_⟩
    exact (X.th_eq_zero_iff hsP).mp h0
  ·
    obtain ⟨w', hw'pl, hw'0, hw'w⟩ := pl'_other w hw
    obtain ⟨b, hbP, hbth⟩ := X.th_exists w'
    have hbM : b ∈ M := C.P_le_M hbP
    have hbS : b ∈ S := X.P_le_S hbP
    refine ⟨b * y₁, w, T.mul_mem (C.hcs.le_T hbS) hy1T, ?_, hw, ?_, ?_⟩
    · intro h
      apply hy1S
      have : y₁ = b⁻¹ * (b * y₁) := by group
      rw [this]
      exact S.mul_mem (S.inv_mem hbS) h
    · intro q hq hqpl
      have hbc : b * q * b⁻¹ = q := by
        have hc := X.comm_th hbP hq
        have hB : Bf (X.th b) (X.th q) = 0 := by
          rw [hbth, Bf_comm]
          exact pl_orth w _ _ hw hqpl hw'pl
        rw [hB] at hc
        have hz0 : C.zp 0 = 1 := by simp [StdCfg.zp]
        rw [hz0] at hc
        calc b * q * b⁻¹ = (b * q * b⁻¹ * q⁻¹) * q := by group
          _ = q := by rw [hc, one_mul]
      have h1 := hcent q hq hqpl
      calc (b * y₁) * q * (b * y₁)⁻¹ = b * (y₁ * q * y₁⁻¹) * b⁻¹ := by group
        _ = q := by rw [h1, hbc]
    ·
      have hy1c : y₁ * (b * y₁) = (y₁ * b * y₁⁻¹) * (y₁ * y₁) := by group
      have hb' : y₁ * b * y₁⁻¹ ∈ borelP M L := (hth1 b hbP).1
      have hbth' : X.th (y₁ * b * y₁⁻¹) = w' + w := by
        rw [(hth1 b hbP).2, hbth, pl'_Bfw w w' hw hw'pl hw'0 hw'w, one_smul]
      have hprod : (b * y₁) * (b * y₁) = b * (y₁ * b * y₁⁻¹) * (y₁ * y₁) := by group
      have hP : (b * y₁) * (b * y₁) ∈ borelP M L := by
        rw [hprod]
        exact mul_mem (mul_mem hbP hb') hsP
      have hth0 : X.th ((b * y₁) * (b * y₁)) = 0 := by
        rw [hprod, X.th_mul (mul_mem hbP hb') hsP, X.th_mul hbP hb', hbth, hbth', h0]
        calc w' + (w' + w) + w = (w' + w') + (w + w) := by abel
          _ = 0 := by rw [V4_add_self, V4_add_self, add_zero]
      exact (X.th_eq_zero_iff hP).mp hth0

theorem exists_j :
    ∃ j ∈ T, j ∉ S ∧ j ^ 2 = C.zU := by
  obtain ⟨y₂, w, hy2T, hy2S, hw, hcent, hsq⟩ := X.exists_y2
  rcases hsq with h1 | h1
  ·
    obtain ⟨a1, a2, ha1, ha2, ha10, ha20, ha12, hall, hsolve⟩ := pl_basis w hw
    obtain ⟨a₀, ha₀P, ha₀th⟩ := X.th_exists a1
    have ha₀S : a₀ ∈ S := X.P_le_S ha₀P
    have ha₀2 : a₀ * a₀ = C.zU := by
      rcases X.sq_th ha₀P with ⟨-, h2⟩ | ⟨h2, -⟩
      · rw [ha₀th, pl_q w a1 ha1 ha10] at h2
        exact absurd h2 (by decide)
      · exact h2
    have hcomm : y₂ * a₀ = a₀ * y₂ := by
      have := hcent a₀ ha₀P (by rw [ha₀th]; exact ha1)
      calc y₂ * a₀ = (y₂ * a₀ * y₂⁻¹) * y₂ := by group
        _ = a₀ * y₂ := by rw [this]
    refine ⟨y₂ * a₀, T.mul_mem hy2T (C.hcs.le_T ha₀S), ?_, ?_⟩
    · intro h
      apply hy2S
      have : y₂ = (y₂ * a₀) * a₀⁻¹ := by group
      rw [this]
      exact S.mul_mem h (S.inv_mem ha₀S)
    · calc (y₂ * a₀) ^ 2 = y₂ * a₀ * (y₂ * a₀) := by rw [pow_two]
        _ = y₂ * (a₀ * y₂) * a₀ := by group
        _ = y₂ * (y₂ * a₀) * a₀ := by rw [hcomm]
        _ = (y₂ * y₂) * (a₀ * a₀) := by group
        _ = C.zU := by rw [h1, ha₀2, one_mul]
  · exact ⟨y₂, hy2T, hy2S, by rw [pow_two]; exact h1⟩

end Sec

end CFSG.QuasithinUnique.A5
