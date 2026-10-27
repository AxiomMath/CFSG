module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5G
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem5F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem autOn_eq_top_of_isLine625_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4) {F : Subgroup G}
    (hFV : F ≤ V) (hF4 : Nat.card F = 4) {v : Fin 2 → h.data.K} (hL : h.IsLine625 F v) :
    autOn (ch6MV M V ⊓ Subgroup.normalizer (F : Set G)) F = ⊤ := by
  have hK := h.card_K_ch625

  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_ch625 hK
  obtain ⟨u, hu⟩ : ∃ u : Fin 2 → h.data.K, det2 v u ≠ 0 := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hL.1
        funext i
        fin_cases i <;> simp [h0, h1]
      exact ⟨![1, 0], by simp [det2, h0, h1]⟩
    · exact ⟨![0, 1], by simp [det2, h0]⟩
  have hdet : det2 (ω • v) (ω⁻¹ • u) = det2 v u := by
    rw [det2_smul_left_ch625, det2_smul_right_ch625, ← mul_assoc, mul_inv_cancel₀ hω0, one_mul]
  obtain ⟨l, hlL, hlv, -⟩ := h.exists_L_basis_ch625 hu hdet
  have hlin := (h.isLin625_and_det_of_mem_L l hlL).1
  have hlc : ∀ c : h.data.K, h.data.conj l (c • v) = (c * ω) • v := fun c => by
    rw [hlin, hlv, smul_smul]
  have hlv' : h.data.conj l (ω⁻¹ • v) = v := by
    rw [hlc, inv_mul_cancel₀ hω0, one_smul]
  have hL' := h.isLine625_conjSubgroup hL l (σ := RingEquiv.refl _) (fun c w => hlin c w) hlv'
  have hlN : (l : G) ∈ Subgroup.normalizer (F : Set G) := by
    have hFlV : conjSubgroup F l ≤ V := by
      have := conjSubgroup_mono_left (l : G) hFV
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr l.2] at this
    refine conjSubgroup_eq_iff_mem_normalizer.mp (h.eq_of_vec625_iff hFlV hFV fun w => ?_)
    rw [hL'.2, hL.2]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c * ω⁻¹, by rw [smul_smul]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c * ω, by rw [smul_smul, mul_assoc, mul_inv_cancel₀ hω0, mul_one]⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω3 := pow_three_ch625 hK hω0
  have hord₃ := h.orderOf_conjAct_eq_prime hFV (p := 3) l hlN (fun w hw => by
      obtain ⟨c, rfl⟩ := (hL.2 w).mp hw
      rw [pow_succ, pow_two, h.data.conj_mul, h.data.conj_mul, hlc, hlc, hlc]
      congr 1
      linear_combination c * hω3)
    ((hL.2 v).mpr ⟨1, (one_smul _ v).symm⟩) (by
      rw [hlv]
      intro he
      apply hω1
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hL.1
      have := congrFun he i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hi
      exact mul_right_cancel₀ hi (this.trans (one_mul _).symm))

  obtain ⟨l', hl'L, hF⟩ := h.exists_conj_ZS_of_isLine625 hFV hL
  obtain ⟨t₀, ht₀T, ht₀Z⟩ := h.exists_not_mem_centralizer_ZS_F4 h331 h615
  have ht₀N : t₀ ∈ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    h.toHyp611Nat.T_le_normalizer_ZS ht₀T
  set k := l'⁻¹ * t₀ * l' with hk
  have hkM : k ∈ ch6MV M V := (ch6MV M V).mul_mem ((ch6MV M V).mul_mem
    ((ch6MV M V).inv_mem (h.L_le_MV_ch625 hl'L)) (h.T_le_MV_ch625 ht₀T)) (h.L_le_MV_ch625 hl'L)
  have hkN : k ∈ Subgroup.normalizer (F : Set G) := by
    rw [hF]
    apply conjSubgroup_eq_iff_mem_normalizer.mp
    rw [conjSubgroup_conjSubgroup]
    have e : l' * k = t₀ * l' := by rw [hk]; group
    rw [e, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr ht₀N]
  obtain ⟨z, hz, hzt⟩ : ∃ z ∈ ch6ZS T L V, z * t₀ ≠ t₀ * z := by
    by_contra hcon
    push Not at hcon
    exact ht₀Z (Subgroup.mem_centralizer_iff.mpr hcon)
  have hne : conjAct F ⟨k, hkN⟩ ≠ 1 := by
    intro h1
    have hf : l'⁻¹ * z * l' ∈ F := by
      rw [hF, mem_conjSubgroup_iff]
      simpa [mul_assoc] using hz
    have := congrArg (fun φ : MulAut ↥F => ((φ ⟨l'⁻¹ * z * l', hf⟩ : ↥F) : G)) h1
    simp only [MulAut.one_apply] at this
    rw [conjAct_apply_coe] at this
    apply hzt
    have e : k * (l'⁻¹ * z * l') * k⁻¹ = l'⁻¹ * (t₀ * z * t₀⁻¹) * l' := by rw [hk]; group
    rw [e] at this
    have h2 : t₀ * z * t₀⁻¹ = z := by
      have := congrArg (fun g => l' * g * l'⁻¹) this
      simpa [mul_assoc] using this
    calc z * t₀ = t₀ * z * t₀⁻¹ * t₀ := by rw [h2]
      _ = t₀ * z := by group
  have h2dvd : 2 ∣ orderOf (conjAct F ⟨k, hkN⟩) := by
    obtain ⟨j, hj⟩ := h.sylow.1 ⟨t₀, ht₀T⟩
    have hj' : t₀ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hkj : (conjAct F ⟨k, hkN⟩) ^ 2 ^ j = 1 := by
      rw [← map_pow]
      have e : (⟨k, hkN⟩ : Subgroup.normalizer (F : Set G)) ^ 2 ^ j = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow, Subgroup.coe_one, hk]
        rw [show l'⁻¹ * t₀ * l' = (MulAut.conj l'⁻¹) t₀ by simp, ← map_pow,
          hj', map_one]
      rw [e, map_one]
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hkj)
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · rw [hi0, pow_zero, orderOf_eq_one_iff] at hio
      exact absurd hio hne
    · rw [hio]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hi0)
  exact eq_top_of_two_three_ch625 hF4 (fun u hu => h.sq_eq_one_of_mem_V (hFV hu))
    (h2dvd.trans (Subgroup.orderOf_mk _ (conjAct_mem_autOn_inf hkM hkN) ▸
      orderOf_dvd_natCard (⟨_, conjAct_mem_autOn_inf hkM hkN⟩ :
        ↥(autOn (ch6MV M V ⊓ Subgroup.normalizer (F : Set G)) F))))
    (dvd_card_of_orderOf_ch625 (conjAct_mem_autOn_inf (h.L_le_MV_ch625 hlL) hlN) hord₃)

theorem autOn_eq_top_ch625_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4) {F : Subgroup G}
    (hFV : F ≤ V) (hF4 : Nat.card F = 4) :
    autOn (ch6MV M V ⊓ Subgroup.normalizer (F : Set G)) F = ⊤ := by
  rcases h.four_cases_ch625 hFV hF4 with ⟨v, hL⟩ | ⟨x, y, hP⟩
  · exact h.autOn_eq_top_of_isLine625_F4 h331 h615 hFV hF4 hL
  · exact h.autOn_eq_top_of_isPlane625 hFV hF4 hP

theorem card_type3_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4)
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 2) :
    Nat.card {F : Subgroup G // F ≤ V ∧ Nat.card F = 4 ∧ ¬ IsCentralType L V F 1 ∧
      ¬ IsFieldType M L V F 1} = 20 := by
  obtain ⟨F₀, hF₀V, hF₀4, hF₀c, hF₀f⟩ := h.exists_type3_F4 h331 h615 hidx
  set N := ch6MV M V ⊓ Subgroup.normalizer (F₀ : Set G) with hN
  have hK4 := isKleinFour_of_card_four_ch62 hF₀4 (fun u hu => h.sq_eq_one_of_mem_V (hF₀V hu))

  have hN6 : (N ⊓ Subgroup.centralizer (F₀ : Set G)).relIndex N = 6 := by
    rw [← card_autOn_eq_relIndex (inf_le_right : N ≤ Subgroup.normalizer (F₀ : Set G)),
      h.autOn_eq_top_ch625_F4 h331 h615 hF₀V hF₀4, Subgroup.card_top,
      CFSG.GorensteinWalter.kleinFourAut_card]

  obtain ⟨x, y, hP⟩ := h.isPlane625_of_not_central hF₀V hF₀4 hF₀c
  have hNC : N ⊓ Subgroup.centralizer (F₀ : Set G) =
      ch6MV M V ⊓ Subgroup.centralizer (V : Set G) := by
    apply le_antisymm
    · rintro m ⟨⟨hmM, -⟩, hmC⟩
      refine ⟨hmM, ?_⟩
      by_cases hlin : h.IsLin625 ⟨m, hmM.2⟩
      · apply h.data.mem_centralizer_of_conj_eq ⟨m, hmM.2⟩
        intro w
        have hx := h.conj_fix_of_mem_centralizer hmM.2 hmC ((hP.2 x).mpr (Or.inr (Or.inl rfl)))
        have hy := h.conj_fix_of_mem_centralizer hmM.2 hmC
          ((hP.2 y).mpr (Or.inr (Or.inr (Or.inl rfl))))
        rw [eq_add_of_det2_ne_zero hP.1 w, map_add, hlin, hlin, hx, hy]
      · exact absurd ((h.isFieldType_iff_ch625 hF₀V hF₀4).mpr ⟨m, hmM, hmC, hmM.2, hlin⟩) hF₀f
    · rintro m ⟨hmM, hmC⟩
      have hmC' : m ∈ Subgroup.centralizer (F₀ : Set G) := Subgroup.centralizer_le hF₀V hmC
      exact ⟨⟨hmM, Subgroup.centralizer_le_normalizer _ hmC'⟩, hmC'⟩

  have h120 : (ch6MV M V ⊓ Subgroup.centralizer (V : Set G)).relIndex (ch6MV M V) = 120 := by
    rw [← card_autOn_eq_relIndex (inf_le_right : ch6MV M V ≤ Subgroup.normalizer (V : Set G))]
    have h1 := Subgroup.relIndex_mul_card (H := autOn L V) (K := autOn (ch6MV M V) V)
    rw [inf_of_le_left (A4.autOn_mono h.L_le_MV_ch625), hidx,
      h.toHyp611Nat.card_autOn_L_ch6] at h1
    exact h1.symm.trans (by norm_num)

  have h20 : N.relIndex (ch6MV M V) = 20 := by
    have h1 := Subgroup.relIndex_mul_relIndex (ch6MV M V ⊓ Subgroup.centralizer (V : Set G)) N
      (ch6MV M V) (by rw [← hNC]; exact inf_le_left) inf_le_left
    rw [← hNC, hN6, hNC, h120] at h1
    omega

  have hfib : ∀ a b : ↥(ch6MV M V),
      (⟨conjSub (a : G) F₀, by
          rw [conjSub_eq_conjSubgroup_ch62]
          exact h.type3_conjSubgroup ((ch6MV M V).inv_mem a.2) hF₀V hF₀4 hF₀c hF₀f⟩ :
        {F : Subgroup G // F ≤ V ∧ Nat.card F = 4 ∧ ¬ IsCentralType L V F 1 ∧
          ¬ IsFieldType M L V F 1}) =
        ⟨conjSub (b : G) F₀, by
          rw [conjSub_eq_conjSubgroup_ch62]
          exact h.type3_conjSubgroup ((ch6MV M V).inv_mem b.2) hF₀V hF₀4 hF₀c hF₀f⟩ ↔
        a⁻¹ * b ∈ N.subgroupOf (ch6MV M V) := by
    intro a b
    rw [Subtype.mk.injEq, Subgroup.mem_subgroupOf]
    constructor
    · intro hab
      refine ⟨(a⁻¹ * b).2, mem_normalizer_of_conjSub_eq_ch625 ?_⟩
      have e : ((a⁻¹ * b : ↥(ch6MV M V)) : G) = (a : G)⁻¹ * b := by simp
      rw [e, conjSub_mul, ← hab, conjSub_conjSub_inv]
    · intro hab
      have e : (b : G) = a * ((a⁻¹ * b : ↥(ch6MV M V)) : G) := by simp
      rw [e, conjSub_mul, conjSub_eq_of_mem_normalizer' hab.2]
  rw [card_eq_index_of_fibers_ch625 (H := N.subgroupOf (ch6MV M V)) _ ?_ hfib]
  · exact h20
  · rintro ⟨F, hFV, hF4, hFc, hFf⟩
    obtain ⟨m, hmM, rfl⟩ := h.exists_conj_of_type3_F4 h331 h615 hF₀V hF₀4 hFV hF4 hF₀c hF₀f
      hFc hFf
    refine ⟨⟨m⁻¹, (ch6MV M V).inv_mem hmM⟩, ?_⟩
    apply Subtype.ext
    simp only
    rw [conjSub_eq_conjSubgroup_ch62, inv_inv]

end Hyp6Sec2

end CFSG.Quasithin.H13
