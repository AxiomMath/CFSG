module

public import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter
open scoped MatrixGroups

theorem two_pow_dvd_sq_sub_one (p m : ℕ) (hp : Odd p) (hp1 : 1 < p) (hm : m ≠ 0) :
    2 ^ (padicValNat 2 m + 3) ∣ (p ^ m) ^ 2 - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : (p ^ m) ^ 2 = p ^ (2 * m) := by rw [← pow_mul, mul_comm]
  have hx : ¬ 2 ∣ p := by
    rintro ⟨c, hc⟩
    rcases hp with ⟨k, hk⟩
    omega
  have hxy : 2 ∣ p - 1 := by
    rcases hp with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hlte := padicValNat.pow_two_sub_pow (x := p) (y := 1) hp1 hxy hx (n := 2 * m)
    (by omega) (even_two_mul m)
  rw [one_pow] at hlte
  have h2m : padicValNat 2 (2 * m) = padicValNat 2 m + 1 := by
    rw [padicValNat.mul (by norm_num) hm, padicValNat.self (by norm_num)]
    ring
  have hp1' : p - 1 ≠ 0 := by omega
  have hp2' : p + 1 ≠ 0 := by omega
  have hsum : 3 ≤ padicValNat 2 (p + 1) + padicValNat 2 (p - 1) := by
    have h4 : 4 ∣ p + 1 ∨ 4 ∣ p - 1 := by
      rcases hp with ⟨k, hk⟩
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · right; exact ⟨j, by omega⟩
      · left; exact ⟨j + 1, by omega⟩
    have e1 : 1 ≤ padicValNat 2 (p + 1) := by
      have : 2 ^ 1 ∣ p + 1 := by
        rcases hp with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩
      exact (padicValNat_dvd_iff_le (p := 2) (a := p + 1) (n := 1) hp2').mp this
    have e2 : 1 ≤ padicValNat 2 (p - 1) :=
      (padicValNat_dvd_iff_le (p := 2) (a := p - 1) (n := 1) hp1').mp (by simpa using hxy)
    rcases h4 with h | h
    · have : 2 ≤ padicValNat 2 (p + 1) :=
        (padicValNat_dvd_iff_le (p := 2) (a := p + 1) (n := 2) hp2').mp (by
          have : (4 : ℕ) = 2 ^ 2 := by norm_num
          rw [← this]; exact h)
      omega
    · have : 2 ≤ padicValNat 2 (p - 1) :=
        (padicValNat_dvd_iff_le (p := 2) (a := p - 1) (n := 2) hp1').mp (by
          have : (4 : ℕ) = 2 ^ 2 := by norm_num
          rw [← this]; exact h)
      omega
  have hge : padicValNat 2 m + 3 ≤ padicValNat 2 (p ^ (2 * m) - 1) := by omega
  have hne : p ^ (2 * m) - 1 ≠ 0 := by
    have : 1 < p ^ (2 * m) := Nat.one_lt_pow (by omega) hp1
    omega
  rw [hpow]
  exact (padicValNat_dvd_iff_le hne).mpr hge

section FG

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

include e in
omit [Finite K] in
theorem two_pow_dvd_card (h : L2Field F) (p m : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card F = p ^ m) : 2 ^ (padicValNat 2 m + 2) ∣ Nat.card K := by
  have hm : m ≠ 0 := by
    rintro rfl
    have := h.2
    rw [hcard] at this
    simp at this
  have h1 := two_pow_dvd_sq_sub_one p m hodd hp.one_lt hm
  rw [← hcard] at h1
  rw [card_eq_of_L2Field e h]
  have h2 : 2 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    have h3 : 2 ∣ Nat.card F ^ 2 - 1 :=
      (dvd_pow_self 2 (by omega : padicValNat 2 m + 3 ≠ 0)).trans h1
    exact dvd_mul_of_dvd_right h3 _
  have h4 : 2 ^ (padicValNat 2 m + 3) ∣ Nat.card F * (Nat.card F ^ 2 - 1) :=
    dvd_mul_of_dvd_right h1 _
  have h5 : Nat.card F * (Nat.card F ^ 2 - 1) = 2 * (Nat.card F * (Nat.card F ^ 2 - 1) / 2) :=
    (Nat.mul_div_cancel' h2).symm
  rw [h5, pow_succ, mul_comm (2 ^ (padicValNat 2 m + 2)) 2] at h4
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4

theorem card_P_eq (N : L2Notation e) :
    Nat.card N.P = 2 ^ (Nat.card K).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP'⟩ := Glauberman.sylow_inf_normal (G := MulAut K) (p := 2) N.T (N := innAut K)
  have h1 : Nat.card N.P = Nat.card ((N.T : Subgroup (MulAut K)) ⊓ innAut K |>.subgroupOf (innAut K)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : (N.T : Subgroup (MulAut K)) ⊓ innAut K ≤ innAut K)).toEquiv.symm
  have h2 := Sylow.card_eq_multiplicity P'
  rw [hP'] at h2
  rw [h1, h2, card_innAut e]

theorem ivk_1_2f : IVK_1_2f := by
  intro F _ _ hF K _ _ e N
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    simp only [L2Notation.Pt, L2Notation.R, Subgroup.mem_inf] at hx
    have h1 : x ∈ innDiagSub e ⊓ fieldAutSub e := ⟨hx.1.2, hx.2.2⟩
    rw [innDiagSub_inf_fieldAutSub e] at h1
    exact h1
  · intro n hn
    obtain ⟨p, m, hp, hodd, hm, hcard⟩ := isOddPrimePower_of_L2Field hF
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hnfac : n = (Nat.card K).factorization 2 := by
      have h := card_P_eq e N
      rw [hn] at h
      exact Nat.pow_right_injective (le_refl 2) h
    have hdvd := two_pow_dvd_card e hF p m hp hodd hcard
    have ha : padicValNat 2 m + 2 ≤ n := by
      rw [hnfac]
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hKpos.ne').mp hdvd
    have hR2 : IsPGroup 2 ↥N.R := N.T.isPGroup'.to_le (inf_le_left : N.R ≤ (N.T : Subgroup (MulAut K)))
    obtain ⟨j, hj⟩ := hR2.exists_card_eq
    have hRdvd : Nat.card N.R ∣ Nat.card (fieldAutSub e) :=
      Subgroup.card_dvd_of_le (inf_le_right : N.R ≤ fieldAutSub e)
    have hFcard : Nat.card (fieldAutSub e) = m := (ivk_1_2e F hF K e).2.2 p m hp hcard
    rw [hj, hFcard] at hRdvd
    have hjle : j ≤ padicValNat 2 m :=
      (padicValNat_dvd_iff_le (p := 2) (a := m) (n := j) (by omega)).mp hRdvd
    rw [hj]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

include e in
omit [Finite K] in
theorem orderOf_conj_eq (a : K) : orderOf (MulAut.conj a) = orderOf a :=
  orderOf_injective (MulAut.conj : K →* MulAut K) (conj_injective_of_L2 e) a

omit [Finite F] [Finite K] in
theorem isInvolution_toPSL {c : K} (hc : orderOf c = 2) :
    BenderSuzuki.PFAppendixIII.IsInvolution (toPSL e c) := by
  constructor
  · intro h1
    have : c = 1 := (toPSL e).injective (by simpa using h1)
    rw [this, orderOf_one] at hc
    omega
  · have hc2 : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    rw [← map_pow, hc2, map_one]

include e in
omit [Finite K] in
theorem inn_involutions_conj (h : L2Field F) {x y : MulAut K} (hx : x ∈ innAut K)
    (hy : y ∈ innAut K) (hxo : orderOf x = 2) (hyo : orderOf y = 2) :
    ConjUnder (innAut K) x y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hao : orderOf a = 2 := by rw [← orderOf_conj_eq e a]; exact hxo
  have hbo : orderOf b = 2 := by rw [← orderOf_conj_eq e b]; exact hyo
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F
    (isOddPrimePower_of_L2Field h) (toPSL e a) (toPSL e b) (isInvolution_toPSL e hao)
    (isInvolution_toPSL e hbo)
  refine ⟨MulAut.conj ((toPSL e).symm g), ⟨(toPSL e).symm g, rfl⟩, ?_⟩
  have h1 : (toPSL e).symm g * a * ((toPSL e).symm g)⁻¹ = b := by
    apply (toPSL e).injective
    simpa [map_mul, map_inv] using hg
  rw [← map_inv, ← map_mul, ← map_mul, h1]

omit [Finite K] in
theorem innDiagHom_toPGL (k : K) :
    innDiagHom e (Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e k)) = MulAut.conj k := by
  ext x
  apply (toPSL e).injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_toPSL_innDiagHom]
  simp [MulAut.conj_apply]

omit [Finite K] in
theorem innDiagHom_mem_innAut_iff (A : PGL2 F) :
    innDiagHom e A ∈ innAut K ↔
      A ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨toPSL e k, ?_⟩
    apply innDiagHom_injective e
    rw [innDiagHom_toPGL, hk]
  · rintro ⟨s, rfl⟩
    refine ⟨(toPSL e).symm s, ?_⟩
    have := innDiagHom_toPGL e ((toPSL e).symm s)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm

include e in
theorem outer_involutions_conj (h : L2Field F) {x y : MulAut K} (hx : x ∈ innDiagSub e)
    (hxn : x ∉ innAut K) (hy : y ∈ innDiagSub e) (hyn : y ∉ innAut K) (hxo : orderOf x = 2)
    (hyo : orderOf y = 2) : ConjUnder (innAut K) x y := by
  have hodd := isOddPrimePower_of_L2Field h
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  have hAo : orderOf A = 2 :=
    (orderOf_injective (innDiagHom e) (innDiagHom_injective e) A).symm.trans hxo
  have hBo : orderOf B = 2 :=
    (orderOf_injective (innDiagHom e) (innDiagHom_injective e) B).symm.trans hyo
  have hinv : ∀ C : PGL2 F, orderOf C = 2 → BenderSuzuki.PFAppendixIII.IsInvolution C := by
    intro C hC
    constructor
    · intro h1
      have := orderOf_eq_one_iff.mpr h1
      omega
    · have := pow_orderOf_eq_one C
      rwa [hC] at this
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three F hodd h.2
  have hAc : A ∉ commutator (PGL2 F) := by
    rw [hcomm]; exact fun hh => hxn ((innDiagHom_mem_innAut_iff e A).mpr hh)
  have hBc : B ∉ commutator (PGL2 F) := by
    rw [hcomm]; exact fun hh => hyn ((innDiagHom_mem_innAut_iff e B).mpr hh)
  obtain ⟨C, hC⟩ := isConj_iff.mp
    (pgl2_outer_involutions_conjugate F hodd h.2 (hinv A hAo) (hinv B hBo) hAc hBc)
  set c : MulAut K := innDiagHom e C with hcdef
  set x : MulAut K := innDiagHom e A with hxdef
  have hcx : c * x * c⁻¹ = innDiagHom e B := by
    rw [hcdef, hxdef, ← map_inv, ← map_mul, ← map_mul, hC]
  have hcΔ : c ∈ innDiagSub e := ⟨C, rfl⟩
  by_cases hc : c ∈ innAut K
  · exact ⟨c, hc, hcx⟩
  · refine ⟨c * x, ?_, ?_⟩
    · have hidx := innAut_relIndex_two e h
      unfold Subgroup.relIndex at hidx
      exact (Subgroup.mul_mem_iff_of_index_two hidx
        (a := (⟨c, hcΔ⟩ : ↥(innDiagSub e))) (b := ⟨x, ⟨A, rfl⟩⟩)).mpr (iff_of_false hc hxn)
    · have hx2 : x * x = 1 := by
        have : x ^ 2 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
        rwa [pow_two] at this
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
      calc c * x * x * (c * x)⁻¹ = c * (x * x) * x⁻¹ * c⁻¹ := by group
        _ = c * x * c⁻¹ := by rw [hx2, hxinv]; group
        _ = innDiagHom e B := hcx

theorem ivk_1_2g : IVK_1_2g := by
  intro F _ _ hF K _ _ e N
  constructor
  · intro x hx y hy hxo hyo
    exact inn_involutions_conj e hF hx.2 hy.2 hxo hyo
  · intro x y hx hxn hy hyn hxo hyo
    have hxn' : x ∉ innAut K := fun hh => hxn ⟨hx.1, hh⟩
    have hyn' : y ∉ innAut K := fun hh => hyn ⟨hy.1, hh⟩
    exact outer_involutions_conj e hF hx.2 hxn' hy.2 hyn' hxo hyo

end FG

end CFSG.GH74.GLS.IVK
