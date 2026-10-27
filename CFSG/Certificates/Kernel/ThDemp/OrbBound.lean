
module

public import CFSG.Certificates.Kernel.ThDemp.OrbBoundBase

public import CFSG.Certificates.Kernel.ThDemp.OrbElt
public import CFSG.Certificates.Kernel.ThDemp.OrbMain
public import CFSG.Certificates.Kernel.ThDemp.OrbPts
public import CFSG.Certificates.Kernel.ThDemp.Sound

public section

namespace CFSG.Certificates.ThDemp.Bound

open MulAction CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp CFSG.KC.Loop
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes CFSG.Certificates.ThDemp.Batches
  CFSG.Certificates.ThDemp.Key CFSG.Certificates.ThDemp.Rows CFSG.Certificates.ThDemp.Stab
  CFSG.Certificates.ThDemp.USp CFSG.Certificates.ThDemp.Cent CFSG.Certificates.ThDemp.Elt
  CFSG.Certificates.ThDemp.Pts

set_option exponentiation.threshold 2000

variable {J : Subgroup (GL (Fin 248) (ZMod 2))} {D : DempData} {O : OrbData}

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

structure NormFacts (D : DempData) (O : OrbData) : Prop where
  comm : D.mul (D.mul (chainEl D O.dm) (wordM D (lgetL O.words 7))) (chainEl D O.x31) =
    D.mul (pow5 D (chainEl D O.x31) 5) (D.mul (chainEl D O.dm) (wordM D (lgetL O.words 7)))
  k1 : keyL D.rm (U0 D) ≠ keyL D.rm (mulB (cR 5) D.rm (U0 D)
    (D.mul (chainEl D O.dm) (wordM D (lgetL O.words 7))))
  k2 : keyL D.rm (mulB (cR 5) D.rm (U0 D) (D.mul (chainEl D O.dm) (wordM D (lgetL O.words 7)))) ≠
    keyL D.rm (mulB (cR 5) D.rm (mulB (cR 5) D.rm (U0 D)
      (D.mul (chainEl D O.dm) (wordM D (lgetL O.words 7))))
      (D.mul (chainEl D O.dm) (wordM D (lgetL O.words 7))))

theorem normChk_facts (h : normChk D O = true) : NormFacts D O := by
  unfold normChk at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h⟩ := Unfold.andB_split h
  obtain ⟨h2, h⟩ := Unfold.andB_split h
  obtain ⟨-, h3⟩ := Unfold.andB_split h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun e => ?_, fun e => ?_⟩
  · have := Unfold.notB_true h2
    rw [e, Nat.beq_refl] at this
    exact absurd this (by decide)
  · have := Unfold.notB_true h3
    rw [e, Nat.beq_refl] at this
    exact absurd this (by decide)

theorem smul_eq_of_combChk (hF : DempFacts D) {H : Subgroup J} (x : H) {P X G : ℕ}
    (hx : 𝕄 (x : J) = pkMat X) (hP : LIL (rowsOf (2 ^ 248 - 1) P))
    (hc : combChk D.rm (mulB (cR 5) D.rm P X) P G = true) : x • sp P = sp P := by
  rw [Cent.Ctx.hrm hF, cR_eq] at hc
  have hl := lil_mulB (P := P) (N := X) (M' := 𝕄 (x : J)⁻¹) (by rw [← hx]; exact mat_mul_inv _) hP
  have e := sp_eq_of_combChk hc hl hP
  rw [sp_mulB, ← hx] at e
  change ((x : J) : GL (Fin 248) (ZMod 2)) • sp P = sp P
  exact (Act.smul_eq_self_iff _ _).mpr e

theorem exists_conjSet (C : Ctx D O J) (hF : DempFacts D) (h1 : Elt1Facts D O) (q : ℕ)
    (P : Pts) (x y : C.Dg) (hS : Nat.card (stabilizer C.Dg P) = 155)
    (hy : y ∈ stabilizer C.Dg P) (hyo : orderOf y = 31) (hxo : orderOf x = 31)
    (hkill : KillU D (Qm q (𝕄 (x : J))))
    (hcount : {k | 0 < k ∧ k < 31 ∧ KillU D (Qm q ((𝕄 (y : J)) ^ k))}.ncard ≤ 5) :
    ∃ T : Finset C.Dg, T.card ≤ 5 ∧ ∀ t ∈ stabilizer C.Dg P, IsConj x t → t ∈ T := by
  classical
  set Kf := (Finset.range 31).filter (fun k => 0 < k ∧ KillU D (Qm q ((𝕄 (y : J)) ^ k)))
  have hK : Kf.card ≤ 5 := by
    have e : (↑Kf : Set ℕ) = {k | 0 < k ∧ k < 31 ∧ KillU D (Qm q ((𝕄 (y : J)) ^ k))} := by
      ext k
      simp only [Kf, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      tauto
    rw [← Set.ncard_coe_finset, e]
    exact hcount
  refine ⟨Kf.image (fun k => y ^ k), (Finset.card_image_le).trans hK, fun t ht hc => ?_⟩
  have hto : orderOf t = 31 := by rw [OrbMain.orderOf_of_isConj hc, hxo]
  have hfin : Finite (stabilizer C.Dg P) := inferInstance
  have hz : (⟨t, ht⟩ : stabilizer C.Dg P) ∈ Subgroup.zpowers (⟨y, hy⟩ : stabilizer C.Dg P) :=
    mem_zpowers_of_card hS (by rw [← Subgroup.orderOf_coe]; exact hyo)
      (by rw [← Subgroup.orderOf_coe]; exact hto)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have htz : t ∈ Subgroup.zpowers y := ⟨k, by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_zpow] at this⟩
  obtain ⟨n, hn, hnt⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp htz)
  rw [hyo, Finset.mem_range] at hn
  refine Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, ?_, ?_⟩, hnt⟩
  · rcases Nat.eq_zero_or_pos n with rfl | h0
    · rw [pow_zero] at hnt
      rw [← hnt, orderOf_one] at hto
      omega
    · exact h0
  ·
    obtain ⟨c, hcx⟩ := isConj_iff.mp hc
    have hct : (c : J) * (x : J) = (t : J) * (c : J) := by
      rw [← hcx]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    have hm := congrArg (fun z : J => 𝕄 z) hct
    simp only [FwdRel.mat_mul] at hm
    have hQ := Qm_semiconj q hm
    have htn : 𝕄 (t : J) = (𝕄 (y : J)) ^ n := by
      rw [← hnt, Subgroup.coe_pow, mat_pow]
    rw [← htn]
    intro w hw
    have hwc := Cent.Ctx.mem_U_mul C hF (Ctx.mapM_U0 C hF h1) c.2 hw
    have e1 : Matrix.vecMul (Matrix.vecMul w (𝕄 (c : J))) (Qm q (𝕄 (x : J))) = 0 := hkill _ hwc
    have e2 : Matrix.vecMul w (Qm q (𝕄 (t : J))) =
        Matrix.vecMul (Matrix.vecMul (Matrix.vecMul w (𝕄 (c : J))) (Qm q (𝕄 (x : J))))
          (𝕄 (c : J)⁻¹) := by
      rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hQ, Matrix.mul_assoc,
        mat_mul_inv, Matrix.mul_one]
    rw [e2, e1, Matrix.zero_vecMul]

namespace Ctx

variable (C : Ctx D O J) (hF : DempFacts D) (hJ : RegJ D J) (hc : OrbChecks D O)
include hF hJ hc

theorem suborbitHyp [Finite J] (hcard : Nat.card J ≤ 90745943887872000)
    (hD : Nat.card C.Dg = 319979520) :
    OrbMain.SuborbitHyp C.Dg (sp (U0 D)) (fun i : Fin 10 => sp (pt D O i)) := by
  have hrm := Cent.Ctx.hrm hF
  have h1 := eltChk1_facts hc.elt1
  have hU := Ctx.lil_U0 hF h1
  have hP := fun i => Pts.lil_pt hF hJ h1.words hU i
  have hsymm : ∀ {a b : Pts}, b ∈ orbit C.Dg a → a ∈ orbit C.Dg b := fun h => by
    rw [orbit_eq_iff.mpr h]
    exact mem_orbit_self _
  refine ⟨hcard, hD, Ctx.le_stabilizer C hF h1, fun i => Pts.sp_pt_mem_orbit hF hJ h1.words i,
    fun i => ?_, ?_, ?_, ?_⟩
  · rw [← hc.sb i]
    exact C.card_stabilizer_pt hrm (hc.batch i i.isLt) (hc.ky i i.isLt) (hc.low i i.isLt) (hP i)
  · exact Pts.Ctx.ncard_orbit_nine C hrm hc.orb (Pts.pt_lt hrm hc.w9) (hP 9)
  · intro hm
    exact C.not_mem_orbit_pt hrm hc.cross56 (hc.ky 6 (by omega)) (hP 5) (hP 6) (hsymm hm)
  · intro hm
    exact C.not_mem_orbit_pt hrm hc.cross78 (hc.ky 8 (by omega)) (hP 7) (hP 8) (hsymm hm)

theorem card_centralizer_bounds [Finite J] (hcard : Nat.card J ≤ 90745943887872000)
    (hD : Nat.card C.Dg = 319979520) :
    (∃ x : J, x ∈ C.Dg ∧ 𝕄 x = pkMat (chainEl D O.x5) ∧ orderOf x = 5 ∧
      Nat.card (Subgroup.centralizer ({x} : Set J)) ≤ 3000) ∧
    (∃ x : J, x ∈ C.Dg ∧ 𝕄 x = pkMat (chainEl D O.x31) ∧ orderOf x = 31 ∧
      Nat.card (Subgroup.centralizer ({x} : Set J)) ≤ 31) := by
  have hrm := Cent.Ctx.hrm hF
  have hk := hF.consts
  have h1 := eltChk1_facts hc.elt1
  have hcf := centChk_facts hc.cent
  obtain ⟨c5, c31, cyb, cdm⟩ := codesChk_facts hc.codes
  have hU := Ctx.lil_U0 hF h1
  have hP := fun i => Pts.lil_pt hF hJ h1.words hU i
  have hfix := Ctx.mapM_U0 C hF h1
  have hle := Ctx.le_stabilizer C hF h1
  have H := suborbitHyp C hF hJ hc hcard hD
  set x5 : C.Dg := ⟨Elt.Ctx.elt C O.x5, Elt.Ctx.elt_mem C _⟩ with hx5
  set x31 : C.Dg := ⟨Elt.Ctx.elt C O.x31, Elt.Ctx.elt_mem C _⟩ with hx31
  set yb : C.Dg := ⟨Elt.Ctx.elt C O.yb, Elt.Ctx.elt_mem C _⟩ with hyb
  have m5 : 𝕄 (x5 : J) = pkMat (chainEl D O.x5) := Elt.Ctx.mat_elt C hF c5
  have m31 : 𝕄 (x31 : J) = pkMat (chainEl D O.x31) := Elt.Ctx.mat_elt C hF c31
  have mb : 𝕄 (yb : J) = pkMat (chainEl D O.yb) := Elt.Ctx.mat_elt C hF cyb
  have q5 := ordChk_sound hF h1.o5 (by norm_num) (inLayout_chainEl hF _)
  have q31 := ordChk_sound hF h1.o31 (by norm_num) (inLayout_chainEl hF _)
  have qb := ordChk_sound hF h1.ob (by norm_num) (inLayout_chainEl hF _)
  have o5 : orderOf x5 = 5 := orderOf_of_mat x5 m5 (by norm_num) q5
  have o31 : orderOf x31 = 31 := orderOf_of_mat x31 m31 (by norm_num) q31
  have ob : orderOf yb = 31 := orderOf_of_mat yb mb (by norm_num) qb
  have ha : x31 ∈ stabilizer C.Dg (sp (pt D O 7)) := smul_eq_of_combChk hF x31 m31 (hP 7) h1.ga
  have hb : yb ∈ stabilizer C.Dg (sp (pt D O 8)) := smul_eq_of_combChk hF yb mb (hP 8) h1.gb
  refine ⟨⟨x5, x5.2, m5, (Subgroup.orderOf_coe x5).trans o5,
    H.card_centralizer_five x5 o5 (Cent.Ctx.card_centralizer_five_le C hF hfix hcf x5 m5)
      (Pts.Ctx.ncard_fix_nine C hrm hc.orb (Pts.pt_lt hrm hc.w9) (hP 9) x5 m5) x31 yb ha hb o31 ob⟩,
    ⟨x31, x31.2, m31, (Subgroup.orderOf_coe x31).trans o31, ?_⟩⟩
  obtain ⟨kill1, nk5, nk25, cnt31, cntb⟩ := qChk_sound hc.q hrm (Cent.Ctx.hbv hF) q31.1 qb.1
  have hS7 : Nat.card (stabilizer C.Dg (sp (pt D O 7))) = 155 := H.stab 7
  have hS8 : Nat.card (stabilizer C.Dg (sp (pt D O 8))) = 155 := H.stab 8
  rw [← m31] at kill1 nk5 nk25 cnt31
  rw [← mb] at cntb
  obtain ⟨T7, hT7, h7⟩ := exists_conjSet C hF h1 O.qm _ x31 x31 hS7 ha o31 o31 kill1 cnt31
  obtain ⟨T8, hT8, h8⟩ := exists_conjSet C hF h1 O.qm _ x31 yb hS8 hb ob o31 kill1 cntb
  have hr7 : ∀ r ∈ lgetL O.words 7, 0 < r ∧ r < D.nreg := fun r hr => by
    obtain ⟨w, hw', hrw⟩ := Pts.mem_lgetL _ _ _ hr
    exact Pts.wordsChk_sound h1.words w hw' r hrw
  obtain ⟨g7, hg7⟩ := Pts.exists_word hJ _ hr7
  obtain ⟨Mn, hMn⟩ : ∃ Mn, Mn = D.mul (chainEl D O.dm) (wordM D (lgetL O.words 7)) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : J, 𝕄 m = pkMat Mn := by
    refine ⟨Elt.Ctx.elt C O.dm * g7, ?_⟩
    rw [mat_mul', Elt.Ctx.mat_elt C hF cdm, hg7, hMn, DempData.mul, pkMat_mulB hk, wordM,
      Unfold.pkMat_wordM hF, pkMat_one hk, Matrix.one_mul]
  have nf := normChk_facts hc.norm
  have ncomm := nf.comm
  have nk2 := nf.k2
  rw [← hMn] at ncomm nk2
  obtain ⟨X, hX⟩ : ∃ X, X = 𝕄 (x31 : J) := ⟨_, rfl⟩
  rw [← hX] at kill1 nk5 nk25 cnt31
  have hmX : 𝕄 m * X = X ^ 5 * 𝕄 m := by
    have e := congrArg pkMat ncomm
    rw [DempData.mul, DempData.mul, pkMat_mulB hk, pkMat_mulB hk, pow5,
      pkMat_powB hk _ 5 5 (by norm_num)] at e
    rw [hm, hX, m31]
    exact e
  have hmx : m * (x31 : J) = (x31 : J) ^ 5 * m := by
    apply FwdRel.mat_injective
    change 𝕄 (m * (x31 : J)) = 𝕄 ((x31 : J) ^ 5 * m)
    rw [FwdRel.mat_mul, FwdRel.mat_mul, mat_pow, ← hX]
    exact hmX
  have hxm : (x31 : J) * m⁻¹ = m⁻¹ * (x31 : J) ^ 5 := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hmx, mul_inv_cancel_right]
  have hfixU : ∀ k : ℕ, ((x31 : J) ^ k) • sp (U0 D) = sp (U0 D) := fun k =>
    mem_stabilizer_iff.mp (hle (Subgroup.pow_mem _ x31.2 k))
  have hMinv : pkMat Mn * 𝕄 m⁻¹ = 1 := by rw [← hm]; exact mat_mul_inv m
  set Q1 := mulB (rep 1 256 5) (2 ^ 248 - 1) (U0 D) Mn
  set Q2 := mulB (rep 1 256 5) (2 ^ 248 - 1) Q1 Mn
  have l1 : LIL (rowsOf (2 ^ 248 - 1) Q1) := lil_mulB hMinv hU
  have l2 : LIL (rowsOf (2 ^ 248 - 1) Q2) := lil_mulB hMinv l1
  have e1 : sp Q1 = m⁻¹ • sp (U0 D) := by rw [inv_smul_eq, hm, sp_mulB]
  have e2 : sp Q2 = m⁻¹ • m⁻¹ • sp (U0 D) := by rw [← e1, inv_smul_eq, hm, sp_mulB]
  have h12 : sp Q1 ≠ sp Q2 := by
    intro e
    have k2 := nk2
    rw [hrm, cR_eq] at k2
    exact k2 (Act.keyL_eq l1 l2 e)
  have hω₁ : sp Q1 ∈ orbit J (sp (U0 D)) := mem_orbit_iff.mpr ⟨m⁻¹, e1.symm⟩
  have hω₂ : sp Q2 ∈ orbit J (sp (U0 D)) := mem_orbit_iff.mpr ⟨m⁻¹ * m⁻¹, by rw [mul_smul, e2]⟩
  have hx₁ : (x31 : J) • sp Q1 = sp Q1 := by
    rw [e1, smul_smul, hxm, mul_smul, hfixU]
  have hx₂ : (x31 : J) • sp Q2 = sp Q2 := by
    rw [e2, smul_smul, hxm, mul_smul, smul_smul ((x31 : J) ^ 5) m⁻¹, pow_mul_inv hxm 5, mul_smul,
      hfixU]
  have hc : ∀ c ∈ Subgroup.centralizer ({(x31 : J)} : Set J),
      c • sp (U0 D) ≠ sp Q1 ∧ c • sp (U0 D) ≠ sp Q2 := by
    intro c hcc
    have hci : 𝕄 c⁻¹ * X = X * 𝕄 c⁻¹ := by
      rw [hX]
      have := congrArg (fun z : J => 𝕄 z) (inv_comm_of_mem_cent hcc)
      simp only [FwdRel.mat_mul] at this
      exact this
    have hkc : ∀ w ∈ mapM (𝕄 c⁻¹) (sp (U0 D)), Matrix.vecMul w (Qm O.qm X) = 0 := by
      intro w hw
      obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hw
      change Matrix.vecMul (Matrix.vecMul w' (𝕄 c⁻¹)) _ = 0
      rw [Matrix.vecMul_vecMul, Qm_semiconj O.qm hci, ← Matrix.vecMul_vecMul, kill1 w' hw',
        Matrix.zero_vecMul]
    rw [smul_eq_mapM]
    constructor
    · intro e
      obtain ⟨w, hw, hne⟩ := not_kill_map m rfl hmX O.qm nk5
      rw [hm, ← sp_mulB] at hw
      rw [← e] at hw
      exact hne (hkc w hw)
    · intro e
      have hA : 𝕄 (m * m) * X = X ^ 25 * 𝕄 (m * m) := by
        rw [FwdRel.mat_mul, Matrix.mul_assoc, hmX, ← Matrix.mul_assoc, pow_semiconj hmX 5,
          Matrix.mul_assoc, ← pow_mul]
      obtain ⟨w, hw, hne⟩ := not_kill_map (m * m) rfl hA O.qm nk25
      rw [FwdRel.mat_mul, hm, mapM_mul, ← sp_mulB, ← sp_mulB] at hw
      rw [← e] at hw
      exact hne (hkc w hw)
  exact H.card_centralizer_thirtyone x31 o31 (Cent.Ctx.card_centralizer_thirtyone_le C hF hfix hcf
    x31 m31) T7 T8 hT7 hT8 h7 h8 (sp Q1) (sp Q2) h12 hω₁ hω₂ hx₁ hx₂ hc

end Ctx

end CFSG.Certificates.ThDemp.Bound

end
