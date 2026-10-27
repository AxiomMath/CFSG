module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Frame
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Quat
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3H
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Mat
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3 Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2 CFSG.ClassicalInvolution.Q3.TA3.Q5U3
open CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement

@[expose] def ScalarsInCore {A : Type} [Group A] {T : Subgroup A} {z : A} {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (F : U3Frame T z p f h) (R : Subgroup A) : Prop :=
  ∀ r : A, r ∈ R → r ∈ T →
    ∃ Ar : ↥(GU2Stated (p ^ f) K), F.π Ar = r ∧
      ∃ c : Kˣ, (Ar : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) c

theorem norm_eq_one_of_scalar_mem {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin 2) c ∈ GU2Stated (p ^ f) K) : h.norm (c : K) = 1 := by
  rw [Lemma41aU3.mem_GU2Stated_iff h] at hc
  have e := congrFun (congrFun hc 0) 0
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two] at e
  rw [UnitaryFieldData.norm, mul_comm]
  exact e

section Gen

variable {A : Type} [Group A] [Finite A] {T : Subgroup A} [T.Normal] {R : Subgroup A} {S : Sylow 2 R}
  {z : A} {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} (F : U3Frame T z p f h)

theorem not_mem_of_inv (hsc : ScalarsInCore F R) {a b : A} {Aa : ↥(GU2Stated (p ^ f) K)} {c : Kˣ}
    (hAa : (Aa : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) c) (ha : F.π Aa = a) (hbR : b ∈ R)
    (hbT : b ∈ T) (hba : b * a * b⁻¹ = a⁻¹) (hasq : a * a ≠ 1) : False := by
  obtain ⟨Ab, hAb, cb, hcb⟩ := hsc b hbR hbT
  have hcomm : Ab * Aa = Aa * Ab := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcb, hAa]
    exact scalar_mul_comm cb _)
  have hab : b * a = a * b := by
    rw [← hAb, ← ha, ← map_mul, ← map_mul, hcomm]
  have h1 : a = a⁻¹ := by
    rw [← hba, hab, mul_inv_cancel_right]
  apply hasq
  calc a * a = a * a⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel a

theorem b_not_mem (hsc : ScalarsInCore F R) {a b : A} {Aa : ↥(GU2Stated (p ^ f) K)} {c : Kˣ}
    (hAa : (Aa : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) c) (ha : F.π Aa = a) (hbR : b ∈ R)
    (hba : b * a * b⁻¹ = a⁻¹) (hasq : a * a ≠ 1) : b ∉ T :=
  fun hbT => not_mem_of_inv F hsc hAa ha hbR hbT hba hasq

theorem b_form (hC : Subgroup.centralizer (T : Set A) = ⊥) (hq : 2 < p ^ f) (h5 : 5 ≤ p ^ f)
    (hRJ : R ≤ Subgroup.centralizer ((F.J : Subgroup A) : Set A))
    {b : A} (hbS : b ∈ sylowSet S) (hbz : b * b = z) (hbT : b ∉ T) :
    ∃ (M : unitaryIsom3 h) (m m' : K),
      MulAut.congr F.E (MulAut.conjNormal b) = psuConj h M * psuField h (barE h) ∧
      ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, m, 0; -m, 0, 0; 0, 0, m'] := by
  have hbR : b ∈ R := mem_sylowSet_le S hbS
  have hzT : z ∈ T := by
    rw [← F.hπ1]
    exact F.π_mem _
  set s : MulAut (unitaryPSU h 3) := MulAut.congr F.E (MulAut.conjNormal b) with hs
  have hEz : F.E ⟨z, hzT⟩ = ((Lemma41aU3.blkU h ⟨-1, neg_one_mem_GU2 h⟩ : unitarySU p f K 3) :
      unitaryPSU h 3) := by
    have e1 : (⟨z, hzT⟩ : ↥T) = ⟨F.π ⟨-1, neg_one_mem_GU2 h⟩, F.π_mem _⟩ := Subtype.ext F.hπ1.symm
    rw [e1]
    exact F.hπE _ _
  have hs2 : s * s = MulAut.conj ((Lemma41aU3.blkU h ⟨-1, neg_one_mem_GU2 h⟩ : unitarySU p f K 3) :
      unitaryPSU h 3) := by
    rw [hs, ← map_mul, ← map_mul, hbz, congr_conjNormal_of_mem F.E hzT, hEz]
  have hni : ∀ g : unitarySU p f K 3, s ≠ MulAut.conj (g : unitaryPSU h 3) := by
    intro g hg
    set n := F.E.symm (g : unitaryPSU h 3) with hn
    have h1 : MulAut.conjNormal (H := T) b = MulAut.conjNormal (n : A) := by
      apply (MulAut.congr F.E).injective
      rw [← hs, hg, congr_conjNormal_of_mem F.E n.2]
      congr 1
      rw [hn, Subtype.coe_eta, MulEquiv.apply_symm_apply]
    have h2 : (n : A)⁻¹ * b ∈ Subgroup.centralizer (T : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have := congrArg (fun φ : MulAut T => ((φ ⟨m, hm⟩ : T) : A)) h1
      simp only [MulAut.conjNormal_apply] at this
      calc m * ((n : A)⁻¹ * b) = (n : A)⁻¹ * ((n : A) * m * (n : A)⁻¹) * b := by group
        _ = (n : A)⁻¹ * b * m := by rw [← this]; group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact hbT (h2 ▸ n.2)
  obtain ⟨x, hxu, hx2, hx3⟩ := exists_norm_one_gen h h5
  have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hxu
  have hfixJ : ∀ A : ↥(GU2Stated (p ^ f) K), GeneralLinearGroup.det (A : GL (Fin 2) K) = 1 →
      s ((Lemma41aU3.blkU h A : unitarySU p f K 3) : unitaryPSU h 3) =
        ((Lemma41aU3.blkU h A : unitarySU p f K 3) : unitaryPSU h 3) := by
    intro A hA
    have hbA : b * F.π A = F.π A * b :=
      (Subgroup.mem_centralizer_iff.mp (hRJ hbR) (F.π A)
        (Subgroup.mem_map.mpr ⟨A, mem_slPart.mpr hA, rfl⟩)).symm
    rw [← F.hπE A (F.π_mem A), hs]
    exact congr_conjNormal_fix F.E (F.π_mem A) hbA
  have hfx := hfixJ ⟨_, dx_mem h hxu hx0⟩ (det_mk2 _ _ _ _ (dx_det hx0))
  have hfw := hfixJ ⟨_, w_mem h⟩ (det_mk2 _ _ _ _ w_det)
  obtain ⟨M, m, m', hsM, hM⟩ :=
    sigma_form h hq hs2 hni hxu hx2 hx3 (coe_blkU_dx h hxu hx0) (coe_blkU_w h) hfx hfw
  exact ⟨M, m, m', hsM, hM⟩

theorem entry_U3 {r : ℕ} (hr : 4 ≤ r) (hC : Subgroup.centralizer (T : Set A) = ⊥)
    (hcomm : SocleComm2 ↥T) (hsc : ScalarsInCore F R) (hd : TightDatum R S z)
    (hc : TightClsR r A R S z) :
    ∃ (Al : ↥(GU2Stated (p ^ f) K)) (l : Kˣ) (b : A),
      (Al : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) l ∧ F.π Al ∈ sylowSet S ∧
      h.norm (l : K) = 1 ∧ l ^ 2 ^ (r - 2) = 1 ∧ l ^ 2 ≠ 1 ∧ l ^ 3 ≠ 1 ∧
      b ∈ sylowSet S ∧ b ∉ T ∧ b * b = z := by
  obtain ⟨x, b, hxS, hbS, hxord, hbx, hbb⟩ := exists_quat_full_of_datum (show 3 ≤ r by omega) hc
  have hxR : x ∈ R := mem_sylowSet_le S hxS
  have hbR : b ∈ R := mem_sylowSet_le S hbS
  have hP : IsPGroup 2 (sylowSet S) := S.isPGroup'.map _
  have hx2T : x ^ 2 ∈ T := by
    have hle := hcomm A T ‹T.Normal› ⟨MulEquiv.refl _⟩ hC (sylowSet S) hP
    have hcm : ⁅x, b⁆ ∈ T := hle (Subgroup.commutator_mem_commutator hxS hbS)
    have hbx' : b * x⁻¹ * b⁻¹ = x := by
      calc b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
        _ = x := by rw [hbx, inv_inv]
    have hcm' : ⁅x, b⁆ = x ^ 2 := by
      rw [commutatorElement_def, show x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) by group, hbx', sq]
    rw [← hcm']
    exact hcm
  have hord_dvd : ∀ n : ℕ, x ^ n = 1 → 2 ^ (r - 1) ∣ n := fun n hn => by
    rw [← hxord]
    exact orderOf_dvd_of_pow_eq_one hn
  have h8 : 8 ∣ 2 ^ (r - 1) := by
    have e8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [e8]
    exact pow_dvd_pow 2 (by omega)
  have hpow1 : x ^ (2 ^ (r - 2)) ≠ 1 := fun h1 => by
    have hd1 := hord_dvd _ h1
    have e1 : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e1] at hd1
    have hle := Nat.le_of_dvd (by positivity) hd1
    have hpos : 0 < 2 ^ (r - 2) := by positivity
    omega
  have hsq1 : (x ^ (2 ^ (r - 2))) ^ 2 = 1 := by
    rw [← pow_mul]
    have e2 : 2 ^ (r - 2) * 2 = 2 ^ (r - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [e2, ← hxord]
    exact pow_orderOf_eq_one x
  have hzx : x ^ (2 ^ (r - 2)) = z :=
    hd.eq_of_orderOf_eq_two (R.pow_mem hxR _) (orderOf_eq_prime hsq1 hpow1)
  have hbb' : b * b = z := hbb.trans hzx
  obtain ⟨Al₀, hπAl₀, c', hc'⟩ := hsc (x ^ 2) (R.pow_mem hxR 2) hx2T
  have hnc : h.norm (c' : K) = 1 := by
    apply norm_eq_one_of_scalar_mem (h := h)
    rw [← hc']
    exact Al₀.2
  have hnl : h.norm ((c' ^ 3 : Kˣ) : K) = 1 := by
    have e : h.norm ((c' ^ 3 : Kˣ) : K) = (h.norm (c' : K)) ^ 3 := by
      simp only [UnitaryFieldData.norm, Units.val_pow_eq_pow_val, map_pow]
      ring
    rw [e, hnc, one_pow]
  set Al : ↥(GU2Stated (p ^ f) K) :=
    ⟨GeneralLinearGroup.scalar (Fin 2) (c' ^ 3), scalar_mem_GU2 h hnl⟩ with hAl
  have hAl_eq : Al = Al₀ ^ 3 := Subtype.ext (by
    rw [Subgroup.coe_pow, hc']
    exact map_pow _ _ _)
  have hπAl : F.π Al = (x ^ 2) ^ 3 := by rw [hAl_eq, map_pow, hπAl₀]
  have hπAlS : F.π Al ∈ sylowSet S := by
    rw [hπAl]
    exact pow_mem (pow_mem hxS 2) 3
  have hlpow : (c' ^ 3) ^ 2 ^ (r - 2) = 1 := by
    have hker : F.π (Al₀ ^ 2 ^ (r - 2)) = 1 := by
      rw [map_pow, hπAl₀, ← pow_mul]
      have e3 : 2 * 2 ^ (r - 2) = 2 ^ (r - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [e3, ← hxord]
      exact pow_orderOf_eq_one x
    obtain ⟨ω, hω3, hω⟩ := F.hk _ hker
    rw [Subgroup.coe_pow, hc', ← map_pow] at hω
    have hω' : c' ^ 2 ^ (r - 2) = ω := scalar_injective hω
    rw [← pow_mul, show 3 * 2 ^ (r - 2) = 2 ^ (r - 2) * 3 from mul_comm _ _, pow_mul, hω', hω3]
  have hl2 : (c' ^ 3) ^ 2 ≠ 1 := by
    intro h1
    have hA2 : Al ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      show GeneralLinearGroup.scalar (Fin 2) (c' ^ 3) ^ 2 = 1
      rw [← map_pow, h1, map_one])
    have h3 : (F.π Al) ^ 2 = 1 := by rw [← map_pow, hA2, map_one]
    have h4 : x ^ 12 = 1 := by
      calc x ^ 12 = ((x ^ 2) ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul]
        _ = 1 := by rw [← hπAl]; exact h3
    have := (h8.trans (hord_dvd 12 h4))
    norm_num at this
  have hl3 : (c' ^ 3) ^ 3 ≠ 1 := by
    intro h1
    have hA3 : Al ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      show GeneralLinearGroup.scalar (Fin 2) (c' ^ 3) ^ 3 = 1
      rw [← map_pow, h1, map_one])
    have h3 : (F.π Al) ^ 3 = 1 := by rw [← map_pow, hA3, map_one]
    have h4 : x ^ 18 = 1 := by
      calc x ^ 18 = ((x ^ 2) ^ 3) ^ 3 := by rw [← pow_mul, ← pow_mul]
        _ = 1 := by rw [← hπAl]; exact h3
    have := (h8.trans (hord_dvd 18 h4))
    norm_num at this
  have hba : b * x ^ 2 * b⁻¹ = (x ^ 2)⁻¹ := by
    rw [← conj_pow, hbx, inv_pow]
  have hasq : x ^ 2 * x ^ 2 ≠ 1 := by
    intro h1
    have h4 : x ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
      exact h1
    have := (h8.trans (hord_dvd 4 h4))
    norm_num at this
  have hbT : b ∉ T := b_not_mem F hsc hc' hπAl₀ hbR hba hasq
  exact ⟨Al, c' ^ 3, b, rfl, hπAlS, hnl, hlpow, hl2, hl3, hbS, hbT, hbb'⟩

end Gen

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3
