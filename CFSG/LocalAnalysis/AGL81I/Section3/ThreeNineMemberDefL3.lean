module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3Cyclic
public import CFSG.CGT.T75N.L29Count
public import CFSG.GH74.KGroups.L3EpsAutDiag
public import CFSG.Quasithin.Background.A318PL3Inst
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.Blueprint
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.KGroups.L3Eps
open CFSG.CGT.T75N
open Matrix
open scoped MatrixGroups

private theorem three_dvd_card_psl_three {p : ℕ} [Fact p.Prime] :
    3 ∣ Nat.card (PSL(3, ZMod p)) := by
  classical
  let w : Equiv.Perm (Fin 3) := finRotate 3
  let P : Matrix (Fin 3) (Fin 3) (ZMod p) := permMatrix 3 (ZMod p) w
  have hdet : P.det = 1 := by
    rw [det_permMatrix, sign_finRotate]
    norm_num
  let g : SL(3, ZMod p) := ⟨P, hdet⟩
  have hw3 : w ^ 3 = 1 := by decide
  have hmul : ∀ n : ℕ, P ^ n = permMatrix 3 (ZMod p) (w ^ n) := by
    intro n
    induction n with
    | zero => simp [P, BinaryParabolic.permMatrix_one']
    | succ n ih =>
      rw [pow_succ, ih, BinaryParabolic.permMatrix_mul_permMatrix, ← pow_succ]
  have hP3 : P ^ 3 = 1 := by
    rw [hmul 3, hw3, BinaryParabolic.permMatrix_one']
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    show ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) ^ 3) = 1
    simpa [g] using hP3
  have hg_ne : QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p))) g ≠ 1 := by
    intro h
    have hmem : g ∈ Subgroup.center (SL(3, ZMod p)) := by
      rwa [← QuotientGroup.eq_one_iff]
    obtain ⟨r, -, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
    have h10' : Matrix.scalar (Fin 3) r (1 : Fin 3) (0 : Fin 3) =
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 0 :=
      congrFun (congrFun hscalar 1) 0
    have hP10 : (P : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 0 = 1 := by
      rw [show P = permMatrix 3 (ZMod p) w from rfl, permMatrix_apply]
      rw [if_pos (by decide : (1 : Fin 3) = w 0)]
    have : (0 : ZMod p) = 1 := by
      simpa [g, Matrix.scalar_apply, hP10] using h10'
    exact zero_ne_one this
  have hg3' : (QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p))) g) ^ 3 = 1 := by
    rw [← map_pow, hg3, map_one]
  have hord : orderOf (QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p))) g) = 3 :=
    orderOf_eq_prime hg3' hg_ne
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p))) g)
  rwa [hord] at hdvd

private theorem index_flagStabilizer_sl3_one {p : ℕ} [Fact p.Prime] :
    (flagStabilizer 3 (ZMod p) ({1} : Set ℕ)).index = p ^ 2 + p + 1 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1 : ((stabilizer (flagSpace 3 (ZMod p) 1)).index : ℚ) = (p : ℚ) ^ 2 + p + 1 := by
    rw [index_stabilizer_flag_gauss (K := ZMod p) (n := 3) (k := 1) (by norm_num),
      Nat.card_zmod, gaussianCoeff_one]
    have hp1 : ((p : ℚ) - 1) ≠ 0 := by
      have : (2 : ℚ) ≤ p := by exact_mod_cast hp
      linarith
    field_simp
    ring
  rw [flagStabilizer_singleton]
  exact_mod_cast h1

private theorem index_flagStabilizer_sl3_two {p : ℕ} [Fact p.Prime] :
    (flagStabilizer 3 (ZMod p) ({2} : Set ℕ)).index = p ^ 2 + p + 1 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1 : ((stabilizer (flagSpace 3 (ZMod p) 2)).index : ℚ) = (p : ℚ) ^ 2 + p + 1 := by
    rw [index_stabilizer_flag_gauss (K := ZMod p) (n := 3) (k := 2) (by norm_num),
      Nat.card_zmod, gaussianCoeff_symm (q := p) (n := 3) (k := 2) hp (by norm_num)]
    norm_num
    rw [gaussianCoeff_one]
    have hp1 : ((p : ℚ) - 1) ≠ 0 := by
      have : (2 : ℚ) ≤ p := by exact_mod_cast hp
      linarith
    field_simp
    ring
  rw [flagStabilizer_singleton]
  exact_mod_cast h1

private theorem reflection_conj_diagSL {p : ℕ} [Fact p.Prime] {a b c : ZMod p}
    (h : a * b * c = 1) (h' : b * a * c = 1) (hc : c = 1) :
    reflection 3 (ZMod p) 1 (by norm_num) (by norm_num) * diagSL a b c h *
        (reflection 3 (ZMod p) 1 (by norm_num) (by norm_num))⁻¹ =
      diagSL b a c h' := by
  classical
  set r : SL(3, ZMod p) := reflection 3 (ZMod p) 1 (by norm_num) (by norm_num)
  let A : GL (Fin 3) (ZMod p) := SpecialLinearGroup.toGL r
  set ρ : Equiv.Perm (Fin 3) := Equiv.swap (⟨0, by omega⟩ : Fin 3) ⟨1, by omega⟩ with hρdef
  have hρ : ∀ i j, reflectionMatrix 3 (ZMod p) 1 i j ≠ 0 → i = ρ j := by
    intro i j hij
    rw [reflectionMatrix_eq 1 (by norm_num) (by norm_num)] at hij
    rw [Matrix.mul_diagonal] at hij
    have hpij : permMatrix 3 (ZMod p) ρ i j ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hij
      exact hij rfl
    rw [permMatrix_apply] at hpij
    by_contra hne
    rw [if_neg hne] at hpij
    exact hpij rfl
  have hconj := conj_diag_of_perm (A := A) (ρ := ρ) hρ (φ := ![(a : ZMod p), b, c])
  have hxmat : ((SpecialLinearGroup.toGL (diagSL a b c h) : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) = Matrix.diagonal ![(a : ZMod p), b, c] := rfl
  have hxmat' : ((SpecialLinearGroup.toGL (diagSL b a c h') : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) = Matrix.diagonal ![b, a, c] := rfl
  have hmat : (A : Matrix (Fin 3) (Fin 3) (ZMod p)) *
      Matrix.diagonal ![(a : ZMod p), b, c] *
      ((A⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      Matrix.diagonal ![b, a, c] := by
    rw [hconj]
    congr 1
    ext i
    fin_cases i <;> simp [ρ, hρdef, hc, Equiv.swap_apply_def]
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv]
  change A * SpecialLinearGroup.toGL (diagSL a b c h) * A⁻¹ =
    SpecialLinearGroup.toGL (diagSL b a c h')
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul]
  rw [hxmat, hxmat']
  exact congrFun (congrFun hmat i) j

private theorem dvd_p_sub_one_of_upperTriangular_isBorelDLocal {p d : ℕ} [Fact p.Prime]
    (hd : d.Prime) (hdp : d ≠ p) (hdG : d ∣ Nat.card PSL(3, ZMod p))
    {Y : Subgroup PSL(3, ZMod p)} (hY : IsBorelDLocal p d Y)
    (hpre : Y.comap (QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))) =
      upperTriangular 3 (ZMod p)) : d ∣ p - 1 := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  let π : SL(3, ZMod p) →* PSL(3, ZMod p) :=
    QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let A : Subgroup (SL(3, ZMod p)) := Y.comap π
  have hA_B : A = upperTriangular 3 (ZMod p) := hpre
  have hdY : d ∣ Nat.card Y := by
    have hdvd : d ∣ Nat.card Y * Y.index := by
      rw [Subgroup.card_mul_index]
      exact hdG
    rcases hd.dvd_mul.mp hdvd with h | h
    · exact h
    · exact absurd h (hY.not_dvd_index hd)
  have hYeq : A.map π = Y := by
    rw [show A = Y.comap π from rfl, Subgroup.map_comap_eq_self_of_surjective hπ]
  have hdA : d ∣ Nat.card A := by
    have h := Subgroup.card_map_dvd A π
    rw [hYeq] at h
    exact hdY.trans h
  have hdB : d ∣ Nat.card (upperTriangular 3 (ZMod p)) := by
    rwa [← hA_B]
  obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' d
    (G := ↥(upperTriangular 3 (ZMod p))) hdB
  have hx0' : orderOf (x0 : SL(3, ZMod p)) = d := by
    rw [Subgroup.orderOf_coe, hx0]
  let E : Subgroup (SL(3, ZMod p)) := Subgroup.zpowers (x0 : SL(3, ZMod p))
  have hEcard : Nat.card E = d := by
    rw [show E = Subgroup.zpowers (x0 : SL(3, ZMod p)) from rfl, Nat.card_zpowers, hx0']
  have hEpg : IsPGroup d E := IsPGroup.of_card (n := 1) (by rw [hEcard, pow_one])
  have hEne : E ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card E = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hEcard] at h1
    exact hd.ne_one h1
  have hE_le : E ≤ upperTriangular 3 (ZMod p) := Subgroup.zpowers_le.mpr x0.2
  exact dvd_card_sub_one_of_isPGroup_le_borelSL3 hE_le hEne hEpg hd hdp

private theorem diagSL_not_mem_center_of_order {p d : ℕ} [Fact p.Prime] {u : (ZMod p)ˣ}
    (hd : d.Prime) (hd2 : d ≠ 2) (hu : orderOf u = d)
    (hux : (u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * 1 = 1) :
    diagSL (u : ZMod p) ((u⁻¹ : (ZMod p)ˣ) : ZMod p) 1 hux ∉
      Subgroup.center (SL(3, ZMod p)) := by
  classical
  intro hc
  obtain ⟨r, -, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have h00 : r = (u : ZMod p) := by
    have h := congrFun (congrFun hscalar 0) 0
    rw [Matrix.scalar_apply, coe_diagSL, Matrix.diagonal_apply_eq] at h
    exact h
  have h11 : r = ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    have h := congrFun (congrFun hscalar 1) 1
    rw [Matrix.scalar_apply, coe_diagSL, Matrix.diagonal_apply_eq] at h
    exact h
  have huu : u = u⁻¹ := Units.ext (h00.symm.trans h11)
  have hsq : u ^ 2 = 1 := by
    rw [sq]
    calc u * u = u * u⁻¹ := congrArg (fun z => u * z) huu
      _ = 1 := mul_inv_cancel u
  have hdvd2 : d ∣ 2 := by
    rw [← hu]
    exact orderOf_dvd_of_pow_eq_one hsq
  have hle := Nat.le_of_dvd (by norm_num) hdvd2
  have h2 := hd.two_le
  omega

private theorem exists_diagonal_element_conj_reflection {p d : ℕ} [Fact p.Prime]
    (hd : d.Prime) (hd2 : d ≠ 2) (hddvd : d ∣ p - 1) :
    ∃ x : SL(3, ZMod p), x ∈ upperTriangular 3 (ZMod p) ∧
      x ∉ Subgroup.center (SL(3, ZMod p)) ∧ x ^ d = 1 ∧
      reflection 3 (ZMod p) 1 (by norm_num) (by norm_num) * x *
        (reflection 3 (ZMod p) 1 (by norm_num) (by norm_num))⁻¹ = x⁻¹ := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' d
    (G := ((ZMod p)ˣ)) (by
      rw [Nat.card_units, Nat.card_zmod]
      exact hddvd)
  have hux : (u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * 1 = 1 := by
    rw [mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hux' : ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * (u : ZMod p) * 1 = 1 := by
    rw [mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let x : SL(3, ZMod p) := diagSL (u : ZMod p) ((u⁻¹ : (ZMod p)ˣ) : ZMod p) 1 hux
  have huxd : (u : ZMod p) ^ d = 1 := by
    have h := congrArg Units.val (pow_orderOf_eq_one u)
    rw [hu, Units.val_pow_eq_pow_val, Units.val_one] at h
    exact h
  have huxd' : (((u⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ d = 1 := by
    have h := congrArg Units.val (pow_orderOf_eq_one (u⁻¹))
    rw [orderOf_inv, hu, Units.val_pow_eq_pow_val, Units.val_one] at h
    exact h
  have hxpow : x ^ d = 1 := by
    rw [show x = diagSL (u : ZMod p) ((u⁻¹ : (ZMod p)ˣ) : ZMod p) 1 hux from rfl,
      diagSL_pow]
    exact (diagSL_congr huxd huxd' (by norm_num)).trans (diagSL_one (by ring))
  have hx_not_center : x ∉ Subgroup.center (SL(3, ZMod p)) := by
    rw [show x = diagSL (u : ZMod p) ((u⁻¹ : (ZMod p)ˣ) : ZMod p) 1 hux from rfl]
    exact diagSL_not_mem_center_of_order hd hd2 hu hux
  have hx_mem_B : x ∈ upperTriangular 3 (ZMod p) := by
    rw [mem_upperTriangular]
    intro i j hij
    rw [show x = diagSL (u : ZMod p) ((u⁻¹ : (ZMod p)ˣ) : ZMod p) 1 hux from rfl,
      coe_diagSL, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
  have hconj_r : reflection 3 (ZMod p) 1 (by norm_num) (by norm_num) * x *
      (reflection 3 (ZMod p) 1 (by norm_num) (by norm_num))⁻¹ =
      diagSL ((u⁻¹ : (ZMod p)ˣ) : ZMod p) (u : ZMod p) 1 hux' :=
    reflection_conj_diagSL hux hux' rfl
  have hx_inv : x⁻¹ = diagSL ((u⁻¹ : (ZMod p)ˣ) : ZMod p) (u : ZMod p) 1 hux' := by
    rw [show x = diagSL (u : ZMod p) ((u⁻¹ : (ZMod p)ˣ) : ZMod p) 1 hux from rfl,
      diagSL_inv']
    exact diagSL_congr (by rw [← Units.val_inv_eq_inv_val])
      (by rw [← Units.val_inv_eq_inv_val, inv_inv]) (by norm_num)
  exact ⟨x, hx_mem_B, hx_not_center, hxpow, hconj_r.trans hx_inv.symm⟩

private theorem normalizer_zpowers_le_of_borel_diagonal {p d : ℕ} [Fact p.Prime]
    (hd : d.Prime) {Y : Subgroup PSL(3, ZMod p)} (hY : IsBorelDLocal p d Y)
    {x : SL(3, ZMod p)}
    (hx_mem : x ∈ Y.comap (QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))))
    (hxpow : x ^ d = 1) (hxnc : x ∉ Subgroup.center (SL(3, ZMod p))) :
    Subgroup.normalizer (Subgroup.zpowers
      (QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p))) x) :
        Set (PSL(3, ZMod p))) ≤ Y := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  let y : PSL(3, ZMod p) := QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p))) x
  have hy_mem_Y : y ∈ Y := Subgroup.mem_comap.mp hx_mem
  have hy_d : y ^ d = 1 := by
    rw [show y = QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p))) x from rfl,
      ← map_pow, hxpow, map_one]
  have hy_ne : y ≠ 1 := by
    intro h
    have hker : x ∈ Subgroup.center (SL(3, ZMod p)) := by
      rw [← QuotientGroup.eq_one_iff]
      exact h
    exact hxnc hker
  have hord_y : orderOf y = d := orderOf_eq_prime hy_d hy_ne
  let H : Subgroup (PSL(3, ZMod p)) := Subgroup.zpowers y
  have hH_le : H ≤ Y := Subgroup.zpowers_le.mpr hy_mem_Y
  have hH_abel : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (isMulCommutative_iff.mp
      (inferInstance : IsMulCommutative ↥H) ⟨a, ha⟩ ⟨b, hb⟩)
  have hdH : d ∣ Nat.card H := by
    rw [show H = Subgroup.zpowers y from rfl, Nat.card_zpowers, hord_y]
  exact hY.normalizer_le_of_dvd hd hH_le hH_abel hdH

private theorem upperTriangular_not_isBorelDLocal {p d : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ≠ p) (hdG : d ∣ Nat.card PSL(3, ZMod p))
    {Y : Subgroup PSL(3, ZMod p)} (hY : IsBorelDLocal p d Y)
    (hpre : Y.comap (QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))) =
      upperTriangular 3 (ZMod p)) : False := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  have hddvd : d ∣ p - 1 :=
    dvd_p_sub_one_of_upperTriangular_isBorelDLocal hd hdp hdG hY hpre
  obtain ⟨x, hx_mem_B, hx_not_center, hxpow, hrx⟩ :=
    exists_diagonal_element_conj_reflection hd hd2 hddvd
  let π : SL(3, ZMod p) →* PSL(3, ZMod p) :=
    QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))
  let A : Subgroup (SL(3, ZMod p)) := Y.comap π
  have hA_B : A = upperTriangular 3 (ZMod p) := hpre
  have hx_mem_A : x ∈ A := by
    rw [hA_B]
    exact hx_mem_B
  have hx_mem_comap : x ∈ Y.comap
      (QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))) := by
    rwa [show A = Y.comap π from rfl] at hx_mem_A
  have hNH : Subgroup.normalizer (Subgroup.zpowers (π x) : Set (PSL(3, ZMod p))) ≤ Y :=
    normalizer_zpowers_le_of_borel_diagonal hd hY hx_mem_comap hxpow hx_not_center
  set r : SL(3, ZMod p) := reflection 3 (ZMod p) 1 (by norm_num) (by norm_num)
  have hconj : MulAut.conj (π r) (π x) = (π x)⁻¹ := by
    rw [MulAut.conj_apply]
    calc π r * π x * (π r)⁻¹
        = π (r * x) * (π r)⁻¹ := by rw [← map_mul]
      _ = π (r * x) * π r⁻¹ := by rw [← map_inv]
      _ = π (r * x * r⁻¹) := by rw [← map_mul]
      _ = π (x⁻¹) := by rw [hrx]
      _ = (π x)⁻¹ := by rw [map_inv]
  have hπrN : π r ∈ Subgroup.normalizer (Subgroup.zpowers (π x) :
      Set (PSL(3, ZMod p))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap : (Subgroup.zpowers (π x)).map (MulAut.conj (π r)) =
        Subgroup.zpowers (MulAut.conj (π r) (π x)) := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hmap, hconj, Subgroup.zpowers_inv]
  have hπrY : π r ∈ Y := hNH hπrN
  have hrA : r ∈ A := by
    rw [show A = Y.comap π from rfl]
    exact Subgroup.mem_comap.mpr hπrY
  rw [hA_B] at hrA
  exact reflection_not_mem_upperTriangular_sl3 (d := 1) (by norm_num) (by norm_num) hrA

private theorem statedClassicalModel_psl_three_of_isPSLType {G : Type} [Group G] {p : ℕ}
    (hp : p.Prime) (hG : IsPSLType 3 (ZMod p) G) : StatedClassicalModel G .PSL 3 p 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hG
  refine ⟨⟨hp, le_rfl, by norm_num, ?_, ?_⟩, ZMod p, inferInstance, inferInstance, ?_,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
      (ZMod p))⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · rw [Nat.card_zmod, pow_one]

private theorem center_eq_bot_of_isPSLType_three {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hG : IsPSLType 3 (ZMod p) G) : Subgroup.center G = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hG
  have hsimplePSL : IsSimpleGroup (PSL(3, ZMod p)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := ZMod p) (n := 3) (by norm_num)
      (Or.inl (by norm_num))).2.1
  have hsimpleG : IsSimpleGroup G := e.isSimpleGroup_congr.mpr hsimplePSL
  have hZle : Nat.card (Subgroup.center (SL(3, ZMod p))) ≤ 3 := by
    rw [Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
    simpa using card_rootsOfUnity (ZMod p) 3
  have hp_not_dvd : ¬ p ∣ Nat.card (Subgroup.center (SL(3, ZMod p))) := by
    intro hdiv
    have hpos : 0 < Nat.card (Subgroup.center (SL(3, ZMod p))) := Nat.card_pos
    have hle := Nat.le_of_dvd hpos hdiv
    omega
  have hcardEq : Nat.card (SL(3, ZMod p)) =
      Nat.card G * Nat.card (Subgroup.center (SL(3, ZMod p))) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (SL(3, ZMod p)))
    rw [h1, ← Nat.card_congr e.toEquiv]
  have hpdvd : p ^ 3 ∣ Nat.card G := by
    have h : p ^ 3 ∣ Nat.card (SL(3, ZMod p)) := by
      rw [CFSG.GroupTheory.card_SL3_zmod hp]
      exact dvd_mul_right _ _
    rw [hcardEq] at h
    have hcop : Nat.Coprime (p ^ 3) (Nat.card (Subgroup.center (SL(3, ZMod p)))) :=
      Nat.Coprime.pow_left 3 ((hp.coprime_iff_not_dvd).mpr hp_not_dvd)
    exact hcop.dvd_of_dvd_mul_right h
  have hnotprime : ¬ (Nat.card G).Prime := by
    intro hprime
    have hpdvd' : p ∣ Nat.card G := (dvd_pow_self p (by norm_num)).trans hpdvd
    rcases hprime.eq_one_or_self_of_dvd p hpdvd' with h1 | h1
    · exact hp.ne_one h1
    · rw [← h1] at hpdvd
      have hle : p ^ 3 ≤ p := Nat.le_of_dvd hp.pos hpdvd
      have hp2 : 2 ≤ p := hp.two_le
      have hp_lt : p < p ^ 3 := by
        have hsq : 1 < p ^ 2 := by nlinarith
        calc p = p * 1 := (mul_one p).symm
          _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left hsq hp.pos
          _ = p ^ 3 := by ring
      omega
  have hnotcomm : ¬ IsMulCommutative G := by
    intro hcomm
    haveI : IsSimpleGroup G := hsimpleG
    let : CommGroup G :=
      { (inferInstance : Group G) with
        mul_comm := fun x y => hcomm.is_comm.comm x y }
    exact hnotprime IsSimpleGroup.prime_card
  exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnotcomm

private theorem three_dvd_card_of_isPSLType_three {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hG : IsPSLType 3 (ZMod p) G) : 3 ∣ Nat.card G := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hG
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_psl_three

private theorem outer_dvd_of_isPSLType_three {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hG : IsPSLType 3 (ZMod p) G) :
    Nat.card (Outer G) ∣ 2 * Nat.gcd 3 (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : StatedClassicalModel G .PSL 3 p 1 :=
    statedClassicalModel_psl_three_of_isPSLType hp hG
  have h := CFSG.Quasithin.A318P.outer_dvd_linear hS
  simpa using h

private theorem outer_not_dvd_and_only_three {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hG : IsPSLType 3 (ZMod p) G) :
    ¬ p ∣ Nat.card (Outer G) ∧
      (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (Outer G) → q = 3) := by
  have hOut := outer_dvd_of_isPSLType_three hp hG
  have hgpos : 0 < Nat.gcd 3 (p - 1) := by
    rcases Nat.eq_zero_or_pos (Nat.gcd 3 (p - 1)) with h | h
    · exfalso
      have h3 : Nat.gcd 3 (p - 1) ∣ 3 := Nat.gcd_dvd_left 3 (p - 1)
      rw [h] at h3
      exact absurd (Nat.eq_zero_of_zero_dvd h3) (by norm_num)
    · exact h
  have hout_le : Nat.card (Outer G) ≤ 2 * Nat.gcd 3 (p - 1) :=
    Nat.le_of_dvd (by omega : 0 < 2 * Nat.gcd 3 (p - 1)) hOut
  have hgcd : Nat.gcd 3 (p - 1) ≤ 3 :=
    Nat.le_of_dvd (by norm_num : 0 < 3) (Nat.gcd_dvd_left 3 (p - 1))
  have hbound : 2 * Nat.gcd 3 (p - 1) < p := by
    rcases eq_or_lt_of_le hp5 with rfl | hp7
    · norm_num
    · have hpodd : Odd p := hp.odd_of_ne_two (by omega)
      obtain ⟨k, hk⟩ := hpodd
      omega
  have hout_lt : Nat.card (Outer G) < p := lt_of_le_of_lt hout_le hbound
  constructor
  · intro hdiv
    haveI : Nonempty (Outer G) := ⟨1⟩
    have hle : p ≤ Nat.card (Outer G) := Nat.le_of_dvd (Nat.card_pos (α := Outer G)) hdiv
    omega
  · intro q hq hq2 hqdvd
    have hq_dvd : q ∣ 2 * Nat.gcd 3 (p - 1) := hqdvd.trans hOut
    have hq3 : q ∣ 3 := by
      rcases hq.dvd_mul.mp hq_dvd with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2) hq2
      · exact h2.trans (Nat.gcd_dvd_left 3 (p - 1))
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hq3

theorem threeNineOut_psl_three {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hG : IsPSLType 3 (ZMod p) G) :
    Subgroup.center G = ⊥ ∧ ¬ p ∣ Nat.card (Outer G) ∧
      (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (Outer G) → q = 3) ∧ 3 ∣ Nat.card G ∧
      Nat.card (Outer G) ∣ 2 * Nat.gcd 3 (p - 1) := by
  obtain ⟨hnotp, hq3⟩ := outer_not_dvd_and_only_three hp hp5 hG
  exact ⟨center_eq_bot_of_isPSLType_three hp hp5 hG, hnotp, hq3,
    three_dvd_card_of_isPSLType_three hp hG, outer_dvd_of_isPSLType_three hp hG⟩

theorem isCyclic_of_isPGroup_psl_three {p d : ℕ} [Fact p.Prime] (hd : d.Prime) (hd2 : d ≠ 2)
    (hdp : d ∣ p + 1) {S : Subgroup PSL(3, ZMod p)} (hS : IsPGroup d S) : IsCyclic S := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fact d.Prime := ⟨hd⟩
  have hdp' : d ≠ p := by
    intro hdpq
    subst hdpq
    have h : d ∣ 1 := by
      have h' := Nat.dvd_sub hdp (dvd_refl d)
      have h'' : d + 1 - d = 1 := by omega
      rwa [h''] at h'
    exact hd.ne_one (Nat.dvd_one.mp h)
  let Q : Sylow d (SL(3, ZMod p)) := Classical.arbitrary _
  have hQcyc : IsCyclic ↥(Q : Subgroup (SL(3, ZMod p))) :=
    isCyclic_of_isSylow_dvd_p_add_one_of_prime_ne_two hp hd hd2 hdp' hdp
      (Subgroup.topEquiv) (by
        rw [CFSG.ABGLocalTools.isSylowOf_iff]
        exact ⟨le_top, Q.isPGroup', by simpa using Q.not_dvd_index⟩)
  let π : SL(3, ZMod p) →* PSL(3, ZMod p) :=
    QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let T : Sylow d (PSL(3, ZMod p)) := Q.mapSurjective hπ
  have hTcyc : IsCyclic ↥(T : Subgroup (PSL(3, ZMod p))) := by
    rw [Sylow.coe_mapSurjective]
    let f : ↥(Q : Subgroup (SL(3, ZMod p))) →*
        ↥((Q : Subgroup (SL(3, ZMod p))).map π) :=
      { toFun := fun x => ⟨π x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩
        map_one' := Subtype.ext π.map_one
        map_mul' := fun x y => Subtype.ext (π.map_mul x y) }
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
    haveI : IsCyclic ↥(Q : Subgroup (SL(3, ZMod p))) := hQcyc
    exact isCyclic_of_surjective f hf
  obtain ⟨T', hST'⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL(3, ZMod p)) T T'
  haveI : IsCyclic ↥(T' : Subgroup (PSL(3, ZMod p))) := by
    rw [← hg]
    exact (T.equivSMul g).isCyclic.mp hTcyc
  exact Subgroup.isCyclic_of_le (H := S)
    (H' := (T' : Subgroup (PSL(3, ZMod p)))) hST'

private theorem exists_conj_upperTriangular_le_comap {p d : ℕ} [Fact p.Prime]
    {Y : Subgroup PSL(3, ZMod p)} (hY : IsBorelDLocal p d Y) :
    ∃ g : PSL(3, ZMod p), IsBorelDLocal p d (Y.map (MulAut.conj g).toMonoidHom) ∧
      upperTriangular 3 (ZMod p) ≤
        (Y.map (MulAut.conj g).toMonoidHom).comap
          (QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))) := by
  classical
  have hp : p.Prime := Fact.out
  let π : SL(3, ZMod p) →* PSL(3, ZMod p) :=
    QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let U : Subgroup (SL(3, ZMod p)) := unitriangular 3 (ZMod p)
  have hUis : CFSG.ABGLocalTools.IsSylowOf p U ⊤ := isSylowOf_unitriangular_sl3
  have hUidx : ¬ p ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hUis).2.2
  let Q : Sylow p (SL(3, ZMod p)) := hUis.isPGroup.toSylow hUidx
  have hQcoe : (Q : Subgroup (SL(3, ZMod p))) = U := hUis.isPGroup.toSylow_coe hUidx
  let P0 : Sylow p (PSL(3, ZMod p)) := Q.mapSurjective hπ
  have hP0coe : (P0 : Subgroup (PSL(3, ZMod p))) = U.map π := by
    rw [show P0 = Q.mapSurjective hπ from rfl, Sylow.coe_mapSurjective, hQcoe]
  obtain ⟨g, hYmap, hN⟩ := hY.exists_conj hp P0
  refine ⟨g, hYmap, ?_⟩
  rw [← normalizer_unitriangular (K := ZMod p) (n := 3), ← Subgroup.map_le_iff_le_comap]
  refine (Subgroup.le_normalizer_map π).trans ?_
  rwa [hP0coe] at hN

private theorem dvd_p_add_one_of_isBorelDLocal_index {p d : ℕ} [Fact p.Prime]
    (hd : d.Prime) (hdp : d ≠ p) (hdG : d ∣ Nat.card PSL(3, ZMod p))
    {Y : Subgroup PSL(3, ZMod p)} (hY : IsBorelDLocal p d Y)
    (hidx : Y.index = p ^ 2 + p + 1) : d ∣ p + 1 := by
  have hp : p.Prime := Fact.out
  have hmod : p ^ 2 + p + 1 ≡ 1 [MOD d] := by
    rw [← hidx]
    exact hY.index_modEq_one_of_dvd hd hdG
  have hdiv : d ∣ p ^ 2 + p := by
    have h := hmod.symm.dvd'
    rwa [show p ^ 2 + p + 1 - 1 = p ^ 2 + p by omega] at h
  rw [show p ^ 2 + p = p * (p + 1) by ring] at hdiv
  rcases hd.dvd_mul.mp hdiv with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hd hp).mp h) hdp
  · exact h

theorem exists_conj_comap_eq_flagStabilizer {p d : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ≠ p) (hdG : d ∣ Nat.card PSL(3, ZMod p))
    {Y : Subgroup PSL(3, ZMod p)} (hY : IsBorelDLocal p d Y) :
    d ∣ p + 1 ∧ ∃ g : PSL(3, ZMod p), ∃ i : ℕ, (i = 1 ∨ i = 2) ∧
      (Y.map (MulAut.conj g).toMonoidHom).comap
          (QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))) =
        flagStabilizer 3 (ZMod p) ({i} : Set ℕ) := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨g, hY', hBleA⟩ := exists_conj_upperTriangular_le_comap hY
  let Y' : Subgroup (PSL(3, ZMod p)) := Y.map (MulAut.conj g).toMonoidHom
  let π : SL(3, ZMod p) →* PSL(3, ZMod p) :=
    QuotientGroup.mk' (Subgroup.center (SL(3, ZMod p)))
  let A : Subgroup (SL(3, ZMod p)) := Y'.comap π
  rcases borel_overgroups_sl3 A hBleA with hA | hA | hA | hA
  · exfalso
    have htop : Y' = ⊤ := by
      have h1 := Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective (Subgroup.center (SL(3, ZMod p)))) Y'
      rw [show Y'.comap π = A from rfl, hA,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
      exact h1.symm
    exact hY'.lt_top.ne htop
  · have hidx : Y'.index = p ^ 2 + p + 1 := by
      rw [← Subgroup.index_comap_of_surjective (H := Y')
        (QuotientGroup.mk'_surjective (Subgroup.center (SL(3, ZMod p))))]
      rw [show Y'.comap π = A from rfl, hA]
      exact index_flagStabilizer_sl3_one
    refine ⟨dvd_p_add_one_of_isBorelDLocal_index hd hdp hdG hY' hidx, g, 1, Or.inl rfl, ?_⟩
    show A = flagStabilizer 3 (ZMod p) ({1} : Set ℕ)
    exact hA
  · have hidx : Y'.index = p ^ 2 + p + 1 := by
      rw [← Subgroup.index_comap_of_surjective (H := Y')
        (QuotientGroup.mk'_surjective (Subgroup.center (SL(3, ZMod p))))]
      rw [show Y'.comap π = A from rfl, hA]
      exact index_flagStabilizer_sl3_two
    refine ⟨dvd_p_add_one_of_isBorelDLocal_index hd hdp hdG hY' hidx, g, 2, Or.inr rfl, ?_⟩
    show A = flagStabilizer 3 (ZMod p) ({2} : Set ℕ)
    exact hA
  · exfalso
    exact upperTriangular_not_isBorelDLocal hp5 hd hd2 hdp hdG hY'
      (by simpa [A, Y'] using hA)

end CFSG.LocalAnalysis.AGL81I.Section3
