module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutSU2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3AutCard
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DFin
import CFSG.Quasithin.Background.GoldschmidtListedSolv

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.UnitaryFlag
open Matrix.GeneralLinearGroup (scalar coe_scalar)
open scoped Matrix

variable {K : Type} [Field K]

theorem exists_heisData_statedSU_two [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ∃ X P w F : ↥(StatedSU 3 (2 ^ 1) K), HeisData ↥(StatedSU 3 (2 ^ 1) K) X P w F ∧
      ((w : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) := by
  have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  have hchar : CharP K 2 := h.charP
  obtain ⟨ω, hω3, hω1⟩ := exists_primitive_cube_root K (by rw [hK]; norm_num)
  have hsum : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  have hωq : ω ^ (2 ^ 1) = ω ^ 2 := by norm_num
  set H : Subgroup (GL (Fin 3) K) := StatedSU 3 (2 ^ 1) K with hH
  have hXH : Matrix.SpecialLinearGroup.toGL (hXsl hω3) ∈ H :=
    (mem_unitarySU_iff h).2 ⟨det_hX hω3, hX_unitary h hω3 hωq⟩
  have hPH : Matrix.SpecialLinearGroup.toGL (hPsl : Matrix.SpecialLinearGroup (Fin 3) K) ∈ H :=
    (mem_unitarySU_iff h).2 ⟨det_hP, hP_unitary h⟩
  have hω0 := ne_zero_of_pow_three hω3
  have hwH : wGL hω3 ∈ H := scalar_mem_unitarySU h (by norm_num) (c := Units.mk0 ω hω0)
    (by
      show ω * h.bar ω = 1
      rw [h.bar_apply]
      calc ω * ω ^ 2 ^ 1 = ω ^ 3 := by ring
        _ = 1 := hω3)
    (Units.ext (by simpa using hω3))
  let Fsl : Matrix.SpecialLinearGroup (Fin 3) K := ⟨hF ω, det_hF hsum⟩
  have hFH : Matrix.SpecialLinearGroup.toGL Fsl ∈ H :=
    (mem_unitarySU_iff h).2 ⟨det_hF hsum, hF_unitary hsum h rfl⟩
  have hcard : Nat.card ↥H = 216 := by
    have hZ := card_unitaryScalars h (n := 3) (by norm_num)
    have hPSU : Nat.card (unitaryPSU h 3) = 72 := by
      rw [Nat.card_congr (unitaryPSUEquiv h (n := 3) (by norm_num)).toEquiv]
      exact CFSG.Quasithin.card_statedProj_one hK
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (unitaryScalars h 3)
    rw [hZ, hPSU] at this
    have h3 : Nat.gcd 3 (2 ^ 1 + 1) = 3 := by norm_num
    rw [h3] at this
    exact this
  let Xm : ↥H := ⟨_, hXH⟩
  let Pm : ↥H := ⟨_, hPH⟩
  let wm : ↥H := ⟨_, hwH⟩
  let Fm : ↥H := ⟨_, hFH⟩
  have hcomm_scalar : ∀ y : ↥H, y * Xm = Xm * y → y * Pm = Pm * y →
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.scalar (Fin 3) (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) := by
    intro y h1 h2
    refine eq_scalar_of_commute hω3 hω1 _ ?_ ?_
    · have := congrArg (fun u : ↥H => ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
      exact this
    · have := congrArg (fun u : ↥H => ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h2
      exact this
  have htt : (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; 0, 0, 1; 0, 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have htne : (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) ≠ 1 := fun h' => by
    have := congrFun (congrFun h' 1) 1
    simp at this
  have hFF : (((Matrix.SpecialLinearGroup.toGL Fsl) ^ 2 : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
    rw [Units.val_pow_eq_pow_val, pow_two]
    exact hF_mul_hF hsum
  have hHeis : HeisData ↥H Xm Pm wm Fm := by
    refine
      { card := hcard
        w_central := fun g => Subtype.ext (Matrix.GeneralLinearGroup.scalar_commute _ _)
        w_pow := Subtype.ext (wGL_pow_three hω3)
        w_ne := ?_
        X_pow := Subtype.ext (XGL_pow_three hω3)
        P_pow := Subtype.ext PGL_pow_three
        XP := Subtype.ext (XGL_mul_PGL hω3)
        FP := ?_
        FX := ?_
        F_pow := ?_
        F_sq := ?_
        cent := ?_
        center_le := ?_ }
    · intro h'
      have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0)
        (congrArg Subtype.val h')
      simp [wm, wGL, Matrix.scalar_apply] at this
      exact hω1 this
    · refine Subtype.ext (mul_inv_eq_iff_eq_mul.2 (Units.ext ?_))
      exact hF_mul_hP hsum
    · refine Subtype.ext (mul_inv_eq_iff_eq_mul.2 ?_)
      refine (inv_mul_eq_iff_eq_mul.2 (Units.ext ?_)).symm
      show (hF ω) = (hP : Matrix (Fin 3) (Fin 3) K) * (hF ω * hX ω)
      rw [← mul_assoc]
      exact (hP_mul_hF_mul_hX hsum).symm
    · refine Subtype.ext (Units.ext ?_)
      show (((Matrix.SpecialLinearGroup.toGL Fsl) ^ 4 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Units.val_pow_eq_pow_val, hFF, pow_two, htt]
    · intro h'
      have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K))
        (congrArg Subtype.val h')
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [hFF] at this
      exact htne this
    · intro y h1 h2
      have hy := hcomm_scalar y h1 h2
      refine Subgroup.mem_center_iff.2 fun g => Subtype.ext (Units.ext ?_)
      show ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((y : GL (Fin 3) K) : Matrix _ _ K)
        = ((y : GL (Fin 3) K) : Matrix _ _ K) * ((g : GL (Fin 3) K) : Matrix _ _ K)
      rw [hy]
      exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).symm.eq
    · intro z hz
      have h1 : z * Xm = Xm * z := (Subgroup.mem_center_iff.1 hz Xm).symm
      have h2 : z * Pm = Pm * z := (Subgroup.mem_center_iff.1 hz Pm).symm
      have hzs := hcomm_scalar z h1 h2
      set c : K := ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 with hc
      have hdet : c ^ 3 = 1 := by
        have := ((mem_unitarySU_iff h).1 z.2).1
        rw [hzs] at this
        simpa [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three, pow_succ] using this
      obtain ⟨b, -, hb⟩ := eq_pow_of_pow_three_eq_one hω3 hω1 hdet
      refine Subgroup.mem_zpowers_iff.2 ⟨b, ?_⟩
      refine Subtype.ext (Units.ext ?_)
      rw [zpow_natCast]
      show (((wGL hω3) ^ b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      rw [hzs, wGL, ← map_pow, coe_scalar, Units.val_pow_eq_pow_val, Units.val_mk0, hb]
  exact ⟨Xm, Pm, wm, Fm, hHeis, ⟨Units.mk0 ω hω0, rfl⟩⟩

section Quotient

variable {M : Type} [Group M] [Finite M] {X P w F : M}

theorem closure_pair_comm_cube {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (∀ x ∈ Subgroup.closure ({a, b} : Set G), ∀ y ∈ Subgroup.closure ({a, b} : Set G),
      x * y = y * x) ∧ ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ 3 = 1 := by
  have h1 : ∀ s ∈ ({a, b} : Set G), ∀ x ∈ Subgroup.closure ({a, b} : Set G), x * s = s * x := by
    intro s hs x hx
    have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer {s} := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff.1 hu]
      rcases ht with rfl | ht
      · rcases hs with rfl | hs
        · rfl
        · rw [Set.mem_singleton_iff.1 hs]; exact hab.symm
      · rw [Set.mem_singleton_iff.1 ht]
        rcases hs with rfl | hs
        · exact hab
        · rw [Set.mem_singleton_iff.1 hs]
    exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) s rfl).symm
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b} : Set G), ∀ y ∈ Subgroup.closure ({a, b} : Set G),
      x * y = y * x := by
    intro x hx y hy
    have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer {y} := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff.1 hu]
      exact h1 t ht y hy
    exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) y rfl).symm
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff.1 hx]; exact hb
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := hcomm x hx y hy
    rw [hc.mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

namespace HeisData

variable (H : HeisData M X P w F)

include H

theorem center_eq_zpowers : Subgroup.center M = Subgroup.zpowers w :=
  le_antisymm (fun z hz => H.center_le z hz)
    (Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 fun g => (H.w_central g).symm))

theorem card_center : Nat.card (Subgroup.center M) = 3 := by
  rw [H.center_eq_zpowers, Nat.card_zpowers, orderOf_eq_prime H.w_pow H.w_ne]

theorem center_le_R : Subgroup.center M ≤ heisR X P := by
  rw [H.center_eq_zpowers]
  exact Subgroup.zpowers_le.2 H.w_mem

theorem mem_R_of_comm_mod_center {y : M}
    (hX : y * X * y⁻¹ * X⁻¹ ∈ Subgroup.center M) (hP : y * P * y⁻¹ * P⁻¹ ∈ Subgroup.center M) :
    y ∈ heisR X P := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, w ^ i = y * X * y⁻¹ * X⁻¹ :=
    Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (H.center_le _ hX))
  obtain ⟨j, hj⟩ : ∃ j : ℕ, w ^ j = y * P * y⁻¹ * P⁻¹ :=
    Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (H.center_le _ hP))
  have hw2 : (w⁻¹) ^ 2 = w := by
    calc (w⁻¹) ^ 2 = w⁻¹ * w⁻¹ * w ^ 3 := by rw [H.w_pow, mul_one, pow_two]
      _ = w := by group
  set r : M := P ^ (2 * i) * X ^ j with hr
  have hrX : r * X * r⁻¹ = y * X * y⁻¹ := by
    have h1 : r * X * r⁻¹ = P ^ (2 * i) * X * (P ^ (2 * i))⁻¹ := by
      have hc : Commute (X ^ j) X := (Commute.refl X).pow_left j
      calc r * X * r⁻¹ = P ^ (2 * i) * (X ^ j * X * (X ^ j)⁻¹) * (P ^ (2 * i))⁻¹ := by
            rw [hr]; group
        _ = P ^ (2 * i) * X * (P ^ (2 * i))⁻¹ := by
            rw [hc.eq]; group
    rw [h1, H.conj_pow_X, pow_mul, hw2, hi]
    group
  have hrP : r * P * r⁻¹ = y * P * y⁻¹ := by
    have hc : Commute (P ^ (2 * i)) P := (Commute.refl P).pow_left _
    have hcw : Commute (w ^ j) (P ^ (2 * i)) := ((show Commute w (P ^ (2 * i)) from
      H.w_central _).pow_left j)
    calc r * P * r⁻¹ = P ^ (2 * i) * (X ^ j * P * (X ^ j)⁻¹) * (P ^ (2 * i))⁻¹ := by
          rw [hr]; group
      _ = P ^ (2 * i) * (w ^ j * P) * (P ^ (2 * i))⁻¹ := by rw [H.conj_pow_P]
      _ = w ^ j * (P ^ (2 * i) * P * (P ^ (2 * i))⁻¹) := by
          rw [← mul_assoc, ← mul_assoc, ← hcw.eq]; group
      _ = w ^ j * P := by rw [hc.eq]; group
      _ = y * P * y⁻¹ := by rw [hj]; group
  have hyX : (r⁻¹ * y) * X = X * (r⁻¹ * y) := by
    calc r⁻¹ * y * X = r⁻¹ * (y * X * y⁻¹) * y := by group
      _ = r⁻¹ * (r * X * r⁻¹) * y := by rw [hrX]
      _ = X * (r⁻¹ * y) := by group
  have hyP : (r⁻¹ * y) * P = P * (r⁻¹ * y) := by
    calc r⁻¹ * y * P = r⁻¹ * (y * P * y⁻¹) * y := by group
      _ = r⁻¹ * (r * P * r⁻¹) * y := by rw [hrP]
      _ = P * (r⁻¹ * y) := by group
  have hcen : r⁻¹ * y ∈ Subgroup.center M := H.cent _ hyX hyP
  have hR : r ∈ heisR X P :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (P_mem_heisR X P) _) (Subgroup.pow_mem _ (X_mem_heisR X P) _)
  have hz : r⁻¹ * y ∈ heisR X P := H.center_le_R hcen
  have : y = r * (r⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ hR hz

end HeisData


open CFSG.HardMathSupport.Solomon.UniquenessMaximal in
theorem not_hasElemSection3_four_heis (H : HeisData M X P w F)
    (P3 : Subgroup (MulAut (M ⧸ Subgroup.center M))) (hP : IsPGroup 3 P3) :
    ¬ HasElemSection3 P3 4 := by
  classical
  set Z := Subgroup.center M with hZ
  let mk : M →* M ⧸ Z := QuotientGroup.mk' Z
  have hmk : Function.Surjective mk := QuotientGroup.mk'_surjective Z
  let R := heisR X P
  let V : Subgroup (M ⧸ Z) := R.map mk
  have hVn : V.Normal := H.normal_R.map mk hmk
  have hVcard : Nat.card V = 9 := by
    have h := Subgroup.card_ker_mul_card_range (mk.comp R.subtype)
    have hker : (mk.comp R.subtype).ker = Z.subgroupOf R := by
      ext x
      simp [mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hrange : (mk.comp R.subtype).range = V := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe H.center_le_R).toEquiv,
      H.card_center, H.card_R] at h
    omega
  have hVcl : V = Subgroup.closure ({mk X, mk P} : Set (M ⧸ Z)) := by
    show (heisR X P).map mk = _
    rw [heisR, MonoidHom.map_closure]
    congr 1
    ext z
    simp [Set.image_pair]
  have hab : mk X * mk P = mk P * mk X := by
    rw [← map_mul, ← map_mul]
    show (QuotientGroup.mk (X * P) : M ⧸ Z) = QuotientGroup.mk (P * X)
    rw [QuotientGroup.eq]
    have hc : Commute w⁻¹ (P * X) := Commute.inv_left (show Commute w (P * X) from H.w_central _)
    have : (X * P)⁻¹ * (P * X) = w⁻¹ := by
      rw [H.XP, _root_.mul_inv_rev]
      calc (P * X)⁻¹ * w⁻¹ * (P * X) = (P * X)⁻¹ * (w⁻¹ * (P * X)) := by group
        _ = (P * X)⁻¹ * ((P * X) * w⁻¹) := by rw [hc.eq]
        _ = w⁻¹ := by group
    rw [this, hZ, H.center_eq_zpowers]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers w)
  have hX3 : mk X ^ 3 = 1 := by rw [← map_pow, H.X_pow, map_one]
  have hP3 : mk P ^ 3 = 1 := by rw [← map_pow, H.P_pow, map_one]
  obtain ⟨hVcomm', hV3'⟩ := closure_pair_comm_cube hab hX3 hP3
  rw [← hVcl] at hVcomm' hV3'
  have hYcard : Nat.card (M ⧸ Z) = 72 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [H.card, H.card_center] at h
    omega
  have hcent : ∀ y : M ⧸ Z, (∀ v ∈ V, y * v = v * y) → y ∈ V := by
    intro y hy
    obtain ⟨y', rfl⟩ := hmk y
    have hXV : mk X ∈ V := ⟨X, X_mem_heisR X P, rfl⟩
    have hPV : mk P ∈ V := ⟨P, P_mem_heisR X P, rfl⟩
    have h1 := hy _ hXV
    have h2 := hy _ hPV
    have hcX : y' * X * y'⁻¹ * X⁻¹ ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      show mk (y' * X * y'⁻¹ * X⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have hcP : y' * P * y'⁻¹ * P⁻¹ ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      show mk (y' * P * y'⁻¹ * P⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]
      group
    exact ⟨y', H.mem_R_of_comm_mod_center hcX hcP, rfl⟩
  have hcard27 : Nat.card P3 ≤ 27 :=
    card_le_twentySeven_of_pGroup (Y := M ⧸ Z) V hVcard hVcomm' hV3' hYcard hcent P3 hP
  rintro ⟨H', N, hNH, hHP, -, -, -, hidx⟩
  have h1 : (N.subgroupOf H').index ∣ Nat.card H' := Subgroup.relIndex_dvd_card N H'
  have h2 : Nat.card H' ≤ Nat.card P3 := Subgroup.card_le_of_le hHP
  have h3 : (N.subgroupOf H').index ≤ Nat.card H' := Nat.le_of_dvd Nat.card_pos h1
  omega

end Quotient

open CFSG.HardMathSupport.Solomon.UniquenessMaximal in
theorem not_hasElemSection3_of_equiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    (e : Y ≃* Y') (h' : ∀ P : Subgroup (MulAut Y'), IsPGroup 3 P → ¬ HasElemSection3 P 4)
    (P : Subgroup (MulAut Y)) (hP : IsPGroup 3 P) : ¬ HasElemSection3 P 4 := fun hs =>
  h' (P.map (MulAut.congr e).toMonoidHom) (hP.map _)
    (HasElemSection3.map_of_inj _ (MulAut.congr e).injective hs)

open CFSG.HardMathSupport.Solomon.UniquenessMaximal in
theorem not_hasElemSection3_four_statedProj_two [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* StatedProj (StatedSU 3 (2 ^ 1) K))
    (P : Subgroup (MulAut Y)) (hP : IsPGroup 3 P) : ¬ HasElemSection3 P 4 := by
  obtain ⟨X, P0, w, F, H, hw⟩ := exists_heisData_statedSU_two hK
  have hsub : (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ 1) K) =
      Subgroup.center ↥(StatedSU 3 (2 ^ 1) K) := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨c, hc⟩
      refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
      show ((g : GL (Fin 3) K) * (x : GL (Fin 3) K)) = (x : GL (Fin 3) K) * g
      rw [← hc]
      have hcen : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨c, rfl⟩
      exact Subgroup.mem_center_iff.1 hcen _
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (H.center_le x hx)
      have : (x : GL (Fin 3) K) = (w : GL (Fin 3) K) ^ n := by
        rw [← hn]; rfl
      rw [this]
      exact (StatedScalars (Fin 3) K).zpow_mem hw n
  let e0 : StatedProj (StatedSU 3 (2 ^ 1) K) ≃* ↥(StatedSU 3 (2 ^ 1) K) ⧸
      Subgroup.center ↥(StatedSU 3 (2 ^ 1) K) :=
    QuotientGroup.quotientMulEquivOfEq hsub
  exact not_hasElemSection3_of_equiv (e.trans e0)
    (fun P hP => not_hasElemSection3_four_heis H P hP) P hP

end CFSG.HardMathSupport.Solomon.Coordinator
