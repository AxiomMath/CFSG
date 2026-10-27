module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6VtwDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcOuterNat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6Three

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

open Matrix CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ClassicalInvolution.Balance.StrongBalance (GUid mem_GUid conjSUid coe_conjSUid)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

section Group

variable {G H A : Type*} [Group G] [Group H] [Group A] (ι : H →* G) (α : A →* MulAut H)

theorem conj_pow_eq_of_conj_eq {g : G} {a : A} (h : ∀ z, g * ι z * g⁻¹ = ι (α a z)) (n : ℕ)
    (z : H) : g ^ n * ι z * (g ^ n)⁻¹ = ι (α (a ^ n) z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    calc g ^ (n + 1) * ι z * (g ^ (n + 1))⁻¹ = g ^ n * (g * ι z * g⁻¹) * (g ^ n)⁻¹ := by group
      _ = ι (α (a ^ (n + 1)) z) := by rw [h, ih, pow_succ, map_mul, MulAut.mul_apply]

theorem conj_mul_eq_of_conj_eq {g₁ g₂ : G} {a₁ a₂ : A} (h₁ : ∀ z, g₁ * ι z * g₁⁻¹ = ι (α a₁ z))
    (h₂ : ∀ z, g₂ * ι z * g₂⁻¹ = ι (α a₂ z)) (z : H) :
    g₁ * g₂ * ι z * (g₁ * g₂)⁻¹ = ι (α (a₁ * a₂) z) := by
  calc g₁ * g₂ * ι z * (g₁ * g₂)⁻¹ = g₁ * (g₂ * ι z * g₂⁻¹) * g₁⁻¹ := by group
    _ = ι (α (a₁ * a₂) z) := by rw [h₂, h₁, map_mul, MulAut.mul_apply]

theorem mul_pow_three_eq_of_conj_eq {g : G} {a : A} (h : ∀ z, g * ι z * g⁻¹ = ι (α a z))
    (w : H) : (ι w * g) ^ 3 = ι (w * α a w * α a (α a w)) * g ^ 3 := by
  have hc : ∀ z, g * ι z = ι (α a z) * g := fun z => by
    rw [← h z]
    group
  calc (ι w * g) ^ 3 = ι w * (g * ι w) * (g * ι w) * g := by
        rw [pow_three]
        simp only [mul_assoc]
    _ = ι w * (ι (α a w) * g) * (ι (α a w) * g) * g := by rw [hc w]
    _ = ι w * ι (α a w) * (g * ι (α a w)) * g * g := by group
    _ = ι w * ι (α a w) * (ι (α a (α a w)) * g) * g * g := by rw [hc]
    _ = ι (w * α a w * α a (α a w)) * g ^ 3 := by
        rw [map_mul, map_mul, pow_three]
        simp only [mul_assoc]

end Group

section DiagU

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem diagGL_mem_GUid {n : ℕ} {a : Fin n → Kˣ}
    (ha : ∀ i, unitaryInvolution K ℓ f (a i : K) * (a i : K) = 1) :
    diagGL K n a ∈ GUid (unitaryInvolution K ℓ f) n := by
  rw [mem_GUid, coe_diagGL, conjTr, diagonal_map (map_zero _), diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact ha i

theorem conjSUid_eq_of_isDiag {A : GUid (unitaryInvolution K ℓ f) 6} {a : Fin 6 → K}
    (hA : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal a) {s : Su K ℓ f 6}
    (hs : ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    conjSUid (unitaryInvolution K ℓ f) 6 A s = s := by
  apply Subtype.ext
  rw [coe_conjSUid]
  have hcomm : (A : GL (Fin 6) K) * (s : GL (Fin 6) K) =
      (s : GL (Fin 6) K) * (A : GL (Fin 6) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hA, ← hs.diagonal_diag, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [hcomm, mul_inv_cancel_right]

variable (c : Kˣ) in
@[expose] def vtwD0 : Fin 6 → Kˣ := ![1, 1, 1, 1, c⁻¹, 1]

variable {c : Kˣ}

@[expose] noncomputable def vtwD0GU (hσc : unitaryInvolution K ℓ f (c : K) = ((c⁻¹ : Kˣ) : K)) :
    GUid (unitaryInvolution K ℓ f) 6 :=
  ⟨diagGL K 6 (vtwD0 c), diagGL_mem_GUid fun i => by
    have hσc' : unitaryInvolution K ℓ f ((c⁻¹ : Kˣ) : K) = (c : K) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hσc, Units.val_inv_eq_inv_val, inv_inv]
    fin_cases i
    · show unitaryInvolution K ℓ f ((1 : Kˣ) : K) * ((1 : Kˣ) : K) = 1
      simp
    · show unitaryInvolution K ℓ f ((1 : Kˣ) : K) * ((1 : Kˣ) : K) = 1
      simp
    · show unitaryInvolution K ℓ f ((1 : Kˣ) : K) * ((1 : Kˣ) : K) = 1
      simp
    · show unitaryInvolution K ℓ f ((1 : Kˣ) : K) * ((1 : Kˣ) : K) = 1
      simp
    · show unitaryInvolution K ℓ f ((c⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) = 1
      rw [hσc', ← Units.val_mul, mul_inv_cancel, Units.val_one]
    · show unitaryInvolution K ℓ f ((1 : Kˣ) : K) * ((1 : Kˣ) : K) = 1
      simp⟩

theorem coe_vtwD0GU (hσc : unitaryInvolution K ℓ f (c : K) = ((c⁻¹ : Kˣ) : K)) :
    ((vtwD0GU hσc : GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) = diagGL K 6 (vtwD0 c) :=
  rfl

end DiagU

section X

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {c : Kˣ}

omit [Finite K] [Fact ℓ.Prime] [CharP K ℓ] in
theorem pow_three_eq_one_of_orderOf (hc : orderOf c = 3) : c ^ 3 = 1 := by
  rw [← hc, pow_orderOf_eq_one]

theorem unitaryInvolution_eq_inv_of_orderOf (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    unitaryInvolution K ℓ f (c : K) = ((c⁻¹ : Kˣ) : K) :=
  unitaryInvolution_eq_inv_of_pow_three (pow_three_eq_one_of_orderOf hc) h3


variable (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)

theorem det_vtwC (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    (((vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) :
      GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det =
        ((c⁻¹ : Kˣ) : K) := by
  have hu3 : ((c⁻¹ : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, pow_three_eq_one_of_orderOf hc, inv_one,
      Units.val_one]
  rw [coe_vtwC, Units.val_mul, Units.val_mul, det_mul, det_mul, coe_diagGL, det_diagonal,
    mul_comm (det (P : Matrix (Fin 6) (Fin 6) K)), mul_assoc, ← det_mul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, det_one, mul_one, Fin.prod_univ_six]
  change ((1 : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) *
    ((c⁻¹ : Kˣ) : K) * ((1 : Kˣ) : K) = ((c⁻¹ : Kˣ) : K)
  rw [Units.val_one]
  linear_combination ((c⁻¹ : Kˣ) : K) * hu3

@[expose] noncomputable def vtwW (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) : Su K ℓ f 6 :=
  ⟨((vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3) *
      (vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3))⁻¹ :
        GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K), by
    refine ⟨?_, (vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3) *
      (vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3))⁻¹).2⟩
    have hCinv : ((((vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3))⁻¹ :
        GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det *
        (((vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) :
          GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det =
            1 := by
      rw [← det_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
        Units.val_one, det_one]
    rw [det_vtwC P hP hc h3] at hCinv
    rw [Subgroup.coe_mul, Units.val_mul, det_mul, coe_vtwD0GU, coe_diagGL, det_diagonal,
      Fin.prod_univ_six, mul_comm]
    change _ * (((1 : Kˣ) : K) * ((1 : Kˣ) : K) * ((1 : Kˣ) : K) * ((1 : Kˣ) : K) *
      ((c⁻¹ : Kˣ) : K) * ((1 : Kˣ) : K)) = 1
    rw [Units.val_one, one_mul, one_mul, one_mul, one_mul, mul_one]
    exact hCinv⟩

theorem coe_vtwW (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    ((vtwW P hP hc h3 : Su K ℓ f 6) : GL (Fin 6) K) =
      ((vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3) : GUid (unitaryInvolution K ℓ f) 6) :
        GL (Fin 6) K) *
      ((vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) : GUid (unitaryInvolution K ℓ f) 6) :
        GL (Fin 6) K)⁻¹ :=
  rfl

@[expose] noncomputable def vtwX (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    ↥(twistedE6InndiagGL K (unitaryInvolution K ℓ f)) :=
  ⟨(leviSU hK hf hζ hσζ P hP (vtwW P hP hc h3) : ModGL TwistTag.E6.tag K) * vtwD c,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (leviSU hK hf hζ hσζ P hP (vtwW P hP hc h3)).2)
      (Subgroup.mem_sup_right
        (vtwD_mem_twistedE6DiagGL (unitaryInvolution_eq_inv_of_orderOf hc h3)))⟩

theorem coe_vtwX (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    ((vtwX hK hf hζ hσζ P hP hc h3 : ↥(twistedE6InndiagGL K (unitaryInvolution K ℓ f))) :
      ModGL TwistTag.E6.tag K) =
        (leviSU hK hf hζ hσζ P hP (vtwW P hP hc h3) : ModGL TwistTag.E6.tag K) * vtwD c :=
  rfl

theorem leviSU_conj_leviSU (y z : Su K ℓ f 6) :
    (leviSU hK hf hζ hσζ P hP y : ModGL TwistTag.E6.tag K) *
        (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K) *
        (leviSU hK hf hζ hσζ P hP y : ModGL TwistTag.E6.tag K)⁻¹ =
      (leviSU hK hf hζ hσζ P hP
        (conjSUid (unitaryInvolution K ℓ f) 6 ⟨(y : GL (Fin 6) K), y.2.2⟩ z) :
          ModGL TwistTag.E6.tag K) := by
  have e : conjSUid (unitaryInvolution K ℓ f) 6 ⟨(y : GL (Fin 6) K), y.2.2⟩ z = y * z * y⁻¹ :=
    Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv]
  rfl

theorem vtwX_conj_leviSU (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) (y : Su K ℓ f 6) :
    (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) *
        (leviSU hK hf hζ hσζ P hP y : ModGL TwistTag.E6.tag K) *
        (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K)⁻¹ =
      (leviSU hK hf hζ hσζ P hP (conjSUid (unitaryInvolution K ℓ f) 6
        (vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3)) y) : ModGL TwistTag.E6.tag K) := by
  set ι' := (twistedE6RootGroup K (unitaryInvolution K ℓ f)).subtype.comp
    (leviSU hK hf hζ hσζ P hP) with hι'
  have hD : ∀ z, vtwD c * ι' z * (vtwD c)⁻¹ = ι' (conjSUid (unitaryInvolution K ℓ f) 6
      (vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3)) z) := fun z =>
    vtwD_conj_leviSU hK hf hζ hσζ P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) z
  have hw : ∀ z, ι' (vtwW P hP hc h3) * ι' z * (ι' (vtwW P hP hc h3))⁻¹ =
      ι' (conjSUid (unitaryInvolution K ℓ f) 6
        ⟨((vtwW P hP hc h3 : Su K ℓ f 6) : GL (Fin 6) K), (vtwW P hP hc h3).2.2⟩ z) := fun z =>
    leviSU_conj_leviSU hK hf hζ hσζ P hP _ z
  have h := conj_mul_eq_of_conj_eq ι' (conjSUid (unitaryInvolution K ℓ f) 6) hw hD y
  have he : (⟨((vtwW P hP hc h3 : Su K ℓ f 6) : GL (Fin 6) K), (vtwW P hP hc h3).2.2⟩ :
      GUid (unitaryInvolution K ℓ f) 6) * vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) =
        vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    change ((vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3) :
        GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) *
      ((vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) :
        GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K)⁻¹ *
      ((vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) :
        GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) = _
    group
  rw [he] at h
  exact h

theorem vtwD0GU_pow_three (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3) ^ 3 = 1 := by
  have h : vtwD0 c ^ 3 = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    fin_cases i <;> simp [vtwD0, pow_three_eq_one_of_orderOf hc, inv_pow]
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, coe_vtwD0GU, ← map_pow, h, map_one, OneMemClass.coe_one]

theorem vtwC_pow_three (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) ^ 3 = 1 := by
  have h : vtwE c ^ 3 = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    fin_cases i <;> simp [vtwE, pow_three_eq_one_of_orderOf hc, inv_pow]
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, coe_vtwC, conj_pow, ← map_pow, h, map_one, mul_one, mul_inv_cancel,
    OneMemClass.coe_one]

theorem vtwX_pow_three (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    vtwX hK hf hζ hσζ P hP hc h3 ^ 3 = 1 := by
  set ι' := (twistedE6RootGroup K (unitaryInvolution K ℓ f)).subtype.comp
    (leviSU hK hf hζ hσζ P hP) with hι'
  have hD : ∀ z, vtwD c * ι' z * (vtwD c)⁻¹ = ι' (conjSUid (unitaryInvolution K ℓ f) 6
      (vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3)) z) := fun z =>
    vtwD_conj_leviSU hK hf hζ hσζ P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) z
  have hd : ((vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3) :
      GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) ^ 3 = 1 := by
    rw [← SubgroupClass.coe_pow, vtwD0GU_pow_three hc h3, OneMemClass.coe_one]
  have hC : ((vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) :
      GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) ^ 3 = 1 := by
    rw [← SubgroupClass.coe_pow, vtwC_pow_three P hP hc h3, OneMemClass.coe_one]
  have key : vtwW P hP hc h3 * conjSUid (unitaryInvolution K ℓ f) 6
      (vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3)) (vtwW P hP hc h3) *
      conjSUid (unitaryInvolution K ℓ f) 6 (vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3))
        (conjSUid (unitaryInvolution K ℓ f) 6
          (vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3)) (vtwW P hP hc h3)) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_conjSUid, coe_conjSUid, coe_conjSUid, coe_vtwW,
      OneMemClass.coe_one]
    set d := ((vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3) :
      GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) with hddef
    set C := ((vtwC P hP (unitaryInvolution_eq_inv_of_orderOf hc h3) :
      GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) with hCdef
    have e : d * C⁻¹ * (C * (d * C⁻¹) * C⁻¹) * (C * (C * (d * C⁻¹) * C⁻¹) * C⁻¹) =
        d * d * d * (C ^ 3)⁻¹ := by group
    rw [e, ← pow_three', hd, hC, inv_one, mul_one]
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, coe_vtwX, OneMemClass.coe_one]
  change (ι' (vtwW P hP hc h3) * vtwD c) ^ 3 = 1
  rw [mul_pow_three_eq_of_conj_eq ι' (conjSUid (unitaryInvolution K ℓ f) 6) hD,
    vtwD_pow_three (pow_three_eq_one_of_orderOf hc), mul_one, key, map_one]

theorem vtwX_commute_rootSL2 (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) *
        rootSL2 TwistTag.E6.tag K e6HighestRoot A =
      rootSL2 TwistTag.E6.tag K e6HighestRoot A *
        (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) := by
  have hw := (rootSL2_commute_of_mem_leviJ A
    (leviSU_mem_leviJ hK hf hζ hσζ P hP (vtwW P hP hc h3))).symm
  have hD : vtwD c * rootSL2 TwistTag.E6.tag K e6HighestRoot A =
      rootSL2 TwistTag.E6.tag K e6HighestRoot A * vtwD c :=
    (mul_inv_eq_iff_eq_mul).1 (vtwD_conj_rootSL2 A)
  rw [coe_vtwX, mul_assoc, hD, ← mul_assoc, hw, mul_assoc]

theorem vtwX_conj_leviSU_of_isDiag (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) {s : Su K ℓ f 6}
    (hs : ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) *
        (leviSU hK hf hζ hσζ P hP s : ModGL TwistTag.E6.tag K) *
        (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K)⁻¹ =
      (leviSU hK hf hζ hσζ P hP s : ModGL TwistTag.E6.tag K) := by
  rw [vtwX_conj_leviSU, conjSUid_eq_of_isDiag (by rw [coe_vtwD0GU, coe_diagGL]) hs]

theorem vtwX_ne_one (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    vtwX hK hf hζ hσζ P hP hc h3 ≠ 1 := by
  intro h1
  have h1' : (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) = 1 := by rw [h1]; rfl
  have key : ∀ y, leviSU hK hf hζ hσζ P hP (conjSUid (unitaryInvolution K ℓ f) 6
      (vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3)) y) = leviSU hK hf hζ hσζ P hP y :=
    fun y => by
      have h := vtwX_conj_leviSU hK hf hζ hσζ P hP hc h3 y
      rw [h1', one_mul, inv_one, mul_one] at h
      exact (Subtype.ext h).symm
  have h04 := eq_of_forall_leviSU_conjSUid_eq hK hf hζ hσζ P hP
    (by rw [coe_vtwD0GU, coe_diagGL]) key 0 4
  have hc1 : c ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc
    exact absurd hc (by norm_num)
  have h04' : (1 : Kˣ) = c⁻¹ := Units.ext h04
  exact hc1 (inv_eq_one.1 h04'.symm)

theorem orderOf_vtwX (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1) :
    orderOf (vtwX hK hf hζ hσζ P hP hc h3) = 3 :=
  orderOf_eq_prime (vtwX_pow_three hK hf hζ hσζ P hP hc h3) (vtwX_ne_one hK hf hζ hσζ P hP hc h3)

end X

section Incl


variable {K : Type} [Field K]

theorem twistedE6RootGroup_le_twistedE6InndiagGL (σ : K ≃+* K) :
    twistedE6RootGroup K σ ≤ twistedE6InndiagGL K σ :=
  le_sup_left

theorem twistedE6InndiagConj_inclusion (σ : K ≃+* K) (g : ↥(twistedE6RootGroup K σ)) :
    twistedE6InndiagConj K σ (Subgroup.inclusion (twistedE6RootGroup_le_twistedE6InndiagGL σ) g) =
      MulAut.conj g :=
  MulEquiv.ext fun _ => Subtype.ext rfl

end Incl

section Phi


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)
  {c : Kˣ} (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1)
  (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))

theorem vtwX_commute_twE6Phi (b : Fin 5 → Multiplicative (ZMod 3)) :
    Commute (vtwX hK hf hζ hσζ P hP hc h3)
      (Subgroup.inclusion (twistedE6RootGroup_le_twistedE6InndiagGL (unitaryInvolution K ℓ f))
        (twE6Phi hK hf hζ hσζ P hP (by norm_num : (3 : ℕ) ≠ 2) hc hct (diagThreeHom c hc h3)
          b)) := by
  apply Subtype.ext
  change (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) *
      ((twE6R0 c hct : ModGL TwistTag.E6.tag K) ^ (Multiplicative.toAdd (b 0)).val *
        (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 fun i : Fin 4 => b i.succ) :
          ModGL TwistTag.E6.tag K)) =
    ((twE6R0 c hct : ModGL TwistTag.E6.tag K) ^ (Multiplicative.toAdd (b 0)).val *
        (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 fun i : Fin 4 => b i.succ) :
          ModGL TwistTag.E6.tag K)) * (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K)
  have hr : Commute (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K)
      (twE6R0 c hct : ModGL TwistTag.E6.tag K) := by
    rw [Commute, SemiconjBy, coe_twE6R0]
    exact vtwX_commute_rootSL2 hK hf hζ hσζ P hP hc h3 _
  have hs : Commute (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K)
      (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 fun i : Fin 4 => b i.succ) :
        ModGL TwistTag.E6.tag K) := by
    have h := vtwX_conj_leviSU_of_isDiag hK hf hζ hσζ P hP hc h3
      (s := diagThreeHom c hc h3 fun i : Fin 4 => b i.succ)
      (by rw [coe_diagThreeHom]; exact Matrix.isDiag_diagonal _)
    rw [Commute, SemiconjBy]
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  exact ((hr.pow_right _).mul_right hs).eq

@[expose] noncomputable def vtwPhi :
    (Fin 6 → Multiplicative (ZMod 3)) →* ↥(twistedE6InndiagGL K (unitaryInvolution K ℓ f)) :=
  (MonoidHom.noncommCoprod (powHom (vtwX hK hf hζ hσζ P hP hc h3)
      (orderOf_vtwX hK hf hζ hσζ P hP hc h3))
    ((Subgroup.inclusion (twistedE6RootGroup_le_twistedE6InndiagGL
      (unitaryInvolution K ℓ f))).comp
      (twE6Phi hK hf hζ hσζ P hP (by norm_num : (3 : ℕ) ≠ 2) hc hct (diagThreeHom c hc h3)))
    fun a b => by
      rw [powHom_apply]
      exact (vtwX_commute_twE6Phi hK hf hζ hσζ P hP hc h3 hct b).pow_left _).comp
    (splitHom (Multiplicative (ZMod 3)) 5)

theorem vtwPhi_apply (y : Fin 6 → Multiplicative (ZMod 3)) :
    ((vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ↥(twistedE6InndiagGL K (unitaryInvolution K ℓ f))) :
      ModGL TwistTag.E6.tag K) =
        (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) ^
            (Multiplicative.toAdd (y 0)).val *
          ((twE6R0 c hct : ModGL TwistTag.E6.tag K) ^ (Multiplicative.toAdd (y 1)).val *
            (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 fun i : Fin 4 => y i.succ.succ) :
              ModGL TwistTag.E6.tag K)) :=
  rfl

@[expose] noncomputable def vtwV :
    Subgroup (MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :=
  ((twistedE6InndiagConj K (unitaryInvolution K ℓ f)).comp
    (vtwPhi hK hf hζ hσζ P hP hc h3 hct)).range

@[expose] noncomputable def vtwA (y : Fin 6 → Multiplicative (ZMod 3)) :
    GUid (unitaryInvolution K ℓ f) 6 :=
  vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3) ^ (Multiplicative.toAdd (y 0)).val *
    ⟨((diagThreeHom c hc h3 fun i : Fin 4 => y i.succ.succ : Su K ℓ f 6) : GL (Fin 6) K),
      (diagThreeHom c hc h3 fun i : Fin 4 => y i.succ.succ).2.2⟩

theorem coe_vtwA (y : Fin 6 → Multiplicative (ZMod 3)) :
    (((vtwA hc h3 y : GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) =
        diagonal fun i => (((vtwD0 c ^ (Multiplicative.toAdd (y 0)).val) *
          diagTuple c hc (snocOneHom (Multiplicative (ZMod 3)) 4
            fun j : Fin 4 => y j.succ.succ)) i : K) := by
  rw [vtwA, Subgroup.coe_mul, SubgroupClass.coe_pow, coe_vtwD0GU, ← map_pow, Units.val_mul,
    coe_diagGL]
  change diagonal (fun i => ((vtwD0 c ^ (Multiplicative.toAdd (y 0)).val) i : K)) *
    (((diagThreeHom c hc h3 fun i : Fin 4 => y i.succ.succ : Su K ℓ f 6) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = _
  rw [coe_diagThreeHom, diagonal_mul_diagonal]
  rfl

theorem vtwPhi_conj_leviSU (y : Fin 6 → Multiplicative (ZMod 3)) (z : Su K ℓ f 6) :
    (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K) *
        (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K) *
        (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K)⁻¹ =
      (leviSU hK hf hζ hσζ P hP (conjSUid (unitaryInvolution K ℓ f) 6 (vtwA hc h3 y) z) :
        ModGL TwistTag.E6.tag K) := by
  set ι' := (twistedE6RootGroup K (unitaryInvolution K ℓ f)).subtype.comp
    (leviSU hK hf hζ hσζ P hP) with hι'
  have hx : ∀ z, (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) * ι' z *
      (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K)⁻¹ =
        ι' (conjSUid (unitaryInvolution K ℓ f) 6
          (vtwD0GU (unitaryInvolution_eq_inv_of_orderOf hc h3)) z) := fun z =>
    vtwX_conj_leviSU hK hf hζ hσζ P hP hc h3 z
  have hr : ∀ z, (twE6R0 c hct : ModGL TwistTag.E6.tag K) ^ (Multiplicative.toAdd (y 1)).val *
      ι' z * ((twE6R0 c hct : ModGL TwistTag.E6.tag K) ^ (Multiplicative.toAdd (y 1)).val)⁻¹ =
        ι' (conjSUid (unitaryInvolution K ℓ f) 6 1 z) := fun z => by
    have h := congrArg Subtype.val (twE6R0_pow_commute c hct (Multiplicative.toAdd (y 1)).val
      (leviSU_mem_leviJ hK hf hζ hσζ P hP z))
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at h
    rw [map_one, MulAut.one_apply]
    change (twE6R0 c hct : ModGL TwistTag.E6.tag K) ^ (Multiplicative.toAdd (y 1)).val *
        (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K) *
        ((twE6R0 c hct : ModGL TwistTag.E6.tag K) ^ (Multiplicative.toAdd (y 1)).val)⁻¹ =
      (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K)
    rw [h, mul_inv_cancel_right]
  have hs : ∀ z, ι' (diagThreeHom c hc h3 fun i : Fin 4 => y i.succ.succ) * ι' z *
      (ι' (diagThreeHom c hc h3 fun i : Fin 4 => y i.succ.succ))⁻¹ =
        ι' (conjSUid (unitaryInvolution K ℓ f) 6
          ⟨((diagThreeHom c hc h3 fun i : Fin 4 => y i.succ.succ : Su K ℓ f 6) : GL (Fin 6) K),
            (diagThreeHom c hc h3 fun i : Fin 4 => y i.succ.succ).2.2⟩ z) := fun z =>
    leviSU_conj_leviSU hK hf hζ hσζ P hP _ z
  have h := conj_mul_eq_of_conj_eq ι' (conjSUid (unitaryInvolution K ℓ f) 6)
    (conj_pow_eq_of_conj_eq ι' (conjSUid (unitaryInvolution K ℓ f) 6) hx
      (Multiplicative.toAdd (y 0)).val)
    (conj_mul_eq_of_conj_eq ι' (conjSUid (unitaryInvolution K ℓ f) 6) hr hs) z
  rw [one_mul] at h
  rw [vtwPhi_apply]
  exact h

theorem vtwPhi_commute_twE6T (y : Fin 6 → Multiplicative (ZMod 3)) :
    (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K) *
        (twE6T K ℓ f : ModGL TwistTag.E6.tag K) =
      (twE6T K ℓ f : ModGL TwistTag.E6.tag K) *
        (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K) := by
  have hx : Commute (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K)
      (twE6T K ℓ f : ModGL TwistTag.E6.tag K) := by
    rw [Commute, SemiconjBy, coe_twE6T]
    exact vtwX_commute_rootSL2 hK hf hζ hσζ P hP hc h3 _
  have hr : Commute (twE6R0 c hct : ModGL TwistTag.E6.tag K)
      (twE6T K ℓ f : ModGL TwistTag.E6.tag K) := by
    have h := congrArg Subtype.val (twE6R0_mul_twE6T c hct)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h
  have hs : Commute
      (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 fun i : Fin 4 => y i.succ.succ) :
        ModGL TwistTag.E6.tag K) (twE6T K ℓ f : ModGL TwistTag.E6.tag K) := by
    have h := congrArg Subtype.val (twE6T_commute (K := K) (ℓ := ℓ) (f := f)
      (leviSU_mem_leviJ hK hf hζ hσζ P hP
        (diagThreeHom c hc h3 fun i : Fin 4 => y i.succ.succ)))
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h.symm
  rw [vtwPhi_apply]
  exact ((hx.pow_left _).mul_left ((hr.pow_left _).mul_left hs)).eq

theorem vtwV_le : vtwV hK hf hζ hσζ P hP hc h3 hct ≤
    twistedE6Inn K (unitaryInvolution K ℓ f) ⊔ twistedE6Diag K (unitaryInvolution K ℓ f) := by
  rw [← range_twistedE6InndiagConj]
  rintro _ ⟨y, rfl⟩
  exact ⟨_, rfl⟩

theorem vtwPhi_eq_of_eq_one {y : Fin 6 → Multiplicative (ZMod 3)} (h0 : y 0 = 1)
    (h25 : ∀ j : Fin 4, y j.succ.succ = 1) :
    vtwPhi hK hf hζ hσζ P hP hc h3 hct y =
      Subgroup.inclusion (twistedE6RootGroup_le_twistedE6InndiagGL (unitaryInvolution K ℓ f))
        (twE6R0 c hct ^ (Multiplicative.toAdd (y 1)).val) := by
  apply Subtype.ext
  have h25' : (fun j : Fin 4 => y j.succ.succ) = 1 := funext h25
  rw [vtwPhi_apply, h0, h25', toAdd_one, ZMod.val_zero, pow_zero, one_mul, map_one, map_one,
    OneMemClass.coe_one, mul_one]
  rfl

theorem vtwPhi_mulSingle_one :
    vtwPhi hK hf hζ hσζ P hP hc h3 hct (Pi.mulSingle 1 (Multiplicative.ofAdd 1)) =
      Subgroup.inclusion (twistedE6RootGroup_le_twistedE6InndiagGL (unitaryInvolution K ℓ f))
        (twE6R0 c hct) := by
  have h0 : (Pi.mulSingle 1 (Multiplicative.ofAdd 1) : Fin 6 → Multiplicative (ZMod 3)) 0 = 1 :=
    Pi.mulSingle_eq_of_ne (by decide) _
  have h25 : ∀ j : Fin 4,
      (Pi.mulSingle 1 (Multiplicative.ofAdd 1) : Fin 6 → Multiplicative (ZMod 3)) j.succ.succ =
        1 := by
    intro j
    apply Pi.mulSingle_eq_of_ne
    fin_cases j <;> decide
  have h1 : (Multiplicative.toAdd
      ((Pi.mulSingle 1 (Multiplicative.ofAdd 1) : Fin 6 → Multiplicative (ZMod 3)) 1)).val = 1 := by
    rw [Pi.mulSingle_eq_same, toAdd_ofAdd, ZMod.val_one]
  have e := vtwPhi_eq_of_eq_one hK hf hζ hσζ P hP hc h3 hct h0 h25
  rw [h1, pow_one] at e
  exact e

theorem conj_twE6R0_mem_vtwV :
    MulAut.conj (twE6R0 c hct) ∈ vtwV hK hf hζ hσζ P hP hc h3 hct :=
  ⟨Pi.mulSingle 1 (Multiplicative.ofAdd 1),
    (congrArg (twistedE6InndiagConj K (unitaryInvolution K ℓ f))
      (vtwPhi_mulSingle_one hK hf hζ hσζ P hP hc h3 hct)).trans
        (twistedE6InndiagConj_inclusion _ _)⟩

end Phi

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

end
