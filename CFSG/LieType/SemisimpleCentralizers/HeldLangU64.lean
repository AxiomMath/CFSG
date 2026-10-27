module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Red
public import CFSG.LieType.SemisimpleCentralizers.HeldLangPSU
public import CFSG.LieType.SemisimpleCentralizers.HeldLangU64Ord
public import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Fischer.Classification.Recognition
  CFSG.HardMathSupport.Foote.ModuleExclusions

theorem isQuasisimple_of_simple_perfect {X : Type*} [Group X] [IsSimpleGroup X] (hp : Group.IsPerfect X) :
    CFSG.Open.IsQuasisimple X := by
  have hcen : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : X, a * b = b * a := fun a b => (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
      have hbot : commutator X = ⊥ := by
        rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
        intro a _ b _
        rw [Subgroup.mem_bot, commutatorElement_def]
        calc a * b * a⁻¹ * b⁻¹ = b * a * a⁻¹ * b⁻¹ := by rw [hcomm a b]
          _ = 1 := by group
      have htop : commutator X = ⊤ := hp.commutator_eq_top
      rw [hbot] at htop
      obtain ⟨a, b, hab⟩ := exists_pair_ne X
      apply hab
      have h1 : a ∈ (⊥ : Subgroup X) := htop ▸ Subgroup.mem_top a
      have h2 : b ∈ (⊥ : Subgroup X) := htop ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot.1 h1, Subgroup.mem_bot.1 h2]
  exact ⟨hp.commutator_eq_top, ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩

theorem center_eq_bot_of_simple_perfect {X : Type*} [Group X] [IsSimpleGroup X] (hp : Group.IsPerfect X) :
    Subgroup.center X = ⊥ := by
  have hq := isQuasisimple_of_simple_perfect hp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := fun a b => (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
    have hbot : commutator X = ⊥ := by
      rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_def]
      calc a * b * a⁻¹ * b⁻¹ = b * a * a⁻¹ * b⁻¹ := by rw [hcomm a b]
        _ = 1 := by group
    have htop : commutator X = ⊤ := hp.commutator_eq_top
    rw [hbot] at htop
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    apply hab
    have h1 : a ∈ (⊥ : Subgroup X) := htop ▸ Subgroup.mem_top a
    have h2 : b ∈ (⊥ : Subgroup X) := htop ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot.1 h1, Subgroup.mem_bot.1 h2]

theorem exists_isometry_rep {K : Type} [Field K] {d : ℕ} {bar : K ≃+* K} (hbar : IsUnitaryInvolution bar)
    (A : GL (Fin d) K) {μ : K} (hμ0 : μ ≠ 0) (hμ : bar μ = μ)
    (hA : conjTr bar (A : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) = μ • 1) :
    ∃ (A' : GL (Fin d) K) (l : Kˣ), IsIso bar A' ∧
      A = Matrix.GeneralLinearGroup.scalar (Fin d) l * A' := by
  obtain ⟨l₁, hl₁⟩ := hbar.exists_norm (d := μ⁻¹) (by rw [map_inv₀, hμ])
  have hl₁0 : l₁ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hl₁
    exact (inv_ne_zero hμ0) hl₁.symm
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 l₁ hl₁0) * A,
    (Units.mk0 l₁ hl₁0)⁻¹, ?_, ?_⟩
  · unfold IsIso
    rw [coe_scalar_mul, conjTr_smul' bar, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA, smul_smul,
      Units.val_mk0, hl₁, inv_mul_cancel₀ hμ0, one_smul]
  · rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem conj_eq_of_scalar {K : Type} [Field K] {d : ℕ} (l : Kˣ) (A' g : GL (Fin d) K) :
    (Matrix.GeneralLinearGroup.scalar (Fin d) l * A') * g *
      (Matrix.GeneralLinearGroup.scalar (Fin d) l * A')⁻¹ = A' * g * A'⁻¹ := by
  set s := Matrix.GeneralLinearGroup.scalar (Fin d) l
  have hs : ∀ z : GL (Fin d) K, s * z * s⁻¹ = z := fun z => by
    rw [scalar_mul_comm l z, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : (s * A') * g * (s * A')⁻¹ = s * (A' * g * A'⁻¹) * s⁻¹ := by group
  rw [h2, hs]

theorem u64FieldPiece : U64FieldPiece := by
  intro d n K _ _ hcard hd5 h5 hn4 u f hu hf hford huf3 J hJ hJl
  have hn1 : 1 ≤ n := by omega
  have hd1 : 1 ≤ d := by omega
  have hd3 : 3 ≤ d := by omega
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := fun H => by have := H.1; omega
  haveI : NeZero d := ⟨by omega⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdat : UnitaryFieldData 2 n K := unitaryFieldData_of_card hn1 hcard
  haveI : CharP K 2 := hdat.charP
  have hKe : Nat.card K = 2 ^ (2 * n) := by rw [hcard, ← pow_mul, Nat.mul_comm]
  let bar : K ≃+* K := unitaryInvolution K 2 n
  have hbar : IsUnitaryInvolution bar := isUnitaryInvolution_unitaryInvolution hcard
  have hbarapp : ∀ x, bar x = x ^ 2 ^ n := fun x => unitaryInvolution_apply K 2 n x
  have hS : StatedSU d (2 ^ n) K = SUid bar d := (SUid_eq_statedSU hcard d).symm
  have hbarh : ∀ x, hdat.bar x = bar x := fun x => by rw [hbarapp]; rfl
  obtain ⟨A, hA, huA⟩ := hu
  obtain ⟨σ, hfσ⟩ := hf
  have hcomm : ∀ x, σ (bar x) = bar (σ x) := fun x => by rw [hbarapp, hbarapp, map_pow]
  have hfeq : f = uFieldAut hdat hd1 σ := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : (((glAut σ (g : GL (Fin d) K) : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) =
        ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ := rfl
    rw [hfσ g ⟨glAut σ g, uFieldSU_mem hdat σ g⟩ hg]
    exact (uFieldAut_proj hdat hd1 σ g).symm
  have hf3 : (uFieldAut hdat hd1 σ) ^ 3 = 1 := by
    rw [← hfeq, ← hford]
    exact pow_orderOf_eq_one f
  have hσ3 : σ ^ 3 = 1 := by
    have h2 := uFactor_uFieldAut_eq hn1 hcard hd1 hd3 hq (σ ^ 3)
    rw [map_pow, hf3, map_one] at h2
    exact h2.symm
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, map_one] at hfeq
    rw [hfeq, orderOf_one] at hford
    exact absurd hford (by norm_num)
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hodd : Odd (orderOf σ) := by rw [hσord]; decide
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  have hμ : bar μ = μ := by rw [hbarapp]; exact hμq
  have hAconj : conjTr bar (A : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) = μ • 1 := by
    have : (A : Matrix (Fin d) (Fin d) K).map bar = (A : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ n) := by
      ext i j
      simp [hbarapp]
    unfold conjTr
    rw [this]
    exact hAμ
  obtain ⟨A', l, hA', hAA'⟩ := exists_isometry_rep hbar A hμ0 hμ hAconj
  have hmemσ : ∀ x : GL (Fin d) K, x ∈ StatedSU d (2 ^ n) K → glMap σ x ∈ StatedSU d (2 ^ n) K := by
    intro x hx
    rw [hS] at hx ⊢
    exact glMap_mem_SUid hcomm hx
  have hmemT : ∀ x : GL (Fin d) K, x ∈ StatedSU d (2 ^ n) K →
      A' * glMap σ x * A'⁻¹ ∈ StatedSU d (2 ^ n) K := by
    intro x hx
    rw [hS] at hx ⊢
    exact suTwist_mem hcomm hbar.invol hA' hx
  have hcompat : ∀ x x' : ↥(StatedSU d (2 ^ n) K), (x' : GL (Fin d) K) = A' * glMap σ x * A'⁻¹ →
      (u * f) (QuotientGroup.mk x) = QuotientGroup.mk x' := by
    intro x x' hx'
    have hfx : f (QuotientGroup.mk x) = QuotientGroup.mk ⟨glMap σ x, hmemσ x x.2⟩ :=
      hfσ x ⟨glMap σ x, hmemσ x x.2⟩ rfl
    rw [MulAut.mul_apply, hfx]
    exact huA ⟨glMap σ x, hmemσ x x.2⟩ x' (by rw [hx', hAA', conj_eq_of_scalar])
  have hiter : ∀ (k : ℕ) (x : ↥(StatedSU d (2 ^ n) K)), ∃ x' : ↥(StatedSU d (2 ^ n) K),
      (x' : GL (Fin d) K) = (fun z : GL (Fin d) K => A' * glMap σ z * A'⁻¹)^[k] x ∧
      ((u * f) ^ k) (QuotientGroup.mk x) = QuotientGroup.mk x' := by
    intro k
    induction k with
    | zero => intro x; exact ⟨x, rfl, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨xk, hxk, hmk⟩ := ih x
      refine ⟨⟨A' * glMap σ xk * A'⁻¹, hmemT xk xk.2⟩, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', ← hxk]
      · rw [pow_succ', MulAut.mul_apply, hmk]
        exact hcompat xk _ rfl
  have hNiso : IsIso bar (normProd σ A' 3) := hA'.normProd hcomm 3
  have hNmem : normProd σ A' 3 ∈ uU hdat d := by
    rw [mem_uU]
    have : ((normProd σ A' 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map hdat.bar =
        ((normProd σ A' 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map bar := by
      ext i j
      simp [hbarh]
    rw [this]
    exact hNiso
  have hone : uConjAut hdat hd1 ⟨normProd σ A' 3, hNmem⟩ = 1 := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨x', hx'1, hx'2⟩ := hiter 3 x
    have h1 : ((u * f) ^ 3) (QuotientGroup.mk x) = QuotientGroup.mk x := by
      rw [huf3]
      rfl
    have hx'3 : (x' : GL (Fin d) K) = normProd σ A' 3 * (x : GL (Fin d) K) * (normProd σ A' 3)⁻¹ := by
      rw [hx'1, iterate_twist_formula, hσ3, glMap_one]
    calc uConjAut hdat hd1 ⟨normProd σ A' 3, hNmem⟩ (QuotientGroup.mk x)
        = QuotientGroup.mk ⟨_, uConjSU_mem hdat ⟨normProd σ A' 3, hNmem⟩ x⟩ :=
          uConjAut_proj hdat hd1 ⟨normProd σ A' 3, hNmem⟩ x
      _ = QuotientGroup.mk x' := by
          congr 1
          exact Subtype.ext hx'3.symm
      _ = QuotientGroup.mk x := by rw [← hx'2, h1]
      _ = (1 : MulAut (StatedProj (StatedSU d (2 ^ n) K))) (QuotientGroup.mk x) := rfl
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff hdat hd3 ⟨normProd σ A' 3, hNmem⟩).1 hone
  have hcscal : Ai σ (A' : Matrix (Fin d) (Fin d) K) (orderOf σ) = ((c : Kˣ) : K) • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hσord, ← coe_normProd]
    have : (normProd σ A' 3 : GL (Fin d) K) = Matrix.GeneralLinearGroup.scalar (Fin d) c := hc
    rw [this, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hβ' : ∀ x x' : ↥(StatedSU d (2 ^ n) K), (x' : GL (Fin d) K) = A' * glMap σ x * A'⁻¹ →
      (u * f).toMonoidHom (QuotientGroup.mk x) = QuotientGroup.mk x' := fun x x' h => hcompat x x' h
  obtain ⟨Y, hYC, hYn, hCY, ⟨eY⟩⟩ := exists_psu_fix_of_eq (p := 2) (e := 2 * n) Nat.prime_two (by omega) hKe
    hbar hcomm hodd (StatedSU d (2 ^ n) K) hS A' hA' hcscal (u * f).toMonoidHom hβ'
  obtain ⟨j, hj2, hjcard, hform⟩ := exists_barFix_eq (p := 2) (e := 2 * n) Nat.prime_two (by omega) hKe hbar
    hcomm hodd
  have hF0 := card_fixField (p := 2) (e := 2 * n) Nat.prime_two (by omega) hKe σ
  haveI : Finite (fixField σ) := CFSG.Semidihedral.FixedFieldData.finite_of_prime_power_card _ Nat.prime_two hF0
  haveI : CharP (fixField σ) 2 :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card _ Nat.prime_two hF0
  have hbF := isUnitaryInvolution_barFix (p := 2) (e := 2 * n) Nat.prime_two (by omega) hKe hbar hcomm hodd
  have hsimp : IsSimpleGroup (StatedProj (SUid (barFix σ bar hcomm hbar.invol) d)) :=
    isSimpleGroup_statedProj_SUid hbF hd3 (fun h => absurd h (by omega))
  have hperfSU : Group.IsPerfect (SUid (barFix σ bar hcomm hbar.invol) d) :=
    isPerfect_SUid hbF hd3 (fun h => absurd h (by omega))
  have hperf : Group.IsPerfect (StatedProj (SUid (barFix σ bar hcomm hbar.invol) d)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI := hsimp
  haveI hYsimp : IsSimpleGroup ↥Y := eY.isSimpleGroup
  have hYperf : Group.IsPerfect ↥Y :=
    Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
  have hYq : CFSG.Open.IsQuasisimple ↥Y := isQuasisimple_of_simple_perfect hYperf
  obtain ⟨hJle, hJsub, -, -⟩ := hJ
  have hJq : CFSG.Open.IsQuasisimple ↥J := hasLabel_isQuasisimple hJl
  have hJY : J ≤ Y :=
    (IsQuasisimple.le_commutator hJq).trans ((Subgroup.commutator_mono hJle hJle).trans hCY)
  have hJYsub : CFSG.Open.IsSubnormal J Y := by
    have := CFSG.Fischer.Classification.Recognition.IsSubnormal.inf_normal hJsub hYC hYn
    rwa [inf_eq_left.2 hJY] at this
  have hJeq : J = Y := IsComponentOf.eq_of_isQuasisimple ⟨hJY, hJYsub, hJq⟩ hYq
  subst hJeq
  have hZJ : Subgroup.center ↥J = ⊥ := center_eq_bot_of_simple_perfect hYperf
  obtain ⟨K₅, _, _, hK₅, ⟨e5⟩⟩ := model_twA hZJ hJl (rfl : (⟨.twA, 4, 2⟩ : GLALabel).tag = .twA)
  have hK₅' : Nat.card K₅ = (2 ^ 2) ^ 2 := hK₅
  have e5' : ↥J ≃* StatedProj (StatedSU 5 (2 ^ 2) K₅) := e5
  have hP0card : Nat.card (StatedProj (SUid (barFix σ bar hcomm hbar.invol) d)) =
      Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K₅)) :=
    Nat.card_congr (eY.symm.toEquiv.trans e5'.toEquiv)
  have hbeq : barFix σ bar hcomm hbar.invol = unitaryInvolution (fixField σ) 2 j :=
    RingEquiv.ext fun x => by rw [hform x, unitaryInvolution_apply]
  have hSUeq : SUid (barFix σ bar hcomm hbar.invol) d = StatedSU d (2 ^ j) (fixField σ) := by
    rw [hbeq]
    exact SUid_eq_statedSU hjcard d
  have hcardP0 : Nat.card (StatedProj (SUid (barFix σ bar hcomm hbar.invol) d)) =
      Nat.card (StatedProj (StatedSU d (2 ^ j) (fixField σ))) := by rw [hSUeq]
  have hσord' := hσord
  have hj1 : 1 ≤ j := by rw [hσord] at hj2; omega
  have hv1 := padicValNat_card_psu hj1 hd1 hjcard
  have hv2 := padicValNat_card_psu (a := 2) (d := 5) (K := K₅) (by norm_num) (by norm_num) hK₅'
  have heq : j * (d * (d - 1) / 2) = 20 := by
    have h := congrArg (padicValNat 2) (hcardP0.symm.trans hP0card)
    rw [hv1, hv2] at h
    simpa using h
  obtain ⟨hd5', hj2'⟩ := eq_of_mul_eq_twenty hd5 hj1 heq
  refine ⟨?_, hd5'⟩
  have hdvd := orderOf_dvd_of_card (p := 2) (e := 2 * n) Nat.prime_two (by omega) hKe σ
  rw [hσord] at hdvd hj2
  omega

end CFSG.LieType.SemisimpleCentralizers.HeldLang
