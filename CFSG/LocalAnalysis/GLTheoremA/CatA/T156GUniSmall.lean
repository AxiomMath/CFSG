module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniGeom
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GDefs
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Timmesfeld.Orders.ClassicalLinearThree
public import Certificates.Certificate16005
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate9124
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156.Uni

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

theorem catalogIs_u3eight {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 3) ^ 2) :
    catalogIs (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ 3))) S9.isU3eight := by
  haveI := Fintype.ofFinite K
  have hK8 : Nat.card K = 8 ^ 2 := by rw [hK]; norm_num
  have hKf : Fintype.card K = 8 ^ 2 := by rw [← Nat.card_eq_fintype_card, hK8]
  obtain ⟨q', hv, -, hq8, ⟨e⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (K := K) (m := 3) (q := 8) hKf le_rfl (by decide)
  have hc := CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.center_statedSU_eq K hK8
    (by norm_num) (by norm_num)
  let e₁ : LargeEvenProj (LargeEvenSUGroup (Fin 3) K 8) ≃*
      ↥(StatedSU 3 8 K) ⧸ Subgroup.center ↥(StatedSU 3 8 K) :=
    (QuotientGroup.quotientMulEquivOfEq hc).symm
  exact ⟨_, by simpa [S9.isU3eight, onLie] using hq8, ⟨e₁.trans e⟩⟩

theorem dvd_sub_one_of_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a)
    (h : p ∣ a ^ p - 1) : p ∣ a - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rw [Nat.cast_sub (Nat.one_le_pow _ _ ha)] at h
  rw [Nat.cast_sub ha]
  push_cast at h ⊢
  rwa [ZMod.pow_card] at h

theorem dvd_add_one_of_dvd_pow_add_one {p : ℕ} (hp : p.Prime) {a : ℕ} (h : p ∣ a ^ p + 1) :
    p ∣ a + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  push_cast at h ⊢
  rwa [ZMod.pow_card] at h

theorem coprime_sq_sub_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.Coprime p ((2 ^ p) ^ 2 - 1) := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
  have h4 : (2 ^ p) ^ 2 = 4 ^ p := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h4] at h
  have h3 := dvd_sub_one_of_dvd_pow_sub_one hp (by norm_num) h
  have : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
  omega

theorem coprime_card_su3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.Coprime p ((2 ^ p) ^ 3 * ((2 ^ p) ^ 2 - 1) * ((2 ^ p) ^ 3 + 1)) := by
  refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ (coprime_sq_sub_one hp hp5)) ?_
  · refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
    rw [← pow_mul] at h
    have h2 := hp.dvd_of_dvd_pow h
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  · refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
    have h8 : (2 ^ p) ^ 3 = 8 ^ p := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h8] at h
    have h9 := dvd_add_one_of_dvd_pow_add_one hp h
    have h3 : p ∣ 3 := hp.dvd_of_dvd_pow (n := 2) (by norm_num at h9 ⊢; exact h9)
    have : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    omega

theorem eq_one_of_pow_eq_one_of_coprime {G : Type*} [Group G] {p : ℕ}
    (hcop : Nat.Coprime p (Nat.card G)) {x : G} (hx : x ^ p = 1) : x = 1 := by
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  have h3 : orderOf x ∣ Nat.gcd p (Nat.card G) := Nat.dvd_gcd h1 h2
  rw [hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

section Triv

variable {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {j : ℕ}

theorem mem_scalars_of_conj_triv (hd : 3 ≤ d) (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    (hdK : (d, 2 ^ j) ≠ (3, 2)) {X : GL (Fin d) K}
    (hmem : ∀ x : LargeEvenSUGroup (Fin d) K (2 ^ j),
      X * (x : GL (Fin d) K) * X⁻¹ ∈ LargeEvenSUGroup (Fin d) K (2 ^ j))
    (htriv : ∀ x : LargeEvenSUGroup (Fin d) K (2 ^ j),
      (QuotientGroup.mk (⟨X * (x : GL (Fin d) K) * X⁻¹, hmem x⟩ :
        LargeEvenSUGroup (Fin d) K (2 ^ j)) : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j))) =
        QuotientGroup.mk x) :
    X ∈ LargeEvenScalars (Fin d) K := by
  have hscalarCenter : LargeEvenScalars (Fin d) K = Subgroup.center (GL (Fin d) K) :=
    largeEvenScalars_def.trans Matrix.GeneralLinearGroup.center_eq_range_scalar.symm
  have hcent : ∀ g ∈ LargeEvenSUGroup (Fin d) K (2 ^ j), ⁅X, g⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro g hg
    have hq := QuotientGroup.eq.mp (htriv ⟨g, hg⟩).symm
    have hz : (g⁻¹ * (X * g * X⁻¹) : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
      rw [← hscalarCenter]
      exact Subgroup.mem_subgroupOf.mp hq
    have h1 : ⁅X, g⁆ = g * (g⁻¹ * (X * g * X⁻¹)) * g⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h1, Subgroup.mem_center_iff.mp hz g]
    simpa using hz
  refine mem_scalars_of_commute_su (k := K) (g := j) hj hK hd (RingHom.id K) fun x hx => ?_
  have hid : Matrix.GeneralLinearGroup.map (RingHom.id K) x = x := by
    apply Units.ext
    ext a b
    rfl
  rw [hid]
  exact LinearFieldFix.commute_of_commutator_mem_center (commutator_su hK hd hdK) hcent hx

theorem uAdj_pow (M : Matrix (Fin d) (Fin d) K) (n : ℕ) : uAdj j (M ^ n) = (uAdj j M) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, uAdj_one]
  | succ n ih => rw [pow_succ, uAdj_mul, ih, pow_succ']

end Triv

section Order

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_of_pow_eq_one_u3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = (2 ^ p) ^ 2)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ p)))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ p)))
      (LargeEvenGUSet (Fin 3) K (2 ^ p)))
    (hφp : φ ^ p = 1) : φ = 1 := by
  obtain ⟨A, hAGU, hA⟩ := hφ
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hq2 : 2 ^ p ≠ 2 := by
    intro h
    have : 2 ^ p = 2 ^ 1 := by rw [h]; norm_num
    have := Nat.pow_right_injective (le_refl 2) this
    omega
  have hdK : (3, 2 ^ p) ≠ (3, 2) := fun h => hq2 (Prod.mk.inj h).2
  have hpowmem : ∀ (m : ℕ) (x : GL (Fin 3) K), x ∈ LargeEvenSUGroup (Fin 3) K (2 ^ p) →
      A ^ m * x * (A ^ m)⁻¹ ∈ LargeEvenSUGroup (Fin 3) K (2 ^ p) := by
    intro m
    induction m with
    | zero =>
        intro x hx
        simpa using hx
    | succ m ih =>
        intro x hx
        have h2 : A ^ (m + 1) * x * (A ^ (m + 1))⁻¹ = A * (A ^ m * x * (A ^ m)⁻¹) * A⁻¹ := by
          group
        rw [h2]
        exact conj_mem_su hAGU (ih x hx)
  have hpowφ : ∀ (m : ℕ) (x : LargeEvenSUGroup (Fin 3) K (2 ^ p)),
      (φ ^ m) (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ p)) x) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ p))
          ⟨A ^ m * (x : GL (Fin 3) K) * (A ^ m)⁻¹, hpowmem m x x.2⟩ := by
    intro m
    induction m with
    | zero =>
        intro x
        rw [pow_zero, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        simp
    | succ m ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, ih x]
        rw [hA ⟨A ^ m * (x : GL (Fin 3) K) * (A ^ m)⁻¹, hpowmem m x x.2⟩
          ⟨A * (A ^ m * (x : GL (Fin 3) K) * (A ^ m)⁻¹) * A⁻¹,
            conj_mem_su hAGU (hpowmem m x x.2)⟩ rfl]
        congr 1
        apply Subtype.ext
        change A * (A ^ m * (x : GL (Fin 3) K) * (A ^ m)⁻¹) * A⁻¹ =
          A ^ (m + 1) * (x : GL (Fin 3) K) * (A ^ (m + 1))⁻¹
        group
  have hXs : A ^ p ∈ LargeEvenScalars (Fin 3) K := by
    refine mem_scalars_of_conj_triv (le_refl 3) hp1 hK hdK (fun x => hpowmem p x x.2) fun x => ?_
    have h1 := hpowφ p x
    rw [hφp, MulAut.one_apply] at h1
    exact h1.symm
  rw [largeEvenScalars_def] at hXs
  obtain ⟨l, hl⟩ := hXs
  have hcopK : Nat.Coprime (Nat.card Kˣ) p := by
    rw [Nat.card_units, hK]
    exact (coprime_sq_sub_one hp hp5).symm
  have hcopK' : Nat.Coprime p (Nat.card Kˣ) := hcopK.symm
  obtain ⟨ν, hν⟩ : ∃ ν : Kˣ, ν ^ p = l :=
    ⟨(powCoprime hcopK).symm l, (powCoprime hcopK).apply_symm_apply l⟩
  set B : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * A with hBdef
  have hBp : B ^ p = 1 := by
    rw [hBdef, Commute.mul_pow (Matrix.GeneralLinearGroup.scalar_commute ν⁻¹ A), ← map_pow,
      ← hl, ← map_mul, inv_pow, hν, inv_mul_cancel, map_one]
  have hBmat : (B : Matrix (Fin 3) (Fin 3) K) = ((ν⁻¹ : Kˣ) : K) • (A : Matrix (Fin 3) (Fin 3) K) := by
    rw [hBdef, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
  have hdetB : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : (Matrix.GeneralLinearGroup.det B) ^ p = 1 := by rw [← map_pow, hBp, map_one]
    have h2 := eq_one_of_pow_eq_one_of_coprime hcopK' h1
    have h3 := congrArg (fun u : Kˣ => (u : K)) h2
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h3
  obtain ⟨μ, hμ0, -, hAμ⟩ := id hAGU
  set μ' : K := ((ν⁻¹ : Kˣ) : K) ^ 2 ^ p * ((ν⁻¹ : Kˣ) : K) * μ with hμ'
  have hμ'0 : μ' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (Units.ne_zero _)) hμ0
  have hBμ : uAdj p (B : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
      μ' • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have hAμ' : uAdj p (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
        μ • (1 : Matrix (Fin 3) (Fin 3) K) := hAμ
    rw [hBmat, uAdj_smul, Matrix.smul_mul, Matrix.mul_smul, hAμ', smul_smul, smul_smul, hμ']
  have hBinv : (B : Matrix (Fin 3) (Fin 3) K) * ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hadjB : uAdj p (B : Matrix (Fin 3) (Fin 3) K) =
      μ' • ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    calc uAdj p (B : Matrix (Fin 3) (Fin 3) K)
        = uAdj p (B : Matrix (Fin 3) (Fin 3) K) *
            ((B : Matrix (Fin 3) (Fin 3) K) * ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
          rw [hBinv, Matrix.mul_one]
      _ = μ' • ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [← Matrix.mul_assoc, hBμ, Matrix.smul_mul, Matrix.one_mul]
  have hBpm : (B : Matrix (Fin 3) (Fin 3) K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hBp, Units.val_one]
  have hBipm : ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hBp, inv_one, Units.val_one]
  have hμ'p : μ' ^ p = 1 := by
    have h1 : uAdj p ((B : Matrix (Fin 3) (Fin 3) K) ^ p) = μ' ^ p • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [uAdj_pow, hadjB, smul_pow, hBipm]
    rw [hBpm, uAdj_one] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa using h2.symm
  have hμ'1 : μ' = 1 := by
    have h1 := eq_one_of_pow_eq_one_of_coprime hcopK' (x := Units.mk0 μ' hμ'0)
      (by apply Units.ext; simpa using hμ'p)
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    simpa using h2
  have hBSU : B ∈ LargeEvenSUGroup (Fin 3) K (2 ^ p) := by
    rw [mem_LargeEvenSU_iff]
    refine ⟨hdetB, ?_⟩
    have := hBμ
    rw [hμ'1, one_smul] at this
    exact this
  have hcardSU : Nat.card ↥(LargeEvenSUGroup (Fin 3) K (2 ^ p)) =
      (2 ^ p) ^ 3 * ((2 ^ p) ^ 2 - 1) * ((2 ^ p) ^ 3 + 1) :=
    CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK
  have hB1 : B = 1 := by
    have h1 : (⟨B, hBSU⟩ : LargeEvenSUGroup (Fin 3) K (2 ^ p)) ^ p = 1 := by
      apply Subtype.ext
      simpa using hBp
    have h2 := eq_one_of_pow_eq_one_of_coprime (hcardSU ▸ coprime_card_su3 hp hp5) h1
    exact congrArg Subtype.val h2
  have hAc : A = Matrix.GeneralLinearGroup.scalar (Fin 3) ν := by
    have h1 : A = Matrix.GeneralLinearGroup.scalar (Fin 3) ν * B := by
      rw [hBdef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [h1, hB1, mul_one]
  refine MulEquiv.ext fun y => ?_
  change φ y = y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 := hA y ⟨A * (y : GL (Fin 3) K) * A⁻¹, conj_mem_su hAGU y.2⟩ rfl
  change φ (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ p)) y) =
    LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ p)) y
  rw [h1]
  congr 1
  apply Subtype.ext
  change A * (y : GL (Fin 3) K) * A⁻¹ = (y : GL (Fin 3) K)
  rw [hAc, Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

theorem fixAlt_u3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = (2 ^ p) ^ 2)
    (x : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ p)))) :
    FixAlt p (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ p)))
      (LargeEvenGUSet (Fin 3) K (2 ^ p))) x := by
  refine Or.inr fun E hE hEx => ?_
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 fun φ hφ =>
    eq_one_of_pow_eq_one_u3 hp hp5 hK (hEx φ hφ).1 (hE.2 φ hφ)
  rw [hbot, Subgroup.card_bot]
  exact hp.one_lt.le

end Order

end CFSG.LocalAnalysis.GLTheoremA.T156.Uni

end
