module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311j
public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6CoverTw
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Lines
public import CFSG.LieType.SeitzGeneration.ExcHigh.CubePlanes
public import CFSG.LieType.SeitzGeneration.QuasiHighClassical
public import CFSG.HardMathSupport.Lang.TwE6Step3.D4LinesMain
public import CFSG.HardMathSupport.Lang.TwE6Step3.Assembly
public import CFSG.HardMathSupport.Lang.TwE6Step3.Lines
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest7
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Cases
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Kill
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShell
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShellGl
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHKey
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSmall
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenReps
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Reduce
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26AutMain
public import CFSG.LargeExtraspecial.S8CBFCrit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141f2
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Auto
public import CFSG.Quasithin.SteinbergCBGDTrace
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.LayerEngineG
public import CFSG.RankThree.PartTwo.KFacts.AutPSUDet

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311j

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section E6SixR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective adjEmb_mem
  adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff twistedTorusOf
  twistedFixedPoints mem_twistedFixedPoints subtorusSigma subtorusSigma_le_twistedTorusOf
  pow_eq_one_of_orderOf_rootDiagUnit ne_one_of_orderOf_rootDiagUnit)

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false

theorem not_isSolvable_rClosure_of_quasisimple_le_range {G M : Type} [Group G] [Group M] [Finite G]
    {x : G} (ψ : Subgroup.centralizer ({x} : Set G) →* M) (hψ : Function.Injective ψ)
    {Pt : Subgroup M} (hPq : CFSG.IsQuasisimple Pt) (hPle : Pt ≤ ψ.range) {r : ℕ} [Fact r.Prime]
    (hdvd : r ∣ Nat.card Pt) :
    ¬ Group.IsSolvable ↥(Subgroup.closure {y : G | Commute y x ∧ ∃ m : ℕ, y ^ (r ^ m) = 1}) := by
  classical
  intro hsol
  haveI : Finite Pt := by
    haveI : Finite ψ.range := Set.Finite.to_subtype (Set.finite_range ψ)
    exact Finite.of_injective _ (Subgroup.inclusion_injective hPle)
  have hPr := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.le_closure_pow_of_quasisimple
    (r := r) hPq hdvd
  have hPS : Pt ≤ (Subgroup.closure {y : Subgroup.centralizer ({x} : Set G) |
      ∃ m : ℕ, y ^ (r ^ m) = 1}).map ψ := by
    refine hPr.trans ((Subgroup.closure_le _).2 ?_)
    rintro w ⟨hwP, n, hn⟩
    obtain ⟨y, rfl⟩ := hPle hwP
    refine ⟨y, Subgroup.subset_closure ⟨n, hψ ?_⟩, rfl⟩
    rw [map_pow, map_one]
    exact hn
  have hSsol : Group.IsSolvable ↥(Subgroup.closure {y : Subgroup.centralizer ({x} : Set G) |
      ∃ m : ℕ, y ^ (r ^ m) = 1}) := by
    have hle : (Subgroup.closure {y : Subgroup.centralizer ({x} : Set G) |
        ∃ m : ℕ, y ^ (r ^ m) = 1}).map (Subgroup.centralizer ({x} : Set G)).subtype ≤
        Subgroup.closure {y : G | Commute y x ∧ ∃ m : ℕ, y ^ (r ^ m) = 1} := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨y, ⟨n, hn⟩, rfl⟩
      have hyc : Commute (y : G) x := Subgroup.mem_centralizer_singleton_iff.1 y.2
      refine ⟨hyc, n, ?_⟩
      rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hn, Subgroup.coe_one]
    have hf : Function.Injective ((Subgroup.inclusion hle).comp
        (Subgroup.equivMapOfInjective _ _
          (Subgroup.centralizer ({x} : Set G)).subtype_injective).toMonoidHom) :=
      (Subgroup.inclusion_injective hle).comp (MulEquiv.injective _)
    haveI := hsol
    exact solvable_of_solvable_injective hf
  have hmapsol : Group.IsSolvable ↥((Subgroup.closure {y : Subgroup.centralizer ({x} : Set G) |
      ∃ m : ℕ, y ^ (r ^ m) = 1}).map ψ) := by
    haveI := hSsol
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective _ ψ hψ).toMonoidHom)
      (MulEquiv.surjective _)
  have hPsol : Group.IsSolvable ↥Pt := by
    haveI := hmapsol
    exact solvable_of_solvable_injective (Subgroup.inclusion_injective hPS)
  exact CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.not_isSolvable_of_isQuasisimple' hPq hPsol

theorem ringChar_dvd_card_phi6Qθ_of_A2 {K : Type} [Field K] [Finite K] {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {Fr : Ω →+* Ω} {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorus (phi6N Ω) Fr) (hxp : orderOf x = p)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    ℓ ∣ Nat.card ↥(phi6Qθ Ω Fr (torusRootKernel x)) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨-, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi6TorusTorsion Ω Fr p := ⟨hx, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hQ₁, π, hθ⟩ := phi6_A2_transport hp3 hFr hζ hr hxT hx1 hA2
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_reversing_of_theta hFrs
    (phi6ThetaConj Ω Fr w) (phi6ThetaConj_injective w) π hθ
  obtain ⟨e, -⟩ := exists_mulEquiv_fixSubgroup6 hQ₁ hmaps Φ hΦ₀
  obtain ⟨-, ⟨H', hH'⟩, -, -, -⟩ := sln_root_permuting_frobenius_fixed_unitary hℓ hf hK
    (le_refl 3) π Φ b (fun i j hij t => by rw [hΦt, hFr])
  have hcard := CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_card_eq_of_conj (fixSubgroup Φ)
    (unitarySet (ℓ ^ f) 3) (fun Y hY => hY.2.1) H' hH'
  have h3 := TwCardAux.card_unitarySet_three (Ω := Ω) (ℓ := ℓ) hf
  rw [show phi6Qθ Ω Fr (torusRootKernel x) =
      rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ (phi6Theta Ω Fr).eqLocus (MonoidHom.id _) from rfl,
    Nat.card_congr e.toEquiv, hcard, h3]
  exact dvd_mul_of_dvd_left (dvd_pow (dvd_pow_self ℓ (by omega)) (by norm_num)) _

theorem ringChar_dvd_card_phi6P_of_A2A2 {K : Type} [Field K] [Finite K] {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {Fr : Ω →+* Ω} {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorus (phi6N Ω) Fr) (hxp : orderOf x = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    ℓ ∣ Nat.card ↥(phi6P Ω Fr (torusRootKernel x)) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨-, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi6TorusTorsion Ω Fr p := ⟨hx, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hQ₁₂, π, π', h12, h21⟩ := phi6_A2A2_transport hp3 hFr hζ hr hxT hx1 hA2A2
  obtain ⟨θ, hθ, a, b, hab⟩ := exists_exchanged_layer_pos hFrs (phi6ThetaConj Ω Fr w)
    (phi6ThetaConj_injective w) π π' h12 h21
  obtain ⟨k₂, -, h₁, h₂, ψ, -, hψfix, -, -, hψ1, -, -, -, -, -, hder9⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.exchanged_sl3_central_product_frobenius_full_fixed_layer hℓ hf hK Fr
      hFr twoA2MulSup twoA2MulSup_surjective (fun xy => twoA2MulSup_eq_one_iff xy.1 xy.2) θ a b hab
  set Y := phi6Qθ Ω Fr (torusRootKernel x) with hYdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hYF : Y.map (MulAut.conj n).toMonoidHom =
      (fixSubgroup θ).map (subsystemGroup Tag.E6 Ω support13 ⊔
        subsystemGroup Tag.E6 Ω support56).subtype :=
    map_conj_phi6Qθ hQ₁₂ θ hθ
  let F : ↥(subsystemGroup Tag.E6 Ω support13 ⊔ subsystemGroup Tag.E6 Ω support56) →*
      ModGL Tag.E6 Ω := (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _)
  have hF : Function.Injective F := (MulAut.conj n).symm.injective.comp Subtype.val_injective
  have hYf : (fixSubgroup θ).map F = Y := by
    have hid : (MulAut.conj n).symm.toMonoidHom.comp (MulAut.conj n).toMonoidHom =
        MonoidHom.id _ := MonoidHom.ext fun y => by simp
    rw [show F = (MulAut.conj n).symm.toMonoidHom.comp (Subgroup.subtype _) from rfl,
      ← Subgroup.map_map, ← hYF, Subgroup.map_map, hid, Subgroup.map_id]
  set ψ' : SL(3, ↥k₂) →* ModGL Tag.E6 Ω := F.comp ψ with hψ'def
  have hder' : ⁅fixSubgroup θ, fixSubgroup θ⁆ = ψ.range := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hψfix, ← hder9, commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hrange : ψ'.range = ⁅Y, Y⁆ := by
    rw [← hYf, ← Subgroup.map_commutator, hder', MonoidHom.range_comp]
  haveI : CharP ↥k₂ ℓ := (RingHom.charP_iff_charP (algebraMap ↥k₂ Ω) ℓ).2 inferInstance
  set A : SL(3, ↥k₂) := Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1 with hA
  have hAℓ : A ^ ℓ = 1 := by
    have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.transvection_pow_ringChar
      (show (0 : Fin 3) ≠ 1 by decide) (1 : ↥k₂)
    rwa [ringChar.eq ↥k₂ ℓ] at h
  have hψA : ψ A ≠ 1 := by
    rw [ne_eq, hψ1]
    rintro ⟨c, -, hc⟩
    have h01 := congrFun (congrFun hc 0) 1
    simp [Matrix.SpecialLinearGroup.map_apply_coe, hA, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.scalar_apply, Matrix.one_apply, Matrix.single_apply] at h01
  have hψ'A : ψ' A ≠ 1 := fun h => hψA (hF (h.trans (map_one F).symm))
  have hmem : ψ' A ∈ phi6P Ω Fr (torusRootKernel x) := by
    rw [show phi6P Ω Fr (torusRootKernel x) = ⁅Y, Y⁆ from rfl, ← hrange]
    exact ⟨A, rfl⟩
  have hord : orderOf (⟨ψ' A, hmem⟩ : ↥(phi6P Ω Fr (torusRootKernel x))) = ℓ := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hAℓ, map_one]
    · intro h
      exact hψ'A (congrArg Subtype.val h)
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem exists_offLine_rgen_E6_phi6 (K : Type) [Field K] [Finite K] (hK3 : 3 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 6)
    (E : Subgroup (adjointGroup .E6 K)) (hEc : Nat.card E = p ^ 2) (hEp : ∀ x ∈ E, x ^ p = 1)
    {a b : adjointGroup .E6 K} (haE : a ∈ E) (hbE : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
      ¬ Group.IsSolvable ↥(Subgroup.closure {y : adjointGroup .E6 K | Commute y e ∧
        ∃ m : ℕ, y ^ (ringChar K ^ m) = 1}) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  obtain ⟨ℓ, f, hℓ', hchar, hf, hK⟩ := exists_char_pow K
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : Fintype K := Fintype.ofFinite K
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  have hring : ringChar K = ℓ := ringChar.eq K ℓ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr c
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hΦ' : ((Nat.card K : ℕ) : ZMod p) ^ 2 - ((Nat.card K : ℕ) : ZMod p) + 1 = 0 :=
    phi6_of_orderOf hord
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact hΦ'
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    rw [hK] at hpq
    exact hpq
  obtain ⟨hpL, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq'
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E6) := by
    have : Fintype (WeylGroup Tag.E6) := Fintype.ofFinite _
    have hp7 : 7 ≤ p := (e6Six_data hp hp3 hpq).2.2.2.2.1
    rw [(CFSG.RankThree.Chevalley.E6_weyl_length_polynomial).2]
    intro hd
    have h51840 : p ∣ 2 ^ 7 * 3 ^ 4 * 5 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp).1 h51840 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
      · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := e6_six_frame K hf hK hp hp3 hpq L
  have htri : ∀ h : ModGL Tag.E6 L, h ∈ phi6TorusTorsion L Fr p → h ≠ 1 →
      torusRootKernel h = ∅ ∨
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 support13) ∨
      ∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel h = parabolicRoots Tag.E6 supportA2A2 := by
    intro h hhT hh1
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨⟨a, a'⟩, hab⟩ := (mem_phi6TorusTorsion_iff hFr hζ hr h).1 hhT
    have hab0 : (a, a') ≠ 0 := fun h0 => hh1 (by rw [← hab, h0, ofAdd_zero, map_one])
    have hker0 : torusRootKernel h = rootKernel (eisensteinColumn (((ℓ ^ f : ℕ)) : ZMod p) a a') := by
      rw [← hab]
      exact torusRootKernel_phi3TorsionHom hζ _ a a'
    rw [hker0]
    exact rootKernel_eisenstein_trichotomy hp3 hr hab0
  have hbound : ∀ b : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 b ∈ twistedTorusOf (phi6N L)
      (Units.map (entrywiseHom Fr)) → (∀ i, b i ^ p = 1) → b ≠ 1 →
      (rootCharKernel b).ncard ≤ 12 := by
    intro b hbT hbp hb1
    have hhp : rootDiagUnit .E6 b ^ p = 1 := by
      have h1 : rootDiagUnit .E6 (b ^ p) = rootDiagUnit .E6 b ^ p :=
        ((rootDiagUnitHom .E6 L).map_pow b p)
      have h2 : b ^ p = 1 := funext fun i => by simpa using hbp i
      rw [← h1, h2, rootDiagUnit_one]
    have hh1 : rootDiagUnit .E6 b ≠ 1 := fun h => hb1 (by
      apply rootDiagUnit_injective (τ := .E6) (K := L)
      rw [h, rootDiagUnit_one])
    have hkb : torusRootKernel (rootDiagUnit .E6 b) = rootCharKernel b :=
      torusRootKernel_rootDiagUnit b
    rcases htri _ ⟨hbT, hhp⟩ hh1 with h0 | ⟨w, hw⟩ | ⟨w, hw⟩
    · rw [hkb] at h0
      rw [h0, Set.ncard_empty]
      omega
    · rw [hkb] at hw
      have := Set.ncard_image_of_injective (rootCharKernel b) (MulAction.injective w)
      rw [hw, ncard_parabolicRoots_support13] at this
      omega
    · rw [hkb] at hw
      have := Set.ncard_image_of_injective (rootCharKernel b) (MulAction.injective w)
      rw [hw, ncard_parabolicRoots_supportA2A2] at this
      omega
  have hperx : ∀ (x c : adjointGroup .E6 K) (b : Fin Tag.E6.rank → Lˣ), orderOf x = p →
      g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf (phi6N L)
        (Units.map (entrywiseHom Fr)) →
      rootDiagUnit .E6 b = g0⁻¹ * adjEmb .E6 K L (c * x * c⁻¹) * g0 →
      (rootCharKernel b).Nonempty →
      ¬ Group.IsSolvable ↥(Subgroup.closure {y : adjointGroup .E6 K | Commute y x ∧
        ∃ m : ℕ, y ^ (ringChar K ^ m) = 1}) := by
    intro x c b hx hh hb hne
    set ι : adjointGroup .E6 K →* ModGL .E6 L := adjEmb .E6 K L with hιdef
    set h : ModGL .E6 L := g0⁻¹ * ι (c * x * c⁻¹) * g0 with hhdef
    have hordh : orderOf h = p := by
      have e1 : orderOf h = orderOf (ι (c * x * c⁻¹)) := by
        have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
          (ι (c * x * c⁻¹))
        rw [hhdef]
        simpa [MulAut.conj_apply] using this
      have e2 : orderOf (ι (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
        orderOf_injective ι adjEmb_injective _
      have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
        simpa [MulAut.conj_apply] using this
      rw [e1, e2, e3, hx]
    have hhp : h ^ p = 1 := hordh ▸ pow_orderOf_eq_one h
    have hh1 : h ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hordh
      exact hp.one_lt.ne hordh
    have hhT : h ∈ phi6TorusTorsion L Fr p := ⟨hh, hhp⟩
    have hkb : torusRootKernel h = rootCharKernel b := by
      rw [← hb]
      exact torusRootKernel_rootDiagUnit b
    have hrootneg : ∀ α ∈ torusRootKernel h, -α ∈ torusRootKernel h := fun α hα => by
      rw [hkb] at hα ⊢
      exact ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
    have hNorm : torusGroup .E6 L ⊔ rootSpan .E6 L (torusRootKernel h) ≤
        Subgroup.normalizer (rootSpan .E6 L (torusRootKernel h) : Set (ModGL .E6 L)) :=
      torusGroup_sup_rootSpan_le_normalizer fun α hα => hα.1
    have finish : ∀ (S : Set (Fin Tag.E6.rank → ℤ)) (hS : ∀ α ∈ S, IsRoot Tag.E6 α)
        (hSn : ∀ α ∈ S, -α ∈ S) (hSeq : S = torusRootKernel h)
        (P : Subgroup (ModGL .E6 L)) (hPfin : Finite P)
        (hPq : CFSG.IsQuasisimple P) (hPdvd : ℓ ∣ Nat.card P) (hPQ : P ≤ rootSpan .E6 L S)
        (hPR : P ≤ twistedFixedPoints (phi6N L) (Units.map (entrywiseHom Fr)))
        (hPadj : P ≤ adjointGroup .E6 L)
        (hPnorm : ∀ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S,
          y ∈ twistedFixedPoints (phi6N L) (Units.map (entrywiseHom Fr)) →
          ∀ u ∈ P, y * u * y⁻¹ ∈ P)
        (hPcent : ∀ y ∈ torusGroup .E6 L ⊔ rootSpan .E6 L S,
          y ∈ twistedFixedPoints (phi6N L) (Units.map (entrywiseHom Fr)) →
          (∀ u ∈ P, y * u = u * y) →
          y ∈ subtorusSigma (phi6N L) (Units.map (entrywiseHom Fr)) S),
        ¬ Group.IsSolvable ↥(Subgroup.closure {y : adjointGroup .E6 K | Commute y x ∧
          ∃ m : ℕ, y ^ (ringChar K ^ m) = 1}) := by
      intro S hS hSn hSeq P hPfin hPq hPdvd hPQ hPR hPadj hPnorm hPcent
      have hcS : c * x * c⁻¹ ∈ subtorusImage ι g0
          (subtorusSigma (phi6N L) (Units.map (entrywiseHom Fr)) S) := by
        rw [mem_subtorusImage_iff]
        refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
        have hle := rootSpan_le_centralizer (K := L) b (S := S) (by
          rw [hSeq, hkb])
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
        rw [hb] at h1
        exact h1
      have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ,
          rootDiagUnit .E6 a = g0⁻¹ * ι (c * x * c⁻¹) * g0 → rootCharKernel a ⊆ S :=
        fun a ha => by
          have : a = b := rootDiagUnit_injective (ha.trans hb.symm)
          rw [this, hSeq, hkb]
      obtain ⟨ψ, hψinj, -, -, -, -, hPψ, -⟩ := sigma_embedding_data (ι' := Unit) ι
        adjEmb_injective adjEmb_mem (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFrK)
        (phi6N L) g0 hg0C hg0 hperf hp hordW hS hSn (fun _ => P) (fun _ => hPfin)
        (fun _ => hPq) (fun _ => hPQ) (fun _ => hPR) (fun _ => hPadj)
        (fun _ y hy hyR u hu => hPnorm y hy hyR u hu)
        (fun y hy hyR hc => hPcent y hy hyR (fun u hu => hc () u hu)) hx c hcS hkerZ
      haveI : Fact (ringChar K).Prime := ⟨hring ▸ hℓ⟩
      exact not_isSolvable_rClosure_of_quasisimple_le_range ψ hψinj hPq (hPψ ()) (by rw [hring]; exact hPdvd)
    rcases htri h hhT hh1 with hreg | hA2 | hA2A2
    · exfalso
      rw [hkb] at hreg
      exact Set.not_nonempty_empty (hreg ▸ hne)
    ·
      obtain ⟨hfin, hqs, -, hC6, hcentQ⟩ := phi6_A2_case (K := K) hℓ hf hK hFr hp hp3 hpq' hh
        hordh hA2
      have hdvd := ringChar_dvd_card_phi6Qθ_of_A2 (K := K) hℓ hf hK hFr hp hp3 hpq' hh hordh hA2
      refine finish (torusRootKernel h) (fun α hα => (by rw [hkb] at hα; exact hα.1)) hrootneg
        rfl (phi6Qθ L Fr (torusRootKernel h)) hfin hqs hdvd inf_le_left inf_le_right
        (inf_le_left.trans (rootSpan_le_adjointGroup L _))
        (fun y hy hyR u hu => phi6Qθ_conj_mem (hNorm hy) hyR hu) (fun y hy hyR hc => ?_)
      have hyH : y ∈ torusGroup .E6 L := hC6 ⟨hy, Subgroup.mem_centralizer_iff.2 fun u hu =>
        (hc u hu).symm⟩
      have hcent := hcentQ y hyH (fun u hu => hc u hu)
      exact Subgroup.mem_inf.2 ⟨mem_twistedTorus.2 ⟨hyH, mem_twistedFixedPoints.1 hyR⟩,
        Subgroup.mem_centralizer_iff.2 fun g hg => (hcent g hg).symm⟩
    ·
      obtain ⟨hfin, hqs, -, -, -, hC6, hcentQ⟩ := phi6_A2A2_case (K := K) hℓ hf hK hFr hp hp3
        hpq' hh hordh hA2A2
      have hdvd := ringChar_dvd_card_phi6P_of_A2A2 (K := K) hℓ hf hK hFr hp hp3 hpq' hh hordh hA2A2
      refine finish (torusRootKernel h) (fun α hα => (by rw [hkb] at hα; exact hα.1)) hrootneg
        rfl (phi6P L Fr (torusRootKernel h)) hfin hqs hdvd ((phi6P_le _).trans inf_le_left)
        ((phi6P_le _).trans inf_le_right)
        ((phi6P_le _).trans (inf_le_left.trans (rootSpan_le_adjointGroup L _)))
        (fun y hy hyR u hu => phi6P_conj_mem (hNorm hy) hyR hu) (fun y hy hyR hc => ?_)
      have hyH : y ∈ torusGroup .E6 L := hC6 ⟨hy, Subgroup.mem_centralizer_iff.2 fun u hu =>
        (hc u hu).symm⟩
      have hcent := hcentQ y hyH (fun u hu => hc u hu)
      exact Subgroup.mem_inf.2 ⟨mem_twistedTorus.2 ⟨hyH, mem_twistedFixedPoints.1 hyR⟩,
        Subgroup.mem_centralizer_iff.2 fun g hg => (hcent g hg).symm⟩
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311g.exists_offLine_rgen_of_kernel
    (Units.map (entrywiseHom Fr)) (phi6N L) g0 hp hconj 12
    (by rw [card_rootFinset_E6]; norm_num) hbound hperx E hEc hEp haE hbE ha1 hb1

end E6SixR

section E6SixX2R

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints adjEmb
  exists_finite_field_isAlgClosure exists_aut_of_rootData_n)

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux (UFrame fixedRootGroup frame_card_dvd
  hrat_perfect exists_prime_pow_card charP_langLevi units_map_comp frobenius_bijective')

open CFSG.RankThree.Classical2 (fixSubgroup)

open Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem ringChar_dvd_card_frame_of_exchange {τ : Tag} {K : Type} [Field K]
    [Finite K] {w : WeylGroup τ} (D : LangLevi τ K w) {S Sa Sb : Set (Fin τ.rank → ℤ)}
    (Ea : UFrame τ D.L 3 Sa) (hSaroot : ∀ α ∈ Sa, IsRoot τ α)
    (hab : ∀ α ∈ Sa, w • α ∈ Sb)
    (hsq : ∀ i j : Fin 3, i ≠ j → w • (w • Ea.r i j) = Ea.r i j)
    (hS : rootSpan τ D.L S = rootSpan τ D.L Sa ⊔ rootSpan τ D.L Sb)
    (hcomm : ∀ x ∈ rootSpan τ D.L Sa, ∀ y ∈ rootSpan τ D.L Sb, x * y = y * x)
    (hrat : ∀ P : Subgroup (ModGL τ D.L), Finite P → P ≤ adjointGroup τ D.L →
      (∀ x ∈ P, Units.map (entrywiseHom D.Fr) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb τ K D.L).range) :
    ringChar K ∣ Nat.card ↥(D.frame S) := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨ℓ, f, hℓ, hf, hkK⟩ := exists_prime_pow_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP D.L ℓ := charP_langLevi D hℓ hkK
  have hKℓ : ringChar K = ℓ := by
    haveI : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (k := f) hf hkK
    exact ringChar.eq K ℓ
  set n := canonicalRep (coxeterSystem τ) D.L w with hn
  set Φ : ModGL τ D.L →* ModGL τ D.L := Units.map (entrywiseHom D.Fr) with hΦ
  have hnm : n ∈ monomialSubgroup τ D.L := canonicalRep_mem_monomialSubgroup D.L w
  have hwn : weylQuotientHom τ D.L ⟨n, hnm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hΦn : Φ n = n :=
    entrywise_canonicalRep (RingEquiv.ofBijective D.Fr (frobenius_bijective' D)) w
  let T : ModGL τ D.L →* ModGL τ D.L := (MulAut.conj n).toMonoidHom.comp Φ
  have hT : ∀ x, T x = n * Φ x * n⁻¹ := fun x => by simp [T, MulAut.conj_apply]
  have hTab : ∀ x ∈ rootSpan τ D.L Sa, T x ∈ rootSpan τ D.L Sb := fun x hx => by
    rw [hT]
    exact CFSG.RankThree.PartOne.TCX.E.twist_rootSpan_le_w D.Fr n hnm hSaroot
      (fun α hα => by rw [hwn]; exact hab α hα) x hx
  have hΦΦ : ∀ x, Φ (Φ x) = Units.map (entrywiseHom (D.Fr.comp D.Fr)) x := fun x =>
    units_map_comp D.Fr D.Fr x
  have hTT : ∀ x, T (T x) =
      (n * n) * Units.map (entrywiseHom (D.Fr.comp D.Fr)) x * (n * n)⁻¹ := by
    intro x
    rw [hT, hT, map_mul, map_mul, map_inv, hΦn, hΦΦ]
    group
  have hFr₂bij : Function.Bijective (D.Fr.comp D.Fr) :=
    (frobenius_bijective' D).comp (frobenius_bijective' D)
  have hn₂m : n * n ∈ monomialSubgroup τ D.L := mul_mem hnm hnm
  have hwn₂ : weylQuotientHom τ D.L ⟨n * n, hn₂m⟩ = w * w := by
    have : (⟨n * n, hn₂m⟩ : ↥(monomialSubgroup τ D.L)) = ⟨n, hnm⟩ * ⟨n, hnm⟩ := rfl
    rw [this, map_mul, hwn]
  have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : D.Lˣ, ∀ c : D.L,
      (n * n) * pinnedX τ D.L (Ea.r i j) c * (n * n)⁻¹ =
        pinnedX τ D.L (Ea.r ((fun i j => (i, j)) i j).1 ((fun i j => (i, j)) i j).2) ((b : D.L) * c) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn₂m (Ea.isRoot i j hij)
    refine ⟨μ, fun c => ?_⟩
    rw [hμ c, hwn₂, mul_smul, hsq i j hij]
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n Ea.ρ Ea.inj Ea.r Ea.ε Ea.gen
    (D.Fr.comp D.Fr) hFr₂bij (n * n) (fun i j => (i, j)) (fun i j hij => hij)
    (fun i j hij => ⟨i, j, hij, rfl⟩) hconj
  obtain ⟨K₂, _, _, hK₂ac, hK₂card⟩ := exists_finite_field_isAlgClosure ℓ (2 * f) (by omega) K D.L
  haveI : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂card]
    exact pow_ne_zero _ hℓ.ne_zero)
  haveI : CharP K₂ ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
    (k := 2 * f) (by omega) hK₂card
  have hshape' : ∀ (i j : Fin 3) (hij : i ≠ j) (t : D.L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, D.L)) :
        Matrix (Fin 3) (Fin 3) D.L) =
      1 + Matrix.single ((Equiv.refl (Fin 3)) i) ((Equiv.refl (Fin 3)) j)
        ((b i j : D.L) * t ^ ℓ ^ (2 * f)) := by
    intro i j hij t
    rw [hshape i j hij t]
    have : (D.Fr.comp D.Fr) t = t ^ ℓ ^ (2 * f) := by
      rw [RingHom.comp_apply, D.hFr, D.hFr, hkK, ← pow_mul, ← pow_add, two_mul]
    rw [this]
    rfl
  obtain ⟨-, ⟨H, hH⟩, hfin, hq, -, -⟩ :=
    CFSG.RankThree.Classical2.sln_root_permuting_frobenius_fixed_split (k := K₂)
      (Ω := D.L) hℓ (by omega : 1 ≤ 2 * f) hK₂card (by norm_num : 3 ≤ 3) (Equiv.refl (Fin 3)) Φ' b
      hshape'
  have hρSa : ∀ X, Ea.ρ X ∈ rootSpan τ D.L Sa := fun X => by
    rw [← Ea.range]
    exact ⟨X, rfl⟩
  let θ : SL(3, D.L) →* ModGL τ D.L :=
    { toFun := fun X => Ea.ρ X * T (Ea.ρ X)
      map_one' := by simp
      map_mul' := fun X Y => by
        have hc : Ea.ρ Y * T (Ea.ρ X) = T (Ea.ρ X) * Ea.ρ Y :=
          hcomm _ (hρSa Y) _ (hTab _ (hρSa X))
        show Ea.ρ (X * Y) * T (Ea.ρ (X * Y)) = Ea.ρ X * T (Ea.ρ X) * (Ea.ρ Y * T (Ea.ρ Y))
        rw [map_mul, map_mul]
        calc Ea.ρ X * Ea.ρ Y * (T (Ea.ρ X) * T (Ea.ρ Y))
            = Ea.ρ X * (Ea.ρ Y * T (Ea.ρ X)) * T (Ea.ρ Y) := by group
          _ = Ea.ρ X * (T (Ea.ρ X) * Ea.ρ Y) * T (Ea.ρ Y) := by rw [hc]
          _ = Ea.ρ X * T (Ea.ρ X) * (Ea.ρ Y * T (Ea.ρ Y)) := by group }
  let κ : ↥(fixSubgroup Φ') →* ModGL τ D.L := θ.comp (fixSubgroup Φ').subtype
  have hκ : ∀ x : ↥(fixSubgroup Φ'), κ x = Ea.ρ (x : SL(3, D.L)) * T (Ea.ρ (x : SL(3, D.L))) :=
    fun x => rfl
  have hker : ∀ x : ↥(fixSubgroup Φ'), κ x = 1 → (x : SL(3, D.L)) ∈ Subgroup.center SL(3, D.L) := by
    intro x hx
    set X : SL(3, D.L) := (x : SL(3, D.L)) with hX
    have h1 : Ea.ρ X * T (Ea.ρ X) = 1 := by rw [← hκ]; exact hx
    have h2 : Ea.ρ X ∈ rootSpan τ D.L Sb := by
      have : Ea.ρ X = (T (Ea.ρ X))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact inv_mem (hTab _ (hρSa X))
    rw [Subgroup.mem_center_iff]
    intro Y
    apply Ea.inj
    rw [map_mul Ea.ρ Y X, map_mul Ea.ρ X Y]
    exact hcomm _ (hρSa Y) _ h2
  have hP₀ : κ.range ≤ fixedRootGroup D S := by
    rintro _ ⟨x, rfl⟩
    rw [hκ]
    set X : SL(3, D.L) := (x : SL(3, D.L)) with hX
    refine Subgroup.mem_inf.2 ⟨?_, mem_twistedFixedPoints.2 ?_⟩
    · rw [hS]
      exact mul_mem (Subgroup.mem_sup_left (hρSa X)) (Subgroup.mem_sup_right (hTab _ (hρSa X)))
    · have hXfix : Φ' X = X := x.2
      have hTTx : T (T (Ea.ρ X)) = Ea.ρ X := by rw [hTT, hΦ' X, hXfix]
      have hc : Ea.ρ X * T (Ea.ρ X) = T (Ea.ρ X) * Ea.ρ X :=
        hcomm _ (hρSa X) _ (hTab _ (hρSa X))
      have h3 : T (Ea.ρ X * T (Ea.ρ X)) = Ea.ρ X * T (Ea.ρ X) := by
        rw [map_mul, hTTx, ← hc]
      exact (hT _).symm.trans h3
  haveI := hfin
  have hfinP : Finite ↥κ.range := Set.Finite.to_subtype (Set.finite_range κ)
  have hperfP : ⁅κ.range, κ.range⁆ = κ.range := by
    have htop : ⁅(⊤ : Subgroup ↥(fixSubgroup Φ')), ⊤⁆ = ⊤ := Group.isPerfect_def.1 hq.1
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  have hdvd := frame_card_dvd D S hrat κ.range hP₀ hfinP hperfP
  set Y₀ : SL(3, K₂) := Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1 with hY₀
  have hY₀ℓ : Y₀ ^ ℓ = 1 := by
    have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.transvection_pow_ringChar
      (show (0 : Fin 3) ≠ 1 by decide) (1 : K₂)
    rwa [ringChar.eq K₂ ℓ] at h
  have hY₀c : Y₀ ∉ Subgroup.center SL(3, K₂) := fun h =>
    one_ne_zero ((Matrix.SpecialLinearGroup.transvection_mem_center_iff
      (show (0 : Fin 3) ≠ 1 by decide) (1 : K₂)).1 h)
  set ι : SL(3, K₂) →* SL(3, D.L) := Matrix.SpecialLinearGroup.map (algebraMap K₂ D.L) with hι
  have hιinj : Function.Injective ι :=
    CFSG.RankThree.Classical2.specialLinearGroup_map_injective (algebraMap K₂ D.L).injective
  set X₀ : SL(3, D.L) := H * ι Y₀ * H⁻¹ with hX₀
  have hX₀fix : X₀ ∈ fixSubgroup Φ' := (hH X₀).2 ⟨Y₀, rfl⟩
  set x₀ : ↥(fixSubgroup Φ') := ⟨X₀, hX₀fix⟩ with hx₀
  have hx₀ℓ : x₀ ^ ℓ = 1 := by
    apply Subtype.ext
    show X₀ ^ ℓ = 1
    rw [hX₀, conj_pow, ← map_pow, hY₀ℓ, map_one, mul_one, mul_inv_cancel]
  have hκx₀ : κ x₀ ≠ 1 := by
    intro h1
    have hc := hker x₀ h1
    apply hY₀c
    rw [Subgroup.mem_center_iff]
    intro Z
    apply hιinj
    have hcZ := Subgroup.mem_center_iff.1 hc (H * ι Z * H⁻¹)
    have e : H * ι Z * H⁻¹ * X₀ = X₀ * (H * ι Z * H⁻¹) := hcZ
    rw [hX₀] at e
    have e2 : H * (ι Z * ι Y₀) * H⁻¹ = H * (ι Y₀ * ι Z) * H⁻¹ := by
      calc H * (ι Z * ι Y₀) * H⁻¹ = H * ι Z * H⁻¹ * (H * ι Y₀ * H⁻¹) := by group
        _ = H * ι Y₀ * H⁻¹ * (H * ι Z * H⁻¹) := e
        _ = H * (ι Y₀ * ι Z) * H⁻¹ := by group
    have e3 := mul_left_cancel (mul_right_cancel e2)
    rw [map_mul, map_mul]
    exact e3
  have hκx₀ℓ : κ x₀ ^ ℓ = 1 := by rw [← map_pow, hx₀ℓ, map_one]
  have hmem : κ x₀ ∈ κ.range := ⟨x₀, rfl⟩
  have hord : orderOf (⟨κ x₀, hmem⟩ : ↥κ.range) = ℓ := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hκx₀ℓ
    · intro h
      exact hκx₀ (congrArg Subtype.val h)
  have hℓP : ℓ ∣ Nat.card ↥κ.range := by
    rw [← hord]
    exact orderOf_dvd_natCard _
  rw [hKℓ]
  exact hℓP.trans hdvd

theorem ringChar_dvd_card_e6Six_X₂ (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    ringChar K ∣ Nat.card ↥(TwClass.e6Six.X₂ D) := by
  classical
  let Ea : UFrame TwClass.e6Six.tag D.L 3 TwCardAux.e6Sa :=
    (TwCardAux.UFrame.ofAn (CFSG.RankThree.PartOne.TCX.E.a2Std₁.embedding 1) D.L).cast TwCardAux.e6_Sa_emb_eq
  have hsq : ∀ i j : Fin 3, i ≠ j → TwClass.e6Six.w • (TwClass.e6Six.w • Ea.r i j) = Ea.r i j := by
    intro i j hij
    show (coxeterSystem Tag.E6).wordProd TwClass.wordE6 •
      ((coxeterSystem Tag.E6).wordProd TwClass.wordE6 •
        ((1 : WeylGroup Tag.E6) • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 i j)) =
          (1 : WeylGroup Tag.E6) • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 i j
    rw [one_smul]
    exact TwCardAux.e6_hsq i j hij
  refine ringChar_dvd_card_frame_of_exchange D (S := TwClass.e6Six.S₂) (Sa := TwCardAux.e6Sa)
    (Sb := TwCardAux.e6Sb) Ea TwCardAux.e6_Sa_isRoot TwCardAux.e6_hab hsq ?_
    (TwCardAux.e6_hcomm D.L) (hrat_perfect (Or.inl ⟨rfl, rfl⟩) D)
  show rootSpan Tag.E6 D.L TwClass.e6Six.S₂ = _
  rw [TwCardAux.e6_S₂_eq, CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.rootSpan_union_eq]
  rfl

end E6SixX2R

section E6SixNativeR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

set_option linter.unusedSectionVars false

theorem e6Phi6UniNative (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 6)
    (E : Subgroup (adjointGroup .E6 K)) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : adjointGroup .E6 K | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧
      ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hrK : ringChar K ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  have hK3 : 3 ≤ Nat.card K := three_le_of_orderOf_six hp hp5 hord
  have hKq : TwClass.e6Six.minQ ≤ Nat.card K := hK3
  obtain ⟨D⟩ := twClassLeaves_e6Six.lang K
  have hb := twClassLeaves_e6Six.basic K hKq D
  have hc₁ := (TwCardAux.e6Six_X₁ K hK3 D).1
  have hd₁ : ringChar K ∣ Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1)) :=
    dvd_mul_of_dvd_left (dvd_pow hrK (by norm_num)) _
  have hd₂ : ringChar K ∣ Nat.card ↥(TwClass.e6Six.X₂ D) := ringChar_dvd_card_e6Six_X₂ K D
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311g.uniClosure_eq_top_of_twSubgroups_rgen hb.le₁ hb.le₂
    hb.comm (twClassLeaves_e6Six.closing K hKq D) (twClassLeaves_e6Six.normalizer K hKq D)
    (twClassLeaves_e6Six.planeData K hKq D p hp hp5 hord)
    (fun F hFc hFp a b haF hbF ha1 hb1 => exists_offLine_rgen_E6_phi6 K hK3 hp hp5 hord F hFc hFp haF hbF ha1 hb1)
    (twQuasi TwClass.e6Six K hKq D) (by rw [hc₁]; exact hd₁) hd₂ E hEp hEc

theorem uniSeitzPlanes_E6Six_inner_odd :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6) ∧
      d.1.characteristic ≠ 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, h6⟩, hch2, hn⟩
  obtain rfl : d = .E6 q := hq
  have hq2 : q.p ≠ 2 := by simpa using hch2
  haveI : Fact p.Prime := ⟨hp⟩
  refine uniPlaneGen_cat_odd CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6
    TauCeti.LieTypeIndex.characteristic_E6 hv hq2 ?_ hE hc hin hn
  intro K _ _ hKq _ E₀ hE₀p hE₀c _
  exact e6Phi6UniNative K hp hp5 (by rw [hKq]; exact h6) E₀ hE₀p hE₀c

end E6SixNativeR

section E8TwelveR

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec weylMatrix_pow)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ThirdLineAux
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL blockGL_ne_scalar_of_ne_one coe_blockSL)

open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false

theorem eq_one_of_mem_torusGroup_of_pow_char_j {τ : Tag} {L : Type} [Field L] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] {u : ModGL τ L} (hu : u ∈ torusGroup τ L) (huℓ : u ^ ℓ = 1) : u = 1 := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  have hb : b ^ ℓ = 1 := by
    apply rootDiagUnit_injective (τ := τ) (K := L)
    have h1 : rootDiagUnit τ (b ^ ℓ) = rootDiagUnit τ b ^ ℓ := (rootDiagUnitHom τ L).map_pow b ℓ
    rw [h1, huℓ, rootDiagUnit_one]
  have hb1 : b = 1 := by
    funext i
    have h := congrFun hb i
    simp only [Pi.pow_apply, Pi.one_apply] at h
    apply Units.ext
    apply frobenius_inj L ℓ
    simp only [frobenius_def, Pi.one_apply, Units.val_one, one_pow]
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  rw [hb1, rootDiagUnit_one]

theorem not_isSolvable_rClosure_of_rElement_mem_range {τ : Tag} {K : Type} [Field K] [Finite K] {L : Type}
    [Field L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hKℓ : ringChar K = ℓ) {x : adjointGroup τ K}
    (ψ : Subgroup.centralizer ({x} : Set (adjointGroup τ K)) →* ModGL τ L) (hψ : Function.Injective ψ)
    (hsol : ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup τ K))), V.Normal →
      Group.IsSolvable V → ∀ v ∈ V, ψ v ∈ torusGroup τ L)
    {u : ModGL τ L} (hu : u ∈ ψ.range) (hu1 : u ≠ 1) (huℓ : u ^ ℓ = 1) :
    ¬ Group.IsSolvable ↥(Subgroup.closure {y : adjointGroup τ K | Commute y x ∧
      ∃ m : ℕ, y ^ (ringChar K ^ m) = 1}) := by
  classical
  intro hR
  set R := Subgroup.closure {y : adjointGroup τ K | Commute y x ∧ ∃ m : ℕ, y ^ (ringChar K ^ m) = 1}
    with hRdef
  set C := Subgroup.centralizer ({x} : Set (adjointGroup τ K)) with hCdef
  have hRC : R ≤ C := (Subgroup.closure_le _).2 fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 hy.1.eq
  have hconjR : ∀ g ∈ C, ∀ z ∈ R, g * z * g⁻¹ ∈ R := by
    intro g hg z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨hzx, m, hm⟩ := hz
      refine Subgroup.subset_closure ⟨?_, m, ?_⟩
      · have hg' : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hg
        have hz' : z * x = x * z := hzx.eq
        show g * z * g⁻¹ * x = x * (g * z * g⁻¹)
        calc g * z * g⁻¹ * x = g * z * (g⁻¹ * x) := by group
          _ = g * z * (x * g⁻¹) := by
              rw [show g⁻¹ * x = x * g⁻¹ by
                rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hg', mul_assoc, mul_inv_cancel, mul_one]]
          _ = g * (z * x) * g⁻¹ := by group
          _ = g * (x * z) * g⁻¹ := by rw [hz']
          _ = (g * x) * z * g⁻¹ := by group
          _ = (x * g) * z * g⁻¹ := by rw [hg']
          _ = x * (g * z * g⁻¹) := by group
      · rw [conj_pow, hm, mul_one, mul_inv_cancel]
    | one => simp
    | mul a b _ _ ha hb =>
      have h := R.mul_mem ha hb
      rwa [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group] at h
    | inv a _ ha =>
      have h := R.inv_mem ha
      rwa [show (g * a * g⁻¹)⁻¹ = g * a⁻¹ * g⁻¹ by group] at h
  set V : Subgroup C := R.subgroupOf C with hVdef
  have hVn : V.Normal := by
    constructor
    intro v hv g
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    exact hconjR g g.2 v hv
  have hVs : Group.IsSolvable V := by
    haveI := hR
    exact solvable_of_solvable_injective (f := (Subgroup.subgroupOfEquivOfLe hRC).toMonoidHom)
      (MulEquiv.injective _)
  obtain ⟨k, rfl⟩ := hu
  have hkℓ : k ^ ℓ = 1 := hψ (by rw [map_pow, huℓ, map_one])
  have hkR : (k : adjointGroup τ K) ∈ R := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_centralizer_singleton_iff.1 k.2, 1, ?_⟩
    rw [pow_one, hKℓ, ← Subgroup.coe_pow, hkℓ, Subgroup.coe_one]
  have hkV : k ∈ V := Subgroup.mem_subgroupOf.2 hkR
  exact hu1 (eq_one_of_mem_torusGroup_of_pow_char_j (hsol V hVn hVs k hkV) huℓ)

theorem mem_range_of_fixed_of_commute_E8 {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (n g0 : ModGL .E8 L)
    (hg0C : g0 ∈ adjointGroup .E8 L) (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * n)
    {x c : adjointGroup .E8 K} {u : ModGL .E8 L} (hu : u ∈ adjointGroup .E8 L) {ℓ : ℕ} (hℓ0 : 0 < ℓ)
    (huℓ : u ^ ℓ = 1) (huθ : n * Units.map (entrywiseHom Fr) u * n⁻¹ = u)
    (hucomm : u * (g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0) =
      (g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0) * u)
    (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →* ModGL .E8 L)
    (hψ : ∀ y, ψ y = g0⁻¹ * adjEmb .E8 K L (c * (y : adjointGroup .E8 K) * c⁻¹) * g0) :
    u ∈ ψ.range := by
  classical
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦ
  set Y := g0 * u * g0⁻¹ with hYdef
  have hYC : Y ∈ adjointGroup .E8 L := mul_mem (mul_mem hg0C hu) (inv_mem hg0C)
  have hYF : Φ Y = Y := by
    rw [hYdef, map_mul, map_mul, map_inv, hg0]
    calc g0 * n * Φ u * (g0 * n)⁻¹ = g0 * (n * Φ u * n⁻¹) * g0⁻¹ := by group
      _ = g0 * u * g0⁻¹ := by rw [huθ]
  have hYℓ : Y ^ ℓ = 1 := by rw [hYdef, conj_pow, huℓ, mul_one, mul_inv_cancel]
  have hfo : IsOfFinOrder Y := isOfFinOrder_iff_pow_eq_one.2 ⟨ℓ, hℓ0, hYℓ⟩
  haveI : Finite (Subgroup.zpowers Y) := Finite.of_equiv _ (finEquivZPowers hfo)
  have hZC : Subgroup.zpowers Y ≤ adjointGroup .E8 L := Subgroup.zpowers_le.2 hYC
  have hZF : ∀ z ∈ Subgroup.zpowers Y, Φ z = z := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [map_zpow, hYF]
  have h := (finite_fixed_subgroup_rational_perfect (K := K) (L := L) 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr (Subgroup.zpowers Y) hZC hZF).1
  have hle : Subgroup.zpowers Y ≤ (adjEmb .E8 K L).range := by
    rw [adjEmb_range]
    exact Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1 h)
  obtain ⟨z, hz⟩ := hle (Subgroup.mem_zpowers Y)
  have hzc : z * (c * x * c⁻¹) = (c * x * c⁻¹) * z := by
    apply adjEmb_injective (τ := .E8) (K := K) (L := L)
    rw [map_mul (adjEmb .E8 K L) z, map_mul (adjEmb .E8 K L) (c * x * c⁻¹) z, hz, hYdef]
    calc g0 * u * g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹)
        = g0 * (u * (g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0)) * g0⁻¹ := by group
      _ = g0 * ((g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0) * u) * g0⁻¹ := by rw [hucomm]
      _ = adjEmb .E8 K L (c * x * c⁻¹) * (g0 * u * g0⁻¹) := by group
  refine MonoidHom.mem_range.2 ⟨⟨c⁻¹ * z * c, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
  · calc c⁻¹ * z * c * x = c⁻¹ * (z * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * z) * c := by rw [hzc]
      _ = x * (c⁻¹ * z * c) := by group
  · rw [hψ]
    show g0⁻¹ * adjEmb .E8 K L (c * (c⁻¹ * z * c) * c⁻¹) * g0 = u
    rw [show c * (c⁻¹ * z * c) * c⁻¹ = z by group, hz, hYdef]
    group

theorem exists_fixed_rElement_twoA2_E8 {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {k₂ : Type} [Field k₂] [Algebra k₂ L] [IsAlgClosure k₂ L] (hk₂ : Nat.card k₂ = ℓ ^ (2 * f))
    (M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) (n : ModGL Tag.E8 L)
    (hn : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : ∀ u, weylQuotientHom Tag.E8 L ⟨n, hn⟩ • u = M *ᵥ u) (v₁ v₂ : WeylGroup Tag.E8)
    (h12 : ∀ i j : Fin 3, i ≠ j → ∃ i' j' : Fin 3, i' ≠ j' ∧
      M *ᵥ sigmaRootE8 v₁ i j = sigmaRootE8 v₂ i' j')
    (hπ₁ : ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j →
      (M * M) *ᵥ sigmaRootE8 v₁ i j = sigmaRootE8 v₁ (π j) (π i))
    (horth : ∀ α ∈ sigmaSetE8 v₁, ∀ β ∈ sigmaSetE8 v₂,
      α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ β) = 0) :
    ∃ u ∈ rootSpan Tag.E8 L (sigmaSetE8 v₁ ∪ sigmaSetE8 v₂),
      n * Units.map (entrywiseHom Fr) u * n⁻¹ = u ∧ u ≠ 1 ∧ u ^ ℓ = 1 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hΦ
  set Fr₂ : L →+* L := Fr.comp Fr with hFr₂def
  have hFr₂ : ∀ c, Fr₂ c = c ^ (ℓ ^ (2 * f)) := fun c => by
    rw [hFr₂def, RingHom.comp_apply, hFr, hFr, ← pow_mul, ← pow_add, two_mul]
  have hFr₂bij : Function.Bijective Fr₂ := ⟨Fr₂.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ (2 * f) from pow_pos hℓ.pos _)
    exact ⟨x, by rw [hFr₂, hx]⟩⟩
  have hS : ∀ v : WeylGroup Tag.E8, ∀ r ∈ sigmaSetE8 v, IsRoot Tag.E8 r := fun v r hr => by
    rw [sigmaSetE8_eq] at hr
    obtain ⟨i, j, hij, rfl⟩ := hr
    exact isRoot_sigmaRootE8 v hij
  have hmap12 : ∀ α ∈ sigmaSetE8 v₁, M *ᵥ α ∈ sigmaSetE8 v₂ := by
    intro α hα
    rw [sigmaSetE8_eq] at hα
    obtain ⟨i, j, hij, rfl⟩ := hα
    obtain ⟨i', j', hij', h⟩ := h12 i j hij
    rw [h, sigmaSetE8_eq]
    exact ⟨i', j', hij', rfl⟩
  have hT₁₂ := twist_rootSpan_le (L := L) Fr M n hn hnW (hS v₁) hmap12
  have hcomm := rootSpan_commute_of_orth (L := L) (τ := Tag.E8) (Or.inr (Or.inr (Or.inr rfl)))
    (hS v₁) (hS v₂) horth
  set Tm : ModGL Tag.E8 L →* ModGL Tag.E8 L := (MulAut.conj n).toMonoidHom.comp Φ with hTm
  have hTapp : ∀ x, Tm x = n * Φ x * n⁻¹ := fun x => by simp [hTm, MulAut.conj_apply]
  have hTinj : Function.Injective Tm :=
    (MulAut.conj n).injective.comp (Units.map_injective (f := entrywiseHom Fr)
      (entrywise_injective Fr))
  obtain ⟨π, hpi⟩ := hπ₁
  choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) =>
    rhoSigmaE8_transvection (L := L) v₁ i j hij
  have hΨ : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      (Tm.comp Tm) (pinnedX Tag.E8 L (sigmaRootE8 v₁ i j) c) =
        pinnedX Tag.E8 L (sigmaRootE8 v₁ (π j) (π i)) ((b : L) * Fr₂ c) := by
    intro i j hij
    obtain ⟨i', j', hij', hMα⟩ := h12 i j hij
    obtain ⟨μ, hμ⟩ := twist_pinnedX Fr M n hn hnW (isRoot_sigmaRootE8 v₁ hij)
    have hroot' : IsRoot Tag.E8 (M *ᵥ sigmaRootE8 v₁ i j) := by
      rw [hMα]
      exact isRoot_sigmaRootE8 v₂ hij'
    obtain ⟨μ', hμ'⟩ := twist_pinnedX Fr M n hn hnW hroot'
    refine ⟨μ' * Units.map (Fr : L →* L) μ, fun c => ?_⟩
    have e1 : ∀ x, (Tm.comp Tm) x = Tm (Tm x) := fun x => rfl
    rw [e1, hTapp, hTapp, hμ c, hμ', Matrix.mulVec_mulVec, hpi i j hij]
    congr 1
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, map_mul, hFr₂def,
      RingHom.comp_apply]
    ring
  obtain ⟨Φ', hΦ'1, b, hshape⟩ := exists_aut_of_rootData_hom (rhoSigmaE8 L v₁)
    (rhoSigmaE8_injective v₁) (sigmaRootE8 v₁) ε hε Fr₂ hFr₂bij (Tm.comp Tm)
    (hTinj.comp hTinj) (fun i j => (π j, π i)) (fun i j hij => π.injective.ne hij.symm)
    (fun i j hij => ⟨π.symm j, π.symm i, π.symm.injective.ne hij.symm, by simp⟩) hΨ
  have hshape' : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ (2 * f)) :=
    fun i j hij t => by rw [hshape i j hij t, hFr₂]
  obtain ⟨-, -, ⟨J, hJ⟩, -, -⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary hℓ (by omega : 1 ≤ 2 * f)
      hk₂ π Φ' b hshape'
  haveI : CharP k₂ ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
    (k := 2 * f) (by omega) hk₂
  obtain ⟨Y₀, hY₀1, hY₀r⟩ := Inputs2311g.exists_sl2_rElement_ne_one k₂
  have hY₀ℓ : Y₀ ^ ℓ = 1 := by rwa [ringChar.eq k₂ ℓ] at hY₀r
  set Ym : SL(2, L) := Matrix.SpecialLinearGroup.map (algebraMap k₂ L) Y₀ with hYm
  have hYm1 : Matrix.SpecialLinearGroup.toGL Ym ≠ 1 := by
    intro h
    apply hY₀1
    apply CFSG.GH74.Filter.Lie.sl2_map_injective (algebraMap k₂ L)
    rw [map_one]
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_one]
    exact h
  set X : SL(3, L) := J * (blockSL L 2 1 Ym : SL(3, L)) * J⁻¹ with hX
  have hXfix : Φ' X = X := hJ Y₀
  have hXℓ : X ^ ℓ = 1 := by
    rw [hX, conj_pow, ← map_pow, hYm, ← map_pow, hY₀ℓ, map_one, map_one, mul_one, mul_inv_cancel]
  have hXnc : X ∉ Subgroup.center SL(3, L) := by
    intro hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
    have h1 : (blockSL L 2 1 Ym : SL(3, L)) = J⁻¹ * X * J := by rw [hX]; group
    have h2 : ((J⁻¹ * X * J : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = Matrix.scalar (Fin 3) r := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← hr,
        Matrix.mul_assoc, (Matrix.scalar_commute r (fun _ => Commute.all _ _) _).eq,
        ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    apply blockGL_ne_scalar_of_ne_one (K := L) (k := 2) (m := 1) le_rfl hYm1 r
    rw [← coe_blockSL]
    exact (congrArg (fun A : SL(3, L) => (A : Matrix (Fin 3) (Fin 3) L)) h1).trans h2
  set ρ := rhoSigmaE8 L v₁ with hρ
  set g : ModGL Tag.E8 L := ρ X with hg
  have hgQ : g ∈ rootSpan Tag.E8 L (sigmaSetE8 v₁) := by
    rw [← rhoSigmaE8_range]
    exact ⟨X, rfl⟩
  have hTgQ : Tm g ∈ rootSpan Tag.E8 L (sigmaSetE8 v₂) := by
    rw [hTapp]
    exact hT₁₂ g hgQ
  have hTT : Tm (Tm g) = g := by
    have h := hΦ'1 X
    rw [hXfix] at h
    exact h
  have hgc : g * Tm g = Tm g * g := hcomm g hgQ (Tm g) hTgQ
  refine ⟨g * Tm g, ?_, ?_, ?_, ?_⟩
  · rw [rootSpan_union_eq]
    exact mul_mem (Subgroup.mem_sup_left hgQ) (Subgroup.mem_sup_right hTgQ)
  · rw [← hTapp, map_mul, hTT, ← hgc]
  · intro h1
    have hgeq : g = (Tm g)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hgQ₂ : g ∈ rootSpan Tag.E8 L (sigmaSetE8 v₂) := by
      rw [hgeq]
      exact inv_mem hTgQ
    apply hXnc
    rw [Subgroup.mem_center_iff]
    intro Z
    apply rhoSigmaE8_injective (L := L) v₁
    have hZQ : ρ Z ∈ rootSpan Tag.E8 L (sigmaSetE8 v₁) := by
      rw [← rhoSigmaE8_range]
      exact ⟨Z, rfl⟩
    show ρ (Z * X) = ρ (X * Z)
    rw [map_mul ρ Z X, map_mul ρ X Z]
    exact hcomm (ρ Z) hZQ g hgQ₂
  · have hgℓ : g ^ ℓ = 1 := by rw [hg, ← map_pow, hXℓ, map_one]
    rw [(show Commute g (Tm g) from hgc).mul_pow, hgℓ, ← map_pow, hgℓ, map_one, mul_one]

theorem exists_offLine_rgen_E8_phi12_aux (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hp7 : 7 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord12 : orderOf ((Nat.card K : ℕ) : ZMod p) = 12)
    (hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 4 - ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8T12WW)
    (E : Subgroup (adjointGroup .E8 K)) (hEc : Nat.card E = p ^ 2) (hEp : ∀ x ∈ E, x ^ p = 1)
    {a b : adjointGroup .E8 K} (haE : a ∈ E) (hbE : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
      ¬ Group.IsSolvable ↥(Subgroup.closure {y : adjointGroup .E8 K | Commute y e ∧
        ∃ m : ℕ, y ^ (ringChar K ^ m) = 1}) := by
  classical
  have hD4 : CFSG.RankThree.PartOne.KE.D4TrialityLayer Tag.E8 :=
    CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hKℓ : ringChar K = ℓ := ringChar.eq K ℓ
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hnWv : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = e8T12V *ᵥ u := fun u => by
    rw [hnW]
    exact e8T12_weylImage u
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E8) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))
  have hT : twistedTorusOf n Φ = (fixedCharTuples e8T12V Fr).map (rootDiagUnitHom .E8 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnWv Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  set G1 := fixedBlockTuples e8T12V Fr
    (e8T12Bas e8T12B1List e8T12B2List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG1
  set G2 := fixedBlockTuples e8T12V Fr
    (e8T12Bas e8T12B2List e8T12B1List '' {i : Fin Tag.E8.rank | (i : ℕ) < 4}) with hG2
  set N : ℕ := (Nat.card K ^ 4 - Nat.card K ^ 2 + 1) ^ 2 with hNdef
  set Z0 : Subgroup (ModGL .E8 L) := (G1 ⊔ G2).map (rootDiagUnitHom .E8 L) with hZ0def
  have hZ0le : Z0 ≤ twistedTorusOf n Φ := by
    rw [hT]
    exact Subgroup.map_mono (sup_le inf_le_left inf_le_left)
  have hZ0card : Nat.card Z0 = N := by
    rw [hZ0def, Subgroup.card_map_of_injective hinj0]
    exact e8T12_card_sup Fr hFr hℓ hℓq hq2
  have h24 : Nat.card K ^ 2 ≤ Nat.card K ^ 4 :=
    Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) hq2) (by norm_num)
  have hN : N ≠ 0 := pow_ne_zero 2 (by omega)
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p = p ^ N.factorization p :=
    e8T12_ordProj hp hp3 hpq hord12
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := sigma_untwisted_sylow .E8 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp hp3 n hnC Z0 hZ0le hN hZ0card hord
  have hconj' : ∀ Q : Subgroup (adjointGroup .E8 K), IsPGroup p Q →
      ∃ c : adjointGroup .E8 K, ∀ y ∈ Q,
        g0⁻¹ * adjEmb .E8 K L (c * y * c⁻¹) * g0 ∈ twistedTorusOf n Φ := by
    intro Q hQ
    obtain ⟨c, hc⟩ := hconj Q hQ
    exact ⟨c, fun y hy => hZ0le ((mem_subtorusImage_iff _ _ _ _).1 (hc y hy))⟩
  have hbfix : ∀ b : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 b ∈ twistedTorusOf n Φ →
      b ∈ fixedCharTuples e8T12V Fr := by
    intro b hbT
    rw [hT] at hbT
    obtain ⟨b', hb', hb'e⟩ := hbT
    have : b' = b := hinj0 hb'e
    rw [← this]
    exact hb'
  have hbound : ∀ b : Fin Tag.E8.rank → Lˣ, rootDiagUnit .E8 b ∈ twistedTorusOf n Φ →
      (∀ i, b i ^ p = 1) → b ≠ 1 → (rootCharKernel b).ncard ≤ 24 := by
    intro b hbT hbp hb1
    have hcls : ∀ j, j < 14 → (classSetL e8T12Rows j).ncard ≤ 24 := fun j hj =>
      (ncard_classSetL_le _ _).trans (e8T12_classes_le j hj)
    rcases e8T12_kernel_structure Fr hFr hp hp3 hΦ (hbfix b hbT) hbp hb1 with
      h0 | ⟨cc, hcc, hker', -⟩ | ⟨cc, hcc, hker', -⟩
    · rw [h0, Set.ncard_empty]
      omega
    · rw [hker']
      refine hcls _ ?_
      revert cc
      have : ∀ c ∈ e8T12D4Certs, c.cls < 14 := by decide +kernel
      exact fun cc hcc _ => this cc hcc
    · rw [hker']
      refine hcls _ ?_
      revert cc
      have : ∀ c ∈ e8T12TwoA2Certs, c.cls < 14 := by decide +kernel
      exact fun cc hcc _ => this cc hcc
  have hperx : ∀ (x c : adjointGroup .E8 K) (b : Fin Tag.E8.rank → Lˣ), orderOf x = p →
      g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈ twistedTorusOf n Φ →
      rootDiagUnit .E8 b = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 →
      (rootCharKernel b).Nonempty →
      ¬ Group.IsSolvable ↥(Subgroup.closure {y : adjointGroup .E8 K | Commute y x ∧
        ∃ m : ℕ, y ^ (ringChar K ^ m) = 1}) := by
    intro x c b hx hh hb hne
    have hbh' : rootDiagUnit .E8 b = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 := hb
    have hordh : orderOf (g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0) = p := by
      have e1 : orderOf (g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0) =
          orderOf (adjEmb .E8 K L (c * x * c⁻¹)) := by
        have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective
          (adjEmb .E8 K L (c * x * c⁻¹))
        simpa [MulAut.conj_apply] using this
      have e2 : orderOf (adjEmb .E8 K L (c * x * c⁻¹)) = orderOf (c * x * c⁻¹) :=
        orderOf_injective (adjEmb .E8 K L) adjEmb_injective _
      have e3 : orderOf (c * x * c⁻¹) = orderOf x := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
        simpa [MulAut.conj_apply] using this
      rw [e1, e2, e3, hx]
    have hbp : orderOf (rootDiagUnit .E8 b) = p := by rw [hbh']; exact hordh
    have hap := CFSG.RankThree.PartOne.KE.pow_eq_one_of_orderOf_rootDiagUnit hbp
    have hb1 := CFSG.RankThree.PartOne.KE.ne_one_of_orderOf_rootDiagUnit hp hbp
    have hkd := e8T12_kernel_structure Fr hFr hp hp3 hΦ (hbfix b (hbh' ▸ hh)) hap hb1
    rcases hkd with hA | ⟨cc, hcc, hker', hgood⟩ | ⟨cc, hcc, hker', hgood⟩
    · exfalso
      rw [hA] at hne
      exact Set.not_nonempty_empty hne
    ·
      obtain ⟨hS1, u, hu, hcertw⟩ := D4Cert.sound hgood
      obtain ⟨-, -, -, hab, hbc, hac, ha, hbl, hcl, -⟩ := hgood
      set v : WeylGroup .E8 := (coxeterSystem .E8).wordProd cc.w with hv
      have hSeq : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots .E8 (d4Nodes .E8) :=
        hker'.trans hS1
      have hcert : ∃ u ∈ parabolicWeylGroup .E8 (d4Nodes .E8),
          ∀ α ∈ parabolicRoots .E8 (d4Nodes .E8),
            (v⁻¹ * weylQuotientHom .E8 L ⟨n, hnm⟩ * v) • α =
              u • permLattice (List.formPerm [cc.a, cc.b, cc.c]) α := by
        rw [hnW]
        exact ⟨u, hu, hcertw⟩
      obtain ⟨P, hfam, hP1, h₀, hh₀⟩ := e8_d4_family hD4 hf hK v n hnm hnC cc.a cc.b cc.c hab hbc
        hac (by rcases ha with h | h | h <;> simp [h]) (by rcases hbl with h | h | h <;> simp [h])
        (by rcases hcl with h | h | h <;> simp [h]) hcert
      obtain ⟨ψ, hψinj, -, hψHQ, hψR, -, hPψ, -⟩ := e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp hordW
        hx c hbh' hh hSeq (d4Set_isRoot v) (d4Set_neg v) hfam
      have hcomm := e8_perx_commutator Fr n (d4Set_isRoot v) ψ hψHQ hψR hP1 (hPψ ()) (hfam.2.1 ())
      exact Inputs2311g.not_isSolvable_rClosure_of_layer ψ hψinj (hfam.2.1 ()) hcomm (e8Index 3) h₀ hh₀
    ·
      obtain ⟨hS1, hex12, hex21, hπ₁, hπ₂, horth⟩ :=
        TwoA2Cert.sound (M := e8T12V) (Wl := e8T12VList) e8T12V_eq hgood
      obtain ⟨k₂, _, _, _, hk₂⟩ := exists_finite_field_isAlgClosure ℓ (2 * f) (by omega) K L
      set v₁ : WeylGroup .E8 := (coxeterSystem .E8).wordProd cc.w₁ with hv₁
      set v₂ : WeylGroup .E8 := (coxeterSystem .E8).wordProd cc.w₂ with hv₂
      obtain ⟨P, hfam⟩ := e8_two_A2_family hf Fr hFr' hk₂ e8T12V n hnm hnWv v₁ v₂ hex12 hex21 hπ₁
        hπ₂ horth
      have hSeq : rootCharKernel b = sigmaSetE8 v₁ ∪ sigmaSetE8 v₂ := hker'.trans hS1
      obtain ⟨ψ, hψinj, hψeq, -, -, -, -, hψsol⟩ := e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp
        hordW hx c hbh' hh hSeq (twoA2Set_isRoot _ _) (twoA2Set_neg _ _) hfam
      obtain ⟨u, huS, huθ, hu1, huℓ⟩ :=
        exists_fixed_rElement_twoA2_E8 hf Fr hFr' hk₂ e8T12V n hnm hnWv v₁ v₂ hex12 hπ₁ horth
      have huC : u ∈ adjointGroup .E8 L :=
        (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α :
          rootSpan .E8 L (sigmaSetE8 v₁ ∪ sigmaSetE8 v₂) ≤ adjointGroup .E8 L) huS
      have hucomm : u * (g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0) =
          (g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0) * u := by
        have hsub : sigmaSetE8 v₁ ∪ sigmaSetE8 v₂ ⊆ rootCharKernel b := fun α hα => by
          rw [hSeq]
          exact hα
        have h1 := Subgroup.mem_centralizer_singleton_iff.1
          (CFSG.LieType.Chevalley.rootSpan_le_centralizer (K := L) b hsub huS)
        rw [← hbh']
        exact h1
      have hur : u ∈ ψ.range :=
        mem_range_of_fixed_of_commute_E8 Fr hFr n g0 hg0C hg0 huC hℓ.pos huℓ huθ hucomm ψ hψeq
      exact not_isSolvable_rClosure_of_rElement_mem_range hKℓ ψ hψinj
        (fun V hV hVs v hv => (mem_twistedTorusOf.1
          (subtorusSigma_le_twistedTorusOf _ _ _ (hψsol V hV hVs v hv))).1) hur hu1 huℓ
  exact Inputs2311g.exists_offLine_rgen_of_kernel Φ n g0 hp hconj' 24
    (by rw [card_rootFinset_E8]; norm_num) hbound hperx E hEc hEp haE hbE ha1 hb1

theorem exists_offLine_rgen_E8_phi12 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 12)
    (E : Subgroup (adjointGroup .E8 K)) (hEc : Nat.card E = p ^ 2) (hEp : ∀ x ∈ E, x ^ p = 1)
    {a b : adjointGroup .E8 K} (haE : a ∈ E) (hbE : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
      ¬ Group.IsSolvable ↥(Subgroup.closure {y : adjointGroup .E8 K | Commute y e ∧
        ∃ m : ℕ, y ^ (ringChar K ^ m) = 1}) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, f, hℓ, hchar, hf, hK⟩ := exists_char_pow K
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := fun h => by
    rw [h, orderOf_zero] at hord
    omega
  have hdvd : 12 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have hp7 : 7 < p := by omega
  have hpq : ¬ p ∣ Nat.card K := fun h => hq0 ((ZMod.natCast_eq_zero_iff _ _).2 h)
  have hΦ' := phi12_of_orderOf hord
  have hcm := canonicalRep_mem_monomialSubgroup L ((coxeterSystem .E8).wordProd e8T12WW)
  have hnW : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L
      ((coxeterSystem .E8).wordProd e8T12WW), hcm⟩ = (coxeterSystem .E8).wordProd e8T12WW :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  exact exists_offLine_rgen_E8_phi12_aux K hf hK hp (by omega) hp7 hpq hord hΦ' L _ hcm hnW E hEc hEp
    haE hbE ha1 hb1

end E8TwelveR

section E8TwelveNativeR

open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

set_option linter.unusedSectionVars false

theorem e8Phi12UniNative (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 12)
    (E : Subgroup (adjointGroup .E8 K)) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    Subgroup.closure {k : adjointGroup .E8 K | ∃ x ∈ E, x ≠ 1 ∧ Commute k x ∧
      ∃ m : ℕ, k ^ (ringChar K ^ m) = 1} = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hrK : ringChar K ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  have hKq : TwClass.e8Twelve.minQ ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨D⟩ := twClassLeaves_e8Twelve.lang K
  have hb := twClassLeaves_e8Twelve.basic K hKq D
  obtain ⟨hc₁, hc₂, -⟩ := TwCardAux.e8Twelve_frames K D
  have hd : ringChar K ∣ CFSG.Open.ordTrialityD4 (Nat.card K) := by
    unfold CFSG.Open.ordTrialityD4
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow hrK (by norm_num)) _) _) _
  exact Inputs2311g.uniClosure_eq_top_of_twSubgroups_rgen hb.le₁ hb.le₂ hb.comm
    (twClassLeaves_e8Twelve.closing K hKq D) (twClassLeaves_e8Twelve.normalizer K hKq D)
    (twClassLeaves_e8Twelve.planeData K hKq D p hp hp5 hord)
    (fun F hFc hFp a b haF hbF ha1 hb1 =>
      exists_offLine_rgen_E8_phi12 K hp hp5 hord F hFc hFp haF hbF ha1 hb1)
    (twQuasi TwClass.e8Twelve K hKq D) (by rw [hc₁]; exact hd) (by rw [hc₂]; exact hd) E hEp hEc

theorem uniSeitzPlanes_E8Twelve_inner_odd :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : TauCeti.PrimePower, d.1 = .E8 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 12) ∧
      d.1.characteristic ≠ 2 ∧ ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, h12⟩, hch, hn⟩
  obtain rfl : d = .E8 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f.uniPlaneGen_E8_of_native hv hch
    (fun K _ _ hKq _ E₀ h1 h2 _ => e8Phi12UniNative K hp hp5 (by rw [hKq]; exact h12) E₀ h1 h2) hE hc hin hn

end E8TwelveNativeR

@[expose] def TrialityInnerAt (D : ℕ → ℕ → Prop) (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    (E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d))) : Prop :=
  InnerPlane d p E ∧ 5 ≤ p ∧ (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q ∧ D p q.card) ∧
    ¬ NormalizesRSubgroup d E

@[expose] def TrialityPhi3Inner (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    (E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d))) : Prop :=
  TrialityInnerAt (fun p c => p ∣ c ^ 2 + c + 1) d p E

theorem not_isD2SeitzException_trialityD4_j (p : ℕ) (q : TauCeti.PrimePower) :
    ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p (.trialityD4 q) := by
  rintro (⟨-, ⟨q', -, -, h⟩ | ⟨q', -, -, h⟩ | ⟨q', -, -, h⟩ | ⟨q', -, -, h | h⟩ | h⟩ | ⟨-, h | h⟩) <;> cases h

section E6ThreeR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (m := 2)) ∅

set_option linter.unusedSectionVars false

theorem le_closure_hyperRSet_of_rFixed {G : Type} [Group G] {p r : ℕ} [hp : Fact p.Prime]
    {cube B Y E' : Subgroup G} (hab : IsElemAbelian p cube)
    (hcube : Nat.card cube = p ^ 3) (hBle : B ≤ cube) (hB : Nat.card B = p)
    (hBY : Disjoint B Y) (hcent : ∀ y ∈ Y, ∀ b ∈ B, Commute y b)
    (hE'le : E' ≤ cube) (hE'Y : E' ≤ Y)
    (hgen : Y ≤ Subgroup.closure {y : G | y ∈ Y ∧ (∃ n : ℕ, y ^ r ^ n = 1) ∧
      ∃ x ∈ E', x ≠ 1 ∧ Commute y x}) :
    Y ≤ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ cube r p) := by
  have hcomm : ∀ a ∈ cube, ∀ b ∈ cube, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine hgen.trans (Subgroup.closure_mono ?_)
  rintro y ⟨hyY, hyr, x, hxE, hx1, hyx⟩
  have hxcube : x ∈ cube := hE'le hxE
  have hord : orderOf x = p := orderOf_eq_prime (hab.2 _ hxcube) hx1
  have hzp : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers]; exact hord
  have hdisj : Disjoint B (Subgroup.zpowers x) :=
    hBY.mono_right (Subgroup.zpowers_le.2 (hE'Y hxE))
  have hcommBZ : ∀ h ∈ B, ∀ z ∈ Subgroup.zpowers x, Commute h z := by
    intro h hh z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (hcomm h (hBle hh) x hxcube).zpow_right n
  have hFcard : Nat.card ↥(B ⊔ Subgroup.zpowers x) = p ^ 2 := by
    rw [CFSG.HardMathSupport.Malle.SeitzCube.card_sup_of_commute B _ hcommBZ hdisj, hB, hzp]
    ring
  have hFle : B ⊔ Subgroup.zpowers x ≤ cube := sup_le hBle (Subgroup.zpowers_le.2 hxcube)
  have hFcent : B ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcent y hyY b hb).eq.symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyx.eq.symm
  refine ⟨Subgroup.mem_top _, hyr, B ⊔ Subgroup.zpowers x, hFle,
    CFSG.HardMathSupport.Malle.SeitzCube.relIndex_eq_of_card hFle hp.out.pos hFcard hcube, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  exact Subgroup.mem_centralizer_singleton_iff.1 (hFcent hf)

theorem le_closure_rFixed_of_isoLie_triality {P : ℕ → Prop} {D : ℕ → ℕ → Prop}
    (h3 : UniSeitzPlanes fun d p E => TrialityInnerAt D d p E ∧ P d.1.characteristic)
    {G : Type} [Group G] {Y E' : Subgroup G} {q : TauCeti.PrimePower}
    (hiso : CFSG.RankThree.PartOne.Census3.IsoLie ↥Y (.trialityD4 q)) (hP : P q.p)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p) (hdvd : D p q.card)
    (hE'Y : E' ≤ Y) (hE'c : ∀ a ∈ E', ∀ b ∈ E', Commute a b) (hE'p : ∀ a ∈ E', a ^ p = 1)
    (hE'card : Nat.card E' = p ^ 2) :
    Y ≤ Subgroup.closure {y : G | y ∈ Y ∧ (∃ n : ℕ, y ^ q.p ^ n = 1) ∧
      ∃ x ∈ E', x ≠ 1 ∧ Commute y x} := by
  classical
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  set d : TauCeti.ValidLieTypeIndex := ⟨.trialityD4 q, hv⟩ with hd
  have hexc : IsChevalleyExcIndex d.1 := Or.inr (Or.inl ⟨q, rfl⟩)
  have hinj : Function.Injective (MulAut.conj : CFSG.LieType.SeitzGeneration.Cat d →* _) :=
    Inputs2311c.conj_injective_cat_of_chevalleyExc hexc
  have hchar : d.1.characteristic = q.p := TauCeti.LieTypeIndex.characteristic_trialityD4 q
  set E₀ : Subgroup (CFSG.LieType.SeitzGeneration.Cat d) := (E'.subgroupOf Y).map e0.toMonoidHom with hE₀
  set E₁ : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d)) :=
    E₀.map (MulAut.conj : CFSG.LieType.SeitzGeneration.Cat d →* _) with hE₁
  have hYel : IsElemAbelian p (E'.subgroupOf Y) := by
    refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact (hE'c _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)).eq
    · apply Subtype.ext
      exact hE'p _ (Subgroup.mem_subgroupOf.1 hx)
  have hE₁el : IsElemAbelian p E₁ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hYel e0.toMonoidHom) _
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective hinj, hE₀, Subgroup.card_map_of_injective e0.injective,
      ← hE'card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'Y).toEquiv
  have hin : InnerPlane d p E₁ := Subgroup.map_le_range _ _
  have hp2 : p ≠ 2 := by omega
  have hpd : p ≠ d.1.characteristic := by rw [hchar]; exact hpq
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1 := not_isD2SeitzException_trialityD4_j p q
  have hgen : UniPlaneGen d.1.characteristic E₁ := by
    by_cases hN : NormalizesRSubgroup d E₁
    · exact Inputs2311c.uniSeitzPlanes_excParabolic d p hp hp2 hpd hex E₁ hE₁el hE₁c ⟨hin, hexc, hN⟩
    · exact h3 d p hp hp2 hpd hex E₁ hE₁el hE₁c ⟨⟨hin, hp5, ⟨q, rfl, hdvd⟩, hN⟩, by rw [hchar]; exact hP⟩
  rw [hchar] at hgen
  set φ : CFSG.LieType.SeitzGeneration.Cat d →* G := Y.subtype.comp e0.symm.toMonoidHom with hφ
  have hle : (uniPlaneClosure q.p E₁).map φ ≤ Subgroup.closure {y : G | y ∈ Y ∧
      (∃ n : ℕ, y ^ q.p ^ n = 1) ∧ ∃ x ∈ E', x ≠ 1 ∧ Commute y x} := by
    rw [uniPlaneClosure, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨s, ⟨ε, hε, hε1, hεs, n, hn⟩, rfl⟩
    obtain ⟨c, hc, rfl⟩ := hε
    obtain ⟨x', hx', rfl⟩ := hc
    refine ⟨(e0.symm s).2, ⟨n, ?_⟩, (x' : G), Subgroup.mem_subgroupOf.1 hx', ?_, ?_⟩
    · rw [← map_pow, hn, map_one]
    · intro h1
      apply hε1
      have hx1 : x' = 1 := Subtype.ext h1
      rw [hx1, map_one, map_one]
    · have h1 : e0 x' * s * (e0 x')⁻¹ = s := hεs
      have h2 : x' * e0.symm s * x'⁻¹ = e0.symm s := by
        have h := congrArg e0.symm h1
        rwa [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at h
      have h3' : (x' : G) * ((e0.symm s : Y) : G) * (x' : G)⁻¹ = ((e0.symm s : Y) : G) := by
        have h := congrArg Subtype.val h2
        simpa using h
      exact (mul_inv_eq_iff_eq_mul.1 h3').symm
  intro y hy
  have htop : e0 ⟨y, hy⟩ ∈ uniPlaneClosure q.p E₁ := by
    rw [show uniPlaneClosure q.p E₁ = ⊤ from hgen]
    exact Subgroup.mem_top _
  have hφy : φ (e0 ⟨y, hy⟩) = y := by simp [hφ]
  exact hle ⟨_, htop, hφy⟩

theorem top_le_closure_hyperRSet_cube_E6 {P : ℕ → Prop}
    (h3 : UniSeitzPlanes fun d p E => TrialityPhi3Inner d p E ∧ P d.1.characteristic)
    (K : Type) [Field K] [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r] (hP : P r)
    (ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K) (hψ : IsSignedFrame K ψ)
    (hinj : ∀ i, Function.Injective (ψ i)) (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B))
    {p : ℕ} (g : SL(3, K)) (hp : p.Prime) (hp5 : 5 ≤ p) (hpr : p ≠ r)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) (hg : orderOf g = p) :
    (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤
      Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ (cube ψ g) r p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL Tag.E6 K) := CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨hpq, hp3⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_add_add_one_of_orderOf_eq_three hp hord
  obtain ⟨ψL, hLinj, hLcomm, hψL⟩ :=
    CFSG.HardMathSupport.Malle.SeitzCube.exists_three_sl3_E6_signed (FiniteField.Extension K r 3)
  have hψ' : ∀ i : Fin 3, ∀ γ : Fin 2 → ℤ, γ ∈ RA2 → ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      ((ψ i (CFSG.LieType.Steinberg.SL.x 2 K γ c) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        pinnedX Tag.E6 K (CFSG.HardMathSupport.Malle.SeitzCube.e6A2Frame i γ) (ε * c) := by
    intro i γ hγ
    refine ⟨(CFSG.HardMathSupport.Malle.SeitzCube.e6A2Sign i γ : K), ?_, hψ i γ hγ⟩
    rcases CFSG.HardMathSupport.Malle.SeitzCube.e6A2Sign_eq i γ with h1 | h1 <;> rw [h1] <;> simp
  have hZ : ∀ x : SL(3, K), x ^ p = 1 → (∀ A, Commute x A) → x = 1 :=
    fun _ hx hc => eq_one_of_commute_sl3 hp hp3 hx hc
  have hNQ : negRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) ≤ adjointGroup Tag.E6 K :=
    rootSpan_le_adjointGroup K _
  have hab := isElemAbelian_cube hinj hcomm hp hp3 hg
  have hcube := card_cube hinj hcomm hp hp3 hg
  have hD4 : ∀ s : ℕ, s < 3 → ∀ u : adjointGroup Tag.E6 K,
      ((u : ModGL Tag.E6 K) ∈ parabolicRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) ∨
        (u : ModGL Tag.E6 K) ∈ negRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)) →
      Commute u (ψ 0 g * ψ 1 (g ^ (Nat.card K ^ s))) →
      u ∈ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ (cube ψ g) r p) := by
    intro s hs u hu he
    obtain ⟨Y, hY1, hY2, hY3, hY4, ⟨q', hqc, hqp, hiso⟩, hcen⟩ :=
      CFSG.HardMathSupport.Malle.SeitzCube.exists_d4Line_layer hψ hp hp3 hpr hpq hg ⟨s, hs⟩
    have huY : u ∈ Y := by
      rcases hu with hu | hu
      · exact hY2 (parabolicRadicalRoots Tag.E6 (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1))
          (fun α hα => (mem_parabolicRadicalRoots_iff.1 hα).1)
          (fun F _ a v hv hva => mem_rootSpan_radical_inter_of_mem_centralizer hv hva)
          (fun F _ => (parabolicLevi_le_parabolicSubgroup _).trans
            (parabolicSubgroup_le_normalizer_parabolicRadical _)) u hu he
      · exact hY2 (negRadicalRoots Tag.E6 (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1))
          (fun α hα => isRoot_of_mem_negRadicalRoots hα)
          (fun F _ a v hv hva => mem_rootSpan_negRadicalRoots_inter_of_mem_centralizer hv hva)
          (fun F _ => parabolicLevi_le_normalizer_negRadical F _) u hu he
    set m : ℕ := Nat.card K ^ s with hm
    set e : adjointGroup Tag.E6 K := ψ 0 g * ψ 1 (g ^ m) with he_def
    set e' : adjointGroup Tag.E6 K := ψ 0 g * ψ 1 (g ^ ((p - 1) * m)) with he'_def
    have hcc : ∀ a ∈ cube ψ g, ∀ b ∈ cube ψ g, Commute a b := fun a ha b hb =>
      congrArg Subtype.val (hab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hψ1 : ∀ y : ℕ, ψ 1 (g ^ y) ∈ cube ψ g := fun y => by
      rw [map_pow]; exact Subgroup.pow_mem _ (mem_cube 1) y
    have hmix : ∀ y : ℕ, ψ 0 g * ψ 1 (g ^ y) ∈ cube ψ g := fun y =>
      Subgroup.mul_mem _ (mem_cube 0) (hψ1 y)
    have hecube : e ∈ cube ψ g := hmix m
    have he'cube : e' ∈ cube ψ g := hmix _
    have hordc : ∀ x ∈ cube ψ g, x ≠ 1 → orderOf x = p := fun x hx hx1 =>
      orderOf_eq_prime (hab.2 x hx) hx1
    have heord : orderOf e = p := hordc e hecube (by
      have := CFSG.HardMathSupport.Malle.SeitzCube.mix_ne hinj hcomm hp hp3 hg m 0
      rwa [zpow_zero] at this)
    have he'ord : orderOf e' = p := hordc e' he'cube (by
      have := CFSG.HardMathSupport.Malle.SeitzCube.mix_ne hinj hcomm hp hp3 hg ((p - 1) * m) 0
      rwa [zpow_zero] at this)
    have hBle : Subgroup.zpowers e ≤ cube ψ g := Subgroup.zpowers_le.2 hecube
    have hB : Nat.card (Subgroup.zpowers e) = p := by rw [Nat.card_zpowers, heord]
    have hBY : Disjoint (Subgroup.zpowers e) Y := by
      rw [Subgroup.disjoint_def]
      intro x hxB hxY
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxB
      refine hcen _ hxY ?_
      intro z hz
      exact ((hY1 z hz).zpow_right n).eq
    have hcent : ∀ y ∈ Y, ∀ b ∈ Subgroup.zpowers e, Commute y b := fun y hy b hb => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (hY1 y hy).zpow_right n
    have haord : orderOf (ψ 2 g) = p := hordc _ (mem_cube 2) (fun h1 => by
      have : g = 1 := hinj 2 (by rw [h1, map_one])
      rw [this, orderOf_one] at hg
      exact hp.ne_one hg.symm)
    have hE'le : Subgroup.zpowers (ψ 2 g) ⊔ Subgroup.zpowers e' ≤ cube ψ g :=
      sup_le (Subgroup.zpowers_le.2 (mem_cube 2)) (Subgroup.zpowers_le.2 he'cube)
    have hE'Y : Subgroup.zpowers (ψ 2 g) ⊔ Subgroup.zpowers e' ≤ Y :=
      sup_le (Subgroup.zpowers_le.2 hY3) (Subgroup.zpowers_le.2 hY4)
    have hdisj : Disjoint (Subgroup.zpowers (ψ 2 g)) (Subgroup.zpowers e') :=
      CFSG.HardMathSupport.Malle.SeitzCube.disjoint_zpowers_of_orderOf_prime hp he'ord (fun hmem => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
        exact CFSG.HardMathSupport.Malle.SeitzCube.mix_ne hinj hcomm hp hp3 hg ((p - 1) * m) k hk.symm)
    have hcommZ : ∀ x ∈ Subgroup.zpowers (ψ 2 g), ∀ y ∈ Subgroup.zpowers e', Commute x y :=
      fun x hx y hy => hcc x (Subgroup.zpowers_le.2 (mem_cube 2) hx) y
        (Subgroup.zpowers_le.2 he'cube hy)
    have hE'card : Nat.card ↥(Subgroup.zpowers (ψ 2 g) ⊔ Subgroup.zpowers e') = p ^ 2 := by
      rw [CFSG.HardMathSupport.Malle.SeitzCube.card_sup_of_commute _ _ hcommZ hdisj, Nat.card_zpowers,
        Nat.card_zpowers, haord, he'ord]
      ring
    have hgen := le_closure_rFixed_of_isoLie_triality (D := fun p c => p ∣ c ^ 2 + c + 1) h3 hiso
      (by rw [hqp]; exact hP) hp hp5
      (by rw [hqp]; exact hpr) (by rw [hqc]; exact hpq) hE'Y
      (fun a ha b hb => hcc a (hE'le ha) b (hE'le hb)) (fun a ha => hab.2 a (hE'le ha)) hE'card
    rw [hqp] at hgen
    exact le_closure_hyperRSet_of_rFixed hab hcube hBle hB hBY hcent hE'le hE'Y hgen huY
  have hline : ∀ B : Subgroup (adjointGroup Tag.E6 K), B ≤ plane ψ g →
      B.relIndex (plane ψ g) = p → ∀ u : adjointGroup Tag.E6 K,
      ((u : ModGL Tag.E6 K) ∈ parabolicRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) ∨
        (u : ModGL Tag.E6 K) ∈ negRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)) →
      (∃ n : ℕ, u ^ r ^ n = 1) → u ∈ Subgroup.centralizer (B : Set (adjointGroup Tag.E6 K)) →
      u ∈ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ (cube ψ g) r p) := by
    intro B hB hBi u hu hur huC
    obtain ⟨x, y, hx, hy, hxy, hbB⟩ :=
      exists_pow_mul_pow_mem_of_relIndex hinj hcomm hp hZ hg hB hBi
    have hub : Commute u (ψ 0 (g ^ x) * ψ 1 (g ^ y)) :=
      ((Subgroup.mem_centralizer_iff.1 huC) _ hbB).symm
    rcases line_cases hp (Nat.card K) hx hy hxy with ⟨hxn, s, hs⟩ | ⟨hxy', hD4'⟩
    ·
      have hs' : (y : ZMod p) = (x : ZMod p) * ((Nat.card K ^ (s : ℕ) : ℕ) : ZMod p) := by
        rw [hs]
        push_cast
        rfl
      have hu' := centralizer_pow_mul_pow_le hcomm hp hg hxn hs'
        (Subgroup.mem_centralizer_singleton_iff.2 hub.eq)
      exact hD4 s s.isLt u hu (Subgroup.mem_centralizer_singleton_iff.1 hu')
    ·
      have hu2 : (u : ModGL Tag.E6 K) ∈ ((adjointGroup Tag.E6 K).subtype.comp (ψ 2)).range := by
        rcases hu with hu | hu
        · exact mem_range_two_of_mem_radical_of_commute hψ hψL hLinj hLcomm hp hp3 hpr hpq hg
            hxy' hD4' hu (hub.map (adjointGroup Tag.E6 K).subtype)
        · exact mem_range_two_of_commute
            (S := negRadicalRoots Tag.E6 (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1))
            (fun _ _ hv hva => mem_rootSpan_negRadicalRoots_inter_of_mem_centralizer hv hva)
            (fun _ hα => not_mem_block_zero_one_of_neg_mem_radical hα)
            (parabolicLevi_le_normalizer_negRadical _ _) hψ hψL hLinj hLcomm hp hp3 hpr hpq hg
            hxy' hD4' hu (hub.map (adjointGroup Tag.E6 K).subtype)
      obtain ⟨z, hz⟩ := hu2
      have hz' : ψ 2 z = u := Subtype.ext hz
      refine Subgroup.subset_closure ⟨Subgroup.mem_top _, hur,
        cube ψ g ⊓ Subgroup.centralizer ((ψ 2).range : Set (adjointGroup Tag.E6 K)), inf_le_left,
        relIndex_cube_inf_centralizer hinj hcomm hp hp3 hg 2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      rw [← hz']
      exact ((Subgroup.mem_centralizer_iff.1 hf.2) _ ⟨z, rfl⟩).symm
  set Q : Subgroup (adjointGroup Tag.E6 K) :=
    parabolicRadicalIn Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) with hQdef
  set Q' : Subgroup (adjointGroup Tag.E6 K) :=
    (negRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)).subgroupOf (adjointGroup Tag.E6 K)
    with hQ'def
  have hQr : IsPGroup r Q := by
    have := Fintype.ofFinite K
    exact isPGroup_radicalIn_E6 K
  have hQ'r : IsPGroup r Q' :=
    (isPGroup_negRadical K _).of_equiv (Subgroup.subgroupOfEquivOfLe hNQ).symm
  have htop : (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ Q ⊔ Q' := by
    intro u _
    have : IsSimpleGroup (adjointGroup Tag.E6 K) := isSimpleGroup_adjointGroup_of_isQuasisimple
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K)
    have hAB := adjointGroup_le_parabolicRadical_sup_negRadical K (r := r) e6PlaneLeviSet_ne_univ u.2
    rw [hQdef, hQ'def, parabolicRadicalIn,
      ← Subgroup.subgroupOf_sup (CFSG.LieType.Chevalley.parabolicRadical_le_adjointGroup _) hNQ]
    exact Subgroup.mem_subgroupOf.2 hAB
  have hnQ : plane ψ g ≤ Subgroup.normalizer (Q : Set (adjointGroup Tag.E6 K)) :=
    plane_le_normalizer_radicalIn_E6 K ψ hψ' g
  have hnQ' : plane ψ g ≤ Subgroup.normalizer (Q' : Set (adjointGroup Tag.E6 K)) := by
    intro x hx
    have hL : ((x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
        parabolicLevi Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) :=
      plane_le_parabolicLevi_E6 K ψ hψ' g ⟨x, hx, rfl⟩
    have hN := parabolicLevi_le_normalizer_negRadical K _ hL
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro y
    have hy := hN (y : ModGL Tag.E6 K)
    simp only [hQ'def, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hy
  obtain ⟨hA, hA1⟩ := plane_spec hinj hcomm hp hp3 hg
  haveI : IsElementaryAbelian p (plane ψ g) :=
    CFSG.LieType.SeitzGeneration.isElementaryAbelian_of_isElemAbelian hA
  haveI : Nontrivial (plane ψ g) := (Subgroup.nontrivial_iff_ne_bot _).2 hA1
  have hrp : r ≠ p := fun h => hpr h.symm
  have hQp : ¬ p ∣ Nat.card Q := CFSG.LieType.Chevalley.not_dvd_card_of_isPGroup hrp hQr
  have hQ'p : ¬ p ∣ Nat.card Q' := CFSG.LieType.Chevalley.not_dvd_card_of_isPGroup hrp hQ'r
  have hQle : Q ≤ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ (cube ψ g) r p) := by
    refine (CFSG.LieType.Chevalley.le_closure_hyperRSet_of_coprime (C := Q) hQr hQp hnQ le_rfl).trans
      ((Subgroup.closure_le _).2 ?_)
    rintro u ⟨huQ, hur, B, hB, hBi, huB⟩
    exact hline B hB hBi u (Or.inl (Subgroup.mem_subgroupOf.1 huQ)) hur huB
  have hQ'le : Q' ≤ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ (cube ψ g) r p) := by
    refine (CFSG.LieType.Chevalley.le_closure_hyperRSet_of_coprime (C := Q') hQ'r hQ'p hnQ'
      le_rfl).trans ((Subgroup.closure_le _).2 ?_)
    rintro u ⟨huQ, hur, B, hB, hBi, huB⟩
    exact hline B hB hBi u (Or.inr (Subgroup.mem_subgroupOf.1 huQ)) hur huB
  exact htop.trans (sup_le hQle hQ'le)

theorem uniPlaneGen_of_sylowTorus_rgen {d : TauCeti.ValidLieTypeIndex} {p m : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : CFSG.LieType.SeitzGeneration.Cat d →* _))
    (hS : SylowTorus (CFSG.LieType.SeitzGeneration.Cat d) p m)
    {Ec : Subgroup (CFSG.LieType.SeitzGeneration.Cat d)} (hEcel : IsElemAbelian p Ec)
    (hEcc : Nat.card Ec = p ^ m)
    (hgen : (⊤ : Subgroup (CFSG.LieType.SeitzGeneration.Cat d)) ≤
      Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ Ec d.1.characteristic p))
    {E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d))} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hin : InnerPlane d p E) : UniPlaneGen d.1.characteristic E := by
  classical
  obtain ⟨E', hE'el, hE'c, hE'map⟩ := CFSG.HardMathSupport.Lang.AnisoE6.exists_map_conj_eq hinj hin hE hEc
  obtain ⟨T, V0, -, hconj, hV0T, hV0tor, hV0el, hV0c⟩ := hS.exists_torus
  obtain ⟨g, hg⟩ := hconj E' (CFSG.Open.IsElemAbelian.isPGroup hE'el)
  set V : Subgroup (CFSG.LieType.SeitzGeneration.Cat d) := V0.map (MulAut.conj g).toMonoidHom with hVdef
  have hVel : IsElemAbelian p V :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hV0el _
  have hVc : Nat.card V = p ^ m := by
    rw [hVdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hV0c]
  have hE'V : E' ≤ V := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := hg hx
    have htp : t ^ p = 1 := by
      have h1 := hE'el.2 x hx
      rw [← hxt] at h1
      have : (MulAut.conj g) (t ^ p) = 1 := by
        rw [map_pow]
        exact h1
      exact (MulAut.conj g).injective (this.trans (map_one _).symm)
    exact ⟨t, hV0tor t ht htp, hxt⟩
  obtain ⟨x, hx⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.exists_conj_of_sylowTorus_cube hp hS hEcel hEcc hVel hVc
  have hVgen : (⊤ : Subgroup (CFSG.LieType.SeitzGeneration.Cat d)) ≤
      Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ V d.1.characteristic p) := by
    refine CFSG.LieType.SeitzGeneration.QuasiHigh.closure_hyperRSet_of_mulEquiv (MulAut.conj x)⁻¹ ?_
    have hVEc : V.map ((MulAut.conj x)⁻¹ : MulAut _).toMonoidHom = Ec := by
      rw [hx, Subgroup.map_map]
      convert Subgroup.map_id Ec
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    rw [hVEc]
    exact hgen
  rw [UniPlaneGen, eq_top_iff]
  refine hVgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro s ⟨-, ⟨n, hn⟩, B, hBV, hBi, hsB⟩
  obtain ⟨y, hyEB, hy1⟩ := CFSG.LieType.SeitzGeneration.ExcHigh.exists_ne_one_mem_plane_inf_hyperplane hp hE'V
    hE'c hBi (by rw [hVc]; exact (pow_pos hp.pos m).ne')
  refine mem_uniPlaneClosure (e := MulAut.conj y) ?_ ?_ ?_ hn
  · rw [← hE'map]
    exact Subgroup.mem_map_of_mem _ hyEB.1
  · intro h1
    exact hy1 (hinj (by rw [h1, map_one]))
  · rw [MulAut.conj_apply, Subgroup.mem_centralizer_iff.1 hsB y hyEB.2, mul_inv_cancel_right]

theorem uniSeitzPlanes_E6Three_inner_of_triality {P : ℕ → Prop}
    (h3 : UniSeitzPlanes fun d p E => TrialityPhi3Inner d p E ∧ P d.1.characteristic) :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 3) ∧
      P d.1.characteristic := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, hord⟩, hch⟩
  obtain rfl : d = .E6 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar : (TauCeti.LieTypeIndex.E6 q).characteristic = q.p := TauCeti.LieTypeIndex.characteristic_E6 q
  have hpq : p ≠ q.p := fun h => hpd (by rw [hchar]; exact h)
  have hq2 : P q.p := by rw [← hchar]; exact hch
  have h7 := CFSG.LieType.SeitzGeneration.ExcHigh.seven_le_of_orderOf_three hp hp5 hord
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  obtain ⟨ψ, hinj, hcomm, hψ⟩ := CFSG.HardMathSupport.Malle.SeitzCube.exists_three_sl3_E6_signed K
  obtain ⟨hdvd, hp3⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_add_add_one_of_orderOf_eq_three hp hord
  have hdvdK : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by rw [hK]; exact hdvd
  obtain ⟨g, hg⟩ := exists_sl3_orderOf (K := K) hp hp3 hdvdK
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 := by rw [hK]; exact hord
  have hgen := top_le_closure_hyperRSet_cube_E6 h3 K q.p hq2 ψ hψ hinj hcomm g hp hp5 hpq hordK hg
  set Vc : Subgroup (CFSG.LieType.SeitzGeneration.Cat ⟨.E6 q, hv⟩) := (cube ψ g).map e.symm.toMonoidHom
    with hVc
  have hVcmap : Vc.map e.toMonoidHom = cube ψ g := by
    rw [hVc, Subgroup.map_map]
    convert Subgroup.map_id (cube ψ g)
    ext y
    simp
  have hVcgen : (⊤ : Subgroup (CFSG.LieType.SeitzGeneration.Cat ⟨.E6 q, hv⟩)) ≤
      Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ Vc q.p p) := by
    refine CFSG.LieType.SeitzGeneration.QuasiHigh.closure_hyperRSet_of_mulEquiv e ?_
    rw [hVcmap]
    exact hgen
  have hVcel : IsElemAbelian p Vc :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p (isElemAbelian_cube hinj hcomm hp hp3 hg) _
  have hVcc : Nat.card Vc = p ^ 3 := by
    rw [hVc, Subgroup.card_map_of_injective e.symm.injective]
    exact card_cube hinj hcomm hp hp3 hg
  rw [← hchar] at hVcgen
  exact uniPlaneGen_of_sylowTorus_rgen hp (CFSG.HardMathSupport.Malle.SeitzCube.conj_injective_cat_E6 q hv)
    (CFSG.LieType.SeitzGeneration.ExcHigh.sylowTorus_cat_E6_three hv hp h7 hpq hord) hVcel hVcc hVcgen hE hc hin

end E6ThreeR

section TwE6SixR

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
open CFSG.RankThree.Chevalley (d4Support d4Layer)

open CFSG.HardMathSupport.Lang.TwE6Step3
open scoped Matrix

set_option linter.unusedSectionVars false

theorem eq_one_of_mem_torusGroup_of_pow_pow_j {τ : Tag} {L : Type} [Field L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    {t : ModGL τ L} (ht : t ∈ torusGroup τ L) {m : ℕ} (h : t ^ (ℓ ^ m) = 1) : t = 1 := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    apply ih
    have h' : (t ^ (ℓ ^ m)) ^ ℓ = 1 := by rw [← pow_mul, ← pow_succ]; exact h
    exact eq_one_of_mem_torusGroup_of_pow_char_j (Subgroup.pow_mem _ ht _) h'

theorem not_dvd_orderOf_of_mem_torusGroup_j {τ : Tag} {L : Type} [Field L] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    [CharP L ℓ] {t : ModGL τ L} (ht : t ∈ torusGroup τ L) (h0 : orderOf t ≠ 0) : ¬ ℓ ∣ orderOf t := by
  rintro ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact h0 hc
  have h1 : (t ^ c) ^ ℓ = 1 := by
    rw [← pow_mul, mul_comm, ← hc, pow_orderOf_eq_one]
  have h2 : t ^ c = 1 := eq_one_of_mem_torusGroup_of_pow_char_j (Subgroup.pow_mem _ ht c) h1
  have h3 : orderOf t ∣ c := orderOf_dvd_of_pow_eq_one h2
  rw [hc] at h3
  have h4 := Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) h3
  have h5 := hℓ.out.two_le
  nlinarith [Nat.pos_of_ne_zero hc0]

theorem mul_mem_of_rElement_j {G : Type*} [Group G] {N : Subgroup G} {k₀ n : G} {r m : ℕ} (hr : r.Prime)
    (hn : n ∈ N) (hk₀N : ∀ z ∈ N, k₀⁻¹ * z * k₀ ∈ N) (hcop : ¬ r ∣ orderOf k₀)
    (hk : (k₀ * n) ^ (r ^ m) = 1) : k₀ * n ∈ N := by
  have hpow : ∀ j : ℕ, ∃ n' ∈ N, (k₀ * n) ^ j = k₀ ^ j * n' := by
    intro j
    induction j with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨n', hn', he⟩ := ih
      refine ⟨k₀⁻¹ * n' * k₀ * n, N.mul_mem (hk₀N n' hn') hn, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨n', hn', he⟩ := hpow (r ^ m)
  have hk₀m : k₀ ^ (r ^ m) ∈ N := by
    rw [hk] at he
    rw [eq_inv_of_mul_eq_one_left he.symm]
    exact inv_mem hn'
  have hcopr : (r ^ m).Coprime (orderOf k₀) :=
    Nat.Coprime.pow_left m ((Nat.coprime_or_dvd_of_prime hr _).resolve_right hcop)
  have hk₀ : k₀ ∈ Subgroup.zpowers (k₀ ^ (r ^ m)) := mem_zpowers_pow_iff.2 hcopr
  exact N.mul_mem ((Subgroup.zpowers_le.2 hk₀m) hk₀) hn

theorem mem_closure_hyperRSet_of_commute_pair_j {Y : Type*} [Group Y] {p r : ℕ} [hp : Fact p.Prime]
    {E : Subgroup Y} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {y e : Y}
    (hy : y ∈ E) (he : e ∈ E) (hy1 : y ≠ 1) (hey : e ∉ Subgroup.zpowers y) {k : Y}
    (hky : k * y = y * k) (hke : k * e = e * k) (hkr : ∃ n : ℕ, k ^ r ^ n = 1) :
    k ∈ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ E r p) := by
  classical
  have hFE : Subgroup.closure {y, e} ≤ E := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [hy, he]
  have hye : y * e = e * y := congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨e, he⟩)
  have hyp : y ^ p = 1 := hE.2 y hy
  have hep : e ^ p = 1 := hE.2 e he
  have hcardF : Nat.card (Subgroup.closure ({y, e} : Set Y)) = p ^ 2 := by
    have : NeZero p := ⟨hp.out.ne_zero⟩
    have hle := card_closure_pair_le_sq hye hyp hep
    have hzy : Nat.card (Subgroup.zpowers y) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1]
    have hlt : Subgroup.zpowers y < Subgroup.closure {y, e} := by
      refine lt_of_le_of_ne ?_ fun h => hey ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
      · rw [h]
        exact Subgroup.subset_closure (by simp)
    have hfinE : Finite E :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
    have : Finite (Subgroup.closure ({y, e} : Set Y)) :=
      Finite.of_injective (Subgroup.inclusion hFE) (Subgroup.inclusion_injective hFE)
    have hgt := Subgroup.card_lt_of_lt hlt
    have hdvd : Nat.card (Subgroup.closure ({y, e} : Set Y)) ∣ p ^ 3 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hFE
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    rw [hk'] at hle hgt ⊢
    rw [hzy] at hgt
    have h2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
    have h1 : 1 < k := by
      by_contra hk1
      push Not at hk1
      interval_cases k
      · simp at hgt
        exact absurd hgt (by have := hp.out.one_lt; omega)
      · simp at hgt
    have : k = 2 := by omega
    rw [this]
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, hkr, Subgroup.closure {y, e}, hFE,
    CFSG.HardMathSupport.Malle.SeitzCube.relIndex_eq_of_card hFE hp.out.pos hcardF hcard, ?_⟩
  have hc : Subgroup.closure {y, e} ≤ Subgroup.centralizer {k} := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl
    exacts [hky.symm, hke.symm]
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  exact Subgroup.mem_centralizer_singleton_iff.1 (hc hf)

theorem mem_closure_hyperRSet_of_mulEquiv_j {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {r p : ℕ} {A : Subgroup G} {k : G}
    (h : e k ∈ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ (A.map e.toMonoidHom) r p)) :
    k ∈ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ A r p) := by
  have hA : (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext x
    simp
  have hS : e.symm.toMonoidHom '' CFSG.LieType.Chevalley.hyperRSet ⊤ (A.map e.toMonoidHom) r p ⊆
      CFSG.LieType.Chevalley.hyperRSet ⊤ A r p := by
    rintro _ ⟨y, ⟨-, ⟨n, hn⟩, B, hB, hBi, hyB⟩, rfl⟩
    refine ⟨Subgroup.mem_top _, ⟨n, by rw [← map_pow, hn, map_one]⟩,
      B.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
    · rw [← hA]
      exact Subgroup.map_mono hB
    · rw [← hA, Subgroup.relIndex_map_map_of_injective _ _ e.symm.injective, hBi]
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hyB b hb]
  have hle : (Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ (A.map e.toMonoidHom) r p)).map
      e.symm.toMonoidHom ≤ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ A r p) := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hS
  exact hle (Subgroup.mem_map.2 ⟨e k, h, (by simp : e.symm.toMonoidHom (e k) = k)⟩)

theorem le_closure_of_map_le_j {G H : Type*} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ)
    {X : Subgroup G} {P : Subgroup H} {T : Set G} {W : Set H}
    (hXP : ∀ x ∈ X, φ x ∈ P) (hP : P ≤ Subgroup.closure W) (hW : W ⊆ φ '' T) :
    X ≤ Subgroup.closure T := by
  intro x hx
  have h1 : φ x ∈ (Subgroup.closure T).map φ := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hW (hP (hXP x hx))
  obtain ⟨x', hx', hxx'⟩ := h1
  rw [← hφ hxx']
  exact hx'

theorem ringChar_dvd_card_of_rootSL2_mem_j {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    {P : Subgroup (ModGL τ L)} (i : Fin τ.rank) (h₀ : ModGL τ L)
    (hroot : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K,
      h₀ * simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map (algebraMap K L) B) * h₀⁻¹ ∈ P) :
    ringChar K ∣ Nat.card P := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hr, -⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hr⟩
  obtain ⟨Y, hY1, hYr⟩ := Inputs2311g.exists_sl2_rElement_ne_one K
  have hzP := hroot Y
  have hzr : (h₀ * simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹) ^
      ringChar K = 1 := by
    rw [conj_pow, ← map_pow, ← map_pow, hYr, map_one, map_one, mul_one, mul_inv_cancel]
  have hz1 : h₀ * simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ≠ 1 := by
    intro h
    apply hY1
    have h1 : simpleRootSL2 τ L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) = 1 := by
      have := congrArg (fun w => h₀⁻¹ * w * h₀) h
      simpa [mul_assoc] using this
    apply CFSG.GH74.Filter.Lie.sl2_map_injective (algebraMap K L)
    apply CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_field τ i
    rw [h1, map_one, map_one]
  have ho : orderOf (⟨_, hzP⟩ : P) = ringChar K := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hzr hz1
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem eq_one_of_kernel_empty_tw {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} [hpF : Fact p.Prime] (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    {E : Subgroup (twistedE6RootGroup K σ)} (hE : IsElemAbelian p E)
    (c : twistedE6RootGroup K σ)
    (hT : ∀ e ∈ E, psiT g0 c e ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)))
    {y : twistedE6RootGroup K σ} (hy : y ∈ E) (hy1 : y ≠ 1)
    (hSig : torusRootKernel (psiT g0 c y) = ∅) {k : twistedE6RootGroup K σ} (hk : k * y = y * k)
    {m : ℕ} (hkr : k ^ (ℓ ^ m) = 1) : k = 1 := by
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  obtain ⟨ι', KL, ψ, -, hψ, hspan, -⟩ := tw6_perx K hf hK σ hσ hpF.out hp3 hpq L hg0C hg0 hperf
    hyo c (hT y hy)
  have hkC : k ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk
  have hψk := hspan ⟨k, hkC⟩
  rw [hψ] at hψk
  change psiT g0 c k ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel (psiT g0 c y)) at hψk
  rw [hSig] at hψk
  have hbot : rootSpan Tag.E6 L (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rw [hbot, sup_bot_eq] at hψk
  have hpow : psiT g0 c k ^ (ℓ ^ m) = 1 := by rw [← psiT_pow, hkr, psiT_one]
  have h1 : psiT g0 c k = 1 := eq_one_of_mem_torusGroup_of_pow_pow_j hψk hpow
  exact psiT_injective g0 c (h1.trans (psiT_one g0 c).symm)

theorem mem_closure_hyperRSet_of_kernel_A2_tw {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} [hpF : Fact p.Prime] (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    {E : Subgroup (twistedE6RootGroup K σ)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (c : twistedE6RootGroup K σ)
    (hT : ∀ e ∈ E, psiT g0 c e ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)))
    {y : twistedE6RootGroup K σ} (hy : y ∈ E) (hy1 : y ≠ 1)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (psiT g0 c y) = parabolicRoots Tag.E6 support13)
    {k : twistedE6RootGroup K σ} (hk : k * y = y * k) {m : ℕ} (hkr : k ^ (ℓ ^ m) = 1) :
    k ∈ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ E ℓ p) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c, (iterateFrobenius L ℓ f) c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨w, hw⟩ := hA2
  set β : Fin Tag.E6.rank → ℤ := w⁻¹ • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) with hβdef
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  have hsingle : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ rootFinset .E6 := by decide +kernel
  have hβS : β ∈ torusRootKernel (psiT g0 c y) := by
    have hmem : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 support13 := by
      refine ⟨mem_rootFinset.1 hsingle, fun i hi => ?_⟩
      have hi0 : i ≠ 0 := fun h => hi (h ▸ Or.inl rfl)
      simp [hi0]
    rw [← hw] at hmem
    obtain ⟨α, hα, hαw⟩ := hmem
    rw [hβdef, ← hαw, inv_smul_smul]
    exact hα
  have hβroot : IsRoot Tag.E6 β := hβS.1
  have hET : ∀ e ∈ E, psiT g0 c e ∈ torusGroup Tag.E6 L := fun e he => (mem_twistedTorusOf.1 (hT e he)).1
  obtain ⟨⟨e, he⟩, hey, hχe⟩ := exists_mem_ker_not_mem_zpowers hE hEc (cubeChar g0 c hET β) hy
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hET e he)
  have hbβ : rootChar b β = 1 := (cubeChar_eq_one_iff hET hβroot ⟨e, he⟩ hb).1 hχe
  have hbT : rootDiagUnit Tag.E6 b ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)) := by
    rw [← hb]
    exact hT e he
  have hsub := subset_rootCharKernel_of_A2 hFr (hT y hy) hw hbT hbβ
  have hcent : torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel (psiT g0 c y)) ≤
      Subgroup.centralizer {rootDiagUnit Tag.E6 b} := by
    refine sup_le ?_ (CFSG.LieType.Chevalley.rootSpan_le_centralizer b hsub)
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact torusGroup_comm hx (mem_twistedTorusOf.1 hbT).1
  obtain ⟨ι', KL, ψ, -, hψ, hspan, -⟩ := tw6_perx K hf hK σ hσ hpF.out hp3 hpq L hg0C hg0 hperf
    hyo c (hT y hy)
  have hkC : k ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk
  have hψk : psiT g0 c k ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel (psiT g0 c y)) := by
    have h := hspan ⟨k, hkC⟩
    rw [hψ] at h
    exact h
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (hcent hψk)
  rw [← hb] at hc
  have hc' : psiT g0 c k * psiT g0 c e = psiT g0 c e * psiT g0 c k := hc
  have hke : k * e = e * k := by
    apply psiT_injective g0 c
    rw [psiT_mul, psiT_mul]
    exact hc'
  exact mem_closure_hyperRSet_of_commute_pair_j hE hEc hy he hy1 hey hk hke ⟨m, hkr⟩

theorem mem_closure_hyperRSet_of_kernel_A2A2_tw {ℓ f : ℕ} [hℓF : Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} [hpF : Fact p.Prime] (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    {E : Subgroup (twistedE6RootGroup K σ)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (c : twistedE6RootGroup K σ)
    (hT : ∀ e ∈ E, psiT g0 c e ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)))
    {y : twistedE6RootGroup K σ} (hy : y ∈ E) (hy1 : y ≠ 1) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' torusRootKernel (psiT g0 c y) = parabolicRoots Tag.E6 supportA2A2)
    (hsplit : TwoA2Split L (iterateFrobenius L ℓ f)
      ((fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support13)
      ((fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support56))
    {k : twistedE6RootGroup K σ} (hk : k * y = y * k) {m : ℕ} (hkr : k ^ (ℓ ^ m) = 1) :
    k ∈ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ E ℓ p) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  set Sx := torusRootKernel (psiT g0 c y) with hSxdef
  have hvS := tw6_torusRootKernel_smul_stable hFr (hT y hy)
  have hT' : ∀ β ∈ parabolicRoots Tag.E6 supportA2A2,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 supportA2A2 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨hT13, hT56⟩ := conj_e6T3W_preserves_blocks hT'
  set S₁ : Set (Fin Tag.E6.rank → ℤ) :=
    (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support13 with hS₁
  set S₂ : Set (Fin Tag.E6.rank → ℤ) :=
    (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support56 with hS₂
  have hw₁ : (w • ·) '' S₁ = parabolicRoots Tag.E6 support13 := by
    rw [hS₁, Set.image_image]
    simp
  have hw₂ : (w • ·) '' S₂ = parabolicRoots Tag.E6 support56 := by
    rw [hS₂, Set.image_image]
    simp
  have hvS₁ : ∀ α ∈ S₁, e6T3W • α ∈ S₁ := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨(w * e6T3W * w⁻¹) • β, hT13 β hβ, by simp [mul_smul]⟩
  have hvS₂ : ∀ α ∈ S₂, e6T3W • α ∈ S₂ := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨(w * e6T3W * w⁻¹) • β, hT56 β hβ, by simp [mul_smul]⟩
  have hSx : Sx = S₁ ∪ S₂ := by
    ext α
    constructor
    · intro hα
      have hmem : w • α ∈ parabolicRoots Tag.E6 supportA2A2 := hw ▸ ⟨α, hα, rfl⟩
      have h13 : (w • α) 1 = 0 ∧ (w • α) 3 = 0 := by
        refine ⟨hmem.2 1 ?_, hmem.2 3 ?_⟩ <;> (rw [mem_supportA2A2]; decide)
      rcases supportA2A2_root_split _ (mem_rootFinset.2 hmem.1) h13 with h | h
      · left
        refine ⟨w • α, ⟨hmem.1, fun i hi => ?_⟩, by simp⟩
        have hiA : i ∈ supportA2A2 ∨ i ∉ supportA2A2 := em _
        rcases hiA with hiA | hiA
        · rw [mem_supportA2A2] at hiA
          rcases hiA with rfl | rfl | rfl | rfl
          · exact absurd (Or.inl rfl) hi
          · exact absurd (Or.inr rfl) hi
          · exact h.1
          · exact h.2
        · exact hmem.2 i hiA
      · right
        refine ⟨w • α, ⟨hmem.1, fun i hi => ?_⟩, by simp⟩
        have hiA : i ∈ supportA2A2 ∨ i ∉ supportA2A2 := em _
        rcases hiA with hiA | hiA
        · rw [mem_supportA2A2] at hiA
          rcases hiA with rfl | rfl | rfl | rfl
          · exact h.1
          · exact h.2
          · exact absurd (Or.inl rfl) hi
          · exact absurd (Or.inr rfl) hi
        · exact hmem.2 i hiA
    · rintro (⟨β, hβ, rfl⟩ | ⟨β, hβ, rfl⟩)
      · have hβA : β ∈ parabolicRoots Tag.E6 supportA2A2 :=
          ⟨hβ.1, fun i hi => hβ.2 i (fun hi' => hi (by
            rw [mem_supportA2A2]
            rcases hi' with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)))⟩
        rw [← hw] at hβA
        obtain ⟨α, hα, rfl⟩ := hβA
        simpa using hα
      · have hβA : β ∈ parabolicRoots Tag.E6 supportA2A2 :=
          ⟨hβ.1, fun i hi => hβ.2 i (fun hi' => hi (by
            rw [mem_supportA2A2]
            rcases hi' with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))))⟩
        rw [← hw] at hβA
        obtain ⟨α, hα, rfl⟩ := hβA
        simpa using hα
  have hET : ∀ e ∈ E, psiT g0 c e ∈ torusGroup Tag.E6 L :=
    fun e he => (mem_twistedTorusOf.1 (hT e he)).1
  have hblock : ∀ (i j : Fin Tag.E6.rank) (J : Set (Fin Tag.E6.rank)) (S : Set (Fin Tag.E6.rank → ℤ)),
      (∀ k, k ∈ J ↔ (k = i ∨ k = j)) → i ≠ j →
      (∀ α ∈ rootFinset .E6, (∀ k : Fin Tag.E6.rank, k ≠ i → k ≠ j → α k = 0) →
        (α j = 1 ∨ α j = -1) ∨ (α = Pi.single i 1 ∨ α = -Pi.single i 1)) →
      (∀ α ∈ S, e6T3W • α ∈ S) → (w • ·) '' S = parabolicRoots Tag.E6 J →
      ∃ e ∈ E, e ∉ Subgroup.zpowers y ∧
        rootSpan Tag.E6 L S ≤ Subgroup.centralizer {psiT g0 c e} := by
    intro i j J S hJ hij hcases hvS' hwS
    have hβroot : IsRoot Tag.E6 (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) :=
      IsRoot.smul (isRoot_single Tag.E6 i) w⁻¹
    obtain ⟨⟨e, he⟩, hey, hχe⟩ := exists_mem_ker_not_mem_zpowers hE hEc
      (cubeChar g0 c hET (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) hy
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hET e he)
    have hbβ := (cubeChar_eq_one_iff hET hβroot ⟨e, he⟩ hb).1 hχe
    have hbT : rootDiagUnit Tag.E6 b ∈ twistedTorusOf (tw6N L) (twistE6 L Fr) := by
      rw [← hb]
      exact hT e he
    have hsub := subset_rootCharKernel_of_block hFr hvS' hJ hij hcases hwS hbT hbβ
    refine ⟨e, he, hey, ?_⟩
    rw [hb]
    exact CFSG.LieType.Chevalley.rootSpan_le_centralizer b hsub
  obtain ⟨e₁, he₁, he₁y, hc₁⟩ := hblock 0 2 support13 S₁ (fun k => Iff.rfl) (by decide)
    support13_root_cases hvS₁ hw₁
  obtain ⟨e₂, he₂, he₂y, hc₂⟩ := hblock 4 5 support56 S₂ (fun k => Iff.rfl) (by decide)
    support56_root_cases hvS₂ hw₂
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
  have : Finite (fixSubfield σ) := inferInstance
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_twisted hℓ hf hK σ hσ
  haveI : CharP (fixSubfield σ) ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (k := f) hf hkc
  have hp7 : 7 ≤ p := (e6Six_data hpF.out hp3 hpq).2.2.2.2.1
  have hq3 : 3 ≤ ℓ ^ f := by
    by_contra hlt
    have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
    have h2 : ℓ ^ f = 2 := by omega
    rw [h2] at hpq
    norm_num at hpq
    have := Int.le_of_dvd (by norm_num) hpq
    omega
  have hroots₁ : ∀ α ∈ S₁, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 w⁻¹
  have hroots₂ : ∀ α ∈ S₂, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 w⁻¹
  obtain ⟨-, hfin₁, hq₁, -, h₀₁, hh₀₁⟩ := tw6_A2_layer_gen (Fr := Fr) hf hkc hq3 hFr hroots₁ hvS₁ hw₁
  obtain ⟨-, hfin₂, hq₂, -, h₀₂, hh₀₂⟩ := tw6_A2_layer_gen₂ (Fr := Fr) hf hkc hq3 hFr hroots₂ hvS₂ hw₂
  obtain ⟨ι', KL, ψ, -, hψ, hspan, hfix, -⟩ := tw6_perx K hf hK σ hσ hpF.out hp3 hpq L hg0C hg0
    hperf hyo c (hT y hy)
  have hkC : k ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk
  have hψk : psiT g0 c k ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (S₁ ∪ S₂) := by
    have h := hspan ⟨k, hkC⟩
    rw [hψ] at h
    change psiT g0 c k ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L Sx at h
    rw [hSx] at h
    exact h
  have hθk : tw6Theta L Fr (psiT g0 c k) = psiT g0 c k := by
    have h := hfix ⟨k, hkC⟩
    rw [hψ] at h
    rw [tw6Theta_apply]
    exact h
  obtain ⟨t, htH, htθ, a₁, ha₁S, ha₁θ, a₂, ha₂S, ha₂θ, hdec⟩ := hsplit _ hψk hθk
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hET y hy)
  have hcy : rootSpan Tag.E6 L Sx ≤ Subgroup.centralizer {psiT g0 c y} := by
    rw [hb]
    refine CFSG.LieType.Chevalley.rootSpan_le_centralizer b ?_
    rw [hSxdef, hb, torusRootKernel_rootDiagUnit]
  have hland : ∀ (S : Set (Fin Tag.E6.rank → ℤ)), S ⊆ Sx →
      Finite ↥(rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _)) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _)) →
      ∀ a ∈ rootSpan Tag.E6 L S, tw6Theta L Fr a = a →
        ∃ x : twistedE6RootGroup K σ, psiT g0 c x = a ∧ x * y = y * x := by
    intro S hS hfinS hqS a haS haθ
    have hperfS := Subgroup.isPerfect_iff.1 hqS.1
    have hadjS : rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _) ≤
        adjointGroup Tag.E6 L := fun u hu => rootSpan_le_adjointGroup L S hu.1
    have hfixS : ∀ u ∈ rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _),
        tw6N L * twistE6 L Fr u * (tw6N L)⁻¹ = u := fun u hu => by
      rw [← tw6Theta_apply]
      exact hu.2
    obtain ⟨x, hx⟩ := exists_psiT_eq_of_mem hg0C hg0 hperf c hfinS hperfS hadjS hfixS
      (u := a) ⟨haS, haθ⟩
    refine ⟨x, hx, ?_⟩
    have hca : a ∈ Subgroup.centralizer {psiT g0 c y} :=
      hcy (CFSG.LieType.Chevalley.rootSpan_mono hS haS)
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hca
    rw [← hx] at hc
    exact commute_of_psiT_commute hc
  have hS₁x : S₁ ⊆ Sx := by rw [hSx]; exact Set.subset_union_left
  have hS₂x : S₂ ⊆ Sx := by rw [hSx]; exact Set.subset_union_right
  obtain ⟨x₁, hx₁, -⟩ := hland S₁ hS₁x hfin₁ hq₁ a₁ ha₁S ha₁θ
  obtain ⟨x₂, hx₂, -⟩ := hland S₂ hS₂x hfin₂ hq₂ a₂ ha₂S ha₂θ
  set k₀ := k * x₂⁻¹ * x₁⁻¹ with hk₀
  have hψk₀ : psiT g0 c k₀ = t := by
    rw [hk₀, psiT_mul, psiT_mul, psiT_inv, psiT_inv, hx₁, hx₂, hdec]
    group
  let ψh : twistedE6RootGroup K σ →* ModGL Tag.E6 L := MonoidHom.mk' (psiT g0 c) (psiT_mul g0 c)
  set X₁ : Subgroup (twistedE6RootGroup K σ) := (rootSpan Tag.E6 L S₁).comap ψh with hX₁
  set X₂ : Subgroup (twistedE6RootGroup K σ) := (rootSpan Tag.E6 L S₂).comap ψh with hX₂
  have hx₁X : x₁ ∈ X₁ := by
    show psiT g0 c x₁ ∈ rootSpan Tag.E6 L S₁
    rw [hx₁]
    exact ha₁S
  have hx₂X : x₂ ∈ X₂ := by
    show psiT g0 c x₂ ∈ rootSpan Tag.E6 L S₂
    rw [hx₂]
    exact ha₂S
  have hconjS : ∀ (S : Set (Fin Tag.E6.rank → ℤ)), (∀ α ∈ S, IsRoot Tag.E6 α) → ∀ z,
      psiT g0 c z ∈ rootSpan Tag.E6 L S → psiT g0 c (k₀⁻¹ * z * k₀) ∈ rootSpan Tag.E6 L S := by
    intro S hS z hz
    rw [psiT_mul, psiT_mul, psiT_inv, hψk₀]
    have hnorm := CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS (inv_mem htH)
    have h := (Subgroup.mem_normalizer_iff.1 hnorm (psiT g0 c z)).1 hz
    simpa using h
  have hk₀N : ∀ z ∈ X₁ ⊔ X₂, k₀⁻¹ * z * k₀ ∈ X₁ ⊔ X₂ := by
    intro z hz
    have hle : (X₁ ⊔ X₂).map (MulAut.conj k₀⁻¹).toMonoidHom ≤ X₁ ⊔ X₂ := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        show psiT g0 c (k₀⁻¹ * z * k₀⁻¹⁻¹) ∈ rootSpan Tag.E6 L S₁
        rw [inv_inv]
        exact hconjS S₁ hroots₁ z hz
      · rintro _ ⟨z, hz, rfl⟩
        show psiT g0 c (k₀⁻¹ * z * k₀⁻¹⁻¹) ∈ rootSpan Tag.E6 L S₂
        rw [inv_inv]
        exact hconjS S₂ hroots₂ z hz
    have h := hle ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using h
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hk₀ord : ¬ ℓ ∣ orderOf k₀ := by
    have h0 : orderOf (psiT g0 c k₀) = orderOf k₀ := orderOf_injective ψh (psiT_injective g0 c) k₀
    rw [hψk₀] at h0
    rw [← h0]
    exact not_dvd_orderOf_of_mem_torusGroup_j htH (by rw [h0]; exact (orderOf_pos k₀).ne')
  have hkeq : k = k₀ * (x₁ * x₂) := by rw [hk₀]; group
  have hkN : k ∈ X₁ ⊔ X₂ := by
    rw [hkeq]
    refine mul_mem_of_rElement_j (m := m) hℓ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hx₁X)
      (Subgroup.mem_sup_right hx₂X)) hk₀N hk₀ord ?_
    rw [← hkeq]
    exact hkr
  have hXle : ∀ (S : Set (Fin Tag.E6.rank → ℤ)), S ⊆ Sx → (∀ α ∈ S, IsRoot Tag.E6 α) →
      Finite ↥(rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _)) →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _)) →
      ∀ (i : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 L), (∀ B : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield σ),
        h₀ * simpleRootSL2 Tag.E6 L i (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) L) B) *
          h₀⁻¹ ∈ rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _)) →
      ∀ e ∈ E, e ∉ Subgroup.zpowers y → rootSpan Tag.E6 L S ≤ Subgroup.centralizer {psiT g0 c e} →
      (rootSpan Tag.E6 L S).comap ψh ≤ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ E ℓ p) := by
    intro S hS hSr hfinS hqS i h₀ hh₀ e he hey hce
    haveI := hfinS
    have hdvd : ℓ ∣ Nat.card ↥(rootSpan Tag.E6 L S ⊓ (tw6Theta L Fr).eqLocus (MonoidHom.id _)) := by
      have h := ringChar_dvd_card_of_rootSL2_mem_j (K := fixSubfield σ) i h₀ hh₀
      rwa [ringChar.eq (fixSubfield σ) ℓ] at h
    have hPgen := Inputs2311f.le_closure_pow_of_quasisimple (r := ℓ) hqS hdvd
    refine (le_closure_of_map_le_j ψh (psiT_injective g0 c)
      (T := {z | z ∈ (rootSpan Tag.E6 L S).comap ψh ∧ ∃ n : ℕ, z ^ (ℓ ^ n) = 1}) ?_ hPgen ?_).trans
      ((Subgroup.closure_le _).2 ?_)
    · intro z hz
      refine ⟨hz, ?_⟩
      have hzC : z ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hca : psiT g0 c z ∈ Subgroup.centralizer {psiT g0 c y} :=
          hcy (CFSG.LieType.Chevalley.rootSpan_mono hS hz)
        exact commute_of_psiT_commute (Subgroup.mem_centralizer_singleton_iff.1 hca)
      have h := hfix ⟨z, hzC⟩
      rw [hψ] at h
      show tw6Theta L Fr (psiT g0 c z) = psiT g0 c z
      rw [tw6Theta_apply]
      exact h
    · rintro u ⟨huP, n, hn⟩
      obtain ⟨z, hz, -⟩ := hland S hS hfinS hqS u huP.1 huP.2
      refine ⟨z, ⟨?_, n, ?_⟩, hz⟩
      · show psiT g0 c z ∈ rootSpan Tag.E6 L S
        rw [hz]
        exact huP.1
      · apply psiT_injective g0 c
        rw [psiT_pow, hz, hn, psiT_one]
    · rintro z ⟨hz, n, hn⟩
      have hzy : z * y = y * z := by
        have hca : psiT g0 c z ∈ Subgroup.centralizer {psiT g0 c y} :=
          hcy (CFSG.LieType.Chevalley.rootSpan_mono hS hz)
        exact commute_of_psiT_commute (Subgroup.mem_centralizer_singleton_iff.1 hca)
      have hze : z * e = e * z :=
        commute_of_psiT_commute (Subgroup.mem_centralizer_singleton_iff.1 (hce hz))
      exact mem_closure_hyperRSet_of_commute_pair_j hE hEc hy he hy1 hey hzy hze ⟨n, hn⟩
  exact (sup_le (hXle S₁ hS₁x hroots₁ hfin₁ hq₁ _ h₀₁ hh₀₁ e₁ he₁ he₁y hc₁)
    (hXle S₂ hS₂x hroots₂ hfin₂ hq₂ _ h₀₂ hh₀₂ e₂ he₂ he₂y hc₂)) hkN

theorem mem_closure_hyperRSet_of_kernel_D4_tw {P : ℕ → Prop}
    (h6 : UniSeitzPlanes fun d p E =>
      TrialityInnerAt (fun p c => p ∣ c ^ 2 - c + 1) d p E ∧ P d.1.characteristic)
    {ℓ f : ℕ} [hℓF : Fact ℓ.Prime] (hP : P ℓ) (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} [hpF : Fact p.Prime] (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    {E : Subgroup (twistedE6RootGroup K σ)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (c : twistedE6RootGroup K σ)
    (hT : ∀ e ∈ E, psiT g0 c e ∈ twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)))
    {y : twistedE6RootGroup K σ} (hy : y ∈ E) (hy1 : y ≠ 1) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' torusRootKernel (psiT g0 c y) = parabolicRoots Tag.E6 d4Support)
    (hsplit : D4Split L (iterateFrobenius L ℓ f) (torusRootKernel (psiT g0 c y)))
    {k : twistedE6RootGroup K σ} (hk : k * y = y * k) {m : ℕ} (hkr : k ^ (ℓ ^ m) = 1) :
    k ∈ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ E ℓ p) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hy) hy1
  set Sx := torusRootKernel (psiT g0 c y) with hSxdef
  have hET : ∀ e ∈ E, psiT g0 c e ∈ torusGroup Tag.E6 L :=
    fun e he => (mem_twistedTorusOf.1 (hT e he)).1
  obtain ⟨hpq', hord6, -, -, hp7, -⟩ := e6Six_data hpF.out hp3 hpq
  have hpℓ : p ≠ ℓ := fun h => hpq' (by rw [h]; exact dvd_pow_self ℓ (by omega))
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
  have : Finite (fixSubfield σ) := inferInstance
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_twisted hℓ hf hK σ hσ
  obtain ⟨-, hfinP, hqsP, -, -, e4, g4, he4, -, ⟨hPequiv⟩⟩ :=
    CFSG.HardMathSupport.Lang.SeitzPlane.tw6_D4_layer_data' (K := fixSubfield σ) (Fr := Fr)
      (ℓ := ℓ) (f := f) hf hkc hFr (hT y hy) hw
  set P0 : Subgroup (ModGL Tag.E6 L) :=
    rootSpan Tag.E6 L Sx ⊓ twistedFixedPoints (tw6N L) (twistE6 L Fr) with hP0
  have hperfP : ⁅P0, P0⁆ = P0 := Subgroup.isPerfect_iff.1 hqsP.1
  obtain ⟨ι', KL, ψ, -, hψ, hspan, hfix, -⟩ := tw6_perx K hf hK σ hσ hpF.out hp3 hpq L hg0C hg0
    hperf hyo c (hT y hy)
  let ψh : twistedE6RootGroup K σ →* ModGL Tag.E6 L :=
    MonoidHom.mk' (psiT g0 c) (psiT_mul g0 c)
  set Y : Subgroup (twistedE6RootGroup K σ) := (rootSpan Tag.E6 L Sx).comap ψh with hY
  have hmemY : ∀ x, x ∈ Y ↔ psiT g0 c x ∈ rootSpan Tag.E6 L Sx := fun x => Iff.rfl
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hET y hy)
  have hcy : rootSpan Tag.E6 L Sx ≤ Subgroup.centralizer {psiT g0 c y} := by
    rw [hb]
    refine CFSG.LieType.Chevalley.rootSpan_le_centralizer b ?_
    rw [hSxdef, hb, torusRootKernel_rootDiagUnit]
  have hYy : ∀ g ∈ Y, g * y = y * g := by
    intro g hg
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (hcy hg)
    exact commute_of_psiT_commute (g0 := g0) (c := c) hc
  have hYθ : ∀ x ∈ Y, psiT g0 c x ∈ twistedFixedPoints (tw6N L) (twistE6 L Fr) := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hYy x hx
    have h := hfix ⟨x, hxC⟩
    rw [hψ] at h
    exact h
  have hPsurj : ∀ u ∈ P0, ∃ x : twistedE6RootGroup K σ, psiT g0 c x = u := by
    intro u hu
    have hadjP : P0 ≤ adjointGroup Tag.E6 L := fun v hv => rootSpan_le_adjointGroup L Sx hv.1
    have hfixP : ∀ v ∈ P0, tw6N L * twistE6 L Fr v * (tw6N L)⁻¹ = v := fun v hv => hv.2
    exact exists_psiT_eq_of_mem hg0C hg0 hperf c hfinP hperfP hadjP hfixP hu
  let φ0 : ↥Y →* ↥P0 :=
    (ψh.comp Y.subtype).codRestrict P0 (fun x => ⟨x.2, hYθ x x.2⟩)
  have hφ0 : Function.Bijective φ0 := by
    refine ⟨fun a b hab => ?_, fun u => ?_⟩
    · apply Subtype.ext
      apply psiT_injective g0 c
      exact congrArg Subtype.val hab
    · obtain ⟨x, hx⟩ := hPsurj u u.2
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [hmemY, hx]
      exact u.2.1
  let eY : ↥Y ≃* ↥P0 := MulEquiv.ofBijective φ0 hφ0
  have hYfin : Finite Y := Finite.of_equiv _ eY.symm.toEquiv
  let φY : ↥Y ≃* ↥(d4Layer Fr e4) :=
    eY.trans (hPequiv.trans (CFSG.HardMathSupport.Malle.SeitzCube.d4ThetaFixedEquivLayer Fr e4))
  obtain ⟨K₃, _, _, _, _, hK₃⟩ := CFSG.HardMathSupport.Lang.TwE6Step3.exists_subfield_card (ℓ := ℓ)
    (n := f * 3) (by omega) (K := K) (Ω := L)
  have hK3 : Nat.card K₃ = (ℓ ^ f) ^ 3 := by rw [hK₃, pow_mul]
  haveI hchar : CharP K₃ ℓ := ⟨fun x => by
    rw [← (algebraMap K₃ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L ℓ x⟩
  let σ₃ : K₃ →+* K₃ := iterateFrobenius K₃ ℓ f
  have hσ₃ : ∀ c, σ₃ c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  let σe : K₃ ≃+* K₃ :=
    RingEquiv.ofBijective σ₃ ⟨σ₃.injective, Finite.surjective_of_injective σ₃.injective⟩
  have hσe : ∀ c, σe c = c ^ (ℓ ^ f) := fun c => hσ₃ c
  have hσe' : ∀ c, σe.toRingHom c = c ^ (ℓ ^ f) := hσe
  have hv : (TauCeti.LieTypeIndex.trialityD4 ⟨ℓ, f, hℓ, hf⟩).Valid :=
    TauCeti.LieTypeIndex.valid_trialityD4 _
  obtain ⟨mY⟩ := CFSG.HardMathSupport.Malle.SeitzCube.nonempty_d4Layer_equiv (Ω := L) hℓ hf hK3 he4
    hσe' hFr
  obtain ⟨cY⟩ := CFSG.HardMathSupport.Malle.SeitzCube.nonempty_d4Layer_equiv_cat (Ω := L) hℓ hf hK3 he4
    hσe' hFr hv
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie ↥Y (.trialityD4 ⟨ℓ, f, hℓ, hf⟩) :=
    ⟨hv, ⟨φY.trans cY⟩⟩
  have hsimple : IsSimpleGroup Y := by
    obtain ⟨-, hsimp⟩ :=
      CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_trialityD4 (q := ⟨ℓ, f, hℓ, hf⟩) hv
    haveI := hsimp
    exact (φY.trans cY).isSimpleGroup
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hle : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hcast : (((ℓ ^ f) ^ 2 - ℓ ^ f + 1 : ℕ) : ℤ) =
      ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    push_cast [Nat.cast_sub hle]
    ring
  have hpN : p ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := Int.natCast_dvd_natCast.1 (by rw [hcast]; exact hpq)
  have hd' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    have : ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 =
        ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by ring
    rw [this]
    exact hpq
  have hplane : ∃ F : Subgroup Y, IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
    have hshape := CFSG.RankThree.PartOne.K128.sylowShape_D4_36 hf K₃ hK3 σe hσe (ε := -1)
      (Or.inr rfl) hpF.out (by omega) hd'
    have he1 : 1 ≤ ((CFSG.RankThree.PartOne.KGD.d4T36d (-1) (ℓ ^ f)).factorization p) := by
      rw [CFSG.RankThree.PartOne.K128.d4T36d_neg_eq hq1]
      exact (hpF.out.factorization_pos_of_dvd (by
        have : 0 < (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := by omega
        omega) hpN)
    exact exists_plane_of_sylowShape he1 (hshape.of_mulEquiv (φY.trans mY))
  have hcen : ∀ z : Y, (∀ g : Y, g * z = z * g) → z = 1 := by
    intro z hz
    haveI := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · have hzc : z ∈ Subgroup.center Y := Subgroup.mem_center_iff.2 fun g => hz g
      rw [h] at hzc
      exact Subgroup.mem_bot.1 hzc
    · exfalso
      obtain ⟨F, hF, hFc⟩ := hplane
      have hcommY : ∀ a b : Y, a * b = b * a := fun a b => by
        have : a ∈ Subgroup.center Y := by rw [h]; trivial
        exact (Subgroup.mem_center_iff.1 this b).symm
      let : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hcommY }
      have hprime := IsSimpleGroup.prime_card (α := Y)
      have hpdvd : p ^ 2 ∣ Nat.card Y := hFc ▸ Subgroup.card_subgroup_dvd_card F
      have hp1 : p ∣ Nat.card Y := dvd_trans (dvd_pow_self p two_ne_zero) hpdvd
      rcases (Nat.dvd_prime hprime).1 hp1 with h1 | h1
      · exact hpF.out.one_lt.ne' h1
      · rw [← h1] at hpdvd
        have := Nat.le_of_dvd hpF.out.pos hpdvd
        nlinarith [hp7]
  have hdisj : Disjoint (Subgroup.zpowers y) Y := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxY
    have hcomm : ∀ g : ↥Y, g * (⟨x, hxY⟩ : ↥Y) = ⟨x, hxY⟩ * g := by
      intro g
      apply Subtype.ext
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxz
      exact ((show Commute (g : twistedE6RootGroup K σ) y from hYy g g.2).zpow_right n).eq
    exact congrArg Subtype.val (hcen ⟨x, hxY⟩ hcomm)
  have hspan' : ∀ x : twistedE6RootGroup K σ, x * y = y * x →
      psiT g0 c x ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L Sx := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hx
    have h := hspan ⟨x, hxC⟩
    rw [hψ] at h
    exact h
  have hYn : ∀ c' : twistedE6RootGroup K σ, c' * y = y * c' → ∀ x ∈ Y, c' * x * c'⁻¹ ∈ Y := by
    intro c' hc' x hx
    have hnorm : torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L Sx ≤
        Subgroup.normalizer (rootSpan Tag.E6 L Sx : Set (ModGL Tag.E6 L)) :=
      sup_le (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (fun α hα => hα.1))
        Subgroup.le_normalizer
    have h := (Subgroup.mem_normalizer_iff.1 (hnorm (hspan' c' hc'))) (psiT g0 c x)
    rw [hmemY]
    rw [psiT_mul, psiT_mul, psiT_inv]
    exact h.1 hx
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hS := sylowTorus_twistedE6_six hℓ hf K hK σ hσ hpF.out hp7 hpq' hord6
  obtain ⟨F, hF, hFc⟩ := hplane
  have hFmap : IsElemAbelian p (F.map Y.subtype) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF Y.subtype
  have hFmapc : Nat.card (F.map Y.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y), hFc]
  have hFY : F.map Y.subtype ≤ Y := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨E', hE'E, hE'Y, hE'ab, hE'c⟩ := exists_plane_le_cube_inf (p := p)
    (fun Q hQ a ha b hb => CFSG.HardMathSupport.Timmesfeld.CrossChar.mul_comm_of_sylowTorus hS hQ ha hb)
    (fun F hF => hS.rank_le hpF.out hF) hE hEc hy hYy hYn hFmap hFmapc hFY
  have hkC : k ∈ Subgroup.centralizer ({y} : Set (twistedE6RootGroup K σ)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hk
  have hψk := hspan' k hk
  have hθk : tw6Theta L Fr (psiT g0 c k) = psiT g0 c k := by
    have h := hfix ⟨k, hkC⟩
    rw [hψ] at h
    rw [tw6Theta_apply]
    exact h
  obtain ⟨t, htH, htθ, a, haS, haθ, hdec⟩ := hsplit _ hψk hθk
  have haP : a ∈ P0 := by
    refine ⟨haS, ?_⟩
    show tw6N L * twistE6 L Fr a * (tw6N L)⁻¹ = a
    rw [← tw6Theta_apply]
    exact haθ
  obtain ⟨x, hx⟩ := hPsurj a haP
  have hxY : x ∈ Y := by
    rw [hmemY, hx]
    exact haS
  set k₀ := k * x⁻¹ with hk₀
  have hψk₀ : psiT g0 c k₀ = t := by
    rw [hk₀, psiT_mul, psiT_inv, hx, hdec]
    group
  have hk₀Y : ∀ z ∈ Y, k₀⁻¹ * z * k₀ ∈ Y := by
    intro z hz
    rw [hmemY, psiT_mul, psiT_mul, psiT_inv, hψk₀]
    have hnorm := CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan
      (S := Sx) (fun α hα => hα.1) (inv_mem htH)
    have h := (Subgroup.mem_normalizer_iff.1 hnorm (psiT g0 c z)).1 hz
    simpa using h
  have hk₀ord : ¬ ℓ ∣ orderOf k₀ := by
    have h0 : orderOf (psiT g0 c k₀) = orderOf k₀ := orderOf_injective ψh (psiT_injective g0 c) k₀
    rw [hψk₀] at h0
    rw [← h0]
    exact not_dvd_orderOf_of_mem_torusGroup_j htH (by rw [h0]; exact (orderOf_pos k₀).ne')
  have hkeq : k = k₀ * x := by rw [hk₀]; group
  have hkY : k ∈ Y := by
    rw [hkeq]
    refine mul_mem_of_rElement_j (m := m) hℓ hxY hk₀Y hk₀ord ?_
    rw [← hkeq]
    exact hkr
  have hgen := le_closure_rFixed_of_isoLie_triality (D := fun p c => p ∣ c ^ 2 - c + 1) h6 hiso hP
    hpF.out (by omega) hpℓ (by rw [TauCeti.PrimePower.card_def]; exact hpN) hE'Y
    (fun a ha b hb => congrArg Subtype.val (hE'ab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    (fun a ha => hE'ab.2 a ha) hE'c
  have hB : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyo]
  have hcent : ∀ g ∈ Y, ∀ b ∈ Subgroup.zpowers y, Commute g b := fun g hg b hb => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (show Commute g y from hYy g hg).zpow_right n
  exact le_closure_hyperRSet_of_rFixed hE hEc (Subgroup.zpowers_le.2 hy) hB hdisj hcent hE'E hE'Y hgen hkY

theorem mem_closure_hyperRSet_twE6_line {P : ℕ → Prop}
    (h6 : UniSeitzPlanes fun d p E =>
      TrialityInnerAt (fun p c => p ∣ c ^ 2 - c + 1) d p E ∧ P d.1.characteristic)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hP : P q.p) (p : ℕ)
    (hp : p.Prime) (hpq : p ≠ q.p) (hord : orderOf ((q.card : ℕ) : ZMod p) = 6)
    (E : Subgroup (CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩)) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) (y : CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩) (hy : y ∈ E)
    (hy1 : y ≠ 1) (k : CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩) (hk : k * y = y * k)
    {m : ℕ} (hkr : k ^ (q.p ^ m) = 1) :
    k ∈ Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ E q.p p) := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  obtain ⟨hdvd, -⟩ := CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_sub_add_one_of_orderOf_eq_six
    hp hord
  have hx0 : ((q.card : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hord
    exact absurd hord (by norm_num)
  have h6' : 6 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have hp7 : 7 ≤ p := by
    have := hp.two_le
    obtain ⟨m, hm⟩ := h6'
    omega
  have hp3' : 3 < p := by omega
  have hp5 : 5 < p := by omega
  have hpq' : (p : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 - ((q.p ^ q.exponent : ℕ) : ℤ) + 1 := by
    rw [← hcard]
    have hle : q.card ≤ q.card ^ 2 := Nat.le_self_pow (by norm_num) _
    have : ((q.card ^ 2 - q.card + 1 : ℕ) : ℤ) = ((q.card : ℕ) : ℤ) ^ 2 - (q.card : ℤ) + 1 := by
      push_cast [hle]
      ring
    rw [← this]
    exact Int.natCast_dvd_natCast.2 hdvd
  let L := AlgebraicClosure K
  have : CharP L q.p := charP_of_injective_algebraMap (algebraMap K L).injective q.p
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := tw6_frame K hf hK σ hσ hp hp3' hpq' L
  set E' := E.map e.toMonoidHom with hE'def
  have hE' : IsElemAbelian p E' := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hE'c : Nat.card E' = p ^ 3 := by
    rw [hE'def, Subgroup.card_map_of_injective e.injective, hEc]
  have hE'p : IsPGroup p E' := IsPGroup.of_card hE'c
  obtain ⟨c, hc⟩ := hconj E' hE'p
  have hT : ∀ x ∈ E', psiT g0 c x ∈
      twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L q.p q.exponent)) := hc
  have hy' : e y ∈ E' := ⟨y, hy, rfl⟩
  have hy'1 : e y ≠ 1 := by
    intro h
    exact hy1 (e.injective (h.trans e.map_one.symm))
  have hk' : e k * e y = e y * e k := by rw [← map_mul, hk, map_mul]
  have hkr' : e k ^ (q.p ^ m) = 1 := by rw [← map_pow, hkr, map_one]
  have hFr : ∀ c, (iterateFrobenius L q.p q.exponent) c = c ^ (q.p ^ q.exponent) :=
    fun c => iterateFrobenius_def q.p q.exponent c
  have hq0 : ((q.p ^ q.exponent : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow q.exponent_pos.ne']
  obtain ⟨-, ⟨ζ, hζ⟩, -⟩ := tw6_prime_setup (L := L) hq0 hp hpq'
  have : NeZero p := ⟨hp.ne_zero⟩
  have hxp : psiT g0 c (e y) ^ p = 1 := by
    rw [← psiT_pow, hE'.2 _ hy', psiT_one]
  have hx1 : psiT g0 c (e y) ≠ 1 := by
    intro h
    exact hy'1 (psiT_injective g0 c (h.trans (psiT_one g0 c).symm))
  obtain ⟨z, -, hz, hker, hz0⟩ := exists_column_of_tw6Torus hFr hζ (hT _ hy') hxp
  have hq2 : 2 ≤ q.p ^ q.exponent := le_trans q.prime_p.two_le (Nat.le_self_pow (by omega) _)
  have hvS := tw6_torusRootKernel_smul_stable hFr (hT _ hy')
  rcases phi3_kernel_types hp5 z (hz0 hx1) _ hz with h0 | hA2 | hA2A2 | hD4
  · have h1 := eq_one_of_kernel_empty_tw K hf hK σ hσ hp3' hpq' L hg0C hg0 hperf hE' c hT hy' hy'1
      (hker.trans h0) hk' hkr'
    have hk1 : k = 1 := e.injective (h1.trans e.map_one.symm)
    rw [hk1]
    exact Subgroup.one_mem _
  · refine mem_closure_hyperRSet_of_mulEquiv_j e ?_
    exact mem_closure_hyperRSet_of_kernel_A2_tw K hf hK σ hσ hp3' hpq' L hg0C hg0 hperf hE' hE'c c hT
      hy' hy'1 (by rw [hker]; exact hA2) hk' hkr'
  · refine mem_closure_hyperRSet_of_mulEquiv_j e ?_
    obtain ⟨w, hw⟩ := hA2A2
    have hw' : (w • ·) '' torusRootKernel (psiT g0 c (e y)) = parabolicRoots Tag.E6 supportA2A2 := by
      rw [hker]; exact hw
    have hT' : ∀ β ∈ parabolicRoots Tag.E6 supportA2A2,
        (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 supportA2A2 := by
      intro β hβ
      rw [← hw'] at hβ ⊢
      obtain ⟨α, hα, rfl⟩ := hβ
      exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
    obtain ⟨hT13, hT56⟩ := conj_e6T3W_preserves_blocks hT'
    exact mem_closure_hyperRSet_of_kernel_A2A2_tw K hf hK σ hσ hp3' hpq' L hg0C hg0 hperf hE' hE'c c
      hT hy' hy'1 hw' (twoA2Split_of_blocks hq2 hFr hT13 hT56) hk' hkr'
  · refine mem_closure_hyperRSet_of_mulEquiv_j e ?_
    obtain ⟨w, hw0⟩ := hD4
    have hw : (w • ·) '' torusRootKernel (psiT g0 c (e y)) = parabolicRoots Tag.E6 d4Support := by
      rw [hker]; exact hw0
    have hT' : ∀ β ∈ parabolicRoots Tag.E6 d4Support,
        (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 d4Support := by
      intro β hβ
      rw [← hw] at hβ ⊢
      obtain ⟨α, hα, rfl⟩ := hβ
      exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
    have hSx : torusRootKernel (psiT g0 c (e y)) =
        (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 d4Support := by
      rw [← hw, Set.image_image]
      simp
    have hsplit : D4Split L (iterateFrobenius L q.p q.exponent) (torusRootKernel (psiT g0 c (e y))) := by
      rw [hSx]
      intro m hm hθm
      exact fixedSplit_of_block hq2 hFr hT' hm hθm
    exact mem_closure_hyperRSet_of_kernel_D4_tw h6 hP K hf hK σ hσ hp3' hpq' L hg0C hg0 hperf hE' hE'c c
      hT hy' hy'1 hw hsplit hk' hkr'

theorem exists_cube_top_le_closure_hyperRSet_twE6 {P : ℕ → Prop}
    (h6 : UniSeitzPlanes fun d p E =>
      TrialityInnerAt (fun p c => p ∣ c ^ 2 - c + 1) d p E ∧ P d.1.characteristic)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hP : P q.p) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p) (hord : orderOf ((q.card : ℕ) : ZMod p) = 6) :
    ∃ E₁ : Subgroup (CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩), IsElemAbelian p E₁ ∧
      Nat.card E₁ = p ^ 3 ∧ (⊤ : Subgroup (CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩)) ≤
        Subgroup.closure (CFSG.LieType.Chevalley.hyperRSet ⊤ E₁ q.p p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨h6', -⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_sub_add_one_of_orderOf_eq_six hp hord
  have hp3' : 3 < p := by omega
  have h7 := CFSG.LieType.SeitzGeneration.ExcHigh.seven_le_of_orderOf_six hp hord
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hq1 : 1 ≤ q.card := by rw [hcard]; exact Nat.one_le_pow _ _ q.prime_p.pos
  have hpq' : ¬ p ∣ q.card := by
    intro hd
    rw [hcard] at hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow hd))
  have hnd : ¬ p ∣ q.card ^ 2 - 1 :=
    CFSG.LieType.SeitzGeneration.ExcHigh.not_dvd_sq_sub_one_of_orderOf hp hq1 hord (by omega)
  have hpqZ : (p : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 - ((q.p ^ q.exponent : ℕ) : ℤ) + 1 := by
    rw [← hcard]
    have h1 := Int.natCast_dvd_natCast.2 h6'
    have h2 : ((q.card ^ 2 - q.card + 1 : ℕ) : ℤ) = (q.card : ℤ) ^ 2 - q.card + 1 := by
      rw [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero q.card), Nat.cast_pow,
        Nat.cast_one]
    rwa [h2] at h1
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  have : Finite (ModGL TwistTag.E6.tag K) := by
    have hK0 : Nat.card K ≠ 0 := by
      rw [hK]
      exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero)
    have : Finite K := Nat.finite_of_card_ne_zero hK0
    have : Fintype K := Fintype.ofFinite K
    exact finite_modGL
  have : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩) :=
    Finite.of_equiv (twistedE6RootGroup K σ) e.symm.toEquiv
  have hcommCat : ∀ Q : Subgroup (CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩), IsPGroup p Q →
      ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro Q hQ a ha b hb
    have hQ' : IsPGroup p (Q.map e.toMonoidHom) := hQ.map _
    have hab := pSubgroup_comm_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp hp3' hpqZ
      (Q.map e.toMonoidHom) hQ' (e a) ⟨a, ha, rfl⟩ (e b) ⟨b, hb, rfl⟩
    exact e.injective (by simpa using hab)
  obtain ⟨E, R, hE, hEc, hRne, hRp, hEN⟩ :=
    CFSG.HardMathSupport.Lang.SeitzPlane.exists_plane_twistedE6RootGroup_six q.prime_p q.exponent_pos K
      hK σ hσ hp hp3' (by rw [← hcard]; exact hpq') (by rw [← hcard]; exact hord)
      (by rw [← hcard]; exact hnd)
  let f : twistedE6RootGroup K σ →* CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩ := e.symm.toMonoidHom
  have hf : Function.Injective f := e.symm.injective
  have hE₀' : IsElemAbelian p (E.map f) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE f
  have hE₀c' : Nat.card (E.map f) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hf, hEc]
  have hN : ∀ x ∈ E.map f, (R.map f).map (MulAut.conj x).toMonoidHom = R.map f := by
    rintro _ ⟨x, hx, rfl⟩
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hy' : x * y * x⁻¹ ∈ R := by
        rw [← hEN x hx]
        exact ⟨y, hy, rfl⟩
      exact ⟨x * y * x⁻¹, hy', by simp [MulAut.conj_apply, f]⟩
    · rintro ⟨y, hy, rfl⟩
      have hy' : x⁻¹ * y * x ∈ R := by
        have := hEN x⁻¹ (inv_mem hx)
        rw [← this]
        exact ⟨y, hy, by simp⟩
      refine ⟨f (x⁻¹ * y * x), ⟨_, hy', rfl⟩, ?_⟩
      simp [MulAut.conj_apply, f, mul_assoc]
  have hE'1 : E.map f ≠ ⊥ := by
    intro hbot
    have := hE₀c'
    rw [hbot, Subgroup.card_bot] at this
    have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hchar : (TauCeti.LieTypeIndex.twistedE6 q).characteristic = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedE6 q
  have hRne' : R.map f ≠ ⊥ := by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hf]
  have hRp' : IsPGroup (TauCeti.LieTypeIndex.twistedE6 q).characteristic (R.map f) := by
    rw [hchar]
    exact hRp.map f
  have hHy := CFSG.LieType.SeitzGeneration.QuasiHigh.seitzExcParabolicRChevalley
    ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩ p hp (by rw [hchar]; exact hpq)
    (Or.inr (Or.inr ⟨q, rfl⟩)) _ hE₀' hE'1 ⟨R.map f, hRne', hRp', hN⟩
  rw [hchar] at hHy
  obtain ⟨T, V0, -, -, -, -, hV0el, hV0c⟩ :=
    (CFSG.LieType.SeitzGeneration.ExcHigh.sylowTorus_cat_twE6_six hv hp h7 hpq hord).exists_torus
  obtain ⟨E₁, hle, hE₁, hE₁c⟩ := exists_cube_containing_plane hcommCat hE₀' hE₀c' hV0el hV0c
  refine ⟨E₁, hE₁, hE₁c, hHy.trans ((Subgroup.closure_le _).2 ?_)⟩
  rintro x ⟨-, hxr, B, hB, hBi, hxB⟩
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.relIndex_bot_left, hE₀c'] at hBi
    have h1 : p ^ 2 = p ^ 1 := by rw [hBi, pow_one]
    have := Nat.pow_right_injective hp.two_le h1
    omega
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  obtain ⟨n, hn⟩ := hxr
  exact mem_closure_hyperRSet_twE6_line h6 q hv hP p hp hpq hord E₁ hE₁ hE₁c y (hle (hB y.2))
    (fun h1 => hy (Subtype.ext h1)) x (Subgroup.mem_centralizer_iff.1 hxB y y.2).symm hn

theorem uniSeitzPlanes_twE6Six_inner_of_triality {P : ℕ → Prop}
    (h6 : UniSeitzPlanes fun d p E =>
      TrialityInnerAt (fun p c => p ∣ c ^ 2 - c + 1) d p E ∧ P d.1.characteristic) :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6) ∧
      P d.1.characteristic := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, hp5, ⟨q, hq, hord⟩, hch⟩
  obtain rfl : d = .twistedE6 q := hq
  haveI : Fact p.Prime := ⟨hp⟩
  have hchar : (TauCeti.LieTypeIndex.twistedE6 q).characteristic = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedE6 q
  have hpq : p ≠ q.p := fun h => hpd (by rw [hchar]; exact h)
  have hPq : P q.p := by rw [← hchar]; exact hch
  have h7 := CFSG.LieType.SeitzGeneration.ExcHigh.seven_le_of_orderOf_six hp hord
  obtain ⟨E₁, hE₁, hE₁c, hgen⟩ := exists_cube_top_le_closure_hyperRSet_twE6 h6 q hv hPq hp hp5 hpq hord
  rw [← hchar] at hgen
  exact uniPlaneGen_of_sylowTorus_rgen hp
    (Inputs2311c.conj_injective_cat_of_chevalleyExc (Or.inr (Or.inr ⟨q, rfl⟩)))
    (CFSG.LieType.SeitzGeneration.ExcHigh.sylowTorus_cat_twE6_six hv hp h7 hpq hord) hE₁ hE₁c hgen hE hc hin

end TwE6SixR

section TrialityCited

set_option linter.unusedSectionVars false

theorem uniSeitzPlanes_E6Three_inner :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 3) := by
  have h3 : UniSeitzPlanes fun d p E => TrialityPhi3Inner d p E ∧ (fun _ => True) d.1.characteristic := by
    refine UniSeitzPlanes.mono (fun d p E hs => ?_) Inputs2311k.uniSeitzPlanes_triality_inner_phi36
    obtain ⟨⟨hin, hp5, ⟨q, hq, hdvd⟩, -⟩, -⟩ := hs
    exact ⟨hin, hp5, q, hq, Or.inl hdvd⟩
  refine UniSeitzPlanes.mono (fun d p E hs => ?_)
    (uniSeitzPlanes_E6Three_inner_of_triality (P := fun _ => True) h3)
  obtain ⟨hin, hp5, hE6⟩ := hs
  exact ⟨hin, hp5, hE6, trivial⟩

theorem uniSeitzPlanes_twE6Six_inner :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧
      (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6) := by
  have h6 : UniSeitzPlanes fun d p E =>
      TrialityInnerAt (fun p c => p ∣ c ^ 2 - c + 1) d p E ∧ (fun _ => True) d.1.characteristic := by
    refine UniSeitzPlanes.mono (fun d p E hs => ?_) Inputs2311k.uniSeitzPlanes_triality_inner_phi36
    obtain ⟨⟨hin, hp5, ⟨q, hq, hdvd⟩, -⟩, -⟩ := hs
    exact ⟨hin, hp5, q, hq, Or.inr hdvd⟩
  refine UniSeitzPlanes.mono (fun d p E hs => ?_)
    (uniSeitzPlanes_twE6Six_inner_of_triality (P := fun _ => True) h6)
  obtain ⟨hin, hp5, hTw⟩ := hs
  exact ⟨hin, hp5, hTw, trivial⟩

end TrialityCited

@[expose] def OddCpfInnerExc2 : Prop :=
  UniSeitzPlanes fun d p E => OddCpfRest d p E ∧ InnerPlane d p E ∧ 5 ≤ p ∧
    ((∃ q : TauCeti.PrimePower, d.1 = .E7 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .E8 q ∧ 7 ≤ p ∧
        (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 6)))

@[expose] def Input23_11TwoRestExc2 : Prop :=
  UniSeitzPlanes fun d p E => d.1.characteristic = 2 ∧ 5 ≤ p ∧ CentralPrimeFree p d.1 ∧
    InnerPlane d p E ∧ ¬ NormalizesRSubgroup d E ∧
    ((∃ q : TauCeti.PrimePower, d.1 = .E7 q ∧ orderOf ((q.card : ℕ) : ZMod p) = 6) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .E8 q ∧ (orderOf ((q.card : ℕ) : ZMod p) = 3 ∨
        orderOf ((q.card : ℕ) : ZMod p) = 6)))

section Residual

open TauCeti

set_option linter.unusedSectionVars false

theorem oddCpfInnerExc_of_rest (h : OddCpfInnerExc2) : SeitzRest7.OddCpfInnerExc := by
  intro d p hp hp2 hpd hex E hE hc ⟨⟨hR, hcase⟩, hin, hntri⟩
  have hch : d.1.characteristic ≠ 2 := hR.1.1
  rcases hcase with ⟨hni, -⟩ | ⟨-, hexc, hsub⟩ | ⟨hni, -⟩
  · exact absurd hin hni
  · have hnR : ¬ NormalizesRSubgroup d E := fun hN => hR.2.2 ⟨hin, hexc, hN⟩
    rcases hsub with ⟨h5, hcls⟩ | ⟨hp3, ⟨q, hq, -⟩ | htw⟩
    · rcases hcls with ⟨q, hq, h3 | h6⟩ | ⟨q, hq, h2 | h6⟩ | ⟨q, hq, hp7, h3 | h6 | h8 | h12⟩ |
          ⟨q, hq, h1, hdeg⟩ | ⟨q, hq, -⟩
      · exact uniSeitzPlanes_E6Three_inner d p hp hp2 hpd hex E hE hc ⟨hin, h5, ⟨q, hq, h3⟩⟩
      · exact uniSeitzPlanes_E6Six_inner_odd d p hp hp2 hpd hex E hE hc ⟨hin, h5, ⟨q, hq, h6⟩, hch, hnR⟩
      · exact uniSeitzPlanes_E7Two_inner_odd d p hp hp2 hpd hex E hE hc ⟨hin, h5, ⟨q, hq, h2⟩, hch, hnR⟩
      · exact h d p hp hp2 hpd hex E hE hc ⟨hR, hin, h5, Or.inl ⟨q, hq, h6⟩⟩
      · exact h d p hp hp2 hpd hex E hE hc ⟨hR, hin, h5, Or.inr ⟨q, hq, hp7, Or.inl h3⟩⟩
      · exact h d p hp hp2 hpd hex E hE hc ⟨hR, hin, h5, Or.inr ⟨q, hq, hp7, Or.inr h6⟩⟩
      · exact uniSeitzPlanes_E8_eight_inner_odd d p hp hp2 hpd hex E hE hc ⟨hin, ⟨q, hq, h8⟩, hch, hnR⟩
      · exact uniSeitzPlanes_E8Twelve_inner_odd d p hp hp2 hpd hex E hE hc ⟨hin, h5, ⟨q, hq, h12⟩, hch, hnR⟩
      · have hq2 : q.p ≠ 2 := by
          intro h2'
          apply hch
          rw [hq, LieTypeIndex.characteristic_twistedE6, h2']
        by_cases hplus : p ∣ q.card + 1
        · exact uniSeitzPlanes_twE6Two_inner_odd d p hp hp2 hpd hex E hE hc
            ⟨hin, h5, hnR, q, hq, hq2, hplus⟩
        by_cases h34 : orderOf ((q.card : ℕ) : ZMod p) = 3 ∨ orderOf ((q.card : ℕ) : ZMod p) = 4
        · exact uniSeitzPlanes_twE6ThreeFour_inner_odd d p hp hp2 hpd hex E hE hc
            ⟨hin, h5, hnR, q, hq, hq2, h34⟩
        · push Not at h34
          have hq1 : 1 ≤ q.card := by
            rw [PrimePower.card_def]
            exact Nat.one_le_pow _ _ q.prime_p.pos
          exact uniSeitzPlanes_twE6Six_inner d p hp hp2 hpd hex E hE hc ⟨hin, h5,
            ⟨q, hq, Inputs2311i.orderOf_eq_six_of_degCountTw hp hq1 h1 hplus h34.1 h34.2 hdeg⟩⟩
      · exact absurd ⟨q, hq⟩ hntri
    · exact absurd ⟨q, hq⟩ hntri
    · obtain ⟨q, hq, hq3⟩ := htw
      have hq2 : q.card ≠ 2 := by
        intro h2'
        apply hch
        rw [hq, LieTypeIndex.characteristic_twistedE6]
        have hpow : q.p ^ q.exponent = 2 := by rw [← PrimePower.card_def]; exact h2'
        have hdvd : q.p ∣ 2 := by
          rw [← hpow]
          exact dvd_pow_self _ q.exponent_pos.ne'
        exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
      exact CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover.twE6ThreeOpenInner_holds d p hp hp2 hpd hex E hE hc
        ⟨hin, hp3, ⟨q, hq, hq3, hq2⟩, hnR⟩
  · exact absurd hin hni

theorem input23_11TwoRestExc_of_rest (h : Input23_11TwoRestExc2) : SeitzRest7.Input23_11TwoRestExc := by
  intro d p hp hp2 hpd hex E hE hc hs
  obtain ⟨hch, hp5, hcpf, hin, hn, hcls⟩ := hs
  rcases hcls with hE6 | hE7 | hE8 | hTw
  · exact uniSeitzPlanes_E6Three_inner d p hp hp2 hpd hex E hE hc ⟨hin, hp5, hE6⟩
  · exact h d p hp hp2 hpd hex E hE hc ⟨hch, hp5, hcpf, hin, hn, Or.inl hE7⟩
  · exact h d p hp hp2 hpd hex E hE hc ⟨hch, hp5, hcpf, hin, hn, Or.inr hE8⟩
  · exact uniSeitzPlanes_twE6Six_inner d p hp hp2 hpd hex E hE hc ⟨hin, hp5, hTw⟩

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311j
