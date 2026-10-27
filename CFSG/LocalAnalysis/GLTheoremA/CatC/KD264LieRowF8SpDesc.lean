module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCyc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpForm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreTransfer
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8LnLift
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Sp

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank
  CFSG.RankThree.CASymplecticSubfield CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.ComponentClassification.UnbalancedCatalog

theorem charP_two_of_card_eight {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    CharP K 2 := by
  haveI := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  have hpn : p ^ (n : ℕ) = 2 ^ 3 := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
    norm_num
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 ^ 3 := by
      rw [← hpn]
      exact dvd_pow_self p (PNat.ne_zero n)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact hchar

noncomputable def spFieldEquiv {F : Type} [Field F] (e : F ≃+* ZMod 2) (n : ℕ) :
    StatedSp n F ≃* StatedSp n (ZMod 2) :=
  ((StatedSp n F).equivMapOfInjective
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin n ⊕ Fin n) e).toMonoidHom
      (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin n ⊕ Fin n) e).injective).trans
    (MulEquiv.subgroupCongr (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp e n))

section AutFacts

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sp_quot_cyclic (hn : 3 ≤ n) :
    IsCyclic (MulAut (StatedProj (StatedSp n K)) ⧸ inner (StatedProj (StatedSp n K))) := by
  haveI : (inner (StatedProj (StatedSp n K))).Normal := inner_normal _
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (inner (StatedProj (StatedSp n K)))).comp (fieldAut n K)) := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i, hi, c, ⟨σ, rfl⟩, rfl⟩ := CFSG.StandardType.AutPSp.exists_mul_compl hn α
    refine ⟨σ, ?_⟩
    show (QuotientGroup.mk (fieldAut n K σ) : _ ⧸ inner (StatedProj (StatedSp n K))) =
      QuotientGroup.mk (i * fieldAut n K σ)
    rw [QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (N := inner (StatedProj (StatedSp n K))) i).2 hi, one_mul]
  exact isCyclic_of_surjective _ hsurj

theorem sp_innAutDerived_eq_inner (hn : 3 ≤ n) :
    innAutDerived (StatedProj (StatedSp n K)) = inner (StatedProj (StatedSp n K)) := by
  haveI : (inner (StatedProj (StatedSp n K))).Normal := inner_normal _
  haveI := sp_quot_cyclic (n := n) (K := K) hn
  apply le_antisymm
  · refine sup_le le_rfl ?_
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hc : Commute (QuotientGroup.mk x : _ ⧸ inner (StatedProj (StatedSp n K)))
        (QuotientGroup.mk y) := IsMulCommutative.is_comm.comm _ _
    rw [hc.eq]
    group
  · exact inner_le_innAutDerived _

theorem sp_outCyc (hn : 3 ≤ n) : OutCycAt 3 (StatedProj (StatedSp n K)) := by
  haveI : (inner (StatedProj (StatedSp n K))).Normal := inner_normal _
  haveI := sp_quot_cyclic (n := n) (K := K) hn
  refine outCycAt_of_cyclic Nat.prime_three ⊤ (fun _ _ => Subgroup.mem_top _)
    ((QuotientGroup.mk' (inner (StatedProj (StatedSp n K)))).comp
      (⊤ : Subgroup (MulAut (StatedProj (StatedSp n K)))).subtype) ?_
  intro x hx _
  have hx' : (x : MulAut (StatedProj (StatedSp n K))) ∈ inner (StatedProj (StatedSp n K)) :=
    (QuotientGroup.eq_one_iff _).1 hx
  exact inner_le_innAutDerived _ hx'

theorem center_sp_eq_bot (hn : 3 ≤ n) :
    Subgroup.center (StatedProj (StatedSp n K)) = ⊥ := by
  haveI : NeZero n := ⟨by omega⟩
  let e : StatedSp n K ≃* StatedProj (StatedSp n K) :=
    MulEquiv.ofBijective (proj n K)
      ⟨CFSG.StandardType.AutPSp.proj_injective, proj_surjective (r := n) (K := K)⟩
  rw [← Subgroup.map_center_eq e, CFSG.StandardType.AutPSp.center_eq_bot, Subgroup.map_bot]

end AutFacts


section Descent

theorem exists_descent_sp {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    (b : MulAut (StatedProj (StatedSp n K))) (hb3 : b ^ 3 = 1)
    (hbout : b ∉ inner (StatedProj (StatedSp n K))) :
    ∃ ι : ↥(TauCeti.BilinForm.isometryGroup (stdForm n)) →* StatedProj (StatedSp n K),
      Function.Injective ι ∧ (∀ v, b (ι v) = ι v) ∧ (∀ x, b x = x → x ∈ ι.range) := by
  classical
  haveI hchar : CharP K 2 := charP_two_of_card_eight hK
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have hpdvd : 3 ∣ Nat.card (StatedProj (StatedSp n K)) := by
    have hr : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSp n K)) := by
      have := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp (K := K) (n := n)
        (r := 3) Nat.prime_three (by rw [hK]; norm_num)
      omega
    obtain ⟨E, -, -, hE⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank
      Nat.prime_three hr
    have h1 : 3 ∣ Nat.card (StatedSp n K) := by
      have h2 : Nat.card E ∣ Nat.card (StatedSp n K) := Subgroup.card_subgroup_dvd_card E
      rw [hE, pow_one] at h2
      exact h2
    haveI : NeZero n := ⟨by omega⟩
    have e : StatedSp n K ≃* StatedProj (StatedSp n K) :=
      MulEquiv.ofBijective (proj n K)
        ⟨CFSG.StandardType.AutPSp.proj_injective, proj_surjective (r := n) (K := K)⟩
    rwa [← Nat.card_congr e.toEquiv]
  obtain ⟨σ, h, hσ, -, hbeq, -⟩ := exists_conj_fieldAut_psp (ℓ := 2) (f := 3) (r := n) (p := 3)
    Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) (by norm_num) (by omega) hK'
    (by omega) hb3 hbout hpdvd
  obtain ⟨-, hcard, -, -, hinj, hfixpts, -⟩ :=
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.symplectic_prime_subfield_fixed_group_and_full_centralizer_odd
      (ℓ := 2) (p := 3) (f := 3) (r := n) Nat.prime_two Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num) (by omega) hK' σ hσ
  have hcard2 : Nat.card (descentField σ) = 2 := by
    rw [hcard]
    norm_num
  haveI : Finite (descentField σ) := inferInstance
  obtain ⟨e₀⟩ := exists_ringEquiv_zmod2 (descentField σ) hcard2
  obtain ⟨stdIso⟩ := exists_stdIso n
  haveI : NeZero n := ⟨by omega⟩
  let φ : StatedSp n (descentField σ) ≃* StatedSp n (ZMod 2) := spFieldEquiv e₀ n
  let ι₁ : ↥(TauCeti.BilinForm.isometryGroup (stdForm n)) →* StatedProj (StatedSp n K) :=
    (subfieldSpProj n (descentField σ)).comp ((proj n (descentField σ)).comp
      (φ.symm.toMonoidHom.comp stdIso.symm.toMonoidHom))
  have hproj_inj : Function.Injective (proj n (descentField σ)) := by
    haveI : Fintype (descentField σ) := Fintype.ofFinite _
    haveI : CharP (descentField σ) 2 :=
      charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hcard2)
    exact CFSG.StandardType.AutPSp.proj_injective
  have hι₁inj : Function.Injective ι₁ := fun a b hab =>
    stdIso.symm.injective (φ.symm.injective (hproj_inj (hinj hab)))
  have hrange : ι₁.range = subfieldFixedGroup K n σ := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨proj n (descentField σ) (φ.symm (stdIso.symm v)), rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨g, rfl⟩ := proj_surjective (r := n) (K := descentField σ) y
      refine ⟨stdIso (φ g), ?_⟩
      simp [ι₁]
  have hfixι : ∀ y ∈ ι₁.range, fieldAut n K σ y = y := fun y hy =>
    (hfixpts y).1 (hrange ▸ hy)
  refine ⟨h.toMonoidHom.comp ι₁, h.injective.comp hι₁inj, ?_, ?_⟩
  · intro v
    show b (h (ι₁ v)) = h (ι₁ v)
    rw [hbeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfixι _ ⟨v, rfl⟩]
  · intro x hx
    have h1 : fieldAut n K σ (h⁻¹ x) = h⁻¹ x := by
      rw [hbeq, MulAut.mul_apply, MulAut.mul_apply] at hx
      have h2 : h (fieldAut n K σ (h⁻¹ x)) = h (h⁻¹ x) := by rw [hx, MulAut.apply_inv_self]
      exact h.injective h2
    have h3 : h⁻¹ x ∈ ι₁.range := hrange ▸ (hfixpts _).2 h1
    obtain ⟨v, hv⟩ := h3
    refine ⟨v, ?_⟩
    show h (ι₁ v) = x
    rw [hv, MulAut.apply_inv_self]

end Descent

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Sp

end
