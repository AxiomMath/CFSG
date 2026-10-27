module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Prop415Mid
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Prop415Aut
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Lemma414
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Main
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Open.StatedCenterThree
import CFSG.Open.StatedSUFieldChange
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pGroup_residual {p : ℕ} (hp : p.Prime) {B : Subgroup G} (hB : IsPGroup p B) :
    ∀ N : Subgroup G, N ≤ B → (N.subgroupOf B).Normal → Nat.Coprime p (N.subgroupOf B).index →
      N = B := by
  intro N hNB _ hcop
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hB.exists_card_eq
  have hidx : (N.subgroupOf B).index ∣ p ^ k := hk ▸ Subgroup.index_dvd_card _
  have h1 : (N.subgroupOf B).index = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hcop).symm hidx
  have h2 : N.subgroupOf B = ⊤ := Subgroup.index_eq_one.1 h1
  exact le_antisymm hNB (Subgroup.subgroupOf_eq_top.1 h2)

private theorem k3_exists_primePower_card_eq (F : Type) [Field F] [Finite F] :
    ∃ (q : TauCeti.PrimePower) (_ : Fact q.p.Prime), q.card = Nat.card F ∧
      Nonempty (F ≃+* GaloisField q.p q.exponent) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨m, hp, hm⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hp⟩
  refine ⟨⟨ringChar F, m, hp, m.pos⟩, ⟨hp⟩, ?_, ⟨?_⟩⟩
  · rw [TauCeti.PrimePower.card_def, Nat.card_eq_fintype_card, hm]
  · have : Fintype (GaloisField (ringChar F) m) := Fintype.ofFinite _
    refine FiniteField.ringEquivOfCardEq (K := F) (K' := GaloisField (ringChar F) m) ?_
    rw [hm, ← Nat.card_eq_fintype_card, GaloisField.card _ _ m.ne_zero]

private theorem k3_exists_primePower_sq_card_eq (F : Type) [Field F] [Finite F] {q : ℕ}
    (hFq : Nat.card F = q ^ 2) (hq : 2 ≤ q) :
    ∃ (Q : TauCeti.PrimePower) (_ : Fact Q.p.Prime), Q.card = q ∧
      Nonempty (F ≃+* GaloisField Q.p (2 * Q.exponent)) := by
  obtain ⟨⟨p, e, hp, he⟩, hpf, hQ₀, ⟨φ⟩⟩ := k3_exists_primePower_card_eq F
  rw [TauCeti.PrimePower.card_def, hFq] at hQ₀
  have hqd : q ∣ p ^ e := ⟨q, by rw [hQ₀, pow_two]⟩
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hqd
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hq
  have hek : e = 2 * k := by
    refine Nat.pow_right_injective hp.two_le ?_
    show p ^ e = p ^ (2 * k)
    rw [hQ₀, ← pow_mul, mul_comm]
  subst hek
  exact ⟨⟨p, k, hp, Nat.pos_of_ne_zero hk⟩, ⟨hp⟩, TauCeti.PrimePower.card_def _, ⟨φ⟩⟩

private theorem k3_center_statedSU_three_eq {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (h3 : 3 ∣ q + 1) :
    Subgroup.center (StatedSU 3 q F) = (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F) := by
  have hq2 := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hF
  have hq : q ≠ 0 := by omega
  symm
  refine Subgroup.eq_of_le_of_card_ge (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _) ?_
  rw [CFSG.Open.StatedCenterThree.card_center_statedSU_three hF h3]
  have h3F : 3 ∣ Nat.card F - 1 := by
    rw [hF, CFSG.Open.StatedCenterThree.sq_sub_one_eq (by omega)]
    exact Dvd.dvd.mul_left h3 _
  have hr : Nat.card (rootsOfUnity 3 F) = 3 :=
    CFSG.Open.StatedCenterThree.card_rootsOfUnity_three h3F
  let f : rootsOfUnity 3 F → ↥((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F)) := fun ζ =>
    ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ : Fˣ),
      CFSG.Open.StatedCenterThree.scalar_mem hq h3 ((mem_rootsOfUnity 3 (ζ : Fˣ)).mp ζ.2)⟩,
      Subgroup.mem_subgroupOf.2 ⟨(ζ : Fˣ), rfl⟩⟩
  refine hr.symm.le.trans (Nat.card_le_card_of_injective f fun ζ₁ ζ₂ h => ?_)
  have h' : ((Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ₁ : Fˣ) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 0 =
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ₂ : Fˣ) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 0 :=
    congrArg (fun z : ↥((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F)) =>
      ((((z : StatedSU 3 q F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0)) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h'
  exact Subtype.ext (Units.ext h')

theorem catalogIs_k3_of_statedSL_three {Q F : Type} [Group Q] [Field F] [Finite F]
    (h6 : Nat.card F % 6 = 1) (e : Q ≃* StatedSL 3 F) :
    catalogIs (Q ⧸ Subgroup.center Q) (k3 3) := by
  obtain ⟨q, _, hqc, ⟨φ⟩⟩ := k3_exists_primePower_card_eq F
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [hqc]
    omega
  refine ⟨.lie ⟨.A 2 q, hv⟩, ?_, ⟨?_⟩⟩
  · show 3 = 3 ∧ q.card % 6 = 1
    rw [hqc]
    exact ⟨rfl, h6⟩
  · let e₁ : Q ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
      e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
    exact ((QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
      (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) φ)).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm

theorem catalogIs_k3_of_statedSU_three {Q F : Type} [Group Q] [Field F] [Finite F] {q : ℕ}
    (hFq : Nat.card F = q ^ 2) (h6 : q % 6 = 5) (e : Q ≃* StatedSU 3 q F) :
    catalogIs (Q ⧸ Subgroup.center Q) (k3 3) := by
  have hq2 := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hFq
  have h3 : 3 ∣ q + 1 := by omega
  have hq3 : 3 ≤ q := by omega
  obtain ⟨R, _, hRc, ⟨φ⟩⟩ := k3_exists_primePower_sq_card_eq F hFq hq2
  have hv : (TauCeti.LieTypeIndex.twistedA 2 R).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨⟨le_rfl, fun _ => ?_⟩, fun h => h⟩
    show 3 ≤ R.card
    rw [hRc]
    exact hq3
  have hR' : R.p ^ R.exponent = q := (TauCeti.PrimePower.card_def R).symm.trans hRc
  subst hR'
  have hFq' : Nat.card (GaloisField R.p (2 * R.exponent)) = (R.p ^ R.exponent) ^ 2 := by
    rw [GaloisField.card _ _ (by have := R.exponent_pos; omega), ← pow_mul, mul_comm]
  have e₃ : Q ≃* StatedSU 3 (R.p ^ R.exponent) (GaloisField R.p (2 * R.exponent)) :=
    e.trans (CFSG.Open.StatedSUFieldChange.statedSUEquiv φ 3 _)
  refine ⟨.lie ⟨.twistedA 2 R, hv⟩, ?_, ⟨?_⟩⟩
  · show 3 = 3 ∧ R.card % 6 = 5
    rw [TauCeti.PrimePower.card_def]
    exact ⟨rfl, h6⟩
  · exact ((QuotientGroup.congr _ _ e₃ (Subgroup.map_center_eq e₃)).trans
      (QuotientGroup.quotientMulEquivOfEq (k3_center_statedSU_three_eq hFq' h3))).trans
      (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 R hv).symm

theorem catalogIs_k3_of_k3LinearCover {p : ℕ} {Q : Type} [Group Q] (h : K3LinearCover p Q) :
    catalogIs (Q ⧸ Subgroup.center Q) (k3 p) := by
  obtain ⟨rfl, r, f, -, -, ⟨h6, hfl⟩ | ⟨h6, hfl⟩⟩ := h
  · obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = r ^ f ∧ Nonempty (Q ≃* StatedSL 3 F) := by
      simpa [FullLinearCover] using hfl
    exact catalogIs_k3_of_statedSL_three (by rw [hc]; exact h6) e
  · obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = (r ^ f) ^ 2 ∧ Nonempty (Q ≃* StatedSU 3 (r ^ f) F) := by
      simpa [FullLinearCover] using hfl
    exact catalogIs_k3_of_statedSU_three hc h6 e

theorem catalogIs_k3_of_k3Cover {p : ℕ} {Q : Type} [Group Q] (h : K3Cover p Q) :
    catalogIs (Q ⧸ Subgroup.center Q) (k3 p) := by
  obtain ⟨-, h | h | h⟩ := h
  · obtain ⟨hZ, i, hi, ⟨e⟩⟩ := h
    exact ⟨i, hi, ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans e)⟩⟩
  · exact catalogIs_k3_of_k3LinearCover h
  · obtain ⟨i, hi, ⟨-, -, -, -, π, hπ, hker, -⟩, -⟩ := h
    refine ⟨i, ?_, ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩⟩
    cases i <;> first | exact ⟨hi.1, Or.inl hi.2⟩ | exact ⟨hi.1, Or.inr hi.2⟩ | exact hi.elim

theorem level_three_of_not_balanced {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2) (hS3 : Stage3 G p)
    (h1912 : I1912At) (hd : dLevel G p = 3) {B : Subgroup G} {a : G} {I : Subgroup G}
    (hSt : IsSTriple p B a I) (hBI : B ≤ Subgroup.normalizer (I : Set G))
    (hnb : ¬ IsCompTwoPrimaryWeaklyLocallyBalanced p 1 B I) : catalogIs (PSimple p I) (k3 p) := by
  have h1 := tripleLevel_le_dLevel hSt
  obtain ⟨hB, hess, hI⟩ := hSt
  rw [hd] at h1
  unfold tripleLevel at h1
  have hnG : ¬ IsGStar p B I := by
    intro hG
    rw [if_pos hG] at h1
    omega
  rw [if_neg hnG] at h1
  have h2 : 2 < fullCoverLevel p (PQuot p I) := by
    by_contra hcon
    exact hnb (balanced_of_level_le_two hpp hp2 hS3 h1912 hB hess.1 hess.2.1 hI hBI (by omega))
  exact catalogIs_k3_of_k3Cover (k3Cover_of_fullCoverLevel_eq_three (by omega))

private theorem barX_oPPrimeP_415 (p : ℕ) (X : Subgroup G) :
    barX p X (oPPrimeP p X) = CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := by
  have hJg : (oPPrimeP p X).subgroupOf X =
      (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  show ((oPPrimeP p X).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = _
  rw [hJg]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

private theorem barX_le_centralizer_415 {p : ℕ} {X S T : Subgroup G}
    (h : ∀ t ∈ T, ∀ s ∈ S, ⁅t, s⁆ ∈ GLAPPrimeCoreOf p X) :
    barX p X S ≤ Subgroup.centralizer (barX p X T : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  refine barX_le_centralizer fun s hs t ht _ _ => ?_
  have h3 := Subgroup.inv_mem _ (h t ht s hs)
  rwa [commutatorElement_inv] at h3

private theorem eq_bot_of_le_fitting_415 {Q : Type} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcore : CFSG.pPrimeCore p Q = ⊥)
    {T : Subgroup Q} (hT : IsPGroup 2 T)
    (hc : T ≤ Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q)) : T = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : T ≤ CFSG.fittingSubgroup Q := by
    have h := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting Q
    rw [← CFSG.generalizedFitting_eq_componentClassification] at h
    exact hc.trans h
  have hpT : IsPGroup p T :=
    (CFSG.pCore_isPGroup (p := p) (G := Q)).to_le (h1.trans (CFSG.Fitting_eq_pcore Q p hcore).le)
  exact disjoint_self.1 (IsPGroup.disjoint_of_ne 2 p hp2.symm T T hT hpT)

private theorem le_glaPPrimeCoreOf_of_component_commutators {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X S : Subgroup G} (hS2 : IsPGroup 2 S) (hSX : S ≤ X)
    (hQ : (⁅oPPrimeP p X, S⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p X)
    (hJ : ∀ J : Subgroup G, GLAPComponent p X J → (⁅J, S⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p X) :
    S ≤ GLAPPrimeCoreOf p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcore : CFSG.pPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hS2' : IsPGroup 2 (barX p X S) :=
    (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm).map _
  have hF : CFSG.generalizedFitting (↥X ⧸ GLAPPrimeCore p ↥X) ≤
      Subgroup.centralizer (barX p X S : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rw [CFSG.generalizedFitting.eq_sup]
    refine sup_le ?_ ?_
    · rw [CFSG.Fitting_eq_pcore _ p hcore, Subgroup.le_centralizer_iff, ← barX_oPPrimeP_415 p X]
      exact barX_le_centralizer_415 fun t ht s hs => Subgroup.commutator_le.1 hQ t ht s hs
    · refine sSup_le fun K hK => ?_
      obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq X ((CFSG.isComponent_iff_open K).1 hK)
      rw [Subgroup.le_centralizer_iff]
      exact barX_le_centralizer_415 fun l hl s hs => Subgroup.commutator_le.1 (hJ L hL) l hl s hs
  have hbot : barX p X S = ⊥ :=
    eq_bot_of_le_fitting_415 hp hp2 hcore hS2' (Subgroup.le_centralizer_iff.2 hF)
  intro s hs
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨s, hSX hs⟩ ∈ barX p X S :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨s, hSX hs⟩, h1, rfl⟩

theorem exists_noncentral_component {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a x : G}
    {S₁ : Subgroup G} (hax : x ∈ Subgroup.centralizer ({a} : Set G)) (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) (hS₁2 : IsPGroup 2 S₁)
    (hS₁x : S₁ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))
    (hS₁a : S₁ ≤ Subgroup.centralizer ({a} : Set G))
    (hS₁n : ¬ S₁ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G))) :
    ∃ I : Subgroup G, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) I ∧
      x ∈ Subgroup.normalizer (I : Set G) ∧ ¬ CentMod p I x ∧ ∃ s ∈ S₁, ¬ CentMod p I s := by
  classical
  have hDX : Subgroup.zpowers x ≤ Subgroup.centralizer ({a} : Set G) := Subgroup.zpowers_le.2 hax
  have hDel : IsElemAbelian p (Subgroup.zpowers x) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hD1 : Subgroup.zpowers x ≠ ⊥ := fun h => hx1 (Subgroup.zpowers_eq_bot.1 h)
  have hin : InDelta p (Subgroup.centralizer ({a} : Set G)) (Subgroup.zpowers x) S₁ :=
    InDelta.of_le_gLADelta hp hDX hDel hD1 hS₁a (by rw [gLADelta_zpowers hp hxp hx1]; exact hS₁x)
  have hQ : (⁅oPPrimeP p (Subgroup.centralizer ({a} : Set G)), S₁⁆ : Subgroup G) ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) :=
    hin.commutator_oPrimePOf_le h1Stmt_zero hp
  obtain ⟨I, hI, hnc⟩ : ∃ I : Subgroup G, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) I ∧
      ¬ (⁅I, S₁⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set G)) := by
    by_contra hcon
    push_neg at hcon
    exact hS₁n (le_glaPPrimeCoreOf_of_component_commutators hp hp2 hS₁2 hS₁a hQ hcon)
  obtain ⟨hDN, hker⟩ := (hin.main h1Stmt_zero hp hI).2 hnc
  have hxN : x ∈ Subgroup.normalizer (I : Set G) := hDN (Subgroup.mem_zpowers x)
  refine ⟨I, hI, hxN, ?_, ?_⟩
  · intro hcm
    have hxq : x ∈ CFSG.HardMathSupport.Solomon.LocalBalance.centralizerQuot I (GLAPPrimeCoreOf p I) :=
      ⟨(CFSG.LocalAnalysis.GLTheoremA.centMod_iff.1 hcm).1,
        CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf p I
          (CFSG.LocalAnalysis.GLTheoremA.centMod_iff.1 hcm).1,
        fun y hy => (CFSG.LocalAnalysis.GLTheoremA.centMod_iff.1 hcm).2 y hy⟩
    have hxk : x ∈ CFSG.HardMathSupport.Solomon.LocalBalance.kerB p (Subgroup.zpowers x) I := by
      unfold CFSG.HardMathSupport.Solomon.LocalBalance.kerB
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers x, hxq⟩
    rw [hker, Subgroup.mem_bot] at hxk
    exact hx1 hxk
  · by_contra hcon
    push_neg at hcon
    apply hnc
    have h1 : (⁅I, S₁⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p I := by
      rw [Subgroup.commutator_le]
      intro l hl s hs
      exact (CFSG.LocalAnalysis.GLTheoremA.centMod_iff.1 (hcon s hs)).2 l hl
    exact h1.trans (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hp hI.2.1)

theorem normalizes_of_commutator {p : ℕ} {B S I C : Subgroup G}
    (hI : GLAPComponent p C I)
    (hall : ∀ I' : Subgroup G, GLAPComponent p C I' → B ≤ Subgroup.normalizer (I' : Set G))
    (hSC : S ≤ C) (hBSS : (⁅B, S⁆ : Subgroup G) = S) : S ≤ Subgroup.normalizer (I : Set G) := by
  calc S = ⁅B, S⁆ := hBSS.symm
    _ ≤ Subgroup.normalizer (I : Set G) := by
      rw [Subgroup.commutator_le]
      intro b hb s hs
      have hsC : s ∈ C := hSC hs
      have hCs : GLBConj s C = C := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hsC)
      have hI'' : GLAPComponent p C (GLBConj s I) := by
        have := glaPComponent_gLBConj hI s
        rwa [hCs] at this
      have hb1 : b ∈ Subgroup.normalizer (I : Set G) := hall I hI hb
      have hb2 : b⁻¹ ∈ Subgroup.normalizer ((GLBConj s I : Subgroup G) : Set G) :=
        Subgroup.inv_mem _ (hall _ hI'' hb)
      have hu : s * b⁻¹ * s⁻¹ ∈ Subgroup.normalizer (I : Set G) := by
        rw [mem_normalizer_iff_gLBConj_eq] at hb2 ⊢
        calc GLBConj (s * b⁻¹ * s⁻¹) I = GLBConj s⁻¹ (GLBConj b⁻¹ (GLBConj s I)) := by
              rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_assoc]
          _ = GLBConj s⁻¹ (GLBConj s I) := by rw [hb2]
          _ = I := by rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
      have hcomm : ⁅b, s⁆ = b * (s * b⁻¹ * s⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      rw [hcomm]
      exact Subgroup.mul_mem _ hb1 hu

theorem commutator_subgroupOf_of_le {N F₁ F₂ : Subgroup G} (h₁ : F₁ ≤ N) (h₂ : F₂ ≤ N) :
    (⁅F₁, F₂⁆ : Subgroup G).subgroupOf N = ⁅F₁.subgroupOf N, F₂.subgroupOf N⁆ := by
  have h₃ : (⁅F₁, F₂⁆ : Subgroup G) ≤ N :=
    (Subgroup.commutator_mono h₁ h₂).trans (commutator_self_le N)
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le h₃, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le h₁, Subgroup.map_subgroupOf_eq_of_le h₂]

theorem autBar_commutator {p : ℕ} {F₁ F₂ L : Subgroup G}
    (h₁ : F₁ ≤ Subgroup.normalizer (L : Set G)) (h₂ : F₂ ≤ Subgroup.normalizer (L : Set G)) :
    autBar p (⁅F₁, F₂⁆ : Subgroup G) L =
      (⁅autBar p F₁ L, autBar p F₂ L⁆ : Subgroup (MulAut (barOf p L))) := by
  have h₃ : (⁅F₁, F₂⁆ : Subgroup G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.commutator_mono h₁ h₂).trans (commutator_self_le _)
  unfold autBar
  rw [inf_eq_left.2 h₁, inf_eq_left.2 h₂, inf_eq_left.2 h₃,
    commutator_subgroupOf_of_le h₁ h₂, Subgroup.map_commutator]

theorem autBar_le_autBar {p : ℕ} {F₁ F₂ L : Subgroup G} (h : F₁ ≤ F₂) :
    autBar p F₁ L ≤ autBar p F₂ L := by
  unfold autBar
  apply Subgroup.map_mono
  intro g hg
  exact Subgroup.mem_subgroupOf.2
    (Subgroup.mem_inf.2 ⟨h (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).1, g.2⟩)

theorem barAut_mem_autBar {p : ℕ} {I F : Subgroup G} (hF : F ≤ Subgroup.normalizer (I : Set G))
    {x : G} (hx : x ∈ F) : barAut p I ⟨x, hF hx⟩ ∈ autBar p F I := by
  refine Subgroup.mem_map_of_mem _ ?_
  exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hx, hF hx⟩)

theorem autBar_normalizes {p : ℕ} {F₁ F₂ L : Subgroup G}
    (h₁ : F₁ ≤ Subgroup.normalizer (L : Set G)) (h₂ : F₂ ≤ Subgroup.normalizer (L : Set G))
    (h : F₁ ≤ Subgroup.normalizer (F₂ : Set G)) :
    autBar p F₁ L ≤ Subgroup.normalizer (autBar p F₂ L : Set (MulAut (barOf p L))) := by
  unfold autBar
  rw [inf_eq_left.2 h₁, inf_eq_left.2 h₂]
  have hN : F₁.subgroupOf (Subgroup.normalizer (L : Set G)) ≤
      Subgroup.normalizer ((F₂.subgroupOf (Subgroup.normalizer (L : Set G)) :
        Subgroup ↥(Subgroup.normalizer (L : Set G))) : Set ↥(Subgroup.normalizer (L : Set G))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.1 (h (Subgroup.mem_subgroupOf.1 hx)) (y : G)
    simpa [Subgroup.mem_subgroupOf] using this
  exact (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map _)

theorem isPGroup_autBar {p q : ℕ} {F L : Subgroup G} (hF : IsPGroup q F) :
    IsPGroup q (autBar p F L) := by
  rintro ⟨g, hg⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
  have hxF : (x : G) ∈ F := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1
  obtain ⟨k, hk⟩ := hF ⟨(x : G), hxF⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : x ^ (q ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  show (barAut p L x) ^ (q ^ k) = 1
  rw [← map_pow, h1, map_one]

theorem autBar_index_le {p : ℕ} {S Ss L : Subgroup G} (hSsS : Ss ≤ S)
    (hS : S ≤ Subgroup.normalizer (L : Set G)) (h : Nat.card S ≤ 4 * Nat.card Ss) :
    Nat.card (autBar p S L) ≤ 4 * Nat.card (autBar p Ss L) := by
  have hSs : Ss ≤ Subgroup.normalizer (L : Set G) := hSsS.trans hS
  unfold autBar
  rw [inf_eq_left.2 hS, inf_eq_left.2 hSs]
  have hAT : Ss.subgroupOf (Subgroup.normalizer (L : Set G)) ≤
      S.subgroupOf (Subgroup.normalizer (L : Set G)) := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hSsS (Subgroup.mem_subgroupOf.1 hx))
  have hT₀card : Nat.card (S.subgroupOf (Subgroup.normalizer (L : Set G))) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  have hA₀card : Nat.card (Ss.subgroupOf (Subgroup.normalizer (L : Set G))) = Nat.card Ss :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSs).toEquiv
  have h1 := Subgroup.relIndex_mul_card (H := (barAut p L).ker)
    (K := S.subgroupOf (Subgroup.normalizer (L : Set G)))
  have h2 := Subgroup.relIndex_mul_card (H := (barAut p L).ker)
    (K := Ss.subgroupOf (Subgroup.normalizer (L : Set G)))
  rw [Subgroup.relIndex_ker] at h1 h2
  have hle := Subgroup.card_le_of_le (inf_le_inf_left (barAut p L).ker hAT)
  have hpos : 0 < Nat.card ↥((barAut p L).ker ⊓ S.subgroupOf (Subgroup.normalizer (L : Set G))) :=
    Nat.card_pos
  have key : Nat.card ↥((S.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)) *
      Nat.card ↥((barAut p L).ker ⊓ S.subgroupOf (Subgroup.normalizer (L : Set G))) ≤
      (4 * Nat.card ↥((Ss.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))) *
        Nat.card ↥((barAut p L).ker ⊓ S.subgroupOf (Subgroup.normalizer (L : Set G))) := by
    calc _ = Nat.card (S.subgroupOf (Subgroup.normalizer (L : Set G))) := h1
      _ ≤ 4 * Nat.card (Ss.subgroupOf (Subgroup.normalizer (L : Set G))) := by
          rw [hT₀card, hA₀card]
          exact h
      _ = 4 * (Nat.card ↥((Ss.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)) *
            Nat.card ↥((barAut p L).ker ⊓ Ss.subgroupOf (Subgroup.normalizer (L : Set G)))) := by
          rw [h2]
      _ ≤ 4 * (Nat.card ↥((Ss.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)) *
            Nat.card ↥((barAut p L).ker ⊓ S.subgroupOf (Subgroup.normalizer (L : Set G)))) := by
          gcongr
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right key hpos

theorem innerAut_le_autBar {p : ℕ} {I F : Subgroup G} (hIF : I ≤ F)
    (hF : F ≤ Subgroup.normalizer (I : Set G)) : innerAut (barOf p I) ≤ autBar p F I := by
  rintro _ ⟨k, rfl⟩
  obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective k
  have hiF : (i : G) ∈ F := hIF i.2
  have h := barAut_mem_autBar (p := p) hF hiF
  convert h using 1
  ext z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  rw [barAut_mk]
  simp only [MulAut.conj_apply]
  first | rfl | simp [Subgroup.normalizerMonoidHom_apply_apply_coe] | done

theorem centMod_of_barAut_eq_one {p : ℕ} {I : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (I : Set G)) (h : barAut p I ⟨x, hx⟩ = 1) : CentMod p I x := by
  refine ⟨hx, ?_⟩
  rw [Subgroup.commutator_le]
  intro y hy k hk
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hxn : x ^ n ∈ Subgroup.normalizer (I : Set G) := Subgroup.zpow_mem _ hx n
  have h1 : barAut p I ⟨x ^ n, hxn⟩ = 1 := by
    have e : (⟨x ^ n, hxn⟩ : ↥(Subgroup.normalizer (I : Set G))) =
        (⟨x, hx⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ n := Subtype.ext (by simp)
    rw [e, map_zpow, h, one_zpow]
  have hyi : y⁻¹ ∈ I := I.inv_mem hy
  have h2 := congrArg (fun φ : MulAut (barOf p I) => φ (QuotientGroup.mk ⟨y⁻¹, hyi⟩)) h1
  simp only [barAut_mk, MulAut.one_apply] at h2
  rw [QuotientGroup.eq] at h2
  refine ⟨_, Subgroup.inv_mem _ h2, ?_⟩
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def, mul_assoc]

theorem barAut_ne_one {p : ℕ} {I : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (I : Set G))
    (hnc : ¬ CentMod p I x) : barAut p I ⟨x, hx⟩ ≠ 1 :=
  fun h => hnc (centMod_of_barAut_eq_one hx h)

theorem autBar_ne_bot {p : ℕ} {I S₁ : Subgroup G} (hS₁ : S₁ ≤ Subgroup.normalizer (I : Set G))
    {s : G} (hs : s ∈ S₁) (hsnc : ¬ CentMod p I s) : autBar p S₁ I ≠ ⊥ := by
  intro h
  have hmem := barAut_mem_autBar (p := p) hS₁ hs
  rw [h] at hmem
  exact barAut_ne_one (hS₁ hs) hsnc (Subgroup.mem_bot.1 hmem)

private theorem q4_isPGroup_zpowers {M : Type*} [Group M] {p : ℕ} {y : M} (h : y ^ p = 1) :
    IsPGroup p (Subgroup.zpowers y) := by
  intro g
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, h, one_zpow]
  rfl

private theorem q4_centralizer_zpowers_eq {M : Type*} [Group M] (y : M) :
    Subgroup.centralizer ((Subgroup.zpowers y : Subgroup M) : Set M) =
      Subgroup.centralizer ({y} : Set M) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h y (Subgroup.mem_zpowers y)).symm
  · intro h k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_left (show Commute y g from h.symm) n).eq

private theorem q4_image_le_core {p : ℕ} (hp : p.Prime) {I V Ss : Subgroup G} {x : G}
    (hV : V ≤ Subgroup.normalizer (I : Set G)) (hxV : x ∈ V) (hxp : x ^ p = 1)
    (hSsV : Ss ≤ V) (hSs : Ss ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) :
    autBar p Ss I ≤ GLAPPrimeCoreOf p (autBar p V I ⊓
      Subgroup.centralizer ({barAut p I ⟨x, hV hxV⟩} : Set (MulAut (barOf p I)))) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥V →* ↥(autBar p V I),
      ∀ v : ↥V, (φ v : MulAut (barOf p I)) = barAut p I ⟨(v : G), hV v.2⟩ :=
    ⟨((barAut p I).comp (Subgroup.inclusion hV)).codRestrict (autBar p V I)
      (fun v => barAut_mem_autBar hV v.2), fun v => rfl⟩
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.1 (show (z : MulAut (barOf p I)) ∈
      ((V ⊓ Subgroup.normalizer (I : Set G)).subgroupOf (Subgroup.normalizer (I : Set G))).map
        (barAut p I) from z.2)
    have hkV : (k : G) ∈ V := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).1
    exact ⟨⟨(k : G), hkV⟩, Subtype.ext ((hφ ⟨(k : G), hkV⟩).trans hkz)⟩
  have hxp' : (⟨x, hxV⟩ : ↥V) ^ p = 1 := Subtype.ext hxp
  have hQp : IsPGroup p (Subgroup.zpowers (⟨x, hxV⟩ : ↥V)) := q4_isPGroup_zpowers hxp'
  have hImg : (Subgroup.centralizer ({(⟨x, hxV⟩ : ↥V)} : Set ↥V)).map V.subtype =
      Subgroup.centralizer ({x} : Set G) ⊓ V := by
    ext g
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hw)
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (by simpa using hw'), w.2⟩
    · intro hg
      obtain ⟨hgC, hgV⟩ := Subgroup.mem_inf.1 hg
      exact ⟨⟨g, hgV⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hgC)), rfl⟩
  have hI1 : (GLAPPrimeCoreOf p (Subgroup.centralizer ({(⟨x, hxV⟩ : ↥V)} : Set ↥V))).map
      V.subtype = GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ V) := by
    rw [CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p V.subtype
      V.subtype_injective, hImg]
  have hSsC : Ss.subgroupOf V ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ({(⟨x, hxV⟩ : ↥V)} : Set ↥V)) := by
    intro v hv
    have hmem : (v : G) ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ V) :=
      CFSG.HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp _ _
        ⟨hSs (Subgroup.mem_subgroupOf.1 hv), v.2⟩
    rw [← hI1] at hmem
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.1 hmem
    have hwv' : w = v := Subtype.ext hwv
    rw [← hwv']
    exact hw
  have hφx : (φ ⟨x, hxV⟩ : MulAut (barOf p I)) = barAut p I ⟨x, hV hxV⟩ := hφ ⟨x, hxV⟩
  have hImg2 : (Subgroup.centralizer ({φ ⟨x, hxV⟩} : Set ↥(autBar p V I))).map
      (autBar p V I).subtype =
      autBar p V I ⊓ Subgroup.centralizer ({barAut p I ⟨x, hV hxV⟩} :
        Set (MulAut (barOf p I))) := by
    ext g
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hz)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hφx] at hz'
      exact Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_singleton_iff.2 hz'⟩
    · intro hg
      obtain ⟨hgV, hgC⟩ := Subgroup.mem_inf.1 hg
      refine ⟨⟨g, hgV⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hφx]
      exact Subgroup.mem_centralizer_singleton_iff.1 hgC
  have hI2 : (GLAPPrimeCoreOf p (Subgroup.centralizer ({φ ⟨x, hxV⟩} : Set ↥(autBar p V I)))).map
      (autBar p V I).subtype = GLAPPrimeCoreOf p (autBar p V I ⊓
        Subgroup.centralizer ({barAut p I ⟨x, hV hxV⟩} : Set (MulAut (barOf p I)))) := by
    rw [← hImg2]
    exact CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p
      (autBar p V I).subtype (autBar p V I).subtype_injective _
  have hB1 : (Ss.subgroupOf V).map φ ≤ (GLAPPrimeCoreOf p
      (Subgroup.centralizer ({(⟨x, hxV⟩ : ↥V)} : Set ↥V))).map φ := Subgroup.map_mono hSsC
  have hH1 := CFSG.HardMathSupport.Timmesfeld.Proving.map_glaPPrimeCoreOf_centralizer_le φ hφs hp hQp
  rw [q4_centralizer_zpowers_eq, MonoidHom.map_zpowers, q4_centralizer_zpowers_eq] at hH1
  have hA : autBar p Ss I ≤ ((Ss.subgroupOf V).map φ).map (autBar p V I).subtype := by
    intro g hg
    unfold autBar at hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
    have hkS : (k : G) ∈ Ss := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).1
    have hkV : (k : G) ∈ V := hSsV hkS
    exact ⟨φ ⟨(k : G), hkV⟩, Subgroup.mem_map.2 ⟨⟨(k : G), hkV⟩,
      Subgroup.mem_subgroupOf.2 hkS, rfl⟩, hφ ⟨(k : G), hkV⟩⟩
  exact hA.trans ((Subgroup.map_mono (f := (autBar p V I).subtype) (hB1.trans hH1)).trans
    (le_of_eq hI2))

theorem image_le_core {p : ℕ} (hp : p.Prime) {I B S Ss : Subgroup G} {x : G}
    (hBI : B ≤ Subgroup.normalizer (I : Set G)) (hSI : S ≤ Subgroup.normalizer (I : Set G))
    (hxB : x ∈ B) (hxp : x ^ p = 1) (hSsS : Ss ≤ S)
    (hSs : Ss ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) :
    autBar p Ss I ≤ GLAPPrimeCoreOf p (autBar p (B ⊔ S ⊔ I) I ⊓
      Subgroup.centralizer ({barAut p I ⟨x, hBI hxB⟩} : Set (MulAut (barOf p I)))) := by
  have hBV : B ≤ B ⊔ S ⊔ I := le_sup_left.trans le_sup_left
  have hSV : S ≤ B ⊔ S ⊔ I := le_sup_right.trans le_sup_left
  have hVN : B ⊔ S ⊔ I ≤ Subgroup.normalizer (I : Set G) :=
    sup_le (sup_le hBI hSI) Subgroup.le_normalizer
  exact q4_image_le_core hp hVN (hBV hxB) hxp (hSsS.trans hSV) hSs

theorem step10_delta {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) (hS3 : Stage3 G p)
    (hS4o : Stage4Order G p) (h1912 : I1912At) (h1913 : I1913At) (h2027 : I2027At)
    {B : Subgroup G} {x : G} {L : Subgroup G} (hD3 : D3Data G p B x L) {D S Ss : Subgroup G}
    (hP : Prop415Pre B x D S Ss) :
    (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≤ GLADelta p D := by
  have hp3 := hD3.p_eq
  subst hp3
  have hpp : Nat.Prime 3 := hp.1.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨-, -, -, -, -, -, -, h412⟩ := hS4o
  obtain ⟨hB, hess, hL⟩ := hD3.isS0.1
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hBel : IsElemAbelian 3 B := hB.1
  have hd : dLevel G 3 = 3 := hD3.hd
  have hd4 : dLevel G 3 ≤ 4 := by omega
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  refine le_iInf fun a => le_iInf fun haD => le_iInf fun ha1 => ?_
  by_contra hnot
  have haB : a ∈ B := hP.DB haD
  have hSa : S ≤ Subgroup.centralizer ({a} : Set G) :=
    hP.SD.trans (Subgroup.centralizer_le (by rw [Set.singleton_subset_iff]; exact haD))
  have hSS' : (⁅S, S⁆ : Subgroup G) ≤ S := commutator_self_le S
  have hBS' : B ≤ Subgroup.normalizer ((⁅S, S⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hP.BS hP.BS
  have hS₁S' : (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≤ ⁅S, S⁆ := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_normalizes hBS'
  have hS₁2 : IsPGroup 2 (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) :=
    hP.S2.to_le (hS₁S'.trans hSS')
  have hess_a : IsEssential 3 B a := isEssential_of_two_group haB ha1 hP.S2 hSa hP.BS hP.ne
  have hS₁x : (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≤
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) :=
    hS₁S'.trans (hP.SSle.trans hP.Ssx)
  have hS₁a : (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) :=
    hS₁S'.trans (hSS'.trans hSa)
  have hax : x ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hxB haB)
  obtain ⟨I, hIcomp, hxI, hxnc, s, hs, hsnc⟩ :=
    exists_noncentral_component hpp hp2 hax hx1 hx3 hS₁2 hS₁x hS₁a hnot
  have hall : ∀ I' : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) I' →
      B ≤ Subgroup.normalizer (I' : Set G) :=
    fun I' hI' => h412 hd4 B a I' ⟨hB, hess_a, hI'⟩
  have hBI : B ≤ Subgroup.normalizer (I : Set G) := hall I hIcomp
  have hSI : S ≤ Subgroup.normalizer (I : Set G) :=
    normalizes_of_commutator hIcomp hall hSa hP.BSS
  have hSsI : Ss ≤ Subgroup.normalizer (I : Set G) := hP.SsS.trans hSI
  have hS'I : (⁅S, S⁆ : Subgroup G) ≤ Subgroup.normalizer (I : Set G) := hSS'.trans hSI
  have hS₁I : (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≤ Subgroup.normalizer (I : Set G) :=
    hS₁S'.trans hS'I
  have hVI : B ⊔ S ⊔ I ≤ Subgroup.normalizer (I : Set G) :=
    sup_le (sup_le hBI hSI) Subgroup.le_normalizer
  have hBV₀ : B ≤ Subgroup.normalizer ((B ⊔ S ⊔ I : Subgroup G) : Set G) :=
    le_normalizer_sup (le_normalizer_sup Subgroup.le_normalizer hP.BS) hBI
  have hKq : CFSG.Open.IsQuasisimple (barOf 3 I) := isQuasisimple_pQuot_of_glaPComponent hpp hIcomp
  have hlevel := level_three_of_not_balanced hpp hp2 hS3 h1912 hd ⟨hB, hess_a, hIcomp⟩ hBI
  refine step10_aut hKq h1913 h2027 (V := autBar 3 (B ⊔ S ⊔ I) I)
    (xt := barAut 3 I ⟨x, hBI hxB⟩)
    (CFSG.HardMathSupport.Timmesfeld.Balance.Alt.isElemAbelian_autBar hBel I)
    (isPGroup_autBar hP.S2) (autBar_normalizes hBI hSI hP.BS) ?_ (autBar_le_autBar hP.SsS)
    (autBar_normalizes hBI hSsI hP.BSs) (autBar_index_le hP.SsS hSI hP.idx) ?_ ?_
    (innerAut_le_autBar le_sup_right hVI) (autBar_le_autBar (le_sup_left.trans le_sup_left))
    (autBar_normalizes hBI hVI hBV₀) (barAut_mem_autBar hBI hxB) (barAut_ne_one (hBI hxB) hxnc)
    (image_le_core hpp hBI hSI hxB hx3 hP.SsS hP.Ssx) hlevel
  · rw [← autBar_commutator hBI hSI, hP.BSS]
  · rw [← autBar_commutator hSI hSI]
    exact autBar_le_autBar hP.SSle
  · rw [← autBar_commutator hSI hSI, ← autBar_commutator hBI hS'I]
    exact autBar_ne_bot hS₁I hs hsnc

theorem prop415_final {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) (hS3 : Stage3 G p)
    (hS4o : Stage4Order G p) (h1912 : I1912At) (h1913 : I1913At) (h2027 : I2027At)
    {B : Subgroup G} {x : G} {L : Subgroup G} (hD3 : D3Data G p B x L) {D S Ss : Subgroup G}
    (hP : Prop415Pre B x D S Ss) : False := by
  have h1 := step10_delta hctx hp hS3 hS4o h1912 h1913 h2027 hD3 hP
  have hp3 := hD3.p_eq
  subst hp3
  have hpp : Nat.Prime 3 := hp.1.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hΔ : GLADeltaZero G 3 := hp.2.2
  obtain ⟨hB, -, -⟩ := hD3.isS0.1
  have hSS' : (⁅S, S⁆ : Subgroup G) ≤ S := commutator_self_le S
  have hBS' : B ≤ Subgroup.normalizer ((⁅S, S⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hP.BS hP.BS
  have hS₁S' : (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≤ ⁅S, S⁆ := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_normalizes hBS'
  have hS₁2 : IsPGroup 2 (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) :=
    hP.S2.to_le (hS₁S'.trans hSS')
  have hBS₁ : B ≤ Subgroup.normalizer ((⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer hBS'
  have hcop : Nat.Coprime 3 (Nat.card (⁅S, S⁆ : Subgroup G)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (hP.S2.to_le hSS').exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hpp Nat.prime_two).2 hp2)
  have hSB := i321UsedAt_holds (G := G) 3 hpp (⁅S, S⁆ : Subgroup G) B hcop hBS'
    (pGroup_residual hpp (isPGroup_of_isElemAbelian hB.1))
  have hne : (⁅(⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G), B⁆ : Subgroup G) ≠ ⊥ := by
    rw [Subgroup.commutator_comm B (⁅S, S⁆ : Subgroup G), hSB]
    rw [← Subgroup.commutator_comm B (⁅S, S⁆ : Subgroup G)]
    exact hP.ne
  exact delta_zero_contra hpp hp2 hΔ hB hP.DB hP.Del (hP.Dc.trans (by norm_num)) hS₁2 h1 hBS₁ hne

theorem prop415 {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) (hS3 : Stage3 G p)
    (hS4o : Stage4Order G p) (h413 : Lemma413At G p) (h414 : Lemma414At G p) (h183 : Input18_3_4)
    (h1810 : I1810UsedAt G p) (h145 : I145UsedAt G p) (h264 : I264At G p) (h91 : I91At G)
    (h147 : I147At G) (h1016 : I1016At G) (h71 : I71M12At G) (h1426 : I1426At G p)
    (h1912 : I1912At) (h1913 : I1913At) (h2027 : I2027At) :
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsS0 p B x L →
      Odd (Nat.card (⁅L, GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))⁆ : Subgroup G)) := by
  intro B x L hS0
  by_contra hodd
  have hev := Nat.not_odd_iff_even.1 hodd
  have hD3 := prop415_d3 hctx hp hS3 hS4o h413 h414 h183 h1810 h264 h91 h147 hS0 hev
  obtain ⟨B', hD3', hM⟩ : ∃ B' : Subgroup G, D3Data G p B' x L ∧
      (catalogIs (PSimple p L) isM12 → ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧
        B' ≤ Subgroup.normalizer (U : Set G) ∧ ¬ U ≤ GLAPPrimeCoreOf p L) := by
    by_cases hM12 : catalogIs (PSimple p L) isM12
    · obtain ⟨B', hD3', U, hU⟩ := m12_adjust hctx hp h1810 h1016 h71 hD3 hM12
      exact ⟨B', hD3', fun _ => ⟨U, hU⟩⟩
    · exact ⟨B, hD3, fun h => absurd h hM12⟩
  obtain ⟨D, S, Ss, hP⟩ := prop415_pre hctx hp h1810 h145 h1426 hD3' hM
  exact prop415_final hctx hp hS3 hS4o h1912 h1913 h2027 hD3' hP

end CFSG.LocalAnalysis.GLTheoremA
