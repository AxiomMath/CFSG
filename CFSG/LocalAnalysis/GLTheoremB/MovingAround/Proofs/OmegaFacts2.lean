module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims137
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFacts
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims138
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvFinal
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.CTP.SpEven
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate41501
public import Certificates.Certificate7233Base
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts2

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Curtis.Coordinator.PLType (fourProd)

theorem card_eq_omegaOrd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hfp : HasFixedPointFreeOrder ε n p) {K : Type} [Group K] [Finite K]
    (hK : IsOmegaTwo ε (n + 1) K) : Nat.card K = OmegaFacts.omegaOrd ε (n + 1) := by
  rcases OmegaFacts.omega_data hK with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, h60, -⟩ |
      ⟨-, h, -⟩
  · omega
  · omega
  · exact absurd hfp
      (CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2)
  · rw [h60]
    decide
  · exact h

theorem card_statedSp_eq_fourProd (n : ℕ) :
    Nat.card ↥(StatedSp n (ZMod 2)) = 2 ^ (n ^ 2) * fourProd n := by
  rw [OmegaFacts.card_statedSp_zmod_two]
  unfold fourProd
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [pow_mul]
  norm_num

theorem not_dvd_sign_succ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hfp : HasFixedPointFreeOrder ε n p) :
    ¬ p ∣ (if ε then 2 ^ (n + 1) - 1 else 2 ^ (n + 1) + 1) := by
  have hd := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.dvd_typeSign_of_hasFixedPointFreeOrder
    hp hp2 hn hfp
  unfold CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.typeSign at hd
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  intro h
  cases ε
  · simp only [Bool.false_eq_true, ↓reduceIte] at hd h
    have h2 : 2 ^ (n + 1) + 1 + 1 = 2 * (2 ^ n + 1) := by omega
    have h3 : p ∣ 2 ^ (n + 1) + 1 + 1 := h2 ▸ dvd_mul_of_dvd_right hd 2
    have h4 : p ∣ 1 := (Nat.dvd_add_right h).1 h3
    exact hp.ne_one (Nat.dvd_one.1 h4)
  · simp only [↓reduceIte] at hd h
    have h2 : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by omega
    rw [h2] at h
    have h4 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_right hd 2)).1 h
    exact hp.ne_one (Nat.dvd_one.1 h4)

theorem input10_13Omega_holds : Claims137.Input10_13Omega := by
  intro p hp hp2 ε n hn hfp K _ _ L hK hL
  obtain ⟨e⟩ := hL
  have hKc := card_eq_omegaOrd hp hp2 hn hfp hK
  have hLc : Nat.card ↥L = 2 ^ (n ^ 2) * fourProd n := by
    rw [Nat.card_congr e.toEquiv, card_statedSp_eq_fourProd]
  rw [hLc]
  refine Dvd.dvd.mul_left ?_ _
  have hdvd : p ^ (Nat.card K).factorization p ∣ Nat.card K := Nat.ordProj_dvd _ _
  rw [hKc] at hdvd ⊢
  unfold OmegaFacts.omegaOrd at hdvd ⊢
  simp only [Nat.add_sub_cancel] at hdvd ⊢
  refine Nat.Coprime.dvd_of_dvd_mul_left ?_ hdvd
  refine Nat.Coprime.pow_left _ ?_
  refine Nat.Coprime.mul_right ?_ ?_
  · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  · exact (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_sign_succ hp hp2 hn hfp)

section LiftSimple

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk barOf coprime_card_gLAPPrimeCore_aux)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open AltFacts2 (isPiGroup_of_mulEquiv le_Ke_of_component core_le_Ke)
open AltFacts3 (fixedSub_barAut_eq_p ker_inclusion_le_core)

variable {G : Type} [Group G] [Finite G]

theorem lift_simple {p : ℕ} (hp : p.Prime) {K : Subgroup G} {e : G}
    (heN : e ∈ Subgroup.normalizer (K : Set G)) (hep : e ^ p = 1)
    {A₀ : Subgroup (barOf p K)}
    (hA₀F : A₀ ≤ fixedSub (barAut p K ⟨e, heN⟩))
    (hA₀N : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), y ∈ Subgroup.normalizer (A₀ : Set (barOf p K)))
    (hsimpA : IsSimpleGroup ↥A₀) (hpdvd : p ∣ Nat.card ↥A₀) (hPiA : IsPiGroup p ↥A₀) :
    A₀ ≤ barX p K (Prop1116.Ke p K e) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hntA : Nontrivial ↥A₀ := hsimpA.toNontrivial
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({e} : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  have hF : fixedSub (barAut p K ⟨e, heN⟩) = barX p K C := fixedSub_barAut_eq_p hp hep heN
  let ρ : ↥C →* barOf p K :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hCK)
  have hρF : ∀ c : ↥C, ρ c ∈ fixedSub (barAut p K ⟨e, heN⟩) := by
    intro c
    rw [hF]
    exact ⟨⟨c, hCK c.2⟩, Subgroup.mem_subgroupOf.2 c.2, rfl⟩
  have hρsurj : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), ∃ c : ↥C, ρ c = y := by
    intro y hy
    rw [hF] at hy
    obtain ⟨⟨c, hcK⟩, hc, rfl⟩ := hy
    exact ⟨⟨c, Subgroup.mem_subgroupOf.1 hc⟩, rfl⟩
  have hkerC : ∀ x : ↥C, ρ x = 1 → x ∈ GLAPPrimeCore p ↥C := fun x hx =>
    ker_inclusion_le_core p hCK (MonoidHom.mem_ker.2 hx)
  set NC : Subgroup ↥C := GLAPPrimeCore p ↥C with hNC
  set R : Subgroup (barOf p K) := NC.map ρ with hR
  have hRcop : Nat.Coprime p (Nat.card R) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ ρ) (coprime_card_gLAPPrimeCore_aux p ↥C)
  have hRnorm : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    intro y hy r hr
    obtain ⟨c, rfl⟩ := hρsurj y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hr
    refine Subgroup.mem_map.2 ⟨c * n * c⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact (GLAPPrimeCore.normal p ↥C).conj_mem n hn c
  have hRA : ∀ a ∈ A₀, a ∈ R → a = 1 := by
    have hnormS : (R.subgroupOf A₀).Normal := ⟨fun r hr a => by
      have hr' : (r : barOf p K) ∈ R := hr
      show ((a * r * a⁻¹ : ↥A₀) : barOf p K) ∈ R
      simpa using hRnorm (a : barOf p K) (hA₀F a.2) _ hr'⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf A₀) with h | h
    · intro a ha haR
      have h1 : (⟨a, ha⟩ : ↥A₀) ∈ R.subgroupOf A₀ := haR
      rw [h, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    · exfalso
      have hle : A₀ ≤ R := fun a ha => by
        have h1 : (⟨a, ha⟩ : ↥A₀) ∈ R.subgroupOf A₀ := by rw [h]; exact Subgroup.mem_top _
        exact h1
      have hd : Nat.card ↥A₀ ∣ Nat.card ↥R := Subgroup.card_dvd_of_le hle
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hRcop (dvd_refl p) (hpdvd.trans hd))
  set P : Subgroup ↥C := A₀.comap ρ with hP
  have hPnorm : P.Normal := ⟨fun x hx c => by
    have hx' : ρ x ∈ A₀ := hx
    show ρ (c * x * c⁻¹) ∈ A₀
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hA₀N _ (hρF c)) (ρ x)).1 hx'⟩
  set K' : Subgroup (↥C ⧸ NC) := P.map (QuotientGroup.mk' NC) with hK'
  let π₁ : ↥P →* ↥A₀ := (ρ.comp P.subtype).codRestrict A₀ (fun x => x.2)
  have hπ₁ : Function.Surjective π₁ := by
    intro a
    obtain ⟨c, hc⟩ := hρsurj (a : barOf p K) (hA₀F a.2)
    have hcP : c ∈ P := by
      show ρ c ∈ A₀
      rw [hc]; exact a.2
    exact ⟨⟨c, hcP⟩, Subtype.ext hc⟩
  let π₂ : ↥P →* ↥K' :=
    ((QuotientGroup.mk' NC).comp P.subtype).codRestrict K' (fun x => ⟨x, x.2, rfl⟩)
  have hπ₂ : Function.Surjective π₂ := by
    rintro ⟨_, ⟨c, hc, rfl⟩⟩
    exact ⟨⟨c, hc⟩, rfl⟩
  have hker12 : π₁.ker ≤ π₂.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : ρ (x : ↥C) = 1 := congrArg Subtype.val hx
    have h2 : (x : ↥C) ∈ NC := hkerC _ h1
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h2)
  let f1 : ↥A₀ →* ↥K' :=
    (QuotientGroup.lift π₁.ker π₂ hker12).comp
      (QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).symm.toMonoidHom
  have hf1 : ∀ x : ↥P, f1 (π₁ x) = π₂ x := by
    intro x
    show (QuotientGroup.lift π₁.ker π₂ hker12)
      ((QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).symm (π₁ x)) = _
    have : (QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).symm (π₁ x) =
        (QuotientGroup.mk x : ↥P ⧸ π₁.ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    rw [this, QuotientGroup.lift_mk]
  have hf1s : Function.Surjective f1 := by
    intro y
    obtain ⟨x, rfl⟩ := hπ₂ y
    exact ⟨π₁ x, hf1 x⟩
  have hKnt : Nontrivial ↥K' := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hPN : ∀ x : ↥C, x ∈ P → x ∈ NC := by
      intro x hx
      have h1 : π₂ ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).1 (congrArg Subtype.val h1)
    have hA₀1 : ∀ a ∈ A₀, a = 1 := by
      intro a ha
      obtain ⟨c, hc⟩ := hρsurj a (hA₀F ha)
      have hcP : c ∈ P := by
        show ρ c ∈ A₀
        rw [hc]; exact ha
      exact hRA a ha ⟨c, hPN c hcP, hc⟩
    obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : ↥A₀)).1 hntA
    exact ha (Subtype.ext (hA₀1 a a.2))
  have hf1i : Function.Injective f1 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f1.ker with h | h
    · exact h
    · exfalso
      have h1 : ∀ x : ↥A₀, f1 x = 1 := fun x => by
        rw [← MonoidHom.mem_ker, h]; exact Subgroup.mem_top x
      obtain ⟨y, hy⟩ := (nontrivial_iff_exists_ne (1 : ↥K')).1 hKnt
      obtain ⟨x, rfl⟩ := hf1s y
      exact hy (h1 x)
  let e₂ : ↥A₀ ≃* ↥K' := MulEquiv.ofBijective f1 ⟨hf1i, hf1s⟩
  have hKq : CFSG.Open.IsQuasisimple ↥K' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e₂ hPiA.1
  have hcomp : IsComponentOf K' (⊤ : Subgroup (↥C ⧸ NC)) := by
    refine ⟨le_top, ?_, hKq⟩
    haveI : K'.Normal := hPnorm.map _ (QuotientGroup.mk'_surjective NC)
    exact IsSubnormal.step le_top (Subgroup.Normal.subgroupOf inferInstance _) (IsSubnormal.refl _)
  obtain ⟨J, hJ, hJK⟩ := exists_glaPComponent_barX_eq (p := p) C hcomp
  let φ : barOf p J ≃* ↥A₀ :=
    (barXEquiv hp hJ.2.1).trans ((MulEquiv.subgroupCongr hJK).trans e₂.symm)
  have hPi : IsPiGroup p (barOf p J) := isPiGroup_of_mulEquiv φ.symm hPiA
  have hJKe : J ≤ Prop1116.Ke p K e := le_Ke_of_component hJ hPi
  intro a ha
  obtain ⟨c, hc⟩ := hρsurj a (hA₀F ha)
  have hcP : c ∈ P := by
    show ρ c ∈ A₀
    rw [hc]; exact ha
  have hmem : QuotientGroup.mk' NC c ∈ barX p C J := by
    rw [hJK]; exact ⟨c, hcP, rfl⟩
  obtain ⟨j', hj', hjc⟩ := hmem
  have hn : j'⁻¹ * c ∈ NC := QuotientGroup.eq.1 hjc
  have hcKe : (c : G) ∈ Prop1116.Ke p K e := by
    have h1 : (j' : G) ∈ Prop1116.Ke p K e := hJKe (Subgroup.mem_subgroupOf.1 hj')
    have h2 : ((j'⁻¹ * c : ↥C) : G) ∈ GLAPPrimeCoreOf p C :=
      (mem_gLAPPrimeCoreOf_iff p C _).2 ⟨(j'⁻¹ * c).2, hn⟩
    have h3 : ((j'⁻¹ * c : ↥C) : G) ∈ Prop1116.Ke p K e := core_le_Ke p K e h2
    have h4 := (Prop1116.Ke p K e).mul_mem h1 h3
    simpa using h4
  refine ⟨⟨(c : G), hCK c.2⟩, Subgroup.mem_subgroupOf.2 hcKe, ?_⟩
  exact hc

end LiftSimple

section PlaneGen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (fixedSub)

local notation "fixV" => CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.fixSub

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem exists_inner_hom {p : ℕ} {D : Type*} [Group D] (hDp : ∀ d : D, d ^ p = 1)
    {Kb L : Type*} [Group Kb] [Group L] (f : Kb ≃* L) (β : D →* MulAut Kb)
    (hAut : ∀ σ : MulAut L, σ ^ p = 1 → ∃ y : L, σ = MulAut.conj y)
    (hcenter : ∀ z : L, (∀ x : L, z * x = x * z) → z = 1) :
    ∃ Yh : D →* L, ∀ (d : D) (x : Kb), f (β d x) = Yh d * f x * (Yh d)⁻¹ := by
  classical
  let ψ : D →* MulAut L := (MulAut.congr f).toMonoidHom.comp β
  have hψp : ∀ a : D, ψ a ^ p = 1 := by
    intro a
    rw [← map_pow, hDp a, map_one]
  choose yfun hyfun using fun a : D => hAut (ψ a) (hψp a)
  have hconj_inj : ∀ u v : L, MulAut.conj u = MulAut.conj v → u = v := by
    intro u v h
    have h1 : v⁻¹ * u = 1 := hcenter _ (fun x => by
      have := congrArg (fun f : MulAut L => f x) h
      simp only [MulAut.conj_apply] at this
      calc (v⁻¹ * u) * x = v⁻¹ * (u * x * u⁻¹) * u := by group
        _ = v⁻¹ * (v * x * v⁻¹) * u := by rw [this]
        _ = x * (v⁻¹ * u) := by group)
    exact (inv_mul_eq_one.mp h1).symm
  let Yh : D →* L :=
    { toFun := yfun
      map_one' := by
        apply hconj_inj
        rw [← hyfun, map_one, map_one]
      map_mul' := fun a b => by
        apply hconj_inj
        rw [map_mul, ← hyfun, ← hyfun, ← hyfun, map_mul] }
  refine ⟨Yh, fun d x => ?_⟩
  have h1 : ψ d (f x) = MulAut.conj (Yh d) (f x) := by
    rw [hyfun d]
    rfl
  have h2 : ψ d (f x) = f (β d x) := by
    show f (β d (f.symm (f x))) = f (β d x)
    rw [MulEquiv.symm_apply_apply]
  rw [← h2, h1]
  rfl

variable [Module.Finite (ZMod 2) V]

theorem piDataOf_elementaryGroup {p : ℕ} (h4 : 4 ≤ finrank (ZMod 2) V)
    (hPi : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ^ p = 1 →
      4 ≤ finrank (ZMod 2) (fixV (Subgroup.zpowers g)) → PiData p Q (fixV (Subgroup.zpowers g))) :
    PiDataOf p ↥(elementaryGroup Q) := by
  have hfix : fixV (Subgroup.zpowers (1 : V ≃ₗ[ZMod 2] V)) = ⊤ := by
    ext v
    rw [mem_fixSub_zpowers]
    simp
  have h1 := hPi 1 (one_mem _) (one_pow _) (by rw [hfix, finrank_top]; exact h4)
  rw [hfix] at h1
  have h2 : PiDataOf p ↥(orthJ Q (⊤ : Submodule (ZMod 2) V)) := h1
  rw [orthJ_top_eq_elementaryGroup] at h2
  exact h2

theorem top_le_of_plane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ finrank (ZMod 2) V)
    (hAut : ∀ σ : MulAut ↥(elementaryGroup Q), σ ^ p = 1 →
      ∃ y : ↥(elementaryGroup Q), σ = MulAut.conj y)
    (hcenterO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ x ∈ elementaryGroup Q, g * x = x * g) → g = 1)
    (hfix : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      (∀ x ∈ E, x ^ p = 1) → ∃ P : HypPair Q, ∀ g ∈ E, g P.e = P.e ∧ g P.f = P.f)
    (hPi : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ^ p = 1 →
      4 ≤ finrank (ZMod 2) (fixV (Subgroup.zpowers g)) → PiData p Q (fixV (Subgroup.zpowers g)))
    {Kb : Type*} [Group Kb] [Finite Kb] (f : Kb ≃* ↥(elementaryGroup Q))
    {D : Type*} [Group D] [Finite D] (β : D →* MulAut Kb)
    (hDcomm : ∀ a b : D, a * b = b * a) (hDp : ∀ d : D, d ^ p = 1) (hDcard : Nat.card D = p ^ 2)
    (S : Subgroup Kb)
    (hS : ∀ d : D, d ≠ 1 → ∀ A₀ : Subgroup Kb, A₀ ≤ fixedSub (β d) →
        (∀ y ∈ fixedSub (β d), y ∈ Subgroup.normalizer (A₀ : Set Kb)) →
        IsSimpleGroup ↥A₀ → p ∣ Nat.card ↥A₀ → IsPiGroup p ↥A₀ → A₀ ≤ S) :
    (⊤ : Subgroup Kb) ≤ S := by
  classical
  have hcenter := hcenter_of_hcenterO hcenterO
  obtain ⟨Yh, hY⟩ := exists_inner_hom hDp f β hAut hcenter
  let F : Kb →* (V ≃ₗ[ZMod 2] V) := (elementaryGroup Q).subtype.comp f.toMonoidHom
  have hFinj : Function.Injective F := Subtype.val_injective.comp f.injective
  have hFapp : ∀ x : Kb, F x = ((f x : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) := fun x => rfl
  have hFO : ∀ x : Kb, F x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun x =>
    elementaryGroup_le_orthogonalGroup Q (f x).2
  let ρ : D →* (V ≃ₗ[ZMod 2] V) := (elementaryGroup Q).subtype.comp Yh
  have hρO : ∀ d, ρ d ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun d =>
    elementaryGroup_le_orthogonalGroup Q (Yh d).2
  have hρp : ∀ d, ρ d ^ p = 1 := fun d => by rw [← map_pow, hDp d, map_one]
  have hfixIff : ∀ (d : D) (x : Kb), β d x = x ↔ ρ d * F x = F x * ρ d := by
    intro d x
    constructor
    · intro h
      have h1 := hY d x
      rw [h] at h1
      have h2 : Yh d * f x = f x * Yh d := by
        calc Yh d * f x = Yh d * f x * (Yh d)⁻¹ * Yh d := by group
          _ = f x * Yh d := by rw [← h1]
      exact congrArg Subtype.val h2
    · intro h
      apply f.injective
      rw [hY d x]
      have h2 : Yh d * f x = f x * Yh d := Subtype.ext h
      rw [h2]
      group
  by_cases hker : ∃ d : D, d ≠ 1 ∧ Yh d = 1
  ·
    obtain ⟨d, hd1, hYd⟩ := hker
    have hβ : ∀ x : Kb, β d x = x := fun x => by
      apply f.injective
      rw [hY d x, hYd]
      group
    have hFtop : (⊤ : Subgroup Kb) ≤ fixedSub (β d) := fun x _ => hβ x
    obtain ⟨hs, hnc, hdvd, hΩ⟩ :=
      PiDataOf.of_mulEquiv (f.symm.trans Subgroup.topEquiv.symm) (piDataOf_elementaryGroup h4 hPi)
    haveI := hs
    exact hS d hd1 ⊤ hFtop (fun y _ => Subgroup.mem_normalizer_iff.2 fun h => by simp) hs hdvd
      (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.isPiGroup_of_simple_data hp hnc hdvd hΩ)
  ·
    push Not at hker
    have hρinj : Function.Injective ρ := by
      rw [injective_iff_map_eq_one]
      intro d hd
      by_contra hd1
      exact hker d hd1 (Subtype.ext hd)
    set A : Subgroup (V ≃ₗ[ZMod 2] V) := ρ.range with hA
    have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rintro _ ⟨d, rfl⟩
      exact hρO d
    have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, hDcomm a b]
    have hAexp : ∀ x ∈ A, x ^ p = 1 := by
      rintro _ ⟨d, rfl⟩
      exact hρp d
    have hAcard : Nat.card A = p ^ 2 := by
      rw [hA, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hρinj, Subgroup.card_top,
        hDcard]
    obtain ⟨P, hP⟩ := hfix A hAO hAexp
    have hgen := elementaryGroup_le_iSup_orthJ hp hp2 hQ hcenterO A hAO hAcomm hAexp hAcard P
      (fun h hh => (hP h hh).1) (fun h hh => (hP h hh).2)
    have key : ∀ (a : V ≃ₗ[ZMod 2] V), a ∈ A ∧ a ≠ 1 ∧
        4 ≤ finrank (ZMod 2) (fixV (Subgroup.zpowers a)) →
        orthJ Q (fixV (Subgroup.zpowers a)) ≤ S.map F := by
      rintro a ⟨⟨d, rfl⟩, ha1, ha4⟩
      have hd1 : d ≠ 1 := fun h => ha1 (by rw [h, map_one])
      set J := orthJ Q (fixV (Subgroup.zpowers (ρ d))) with hJ
      have hJF : J ≤ F.range := by
        intro z hz
        have hzE : z ∈ elementaryGroup Q := orthJ_le_elementaryGroup Q _ hz
        refine ⟨f.symm ⟨z, hzE⟩, ?_⟩
        rw [hFapp, MulEquiv.apply_symm_apply]
      set A₀ : Subgroup Kb := J.comap F with hA₀
      have hmap : A₀.map F = J := Subgroup.map_comap_eq_self hJF
      let eA : ↥A₀ ≃* ↥J := (A₀.equivMapOfInjective F hFinj).trans (MulEquiv.subgroupCongr hmap)
      obtain ⟨hs, hnc, hdvd, hΩ⟩ := PiDataOf.of_mulEquiv eA.symm (hPi (ρ d) (hρO d) (hρp d) ha4)
      haveI := hs
      have hcommJ : ∀ z ∈ J, ρ d * z = z * ρ d :=
        commute_of_forall_apply_eq_orthJ (hρO d) (fun w hw => mem_fixSub_zpowers.mp hw)
      have hA₀F : A₀ ≤ fixedSub (β d) := by
        intro y hy
        exact (hfixIff d y).2 (hcommJ (F y) hy)
      have hA₀N : ∀ y ∈ fixedSub (β d), y ∈ Subgroup.normalizer (A₀ : Set Kb) := by
        intro y hy
        have hc : ρ d * F y = F y * ρ d := (hfixIff d y).1 hy
        refine Subgroup.mem_normalizer_iff.2 fun x => ?_
        show F x ∈ J ↔ F (y * x * y⁻¹) ∈ J
        rw [map_mul, map_mul, map_inv]
        exact mem_orthJ_conj_iff (hFO y) hc.symm (F x)
      have hle := hS d hd1 A₀ hA₀F hA₀N hs hdvd
        (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.isPiGroup_of_simple_data hp hnc hdvd hΩ)
      rw [← hmap]
      exact Subgroup.map_mono hle
    intro x _
    have hx : F x ∈ ⨆ (a : V ≃ₗ[ZMod 2] V) (_ : a ∈ A ∧ a ≠ 1 ∧
        4 ≤ finrank (ZMod 2) (fixV (Subgroup.zpowers a))),
        orthJ Q (fixV (Subgroup.zpowers a)) := hgen (f x).2
    obtain ⟨y, hy, hyx⟩ := (iSup₂_le key) hx
    rwa [hFinj hyx] at hy

end PlaneGen

section OmegaGen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open AltFacts2 (Ke_le)

theorem card_alternatingGroup_seven : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  have h := CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin 7 (by norm_num)
  have h7 : Nat.factorial 7 = 5040 := by decide
  omega

theorem not_isHatSeven_of_isOmegaTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : Bool} {n : ℕ}
    (hn : 1 ≤ n) (hfp : HasFixedPointFreeOrder ε n p) {Y : Type} [Group Y] [Finite Y]
    (hY : IsOmegaTwo ε (n + 1) (Y ⧸ Subgroup.center Y)) : ¬ IsHatSeven Y := by
  rintro ⟨-, -, ⟨e⟩⟩
  have hc := card_eq_omegaOrd hp hp2 hn hfp hY
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup_seven] at hc
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    cases ε
    · revert hc; decide
    · exact CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2 hfp
  · have h64 := OmegaFacts.sixtyFour_dvd_omegaOrd (ε := ε) (m := n + 1) (by omega)
    rw [← hc] at h64
    revert h64; decide

theorem top_le_of_isOmegaTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hfp : HasFixedPointFreeOrder ε n p) {Kb : Type} [Group Kb] [Finite Kb]
    (hΩ : IsOmegaTwo ε (n + 1) Kb)
    {D : Type*} [Group D] [Finite D] (β : D →* MulAut Kb)
    (hDcomm : ∀ a b : D, a * b = b * a) (hDp : ∀ d : D, d ^ p = 1) (hDcard : Nat.card D = p ^ 2)
    (S : Subgroup Kb)
    (hS : ∀ d : D, d ≠ 1 → ∀ A₀ : Subgroup Kb, A₀ ≤ fixedSub (β d) →
        (∀ y ∈ fixedSub (β d), y ∈ Subgroup.normalizer (A₀ : Set Kb)) →
        IsSimpleGroup ↥A₀ → p ∣ Nat.card ↥A₀ → IsPiGroup p ↥A₀ → A₀ ≤ S) :
    (⊤ : Subgroup Kb) ≤ S := by
  cases ε
  ·
    obtain ⟨φ⟩ := hΩ
    have hm : 2 ≤ n + 1 := by omega
    have hstd : IsStdSpace false (quadMinus (n + 1) (ZMod 2) 1 1) (n + 1) :=
      ⟨LinearEquiv.refl _ _, fun v => rfl⟩
    have hnd : (polarBilin (quadMinus (n + 1) (ZMod 2) 1 1)).Nondegenerate :=
      nondegenerate_polarBilin_quadMinus_of_finite (n + 1) (ZMod 2)
        (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
    have hfr : finrank (ZMod 2) (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2) =
        2 * n + 2 := by
      rw [finrank_fintype_fun_eq_card]
      simp [Fintype.card_sum]
      omega
    refine top_le_of_plane hp hp2 hnd (by rw [hfr]; omega)
      (inner_of_mulEquiv (statedOmegaMinusEquiv hm) (aut_inner_minus autU42Five hp hp2 hn hfp))
      ?_ ?_ ?_ (φ.trans (statedOmegaMinusEquiv hm)) β hDcomm hDp hDcard S hS
    · intro g hg hc
      exact eq_one_of_commute_eichler hnd (by rw [hfr]; omega) fun u w _ _ =>
        hc _ (eichler_mem_elementaryGroup _ u w)
    · intro E hE hexp
      exact exists_fixed_hypPair_of_hasFpf hnd hp hp2 hn hfp hstd hE hexp
    · intro g hg hgp hdim
      exact piData_of_fixedSpace hnd hstd hp hp2 hn hfp hg hgp hdim
  ·
    obtain ⟨φ⟩ := hΩ
    have hn2 : 2 ≤ n := by
      by_contra h
      obtain rfl : n = 1 := by omega
      exact CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2 hfp
    have hm : 3 ≤ n + 1 := by omega
    have hstd : IsStdSpace true (quadPlus (n + 1) (ZMod 2)) (n + 1) :=
      ⟨LinearEquiv.refl _ _, fun v => rfl⟩
    have hnd := nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2)
    refine top_le_of_plane hp hp2 hnd ?_
      (inner_of_mulEquiv (statedOmegaPlusEquiv hm) (aut_inner_plus hp hp2 hn hfp))
      ?_ ?_ ?_ (φ.trans (statedOmegaPlusEquiv hm)) β hDcomm hDp hDcard S hS
    · rw [finrank_fintype_fun_eq_card]
      simp [Fintype.card_sum]
      omega
    · intro g hg hc
      exact eq_one_of_commute_elementaryGroup_of_isPlusSpace hm hstd hg hc
    · intro E hE hexp
      exact exists_fixed_hypPair_of_hasFpf hnd hp hp2 hn hfp hstd hE hexp
    · intro g hg hgp hdim
      exact piData_of_fixedSpace hnd hstd hp hp2 hn hfp hg hgp hdim

theorem inputOmegaGen_of_piCenter (hPC : InputPiCenter) : Prop1116.InputOmegaGen := by
  intro G _ _ p hp hp2 X K B hK _ hBn hBel hBrk hΩ'
  obtain ⟨ε, n, hn, hΩ, hfp⟩ := hΩ'
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := ⨆ (e : G) (_ : e ∈ B) (_ : e ≠ 1), Prop1116.Ke p K e with hH
  have hHK : H ≤ K := iSup_le fun e => iSup_le fun _ => iSup_le fun _ => Ke_le p K e
  have hKe_le : ∀ e ∈ B, e ≠ 1 → Prop1116.Ke p K e ≤ H := fun e he he1 =>
    le_iSup_of_le e (le_iSup_of_le he (le_iSup_of_le he1 le_rfl))
  suffices htop : barX p K H = ⊤ by
    have hcov := (barX_eq_top_iff p hHK).1 htop
    exact ((barX_eq_iff_cov hp hK.2.1 hHK).2 hcov).ge
  have hq : CFSG.Open.IsQuasisimple (barOf p K) :=
    (isQuasisimple_barX_iff hp hK.2.1).1 hK.2.2.1.2.2
  have hO : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hPiK : IsPiGroup p (barOf p K) := ⟨hq, hO, Or.inr (Or.inl ⟨n, ε, hn, hΩ, hfp⟩)⟩
  have hZ : Subgroup.center (barOf p K) = ⊥ :=
    hPC _ p hp hp2 hPiK (not_isHatSeven_of_isOmegaTwo hp hp2 hn hfp hΩ)
  let f₀ : barOf p K ≃* (barOf p K ⧸ Subgroup.center (barOf p K)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hΩK : IsOmegaTwo ε (n + 1) (barOf p K) := by
    cases ε
    · obtain ⟨φ⟩ := hΩ
      exact ⟨f₀.trans φ⟩
    · obtain ⟨φ⟩ := hΩ
      exact ⟨f₀.trans φ⟩
  obtain ⟨D, hDB, hDel, hDcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hBrk
  let β : ↥D →* MulAut (barOf p K) := (barAut p K).comp (Subgroup.inclusion (hDB.trans hBn))
  have hDcomm : ∀ a b : ↥D, a * b = b * a := fun a b => hDel.1.is_comm.comm a b
  have hDp : ∀ d : ↥D, d ^ p = 1 := fun d => Subtype.ext (by simpa using hDel.2 d d.2)
  refine eq_top_iff.2 (top_le_of_isOmegaTwo hp hp2 hn hfp hΩK β hDcomm hDp hDcard _ ?_)
  intro d hd1 A₀ hA₀F hA₀N hs hdvd hpi
  have hdB : (d : G) ∈ B := hDB d.2
  have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
  exact (lift_simple hp (hBn hdB) (hBel.2 _ hdB) hA₀F hA₀N hs hdvd hpi).trans
    (barX_mono_of_le p (hKe_le _ hdB hd1'))

theorem inputOmegaGen_holds :
    Prop1116.InputOmegaGen :=
  inputOmegaGen_of_piCenter SchurFacts.inputPiCenter_holds

end OmegaGen

section Chev2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

theorem piDataOf_of_isOmegaTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hfp : HasFixedPointFreeOrder ε n p) {Y : Type*} [Group Y] (hY : IsOmegaTwo ε (n + 1) Y) :
    PiDataOf p Y := by
  cases ε
  · obtain ⟨φ⟩ := hY
    have hm : 2 ≤ n + 1 := by omega
    have hstd : IsStdSpace false (quadMinus (n + 1) (ZMod 2) 1 1) (n + 1) :=
      ⟨LinearEquiv.refl _ _, fun v => rfl⟩
    have hnd : (polarBilin (quadMinus (n + 1) (ZMod 2) 1 1)).Nondegenerate :=
      nondegenerate_polarBilin_quadMinus_of_finite (n + 1) (ZMod 2)
        (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
    have hfr : finrank (ZMod 2) (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2) =
        2 * n + 2 := by
      rw [finrank_fintype_fun_eq_card]
      simp [Fintype.card_sum]
      omega
    exact (piDataOf_elementaryGroup (by rw [hfr]; omega)
      (fun g hg hgp hdim => piData_of_fixedSpace hnd hstd hp hp2 hn hfp hg hgp hdim)).of_mulEquiv
      (φ.trans (statedOmegaMinusEquiv hm)).symm
  · obtain ⟨φ⟩ := hY
    have hn2 : 2 ≤ n := by
      by_contra h
      obtain rfl : n = 1 := by omega
      exact CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2 hfp
    have hm : 3 ≤ n + 1 := by omega
    have hstd : IsStdSpace true (quadPlus (n + 1) (ZMod 2)) (n + 1) :=
      ⟨LinearEquiv.refl _ _, fun v => rfl⟩
    have hnd := nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2)
    have h4 : 4 ≤ finrank (ZMod 2) (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) := by
      rw [finrank_fintype_fun_eq_card]
      simp [Fintype.card_sum]
      omega
    exact (piDataOf_elementaryGroup h4
      (fun g hg hgp hdim => piData_of_fixedSpace hnd hstd hp hp2 hn hfp hg hgp hdim)).of_mulEquiv
      (φ.trans (statedOmegaPlusEquiv hm)).symm

theorem two_le_pRank_inf_centralizer {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {J B : Subgroup X} {L : Type*} [Group L] (e : ↥J ≃* L)
    (hAut : ∀ σ : MulAut L, σ ^ p = 1 → ∃ y : L, σ = MulAut.conj y)
    (hcenter : ∀ z : L, (∀ x : L, z * x = x * z) → z = 1)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (J : Set X))
    (hJp : ¬ p ^ 3 ∣ Nat.card ↥J) (hB4 : 4 ≤ CFSG.Open.pRank p B) :
    2 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (J : Set X)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite L := Finite.of_equiv ↥J e.toEquiv
  let β : ↥B →* MulAut ↥J := J.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hDp : ∀ b : ↥B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hB.2 b b.2)
  obtain ⟨Yh, hY⟩ := exists_inner_hom hDp e β hAut hcenter
  have hker : ∀ b : ↥B, Yh b = 1 → (b : X) ∈ Subgroup.centralizer (J : Set X) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : β b ⟨x, hx⟩ = ⟨x, hx⟩ := by
      apply e.injective
      rw [hY, hb]
      group
    have h2 : (b : X) * x * (b : X)⁻¹ = x := congrArg Subtype.val h1
    calc x * (b : X) = (b : X) * x * (b : X)⁻¹ * (b : X) := by rw [h2]
      _ = (b : X) * x := by group
  have hBp : IsPGroup p ↥B := CFSG.Open.IsElemAbelian.isPGroup hB
  obtain ⟨r, hr⟩ := (hBp.of_surjective Yh.rangeRestrict Yh.rangeRestrict_surjective).exists_card_eq
  have hrJ : p ^ r ∣ Nat.card ↥J := by
    rw [← hr, Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hr2 : r ≤ 2 := by
    by_contra h
    exact hJp ((pow_dvd_pow p (by omega)).trans hrJ)
  set m := CFSG.Open.pRank p B with hm
  have hBc : Nat.card ↥B = p ^ m := Claims138.card_eq_pow_pRank hp hB
  have hkr := Subgroup.card_ker_mul_card_range Yh
  rw [hBc, hr] at hkr
  have hkc : Nat.card ↥Yh.ker = p ^ (m - r) := by
    have hpr : 0 < p ^ r := pow_pos hp.pos r
    refine Nat.eq_of_mul_eq_mul_right hpr ?_
    rw [hkr, ← pow_add, Nat.sub_add_cancel (by omega)]
  let f : ↥Yh.ker →* X := B.subtype.comp Yh.ker.subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have hfr : f.range ≤ B ⊓ Subgroup.centralizer (J : Set X) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨(k : ↥B).2, hker k k.2⟩
  have hcomm : ∀ a b : ↥Yh.ker, a * b = b * a := fun a b =>
    Subtype.ext (hB.1.is_comm.comm (a : ↥B) (b : ↥B))
  have hpow : ∀ a : ↥Yh.ker, a ^ p = 1 := fun a => Subtype.ext (hDp a)
  have := CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow hkc f hf hfr
  omega

theorem not_pow_three_dvd_of_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : Bool} {n : ℕ}
    (hn : 1 ≤ n) (hn2 : n ≤ 2) (hfp : HasFixedPointFreeOrder ε n p) {Y : Type} [Group Y] [Finite Y]
    (hY : IsOmegaTwo ε (n + 1) Y) : ¬ p ^ 3 ∣ Nat.card Y := by
  have hdvd := dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 hn hfp
  rw [card_eq_omegaOrd hp hp2 hn hfp hY]
  interval_cases n
  · cases ε
    · have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa [typeSign] using hdvd)
      subst h3
      decide
    · exact absurd hfp
        (CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2)
  · cases ε
    · have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa [typeSign] using hdvd)
      subst h5
      rw [OmegaFacts.omegaOrd_three_minus]
      decide
    · have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa [typeSign] using hdvd)
      subst h3
      rw [OmegaFacts.omegaOrd_three_plus]
      decide

theorem not_mulEquiv_alt_of_three_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : Bool} {n : ℕ}
    (hn3 : 3 ≤ n) (hfp : HasFixedPointFreeOrder ε n p) {Y : Type} [Group Y] [Finite Y]
    (hY : IsOmegaTwo ε (n + 1) Y) (N : ℕ) : ¬ Nonempty (Y ≃* alternatingGroup (Fin N)) := by
  rintro ⟨f⟩
  have hc := Nat.card_congr f.toEquiv
  rw [card_eq_omegaOrd hp hp2 (by omega) hfp hY] at hc
  rcases Nat.lt_or_ge N 5 with h5 | h5
  · have hle : Nat.card (alternatingGroup (Fin N)) ≤ 24 := by
      have h1 := Subgroup.card_le_card_group (alternatingGroup (Fin N))
      rw [Nat.card_perm, Nat.card_fin] at h1
      have h2 : N.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le (by omega)
      have h3 : (4 : ℕ).factorial = 24 := by decide
      omega
    have h64 := OmegaFacts.sixtyFour_dvd_omegaOrd (ε := ε) (m := n + 1) (by omega)
    have hpos := OmegaFacts.omegaOrd_pos (ε := ε) (m := n + 1) (by omega)
    have := Nat.le_of_dvd hpos h64
    omega
  · have h2 := CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin N h5
    refine CFSG.HardMathSupport.Curtis.Coordinator.PLType.factorial_ne_two_mul_orth (m := n + 1)
      (by omega) h5 (A := if ε then 2 ^ (n + 1) - 1 else 2 ^ (n + 1) + 1) (by cases ε <;> simp) ?_
    rw [← h2, ← hc]
    unfold OmegaFacts.omegaOrd
    simp only [Nat.add_sub_cancel]

theorem eq_gamma_of_isOmegaTwo {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J B : Subgroup X} {ε : Bool} {n : ℕ} (hn : 1 ≤ n) (hΩ : IsOmegaTwo ε (n + 1) ↥J)
    (hfp : HasFixedPointFreeOrder ε n p) (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (J : Set X)) (hB4 : 4 ≤ CFSG.Open.pRank p B) :
    J = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      J ⊓ Subgroup.normalizer (U : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hsJ, hncJ, -, -⟩ := piDataOf_of_isOmegaTwo hp hp2 hn hfp hΩ
  haveI := hsJ
  have hZJ : Subgroup.center ↥J = ⊥ := center_eq_bot_of_simple_nonabelian hncJ
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  ·
    refine Claims138.eq_gamma_of_two_le_pRank ?_
    have hJp := not_pow_three_dvd_of_le_two hp hp2 hn (by omega) hfp hΩ
    have hcen : ∀ z : ↥J, (∀ x : ↥J, z * x = x * z) → z = 1 := fun z hz => by
      have hz' : z ∈ Subgroup.center ↥J := Subgroup.mem_center_iff.2 fun g => (hz g).symm
      rw [hZJ] at hz'
      exact Subgroup.mem_bot.1 hz'
    cases ε
    · obtain ⟨φ⟩ := hΩ
      exact two_le_pRank_inf_centralizer hp (MulEquiv.refl ↥J)
        (inner_of_mulEquiv φ.symm (aut_inner_minus autU42Five hp hp2 hn hfp)) hcen hB hBN hJp hB4
    · obtain ⟨φ⟩ := hΩ
      exact two_le_pRank_inf_centralizer hp (MulEquiv.refl ↥J)
        (inner_of_mulEquiv φ.symm (aut_inner_plus hp hp2 hn hfp)) hcen hB hBN hJp hB4
  ·
    refine le_antisymm ?_ (iSup_le fun U => iSup_le fun _ => iSup_le fun _ => inf_le_left)
    have hOCG : CFSG.HardMathSupport.Timmesfeld.Coordinator.OrthCentGen :=
      orthCentGen_of_autU42Five autU42Five
    set N : Subgroup X := Subgroup.normalizer (J : Set X) with hN
    have hJN : J ≤ N := Subgroup.le_normalizer
    set K : Subgroup ↥N := J.subgroupOf N with hK
    set A : Subgroup ↥N := B.subgroupOf N with hA
    let eK : ↥K ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJN
    obtain ⟨hs, hnc, hdvd, hΩK⟩ := (piDataOf_of_isOmegaTwo hp hp2 hn hfp hΩ).of_mulEquiv eK.symm
    haveI := hs
    have hPiK : IsPiGroup p ↥K := isPiGroup_of_simple_data hp hnc hdvd hΩK
    have hZK : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_nonabelian hnc
    let eZ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
    haveI hKn : K.Normal := Subgroup.normal_in_normalizer
    have hcomp : IsComponentOf K ⊤ := by
      refine ⟨le_top, ?_, hPiK.1⟩
      exact IsSubnormal.step le_top (Subgroup.Normal.subgroupOf inferInstance _) (IsSubnormal.refl _)
    have hOrth : CFSG.LocalAnalysis.GLTheoremB.IsOrthType p ↥K := by
      obtain ⟨n', ε', h1, h2, h3⟩ := hΩK
      refine ⟨n', ε', h1, ?_, h3⟩
      cases ε'
      · obtain ⟨ψ⟩ := h2
        exact ⟨eZ.trans ψ⟩
      · obtain ⟨ψ⟩ := h2
        exact ⟨eZ.trans ψ⟩
    have hΩKZ : IsOmegaTwo ε (n + 1) (↥K ⧸ Subgroup.center ↥K) := by
      cases ε
      · obtain ⟨φ⟩ := hΩ
        exact ⟨(eZ.trans eK).trans φ⟩
      · obtain ⟨φ⟩ := hΩ
        exact ⟨(eZ.trans eK).trans φ⟩
    have hnA : ¬ CFSG.LocalAnalysis.GLTheoremB.IsAltType p ↥K := by
      rintro (⟨k, hk⟩ | ⟨-, hk⟩)
      · exact not_mulEquiv_alt_of_three_le hp hp2 hn3 hfp hΩKZ _ hk
      · exact not_mulEquiv_alt_of_three_le hp hp2 hn3 hfp hΩKZ _ hk
    have hAel : IsElemAbelian p A := CFSG.Open.IsElemAbelian.subgroupOf hB N
    have hAK : A ≤ Subgroup.normalizer (K : Set ↥N) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hKn]
      exact le_top
    have hgen := hOCG (↥N) p hp hp2 K hcomp hPiK hOrth hnA A hAel hAK
    have hBc : Nat.card ↥B = p ^ CFSG.Open.pRank p B := Claims138.card_eq_pow_pRank hp hB
    have hAc : Nat.card ↥A = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
    have hmap : (GL83.CompFam.centGenI p A K).map N.subtype ≤
        ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
          J ⊓ Subgroup.normalizer (U : Set X) := by
      unfold GL83.CompFam.centGenI
      rw [Subgroup.map_iSup]
      refine iSup_le fun E => ?_
      set U : Subgroup X := E.1.map N.subtype with hU
      have hUB : U ≤ B := by
        rintro _ ⟨y, hy, rfl⟩
        exact Subgroup.mem_subgroupOf.1 (E.2.1 hy)
      have hUc : Nat.card ↥U = Nat.card ↥E.1 := Subgroup.card_map_of_injective N.subtype_injective
      have hUel : IsElemAbelian p U := CFSG.Open.IsElemAbelian.mono hB hUB
      have hU2 : 2 ≤ CFSG.Open.pRank p U := by
        have h1 := Claims138.card_eq_pow_pRank hp hUel
        have h2 : p ^ CFSG.Open.pRank p B ≤ p * p ^ CFSG.Open.pRank p U := by
          rw [← hBc, ← hAc, ← h1, hUc]
          exact E.2.2
        rw [← pow_succ'] at h2
        have h3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
        omega
      refine le_iSup_of_le U (le_iSup_of_le hUB (le_iSup_of_le hU2 ?_))
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyK, hyC⟩ := Subgroup.mem_inf.1 hy
      refine ⟨Subgroup.mem_subgroupOf.1 hyK, ?_⟩
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨z, hz, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 hyC z hz
      exact congrArg Subtype.val this
    intro x hx
    have hxK : (⟨x, hJN hx⟩ : ↥N) ∈ K := Subgroup.mem_subgroupOf.2 hx
    exact hmap ⟨⟨x, hJN hx⟩, hgen hxK, rfl⟩

theorem nonempty_commutator_statedSp_two_mulEquiv_alt :
    Nonempty (↥(⁅(StatedSp 2 (ZMod 2)), (StatedSp 2 (ZMod 2))⁆ :
      Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 2))) ≃* ↥(alternatingGroup (Fin 6))) := by
  obtain ⟨ψ⟩ := OmegaFacts.nonempty_statedSp_two_mulEquiv_perm_six
  set H : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := StatedSp 2 (ZMod 2) with hH
  have h1 : (commutator ↥H).map H.subtype = ⁅H, H⁆ := Subgroup.map_subtype_commutator H
  have h2 : (commutator ↥H).map ψ.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ ψ.surjective, ← commutator_def,
      alternatingGroup.commutator_perm_eq (by simp)]
  exact ⟨(MulEquiv.subgroupCongr h1.symm).trans
    ((Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).symm.trans
      ((Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
        (MulEquiv.subgroupCongr h2)))⟩

theorem not_pow_three_dvd_card_alt_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 3 ∣ Nat.card ↥(alternatingGroup (Fin 6)) := by
  have h := CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin 6 (by norm_num)
  have h6 : Nat.factorial 6 = 720 := by decide
  have hc : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by omega
  rw [hc]
  intro hd
  have hle : p ^ 3 ≤ 360 := Nat.le_of_dvd (by norm_num) hd
  have hp7 : p ≤ 7 := by
    by_contra h8
    have : 8 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases p <;> first | exact hp2 rfl | (revert hd; decide) | (revert hp; decide)

theorem eq_gamma_of_sp_two {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J B : Subgroup X}
    (e : ↥J ≃* ↥(⁅(StatedSp 2 (ZMod 2)), (StatedSp 2 (ZMod 2))⁆ :
      Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod 2))))
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (J : Set X))
    (hB4 : 4 ≤ CFSG.Open.pRank p B) :
    J = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      J ⊓ Subgroup.normalizer (U : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨f⟩ := nonempty_commutator_statedSp_two_mulEquiv_alt
  let e' : ↥J ≃* ↥(alternatingGroup (Fin 6)) := e.trans f
  have hAut : ∀ σ : MulAut ↥(alternatingGroup (Fin 6)), σ ^ p = 1 →
      ∃ y : ↥(alternatingGroup (Fin 6)), σ = MulAut.conj y := by
    intro σ hσ
    have hodd : Odd (orderOf σ) := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hσ) with h | h
      · rw [h]; exact odd_one
      · rw [h]; exact hp.odd_of_ne_two hp2
    obtain ⟨y, hy⟩ := CFSG.ASVolI.burnsideA26_a6 (MulEquiv.refl _) σ hodd
    exact ⟨y, hy.symm⟩
  have hcen : ∀ z : ↥(alternatingGroup (Fin 6)), (∀ x, z * x = x * z) → z = 1 := by
    intro z hz
    have hz' : z ∈ Subgroup.center ↥(alternatingGroup (Fin 6)) :=
      Subgroup.mem_center_iff.2 fun g => (hz g).symm
    rw [alternatingGroup.center_eq_bot (by simp)] at hz'
    exact Subgroup.mem_bot.1 hz'
  have hJp : ¬ p ^ 3 ∣ Nat.card ↥J := by
    rw [Nat.card_congr e'.toEquiv]
    exact not_pow_three_dvd_card_alt_six hp hp2
  exact Claims138.eq_gamma_of_two_le_pRank
    (two_le_pRank_inf_centralizer hp e' hAut hcen hB hBN hJp hB4)

@[expose] def InputI2319Sp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (J B : Subgroup X),
    (∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥J ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ :
        Subgroup (GL (Fin n ⊕ Fin n) (ZMod 2))))) →
    IsElemAbelian p B → B ≤ Subgroup.normalizer (J : Set X) →
    (∀ A : Subgroup X, A ≤ B ⊔ J → IsElemAbelian p A → Nat.card A ≤ Nat.card B) →
    4 ≤ CFSG.Open.pRank p B →
    J = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      J ⊓ Subgroup.normalizer (U : Set X)

theorem inputI2319Chev2_of_sp (hSp : InputI2319Sp) : Claims138.InputI2319Chev2 := by
  intro X _ _ p hp hp2 J B hJt hB hBN hcard hB4
  rcases hJt with ⟨n, hn, ⟨e⟩⟩ | ⟨ε, n, hn, hΩ, hfp⟩
  · rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      exact eq_gamma_of_sp_two hp hp2 e hB hBN hB4
    · exact hSp X p hp hp2 J B ⟨n, h3, ⟨e⟩⟩ hB hBN hcard hB4
  · exact eq_gamma_of_isOmegaTwo hp hp2 hn hΩ hfp hB hBN hB4

end Chev2

section MaxEA

theorem conj_of_not_dvd_index {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {E₁ E₂ : Subgroup X} (h₁ : IsPGroup p E₁) (h₂ : IsPGroup p E₂) (i₁ : ¬ p ∣ E₁.index)
    (i₂ : ¬ p ∣ E₂.index) : ∃ x : X, E₂ = E₁.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X (h₁.toSylow i₁) (h₂.toSylow i₂)
  refine ⟨x, ?_⟩
  have := congrArg (fun S : Sylow p X => (S : Subgroup X)) hx
  simp only [IsPGroup.toSylow_coe] at this
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, IsPGroup.toSylow_coe] at this
  exact this.symm

theorem not_dvd_index_of_card_le {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {E₀ E : Subgroup X} (hE₀ : IsElemAbelian p E₀) (hi : ¬ p ∣ E₀.index) (hE : IsElemAbelian p E)
    (hm : Nat.card ↥E₀ ≤ Nat.card ↥E) : ¬ p ∣ E.index := by
  have hE₀p : IsPGroup p E₀ := CFSG.Open.IsElemAbelian.isPGroup hE₀
  have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have hPc : Nat.card (P : Subgroup X) = Nat.card ↥E₀ := by
    have h1 := P.card_eq_multiplicity
    have h2 := (hE₀p.toSylow hi).card_eq_multiplicity
    rw [IsPGroup.toSylow_coe] at h2
    rw [h1, h2]
  have hEq : E = P := Subgroup.eq_of_le_of_card_ge hEP (by rw [hPc]; exact hm)
  rw [hEq]
  exact P.not_dvd_index

theorem isElemAbelian_zpowers {X : Type*} [Group X] {p : ℕ} {g : X} (hg : g ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers g) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    show (a : X) * b = b * a
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self g i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

theorem exists_sylow_ea_of_sq_not_dvd {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    (hd : p ∣ Nat.card X) (hd2 : ¬ p ^ 2 ∣ Nat.card X) :
    ∃ E₀ : Subgroup X, IsElemAbelian p E₀ ∧ ¬ p ∣ E₀.index := by
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  refine ⟨Subgroup.zpowers g, isElemAbelian_zpowers (hg ▸ pow_orderOf_eq_one g), fun hi => hd2 ?_⟩
  have h1 := (Subgroup.zpowers g).card_mul_index
  rw [Nat.card_zpowers, hg] at h1
  rw [← h1, pow_two]
  exact Nat.mul_dvd_mul_left p hi

theorem conj_maxEA_of_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hn2 : n ≤ 2) (hfp : HasFixedPointFreeOrder ε n p) {X : Type} [Group X] [Finite X]
    (hX : IsOmegaTwo ε (n + 1) X) (E₁ E₂ : Subgroup X) (hE₁ : IsElemAbelian p E₁)
    (hE₂ : IsElemAbelian p E₂)
    (hm₁ : ∀ F : Subgroup X, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₁)
    (hm₂ : ∀ F : Subgroup X, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₂) :
    ∃ x : X, E₂ = E₁.map (MulAut.conj x).toMonoidHom := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.dvd_typeSign_of_hasFixedPointFreeOrder
    hp hp2 hn hfp
  have hc := card_eq_omegaOrd hp hp2 hn hfp hX
  obtain ⟨E₀, hE₀, hi₀⟩ : ∃ E₀ : Subgroup X, IsElemAbelian p E₀ ∧ ¬ p ∣ E₀.index := by
    interval_cases n
    · cases ε
      · have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (by simpa [CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.typeSign] using hdvd)
        subst h3
        have h60 : Nat.card X = 60 := by rw [hc]; decide
        exact exists_sylow_ea_of_sq_not_dvd (by rw [h60]; norm_num) (by rw [h60]; norm_num)
      · exact absurd hfp
          (CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2)
    · cases ε
      · have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1
          (by simpa [CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.typeSign] using hdvd)
        subst h5
        have hcard : Nat.card X = 25920 := by rw [hc, OmegaFacts.omegaOrd_three_minus]
        exact exists_sylow_ea_of_sq_not_dvd (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
      · have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (by simpa [CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.typeSign] using hdvd)
        subst h3
        have hcard : Nat.card X = 20160 := by rw [hc, OmegaFacts.omegaOrd_three_plus]
        have hrk := OmegaFacts.two_le_pRank_three_of_isOmegaTwo (ε := true) (n := 2) le_rfl hX
        obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank Nat.prime_three.one_lt
          (⊤ : Subgroup X)
        refine ⟨E, hE, fun hi => ?_⟩
        have h1 := E.card_mul_index
        rw [hEc, hcard] at h1
        have h9 : 9 ∣ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
          (show (9 : ℕ) = 3 ^ 2 by norm_num) ▸ pow_dvd_pow 3 hrk
        obtain ⟨a, ha⟩ := h9
        obtain ⟨b, hb⟩ := hi
        rw [ha, hb] at h1
        have h27 : (27 : ℕ) ∣ 20160 := ⟨a * b, by rw [← h1]; ring⟩
        exact absurd h27 (by norm_num)
  have hi₁ := not_dvd_index_of_card_le hE₀ hi₀ hE₁ (hm₁ E₀ hE₀)
  have hi₂ := not_dvd_index_of_card_le hE₀ hi₀ hE₂ (hm₂ E₀ hE₀)
  exact conj_of_not_dvd_index (CFSG.Open.IsElemAbelian.isPGroup hE₁)
    (CFSG.Open.IsElemAbelian.isPGroup hE₂) hi₁ hi₂

end MaxEA

section MaxEAIsom

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

@[expose] def InputIsomMaxEAConj : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (ε : Bool) (n : ℕ), 3 ≤ n → HasFixedPointFreeOrder ε n p →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
      (Q : QuadraticForm (ZMod 2) V), IsStdSpace ε Q (n + 1) →
    ∀ E₁ E₂ : Subgroup (V ≃ₗ[ZMod 2] V),
      E₁ ≤ TauCeti.QuadraticMap.orthogonalGroup Q → E₂ ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian p E₁ → IsElemAbelian p E₂ →
      (∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
        IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₁) →
      (∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
        IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₂) →
      ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, E₂ = E₁.map (MulAut.conj g).toMonoidHom

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem reflect_not_mem_commutator (hnd : (polarBilin Q).Nondegenerate) {w : V} (hw : Q w = 1) :
    reflect Q w ∉
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  intro hmem
  have hle := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup (Q := Q) hnd
  have h2 : reflect Q w ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      Even (Module.finrank (ZMod 2)
        (CFSG.RankThree.OrthogonalInvolutions.commSpace (reflect Q w))) := hle hmem
  have h3 := CFSG.RankThree.Literature.FSmith.finrank_commSpace_reflect hnd hw
  rw [h3] at h2
  exact (by decide : ¬ Even 1) h2.2

theorem commute_reflect {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {w : V} (hw : Q w = 1) (hgw : g w = w) : g * reflect Q w = reflect Q w * g := by
  ext x
  simp only [LinearEquiv.mul_apply]
  rw [reflect_apply_of_map_eq_one hw, reflect_apply_of_map_eq_one hw, map_add, map_smul, hgw]
  have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg x w
  rw [hgw] at this
  rw [this]

theorem isElemAbelian_comap {G H : Type*} [Group G] [Group H] {p : ℕ} {F : G →* H}
    (hF : Function.Injective F) {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap F) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hF ?_)⟩⟩, fun y hy => hF ?_⟩
  · have := hE.1.is_comm.comm (⟨F a, a.2⟩ : ↥E) ⟨F b, b.2⟩
    have h := congrArg Subtype.val this
    simpa [map_mul] using h
  · rw [map_pow, hE.2 _ hy, map_one]

theorem conj_maxEA_of_isom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hfp : HasFixedPointFreeOrder ε n p) (hnd : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) (hstd : IsStdSpace ε Q (n + 1))
    (hEQ : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ E₁ E₂ : Subgroup (V ≃ₗ[ZMod 2] V),
      E₁ ≤ TauCeti.QuadraticMap.orthogonalGroup Q → E₂ ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian p E₁ → IsElemAbelian p E₂ →
      (∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
        IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₁) →
      (∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
        IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₂) →
      ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, E₂ = E₁.map (MulAut.conj g).toMonoidHom)
    {X : Type} [Group X] [Finite X] (f : X ≃* ↥(elementaryGroup Q)) (E₁ E₂ : Subgroup X)
    (hE₁ : IsElemAbelian p E₁) (hE₂ : IsElemAbelian p E₂)
    (hm₁ : ∀ F : Subgroup X, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₁)
    (hm₂ : ∀ F : Subgroup X, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₂) :
    ∃ x : X, E₂ = E₁.map (MulAut.conj x).toMonoidHom := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  set O : Subgroup (V ≃ₗ[ZMod 2] V) := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  let F : X →* (V ≃ₗ[ZMod 2] V) := (elementaryGroup Q).subtype.comp f.toMonoidHom
  have hFinj : Function.Injective F := Subtype.val_injective.comp f.injective
  have hFr : ∀ z ∈ elementaryGroup Q, ∃ x : X, F x = z := fun z hz =>
    ⟨f.symm ⟨z, hz⟩, by simp [F]⟩
  have hFE : ∀ x : X, F x ∈ elementaryGroup Q := fun x => (f x).2
  have hEO : elementaryGroup Q ≤ O := elementaryGroup_le_orthogonalGroup Q
  set H : Subgroup ↥O := (elementaryGroup Q).subgroupOf O with hH
  have hHidx : H.index = 2 := by
    have h1 := CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup Q hnd
    rw [← CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hnd h6, hEQ]
      at h1
    exact h1
  have hmemH : ∀ (g : V ≃ₗ[ZMod 2] V) (hg : g ∈ O), (⟨g, hg⟩ : ↥O) ∈ H ↔ g ∈ elementaryGroup Q :=
    fun g hg => Subgroup.mem_subgroupOf
  have hodd : ∀ g ∈ O, g ^ p = 1 → g ∈ elementaryGroup Q := by
    intro g hg hgp
    obtain ⟨k, hk⟩ : Odd p := hp.odd_of_ne_two hp2
    set a : ↥O := ⟨g, hg⟩ with ha
    have hap : a ^ p = 1 := Subtype.ext (by simpa [ha] using hgp)
    have h2 : a ^ 2 ∈ H := Subgroup.sq_mem_of_index_two hHidx a
    have h3 : (a ^ 2) ^ (k + 1) = a := by
      rw [← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, hap, one_mul]
    have h4 : a ∈ H := h3 ▸ pow_mem h2 (k + 1)
    exact (hmemH g hg).1 h4
  set E₁' : Subgroup (V ≃ₗ[ZMod 2] V) := E₁.map F with hE₁'
  set E₂' : Subgroup (V ≃ₗ[ZMod 2] V) := E₂.map F with hE₂'
  have hE₁'O : E₁' ≤ O := by rintro _ ⟨x, -, rfl⟩; exact hEO (hFE x)
  have hE₂'O : E₂' ≤ O := by rintro _ ⟨x, -, rfl⟩; exact hEO (hFE x)
  have hE₁'el : IsElemAbelian p E₁' := CFSG.SectionRank.isElemAbelian_map hE₁ F
  have hE₂'el : IsElemAbelian p E₂' := CFSG.SectionRank.isElemAbelian_map hE₂ F
  have hmax : ∀ (E : Subgroup X), (∀ F' : Subgroup X, IsElemAbelian p F' → Nat.card ↥F' ≤ Nat.card ↥E) →
      ∀ F' : Subgroup (V ≃ₗ[ZMod 2] V), F' ≤ O → IsElemAbelian p F' →
        Nat.card ↥F' ≤ Nat.card ↥(E.map F) := by
    intro E hE F' hF'O hF'
    have hF'E : F' ≤ F.range := by
      intro z hz
      obtain ⟨x, hx⟩ := hFr z (hodd z (hF'O hz) (hF'.2 z hz))
      exact ⟨x, hx⟩
    have h1 : (F'.comap F).map F = F' := Subgroup.map_comap_eq_self hF'E
    have h2 := hE (F'.comap F) (isElemAbelian_comap hFinj hF')
    rw [Subgroup.card_map_of_injective hFinj, ← h1, Subgroup.card_map_of_injective hFinj]
    exact h2
  obtain ⟨g, hgO, hg⟩ := hconj E₁' E₂' hE₁'O hE₂'O hE₁'el hE₂'el (hmax E₁ hm₁) (hmax E₂ hm₂)
  obtain ⟨P, hP⟩ := exists_fixed_hypPair_of_hasFpf hnd hp hp2 hn hfp hstd hE₁'O
    (fun x hx => hE₁'el.2 x hx)
  set w : V := P.e + P.f with hw
  have hQw : Q w = 1 := by
    rw [hw, QuadraticMap.map_add Q P.e P.f, P.Q_e, P.Q_f, P.polar_ef]
    simp
  have hrO : reflect Q w ∈ O := reflect_mem_orthogonalGroup Q w
  have hrE : reflect Q w ∉ elementaryGroup Q := hEQ ▸ reflect_not_mem_commutator hnd hQw
  have hrc : E₁'.map (MulAut.conj (reflect Q w)).toMonoidHom = E₁' := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyw : y w = w := by
        rw [hw, map_add, (hP y hy).1, (hP y hy).2]
      have hc := commute_reflect (hE₁'O hy) hQw hyw
      have : (MulAut.conj (reflect Q w)).toMonoidHom y = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← hc]
        group
      rw [this]
      exact hy
    · intro hz
      have hzw : z w = w := by
        rw [hw, map_add, (hP z hz).1, (hP z hz).2]
      have hc := commute_reflect (hE₁'O hz) hQw hzw
      refine ⟨z, hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hc]
      group
  obtain ⟨g', hg'E, hg'⟩ : ∃ g' ∈ elementaryGroup Q,
      E₂' = E₁'.map (MulAut.conj g').toMonoidHom := by
    by_cases hgE : g ∈ elementaryGroup Q
    · exact ⟨g, hgE, hg⟩
    · refine ⟨g * reflect Q w, ?_, ?_⟩
      · have h1 := (Subgroup.mul_mem_iff_of_index_two hHidx (a := ⟨g, hgO⟩) (b := ⟨reflect Q w, hrO⟩))
        have h2 : (⟨g, hgO⟩ : ↥O) * ⟨reflect Q w, hrO⟩ ∈ H :=
          h1.2 ⟨fun h => absurd ((hmemH g hgO).1 h) hgE,
            fun h => absurd ((hmemH _ hrO).1 h) hrE⟩
        exact (hmemH _ (mul_mem hgO hrO)).1 h2
      · have hcomp : (MulAut.conj (g * reflect Q w)).toMonoidHom =
            (MulAut.conj g).toMonoidHom.comp (MulAut.conj (reflect Q w)).toMonoidHom :=
          MonoidHom.ext fun y => by simp [MulAut.conj_apply, mul_assoc]
        rw [hg, hcomp, ← Subgroup.map_map, hrc]
  obtain ⟨x, hx⟩ := hFr g' hg'E
  refine ⟨x, Subgroup.map_injective hFinj ?_⟩
  have hcomp : F.comp (MulAut.conj x).toMonoidHom = (MulAut.conj g').toMonoidHom.comp F := by
    refine MonoidHom.ext fun y => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
      hx]
  show E₂' = (E₁.map (MulAut.conj x).toMonoidHom).map F
  rw [hg', hE₁', Subgroup.map_map, Subgroup.map_map, hcomp]

theorem input10_2Omega_of_isom (h : InputIsomMaxEAConj) : Claims137.Input10_2Omega := by
  intro p hp hp2 ε n hn hfp X _ _ hX E₁ E₂ hE₁ hE₂ hm₁ hm₂
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · exact conj_maxEA_of_le_two hp hp2 hn (by omega) hfp hX E₁ E₂ hE₁ hE₂ hm₁ hm₂
  · cases ε
    · obtain ⟨φ⟩ := hX
      have hm : 2 ≤ n + 1 := by omega
      have hstd : IsStdSpace false (quadMinus (n + 1) (ZMod 2) 1 1) (n + 1) :=
        ⟨LinearEquiv.refl _ _, fun v => rfl⟩
      have hnd : (polarBilin (quadMinus (n + 1) (ZMod 2) 1 1)).Nondegenerate :=
        nondegenerate_polarBilin_quadMinus_of_finite (n + 1) (ZMod 2)
          (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
      have h6 : 6 ≤ finrank (ZMod 2) (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2) := by
        rw [finrank_fintype_fun_eq_card]
        simp [Fintype.card_sum]
        omega
      have hEQ := commutator_orthogonalGroup_eq_of_isometry_minus (K := ZMod 2)
        (Q := quadMinus (n + 1) (ZMod 2) 1 1) hm (LinearEquiv.refl _ _) fun v => rfl
      exact conj_maxEA_of_isom hp hp2 hn hfp hnd h6 hstd hEQ
        (h p hp hp2 false n h3 hfp _ _ hstd) (φ.trans (statedOmegaMinusEquiv hm)) E₁ E₂ hE₁ hE₂
        hm₁ hm₂
    · obtain ⟨φ⟩ := hX
      have hm : 3 ≤ n + 1 := by omega
      have hstd : IsStdSpace true (quadPlus (n + 1) (ZMod 2)) (n + 1) :=
        ⟨LinearEquiv.refl _ _, fun v => rfl⟩
      have hnd := nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2)
      have h6 : 6 ≤ finrank (ZMod 2) (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) := by
        rw [finrank_fintype_fun_eq_card]
        simp [Fintype.card_sum]
        omega
      have hEQ := commutator_orthogonalGroup_eq_of_isometry_plus (K := ZMod 2)
        (Q := quadPlus (n + 1) (ZMod 2)) hm (LinearEquiv.refl _ _) fun v => rfl
      exact conj_maxEA_of_isom hp hp2 hn hfp hnd h6 hstd hEQ
        (h p hp hp2 true n h3 hfp _ _ hstd) (φ.trans (statedOmegaPlusEquiv hm)) E₁ E₂ hE₁ hE₂
        hm₁ hm₂

end MaxEAIsom

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts2
