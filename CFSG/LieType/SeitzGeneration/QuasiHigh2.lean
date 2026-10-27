module

public import CFSG.LieType.SeitzGeneration.QuasiHigh
public import CFSG.LieType.SeitzGeneration.QuasiHigh2Linear
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighUnitaryGU
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec5Nine
public import CFSG.CGT.Timmesfeld75.Sec5Ten
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TwoGroupExtension
public import CFSG.LieType.ChevTwo.Defs
public import CFSG.LieType.SeitzGeneration.OuterNarrowClassical
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma136
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13g
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Norm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Quot
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Lift
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.RankThree.PartOne.CTP.StdSub
public import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.KernelTrivialBridge
public import CFSG.Sporadic.Co2Schreier.ThirdChain
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2323
public import Certificates.Certificate6006

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh2

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (SeitzQuasiHigh)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex Seitz2310CubeSimple)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

@[expose] def InvP'Pair {K : Type*} [Group K] (p : ℕ) (E : Subgroup (MulAut K)) : Prop :=
  ∃ H₁ H₂ : Subgroup (K ⧸ Subgroup.center K), ¬ p ∣ Nat.card H₁ ∧ ¬ p ∣ Nat.card H₂ ∧
    (∀ f ∈ E, ∀ s ∈ H₁, quotAut f s ∈ H₁) ∧ (∀ f ∈ E, ∀ s ∈ H₂, quotAut f s ∈ H₂) ∧
    H₁ ⊔ H₂ = ⊤

theorem seitzHyperGamma_eq_top_of_invP'Pair {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) (hE1 : E ≠ ⊥) (h : InvP'Pair p E) : seitzHyperGamma p E = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨H₁, H₂, hp₁, hp₂, hs₁, hs₂, hgen⟩ := h
  refine seitzHyperGamma_eq_top_of_p'Subgroups hperf hE hE1 {H₁, H₂} ?_ ?_ ?_
  · rintro H (rfl | hH)
    · exact hp₁
    · rw [Set.mem_singleton_iff.1 hH]; exact hp₂
  · rintro H (rfl | hH)
    · exact hs₁
    · rw [Set.mem_singleton_iff.1 hH]; exact hs₂
  · rw [iSup_insert, iSup_singleton, hgen]

section UnitaryDiag

open Matrix CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP CFSG.ClassicalInvolution.Phan
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.Universal.Unitary

variable {ℓ f : ℕ} {Kf : Type} [Field Kf]

@[expose] noncomputable def toPU (h : UnitaryFieldData ℓ f Kf) (n : ℕ) :
    unitarySU ℓ f Kf n →* primeFormP h (idGram Kf n) :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram Kf n)) n)).comp
    (Subgroup.inclusion (le_of_eq (unitarySU_eq_gramSU h n)))

theorem toPU_surjective (h : UnitaryFieldData ℓ f Kf) (n : ℕ) :
    Function.Surjective (toPU h n) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨⟨g.1, le_of_eq (unitarySU_eq_gramSU h n).symm g.2⟩, rfl⟩

theorem primeFormConjHom_toPU (h : UnitaryFieldData ℓ f Kf) {n : ℕ}
    {A : primeFormUnitary h (idGram Kf n)} {g : unitarySU ℓ f Kf n}
    (hA : ((A : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) * ((g : GL (Fin n) Kf) :
      Matrix (Fin n) (Fin n) Kf) = ((g : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
        ((A : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf)) :
    primeFormConjHom h (idGram Kf n) A (toPU h n g) = toPU h n g := by
  show primeFormConjHom h (idGram Kf n) A
    ((⟨(g : GL (Fin n) Kf), le_of_eq (unitarySU_eq_gramSU h n) g.2⟩ : gramSU h (idGram Kf n)) :
      primeFormP h (idGram Kf n)) =
    ((⟨(g : GL (Fin n) Kf), le_of_eq (unitarySU_eq_gramSU h n) g.2⟩ : gramSU h (idGram Kf n)) :
      primeFormP h (idGram Kf n))
  rw [primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  show (A : GL (Fin n) Kf) * g * (A : GL (Fin n) Kf)⁻¹ = g
  have hcomm : (A : GL (Fin n) Kf) * g = g * (A : GL (Fin n) Kf) := Units.ext (by
    simp only [Units.val_mul]
    exact hA)
  rw [hcomm, mul_inv_cancel_right]

@[expose] def UDiagGU {K : Type*} [Group K] (p : ℕ) (E : Subgroup (MulAut K)) : Prop :=
  ∃ (ℓ f n : ℕ) (Kf : Type) (_ : Field Kf) (h : UnitaryFieldData ℓ f Kf)
    (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf (n + 1))),
    2 ≤ n ∧ p ∣ ℓ ^ f + 1 ∧ ℓ ^ f ≠ 2 ∧
    E.map (modelAut θ) ≤ primeFormD h (idGram Kf (n + 1)) ∧
    (∀ x y : primeFormUnitary h (idGram Kf (n + 1)),
      primeFormConjHom h (idGram Kf (n + 1)) x ∈ E.map (modelAut θ) →
      primeFormConjHom h (idGram Kf (n + 1)) y ∈ E.map (modelAut θ) → x * y = y * x) ∧
    ∀ x : primeFormUnitary h (idGram Kf (n + 1)),
      primeFormConjHom h (idGram Kf (n + 1)) x ∈ E.map (modelAut θ) → x ^ (ℓ ^ f + 1) = 1

theorem seitzHyperGamma_eq_top_of_uDiagGU {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) (hU : UDiagGU p E) :
    seitzHyperGamma p E = ⊤ := by
  classical
  obtain ⟨ℓ, f, n, Kf, _, h, θ, hn, hpq, hq, hD, hcomm, hpow⟩ := hU
  have hfin := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP Kf ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  set κ := primeFormConjHom h (idGram Kf (n + 1)) with hκ
  set E' := E.map (modelAut θ) with hE'def
  have hinj := modelAut_injective hperf θ
  have hE'a : IsElemAbelian p E' := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hcard' : Nat.card E' = p ^ 3 := by rw [Subgroup.card_map_of_injective hinj, hcard]
  haveI : Finite E' :=
    Nat.finite_of_card_ne_zero (by rw [hcard']; exact pow_ne_zero 3 hp.ne_zero)
  have hq4 : 4 ≤ ℓ ^ f := by
    have h2 : 2 ≤ ℓ ^ f := le_trans h.prime.two_le (Nat.le_self_pow (by have := h.one_le; omega) ℓ)
    rcases (by omega : ℓ ^ f = 2 ∨ ℓ ^ f = 3 ∨ 4 ≤ ℓ ^ f) with h2' | h3 | h4
    · exact absurd h2' hq
    · rw [h3] at hpq
      have : p ∣ 2 ^ 2 := by norm_num; exact hpq
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
        hp2
    · exact h4
  have hker : ∀ g ∈ κ.ker, ∃ c : Kf,
      ((g : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) = c • 1 := by
    intro g hg
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff (by omega) (by omega) g).1 hg
    refine ⟨(c : Kf), ?_⟩
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  set Eh : Subgroup (primeFormUnitary h (idGram Kf (n + 1))) := E'.comap κ with hEh
  have hGcomm : ∀ u ∈ Eh, ∀ v ∈ Eh, u * v = v * u := fun u hu v hv => hcomm u v hu hv
  have hGpow : ∀ u ∈ Eh, u ^ (ℓ ^ f + 1) = 1 := fun u hu => hpow u hu
  have hdvdK : ℓ ^ f + 1 ∣ Nat.card Kf - 1 := by
    have h1 : Nat.card Kf - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
      rw [h.card_eq_sq, mul_comm]
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa [sq] using this
    rw [h1]
    exact Dvd.intro_left _ rfl
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hdvdK
  haveI : NeZero (ℓ ^ f + 1) := ⟨by omega⟩
  obtain ⟨P, hP⟩ :=
    CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m h hζ dvd_rfl Eh hGcomm hGpow
  let Pg : GL (Fin (n + 1)) Kf := (P : GL (Fin (n + 1)) Kf)
  let Dg : primeFormUnitary h (idGram Kf (n + 1)) → GL (Fin (n + 1)) Kf := fun x =>
    Pg⁻¹ * (x : GL (Fin (n + 1)) Kf) * Pg
  have hdiag : ∀ x : Eh,
      ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf).IsDiag :=
    fun x => hP x x.2
  have hDmul : ∀ x y : primeFormUnitary h (idGram Kf (n + 1)), Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin (n + 1) → Eh →* Kf := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hnz : ∀ (x : Eh) (c : Fin (n + 1)),
      ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) c c ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) *
        (((Dg x)⁻¹ : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  let π' : Eh →* E' := (κ.comp Eh.subtype).codRestrict E' fun x => x.2
  have hπ' : Function.Surjective π' := by
    rintro ⟨e, he⟩
    obtain ⟨g, hg⟩ := hD he
    exact ⟨⟨g, show κ g ∈ E' by rw [hg]; exact he⟩, Subtype.ext hg⟩
  have hπ'v : ∀ x : Eh, ((π' x : E') : MulAut (primeFormP h (idGram Kf (n + 1)))) = κ x :=
    fun _ => rfl
  have hscal : ∀ x : Eh, π' x = 1 → ∀ a b : Fin (n + 1), χ a x = χ b x := by
    intro x hx a b
    have hx' : (x : primeFormUnitary h (idGram Kf (n + 1))) ∈ κ.ker := by
      rw [MonoidHom.mem_ker, ← hπ'v, hx]
      rfl
    obtain ⟨c, hc⟩ := hker _ hx'
    have hD' : ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) = c • 1 := by
      have hPinv : ((Pg⁻¹ : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) *
          (Pg : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) = 1 := Units.inv_mul _
      simp only [Dg, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPinv]
    show ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) a a =
      ((Dg x : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) b b
    rw [hD']
    simp
  have hexpE : ∀ x : E', x ^ p = 1 := fun x => Subtype.ext (by simpa using hE'a.2 x x.2)
  have hhyper : ∀ i : Fin n, ∃ F : Subgroup E', F.index = p ∧ ∀ x : Eh, π' x ∈ F →
      χ i.castSucc x = χ i.succ x := by
    intro i
    let ρ : Eh →* Kfˣ := (χ i.castSucc).toHomUnits / (χ i.succ).toHomUnits
    have hkerρ : π'.ker ≤ ρ.ker := fun x hx =>
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux.ratio_apply_eq_one_iff
        _ _ x).2 (hscal x hx _ _)
    let ρb : E' →* Kfˣ := (QuotientGroup.lift π'.ker ρ hkerρ).comp
      (QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm.toMonoidHom
    have hρb : ∀ x : Eh, ρb (π' x) = ρ x := by
      intro x
      have h1 : (QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm (π' x) =
          (x : Eh ⧸ π'.ker) := (MulEquiv.symm_apply_eq _).2 rfl
      show QuotientGroup.lift π'.ker ρ hkerρ
        ((QuotientGroup.quotientKerEquivOfSurjective π' hπ').symm (π' x)) = ρ x
      rw [h1]
      rfl
    obtain ⟨F, hF, hFeq⟩ := exists_hyperplane_eq_of_hom hp hexpE hcard'
      ((Units.coeHom Kf).comp ρb) 1
    refine ⟨F, hF, fun x hx => ?_⟩
    have h1 : ρb (π' x) = 1 := Units.ext (by simpa using hFeq _ hx)
    rw [hρb] at h1
    exact (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux.ratio_apply_eq_one_iff
      _ _ x).1 h1
  let φ := conjSU h P
  let ε : Su Kf ℓ f (n + 1) ≃* unitarySU ℓ f Kf (n + 1) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq (n + 1))
  let ι : Fin n → (Su Kf ℓ f 2 →* unitarySU ℓ f Kf (n + 1)) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 Kf ℓ f n i)
  let g : Fin n → (Su Kf ℓ f 2 →* K ⧸ Subgroup.center K) := fun i =>
    θ.symm.toMonoidHom.comp ((toPU h (n + 1)).comp (φ.toMonoidHom.comp (ι i)))
  haveI : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSU 2 (ℓ ^ f) Kf) :=
    CFSG.RankThree.SubgroupLists.isPerfect_statedSU_two h.card_eq_sq hq4
  let ε₂ : Su Kf ℓ f 2 ≃* CFSG.Assembly.LowTwoRank.StatedSU 2 (ℓ ^ f) Kf :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq 2)
  haveI : Group.IsPerfect (Su Kf ℓ f 2) :=
    Group.IsPerfect.ofSurjective (f := ε₂.symm.toMonoidHom) ε₂.symm.surjective
  refine seitzHyperGamma_eq_top_of_perfect hperf (Set.range fun i => (g i).range) ?_ ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact commutator_range_eq_of_perfect (g i)
  · rintro _ ⟨i, rfl⟩
    obtain ⟨F, hF, hFc⟩ := hhyper i
    set F₀ : Subgroup (MulAut K) := (F.map E'.subtype).comap (modelAut θ) ⊓ E with hF₀
    have hmap : F₀.map (modelAut θ) = F.map E'.subtype := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
        exact hx
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := (Subgroup.map_subtype_le F) hy
        exact ⟨x, ⟨hy, hx⟩, rfl⟩
    have hrel : F₀.relIndex E = p := by
      rw [← Subgroup.relIndex_map_map_of_injective F₀ E hinj, hmap, ← hE'def,
        Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective E'.subtype_injective]
      exact hF
    refine ⟨F₀, inf_le_right, hrel, fun f' hf' s hs => ?_⟩
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨⟨e, he⟩, heF, hee⟩ := hf'.1
    obtain ⟨A, hA⟩ := hD he
    have hAEh : A ∈ Eh := show κ A ∈ E' by rw [hA]; exact he
    have hπ'A : π' ⟨A, hAEh⟩ ∈ F := by
      have : π' ⟨A, hAEh⟩ = ⟨e, he⟩ := Subtype.ext hA
      rw [this]
      exact heF
    have hxχ := hFc ⟨A, hAEh⟩ hπ'A
    set yb : unitarySU ℓ f Kf (n + 1) := ι i a with hyb
    have hblock : (((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) = CFSG.ClassicalInvolution.Phan.blockMat (n + 1) i
          (((a : Su Kf ℓ f 2) : GL (Fin 2) Kf) : Matrix (Fin 2) (Fin 2) Kf) := rfl
    have hdD : ((Dg A : GL (Fin (n + 1)) Kf) : Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) =
        Matrix.diagonal (fun c => ((Dg A : GL (Fin (n + 1)) Kf) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Kf) c c) :=
      ((hdiag ⟨A, hAEh⟩).diagonal_diag).symm
    have hYD : ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Dg A =
        Dg A * ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hblock, hdD]
      exact blockMat_mul_diagonal_comm (by omega) _ (hnz ⟨A, hAEh⟩) i.castSucc i.succ (by simp)
        (by simp) hxχ _
    have hAeq : ((A : primeFormUnitary h (idGram Kf (n + 1))) : GL (Fin (n + 1)) Kf) =
        Pg * Dg A * Pg⁻¹ := by simp [Dg, mul_assoc]
    have hcxG : ((A : primeFormUnitary h (idGram Kf (n + 1))) : GL (Fin (n + 1)) Kf) *
        ((φ yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) =
        ((φ yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) *
          ((A : primeFormUnitary h (idGram Kf (n + 1))) : GL (Fin (n + 1)) Kf) := by
      rw [coe_conjSU, hAeq]
      calc Pg * Dg A * Pg⁻¹ * (Pg * ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Pg⁻¹)
          = Pg * (Dg A * ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf)) * Pg⁻¹ := by
            group
        _ = Pg * (((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Dg A) * Pg⁻¹ := by
            rw [hYD]
        _ = Pg * ((yb : unitarySU ℓ f Kf (n + 1)) : GL (Fin (n + 1)) Kf) * Pg⁻¹ *
            (Pg * Dg A * Pg⁻¹) := by group
    have hfix : κ A (toPU h (n + 1) (φ yb)) = toPU h (n + 1) (φ yb) := by
      refine primeFormConjHom_toPU h ?_
      have := congrArg Units.val hcxG
      simpa only [Units.val_mul] using this
    have h1 := modelAut_apply θ f' (toPU h (n + 1) (φ yb))
    rw [← hee] at h1
    change e (toPU h (n + 1) (φ yb)) = θ (quotAut f' (θ.symm (toPU h (n + 1) (φ yb)))) at h1
    rw [← hA, hfix] at h1
    show quotAut f' (θ.symm (toPU h (n + 1) (φ yb))) = θ.symm (toPU h (n + 1) (φ yb))
    exact θ.injective (by rw [← h1, MulEquiv.apply_symm_apply])
  ·
    have hgen : ⨆ i : Fin n, (ι i).range = ⊤ := by
      have h1 := iSup_range_blockEmb2 (K := Kf) (p := ℓ) (f := f) h.card_eq_sq hq n
      have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
      rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
      simpa [ι, MonoidHom.range_comp] using h2
    have hrange : ∀ i, (g i).range =
        (((ι i).range.map φ.toMonoidHom).map (toPU h (n + 1))).map θ.symm.toMonoidHom := by
      intro i
      simp only [g, MonoidHom.range_comp, Subgroup.map_map]
    rw [iSup_range, show (⨆ i, (g i).range) =
        ((⨆ i, (ι i).range).map φ.toMonoidHom |>.map (toPU h (n + 1))).map θ.symm.toMonoidHom by
      simp only [hrange, Subgroup.map_iSup], hgen,
      Subgroup.map_top_of_surjective _ φ.surjective,
      Subgroup.map_top_of_surjective _ (toPU_surjective h (n + 1)),
      Subgroup.map_top_of_surjective _ θ.symm.surjective]

end UnitaryDiag

@[expose] def SeitzCoverCubeRest : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) → CoverIndex p d.1 →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 3 →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E → ¬ ExcIsotropic d E → ¬ LinearDiag p E → ¬ InvP'Pair p E →
      ¬ UDiagGU p E → seitzHyperGamma p E = ⊤

theorem seitzCoverFamExcRest_three_of_cubeRest (h : SeitzCoverCubeRest) :
    SeitzCoverFamExcRest 3 := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz hci E hE hcard hex hCS hX
  by_cases hLD : LinearDiag p E
  · exact seitzHyperGamma_eq_top_of_linearDiag hq.1 hp hp2 hE hcard hLD
  by_cases hP : InvP'Pair p E
  · exact seitzHyperGamma_eq_top_of_invP'Pair hq.1 hp hE (ne_bot_of_card hp (by norm_num) hcard) hP
  by_cases hU : UDiagGU p E
  · exact seitzHyperGamma_eq_top_of_uDiagGU hq.1 hp hp2 hE hcard hU
  exact h p hp hp2 K hq d hd hpd hL34 hz hci E hE hcard hex hCS hX hLD hP hU

@[expose] noncomputable def standardLinearModel {K : Type*} [Group K] {m : ℕ}
    {q : TauCeti.PrimePower} [Fact q.p.Prime] {hv : (TauCeti.LieTypeIndex.A m q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group) :
    K ⧸ Subgroup.center K ≃* projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
  e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _))

theorem linearDiag_of_standard {K : Type*} [Group K] {m : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.A m q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) (hpm : p ∣ m + 1) (hpq1 : p ∣ q.card - 1)
    {E : Subgroup (MulAut K)}
    (hlin : haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      E.map (modelAut (standardLinearModel e)) ≤
        linearAutGroup (m + 1) (GaloisField q.p q.exponent)) :
    LinearDiag p E := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hn : 3 ≤ m + 1 := by
    have := Nat.le_of_dvd (by omega) hpm
    have := hp.two_le
    omega
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hpF : (p : GaloisField q.p q.exponent) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p p).1 h
    exact hpq ((Nat.prime_dvd_prime_iff_eq q.prime_p hp).1 this).symm
  exact ⟨m + 1, GaloisField q.p q.exponent, inferInstance, inferInstance, standardLinearModel e,
    hn, hpF, by rw [hcardF]; exact hpq1, hlin⟩

theorem not_le_linearAutGroup_of_cubeRest {K : Type*} [Group K] {m : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.A m q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) (hci : CoverIndex p (.A m q))
    {E : Subgroup (MulAut K)} (hLD : ¬ LinearDiag p E) :
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    ¬ E.map (modelAut (standardLinearModel e)) ≤
      linearAutGroup (m + 1) (GaloisField q.p q.exponent) :=
  fun hlin => hLD (linearDiag_of_standard e hp hp2 hpq hci.1 hci.2 hlin)

section Mono

variable {G : Type*} [Group G]

theorem exists_hyperplane_of_ne_bot {p : ℕ} (hp : p.Prime) {F : Subgroup G} [Finite F]
    (hF : IsElemAbelian p F) (hF1 : F ≠ ⊥) : ∃ H ≤ F, H.relIndex F = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := (isPGroup_of_isElemAbelian hF).exists_card_eq
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [pow_zero] at ha
      exact absurd (Subgroup.eq_bot_of_card_eq F ha) hF1
    · exact h
  obtain ⟨H₀, hH₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) p (n := a - 1)
    (by rw [ha]; exact pow_dvd_pow p (by omega))
  refine ⟨H₀.map F.subtype, Subgroup.map_subtype_le H₀, ?_⟩
  rw [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
    F.subtype_injective]
  have h := H₀.card_mul_index
  rw [hH₀, ha] at h
  have h' : p ^ (a - 1) * H₀.index = p ^ (a - 1) * p := by
    rw [h, ← pow_succ]
    congr 1
    omega
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h'

end Mono

end CFSG.LieType.SeitzGeneration.QuasiHigh2
