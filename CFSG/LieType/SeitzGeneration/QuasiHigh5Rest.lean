module

public import CFSG.LieType.SeitzGeneration.QuasiHigh5
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.SUCentrallyClosed
public import CFSG.LieType.SeitzGeneration.UnitaryOuterNonabFive
public import CFSG.LieType.SeitzGeneration.UnitaryNonabHeis
public import CFSG.LieType.SeitzGeneration.UnitaryNonabNonPth
public import CFSG.LieType.SeitzGeneration.UnitaryNonCube
public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorPair
public import CFSG.LieType.SeitzGeneration.UnitaryNonabToral
public import CFSG.LieType.SeitzGeneration.SingerUMain
public import CFSG.LieType.SeitzGeneration.HeisTorusUGen
public import CFSG.LieType.SeitzGeneration.OuterUnitaryWide
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LieType.SeitzGeneration.OuterSUField
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactCore
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithNF
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz434
public import CFSG.RankThree.PartTwo.Sec19.Step199Proof

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh5

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex)

section UCover

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n : ℕ} {Kf : Type} [Field Kf]

abbrev GU1 (h : UnitaryFieldData ℓ f Kf) (n : ℕ) : Subgroup (GL (Fin n) Kf) :=
  gramSU h (idGram Kf n)

noncomputable abbrev piG (h : UnitaryFieldData ℓ f Kf) (n : ℕ) :
    GU1 h n →* primeFormP h (idGram Kf n) :=
  QuotientGroup.mk' (normOneScalars h (gramSU h (idGram Kf n)) n)

theorem gramSU_eq_statedSU (h : UnitaryFieldData ℓ f Kf) (n : ℕ) :
    GU1 h n = CFSG.Open.StatedSU n (ℓ ^ f) Kf :=
  (unitarySU_eq_gramSU h n).symm

theorem sUid_eq_gramSU [Finite Kf] [Fact ℓ.Prime] [CharP Kf ℓ] (h : UnitaryFieldData ℓ f Kf)
    (n : ℕ) : SUid (CFSG.LieType.BorelTits.unitaryInvolution Kf ℓ f) n = GU1 h n := by
  rw [SUid_eq_statedSU h.card_eq_sq n, gramSU_eq_statedSU]

theorem commutator_GU1_eq_top (h : UnitaryFieldData ℓ f Kf) (hn : 3 ≤ n)
    (hne : (n, ℓ ^ f) ≠ (3, 2)) : commutator (GU1 h n) = ⊤ := by
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI := h.finite
  haveI : CharP Kf ℓ := h.charP
  have hperf := CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd h.card_eq_sq hn hne
  have e : CFSG.Open.StatedSU n (ℓ ^ f) Kf ≃* GU1 h n :=
    MulEquiv.subgroupCongr (gramSU_eq_statedSU h n).symm
  haveI : Group.IsPerfect (GU1 h n) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.commutator_eq_top

theorem exists_su_lift
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    (h : UnitaryFieldData ℓ f Kf) (hn : 3 ≤ n) (hne : (n, ℓ ^ f) ≠ (3, 2))
    (hq4 : Even n → 4 ≤ ℓ ^ f) (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n)) :
    ∃ φ : GU1 h n →* K, Function.Surjective φ ∧
      ∀ g, θ ((φ g : K) : K ⧸ Subgroup.center K) = piG h n g := by
  classical
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI := h.finite
  haveI : CharP Kf ℓ := h.charP
  haveI : Group.IsPerfect K := ⟨hperf⟩
  set S := CFSG.Open.StatedSU n (ℓ ^ f) Kf with hSdef
  let ε : GU1 h n ≃* S := MulEquiv.subgroupCongr (gramSU_eq_statedSU h n)
  let π' : S →* primeFormP h (idGram Kf n) := (piG h n).comp ε.symm.toMonoidHom
  let ρ : K →* primeFormP h (idGram Kf n) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker ≤ Subgroup.center K := by
    intro x hx
    have h1 : θ (x : K ⧸ Subgroup.center K) = 1 := hx
    exact (QuotientGroup.eq_one_iff x).1 ((θ.map_eq_one_iff).1 h1)
  let Q : Subgroup (K × S) := MonoidHom.eqLocus (ρ.comp (MonoidHom.fst _ _))
    (π'.comp (MonoidHom.snd _ _))
  let pr : Q →* S := (MonoidHom.snd _ _).comp Q.subtype
  have hpr : Function.Surjective pr := fun g => by
    obtain ⟨k, hk⟩ := hρ (π' g)
    exact ⟨⟨(k, g), hk⟩, rfl⟩
  have hprk : pr.ker ≤ Subgroup.center Q := by
    intro x hx
    have hx2 : (x : K × S).2 = 1 := hx
    have hxP : ρ (x : K × S).1 = π' (x : K × S).2 := x.2
    have hx1 : (x : K × S).1 ∈ Subgroup.center K := by
      refine hker ?_
      rw [MonoidHom.mem_ker, hxP, hx2, map_one]
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.1 hx1 _
    · show (y : K × S).2 * (x : K × S).2 = (x : K × S).2 * (y : K × S).2
      rw [hx2, mul_one, one_mul]
  obtain ⟨σ, hσ⟩ : ∃ s : S →* Q, ∀ g, pr (s g) = g := by
    by_cases he : Even n
    · set eq := equivStatedSU h.card_eq_sq n with heq
      let pr' : Q →* SU (CFSG.LieType.BorelTits.unitaryInvolution Kf ℓ f) n :=
        eq.symm.toMonoidHom.comp pr
      have hpr' : Function.Surjective pr' := eq.symm.surjective.comp hpr
      have hprk' : pr'.ker ≤ Subgroup.center Q := by
        intro x hx
        apply hprk
        have h1 : eq.symm (pr x) = 1 := hx
        exact (eq.symm.map_eq_one_iff).1 h1
      obtain ⟨s', hs'⟩ := CFSG.LieType.Steinberg.CentralExt.SUClosed.su_exists_section_of_central
        h.card_eq_sq he (by obtain ⟨k, hk⟩ := he; omega) (hq4 he) hpr' hprk'
      refine ⟨s'.comp eq.symm.toMonoidHom, fun g => ?_⟩
      have h1 := hs' (eq.symm g)
      have h2 : eq.symm (pr (s' (eq.symm g))) = eq.symm g := h1
      exact eq.symm.injective h2
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        h.card_eq_sq h.one_le hn he hne hpr hprk
  let φ' : S →* K := (MonoidHom.fst _ _).comp (Q.subtype.comp σ)
  have hφ'ρ : ∀ g, ρ (φ' g) = π' g := by
    intro g
    have h1 : ρ ((σ g : K × S).1) = π' ((σ g : K × S).2) := (σ g).2
    have h2 : (σ g : K × S).2 = g := hσ g
    rw [h2] at h1
    exact h1
  let φ : GU1 h n →* K := φ'.comp ε.toMonoidHom
  have hφθ : ∀ g, θ ((φ g : K) : K ⧸ Subgroup.center K) = piG h n g := by
    intro g
    have h1 := hφ'ρ (ε g)
    change θ ((φ' (ε g) : K) : K ⧸ Subgroup.center K) = _
    rw [show θ ((φ' (ε g) : K) : K ⧸ Subgroup.center K) = ρ (φ' (ε g)) from rfl, h1]
    show piG h n (ε.symm (ε g)) = piG h n g
    rw [MulEquiv.symm_apply_apply]
  refine ⟨φ, ?_, hφθ⟩
  have htop : φ.range = ⊤ := eq_top_of_map_eq_top_of_perfect ρ hker (by
    rw [← MonoidHom.range_comp, eq_top_iff]
    rintro x -
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      (normOneScalars h (gramSU h (idGram Kf n)) n) x
    exact ⟨g, hφθ g⟩)
  exact MonoidHom.range_eq_top.1 htop

theorem seitzHyperGamma_eq_top_of_suModel {K : Type*} [Group K] (h : UnitaryFieldData ℓ f Kf)
    (hn : 3 ≤ n) (hne : (n, ℓ ^ f) ≠ (3, 2))
    (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n)) (φ : GU1 h n →* K)
    (hφ : Function.Surjective φ)
    (hφθ : ∀ g, θ ((φ g : K) : K ⧸ Subgroup.center K) = piG h n g) {p : ℕ} (hp : p.Prime)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    {S : Set (GU1 h n)} (hS : Subgroup.closure S = ⊤)
    (hfix : ∀ g ∈ S, ∃ e ∈ E, e ≠ 1 ∧ ∃ α : GU1 h n →* GU1 h n, α g = g ∧
      ∀ g', QuasiHigh2.modelAut θ e (piG h n g') = piG h n (α g')) :
    seitzHyperGamma p E = ⊤ := by
  refine seitzHyperGamma_eq_top_of_cover (commutator_GU1_eq_top h hn hne) φ hφ hp hE hcard hS ?_
  intro g hg
  obtain ⟨e, he, he1, α, hαg, hα⟩ := hfix g hg
  refine ⟨e, he, he1, α, hαg, fun g' => θ.injective ?_⟩
  rw [model_mk_apply, hφθ, hφθ, hα]

theorem primeFormConjHom_piG (h : UnitaryFieldData ℓ f Kf) (A : primeFormUnitary h (idGram Kf n))
    (g : GU1 h n) : primeFormConjHom h (idGram Kf n) A (piG h n g) =
      piG h n (primeFormConjSU h (idGram Kf n) A g) :=
  primeFormConjAut_mk h (idGram Kf n) A g

theorem primeFormConjSU_eq_self_of_comm (h : UnitaryFieldData ℓ f Kf)
    (A : primeFormUnitary h (idGram Kf n)) {g : GU1 h n}
    (hg : ((g : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
      ((A : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
      ((A : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) * ((g : GL (Fin n) Kf) :
        Matrix (Fin n) (Fin n) Kf)) :
    primeFormConjSU h (idGram Kf n) A g = g := by
  apply Subtype.ext
  change (A : GL (Fin n) Kf) * g * (A : GL (Fin n) Kf)⁻¹ = g
  have hc : (A : GL (Fin n) Kf) * (g : GL (Fin n) Kf) = g * A :=
    Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hg.symm)
  rw [hc, mul_inv_cancel_right]

theorem closure_eq_top_of_sUid [Finite Kf] [Fact ℓ.Prime] [CharP Kf ℓ]
    (h : UnitaryFieldData ℓ f Kf) {ι : Type*}
    (M : ι → Matrix (Fin n) (Fin n) Kf) (S : Set (GU1 h n))
    (hS : ∀ i, ∀ g : GU1 h n, ((g : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) * M i =
      M i * ((g : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) → g ∈ S)
    (htop : ∀ H : Subgroup (SUid (CFSG.LieType.BorelTits.unitaryInvolution Kf ℓ f) n),
      (∀ i, CFSG.LieType.SeitzGeneration.HeisTensor.Cent H (M i)) → H = ⊤) :
    Subgroup.closure S = ⊤ := by
  let ε : SUid (CFSG.LieType.BorelTits.unitaryInvolution Kf ℓ f) n ≃* GU1 h n :=
    MulEquiv.subgroupCongr (sUid_eq_gramSU h n)
  have hH := htop ((Subgroup.closure S).comap ε.toMonoidHom) (fun i g hg =>
    Subgroup.subset_closure (hS i (ε g) hg))
  rw [eq_top_iff]
  intro z _
  have hz : ε.symm z ∈ (Subgroup.closure S).comap ε.toMonoidHom := by
    rw [hH]
    exact Subgroup.mem_top _
  simpa using hz

end UCover

section UPlane

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n p : ℕ} {Kf : Type} [Field Kf]

@[expose] def liftCent (h : UnitaryFieldData ℓ f Kf) (n : ℕ)
    (Ē : Subgroup (MulAut (primeFormP h (idGram Kf n)))) : Set (GU1 h n) :=
  {g | ∃ W : primeFormUnitary h (idGram Kf n), primeFormConjHom h (idGram Kf n) W ∈ Ē ∧
    primeFormConjHom h (idGram Kf n) W ≠ 1 ∧
    ((g : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
      ((W : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
      ((W : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
        ((g : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf)}

theorem closure_liftCent_of_family [Finite Kf] [Fact ℓ.Prime] [CharP Kf ℓ]
    (h : UnitaryFieldData ℓ f Kf) {Ē : Subgroup (MulAut (primeFormP h (idGram Kf n)))}
    {ι : Type*} (W : ι → primeFormUnitary h (idGram Kf n))
    (hW : ∀ i, primeFormConjHom h (idGram Kf n) (W i) ∈ Ē)
    (hW1 : ∀ i, primeFormConjHom h (idGram Kf n) (W i) ≠ 1)
    (htop : ∀ H : Subgroup (SUid (CFSG.LieType.BorelTits.unitaryInvolution Kf ℓ f) n),
      (∀ i, CFSG.LieType.SeitzGeneration.HeisTensor.Cent H
        (((W i : primeFormUnitary h (idGram Kf n)) : GL (Fin n) Kf) :
          Matrix (Fin n) (Fin n) Kf)) → H = ⊤) :
    Subgroup.closure (liftCent h n Ē) = ⊤ :=
  closure_eq_top_of_sUid h (fun i => ((W i : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf)) _
    (fun i g hg => ⟨W i, hW i, hW1 i, hg⟩) htop

theorem scalar_mem_GU (h : UnitaryFieldData ℓ f Kf) {c : Kfˣ} (hc : h.norm (c : Kf) = 1) :
    GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram Kf n) :=
  scalar_mem_primeFormUnitary_one h hc

theorem conjHom_ne_one_of_qcomm (h : UnitaryFieldData ℓ f Kf) (hn : 3 ≤ n)
    {W₀ W₁ : primeFormUnitary h (idGram Kf n)} {ζ : Kf} (hζ1 : ζ ≠ 1)
    (hcomm : ((W₀ : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
      ((W₁ : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
      ζ • (((W₁ : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
        ((W₀ : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf))) :
    primeFormConjHom h (idGram Kf n) W₀ ≠ 1 ∧
      ∀ j : ℕ, primeFormConjHom h (idGram Kf n) (W₁ * W₀ ^ j) ≠ 1 := by
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  have hkey : (W₀ : GL (Fin n) Kf) * W₁ ≠ W₁ * W₀ := by
    intro hc
    have h1 : ((W₀ : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
        ((W₁ : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
        ((W₁ : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
          ((W₀ : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) := by
      rw [← Units.val_mul, ← Units.val_mul, hc]
    rw [h1] at hcomm
    have h2 : (1 - ζ) • (((W₁ : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
        ((W₀ : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf)) = 0 := by
      rw [sub_smul, one_smul, ← hcomm, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact hζ1 (sub_eq_zero.1 h3).symm
    · have h4 : (((W₁ : GL (Fin n) Kf) * (W₀ : GL (Fin n) Kf) : GL (Fin n) Kf) :
          Matrix (Fin n) (Fin n) Kf) ≠ 0 := Units.ne_zero _
      rw [Units.val_mul] at h4
      exact h4 h3
  refine ⟨fun h1 => hkey ?_, fun j h1 => hkey ?_⟩
  · obtain ⟨c, -, hc⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn W₀).1 h1
    rw [hc]
    exact (commute_scalar c _).eq.symm
  · obtain ⟨c, -, hc⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn (W₁ * W₀ ^ j)).1 h1
    have hW₁ : (W₁ : GL (Fin n) Kf) = GeneralLinearGroup.scalar (Fin n) c *
        ((W₀ : GL (Fin n) Kf) ^ j)⁻¹ := by
      rw [← hc]
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      group
    rw [hW₁]
    have h2 : Commute (W₀ : GL (Fin n) Kf) (GeneralLinearGroup.scalar (Fin n) c) :=
      commute_scalar c _
    have h3 : Commute (W₀ : GL (Fin n) Kf) (((W₀ : GL (Fin n) Kf) ^ j)⁻¹) :=
      ((Commute.refl (W₀ : GL (Fin n) Kf)).pow_right j).inv_right
    exact (h2.mul_right h3).eq

theorem conjHom_scalar_mul (h : UnitaryFieldData ℓ f Kf) (hn : 3 ≤ n) {c : Kfˣ}
    (hc : h.norm (c : Kf) = 1) (W : primeFormUnitary h (idGram Kf n)) :
    primeFormConjHom h (idGram Kf n) (⟨GeneralLinearGroup.scalar (Fin n) c, scalar_mem_GU h hc⟩ * W) =
      primeFormConjHom h (idGram Kf n) W := by
  rw [map_mul, (OuterUnitaryWide.conjHom_eq_one_iff h hn _).2 ⟨c, hc, rfl⟩, one_mul]

theorem norm_inv_eq_one (h : UnitaryFieldData ℓ f Kf) {μ : Kf} (hμ : h.bar μ * μ = 1) :
    h.norm μ⁻¹ = 1 := by
  rw [UnitaryFieldData.norm, map_inv₀, ← mul_inv, mul_comm, hμ, inv_one]

theorem closure_liftCent_toral (h : UnitaryFieldData ℓ f Kf) (hn : 3 ≤ n) (hq2 : ℓ ^ f ≠ 2)
    (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) {Ē : Subgroup (MulAut (primeFormP h (idGram Kf n)))}
    {A B : primeFormUnitary h (idGram Kf n)} (hAE : primeFormConjHom h (idGram Kf n) A ∈ Ē)
    (hBE : primeFormConjHom h (idGram Kf n) B ∈ Ē) (hAB : A * B = B * A)
    (hword1 : ∀ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) → primeFormConjHom h (idGram Kf n) (A ^ a * B ^ b) ≠ 1)
    {μ μ' : Kfˣ} (hμN : h.bar (μ : Kf) * μ = 1) (hμ'N : h.bar (μ' : Kf) * μ' = 1)
    (hAp : (A : GL (Fin n) Kf) ^ p = GeneralLinearGroup.scalar (Fin n) (μ ^ p))
    (hBp : (B : GL (Fin n) Kf) ^ p = GeneralLinearGroup.scalar (Fin n) (μ' ^ p)) :
    Subgroup.closure (liftCent h n Ē) = ⊤ := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set κ := primeFormConjHom h (idGram Kf (m + 1)) with hκ
  have hμi : h.norm ((μ⁻¹ : Kfˣ) : Kf) = 1 := by
    rw [Units.val_inv_eq_inv_val]; exact norm_inv_eq_one h hμN
  have hμ'i : h.norm ((μ'⁻¹ : Kfˣ) : Kf) = 1 := by
    rw [Units.val_inv_eq_inv_val]; exact norm_inv_eq_one h hμ'N
  set sμ : primeFormUnitary h (idGram Kf (m + 1)) :=
    ⟨GeneralLinearGroup.scalar (Fin (m + 1)) μ⁻¹, scalar_mem_GU h hμi⟩ with hsμ
  set sμ' : primeFormUnitary h (idGram Kf (m + 1)) :=
    ⟨GeneralLinearGroup.scalar (Fin (m + 1)) μ'⁻¹, scalar_mem_GU h hμ'i⟩ with hsμ'
  have hcs : ∀ (s : primeFormUnitary h (idGram Kf (m + 1))) (c : Kfˣ),
      (s : GL (Fin (m + 1)) Kf) = GeneralLinearGroup.scalar (Fin (m + 1)) c →
        ∀ g : primeFormUnitary h (idGram Kf (m + 1)), Commute s g := by
    intro s c hs g
    apply Subtype.ext
    change (s : GL (Fin (m + 1)) Kf) * g = g * s
    rw [hs]
    exact (commute_scalar c (g : GL (Fin (m + 1)) Kf)).eq.symm
  set x : primeFormUnitary h (idGram Kf (m + 1)) := sμ * A with hx
  set y : primeFormUnitary h (idGram Kf (m + 1)) := sμ' * B with hy
  have hxy : Commute x y := by
    have h1 : Commute A B := hAB
    exact ((hcs sμ μ⁻¹ rfl sμ').mul_left ((hcs sμ' μ'⁻¹ rfl A).symm)).mul_right
      (((hcs sμ μ⁻¹ rfl B)).mul_left h1)
  have hx1 : x ^ p = 1 := by
    apply Subtype.ext
    rw [hx, (hcs sμ μ⁻¹ rfl A).mul_pow, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
      hAp]
    simp [hsμ, ← map_pow, ← map_mul]
  have hy1 : y ^ p = 1 := by
    apply Subtype.ext
    rw [hy, (hcs sμ' μ'⁻¹ rfl B).mul_pow, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
      hBp]
    simp [hsμ', ← map_pow, ← map_mul]
  have hκx : ∀ a b : ℕ, κ (x ^ a * y ^ b) = κ (A ^ a * B ^ b) := by
    intro a b
    have h1 : κ sμ = 1 := (OuterUnitaryWide.conjHom_eq_one_iff h hn sμ).2 ⟨μ⁻¹, hμi, rfl⟩
    have h2 : κ sμ' = 1 := (OuterUnitaryWide.conjHom_eq_one_iff h hn sμ').2 ⟨μ'⁻¹, hμ'i, rfl⟩
    rw [hx, hy, (hcs sμ μ⁻¹ rfl A).mul_pow, (hcs sμ' μ'⁻¹ rfl B).mul_pow, map_mul, map_mul,
      map_mul, map_pow κ sμ, map_pow κ sμ', h1, h2, one_pow, one_pow, one_mul, one_mul, map_mul]
  have hind' : ∀ a b : ℕ, x ^ a * y ^ b = 1 → p ∣ a ∧ p ∣ b := by
    intro a b h1
    by_contra hab
    apply hword1 a b hab
    rw [← hκx, h1, map_one]
  set G := commPairSubgroupP hp hxy hx1 hy1 with hG
  have hcardG : Nat.card G = p ^ 2 := card_commPairSubgroupP hp hxy hx1 hy1 hind'
  have hcl := closure_centralizers_unitarySU_of_dvd_add_one_gu h hp hpq hq2 G
    (commPairSubgroupP_comm hp hxy hx1 hy1) (commPairSubgroupP_exp hp hxy hx1 hy1) hcardG
  let ε : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f Kf (m + 1) ≃* GU1 h (m + 1) :=
    MulEquiv.subgroupCongr (gramSU_eq_statedSU h (m + 1)).symm
  rw [eq_top_iff]
  intro g _
  have hg : ε.symm g ∈ Subgroup.closure {g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f Kf
      (m + 1) | ∃ x ∈ G, x ≠ 1 ∧ (g : GL (Fin (m + 1)) Kf) * (x : GL (Fin (m + 1)) Kf) =
        (x : GL (Fin (m + 1)) Kf) * (g : GL (Fin (m + 1)) Kf)} := hcl ▸ Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem ε.toMonoidHom hg
  rw [MonoidHom.map_closure] at hmap
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hmap
  refine (Subgroup.closure_mono ?_) hmap
  rintro _ ⟨g', ⟨z, hzG, hz1, hz⟩, rfl⟩
  obtain ⟨a, b, rfl⟩ := hzG
  refine ⟨x ^ a * y ^ b, ?_, ?_, ?_⟩
  · rw [hκx, map_mul, map_pow, map_pow]
    exact Ē.mul_mem (Ē.pow_mem hAE a) (Ē.pow_mem hBE b)
  · intro h1
    apply hz1
    have hab := hind' a b
    by_cases hp' : p ∣ a ∧ p ∣ b
    · obtain ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩ := hp'
      rw [pow_mul, pow_mul, hx1, hy1, one_pow, one_pow, one_mul]
    · exact absurd (by rw [← hκx]; exact h1) (hword1 a b hp')
  · change ((ε g' : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) *
      ((x ^ a * y ^ b : primeFormUnitary h (idGram Kf (m + 1))) : GL (Fin (m + 1)) Kf) = _
    rw [show ((ε g' : GL (Fin (m + 1)) Kf)) = (g' : GL (Fin (m + 1)) Kf) from rfl,
      ← Units.val_mul, hz, Units.val_mul]

theorem dvd_of_qcomm {K : Type} [Field K] {X Y : GL (Fin n) K} {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hcomm : (Y : Matrix (Fin n) (Fin n) K) * X = ζ • ((X : Matrix (Fin n) (Fin n) K) * Y)) :
    p ∣ n := by
  have h1 := congrArg Matrix.det hcomm
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Fintype.card_fin, mul_comm
    (Matrix.det (X : Matrix (Fin n) (Fin n) K))] at h1
  have hdet : (Y : Matrix (Fin n) (Fin n) K).det * (X : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
    mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero Y) (Matrix.GeneralLinearGroup.det_ne_zero X)
  have h2 : ζ ^ n = 1 := by
    have h3 : (ζ ^ n - 1) * ((Y : Matrix (Fin n) (Fin n) K).det *
        (X : Matrix (Fin n) (Fin n) K).det) = 0 := by linear_combination -h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hdet)
  exact hζ.dvd_of_pow_eq_one n h2

theorem closure_liftCent_of_exact (h : UnitaryFieldData ℓ f Kf)
    {Ē : Subgroup (MulAut (primeFormP h (idGram Kf n)))}
    (Ws : Set (primeFormUnitary h (idGram Kf n)))
    (hW : ∀ W ∈ Ws, primeFormConjHom h (idGram Kf n) W ∈ Ē ∧ primeFormConjHom h (idGram Kf n) W ≠ 1)
    (htop : ∀ Q : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f Kf n),
      (∀ W ∈ Ws, ∀ g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f Kf n,
        ((g : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
            ((W : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
          ((W : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
            ((g : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) → g ∈ Q) → Q = ⊤) :
    Subgroup.closure (liftCent h n Ē) = ⊤ := by
  let ε : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f Kf n ≃* GU1 h n :=
    MulEquiv.subgroupCongr (gramSU_eq_statedSU h n).symm
  have hQ := htop ((Subgroup.closure (liftCent h n Ē)).comap ε.toMonoidHom) fun W hWs g hg =>
    Subgroup.subset_closure ⟨W, (hW W hWs).1, (hW W hWs).2, hg⟩
  rw [eq_top_iff]
  intro z _
  have hz : ε.symm z ∈ (Subgroup.closure (liftCent h n Ē)).comap ε.toMonoidHom := by
    rw [hQ]
    exact Subgroup.mem_top _
  simpa using hz

theorem heisClosure_le_outerHeisClosure_one {ω : Kf} (hω : IsPrimitiveRoot ω 3) :
    heisClosure ℓ f Kf ω ≤ outerHeisClosure ℓ f Kf ω 1 := by
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  have hDD : hD ω = heisD ω := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD, heisD]
  have hSC : (hS : Matrix (Fin 3) (Fin 3) Kf) = heisC 1 := rfl
  have hDS : hD ω * hS = ω • (hS * hD ω) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hD, hS, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have hDSS : (hD ω * hS * hS) ^ 2 = hS * hD ω ^ 2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hD, hS, sq, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have hsq : ∀ {A M : Matrix (Fin 3) (Fin 3) Kf} {c : Kf}, A * M = c • (M * A) →
      A * M ^ 2 = c ^ 2 • (M ^ 2 * A) := by
    intro A M c hAM
    rw [sq, sq, ← Matrix.mul_assoc, hAM, Matrix.smul_mul, Matrix.mul_assoc, hAM, Matrix.mul_smul,
      smul_smul, Matrix.mul_assoc]
  unfold heisClosure outerHeisClosure
  apply Subgroup.closure_mono
  rintro g ⟨M, hM, c, hgM⟩
  simp only [heisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact ⟨heisD ω, by simp [outerHeisLines], c, by rw [← hDD]; exact hgM⟩
  · exact ⟨heisC 1, by simp [outerHeisLines], c, by rw [← hSC]; exact hgM⟩
  · refine ⟨heisC 1 * heisD ω, by simp [outerHeisLines], ?_⟩
    rw [← hDD, ← hSC]
    refine (mem_FixU_smul hω0).1 ?_
    rw [← hDS]
    exact ⟨c, hgM⟩
  · refine ⟨heisC 1 * heisD ω ^ 2, by simp [outerHeisLines], c ^ 2, ?_⟩
    rw [← hDD, ← hSC, ← hDSS]
    exact hsq hgM

theorem closure_outerHeisExactFix_one
    (h : UnitaryFieldData ℓ f Kf)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq2 : ℓ ^ f ≠ 2) {ω : Kf} (hω : IsPrimitiveRoot ω 3) :
    Subgroup.closure (CFSG.RankThree.PartTwo.Sec19.outerHeisExactFix ℓ f Kf ω 1) = ⊤ := by
  obtain ⟨s, hs⟩ := CFSG.RankThree.PartTwo.Sec19.exists_heisC_one_su h
  have hsQ : s ∈ Subgroup.closure (CFSG.RankThree.PartTwo.Sec19.outerHeisExactFix ℓ f Kf ω 1) :=
    Subgroup.subset_closure ⟨heisC 1, by simp [outerHeisLines], by rw [hs]⟩
  have hle := CFSG.RankThree.PartTwo.Sec19.fixU_le_exactClosure_of_shift h hq3 hω (one_pow _) hs
    hsQ
  have htop : outerHeisClosure ℓ f Kf ω 1 = ⊤ :=
    top_unique ((unitaryHeisCore_iff.1 unitaryHeisCore ℓ f Kf h hq3 hq2 ω hω).symm.le.trans
      (heisClosure_le_outerHeisClosure_one hω))
  rw [htop] at hle
  exact top_unique hle

theorem eq_top_of_exact_normal (h : UnitaryFieldData ℓ f Kf) {ω α a b : Kf}
    {X Y : Matrix (Fin 3) (Fin 3) Kf} (P : primeFormUnitary h (idGram Kf 3))
    (hXP : X * ((P : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
      ((P : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * (a • heisC α))
    (hYP : Y * ((P : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
      ((P : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * (b • heisD ω))
    (hcl : Subgroup.closure (CFSG.RankThree.PartTwo.Sec19.outerHeisExactFix ℓ f Kf ω α) = ⊤)
    {Q : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f Kf 3)}
    (hQ : ∀ M ∈ ({X, Y, X * Y, X * Y ^ 2} : Set (Matrix (Fin 3) (Fin 3) Kf)),
      ∀ g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f Kf 3,
        ((g : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * M =
          M * ((g : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) → g ∈ Q) :
    Q = ⊤ := by
  refine eq_top_of_conj_closure h P hcl fun g hg => ?_
  obtain ⟨M, hM, hgM⟩ := hg
  have hc : ∀ {N M' : Matrix (Fin 3) (Fin 3) Kf},
      M' ∈ ({X, Y, X * Y, X * Y ^ 2} : Set (Matrix (Fin 3) (Fin 3) Kf)) →
      M' * ((P : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
        ((P : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * N →
      ((g : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * N =
        N * ((g : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) →
      CFSG.RankThree.PartOne.KFU.conjSU h P g ∈ Q := fun hM' hMP hgN =>
    hQ _ hM' _ (CFSG.RankThree.PartTwo.Sec19.comm_conjSU h P hMP hgN).symm
  simp only [outerHeisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact hc (by simp) hXP (CFSG.RankThree.PartTwo.Sec19.comm_smul_of_comm a hgM)
  · exact hc (by simp) hYP (CFSG.RankThree.PartTwo.Sec19.comm_smul_of_comm b hgM)
  · refine hc (by simp) (intertwine_mul_right hXP hYP) ?_
    have hN : (a • heisC α) * (b • heisD ω) = (a * b) • (heisC α * heisD ω) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hN]
    exact CFSG.RankThree.PartTwo.Sec19.comm_smul_of_comm _ hgM
  · refine hc (by simp) (intertwine_mul_right hXP (intertwine_pow_right hYP 2)) ?_
    have hN : (a • heisC α) * (b • heisD ω) ^ 2 = (a * b ^ 2) • (heisC α * heisD ω ^ 2) := by
      rw [smul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hN]
    exact CFSG.RankThree.PartTwo.Sec19.comm_smul_of_comm _ hgM

theorem closure_liftCent_heis_three
    (h : UnitaryFieldData ℓ f Kf)
    (hq2 : ℓ ^ f ≠ 2) (hq3 : 3 ∣ ℓ ^ f + 1) {Ē : Subgroup (MulAut (primeFormP h (idGram Kf 3)))}
    {X Y : primeFormUnitary h (idGram Kf 3)}
    (hXE : primeFormConjHom h (idGram Kf 3) X ∈ Ē) (hYE : primeFormConjHom h (idGram Kf 3) Y ∈ Ē)
    (hX1 : primeFormConjHom h (idGram Kf 3) X ≠ 1) (hY1 : primeFormConjHom h (idGram Kf 3) Y ≠ 1)
    (hXY1 : primeFormConjHom h (idGram Kf 3) (X * Y) ≠ 1)
    (hXY2 : primeFormConjHom h (idGram Kf 3) (X * Y ^ 2) ≠ 1)
    {ζ ν γ : Kf} (hζ : IsPrimitiveRoot ζ 3) (hν0 : ν ≠ 0) (hνN : h.bar ν * ν = 1) (hγ0 : γ ≠ 0)
    (hYp : (((Y : GL (Fin 3) Kf) ^ 3 : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) = (ν ^ 3) • 1)
    (hXp : (((X : GL (Fin 3) Kf) ^ 3 : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) = γ • 1)
    (hYX : ((Y : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) *
        ((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
      ζ • (((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) *
        ((Y : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf))) :
    Subgroup.closure (liftCent h 3 Ē) = ⊤ := by
  classical
  refine closure_liftCent_of_exact h {X, Y, X * Y, X * Y ^ 2} ?_ fun Q hQ => ?_
  · rintro W (rfl | rfl | rfl | rfl)
    · exact ⟨hXE, hX1⟩
    · exact ⟨hYE, hY1⟩
    · exact ⟨by rw [map_mul]; exact Ē.mul_mem hXE hYE, hXY1⟩
    · exact ⟨by rw [map_mul, map_pow]; exact Ē.mul_mem hXE (Ē.pow_mem hYE 2), hXY2⟩
  have hQ' : ∀ M ∈ ({((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf),
      ((Y : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf),
      ((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) *
        ((Y : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf),
      ((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) *
        ((Y : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) ^ 2} :
        Set (Matrix (Fin 3) (Fin 3) Kf)),
      ∀ g : CFSG.ClassicalGroups.UnitaryFlag.unitarySU ℓ f Kf 3,
        ((g : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * M =
          M * ((g : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) → g ∈ Q := by
    rintro M (rfl | rfl | rfl | rfl) g hg
    · exact hQ X (by simp) g hg
    · exact hQ Y (by simp) g hg
    · refine hQ (X * Y) (by simp) g ?_
      rw [Subgroup.coe_mul, Units.val_mul]
      exact hg
    · refine hQ (X * Y ^ 2) (by simp) g ?_
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
      exact hg
  have hνi : h.norm ((Units.mk0 ν hν0)⁻¹ : Kfˣ) = 1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
    exact norm_inv_eq_one h hνN
  obtain ⟨Y', hY'm⟩ : ∃ Y' : primeFormUnitary h (idGram Kf 3),
      ((Y' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
        ν⁻¹ • ((Y : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) :=
    ⟨⟨GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ν hν0)⁻¹, scalar_mem_GU h hνi⟩ * Y, by
      rw [Subgroup.coe_mul, Units.val_mul, coe_scalarGL, Matrix.smul_mul, Matrix.one_mul,
        Units.val_inv_eq_inv_val, Units.val_mk0]⟩
  have hY'3 : ((Y' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) ^ 3 = 1 := by
    rw [hY'm, smul_pow, ← Units.val_pow_eq_pow_val, hYp, smul_smul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 3 hν0), one_smul]
  have hYm : ((Y : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
      ν • ((Y' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) := by
    rw [hY'm, smul_smul, mul_inv_cancel₀ hν0, one_smul]
  have hY'X : ((Y' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) *
      ((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
      ζ • (((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) *
        ((Y' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf)) := by
    rw [hY'm, Matrix.smul_mul, hYX, Matrix.mul_smul, smul_comm]
  have hX3 : ((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) ^ 3 = γ • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hXp
  have hγN : γ ^ (ℓ ^ f + 1) = 1 := by
    have h1 := bar_mul_eq_one_of_scalar_pow h (by norm_num) X.2 hXp
    rw [h.bar_apply, ← pow_succ] at h1
    exact h1
  have hYP : ∀ (P : GL (Fin 3) Kf) (ξ : Kf),
      ((Y' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * (P : Matrix (Fin 3) (Fin 3) Kf) =
        (P : Matrix (Fin 3) (Fin 3) Kf) * diagonal ![ξ, ξ * ζ, ξ * ζ ^ 2] →
      ((Y : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * (P : Matrix (Fin 3) (Fin 3) Kf) =
        (P : Matrix (Fin 3) (Fin 3) Kf) * ((ν * ξ) • heisD ζ) := by
    intro P ξ hP
    rw [CFSG.RankThree.PartTwo.Sec19.diagonal_xi_eq_smul_heisD] at hP
    rw [hYm, Matrix.smul_mul, hP]
    simp only [Matrix.mul_smul, smul_smul]
  by_cases hγc : ∃ μ : Kf, μ ^ 3 = γ
  ·
    obtain ⟨μ, hμ⟩ := hγc
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hμ
      exact hγ0 hμ.symm
    have hμN : h.bar μ * μ = 1 :=
      bar_mul_eq_one_of_pow_eq h Nat.prime_three (by norm_num) hq3 hμ0 hμ hγN
    have hμi : h.norm ((Units.mk0 μ hμ0)⁻¹ : Kfˣ) = 1 := by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0]
      exact norm_inv_eq_one h hμN
    obtain ⟨X', hX'm⟩ : ∃ X' : primeFormUnitary h (idGram Kf 3),
        ((X' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
          μ⁻¹ • ((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) :=
      ⟨⟨GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0)⁻¹, scalar_mem_GU h hμi⟩ * X, by
        rw [Subgroup.coe_mul, Units.val_mul, coe_scalarGL, Matrix.smul_mul, Matrix.one_mul,
          Units.val_inv_eq_inv_val, Units.val_mk0]⟩
    have hX'3 : ((X' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) ^ 3 = (1 : Kf) • 1 := by
      rw [hX'm, smul_pow, hX3, smul_smul, inv_pow, hμ, inv_mul_cancel₀ hγ0]
    have hY'X' : ((Y' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) *
        ((X' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
        ζ • (((X' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) *
          ((Y' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf)) := by
      rw [hX'm, Matrix.mul_smul, hY'X, Matrix.smul_mul, smul_comm]
    have hXm : ((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
        μ • ((X' : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) := by
      rw [hX'm, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    obtain ⟨P, ξ, hP, -, hYP', hXP'⟩ :=
      exists_unitary_heisenberg_basis_alpha h hq3 X'.2 Y'.2 hζ hY'X' hY'3 hX'3
    refine eq_top_of_exact_normal h (a := μ) (b := ν * ξ) ⟨P, hP⟩ ?_ (hYP P ξ hYP')
      (closure_outerHeisExactFix_one h hq3 hq2 hζ) hQ'
    change ((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * (P : Matrix (Fin 3) (Fin 3) Kf) =
      (P : Matrix (Fin 3) (Fin 3) Kf) * (μ • heisC 1)
    rw [hXm, Matrix.smul_mul, hXP', Matrix.mul_smul]
  ·
    obtain ⟨P, ξ, hP, -, hYP', hXP'⟩ :=
      exists_unitary_heisenberg_basis_alpha h hq3 X.2 Y'.2 hζ hY'X hY'3 hX3
    refine eq_top_of_exact_normal h (a := 1) (b := ν * ξ) ⟨P, hP⟩ ?_ (hYP P ξ hYP')
      (CFSG.RankThree.PartTwo.Sec19.unitaryOuterHeisCoreExact_holds ℓ f Kf h hq3 hq2 ζ γ hζ hγN
        hγc) hQ'
    change ((X : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * (P : Matrix (Fin 3) (Fin 3) Kf) =
      (P : Matrix (Fin 3) (Fin 3) Kf) * ((1 : Kf) • heisC γ)
    rw [one_smul]
    exact hXP'

theorem closure_liftCent_eq_top
    [Finite Kf] [Fact ℓ.Prime]
    [CharP Kf ℓ] (h : UnitaryFieldData ℓ f Kf) (hn : 3 ≤ n) (hq2 : ℓ ^ f ≠ 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) {Ē : Subgroup (MulAut (primeFormP h (idGram Kf n)))}
    (hĒ : IsElemAbelian p Ē) (hc : Nat.card Ē = p ^ 2) (hD : Ē ≤ primeFormD h (idGram Kf n)) :
    Subgroup.closure (liftCent h n Ē) = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hn0 : 0 < n := by omega
  set κ := primeFormConjHom h (idGram Kf n) with hκ
  obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_independent_pair hp Ē hĒ.2 hc
  obtain ⟨A, rfl⟩ := hD he₁
  obtain ⟨B, rfl⟩ := hD he₂
  have hind := hind_of_indep h hn hp hĒ he₁ he₂ he₂1 he₁₂
  have hA1 : κ A ≠ 1 := fun h1 => he₁₂ (h1 ▸ Subgroup.one_mem _)
  have hwordE : ∀ a b : ℕ, κ (A ^ a * B ^ b) ∈ Ē := fun a b => by
    rw [map_mul, map_pow, map_pow]
    exact Ē.mul_mem (Ē.pow_mem he₁ a) (Ē.pow_mem he₂ b)
  have hword1 : ∀ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) → κ (A ^ a * B ^ b) ≠ 1 := by
    intro a b hab h1
    obtain ⟨c, -, hc'⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn _).1 h1
    apply hab
    refine hind a b ⟨(c : Kf), ?_⟩
    have := congrArg (fun x : GL (Fin n) Kf => (x : Matrix (Fin n) (Fin n) Kf)) hc'
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow, coe_scalarGL] using this
  have hcube : ∀ C : primeFormUnitary h (idGram Kf n), κ C ∈ Ē →
      ∃ α : Kfˣ, ((C : GL (Fin n) Kf) ^ p : GL (Fin n) Kf) =
        GeneralLinearGroup.scalar (Fin n) α := by
    intro C hC
    have h1 : κ (C ^ p) = 1 := by
      rw [map_pow]
      exact hĒ.2 _ hC
    obtain ⟨d, -, hd⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn (C ^ p)).1 h1
    exact ⟨d, by simpa only [Subgroup.coe_pow] using hd⟩
  obtain ⟨α, hα⟩ := hcube A he₁
  obtain ⟨β, hβ⟩ := hcube B he₂
  have hx3 : (((A : GL (Fin n) Kf) ^ p : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
      (α : Kf) • 1 := by
    rw [hα]
    exact coe_scalarGL α
  have hy3 : (((B : GL (Fin n) Kf) ^ p : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
      (β : Kf) • 1 := by
    rw [hβ]
    exact coe_scalarGL β
  have hx3m : ((A : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) ^ p = (α : Kf) • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hx3
  have hy3m : ((B : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) ^ p = (β : Kf) • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hy3
  have hcomm' : κ A * κ B = κ B * κ A :=
    congrArg Subtype.val (hĒ.1.is_comm.comm (⟨_, he₁⟩ : Ē) ⟨_, he₂⟩)
  obtain ⟨c, -, hcBA⟩ : ∃ c : Kfˣ, h.norm (c : Kf) = 1 ∧
      ((B * A * (A * B)⁻¹ : primeFormUnitary h (idGram Kf n)) : GL (Fin n) Kf) =
        GeneralLinearGroup.scalar (Fin n) c := by
    refine (OuterUnitaryWide.conjHom_eq_one_iff h hn _).1 ?_
    rw [map_mul, map_mul, map_inv, map_mul, hcomm']
    exact mul_inv_cancel _
  have hBA : (B : GL (Fin n) Kf) * A =
      GeneralLinearGroup.scalar (Fin n) c * ((A : GL (Fin n) Kf) * B) := by
    have : (B : GL (Fin n) Kf) * A * ((A : GL (Fin n) Kf) * B)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) c := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcBA
    rw [← this]
    group
  have hBAm : ((B : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
      ((A : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
        (c : Kf) • (((A : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
          ((B : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf)) := by
    have := congrArg (fun g : GL (Fin n) Kf => (g : Matrix (Fin n) (Fin n) Kf)) hBA
    simp only [Units.val_mul, coe_scalarGL, Matrix.smul_mul, Matrix.one_mul] at this
    exact this
  have hcp : (c : Kf) ^ p = 1 := pow_eq_one_of_smul_comm_p hn0 α.ne_zero hx3 hBAm
  have hc0 : (c : Kf) ≠ 0 := c.ne_zero
  have hpow1 : ∀ {γ : Kf}, h.bar γ * γ = 1 → γ ^ (ℓ ^ f + 1) = 1 := fun hγ => by
    rw [h.bar_apply, ← pow_succ] at hγ
    exact hγ
  have hαN : h.bar (α : Kf) * α = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) A.2 hx3
  have hβN : h.bar (β : Kf) * β = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) B.2 hy3
  have hpK : p ∣ Nat.card Kf - 1 := dvd_card_sub_one_of_unitary h hpq
  obtain ⟨a, b, hab, ν, hν⟩ := exists_pth_power_word hp hpK α.ne_zero β.ne_zero
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (pow_ne_zero a α.ne_zero) (pow_ne_zero b β.ne_zero)
      (by rw [← hν, zero_pow hp.ne_zero])
  set Y : primeFormUnitary h (idGram Kf n) := A ^ a * B ^ b with hYdef
  have hYm : ((Y : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
      ((A : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) ^ a *
        ((B : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) ^ b := by
    simp only [hYdef, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
  have hYp : (((Y : GL (Fin n) Kf) ^ p : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
      (ν ^ p) • 1 := by
    rw [Units.val_pow_eq_pow_val, hYm, pow_word_p hp hp2 hx3m hy3m hBAm hcp a b, hν]
  have hνN : h.bar ν * ν = 1 := by
    have hYN : h.bar (ν ^ p) * ν ^ p = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) Y.2 hYp
    exact bar_mul_eq_one_of_pow_eq h hp hp2 hpq hν0 rfl (hpow1 hYN)
  have hYE : κ Y ∈ Ē := hwordE a b
  have hY1 : κ Y ≠ 1 := hword1 a b hab
  obtain ⟨X, γ, ζ, hXE, hX1, hXp, hsplit, hYX, hζp, hζc⟩ :
      ∃ (X : primeFormUnitary h (idGram Kf n)) (γ : Kfˣ) (ζ : Kf), κ X ∈ Ē ∧ κ X ≠ 1 ∧
        (((X : GL (Fin n) Kf) ^ p : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
          (γ : Kf) • 1 ∧
        (((∃ μ : Kf, μ ^ p = (α : Kf)) ∧ (∃ μ : Kf, μ ^ p = (β : Kf))) ∨
          ¬ ∃ μ : Kf, μ ^ p = (γ : Kf)) ∧
        ((Y : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
            ((X : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
          ζ • (((X : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) *
            ((Y : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf)) ∧
        ((c : Kf) ≠ 1 → IsPrimitiveRoot ζ p) ∧ ((c : Kf) = 1 → ζ = 1) := by
    by_cases hpb : p ∣ b
    · have hpa : ¬ p ∣ a := fun h1 => hab ⟨h1, hpb⟩
      refine ⟨B, β, ((c : Kf) ^ a)⁻¹, he₂, he₂1, hy3, ?_, ?_, fun hc1 => ?_, fun hc1 => ?_⟩
      · by_cases hboth : (∃ μ : Kf, μ ^ p = (α : Kf)) ∧ (∃ μ : Kf, μ ^ p = (β : Kf))
        · exact Or.inl hboth
        · refine Or.inr ?_
          rintro ⟨μ, hμ⟩
          obtain ⟨k, hk⟩ := hpb
          have hne : ((β : Kf) ^ k) ^ p ≠ 0 := pow_ne_zero _ (pow_ne_zero _ β.ne_zero)
          have hαa : (α : Kf) ^ a = (ν * ((β : Kf) ^ k)⁻¹) ^ p := by
            rw [mul_pow, inv_pow, hν, hk, pow_mul', mul_inv_cancel_right₀ hne]
          exact hboth ⟨pth_power_of_pow_coprime hp α.ne_zero hpa hαa, ⟨μ, hμ⟩⟩
      · rw [hYm, word_comm_right hBAm a b, smul_smul, inv_mul_cancel₀ (pow_ne_zero a hc0),
          one_smul]
      · have hprim : IsPrimitiveRoot (c : Kf) p :=
          isPrimitiveRoot_of_pow_eq_one_ne_one hp hcp hc1
        have hcop : Nat.Coprime a p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa).symm
        exact (hprim.pow_of_coprime a hcop).inv
      · rw [hc1, one_pow, inv_one]
    · refine ⟨A, α, (c : Kf) ^ b, he₁, hA1, hx3, ?_, ?_, fun hc1 => ?_, fun hc1 => ?_⟩
      · by_cases hboth : (∃ μ : Kf, μ ^ p = (α : Kf)) ∧ (∃ μ : Kf, μ ^ p = (β : Kf))
        · exact Or.inl hboth
        · refine Or.inr ?_
          rintro ⟨μ, hμ⟩
          have hne : (μ ^ a) ^ p ≠ 0 := by
            refine pow_ne_zero _ (pow_ne_zero _ ?_)
            rintro rfl
            rw [zero_pow hp.ne_zero] at hμ
            exact α.ne_zero hμ.symm
          have hβb : (β : Kf) ^ b = (ν * (μ ^ a)⁻¹) ^ p := by
            rw [mul_pow, inv_pow, hν, ← pow_mul, mul_comm a p, pow_mul, hμ,
              mul_comm ((α : Kf) ^ a) ((β : Kf) ^ b), mul_assoc,
              mul_inv_cancel₀ (pow_ne_zero a α.ne_zero), mul_one]
          exact hboth ⟨⟨μ, hμ⟩, pth_power_of_pow_coprime hp β.ne_zero hpb hβb⟩
      · rw [hYm]
        exact word_comm_left hBAm a b
      · have hprim : IsPrimitiveRoot (c : Kf) p :=
          isPrimitiveRoot_of_pow_eq_one_ne_one hp hcp hc1
        have hcop : Nat.Coprime b p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpb).symm
        exact hprim.pow_of_coprime b hcop
      · rw [hc1, one_pow]
  have hXpm : ((X : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) ^ p = (γ : Kf) • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hXp
  by_cases hc1 : (c : Kf) = 1
  ·
    have hcu : c = 1 := Units.ext hc1
    have hAB : A * B = B * A := by
      apply Subtype.ext
      change (A : GL (Fin n) Kf) * B = B * A
      rw [hBA, hcu, map_one, one_mul]
    rcases hsplit with ⟨⟨μ, hμ⟩, ⟨μ', hμ'⟩⟩ | hγn
    ·
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hμ
        exact α.ne_zero hμ.symm
      have hμ'0 : μ' ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hμ'
        exact β.ne_zero hμ'.symm
      have hμN : h.bar μ * μ = 1 := bar_mul_eq_one_of_pow_eq h hp hp2 hpq hμ0 hμ (hpow1 hαN)
      have hμ'N : h.bar μ' * μ' = 1 := bar_mul_eq_one_of_pow_eq h hp hp2 hpq hμ'0 hμ' (hpow1 hβN)
      refine closure_liftCent_toral h hn hq2 hp hpq he₁ he₂ hAB hword1 (μ := Units.mk0 μ hμ0)
        (μ' := Units.mk0 μ' hμ'0) hμN hμ'N ?_ ?_
      · rw [hα]
        congr 1
        exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ])
      · rw [hβ]
        congr 1
        exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ'])
    ·
      have hζ1 : ζ = 1 := hζc hc1
      have hXY : (X : GL (Fin n) Kf) * Y = Y * X := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hYX, hζ1, one_smul]
      have hYns : ∀ c' : Kf, ((Y : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) ≠ c' • 1 := by
        intro c' hc'
        obtain ⟨u, hu⟩ := exists_scalarGL_of_coe_eq hn0 hc'
        apply hY1
        refine (OuterUnitaryWide.conjHom_eq_one_iff h hn Y).2 ⟨u, ?_, hu⟩
        have hmem : GeneralLinearGroup.scalar (Fin n) u ∈ primeFormUnitary h (idGram Kf n) :=
          hu ▸ Y.2
        exact norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) 1 hmem
      by_cases hp3 : p = 3
      · subst hp3
        obtain ⟨ζ₃, hζ₃, hζ₃N⟩ := NonPth.exists_primitive_prime_root_bar h hp hpq
        refine closure_liftCent_of_family h ![X, Y]
          (fun i => by fin_cases i; exacts [hXE, hYE]) (fun i => by fin_cases i; exacts [hX1, hY1])
          fun H hH => ?_
        exact NonCube.eq_top_of_noncube_pair h hq2 X.2 Y.2 hXY hXp hγn hYp hν0 hνN hζ₃.pow_eq_one
          (hζ₃.ne_one (by norm_num)) hζ₃N hYns (fun g hg => hH 0 g hg) (fun g hg => hH 1 g hg)
      · have hp5 : 5 ≤ p := by
          have := hp.two_le
          rcases (show p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h3 | h4 | h5
          · exact absurd h3 hp3
          · exact absurd (h4 ▸ hp) (by norm_num)
          · exact h5
        have hνi : h.norm ((Units.mk0 ν hν0)⁻¹ : Kfˣ) = 1 := by
          rw [Units.val_inv_eq_inv_val, Units.val_mk0]
          exact norm_inv_eq_one h hνN
        set Y' : primeFormUnitary h (idGram Kf n) :=
          ⟨GeneralLinearGroup.scalar (Fin n) (Units.mk0 ν hν0)⁻¹, scalar_mem_GU h hνi⟩ * Y with hY'
        have hY'E : κ Y' = κ Y := conjHom_scalar_mul h hn hνi Y
        have hY'm : ((Y' : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) =
            ν⁻¹ • ((Y : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) := by
          rw [hY', Subgroup.coe_mul, Units.val_mul, coe_scalarGL, Matrix.smul_mul, Matrix.one_mul,
            Units.val_inv_eq_inv_val, Units.val_mk0]
        have hXY' : (X : GL (Fin n) Kf) * Y' = Y' * X := by
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, hY'm, Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul,
            ← Units.val_mul, hXY]
        have hY'p : (((Y' : GL (Fin n) Kf) ^ p : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) = 1 := by
          rw [Units.val_pow_eq_pow_val, hY'm, smul_pow, ← Units.val_pow_eq_pow_val, hYp, smul_smul,
            inv_pow, inv_mul_cancel₀ (pow_ne_zero p hν0), one_smul]
        have hY'ns : ∀ c' : Kf, ((Y' : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) ≠ c' • 1 := by
          intro c' hc'
          apply hYns (ν * c')
          rw [hY'm] at hc'
          have h1 := congrArg (fun Z => ν • Z) hc'
          simpa [smul_smul, hν0] using h1
        refine closure_liftCent_of_family h ![X, Y']
          (fun i => by fin_cases i; exacts [hXE, hY'E ▸ hYE])
          (fun i => by fin_cases i; exacts [hX1, hY'E ▸ hY1]) fun H hH => ?_
        exact NonPth.eq_top_of_nonpth_pair h hp hp5 hpq X.2 Y'.2 hXY' hXp hγn hY'p hY'ns
          (hH 0) (hH 1)
  ·
    have hζ : IsPrimitiveRoot ζ p := hζp hc1
    have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
    have hpn : p ∣ n := dvd_of_qcomm hζ hYX
    have hpn' : p ≤ n := Nat.le_of_dvd hn0 hpn
    obtain ⟨-, hXYj⟩ := conjHom_ne_one_of_qcomm h hn (W₀ := Y) (W₁ := X) hζ1 hYX
    have hXYjE : ∀ j : ℕ, κ (X * Y ^ j) ∈ Ē := fun j => by
      rw [map_mul, map_pow]
      exact Ē.mul_mem hXE (Ē.pow_mem hYE j)
    have hXYjm : ∀ j : ℕ, (((X * Y ^ j : primeFormUnitary h (idGram Kf n)) : GL (Fin n) Kf) :
        Matrix (Fin n) (Fin n) Kf) = (((X : GL (Fin n) Kf) * (Y : GL (Fin n) Kf) ^ j :
          GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) := fun j => by
      rw [Subgroup.coe_mul, Subgroup.coe_pow]
    by_cases hp3 : p = 3
    · subst hp3
      by_cases hn3 : n = 3
      · subst hn3
        have hXY1 : κ (X * Y) ≠ 1 := by
          have := hXYj 1
          rwa [pow_one] at this
        exact closure_liftCent_heis_three h hq2 hpq hXE hYE hX1 hY1 hXY1 (hXYj 2) hζ hν0 hνN
          γ.ne_zero hYp hXp hYX
      have hn4 : 4 ≤ n := by omega
      have hζN : h.bar ζ * ζ = 1 := by
        obtain ⟨k, hk⟩ := hpq
        rw [h.bar_apply, ← pow_succ, hk, pow_mul, hζ.pow_eq_one, one_pow]
      have hX0 : κ X ≠ 1 := hX1
      have hXY1E : κ (X * Y) ∈ Ē := by
        have := hXYjE 1
        rwa [pow_one] at this
      have hXY1 : κ (X * Y) ≠ 1 := by
        have := hXYj 1
        rwa [pow_one] at this
      have hXY2E : κ (X * (Y * Y)) ∈ Ē := by
        have := hXYjE 2
        rwa [pow_two] at this
      have hXY2 : κ (X * (Y * Y)) ≠ 1 := by
        have := hXYj 2
        rwa [pow_two] at this
      refine closure_liftCent_of_family h ![Y, X, X * Y, X * (Y * Y)]
        (fun i => by fin_cases i; exacts [hYE, hXE, hXY1E, hXY2E])
        (fun i => by fin_cases i; exacts [hY1, hX0, hXY1, hXY2]) fun H hH => ?_
      exact HeisTensor.eq_top_of_heis_pair h hn4 Y.2 X.2 hζ.pow_eq_one hζ1 hζN hν0 hνN hYp hXp
        hYX (hH 0) (hH 1) (hH 2) (hH 3)
    · have hp5 : 5 ≤ p := by
        have := hp.two_le
        rcases (show p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h3 | h4 | h5
        · exact absurd h3 hp3
        · exact absurd (h4 ▸ hp) (by norm_num)
        · exact h5
      by_cases hnp : n = p ∧ ¬ ∃ μ : Kf, μ ^ p = (γ : Kf)
      · obtain ⟨hnp', hγn⟩ := hnp
        subst hnp'
        refine closure_liftCent_of_family h ![Y, X]
          (fun i => by fin_cases i; exacts [hYE, hXE])
          (fun i => by fin_cases i; exacts [hY1, hX1]) fun H hH => ?_
        exact eq_top_of_heis_pair_prime_nonsplit h (singerTorusGenU_of_prime h hp5 hpq) hp hp5 hpq
          Y.2 X.2 hζ hν0 hνN hγn hYp hXp hYX (hH 0) (hH 1)
      · have hα' : n = p → ∃ μ : Kf, μ ^ p = (γ : Kf) := by
          intro hn'
          by_contra hγ
          exact hnp ⟨hn', hγ⟩
        refine closure_liftCent_of_family h
          (fun i : Option (Fin p) => i.elim Y fun j => X * Y ^ (j : ℕ))
          (fun i => by cases i; exacts [hYE, hXYjE _]) (fun i => by cases i; exacts [hY1, hXYj _])
          fun H hH => ?_
        exact eq_top_of_heis_pair_all_gu h (torusFourierGenU_of_prime h hp5 hpq) hp hp5 hpq hpn'
          Y.2 X.2 hζ hν0 hνN hα' hYp hXp hYX (hH none) fun j hj => hH (some ⟨j, hj⟩)

theorem seitzHyperGamma_eq_top_unitary_diag
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) (h : UnitaryFieldData ℓ f Kf)
    (hn : 3 ≤ n) (hq2 : ℓ ^ f ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    (hq4 : Even n → 4 ≤ ℓ ^ f) (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hD : E.map (QuasiHigh2.modelAut θ) ≤ primeFormD h (idGram Kf n)) :
    seitzHyperGamma p E = ⊤ := by
  classical
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI := h.finite
  haveI : CharP Kf ℓ := h.charP
  have hne : (n, ℓ ^ f) ≠ (3, 2) := fun h' => hq2 (Prod.mk.inj h').2
  have hinj := QuasiHigh2.modelAut_injective hperf θ
  have hĒ : IsElemAbelian p (E.map (QuasiHigh2.modelAut θ)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hĒc : Nat.card (E.map (QuasiHigh2.modelAut θ)) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  obtain ⟨φ, hφ, hφθ⟩ := exists_su_lift hperf h hn hne hq4 θ
  have hcl := closure_liftCent_eq_top h hn hq2 hp hp2 hpq hĒ hĒc hD
  refine seitzHyperGamma_eq_top_of_suModel h hn hne θ φ hφ hφθ hp hE hcard hcl ?_
  rintro g ⟨W, ⟨e, he, heW⟩, hW1, hgW⟩
  refine ⟨e, he, fun h1 => hW1 ?_, (primeFormConjSU h (idGram Kf n) W).toMonoidHom,
    primeFormConjSU_eq_self_of_comm h W hgW, fun g' => ?_⟩
  · rw [← heW, h1, map_one]
  · rw [heW]
    exact primeFormConjHom_piG h W g'

end UPlane

section UField

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.LieType.Chevalley

variable {ℓ f n p : ℕ} {Kf : Type} [Field Kf]

theorem primeFormFieldSU_eq_self_of_mem_suSub (h : UnitaryFieldData ℓ f Kf) {σ : Kf ≃+* Kf}
    {e : ℕ} (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : Kf) = h.bar c) {g : GU1 h n}
    (hg : g ∈ suSub h h₀ hbar n) :
    primeFormFieldSU h (isPrimeFormGram_one (n := n)) σ g = g := by
  obtain ⟨g₀, rfl⟩ := hg
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change σ ((((g₀ : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j :
    fixSubfield σ) : Kf) = (((g₀ : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n)
      (fixSubfield σ)) i j : Kf)
  exact ((((g₀ : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2)

theorem seitzHyperGamma_eq_top_unitary_field
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) (h : UnitaryFieldData ℓ f Kf)
    (hn3 : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hq4 : Even n → 4 ≤ ℓ ^ f) (hq8 : n = 3 → ℓ ^ f ≠ 2 ^ p)
    (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hout : ¬ E.map (QuasiHigh2.modelAut θ) ≤ primeFormD h (idGram Kf n)) :
    seitzHyperGamma p E = ⊤ := by
  classical
  have hfin : Finite Kf := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP Kf ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  have hne' : (n, ℓ ^ f) ≠ (3, 2) := fun h' => hne ⟨(Prod.mk.inj h').1, (Prod.mk.inj h').2⟩
  have hC : IsPrimeFormGram (1 : GL (Fin n) Kf) := isPrimeFormGram_one
  set ι := primeFormFieldFactor h hC hn3 hne with hι
  set κ := primeFormConjHom h ((1 : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf) with hκ
  have hinj := QuasiHigh2.modelAut_injective hperf θ
  obtain ⟨a, haE, haD⟩ : ∃ a ∈ E.map (QuasiHigh2.modelAut θ), a ∉ primeFormD h (idGram Kf n) := by
    by_contra hcon
    push Not at hcon
    exact hout fun a ha => hcon a ha
  have hĒ : IsElemAbelian p (E.map (QuasiHigh2.modelAut θ)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have haι : ι a ≠ 1 := fun h1 => haD (by
    rw [← ker_primeFormFieldFactor h hC hn3 hne]
    exact h1)
  have ha1 : a ≠ 1 := fun h1 => haι (by rw [h1, map_one])
  have hap : a ^ p = 1 := hĒ.2 a haE
  have haord : orderOf a = p := orderOf_eq_prime hap ha1
  have hσp : (ι a) ^ p = 1 := by rw [← map_pow, hap, map_one]
  have hσord : orderOf (ι a) = p := orderOf_eq_prime hσp haι
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne hp hp2 hpℓ a
      haord _ rfl hσord
  set σ := ι a with hσdef
  set θ' : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n) := θ.trans (κ M)⁻¹ with hθ'
  have hlift : ∀ β ∈ (E.map (QuasiHigh2.modelAut θ)).map (MulAut.congr (κ M)⁻¹).toMonoidHom,
      ∃ e ∈ E, QuasiHigh2.modelAut θ' e = β := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, modelAut_trans θ (κ M)⁻¹ e⟩
  set E' := E.map (QuasiHigh2.modelAut θ') with hE'def
  have hE'eq : E' = (E.map (QuasiHigh2.modelAut θ)).map (MulAut.congr (κ M)⁻¹).toMonoidHom := by
    rw [hE'def, Subgroup.map_map]
    congr 1
  have hE'a : IsElemAbelian p E' := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [hE'def, Subgroup.card_map_of_injective (QuasiHigh2.modelAut_injective hperf θ'), hcard]
  set fσ := primeFormFieldHom h hC σ with hfσdef
  have hfσE : fσ ∈ E' := by
    rw [hE'eq]
    refine ⟨a, haE, ?_⟩
    change (κ M)⁻¹ * a * ((κ M)⁻¹)⁻¹ = _
    rw [inv_inv]
    exact hM
  have hισ : ι fσ = σ := by
    have := primeFormFieldFactor_apply h hC hn3 hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ1 : σ ≠ 1 := haι
  have hfσ1 : fσ ≠ 1 := fun h1 => hσ1 (by rw [← hισ, h1, map_one])
  have hfσp : fσ ^ p = 1 := by
    rw [hfσdef, ← map_pow, ← hσord, pow_orderOf_eq_one, map_one]
  have hfσord : orderOf fσ = p := orderOf_eq_prime hfσp hfσ1
  obtain ⟨x₀, hx₀E, hx₀⟩ : ∃ x₀ ∈ E', x₀ ∉ Subgroup.zpowers fσ := by
    by_contra hcon
    push Not at hcon
    have hle : E' ≤ Subgroup.zpowers fσ := fun x hx => hcon x hx
    have hfin' : Finite (Subgroup.zpowers fσ) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hfσord]; exact hp.ne_zero)
    have h1 := Subgroup.card_le_of_le hle
    rw [hE'c, Nat.card_zpowers, hfσord] at h1
    nlinarith [hp.two_le]
  have hτp : (ι x₀) ^ p = 1 := by rw [← map_pow, hE'a.2 x₀ hx₀E, map_one]
  have hKcard : Nat.card Kf = ℓ ^ (2 * f) := h.card
  have hcyc : IsCyclic (Kf ≃+* Kf) :=
    isCyclic_ringEquiv_of_card h.prime (by have := h.one_le; omega) hKcard
  have hfinAut : Finite (Kf ≃+* Kf) := Finite.of_injective _ DFunLike.coe_injective
  have hτ : ι x₀ ∈ Subgroup.zpowers σ := OuterSUField.mem_zpowers_of_pow_eq_one hp hσord hτp
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hτ
  set b := x₀ * (fσ ^ j)⁻¹ with hbdef
  have hbE : b ∈ E' := E'.mul_mem hx₀E (E'.inv_mem (zpow_mem hfσE j))
  have hιb : ι b = 1 := by
    rw [hbdef, map_mul, map_inv, map_zpow, hισ, hj, mul_inv_cancel]
  have hb1 : b ≠ 1 := by
    intro h1
    apply hx₀
    rw [mul_inv_eq_one.mp h1]
    exact Subgroup.zpow_mem_zpowers _ _
  have ha'E : b * fσ ∈ E' := E'.mul_mem hbE hfσE
  have ha'ι : ι (b * fσ) = σ := by rw [map_mul, hιb, one_mul, hισ]
  have ha'1 : b * fσ ≠ 1 := fun h1 => hσ1 (by rw [← ha'ι, h1, map_one])
  have ha'ord : orderOf (b * fσ) = p := orderOf_eq_prime (hE'a.2 _ ha'E) ha'1
  obtain ⟨-, -, -, -, -, M', hM'⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne hp hp2 hpℓ
      (b * fσ) ha'ord σ ha'ι hσord
  have h₀ : UnitaryFieldData ℓ (f / p) (fixSubfield σ) :=
    fixSubfield_unitaryFieldData h hp hp2 hσord
  have hbar : ∀ c : fixSubfield σ, (h₀.bar c : Kf) = h.bar c :=
    fixSubfield_unitaryFieldData_bar h hp hp2 hσord
  have hpf : p ∣ f := (dvd_and_card_fixSubfield_unitary h hp hp2 hσord).1
  have hfeq : f = p * (f / p) := (Nat.mul_div_cancel' hpf).symm
  have hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := by
    rintro ⟨hn3', h2⟩
    obtain ⟨hℓ2, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 h2
    apply hq8 hn3'
    rw [hfeq, hf1, mul_one, hℓ2]
  set Q := QuotientGroup.mk' (normOneScalars h
    (gramSU h ((1 : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf)) n) with hQ
  have hFmk : (subfieldPSU h h₀ hbar n).range = (suSub h h₀ hbar n).map Q :=
    range_subfieldPSU_eq_map h h₀ hbar n
  have hfixF : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, fσ x = x := fun x hx =>
    range_subfieldPSU_le h n h₀ hbar hx
  have hconj : (κ M')⁻¹ * (b * fσ) * κ M' = fσ := hM'
  have hconj' : (b * fσ) * κ M' = κ M' * fσ := by
    calc (b * fσ) * κ M' = κ M' * ((κ M')⁻¹ * (b * fσ) * κ M') := by group
      _ = κ M' * fσ := by rw [hconj]
  have hne'' : (suSub h h₀ hbar n).map (primeFormConjSU h _ M').toMonoidHom ≠
      suSub h h₀ hbar n := by
    intro heq
    have hFmap : ((subfieldPSU h h₀ hbar n).range).map (κ M').toMonoidHom =
        (subfieldPSU h h₀ hbar n).range := by
      rw [hFmk, map_primeFormConjHom_map_mk h h₀ hbar n M', heq]
    have hfix' : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, (b * fσ) x = x := by
      intro x hx
      have hx' : x ∈ ((subfieldPSU h h₀ hbar n).range).map (κ M').toMonoidHom := by
        rw [hFmap]
        exact hx
      obtain ⟨y, hy, rfl⟩ := hx'
      change (b * fσ) (κ M' y) = κ M' y
      rw [show (b * fσ) (κ M' y) = (b * fσ * κ M') y from rfl, hconj', MulAut.mul_apply,
        hfixF y hy]
    have hβ : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, b x = x := by
      intro x hx
      have h3 : (b * fσ) x = b (fσ x) := rfl
      rw [hfixF x hx] at h3
      rw [← h3]
      exact hfix' x hx
    obtain ⟨τ, -, hτ⟩ := eq_primeFormFieldHom_of_fix h n h₀ hbar hn3 hne hq₀ b hβ
    have hτ1 : τ = 1 := by
      have e1 := primeFormFieldFactor_apply h hC hn3 hne 1 τ
      rw [map_one, one_mul] at e1
      rw [← e1, ← hτ]
      exact hιb
    apply hb1
    rw [hτ, hτ1, map_one]
  have hgen : Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
        ((1 : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf))) ∪
      ((suSub h h₀ hbar n).map (primeFormConjSU h _ M').toMonoidHom : Set (gramSU h
        ((1 : GL (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf)))) = ⊤ := by
    by_cases hq2 : ℓ ^ (f / p) = 2
    · have hn4 : 4 ≤ n := by
        by_contra h4
        exact hq₀ ⟨by omega, hq2⟩
      obtain ⟨hℓ2, hf₀1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hq2
      subst hℓ2
      exact CFSG.RankThree.PartOne.SEITZ5.subfieldPairSUF2Odd_of_four_le hn4 f (f / p) Kf h
        (fixSubfield σ) h₀ hbar p hp hp2 hfeq hf₀1 M' hne''
    · exact subfieldPairSUOdd_of_ne_two ℓ f (f / p) Kf h (fixSubfield σ) h₀ hbar p hp hp2 hfeq hq2
        n hn3 M' hne''
  obtain ⟨φ, hφ, hφθ⟩ := exists_su_lift hperf h hn3 hne' hq4 θ'
  obtain ⟨e₁, he₁, he₁σ⟩ : ∃ e ∈ E, QuasiHigh2.modelAut θ' e = fσ := hfσE
  obtain ⟨e₂, he₂, he₂b⟩ : ∃ e ∈ E, QuasiHigh2.modelAut θ' e = b * fσ := ha'E
  have he₁1 : e₁ ≠ 1 := fun h1 => hfσ1 (by rw [← he₁σ, h1, map_one])
  have he₂1 : e₂ ≠ 1 := fun h1 => ha'1 (by rw [← he₂b, h1, map_one])
  have hbf : b * fσ = κ M' * fσ * (κ M')⁻¹ := by
    rw [← hconj']
    group
  have hκinv : ∀ g' : GU1 h n, (κ M')⁻¹ (piG h n g') =
      piG h n ((primeFormConjSU h _ M').symm g') := by
    intro g'
    change (κ M').symm (piG h n g') = _
    rw [MulEquiv.symm_apply_eq, primeFormConjHom_piG, MulEquiv.apply_symm_apply]
  refine seitzHyperGamma_eq_top_of_suModel h hn3 hne' θ' φ hφ hφθ hp hE hcard hgen ?_
  rintro g (hg | ⟨g₀, hg₀, rfl⟩)
  · refine ⟨e₁, he₁, he₁1, (primeFormFieldSU h hC σ).toMonoidHom,
      primeFormFieldSU_eq_self_of_mem_suSub h h₀ hbar hg, fun g' => ?_⟩
    rw [he₁σ]
    exact primeFormFieldAut_mk h hC σ g'
  · refine ⟨e₂, he₂, he₂1, (primeFormConjSU h _ M').toMonoidHom.comp
      ((primeFormFieldSU h hC σ).toMonoidHom.comp (primeFormConjSU h _ M').symm.toMonoidHom),
      ?_, fun g' => ?_⟩
    · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.symm_apply_apply]
      rw [primeFormFieldSU_eq_self_of_mem_suSub h h₀ hbar hg₀]
    · rw [he₂b, hbf, MulAut.mul_apply, MulAut.mul_apply, hκinv]
      have h1 : fσ (piG h n ((primeFormConjSU h _ M').symm g')) =
          piG h n (primeFormFieldSU h hC σ ((primeFormConjSU h _ M').symm g')) :=
        primeFormFieldAut_mk h hC σ _
      rw [h1, primeFormConjHom_piG]
      rfl

end UField

section UAssembly

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

variable {ℓ f n : ℕ} {Kf : Type} [Field Kf]

theorem map_modelAut_le_primeFormD_of_inner {K : Type*} [Group K] (h : UnitaryFieldData ℓ f Kf)
    (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf n)) {E : Subgroup (MulAut K)}
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range) :
    E.map (QuasiHigh2.modelAut θ) ≤ primeFormD h (idGram Kf n) := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨k, rfl⟩ := hinn hg
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective
    (normOneScalars h (gramSU h (idGram Kf n)) n) (θ (k : K ⧸ Subgroup.center K))
  refine ⟨⟨(s : GL (Fin n) Kf), s.2.1⟩, ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H t =>
    rw [primeFormConjHom_mk, QuasiHigh2.modelAut_apply, QuasiHigh.quotAut_conj, map_mul, map_mul,
      map_inv, MulEquiv.apply_symm_apply, ← hs]
    rfl

theorem excIndex_twistedA_two {m : ℕ} {q : TauCeti.PrimePower} (hq : q.card = 2)
    (h3 : 3 ∣ m + 1) (hm : m ≠ 2) :
    ExcIndex 3 (.twistedA m q) ∧ ¬ IsSixIndex (.twistedA m q) := by
  have hq1 : IsTwoPow q 1 :=
    (Nat.Prime.pow_eq_iff Nat.prime_two).1 (by rw [← TauCeti.PrimePower.card_def]; exact hq)
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := h3
    rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
    · exact Or.inl ⟨rfl, Or.inr ⟨hq1, by omega⟩⟩
    · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨Or.inl hq1, k, hk3, hk⟩)⟩
  · rintro (h | h | h)
    · exact h
    · exact h
    · have h3' : q.exponent = 3 := h.1.2
      have h1' : q.exponent = 1 := hq1.2
      omega

theorem isSixIndex_twistedA_eight {q : TauCeti.PrimePower} (hq : q.card = 8) :
    IsSixIndex (.twistedA 2 q) := by
  have hq' : q.p ^ q.exponent = 2 ^ 3 := by rw [← TauCeti.PrimePower.card_def, hq]; norm_num
  have hp2 : q.p = 2 := by
    have h1 : q.p ∣ 2 ^ 3 := hq' ▸ dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow h1)
  have he : q.exponent = 3 := by
    rw [hp2] at hq'
    exact Nat.pow_right_injective (le_refl 2) hq'
  exact Or.inr (Or.inr ⟨⟨hp2, he⟩, Or.inl rfl⟩)

theorem seitzHyperGamma_eq_top_unitary
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {m : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA m q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group)
    (hpq : p ≠ q.p) (hci : CoverIndex p (.twistedA m q)) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hex : ¬ ExcIndex p (.twistedA m q) ∨
      (IsSixIndex (.twistedA m q) ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) :
    seitzHyperGamma p E = ⊤ := by
  classical
  obtain ⟨hℓ, hf, hn3, hne, Kf, _, hU, ⟨θ'⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv e)
  haveI := hU.finite
  haveI : Fact q.p.Prime := ⟨hℓ⟩
  haveI : CharP Kf q.p := hU.charP
  have hqcard : q.p ^ q.exponent = q.card := (TauCeti.PrimePower.card_def q).symm
  have hpq1 : p ∣ q.p ^ q.exponent + 1 := by
    rw [hqcard]
    exact hci.2
  have hpm : p ∣ m + 1 := hci.1
  have hq2 : q.p ^ q.exponent ≠ 2 := by
    intro h2
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by
      rw [h2] at hpq1
      exact hpq1)
    subst hp3
    have hm2 : m ≠ 2 := fun hm => hne ⟨by omega, h2⟩
    obtain ⟨hX, hS⟩ := excIndex_twistedA_two (by rw [← hqcard]; exact h2) hpm hm2
    rcases hex with h1 | h1
    · exact h1 hX
    · exact hS h1.1
  have hq4 : Even (m + 1) → 4 ≤ q.p ^ q.exponent := by
    intro _
    have h2 : 2 ≤ q.p ^ q.exponent :=
      le_trans hℓ.two_le (Nat.le_self_pow q.exponent_pos.ne' q.p)
    have h3 : q.p ^ q.exponent ≠ 3 := by
      intro h3
      rw [h3] at hpq1
      have : p ∣ 2 ^ 2 := by norm_num; exact hpq1
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
    omega
  by_cases hD : E.map (QuasiHigh2.modelAut θ') ≤ primeFormD hU (idGram Kf (m + 1))
  · exact seitzHyperGamma_eq_top_unitary_diag hperf hU hn3 hq2 hp hp2 hpq1 hq4 θ' hE hcard hD
  · refine seitzHyperGamma_eq_top_unitary_field hperf hU hn3 hne hp hp2 hpq hq4 ?_ θ' hE hcard hD
    intro hm3 h8
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hm3 ▸ hpm)
    subst hp3
    have hm2 : m = 2 := by omega
    subst hm2
    have hsix : IsSixIndex (.twistedA 2 q) := isSixIndex_twistedA_eight (by
      rw [← hqcard, h8]
      norm_num)
    rcases hex with h1 | h1
    · exact h1 (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr hsix)))⟩)
    · exact hD (map_modelAut_le_primeFormD_of_inner hU θ' h1.2)

end UAssembly

@[expose] def SeitzCoverFamExcRest2Rest : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) → CoverIndex p d.1 →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 2 →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E → ¬ ExcIsotropic d E →
      ((∃ q, d.1 = TauCeti.LieTypeIndex.E6 q) ∨ (∃ q, d.1 = TauCeti.LieTypeIndex.twistedE6 q)) →
        seitzHyperGamma p E = ⊤

theorem seitzCoverFamExcRest_two_of_rest
    (h : SeitzCoverFamExcRest2Rest) : SeitzCoverFamExcRest 2 := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz hci E hE hcard hex hCS hX
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A m q =>
    obtain ⟨e⟩ := hd
    refine seitzHyperGamma_eq_top_linear hp hp2 hq.1 e (by simpa using hpd) hci ?_ hE hcard
    rintro ⟨rfl, rfl, hq4⟩
    exact hL34 ⟨rfl, CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isLThreeFour_of_index
      ⟨.A 2 q, hv⟩ q rfl (primePower_card_four_aux hq4) e⟩
  | twistedA m q =>
    obtain ⟨e⟩ := hd
    exact seitzHyperGamma_eq_top_unitary hp hp2 hq.1 e (by simpa using hpd) hci hE hcard hex
  | E6 q =>
    exact h p hp hp2 K hq ⟨.E6 q, hv⟩ hd hpd hL34 hz hci E hE hcard hex hCS hX (Or.inl ⟨q, rfl⟩)
  | twistedE6 q =>
    exact h p hp hp2 K hq ⟨.twistedE6 q, hv⟩ hd hpd hL34 hz hci E hE hcard hex hCS hX
      (Or.inr ⟨q, rfl⟩)
  | _ => exact hci.elim

end CFSG.LieType.SeitzGeneration.QuasiHigh5
