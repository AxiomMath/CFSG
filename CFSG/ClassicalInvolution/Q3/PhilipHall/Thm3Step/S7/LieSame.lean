module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoOrbit
public import CFSG.ClassicalInvolution.Q3.Q3EXG2D4Gen
public import CFSG.ClassicalInvolution.Uniform.U3M11
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralD4
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.ClassicalInvolution.Q3.Q3WAComp
public import CFSG.ClassicalInvolution.Q3.LieDecomposition
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectExc
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf18CaseIB
public import CFSG.GH74.GLS.Bg.Rank
public import CFSG.GH74.GLS.IVK.Lifted.GroupAux
public import CFSG.GH74.GLS.IVK.Lifted.IIAutB
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut
public import CFSG.GH74.GLS.IVK.Lifted.Strong
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage1.Main.Basic
public import CFSG.GH74.GLS.Stage1.Main.BrFusedBase
public import CFSG.GH74.GLS.Stage1.Main.BrFusedPair
public import CFSG.GH74.GLS.Stage1.Main.BrG2Base
public import CFSG.GH74.GLS.Stage1.Main.BrIndex
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassA
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassI
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassU
public import CFSG.GH74.GLS.Stage1.Main.II4Proof
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L284
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47c
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafC1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx64
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic25
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Statements
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Arith
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2Three
public import CFSG.GH74.GLS.TwoThin.KGroupCore
public import CFSG.GH74.Generic.S3.B2Tab1
public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GH74.Uniqueness.SU.SU13TA1Class
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.RankThree.PartOne.S10.PlaneContract
public import CFSG.Sporadic.Th.Max3.Packet

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open scoped MatrixGroups

section Conj

variable {G P : Type} [Group G] [Group P]

theorem map_conjSub_hom (ψ : G →* P) (g : G) (R : Subgroup G) :
    (conjSub g R).map ψ = conjSub (ψ g) (R.map ψ) := by
  ext x
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨ψ r, ⟨r, hr, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨g * r * g⁻¹, ⟨r, hr, rfl⟩, by simp⟩

theorem conjInvariant_union_conjClass (A B : Subgroup G) :
    ConjInvariant (CoreAssembly.conjClass A ∪ CoreAssembly.conjClass B) := by
  rintro n _ (⟨g, rfl⟩ | ⟨g, rfl⟩)
  · exact Or.inl ⟨n * g, conjSub_mul n g A⟩
  · exact Or.inr ⟨n * g, conjSub_mul n g B⟩

theorem card_map_of_injOn {ψ : G →* P} {R : Subgroup G} (h : ∀ r ∈ R, ψ r = 1 → r = 1) :
    Nat.card ↥(R.map ψ) = Nat.card R := by
  have hinj : Function.Injective (ψ.comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    exact Subtype.ext (h r r.2 hr)
  have hr : (ψ.comp R.subtype).range = R.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isClassicalMember3_conjSub {Λ : Subgroup G} {w : G} (h : IsClassicalMember3 Λ w)
    (g : G) : IsClassicalMember3 (conjSub g Λ) (g * w * g⁻¹) := by
  have := h.map_mulEquiv (MulAut.conj g)
  rw [MulAut.conj_apply] at this
  exact this

end Conj

section Lie


variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem exists_classical_of_orbitLie (hF : FStarSimple Y) (hΦ : TypeRHyp Φ) {M : Subgroup Y}
    (hM : M ∈ Φ) {z : Y} (hz : IsUniqueInvolution M z)
    (hzH : z ∈ omegaGen (lOrbit (genFittingFStar Y) M))
    (h : OrbitLie ↥(omegaGen (lOrbit (genFittingFStar Y) M))
      (M.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) M))) ⟨z, hzH⟩) :
    Nat.card M = 8 ∧ ∃ (Λ : Subgroup ↥(genFittingFStar Y)) (w : ↥(genFittingFStar Y)),
      (w : Y) = z ∧ M ≤ Λ.map (genFittingFStar Y).subtype ∧ Nat.card Λ = 24 ∧
        IsClassicalMember3 Λ w := by
  obtain ⟨hHL, h8, -⟩ := lie_case hF hΦ hM hz hzH h
  set L := genFittingFStar Y with hL
  set H := omegaGen (lOrbit L M) with hH
  have hMH : M ≤ H := le_omegaGen mem_lOrbit_self
  obtain ⟨c, -, -, φ, -, -, F, -, hMF, h24, hcl⟩ := h
  let e : ↥H ≃* ↥L := MulEquiv.subgroupCongr hHL
  refine ⟨h8, (F.map φ).map e.toMonoidHom, e ⟨z, hzH⟩, rfl, ?_, ?_, hcl.map_mulEquiv e⟩
  · have hmap : ((F.map φ).map e.toMonoidHom).map L.subtype = (F.map φ).map H.subtype := by
      rw [Subgroup.map_map]
      rfl
    rw [hmap]
    have := Subgroup.map_mono (f := H.subtype) hMF
    rwa [Subgroup.map_subgroupOf_eq_of_le hMH] at this
  · rw [Subgroup.card_map_of_injective e.injective, h24]

end Lie

section Fund


@[expose] def TD4ThreeFund24 : Prop :=
  ∀ n : ℕ, CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 n 3 1 →
    ∀ R₁ ∈ (CompData.model .trialityD4 n).fund, ∀ R₂ ∈ (CompData.model .trialityD4 n).fund,
      Nat.card R₁ = 24 → Nat.card R₂ = 24 → ∃ g, R₂ = conjSub g R₁

theorem card_le_card_sl2 (F : Type) [Field F] [Finite F] : Nat.card F ≤ Nat.card SL(2, F) := by
  refine Nat.card_le_card_of_injective (CFSG.LieType.Steinberg.sl2Upper (k := F)) ?_
  intro a b h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [CFSG.LieType.Steinberg.sl2Upper] using this

theorem td4ThreeFund24_proved : TD4ThreeFund24 := by
  intro n hadm R₁ hR₁ R₂ hR₂ h₁ h₂
  set D := (modelUniv .trialityD4 n 3 1 Nat.prime_three).D with hD
  have hB : ModelFacts.HasBruhatDatum D :=
    ModelFacts.hasBruhatDatum .trialityD4 n 3 1 Nat.prime_three trivial hadm
  obtain ⟨_, _, hct, -⟩ := hB
  have key : ∀ R ∈ (CompData.model .trialityD4 n).fund, ∃ (i : Fin D.rank)
      (g : (CompData.model .trialityD4 n).G),
      R = (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).map
        (MulAut.conj g).toMonoidHom := by
    intro R hR
    obtain ⟨g, γ, hγ, rfl⟩ := ModelFacts.mem_roots_of_mem_fundamentalSubgroups (t := .trialityD4)
      (D := D) hR
    obtain ⟨w, i, rfl⟩ : ∃ (w : (CFSG.LieType.RootSystem.coxeterMatrix D.isFiniteType).Group)
        (i : Fin D.rank), γ = CFSG.LieType.RootSystem.weylAction D.isFiniteType w
          (Pi.single i 1) := by
      rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
      · exact ⟨w, i, rfl⟩
      · exact absurd hi (Set.notMem_empty i)
    obtain ⟨g', hg'⟩ := ModelFacts.exists_map_conj_rankOne hct w
    have h1 := hg' (Pi.single i 1) (Or.inl ⟨1, i, by simp⟩)
    refine ⟨i, g * g', ?_⟩
    rw [← h1, ModelFacts.map_conj_map_conj]
  have hK : Nat.card (GaloisField 3 (3 * 1)) = (3 ^ 1) ^ 3 := by
    rw [GaloisField.card 3 (3 * 1) (by norm_num)]
    norm_num
  have hσ : ∀ c : GaloisField 3 (3 * 1),
      iterateFrobenius (GaloisField 3 (3 * 1)) 3 1 (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1
        (iterateFrobenius (GaloisField 3 (3 * 1)) 3 1 c)) = c :=
    CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hK fun c => iterateFrobenius_def 3 1 c
  have hshort : ∀ hi : 1 < D.rank, 27 ≤ Nat.card ↥(D.rootGroup (Pi.single ⟨1, hi⟩ 1) ⊔
      D.rootGroup (-Pi.single ⟨1, hi⟩ 1)) := by
    intro hi
    have hr := ModelFacts.rankOne_short_eq_range hσ
    have h1 : Nat.card ↥(D.rootGroup (Pi.single ⟨1, hi⟩ 1) ⊔ D.rootGroup (-Pi.single ⟨1, hi⟩ 1)) =
        Nat.card SL(2, GaloisField 3 (3 * 1)) := by
      have h1' := congrArg (fun H : Subgroup _ => Nat.card ↥H) hr
      refine h1'.trans ?_
      exact (Nat.card_congr (MonoidHom.ofInjective
        (CFSG.LieType.Steinberg.TwistedD4.slShort_injective hσ)).toEquiv).symm
    have h2 := card_le_card_sl2 (GaloisField 3 (3 * 1))
    rw [GaloisField.card 3 (3 * 1) (by norm_num)] at h2
    rw [h1]
    norm_num at h2 ⊢
    exact h2
  have hlong : ∀ R ∈ (CompData.model .trialityD4 n).fund, Nat.card R = 24 →
      ∃ (hi : 0 < D.rank) (g : (CompData.model .trialityD4 n).G),
        R = (D.rootGroup (Pi.single ⟨0, hi⟩ 1) ⊔
          D.rootGroup (-Pi.single ⟨0, hi⟩ 1)).map (MulAut.conj g).toMonoidHom := by
    intro R hR h24
    obtain ⟨⟨k, hk⟩, g, rfl⟩ := key R hR
    have hk2 : k < 2 := hk
    interval_cases k
    · exact ⟨hk, g, rfl⟩
    · exfalso
      have hc := Subgroup.card_map_of_injective (K := D.rootGroup (Pi.single ⟨1, hk⟩ 1) ⊔
        D.rootGroup (-Pi.single ⟨1, hk⟩ 1)) (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
      have h27 := hshort hk
      have h24' := hc.symm.trans h24
      omega
  obtain ⟨hi₁, g₁, rfl⟩ := hlong R₁ hR₁ h₁
  obtain ⟨hi₂, g₂, rfl⟩ := hlong R₂ hR₂ h₂
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  show _ = Subgroup.map _ _
  rw [ModelFacts.map_conj_map_conj, inv_mul_cancel_right]


theorem modelFacts_isFundTag_of {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    (h : Generic.IsFundTag t) : ModelFacts.IsFundTag t := by
  cases t <;> first | trivial | exact h.elim

theorem exists_conj_of_fund (hD4 : TD4ThreeFund24) {c : CompData} (hV : c.Valid) {P : Type}
    [Group P] (ψ : c.G →* P) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center c.G)
    (hsol : ¬ Group.IsSolvable P) (hG : ¬ CFSG.Blueprint.LieModel P .G2 0 3 1)
    {R₁ R₂ : Subgroup c.G} (h₁ : R₁ ∈ c.fund) (h₂ : R₂ ∈ c.fund)
    (h24₁ : Nat.card ↥(R₁.map ψ) = 24) (h24₂ : Nat.card ↥(R₂.map ψ) = 24) :
    ∃ g : c.G, R₂ = conjSub g R₁ := by
  rcases hV with ⟨t, n, hfund, hadm, rfl⟩ | rfl | rfl
  · by_cases hG2 : t = .G2
    · subst hG2
      exfalso
      have hZ : Subgroup.center (CompData.model .G2 n).G = ⊥ :=
        CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := GaloisField 3 1)
      have hinj : Function.Injective ψ :=
        (MonoidHom.ker_eq_bot_iff ψ).mp (le_bot_iff.mp (hker.trans hZ.le))
      exact hG (CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩)
        (Q3W.EX.lieModel_modelG2 n))
    by_cases hD : t = .trialityD4
    · subst hD
      have hinj : ∀ {R : Subgroup (CompData.model .trialityD4 n).G},
          R ∈ (CompData.model .trialityD4 n).fund → Nat.card ↥(R.map ψ) = Nat.card R := by
        intro R hR
        exact card_map_of_injOn fun r hr h1 => ModelFacts.eq_one_of_mem_center_D4 n 3 1
          Nat.prime_three trivial hadm hR hr (hker h1)
      exact hD4 n hadm R₁ h₁ R₂ h₂ (by rw [← hinj h₁, h24₁]) (by rw [← hinj h₂, h24₂])
    · obtain ⟨g, hg⟩ := ModelFacts.fundamentalSingleClass t n 3 1 Nat.prime_three
        (modelFacts_isFundTag_of hfund) hadm hG2 hD R₁ h₁ R₂ h₂
      exact ⟨g, hg⟩
  · haveI := isSolvable_sl2Three
    exact absurd (Group.isSolvable_of_surjective hψ) hsol
  · exact Uniform.m11_classicalClass_conj h₁ h₂

theorem inClass3_union {X : Type} [Group X] [IsSimpleGroup X] {Λ₁ Λ₂ : Subgroup X} {w₁ w₂ : X}
    (h₁ : IsClassicalMember3 Λ₁ w₁) (h₂ : IsClassicalMember3 Λ₂ w₂) :
    InClass3 (CoreAssembly.conjClass Λ₁ ∪ CoreAssembly.conjClass Λ₂) where
  nonempty := ⟨Λ₁, Or.inl (CoreAssembly.mem_conjClass_self Λ₁)⟩
  conjInvariant := conjInvariant_union_conjClass Λ₁ Λ₂
  generated := by
    have hn := omegaGen_normal (conjInvariant_union_conjClass Λ₁ Λ₂)
    rcases hn.eq_bot_or_eq_top with hb | ht
    · exfalso
      have hle : Λ₁ ≤ omegaGen (CoreAssembly.conjClass Λ₁ ∪ CoreAssembly.conjClass Λ₂) :=
        le_omegaGen (Or.inl (CoreAssembly.mem_conjClass_self Λ₁))
      rw [hb] at hle
      have hw : w₁ = 1 := Subgroup.mem_bot.mp (hle h₁.mem)
      have h2 := h₁.orderOf_eq_two
      rw [hw, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · exact ht
  classical := by
    rintro _ (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact ⟨_, isClassicalMember3_conjSub h₁ g⟩
    · exact ⟨_, isClassicalMember3_conjSub h₂ g⟩

theorem twoLieOrbitsSame_of_cit3 (hD4 : TD4ThreeFund24) : TwoLieOrbitsSame := by
  classical
  intro Y _ _ hcit hO _ hF Φ hΦ K hK J hJ zK zJ hzK hzJ ⟨hzKH, hLK⟩ ⟨hzJH, hLJ⟩ hG
  set L := genFittingFStar Y with hLdef
  haveI : IsSimpleGroup ↥L := hF.1
  haveI hLn : L.Normal := genFittingFStar_normal Y
  have hC := centralizer_eq_bot_of_fStarSimple hF
  obtain ⟨hK8, Λ₁, w₁, -, hKΛ₁, h24₁, hcl₁⟩ := exists_classical_of_orbitLie hF hΦ hK hzK hzKH hLK
  obtain ⟨hJ8, Λ₂, w₂, -, hJΛ₂, h24₂, hcl₂⟩ := exists_classical_of_orbitLie hF hΦ hJ hzJ hzJH hLJ
  set Ψ := CoreAssembly.conjClass Λ₁ ∪ CoreAssembly.conjClass Λ₂ with hΨdef
  have hcard : Nat.card ↥L < Nat.card Y + 1 := Nat.lt_succ_of_le (Subgroup.card_le_card_group L)
  obtain ⟨ι, _, ⟨D₀⟩⟩ := hcit ↥L hcard Ψ (inClass3_union hcl₁ hcl₂)
  have hOL : classicalInvolutionOddCore ↥L = ⊥ := oddCore_eq_bot_of_le hO hLn hC le_rfl
  let e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hOL).trans QuotientGroup.quotientBot
  let D := D₀.congr e
  have hid : ∀ x : ↥L, e (QuotientGroup.mk' (classicalInvolutionOddCore ↥L) x) = x := fun x => rfl
  have hmem : ∀ A ∈ Ψ, A ∈ Subgroup.map e.toMonoidHom '' oddQuotientFamily Ψ := by
    intro A hA
    refine ⟨A.map (QuotientGroup.mk' _), ⟨A, hA, rfl⟩, ?_⟩
    rw [Subgroup.map_map]
    ext x
    simp only [Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, hid]
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  obtain ⟨i₁, R₁, hR₁, hΛR₁⟩ :=
    D.fundamental Λ₁ (hmem _ (Or.inl (CoreAssembly.mem_conjClass_self _)))
  obtain ⟨i₂, R₂, hR₂, hΛR₂⟩ :=
    D.fundamental Λ₂ (hmem _ (Or.inr (CoreAssembly.mem_conjClass_self _)))
  have hrange : ∀ i, (D.hom i).range = ⊤ := by
    intro i
    rcases (Q3W.range_normal3 D i).eq_bot_or_eq_top with hb | ht
    · exfalso
      obtain ⟨R, -, hRm⟩ := D.meets i
      have h24' := D.card_eq _ hRm
      have hRb : R.map (D.hom i) = ⊥ := by
        rw [eq_bot_iff, ← hb]
        exact Subgroup.map_le_range _ _
      rw [hRb, Subgroup.card_bot] at h24'
      norm_num at h24'
    · exact ht
  have hi : i₂ = i₁ := by
    by_contra hne
    obtain ⟨a, b, hab⟩ := hF.2
    exact hab (Q3W.commutes_range3 D hne a (by rw [hrange]; trivial) b (by rw [hrange]; trivial))
  subst hi
  have hsurj : Function.Surjective (D.hom i₂) := MonoidHom.range_eq_top.mp (hrange i₂)
  have hsol : ¬ Group.IsSolvable ↥L := by
    intro hs
    obtain ⟨a, b, hab⟩ := hF.2
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hs a b)
  obtain ⟨g, hg⟩ := exists_conj_of_fund hD4 (D.valid i₂) (D.hom i₂) hsurj (D.ker_le_center i₂)
    hsol hG hR₁ hR₂ (hΛR₁ ▸ h24₁) (hΛR₂ ▸ h24₂)
  set l : ↥L := D.hom i₂ g with hl
  have hΛY : Λ₂.map L.subtype = conjSub (l : Y) (Λ₁.map L.subtype) := by
    rw [hΛR₂, hg, map_conjSub_hom, ← hΛR₁, map_conjSub_hom]
    rfl
  obtain ⟨eΛ⟩ := nonempty_sl23_of_classical hcl₂ h24₂
  let eΛY : ↥(Λ₂.map L.subtype) ≃* SL(2, ZMod 3) :=
    (Λ₂.equivMapOfInjective L.subtype L.subtype_injective).symm.trans eΛ
  have hKl : conjSub (l : Y) K ≤ Λ₂.map L.subtype := by
    rw [hΛY]
    exact Subgroup.map_mono hKΛ₁
  have hKl8 : Nat.card ↥(conjSub (l : Y) K) = 8 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj (l : Y)).injective, hK8]
  exact ⟨l, l.2, (eq_of_card_eight eΛY hJΛ₂ hKl hJ8 hKl8).symm⟩

theorem twoLieOrbitsSame_proved : TwoLieOrbitsSame :=
  twoLieOrbitsSame_of_cit3 td4ThreeFund24_proved

end Fund

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
