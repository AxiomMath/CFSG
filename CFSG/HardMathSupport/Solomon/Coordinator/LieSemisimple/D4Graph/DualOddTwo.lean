module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualOddOne

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
  (un_final_T eq_bot_or_isSolvable_quotient_of_equiv)


section CoreT

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

include hφ in
theorem A2Core.un_polarity_core_T {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hq : q = (p ^ f) ^ 4) (ε : K ≃+* K) (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (hcommε : ∀ y, fieldActor (t := TwistTag.D4) σ (ε * ε) (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ (ε * ε) y)) :
    ∀ (A : Subgroup ↥(foldFix (unTauX h φ ε hcomm))) [A.Normal],
      A = ⊥ ∨ Group.IsSolvable (↥(foldFix (unTauX h φ ε hcomm)) ⧸ A) := by
  have hσ' : ∀ c, σ c = c ^ ((p ^ f) ^ 4) := fun c => by rw [h.frob c, hq]
  have hK : Nat.card K = ((p ^ f) ^ 4) ^ 3 := by rw [h.card, hq]
  have hεσ : ∀ c, ε (σ c) = σ (ε c) := un_eps_sigma hσ' hε
  have hε4 : ∀ c, ε (ε (ε (ε c))) = c := un_eps_four hK hε
  have : CharP (UnK σ) p := un_charP_unK σ
  have hk : Nat.card (UnK σ) = (p ^ f) ^ 4 := un_card_unK hf hK hσ'
  have hεk : ∀ a : UnK σ, unEps ε hεσ a = a ^ (p ^ f) := un_eps_frob hσ' hε hεσ
  have hεε : ∀ c, (ε * ε) (σ c) = σ ((ε * ε) c) := fun c => by
    show ε (ε (σ c)) = σ (ε (ε c))
    rw [hεσ, hεσ]
  obtain ⟨n₁, n₂, hn₁, hn₂, hn₁', -⟩ := (unD_spec h φ hφ).lifts
  have hn₁X : (n₁ : ↥(foldFix (a2Phi h φ))) = unSlFix h φ hφ unSL2W :=
    Subtype.ext (hn₁'.trans (unSlFix_w h φ hφ).symm)
  obtain ⟨κ, hκ⟩ := unRho_tau h φ hφ hn₂ ε hεσ hcomm
  have hτ := un_isOpposition h φ hφ ε hεσ hcomm
  have hτe := un_tauX_tauX h φ ε hcomm hcommε
  have hBsolv : Group.IsSolvable ↥(unD h φ hφ).B := by
    haveI := (d4RGD2 σ.toRingHom h.cube_apply).isSolvable_B
    let f₀ : ↥(unD h φ hφ).B →*
        ↥((⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))) :=
      ((foldFix (a2Phi h φ)).subtype.comp (unD h φ hφ).B.subtype).codRestrict _
        (fun x => ((unD_spec h φ hφ).B x.1).1 x.2)
    exact solvable_of_solvable_injective (f := f₀) fun a b hab => by
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
  refine un_final_T hp2 (by omega) (unD h φ hφ) hBsolv (unTauX h φ ε hcomm)
    (unFieldX h φ (ε * ε) hcommε) hτ hτe
    (fun b hb => by rw [← hτe b]; exact hτ.tau_sq_mem_B hb)
    (un_tauX_four h φ ε hε4 hcomm) hk (unEps ε hεσ) hεk (unRho h φ hφ n₂)
    (unRho_injective h φ hφ n₂) κ (fun a => (hκ a).1) (fun a => (hκ a).2)
    (unRho_upper_mem h φ hφ hn₂) (fun y hy => unRho_upper_surj h φ hφ hn₂ hy)
    (unRho_lower_mem h φ hφ hn₂) (unRho_N h φ hφ hn₂ hn₁ hn₁X) (unRho_H h φ hφ hn₂)
    (unX1 h φ hφ) (unX1_injective h φ hφ) (unX1_mem h φ hφ) (fun y hy => unX1_surj h φ hφ hy)
    (unX1_torus h φ hφ) ?_ (un_hab h φ hφ (Or.inl rfl)) (un_hab h φ hφ (Or.inr rfl))
    (un_hTor h φ hφ) (un_chat_X h φ hφ ε hεσ hcomm)
  intro a
  rw [unX1_field h φ hφ (ε * ε) hεε hcommε a, unEps_mul ε ε hεσ hεσ hεε a]


end CoreT

section PolarityT

theorem un_polarity_T {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2)
    {K₄ : Type} [Field K₄] [Finite K₄] [CharP K₄ p] (hK₄ : Nat.card K₄ = ((p ^ f) ^ 4) ^ 3)
    (σ₄ ε : K₄ ≃+* K₄) (hσ₄ : ∀ c, σ₄ c = c ^ ((p ^ f) ^ 4))
    (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) (b : K₄ˣ) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (s₄ : graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)
    (hs₄ : (s₄ : ModGL TwistTag.D4.tag K₄) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1]) :
    ∀ (F₀ : Subgroup ↥(foldFix (((MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄ :
        MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ⊓
        foldFix ((unTau σ₄ ε : MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _))) [F₀.Normal],
      F₀ = ⊥ ∨ Group.IsSolvable (↥(foldFix (((MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄ :
        MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ⊓
        foldFix ((unTau σ₄ ε : MulAut (graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom)) :
        graphFixedRootGroup TwistTag.D4 K₄ σ₄.toRingHom ≃* _)) ⧸ F₀) := by
  have hA : A2Std σ₄ b ((p ^ f) ^ 4) := un_a2Std hp2 hf hq hK₄ hσ₄ hb3 hb1
  have hεσ : ∀ c, ε (σ₄ c) = σ₄ (ε c) := un_eps_sigma hσ₄ hε
  have hεε : ∀ c, (ε * ε) (σ₄ c) = σ₄ ((ε * ε) c) := fun c => by
    show ε (ε (σ₄ c)) = σ₄ (ε (ε c))
    rw [hεσ, hεσ]
  have hφ₄ := a2_hφ_of_class (σ := σ₄) (d := b) hs₄
  have hcomm := unTau_comm_phi σ₄ ε (fun c => (hεσ c).symm) b (un_eps_unit hq hε hb3) s₄ hs₄
  have hcommε := unField_comm_phi σ₄ (ε * ε) hεε b (un_eps_sq_unit hq hε hb3) s₄ hs₄
  have hNo := A2Core.un_polarity_core_T hA.toCore _ hφ₄ hp2 hf rfl ε hε hcomm hcommε
  obtain ⟨e, -⟩ := un_fixfix_equiv hA _ ε hcomm
  exact eq_bot_or_isSolvable_quotient_of_equiv e hNo


end PolarityT

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Matrix MatrixGroups


set_option linter.unusedSectionVars false

theorem d4OuterThreeA2Minus_T {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hs : D4MinusToral p f hp K σ s) :
    ∀ (N : Subgroup ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)))
      [N.Normal], N = ⊥ ∨ Group.IsSolvable
        (↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) ⧸ N) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₄, hF, hfin, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame hp hf hq K hK σ hσ s hs
  have hT := un_polarity_T hp2 hf hq hK₄ σ₄ ε hσ₄ hε b hb3 hb1 s₄ hs₄
  obtain ⟨e, -⟩ := un_fixSub_equiv (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
    (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (unTau σ₄ ε) ψ₄ hinj hint hfix
  have hT' := eq_bot_or_isSolvable_quotient_of_equiv e.symm hT
  exact eq_bot_or_isSolvable_quotient_of_equiv
    (MulEquiv.subgroupCongr (fixSub_eq_fixSubgroup _)) hT'

section EllMinus

theorem minusEll_conj_toral (h : RotLang) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hn : D4MinusElliptic p f hp K σ n)
    (hN : normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1) :
    ∃ y₀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, D4MinusToral p f hp K σ s ∧
      MulAut.conj y₀ * (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) *
        (MulAut.conj y₀)⁻¹ = MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ := by
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h2 := hp.two_le
    have : p = 4 := by omega
    subst this
    norm_num at hp
  obtain ⟨L, _, _, _, _, g₀, hg₀, hnM, hnT⟩ := hn
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := id hg₀
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm := d4Minus_hcomm hσ Fr hFr
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega : f ≠ 0) p)
  set δ := fieldActor (t := TwistTag.D4) σ σ with hδ
  set ψ := d4MinusPsi σ L g₀ with hψdef
  have hn'M : ψ n ∈ monomialSubgroup TwistTag.D4.tag L := by
    rw [hψdef, d4MinusPsi_apply]
    exact hnM
  have hn'T : ψ n ∉ torusGroup TwistTag.D4.tag L := by
    rw [hψdef, d4MinusPsi_apply]
    exact hnT
  have hn'F : trialityOpposition L * twistHom TwistTag.D4 L Fr (ψ n) *
      (trialityOpposition L)⁻¹ = ψ n :=
    ((d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F (ψ n)).1 ⟨n, rfl⟩).2
  have hFn : twistHomOppHom Fr (ψ n) = ψ n := by
    rw [twistHomOppHom_apply]
    exact hn'F
  have hψ : ∀ u, ψ (δ u) = (diagramMap TwistTag.D4 L)⁻¹ * ψ u * diagramMap TwistTag.D4 L :=
    fun u => d4MinusPsi_fieldActor Fr hcomm hg₀P u
  have hN3 : n * δ n * δ (δ n) = 1 := by rw [← normSeq_three]; exact hN
  have hcyc : ψ n * ((diagramMap TwistTag.D4 L)⁻¹ * ψ n * diagramMap TwistTag.D4 L) *
      ((diagramMap TwistTag.D4 L)⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * ψ n *
        diagramMap TwistTag.D4 L) * diagramMap TwistTag.D4 L) = 1 := by
    have e1 := hψ n
    have e2 := hψ (δ n)
    have := congrArg ψ hN3
    rw [map_mul, map_mul, map_one, e2, e1] at this
    exact this
  have hx3 := cube_of_cocycle hcyc
  have hw : weylQuotientHom TwistTag.D4.tag L ⟨ψ n, hn'M⟩ ∈ relWeylTwist TwistTag.D4 :=
    weyl_mem_rel_of hn'M fun k w hk hxe => d4MnFL_relWeylTwist_of_fixed Fr hk hxe hn'F
  have hA := exists_cube_root_unit (L := L) (three_ne_zero_of_charP hp hp3)
  have he3 : (-((p ^ f : ℕ) : ℤ)) % 3 = 1 := by
    generalize p ^ f = q at hq ⊢
    omega
  obtain ⟨b, hb3, hb1, y, hyG, hyF, hy⟩ := ell_main_L (ellFrame_two f hq2) he3 hn'M hn'T hw hx3
    hFn hA (fun b hb3 hb1 ζ hζ h1 h2 => by
      obtain ⟨z, hz, hzeq⟩ := (h p f hp5 hf L b hb3 hb1 ζ hζ h1 h2).2 hq
      exact ⟨z, hz, by rw [twistHomOppHom_apply]; exact hzeq⟩)
  have hyr : y ∈ ψ.range := by
    rw [hψdef]
    refine (d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F y).2 ⟨hyG, ?_⟩
    have := hyF
    rw [twistHomOppHom_apply] at this
    exact this
  obtain ⟨y₀, rfl⟩ := hyr
  have hs := ell_psi_toral δ ψ hψ y₀ n b hy
  set s := y₀ * n * (δ y₀)⁻¹ with hsdef
  have hsT : D4MinusToral p f hp K σ s := by
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, g₀, b, hg₀, hb3, hb1, ?_⟩
    have h1 := hs
    rw [hψdef, d4MinusPsi_apply] at h1
    calc triEmb K σ L s = g₀ * (g₀⁻¹ * triEmb K σ L s * g₀) * g₀⁻¹ := by group
      _ = _ := by rw [h1]; rfl
  exact ⟨y₀, s, hsT, conj_twist_eq δ y₀ n⟩

end EllMinus

section Odd2

theorem perfectInLayer_minusToral {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hs : D4MinusToral p f hp K σ s) :
    PerfectInLayer (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := by
  haveI : Finite ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) :=
    inferInstance
  refine perfectInLayer_of_noAbel_of_solvable_quotient _ ?_ ?_
  · intro N hN hc
    have hOut := d4OuterThreeA2Minus_thm p f hp hp2 hp3 hf hq K hK σ hσ s hs
    unfold D4Out at hOut
    exact hOut.1 N hN (fun x y => Subtype.ext (hc x.1 x.2 y.1 y.2))
  · intro N _
    exact d4OuterThreeA2Minus_T hp hp2 hf hq hK σ hσ s hs N

theorem outer_three_odd_two {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2)
    {K₃ : Type} [Field K₃] [Finite K₃] (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    PerfectInLayer φ := by
  have hp : ℓ.Prime := Fact.out
  have hp2 : ℓ ≠ 2 := by omega
  have hp3 : ℓ ≠ 3 := by omega
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [h]; exact map_one _⟩
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot Fr.surjective
  have hψ3 := d4_fieldActor_pow_three K₃ hK₃ Fr hFr
  have hG2 : PerfectInLayer (fieldActor (t := TwistTag.D4) Fr Fr) := by
    have hK3 : Nat.card K₃ = ℓ ^ (3 * f) := by rw [hK₃, ← pow_mul, mul_comm]
    have : CharP K₃ ℓ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3
    exact perfectInLayer_fieldActor hp2 Fr (ringEquiv_cube_apply_eq hK₃ hFr)
  have hTor : ∀ s, D4MinusToral ℓ f hp K₃ Fr s →
      PerfectInLayer (MulAut.conj s * fieldActor (t := TwistTag.D4) Fr Fr) := fun s hs =>
    perfectInLayer_minusToral hp hp2 hp3 hf hq hK₃ Fr hFr s hs
  rcases d4Minus_outer_three_nf hp hp2 hp3 hf hq K₃ hK₃ Fr hFr φ hφord hφ with
    ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ | ⟨y, n, hn, hyn⟩
  · rcases hy with hy | hy
    · exact perfectInLayer_of_conj_eq y hy hG2
    · exact perfectInLayer_of_conj_eq y hy ((perfectInLayer_inv_iff _).2 hG2)
  · rcases hys with hys | hys
    · exact perfectInLayer_of_conj_eq y hys (hTor s hs)
    · exact perfectInLayer_of_conj_eq y hys ((perfectInLayer_inv_iff _).2 (hTor s hs))
  · have hc := pow_three_of_conj_eq y hφ3 hyn
    have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hc
    obtain ⟨y₀, s, hsT, hconj⟩ :=
      minusEll_conj_toral rotLang_holds hp hp2 hp3 hf hq hK₃ Fr hFr n hn hN
    have hPL := perfectInLayer_of_conj_eq y₀ hconj (hTor s hsT)
    rcases hyn with hyn | hyn
    · exact perfectInLayer_of_conj_eq y hyn hPL
    · exact perfectInLayer_of_conj_eq y hyn ((perfectInLayer_inv_iff _).2 hPL)

end Odd2

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
