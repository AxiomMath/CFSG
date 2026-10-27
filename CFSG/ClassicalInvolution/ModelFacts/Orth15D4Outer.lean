module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Lift
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Inner

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ComponentClassification.CatalogueBHigherLinearField Matrix
open scoped MatrixGroups commutatorElement

section Residual

variable (p f : ℕ) [Fact p.Prime]

@[expose] def D4FixLift : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (fr : Frame (quadPlus 4 (GaloisField p f)))
      (α : spinGroup (quadPlus 4 (GaloisField p f)) ≃* spinGroup (quadPlus 4 (GaloisField p f))),
      (∀ g ∈ ⁅(fr.La.range ⊔ fr.swap.La.range).comap (spinAction (quadPlus 4 (GaloisField p f))),
        (fr.La.range ⊔ fr.swap.La.range).comap (spinAction (quadPlus 4 (GaloisField p f)))⁆,
          α g = g) →
      ∃ (A : GL (Fin 4 ⊕ Fin 4) (GaloisField p f)) (φ : GaloisField p f ≃+* GaloisField p f)
        (μ : (GaloisField p f)ˣ),
        (∀ v : Fin 4 ⊕ Fin 4 → GaloisField p f,
          quadPlus 4 (GaloisField p f) (A.val *ᵥ (fun i => φ (v i))) =
            μ * φ (quadPlus 4 (GaloisField p f) v)) ∧
        ∀ x, spinMatrix (quadPlus 4 (GaloisField p f)) (α x) =
          A * glFieldEquiv (Fin 4 ⊕ Fin 4) φ (spinMatrix (quadPlus 4 (GaloisField p f)) x) * A⁻¹

end Residual

section Lift

variable {p f : ℕ} [Fact p.Prime]

theorem liftSimFr_of_d4FixLift (hfl : D4FixLift p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {H : Type}
    [Group H] (ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f)))) :
    LiftSimFr (quadPlus 4 (GaloisField p f)) ψ := by
  intro fr σ hσ
  have hn3 : 3 ≤ 4 := by norm_num
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) :=
    isPerfect_spinGroup_quadPlus hn3
  have : NeZero 4 := ⟨by norm_num⟩
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have hfin : Finite (spinGroup (quadPlus 4 (GaloisField p f))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hC : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f)))) :=
    not_dvd_card_center_plus hp2 hn3
  have hθker : ψ.rangeRestrict.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) :=
    by rwa [MonoidHom.ker_rangeRestrict]
  have hθC : ¬ p ∣ Nat.card ψ.rangeRestrict.ker := fun hd =>
    hC (hd.trans (Subgroup.card_dvd_of_le hθker))
  obtain ⟨α, hα⟩ := (ModelFacts.OrthAut.centralPSection_spinPlus (p := p) hn3).exists_mulEquiv_lift
    ψ.rangeRestrict ψ.rangeRestrict_surjective hθker hθC σ
  have hαψ : ∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x) := hα
  have hcentral : ∀ s ∈ (fr.La.range ⊔ fr.swap.La.range).comap
      (spinAction (quadPlus 4 (GaloisField p f))),
      s⁻¹ * α s ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) := by
    intro s hs
    have hℓ := hσ s (Subgroup.mem_comap.mp hs)
    set x := ψ.rangeRestrict s with hx
    have hζ : ∀ m : ↥ψ.range, (x⁻¹ * σ x) * m = m * (x⁻¹ * σ x) := by
      intro m
      obtain ⟨ℓ, rfl⟩ := σ.surjective m
      have h1 := hℓ ℓ
      rw [map_mul, map_mul, map_inv] at h1
      calc x⁻¹ * σ x * σ ℓ = x⁻¹ * (σ x * σ ℓ * (σ x)⁻¹) * σ x := by group
        _ = x⁻¹ * (x * σ ℓ * x⁻¹) * σ x := by rw [h1]
        _ = σ ℓ * (x⁻¹ * σ x) := by group
    refine mem_center_of_commutators_central fun t => hψ ?_
    rw [← MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, map_commutatorElement, map_mul,
      map_inv, hαψ s]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hζ _)
  have hfix := alpha_fixes_commutators α hcentral
  obtain ⟨A, φ, μ, hsim, hmat⟩ := hfl hp2 hq fr α hfix
  exact ⟨α, hαψ, A, φ, μ, hsim, hmat⟩

end Lift

section PairData

variable {p f : ℕ} [Fact p.Prime]

theorem d4PairData (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hadm : StatedLieAdmissible .POmegaPlus 4 p f)
    {H : Type} [Group H] {ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* H}
    {R R' : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    {x x' : spinGroup (quadPlus 4 (GaloisField p f))}
    (hpair : TwinPairOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩
      ψ R R' x x') :
    R ≤ ⁅R, R⁆ ∧ R' ≤ ⁅R', R'⁆ ∧
      R.map (spinAction (quadPlus 4 (GaloisField p f))) ∈ fundSet (quadPlus 4 (GaloisField p f)) ∧
      R'.map (spinAction (quadPlus 4 (GaloisField p f))) ∈
        fundSet (quadPlus 4 (GaloisField p f)) ∧
      (∀ r ∈ R, spinAction (quadPlus 4 (GaloisField p f)) r = 1 → r = 1) ∧
      ∀ r ∈ R', spinAction (quadPlus 4 (GaloisField p f)) r = 1 → r = 1 := by
  have hn3 : 3 ≤ 4 := by norm_num
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) hn3), R ≤ ⁅R, R⁆ :=
    Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := 4) (e := f) trivial hadm (by omega)
  have hnc : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) → r = 1 :=
    fund_noncentral_modelUniv (p := p) (e := f) (t := .POmegaPlus) (n := 4) trivial hadm (by simp)
  have hcorr := (Exotic.fundCorr_plus hp2 hq (le_refl 4)).1
  refine ⟨hperf R hpair.mem, hperf R' hpair.mem', hcorr R hpair.mem, hcorr R' hpair.mem', ?_, ?_⟩
  · exact injOn_of_ker_le_center (ker_spinAction_le_center _) fun r hr hcen =>
      hnc R hpair.mem r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  · exact injOn_of_ker_le_center (ker_spinAction_le_center _) fun r hr hcen =>
      hnc R' hpair.mem' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)

end PairData

section OuterGlue

variable {H : Type} [Group H]

@[expose] def OuterOn (L : Subgroup H) (S : Set H) (z : H) : Prop :=
  ∀ v : ↥(inducedAutOn L),
    (∀ c ∈ S, ∀ hc : c ∈ Subgroup.normalizer (L : Set H),
      v * toInducedAutOn L ⟨c, hc⟩ = toInducedAutOn L ⟨c, hc⟩ * v) →
    v * v * (v * v) = 1 → v * v ≠ 1 →
    (∀ hz : z ∈ Subgroup.normalizer (L : Set H), v * v ≠ toInducedAutOn L ⟨z, hz⟩) →
    ∀ hz : z ∈ Subgroup.normalizer (L : Set H),
      alphaOf (Subgroup.closure ({toInducedAutOn L ⟨z, hz⟩, v * v} :
        Set ↥(inducedAutOn L))) = ⊥

theorem outerOn_congr {L L' : Subgroup H} (hL : L = L') {S S' : Set H} (hS : S = S') {z z' : H}
    (hz : z = z') (h : OuterOn L S z) : OuterOn L' S' z' := by
  subst hL hS hz
  exact h

theorem outer_of_outerOn {K : Type} [Group K] (ψ : K →* H) (R R' : Subgroup K) (x : K)
    (h : OuterOn ψ.range ((R.map ψ : Set H) ∪ (R'.map ψ : Set H)) (ψ x))
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hy2 : v * v * (v * v) = 1) (hy1 : v * v ≠ 1) (hyz : v * v ≠ FrameVertex.innerHom ψ x) :
    alphaOf (Subgroup.closure ({FrameVertex.innerHom ψ x, v * v} :
      Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  refine h v ?_ hy2 hy1 (fun hz => hyz) (mem_normalizer_range ψ x)
  rintro c (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) hc
  · exact hvR r hr
  · exact hvR' r hr

end OuterGlue

section D4Outer

variable {p f : ℕ} [Fact p.Prime]

theorem outerOn_of_pair_ord_d4 (hfl : D4FixLift p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) {H : Type} [Group H] [Finite H]
    {ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* H}
    {R R' : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    {x x' : spinGroup (quadPlus 4 (GaloisField p f))}
    (hpair : TwinPairOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩
      ψ R R' x x')
    (hord : spinAction (quadPlus 4 (GaloisField p f)) x =
      spinAction (quadPlus 4 (GaloisField p f)) x') :
    OuterOn ψ.range ((R.map ψ : Set H) ∪ (R'.map ψ : Set H)) (ψ x) := by
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) :=
    isPerfect_spinGroup_quadPlus hn3
  obtain ⟨hRp, hR'p, hRc, hR'c, hinj, hinj'⟩ := d4PairData hp2 hq hadm hpair
  have hlift := liftSimFr_of_d4FixLift hfl hp2 hq ψ hpair.ker
  intro v hvS hy2 hy1 hyz hz
  have hvR : ∀ r ∈ R, v * spinInd ψ r = spinInd ψ r * v := fun r hr =>
    hvS (ψ r) (Or.inl ⟨r, hr, rfl⟩) (mem_normalizer_range ψ r)
  have hvR' : ∀ r ∈ R', v * spinInd ψ r = spinInd ψ r * v := fun r hr =>
    hvS (ψ r) (Or.inr ⟨r, hr, rfl⟩) (mem_normalizer_range ψ r)
  exact alphaOf_spin_twin_pair_outer_ord hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadPlus 4 _) (range_spinAction_quadPlus hn3) (by omega) hRp hR'p
    hRc hR'c hinj hinj' hpair.ne hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 hord
    hpair.ker hlift v hvR hvR' hy2 hy1 (hyz (mem_normalizer_range ψ x))

theorem twinOuterAlphaOn_d4_of_fixLift (hfl : D4FixLift p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    TwinOuterAlphaOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩ := by
  obtain ⟨-, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  obtain ⟨-, hF⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := f) (by omega)
  obtain ⟨ρ, hρ⟩ := exists_triality hadm h4 hF
  intro H _ _ ψ R R' x x' hpair v hvR hvR' hy2 hy1 hyz
  obtain ⟨hc, hc2⟩ := twinPairOn_central_div hpair
  obtain ⟨σ, hσ, hθ⟩ := exists_aut_ordinary hp2 hadm ρ hρ hc hc2
  have hpair' := twinPairOn_transport hpair σ hσ
  have hord : spinAction (quadPlus 4 (GaloisField p f)) (σ x) =
      spinAction (quadPlus 4 (GaloisField p f)) (σ x') := by
    rw [map_mul, map_inv, map_mul, map_inv] at hθ
    exact mul_inv_eq_one.mp hθ
  have hO' := outerOn_of_pair_ord_d4 hfl hp2 hq hadm hpair' hord
  have hr := range_comp_symm ψ σ
  have hO : OuterOn ψ.range ((R.map ψ : Set H) ∪ (R'.map ψ : Set H)) (ψ x) := by
    refine outerOn_congr hr ?_ ?_ hO'
    · rw [map_map_comp_symm, map_map_comp_symm]
    · simp
  exact outer_of_outerOn ψ R R' x hO v hvR hvR' hy2 hy1 hyz

theorem twinOuterAlpha_d4_of_fixLift (hfl : D4FixLift p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    TwinOuterAlpha p f .POmegaPlus 4 := by
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p f)),
      plusDatum 4 (GaloisField p f) (by norm_num)⟩ → TwinOuterAlphaOn .POmegaPlus M := by
    intro M hM
    subst hM
    exact twinOuterAlphaOn_d4_of_fixLift hfl hp2 hq hadm
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (by norm_num))

end D4Outer

theorem twinSmallOuterD4_of_fixLift (p : ℕ) [Fact p.Prime] (hfl : ∀ f, D4FixLift p f) :
    TwinSmallOuterD4 p :=
  fun hp2 e hq hadm => twinOuterAlpha_d4_of_fixLift (hfl e) hp2 hq hadm

end CFSG.ClassicalInvolution.G2D4Models.Twin
