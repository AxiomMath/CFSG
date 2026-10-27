module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Center
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRows
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge
public import CFSG.ClassicalInvolution.Asc77.AscE184Basic
public import CFSG.ClassicalInvolution.Asc77.AscE184Sec
public import CFSG.ClassicalInvolution.Asc77.AscE186QuotOdd
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Cases
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidFrame
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.RouteD

section Transport

variable {t : StatedLieTag} {M : LieUniversal} {H : Type} [Group H]

theorem twinPairOn_transport {ψ : M.K →* H} {R R' : Subgroup M.K} {x x' : M.K}
    (hp : TwinPairOn t M ψ R R' x x') (σ : M.K ≃* M.K)
    (hσ : ∀ S ∈ fundamentalSubgroups t M.D, S.map σ.toMonoidHom ∈ fundamentalSubgroups t M.D) :
    TwinPairOn t M (ψ.comp σ.symm.toMonoidHom) (R.map σ.toMonoidHom) (R'.map σ.toMonoidHom)
      (σ x) (σ x') where
  ker := by
    intro s hs
    have h1 : σ.symm s ∈ ψ.ker := by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact hs
    have h2 := hp.ker h1
    have : s = σ (σ.symm s) := by simp
    rw [this]
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro y
    have := h2 (σ.symm y)
    simpa using congrArg σ this
  mem := hσ _ hp.mem
  mem' := hσ _ hp.mem'
  ne := by
    intro h
    apply hp.ne
    have := congrArg (fun S : Subgroup M.K => S.map σ.symm.toMonoidHom) h
    simpa [Subgroup.map_map] using this
  comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show σ a * σ b = σ b * σ a
    rw [← map_mul, ← map_mul, hp.comm a ha b hb]
  hx := ⟨x, hp.hx, rfl⟩
  hx2 := by rw [← map_mul, hp.hx2, map_one]
  hx1 := fun h => hp.hx1 (σ.injective (by rw [h, map_one]))
  hx' := ⟨x', hp.hx', rfl⟩
  hx'2 := by rw [← map_mul, hp.hx'2, map_one]
  hx'1 := fun h => hp.hx'1 (σ.injective (by rw [h, map_one]))
  same := by simpa using hp.same

theorem range_comp_symm (ψ : M.K →* H) (σ : M.K ≃* M.K) :
    (ψ.comp σ.symm.toMonoidHom).range = ψ.range := by
  ext h
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨σ.symm s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨σ s, by simp⟩

theorem map_map_comp_symm (ψ : M.K →* H) (σ : M.K ≃* M.K) (R : Subgroup M.K) :
    (R.map σ.toMonoidHom).map (ψ.comp σ.symm.toMonoidHom) = R.map ψ := by
  rw [Subgroup.map_map]
  congr 1
  ext s
  simp

theorem alphaOf_closure_congr {L L' : Subgroup H} (hL : L = L') {a b b' : H}
    (ha : a ∈ Subgroup.normalizer (L : Set H)) (hb : b ∈ Subgroup.normalizer (L : Set H))
    (ha' : a ∈ Subgroup.normalizer (L' : Set H)) (hb' : b' ∈ Subgroup.normalizer (L' : Set H))
    (hbb : b = b') :
    alphaOf (Subgroup.closure ({toInducedAutOn L ⟨a, ha⟩, toInducedAutOn L ⟨b, hb⟩} :
      Set ↥(inducedAutOn L))) = ⊥ ↔
    alphaOf (Subgroup.closure ({toInducedAutOn L' ⟨a, ha'⟩, toInducedAutOn L' ⟨b', hb'⟩} :
      Set ↥(inducedAutOn L'))) = ⊥ := by
  subst hL hbb
  exact Iff.rfl

end Transport

section D4

variable {p f : ℕ} [Fact p.Prime]

theorem alphaOf_twinPair_ord_d4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) {H : Type} [Group H] [Finite H]
    {ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* H}
    {R R' : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    {x x' : spinGroup (quadPlus 4 (GaloisField p f))}
    (hpair : TwinPairOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩
      ψ R R' x x')
    (hord : spinAction (quadPlus 4 (GaloisField p f)) x =
      spinAction (quadPlus 4 (GaloisField p f)) x')
    {u : H} (hun : u ∈ Subgroup.normalizer (ψ.range : Set H)) (hu : u ∈ R.map ψ ⊔ R'.map ψ)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ ψ x) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨u, hun⟩,
      toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) hn3), R ≤ ⁅R, R⁆ :=
    Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := 4) (e := f) trivial hadm (by omega)
  have hnc : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) → r = 1 :=
    fund_noncentral_modelUniv (p := p) (e := f) (t := .POmegaPlus) (n := 4) trivial hadm (by simp)
  have hcorr := (Exotic.fundCorr_plus hp2 hq (le_refl 4)).1
  have hinj : ∀ r ∈ R, spinAction (quadPlus 4 (GaloisField p f)) r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center _) fun r hr hcen =>
      hnc R hpair.mem r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction (quadPlus 4 (GaloisField p f)) r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center _) fun r hr hcen =>
      hnc R' hpair.mem' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  exact alphaOf_spin_twin_pair_ord hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadPlus 4 _) (range_spinAction_quadPlus hn3)
    (centerScalar_quadPlus hn3) (by omega) (hperf R hpair.mem) (hperf R' hpair.mem')
    (hcorr R hpair.mem) (hcorr R' hpair.mem') hinj hinj' hpair.ne hpair.comm hpair.hx hpair.hx2
    hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 hord ψ hpair.ker hpair.same hu hun hu2 hu1 huz


theorem twinPairOn_central_div {t : StatedLieTag} {M : LieUniversal} {H : Type} [Group H]
    {ψ : M.K →* H} {R R' : Subgroup M.K} {x x' : M.K} (hp : TwinPairOn t M ψ R R' x x') :
    x * x'⁻¹ ∈ Subgroup.center M.K ∧ (x * x'⁻¹) * (x * x'⁻¹) = 1 := by
  refine ⟨hp.ker ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hp.same, mul_inv_cancel]
  · have hx'inv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hp.hx'2
    have hcomm : x * x' = x' * x := hp.comm x hp.hx x' hp.hx'
    rw [hx'inv]
    calc x * x' * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hcomm]
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hp.hx2, hp.hx'2, one_mul]

theorem twinInnerAlphaOn_d4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    TwinInnerAlphaOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩ := by
  obtain ⟨-, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  obtain ⟨-, hF⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := f) (by omega)
  obtain ⟨ρ, hρ⟩ := exists_triality hadm h4 hF
  intro H _ _ ψ R R' x x' hpair u hun hu hu2 hu1 huz
  obtain ⟨hc, hc2⟩ := twinPairOn_central_div hpair
  obtain ⟨σ, hσ, hθ⟩ := exists_aut_ordinary hp2 hadm ρ hρ hc hc2
  have hpair' := twinPairOn_transport hpair σ hσ
  have hord : spinAction (quadPlus 4 (GaloisField p f)) (σ x) =
      spinAction (quadPlus 4 (GaloisField p f)) (σ x') := by
    rw [map_mul, map_inv, map_mul, map_inv] at hθ
    exact mul_inv_eq_one.mp hθ
  have hr := range_comp_symm ψ σ
  have hun' : u ∈ Subgroup.normalizer ((ψ.comp σ.symm.toMonoidHom).range : Set H) := by
    rw [hr]
    exact hun
  have hu' : u ∈ (R.map σ.toMonoidHom).map (ψ.comp σ.symm.toMonoidHom) ⊔
      (R'.map σ.toMonoidHom).map (ψ.comp σ.symm.toMonoidHom) := by
    rw [map_map_comp_symm, map_map_comp_symm]
    exact hu
  have hψx : (ψ.comp σ.symm.toMonoidHom) (σ x) = ψ x := by simp
  have key := alphaOf_twinPair_ord_d4 hp2 hq hadm hpair' hord hun' hu' hu2 hu1
    (by rw [hψx]; exact huz)
  exact (alphaOf_closure_congr hr hun' (mem_normalizer_range _ (σ x)) hun
    (mem_normalizer_range ψ x) hψx).mp key

theorem twinInnerAlpha_d4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    TwinInnerAlpha p f .POmegaPlus 4 := by
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p f)),
      plusDatum 4 (GaloisField p f) (by norm_num)⟩ → TwinInnerAlphaOn .POmegaPlus M := by
    intro M hM
    subst hM
    exact twinInnerAlphaOn_d4 hp2 hq hadm
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (by norm_num))

end D4

theorem twinSmallInnerD4 (p : ℕ) [Fact p.Prime] : TwinSmallInnerD4 p :=
  fun hp2 _ hq hadm => twinInnerAlpha_d4 hp2 hq hadm

end CFSG.ClassicalInvolution.G2D4Models.Twin
