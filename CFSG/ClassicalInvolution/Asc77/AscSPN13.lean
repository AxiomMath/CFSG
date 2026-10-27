module

public import CFSG.ClassicalInvolution.Asc77.AscSPN10
public import CFSG.ClassicalInvolution.Asc77.AscSPN12
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift
public import CFSG.ClassicalInvolution.Asc77.AscT7PF

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace SPN

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.G2D4Models.Twin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped commutatorElement MatrixGroups

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem spinGen_of_frame (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hV : 7 ≤ Module.finrank F (ι → F)) {ψ : spinGroup Q →* H}
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) (hlift : LiftSimFr Q ψ)
    {R R' : Subgroup (spinGroup Q)} {x : spinGroup Q} (F₁ : Frame Q)
    (hF₁ : R.map (spinAction Q) = F₁.La.range) (hF₁' : R'.map (spinAction Q) = F₁.swap.La.range)
    (hθx : spinAction Q x = F₁.La (-1)) (s : H) (hs : s ∈ Subgroup.normalizer (ψ.range : Set H))
    (hss : s * s = 1) (hsR : ∀ r ∈ R, s * ψ r = ψ r * s) (hsR' : ∀ r ∈ R', s * ψ r = ψ r * s) :
    (∀ y ∈ ψ.range, s * y = y * s) ∨ (∀ y ∈ ψ.range, s * y * s⁻¹ = ψ x * y * (ψ x)⁻¹) ∨
      (∀ q ∈ ψ.range, q ∈ Subgroup.closure ({q | q ∈ ψ.range ∧ s * q = q * s} ∪
        {q | q ∈ ψ.range ∧ ψ x * q = q * ψ x})) := by
  classical
  set v : ↥(inducedAutOn ψ.range) := toInducedAutOn ψ.range ⟨s, hs⟩ with hvdef
  have hvc : ∀ g : spinGroup Q, s * ψ g = ψ g * s →
      v * toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ =
        toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ * v := by
    intro g hg
    rw [hvdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hg
  have hvR : ∀ r ∈ R, v * spinInd ψ r = spinInd ψ r * v := fun r hr => hvc r (hsR r hr)
  have hvR' : ∀ r ∈ R', v * spinInd ψ r = spinInd ψ r * v := fun r hr => hvc r (hsR' r hr)
  have hv : ∀ g : spinGroup Q, spinAction Q g ∈ F₁.La.range ⊔ F₁.swap.La.range →
      v * toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ =
        toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ * v := by
    intro g hg
    rw [← hF₁, ← hF₁'] at hg
    exact commute_spinInd_of_mem_map_sup (ker_spinAction_le_center Q) ψ v hvR hvR' hg
  have hσ : ∀ g : spinGroup Q, spinAction Q g ∈ F₁.La.range ⊔ F₁.swap.La.range →
      ∀ ℓ : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict g * ℓ * (ψ.rangeRestrict g)⁻¹) =
        ψ.rangeRestrict g * (v : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict g)⁻¹ := by
    intro g hg ℓ
    have h := congrArg (fun a : ↥(inducedAutOn ψ.range) => ((a : MulAut ↥ψ.range) ℓ : ↥ψ.range))
      (hv g hg)
    exact Subtype.ext (congrArg Subtype.val h)
  exact spinGen_core hodd h5 hQ hrange F₁ hV hψ hθx s hs hss (hlift F₁ (v : MulAut ↥ψ.range) hσ)
    hv

end Frame

section Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)}

theorem spinGenOn_of_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hlift : ∀ (H : Type) [Group H] [Finite H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → LiftSimFr Q ψ)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    SpinGenOn t ⟨spinGroup Q, D⟩ := by
  intro H _ _ ψ R R' x x' hpair s hs hss hsR hsR'
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R hpair.mem r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R' hpair.mem' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨F₁, hF₁, hF₁', hθx, -⟩ := swap_of_twin_pair hodd hrange hZ hproj (hperf R hpair.mem)
    (hperf R' hpair.mem') (hcorr R hpair.mem) (hcorr R' hpair.mem') hinj hinj' hpair.ne hpair.hx
    hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 ψ hpair.ker hpair.same
  exact spinGen_of_frame hodd h5 hQ hrange hV hpair.ker (hlift H ψ hpair.ker) F₁ hF₁ hF₁' hθx s hs
    hss hsR hsR'

end Transport

section Families

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

variable {p e : ℕ} [Fact p.Prime]

theorem spinGenOn_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    SpinGenOn .POmegaOdd (modelUniv .POmegaOdd n p e Fact.out) := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p e) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have : Group.IsPerfect (spinGroup (quadOdd n (GaloisField p e))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaOdd) (n := n) trivial hadm
    (by simp)
  show SpinGenOn .POmegaOdd ⟨spinGroup (quadOdd n (GaloisField p e)), oddDatum n (GaloisField p e)⟩
  refine spinGenOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadOdd n _ h2) (range_spinAction_quadOdd h2 hn3)
    (centerScalar_quadOdd h2 hn3) (by omega) (fun F₁ F₂ h => ?_)
    (fun H _ _ ψ hψ => LiftSim.liftSimFr (liftSim_quadOdd hp2 hn3 he ψ hψ)) _
    (fundCorr_odd hp2 hq hadm).1 hperf hnc
  have := finrank_eq_eight_of_proj hodd F₁ F₂ h
  omega

theorem spinGenOn_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    SpinGenOn .POmegaMinus (modelUniv .POmegaMinus n p e Fact.out) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have : Group.IsPerfect (spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr p e)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := n) trivial
    hadm (by simp)
  show SpinGenOn .POmegaMinus ⟨spinGroup (quadMinus n (GaloisField p e)
    (minusCoeffs p e).1 (minusCoeffs p e).2), Twisted.minusDatum n (minusCoeffs_irr p e)⟩
  exact spinGenOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega)
    (fun F₁ F₂ h => hproj_quadMinus hp2 hq hn4 F₁ F₂ h)
    (fun H _ _ ψ hψ => LiftSim.liftSimFr (liftSim_quadMinus hp2 hn4 he ψ hψ)) _
    (fundCorr_minus hp2 hq hadm).1 hperf hnc

end Families

section D4

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem spinGenOn_d4_ord (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) {H : Type} [Group H] [Finite H]
    {ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* H}
    {R R' : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    {x x' : spinGroup (quadPlus 4 (GaloisField p f))}
    (hpair : TwinPairOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩
      ψ R R' x x')
    (hord : spinAction (quadPlus 4 (GaloisField p f)) x =
      spinAction (quadPlus 4 (GaloisField p f)) x') (s : H)
    (hs : s ∈ Subgroup.normalizer (ψ.range : Set H)) (hss : s * s = 1)
    (hsR : ∀ r ∈ R, s * ψ r = ψ r * s) (hsR' : ∀ r ∈ R', s * ψ r = ψ r * s) :
    (∀ y ∈ ψ.range, s * y = y * s) ∨ (∀ y ∈ ψ.range, s * y * s⁻¹ = ψ x * y * (ψ x)⁻¹) ∨
      (∀ q ∈ ψ.range, q ∈ Subgroup.closure ({q | q ∈ ψ.range ∧ s * q = q * s} ∪
        {q | q ∈ ψ.range ∧ ψ x * q = q * ψ x})) := by
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) :=
    isPerfect_spinGroup_quadPlus hn3
  obtain ⟨hRp, hR'p, hRc, hR'c, hinj, hinj'⟩ := d4PairData hp2 hq hadm hpair
  have hlift := liftSimFr_of_d4FixLift d4FixLift_proved hp2 hq ψ hpair.ker
  obtain ⟨F₁, hF₁, hF₁', hθx, -⟩ := swap_of_twin_pair_ord hodd hRp hR'p hRc hR'c hinj hinj'
    hpair.ne hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 hord
  exact spinGen_of_frame hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadPlus 4 _) (range_spinAction_quadPlus hn3) (by omega) hpair.ker
    hlift F₁ hF₁ hF₁' hθx s hs hss hsR hsR'

theorem spinGenOn_d4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    SpinGenOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩ := by
  obtain ⟨-, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  obtain ⟨-, hF⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := f) (by omega)
  obtain ⟨ρ, hρ⟩ := exists_triality hadm h4 hF
  intro H _ _ ψ R R' x x' hpair s hs hss hsR hsR'
  obtain ⟨hc, hc2⟩ := twinPairOn_central_div hpair
  obtain ⟨σ, hσ, hθ⟩ := exists_aut_ordinary hp2 hadm ρ hρ hc hc2
  have hpair' := twinPairOn_transport hpair σ hσ
  have hord : spinAction (quadPlus 4 (GaloisField p f)) (σ x) =
      spinAction (quadPlus 4 (GaloisField p f)) (σ x') := by
    rw [map_mul, map_inv, map_mul, map_inv] at hθ
    exact mul_inv_eq_one.mp hθ
  have hr := range_comp_symm ψ σ
  have hs' : s ∈ Subgroup.normalizer ((ψ.comp σ.symm.toMonoidHom).range : Set H) := by
    rw [hr]
    exact hs
  have hψx : (ψ.comp σ.symm.toMonoidHom) (σ x) = ψ x := by simp
  have hsR₂ : ∀ r ∈ R.map σ.toMonoidHom, s * (ψ.comp σ.symm.toMonoidHom) r =
      (ψ.comp σ.symm.toMonoidHom) r * s := by
    rintro _ ⟨r, hr', rfl⟩
    simpa using hsR r hr'
  have hsR'₂ : ∀ r ∈ R'.map σ.toMonoidHom, s * (ψ.comp σ.symm.toMonoidHom) r =
      (ψ.comp σ.symm.toMonoidHom) r * s := by
    rintro _ ⟨r, hr', rfl⟩
    simpa using hsR' r hr'
  have key := spinGenOn_d4_ord hp2 hq hadm hpair' hord s hs' hss hsR₂ hsR'₂
  rw [hr, hψx] at key
  exact key

end D4

section Final

variable {p f : ℕ} [Fact p.Prime]

theorem spinGen_proved : SpinGen p := by
  intro hp2 t n e hspin hadm hq
  rcases hspin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact spinGenOn_odd hp2 hq hadm
  · have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p e)),
        plusDatum 4 (GaloisField p e) (by norm_num)⟩ → SpinGenOn .POmegaPlus M := by
      intro M hM
      subst hM
      exact spinGenOn_d4 hp2 hq hadm
    exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (by norm_num))
  · exact spinGenOn_minus hp2 hq hadm

theorem spinSectionConn_proved : T7P.SpinSectionConn p f :=
  spinSectionConn_of_spinGen spinGen_proved

end Final

end SPN

end CFSG.ClassicalInvolution.Asc77
