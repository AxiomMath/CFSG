module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinGen
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSmall
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Inner
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Triality

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Ord

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem sq_eq_one_of_central_fund {R : Subgroup (spinGroup Q)}
    (hR : R.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) {y : spinGroup Q} (hy : y ∈ R)
    (hcy : ∀ r ∈ R, y * r = r * y) : y * y = 1 := by
  obtain ⟨i, FR, hFR, -⟩ := hR
  have hθy : spinAction Q y ∈ FR.La.range := hFR ▸ Subgroup.mem_map_of_mem _ hy
  have hθyc : ∀ h ∈ FR.La.range, spinAction Q y * h = h * spinAction Q y := by
    intro h hh
    rw [← hFR] at hh
    obtain ⟨r, hr, rfl⟩ := hh
    rw [← map_mul, ← map_mul, hcy r hr]
  have h1 := sq_eq_one_of_central_le_la FR hθy hθyc
  apply hinj (y * y) (R.mul_mem hy hy)
  rw [map_mul]
  exact h1

theorem exists_twin_frame_ord [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hnc : ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    (hnc' : ∀ r ∈ R', r ∈ Subgroup.center (spinGroup Q) → r = 1) (hne : R ≠ R')
    {x x' a a' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x') (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ∃ (F₁ : OFrame Q) (A A' : SL(2, F)), R.map (spinAction Q) = F₁.La.range ∧
      R'.map (spinAction Q) = F₁.swap.La.range ∧ spinAction Q x = F₁.La (-1) ∧
      spinAction Q x' = F₁.swap.La (-1) ∧ spinAction Q a = F₁.La A ∧
      spinAction Q a' = F₁.swap.La A' ∧ (A : Matrix (Fin 2) (Fin 2) F) * A = -1 ∧
      (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1 := by
  classical
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center hker fun r hr hcen =>
      hnc r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center hker fun r hr hcen =>
      hnc' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ := swap_of_twin_pair_ord hodd hRp hR'p hR hR' hinj hinj' hne
    hx hx2 hx1 hx' hx'2 hx'1 hord
  obtain ⟨A, hA⟩ : ∃ A : SL(2, F), F₁.La A = spinAction Q a := by
    have : spinAction Q a ∈ F₁.La.range := hF₁ ▸ Subgroup.mem_map_of_mem _ ha
    exact this
  obtain ⟨A', hA'⟩ : ∃ A' : SL(2, F), F₁.swap.La A' = spinAction Q a' := by
    have : spinAction Q a' ∈ F₁.swap.La.range := hF₁' ▸ Subgroup.mem_map_of_mem _ ha'
    exact this
  have hperp : ∀ fr : OFrame Q, fr.perp ≠ ⊥ := by
    intro fr h
    have h1 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    rw [h, finrank_bot] at h1
    omega
  have hAA := sq_eq_neg_one_of_sq_mem_center hrange hZ F₁ (hperp F₁) hA hθx hsq
  have hA'A' := sq_eq_neg_one_of_sq_mem_center hrange hZ F₁.swap (hperp F₁.swap) hA' hθx' hsq'
  refine ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hA.symm, hA'.symm, ?_, ?_⟩
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hAA
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hA'A'
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this

theorem spinGroup_eq_centralizer_sup_ord [Finite F] [FiniteDimensional F V]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hnc : ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    (hnc' : ∀ r ∈ R', r ∈ Subgroup.center (spinGroup Q) → r = 1) (hne : R ≠ R')
    (hcomm : ∀ r ∈ R, ∀ r' ∈ R', r * r' = r' * r)
    {x x' a a' : spinGroup Q} (hx : x ∈ R) (hcx : ∀ r ∈ R, x * r = r * x) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x') (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    Subgroup.centralizer ({a * a'} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set (spinGroup Q)) = ⊤ := by
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  obtain ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hθa, hθa', hAA, hA'A'⟩ := exists_twin_frame_ord hodd
    hrange hZ hV hRp hR'p hR hR' hnc hnc' hne hx hx2 hx1 hx' hx'2 hx'1 hord ha ha' hsq hsq'
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have T := twinDatum_of_frame F₁ h2 hQ hAA hA'A' hV
  have hθu : spinAction Q (a * a') = twinInv F₁ A A' := by
    rw [map_mul, hθa, hθa']
    rfl
  have hxu : x * (a * a') = (a * a') * x := by
    have h1 : x * a = a * x := hcx a ha
    have h2' : x * a' = a' * x := hcomm x hx a' ha'
    calc x * (a * a') = (x * a) * a' := by group
      _ = (a * x) * a' := by rw [h1]
      _ = a * (x * a') := by group
      _ = a * (a' * x) := by rw [h2']
      _ = (a * a') * x := by group
  have hθxu : spinAction Q (x * (a * a')) = twinInv F₁ A A' * F₁.La (-1) := by
    rw [hxu, map_mul, hθu, hθx]
  have hd3 : ∀ S : Submodule F V, F₁.perp ≤ S → 3 ≤ Module.finrank F S := fun S hS =>
    le_trans T.dW (Submodule.finrank_mono hS)
  have h₁ := elemOn_le_map_centralizer_of_fix hodd h5 hrange (g := a * a')
    T.toSplitDatum.nd_sup₂W (hd3 _ le_sup_right)
    (by rw [hθu]; exact twinInv_mem_orthogonalGroup F₁ A A')
    (fun y hy => by rw [hθu]; exact T.fix₁ y hy)
  have h₂ := elemOn_le_map_centralizer_of_fix hodd h5 hrange (g := x * (a * a'))
    T.toSplitDatum.nd_sup₁W (hd3 _ le_sup_right)
    (by rw [hθxu]; exact elementaryGroup_le_orthogonalGroup Q T.mem₂)
    (fun y hy => by rw [hθxu]; exact T.fix₂ y hy)
  have hgen := elementaryGroup_le_join_of_decomp hodd hQ T.ndW T.dW T.o₁W T.o₂W T.top
  have hE : (spinAction Q).range ≤ (Subgroup.centralizer ({a * a'} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set (spinGroup Q))).map (spinAction Q) := by
    rw [hrange, Subgroup.map_sup]
    exact hgen.trans (sup_le_sup h₁ h₂)
  exact eq_top_of_range_le_map (spinAction Q) hker hE

end Ord

section D4

variable {p f : ℕ} [Fact p.Prime]

theorem map_symm_centralizer {K : Type*} [Group K] (σ : K ≃* K) (w : K) :
    (Subgroup.centralizer ({σ w} : Set K)).map σ.symm.toMonoidHom =
      Subgroup.centralizer ({w} : Set K) := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c ∈ Subgroup.centralizer ({σ w} : Set K) := hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg σ.symm hc'
    simpa using this
  · intro hg
    refine ⟨σ g, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    show σ g ∈ Subgroup.centralizer ({σ w} : Set K)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg]

theorem twinMFGenerationOn_d4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    TwinMFGenerationOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩ := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hodd, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  obtain ⟨-, hF⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := f) (by omega)
  obtain ⟨ρ, hρ⟩ := exists_triality hadm h4 hF
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
  have hinj : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3),
      ∀ r ∈ R, spinAction (quadPlus 4 (GaloisField p f)) r = 1 → r = 1 := fun R hR =>
    injOn_of_ker_le_center (ker_spinAction_le_center _) fun r hr hcen =>
      hnc R hR r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  intro R R' x x' hd a ha a' ha' hsq hsq' S hS
  have hx2 : x * x = 1 :=
    sq_eq_one_of_central_fund (hcorr R hd.mem) (hinj R hd.mem) hd.hx hd.cx
  have hx'2 : x' * x' = 1 :=
    sq_eq_one_of_central_fund (hcorr R' hd.mem') (hinj R' hd.mem') hd.hx' hd.cx'
  have hc2 : (x * x'⁻¹) * (x * x'⁻¹) = 1 := by
    have hx'inv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
    have hcomm : x * x' = x' * x := hd.comm x hd.hx x' hd.hx'
    rw [hx'inv]
    calc x * x' * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hcomm]
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hx2, hx'2, one_mul]
  obtain ⟨σ, hσ, hθ⟩ := exists_aut_ordinary hp2 hadm ρ hρ hd.same hc2
  have hord : spinAction (quadPlus 4 (GaloisField p f)) (σ x) =
      spinAction (quadPlus 4 (GaloisField p f)) (σ x') := by
    rw [map_mul, map_inv, map_mul, map_inv] at hθ
    exact mul_inv_eq_one.mp hθ
  have hmap : ∀ g : spinGroup (quadPlus 4 (GaloisField p f)),
      g ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) →
        σ g ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) := by
    intro g hg
    rw [Subgroup.mem_center_iff] at hg ⊢
    intro y
    obtain ⟨y', rfl⟩ := σ.surjective y
    rw [← map_mul, ← map_mul, hg y']
  have hR₁ := hσ R hd.mem
  have hR₁' := hσ R' hd.mem'
  have hne₁ : R.map σ.toMonoidHom ≠ R'.map σ.toMonoidHom := fun h =>
    hd.ne (Subgroup.map_injective σ.injective h)
  have hcomm₁ : ∀ r ∈ R.map σ.toMonoidHom, ∀ r' ∈ R'.map σ.toMonoidHom, r * r' = r' * r := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    show σ r * σ r' = σ r' * σ r
    rw [← map_mul, ← map_mul, hd.comm r hr r' hr']
  have hcx₁ : ∀ r ∈ R.map σ.toMonoidHom, σ x * r = r * σ x := by
    rintro _ ⟨r, hr, rfl⟩
    show σ x * σ r = σ r * σ x
    rw [← map_mul, ← map_mul, hd.cx r hr]
  have hgen := spinGroup_eq_centralizer_sup_ord hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadPlus 4 _) (range_spinAction_quadPlus hn3)
    (centerScalar_quadPlus hn3) (by omega) (hperf _ hR₁) (hperf _ hR₁') (hcorr _ hR₁)
    (hcorr _ hR₁') (hnc _ hR₁) (hnc _ hR₁') hne₁ hcomm₁ (x := σ x) (x' := σ x')
    (a := σ a) (a' := σ a') ⟨x, hd.hx, rfl⟩ hcx₁ (by rw [← map_mul, hx2, map_one])
    (fun h => hd.nx (σ.injective (by rw [h, map_one]))) ⟨x', hd.hx', rfl⟩
    (by rw [← map_mul, hx'2, map_one]) (fun h => hd.nx' (σ.injective (by rw [h, map_one])))
    hord ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
    (by have := hmap _ hsq; simpa [map_mul, map_inv] using this)
    (by have := hmap _ hsq'; simpa [map_mul, map_inv] using this)
  have hfin : Subgroup.centralizer ({a * a'} : Set (spinGroup (quadPlus 4 (GaloisField p f)))) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set (spinGroup (quadPlus 4 (GaloisField p f)))) =
        ⊤ := by
    have h1 := congrArg (Subgroup.map σ.symm.toMonoidHom) hgen
    rw [Subgroup.map_sup, ← map_mul σ a a', ← map_mul σ x (a * a'), map_symm_centralizer,
      map_symm_centralizer, Subgroup.map_top_of_surjective _ σ.symm.surjective] at h1
    exact h1
  have hle : (⊤ : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))) ≤
      Subgroup.centralizer ({x} : Set (spinGroup (quadPlus 4 (GaloisField p f)))) ⊔
      Subgroup.centralizer ({a * a'} : Set (spinGroup (quadPlus 4 (GaloisField p f)))) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set (spinGroup (quadPlus 4 (GaloisField p f)))) := by
    rw [← hfin]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  exact le_top.trans hle

theorem twinMFGeneration_plus4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    TwinMFGeneration p f .POmegaPlus 4 := by
  have hp : p.Prime := Fact.out
  have he : 1 ≤ f := one_le_of_five_le_pow hq
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨hp, he, le_refl 4⟩
  refine twinMFGeneration_of_on ?_
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p f)),
      plusDatum 4 (GaloisField p f) (by norm_num)⟩ → TwinMFGenerationOn .POmegaPlus M := by
    intro M hM
    subst hM
    exact twinMFGenerationOn_d4 hp2 hq hadm
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (by norm_num))

end D4

end CFSG.ClassicalInvolution.RouteD.TwinY
