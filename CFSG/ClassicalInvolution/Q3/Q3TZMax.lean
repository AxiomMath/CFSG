module

public import CFSG.ClassicalInvolution.Q3.Q3TZCA
public import CFSG.ClassicalInvolution.Q3.Q3TY14
public import CFSG.ClassicalInvolution.Q3.Q3TWY1
public import CFSG.ClassicalInvolution.RouteD.TWS8Spin
public import CFSG.ClassicalInvolution.Q3.Q3TIYComp
public import CFSG.ClassicalInvolution.Q3.Q3TY6
public import CFSG.ClassicalInvolution.Q3.Q3VF4Row
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TZ

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalGroups.Orthogonal.Small (stabSub)
open CFSG.ClassicalInvolution.Generic (conjSub mem_conjSub_iff conj_mem_conjSub conjSub_map
  conjSub_inv_conjSub)
open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.Orth15
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinDatumOn)
open CFSG.ClassicalInvolution.RouteD.TWS8
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

section Context

structure PairData3 {K : Type} [Group K] (𝓕 : Set (Subgroup K)) (R R' : Subgroup K)
    (x x' : K) : Prop where
  mem : R ∈ 𝓕
  mem' : R' ∈ 𝓕
  ne : R ≠ R'
  hx : x ∈ R
  hx' : x' ∈ R'
  cx : ∀ r ∈ R, x * r = r * x
  cx' : ∀ r ∈ R', x' * r = r * x'
  nx : x ≠ 1
  nx' : x' ≠ 1
  same : x * x'⁻¹ ∈ Subgroup.center K

theorem pairData3_of_datum {t : StatedLieTag} {M : LieUniversal} {R R' : Subgroup M.K}
    {x x' : M.K} (hd : TwinDatumOn t M R R' x x') :
    PairData3 (fundamentalSubgroups t M.D) R R' x x' :=
  ⟨hd.mem, hd.mem', hd.ne, hd.hx, hd.hx', hd.cx, hd.cx', hd.nx, hd.nx', hd.same⟩

structure PairCtx3 {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    (Q : QuadraticForm F (ι → F)) (𝓕 : Set (Subgroup (spinGroup Q))) : Prop where
  hodd : Odd (Nat.card F)
  hQ : (polarBilin Q).Nondegenerate
  hrange : (spinAction Q).range = elementaryGroup Q
  perfect : Group.IsPerfect (spinGroup Q)
  hZ : CenterScalar Q
  hV : 1 ≤ Module.finrank F (ι → F)
  hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False
  hcop : ∀ n ∈ (spinAction Q).ker, ¬ 3 ∣ orderOf n
  hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q
  hpow3 : ∀ R ∈ 𝓕, Pow3 R
  hnc : ∀ R ∈ 𝓕, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1

end Context

section Lift

variable {F : Type} [Field F] {ι : Type} {Q : QuadraticForm F (ι → F)}

theorem conj_pair_mem3 (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q))
    (hcop : ∀ n ∈ (spinAction Q).ker, ¬ 3 ∣ orderOf n) (h2 : (2 : F) ≠ 0)
    {R R' : Subgroup (spinGroup Q)} (hR3 : Pow3 R) (hR'3 : Pow3 R') {fr : OFrame Q}
    (hR : R.map (spinAction Q) = fr.La.range) (hR' : R'.map (spinAction Q) = fr.swap.La.range)
    {g : spinGroup Q} (hg : spinAction Q g ∈ stabE fr) :
    ∀ J ∈ ({R, R'} : Set (Subgroup (spinGroup Q))),
      conjSub g J ∈ ({R, R'} : Set (Subgroup (spinGroup Q))) := by
  have hmap : ∀ J : Subgroup (spinGroup Q), (conjSub g J).map (spinAction Q) =
      conjSub (spinAction Q g) (J.map (spinAction Q)) := fun J => (conjSub_map _ _ _).symm
  obtain ⟨h1, h1'⟩ := La_conj_range h2 fr hg
  intro J hJ
  rcases hJ with rfl | hJ'
  · rcases h1 with h | h
    · left
      exact eq_of_map_eq_of_pow3 (spinAction Q) hker hcop (Pow3.conjSub g hR3) hR3
        (by rw [hmap, hR, h])
    · right
      exact eq_of_map_eq_of_pow3 (spinAction Q) hker hcop (Pow3.conjSub g hR3) hR'3
        (by rw [hmap, hR, h, hR'])
  · rw [Set.mem_singleton_iff] at hJ'
    subst hJ'
    rcases h1' with h | h
    · left
      exact eq_of_map_eq_of_pow3 (spinAction Q) hker hcop (Pow3.conjSub g hR'3) hR3
        (by rw [hmap, hR', h, hR])
    · right
      exact eq_of_map_eq_of_pow3 (spinAction Q) hker hcop (Pow3.conjSub g hR'3) hR'3
        (by rw [hmap, hR', h])

theorem mem_conjStabilizer_of_stabE3 (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q))
    (hcop : ∀ n ∈ (spinAction Q).ker, ¬ 3 ∣ orderOf n) (h2 : (2 : F) ≠ 0)
    {R R' : Subgroup (spinGroup Q)} (hR3 : Pow3 R) (hR'3 : Pow3 R') {fr : OFrame Q}
    (hR : R.map (spinAction Q) = fr.La.range) (hR' : R'.map (spinAction Q) = fr.swap.La.range)
    {g : spinGroup Q} (hg : spinAction Q g ∈ stabE fr) :
    g ∈ CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
      ({R, R'} : Set (Subgroup (spinGroup Q))) := by
  rw [CFSG.ClassicalInvolution.G2D4Models.mem_conjStabilizer_iff]
  intro J
  constructor
  · intro hJ
    have hg' : spinAction Q g⁻¹ ∈ stabE fr := by
      rw [map_inv]
      exact (stabE fr).inv_mem hg
    have := conj_pair_mem3 hker hcop h2 hR3 hR'3 hR hR' hg' (conjSub g J) hJ
    rwa [conjSub_inv_conjSub] at this
  · exact conj_pair_mem3 hker hcop h2 hR3 hR'3 hR hR' hg J

end Lift

section Coatom

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] {Q : QuadraticForm F (ι → F)}

theorem isCoatom_conjStabilizer3 {𝓕 : Set (Subgroup (spinGroup Q))} (c : PairCtx3 Q 𝓕)
    (hpos : ∀ fr : OFrame Q, 1 ≤ Module.finrank F fr.perp)
    (hmax : ∀ fr : OFrame Q, ∀ H : Subgroup ((ι → F) ≃ₗ[F] (ι → F)), stabE fr ≤ H →
      H ≤ elementaryGroup Q → (∃ h ∈ H, ¬ ∀ y ∈ wPlane fr, h y ∈ wPlane fr) →
        elementaryGroup Q ≤ H)
    {R R' : Subgroup (spinGroup Q)} {x x' : spinGroup Q} (hd : PairData3 𝓕 R R' x x') :
    IsCoatom (CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
      ({R, R'} : Set (Subgroup (spinGroup Q)))) := by
  classical
  have := c.perfect
  have hker := ker_spinAction_le_center Q
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card c.hodd
  have hR3 : Pow3 R := c.hpow3 R hd.mem
  have hR'3 : Pow3 R' := c.hpow3 R' hd.mem'
  have huniq : R.map (spinAction Q) = R'.map (spinAction Q) → R = R' := fun h =>
    eq_of_map_eq_of_pow3 (spinAction Q) hker c.hcop hR3 hR'3 h
  obtain ⟨fr, hR, hR', -, -⟩ := Q3TY.exists_pair_frame3 c.hodd c.hrange c.hZ
    c.hV c.hproj huniq (c.hcorr R hd.mem) (c.hcorr R' hd.mem')
    (c.hnc R hd.mem) (c.hnc R' hd.mem') hd.ne hd.hx hd.cx hd.nx hd.hx' hd.cx' hd.nx' hd.same
  have hN : ∀ g : spinGroup Q, g ∈ CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
      ({R, R'} : Set (Subgroup (spinGroup Q))) ↔ spinAction Q g ∈ stabE fr := fun g =>
    ⟨stabE_of_mem_conjStabilizer c.hodd c.hrange hR hR',
      mem_conjStabilizer_of_stabE3 hker c.hcop h2 hR3 hR'3 hR hR'⟩
  have h1 := hpos fr
  refine ⟨?_, fun M hM => ?_⟩
  · intro htop
    obtain ⟨a, ha, ha0⟩ : ∃ a ∈ fr.perp, a ≠ 0 := by
      refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
      rw [h, finrank_bot] at h1
      omega
    have hEa : eichler Q fr.e₁ a ∈ (spinAction Q).range := by
      rw [c.hrange]
      exact eichler_mem_elementaryGroup Q _ _
    obtain ⟨g, hg⟩ := hEa
    have hgN : g ∈ CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
        ({R, R'} : Set (Subgroup (spinGroup Q))) := by
      rw [htop]
      trivial
    have hgW := (hN g).mp hgN
    rw [hg] at hgW
    have hpolar : polar Q fr.e₁ a = 0 := polar_wPlane_perp ha (e₁_mem_wPlane fr)
    have hmem := ((mem_stabE.mp hgW).2 fr.f₁).mp (f₁_mem_wPlane fr)
    rw [eichler_apply fr.Q_e₁ hpolar] at hmem
    have h0 := pA_of_mem hmem
    rw [map_sub, map_add, map_smul, map_smul, pA_of_mem (f₁_mem_wPlane fr),
      pA_of_mem (e₁_mem_wPlane fr), pA_of_mem_perp ha, fr.polar_f₁_e₁] at h0
    simp at h0
    exact ha0 h0
  · obtain ⟨h, hhM, hhN⟩ := IsConcreteLE.exists_of_lt hM
    have hhE : spinAction Q h ∈ elementaryGroup Q := by
      rw [← c.hrange]
      exact ⟨h, rfl⟩
    have hhθ : ¬ ∀ y ∈ wPlane fr, spinAction Q h y ∈ wPlane fr := fun hall =>
      hhN ((hN h).mpr ⟨hhE, mem_stabSub_of_mapsTo hall⟩)
    have hHE : M.map (spinAction Q) ≤ elementaryGroup Q := by
      rw [← c.hrange]
      exact Subgroup.map_le_range _ _
    have hH : stabE fr ≤ M.map (spinAction Q) := by
      intro y hy
      obtain ⟨g, hg⟩ : y ∈ (spinAction Q).range := by
        rw [c.hrange]
        exact hy.1
      exact ⟨g, hM.le ((hN g).mpr (hg ▸ hy)), hg⟩
    have hEle := hmax fr (M.map (spinAction Q)) hH hHE
      ⟨spinAction Q h, Subgroup.mem_map_of_mem _ hhM, hhθ⟩
    have hsup : M ⊔ Subgroup.center (spinGroup Q) = ⊤ := by
      rw [eq_top_iff]
      intro k _
      have hk : spinAction Q k ∈ elementaryGroup Q := by
        rw [← c.hrange]
        exact ⟨k, rfl⟩
      obtain ⟨m, hm, hmk⟩ := hEle hk
      refine Subgroup.mem_sup_of_normal_right.mpr ⟨m, hm, m⁻¹ * k, hker ?_, mul_inv_cancel_left m k⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmk, inv_mul_cancel]
    exact eq_top_of_sup_center_eq_top_of_isPerfect' hsup

end Coatom

section Rows

open CFSG.GroupTheory.WeirSylow (IsPlusType not_isPlusType_quadMinus)
open CFSG.ClassicalInvolution.Q3.Q3TWY (centralQuot3_odd)
open CFSG.ClassicalInvolution.Q3.Q3TY (centralQuot3_minus)
open CFSG.ClassicalInvolution.ModelFacts.TG3 (hproj_odd hproj_minus)
open CFSG.LieType.Universal.Spin.Twisted (minusDatum)


theorem pairCtx3_odd3 :
    PairCtx3 (quadOdd 3 𝔽₃) (fundamentalSubgroups .POmegaOdd (oddDatum 3 𝔽₃)) := by
  have hm : 3 ≤ 3 := le_rfl
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 := ⟨Nat.prime_three, le_rfl, hm, by norm_num⟩
  have cq := centralQuot3_odd (m := 3) hm
  have hY := Q3W.yData3_odd hm hadm
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hdim := Gaps.finrank_odd 3 1 3
  exact ⟨odd_gf3, nondegenerate_polarBilin_quadOdd 3 _ h2, range_spinAction_quadOdd h2 hm,
    isPerfect_spinGroup_quadOdd h2 hm, centerScalar_quadOdd h2 hm, by omega,
    fun F₁ F₂ h => hproj_odd F₁ F₂ h, cq.cop, cq.map_mem, cq.pow3, hY.central⟩

theorem pairCtx3_minus4 : PairCtx3 (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
    (fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1))) := by
  have hirr := minusCoeffs_irr 3 1
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_refl 4⟩
  have cq := centralQuot3_minus hadm
  have hY := Q3W.yData3_minus (le_refl 4) hadm
  have hdim := Gaps.finrank_minus 3 1 4 (by omega)
  exact ⟨odd_gf3, nondegenerate_polarBilin_quadMinus_of_finite 4 _ hirr,
    range_spinAction_quadMinus (le_refl 4) hirr, isPerfect_spinGroup_quadMinus (le_refl 4) hirr,
    centerScalar_quadMinus (le_refl 4) hirr, by omega,
    fun F₁ F₂ h => hproj_minus hirr (le_refl 4) F₁ F₂ h, cq.cop, cq.map_mem, cq.pow3,
    hY.central⟩

theorem twinPairMax3_odd3 : TwinPairMax3 .POmegaOdd 3 := by
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadOdd 3 𝔽₃), oddDatum 3 𝔽₃⟩ →
      ∀ {R R' : Subgroup M.K} {x x' : M.K}, TwinDatumOn .POmegaOdd M R R' x x' →
        IsCoatom (CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
          ({R, R'} : Set (Subgroup M.K))) := by
    intro M hM
    subst hM
    intro R R' x x' hd
    have hdim := Gaps.finrank_odd 3 1 3
    have hperp : ∀ fr : OFrame (quadOdd 3 𝔽₃), Module.finrank 𝔽₃ fr.perp = 3 := fun fr => by
      have := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
      omega
    exact isCoatom_conjStabilizer3 pairCtx3_odd3 (fun fr => by have := hperp fr; omega)
      (fun fr H hH hHE hh => by
        obtain ⟨h, hhH, hhW⟩ := hh
        exact elementaryGroup_le_of_not_maps odd_gf3 pairCtx3_odd3.hQ fr hH hHE
          (by have := hperp fr; omega) (Or.inl (by have := hperp fr; omega)) hhH hhW)
      (pairData3_of_datum hd)
  intro R R' x x' hd
  exact key _ rfl hd

theorem twinPairMax3_minus4 : TwinPairMax3 .POmegaMinus 4 := by
  have hirr := minusCoeffs_irr 3 1
  have hdim := Gaps.finrank_minus 3 1 4 (by omega)
  have hP : ¬ IsPlusType (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) :=
    not_isPlusType_quadMinus (by omega) hirr
  have hperp : ∀ fr : OFrame (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
      Module.finrank 𝔽₃ fr.perp = 4 := fun fr => by
    have := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    omega
  intro R R' x x' hd
  exact isCoatom_conjStabilizer3 pairCtx3_minus4 (fun fr => by have := hperp fr; omega)
    (fun fr H hH hHE hh => by
      obtain ⟨h, hhH, hhW⟩ := hh
      exact elementaryGroup_le_of_not_maps odd_gf3 pairCtx3_minus4.hQ fr hH hHE
        (by have := hperp fr; omega)
        (Or.inr (noTotSing_of_not_isPlusType hP hdim fr)) hhH hhW)
    (pairData3_of_datum hd)

end Rows

end CFSG.ClassicalInvolution.Q3.Q3TZ
