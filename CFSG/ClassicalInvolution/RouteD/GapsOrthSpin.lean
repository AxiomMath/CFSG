module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel
public import CFSG.ClassicalInvolution.RouteD.GapsOrthTransfer
public import CFSG.ClassicalInvolution.RouteD.TypeDLocal
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (Frame IsFundamental)
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv
  FundamentalSingleClass)
open CFSG.ClassicalInvolution.ModelFacts (map_conj_map map_longSL2_range La_range_eq_map_conj)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Dict

variable {m : ℕ}

theorem spinAction_center_mem_scalars {K : Type} [Field K] (hm : 3 ≤ m)
    {z : spinGroup (quadPlus m K)} (hz : z ∈ Subgroup.center (spinGroup (quadPlus m K))) :
    spinAction (quadPlus m K) z ∈ scalars K (Fin m ⊕ Fin m → K) := by
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := K) hm
  have hz' : z ∈ (spinToStatedProj (quadPlus m K) (range_spinMatrix_quadPlus hm)).ker := hZ ▸ hz
  rw [hcomap, Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hz'
  exact hz'

variable (p f) in
theorem finrank_plus (m : ℕ) :
    Module.finrank (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

theorem map_mem_fundSet (hm3 : 3 ≤ m)
    (hsc : FundamentalSingleClass .POmegaPlus (plusDatum m (GaloisField p f) hm3))
    {R : Subgroup (spinGroup (quadPlus m (GaloisField p f)))}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3)) :
    R.map (spinAction (quadPlus m (GaloisField p f))) ∈ fundSet (quadPlus m (GaloisField p f)) := by
  set k₀ : Fin m := ⟨0, by omega⟩ with hk₀
  have hR₀ := rankOne_mem_fundamentalSubgroups_plusDatum (K := GaloisField p f) hm3 k₀
  obtain ⟨g, rfl⟩ := hsc _ hR₀ R hR
  have hR₀eq : CFSG.LieType.CurtisTits.rankOne (plusDatum m (GaloisField p f) hm3).rootGroup k₀ =
      (rankOneD (GaloisField p f) hm3 k₀).range :=
    PlusCT.rankOne_plusRootGroup hm3 k₀
  have hfr := map_longSL2_range (plusFrame m (GaloisField p f) hm3)
    (rootIdxD_ne m (by omega) k₀) true (rootSignD m k₀)
  have hg : spinAction (quadPlus m (GaloisField p f)) g ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus m (GaloisField p f)) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ g v
  have key : (conjSub g (CFSG.LieType.CurtisTits.rankOne
        (plusDatum m (GaloisField p f) hm3).rootGroup k₀)).map
      (spinAction (quadPlus m (GaloisField p f))) =
      (((plusFrame m (GaloisField p f) hm3).toFrame (rootIdxD_ne m (by omega) k₀) true
        (rootSignD m k₀)).La.range).map
        (MulAut.conj (spinAction (quadPlus m (GaloisField p f)) g)).toMonoidHom := by
    show (((CFSG.LieType.CurtisTits.rankOne (plusDatum m (GaloisField p f) hm3).rootGroup k₀).map
      (MulAut.conj g).toMonoidHom).map (spinAction (quadPlus m (GaloisField p f)))) = _
    rw [map_conj_map, hR₀eq]
    exact congrArg (Subgroup.map _) hfr
  rw [key]
  exact ⟨_, IsFundamental.conj hg (IsFundamental.of_frame _)⟩

theorem exists_map_eq (hm3 : 3 ≤ m) (hodd : Odd (Nat.card (GaloisField p f)))
    {L : Subgroup (((Fin m ⊕ Fin m → GaloisField p f)) ≃ₗ[GaloisField p f]
      (Fin m ⊕ Fin m → GaloisField p f))}
    (hL : L ∈ fundSet (quadPlus m (GaloisField p f))) :
    ∃ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3),
      R.map (spinAction (quadPlus m (GaloisField p f))) = L := by
  obtain ⟨i, fr, rfl, -⟩ := hL
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  set k₀ : Fin m := ⟨0, by omega⟩ with hk₀
  have hR₀ := rankOne_mem_fundamentalSubgroups_plusDatum (K := GaloisField p f) hm3 k₀
  have hR₀eq : CFSG.LieType.CurtisTits.rankOne (plusDatum m (GaloisField p f) hm3).rootGroup k₀ =
      (rankOneD (GaloisField p f) hm3 k₀).range :=
    PlusCT.rankOne_plusRootGroup hm3 k₀
  have hfr := map_longSL2_range (plusFrame m (GaloisField p f) hm3)
    (rootIdxD_ne m (by omega) k₀) true (rootSignD m k₀)
  set fr₀ := (plusFrame m (GaloisField p f) hm3).toFrame (rootIdxD_ne m (by omega) k₀) true
    (rootSignD m k₀) with hfr₀
  have : Nontrivial (Fin m ⊕ Fin m → GaloisField p f) := ⟨⟨fr₀.e₁, 0, fr₀.P.e_ne_zero⟩⟩
  have hperp : 2 ≤ Module.finrank (GaloisField p f) fr₀.perp := by
    have h1 := ModelFacts.finrank_perp_add_four fr₀
    have h3 := finrank_plus p f m
    omega
  obtain ⟨x, hx⟩ := ModelFacts.exists_spin_conj hodd
    (nondegenerate_polarBilin_quadPlus m (GaloisField p f)) fr₀ fr hperp
  refine ⟨conjSub x (CFSG.LieType.CurtisTits.rankOne
    (plusDatum m (GaloisField p f) hm3).rootGroup k₀), conjSub_mem_fundamentalSubgroups hR₀ x, ?_⟩
  show (((CFSG.LieType.CurtisTits.rankOne (plusDatum m (GaloisField p f) hm3).rootGroup k₀).map
      (MulAut.conj x).toMonoidHom).map (spinAction (quadPlus m (GaloisField p f)))) = _
  rw [map_conj_map, hR₀eq, La_range_eq_map_conj hx]
  exact congrArg (Subgroup.map _) hfr

end Dict

section Facts

variable {m : ℕ}

theorem not_dvd_card_center_plus (hp2 : p ≠ 2) (hm3 : 3 ≤ m) :
    ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus m (GaloisField p f)))) := by
  have : NeZero m := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus m (GaloisField p f))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadPlus (K := GaloisField p f) hm3
  exact ModelFacts.OrthAut.not_dvd_card_center_spin (quadPlus m (GaloisField p f))
    (range_spinMatrix_quadPlus hm3) hZ hcomap
    (fun x hx => ModelFacts.OrthAut.spin_mul_self_eq_one
      ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2

theorem centralQuot_plus (hp2 : p ≠ 2) (hm : 4 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    CentralQuot (spinAction (quadPlus m (GaloisField p f)))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3))
      (fundSet (quadPlus m (GaloisField p f)))
      (scalars (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f)) := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf1, hm⟩
  have hY := RouteD.yData_plus (p := p) (f := f) hm hadm (by omega)
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) hm3
  have hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3),
      R ≤ ⁅R, R⁆ := by
    have := hY.perfR
    rw [e] at this
    exact this
  have hcentral : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus m (GaloisField p f))) → r = 1 := by
    have := hY.central
    rw [e] at this
    exact this
  have hsc : FundamentalSingleClass .POmegaPlus (plusDatum m (GaloisField p f) hm3) := by
    have := hY.sc
    rw [e] at this
    exact this
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [(RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)).2]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hker := ker_spinAction_le_center (quadPlus m (GaloisField p f))
  exact
    { ker_le := hker
      center_le := fun z hz => spinAction_center_mem_scalars hm3 hz
      perf := fun R hR => le_antisymm
        (Subgroup.commutator_le.mpr fun a ha b hb =>
          R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) (hperf R hR)
      inj := fun R hR r hr h1 => hcentral R hR r hr (hker h1)
      map_mem := fun R hR => map_mem_fundSet hm3 hsc hR
      surj := fun L hL => exists_map_eq hm3 hodd hL }

theorem orthFacts_plusDatum (hp2 : p ≠ 2) (hm : 5 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    OrthFacts (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3))
      (GaloisField p f) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hK' : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hK]
    omega
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have hG := orthGeom_model (K' := GaloisField p (2 * f)) hK hK' hodd
    (nondegenerate_polarBilin_quadPlus m (GaloisField p f)) hdim
  have : NeZero m := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus m (GaloisField p f))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  exact (centralQuot_plus hp2 (by omega) hm3 hq).orthFacts h4 (not_dvd_card_center_plus hp2 hm3) hG

theorem orthFacts_plus (hp2 : p ≠ 2) (hm : 5 ≤ m) (hq : 5 ≤ p ^ f) :
    OrthFacts (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D)
      (GaloisField p f) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) (by omega : 3 ≤ m)
  rw [e]
  exact orthFacts_plusDatum hp2 hm (by omega) hq

end Facts

end CFSG.ClassicalInvolution.RouteD.Gaps
