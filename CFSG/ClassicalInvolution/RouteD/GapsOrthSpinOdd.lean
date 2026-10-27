module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinBLocal
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel
public import CFSG.ClassicalInvolution.RouteD.GapsOrthTransfer

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

section DictOdd

variable {m : ℕ}

theorem spinAction_center_mem_scalars_odd {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (hm : 3 ≤ m)
    {z : spinGroup (quadOdd m K)} (hz : z ∈ Subgroup.center (spinGroup (quadOdd m K))) :
    spinAction (quadOdd m K) z ∈ scalars K (Fin m ⊕ Fin m ⊕ Unit → K) := by
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadOdd h2 hm
  have hz' : z ∈ (spinToStatedProj (quadOdd m K) (range_spinMatrix_quadOdd h2 hm)).ker := hZ ▸ hz
  rw [hcomap, Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hz'
  exact hz'

variable (p f) in
theorem finrank_odd (m : ℕ) :
    Module.finrank (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) = 2 * m + 1 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit]
  ring

theorem map_mem_fundSet_odd (hm3 : 3 ≤ m)
    (hsc : FundamentalSingleClass .POmegaOdd (oddDatum m (GaloisField p f)))
    {R : Subgroup (spinGroup (quadOdd m (GaloisField p f)))}
    (hR : R ∈ fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f))) :
    R.map (spinAction (quadOdd m (GaloisField p f))) ∈ fundSet (quadOdd m (GaloisField p f)) := by
  have hk : (0 : ℕ) + 1 < m := by omega
  set k₀ : Fin m := ⟨0, by omega⟩ with hk₀
  set j₀ : Fin m := ⟨0 + 1, hk⟩ with hj₀
  have hij : k₀ ≠ j₀ := Fin.ne_of_val_ne (by simp [hk₀, hj₀])
  have hR₀ := RouteD.rankOne_mem_fundamentalSubgroups_oddDatum (K := GaloisField p f) hm3
    (i := k₀) (by show 0 + 1 < m; omega)
  obtain ⟨g, rfl⟩ := hsc _ hR₀ R hR
  have hR₀eq : CFSG.LieType.CurtisTits.rankOne (oddDatum m (GaloisField p f)).rootGroup k₀ =
      ((oddFrame m (GaloisField p f)).toHypFrame.longSL2 hij true false).range := by
    have h1 : CFSG.LieType.CurtisTits.rankOne (oddRootGroup m (GaloisField p f)) k₀ =
        (rankOneB (GaloisField p f) k₀).range :=
      le_antisymm (OddCT.rankOne_le_range k₀) (by
        rintro _ ⟨M, rfl⟩
        exact OddCT.rankOneB_mem_rankOne k₀ M)
    rw [rankOneB_of_lt (GaloisField p f) hk rfl hij] at h1
    exact h1
  have hfr := map_longSL2_range (oddFrame m (GaloisField p f)).toHypFrame hij true false
  have hg : spinAction (quadOdd m (GaloisField p f)) g ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd m (GaloisField p f)) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ g v
  have key : (conjSub g (CFSG.LieType.CurtisTits.rankOne
        (oddDatum m (GaloisField p f)).rootGroup k₀)).map
      (spinAction (quadOdd m (GaloisField p f))) =
      (((oddFrame m (GaloisField p f)).toHypFrame.toFrame hij true false).La.range).map
        (MulAut.conj (spinAction (quadOdd m (GaloisField p f)) g)).toMonoidHom := by
    show (((CFSG.LieType.CurtisTits.rankOne (oddDatum m (GaloisField p f)).rootGroup k₀).map
      (MulAut.conj g).toMonoidHom).map (spinAction (quadOdd m (GaloisField p f)))) = _
    rw [map_conj_map, hR₀eq]
    exact congrArg (Subgroup.map _) hfr
  rw [key]
  exact ⟨_, IsFundamental.conj hg (IsFundamental.of_frame _)⟩

theorem exists_map_eq_odd (hm3 : 3 ≤ m) (hodd : Odd (Nat.card (GaloisField p f)))
    {L : Subgroup (((Fin m ⊕ Fin m ⊕ Unit → GaloisField p f)) ≃ₗ[GaloisField p f]
      (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f))}
    (hL : L ∈ fundSet (quadOdd m (GaloisField p f))) :
    ∃ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)),
      R.map (spinAction (quadOdd m (GaloisField p f))) = L := by
  obtain ⟨i, fr, rfl, -⟩ := hL
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hk : (0 : ℕ) + 1 < m := by omega
  set k₀ : Fin m := ⟨0, by omega⟩ with hk₀
  set j₀ : Fin m := ⟨0 + 1, hk⟩ with hj₀
  have hij : k₀ ≠ j₀ := Fin.ne_of_val_ne (by simp [hk₀, hj₀])
  have hR₀ := RouteD.rankOne_mem_fundamentalSubgroups_oddDatum (K := GaloisField p f) hm3
    (i := k₀) (by show 0 + 1 < m; omega)
  have hR₀eq : CFSG.LieType.CurtisTits.rankOne (oddDatum m (GaloisField p f)).rootGroup k₀ =
      ((oddFrame m (GaloisField p f)).toHypFrame.longSL2 hij true false).range := by
    have h1 : CFSG.LieType.CurtisTits.rankOne (oddRootGroup m (GaloisField p f)) k₀ =
        (rankOneB (GaloisField p f) k₀).range :=
      le_antisymm (OddCT.rankOne_le_range k₀) (by
        rintro _ ⟨M, rfl⟩
        exact OddCT.rankOneB_mem_rankOne k₀ M)
    rw [rankOneB_of_lt (GaloisField p f) hk rfl hij] at h1
    exact h1
  have hfr := map_longSL2_range (oddFrame m (GaloisField p f)).toHypFrame hij true false
  set fr₀ := (oddFrame m (GaloisField p f)).toHypFrame.toFrame hij true false with hfr₀
  have : Nontrivial (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) := ⟨⟨fr₀.e₁, 0, fr₀.P.e_ne_zero⟩⟩
  have hperp : 2 ≤ Module.finrank (GaloisField p f) fr₀.perp := by
    have h1 := ModelFacts.finrank_perp_add_four fr₀
    have h3 := finrank_odd p f m
    omega
  obtain ⟨x, hx⟩ := ModelFacts.exists_spin_conj hodd
    (nondegenerate_polarBilin_quadOdd m (GaloisField p f) h2) fr₀ fr hperp
  refine ⟨conjSub x (CFSG.LieType.CurtisTits.rankOne
    (oddDatum m (GaloisField p f)).rootGroup k₀), RouteD.conjSub_mem_fundamentalSubgroups hR₀ x, ?_⟩
  show (((CFSG.LieType.CurtisTits.rankOne (oddDatum m (GaloisField p f)).rootGroup k₀).map
      (MulAut.conj x).toMonoidHom).map (spinAction (quadOdd m (GaloisField p f)))) = _
  rw [map_conj_map, hR₀eq, La_range_eq_map_conj hx]
  exact congrArg (Subgroup.map _) hfr

end DictOdd

section FactsOdd

variable {m : ℕ}

theorem not_dvd_card_center_odd (hp2 : p ≠ 2) (hm3 : 3 ≤ m) :
    ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadOdd m (GaloisField p f)))) := by
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have : Finite (spinGroup (quadOdd m (GaloisField p f))) :=
    ModelFacts.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have : Nonempty (Fin m ⊕ Fin m ⊕ Unit) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadOdd h2 hm3
  exact ModelFacts.OrthAut.not_dvd_card_center_spin (quadOdd m (GaloisField p f))
    (range_spinMatrix_quadOdd h2 hm3) hZ hcomap
    (fun x hx => ModelFacts.OrthAut.spin_mul_self_eq_one
      ((mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx)) hp2

theorem centralQuot_odd (hp2 : p ≠ 2) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    CentralQuot (spinAction (quadOdd m (GaloisField p f)))
      (fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)))
      (fundSet (quadOdd m (GaloisField p f)))
      (scalars (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f)) := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd m p f := ⟨Fact.out, hf1, hm3, hp2⟩
  have hY := RouteD.yData_odd (p := p) (f := f) hm3 hadm (by omega)
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have hperf : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)),
      R ≤ ⁅R, R⁆ := hY.perfR
  have hcentral : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadOdd m (GaloisField p f))) → r = 1 :=
    hY.central
  have hsc : FundamentalSingleClass .POmegaOdd (oddDatum m (GaloisField p f)) := hY.sc
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [(RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)).2]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hker := ker_spinAction_le_center (quadOdd m (GaloisField p f))
  exact
    { ker_le := hker
      center_le := fun z hz => spinAction_center_mem_scalars_odd h2 hm3 hz
      perf := fun R hR => le_antisymm
        (Subgroup.commutator_le.mpr fun a ha b hb =>
          R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) (hperf R hR)
      inj := fun R hR r hr h1 => hcentral R hR r hr (hker h1)
      map_mem := fun R hR => map_mem_fundSet_odd hm3 hsc hR
      surj := fun L hL => exists_map_eq_odd hm3 hodd hL }

theorem orthFacts_oddDatum (hp2 : p ≠ 2) (hm : 4 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    OrthFacts (fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f)))
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
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hG := orthGeom_model (K' := GaloisField p (2 * f)) hK hK' hodd
    (nondegenerate_polarBilin_quadOdd m (GaloisField p f) h2) hdim
  have : Finite (spinGroup (quadOdd m (GaloisField p f))) :=
    ModelFacts.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  exact (centralQuot_odd hp2 hm3 hq).orthFacts h4 (not_dvd_card_center_odd hp2 hm3) hG

theorem orthFacts_odd (hp2 : p ≠ 2) (hm : 4 ≤ m) (hq : 5 ≤ p ^ f) :
    OrthFacts (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D)
      (GaloisField p f) :=
  orthFacts_oddDatum hp2 hm (by omega) hq

end FactsOdd

end CFSG.ClassicalInvolution.RouteD.Gaps
