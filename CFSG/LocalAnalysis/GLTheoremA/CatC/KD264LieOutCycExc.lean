module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCyc
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.RankThree.PartOne.MB3.OddOutExceptional
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Diag
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ElevenRotCheckDefs

public section

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.OutStructure CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.TauCetiBridge CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.HardMathSupport.Dickson.Sec6.I923

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


private theorem mem_innAutDerived_of_e6_field_part_eq_one {K : Type} [Field K] [Finite K]
    (Θ : MulAut (adjointGroup Tag.E6 K) →*
      RingAut K × Multiplicative (ZMod (exactE Tag.E6)))
    (hker : ∀ α : MulAut (adjointGroup Tag.E6 K), α ∈ Θ.ker ↔
      ∃ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
        ∀ h : adjointGroup Tag.E6 K,
          (α h : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a *
            (h : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 a)⁻¹ * (g : ModGL Tag.E6 K)⁻¹)
    {x : MulAut (adjointGroup Tag.E6 K)} (hfield : (Θ x).1 = 1) (hx3 : x ^ 3 = 1) :
    x ∈ innAutDerived (adjointGroup Tag.E6 K) := by
  have hΘ3 : Θ x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hxprod : Θ x = (1, (Θ x).2) := Prod.ext hfield rfl
  have hy3 : (Θ x).2 ^ 3 = 1 := by
    rw [hxprod] at hΘ3
    simpa using hΘ3
  have hcard : Nat.card (Multiplicative (ZMod (exactE Tag.E6))) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rfl
  have hy2 : (Θ x).2 ^ 2 = 1 := by
    simpa [hcard] using pow_card_eq_one' (x := (Θ x).2)
  have hy1 : (Θ x).2 = 1 := by
    have h : (Θ x).2 ^ 3 * ((Θ x).2 ^ 2)⁻¹ = 1 := by rw [hy3, hy2]; simp
    rwa [show (Θ x).2 ^ 3 * ((Θ x).2 ^ 2)⁻¹ = (Θ x).2 by group] at h
  have hΘx : Θ x = 1 := Prod.ext hfield hy1
  obtain ⟨g, a, hga⟩ := (hker x).mp (MonoidHom.mem_ker.mpr hΘx)
  have hxeq : x = MulAut.conj g * rootDiagAutHom Tag.E6 K a := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hga h]
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      rootDiagAutHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_rootDiagAut]
    group
  rw [hxeq]
  exact (innAutDerived _).mul_mem (inner_le_innAutDerived _ ⟨g, rfl⟩)
    (commutator_le_innAutDerived _
      (e6Inndiag_le_commutator K (Subgroup.mem_sup_right ⟨a, rfl⟩)))

private theorem outCycAt_e6_three {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) :
    OutCycAt 3 (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans q.card_def
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK']; exact pow_ne_zero _ q.prime_p.ne_zero)
  haveI : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic q.prime_p K hK').2
  obtain ⟨Θ, -, -, hker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  let φ : (⊤ : Subgroup (MulAut (adjointGroup Tag.E6 K))) →* RingAut K :=
    { toFun := fun x => (Θ (x : MulAut (adjointGroup Tag.E6 K))).1
      map_one' := by simp
      map_mul' := by intro x y; simp }
  refine outCycAt_of_mulEquiv e.symm
    (outCycAt_of_cyclic Nat.prime_three ⊤ (fun _ _ => Subgroup.mem_top _) φ ?_)
  intro x hx hx3
  exact mem_innAutDerived_of_e6_field_part_eq_one Θ hker hx hx3

private theorem outCycAt_g2 (p : ℕ) (hp : p.Prime) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) :
    OutCycAt p (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  have hq3 : 3 ≤ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
      ((TauCeti.LieTypeIndex.valid_iff (.G2 q)).1 hv).1
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 q.p
      q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, hq3⟩,
      untwistedChevalleyModel_of_bridge Even.chevalleyBridgesAll.g2 (MulEquiv.refl _)⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
    CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ .G2 q.p q.exponent hm
  by_cases h2 : q.p = 2
  · rw [h2] at hm
    exact outCycAt_of_outPChain hp (outPNice_G2 hp hm).toChain
  · by_cases h3 : q.p = 3
    · rw [h3] at hm
      exact outCycAt_of_outPChain hp (outPNice_G2_three hp hm).toChain
    · exact outCycAt_of_outPChain hp (outPNice_G2_odd hp h2 h3 hm).toChain

private theorem outCycAt_f4 (p : ℕ) (hp : p.Prime) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) :
    OutCycAt p (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group := by
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group .F4 q.p
      q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      untwistedChevalleyModel_of_bridge Even.chevalleyBridgesAll.f4 (MulEquiv.refl _)⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group :=
    CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ .F4 q.p q.exponent hm
  by_cases h2 : q.p = 2
  · rw [h2] at hm
    exact outCycAt_of_outPChain hp (outPNice_F4 hp hm).toChain
  · exact outCycAt_of_outPChain hp (outPNice_F4_odd hp h2 hm).toChain

private theorem outCycAt_e6 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) :
    OutCycAt p (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group .E6 q.p
      q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      untwistedChevalleyModel_of_bridge Even.chevalleyBridgesAll.e6 (MulEquiv.refl _)⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group :=
    CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ .E6 q.p q.exponent hm
  by_cases h3p : p = 3
  · subst h3p
    exact outCycAt_e6_three hv
  · exact outCycAt_of_outPChain hp (outPNice_E6_gen hp h3p hp2 hm).toChain

private theorem outCycAt_e7 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) :
    OutCycAt p (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group := by
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group .E7 q.p
      q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      untwistedChevalleyModel_of_bridge Even.chevalleyBridgesAll.e7 (MulEquiv.refl _)⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group :=
    CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ .E7 q.p q.exponent hm
  exact outCycAt_of_outPChain hp (outPNice_E7_gen hp hp2 hm).toChain

private theorem outCycAt_e8 (p : ℕ) (hp : p.Prime) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) :
    OutCycAt p (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group := by
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group .E8 q.p
      q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      untwistedChevalleyModel_of_bridge Even.chevalleyBridgesAll.e8 (MulEquiv.refl _)⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group :=
    CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ .E8 q.p q.exponent hm
  exact outCycAt_of_outPChain hp (outPNice_E8_gen hp hm).toChain

theorem lieOutCyc_excUntwisted : LieOutCyc isExcUntwistedIdx := by
  intro d p hp hp2 _ hP
  obtain ⟨d, hd⟩ := d
  cases d with
  | G2 q => exact outCycAt_g2 p hp hd
  | F4 q => exact outCycAt_f4 p hp hd
  | E6 q => exact outCycAt_e6 p hp hp2 hd
  | E7 q => exact outCycAt_e7 p hp hp2 hd
  | E8 q => exact outCycAt_e8 p hp hd
  | A n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | twistedA n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | B n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | C n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | D n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | twistedD n q => exact absurd hP (by simp [isExcUntwistedIdx])
  | twistedE6 q => exact absurd hP (by simp [isExcUntwistedIdx])
  | trialityD4 q => exact absurd hP (by simp [isExcUntwistedIdx])
  | suzuki k => exact absurd hP (by simp [isExcUntwistedIdx])
  | reeG2 k => exact absurd hP (by simp [isExcUntwistedIdx])
  | reeF4 k => exact absurd hP (by simp [isExcUntwistedIdx])
  | tits => exact absurd hP (by simp [isExcUntwistedIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
