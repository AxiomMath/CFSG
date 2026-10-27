module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Ord
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Pred
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralConj

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.Burgoyne.X10
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def ExcInnerNoPSL2 (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → NoPSL2Odd L

theorem NoPSL2Odd.of_central {C K : Type} [Group C] [Group K] [Finite C] (hq : IsQuasisimple C)
    (φ : C →* K) (hφ : Function.Surjective φ) (hker : φ.ker ≤ center C) (h : NoPSL2Odd K) :
    NoPSL2Odd C := by
  intro p f hp h5 hodd hC
  obtain ⟨e⟩ := center_quotient_equiv_of_surjective hq φ hφ hker
  exact h p f hp h5 (odd_card_center_of_surjective hq φ hφ hker hodd)
    (LieType.CurtisTits.lieModel_of_mulEquiv e hC)

theorem noPSL2Odd_of_simple_model (hO : LieOrderFormulasInput) {L Y : Type} [Group L] [Group Y]
    [IsSimpleGroup Y] (hnab : ∃ a b : Y, a * b ≠ b * a) (E : L ≃* Y) {t : StatedLieTag}
    {n r e : ℕ} (hr2 : r ≠ 2) (ht : ExcCompTag t n) (hA1 : ¬ (t = .PSL ∧ n = 2))
    (hadm : StatedLieAdmissible t n r e) (hY : LieModel Y t n r e) : NoPSL2Odd L := by
  refine NoPSL2Odd.of_mulEquiv E ?_
  have hZ : center Y = ⊥ := by
    obtain ⟨a, b, hab⟩ := hnab
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h | h
    · exact h
    · exact absurd ((mem_center_iff.mp (h ▸ mem_top a)) b).symm hab
  let eY : Y ⧸ center Y ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact noPSL2Odd_of_lieModel hO hr2 ht hA1 hadm
    (LieType.CurtisTits.lieModel_of_mulEquiv eY.symm hY)

theorem noPSL2Odd_of_component_equiv {X Y : Type} [Group X] [Group Y] (Φ : X ≃* Y)
    (h : ∀ M : Subgroup Y, IsComponent M → NoPSL2Odd M) {L : Subgroup X} (hL : IsComponent L) :
    NoPSL2Odd L :=
  (h _ (LocalCores.isComponent_map_mulEquiv Φ hL)).of_mulEquiv
    (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)

theorem noPSL2Odd_toralCentralizer_component_of_orbitCheck
    {τ : Tag} {K : Type} [Field K] (hK2 : ringChar K ≠ 2)
    {reps : List (List Bool)} {entries : List (List Bool × ℕ × List ℕ)}
    (hcert : OrbitCheck τ reps entries)
    (hreps : ∀ ρ < reps.length, listMask (τ := τ) (reps.getD ρ []) ≠ (fun _ => false) →
      ∀ N : Subgroup (toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ [])))),
        IsComponent N → NoPSL2Odd N)
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1)
    {M : Subgroup (toralCentralizer τ K b)} (hM : IsComponent M) : NoPSL2Odd M := by
  obtain ⟨ρ, hρ, w, hw, hmap⟩ := exists_conj_toralCentralizer_of_orbitCheck hK2 hcert hb
  by_cases h0 : listMask (τ := τ) (reps.getD ρ []) = fun _ => false
  · refine absurd (eq_one_of_rootChar_smul_eq_one (w := w) fun v => ?_) hb1
    rw [hw v]
    congr 1
    funext i
    change (if listMask (τ := τ) (reps.getD ρ []) i then (-1 : Kˣ) else 1) = 1
    rw [h0]
    rfl
  · let e : toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ []))) ≃*
        toralCentralizer τ K b :=
      ((toralCentralizer τ K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact NoPSL2Odd.of_mulEquiv (M.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective) (hreps ρ hρ h0 _ (LocalCores.isComponent_map_mulEquiv e.symm hM))

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
