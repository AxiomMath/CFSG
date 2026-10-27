module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNF4Two
public import CFSG.HardMathSupport.Curtis.Coordinator.ExcLeafDefs
public import CFSG.HardMathSupport.Foote.E27.SporCentKill
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndPerm

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Foote.E27 TauCeti
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
open CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf (IdxExc)


@[expose] def NFixF4NLevel : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (L : Type) [Field L] [Algebra F L] [IsAlgClosure F L]
    (Fr : L →+* L), (∀ c, Fr c = c ^ Nat.card F) → 3 ∣ Nat.card F + 1 →
    ∀ w0 : WeylGroup Tag.F4, (∀ u : Fin Tag.F4.rank → ℤ, w0 • u = -u) →
    ∀ s : NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr, s ^ 3 = 1 → s ≠ 1 →
      81 ∣ Nat.card (Subgroup.centralizer
        ({s} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)))


theorem innerLeaf_F4_two_of_nlevel (hN : NFixF4NLevel) : InnerLeaf (IdxExc .F4 2) := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hq, hr, rfl⟩ := hd
  obtain ⟨ψ⟩ := e
  obtain ⟨F, _, _, hF, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  have h3 : 3 ∣ Nat.card F + 1 := by rw [hF]; omega
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hℓ⟩
  have hqF : Nat.card F = ringChar F ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP F (ringChar F) := ringChar.charP F
  let L := AlgebraicClosure F
  let Fr : L →+* L := iterateFrobenius L (ringChar F) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card F := fun c => by
    rw [hqF]
    exact iterateFrobenius_def (ringChar F) (f : ℕ) c
  obtain ⟨w0, hw0⟩ := exists_weyl_neg_F4
  have : Finite ↥(adjointGroup Tag.F4 F) := generated_group_finite Tag.F4 F
  obtain ⟨ι, hι, P, -, hPcard⟩ := exists_F4_two_sylow (L := L) Fr hFr h3 hw0
  refine h.false_of_centralizer_kill hz (ψ.trans ε) (P.map ι) ?_ ?_
  · rw [Subgroup.card_map_of_injective hι, hPcard]
  · rintro _ ⟨s, -, rfl⟩ hs3 hs1
    have hs3' : s ^ 3 = 1 := hι (by rw [map_pow, hs3, map_one])
    have hs1' : s ≠ 1 := fun h1 => hs1 (by rw [h1, map_one])
    exact (hN F L Fr hFr h3 w0 hw0 s hs3' hs1').trans
      (CFSG.OddStandard.card_centralizer_dvd_of_injective ι hι s)

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
