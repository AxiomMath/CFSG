module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)

private theorem i167CS_card_B2der_aux1 {K : Type} [Field K] [Finite K]
    (hKcard : Nat.card K = 2) :
    Nat.card (CFSG.Assembly.LargeEvenProj
      ⁅CFSG.Assembly.LargeEvenSpGroup K 2, CFSG.Assembly.LargeEvenSpGroup K 2⁆) ≤ 720 := by
  let C : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
    ⁅CFSG.Assembly.LargeEvenSpGroup K 2, CFSG.Assembly.LargeEvenSpGroup K 2⁆
  have hle : Nat.card (CFSG.Assembly.LargeEvenProj C) ≤ 720 := by
    calc
      Nat.card (CFSG.Assembly.LargeEvenProj C) ≤ Nat.card ↥C :=
        Nat.card_le_card_of_surjective (QuotientGroup.mk' _)
          (QuotientGroup.mk'_surjective
            (N := (CFSG.Assembly.LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf C))
      _ ≤ Nat.card (CFSG.Assembly.LargeEvenSpGroup K 2) := by
        exact Nat.card_le_card_of_injective
          (fun x : ↥C =>
            (⟨x.1, Subgroup.commutator_le_self (CFSG.Assembly.LargeEvenSpGroup K 2) x.2⟩ :
              ↥(CFSG.Assembly.LargeEvenSpGroup K 2)))
          (fun x y h => Subtype.ext
            (congrArg (fun z : ↥(CFSG.Assembly.LargeEvenSpGroup K 2) =>
              (z : GL (Fin 2 ⊕ Fin 2) K)) h))
      _ = 720 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hKcard]
        norm_num
  simpa [C] using hle

theorem i167CS_card_B2der {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (htag : labK.tag = .B2der) (hin : InnDiagKind S labK α) :
    Nat.card S ≤ 720 := by
  unfold CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind
    CFSG.Assembly.LargeEvenMarking at hin
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨R, hR, I, F, hcont⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hlab', -⟩ := hcont
  subst lab'
  rcases labK with ⟨tag, rank, n⟩
  simp only at htag
  cases htag
  simp only [CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeSymplectic] at hraw
  obtain ⟨K, hK, hKf, hKcard, hcont2⟩ := hraw
  let H : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
    if true = true then ⁅CFSG.Assembly.LargeEvenSpGroup K 2,
      CFSG.Assembly.LargeEvenSpGroup K 2⁆ else CFSG.Assembly.LargeEvenSpGroup K 2
  obtain ⟨-, -, θ, -⟩ := hcont2
  have hse : Nat.card S = Nat.card (CFSG.Assembly.LargeEvenProj H) := by
    rw [← Nat.card_congr θ.toEquiv]
    exact (Nat.card_congr
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).toEquiv).symm
  rw [hse]
  simpa [H] using i167CS_card_B2der_aux1 hKcard

end CFSG.LocalAnalysis.GLTheoremA.I167

end
