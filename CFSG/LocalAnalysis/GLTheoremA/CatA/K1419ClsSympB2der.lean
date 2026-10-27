module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsSympCard

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem k1419ClsSympB2der : K1419ClsAt (fun l : GLALabel => l.tag = .B2der) := by
  intro S _ _ α J labK htag hcen hα3 hα1 hin hJc hcat hZ
  have hcardS : Nat.card S ≤ 720 := by
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
    let C : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
      ⁅CFSG.Assembly.LargeEvenSpGroup K 2, CFSG.Assembly.LargeEvenSpGroup K 2⁆
    let H : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
      if true = true then C else CFSG.Assembly.LargeEvenSpGroup K 2
    have hHdef : H = C := by
      change (if true = true then C else CFSG.Assembly.LargeEvenSpGroup K 2) = C
      rw [if_pos rfl]
    have hHle : Nat.card (CFSG.Assembly.LargeEvenProj H) ≤ 720 := by
      calc
        Nat.card (CFSG.Assembly.LargeEvenProj H) ≤ Nat.card ↥H :=
          Nat.card_le_card_of_surjective (QuotientGroup.mk' _)
            (QuotientGroup.mk'_surjective
              (N := (CFSG.Assembly.LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H))
        _ ≤ Nat.card (CFSG.Assembly.LargeEvenSpGroup K 2) := by
          rw [hHdef]
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
    obtain ⟨-, -, θ, -⟩ := hcont2
    have hse : Nat.card S = Nat.card (CFSG.Assembly.LargeEvenProj H) := by
      rw [← Nat.card_congr θ.toEquiv]
      exact (Nat.card_congr
        ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).toEquiv).symm
    rw [hse]
    exact hHle
  have hsimple : IsSimpleGroup (PSimple 3 J) :=
    (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJc).2
  have hlarge : 720 < Nat.card (PSimple 3 J) := k1419ClsSympCard hsimple hcat
  have hsurj : Function.Surjective (fun x : ↥J =>
      QuotientGroup.mk' (Subgroup.center (PQuot 3 J))
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) x)) :=
    (QuotientGroup.mk'_surjective (N := Subgroup.center (PQuot 3 J))).comp
      (QuotientGroup.mk'_surjective (N := GLAPPrimeCore 3 ↥J))
  have hleJ : Nat.card (PSimple 3 J) ≤ Nat.card ↥J :=
    Nat.card_le_card_of_surjective _ hsurj
  have hleS : Nat.card ↥J ≤ Nat.card S :=
    Nat.card_le_card_of_injective (fun x : ↥J => (x : S)) Subtype.val_injective
  exact absurd (le_trans hleJ hleS) (not_le.mpr (lt_of_le_of_lt hcardS hlarge))

end CFSG.LocalAnalysis.GLTheoremA.K1419
