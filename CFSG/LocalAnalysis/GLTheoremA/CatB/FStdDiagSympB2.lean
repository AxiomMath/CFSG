module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd)

theorem fstdSymp_b2der_model {S : Type} [Group S] {labK : GLALabel} {α : MulAut S}
    (htag : labK.tag = .B2der) (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labK α) :
    commutator S = ⊤ ∧ Nat.card S ≤ 720 := by
  unfold InnDiagKind CFSG.Assembly.LargeEvenMarking at hin
  obtain ⟨hperf, lab', hlam, hraw⟩ := hin
  refine ⟨hperf, ?_⟩
  obtain ⟨R, hR, I, F, hcont⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hlab', -⟩ := hcont
  subst lab'
  rcases labK with ⟨tag, rank, n⟩
  simp only at htag
  cases htag
  simp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeSymplectic] at hraw
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

theorem fstdSymp_b2der_false {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    {I : Subgroup S} (htag : labK.tag = .B2der) (hcen : Subgroup.center S = ⊥) (hα1 : α ≠ 1)
    (hin : InnDiagKind S labK α) (hI : CFSG.Open.IsComponentOf I (fixSubgroup α))
    (hord : SmallOrd I) : False := by
  obtain ⟨hperf, hcardS⟩ := fstdSymp_b2der_model htag hcen hin
  have hI360 : 360 ≤ Nat.card ↥I := by
    have hle : Nat.card (↥I ⧸ Subgroup.center ↥I) ≤ Nat.card ↥I :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    rcases hord with h | h <;> omega
  have hIC : Nat.card ↥I ≤ Nat.card ↥(fixSubgroup α) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hI.1) (Subgroup.inclusion_injective hI.1)
  have hC1 : fixSubgroup α ≠ ⊤ := by
    intro h
    apply hα1
    ext s
    have hs : s ∈ fixSubgroup α := by rw [h]; exact Subgroup.mem_top s
    simpa using (CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup).1 hs
  have hi1 : (fixSubgroup α).index ≠ 1 := fun h => hC1 (Subgroup.index_eq_one.1 h)
  have hi0 : (fixSubgroup α).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul : Nat.card ↥(fixSubgroup α) * (fixSubgroup α).index = Nat.card S :=
    Subgroup.card_mul_index _
  have h2 : (fixSubgroup α).index = 2 := by
    by_contra hne
    have h3 : 3 ≤ (fixSubgroup α).index := by omega
    have : 360 * 3 ≤ Nat.card ↥(fixSubgroup α) * (fixSubgroup α).index :=
      Nat.mul_le_mul (by omega) h3
    omega
  haveI : (fixSubgroup α).Normal := Subgroup.normal_of_index_eq_two h2
  have hcyc : IsCyclic (S ⧸ fixSubgroup α) :=
    isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, h2])
  letI : CommGroup (S ⧸ fixSubgroup α) := IsCyclic.commGroup
  have hcomm : commutator S ≤ fixSubgroup α := by
    have := Abelianization.commutator_subset_ker (QuotientGroup.mk' (fixSubgroup α))
    rwa [QuotientGroup.ker_mk'] at this
  rw [hperf] at hcomm
  exact hC1 (top_le_iff.1 hcomm)

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
