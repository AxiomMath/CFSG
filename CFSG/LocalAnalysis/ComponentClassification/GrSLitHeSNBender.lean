module

public import CFSG.Foundations.Basic
public import CFSG.Blueprint.NativeSporadic
import CFSG.Holt.Bender
import CFSG.Goldschmidt.Steps.StrongEmb
import CFSG.Goldschmidt.Steps.LemmaXBasic
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldBasic

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.Open

theorem false_of_isStronglyEmbedded
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {M : Subgroup X} (hM : CFSG.IsStronglyEmbedded M) {V : Subgroup X} (hV : Nat.card V = 4)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) {a : X} (ha : orderOf a = 2) {L : Subgroup X}
    (hLa : L ≤ centralizer ({a} : Set X))
    (eL : L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : ∀ R : Subgroup X, R.Normal → Odd (Nat.card R) → R = ⊥ := by
    intro R hR hodd
    have := hR
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with hb | ht
    · exact hb
    · exfalso
      rw [ht, card_top] at hodd
      have h2 : 2 ∣ Nat.card X := ha ▸ orderOf_dvd_natCard a
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hF : fusionStronglyEmbedded M := hM
  have hsol : Group.IsSolvable M :=
    CFSG.Holt.isSolvable_of_fusionStronglyEmbedded hF hO hV hV2
  have hSO : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M :=
    (CFSG.Goldschmidt.LemmaX.isStronglyEmbeddedOrder_iff M).mpr hF
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 (even_iff_two_dvd.mp hM.2.1)
  have ht2 : orderOf (t : X) = 2 := by rw [Subgroup.orderOf_coe, ht]
  obtain ⟨c, hc⟩ : ∃ c : X, centralizer ({a} : Set X) ≤ M.map (MulAut.conj c).toMonoidHom := by
    by_cases haM : a ∈ M
    · refine ⟨1, fun x hx => ⟨x, ?_, by simp⟩⟩
      exact CFSG.Goldschmidt.centralizer_le_of_stronglyEmbedded hSO ha haM hx
    · obtain ⟨c, hc⟩ :=
        isConj_iff.mp (CFSG.Goldschmidt.isConj_of_mem_of_not_mem hSO ht2 ha t.2 haM)
      refine ⟨c, fun x hx => ⟨c⁻¹ * x * c, ?_, ?_⟩⟩
      · show c⁻¹ * x * c ∈ M
        apply CFSG.Goldschmidt.centralizer_le_of_stronglyEmbedded hSO ht2 t.2
        rw [mem_centralizer_singleton_iff] at hx ⊢
        have ht' : (t : X) = c⁻¹ * a * c := by rw [← hc]; group
        rw [ht']
        calc c⁻¹ * x * c * (c⁻¹ * a * c) = c⁻¹ * (x * a) * c := by group
          _ = c⁻¹ * (a * x) * c := by rw [hx]
          _ = c⁻¹ * a * c * (c⁻¹ * x * c) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  have hM's : Group.IsSolvable (M.map (MulAut.conj c).toMonoidHom) :=
    Group.isSolvable_of_surjective (f := ((MulAut.conj c).subgroupMap M).toMonoidHom)
      ((MulAut.conj c).subgroupMap M).surjective
  have hLs : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion (hLa.trans hc))
      (inclusion_injective (hLa.trans hc))
  have hQs : Group.IsSolvable (L ⧸ pPrimeCore 2 L) := inferInstance
  have hsQ : IsSimpleGroup (L ⧸ pPrimeCore 2 L) :=
    @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He eL
  have hQc := IsSimpleGroup.comm_iff_isSolvable.mpr hQs
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_held
  exact hxy (eL.symm.injective (by rw [map_mul, map_mul]; exact hQc _ _))

end CFSG.ComponentClassification.GrSLit.HeSN
