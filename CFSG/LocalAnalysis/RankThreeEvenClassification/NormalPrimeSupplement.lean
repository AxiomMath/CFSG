module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem index_dvd_normal_supplement_card {G : Type u} [Group G]
    (normalSubgroup supplement : Subgroup G) [normalSubgroup.Normal]
    (hsup : normalSubgroup ⊔ supplement = ⊤) : supplement.index ∣ Nat.card normalSubgroup := by
  let : MulAction normalSubgroup (G ⧸ supplement) :=
    MulAction.compHom (G ⧸ supplement) normalSubgroup.subtype
  let base : G ⧸ supplement := QuotientGroup.mk (1 : G)
  have : MulAction.IsPretransitive normalSubgroup (G ⧸ supplement) := by
    apply (MulAction.isPretransitive_iff_base base).mpr
    intro element
    obtain ⟨representative, rfl⟩ := QuotientGroup.mk_surjective element
    have hmem : representative ∈ normalSubgroup ⊔ supplement := by
      rw [hsup]
      exact Subgroup.mem_top _
    obtain ⟨first, hfirst, second, hsecond, heq⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    refine ⟨⟨first, hfirst⟩, ?_⟩
    rw [MulAction.compHom_smul_def]
    change (first : G) • (QuotientGroup.mk (1 : G) : G ⧸ supplement) = QuotientGroup.mk representative
    rw [MulAction.Quotient.smul_mk]
    change QuotientGroup.mk (first * 1) = QuotientGroup.mk representative
    rw [mul_one, ← heq, QuotientGroup.mk_mul_of_mem first hsecond]
  have hcard : Nat.card (G ⧸ supplement) =
      Nat.card (normalSubgroup ⧸ MulAction.stabilizer normalSubgroup base) := by
    have heq := Nat.card_congr (MulAction.orbitEquivQuotientStabilizer normalSubgroup base)
    rw [MulAction.orbit_eq_univ, Nat.card_univ] at heq
    exact heq
  rw [Subgroup.index_eq_card, hcard]
  exact Subgroup.card_quotient_dvd_card _

theorem normal_prime_subgroup_le_supplement {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (normalSubgroup supplement primeSubgroup : Subgroup G)
    [normalSubgroup.Normal] [primeSubgroup.Normal]
    (hsup : normalSubgroup ⊔ supplement = ⊤)
    (hcomplement : ¬prime ∣ Nat.card normalSubgroup) (hpgroup : IsPGroup prime primeSubgroup) :
    primeSubgroup ≤ supplement := by
  have : Fact prime.Prime := ⟨hprime⟩
  have hindexComplement : ¬prime ∣ supplement.index := fun hdiv =>
    hcomplement (hdiv.trans (index_dvd_normal_supplement_card normalSubgroup supplement hsup))
  let : MulAction primeSubgroup (G ⧸ supplement) :=
    MulAction.compHom (G ⧸ supplement) primeSubgroup.subtype
  obtain ⟨fixed, hfixed⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card
    (G ⧸ supplement) (by simpa only [Subgroup.index_eq_card] using hindexComplement)
  obtain ⟨representative, hrepresentative⟩ := QuotientGroup.mk_surjective fixed
  intro element helement
  have hconjugate : representative * element * representative⁻¹ ∈ primeSubgroup :=
    (inferInstance : primeSubgroup.Normal).conj_mem element helement representative
  have heq := MulAction.mem_fixedPoints.mp hfixed
    (⟨representative * element * representative⁻¹, hconjugate⟩ : primeSubgroup)
  rw [← hrepresentative] at heq
  rw [MulAction.compHom_smul_def] at heq
  change (representative * element * representative⁻¹ : G) • (QuotientGroup.mk representative : G ⧸ supplement) =
    QuotientGroup.mk representative at heq
  rw [MulAction.Quotient.smul_mk] at heq
  change QuotientGroup.mk ((representative * element * representative⁻¹) * representative) =
    QuotientGroup.mk representative at heq
  have hmem := QuotientGroup.eq.mp heq.symm
  simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using hmem

end CFSG.RankThreeEvenClassification.Helpers
