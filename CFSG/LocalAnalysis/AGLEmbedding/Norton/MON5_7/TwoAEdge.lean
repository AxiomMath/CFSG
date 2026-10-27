module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.FusionAssembly
public import CFSG.Monster.Existence.Defs

public section

namespace CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7

open CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint CFSG.Monster.Existence

variable {G : Type} [Group G]

theorem natCard_center_cent_of_twoA {a : G} (ha : orderOf a = 2) (hA : IsTwoACentralizer a) :
    Nat.card (Subgroup.center (cent a)) = 2 := by
  have h := hA.2.1
  have hinj : Function.Injective (cent a).subtype := Subgroup.subtype_injective _
  have h1 : Nat.card ((Subgroup.center (cent a)).map (cent a).subtype) =
      Nat.card (Subgroup.center (cent a)) := Subgroup.card_map_of_injective hinj
  rw [h, Nat.card_zpowers, ha] at h1
  exact h1.symm

theorem fusionGenerationOf_cent_of_baby [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a : G}
    (ha : orderOf a = 2) (hA : IsTwoACentralizer a)
    (hB : FusionGenerationOf NativeSporadic.B p) : FusionGenerationOf (cent a) p := by
  obtain ⟨e⟩ := hA.2.2
  have hc2 := natCard_center_cent_of_twoA ha hA
  let π : cent a →* NativeSporadic.B :=
    MonoidHom.comp (MulEquiv.toMonoidHom e) (QuotientGroup.mk' (Subgroup.center (cent a)))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center (cent a) := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center (cent a)
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  refine fusionGenerationOf_of_central_quotient π hπ hker.le ?_ hB
  intro k hk n hkn
  rw [hker] at hk
  have h1 : orderOf (⟨k, hk⟩ : Subgroup.center (cent a)) ∣ 2 :=
    hc2 ▸ orderOf_dvd_natCard _
  have h2 : orderOf (⟨k, hk⟩ : Subgroup.center (cent a)) ∣ p ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using hkn)
  have hcop : Nat.Coprime 2 (p ^ n) := by
    refine Nat.Coprime.pow_right _ ?_
    exact (Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp2)
  have h3 : orderOf (⟨k, hk⟩ : Subgroup.center (cent a)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have := orderOf_eq_one_iff.mp h3
  simpa using congrArg Subtype.val this

theorem fusionGenerationOf_of_twoA_edge [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a y : G}
    (ha : orderOf a = 2) (hA : IsTwoACentralizer a) (W : Subgroup G)
    (hW : ∀ g, g ∈ W ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a))
    (hKW : cent a ⊔ W = ⊤) (hD : p ∣ Nat.card ↥(cent a ⊓ cent y))
    (hB : FusionGenerationOf NativeSporadic.B p) : FusionGenerationOf G p := by
  have hK : FusionGenerationOf ↥(cent a) p := fusionGenerationOf_cent_of_baby hp2 ha hA hB
  exact fusionGenerationOf_of_sup_normal (cent a) W (cent a ⊓ cent y) inf_le_left
    (inf_centralizer_le_of_edge W hW) (normal_inf_centralizer_of_edge W hW) hKW hD hK

end CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7
