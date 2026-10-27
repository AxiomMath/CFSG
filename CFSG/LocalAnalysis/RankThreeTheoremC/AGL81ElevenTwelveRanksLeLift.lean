module

public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TwelveRanksLe

open CFSG.Open

theorem exists_isElemAbelian_card_nine_of_quotient_twoGroup {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] (hA : IsPGroup 2 A) {F : Subgroup (G ⧸ A)}
    (hF : IsElemAbelian 3 F) (hcard : Nat.card F = 3 ^ 2)
    (hZ : F ⊓ Subgroup.center (G ⧸ A) = ⊥) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ E ⊓ Subgroup.center G = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ¬ 3 ∣ Nat.card A := by
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    rw [hk]
    exact fun h => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have hcop : Nat.Coprime (3 ^ 2) (Nat.card A) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hA3)
  set P : Subgroup G := F.comap (QuotientGroup.mk' A)
  have hPcard : Nat.card P = Nat.card A * 3 ^ 2 := by
    rw [← hcard]
    exact QuotientGroup.card_preimage_mk A (F : Set (G ⧸ A))
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 P))
  have hScard : Nat.card S = 3 ^ 2 := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hA3, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same, zero_add]
  set ι : S →* G := P.subtype.comp (S : Subgroup P).subtype
  set φ : S →* F := ((QuotientGroup.mk' A).comp ι).codRestrict F fun s => s.1.2
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hker : ∀ s : S, ι s ∈ A → s = 1 := by
    intro s hs
    have hdisj := Subgroup.disjoint_of_coprime_natCard (H := (S : Subgroup P).map P.subtype)
      (K := A) (by
        rw [Subgroup.card_map_of_injective Subtype.val_injective, hScard]
        exact hcop)
    have h1 : ι s ∈ (S : Subgroup P).map P.subtype ⊓ A := ⟨⟨s, s.2, rfl⟩, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h2 : (QuotientGroup.mk' A) (ι s) = 1 := congrArg Subtype.val hs
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact (Subgroup.mem_bot).2 (hker s h2)
  refine ⟨ι.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hu, ← hv, ← map_mul, ← map_mul]
    congr 1
    apply hφ
    rw [map_mul, map_mul]
    exact Subtype.ext (hF.comm (φ u).2 (φ v).2)
  · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hg
    have hu : u ^ 3 = 1 := by
      apply hφ
      rw [map_pow, map_one]
      exact Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hF.2 _ (φ u).2)
    rw [← map_pow, hu, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, hScard]
  · rw [eq_bot_iff]
    rintro z ⟨hzE, hzc⟩
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hzE
    have h1 : (QuotientGroup.mk' A) (ι s) ∈ F ⊓ Subgroup.center (G ⧸ A) := by
      refine ⟨s.1.2, Subgroup.mem_center_iff.2 fun q => ?_⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hzc g]
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : s = 1 := hker s h1
    rw [h2, map_one]
    exact Subgroup.one_mem _

end TwelveRanksLe

end CFSG.LocalAnalysis.RankThreeTheoremC
