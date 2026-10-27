module

public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Mult
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLieEven
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltImage
public import CFSG.LocalAnalysis.OddStandard.OddLieFaithful

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowAlt

open CFSG Subgroup Equiv Equiv.Perm

theorem false_of_alt {S : Type} [Group S] [Finite S] {n : ℕ}
    (e : S ≃* alternatingGroup (Fin n)) {t : S} (ht : orderOf t = 2) {J : Subgroup S}
    (hJC : J ≤ centralizer {t}) (hJs : (J.subgroupOf (centralizer {t})).IsSubnormal)
    (htJ : t ∈ J) (hJq : IsTwoQuasisimple ↥J) : False := by
  set ε : S →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom with hε
  have hinj : Function.Injective ε := Subtype.val_injective.comp e.injective
  have hsurj : ∀ q ∈ alternatingGroup (Fin n), ∃ x, ε x = q := fun q hq =>
    ⟨e.symm ⟨q, hq⟩, by simp [hε]⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : ε t ≠ 1 := fun h => by
    have h1 : t = 1 := hinj (by rw [h, map_one])
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : ε t * ε t = 1 := by rw [← map_mul, htt, map_one]
  set u : centralizer ({t} : Set S) := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
  have huL : u ∈ J.subgroupOf (centralizer {t}) := htJ
  have hLq : IsTwoQuasisimple ↥(J.subgroupOf (centralizer {t})) :=
    isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJC).symm hJq
  exact false_of_perfect hinj hsurj ht1 ht2 hJs hLq.1 rfl huL
    (jointKer_commute_of_isTwoQuasisimple hinj ht2 hLq)

end CFSG.ComponentClassification.HarrisLit.T1.RowAlt

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def Harris82Theorem1SimpleKProperOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {z}) → z ∈ L →
      ∀ p : ℕ, p.Prime → p ≠ 2 → IsMTypeSchur p ↥L →
        Blueprint.OddLieType G ∨ Nonempty (G ≃* ↥Blueprint.NativeSporadic.M11)

theorem harris82Theorem1KProper_of_simpleKProperOdd (h : Harris82Theorem1SimpleKProperOdd) :
    Harris82Theorem1KProper :=
  fun G _ _ _ hnonab hK hcat z hz L hL hzL p hp hp2 hM => by
    rcases h G hnonab hK z hz L hL hzL p hp hp2 hM with ⟨τ, n, r, f, -, -, -, hm⟩ | hM11
    · exact hcat (Blueprint.lieModel_catalog G τ n r f hm)
    · obtain ⟨e⟩ := hM11
      exact hcat (.inr (.inr (.inr (.inr ⟨.M11, ⟨e⟩⟩))))

@[expose] def Harris82SporadicRow : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    Blueprint.NativeSporadic.SporadicRep S → ¬ Nonempty (S ≃* ↥Blueprint.NativeSporadic.M11) →
    ∀ t : S, orderOf t = 2 → ∀ L : Subgroup S, IsTwoComponentIn L (centralizer {t}) → t ∈ L →
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ IsMTypeSchur p ↥L

section Certified

theorem harris82Theorem1SimpleKProperOdd_of_row (hK : Harris82Theorem1KProper)
    (hSpor : Harris82SporadicRow) : Harris82Theorem1SimpleKProperOdd := by
  intro G _ _ _ hnonab hKP z hz L hL hzL p hp hp2 hM
  by_cases hcat : Blueprint.Catalog G
  swap
  · exact (hK G hnonab hKP hcat z hz L hL hzL p hp hp2 hM).elim
  have key : ∀ r : ℕ, T1.LieChar r G → Blueprint.OddLieType G := by
    rintro r ⟨τ, n, f, hm⟩
    by_cases hr2 : r = 2
    · subst hr2
      exact (T1.RowLie.false_of_lieChar_two ⟨τ, n, f, hm⟩ hz hL.1 hL.2.1 hL.2.2).elim
    · exact ⟨τ, n, r, f, (Blueprint.LieModel.admissible hm).1, hr2,
        Blueprint.LieModel.admissible hm, hm⟩
  rcases hcat with ⟨q, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, r, f, hm⟩ | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact (T1.RowAlt.false_of_alt e hz hL.1 hL.2.1 hzL hL.2.2).elim
  · refine .inl (key r ⟨t, n, f, .inl ⟨?_, hm⟩⟩)
    rcases Milestones.statedClassicalModel_tag_mem _ t n r f hm with h | h | h | h | h | h <;>
      subst h <;> decide
  · obtain ⟨r, hLie⟩ : ∃ r : ℕ, T1.LieChar r G := by
      rcases hex with ⟨t, r, f, ht, hm⟩ | ⟨t, r, f, ht, hm⟩ | ⟨r, f, hm⟩
      · exact ⟨r, t, 0, f, .inr (.inl ⟨rfl, ht, hm⟩)⟩
      · exact ⟨r, t, 0, f, .inr (.inr (.inl ⟨rfl, ht, hm⟩))⟩
      · exact ⟨r, .twistedB2, 0, f, .inr (.inr (.inr ⟨rfl, rfl, hm⟩))⟩
    exact .inl (key r hLie)
  · by_cases hm11 : Nonempty (G ≃* ↥Blueprint.NativeSporadic.M11)
    · exact .inr hm11
    · exact (hSpor G hnonab hsp hm11 z hz L hL hzL p hp hp2 hM).elim

end Certified

end CFSG.ComponentClassification.HarrisLit

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem oddLieType_of_isMTypeSchur_of_simpleKProperOdd
    (hH : ComponentClassification.HarrisLit.Harris82Theorem1SimpleKProperOdd)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hS : StandardSetting G L)
    (hev : Even (Nat.card (center L))) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : ComponentClassification.HarrisLit.IsMTypeSchur p L) : OddLieType G := by
  have := hS.simple
  obtain ⟨t, ht2, htL, hLT, hL⟩ := exists_intrinsic_twoComponent hS.standard hev
  rcases hH G hS.nonab hS.kProper t ht2 L hL htL p hp hp2 hM with hodd | hM11
  · exact hodd
  · exact (false_of_isSporadic_M11_of_le_centralizer hM11 ht2 hLT
      (Residual.sixty_le_card_of_standard hS.standard)).elim

theorem oddLieThm187b_of_harris82_of_simpleKProperOdd
    (hH : ComponentClassification.HarrisLit.Harris82Theorem1SimpleKProperOdd)
    (hR : OddLieThm187bResidual) : OddLieThm187b := by
  intro G _ _ L hS hU hlie h5 h6 hhsf S hcyc
  by_cases hcase : Odd (Nat.card (center L)) ∨
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ ComponentClassification.HarrisLit.IsMTypeSchur p L
  · exact hR G L hS hU hlie h5 h6 hhsf hcase S hcyc
  · push Not at hcase
    obtain ⟨hnodd, p, hp, hp2, hM⟩ := hcase
    exact Or.inr (Or.inl (oddLieType_of_isMTypeSchur_of_simpleKProperOdd hH hS
      (Nat.not_odd_iff_even.1 hnodd) hp hp2 hM))

theorem oddLieThm187b_of_harris82_of_mult_of_simpleKProperOdd
    (hH : ComponentClassification.HarrisLit.Harris82Theorem1SimpleKProperOdd)
    (hR : OddLieThm187bResidualMult) : OddLieThm187b :=
  oddLieThm187b_of_harris82_of_simpleKProperOdd hH (oddLieThm187bResidual_of_mult hR)

end CFSG.OddStandard
