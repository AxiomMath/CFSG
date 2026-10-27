module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UResDef
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UY6Lang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType CFSG.StandardType.NoOffRest CFSG.StandardType.NoOffE8Five

theorem e8FiveMaxRank_holds
    : E8FiveMaxRank := by
  classical
  intro K _ _ h5 A hA hA3
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  have hℓq : ringChar K ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self _ f.ne_zero
  obtain ⟨g₀, hg₀C, hg₀⟩ := lang_conjugator Tag.E8 K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L
    weylE8W
  have h5ℓ : ¬ ringChar L ∣ 5 := by
    rw [ringChar.eq L (ringChar K)]
    intro hd
    have h55 : ringChar K = 5 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).1 hd
    rw [h55] at hℓq
    have h1 : 5 ∣ Nat.card K * Nat.card K := Dvd.dvd.mul_right hℓq _
    have h2 := (Nat.dvd_add_right h1).1 h5
    exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)
  obtain ⟨ζ, hζo⟩ := exists_unit_orderOf_five_of_isAlgClosed (L := L) h5ℓ
  have hζ : ζ ^ 5 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hkey : ∀ x : ZMod 5, x * x + 1 = 0 → (-x) * (-x) = -1 ∧ x * (-x) = 1 := by decide
  obtain ⟨hlam, hqlam⟩ := hkey ((Nat.card K : ℕ) : ZMod 5) (by
    have h := (ZMod.natCast_eq_zero_iff _ _).2 h5
    push_cast at h
    exact h)
  obtain ⟨ι, -, -, hcard, hcl⟩ :=
    exists_conjLe_of_lang hFr hℓq hζo hζ hlam hqlam h5 hg₀C hg₀
  obtain ⟨c, hc⟩ := hcl A hA hA3.ge
  refine ⟨ι.range.map (MulAut.conj c).toMonoidHom, hc, ?_, ?_⟩
  · rw [MonoidHom.map_range]
    exact isElemAbelian_range_of_module _
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard]

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
