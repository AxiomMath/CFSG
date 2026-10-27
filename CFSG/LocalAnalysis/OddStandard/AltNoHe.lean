module

public import CFSG.LocalAnalysis.OddStandard.AltNoHePerm
public import CFSG.LocalAnalysis.OddStandard.AltNoHeQuasisimple
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.Blueprint.NativeSporadic
import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
import CFSG.Sporadic.He.Simple

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic AltNoHe

theorem exists_mulEquiv_alternatingGroup_of_standard
    {G : Type*} [Group G] [Finite G] {n : ℕ} (e : G ≃* alternatingGroup (Fin n))
    {L : Subgroup G} (hL : standardComponentIsStandard L) :
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty ((L ⧸ center L) ≃* alternatingGroup (Fin m)) := by
  let ε : G →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hinj : Function.Injective ε := Subtype.val_injective.comp e.injective
  have hsurj : ∀ p ∈ alternatingGroup (Fin n), ∃ x, ε x = p := fun p hp =>
    ⟨e.symm ⟨p, hp⟩, by simp [ε]⟩
  obtain ⟨t, ht⟩ : ∃ t : centralizer (L : Set G), orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hL.2.1)
  have hz : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  obtain ⟨-, hLT, hLn, -, -⟩ :=
    LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL t.2 hz
  have hzsq : (t : G) ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one _
  have ht1 : ε t ≠ 1 := by
    intro h
    have h1 : (t : G) = 1 := hinj (by rw [h, map_one])
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have ht2 : ε t * ε t = 1 := by rw [← map_mul, ← sq, hzsq, map_one]
  let π₁ := (quotP ε (t : G)).comp (Subgroup.inclusion hLT)
  let π₂ := (quotF ε (t : G)).comp (Subgroup.inclusion hLT)
  have hn₁ : π₁.range.Normal := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hLn.map _ (quotP_surjective hinj hsurj ht1 ht2)
  have hn₂ : π₂.range.Normal := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hLn.map _ (quotF_surjective hinj hsurj ht1 ht2)
  have hcomm : ∀ a b : L, π₁ a = 1 → π₂ a = 1 → π₁ b = 1 → π₂ b = 1 → a * b = b * a := by
    intro a b ha₁ ha₂ hb₁ hb₂
    apply Subgroup.inclusion_injective hLT
    rw [map_mul, map_mul]
    exact quot_comm hinj ht2 _ _ ha₁ ha₂ hb₁ hb₂
  have := hL.1.2
  rcases exists_card_ge_five_and_mulEquiv_alternatingGroup hL.1.1 π₁ π₂ hn₁ hn₂ hcomm with
    ⟨h5, ⟨f⟩⟩ | ⟨h5, ⟨f⟩⟩
  · exact exists_mulEquiv_alternatingGroup_fin h5 f
  · exact exists_mulEquiv_alternatingGroup_fin h5 f

theorem nat_card_alternatingGroup_fin (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = Nat.factorial m / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin m)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at h2
  omega

theorem factorial_div_two_ne_card_he (m : ℕ) : Nat.factorial m / 2 ≠ 4030387200 := by
  intro h
  by_cases hm : m ≤ 13
  · have h1 : Nat.factorial m ≤ Nat.factorial 13 := Nat.factorial_le hm
    have h2 : Nat.factorial 13 = 6227020800 := by decide
    omega
  · have h1 : Nat.factorial 14 ≤ Nat.factorial m := Nat.factorial_le (by omega)
    have h2 : Nat.factorial 14 = 87178291200 := by decide
    omega

theorem not_isSporadic_he_of_standard_alternating
    {G : Type} [Group G] [Finite G] {n : ℕ} (e : G ≃* alternatingGroup (Fin n))
    {L : Subgroup G} (hL : standardComponentIsStandard L) :
    ¬ IsSporadic (L ⧸ center L) .He := by
  rintro ⟨f⟩
  obtain ⟨m, hm5, ⟨g⟩⟩ := exists_mulEquiv_alternatingGroup_of_standard e hL
  have h1 : Nat.card (alternatingGroup (Fin m)) = Nat.card (Carrier .He) :=
    Nat.card_congr (g.symm.toEquiv.trans f.toEquiv)
  rw [nat_card_alternatingGroup_fin m (by omega),
    show Nat.card (Carrier .He) = 4030387200 from CFSG.Sporadic.He.card_He] at h1
  exact factorial_div_two_ne_card_he m h1

theorem altNoStandardHe :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      ∀ n : ℕ, Odd n → 7 ≤ n → n % 4 ≠ 1 → Nonempty (G ≃* alternatingGroup (Fin n)) →
        ∀ L : Subgroup G, standardComponentIsStandard L → ¬ IsSporadic (L ⧸ center L) .He :=
  fun _ _ _ _ _ _ _ _ _ ⟨e⟩ _ hL => not_isSporadic_he_of_standard_alternating e hL

end CFSG.OddStandard
