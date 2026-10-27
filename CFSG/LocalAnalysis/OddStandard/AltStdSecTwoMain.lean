module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoCaseI
public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverMain
public import CFSG.LocalAnalysis.OddStandard.AltStdSecShape3Main
public import CFSG.LocalAnalysis.OddStandard.AltStdBalOuter

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv CFSG.OddStandard.AltStdBal

@[expose] def ShapeTwoCaseIIClassification : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ) (z u : G)
    (h : Setting G L n), Cyc L Q z → ShapeTwo L Q z u → ∀ e : L ≃* alternatingGroup (Fin n),
      14 ≤ n → ∀ S₀ : Finset (Fin n), S₀.card = 3 → CaseIIAt e z S₀ →
        CaseII e h.hn (L ⊔ zpowers u) z ∨ CaseII e h.hn (L ⊔ zpowers (u * z)) z

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem shapeTwo_dichotomy_of_caseII (htri : ExactShapeTrichotomy)
    (hII : ShapeTwoCaseIIClassification) (h : Setting G L n) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin n)) (hn : 14 ≤ n) :
    CaseII e h.hn (L ⊔ zpowers u) z ∨ CaseII e h.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z n H := by
  classical
  let S₀ : Finset (Fin n) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hS₀ : S₀.card = 3 := by
    simp only [S₀]
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
  have hex : ExactShape z L n := exactShape_of_setting h d T.card
  have ht : z ∈ centralizer (corr (X := G) e (altSub S₀) : Set G) :=
    t_mem_centralizer_corr (X := G) e hex (altSub S₀)
  have hsec := exactShape_section_three hex e hS₀ (by omega) ht
  have hKcat : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S₀))) :=
    isKGroupCat_sec (isKGroupCat_of_kProper h.std.kProper)
      (centralizer_ne_top_of_ne_one h (exists_ne_one_of_card_ge_three e (by omega)))
  have hO := oddCore_sec_eq_bot (corr (X := G) e (altSub S₀))
  rcases htri _ _ _ (n - S₀.card) (by omega) hKcat hO hsec with h1 | h1 | h1 | h1
  · exact (false_of_caseI htri h d T e (by omega) (by omega) (Or.inl hS₀) (by omega) ⟨ht, h1⟩).elim
  · obtain ⟨H, hH⟩ := exists_wreathPair_of_caseIII_root hex e (by omega) hS₀ ⟨ht, h1⟩
    exact Or.inr (Or.inr ⟨H, hH⟩)
  · rcases hII G L Q n z u h d T e hn S₀ hS₀ ⟨ht, h1⟩ with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · omega

theorem false_of_shapeTwo_of_caseII (htri : ExactShapeTrichotomy)
    (hII : ShapeTwoCaseIIClassification) (h : Setting G L n) (d : Cyc L Q z)
    (hQ2 : Nat.card Q = 2) (hn : 14 ≤ n) (hu : u ∈ centralizer ({z} : Set G))
    (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1) (e : L ≃* alternatingGroup (Fin n)) : False :=
  false_of_shapeTwo_of_dichotomy htri h d hQ2 (by omega) hu huL hu2 e
    (shapeTwo_dichotomy_of_caseII htri hII h d ⟨hQ2, hu, huL, hu2⟩ e hn)

theorem altStdBalancedOrder2Outer_ge_fourteen
    (htri : ExactShapeTrichotomy) (hII : ShapeTwoCaseIIClassification) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
      ∀ n : ℕ, 14 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
        ∀ S : Sylow 2 (centralizer (L : Set G)),
          IsCyclic (S : Subgroup (centralizer (L : Set G))) → Nat.card S = 2 →
            (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
            (∃ z : G, z ∈ centralizer (L : Set G) ∧ orderOf z = 2 ∧
              ¬ centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) → False := by
  intro G _ _ L hS n hn hθ S hcyc h2 hbal hex
  obtain ⟨w, hwK, hw2, hwO⟩ := hex
  have h : Setting G L n := ⟨hS, by omega, hθ, ⟨S, hcyc⟩, hbal⟩
  obtain ⟨z, d⟩ := Cyc.of_sylow h S hcyc
  have hQ2 : Nat.card (sylowSub S) = 2 := (card_sylowSub S).trans h2
  obtain ⟨e⟩ := hθ
  obtain ⟨k, hkK, hkz⟩ := exists_conj_of_involution d hwK hw2
  have hO : ¬ centralizer ({z} : Set G) ≤ L ⊔ sylowSub S := by
    intro hle
    apply hwO
    intro c hc
    have hc' : k⁻¹ * c * k ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      rw [← hkz] at hc
      calc k⁻¹ * c * k * z = k⁻¹ * (c * (k * z * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * z * k⁻¹) * c) * k := by rw [hc]
        _ = z * (k⁻¹ * c * k) := by group
    have h1 : k⁻¹ * c * k ∈ L ⊔ centralizer (L : Set G) :=
      sup_le_sup_left d.le L (hle hc')
    have hkK' : k ∈ L ⊔ centralizer (L : Set G) := mem_sup_right hkK
    have := mul_mem (mul_mem hkK' h1) (inv_mem hkK')
    simpa [mul_assoc] using this
  obtain ⟨u, hu, huQ, hsq | hsq⟩ := exists_outer_sq_eq h d hQ2 hO
  · exact false_of_shapeTwo_of_caseII htri hII h d hQ2 hn hu huQ hsq e
  · exact false_of_shape_three h d hQ2 hu huQ hsq

end Main

end CFSG.OddStandard.AltStdSec
