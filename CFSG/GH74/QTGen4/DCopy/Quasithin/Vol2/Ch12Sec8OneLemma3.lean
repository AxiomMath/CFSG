module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem lemma12_8_3_four_F4 (h12213 : Stmt12_2_13_F4) [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro hle
  obtain ⟨-, hsq, -⟩ := h.card_sq
  obtain ⟨e⟩ := h.quot
  rcases (stmt12_2_13_iff_F4.mp h12213) G T L V h.hyp with ⟨v, hvV, hv1, hvM⟩ |
      ⟨n', hn', ⟨e'⟩, hlie⟩ | ⟨-, hA9⟩ | ⟨-, hM24⟩
  · apply hvM
    have hv2 : Nat.card (Subgroup.zpowers v) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hsq v hvV) hv1
    obtain ⟨l, hl, hlZ⟩ := lemma12_8_3_two h hV₁.1 ((Subgroup.zpowers_le).2 hvV) hV₁.2.1
      (by rw [hv2, pow_one])
    have hlM : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
    intro x hx
    have hxn : x ∈ Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hx
    have key : ∀ w, w ∈ V₁ ↔ l⁻¹ * w * l ∈ Subgroup.zpowers v := by
      intro w
      rw [← hlZ, SteinbergBS.mem_conjugate_iff, show l * (l⁻¹ * w * l) * l⁻¹ = w by group]
    have hy : l * x * l⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [key, key, Subgroup.mem_normalizer_iff.1 hxn,
        show x * (l⁻¹ * z * l) * x⁻¹ = l⁻¹ * (l * x * l⁻¹ * z * (l * x * l⁻¹)⁻¹) * l by group]
    have h2 : l⁻¹ * (l * x * l⁻¹) * l ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (mul_mem (inv_mem hlM) (hle hy)) hlM
    rwa [show l⁻¹ * (l * x * l⁻¹) * l = x by group] at h2
  · have hc := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e'.toEquiv)
    have hnn : n = n' := by
      rcases h.n_mem with rfl | rfl | rfl <;> rcases hn' with rfl | rfl
      · rfl
      · rw [card_sl_three_zmod_two, card_sl_four_zmod_two] at hc
        omega
      · rw [card_sl_four_zmod_two, card_sl_three_zmod_two] at hc
        omega
      · rfl
      · rw [card_sl_five_zmod_two, card_sl_three_zmod_two] at hc
        omega
      · rw [card_sl_five_zmod_two, card_sl_four_zmod_two] at hc
        omega
    subst hnn
    exact h.not_linear hlie
  · exact h.not_alt9 hA9
  · exact h.not_m24 hM24

theorem lemma12_8_3_F4 (h12213 : Stmt12_2_13_F4) : Lemma12_8_3_F4 := by
  intro G _ _ T L V n h
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have htop := autOn_eq_top_of_hyp1281One h
  have hMV : autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V = ⊤ :=
    top_le_iff.1 (htop ▸ autOn_mono (le_inf Subgroup.le_normalizer hLV))
  exact ⟨⟨hMV, hMV.trans htop.symm⟩, fun i W₁ W₂ h1 h2 hc1 hc2 => lemma12_8_3_two h h1 h2 hc1 hc2,
    fun i Vi hVi g hg => lemma12_8_3_three h hVi hg, fun V₁ hV₁ => lemma12_8_3_four_F4 h12213 h hV₁⟩

end CFSG.Quasithin.H13
