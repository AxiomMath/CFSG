module

public import CFSG.CGT.PushingUpLit.A78.Sp4Dict
public import CFSG.Timmesfeld.Transvection.Frame

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection

variable {G : Type} [Group G] {Z : Subgroup G} {e : ℕ}

theorem Sp4Local.exists_not_commuting (h : Sp4Local G Z e) :
    ∃ C ∈ zClass Z, ¬ Commuting Z C := by
  by_contra hall
  push Not at hall
  have hle : ⨆ A ∈ zClass Z, A ≤ Subgroup.centralizer (Z : Set G) :=
    iSup₂_le fun A hA => commuting_iff_le_centralizer.1 (hall A hA)
  rw [h.iSup_eq_top, top_le_iff] at hle
  have hZ : Z ≤ Subgroup.center G := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer (Z : Set G) := by rw [hle]; trivial
    exact (Subgroup.mem_centralizer_iff.1 this z hz).symm
  rw [h.center_eq_bot, le_bot_iff] at hZ
  exact h.ne_bot_member (self_mem_zClass Z) hZ

section Frame

variable [Finite G]

theorem Sp4Local.sup_eq_of_opposite (h : Sp4Local G Z e) (hL1 : SylowOppositeSL2)
    {I P Q : Subgroup G} (φ : ↥I ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e))
    (hP : P ∈ zClass Z) (hPI : P ≤ I) (hQI : Q ≤ I) (hQc : Nat.card Q = 2 ^ e)
    (hopp : Opposite P Q) : P ⊔ Q = I := by
  obtain ⟨n, -, hn, ψ, -, -⟩ := hopp.exists_mulEquiv_SL2 (h.isRootClass hL1) hP
    (h.four_le_card_member hP)
  have hne : n = e := by
    have := (h.card_member hP).symm.trans hn
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  subst hne
  refine Subgroup.eq_of_le_of_card_ge (sup_le hPI hQI) ?_
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr ψ.toEquiv]

theorem Sp4Local.exists_smallFrame (h : Sp4Local G Z e) (hL1 : SylowOppositeSL2)
    (hS1 : SylowCountSL2) :
    ∃ P Q : Fin 2 → Subgroup G, IsSmallFrame (zClass Z) P Q 0 := by
  obtain ⟨C, hC, hnc⟩ := h.exists_not_commuting
  obtain ⟨I, -, ⟨φ⟩, h3, h4, h5, h6⟩ := h.dual_at (self_mem_zClass Z) C hC hnc
  have hcount := hS1 h.two_le φ
  have hlt : 1 < {P : Subgroup G | P ≤ I ∧ Nat.card P = 2 ^ e}.ncard := by
    rw [hcount]
    have : 2 ≤ 2 ^ e := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
    omega
  obtain ⟨P₁, Q₁, hP₁, hQ₁, hPQ⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 hlt
  have hP₁Δ : P₁ ∈ zClass Z := h4 P₁ hP₁.1 hP₁.2
  have hQ₁Δ : Q₁ ∈ zClass Z := h4 Q₁ hQ₁.1 hQ₁.2
  have hopp₁ : Opposite P₁ Q₁ := hL1 h.two_le φ hP₁.1 hQ₁.1 hP₁.2 hQ₁.2 hPQ
  have hopp₀ : Opposite Z C := h.opposite_of_not_commuting hL1 (self_mem_zClass Z) hC hnc
  have hsup : P₁ ⊔ Q₁ = I := h.sup_eq_of_opposite hL1 φ hP₁Δ hP₁.1 hQ₁.1 hQ₁.2 hopp₁
  refine ⟨![Z, P₁], ![C, Q₁], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · exact self_mem_zClass Z
    · exact hP₁Δ
  · intro i
    fin_cases i
    · exact hC
    · exact hQ₁Δ
  · intro i
    fin_cases i
    · exact hopp₀
    · exact hopp₁
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h3.mono le_rfl (hsup ▸ le_rfl)
    · exact (h3.mono le_rfl (hsup ▸ le_rfl)).symm
    · exact absurd rfl hij
  · intro X hX hcomm
    have hX1 := hcomm 1 (by decide)
    have hXI : Commuting X I := by
      rw [← hsup]
      exact Commuting.sup_right hX1.1 hX1.2
    exact h6 X hX hXI

end Frame

end CFSG.CGT.PushingUpLit.A78
