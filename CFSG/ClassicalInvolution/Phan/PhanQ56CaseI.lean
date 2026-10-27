module

public import CFSG.ClassicalInvolution.Phan.PhanQ55Plane
public import CFSG.ClassicalInvolution.Phan.PhanQ54Combined

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section CaseI

theorem three_card_lt {q : ℕ} (hq : 5 ≤ q) : 3 * (q + 1) < q ^ 2 - q := by
  rw [Nat.lt_sub_iff_add_lt, pow_two]
  have h1 : 5 * q ≤ q * q := Nat.mul_le_mul_right q hq
  omega

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem exists_cone_of_inf [Finite F] [Finite K] (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0)
    (hε : ε ≠ 0) {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x) (hσu : IsUnitaryInvolution σ) {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 5 ≤ q) {a b c : V8 K} (ha : ffK D a) (hb : ffK D b)
    (hc : ffK D c) (hab : ColK D a b) (hbc : ColK D b c) (hac : ColK D a c)
    (hinf : ∀ v ∈ Submodule.span K {a, b, c}, conj D v ∈ Submodule.span K {a, b, c} → v = 0) :
    ∃ e, ffK D e ∧ ColK D a e ∧ ColK D b e ∧ ColK D c e ∧
      ∃ W, PhanSolid D W ∧ a ∈ W ∧ b ∈ W ∧ c ∈ W ∧ e ∈ W := by
  classical
  have hts := ts_triple ha.1 hb.1 hc.1 hab.1 hac.1 hbc.1
  have haPl : a ∈ Submodule.span K {a, b, c} := Submodule.subset_span (by simp)
  have hbPl : b ∈ Submodule.span K {a, b, c} := Submodule.subset_span (by simp)
  have hcPl : c ∈ Submodule.span K {a, b, c} := Submodule.subset_span (by simp)
  obtain ⟨W, hW, hPlW⟩ := exists_phanSolid_of_colK D hodd h2 hε hσ hts
    (finrank_span_three_le a b c) hinf haPl hbPl hab
  have haW : a ∈ W := hPlW haPl
  have hbW : b ∈ W := hPlW hbPl
  have hcW : c ∈ W := hPlW hcPl
  obtain ⟨e, he, hffe, hcol⟩ := PhanSolid.exists_colK_in_plane D hW h2 hε hσ hσu hK haW hbW ha hb
    hab {a, b, c}
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨haW, ha⟩
      · exact ⟨hbW, hb⟩
      · exact ⟨hcW, hc⟩)
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ Finset.card_le_three) (three_card_lt hq))
  have hP : Submodule.span K {a, b} ≤ W := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact haW
    · exact hbW
  exact ⟨e, hffe, hcol a (by simp), hcol b (by simp), hcol c (by simp), W, hW, haW, hbW, hcW,
    hP he⟩

end CaseI

end CFSG.ClassicalInvolution.PhanQ
