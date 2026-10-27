module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FourPointTwelveCharacters

section Sums

variable {ι : Type*} {M : Type*} [AddCommMonoid M]

theorem sum_eq_sum_of_vanish (B S : Finset ι) (f : ι → M) (hSB : S ⊆ B)
    (h : ∀ χ ∈ B, χ ∉ S → f χ = 0) : ∑ χ ∈ B, f χ = ∑ χ ∈ S, f χ :=
  (Finset.sum_subset hSB h).symm

theorem sum_toFinset (l : List ι) (hl : l.Nodup) (f : ι → M) :
    ∑ χ ∈ l.toFinset, f χ = (l.map f).sum :=
  List.sum_toFinset f hl

theorem nodup_four_iff {a b c e : ι} :
    [a, b, c, e].Nodup ↔ a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ c ≠ e := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ne_eq]
  tauto

theorem nodup_five_iff {a b c e g : ι} :
    [a, b, c, e, g].Nodup ↔ a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ a ≠ g ∧ b ≠ c ∧ b ≠ e ∧ b ≠ g ∧ c ≠ e ∧
      c ≠ g ∧ e ≠ g := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ne_eq]
  tauto

theorem sum_four {a b c e : ι} (h : [a, b, c, e].Nodup) (f : ι → ℤ) :
    ∑ χ ∈ ({a, b, c, e} : Finset ι), f χ = f a + f b + f c + f e := by
  have hl : ({a, b, c, e} : Finset ι) = [a, b, c, e].toFinset := by
    ext χ
    simp
  rw [hl, sum_toFinset _ h]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem sum_five {a b c e g : ι} (h : [a, b, c, e, g].Nodup) (f : ι → ℤ) :
    ∑ χ ∈ ({a, b, c, e, g} : Finset ι), f χ = f a + f b + f c + f e + f g := by
  have hl : ({a, b, c, e, g} : Finset ι) = [a, b, c, e, g].toFinset := by
    ext χ
    simp
  rw [hl, sum_toFinset _ h]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

end Sums

structure ColumnData (ι : Type*) where
  B : Finset ι
  cj : ι → ι
  p₀ : ι
  d : ι → ℤ
  P : ι → ℤ
  Q : ι → ℤ
  L₁ : ι → ℤ
  L₂ : ι → ℤ
  L₃ : ι → ℤ
  c₁ : ι → ℤ
  c₂ : ι → ℤ
  c₃ : ι → ℤ
  cs : ι → ℤ
  Tim : ι → ℤ
  Uim : ι → ℤ
  χ₁ : ι
  χ₂ : ι
  χ₃ : ι
  η₁ : ι
  β₁ : ι
  ε : ℤ

namespace ColumnData

variable {ι : Type*} (D : ColumnData ι)

structure Valid : Prop where
  p_mem : D.p₀ ∈ D.B
  cj_mem : ∀ χ ∈ D.B, D.cj χ ∈ D.B
  cj_cj : ∀ χ, D.cj (D.cj χ) = χ
  cj_p : D.cj D.p₀ = D.p₀
  d_pos : ∀ χ ∈ D.B, 1 ≤ D.d χ
  d_p : D.d D.p₀ = 1
  d_cj : ∀ χ ∈ D.B, D.d (D.cj χ) = D.d χ
  P_p : D.P D.p₀ = 1
  Q_p : D.Q D.p₀ = 0
  L₁_p : D.L₁ D.p₀ = -1
  L₂_p : D.L₂ D.p₀ = -1
  L₃_p : D.L₃ D.p₀ = -1
  c₁_p : D.c₁ D.p₀ = 1
  c₂_p : D.c₂ D.p₀ = 1
  c₃_p : D.c₃ D.p₀ = 1
  cs_p : D.cs D.p₀ = 1
  P_cj : ∀ χ ∈ D.B, D.P (D.cj χ) = D.P χ
  Q_cj : ∀ χ ∈ D.B, D.Q (D.cj χ) = -D.Q χ
  L₁_cj : ∀ χ ∈ D.B, D.L₁ (D.cj χ) = D.L₃ χ
  L₂_cj : ∀ χ ∈ D.B, D.L₂ (D.cj χ) = D.L₂ χ
  L₃_cj : ∀ χ ∈ D.B, D.L₃ (D.cj χ) = D.L₁ χ
  c₁_cj : ∀ χ ∈ D.B, D.c₁ (D.cj χ) = D.c₃ χ
  c₂_cj : ∀ χ ∈ D.B, D.c₂ (D.cj χ) = D.c₂ χ
  c₃_cj : ∀ χ ∈ D.B, D.c₃ (D.cj χ) = D.c₁ χ
  cs_cj : ∀ χ ∈ D.B, D.cs (D.cj χ) = D.cs χ
  Tim_cj : ∀ χ ∈ D.B, D.Tim (D.cj χ) = -D.Tim χ
  Uim_cj : ∀ χ ∈ D.B, D.Uim (D.cj χ) = -D.Uim χ
  P_val : ∀ χ ∈ D.B, D.P χ = 0 ∨ D.P χ = 1 ∨ D.P χ = -1
  Q_val : ∀ χ ∈ D.B, D.Q χ = 0 ∨ D.Q χ = 1 ∨ D.Q χ = -1
  E_card : (D.B.filter (fun χ => D.P χ ≠ 0)).card = 4
  c₁c₁ : ∑ χ ∈ D.B, D.c₁ χ * D.c₁ χ = 8
  c₂c₂ : ∑ χ ∈ D.B, D.c₂ χ * D.c₂ χ = 8
  cscs : ∑ χ ∈ D.B, D.cs χ * D.cs χ = 7
  c₁c₂ : ∑ χ ∈ D.B, D.c₁ χ * D.c₂ χ = 6
  c₁cs : ∑ χ ∈ D.B, D.c₁ χ * D.cs χ = 6
  c₂cs : ∑ χ ∈ D.B, D.c₂ χ * D.cs χ = 6
  L₁L₃ : ∑ χ ∈ D.B, D.L₁ χ * D.L₃ χ = 4
  L₂L₂ : ∑ χ ∈ D.B, D.L₂ χ * D.L₂ χ = 8
  L₁L₂ : ∑ χ ∈ D.B, D.L₁ χ * D.L₂ χ = 4
  L₂L₃ : ∑ χ ∈ D.B, D.L₂ χ * D.L₃ χ = 4
  c₂L₁ : ∑ χ ∈ D.B, D.c₂ χ * D.L₁ χ = 0
  c₂L₂ : ∑ χ ∈ D.B, D.c₂ χ * D.L₂ χ = 0
  c₂L₃ : ∑ χ ∈ D.B, D.c₂ χ * D.L₃ χ = 0
  c₁L₁ : ∑ χ ∈ D.B, D.c₁ χ * D.L₁ χ = 0
  csL₁ : ∑ χ ∈ D.B, D.cs χ * D.L₁ χ = 0
  csL₂ : ∑ χ ∈ D.B, D.cs χ * D.L₂ χ = 0
  c₁P : ∑ χ ∈ D.B, D.c₁ χ * D.P χ = 0
  c₂P : ∑ χ ∈ D.B, D.c₂ χ * D.P χ = 0
  csP : ∑ χ ∈ D.B, D.cs χ * D.P χ = 0
  c₁d : ∑ χ ∈ D.B, D.c₁ χ * D.d χ = 0
  c₂d : ∑ χ ∈ D.B, D.c₂ χ * D.d χ = 0
  csd : ∑ χ ∈ D.B, D.cs χ * D.d χ = 0
  L₁d : ∑ χ ∈ D.B, D.L₁ χ * D.d χ = 0
  L₂d : ∑ χ ∈ D.B, D.L₂ χ * D.d χ = 0
  L₃d : ∑ χ ∈ D.B, D.L₃ χ * D.d χ = 0
  Pd : ∑ χ ∈ D.B, D.P χ * D.d χ = 0
  ReU : ∑ χ ∈ D.B, (-D.L₂ χ - 2 * D.cs χ + D.c₂ χ + D.c₁ χ + D.c₃ χ) ^ 2 = 24
  c₂_par : ∀ χ ∈ D.B, ∃ k : ℤ, D.c₂ χ = D.P χ + 2 * k
  c₁₃_par : ∀ χ ∈ D.B, ∃ k : ℤ, D.c₁ χ + D.c₃ χ = D.Q χ + 2 * k
  L₂_par : ∀ χ ∈ D.B, ∃ k : ℤ, D.L₂ χ = D.P χ + D.Q χ + 2 * k
  c₁₃ : ∀ χ ∈ D.B, 6 * (D.c₁ χ - D.c₃ χ) = 4 * D.Uim χ - D.Tim χ
  T_ne : ∀ χ ∈ D.B, -2 * D.L₂ χ + 2 * D.cs χ - D.c₂ χ - D.c₁ χ - D.c₃ χ ≠ 0 ∨
    D.L₃ χ - D.L₁ χ + D.c₃ χ - D.c₁ χ ≠ 0
  six_mem : D.χ₁ ∈ D.B ∧ D.χ₂ ∈ D.B ∧ D.χ₃ ∈ D.B
  six_nodup : [D.χ₁, D.cj D.χ₁, D.χ₂, D.cj D.χ₂, D.χ₃, D.cj D.χ₃].Nodup
  Uim₁ : D.Uim D.χ₁ = 1
  Uim₂ : D.Uim D.χ₂ = 1
  Uim₃ : D.Uim D.χ₃ = 1
  Tim₁ : D.Tim D.χ₁ = 4
  Tim₂ : D.Tim D.χ₂ = -2
  Tim₃ : D.Tim D.χ₃ = -2
  off_six : ∀ χ ∈ D.B, χ ≠ D.χ₁ → χ ≠ D.cj D.χ₁ → χ ≠ D.χ₂ → χ ≠ D.cj D.χ₂ → χ ≠ D.χ₃ →
    χ ≠ D.cj D.χ₃ → D.Tim χ = 0 ∧ D.Uim χ = 0
  η_mem : D.η₁ ∈ D.B
  η_P : D.P D.η₁ = 0
  ε_val : D.ε = 1 ∨ D.ε = -1
  L₁_η : D.L₁ D.η₁ = 2 * D.ε
  L₁_off : ∀ χ ∈ D.B, D.P χ = 0 → χ ≠ D.η₁ → D.L₁ χ = 0
  L₁_E : ∀ χ ∈ D.B, D.P χ ≠ 0 → D.L₁ χ = 1 ∨ D.L₁ χ = -1
  β_mem : D.β₁ ∈ D.B
  β_P : D.P D.β₁ ≠ 0
  β_L : D.L₁ D.β₁ = -D.P D.β₁
  β_ne : D.β₁ ≠ D.p₀
  Eminus : ∀ χ ∈ D.B, D.P χ ≠ 0 → D.L₁ χ = -D.P χ → χ = D.p₀ ∨ χ = D.β₁
  dich_ne : D.η₁ ≠ D.cj D.η₁ →
    ((D.χ₁ = D.η₁ ∧ D.cj D.χ₁ = D.cj D.η₁) ∨ (D.χ₁ = D.cj D.η₁ ∧ D.cj D.χ₁ = D.η₁)) ∧
      ∀ χ ∈ D.B, D.P χ ≠ 0 → D.L₁ χ = D.L₃ χ
  dich_eq : D.η₁ = D.cj D.η₁ → D.P D.χ₁ ≠ 0 ∧ D.P (D.cj D.χ₁) ≠ 0

end ColumnData

end CFSG.Wreathed.FourPointTwelveCharacters
