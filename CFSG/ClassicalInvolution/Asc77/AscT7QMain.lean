module

public import CFSG.ClassicalInvolution.Asc77.AscT7QData
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Fin
public import CFSG.ClassicalInvolution.Asc77.AscT7QShape

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7Q

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ : G}


open T7F2 T7G2

theorem twoSubgroupsFourGenerated_of_index_four (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    (h11 : C25_11 p f) (h16 : C25_16 p f)
    (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')) : TwoSubgroupsFourGenerated G := by
  obtain ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, hnf⟩ := exists_swap_nonfused hyp
  have hT : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' := ⟨hyp, ht'S, ht'2, ht'R⟩
  obtain ⟨s, hsN, hsn, hst'⟩ := exists_s hT h11 h16 h4 hg hnf
  obtain ⟨a, b, n, i, m, c, hi, hm, hsa, hsb⟩ := exists_coord_s hT h11 h16 h4 hsN hsn
  obtain ⟨k, δ, hs2⟩ := sq_form hT h11 h16 h4 hsN hst' c hi hm hsa hsb
  have hS := closure_eq_S hT h11 h16 h4 hsN hsn c
  have hza := z_eq_pow hT c
  have ha'R' : t' * a * t'⁻¹ ∈ R' := by
    have := conj_mem_conjSub (n := t') c.ha
    rwa [ht'R] at this
  have hb'R' : t' * b * t'⁻¹ ∈ R' := by
    have := conj_mem_conjSub (n := t') c.hb
    rwa [ht'R] at this
  have htz : t' * a ^ (2 ^ n) * t'⁻¹ = a ^ (2 ^ n) := by
    rw [← hza]
    calc t' * z * t'⁻¹ = z * t' * t'⁻¹ := by rw [hyp.hzS t' ht'S]
      _ = z := by group
  apply T7DR.twoSubgroupsFourGenerated_of_sylow S
  intro H hH
  exact genLE_four_of_shape_sub hS c.hbab c.hbb c.pow_card ht'2 htz rfl rfl
    (hT.hcomm a c.ha _ ha'R') (hT.hcomm a c.ha _ hb'R') (hT.hcomm b c.hb _ ha'R')
    (hT.hcomm b c.hb _ hb'R') hi hm hsa hsb hst' hs2 hH

theorem c25_20_ex_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_20_ex p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4
  exfalso
  exact hyp.std.1.cex (Or.inr (twoSubgroupsFourGenerated_of_index_four hyp h11 h16 h4))

theorem c25_21_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_21 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4
  exact Or.inr (twoSubgroupsFourGenerated_of_index_four hyp h11 h16 h4)

end T7Q

end CFSG.ClassicalInvolution.Asc77
