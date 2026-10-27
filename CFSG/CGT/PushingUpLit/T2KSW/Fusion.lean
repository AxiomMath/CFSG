module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG.ABGLocalTools CFSG.RankTwoShapes

variable {G : Type*} [Group G]

private theorem mem_map_conj_inv_iff {H : Subgroup G} {g y : G} :
    y ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

private theorem map_conj_eq_of_pointwise {P : Subgroup G} {a b : G}
    (hab : ∀ x ∈ P, a * x * a⁻¹ = b * x * b⁻¹) :
    P.map (MulAut.conj a).toMonoidHom = P.map (MulAut.conj b).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simpa using (hab x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simpa using hab x hx⟩

theorem exists_moving_step_subgroup {p : ℕ} {S P : Subgroup G} {c : G}
    (h : AlperinDecomposition p S P c) (hc : P.map (MulAut.conj c⁻¹).toMonoidHom ≠ P) :
    ∃ Q : Subgroup G, IsAlperinSubgroup p S Q ∧ P ≤ Q ∧
      ∃ n ∈ Subgroup.normalizer (Q : Set G), n ∉ Subgroup.normalizer (P : Set G) := by
  induction h with
  | one =>
    refine absurd ?_ hc
    ext y
    rw [mem_map_conj_inv_iff]
    simp
  | @step c n Q _ hQ hPQ hn ih =>
    by_cases hcP : P.map (MulAut.conj c⁻¹).toMonoidHom = P
    · refine ⟨Q, hQ, hcP ▸ hPQ, n, hn, fun hnP => hc ?_⟩
      ext y
      rw [mem_map_conj_inv_iff]
      have h1 : ∀ z, z ∈ P ↔ c * z * c⁻¹ ∈ P := fun z => by
        rw [← mem_map_conj_inv_iff, hcP]
      rw [show (c * n) * y * (c * n)⁻¹ = c * (n * y * n⁻¹) * c⁻¹ by group, ← h1]
      exact (Subgroup.mem_normalizer_iff.1 hnP y).symm
    · exact ih hcP

theorem exists_good_Q [Finite G] (T E : Subgroup G) (hT : IsSylowOf 2 T ⊤) (hET : E ≤ T)
    (hnwc : ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ T ∧
      E.map (MulAut.conj g).toMonoidHom ≠ E) :
    ∃ Q : Subgroup G, Q ≤ T ∧ E ≤ Q ∧ Subgroup.centralizer (Q : Set G) ⊓ T ≤ Q ∧
      (∃ n ∈ Subgroup.normalizer (Q : Set G), n ∉ Subgroup.normalizer (E : Set G)) ∧
      ∀ Q' : Subgroup G, Q < Q' → Q' ≤ T →
        Subgroup.normalizer (Q' : Set G) ≤ Subgroup.normalizer (E : Set G) := by
  obtain ⟨g, hgT, hgE⟩ := hnwc
  rw [isSylowOf_iff] at hT
  obtain ⟨-, hTp, hTi⟩ := hT
  rw [Subgroup.relIndex_top_right] at hTi
  let S : Sylow 2 G := hTp.toSylow hTi
  have hS : (S : Subgroup G) = T := rfl
  have hET' : E ≤ (S : Subgroup G) := hS ▸ hET
  have hg' : E.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [inv_inv, hS]
    exact hgT
  obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion S hET' hg'
  rw [hS] at hc
  have hcE : E.map (MulAut.conj c⁻¹).toMonoidHom ≠ E := by
    have hpt : E.map (MulAut.conj c⁻¹).toMonoidHom = E.map (MulAut.conj g).toMonoidHom := by
      apply map_conj_eq_of_pointwise
      intro x hx
      have := hcg x hx
      rw [inv_inv] at this
      simpa [mul_assoc] using this
    rw [hpt]
    exact hgE
  obtain ⟨Q₀, hQ₀, hEQ₀, n₀, hn₀, hn₀E⟩ := exists_moving_step_subgroup hc hcE
  let 𝒬 : Set (Subgroup G) := {Q | Q ≤ T ∧ E ≤ Q ∧ Subgroup.centralizer (Q : Set G) ⊓ T ≤ Q ∧
    ∃ n ∈ Subgroup.normalizer (Q : Set G), n ∉ Subgroup.normalizer (E : Set G)}
  have hQ₀mem : Q₀ ∈ 𝒬 := ⟨hQ₀.1, hEQ₀, hQ₀.2.2.1, n₀, hn₀, hn₀E⟩
  obtain ⟨Q, hQmem, hQmax⟩ := Set.exists_max_image 𝒬 (fun Q : Subgroup G => Nat.card Q)
    (Set.toFinite 𝒬) ⟨Q₀, hQ₀mem⟩
  obtain ⟨hQT, hEQ, hCQ, hmove⟩ := hQmem
  refine ⟨Q, hQT, hEQ, hCQ, hmove, fun Q' hQQ' hQ'T => ?_⟩
  by_contra hnot
  have hQ'mem : Q' ∈ 𝒬 := by
    refine ⟨hQ'T, hEQ.trans hQQ'.le, ?_, ?_⟩
    · intro x hx
      exact hQQ'.le (hCQ ⟨Subgroup.centralizer_le hQQ'.le hx.1, hx.2⟩)
    · by_contra hno
      push Not at hno
      exact hnot fun x hx => hno x hx
  have := hQmax Q' hQ'mem
  have hlt := Subgroup.card_lt_of_lt hQQ'
  omega

end CFSG.CGT.PushingUpLit.T2KSW
