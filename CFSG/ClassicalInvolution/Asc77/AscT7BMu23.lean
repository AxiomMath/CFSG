module

public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonInputs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7B

theorem nonempty_mulEquiv_klein {Q : Type*} [Group Q] {d d' : Q} (hd : d * d = 1)
    (hd' : d' * d' = 1) (hd1 : d ≠ 1) (hd'1 : d' ≠ 1) (hne : d ≠ d') (hc : d * d' = d' * d)
    (hgen : Subgroup.closure ({d, d'} : Set Q) = ⊤) :
    Nonempty (Q ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
  have hdd : d * (d * d') = d' := by rw [← mul_assoc, hd, one_mul]
  have hd'd : d' * d = d * d' := hc.symm
  have h1 : d * d' * d = d' := by rw [hc, mul_assoc, hd, mul_one]
  have h2 : d' * (d * d') = d := by rw [hc, ← mul_assoc, hd', one_mul]
  have e5 : d * d' * d' = d := by rw [mul_assoc, hd', mul_one]
  have e7 : d * d' * (d * d') = 1 := by rw [mul_assoc, h2, hd]
  have hall : ∀ x : Q, x = 1 ∨ x = d ∨ x = d' ∨ x = d * d' := by
    intro x
    have hx : x ∈ Subgroup.closure ({d, d'} : Set Q) := hgen ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr (Or.inl (by simpa using hy)))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
        simp [hd, hd', hdd, hd'd, h1, h2, e5, e7]
    | inv x _ hx =>
      have hinv : ∀ y : Q, (y = 1 ∨ y = d ∨ y = d' ∨ y = d * d') → y⁻¹ = y := by
        intro y hy
        rcases hy with hy | hy | hy | hy <;> rw [hy]
        · simp
        · exact inv_eq_of_mul_eq_one_left hd
        · exact inv_eq_of_mul_eq_one_left hd'
        · exact inv_eq_of_mul_eq_one_left e7
      rw [hinv x hx]
      exact hx
  have hsq : ∀ x : Q, x * x = 1 := by
    intro x
    rcases hall x with hx | hx | hx | hx <;> rw [hx]
    · simp
    · exact hd
    · exact hd'
    · exact e7
  have hdd'1 : d * d' ≠ 1 := fun h => hne (by
    calc d = d * 1 := (mul_one d).symm
      _ = d * (d * d') := by rw [h]
      _ = d' := hdd)
  have hdd'd : d * d' ≠ d := fun h => hd'1 (by
    have := congrArg (d * ·) h
    simpa [← mul_assoc, hd] using this)
  have hdd'd' : d * d' ≠ d' := fun h => hd1 (by
    have := congrArg (· * d') h
    simpa [mul_assoc, hd'] using this)
  have hcard : Nat.card Q = 4 := by
    have hU : (Set.univ : Set Q) = {1, d, d', d * d'} := by
      ext x
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
      exact hall x
    rw [← Set.ncard_univ, hU]
    have n1 : (1 : Q) ∉ ({d, d', d * d'} : Set Q) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hd1.symm, hd'1.symm, hdd'1.symm⟩
    have n2 : d ∉ ({d', d * d'} : Set Q) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, hdd'd.symm⟩
    have n3 : d' ∉ ({d * d'} : Set Q) := by
      simp only [Set.mem_singleton_iff]
      exact hdd'd'.symm
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_insert_of_notMem n3, Set.ncard_singleton]
  have hexp : Monoid.exponent Q = 2 := by
    have : Nontrivial Q := ⟨⟨d, 1, hd1⟩⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq g) hg
  have : IsKleinFour Q := ⟨hcard, hexp⟩
  exact IsKleinFour.nonempty_mulEquiv

end T7B

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C23_1_clique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting p f Ω K K' z → ∀ W ∈ WSet Ω,
      (Thompson.muDelta Ω W).Nonempty ∧ ∀ d ∈ Thompson.muDelta Ω W,
        (Star3T.cent (Thompson.muDelta Ω W) d).ncard = 2

variable {p f}

theorem c23_1_of (h1 : ThompsonCube p f) (h2 : ThompsonStar p f) (hdict : C23_1_clique p f) :
    C23_1 p f := by
  intro G _ _ _ Ω K K' z h W hW
  have hs := h.setting
  obtain ⟨⟨d₀, hd₀⟩, hcl⟩ := hdict G Ω K K' z hs W hW
  have hst : AscStand p f Ω K := hs.stand
  have hP : PartIHyp p f Ω := ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩
  have hTT : Star3T.IsTT (Thompson.muDelta Ω W) :=
    Thompson.isTT_muDelta hst.odd hst.five hst.hyp hW (h1 G Ω hP W hW)
  have hS : Star3T.IsStar (Thompson.muDelta Ω W) :=
    Thompson.isStar_muDelta hst.odd hst.five hst.hyp hW (h2 G Ω hP W hW)
  by_cases hconn : ∀ d ∈ Thompson.muDelta Ω W, ∀ a ∈ Thompson.muDelta Ω W,
      Star3T.Conn (Thompson.muDelta Ω W) d a
  · left
    set Δ := Thompson.muDelta Ω W with hΔ
    obtain ⟨d', hne, hcent⟩ : ∃ d', d₀ ≠ d' ∧ Star3T.cent Δ d₀ = {d₀, d'} := by
      obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.mp (hcl d₀ hd₀)
      have hdx : d₀ ∈ ({x, y} : Set _) := hxy' ▸ Star3T.self_mem_cent hd₀
      rcases hdx with rfl | hdy
      · exact ⟨y, hxy, hxy'⟩
      · rw [Set.mem_singleton_iff] at hdy
        subst hdy
        exact ⟨x, fun e => hxy e.symm, by rw [hxy', Set.pair_comm]⟩
    have hd'c : d' ∈ Star3T.cent Δ d₀ := by rw [hcent]; exact Or.inr rfl
    have hd'Δ : d' ∈ Δ := hd'c.1
    have hcomm : d₀ * d' = d' * d₀ := hd'c.2.symm
    have hcent' : Star3T.cent Δ d' = {d₀, d'} := by
      have hsub : ({d₀, d'} : Set _) ⊆ Star3T.cent Δ d' := by
        intro x hx
        rcases hx with rfl | rfl
        · exact ⟨hd₀, hcomm⟩
        · exact Star3T.self_mem_cent hd'Δ
      exact (Set.eq_of_subset_of_ncard_le hsub
        (by rw [hcl d' hd'Δ, Set.ncard_pair hne]) (Set.toFinite _)).symm
    have hall : ∀ a, Relation.ReflTransGen (Star3T.Adj Δ) d₀ a → a = d₀ ∨ a = d' := by
      intro a hb
      induction hb with
      | refl => exact Or.inl rfl
      | @tail b c _ hbc ih =>
        obtain ⟨-, hc, hbc⟩ := hbc
        rcases ih with rfl | rfl
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent] at this
          exact this
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent'] at this
          exact this
    have hΔeq : Δ = {d₀, d'} := by
      ext a
      constructor
      · exact fun ha => hall a (hconn d₀ hd₀ a ha)
      · rintro (rfl | rfl)
        · exact hd₀
        · exact hd'Δ
    have hgen : Subgroup.closure ({d₀, d'} : Set ↥(muGroup Ω W)) = ⊤ := by
      rw [← hΔeq]
      exact hTT.closure_eq_top
    exact T7B.nonempty_mulEquiv_klein (hTT.mul_self d₀ hd₀) (hTT.mul_self d' hd'Δ)
      (hTT.ne_one d₀ hd₀) (hTT.ne_one d' hd'Δ) hne hcomm hgen
  · right
    push Not at hconn
    obtain ⟨d, hd, a, ha, hnc⟩ := hconn
    obtain ⟨e, -⟩ := Star3T.exists_mulEquiv_perm_four hTT hS hd ha hnc (hcl d hd)
    exact ⟨e⟩

end CFSG.ClassicalInvolution.Asc77
