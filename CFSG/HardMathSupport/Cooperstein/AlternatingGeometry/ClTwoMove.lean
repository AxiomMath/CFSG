module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairPreserving
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_even_swapping_element (σ : Perm Ω) (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x)
    (c : Ω → Bool) (hc : ∀ x, c (σ x) = c x) (Ss W : Subgroup (Perm Ω)) (hWS : W ≤ Ss)
    (hWsw : ∀ x, c x = false → swap x (σ x) ∈ W)
    (hWuniq : ∀ x y, x ≠ y → swap x y ∈ W → c x = false → y = σ x)
    (hnormW : ∀ s ∈ Ss, ∀ w ∈ W, s * w * s⁻¹ ∈ W)
    (htrue : ∀ s ∈ Ss, ∀ x, c x = true → s x = x ∨ s x = σ x)
    (hU : ∀ g ∈ pairPres σ hσ1 hσ2, g ∈ alternatingGroup Ω → g ∈ Ss)
    (hF : (Finset.univ.filter fun x => c x = false).card = 4)
    (hmove : ∃ s ∈ Ss, ∃ y, s y ≠ y ∧ s y ≠ σ y) :
    ∃ a b : Ω, a ≠ σ a ∧ b ≠ a ∧ b ≠ σ a ∧ c a = false ∧ c b = false ∧
      (∀ x, c x = false → x = a ∨ x = σ a ∨ x = b ∨ x = σ b) ∧
      ∃ s2 ∈ Ss, s2 ∈ alternatingGroup Ω ∧ (∀ x, c x = true → s2 x = x) ∧
        (∀ x, c x = false → c (s2 x) = false) ∧ (s2 a = b ∨ s2 a = σ b) := by
  classical
  obtain ⟨s0, hs0, y0, hy1, hy2⟩ := hmove
  have hy0F : c y0 = false := by
    by_contra h
    have h' : c y0 = true := by simpa using h
    rcases htrue s0 hs0 y0 h' with e | e
    · exact hy1 e
    · exact hy2 e
  have hFclosed : ∀ s ∈ Ss, ∀ x, c x = false → c (s x) = false := by
    intro s hs x hx
    by_contra h
    have h' : c (s x) = true := by simpa using h
    rcases htrue s⁻¹ (Ss.inv_mem hs) (s x) h' with e | e
    · have e0 : s⁻¹ (s x) = x := by simp
      rw [e0] at e
      rw [e] at hx; rw [hx] at h'; simp at h'
    · have e0 : s⁻¹ (s x) = x := by simp
      rw [e0] at e
      rw [e, hc] at hx; rw [hx] at h'; simp at h'
  set a := y0 with ha
  set b := s0 a with hb
  have hcb : c b = false := hFclosed s0 hs0 a hy0F
  have hca' : c (σ a) = false := by rw [hc]; exact hy0F
  have hcb' : c (σ b) = false := by rw [hc]; exact hcb
  have haσ : a ≠ σ a := (hσ1 a).symm
  have hbσ : b ≠ σ b := (hσ1 b).symm
  have hba : b ≠ a := hy1
  have hbσa : b ≠ σ a := hy2
  have hσba : σ b ≠ a := fun h => hbσa (by rw [← hσ2 b, h])
  have hσbσa : σ b ≠ σ a := fun h => hba (by simpa [hσ2] using congrArg σ h)
  have hFset : ∀ x, c x = false → x = a ∨ x = σ a ∨ x = b ∨ x = σ b := by
    have hsub : ({a, σ a, b, σ b} : Finset Ω) ⊆ Finset.univ.filter fun x => c x = false := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hcard4 : ({a, σ a, b, σ b} : Finset Ω).card = 4 := by
      have n1 : σ a ∉ ({b, σ b} : Finset Ω) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hbσa.symm, hσbσa.symm⟩
      have n2 : a ∉ ({σ a, b, σ b} : Finset Ω) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨haσ, hba.symm, hσba.symm⟩
      rw [Finset.card_insert_of_notMem n2, Finset.card_insert_of_notMem n1, Finset.card_pair hbσ]
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard4, hF])
    intro x hx
    have : x ∈ ({a, σ a, b, σ b} : Finset Ω) := by
      rw [heq]; simp [hx]
    simpa [or_assoc] using this
  have hs0true : ∀ x, c x = true → s0 (s0 x) = x := by
    intro x hx
    rcases htrue s0 hs0 x hx with e | e
    · rw [e, e]
    · rw [e]
      have hσx : c (σ x) = true := by rw [hc]; exact hx
      rcases htrue s0 hs0 (σ x) hσx with e' | e'
      · exact absurd (s0.injective (e'.trans e.symm)) (hσ1 x)
      · rw [e', hσ2]
  have hinv : Function.Involutive (fun x => if c x = true then s0 x else x) := by
    intro x
    by_cases hx : c x = true
    · have hs : c (s0 x) = true := by
        rcases htrue s0 hs0 x hx with e | e
        · rw [e]; exact hx
        · rw [e, hc]; exact hx
      simp only [hx, hs, ite_true]
      exact hs0true x hx
    · simp [hx]
  let r : Perm Ω := hinv.toPerm
  have hr : ∀ x, r x = if c x = true then s0 x else x := fun x => rfl
  have hrpp : r ∈ pairPres σ hσ1 hσ2 := by
    intro z
    rw [hr z]
    by_cases hz : c z = true
    · rw [if_pos hz]; exact htrue s0 hs0 z hz
    · rw [if_neg hz]; exact Or.inl rfl
  have hswa : swap a (σ a) ∈ Ss := hWS (hWsw a hy0F)
  have hrS : r ∈ Ss := by
    by_cases hev : r ∈ alternatingGroup Ω
    · exact hU r hrpp hev
    · have hsg : sign r = -1 := by
        rcases Int.units_eq_one_or (sign r) with h | h
        · exact absurd (mem_alternatingGroup.2 h) hev
        · exact h
      have hev' : r * swap a (σ a) ∈ alternatingGroup Ω := by
        rw [mem_alternatingGroup, Perm.sign_mul, hsg, sign_swap haσ]; decide
      have hmem := hU _ ((pairPres σ hσ1 hσ2).mul_mem hrpp (swap_mem_pairPres hσ1 hσ2 a)) hev'
      have := Ss.mul_mem hmem hswa
      rwa [mul_assoc, swap_mul_self, mul_one] at this
  set s1 : Perm Ω := r * s0 with hs1def
  have hs1 : s1 ∈ Ss := Ss.mul_mem hrS hs0
  have hs1true : ∀ x, c x = true → s1 x = x := by
    intro x hx
    have hs : c (s0 x) = true := by
      rcases htrue s0 hs0 x hx with e | e
      · rw [e]; exact hx
      · rw [e, hc]; exact hx
    show r (s0 x) = x
    rw [hr, if_pos hs]
    exact hs0true x hx
  have hs1F : ∀ x, c x = false → s1 x = s0 x := by
    intro x hx
    have hs : ¬ c (s0 x) = true := by
      rw [hFclosed s0 hs0 x hx]; simp
    show r (s0 x) = s0 x
    rw [hr, if_neg hs]
  have hs1a : s1 a = b := hs1F a hy0F
  have hs1a' : s1 (σ a) = σ b := by
    have h1 := hnormW s1 hs1 (swap a (σ a)) (hWsw a hy0F)
    rw [← swap_apply_apply, hs1a] at h1
    refine hWuniq b _ ?_ h1 hcb
    intro h
    exact haσ (s1.injective (hs1a.trans h))
  by_cases hsg : sign s1 = 1
  · exact ⟨a, b, haσ, hba, hbσa, hy0F, hcb, hFset, s1, hs1, mem_alternatingGroup.2 hsg, hs1true,
      fun x hx => by rw [hs1F x hx]; exact hFclosed s0 hs0 x hx, Or.inl hs1a⟩
  · have hsg' : sign s1 = -1 := by
      rcases Int.units_eq_one_or (sign s1) with h | h
      · exact absurd h hsg
      · exact h
    refine ⟨a, b, haσ, hba, hbσa, hy0F, hcb, hFset, s1 * swap a (σ a), Ss.mul_mem hs1 hswa, ?_, ?_, ?_,
      Or.inr ?_⟩
    · rw [mem_alternatingGroup, Perm.sign_mul, hsg', sign_swap haσ]; decide
    · intro x hx
      have hxa : x ≠ a := fun h => by rw [h] at hx; rw [hy0F] at hx; simp at hx
      have hxa' : x ≠ σ a := fun h => by rw [h, hc] at hx; rw [hy0F] at hx; simp at hx
      show s1 (swap a (σ a) x) = x
      rw [swap_apply_of_ne_of_ne hxa hxa']
      exact hs1true x hx
    · intro x hx
      show c (s1 (swap a (σ a) x)) = false
      apply hFclosed s1 hs1
      by_cases hxa : x = a
      · rw [hxa, swap_apply_left]; exact hca'
      · by_cases hxa' : x = σ a
        · rw [hxa', swap_apply_right]; exact hy0F
        · rw [swap_apply_of_ne_of_ne hxa hxa']; exact hx
    · show s1 (swap a (σ a) a) = σ b
      rw [swap_apply_left, hs1a']

section Helpers

variable {σ : Perm Ω} {hσ1 : ∀ x, σ x ≠ x} {hσ2 : ∀ x, σ (σ x) = x}

theorem pairPres_comm {g h : Perm Ω} (hg : g ∈ pairPres σ hσ1 hσ2) (hh : h ∈ pairPres σ hσ1 hσ2) :
    g * h = h * g := by
  ext x
  simp only [Perm.mul_apply]
  rcases pair_cases hσ1 hσ2 hg x with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;>
    rcases pair_cases hσ1 hσ2 hh x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp [g1, g2, h1, h2]

theorem comm_sigma_of_normalizer {W : Subgroup (Perm Ω)} (hW : W ≤ pairPres σ hσ1 hσ2)
    (hflip : ∀ x, ∃ w ∈ W, w x = σ x) {h : Perm Ω}
    (hh : h ∈ Subgroup.normalizer (W : Set (Perm Ω))) (x : Ω) : h (σ x) = σ (h x) := by
  obtain ⟨w, hw, hwx⟩ := hflip x
  have hc : h * w * h⁻¹ ∈ W := ((Subgroup.mem_normalizer_iff.1 hh) w).1 hw
  have key : (h * w * h⁻¹) (h x) = h (σ x) := by simp [Perm.mul_apply, hwx]
  rcases hW hc (h x) with e | e
  · exfalso
    rw [key] at e
    exact hσ1 x (h.injective e)
  · rw [key] at e; exact e

theorem conj_mem_pairPres {h : Perm Ω} (hσh : ∀ x, h (σ x) = σ (h x)) {u : Perm Ω}
    (hu : u ∈ pairPres σ hσ1 hσ2) : h * u * h⁻¹ ∈ pairPres σ hσ1 hσ2 := by
  intro z
  simp only [Perm.mul_apply]
  rcases hu (h⁻¹ z) with e | e
  · left; rw [e]; simp
  · right; rw [e, hσh]; simp

end Helpers

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
