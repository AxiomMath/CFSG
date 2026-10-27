module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Blocks

variable {n : ℕ}

theorem exists_maxBlock {I : Set ℕ} (i : ℕ) (hi : i < n) :
    ∃ a b : ℕ, a ≤ i ∧ i < b ∧ b ≤ n ∧ (a = 0 ∨ a ∈ I) ∧ (b = n ∨ b ∈ I) ∧
      ∀ c ∈ I, ¬ (a < c ∧ c < b) := by
  classical
  let P : ℕ → Prop := fun c => c = 0 ∨ c ∈ I
  have hP0 : P 0 := Or.inl rfl
  let a := Nat.findGreatest P i
  have hQ : ∃ c, i < c ∧ (c = n ∨ c ∈ I) := ⟨n, hi, Or.inl rfl⟩
  let b := Nat.find hQ
  have ha1 : a ≤ i := Nat.findGreatest_le i
  have haP : P a := Nat.findGreatest_spec (P := P) (Nat.zero_le i) hP0
  have hbQ : i < b ∧ (b = n ∨ b ∈ I) := Nat.find_spec hQ
  have hbn : b ≤ n := Nat.find_min' hQ ⟨hi, Or.inl rfl⟩
  refine ⟨a, b, ha1, hbQ.1, hbn, haP, hbQ.2, fun c hc ⟨hac, hcb⟩ => ?_⟩
  by_cases hci : c ≤ i
  · exact absurd (Or.inr hc) (Nat.findGreatest_is_greatest hac hci)
  · exact absurd (Nat.find_min' hQ ⟨not_le.mp hci, Or.inr hc⟩) (not_le.mpr hcb)

end Blocks

section Flag

variable {n : ℕ} {K : Type*} [Field K]

theorem mem_stabilizer_flagSpace_of_entries {i : ℕ} {g : SpecialLinearGroup (Fin n) K}
    (h : ∀ k l : Fin n, (l : ℕ) < i → i ≤ (k : ℕ) → (g : Matrix (Fin n) (Fin n) K) k l = 0) :
    g ∈ stabilizer (flagSpace n K i) := by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_flagSpace] at hv
  rw [mem_flagSpace]
  intro k hk
  rw [mulVecLin_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) < i
  · rw [h k l hl hk, zero_mul]
  · rw [hv l (not_lt.mp hl), mul_zero]

theorem mem_flagStabilizer_of_entries {I : Set ℕ} {g : SpecialLinearGroup (Fin n) K}
    (h : ∀ k l : Fin n, ∀ c ∈ I, (l : ℕ) < c → c ≤ (k : ℕ) →
      (g : Matrix (Fin n) (Fin n) K) k l = 0) : g ∈ flagStabilizer n K I :=
  mem_flagStabilizer.mpr fun c hc =>
    mem_stabilizer_flagSpace_of_entries fun k l hl hk => h k l c hc hl hk

theorem mem_unitriangular_of_blocks {I : Set ℕ} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ flagStabilizer n K I)
    (hblocks : ∀ (a m : ℕ) (h : a + m ≤ n), (a = 0 ∨ a ∈ I) → (a + m = n ∨ a + m ∈ I) →
      (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) →
      blkAt a m h (g : Matrix (Fin n) (Fin n) K) = 1) : g ∈ unitriangular n K := by
  have hblk : ∀ (i j : Fin n), ∀ a b : ℕ, a ≤ (i : ℕ) → (i : ℕ) < b → a ≤ (j : ℕ) → (j : ℕ) < b →
      b ≤ n → (a = 0 ∨ a ∈ I) → (b = n ∨ b ∈ I) → (∀ c ∈ I, ¬ (a < c ∧ c < b)) →
      (g : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0 := by
    intro i j a b hai hib haj hjb hbn ha hb hc
    have h1 := hblocks a (b - a) (by omega) ha (by
      rcases hb with hb | hb
      · left; omega
      · right; rwa [show a + (b - a) = b by omega]) (by
      intro c hcI
      have := hc c hcI
      omega)
    have h2 := congrFun (congrFun h1 ⟨(i : ℕ) - a, by omega⟩) ⟨(j : ℕ) - a, by omega⟩
    rw [blkAt_apply, Matrix.one_apply] at h2
    have e1 : (⟨a + ((i : ℕ) - a), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
    have e2 : (⟨a + ((j : ℕ) - a), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
    rw [e1, e2] at h2
    rw [h2]
    simp only [Fin.ext_iff]
    congr 1
    apply propext
    omega
  refine ⟨fun k l hlk => ?_, fun k => ?_⟩
  · obtain ⟨a, b, hal, hlb, hbn, ha, hb, hc⟩ := exists_maxBlock (I := I) (l : ℕ) l.isLt
    by_cases hkb : (k : ℕ) < b
    · rw [hblk k l a b (by omega) hkb hal hlb hbn ha hb hc]
      simp [ne_of_gt hlk]
    · have hbI : b ∈ I := by
        rcases hb with hb | hb
        · exact absurd k.isLt (by omega)
        · exact hb
      exact stabilizer_entries (mem_flagStabilizer.mp hg b hbI) hlb (not_lt.mp hkb)
  · obtain ⟨a, b, hak, hkb, hbn, ha, hb, hc⟩ := exists_maxBlock (I := I) (k : ℕ) k.isLt
    rw [hblk k k a b hak hkb hak hkb hbn ha hb hc]
    simp

end Flag

end CFSG.QuasithinUnique.Vol2Native.A312L
