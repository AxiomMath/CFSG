module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentLift
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentRoots

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin

theorem kap_surj {n : ℕ} (r : Fin n ⊕ Fin n) : ∃ b t, r = kap b t := by
  rcases r with b | b
  · exact ⟨b, true, rfl⟩
  · exact ⟨b, false, rfl⟩

theorem exists_two_ne {n : ℕ} (hn : 3 ≤ n) (a : Fin n) :
    ∃ b₁ b₂ : Fin n, b₁ ≠ a ∧ b₂ ≠ a ∧ b₁ ≠ b₂ := by
  by_cases h0 : a.val = 0
  · exact ⟨⟨1, by omega⟩, ⟨2, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega,
      fun e => by simp [Fin.ext_iff] at e; omega, fun e => by simp [Fin.ext_iff] at e⟩
  · by_cases h1 : a.val = 1
    · exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega,
        fun e => by simp [Fin.ext_iff] at e; omega, fun e => by simp [Fin.ext_iff] at e⟩
    · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega,
        fun e => by simp [Fin.ext_iff] at e; omega, fun e => by simp [Fin.ext_iff] at e⟩

section Node

variable {m : ℕ} {F : Type} [Field F] [CharP F 2]

theorem mem_pSet_iff {A : Set (Fin (m + 3))} {σ : Fin (m + 3) → Bool} {b : Fin (m + 3)} {t : Bool} :
    kap b t ∈ pSet A σ ↔ b ∈ A ∧ σ b = t := by
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨rfl, h2⟩ := kap_inj he
    exact ⟨ha, h2.symm⟩
  · rintro ⟨hb, rfl⟩
    exact ⟨b, hb, rfl⟩

theorem hQ_spinMat (k : spinGroup (quadPlus (m + 3) F)) :
    ∀ v, Qf (m + 3) ((spinMat (quadPlus (m + 3) F) k).mulVec v) = Qf (m + 3) v := fun v => by
  have := spinMatrix_mem (quadPlus (m + 3) F) k v
  rw [spinMat_eq_coe]
  simpa [Qf, quadPlus_apply] using this

theorem cfg_node (hn : 3 ≤ m + 3) (j : Fin (m + 3)) (k : spinGroup (quadPlus (m + 3) F))
    (hk : ∀ u ∈ CFSG.AGLEmbedding.LieOut.radical (plusDatum (m + 3) F hn) j, k * u = u * k) :
    Cfg (spinMat (quadPlus (m + 3) F) k) (pSet (nodeA (m + 3) j) (nodeSign (m + 3) j)) := by
  classical
  set A := nodeA (m + 3) j with hA
  set σ := nodeSign (m + 3) j with hσ
  set G := spinMat (quadPlus (m + 3) F) k with hG
  have hd := pSet_disj A σ
  have hm : ∀ p ∈ pSet A σ, ∀ r, bar r ∉ pSet A σ → r ≠ p → HM G p r := by
    rintro p ⟨a, ha, rfl⟩ r hr hrp
    obtain ⟨b, t, rfl⟩ := kap_surj r
    rw [bar_kap] at hr
    have hab : a ≠ b := by
      rintro rfl
      have : t = !σ a := by
        cases ht : t <;> cases hs : σ a <;> simp_all
      subst this
      exact hr (by rw [Bool.not_not]; exact (mem_pSet_iff).2 ⟨ha, rfl⟩)
    have hb : b ∉ A ∨ (b ∈ A ∧ t = σ b) := by
      by_cases hbA : b ∈ A
      · right
        refine ⟨hbA, ?_⟩
        by_contra hne
        have : t = !σ b := by cases ht : t <;> cases hs : σ b <;> simp_all
        subst this
        exact hr ((mem_pSet_iff).2 ⟨hbA, by simp⟩)
      · exact Or.inl hbA
    have hx := longRoot_mem_radical hn j hab t ha hb (1 : F)
    have hcomm := hk _ hx
    intro x y
    have := comm_entries hn hab (σ a) t k hcomm x y
    simpa [bar_kap] using this
  have htwo : ∀ p ∈ pSet A σ, ∃ r₁ r₂, r₁ ≠ r₂ ∧ (bar r₁ ∉ pSet A σ ∧ r₁ ≠ p) ∧
      (bar r₂ ∉ pSet A σ ∧ r₂ ≠ p) := by
    rintro p ⟨a, ha, rfl⟩
    obtain ⟨b₁, b₂, h1, h2, h12⟩ := exists_two_ne hn a
    let tt : Fin (m + 3) → Bool := fun b => if b ∈ A then σ b else true
    have hr : ∀ b, b ≠ a → bar (kap b (tt b)) ∉ pSet A σ ∧ kap b (tt b) ≠ kap a (σ a) := by
      intro b hba
      refine ⟨fun h => ?_, fun h => hba (kap_inj h).1⟩
      rw [bar_kap] at h
      obtain ⟨hbA, he⟩ := (mem_pSet_iff).1 h
      simp only [tt, if_pos hbA] at he
      cases hs : σ b <;> simp_all
    exact ⟨kap b₁ (tt b₁), kap b₂ (tt b₂), fun e => h12 (kap_inj e).1, hr b₁ h1, hr b₂ h2⟩
  exact ⟨hd, hm, htwo⟩

end Node

end CFSG.HardMathSupport.Cooperstein.StructureLie
