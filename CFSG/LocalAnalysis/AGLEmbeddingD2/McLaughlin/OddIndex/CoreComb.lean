module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Classical

@[expose] noncomputable def orb {Ω : Type} (f : Ω → Ω) (x : Ω) : Finset Ω := {x, f x, f (f x)}

theorem mem_orb_self {Ω : Type} (f : Ω → Ω) (x : Ω) : x ∈ orb f x := by simp [orb]

section Comb

variable {Ω : Type} {f g : Ω → Ω} {D : Ω → Prop}

theorem orb_card {f : Ω → Ω} (hf : ∀ x, f (f (f x)) = x) {x : Ω} (h : f x ≠ x) :
    (orb f x).card = 3 := by
  have h1 : f (f x) ≠ x := fun e => h (by
    have := hf x
    rw [e] at this; exact this)
  have h2 : f x ≠ f (f x) := fun e => h (e.trans (by
    have := congrArg f e
    rw [hf x] at this
    exact this))
  rw [orb, Finset.card_insert_of_notMem, Finset.card_pair h2]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun e => h e.symm, fun e => h1 e.symm⟩

theorem orb_eq_of_mem {f : Ω → Ω} (hf : ∀ x, f (f (f x)) = x) {x y : Ω} (hy : y ∈ orb f x) :
    orb f y = orb f x := by
  simp only [orb, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
  rcases hy with rfl | rfl | rfl
  · rfl
  · simp only [hf]
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · simp only [hf]
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem g_mem_orb (hf : ∀ x, f (f (f x)) = x) (hg : ∀ x, g (g (g x)) = x)
    (hfx : ∀ x, D x → f x ≠ x) (hgx : ∀ x, D x → g x ≠ x)
    (hDf : ∀ x, D x → D (f x))
    (h5 : ∀ x, D x → ∃ y, y ≠ x ∧ y ∈ orb f x ∧ y ∈ orb g x) {x : Ω} (hx : D x) :
    g x ∈ orb f x := by
  obtain ⟨y, hyx, hyT, hyW⟩ := h5 x hx
  have hDT : ∀ r ∈ orb f x, D r := by
    intro r hr
    simp only [orb, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact hx
    · exact hDf _ hx
    · exact hDf _ (hDf _ hx)
  have hTc : (orb f x).card = 3 := orb_card hf (hfx x hx)
  have hWc : (orb g x).card = 3 := orb_card hg (hgx x hx)
  have hTW : orb f x ⊆ orb g x := by
    intro r hr
    by_contra hrW
    have hrx : r ≠ x := fun e => hrW (e ▸ mem_orb_self g x)
    have hry : r ≠ y := fun e => hrW (e ▸ hyW)
    obtain ⟨q, hqr, hqT, hqW⟩ := h5 r (hDT r hr)
    rw [orb_eq_of_mem hf hr] at hqT
    have h3 : ({x, y, r} : Finset Ω) = orb f x := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact mem_orb_self f _
        · exact hyT
        · exact hr
      · rw [hTc, Finset.card_insert_of_notMem, Finset.card_pair hry.symm]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hyx.symm, hrx.symm⟩
    rw [← h3] at hqT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqT
    have hqW' : q ∈ orb g x := by
      rcases hqT with rfl | rfl | rfl
      · exact mem_orb_self g _
      · exact hyW
      · exact absurd rfl hqr
    exact hrW (by
      rw [← orb_eq_of_mem hg hqW', orb_eq_of_mem hg hqW]
      exact mem_orb_self g r)
  have heq : orb f x = orb g x := Finset.eq_of_subset_of_card_le hTW (by rw [hTc, hWc])
  rw [heq]
  simp [orb]

end Comb

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
