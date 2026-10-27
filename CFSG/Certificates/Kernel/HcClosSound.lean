module

public import Certificates.Data.Kernel.HcClos
public import CFSG.Certificates.Kernel.HcReplaySound

public section

namespace CFSG.KC.HcPack

section Pos

variable (q : ℕ → ℕ → ℕ → Bool) (get : ℕ → ℕ) (E : List ℕ) (hg : ∀ i, get i = E.getD i 0)

include hg in
theorem posG_sound (x : ℕ) (k : List ℕ → Bool) :
    ∀ (gs ds : List ℕ), posG q get E.length x gs k ds = true →
      (∀ g ∈ gs, ∃ e ∈ E, q e x g = true) ∧ ∃ ds', k ds' = true
  | [], ds, h => ⟨fun _ hg' => absurd hg' List.not_mem_nil, ds, h⟩
  | g :: gs, [], h => absurd h Bool.false_ne_true
  | g :: gs, d :: ds, h => by
    have e : posG q get E.length x (g :: gs) k (d :: ds) =
        andB (Nat.blt d E.length) (andB (q (get d) x g) (posG q get E.length x gs k ds)) := rfl
    rw [e] at h
    obtain ⟨h1, h⟩ := andB_true h
    obtain ⟨h2, h3⟩ := andB_true h
    obtain ⟨ih1, ih2⟩ := posG_sound x k gs ds h3
    refine ⟨fun g' hg' => ?_, ih2⟩
    rcases List.mem_cons.1 hg' with rfl | hg'
    · have hd : d < E.length := Nat.blt_eq.mp h1
      refine ⟨get d, ?_, h2⟩
      rw [hg, List.getD_eq_getElem _ _ hd]
      exact List.getElem_mem _
    · exact ih1 g' hg'

include hg in
theorem posB_sound (gs : List ℕ) :
    ∀ (xs ds : List ℕ), posB q get E.length gs xs ds = true →
      ∀ x ∈ xs, ∀ g ∈ gs, ∃ e ∈ E, q e x g = true
  | [], _, _ => fun _ hx => absurd hx List.not_mem_nil
  | x :: xs, ds, h => by
    have e : posB q get E.length gs (x :: xs) ds =
        posG q get E.length x gs (posB q get E.length gs xs) ds := rfl
    rw [e] at h
    obtain ⟨h1, ds', h2⟩ := posG_sound q get E hg x _ gs ds h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h1
    · exact posB_sound gs xs ds' h2 y hy

end Pos

theorem closB_sound (mul : ℕ → ℕ → ℕ) (E gs xs ds : List ℕ)
    (h : closB mul (getT (ofT E.length E)) E.length gs xs ds = true) :
    ∀ x ∈ xs, ∀ g ∈ gs, mul x g ∈ E := by
  intro x hx g hg
  obtain ⟨e, he, hq⟩ := posB_sound _ _ E (getT_ofT _ _ (Nat.le_refl _)) gs xs ds h x hx g hg
  rwa [← Nat.eq_of_beq_eq_true hq]

end CFSG.KC.HcPack

end
