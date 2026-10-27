module

public import Certificates.Data.Kernel.G23F48.Reach
public import CFSG.Sporadic.Schreier.ONPermArr

public section

namespace CFSG.KC.G23F48

open CFSG.ONSchreier

variable {n k p : ℕ} {G : Array (Array ℕ)} {T : List (ℕ × ℕ × ℕ)}

theorem reachOK_spec (h : reachOK n k p G T = true) :
    (T.getD 0 (0, 0, 0)).1 = p ∧ p < n ∧ ∀ i < T.length, (T.getD i (0, 0, 0)).1 < n ∧
      (i = 0 ∨ (T.getD i (0, 0, 0)).2.1 < i ∧ (T.getD i (0, 0, 0)).2.2 < k ∧
        (G[(T.getD i (0, 0, 0)).2.2]!)[(T.getD (T.getD i (0, 0, 0)).2.1 (0, 0, 0)).1]! =
          (T.getD i (0, 0, 0)).1) := by
  unfold reachOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun i hi => ?_⟩
  have := h3 i hi
  tauto

theorem reach_of_reachOK {H : Subgroup (Equiv.Perm (Fin n))} {σ : ℕ → Equiv.Perm (Fin n)}
    (hσ : ∀ s < k, PRep n G[s]! (σ s) ∧ σ s ∈ H) (h : reachOK n k p G T = true) (hp : p < n) :
    ∀ i < T.length, ∃ g ∈ H, ((g ⟨p, hp⟩ : Fin n) : ℕ) = (T.getD i (0, 0, 0)).1 := by
  obtain ⟨h1, -, h3⟩ := reachOK_spec h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, h0 | ⟨hj, hs, he⟩⟩ := h3 i hi
    · subst h0
      exact ⟨1, H.one_mem, by rw [h1]; rfl⟩
    · obtain ⟨g, hg, hgp⟩ := ih _ hj (by omega)
      refine ⟨σ (T.getD i (0, 0, 0)).2.2 * g, H.mul_mem (hσ _ hs).2 hg, ?_⟩
      rw [Equiv.Perm.mul_apply, ← (hσ _ hs).1 (g ⟨p, hp⟩), hgp, he]

theorem orbit_of_reachOK {H : Subgroup (Equiv.Perm (Fin n))} {σ : ℕ → Equiv.Perm (Fin n)}
    (hσ : ∀ s < k, PRep n G[s]! (σ s) ∧ σ s ∈ H) (h : reachOK n k p G T = true) (hp : p < n)
    (hnd : (T.map Prod.fst).Nodup) :
    ∃ O : Finset (Fin n), O.card = T.length ∧ ∀ r ∈ O, ∃ g ∈ H, g ⟨p, hp⟩ = r := by
  obtain ⟨-, -, h3⟩ := reachOK_spec h
  let f : Fin T.length → Fin n := fun i => ⟨(T.getD i (0, 0, 0)).1, (h3 i i.2).1⟩
  have hf : Function.Injective f := fun i j e => by
    have e' : (T.getD i (0, 0, 0)).1 = (T.getD j (0, 0, 0)).1 := congrArg Fin.val e
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2,
      List.getElem?_eq_getElem j.2, Option.getD_some] at e'
    have hi : (T.map Prod.fst)[(i : ℕ)]'(by simp) = (T.map Prod.fst)[(j : ℕ)]'(by simp) := by
      simpa using e'
    exact Fin.ext ((hnd.getElem_inj_iff).1 hi)
  refine ⟨Finset.univ.image f, by rw [Finset.card_image_of_injective _ hf]; simp, ?_⟩
  intro r hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
  obtain ⟨g, hg, hgp⟩ := reach_of_reachOK hσ h hp i i.2
  exact ⟨g, hg, Fin.ext hgp⟩

end CFSG.KC.G23F48

end
