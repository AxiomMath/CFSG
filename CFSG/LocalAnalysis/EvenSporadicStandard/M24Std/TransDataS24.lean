module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Tight
public import Certificates.Certificate24841

public section

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

theorem SxtNormChk.mem_iff {g : S24} (h : SxtNormChk m24E1l g) (s : S24) :
    s ∈ m24E1l ↔ g * s * g⁻¹ ∈ m24E1l := by
  refine ⟨fun hs => (h s hs).1, fun hs => ?_⟩
  have := (h _ hs).2
  simpa [mul_assoc] using this

theorem sxtFix_conj (g s : S24) : sxtFix (g * s * g⁻¹) = sxtFix s := by
  unfold sxtFix
  refine Finset.card_equiv (((g : Equiv.Perm (Fin 24)))⁻¹) fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : ((g * s * g⁻¹ : S24) : Equiv.Perm (Fin 24)) i =
      (g : Equiv.Perm (Fin 24)) ((s : Equiv.Perm (Fin 24)) ((g : Equiv.Perm (Fin 24))⁻¹ i)) := rfl
  rw [h1]
  constructor
  · intro h
    simpa using congrArg (fun j => ((g : Equiv.Perm (Fin 24)))⁻¹ j) h
  · intro h
    rw [h]
    simp

theorem sxt_mem_reachStep {P : S24 → Prop} {gs : List S24}
    (hg : ∀ g ∈ gs, ∀ x, P x → P (g * x * g⁻¹)) {l : List S24} (hl : ∀ x ∈ l, P x)
    (pi : ℕ × ℕ) : ∀ x ∈ sxtReachStep gs l pi, P x := by
  unfold sxtReachStep
  split
  · rename_i x g hx hg'
    intro y hy
    rw [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hl y hy
    · rw [normH_eq]
      exact hg g (List.mem_of_getElem? hg') x (hl x (List.mem_of_getElem? hx))
  · exact hl

theorem sxt_mem_reachSteps {P : S24 → Prop} {gs : List S24} {a : S24} (ha : P a)
    (hg : ∀ g ∈ gs, ∀ x, P x → P (g * x * g⁻¹)) (w : List (ℕ × ℕ)) :
    ∀ x ∈ sxtReachSteps gs a w, P x := by
  unfold sxtReachSteps
  suffices ∀ l : List S24, (∀ x ∈ l, P x) → ∀ x ∈ w.foldl (sxtReachStep gs) l, P x from
    this [a] (by simpa using ha)
  induction w with
  | nil => exact fun l hl => hl
  | cons pi w ih => exact fun l hl => ih _ (sxt_mem_reachStep hg hl pi)

theorem sxt_cent
    {s : S24}
    (hs : ∀ x ∈ m24E1l, s * x = x * s) : s ∈ m24E1l := by
  obtain ⟨-, -, h1, hmul, hsq, hcomm, -⟩ := m24_e1_check
  have hss : s * s = 1 := by
    refine Subtype.ext (Equiv.ext fun x => ?_)
    have key : ∀ k ∈ m24E1l, (k : Equiv.Perm (Fin 24)) ((s : Equiv.Perm (Fin 24)) x) =
        (s : Equiv.Perm (Fin 24)) ((k : Equiv.Perm (Fin 24)) x) := fun k hk => by
      have := congrArg (fun p : S24 => (p : Equiv.Perm (Fin 24)) x) (hs k hk)
      simpa using this.symm
    obtain ⟨f, hf, hfx⟩ := Certificates.certificate24841.1 x
      ((s : Equiv.Perm (Fin 24)) x) fun k hk hkx => by rw [key k hk, hkx]
    have hff : (f : Equiv.Perm (Fin 24)) ((f : Equiv.Perm (Fin 24)) x) = x := by
      simpa using congrArg (fun p : S24 => (p : Equiv.Perm (Fin 24)) x) (hsq f hf)
    show (s : Equiv.Perm (Fin 24)) ((s : Equiv.Perm (Fin 24)) x) = x
    calc (s : Equiv.Perm (Fin 24)) ((s : Equiv.Perm (Fin 24)) x)
        = (s : Equiv.Perm (Fin 24)) ((f : Equiv.Perm (Fin 24)) x) := by rw [hfx]
      _ = (f : Equiv.Perm (Fin 24)) ((s : Equiv.Perm (Fin 24)) x) := (key f hf).symm
      _ = (f : Equiv.Perm (Fin 24)) ((f : Equiv.Perm (Fin 24)) x) := by rw [hfx]
      _ = x := hff
  by_contra hns
  set l2 : List S24 := m24E1l ++ m24E1l.map (· * s) with hl2
  have h12 : (1 : S24) ∈ l2 := List.mem_append_left _ h1
  have hss' : ∀ u ∈ m24E1l, ∀ v ∈ m24E1l, u * s * (v * s) = u * v := by
    intro u hu v hv
    calc u * s * (v * s) = u * (s * v) * s := by group
      _ = u * (v * s) * s := by rw [hs v hv]
      _ = u * v * (s * s) := by group
      _ = u * v := by rw [hss, mul_one]
  have hmul2 : ∀ x ∈ l2, ∀ y ∈ l2, x * y ∈ l2 := by
    intro x hx y hy
    simp only [hl2, List.mem_append, List.mem_map] at hx hy ⊢
    rcases hx with hx | ⟨u, hu, rfl⟩ <;> rcases hy with hy | ⟨v, hv, rfl⟩
    · exact Or.inl (hmul x hx y hy)
    · exact Or.inr ⟨x * v, hmul x hx v hv, by rw [mul_assoc]⟩
    · refine Or.inr ⟨u * y, hmul u hu y hy, ?_⟩
      calc u * y * s = u * (y * s) := by rw [mul_assoc]
        _ = u * (s * y) := by rw [hs y hy]
        _ = u * s * y := by rw [mul_assoc]
    · exact Or.inl (by rw [hss' u hu v hv]; exact hmul u hu v hv)
  obtain ⟨B, hB⟩ := exists_subgroup_of_list l2 h12 hmul2
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    rw [hB] at hx hy
    simp only [hl2, List.mem_append, List.mem_map] at hx hy
    rcases hx with hx | ⟨u, hu, rfl⟩ <;> rcases hy with hy | ⟨v, hv, rfl⟩
    · exact hcomm x hx y hy
    · calc x * (v * s) = x * v * s := by rw [mul_assoc]
        _ = v * x * s := by rw [hcomm x hx v hv]
        _ = v * (x * s) := by rw [mul_assoc]
        _ = v * (s * x) := by rw [hs x hx]
        _ = v * s * x := by rw [mul_assoc]
    · calc u * s * y = u * (s * y) := by rw [mul_assoc]
        _ = u * (y * s) := by rw [hs y hy]
        _ = u * y * s := by rw [mul_assoc]
        _ = y * u * s := by rw [hcomm u hu y hy]
        _ = y * (u * s) := by rw [mul_assoc]
    · calc u * s * (v * s) = u * v := hss' u hu v hv
        _ = v * u := hcomm u hu v hv
        _ = v * s * (u * s) := (hss' v hv u hu).symm
  have hBsq : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    rw [hB] at hx
    simp only [hl2, List.mem_append, List.mem_map] at hx
    rcases hx with hx | ⟨u, hu, rfl⟩
    · exact hsq x hx
    · rw [hss' u hu u hu]
      exact hsq u hu
  have hcardB := m24_rank_le B hBcomm hBsq
  have hle : M24E1 ≤ B := fun x hx => by
    rw [hB]
    exact List.mem_append_left _ ((mem_M24E1 x).1 hx)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [card_M24E1]; simpa using hcardB)
  apply hns
  have hsB : s ∈ B := by
    rw [hB]
    exact List.mem_append_right _ (List.mem_map.2 ⟨1, h1, one_mul s⟩)
  rw [← heq] at hsB
  exact (mem_M24E1 s).1 hsB

end CFSG.EvenSporadicStandard.M24Std
