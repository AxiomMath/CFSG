module

public import CFSG.GH74.KGroups.Generic
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.GH74.KGroups

@[expose] def catTab (n m : ℕ) (a b : Tab) : Tab :=
  Array.ofFn (n := n + m) fun i => if i.val < n then a[i.val]! else b[i.val - n]! + n

theorem blockHom_castAdd {n m : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (x : Fin n) : blockHom n m (σ, τ) (Fin.castAdd m x) = Fin.castAdd m (σ x) := by
  simp [blockHom, Equiv.permCongr_apply]

theorem blockHom_natAdd {n m : ℕ} (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (y : Fin m) : blockHom n m (σ, τ) (Fin.natAdd n y) = Fin.natAdd n (τ y) := by
  simp [blockHom, Equiv.permCongr_apply]

theorem tabRep_catTab {n m : ℕ} {a b : Tab} {σ : Equiv.Perm (Fin n)} {τ : Equiv.Perm (Fin m)}
    (ha : TabRep a σ) (hb : TabRep b τ) : TabRep (catTab n m a b) (blockHom n m (σ, τ)) := by
  refine ⟨Array.size_ofFn, fun i => ?_⟩
  rw [catTab, getElem!_pos _ _ (by simp), Array.getElem_ofFn]
  by_cases hi : i.val < n
  · obtain ⟨x, rfl⟩ : ∃ x : Fin n, Fin.castAdd m x = i := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    simp only [Fin.val_castAdd, x.isLt, ↓reduceIte, blockHom_castAdd]
    exact ha.apply x
  · obtain ⟨y, rfl⟩ : ∃ y : Fin m, Fin.natAdd n y = i :=
      ⟨⟨i.val - n, by omega⟩, Fin.ext (by simp only [Fin.val_natAdd]; omega)⟩
    simp only [Fin.val_natAdd, Nat.add_sub_cancel_left, show ¬ n + y.val < n by omega,
      ↓reduceIte, blockHom_natAdd]
    rw [hb.apply y, add_comm]

theorem nonempty_mulEquiv_of_graph {n m : ℕ} {P : Subgroup (Equiv.Perm (Fin n))}
    {Q : Subgroup (Equiv.Perm (Fin m))} {A : Set (Equiv.Perm (Fin n) × Equiv.Perm (Fin m))}
    (hP : Subgroup.closure (Prod.fst '' A) = P) (hQ : Subgroup.closure (Prod.snd '' A) = Q)
    (hcP : Nat.card (Subgroup.closure (blockHom n m '' A)) ≤ Nat.card P)
    (hcQ : Nat.card (Subgroup.closure (blockHom n m '' A)) ≤ Nat.card Q) : Nonempty (P ≃* Q) := by
  set Γ := Subgroup.closure A
  have hcard : Nat.card Γ = Nat.card (Subgroup.closure (blockHom n m '' A)) := by
    rw [← MonoidHom.map_closure, Subgroup.card_map_of_injective (blockHom_injective n m)]
  have hfst : Γ.map (MonoidHom.fst _ _) = P := by rw [MonoidHom.map_closure]; exact hP
  have hsnd : Γ.map (MonoidHom.snd _ _) = Q := by rw [MonoidHom.map_closure]; exact hQ
  let f : Γ →* P := ((MonoidHom.fst _ _).comp Γ.subtype).codRestrict P fun x => by
    rw [← hfst]
    exact ⟨x, x.2, rfl⟩
  let g : Γ →* Q := ((MonoidHom.snd _ _).comp Γ.subtype).codRestrict Q fun x => by
    rw [← hsnd]
    exact ⟨x, x.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hfst] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hsnd] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨(MulEquiv.ofBijective f (hf.bijective_of_nat_card_le (hcard.trans_le hcP))).symm.trans
    (MulEquiv.ofBijective g (hg.bijective_of_nat_card_le (hcard.trans_le hcQ)))⟩

end CFSG.ComponentClassification.GrSLit.HeldFix
