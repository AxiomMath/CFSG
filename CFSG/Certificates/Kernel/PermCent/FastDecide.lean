module

public import CFSG.Certificates.Kernel.PermCent.AllPermsCSound

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Prop121

instance fdSmall5 : Small 5 := ⟨by decide⟩
instance fdSmall6 : Small 6 := ⟨by decide⟩
instance fdSmall7 : Small 7 := ⟨by decide⟩

theorem mem_allPerms_fd : ∀ (m : ℕ) (s : Perm (Fin m)), s ∈ allPerms m
  | 0, s => by simp [allPerms, Subsingleton.elim s 1]
  | m + 1, s => by
      unfold allPerms
      simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
      exact ⟨(Equiv.Perm.decomposeFin s).1, (Equiv.Perm.decomposeFin s).2,
        mem_allPerms_fd m _, Equiv.Perm.decomposeFin.symm_apply_apply s⟩

theorem exists_mem_allPermsP {m : ℕ} (hs : Small m) (σ : Perm (Fin m)) :
    ∃ x ∈ allPermsP m hs, ev x.1 = σ := by
  have h := mem_allPerms_fd m σ
  rw [@allPerms_eq m hs, List.mem_map] at h
  exact h

theorem forall_perm_iff_allPermsP {m : ℕ} (hs : Small m) (P : Perm (Fin m) → Prop) :
    (∀ x ∈ allPermsP m hs, P (ev x.1)) ↔ ∀ σ, P σ :=
  ⟨fun h σ => by
    obtain ⟨x, hx, rfl⟩ := exists_mem_allPermsP hs σ
    exact h x hx, fun h x _ => h _⟩

theorem exists_perm_iff_allPermsP {m : ℕ} (hs : Small m) (P : Perm (Fin m) → Prop) :
    (∃ x ∈ allPermsP m hs, P (ev x.1)) ↔ ∃ σ, P σ :=
  ⟨fun ⟨_, _, h⟩ => ⟨_, h⟩, fun ⟨σ, h⟩ => by
    obtain ⟨x, hx, rfl⟩ := exists_mem_allPermsP hs σ
    exact ⟨x, hx, h⟩⟩

@[expose] def permBEq {n : ℕ} (a b : Perm (Fin n)) : Bool :=
  (List.finRange n).all fun i => a i == b i

theorem permBEq_iff {n : ℕ} (a b : Perm (Fin n)) : permBEq a b = true ↔ a = b := by
  simp only [permBEq, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  exact ⟨fun h => Equiv.ext h, fun h _ => by rw [h]⟩

namespace FastDecide

scoped instance (priority := 20000) decEqPerm {n : ℕ} : DecidableEq (Perm (Fin n)) :=
  fun a b => decidable_of_iff (permBEq a b = true) (permBEq_iff a b)

noncomputable scoped instance (priority := 20000) decForallPerm {m : ℕ} [hs : Small m]
    (P : Perm (Fin m) → Prop) [DecidablePred P] : Decidable (∀ σ, P σ) :=
  @decidable_of_iff _ _ (forall_perm_iff_allPermsP hs P) (List.decidableBAll _ _)

noncomputable scoped instance (priority := 20000) decExistsPerm {m : ℕ} [hs : Small m]
    (P : Perm (Fin m) → Prop) [DecidablePred P] : Decidable (∃ σ, P σ) :=
  @decidable_of_iff _ _ (exists_perm_iff_allPermsP hs P) (List.decidableBEx _ _)

scoped instance (priority := 20001) decBAllList {α : Type*} (p : α → Prop) [DecidablePred p]
    (l : List α) : Decidable (∀ x, x ∈ l → p x) :=
  List.decidableBAll p l

scoped instance (priority := 20001) decBExList {α : Type*} (p : α → Prop) [DecidablePred p]
    (l : List α) : Decidable (∃ x, x ∈ l ∧ p x) :=
  List.decidableBEx p l

end FastDecide

end CFSG.Certificates.Kernel.PkCV

end
