module

public import CFSG.Certificates.Kernel.PermCent.AllPermsCSound
public import CFSG.GH74.GLS.C3.Prop121.Card7F1

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7.FF

theorem decide_units_eq (u v : ℤˣ) : decide (u = v) = (decide (u = -1) == decide (v = -1)) := by
  rcases Int.units_eq_one_or u with h | h <;> rcases Int.units_eq_one_or v with h' | h' <;>
    simp [h, h']

theorem flatMap_congr' {α β : Type*} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem DL_eq : DL = DLP.map fun y => ev y.1 := by
  rw [DL, allPerms_eq 4 inferInstance, List.filter_map, DLP]
  exact congrArg _ (List.filter_congr fun x _ => decide_comm_ev x.1 x4)

theorem F7AL_eq : F7AL = F7C.map fun a => (ev a.1, ev a.2) := by
  unfold F7AL F7C
  rw [forcePL_eq, forcePL_eq, allPerms_eq 7 inferInstance, List.flatMap_map, List.map_flatMap]
  apply flatMap_congr'
  intro x hx
  dsimp only
  rw [DL_eq, List.filter_map, List.map_map, List.map_map]
  congr 1
  apply List.filter_congr
  intro y hy
  have hy' : y ∈ allPermsP 4 inferInstance := (List.mem_filter.1 hy).1
  simp only [Function.comp_apply]
  rw [decide_units_eq, ← par_of_mem_allPermsP hx, ← par_of_mem_allPermsP hy']

theorem F7L_eq : F7L.map Subtype.val = F7C.map fun a => (ev a.1, ev a.2) := by
  rw [← F7AL_eq]
  unfold F7L
  simp [List.map_pmap]
  first
    | exact List.attach_map_subtype_val _
    | exact List.attach_map_val _
    | simp

end CFSG.Certificates.Kernel.PkCV

end
