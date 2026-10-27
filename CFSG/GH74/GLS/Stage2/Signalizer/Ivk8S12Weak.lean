module

public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3S
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier CFSG.Certificates Certificates.Odd87F3 Certificates.Ivk8Weak
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Spec

variable {n : ℕ}

@[expose] def subprodsP {G : Type*} [Group G] : List G → List G
  | [] => [1]
  | g :: gs => (subprodsP gs) ++ (subprodsP gs).map (g * ·)

theorem forall₂_map_comp {t : Table} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) {l : List Table}
    {l' : List (Equiv.Perm (Fin n))} (h : List.Forall₂ (Rep n) l l') :
    List.Forall₂ (Rep n) (l.map (compT n t)) (l'.map (g * ·)) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (Rep.compT ht hab) ih

theorem forall₂_subprods (hn : n < 2 ^ 32) {aT : List Table} {aP : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) aT aP) :
    List.Forall₂ (Rep n) (subprodsT n aT) (subprodsP aP) := by
  induction h with
  | nil => exact .cons (Rep.idT hn) .nil
  | cons hab _ ih => exact List.rel_append ih (forall₂_map_comp hab ih)

theorem mem_subprodsP {G : Type*} [Group G] {N : Subgroup G} {l : List G} (h : ∀ a ∈ l, a ∈ N) :
    ∀ x ∈ subprodsP l, x ∈ N := by
  induction l with
  | nil =>
    intro x hx
    simp only [subprodsP, List.mem_singleton] at hx
    exact hx ▸ N.one_mem
  | cons g gs ih =>
    intro x hx
    simp only [subprodsP, List.mem_append, List.mem_map] at hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) x hx
    · exact N.mul_mem (h g List.mem_cons_self)
        (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) y hy)

end Spec

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
