module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420CoreDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def I1420ModelA {Q : Type} [Group Q] [Finite Q] (p : ℕ) (K I₀ D : Subgroup Q) : Prop :=
  I1420Model p K I₀ D ∧ ∃ a ∈ D, a ≠ 1 ∧ K ≤ Subgroup.centralizer ({a} : Set Q)

@[expose] def I1420Red : Prop :=
  ∀ (p z : ℕ) (s : TauCeti.SporadicName), I1420Target p z s →
    ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420ModelA p K I₀ D →
      S8.IsTypeWithCenter p I₀ (S8.sporIs s) z →
        ∃ (β : MulAut (PSimple p K)) (J : Subgroup (PSimple p K)), I1420Core p z s β J

@[expose] def I1420FactA (p z : ℕ) (s : TauCeti.SporadicName) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420ModelA p K I₀ D →
    S8.IsTypeWithCenter p I₀ (S8.sporIs s) z → catalogIs (PSimple p K) (S8.sporIs .M)

@[expose] def I1420M3A : Prop := I1420FactA 3 3 .Fi24Prime

@[expose] def I1420M5A : Prop := I1420FactA 5 1 .HN

theorem i1420FactA_of_branches (hR : I1420Red) (hL : I1420Lie) (hA : I1420Alt)
    (hS : I1420Spor) {p z : ℕ} {s : TauCeti.SporadicName} (ht : I1420Target p z s) :
    I1420FactA p z s := by
  intro Q _ _ K I₀ D hM hT
  obtain ⟨β, J, hcore⟩ := hR p z s ht Q K I₀ D hM hT
  obtain ⟨i, ⟨e⟩⟩ := hM.1.2.2.2.2.1
  cases i with
  | cyclic q hq =>
    obtain ⟨a, b, hab⟩ := hcore.2.1
    exact absurd (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)) hab
  | alternating n hn => exact (hA p z s ht _ n hn e β J hcore).elim
  | lie idx => exact (hL p z s ht _ idx e β J hcore).elim
  | sporadic t =>
    obtain rfl := hS p z s ht _ t e β J hcore
    exact ⟨.sporadic .M, rfl, ⟨e⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
