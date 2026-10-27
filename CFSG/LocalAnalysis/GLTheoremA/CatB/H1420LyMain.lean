module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420RedMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420MainA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem i1420RowA_of_branches {p z : ℕ} {s t₀ : TauCeti.SporadicName} (hp : p.Prime)
    (hL : ∀ (S : Type) [Group S] [Finite S] (idx : TauCeti.ValidLieTypeIndex),
      S ≃* (TauCeti.CFSGIndex.lie idx).Group → ∀ (β : MulAut S) (J : Subgroup S),
        I1420Core p z s β J → False)
    (hA : ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 5 ≤ n → S ≃* alternatingGroup (Fin n) →
      ∀ (β : MulAut S) (J : Subgroup S), I1420Core p z s β J → False)
    (hS : ∀ (S : Type) [Group S] [Finite S] (t : TauCeti.SporadicName),
      S ≃* (TauCeti.CFSGIndex.sporadic t).Group → ∀ (β : MulAut S) (J : Subgroup S),
        I1420Core p z s β J → t = t₀) :
    ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420ModelA p K I₀ D →
      S8.IsTypeWithCenter p I₀ (S8.sporIs s) z → catalogIs (PSimple p K) (S8.sporIs t₀) := by
  intro Q _ _ K I₀ D hM hT
  obtain ⟨β, J, hcore⟩ := exists_core_of_modelA hp hM hT
  obtain ⟨i, ⟨e⟩⟩ := hM.1.2.2.2.2.1
  cases i with
  | cyclic q hq =>
    obtain ⟨a, b, hab⟩ := hcore.2.1
    exact absurd (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)) hab
  | alternating n hn => exact (hA _ n hn e β J hcore).elim
  | lie idx => exact (hL _ idx e β J hcore).elim
  | sporadic t =>
    obtain rfl := hS _ t e β J hcore
    exact ⟨.sporadic _, rfl, ⟨e⟩⟩

theorem i1420LyA_of_branches
    (hL : ∀ (S : Type) [Group S] [Finite S] (idx : TauCeti.ValidLieTypeIndex),
      S ≃* (TauCeti.CFSGIndex.lie idx).Group → ∀ (β : MulAut S) (J : Subgroup S),
        I1420Core 3 3 .McL β J → False)
    (hA : ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 5 ≤ n → S ≃* alternatingGroup (Fin n) →
      ∀ (β : MulAut S) (J : Subgroup S), I1420Core 3 3 .McL β J → False)
    (hS : ∀ (S : Type) [Group S] [Finite S] (t : TauCeti.SporadicName),
      S ≃* (TauCeti.CFSGIndex.sporadic t).Group → ∀ (β : MulAut S) (J : Subgroup S),
        I1420Core 3 3 .McL β J → t = .Ly) :
    I1420LyA :=
  i1420RowA_of_branches Nat.prime_three hL hA hS

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
