module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23GOCBasic
import CFSG.GroupTheory.ConjKerCenter

public section

namespace CFSG.GroupTheory.StronglyClosedTI

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC (OutCyc)

variable {L : Type} [Group L]

theorem card_map_outer_le_two (hOut : OutCyc L) {A : Subgroup (MulAut L)}
    (hA : ∀ a ∈ A, a * a = 1) : Nat.card (A.map (QuotientGroup.mk' (inner L))) ≤ 2 := by
  set B := A.map (QuotientGroup.mk' (inner L)) with hBdef
  have hB : ∀ b ∈ B, b * b = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hA a ha, map_one]
  have hB2 : IsPGroup 2 B := fun b => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hB b b.2)⟩
  haveI := hOut B hB2
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := B)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact Nat.le_of_dvd (by norm_num)
    (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact Subtype.ext (hB g g.2)))

theorem card_inf_inner_le (hZ : center L = ⊥) {k : ℕ}
    (hk : ∀ E : Subgroup L, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ k) {A : Subgroup (MulAut L)}
    (hA : ∀ a ∈ A, a * a = 1) : Nat.card (A ⊓ inner L : Subgroup (MulAut L)) ≤ k := by
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]
  set E := (A ⊓ inner L).comap (MulAut.conj : L →* MulAut L) with hEdef
  have hE2 : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    apply hinj
    rw [map_mul, map_one]
    exact hA _ (Subgroup.mem_comap.mp hx).1
  have hmap : E.map (MulAut.conj : L →* MulAut L) = A ⊓ inner L :=
    Subgroup.map_comap_eq_self inf_le_right
  calc Nat.card (A ⊓ inner L : Subgroup (MulAut L)) = Nat.card E := by
        rw [← hmap, Subgroup.card_map_of_injective hinj]
    _ ≤ k := hk E hE2

theorem card_le_two_mul_of_outCyc (hZ : center L = ⊥) (hOut : OutCyc L) {k : ℕ}
    (hk : ∀ E : Subgroup L, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ k) {A : Subgroup (MulAut L)}
    (hA : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 2 * k := by
  set π : MulAut L →* Outer L := QuotientGroup.mk' (inner L) with hπ
  set ψ := π.comp A.subtype with hψ
  have h1 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card A := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : Nat.card ψ.range ≤ 2 := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
    exact card_map_outer_le_two hOut hA
  have h3 : Nat.card ψ.ker = Nat.card (A ⊓ inner L : Subgroup (MulAut L)) := by
    refine Nat.card_congr ⟨fun x => ⟨x.1, x.1.2, ?_⟩, fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩, ?_, ?_⟩
    · have h := x.2
      change π ((x : A) : MulAut L) = 1 at h
      exact (QuotientGroup.eq_one_iff _).mp h
    · change π (x : MulAut L) = 1
      exact (QuotientGroup.eq_one_iff _).mpr x.2.2
    · intro x
      rfl
    · intro x
      rfl
  have h4 := card_inf_inner_le hZ hk hA
  rw [← h1, h3, mul_comm 2 k]
  exact Nat.mul_le_mul h4 h2

end CFSG.GroupTheory.StronglyClosedTI

end
