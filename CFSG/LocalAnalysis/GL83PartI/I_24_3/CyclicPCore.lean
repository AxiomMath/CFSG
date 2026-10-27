module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Basic
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Cyclic

public section

namespace GL83.I243

open CFSG CFSG.Open Subgroup

theorem isCyclic_pCore_of_omega {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K : Subgroup X} (hq : IsQuasisimple K) {z : X} (hzp : orderOf z = p)
    (hΩ : ∀ c ∈ K, c ∈ Subgroup.centralizer (K : Set X) → c ^ p = 1 → c ∈ Subgroup.zpowers z) :
    IsCyclic ↥(CFSG.pCore p ↥K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hPc : CFSG.pCore p ↥K ≤ center ↥K := pCore_le_center hp hq
  haveI : IsMulCommutative (CFSG.pCore p ↥K) :=
    ⟨⟨fun a b => Subtype.ext (by
      have := Subgroup.mem_center_iff.mp (hPc b.2) (a : ↥K)
      exact this)⟩⟩
  letI : CommGroup (CFSG.pCore p ↥K) := IsMulCommutative.instCommGroup
  refine isCyclic_of_isPGroup_of_card_pow_le hp CFSG.pCore_isPGroup ?_
  have hcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzp]
  have hmem : ∀ x : {x : CFSG.pCore p ↥K // x ^ p = 1},
      (((x.1 : ↥K)) : X) ∈ Subgroup.zpowers z := by
    intro x
    refine hΩ _ (x.1 : ↥K).2 ?_ ?_
    · have := Subgroup.mem_center_iff.mp (hPc x.1.2)
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      exact congrArg Subtype.val (this ⟨h, hh⟩)
    · have h1 : ((x.1 : ↥K)) ^ p = 1 := congrArg Subtype.val x.2
      have := congrArg (fun y : ↥K => (y : X)) h1
      simpa using this
  have key : Nat.card {x : CFSG.pCore p ↥K // x ^ p = 1} ≤ Nat.card (Subgroup.zpowers z) :=
    Nat.card_le_card_of_injective
      (fun x : {x : CFSG.pCore p ↥K // x ^ p = 1} =>
        (⟨(((x.1 : ↥K)) : X), hmem x⟩ : Subgroup.zpowers z))
      (by
        intro a b hab
        simp only [Subtype.mk.injEq] at hab
        exact Subtype.ext (Subtype.ext (Subtype.ext hab)))
  rwa [hcard] at key

end GL83.I243
