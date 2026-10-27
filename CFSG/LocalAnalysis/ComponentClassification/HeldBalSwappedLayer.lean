module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDG

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement

theorem gsFixedLayer_eq_of_isPComponent_swapped {Q : Type} [Group Q] [Finite Q]
    {A B K : Subgroup Q} {α : Q} (hα : α * α = 1) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (hαB : ∀ y ∈ B, α * y * α⁻¹ ∈ A)
    (hAq : IsQuasisimple ↥A) (hK0 : K ≠ ⊥)
    (hKC : K ≤ (A ⊔ B) ⊓ centralizer ({α} : Set Q))
    (hKp : IsPComponent 2 (K.subgroupOf ((A ⊔ B) ⊓ centralizer ({α} : Set Q)))) :
    gsFixedLayer (A ⊔ B) α = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup Q := (A ⊔ B) ⊓ centralizer ({α} : Set Q) with hC
  set R : Subgroup Q := (HeDQ.delta hAB hαA).range with hR
  set T : Subgroup Q := gsFixedLayer (A ⊔ B) α with hT
  have hKT : K ≤ T := by
    have h1 : (K.subgroupOf C).map C.subtype ≤ (pLayer ↥C 2).map C.subtype :=
      Subgroup.map_mono (le_sSup hKp)
    rw [Subgroup.map_subgroupOf_eq_of_le hKC, hC] at h1
    rw [hT, gsFixedLayer]
    exact h1
  have hTne : T ≠ ⊥ := fun h => hK0 (le_bot_iff.mp (hKT.trans (le_of_eq h)))
  have hTR : T = R := HeDG.gsFixedLayer_eq_range hα hAB hαA hαB hAq hTne
  have hKR : K ≤ R := hTR ▸ hKT
  have hRq : IsQuasisimple ↥R := HeDG.isQuasisimple_range hAB hαA hAq
  have hRC : R ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact HeDG.delta_mem hα hAB hαA x
  have hKsC : (K.subgroupOf C).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 (K.subgroupOf C)).1
      hKp).1
  have hKperf : Group.IsPerfect ↥(K.subgroupOf C) :=
    CatalogueBHeldSmallCore.pComponent_perfect 2 (K.subgroupOf C) hKp
  have hmap : ((K.subgroupOf C).subgroupOf (R.subgroupOf C)).map
      (Subgroup.subgroupOfEquivOfLe hRC).toMonoidHom = K.subgroupOf R := by
    ext z
    constructor
    · rintro ⟨y, hy, hyz⟩
      rw [← hyz]
      exact hy
    · intro hz
      exact ⟨⟨⟨(z : Q), hRC z.2⟩, z.2⟩, hz, rfl⟩
  have hKsR : (K.subgroupOf R).IsSubnormal := by
    rw [← hmap]
    exact (hKsC.subgroupOf).map (Subgroup.subgroupOfEquivOfLe hRC).surjective
  have htop : IsComponent (⊤ : Subgroup ↥R) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hRq, Subgroup.IsSubnormal.top⟩
  rcases LocalCores.component_subnormal_subgroup htop hKsR with hle | hcomm
  ·
    have hRK : R ≤ K := by
      intro x hx
      have h := hle (Subgroup.mem_top (⟨x, hx⟩ : ↥R))
      rwa [Subgroup.mem_subgroupOf] at h
    have hKR' : K = R := le_antisymm hKR hRK
    rw [hTR, hKR']
  ·
    exfalso
    have hcommR : ∀ a b : ↥(K.subgroupOf R), a * b = b * a := by
      intro a b
      apply Subtype.ext
      have hmem : ⁅(a : ↥R), (b : ↥R)⁆ ∈ (⊥ : Subgroup ↥R) := by
        rw [← hcomm]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top (a : ↥R)) b.2
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
    have e : ↥(K.subgroupOf C) ≃* ↥(K.subgroupOf R) :=
      (Subgroup.subgroupOfEquivOfLe hKC).trans (Subgroup.subgroupOfEquivOfLe hKR).symm
    have hcommC : ∀ a b : ↥(K.subgroupOf C), a * b = b * a := by
      intro a b
      apply e.injective
      rw [map_mul, map_mul]
      exact hcommR (e a) (e b)
    haveI : IsMulCommutative ↥(K.subgroupOf C) := IsMulCommutative.of_comm hcommC
    haveI : Group.IsPerfect ↥(K.subgroupOf C) := hKperf
    have hKbot : K ≤ ⊥ := by
      intro x hx
      have h1 : (⟨⟨x, hKC hx⟩, hx⟩ : ↥(K.subgroupOf C)) = 1 := Subsingleton.elim _ _
      have h2 := congrArg Subtype.val h1
      have h3 := congrArg Subtype.val h2
      simpa using h3
    exact hK0 (le_bot_iff.mp hKbot)

end CFSG.ComponentClassification.GrSLit
