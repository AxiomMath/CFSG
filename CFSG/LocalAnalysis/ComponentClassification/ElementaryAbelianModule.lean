module

public import CFSG.LocalAnalysis.ComponentClassification.MinimalNormal

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ElementaryAbelianModule

abbrev moduleStructure {G : Type*} [CommGroup G]
    (prime : ℕ) (hpower : ∀ element : G, element ^ prime = 1) :
    Module (ZMod prime) (Additive G) :=
  AddCommGroup.zmodModule (n := prime) fun element => by
    change prime • Additive.ofMul (Additive.toMul element) = Additive.ofMul (1 : G)
    rw [← ofMul_pow, hpower]

@[expose] noncomputable def linearAutomorphism {G : Type*} [CommGroup G]
    (prime : ℕ) [Module (ZMod prime) (Additive G)] (automorphism : MulAut G) :
    Additive G ≃ₗ[ZMod prime] Additive G := by
  let additiveEquivalence := MulEquiv.toAdditive automorphism
  exact LinearEquiv.ofBijective
    (AddMonoidHom.toZModLinearMap prime additiveEquivalence.toAddMonoidHom)
      additiveEquivalence.bijective

theorem linearAutomorphism_apply {G : Type*} [CommGroup G]
    (prime : ℕ) [Module (ZMod prime) (Additive G)]
    (automorphism : MulAut G) (element : Additive G) :
    linearAutomorphism prime automorphism element =
      Additive.ofMul (automorphism (Additive.toMul element)) := rfl

@[expose] noncomputable def linearAction {G H : Type*} [Group G] [CommGroup H]
    (prime : ℕ) [Module (ZMod prime) (Additive H)] (action : G →* MulAut H) :
    G →* (Additive H ≃ₗ[ZMod prime] Additive H) := by
  refine
    { toFun := fun element => linearAutomorphism prime (action element)
      map_one' := ?_
      map_mul' := ?_ }
  · apply LinearEquiv.ext
    intro member
    rw [linearAutomorphism_apply, map_one]
    rfl
  · intro left right
    apply LinearEquiv.ext
    intro member
    rw [linearAutomorphism_apply, map_mul]
    rfl

theorem linearAction_apply {G H : Type*} [Group G] [CommGroup H]
    (prime : ℕ) [Module (ZMod prime) (Additive H)] (action : G →* MulAut H)
    (actor : G) (element : Additive H) :
    linearAction prime action actor element = Additive.ofMul ((action actor) (Additive.toMul element)) :=
  rfl

theorem linearAction_kernel {G H : Type*} [Group G] [CommGroup H]
    (prime : ℕ) [Module (ZMod prime) (Additive H)] (action : G →* MulAut H) :
    (linearAction prime action).ker = action.ker := by
  ext actor
  change linearAction prime action actor = 1 ↔ action actor = 1
  constructor
  · intro hidentity
    apply MulEquiv.ext
    intro element
    have hvalue := congrArg (fun automorphism : Additive H ≃ₗ[ZMod prime] Additive H =>
      Additive.toMul (automorphism (Additive.ofMul element))) hidentity
    exact hvalue
  · intro hidentity
    apply LinearEquiv.ext
    intro element
    rw [linearAction_apply, hidentity]
    rfl

theorem card_eq_pow_finrank {G : Type*} [CommGroup G] [Finite G]
    (prime : ℕ) [Fact prime.Prime] [Module (ZMod prime) (Additive G)] :
    Nat.card G = prime ^ Module.finrank (ZMod prime) (Additive G) := by
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod prime) (V := Additive G)
  have hadditiveCard : Nat.card (Additive G) = Nat.card G :=
    (Nat.card_congr (Additive.ofMul : G ≃ Additive G)).symm
  rw [hadditiveCard] at hcard
  simpa using hcard

abbrev subgroupCommGroup {G : Type*} [Group G]
    (subgroup : Subgroup G) (hcommutative : IsMulCommutative subgroup) : CommGroup subgroup :=
  { subgroup.toGroup with mul_comm := isMulCommutative_iff.mp hcommutative }

theorem invariant_subspace_eq_bot_or_top {G H : Type*} [Group G] [CommGroup H]
    (prime : ℕ) [Module (ZMod prime) (Additive H)]
    (embedding : H →* G) (hinjective : Function.Injective embedding)
    (hminimal : MinimalNormal.Property embedding.range) (action : G →* MulAut H)
    (hconjugation : ∀ actor : G, ∀ member : H,
      embedding ((action actor) member) = actor * embedding member * actor⁻¹)
    (subspace : Submodule (ZMod prime) (Additive H))
    (hinvariant : ∀ actor : G, ∀ element ∈ subspace,
      linearAction prime action actor element ∈ subspace) :
      subspace = ⊥ ∨ subspace = ⊤ := by
  let localSubgroup : Subgroup H := AddSubgroup.toSubgroup' subspace.toAddSubgroup
  let ambientSubgroup := localSubgroup.map embedding
  have hambientNormal : ambientSubgroup.Normal := ⟨by
    intro member hmember actor
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
    change Additive.ofMul lift ∈ subspace at hlift
    have hfixed := hinvariant actor (Additive.ofMul lift) hlift
    exact Subgroup.mem_map.mpr ⟨(action actor) lift, hfixed, hconjugation actor lift⟩⟩
  by_cases hbot : ambientSubgroup = ⊥
  · left
    apply le_antisymm _ bot_le
    intro element hmem
    have hambient : embedding (Additive.toMul element) ∈ ambientSubgroup :=
      Subgroup.mem_map_of_mem embedding hmem
    rw [hbot] at hambient
    have hone : Additive.toMul element = 1 := hinjective
      ((Subgroup.mem_bot.mp hambient).trans embedding.map_one.symm)
    change element = 0
    exact congrArg Additive.ofMul hone
  · right
    have heq : embedding.range = ambientSubgroup := (minimal_iff.mp hminimal).2
      ⟨hambientNormal, hbot⟩ (Subgroup.map_le_range _ _)
    apply le_antisymm le_top
    intro element _
    have hambient : embedding (Additive.toMul element) ∈ ambientSubgroup :=
      heq ▸ (show embedding (Additive.toMul element) ∈ embedding.range from ⟨_, rfl⟩)
    obtain ⟨lift, hlift, hvalue⟩ := Subgroup.mem_map.mp hambient
    have helements : lift = Additive.toMul element := hinjective hvalue
    change Additive.ofMul lift ∈ subspace at hlift
    have htag : Additive.ofMul (Additive.toMul element) = element := rfl
    rw [helements, htag] at hlift
    exact hlift

end CFSG.ComponentClassification.ElementaryAbelianModule
