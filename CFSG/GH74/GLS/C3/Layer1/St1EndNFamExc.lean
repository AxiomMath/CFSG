module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamGen
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Exc

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)


theorem outer_comm_of_ker_eq_inner {C Q : Type*} [Group C] [Group Q] [IsCyclic Q]
    (Θ : MulAut C →* Q) (hker : Θ.ker = inner C) : IsMulCommutative (Outer C) := by
  refine (QuotientGroup.lift (inner C) Θ hker.ge).isMulCommutative_of_isCyclic_of_ker_le_center ?_
  intro x hx
  rw [QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self, Subgroup.mem_bot] at hx
  rw [hx]
  exact Subgroup.one_mem _


theorem outer_comm_G2
    {T : Type} [Group T] {p f : ℕ} (hT : ChevalleyExceptionalModel T .G2 p f) (hp : Odd p) :
    IsMulCommutative (Outer T) := by
  obtain ⟨⟨hpp, hf, -⟩, hm⟩ := hT
  have hp2 : p ≠ 2 := fun h => by
    subst h
    exact absurd hp (by decide)
  have hm' : UntwistedChevalleyModel T .G2 (p ^ f) := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm'
  have hC : IsMulCommutative (Outer (adjointGroup .G2 K)) := by
    by_cases h3 : p = 3
    · subst h3
      have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
      have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
      have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := this
      obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
      exact outer_comm_of_ker_eq_inner Θ hker
    · have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hpp.pos f).ne')
      have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic hpp K hK).2
      obtain ⟨-, Θ, -, -, hker, -⟩ :=
        odd_F4_and_nonexceptional_G2_automorphism_normal_form hpp hp2 hf K hK .G2 (Or.inr ⟨rfl, h3⟩)
      exact outer_comm_of_ker_eq_inner Θ hker
  exact isMulCommutative_of_mulEquiv'
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e) hC


theorem outer_comm_D4
    {T : Type} [Group T] {p f : ℕ} (hT : ChevalleyExceptionalModel T .trialityD4 p f) (hp : Odd p) :
    IsMulCommutative (Outer T) := by
  obtain ⟨⟨hpp, hf, -⟩, hm⟩ := hT
  have hp2 : p ≠ 2 := fun h => by
    subst h
    exact absurd hp (by decide)
  have hm' : TwistedChevalleyModel T .D4 (p ^ f) := hm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hpp hf hm'
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
    odd_triality_exact_automorphism_normal_form hpp hp2 hf K hK σ hσ
  exact isMulCommutative_of_mulEquiv'
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e)
    (outer_comm_of_ker_eq_inner Θ hker)


theorem lem711_g2 :
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Lem711Empty (fun X _ => LieModel X .G2 0 p f) := by
  intro p f hp hp2 hf X _ _ L K x y h hM
  have hxL : x ∈ L := h.x_mem_L_of_outer_comm
    (outer_comm_G2 (IVK.chevalleyExceptionalModel_of_lieModel_G2 hM) (hp.odd_of_ne_two hp2))
  exact h.false_of_comp_mem_of_mem hxL fun y hy2 hy1 B hB =>
    IVK.GHInv.mem_of_isCompIn_G2 hp hp2 hM hf y
      (orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1) hB

theorem lem711_d4 :
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Lem711Empty (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro p f hp hp2 hf X _ _ L K x y h hM
  have hxL : x ∈ L := h.x_mem_L_of_outer_comm
    (outer_comm_D4 (IVK.chevalleyExceptionalModel_of_lieModel_D4 hM) (hp.odd_of_ne_two hp2))
  exact h.false_of_comp_mem_of_mem hxL fun y hy2 hy1 B hB =>
    IVK.GHInv.mem_of_isCompIn_D4 hp hp2 hM hf y
      (orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1) hB


end CFSG.GH74.GLS
