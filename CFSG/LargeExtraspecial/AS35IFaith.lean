module

public import CFSG.LinearAlgebra.SL2MinimalFaithful
public import CFSG.LargeExtraspecial.AS35IOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.Asc22

open Subgroup Asc77

variable {G : Type} [Group G]

@[expose] noncomputable def conjOnV (N : Subgroup G) (z : G) : ↥N →* MulAut ↥(genV N z) where
  toFun n :=
    { toFun := fun v => ⟨n * v * (n : G)⁻¹, Hyp.conj_mem_genV n.2 v.2⟩
      invFun := fun v => ⟨(n : G)⁻¹ * v * n, by
        simpa using Hyp.conj_mem_genV (N.inv_mem n.2) v.2⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun v w => Subtype.ext (by
        change (n : G) * ((v : G) * w) * (n : G)⁻¹ = (n * v * (n : G)⁻¹) * (n * w * (n : G)⁻¹)
        group) }
  map_one' := by
    ext v
    simp
  map_mul' := fun m n => by
    ext v
    change (m * n : G) * v * (m * n : G)⁻¹ = m * (n * v * (n : G)⁻¹) * (m : G)⁻¹
    group

theorem conjOnV_apply {N : Subgroup G} {z : G} (n : N) (v : genV N z) :
    ((conjOnV N z n v : genV N z) : G) = n * v * (n : G)⁻¹ := rfl

variable {N U P : Subgroup G} {z : G}

namespace Hyp

variable (h : Hyp N U P z)
include h

theorem exists_faithful [Finite G] : ∃ (W : Type) (_ : Group W) (_ : Finite W)
    (ρ : Gbar N z →* MulAut W), Function.Injective ρ ∧
      Nat.card W * Nat.card (Asc77.centerIn z N) = Nat.card (genV N z) := by
  have := h.isMulComm_V
  set C' : Subgroup (genV N z) := (Asc77.centerIn z N).subgroupOf (genV N z) with hC'def
  have hCfix : ∀ (n : N) (c : genV N z), c ∈ C' → conjOnV N z n c = c := by
    intro n c hc
    rw [hC'def, mem_subgroupOf] at hc
    apply Subtype.ext
    rw [conjOnV_apply]
    have h1 := mem_centralizer_iff.1 (mem_inf.1 hc).2 n n.2
    calc (n : G) * c * (n : G)⁻¹ = c * n * (n : G)⁻¹ := by rw [h1]
      _ = c := by group
  have hmap : ∀ n, C'.map (conjOnV N z n : genV N z →* genV N z) = C' := by
    intro n
    ext c
    constructor
    · rintro ⟨d, hd, rfl⟩
      change conjOnV N z n d ∈ C'
      rw [hCfix n d hd]
      exact hd
    · intro hc
      exact ⟨c, hc, hCfix n c hc⟩
  set ρ' := CFSG.SL2MinimalFaithful.quotientAction (conjOnV N z) C' hmap with hρ'
  have hker : kerK N z ≤ ρ'.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext x
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [hρ', CFSG.SL2MinimalFaithful.quotientAction_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [conjOnV_apply]
      have h1 := mem_centralizer_iff.1 (mem_inf.1 (mem_kerK.1 hn)).2 v v.2
      calc (n : G) * v * (n : G)⁻¹ = v * n * (n : G)⁻¹ := by rw [h1]
        _ = v := by group
  let ρ : Gbar N z →* MulAut (genV N z ⧸ C') := QuotientGroup.lift (kerK N z) ρ' hker
  refine ⟨genV N z ⧸ C', inferInstance, inferInstance, ρ, ?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff]
    apply h.o2 inferInstance
    intro x
    obtain ⟨n, hn⟩ := piK_surjective (N := N) (z := z) (x : Gbar N z)
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← hn, ← map_pow, piK_eq_one]
    have hx := MonoidHom.mem_ker.1 x.2
    rw [← hn] at hx
    change ρ' n = 1 at hx
    refine mem_inf.2 ⟨(n ^ 2).2, mem_centralizer_iff.2 fun v hv => ?_⟩
    have hv' := congrArg (fun φ : MulAut (genV N z ⧸ C') => φ ((⟨v, hv⟩ : genV N z) :
      genV N z ⧸ C')) hx
    simp only [hρ', CFSG.SL2MinimalFaithful.quotientAction_mk, MulAut.one_apply] at hv'
    have hc := QuotientGroup.eq.1 hv'
    rw [hC'def, mem_subgroupOf] at hc
    have hc' : ((conjOnV N z n ⟨v, hv⟩ : genV N z) : G)⁻¹ * v ∈ Asc77.centerIn z N := by
      simpa using hc
    set c : G := ((conjOnV N z n ⟨v, hv⟩ : genV N z) : G)⁻¹ * v with hcdef
    have hcV : c ∈ genV N z := (mem_inf.1 hc').1
    have hcc : c * c = 1 := h.mul_self_V hcV
    have hcn := mem_centralizer_iff.1 (mem_inf.1 hc').2 n n.2
    have hnv : (n : G) * v * (n : G)⁻¹ = v * c⁻¹ := by
      rw [hcdef, conjOnV_apply]
      group
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
    have hnc : (n : G) * c⁻¹ * (n : G)⁻¹ = c⁻¹ := by
      rw [hcinv]
      calc (n : G) * c * (n : G)⁻¹ = c * n * (n : G)⁻¹ := by rw [hcn]
        _ = c := by group
    have hsq : ((n ^ 2 : N) : G) * v * ((n ^ 2 : N) : G)⁻¹ = v := by
      calc ((n ^ 2 : N) : G) * v * ((n ^ 2 : N) : G)⁻¹
          = (n : G) * ((n : G) * v * (n : G)⁻¹) * (n : G)⁻¹ := by simp [pow_two, mul_assoc]
        _ = (n : G) * (v * c⁻¹) * (n : G)⁻¹ := by rw [hnv]
        _ = ((n : G) * v * (n : G)⁻¹) * ((n : G) * c⁻¹ * (n : G)⁻¹) := by group
        _ = v * c⁻¹ * c⁻¹ := by rw [hnv, hnc]
        _ = v := by rw [hcinv, mul_assoc, hcc, mul_one]
    calc v * ((n ^ 2 : N) : G) = ((n ^ 2 : N) : G) * v * ((n ^ 2 : N) : G)⁻¹ *
          ((n ^ 2 : N) : G) := by rw [hsq]
      _ = ((n ^ 2 : N) : G) * v := by group
  · rw [card_eq_card_quotient_mul_card_subgroup C']
    congr 1
    exact (Nat.card_congr (subgroupOfEquivOfLe (inf_le_left :
      Asc77.centerIn z N ≤ genV N z)).toEquiv).symm

end Hyp

end CFSG.LargeExtraspecial.Asc22
