module

public import CFSG.LieType.Ree.ReeTorus
public import CFSG.LieType.Ree.RootBruhatEquivariance

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

omit [CharP K t.prime] in
theorem mem_nativeData_U_of_mem_posUnipotent
    {x : ModGL t.tag K}
    (hx : x ∈ posUnipotent t.tag K) :
    (⟨x, posUnipotent_le_adjointGroup hx⟩ : adjointGroup t.tag K) ∈ (nativeData t.tag K).U := by
  have h : (posUnipotent t.tag K).subgroupOf (adjointGroup t.tag K) ≤ (nativeData t.tag K).U := by
    rw [posUnipotent, subgroupOf_rootSpan]
    refine iSup₂_le fun α hα => ?_
    exact ((rootOperatorFamily t.tag).subgroupOf_rootSubgroup_eq K ⟨α, hα.1⟩).le.trans
      (RootGroupData.X_le_U (D := nativeData t.tag K) (α := ⟨α, hα.1⟩) hα.2)
  exact h (Subgroup.mem_subgroupOf.2 hx)

omit [Finite K] [CharP K t.prime] in
theorem coe_reeTorus_mem_torusGroup
    (j : Fin t.tag.rank) (u : Kˣ) :
    ((t.reeTorus a j u : adjointGroup t.tag K) : ModGL t.tag K) ∈ torusGroup t.tag K := by
  rw [reeTorus, Subgroup.coe_mul]
  exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

theorem coe_reeTorus_mem_reeFixedTorus
    (hK : Nat.card K = t.prime ^ (2 * a + 1))
    {j : Fin t.tag.rank} (hj : j ∈ t.longSet) (u : Kˣ) :
    ((t.reeTorus a j u : adjointGroup t.tag K) : ModGL t.tag K) ∈ t.reeFixedTorus K a := by
  refine Subgroup.mem_inf.2 ⟨coe_reeTorus_mem_torusGroup j u,
    mem_reeGamma.2 ⟨(t.reeTorus a j u).2, ?_⟩⟩
  rw [finiteReeAut_eq_reeAut]
  exact (mem_reeFixed t K a).1 (t.reeTorus_mem_reeFixed a hK hj u)

theorem eq_one_of_mem_posUnipotent_of_commute
    (ha : 1 ≤ a)
    (hK : Nat.card K = t.prime ^ (2 * a + 1)) {x : ModGL t.tag K}
    (hx : x ∈ posUnipotent t.tag K) (hc : ∀ h ∈ t.reeFixedTorus K a, h * x = x * h) :
    x = 1 := by
  obtain ⟨u₀, hu₀⟩ := exists_orderOf_eq_card_sub_one (K := K)
  have h1 := t.eq_one_of_mem_U_of_forall_reeTorus a ha hK hu₀
    (mem_nativeData_U_of_mem_posUnipotent hx) fun j hj => by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        hc _ (coe_reeTorus_mem_reeFixedTorus hK hj u₀), mul_inv_cancel_right]
  exact congrArg Subtype.val h1

theorem ree_positive_fixed_torus_centralizer
    (t : ReeTag) (a : ℕ) (ha : 1 ≤ a) (K : Type)
    [Field K] [Finite K] [CharP K t.prime] (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    posUnipotent t.tag K ⊓
        Subgroup.centralizer (t.reeFixedTorus K a : Set (ModGL t.tag K)) = ⊥ ∧
      t.reeFixedPosUnipotent K a ⊓
        Subgroup.centralizer (t.reeFixedTorus K a : Set (ModGL t.tag K)) = ⊥ := by
  have h : posUnipotent t.tag K ⊓
      Subgroup.centralizer (t.reeFixedTorus K a : Set (ModGL t.tag K)) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_bot.2 (eq_one_of_mem_posUnipotent_of_commute ha hK hxU
      fun h hh => Subgroup.mem_centralizer_iff.1 hxC h hh)
  exact ⟨h, eq_bot_iff.2 ((inf_le_inf_right _ inf_le_left).trans h.le)⟩

end ReeTag

end CFSG.LieType.Ree
