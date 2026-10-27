module

public import CFSG.LieType.Chevalley.C2E6FourthResiduePanels
public import CFSG.LieType.Chevalley.C2E6FourthResidueOpposite

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FourthResidue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Chevalley.CosetBuilding

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem _root_.CFSG.LieType.Chevalley.C2E6Std.standard_fourth_residue_orthogonal_minus_eight_flags :
    (∀ w : Fin 4 ⊕ Fin 4 → K, w ∈ Set.range embed ↔
      (∀ i : Fin 3, w (.inl i.castSucc) ∈ Set.range (algebraMap (ZMod 2) K) ∧
        w (.inr i.castSucc) ∈ Set.range (algebraMap (ZMod 2) K)) ∧
      w (.inr (Fin.last 3)) = w (.inl (Fin.last 3)) ^ 2) ∧
    (∀ c : Fin 3 ⊕ Fin 3, embed (hypVec (ZMod 2) (Fin 2 → ZMod 2) c) =
      Pi.single (Sum.map Fin.castSucc Fin.castSucc c) 1) ∧
    embed (tVec 0) = Pi.single (.inl (Fin.last 3)) 1 + Pi.single (.inr (Fin.last 3)) 1 ∧
    embed (tVec 1) =
      ω • Pi.single (.inl (Fin.last 3)) 1 + ω ^ 2 • Pi.single (.inr (Fin.last 3)) 1 ∧
    (∀ v : V0, embed v = ∑ c, v.1 c • embed (hypVec (ZMod 2) (Fin 2 → ZMod 2) c) +
      v.2 0 • embed (tVec 0) + v.2 1 • embed (tVec 1)) ∧
    Function.Injective embed ∧ Submodule.span K (Set.range embed) = ⊤ ∧
    (∀ v : V0, Qminus v =
      ∑ i, v.1 (.inl i) * v.1 (.inr i) + (v.2 0 ^ 2 + v.2 0 * v.2 1 + v.2 1 ^ 2)) ∧
    (∀ v : V0, quadPlus 4 K (embed v) = algebraMap (ZMod 2) K (Qminus v)) ∧
    stdLevi fourthJ = groupD ⊓ stdFixedGroup ∧
    (∀ (l : stdLevi fourthJ) (v : V0),
      embed (rhoMinus l v) = psiD ⟨l, stdLevi_fourthJ_le_groupD l.2⟩ (embed v)) ∧
    Function.Injective rhoMinus ∧ rhoMinus.range = orthElementaryGroup Qminus ∧
    ⁅TauCeti.QuadraticMap.orthogonalGroup Qminus, TauCeti.QuadraticMap.orthogonalGroup Qminus⁆ =
      orthElementaryGroup Qminus ∧
    (∀ k : Fin 3, baseFlag k = Submodule.span (ZMod 2)
      ((fun j : Fin 3 => hypVec (ZMod 2) (Fin 2 → ZMod 2) (.inl j)) '' {j | j ≤ k})) ∧
    (∀ (k : ℕ) (v : V0), k ≤ 3 →
      (embed v ∈ flag 4 K k ↔ v ∈ tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k)) ∧
    (∀ l : stdLevi fourthJ, (l : ModGL Tag.E6 K) ∈ stdLeviBorel fourthJ ↔
      ∀ k : Fin 3, (baseFlag k).map (rhoMinus l : V0 →ₗ[ZMod 2] V0) = baseFlag k) ∧
    (∀ W : Fin 3 → Submodule (ZMod 2) V0, W ∈ singularFlags Qminus 3 ↔
      (∀ i, Module.finrank (ZMod 2) (W i) = i + 1) ∧ Monotone W ∧
        ∀ i, ∀ x ∈ W i, Qminus x = 0) ∧
    (residueFlag (QuotientGroup.mk 1) : Fin 3 → Submodule (ZMod 2) V0) = baseFlag ∧
    (∀ (p : nativeParabolic fourthJ) (x : ParabolicCosets fourthJ) (k : Fin 3),
      (residueFlag (p • x) : Fin 3 → Submodule (ZMod 2) V0) k =
        ((residueFlag x : Fin 3 → Submodule (ZMod 2) V0) k).map
          (rhoMinus (leviProj two_mem_fourthJ p) : V0 →ₗ[ZMod 2] V0)) ∧
    (∀ (d : Fin 3) (x y : nativeParabolic fourthJ),
      ((x⁻¹ * y : nativeParabolic fourthJ) : ModGL Tag.E6 K) ∈ nativeParabolic {d.castSucc} ↔
        ∀ k, k ≠ d → (residueFlag (QuotientGroup.mk x) : Fin 3 → Submodule (ZMod 2) V0) k =
          (residueFlag (QuotientGroup.mk y) : Fin 3 → Submodule (ZMod 2) V0) k) ∧
    (∀ p : nativeParabolic fourthJ,
      (∀ x : ParabolicCosets fourthJ, p • x = x) ↔ (p : ModGL Tag.E6 K) ∈ stdRadical fourthJ) ∧
    (∀ k : Fin 3, (residueFlag (QuotientGroup.mk ⟨_, canonicalRep_longest_mem⟩) :
        Fin 3 → Submodule (ZMod 2) V0) k = Submodule.span (ZMod 2)
          ((fun j : Fin 3 => hypVec (ZMod 2) (Fin 2 → ZMod 2) (.inr j)) '' {j | j ≤ k})) ∧
    Function.Injective (chamberOf fourthJ) ∧
    Set.range (chamberOf fourthJ) =
      residue nativeCoxeterSystem stdDistance fourthJ ((1 : stdGroup) : stdChamber) ∧
    Nat.card (ParabolicCosets fourthJ) = 16065 ∧
    Nat.card (stdLeviBorel fourthJ) = 3 * 2 ^ 12 ∧
    Nat.card (stdLevi fourthJ) = 197406720 ∧
    Nat.card (orthElementaryGroup Qminus) = 197406720 ∧
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qminus) = 394813440 ∧
    (∀ (w : Fin 4 ⊕ Fin 4 → K) (c : Fin 4 ⊕ Fin 4), frob8 w c = w c ^ 2) ∧
    (∀ v : V0, frob8 (embed v) = embed (sMinus v)) ∧
    sMinus ∈ TauCeti.QuadraticMap.orthogonalGroup Qminus ∧
    (∀ c : Fin 3 ⊕ Fin 3,
      sMinus (hypVec (ZMod 2) (Fin 2 → ZMod 2) c) = hypVec (ZMod 2) (Fin 2 → ZMod 2) c) ∧
    sMinus (tVec 0) = tVec 0 ∧ sMinus (tVec 1) = tVec 0 + tVec 1 ∧
    (∀ l : stdLevi fourthJ,
      rhoMinus ⟨betaGL l, betaGL_mem_stdLevi l.2⟩ = sMinus * rhoMinus l * sMinus) ∧
    (∀ (p : nativeParabolic fourthJ) (k : Fin 3),
      (residueFlag (QuotientGroup.mk ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩) :
          Fin 3 → Submodule (ZMod 2) V0) k =
        ((residueFlag (QuotientGroup.mk p) : Fin 3 → Submodule (ZMod 2) V0) k).map
          (sMinus : V0 →ₗ[ZMod 2] V0)) ∧
    sMinus ∉ orthElementaryGroup Qminus ∧
    elemO.Normal ∧ elemO.IsComplement' (Subgroup.zpowers sO) ∧ orderOf sO = 2 ∧
    (∀ x, semidirectEquiv x = x.left * x.right) :=
  ⟨mem_range_embed_iff', embed_hypVec, embed_tVec_zero, embed_tVec_one, embed_eq_sum,
    embed_injective, span_range_embed, Qminus_apply, quadPlus_embed, stdLevi_fourthJ,
    embed_rhoMinus, rhoMinus_injective, range_rhoMinus, commutator_orthogonalGroup_Qminus,
    baseFlag_eq_span, fun _ v hk => embed_mem_flag_iff hk v, mem_stdLeviBorel_iff_baseFlag,
    fun _ => Iff.rfl, residueFlag_one, residueFlag_smul_apply,
    mem_nativeParabolic_singleton_iff, smul_eq_self_iff, residueFlag_longest,
    chamberOf_injective fourthJ, range_chamberOf fourthJ, card_parabolicCosets_fourthJ,
    card_stdLeviBorel_fourthJ, card_stdLevi_fourthJ, card_elementaryGroup_Qminus,
    card_orthogonalGroup_Qminus, fun _ _ => rfl, frob8_embed, sMinus_mem_orthogonalGroup,
    sMinus_hypVec, sMinus_tVec_zero, sMinus_tVec_one, rhoMinus_betaGL, residueFlag_betaGL,
    sMinus_not_mem_elementaryGroup, inferInstance, isComplement'_elemO, orderOf_sO,
    semidirectEquiv_apply⟩

end CFSG.LieType.Chevalley.C2E6Std.FourthResidue
