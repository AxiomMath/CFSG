module

public import CFSG.LieType.Chevalley.C2E6D4Twist

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin

@[expose] def psiDEquiv
    : groupD ≃* orthElementaryGroup (quadPlus 4 K) :=
  (MonoidHom.ofInjective psiD_injective).trans (MulEquiv.subgroupCongr range_psiD)

theorem coe_psiDEquiv
    (g : groupD) :
    (psiDEquiv g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = psiD g := rfl

theorem D4_natural_orthogonal_restriction_faithful :
    (∀ (g : groupD) (v : RootModule Tag.E6 K) (hv : v ∈ moduleD),
      psiD g (phiD ⟨v, hv⟩) =
        phiD ⟨((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v,
          mem_moduleD_of_mem_groupD g.2 v hv⟩) ∧
    (∀ v : Fin 4 ⊕ Fin 4 → K, quadPlus 4 K v = ∑ i, v (Sum.inl i) * v (Sum.inr i)) ∧
    Function.Injective psiD ∧ psiD.range = orthElementaryGroup (quadPlus 4 K) ∧
    (∃ e : groupD ≃* orthElementaryGroup (quadPlus 4 K), ∀ g,
      (e g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = psiD g) ∧
    (unipotentD.subgroupOf groupD).map psiD = unipotent 4 K ∧
    (torusD.subgroupOf groupD).map psiD = (torusElt 4 K).range ∧
    (∀ (a : Fin 4 → Kˣ) (v : Fin 4 ⊕ Fin 4 → K) (c : Fin 4 ⊕ Fin 4),
      torusElt 4 K a v c = ((Sum.elim a a⁻¹ c : Kˣ) : K) * v c) ∧
    (OrthogonalSplit.simpleRoot 4 0 = OrthogonalSplit.eps 4 0 - OrthogonalSplit.eps 4 1 ∧
      OrthogonalSplit.simpleRoot 4 1 = OrthogonalSplit.eps 4 1 - OrthogonalSplit.eps 4 2 ∧
      OrthogonalSplit.simpleRoot 4 2 = OrthogonalSplit.eps 4 2 - OrthogonalSplit.eps 4 3 ∧
      OrthogonalSplit.simpleRoot 4 3 = OrthogonalSplit.eps 4 2 + OrthogonalSplit.eps 4 3) ∧
    (∀ k : Fin 4,
      psiD ⟨canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).simple (jD k)),
          canonicalRep_simple_mem_groupD k⟩ = weylElt 4 K k ∧
        weylElt 4 K k = rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) 1 *
          rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) (-1) *
            rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) 1 ∧
        ((torusWeylNu 4 K (by norm_num) ⟨weylElt 4 K k, weylElt_mem_torusWeyl k⟩ :
          weylGroup 4) : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ)) = simpleRefl 4 k) ∧
    (∀ s : Fin 4 ⊕ Fin 4,
      swapE4F4 (Pi.single s (1 : K)) = Pi.single (Equiv.swap (Sum.inl 3) (Sum.inr 3) s) 1) ∧
    (∀ g : groupD, diagE6GL * (g : ModGL Tag.E6 K) * diagE6GL⁻¹ ∈ groupD) ∧
    (∀ g : groupD, ((conjD g : groupD) : ModGL Tag.E6 K) = diagE6GL * g * diagE6GL⁻¹ ∧
      psiD (conjD g) = swapE4F4 * psiD g * swapE4F4⁻¹) ∧
    (∀ c : K, bar c = c ^ 2) ∧
    (∀ g : groupD, ((betaD g : groupD) : ModGL Tag.E6 K) = betaGL g ∧
      LinearMap.toMatrix' (psiD (betaD g) : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
        (LinearMap.toMatrix' (psiD g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))).map bar) :=
  ⟨fun g _ hv => psiD_phiD g hv, quadPlus_apply 4 K, psiD_injective, range_psiD,
    ⟨psiDEquiv, coe_psiDEquiv⟩, map_psiD_unipotentD, map_psiD_torusD,
    fun a v c => OrthogonalSplit.torusElt_apply a v c,
    ⟨simpleRoot_zero, simpleRoot_one, simpleRoot_two, simpleRoot_three⟩,
    fun k => ⟨psiD_canonicalRep_simple k, rfl,
      congrArg Subtype.val (torusWeylNu_weylElt (by norm_num) k)⟩,
    swapE4F4_single, fun g => conj_mem_groupD g.2, fun g => ⟨rfl, psiD_conjD g⟩, fun _ => rfl,
    fun g => ⟨rfl, psiD_betaD g⟩⟩

end CFSG.LieType.Chevalley.C2E6Std
