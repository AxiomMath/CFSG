module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralConj

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

@[expose] def SLComponentForm (K : Type) [Field K] (G : Type) [Group G] : Prop :=
  ∀ L : Subgroup G, IsComponent L → Nonempty (L ≃* SL(2, K)) ∨
    (Nat.card SL(2, K) ∣ Nat.card L ∧ ∀ L' : Subgroup G, IsComponent L' →
      ¬ Nonempty (L' ≃* SL(2, K)) → Nonempty (L ≃* L'))

@[expose] def OddExcInnerDiagSLForm (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → orderOf α = 2 →
      (∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L → IsQuasisimple L) ∧
        SLComponentForm K (fixedSubgroup α)

theorem slComponentForm_of_mulEquiv {K : Type} [Field K] {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (h : SLComponentForm K H) : SLComponentForm K G := by
  intro L hL
  let eL : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective _ e.injective
  rcases h _ (LocalCores.isComponent_map_mulEquiv e hL) with hSL | ⟨hdvd, hiso⟩
  · obtain ⟨f⟩ := hSL
    exact Or.inl ⟨eL.trans f⟩
  · refine Or.inr ⟨by rwa [Nat.card_congr eL.toEquiv], fun L' hL' hL'SL => ?_⟩
    let eL' : L' ≃* L'.map e.toMonoidHom := L'.equivMapOfInjective _ e.injective
    obtain ⟨f⟩ := hiso _ (LocalCores.isComponent_map_mulEquiv e hL')
      (fun ⟨f⟩ => hL'SL ⟨eL'.trans f⟩)
    exact ⟨(eL.trans f).trans eL'.symm⟩

theorem slComponentForm_of_eq_or_SL {K : Type} [Field K] {G : Type} [Group G] {B : Subgroup G}
    (hB : Nat.card SL(2, K) ∣ Nat.card B)
    (h : ∀ L : Subgroup G, IsComponent L → L = B ∨ Nonempty (L ≃* SL(2, K))) :
    SLComponentForm K G := by
  intro L hL
  rcases h L hL with rfl | hSL
  · refine Or.inr ⟨hB, fun L' hL' hL'SL => ?_⟩
    rcases h L' hL' with rfl | hSL'
    · exact ⟨MulEquiv.refl _⟩
    · exact absurd hSL' hL'SL
  · exact Or.inl hSL

theorem card_SL_dvd_of_rootPair_le
    {τ : Tag} {K : Type} [Field K] (hK2 : ringChar K ≠ 2) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) {H : Subgroup (ModGL τ K)}
    (hle : rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ≤ H) :
    Nat.card SL(2, K) ∣ Nat.card H := by
  obtain ⟨-, ⟨e⟩, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK2 hβ
  have h1 : Nat.card SL(2, K) =
      Nat.card (rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) : Subgroup (ModGL τ K)) :=
    Nat.card_congr e.toEquiv
  rw [h1]
  exact Subgroup.card_dvd_of_le hle

theorem card_SL_dvd_subsystemGroup
    {τ : Tag} {K : Type} [Field K] (hK2 : ringChar K ≠ 2) {J : Set (Fin τ.rank)}
    {i : Fin τ.rank} (hi : i ∈ J) : Nat.card SL(2, K) ∣ Nat.card (subsystemGroup τ K J) := by
  have h0 : ∀ j ∉ J, (Pi.single i 1 : Fin τ.rank → ℤ) j = 0 := fun j hj =>
    Pi.single_eq_of_ne (fun h : j = i => hj (h ▸ hi)) _
  refine card_SL_dvd_of_rootPair_le hK2 (isRoot_single τ i) (sup_le
    (rootSubgroup_le_subsystemGroup ⟨isRoot_single τ i, h0⟩)
    (rootSubgroup_le_subsystemGroup ⟨IsRoot.neg (isRoot_single τ i), fun j hj => ?_⟩))
  rw [Pi.neg_apply, h0 j hj, neg_zero]

theorem toralCentralizer_slForm_of_orbitCheck
    {τ : Tag} {K : Type} [Field K] (hK2 : ringChar K ≠ 2) {reps : List (List Bool)}
    {entries : List (List Bool × ℕ × List ℕ)} (hcert : OrbitCheck τ reps entries)
    (hreps : ∀ ρ < reps.length, listMask (τ := τ) (reps.getD ρ []) ≠ (fun _ => false) →
      SLComponentForm K (toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ [])))))
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    SLComponentForm K (toralCentralizer τ K b) := by
  obtain ⟨ρ, hρ, w, hw, hmap⟩ := exists_conj_toralCentralizer_of_orbitCheck hK2 hcert hb
  by_cases h0 : listMask (τ := τ) (reps.getD ρ []) = fun _ => false
  · refine absurd (eq_one_of_rootChar_smul_eq_one (w := w) fun v => ?_) hb1
    rw [hw v]
    congr 1
    funext i
    change (if listMask (τ := τ) (reps.getD ρ []) i then (-1 : Kˣ) else 1) = 1
    rw [h0]
    rfl
  · let e : toralCentralizer τ K (bitsTuple (listMask (reps.getD ρ []))) ≃*
        toralCentralizer τ K b :=
      ((toralCentralizer τ K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact slComponentForm_of_mulEquiv e.symm (hreps ρ hρ h0)

theorem oddExcInnerDiagSLForm_of_toral
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    (hq : ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
      ∀ α : MulAut (adjointGroup τ K), α ^ 2 = 1 →
        ∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L → IsQuasisimple L)
    (hrow : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 →
      Nat.card K = p ^ f → ∀ b : Fin τ.rank → Kˣ, (∀ i, b i = 1 ∨ b i = -1) → b ≠ 1 →
        SLComponentForm K (toralCentralizer τ K b)) :
    OddExcInnerDiagSLForm τ := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo
  have hKodd : Odd (Nat.card K) := by
    rw [hKp]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag hτ hKodd hαg hα
  exact ⟨hq K hKodd α hα, slComponentForm_of_mulEquiv Θ (hrow K p f hp hp2 hKp b hb (hb1 hα1))⟩

end CFSG.ComponentClassification.CatLeafProof
