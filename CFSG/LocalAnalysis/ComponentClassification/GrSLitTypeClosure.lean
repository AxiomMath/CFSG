module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeStep
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def IsHeldType (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* Blueprint.NativeSporadic.He)

@[expose] def IsL34Type (K : Type) [Group K] : Prop :=
  Blueprint.LieModel K .PSL 3 2 2

@[expose] def IsA7Type (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* alternatingGroup (Fin 7))

@[expose] def IsL2Type (q : ℕ) (K : Type) [Group K] : Prop :=
  Blueprint.LieModel K .PSL 2 q 1

@[expose] def GSRestrictedType (K : Type) [Group K] : Prop :=
  IsHeldType (K ⧸ Open.fusionZStar K) ∨ IsL34Type (K ⧸ Open.fusionZStar K) ∨
    IsA7Type (K ⧸ Open.fusionZStar K) ∨ IsL2Type 5 (K ⧸ Open.fusionZStar K) ∨
    IsL2Type 7 (K ⧸ Open.fusionZStar K)

theorem GSRestrictedType.of_equiv {L M : Type} [Group L] [Group M]
    (e : L ⧸ Open.fusionZStar L ≃* M ⧸ Open.fusionZStar M) (h : GSRestrictedType M) :
    GSRestrictedType L := by
  rcases h with h | h | h | h | h
  · exact Or.inl (h.map fun f => e.trans f)
  · exact Or.inr (Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv e.symm h))
  · exact Or.inr (Or.inr (Or.inl (h.map fun f => e.trans f)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv e.symm h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv e.symm h))))

@[expose] def ProperFixedComponents (τ ρ : ∀ (K : Type) [Group K], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a b : G) (M T : Subgroup G), orderOf a = 2 →
    orderOf b = 2 → a * b = b * a → M ≤ centralizer ({b} : Set G) →
    IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))) → conjugate M a = M →
    T ≤ M ⊓ centralizer ({a} : Set G) →
    IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))) →
    (pPrimeCore 2 T).index < (pPrimeCore 2 M).index →
    τ (M ⧸ Open.fusionZStar M) → ρ (T ⧸ Open.fusionZStar T)

@[expose] def HeldFixedInput : Prop :=
  ProperFixedComponents IsHeldType fun K _ => IsL34Type K ∨ IsA7Type K

@[expose] def L34FixedInput : Prop :=
  ProperFixedComponents IsL34Type fun K _ => IsL2Type 5 K ∨ IsL2Type 7 K

@[expose] def A7FixedInput : Prop :=
  ProperFixedComponents IsA7Type (IsL2Type 5)

@[expose] def L2FixedInput : Prop :=
  ProperFixedComponents (IsL2Type 5) (fun _ _ => False) ∧
    ProperFixedComponents (IsL2Type 7) (fun _ _ => False)

variable {G : Type} [Group G] [Finite G]

theorem gsRestrictedType_of_gsWeakCorr (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) (hHe : HeldFixedInput) (hL34 : L34FixedInput)
    (hA7 : A7FixedInput) (hL2 : L2FixedInput) {a b : G} {L M : Subgroup G}
    (h : GSWeakCorr a L b M) (hbZ : b ∉ center G) (hM : GSRestrictedType M) :
    GSRestrictedType L := by
  rcases gsWeakCorr_type_dichotomy hS hK h hbZ with he | ⟨hMa, hTM, hTpc, hlt, he⟩
  · obtain ⟨e⟩ := he
    exact GSRestrictedType.of_equiv e hM
  · obtain ⟨e⟩ := he
    obtain ⟨ha, hb, hab, -, -, hMb, hMp, -⟩ := h
    refine GSRestrictedType.of_equiv e ?_
    rcases hM with hτ | hτ | hτ | hτ | hτ
    · rcases hHe G a b M _ ha hb hab hMb hMp hMa hTM hTpc hlt hτ with hρ | hρ
      · exact Or.inr (Or.inl hρ)
      · exact Or.inr (Or.inr (Or.inl hρ))
    · rcases hL34 G a b M _ ha hb hab hMb hMp hMa hTM hTpc hlt hτ with hρ | hρ
      · exact Or.inr (Or.inr (Or.inr (Or.inl hρ)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hρ)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hA7 G a b M _ ha hb hab hMb hMp hMa hTM hTpc hlt
        hτ))))
    · exact (hL2.1 G a b M _ ha hb hab hMb hMp hMa hTM hTpc hlt hτ).elim
    · exact (hL2.2 G a b M _ ha hb hab hMb hMp hMa hTM hTpc hlt hτ).elim

theorem gsRestrictedType_of_gsWeakReach (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) (hZ : ∀ z : G, orderOf z = 2 → z ∉ center G)
    (hHe : HeldFixedInput) (hL34 : L34FixedInput) (hA7 : A7FixedInput) (hL2 : L2FixedInput)
    {J₀ J : Subgroup G} (h : GSWeakReach J₀ J) (hJ : GSRestrictedType J) :
    GSRestrictedType J₀ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hJ
  | head hst _ ih =>
    obtain ⟨a, b, hC⟩ := hst
    exact gsRestrictedType_of_gsWeakCorr hS hK hHe hL34 hA7 hL2 hC (hZ b hC.2.1) ih

end CFSG.ComponentClassification.GrSLit
