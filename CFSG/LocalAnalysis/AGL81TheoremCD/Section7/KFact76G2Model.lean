module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def G2ModelNormalizerMax : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ A : Subgroup (adjointGroup .G2 K), Nat.card A = 3 →
      (∀ g : adjointGroup .G2 K, A.map (MulAut.conj g).toMonoidHom ≤
          Subgroup.normalizer (A : Set (adjointGroup .G2 K)) →
        A.map (MulAut.conj g).toMonoidHom = A) →
      IsCoatom (Subgroup.normalizer (A : Set (adjointGroup .G2 K)))

theorem kFactG2NormalizerMax_of_model
    (h : G2ModelNormalizerMax) : KFactG2NormalizerMax := by
  intro X _ _ ⟨q, hv, hp3, ⟨e⟩⟩ A hA hwc
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have hF : Nat.card F = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ : Nonempty (AdjointQuotient .G2 F ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
    by_cases hp : q.p = 2
    · exact CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp _ hF
    · exact CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp _ hF
  let θ : X ≃* adjointGroup .G2 F := e.trans (b.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  have hchar : ringChar F ≠ 3 := by
    rw [ringChar.eq F q.p]
    exact hp3
  have h4 : 4 ≤ Nat.card F := by
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rw [hF]
    by_contra hlt
    have hq : q.card = 3 := by omega
    exact hp3 (Nat.prime_three.pow_eq_iff.mp (by rw [← q.card_def]; exact hq)).1
  have hwc' : ∀ g : adjointGroup .G2 F, (A.map θ.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer ((A.map θ.toMonoidHom : Subgroup _) : Set (adjointGroup .G2 F)) →
      (A.map θ.toMonoidHom).map (MulAut.conj g).toMonoidHom = A.map θ.toMonoidHom := by
    intro g hg
    have hcomp : (MulAut.conj g).toMonoidHom.comp θ.toMonoidHom =
        θ.toMonoidHom.comp (MulAut.conj (θ.symm g)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply]
    have hmap : (A.map θ.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (A.map (MulAut.conj (θ.symm g)).toMonoidHom).map θ.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    rw [hmap] at hg ⊢
    rw [← Subgroup.map_equiv_normalizer_eq] at hg
    rw [hwc (θ.symm g) ((Subgroup.map_le_map_iff_of_injective θ.injective).mp hg)]
  have hco := h F hchar h4 (A.map θ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective θ.injective, hA]) hwc'
  refine (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup θ) _).1 ?_
  rw [MulEquiv.coe_mapSubgroup, Subgroup.map_equiv_normalizer_eq]
  exact hco

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
