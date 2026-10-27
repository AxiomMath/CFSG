module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFamily
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLiftField

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def IsTwoComponent {G : Type*} [Group G] (J : Subgroup G) : Prop :=
  J.IsSubnormal ∧ IsTwoQuasisimple ↥J

@[expose] def IsTwoComponentIn {G : Type*} [Group G] (J A : Subgroup G) : Prop :=
  J ≤ A ∧ (J.subgroupOf A).IsSubnormal ∧ IsTwoQuasisimple ↥J

@[expose] def twoLayer (G : Type*) [Group G] : Subgroup G :=
  sSup {J : Subgroup G | IsTwoComponent J}

@[expose] def Harris82Lemma219Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), orderOf z = 2 →
    (∀ L : Subgroup G, IsTwoComponent L →
      (L.map (MulAut.conj z).toMonoidHom = L →
        ∀ J : Subgroup G, IsTwoComponentIn J (L ⊓ centralizer {z}) →
          IsTwoComponentIn J (centralizer {z})) ∧
      (L.map (MulAut.conj z).toMonoidHom ≠ L →
        IsTwoComponentIn (centralizerResidual (L ⊔ L.map (MulAut.conj z).toMonoidHom) z)
            (centralizer {z}) ∧
          (pPrimeCore 2 ↥((L ⊔ L.map (MulAut.conj z).toMonoidHom) ⊓ centralizer {z})).map
              ((L ⊔ L.map (MulAut.conj z).toMonoidHom) ⊓ centralizer {z}).subtype =
            pPrimeCore 2 G ⊓ ((L ⊔ L.map (MulAut.conj z).toMonoidHom) ⊓ centralizer {z}) ∧
          ∃ φ : ↥L ⧸ pPrimeCore 2 ↥L →*
              ↥(centralizerResidual (L ⊔ L.map (MulAut.conj z).toMonoidHom) z) ⧸
                pPrimeCore 2 ↥(centralizerResidual (L ⊔ L.map (MulAut.conj z).toMonoidHom) z),
            Function.Surjective φ)) ∧
    ∀ J : Subgroup G, IsTwoComponentIn J (centralizer {z}) →
      ∃ K : Subgroup G, IsTwoComponent K ∧
        ((K.map (MulAut.conj z).toMonoidHom = K ∧ IsTwoComponentIn J (K ⊓ centralizer {z})) ∨
          (K.map (MulAut.conj z).toMonoidHom ≠ K ∧
            J = centralizerResidual (K ⊔ K.map (MulAut.conj z).toMonoidHom) z)) ∧
        ⁅J, K ⊔ K.map (MulAut.conj z).toMonoidHom⁆ = K ⊔ K.map (MulAut.conj z).toMonoidHom ∧
        ⁅J, twoLayer G⁆ = K ⊔ K.map (MulAut.conj z).toMonoidHom ∧
        (⨆ g : ↥(twoLayer G), J.map (MulAut.conj (g : G)).toMonoidHom) =
          K ⊔ K.map (MulAut.conj z).toMonoidHom

end CFSG.ComponentClassification.HarrisLit
