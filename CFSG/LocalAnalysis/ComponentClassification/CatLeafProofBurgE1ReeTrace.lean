module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1ReeChar
public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces
public import CFSG.LieType.Chevalley.OddG2ToralInvolutionComponents
public import CFSG.LieType.Ree.SmallReeTorusAction

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.Chevalley

theorem g2CertRoot_injective : ∀ k k' : Fin 12,
    Tag.G2.rootCertificate.root k = Tag.G2.rootCertificate.root k' → k = k' := by
  decide +kernel

theorem g2CertRoot_cartan : ∀ k : Fin 12,
    ∑ j, Tag.G2.cartan ⟨0, by decide⟩ j * Tag.G2.rootCertificate.root k j = g2TorusExpM0 k ∧
      ∑ j, Tag.G2.cartan ⟨1, by decide⟩ j * Tag.G2.rootCertificate.root k j = g2TorusExpM1 k := by
  decide +kernel

@[expose] def g2CertRootEquiv
    : Fin 12 ≃ {v : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 v} :=
  Equiv.ofBijective (fun k => ⟨Tag.G2.rootCertificate.root k, isRoot_G2_iff.2 ⟨k, rfl⟩⟩)
    ⟨fun k k' h => g2CertRoot_injective k k' (congrArg Subtype.val h), fun ⟨v, hv⟩ => by
      obtain ⟨k, hk⟩ := isRoot_G2_iff.1 hv
      exact ⟨k, Subtype.ext hk⟩⟩

theorem trace_smallReeTorusElt
    (a : ℕ) {K : Type} [Field K] (s : Kˣ) :
    LinearMap.trace K (RootModule Tag.G2 K)
        ((smallReeTorusElt a K s : (Module.End K (RootModule Tag.G2 K))ˣ) :
          Module.End K (RootModule Tag.G2 K)) =
      2 + ∑ k, zpowChar K (g2TorusExp (3 ^ a) k) s := by
  have hb : ∀ b : Label Tag.G2,
      ((smallReeTorusElt a K s : (Module.End K (RootModule Tag.G2 K))ˣ) :
        Module.End K (RootModule Tag.G2 K)) (Finsupp.single b 1) b =
        torusEigen ⟨1, by decide⟩ (s ^ 3 ^ a) b * torusEigen ⟨0, by decide⟩ s b := by
    intro b
    rw [smallReeTorusElt, Units.val_mul, Module.End.mul_apply,
      RankThree.Chevalley.torusElt_single, map_smul, RankThree.Chevalley.torusElt_single,
      smul_smul, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  have hinl : ∀ j : Fin Tag.G2.rank,
      ((smallReeTorusElt a K s : (Module.End K (RootModule Tag.G2 K))ˣ) :
        Module.End K (RootModule Tag.G2 K)) (Finsupp.single (Sum.inl j) 1) (Sum.inl j) = 1 := by
    intro j
    rw [hb]
    exact mul_one 1
  have hinr : ∀ β : {v : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 v},
      ((smallReeTorusElt a K s : (Module.End K (RootModule Tag.G2 K))ˣ) :
        Module.End K (RootModule Tag.G2 K)) (Finsupp.single (Sum.inr β) 1) (Sum.inr β) =
        ((s ^ (∑ j, Tag.G2.cartan ⟨0, by decide⟩ j * β.1 j +
          (3 : ℤ) ^ a * ∑ j, Tag.G2.cartan ⟨1, by decide⟩ j * β.1 j) : Kˣ) : K) := by
    intro β
    rw [hb]
    show (((s ^ 3 ^ a) ^ (∑ j, Tag.G2.cartan ⟨1, by decide⟩ j * β.1 j) : Kˣ) : K) *
        ((s ^ (∑ j, Tag.G2.cartan ⟨0, by decide⟩ j * β.1 j) : Kˣ) : K) = _
    rw [← Units.val_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 2
    push_cast
    ring
  rw [trace_rootModule_eq_sum, Fintype.sum_sum_type]
  simp only [hinl, hinr]
  rw [← Equiv.sum_comp g2CertRootEquiv]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun k _ => ?_)
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num [Tag.rank]
  · obtain ⟨h0, h1⟩ := g2CertRoot_cartan k
    rw [zpowChar_apply, g2TorusExp, ← h0, ← h1]
    rfl

theorem trace_reeTorus_G2
    (a : ℕ) {K : Type} [Field K] (s : Kˣ) :
    LinearMap.trace K (RootModule ReeTag.G2.tag K)
        (((ReeTag.G2.reeTorus a ReeTag.g2I0 s : adjointGroup ReeTag.G2.tag K) :
          ModGL ReeTag.G2.tag K) : Module.End K (RootModule ReeTag.G2.tag K)) =
      2 + ∑ k, zpowChar K (g2TorusExp (3 ^ a) k) s := by
  rw [← ReeTag.smallReeTorusElt_eq_reeTorus]
  exact trace_smallReeTorusElt a s

end CFSG.ComponentClassification.CatLeafProof
