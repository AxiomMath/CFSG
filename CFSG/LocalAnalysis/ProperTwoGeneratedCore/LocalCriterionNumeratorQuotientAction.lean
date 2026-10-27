module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorEquivariant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientStrongEmbedding

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFchapter1section1

universe u v w x

variable {G : Type u} {F : Type v} {Omega : Type w} {Xi : Type x}
variable [Group G] [Group F]

theorem transitive_action_equiv_of_surjective_stabilizer_map
    [MulAction G Omega] [MulAction F Xi]
    (hOmega : MulAction.IsPretransitive G Omega)
    (hXi : MulAction.IsPretransitive F Xi)
    (f : G →* F) (hf : Function.Surjective f) (a : Omega) (b : Xi)
    (hker : f.ker ≤ MulAction.stabilizer G a)
    (hstab : (MulAction.stabilizer G a).map f = MulAction.stabilizer F b) :
    ∃ phi : Omega ≃ Xi, phi a = b ∧
      ∀ (g : G) (y : Omega), phi (g • y) = f g • phi y := by
  let : MulAction G Xi := MulAction.compHom Xi f
  have htrans : MulAction.IsPretransitive G Xi := by
    constructor
    intro y y'
    obtain ⟨k, hk⟩ := hXi.exists_smul_eq y y'
    obtain ⟨g, hg⟩ := hf k
    exact ⟨g, by change f g • y = y'; rw [hg]; exact hk⟩
  have hcomp : MulAction.stabilizer G b = (MulAction.stabilizer F b).comap f := by
    ext g
    rfl
  have hsame : MulAction.stabilizer G a = MulAction.stabilizer G b := by
    rw [hcomp, ← hstab, Subgroup.comap_map_eq_self hker]
  exact transitive_action_equiv_of_stabilizer_eq hOmega htrans a b hsame

theorem strong_embedding_surjective_stabilizer_adjustment
    [Finite G] [Finite F]
    (f : G →* F) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (P : Subgroup G) (hP : fusionStronglyEmbedded P) (hker : f.ker ≤ P)
    (hrank : TwoRankAtLeastTwo F) (B : Subgroup F) (hB : fusionStronglyEmbedded B) :
    ∃ c : MulAut F, P.map (c.toMonoidHom.comp f) = B := by
  have himage : fusionStronglyEmbedded (P.map f) :=
    order_strong_embedding_of_native
      (strong_embedding_image_of_contained_odd_kernel f hf hodd
        (native_strong_embedding_of_order_conditions hP) hker)
  obtain ⟨g, hg⟩ := rank_two_strongEmbedding_conjugate hrank (P.map f) B himage hB
  rw [Subgroup.map_map] at hg
  exact ⟨MulAut.conj g⁻¹, hg⟩

theorem strong_embedding_transitive_action_identification_of_odd_kernel
    [Finite G] [Finite F] [MulAction G Omega] [MulAction F Xi]
    (hOmega : MulAction.IsPretransitive G Omega)
    (hXi : MulAction.IsPretransitive F Xi)
    (f : G →* F) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (a : Omega) (b : Xi)
    (ha : fusionStronglyEmbedded (MulAction.stabilizer G a))
    (hker : f.ker ≤ MulAction.stabilizer G a)
    (hrank : TwoRankAtLeastTwo F) (hb : fusionStronglyEmbedded (MulAction.stabilizer F b)) :
    ∃ (c : MulAut F) (phi : Omega ≃ Xi),
      (MulAction.stabilizer G a).map (c.toMonoidHom.comp f) =
        MulAction.stabilizer F b ∧
      phi a = b ∧
      ∀ (g : G) (y : Omega), phi (g • y) = c (f g) • phi y := by
  obtain ⟨c, hc⟩ := strong_embedding_surjective_stabilizer_adjustment f hf hodd
    (MulAction.stabilizer G a) ha hker hrank (MulAction.stabilizer F b) hb
  let E := c.toMonoidHom.comp f
  have hEker : E.ker = f.ker := MonoidHom.ker_mulEquiv_comp f c
  have hEsurj : Function.Surjective E := c.surjective.comp hf
  obtain ⟨phi, hbase, hequiv⟩ := transitive_action_equiv_of_surjective_stabilizer_map
    hOmega hXi E hEsurj a b (hEker.symm ▸ hker) hc
  exact ⟨c, phi, hc, hbase, hequiv⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
