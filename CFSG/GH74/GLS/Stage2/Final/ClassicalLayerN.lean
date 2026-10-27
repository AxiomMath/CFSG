module

public import CFSG.GH74.GLS.Stage2.Final.ClassicalLocal
public import CFSG.GH74.GLS.Stage2.Final.LayerLiftN
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Glue
public import CFSG.GH74.GLS.Stage2.Final.Named

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Main
  CFSG.GH74.GLS.Stage1.Thm3.Sec4

theorem layerN_of_ecInter (hEC : ECInter) {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}
    (hctx : Stage2Ctx G z k S) (hout : Stage2Out G z k S) (hk : k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε)
    {K₁ K₂ : Subgroup G} (hstd : Std4 G z S K₁ K₂) :
    layerTimesSylow z S = K₁ ⊔ K₂ ⊔ S ∧ (K₁ ⊔ K₂ ⊔ S) ⊓ OddCore z = ⊥ := by
  have hEC' := hEC G z k S hctx hk
  have hS : IsPGroup 2 ↥S := hctx.sylow.isPGroup
  have hSC : S ≤ Cen z := hctx.S_le_Cen
  have hK₁ : IsPCompIn 2 (Cen z) K₁ := hstd.comp_isPCompIn (Or.inl rfl)
  have hK₂ : IsPCompIn 2 (Cen z) K₂ := hstd.comp_isPCompIn (Or.inr rfl)
  have hd := hctx.data
  rcases hk with rfl | ⟨ε, rfl⟩
  · cases hd with
    | psp4 h =>
      obtain ⟨q, L₁, L₂, hq⟩ := h
      have h0 : pPrimeCore 2 ↥(Cen z) = ⊥ := hout.oddCore (fun ε h' => by cases h')
      have hcyc : IsCyclic ↥(pPrimeCore 2 ↥(Cen z)) := by
        rw [h0]
        infer_instance
      exact LayerLiftN.layerTimesSylow_eq_of_two_components hS hSC hcyc hK₁ hK₂ hstd.ne hq.pair.comps hEC'
  · cases hd with
    | l4 _ h =>
      obtain ⟨q, L₁, L₂, hq⟩ := h
      have hcyc : IsCyclic ↥(pPrimeCore 2 ↥(Cen z)) := (hout.oddCoreL4 ε q L₁ L₂ rfl hq).1
      exact LayerLiftN.layerTimesSylow_eq_of_two_components hS hSC hcyc hK₁ hK₂ hstd.ne hq.pair.comps hEC'

end CFSG.GH74.GLS.Stage2.Final
