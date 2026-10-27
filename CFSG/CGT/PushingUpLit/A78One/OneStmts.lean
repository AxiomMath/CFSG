module

public import CFSG.CGT.PushingUpLit.T2K.Global

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K

variable {G : Type} [Group G] [Finite G]

abbrev cj (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

structure CexCtx (L M : Subgroup G) (n : ℕ) (T T' : Subgroup G) (x : G) : Prop where
  hyp : T2Hyp G L M n
  nM : M ≤ Subgroup.normalizer (L : Set G)
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M
  le : T' ≤ T
  ge : (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (blockU L : Set G)) ≤ T'
  hx : x ∈ Subgroup.normalizer (T' : Set G)
  hxM : x ∉ M

abbrev cexP (L T : Subgroup G) : Subgroup G := T ⊓ Subgroup.centralizer (blockU L : Set G)

structure EndData (L M : Subgroup G) (n : ℕ) (T T' : Subgroup G) (x : G) : Prop where
  elem : CFSG.Open.IsElemAbelian 2 (cexP L T)
  maxElem : ∀ A, IsMaxElemAbelian T' A ↔ (A = cexP L T ∨ A = cj x⁻¹ (cexP L T))
  ne : cexP L T ≠ cj x⁻¹ (cexP L T)
  sylowJ : CFSG.ABGLocalTools.IsSylowOf 2 (cexP L T ⊔ cj x⁻¹ (cexP L T)) (L ⊔ cexP L T)

namespace CexCtx

variable {L M : Subgroup G} {n : ℕ} {T T' : Subgroup G} {x : G}

theorem inv (c : CexCtx L M n T T' x) : CexCtx L M n T T' x⁻¹ :=
  ⟨c.hyp, c.nM, c.sylow, c.le, c.ge, Subgroup.inv_mem _ c.hx,
    fun h => c.hxM (by simpa using M.inv_mem h)⟩

end CexCtx

end CFSG.CGT.PushingUpLit.A78One
