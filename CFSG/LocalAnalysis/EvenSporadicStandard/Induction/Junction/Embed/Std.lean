module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chains
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Conj

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

section Equiv

variable {H H' : Type} [Group H] [Group H']

theorem jstdModulo_of_equiv {Y Z K : Subgroup H} {Y' Z' K' : Subgroup H'} (e : ↥Y ≃* ↥Y')
    (hZ : (Z.subgroupOf Y).map e.toMonoidHom = Z'.subgroupOf Y')
    (hK : (K.subgroupOf Y).map e.toMonoidHom = K'.subgroupOf Y')
    (h : StdModulo Y Z K) : StdModulo Y' Z' K' := by
  obtain ⟨hZn, hstd⟩ := h
  have hZn' : (Z'.subgroupOf Y').Normal := by
    rw [← hZ]
    exact Subgroup.Normal.map hZn _ e.surjective
  refine ⟨hZn', ?_⟩
  have hZn2 : (Z.subgroupOf Y).Normal := hZn
  let q : (↥Y ⧸ Z.subgroupOf Y) ≃* (↥Y' ⧸ Z'.subgroupOf Y') :=
    QuotientGroup.congr (Z.subgroupOf Y) (Z'.subgroupOf Y') e hZ
  have h1 := stdBare_map_mulEquiv q hstd
  have h2 : ((K.subgroupOf Y).map (QuotientGroup.mk' (Z.subgroupOf Y))).map q.toMonoidHom =
      (K'.subgroupOf Y').map (QuotientGroup.mk' (Z'.subgroupOf Y')) := by
    rw [Subgroup.map_map, ← hK, Subgroup.map_map]
    congr 1
  rwa [h2] at h1

end Equiv

variable {H : Type} [Group H] (Y : Subgroup H)

noncomputable def cqEquivMapSubtype (Lt : Subgroup ↥Y) :
    (↥Lt ⧸ center ↥Lt) ≃* (↥(Lt.map Y.subtype) ⧸ center ↥(Lt.map Y.subtype)) :=
  QuotientGroup.congr _ _ (Lt.equivMapOfInjective Y.subtype Y.subtype_injective)
    (Subgroup.map_center_eq _)

theorem jstdModulo_map_subtype {Lt Kt : Subgroup ↥Y} (s : ↥Y)
    (h : StdModulo (Lt ⊔ zpowers s) (centralizer (Lt : Set ↥Y)) Kt) :
    StdModulo (Lt.map Y.subtype ⊔ zpowers (s : H))
      (centralizer ((Lt.map Y.subtype : Subgroup H) : Set H)) (Kt.map Y.subtype) := by
  have hY : (Lt ⊔ zpowers s).map Y.subtype = Lt.map Y.subtype ⊔ zpowers (s : H) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  let e : ↥(Lt ⊔ zpowers s) ≃* ↥(Lt.map Y.subtype ⊔ zpowers (s : H)) :=
    ((Lt ⊔ zpowers s).equivMapOfInjective Y.subtype Y.subtype_injective).trans
      (MulEquiv.subgroupCongr hY)
  have he : ∀ x : ↥(Lt ⊔ zpowers s), ((e x : ↥(Lt.map Y.subtype ⊔ zpowers (s : H))) : H) =
      ((x : ↥Y) : H) := fun x => rfl
  refine jstdModulo_of_equiv e ?_ ?_ h
  · ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [he]
      refine mem_centralizer_iff.2 ?_
      rintro _ ⟨l, hl, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.1 hx l hl)
    · intro hy
      obtain ⟨x, hx⟩ : ∃ x : ↥(Lt ⊔ zpowers s), e x = y := e.surjective y
      refine ⟨x, ?_, hx⟩
      refine mem_centralizer_iff.2 fun l hl => Subtype.ext ?_
      have := mem_centralizer_iff.1 hy (l : H) ⟨l, hl, rfl⟩
      rw [← hx, he] at this
      exact this
  · ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [he]
      exact ⟨(x : ↥Y), hx, rfl⟩
    · rintro ⟨k, hk, hky⟩
      obtain ⟨x, hx⟩ : ∃ x : ↥(Lt ⊔ zpowers s), e x = y := e.surjective y
      refine ⟨x, ?_, hx⟩
      have h1 : ((x : ↥Y) : H) = (k : H) := by
        rw [← he x, hx]
        exact hky.symm
      have hxk : (x : ↥Y) = k := Subtype.ext h1
      rw [hxk]
      exact hk

end CFSG.EvenSporadicStandard.Induction.Junction
