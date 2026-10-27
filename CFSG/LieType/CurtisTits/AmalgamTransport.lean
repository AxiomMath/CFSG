module

public import CFSG.LieType.CurtisTits.AmalgamRedundancy
public import CFSG.LieType.CurtisTits.TitsGeometry

public section

namespace CFSG.LieType.CurtisTits

open Subgroup

universe u v w

def parabolicIndexComplOrderIso {I : Type v} (𝒮 : Set (Set I))
    (h𝒮 : ∀ C ∈ 𝒮, C ≠ Set.univ) :
    {J : ParabolicIndex I // (OrderDual.ofDual J.1)ᶜ ∈ 𝒮} ≃o ↥𝒮 where
  toFun J := ⟨(OrderDual.ofDual J.1.1)ᶜ, J.2⟩
  invFun C :=
    ⟨⟨OrderDual.toDual C.1ᶜ, by
        simpa only [OrderDual.ofDual_toDual] using Set.nonempty_compl.2 (h𝒮 C.1 C.2)⟩,
      by simpa only [OrderDual.ofDual_toDual, compl_compl] using C.2⟩
  left_inv J := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [OrderDual.toDual_ofDual, compl_compl]
  right_inv C := by
    apply Subtype.ext
    simp only [OrderDual.ofDual_toDual, compl_compl]
  map_rel_iff' := by
    intro J K
    change (OrderDual.ofDual J.1.1)ᶜ ⊆ (OrderDual.ofDual K.1.1)ᶜ ↔ J ≤ K
    rw [Set.compl_subset_compl]
    rfl

theorem IsUniversalCompletion.cotype {K : Type u} [Group K] {I : Type v} {𝒮 : Set (Set I)}
    (h𝒮 : ∀ C ∈ 𝒮, C ≠ Set.univ) {Q : Set I → Subgroup K}
    (hU : IsUniversalCompletion.{u, v, w}
      (fun J : {J : ParabolicIndex I // (OrderDual.ofDual J.1)ᶜ ∈ 𝒮} =>
        Q (OrderDual.ofDual J.1.1))) :
    IsUniversalCompletion.{u, v, w} (fun C : ↥𝒮 => Q C.1ᶜ) :=
  IsUniversalCompletion.congr_orderIso
    (L := fun J : {J : ParabolicIndex I // (OrderDual.ofDual J.1)ᶜ ∈ 𝒮} =>
      Q (OrderDual.ofDual J.1.1))
    (L' := fun C : ↥𝒮 => Q C.1ᶜ)
    (parabolicIndexComplOrderIso 𝒮 h𝒮)
    (fun J => by
      change Q ((OrderDual.ofDual J.1.1)ᶜᶜ) = Q (OrderDual.ofDual J.1.1)
      rw [compl_compl])
    hU

theorem iSup_eq_top_of_isUniversalCompletion {K : Type u} [Group K] {ι : Type v}
    [Preorder ι] {L : ι → Subgroup K} (hU : IsUniversalCompletion.{u, v, u} L) :
    ⨆ i, L i = ⊤ := by
  let N : Subgroup K := ⨆ i, L i
  let φN : ∀ i, L i →* ↥N := fun i => Subgroup.inclusion (le_iSup L i)
  have hφN : IsCompatible L φN := by
    intro i j _ x y hxy
    exact Subtype.ext hxy
  obtain ⟨ψ, hψ, -⟩ := hU ↥N φN hφN
  let φK : ∀ i, L i →* K := fun i => (L i).subtype
  have hφK : IsCompatible L φK := by
    intro i j _ x y hxy
    exact hxy
  obtain ⟨Ψ, -, hΨuniq⟩ := hU K φK hφK
  have hcomp : N.subtype.comp ψ = MonoidHom.id K := by
    have h1 : ∀ i (x : L i), (N.subtype.comp ψ) x = φK i x := by
      intro i x
      rw [MonoidHom.comp_apply, hψ i x]
      rfl
    have h2 : ∀ i (x : L i), (MonoidHom.id K) x = φK i x := fun i x => rfl
    exact (hΨuniq _ h1).trans (hΨuniq _ h2).symm
  change N = ⊤
  refine (Subgroup.eq_top_iff' N).2 fun x => ?_
  have hx : N.subtype (ψ x) = x := by
    have := congrFun (congrArg DFunLike.coe hcomp) x
    simpa using this
  exact hx ▸ (ψ x).2

end CFSG.LieType.CurtisTits
