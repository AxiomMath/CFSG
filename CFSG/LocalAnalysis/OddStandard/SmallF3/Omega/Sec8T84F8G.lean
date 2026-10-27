module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3E0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F4Nrm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section TData

variable {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84_gamma_swaps (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) (hE8 : IsElemAb2 E 8)
    (hT : IsSylow2Of T (normalizer (E : Set G))) {γ : G} (hγ : γ ∈ normalizer (T : Set G))
    (hγ2 : IsPGroup 2 ↥(zpowers γ)) (hγT : γ ∉ T) :
    E.map (MulAut.conj γ).toMonoidHom = F1 ⊔ F2 ∧
      (F1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = E := by
  have hE_le_T := sec8t84_E_le_T D
  have hE_norm : (E.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE_le_T).mpr hT.1
  have hkey : ∀ (δ : G), δ ∈ normalizer (T : Set G) → ∀ A : Subgroup G, A ≤ T →
      IsElemAb2 A 8 → (A.subgroupOf T).Normal →
      A.map (MulAut.conj δ).toMonoidHom = E ∨
        A.map (MulAut.conj δ).toMonoidHom = F1 ⊔ F2 := by
    intro δ hδ A hAT hA8 hAn
    have hδmap : T.map (MulAut.conj δ).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hδ
    have hAmapT : A.map (MulAut.conj δ).toMonoidHom ≤ T := by
      rw [← hδmap]
      exact Subgroup.map_mono hAT
    have h8 : IsElemAb2 (A.map (MulAut.conj δ).toMonoidHom) 8 := by
      refine ⟨hA8.1.map (MulAut.conj δ).toMonoidHom, ?_⟩
      rw [Subgroup.card_map_of_injective (MulAut.conj δ).injective, hA8.2]
    have hnorm : ((A.map (MulAut.conj δ).toMonoidHom).subgroupOf T).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAmapT]
      have hAn' : T ≤ normalizer A := (Subgroup.normal_subgroupOf_iff_le_normalizer hAT).mp hAn
      calc T = T.map (MulAut.conj δ).toMonoidHom := hδmap.symm
        _ ≤ (normalizer A).map (MulAut.conj δ).toMonoidHom := Subgroup.map_mono hAn'
        _ ≤ normalizer (A.map (MulAut.conj δ).toMonoidHom) := Subgroup.le_normalizer_map _
    exact sec8t84_normal_E8 D hAmapT h8 hnorm
  have sylow_eq : ∀ {H P Q : Subgroup G}, IsSylow2Of P H → Q ≤ H → IsPGroup 2 Q →
      P ≤ Q → Q = P := by
    intro H P Q hP hQH hQ2 hPQ
    obtain ⟨P0, hP0⟩ := hP.exists_sylow
    have hQsub : IsPGroup 2 (Q.subgroupOf H) :=
      hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
    have hP0le : (P0 : Subgroup ↥H) ≤ Q.subgroupOf H := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hxP : (x : G) ∈ (P0 : Subgroup ↥H).map H.subtype := ⟨x, hx, rfl⟩
      rw [hP0] at hxP
      exact hPQ hxP
    have heq : Q.subgroupOf H = (P0 : Subgroup ↥H) := P0.is_maximal' hQsub hP0le
    have hmap := congrArg (Subgroup.map H.subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hQH, hP0] at hmap
  have hnot : ∀ (δ : G), δ ∈ normalizer (T : Set G) → IsPGroup 2 ↥(zpowers δ) →
      δ ∉ T → E.map (MulAut.conj δ).toMonoidHom ≠ E := by
    intro δ hδ hδ2 hδT hconj
    have hδE : δ ∈ normalizer (E : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj
    have hWle : T ⊔ zpowers δ ≤ normalizer (E : Set G) :=
      sup_le hT.1 (Subgroup.zpowers_le.mpr hδE)
    have hδzp : zpowers δ ≤ normalizer (T : Set G) := Subgroup.zpowers_le.mpr hδ
    have hW2 : IsPGroup 2 (T ⊔ zpowers δ : Subgroup G) :=
      hT.2.1.to_sup_of_normal_left' hδ2 hδzp
    have hWT : T ⊔ zpowers δ = T := sylow_eq hT hWle hW2 le_sup_left
    exact hδT (hWT ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers δ))
  have hE1 : E.map (MulAut.conj γ).toMonoidHom = F1 ⊔ F2 :=
    (hkey γ hγ E hE_le_T hE8 hE_norm).resolve_left (hnot γ hγ hγ2 hγT)
  have hγinv : γ⁻¹ ∈ normalizer (T : Set G) := (normalizer (T : Set G)).inv_mem hγ
  have hγinv2 : IsPGroup 2 ↥(zpowers γ⁻¹) := by
    rw [Subgroup.zpowers_inv]
    exact hγ2
  have hγinvT : γ⁻¹ ∉ T := fun h => hγT (by simpa using T.inv_mem h)
  have hE1inv : E.map (MulAut.conj γ⁻¹).toMonoidHom = F1 ⊔ F2 :=
    (hkey γ⁻¹ hγinv E hE_le_T hE8 hE_norm).resolve_left (hnot γ⁻¹ hγinv hγinv2 hγinvT)
  have hcomp : (MulAut.conj γ).toMonoidHom.comp (MulAut.conj γ⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  have hE2 : (F1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = E := by
    calc (F1 ⊔ F2).map (MulAut.conj γ).toMonoidHom
        = (E.map (MulAut.conj γ⁻¹).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
          rw [← hE1inv]
      _ = E.map ((MulAut.conj γ).toMonoidHom.comp (MulAut.conj γ⁻¹).toMonoidHom) := by
          rw [Subgroup.map_map]
      _ = E.map (MonoidHom.id G) := by rw [hcomp]
      _ = E := Subgroup.map_id E
  exact ⟨hE1, hE2⟩

end TData

end CFSG.OddStandard.SmallF3.Omega
