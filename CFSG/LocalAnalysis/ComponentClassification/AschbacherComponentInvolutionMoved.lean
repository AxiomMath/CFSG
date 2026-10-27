module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionDiagonal
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionNormalization

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentInvolution

open CFSG.Open
open AschbacherComponentAction

variable {G : Type*} [Group G] [Finite G]

theorem layer_normalizes_component_join (L M : Subgroup G)
    (hL : IsComponentOf L ⊤) (hM : IsComponentOf M ⊤) :
    Layer.subgroup G ≤ Subgroup.normalizer ((L ⊔ M : Subgroup G) : Set G) := by
  have hNL := (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Layer.component_le hL)).mp (Layer.normal_component hL)
  have hNM := (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Layer.component_le hM)).mp (Layer.normal_component hM)
  intro e he
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNL he),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNM he)]

theorem component_join_subnormal (L M : Subgroup G)
    (hL : IsComponentOf L ⊤) (hM : IsComponentOf M ⊤) :
    (L ⊔ M).IsSubnormal := by
  let E := Layer.subgroup G
  have hPE : L ⊔ M ≤ E := sup_le (Layer.component_le hL) (Layer.component_le hM)
  have hnormal : ((L ⊔ M).subgroupOf E).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (layer_normalizes_component_join L M hL hM)
  exact hnormal.isSubnormal.trans hPE (Layer.normal G).isSubnormal

theorem moved_derived_centralizer_component (L : Subgroup G) (a : G)
    (hL : IsComponentOf L ⊤) (ha : orderOf a = 2)
    (hmoved : rightComponent L a ≠ L) :
    IsComponentOf
      ((⁅⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G),
        ⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G)⁆).subgroupOf
          (Subgroup.centralizer ({a} : Set G))) ⊤ := by
  let C := Subgroup.centralizer ({a} : Set G)
  let P := L ⊔ rightComponent L a
  have hsquare := InvolutionLayer.involution_square a ha
  have hinvolutive : Function.Involutive (MulAut.conj a) :=
    fun x => involution_conjugation_twice a x hsquare
  have hcommutes : ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ = ⊥ := by
    rw [← rightComponent_involution L a hsquare]
    exact moved_component_commutes L a hL hmoved
  have hlocal := SwappedQuasisimpleProduct.diagonal_component_of_product_fixed
    L hL.2.2 (MulAut.conj a) hinvolutive hcommutes
  rw [fixed_conjugation_eq_centralizer,
    ← rightComponent_involution L a hsquare,
    ← moved_component_derived_centralizer L a hL ha hmoved hcommutes] at hlocal
  have hsubnormal : ((P ⊓ C).subgroupOf C).IsSubnormal := by
    have h := (component_join_subnormal L (rightComponent L a) hL
      (rightComponent_component L hL a)).comap C.subtype
    have heq : (P ⊓ C).subgroupOf C = P.comap C.subtype := by
      ext x
      change (x.val ∈ P ∧ x.val ∈ C) ↔ x.val ∈ P
      exact and_iff_left x.property
    rw [heq]
    exact h
  have hderivedLe : ⁅⁅L, Subgroup.zpowers a⁆ ⊓ C,
      ⁅L, Subgroup.zpowers a⁆ ⊓ C⁆ ≤ P ⊓ C := by
    rw [moved_component_commutator L a hL hsquare hmoved]
    exact Subgroup.commutator_le_self _
  exact OrdinaryComponentTransport.extend_nested _ (P ⊓ C) C hderivedLe
    inf_le_right hsubnormal hlocal

omit [Finite G] in
theorem centralizes_diagonal_centralizes_factor (L K : Subgroup G) [Group.IsPerfect L]
    (a : G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hKN : K ≤ Subgroup.normalizer (L : Set G))
    (hcommutes : ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ = ⊥)
    (hdiagonal : ⁅K, (InvolutionDiagonal.homomorphism L (MulAut.conj a) hcommutes).range⁆ = ⊥) :
    ⁅K, L⁆ = ⊥ := by
  let M := L.map (MulAut.conj a).toMonoidHom
  have hcentral : L ⊓ M ≤ Subgroup.centralizer (L : Set G) :=
    inf_le_right.trans (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes))
  have hdisplacement : ⁅K, L⁆ ≤ L ⊓ M := by
    apply Subgroup.commutator_le.mpr
    intro k hk l hl
    have hconjL : k * l * k⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hKN hk) l).mp hl
    have hkCommutes := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
    have hconjM : k * (MulAut.conj a l) * k⁻¹ ∈ M := by
      have heq : k * (MulAut.conj a l) * k⁻¹ = MulAut.conj a (k * l * k⁻¹) := by
        simp only [MulAut.conj_apply]
        have hkInv : a⁻¹ * k⁻¹ = k⁻¹ * a⁻¹ := by
          simpa only [mul_inv_rev] using congrArg Inv.inv hkCommutes
        calc
          k * (a * l * a⁻¹) * k⁻¹ = (k * a) * l * (a⁻¹ * k⁻¹) := by group
          _ = (a * k) * l * (k⁻¹ * a⁻¹) := by rw [hkCommutes, hkInv]
          _ = a * (k * l * k⁻¹) * a⁻¹ := by group
      rw [heq]
      exact Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hconjL
    have hfixed : k * (l * MulAut.conj a l) = (l * MulAut.conj a l) * k :=
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hdiagonal hk)
          (l * MulAut.conj a l) ⟨⟨l, hl⟩, rfl⟩).symm
    have hproduct : (k * l * k⁻¹) * (k * (MulAut.conj a l) * k⁻¹) =
        l * MulAut.conj a l := by
      calc
        _ = (k * (l * MulAut.conj a l)) * k⁻¹ := by group
        _ = ((l * MulAut.conj a l) * k) * k⁻¹ := by rw [hfixed]
        _ = l * MulAut.conj a l := by group
    have hmiddleMem : MulAut.conj a l * (k * (MulAut.conj a l) * k⁻¹)⁻¹ ∈ M :=
      M.mul_mem (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hl)
        (M.inv_mem hconjM)
    have hmiddleCommute : l * (MulAut.conj a l * (k * (MulAut.conj a l) * k⁻¹)⁻¹) =
        (MulAut.conj a l * (k * (MulAut.conj a l) * k⁻¹)⁻¹) * l :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.le_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes) hmiddleMem) l hl
    have hcentralMove : k * l * k⁻¹ * l⁻¹ =
        MulAut.conj a l * (k * (MulAut.conj a l) * k⁻¹)⁻¹ := by
      calc
        _ = ((k * l * k⁻¹) * (k * (MulAut.conj a l) * k⁻¹)) *
            (k * (MulAut.conj a l) * k⁻¹)⁻¹ * l⁻¹ := by group
        _ = (l * MulAut.conj a l) *
            (k * (MulAut.conj a l) * k⁻¹)⁻¹ * l⁻¹ := by rw [hproduct]
        _ = (l * (MulAut.conj a l * (k * (MulAut.conj a l) * k⁻¹)⁻¹)) * l⁻¹ := by group
        _ = ((MulAut.conj a l * (k * (MulAut.conj a l) * k⁻¹)⁻¹) * l) * l⁻¹ := by
          rw [hmiddleCommute]
        _ = MulAut.conj a l * (k * (MulAut.conj a l) * k⁻¹)⁻¹ := by group
    change k * l * k⁻¹ * l⁻¹ ∈ L ⊓ M
    refine ⟨L.mul_mem hconjL (L.inv_mem hl), ?_⟩
    rw [hcentralMove]
    exact hmiddleMem
  have hdouble : ⁅⁅L, K⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L K]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hdisplacement.trans hcentral)
  rw [Subgroup.commutator_comm K L]
  exact Quasisimple.perfect_double_commutator L K hdouble

theorem centralized_component_alternative (a : G) (K L : Subgroup G)
    (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (hL : IsComponentOf L ⊤) (hcentral : a ∈ Subgroup.centralizer (L : Set G)) :
    K = L ∨ ⁅K, L⁆ = ⊥ := by
  have hLC : L ≤ Subgroup.centralizer ({a} : Set G) := by
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcentral l hl)
  by_cases hKL : K = L
  · exact Or.inl hKL
  · exact Or.inr (OrdinaryComponentTransport.commute_local_distinct K L _ hKC hLC hK
      (LocalComponents.of_overgroup hL hLC) hKL)

theorem moved_component_alternative (a : G) (ha : orderOf a = 2)
    (K L : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsComponentOf (K.subgroupOf (Subgroup.centralizer ({a} : Set G))) ⊤)
    (hL : IsComponentOf L ⊤) (hmoved : rightComponent L a ≠ L) :
    ⁅K, L⁆ = ⊥ ∨
      K = ⁅⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G),
        ⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G)⁆ := by
  let D := ⁅⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G),
    ⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G)⁆
  have hDC : D ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.commutator_le_self _).trans inf_le_right
  by_cases heq : K = D
  · exact Or.inr heq
  · left
    let : Group.IsPerfect L := ⟨hL.2.2.1⟩
    have hKD := OrdinaryComponentTransport.commute_local_distinct K D _ hKC hDC hK
      (moved_derived_centralizer_component L a hL ha hmoved) heq
    have hsquare := InvolutionLayer.involution_square a ha
    have hcommutes : ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ = ⊥ := by
      rw [← rightComponent_involution L a hsquare]
      exact moved_component_commutes L a hL hmoved
    change ⁅K, ⁅⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G),
      ⁅L, Subgroup.zpowers a⁆ ⊓ Subgroup.centralizer ({a} : Set G)⁆⁆ = ⊥ at hKD
    rw [moved_component_derived_centralizer L a hL ha hmoved hcommutes] at hKD
    exact centralizes_diagonal_centralizes_factor L K a hKC
      (involution_component_normalizes a ha K hKC hK L hL) hcommutes hKD

end CFSG.ComponentClassification.AschbacherComponentInvolution
