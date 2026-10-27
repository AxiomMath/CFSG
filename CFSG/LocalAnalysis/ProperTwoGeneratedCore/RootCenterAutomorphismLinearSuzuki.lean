module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismLinearKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismSuzuki

public section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.LinearModel
open CFSG.ShultStronglyClosedTI.SuzukiModel CFSG.ShultStronglyClosedTI.SuzukiLayerKernel
open CFSG.BenderSuzuki.MatrixGroups

universe u

theorem linear_rootCenterAutomorphisms_of_mulEquiv {G : Type*} [Group G] {K : Type u} [Field K]
    [Finite K] {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f) (e : G ≃* PSL2MatrixGroup K)
    (R : Sylow 2 G) :
    (R : Subgroup G) = (CFSG.omega₁ (G := (R : Subgroup G)) (p := 2)).map
        (R : Subgroup G).subtype ∧ Nat.card R = 2 ^ f ∧
      RootCenterAutomorphisms (R : Subgroup G)
        ((CFSG.omega₁ (G := (R : Subgroup G)) (p := 2)).map (R : Subgroup G).subtype) (2 ^ f) := by
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨T, β, h, hfaith⟩ := linearPointAction_cosets_of_mulEquiv hcard e R
  have hUR := map_omega₁_eq_of_isElemAbelian h.isElemAbelian
  have : MulAction.IsMultiplyPretransitive G
      (G ⧸ Subgroup.normalizer ((R : Subgroup G) : Set G)) 2 := h.isMultiplyPretransitive
  have : MulAction.IsPretransitive G (G ⧸ Subgroup.normalizer ((R : Subgroup G) : Set G)) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hcomm : ∀ x ∈ (R : Subgroup G), ∀ y ∈ (R : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨hUR.symm, h.card_U, ?_⟩
  rw [hUR]
  have haut : {γ : MulAut G | (R : Subgroup G).map γ.toMonoidHom = R ∧
      ∀ u ∈ (R : Subgroup G), γ u = u} = ((R : Subgroup G).map MulAut.conj : Set (MulAut G)) := by
    ext γ
    refine ⟨fun ⟨hγR, hγU⟩ => ?_, ?_⟩
    · obtain ⟨b, hb, hγb⟩ := linear_rank_one_Sylow_layer_kernel_of_mulEquiv hf hcard e R R
        hUR.symm γ hγR hγU (fun x hx => by rw [hγU x hx, inv_mul_cancel]; exact one_mem _)
      exact ⟨b, hb, hγb.symm⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨map_conj_of_mem hr, fun u hu => by
        rw [MulAut.conj_apply, hcomm r hr u hu, mul_inv_cancel_right]⟩
  apply RootCenterAutomorphisms.of_core (fun x => ⟨fun hx => ⟨hx, fun y hy => hcomm x hx y hy⟩,
      fun hx => hx.1⟩) (isElementaryAbelian_of_isElemAbelian h.isElemAbelian) h.card_U
    (fun x hx => by rw [h.isElemAbelian.2 x hx]; exact one_mem _)
    (injOn_conj_of_le_stabilizer h.le_stabilizer_left) haut
  intro R₀ hUR₀ hR₀R _
  obtain rfl : R₀ = R := le_antisymm hR₀R hUR₀
  rw [← haut]
  ext γ
  exact ⟨fun hγ => hγ.1, fun hγ => ⟨hγ, hγ.2⟩⟩

theorem suzuki_rootCenterAutomorphisms_of_mulEquiv
    {G : Type*} [Group G] {a : ℕ} {K : Type}
    [Field K] [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : G ≃* suzukiGroup a K) (R : Sylow 2 G) :
    Nat.card R = (2 ^ (2 * a + 1)) ^ 2 ∧
      RootCenterAutomorphisms (R : Subgroup G)
        ((CFSG.omega₁ (G := (R : Subgroup G)) (p := 2)).map (R : Subgroup G).subtype)
        (2 ^ (2 * a + 1)) := by
  set P : Sylow 2 (suzukiGroup a K) :=
    (suzukiU_isPGroup_index hK).1.toSylow (suzukiU_isPGroup_index hK).2
  have hP : RootCenterAutomorphisms (P : Subgroup (suzukiGroup a K))
      ((CFSG.omega₁ (G := (P : Subgroup (suzukiGroup a K))) (p := 2)).map
        (P : Subgroup (suzukiGroup a K)).subtype) (2 ^ (2 * a + 1)) := by
    change RootCenterAutomorphisms (suzukiU a K)
      ((CFSG.omega₁ (G := suzukiU a K) (p := 2)).map (suzukiU a K).subtype) _
    rw [map_omega₁_suzukiU hK]
    exact suzukiU_rootCenterAutomorphisms ha hK
  refine ⟨?_, hP.of_sylow e P R⟩
  obtain ⟨ε, hε⟩ := exists_mulEquiv_map_eq e P R
  rw [← hε, Subgroup.card_map_of_injective ε.injective]
  exact (suzuki_unipotent_structure hK).2.1

theorem linear_Suzuki_root_center_automorphisms_and_large_root_centralizers :
    (∀ (K : Type u) [Field K] [Finite K] (f : ℕ), 2 ≤ f → Nat.card K = 2 ^ f →
      ∀ R : Sylow 2 (PSL2MatrixGroup K),
        (R : Subgroup (PSL2MatrixGroup K)) =
            (CFSG.omega₁ (G := (R : Subgroup (PSL2MatrixGroup K))) (p := 2)).map
              (R : Subgroup (PSL2MatrixGroup K)).subtype ∧
          Nat.card R = 2 ^ f ∧
          RootCenterAutomorphisms (R : Subgroup (PSL2MatrixGroup K))
            ((CFSG.omega₁ (G := (R : Subgroup (PSL2MatrixGroup K))) (p := 2)).map
              (R : Subgroup (PSL2MatrixGroup K)).subtype) (2 ^ f)) ∧
    ∀ (a : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) →
      ∀ R : Sylow 2 (suzukiGroup a K),
        Nat.card R = (2 ^ (2 * a + 1)) ^ 2 ∧
          RootCenterAutomorphisms (R : Subgroup (suzukiGroup a K))
            ((CFSG.omega₁ (G := (R : Subgroup (suzukiGroup a K))) (p := 2)).map
              (R : Subgroup (suzukiGroup a K)).subtype) (2 ^ (2 * a + 1)) :=
  ⟨fun _ _ _ _ hf hcard R => linear_rootCenterAutomorphisms_of_mulEquiv hf hcard
      (MulEquiv.refl _) R,
    fun _ _ _ _ ha hK R => suzuki_rootCenterAutomorphisms_of_mulEquiv ha hK (MulEquiv.refl _) R⟩

theorem linear_rootCenterAutomorphisms_of_mulEquiv_psl2Binary {G : Type*} [Group G] {f : ℕ}
    (hf : 2 ≤ f) (e : G ≃* PSL2BinaryMatrixGroup f) (R : Sylow 2 G) :
    (R : Subgroup G) = (CFSG.omega₁ (G := (R : Subgroup G)) (p := 2)).map
        (R : Subgroup G).subtype ∧ Nat.card R = 2 ^ f ∧
      RootCenterAutomorphisms (R : Subgroup G)
        ((CFSG.omega₁ (G := (R : Subgroup G)) (p := 2)).map (R : Subgroup G).subtype) (2 ^ f) :=
  linear_rootCenterAutomorphisms_of_mulEquiv hf (GaloisField.card 2 f (by omega)) e R

theorem suzuki_rootCenterAutomorphisms_of_mulEquiv_suzukiMatrixGroup
    {G : Type*} [Group G]
    {m : ℕ} (hm : 1 ≤ m) (e : G ≃* SuzukiMatrixGroup m) (R : Sylow 2 G) :
    Nat.card R = (2 ^ (2 * m + 1)) ^ 2 ∧
      RootCenterAutomorphisms (R : Subgroup G)
        ((CFSG.omega₁ (G := (R : Subgroup G)) (p := 2)).map (R : Subgroup G).subtype)
        (2 ^ (2 * m + 1)) :=
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  suzuki_rootCenterAutomorphisms_of_mulEquiv hm hK
    (e.trans (suzukiGroupEquivSuzukiMatrixGroup hK).symm) R

end CFSG.ProperTwoGeneratedCore.RootCenter
