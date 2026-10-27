module

public import CFSG.CGT.PushingUpLit.SolK.Defs
public import CFSG.CGT.PushingUpLit.SolK.Block

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin.G6
  Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G]

structure ModData (G : Type) [Group G] (X : Subgroup G) (n : ℕ) where
  W : Subgroup G
  ρ : ↥X →* Perm (Fin (2 * n + 1))
  β : ↥W ≃* ↥(coreMod (2 * n + 1))
  ρ_alt : ∀ x, ρ x ∈ alternatingGroup (Fin (2 * n + 1))
  ρ_surj : ∀ a ∈ alternatingGroup (Fin (2 * n + 1)), ∃ x, ρ x = a
  equivar : ∀ (x : ↥X) (w : ↥W) (h : (x : G) * (w : G) * (x : G)⁻¹ ∈ W),
    β ⟨(x : G) * (w : G) * (x : G)⁻¹, h⟩ = coreAct (2 * n + 1) (ρ x) (β w)
  ker : ∀ x : ↥X, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 X
  W_eq : W = ⁅pCoreOf 2 X, X⁆
  W_comm_Y : ∀ w ∈ W, ∀ y ∈ pCoreOf 2 X, w * y = y * w

variable {X : Subgroup G} {n : ℕ} (D : ModData G X n)

namespace ModData

theorem comm {w w' : G} (hw : w ∈ D.W) (hw' : w' ∈ D.W) : w * w' = w' * w := by
  have h : D.β (⟨w, hw⟩ * ⟨w', hw'⟩) = D.β (⟨w', hw'⟩ * ⟨w, hw⟩) := by
    rw [map_mul, map_mul]
    exact mul_comm _ _
  exact congrArg Subtype.val (D.β.injective h)

theorem sq {w : G} (hw : w ∈ D.W) : w ^ 2 = 1 := by
  have h : D.β (⟨w, hw⟩ ^ 2) = D.β 1 := by
    rw [map_pow, map_one]
    refine vcoord_ext fun i => ?_
    rw [pow_two, vcoord_mul, vcoord_one]
    exact CharTwo.add_self_eq_zero _
  exact congrArg Subtype.val (D.β.injective h)

end ModData

theorem mem_map_subtype_iff {K : Subgroup ↥X} {x : ↥X} : (x : G) ∈ K.map X.subtype ↔ x ∈ K :=
  Subgroup.mem_map_iff_mem X.subtype_injective

variable [Finite G]

theorem exists_modData (hL : IsShortGroup ↥X) (hn : 2 ≤ n) (hnat : IsNaturalAltModule ↥X n) :
    Nonempty (ModData G X n) := by
  classical
  obtain ⟨B⟩ := exists_altBlockData hL hn hnat
  let U : Subgroup ↥X := shortU ↥X
  let W : Subgroup G := U.map X.subtype
  let eW : ↥U ≃* ↥W := Subgroup.equivMapOfInjective U X.subtype X.subtype_injective
  have heW : ∀ u : ↥U, ((eW u : ↥W) : G) = ((u : ↥X) : G) := fun u => rfl
  refine ⟨{ W := W
            ρ := B.ρ
            β := eW.symm.trans B.β
            ρ_alt := B.ρ_alt
            ρ_surj := B.ρ_surj
            equivar := ?_
            ker := ?_
            W_eq := ?_
            W_comm_Y := ?_ }⟩
  · intro x w h
    obtain ⟨u, rfl⟩ := eW.surjective w
    have hxu : (x * (u : ↥X) * x⁻¹ : ↥X) ∈ U := by
      obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.1 h
      have : v = x * (u : ↥X) * x⁻¹ := X.subtype_injective (by rw [hvx]; rfl)
      rwa [← this]
    have h1 : (⟨(x : G) * ((eW u : ↥W) : G) * (x : G)⁻¹, h⟩ : ↥W) =
        eW ⟨x * (u : ↥X) * x⁻¹, hxu⟩ := Subtype.ext rfl
    show B.β (eW.symm ⟨(x : G) * ((eW u : ↥W) : G) * (x : G)⁻¹, h⟩) = _
    rw [h1, MulEquiv.symm_apply_apply]
    show B.β ⟨x * (u : ↥X) * x⁻¹, hxu⟩ = coreAct (2 * n + 1) (B.ρ x) (B.β (eW.symm (eW u)))
    rw [MulEquiv.symm_apply_apply]
    exact B.equivar x u hxu
  · intro x
    rw [pCoreOf_eq_map, mem_map_subtype_iff, ← B.ker_ρ, MonoidHom.mem_ker]
  · show U.map X.subtype = ⁅pCoreOf 2 X, X⁆
    rw [pCoreOf_eq_map]
    have h1 : (shortU ↥X).map X.subtype =
        ⁅(CFSG.pCore 2 ↥X).map X.subtype, (⊤ : Subgroup ↥X).map X.subtype⁆ := by
      unfold shortU
      exact Subgroup.map_commutator _ _ _
    rw [Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1
  · intro w hw y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
    rw [pCoreOf_eq_map] at hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
    have := shortU_comm_pCore hL hu hv
    exact congrArg Subtype.val this

end CFSG.CGT.PushingUpLit.SolK
