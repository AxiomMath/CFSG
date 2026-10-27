module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chains

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

@[expose] def KLike (IsK : GroupClass) (X : Subgroup H) : Prop :=
  ∃ (Y : Type) (_ : Group Y) (π : ↥X →* Y), Function.Surjective π ∧ π.ker ≤ center ↥X ∧ IsK Y

@[expose] def GroupClass.IsoInv (C : GroupClass) : Prop :=
  ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → C X → C Y

theorem KLike.of_central_cover {IsK : GroupClass} {K₁ L₁ : Subgroup H} (hK : KLike IsK K₁)
    (hL : Group.IsPerfect ↥L₁) (π : ↥L₁ →* ↥K₁) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center ↥L₁) : KLike IsK L₁ := by
  obtain ⟨Y, _, σ, hσs, hσk, hY⟩ := hK
  refine ⟨Y, inferInstance, σ.comp π, hσs.comp hπ, fun x hx => ?_, hY⟩
  have hσx : π x ∈ σ.ker := by simpa using hx
  have hπx : π x ∈ center ↥K₁ := hσk hσx
  have hZ : ⁅center ↥L₁, (⊤ : Subgroup ↥L₁)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact Subgroup.mem_center_iff.1 hz g
  have hM : ⁅(⊤ : Subgroup ↥L₁), zpowers x⁆ ≤ center ↥L₁ := by
    refine le_trans (Subgroup.commutator_le.2 fun g _ y hy => ?_) hker
    obtain ⟨k, rfl⟩ := hy
    rw [MonoidHom.mem_ker, map_commutatorElement, map_zpow]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_center_iff.1 (zpow_mem hπx k) (π g))
  have h1 : ⁅⁅(⊤ : Subgroup ↥L₁), zpowers x⁆, ⊤⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono hM le_rfl).trans hZ.le)
  have h2 : ⁅⁅zpowers x, (⊤ : Subgroup ↥L₁)⁆, (⊤ : Subgroup ↥L₁)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (zpowers x) (⊤ : Subgroup ↥L₁)]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := (⊤ : Subgroup ↥L₁))
    (H₂ := ⊤) (H₃ := zpowers x) h1 h2
  have hc : ⁅(⊤ : Subgroup ↥L₁), (⊤ : Subgroup ↥L₁)⁆ = (⊤ : Subgroup ↥L₁) := by
    have := Group.isPerfect_def.1 hL
    rwa [_root_.commutator_def] at this
  rw [hc] at h3
  have h4 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3
  rw [Subgroup.mem_center_iff]
  intro g
  exact ((Subgroup.mem_centralizer_iff.1 (h4 (Subgroup.mem_top g)) x (mem_zpowers x))).symm


structure Hyp31Row (IsK IsL : GroupClass) : Prop where
  isK_inv : IsK.IsoInv
  isL_inv : IsL.IsoInv
  quasi_K : ∀ (X : Type) [Group X], IsK X → CFSG.IsQuasisimple X ∧ 3 ≤ CFSG.pRank 2 X
  quasi_L : ∀ (X : Type) [Group X], IsL X →
    CFSG.IsQuasisimple X ∧ center X = CFSG.oddCore X ∧ 3 ≤ CFSG.pRank 2 X
  K_not_exc : ∀ (X : Type) [Group X], IsK X →
    ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f
  K_ne_L : ∀ (X Y : Type) [Group X] [Group Y], IsL X → IsK (Y ⧸ CFSG.oddCore Y) →
    ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y))

structure Sol78Link5bData {H : Type} [Group H] (K₁ L₁ T : Subgroup H) (s : H) : Prop where
  T_two : IsPGroup 2 T
  L_comp : IsCompIn L₁ (centralizer (T : Set H))
  s_two : IsPGroup 2 (zpowers s)
  s_norm : s ∈ normalizer (T : Set H)
  s_sq : s ^ 2 ∈ T
  K_comp : IsCompIn K₁ (centralizer ((T ⊔ zpowers s : Subgroup H) : Set H))
  incl : K₁ ≤ L₁ ⊔ L₁.map (MulAut.conj s).toMonoidHom ∧
    L₁ ⊔ L₁.map (MulAut.conj s).toMonoidHom =
      conjClosure K₁ (layerIn (centralizer (T : Set H)))
  link : Sol78Link5b L₁ K₁ s

structure Hyp31Glob (H : Type) [Group H] [Finite H] (N : Subgroup H) (IsK IsL : GroupClass) :
    Prop where
  fstar : FStarSimple N
  index_le_two : N.index ≤ 2
  type_max : ∀ L₁ : Subgroup H, InL L₁ → IsL ↥L₁ →
    Maximal L₁ ∧ ∃ S : Sylow 2 (centralizer (L₁ : Set H)), IsCyclic ↥S
  not_max : ∀ K₁ : Subgroup H, InL K₁ → KLike IsK K₁ → ∀ G₁ : Subgroup H, N ≤ G₁ →
    ¬ (K₁ ≤ G₁ ∧ Maximal (K₁.subgroupOf G₁))
  desc : ∀ K₁ L₁ : Subgroup H, InL K₁ → KLike IsK K₁ → InL L₁ → ReflTransGen Lt K₁ L₁ →
    (∃ π : ↥L₁ →* ↥K₁, Function.Surjective π ∧ π.ker ≤ center ↥L₁) ∨
      (IsL ↥L₁ ∧ IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁))
  std_in : ∀ (K₁ L₁ T : Subgroup H) (s : H), T ≠ ⊥ → Maximal L₁ → Sol78Link5bData K₁ L₁ T s →
    IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) →
      SolStd (K₁.subgroupOf L₁) ∧ twoAdic (autCentralizer L₁ K₁) ≤ 2

structure Hyp31 (H : Type) [Group H] [Finite H] (N : Subgroup H) (IsK IsL : GroupClass) :
    Prop extends Hyp31Row IsK IsL, Hyp31Glob H N IsK IsL

end CFSG.EvenSporadicStandard.Induction
