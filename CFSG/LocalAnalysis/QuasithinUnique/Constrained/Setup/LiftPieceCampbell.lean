module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate6

public section

namespace CFSG.QuasithinUnique.Setup.Lift.Piece

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Wreath CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

theorem slPerm_apply_mulVec' {k : Type*} [Field k] (A : Matrix.SpecialLinearGroup (Fin 2) k)
    (w : Fin 2 → k) : slPerm k A w = (A : Matrix (Fin 2) (Fin 2) k).mulVec w := by
  rw [slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
  rfl

theorem natQuotSetting_of_module {G : Type} [Group G] {k : Type} [Field k]
    {S P M W : Subgroup G} (hSyl : IsSylowTwoOf S P) (hnn : ¬ (S.subgroupOf P).Normal)
    (hSM : S ≤ M) (hMP : ¬ P ≤ M) (hmax : ∀ Y : Subgroup G, S ≤ Y → Y < P → Y ≤ M)
    (hred : IsTwoReducedIn P W) (ϱ : ↥P →* Matrix.SpecialLinearGroup (Fin 2) k)
    (hϱ : Function.Surjective ϱ) (ψ : ↥W →* Multiplicative (Fin 2 → k))
    (hψ : Function.Surjective ψ)
    (hψϱ : ∀ (p : ↥P) (v v' : ↥W), (v' : G) = (p : G) * (v : G) * (p : G)⁻¹ →
      Multiplicative.toAdd (ψ v') =
        (ϱ p : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (ψ v)))
    (hψker : ψ.ker = (Subgroup.centralizer (oddOrderSubgroup P : Set G)).subgroupOf W) :
    ∃ (ϱ' : ↥P →* Gamma k) (φ : ↥(W.subgroupOf P) →* Multiplicative (Fin 2 → k)),
      IsNatQuotSetting (S.subgroupOf P) (M.subgroupOf P) (W.subgroupOf P) ϱ' φ := by
  classical
  have hSP : S ≤ P := hSyl.1
  have hVP : W ≤ P := hred.1
  let ρ' : ↥P →* Gamma k :=
    ((slGamma k).subtype.comp (slGammaEquiv k).toMonoidHom).comp ϱ
  have hρ'apply : ∀ p : ↥P, ((ρ' p : Gamma k) : Equiv.Perm (Fin 2 → k)) = slPerm k (ϱ p) :=
    fun p => rfl
  let e : ↥(W.subgroupOf P) ≃* ↥W := Subgroup.subgroupOfEquivOfLe hVP
  let φ : ↥(W.subgroupOf P) →* Multiplicative (Fin 2 → k) := ψ.comp e.toMonoidHom
  refine ⟨ρ', φ, ?_⟩
  refine
    { sylow := Layer.isSylowTwoOf_subgroupOf_top' hSyl
      nonnormal := fun hn => hnn hn
      le_M := fun x hx => Subgroup.mem_subgroupOf.mpr (hSM (Subgroup.mem_subgroupOf.mp hx))
      M_lt := ?_
      M_max := ?_
      reduced := isTwoReducedIn_top_of hred
      sl_le := ?_
      two_quot := ?_
      φ_surj := hψ.comp e.surjective
      φ_equiv := ?_
      φ_ker := ?_ }
  · refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hPK : P ≤ M := fun x hx =>
      Subgroup.mem_subgroupOf.mp (show (⟨x, hx⟩ : ↥P) ∈ M.subgroupOf P by rw [htop]; trivial)
    exact hMP hPK
  · intro Y hRY hY
    have hRY' : S ≤ Y.map P.subtype := by
      have := Subgroup.map_mono (f := P.subtype) hRY
      rwa [Subgroup.map_subgroupOf_eq_of_le hSP] at this
    have hYP : Y.map P.subtype < P := by
      refine lt_of_le_of_ne (map_subtype_le_self Y) fun heq => ?_
      apply (lt_top_iff_ne_top.mp hY)
      refine top_unique fun x _ => ?_
      have hx : (x : G) ∈ Y.map P.subtype := by rw [heq]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hmax _ hRY' hYP ⟨y, hy, rfl⟩)
  · intro A
    obtain ⟨p, hp⟩ := hϱ A
    exact ⟨p, by rw [hρ'apply, hp]⟩
  · intro p
    exact ⟨0, by rw [pow_zero, pow_one]; exact (slGammaEquiv k (ϱ p)).2⟩
  · intro p v v' hv'
    have h1 := hψϱ p (e v) (e v') (by exact congrArg Subtype.val hv')
    rw [hρ'apply, slPerm_apply_mulVec']
    exact h1
  · ext v
    have hL : (oddOrderSubgroup (⊤ : Subgroup ↥P)) = (oddOrderSubgroup P).subgroupOf P := by
      rw [← oddOrderSubgroup_top_map P]
      exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm
    rw [hL, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hv
      have h1 : e v ∈ ψ.ker := hv
      rw [hψker, Subgroup.mem_subgroupOf] at h1
      exact (mem_centralizer_subgroupOf_iff (oddOrderSubgroup_le P) (v : ↥P)).mpr h1
    · intro hv
      show e v ∈ ψ.ker
      rw [hψker, Subgroup.mem_subgroupOf]
      exact (mem_centralizer_subgroupOf_iff (oddOrderSubgroup_le P) (v : ↥P)).mp hv

end CFSG.QuasithinUnique.Setup.Lift.Piece
