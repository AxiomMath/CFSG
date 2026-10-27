module

public import CFSG.LinearAlgebra.CoprimeActions.CommSpaceSubrepresentation

public section

namespace CFSG.LinearAlgebra.CoprimeActions.HyperplaneDecompositionOnCommSpace

open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations CFSG.LinearAlgebra.CoprimeActions.CommSpaceSubrepresentation

@[expose] def toTop {G : Type} [Group G] (p : ℕ) (K : Subgroup G) (D : hyperplanes p K) :
    hyperplanes p (⊤ : Subgroup K) :=
  ⟨D.1.subgroupOf K, le_top, by rw [Subgroup.relIndex_top_right]; exact D.2.2⟩

theorem toTop_bijective {G : Type} [Group G] (p : ℕ) (K : Subgroup G) :
    Function.Bijective (toTop p K) := by
  constructor
  · intro D D' h
    have h' : D.1.subgroupOf K = D'.1.subgroupOf K := congrArg Subtype.val h
    apply Subtype.ext
    rw [← Subgroup.map_subgroupOf_eq_of_le D.2.1, h', Subgroup.map_subgroupOf_eq_of_le D'.2.1]
  · rintro ⟨E, -, hE⟩
    have this : (E.map K.subtype).subgroupOf K = E :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective E
    refine ⟨⟨E.map K.subtype, Subgroup.map_subtype_le E, ?_⟩, ?_⟩
    · unfold Subgroup.relIndex
      rw [this]
      rwa [Subgroup.relIndex_top_right] at hE
    · exact Subtype.ext this

theorem decomposition {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (K Z : Subgroup G) (hK : CFSG.Open.IsElemAbelian p K) (hZK : Z ≤ K)
    (hcentral : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) (hodd : Odd (Nat.card Z)) :
    open scoped Classical in
    iSupIndep (fun D : hyperplanes p K => commSpace ρ Z ⊓ fixedSpace ρ D.1) ∧
      (⨆ D : hyperplanes p K, commSpace ρ Z ⊓ fixedSpace ρ D.1) = commSpace ρ Z := by
  classical
  haveI : Finite K := inferInstance
  have hpq : p ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.2 hp) even_two
  let σ := restrictedRepresentation ρ K Z hcentral
  have hTop : CFSG.Open.IsElemAbelian p (⊤ : Subgroup K) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · exact Subtype.ext (hK.1.is_comm.comm a.1 b.1)
    · exact Subtype.ext (hK.2 x.1 x.2)
  have hV : commSpace σ (⊤ : Subgroup K) = ⊤ :=
    commSpace_restrictedRepresentation_top ρ K Z hcentral hodd hZK
  have hind := iSupIndep_fixedSpace hpq σ ⊤ hTop hV
  have hsup := iSup_fixedSpace_hyperplanes hpq σ ⊤ hTop hV
  set e := toTop_bijective p K
  have hg : ∀ D : hyperplanes p K, fixedSpace σ (D.1.subgroupOf K) =
      Submodule.comap (commSpace ρ Z).subtype (commSpace ρ Z ⊓ fixedSpace ρ D.1) :=
    fun D => fixedSpace_restrictedRepresentation ρ K Z hcentral D.1 D.2.1
  have hmap : ∀ D : hyperplanes p K,
      Submodule.map (commSpace ρ Z).subtype (fixedSpace σ (D.1.subgroupOf K)) =
        commSpace ρ Z ⊓ fixedSpace ρ D.1 := fun D => by
    rw [hg, Submodule.map_comap_subtype]; simp
  constructor
  · have h1 := hind.comp e.1
    have h2 := LinearMap.iSupIndep_map (commSpace ρ Z).subtype (commSpace ρ Z).injective_subtype h1
    convert h2 using 1
    funext D
    exact (hmap D).symm
  · have h3 : (⨆ D : hyperplanes p K, fixedSpace σ (D.1.subgroupOf K)) = ⊤ := by
      rw [← hsup]
      apply le_antisymm
      · exact iSup_le fun D => le_iSup (fun E : hyperplanes p (⊤ : Subgroup K) => fixedSpace σ E.1)
          (toTop p K D)
      · exact iSup_le fun E => by
          obtain ⟨D, hD⟩ := e.2 E
          rw [← hD]
          exact le_iSup (fun D : hyperplanes p K => fixedSpace σ (D.1.subgroupOf K)) D
    calc (⨆ D : hyperplanes p K, commSpace ρ Z ⊓ fixedSpace ρ D.1)
        = ⨆ D : hyperplanes p K, Submodule.map (commSpace ρ Z).subtype
            (fixedSpace σ (D.1.subgroupOf K)) := by simp only [hmap]
      _ = Submodule.map (commSpace ρ Z).subtype (⨆ D : hyperplanes p K,
            fixedSpace σ (D.1.subgroupOf K)) := (Submodule.map_iSup _ _).symm
      _ = commSpace ρ Z := by rw [h3, Submodule.map_subtype_top]

end CFSG.LinearAlgebra.CoprimeActions.HyperplaneDecompositionOnCommSpace
