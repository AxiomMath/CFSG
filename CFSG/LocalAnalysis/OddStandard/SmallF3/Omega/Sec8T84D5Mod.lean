module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HModel
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def Sec8T84D5Model {G : Type} [Group G] (P : Subgroup G) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate), Module.finrank (ZMod 3) V = 6 ∧
      quadSign Q = -1 ∧ ∃ P' : Subgroup (ProjOrth Q), IsSylow2Of P' (omegaProj hQ) ∧
        Nonempty (↥P ≃* ↥P')

theorem sec8t84d5_model_of_equiv {G : Type} [Group G] {A B : Subgroup G}
    (h : Nonempty (↥A ≃* ↥B)) (hB : Sec8T84D5Model B) : Sec8T84D5Model A := by
  obtain ⟨V, hV1, hV2, hV3, Q, hQ, hdim, hsign, P', hP', ⟨e⟩⟩ := hB
  obtain ⟨f⟩ := h
  exact ⟨V, hV1, hV2, hV3, Q, hQ, hdim, hsign, P', hP', ⟨f.trans e⟩⟩

theorem sec8t84d5_complement_of_model (hMS : Sec8T84ModelSylow) {G : Type} [Group G]
    {S1 E1 : Subgroup G} (hE1 : E1 ≤ S1) (he : IsElemAb2 E1 4) (hn : (E1.subgroupOf S1).Normal)
    (hmod : Sec8T84D5Model S1) : ∃ K : Subgroup G, K ≤ S1 ∧ E1 ⊓ K = ⊥ ∧ E1 ⊔ K = S1 := by
  obtain ⟨V, hV1, hV2, hV3, Q, hQ, hdim, hsign, P', hP', ⟨ψ⟩⟩ := hmod
  letI : AddCommGroup V := hV1
  letI : Module (ZMod 3) V := hV2
  letI : FiniteDimensional (ZMod 3) V := hV3
  have hψinj : Function.Injective (ψ.toMonoidHom : ↥S1 →* ↥P') := ψ.injective
  set B : Subgroup ↥S1 := E1.subgroupOf S1 with hBdef
  have hBnorm : B.Normal := hn
  have hBcard : Nat.card B = Nat.card E1 := by
    rw [hBdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE1).toEquiv
  have hBel : CFSG.Open.IsElemAbelian 2 B := by
    rw [hBdef]
    exact he.1.subgroupOf S1
  have hBe : IsElemAb2 B 4 := ⟨hBel, by rw [hBcard, he.2]⟩
  set Bψ : Subgroup ↥P' := B.map ψ.toMonoidHom with hBψdef
  have hBψel : CFSG.Open.IsElemAbelian 2 Bψ := by
    rw [hBψdef]
    exact hBel.map ψ.toMonoidHom
  have hBψcard : Nat.card Bψ = 2 ^ 4 := by
    rw [hBψdef, Subgroup.card_map_of_injective ψ.injective, hBe.2]
  have hBψnorm : Bψ.Normal := by
    rw [hBψdef]
    exact hBnorm.map ψ.toMonoidHom ψ.surjective
  set B' : Subgroup (ProjOrth Q) := Bψ.map P'.subtype with hB'def
  have hB'le : B' ≤ P' := by
    rw [hB'def]
    exact Subgroup.map_subtype_le Bψ
  have hB'el : CFSG.Open.IsElemAbelian 2 B' := by
    rw [hB'def]
    exact hBψel.map P'.subtype
  have hB'card : Nat.card B' = 2 ^ 4 := by
    rw [hB'def, Subgroup.card_map_of_injective P'.subtype_injective, hBψcard]
  have hB'sub : B'.subgroupOf P' = Bψ := by
    rw [hB'def]
    exact Subgroup.comap_map_eq_self_of_injective P'.subtype_injective Bψ
  have hB'norm : (B'.subgroupOf P').Normal := by
    rw [hB'sub]
    exact hBψnorm
  have hB' : IsNormalE16In P' B' := ⟨hB'le, ⟨hB'el, hB'card⟩, hB'norm⟩
  obtain ⟨D', hD'le, hD'inf, hD'sup⟩ := (hMS V Q hQ hdim hsign P' hP').2 B' hB'
  set Dψ : Subgroup ↥P' := D'.subgroupOf P' with hDψdef
  have hDψmap : Dψ.map P'.subtype = D' := by
    rw [hDψdef]
    exact Subgroup.map_subgroupOf_eq_of_le hD'le
  have hBψmap : Bψ.map P'.subtype = B' := hB'def.symm
  have hBψinfDψ : Bψ ⊓ Dψ = ⊥ := by
    rw [← hB'sub, hDψdef]
    have hcomap : (B'.subgroupOf P') ⊓ (D'.subgroupOf P') = (B' ⊓ D').subgroupOf P' := by
      simp only [Subgroup.subgroupOf]
      exact Subgroup.comap_inf B' D' P'.subtype
    rw [hcomap, hD'inf, Subgroup.bot_subgroupOf]
  have hBψsupDψ : Bψ ⊔ Dψ = ⊤ := by
    apply Subgroup.map_injective P'.subtype_injective
    rw [Subgroup.map_sup, hBψmap, hDψmap, hD'sup, Subgroup.map_top, Subgroup.range_subtype]
  set D : Subgroup ↥S1 := Dψ.comap ψ.toMonoidHom with hDdef
  have hDmap : D.map ψ.toMonoidHom = Dψ := by
    rw [hDdef]
    exact Subgroup.map_comap_eq_self_of_surjective ψ.surjective Dψ
  have hBmap : B.map ψ.toMonoidHom = Bψ := hBψdef
  have hBDinf : B ⊓ D = ⊥ := by
    apply Subgroup.map_injective hψinj
    rw [Subgroup.map_inf_eq _ _ _ hψinj, hBmap, hDmap, hBψinfDψ, Subgroup.map_bot]
  have hBDsup : B ⊔ D = ⊤ := by
    apply Subgroup.map_injective hψinj
    rw [Subgroup.map_sup, hBmap, hDmap, hBψsupDψ,
      Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective]
  have hEmap : B.map S1.subtype = E1 := by
    rw [hBdef]
    exact Subgroup.map_subgroupOf_eq_of_le hE1
  refine ⟨D.map S1.subtype, Subgroup.map_subtype_le D, ?_, ?_⟩
  · rw [← hEmap, ← Subgroup.map_inf_eq _ _ _ S1.subtype_injective, hBDinf, Subgroup.map_bot]
  · rw [← hEmap, ← Subgroup.map_sup, hBDsup, Subgroup.map_top, Subgroup.range_subtype]

end CFSG.OddStandard.SmallF3.Omega
