module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeavesAmal
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessA
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieModel

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def DCProp {G : Type} [Group G] (A B : Subgroup G) : Prop :=
  ∀ σ : MulAut ↥(A ⊓ B),
    (∀ b : ↥(A ⊓ B), (b : G) ∈ pCoreOf 2 A ↔ ((σ b : ↥(A ⊓ B)) : G) ∈ pCoreOf 2 A) →
      ∃ (a₁ : MulAut ↥A) (a₂ : MulAut ↥B),
        (∀ m : ↥A, (m : G) ∈ B ↔ ((a₁ m : ↥A) : G) ∈ B) ∧
        (∀ m : ↥B, (m : G) ∈ A ↔ ((a₂ m : ↥B) : G) ∈ A) ∧
        ∀ (b : ↥(A ⊓ B)) (m₁ : ↥A) (m₂ : ↥B), (m₁ : G) = b →
          ((a₁ m₁ : ↥A) : G) = (m₂ : G) → ((a₂ m₂ : ↥B) : G) = ((σ b : ↥(A ⊓ B)) : G)

@[expose] def DCStd (F : Type) [Field F] [Finite F] [CharP F 2] : Prop :=
  DCProp (Ln F) (Pt F)

@[expose] def DCStdSwap (F : Type) [Field F] [Finite F] [CharP F 2] : Prop :=
  DCProp (Pt F) (Ln F)

theorem dcProp_of_map {G P : Type} [Group G] [Group P] (E : G ≃* P) (A B : Subgroup G)
    (h : DCProp (A.map E.toMonoidHom) (B.map E.toMonoidHom)) : DCProp A B := by
  intro σ hσ
  have hmap : ∀ (S : Subgroup G) (x : G), E x ∈ S.map E.toMonoidHom ↔ x ∈ S := fun S x => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  let eA : ↥A ≃* ↥(A.map E.toMonoidHom) := E.subgroupMap A
  let eB : ↥B ≃* ↥(B.map E.toMonoidHom) := E.subgroupMap B
  let eI : ↥(A ⊓ B) ≃* ↥(A.map E.toMonoidHom ⊓ B.map E.toMonoidHom) :=
    (E.subgroupMap (A ⊓ B)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_inf_eq A B E.toMonoidHom E.injective))
  have hcA : ∀ x : ↥A, ((eA x : ↥(A.map E.toMonoidHom)) : P) = E x := fun x => rfl
  have hcB : ∀ x : ↥B, ((eB x : ↥(B.map E.toMonoidHom)) : P) = E x := fun x => rfl
  have hcI : ∀ x : ↥(A ⊓ B),
      ((eI x : ↥(A.map E.toMonoidHom ⊓ B.map E.toMonoidHom)) : P) = E x := fun x => rfl
  let σ' : MulAut ↥(A.map E.toMonoidHom ⊓ B.map E.toMonoidHom) := eI.symm.trans (σ.trans eI)
  have hσ'eq : ∀ x : ↥(A ⊓ B), σ' (eI x) = eI (σ x) := fun x => by
    simp only [σ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hσ' : ∀ b' : ↥(A.map E.toMonoidHom ⊓ B.map E.toMonoidHom),
      (b' : P) ∈ pCoreOf 2 (A.map E.toMonoidHom) ↔
        ((σ' b' : ↥(A.map E.toMonoidHom ⊓ B.map E.toMonoidHom)) : P) ∈
          pCoreOf 2 (A.map E.toMonoidHom) := by
    intro b'
    obtain ⟨b, rfl⟩ := eI.surjective b'
    have hc : ∀ x : G, E x ∈ pCoreOf 2 (A.map E.toMonoidHom) ↔ x ∈ pCoreOf 2 A := fun x => by
      rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 E A]
      exact hmap (pCoreOf 2 A) x
    rw [hσ'eq b, hcI, hcI]
    exact (hc _).trans ((hσ b).trans (hc _).symm)
  obtain ⟨a₁', a₂', hm1, hm2, hc'⟩ := h σ' hσ'
  let a₁ : MulAut ↥A := eA.trans (a₁'.trans eA.symm)
  let a₂ : MulAut ↥B := eB.trans (a₂'.trans eB.symm)
  have hs1 : ∀ x : ↥A, eA (a₁ x) = a₁' (eA x) := fun x =>
    MulEquiv.apply_symm_apply eA (a₁' (eA x))
  have hs2 : ∀ x : ↥B, eB (a₂ x) = a₂' (eB x) := fun x =>
    MulEquiv.apply_symm_apply eB (a₂' (eB x))
  have hmemB : ∀ x : ↥A, (x : G) ∈ B ↔
      ((eA x : ↥(A.map E.toMonoidHom)) : P) ∈ B.map E.toMonoidHom := fun x => by
    rw [hcA x]
    exact (hmap B x).symm
  have hmemA : ∀ x : ↥B, (x : G) ∈ A ↔
      ((eB x : ↥(B.map E.toMonoidHom)) : P) ∈ A.map E.toMonoidHom := fun x => by
    rw [hcB x]
    exact (hmap A x).symm
  refine ⟨a₁, a₂, ?_, ?_, ?_⟩
  · intro m
    have key := hmemB (a₁ m)
    rw [hs1 m] at key
    exact (hmemB m).trans ((hm1 (eA m)).trans key.symm)
  · intro m
    have key := hmemA (a₂ m)
    rw [hs2 m] at key
    exact (hmemA m).trans ((hm2 (eB m)).trans key.symm)
  · intro b m₁ m₂ hm₁ hm₂
    have ha1 : ((a₁' (eA m₁) : ↥(A.map E.toMonoidHom)) : P) = E ((a₁ m₁ : ↥A) : G) := by
      rw [← hs1 m₁, hcA]
    have ha2 : ((a₂' (eB m₂) : ↥(B.map E.toMonoidHom)) : P) = E ((a₂ m₂ : ↥B) : G) := by
      rw [← hs2 m₂, hcB]
    have h1 : ((eA m₁ : ↥(A.map E.toMonoidHom)) : P) =
        ((eI b : ↥(A.map E.toMonoidHom ⊓ B.map E.toMonoidHom)) : P) := by
      rw [hcA, hcI, hm₁]
    have h2 : ((a₁' (eA m₁) : ↥(A.map E.toMonoidHom)) : P) =
        ((eB m₂ : ↥(B.map E.toMonoidHom)) : P) := by
      rw [ha1, hcB, hm₂]
    have H := hc' (eI b) (eA m₁) (eB m₂) h1 h2
    have hsb : ((σ' (eI b) : ↥(A.map E.toMonoidHom ⊓ B.map E.toMonoidHom)) : P) =
        E ((σ b : ↥(A ⊓ B)) : G) := by
      rw [hσ'eq b, hcI]
    rw [ha2, hsb] at H
    exact E.injective H

theorem leafL34DC_of_std
    (h : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 → DCStd F ∧ DCStdSwap F) :
    LeafL34DC := by
  intro Mdl _hMdl
  obtain ⟨-, F, hFf, hFfin, hFchar, hFcard, ⟨e1⟩⟩ :=
    CFSG.Quasithin.H13.F431.L3.exists_equiv_projSL3 Mdl.lie
  have hq : Nat.card F = 4 := by norm_num [hFcard]
  have hy1 := CFSG.Quasithin.IsYAmalgamPair.map e1 Mdl.pair
  obtain ⟨g, -, hg⟩ := CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj hy1.1
    (CFSG.QuasithinUnique.Fin257.L3.isSylowTwoOf_U (F := F))
  let E : Mdl.Y ≃* projectiveSL 3 F := e1.trans (MulAut.conj g)
  have hT : Mdl.T0.map E.toMonoidHom = projUnitriangular 3 F := by
    rw [hg, Subgroup.map_map]
    rfl
  have hy2 : CFSG.Quasithin.IsYAmalgamPair (projUnitriangular 3 F)
      (Mdl.M1.map E.toMonoidHom) (Mdl.M2.map E.toMonoidHom) := by
    have := CFSG.Quasithin.IsYAmalgamPair.map E Mdl.pair
    rwa [hT] at this
  rcases CFSG.QuasithinUnique.Borel252.BorelData.yam_cases
      (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := F))
      CFSG.Quasithin.H13.F431.L3.no_normal_two_subgroup hy2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    refine dcProp_of_map E Mdl.M1 Mdl.M2 ?_
    rw [h1, h2]
    exact (h F hq).2
  ·
    refine dcProp_of_map E Mdl.M1 Mdl.M2 ?_
    rw [h1, h2]
    exact (h F hq).1

end CFSG.GH74.QTGen4.DSGen4.L34
