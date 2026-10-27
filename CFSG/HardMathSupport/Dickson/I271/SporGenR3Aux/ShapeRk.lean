module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Inner

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Yardstones.Md0ec50421ce4

@[expose] def ShapeRkAt (p : ℕ) (Good Rk : ∀ (T : Type) [Group T], Prop) {Q : Type} [Group Q]
    (k : Q) : Prop :=
  PConstrainedShape p (Subgroup.centralizer ({k} : Set Q)) ∨
    ∃ J : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) J ∧
      (∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I → I = J) ∧
      Good (PSimple p J) ∧ Rk (PQuot p J)

@[expose] def CentShapeRk (p : ℕ) (Good Rk : ∀ (T : Type) [Group T], Prop) (Q : Type) [Group Q] :
    Prop :=
  ∀ k : Q, k ≠ 1 → k ^ p = 1 → ShapeRkAt p Good Rk k

section Transport

variable {Q Q' : Type} [Group Q] [Finite Q] [Group Q']

theorem ShapeRkAt.of_equiv {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T') [Finite Q']
    (e : Q ≃* Q') {k : Q} (h : ShapeRkAt p Good Rk k) : ShapeRkAt p Good Rk (e k) := by
  have hmap : (Subgroup.centralizer ({k} : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ({e k} : Set Q') := map_centralizer_singleton e k
  rcases h with hc | ⟨J, hJ, hu, hG, hR⟩
  · left
    rw [← hmap]
    exact pConstrainedShape_map e hc
  · right
    refine ⟨J.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rw [← hmap]
      exact glaPComponent_map_equiv hp e hJ
    · intro I' hI'
      have h1 := glaPComponent_map_equiv hp e.symm hI'
      have hmap' : (Subgroup.centralizer ({e k} : Set Q')).map e.symm.toMonoidHom =
          Subgroup.centralizer ({k} : Set Q) := by
        rw [map_centralizer_singleton e.symm (e k), MulEquiv.symm_apply_apply]
      rw [hmap'] at h1
      have h2 := hu _ h1
      rw [← h2, Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext; simp
      rw [this, Subgroup.map_id]
    · exact hGood _ _ (pSimpleEquiv p (e.subgroupMap J)) hG
    · exact hRk _ _ (pQuotEquiv p (e.subgroupMap J)) hR

theorem CentShapeRk.of_equiv {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T') [Finite Q']
    (e : Q ≃* Q') (h : CentShapeRk p Good Rk Q) : CentShapeRk p Good Rk Q' := by
  intro k' hk1 hkp
  set k : Q := e.symm k' with hk
  have hk1' : k ≠ 1 := fun h1 => hk1 (by simpa [hk] using congrArg e h1)
  have hkp' : k ^ p = 1 := by
    apply e.injective
    simpa [hk] using hkp
  have hek : e k = k' := by simp [hk]
  have := ShapeRkAt.of_equiv hp hGood hRk e (h k hk1' hkp')
  rwa [hek] at this

end Transport

section Core

variable {X : Type} [Group X] [Finite X]

theorem comp_dichotomy_rk {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K) {a k : X} (hk : k ∈ K)
    (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X))
    (h : PConstrainedShape p (Subgroup.centralizer ({(⟨k, hk⟩ : ↥K)} : Set ↥K)) ∨
      ∃ J : Subgroup ↥K, GLAPComponent p (Subgroup.centralizer ({(⟨k, hk⟩ : ↥K)} : Set ↥K)) J ∧
        (∀ I : Subgroup ↥K, GLAPComponent p
          (Subgroup.centralizer ({(⟨k, hk⟩ : ↥K)} : Set ↥K)) I → I = J) ∧
        Good (PSimple p J) ∧ Rk (PQuot p J)) :
    (∀ J : Subgroup X, ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) ∨
      ∃ J₀ : Subgroup X, J₀ ≤ K ∧
        (∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → J = J₀) ∧
        Good (PSimple p (J₀.subgroupOf K)) ∧ Rk (PQuot p (J₀.subgroupOf K)) := by
  rcases h with hcon | ⟨I, hI, hu, hG, hR⟩
  · exact Or.inl fun J hJ => not_glaPComponent_of_constrained hp hq hk hc hcon hJ
  · refine Or.inr ⟨I.map K.subtype, Subgroup.map_subtype_le I, ?_, ?_⟩
    · intro J hJ
      have hJK : J ≤ K := hJ.1.trans inf_le_left
      have h1 := glaPComponent_subgroupOf hp
        (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K) hJ
      rw [subgroupOf_inf_centralizer_eq hk hc] at h1
      rw [← Subgroup.map_subgroupOf_eq_of_le hJK, hu _ h1]
    · have h1 : (I.map K.subtype).subgroupOf K = I :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective I
      rw [h1]
      exact ⟨hG, hR⟩

end Core

end CFSG.HardMathSupport.Dickson.I271
