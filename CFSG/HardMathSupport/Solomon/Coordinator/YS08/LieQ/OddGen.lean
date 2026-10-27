module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut

@[expose] def TwoParabolics (q : ℕ) (S : Type*) [Group S] : Prop :=
  ∃ (U : Sylow q S) (P₁ P₂ Q₁ Q₂ : Subgroup S), IsCoatom P₁ ∧ ¬ P₂ ≤ P₁ ∧
    (U : Subgroup S) ≤ P₁ ∧ (U : Subgroup S) ≤ P₂ ∧
    Q₁ ≠ ⊥ ∧ IsPGroup q Q₁ ∧ P₁ ≤ Subgroup.normalizer (Q₁ : Set S) ∧
    Q₂ ≠ ⊥ ∧ IsPGroup q Q₂ ∧ P₂ ≤ Subgroup.normalizer (Q₂ : Set S)

variable {q : ℕ} [Fact q.Prime] {S : Type} [Group S] [Finite S]

theorem exists_radical_le_sylow (hBT : HoldsTits S q) (U : Sylow q S) {P Q : Subgroup S}
    (hQ0 : Q ≠ ⊥) (hQp : IsPGroup q Q) (hUP : (U : Subgroup S) ≤ P)
    (hPN : P ≤ Subgroup.normalizer (Q : Set S)) :
    ∃ R : Subgroup S, IsRadical q R ∧ R ≤ (U : Subgroup S) ∧ P ≤ Subgroup.normalizer (R : Set S) := by
  obtain ⟨hle, hRp, hN, hnetop, hcore, -⟩ := canonical_parabolic_tits hBT hQ0 hQp
  obtain ⟨R, hR⟩ : ∃ R : Subgroup S, R = radInf q Q := ⟨_, rfl⟩
  rw [← hR] at hle hRp hN hnetop hcore
  have hR0 : R ≠ ⊥ := fun hb => hQ0 (le_bot_iff.1 (hb ▸ hle))
  have hPR : P ≤ Subgroup.normalizer (R : Set S) := hPN.trans hN
  have hUN : (U : Subgroup S) ≤ Subgroup.normalizer (R : Set S) := hUP.trans hPR
  have hsup : IsPGroup q ↥(R ⊔ (U : Subgroup S)) := hRp.to_sup_of_normal_left' U.isPGroup' hUN
  have h1 : R ⊔ (U : Subgroup S) = (U : Subgroup S) := U.is_maximal' hsup le_sup_right
  exact ⟨R, ⟨hR0, hRp, hcore, hnetop⟩, h1 ▸ le_sup_left, hPR⟩

theorem radicalGen_of_twoParabolics (hBT : HoldsTits S q) (hI : RadRigidInner q S)
    (h : TwoParabolics q S) : ∀ U : Sylow q S, RadicalGen q S (U : Subgroup S) := by
  obtain ⟨U₀, P₁, P₂, Q₁, Q₂, hP₁, hP₂, hU₁, hU₂, hQ₁0, hQ₁p, hP₁N, hQ₂0, hQ₂p, hP₂N⟩ := h
  refine RadicalGen.of_sylow U₀ ?_
  unfold RadicalGen
  have hlt : P₁ < P₁ ⊔ P₂ := lt_of_le_of_ne le_sup_left (fun h => hP₂ (h ▸ le_sup_right))
  rw [eq_top_iff, ← hP₁.2 _ hlt]
  refine sup_le ?_ ?_
  · obtain ⟨R, hR, hRU, hPR⟩ := exists_radical_le_sylow hBT U₀ hQ₁0 hQ₁p hU₁ hP₁N
    intro x hx
    exact Subgroup.subset_closure ⟨R, hR.2.1, hRU, centralizer_le_of_radRigidInner hI hR, hPR hx⟩
  · obtain ⟨R, hR, hRU, hPR⟩ := exists_radical_le_sylow hBT U₀ hQ₂0 hQ₂p hU₂ hP₂N
    intro x hx
    exact Subgroup.subset_closure ⟨R, hR.2.1, hRU, centralizer_le_of_radRigidInner hI hR, hPR hx⟩

theorem radRigid_of_twoParabolics (hBT : HoldsTits S q) (hI : RadRigidInner q S)
    (h : TwoParabolics q S) : RadRigid q S :=
  radRigid_of_gen hBT (fun _ hR => centralizer_le_of_radRigidInner hI hR)
    (radicalGen_of_twoParabolics hBT hI h)

theorem TwoParabolics.of_mulEquiv {S' : Type} [Group S'] (e : S ≃* S') (h : TwoParabolics q S) :
    TwoParabolics q S' := by
  obtain ⟨U, P₁, P₂, Q₁, Q₂, hP₁, hP₂, hU₁, hU₂, hQ₁0, hQ₁p, hP₁N, hQ₂0, hQ₂p, hP₂N⟩ := h
  have hmap : ∀ {A B : Subgroup S}, A ≤ B → A.map e.toMonoidHom ≤ B.map e.toMonoidHom :=
    fun h => Subgroup.map_mono h
  have hbot : ∀ {A : Subgroup S}, A ≠ ⊥ → A.map e.toMonoidHom ≠ ⊥ := fun {A} hA hb =>
    hA ((Subgroup.map_eq_bot_iff_of_injective A e.injective).1 hb)
  have hnorm : ∀ {P Q : Subgroup S}, P ≤ Subgroup.normalizer (Q : Set S) →
      P.map e.toMonoidHom ≤ Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup S') : Set S') := by
    intro P Q hPQ
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hPQ
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨Sylow.mapSurjective hsurj U, P₁.map e.toMonoidHom, P₂.map e.toMonoidHom,
    Q₁.map e.toMonoidHom, Q₂.map e.toMonoidHom, ?_, ?_, ?_, ?_, hbot hQ₁0, hQ₁p.map _, hnorm hP₁N,
    hbot hQ₂0, hQ₂p.map _, hnorm hP₂N⟩
  · exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) P₁).2 hP₁
  · intro hle
    apply hP₂
    exact (Subgroup.map_le_map_iff_of_injective e.injective).1 hle
  · rw [Sylow.coe_mapSurjective]
    exact hmap hU₁
  · rw [Sylow.coe_mapSurjective]
    exact hmap hU₂

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
