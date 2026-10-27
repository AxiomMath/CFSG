module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Lift

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

variable {P : Type*} [Group P]

@[expose] def GenP (A : Subgroup (MulAut P)) : Prop :=
  ⊤ ≤ ⨆ (S : Subgroup (MulAut P)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S),
    dPart 3 (c25Fix S)

theorem c25Fix_map_conj (τ : MulAut P) (S : Subgroup (MulAut P)) :
    c25Fix (S.map (MulAut.conj τ).toMonoidHom) = (c25Fix S).map τ.toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, mem_c25Fix]
  constructor
  · intro hy
    refine ⟨τ.symm y, fun s hs => ?_, by simp⟩
    have h : τ (s (τ.symm y)) = y := hy _ ⟨s, hs, rfl⟩
    exact τ.injective (by rw [h]; simp)
  · rintro ⟨x, hx, rfl⟩ _ ⟨s, hs, rfl⟩
    show τ (s (τ.symm (τ x))) = τ x
    rw [MulEquiv.symm_apply_apply]
    exact congrArg τ (hx s hs)

theorem dPart_map_equiv {Q : Type*} [Group Q] (φ : P ≃* Q) (p : ℕ) (C : Subgroup P) :
    dPart p (C.map φ.toMonoidHom) = (dPart p C).map φ.toMonoidHom := by
  unfold dPart
  rw [Subgroup.map_sup, Subgroup.map_commutator, MonoidHom.map_closure]
  congr 2
  ext y
  constructor
  · rintro ⟨hy, hord⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    rwa [show orderOf (φ.toMonoidHom x) = orderOf x from MulEquiv.orderOf_eq φ x] at hord
  · rintro ⟨x, ⟨hx, hord⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hx, ?_⟩
    rwa [show orderOf (φ.toMonoidHom x) = orderOf x from MulEquiv.orderOf_eq φ x]

theorem GenP_of_conj (τ : MulAut P) (A : Subgroup (MulAut P))
    (h : GenP (A.map (MulAut.conj τ).toMonoidHom)) : GenP A := by
  set c : MulAut P →* MulAut P := (MulAut.conj τ).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj τ).injective
  have hcsurj : Function.Surjective c := (MulAut.conj τ).surjective
  set Big := ⨆ (S : Subgroup (MulAut P)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S),
    dPart 3 (c25Fix S) with hBig
  have hcardA : Nat.card (A.map c) = Nat.card A := Subgroup.card_map_of_injective hcinj
  have hle : (⨆ (S : Subgroup (MulAut P))
      (_ : S ≤ A.map c ∧ Nat.card (A.map c) ≤ 3 * Nat.card S), dPart 3 (c25Fix S)) ≤
        Big.map τ.toMonoidHom := by
    refine iSup₂_le fun S' hS' => ?_
    set S : Subgroup (MulAut P) := S'.comap c with hS
    have hSS' : S.map c = S' := Subgroup.map_comap_eq_self_of_surjective hcsurj S'
    have hSA : S ≤ A := by
      intro x hx
      have hx' : c x ∈ A.map c := hS'.1 hx
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx'
      rw [← hcinj hax]
      exact ha
    have hcard : Nat.card S = Nat.card S' := by
      rw [← hSS']
      exact (Subgroup.card_map_of_injective hcinj).symm
    have hmem : dPart 3 (c25Fix S) ≤ Big :=
      le_iSup₂_of_le S ⟨hSA, by rw [hcard, ← hcardA]; exact hS'.2⟩ le_rfl
    calc dPart 3 (c25Fix S') = dPart 3 (c25Fix (S.map c)) := by rw [hSS']
      _ = dPart 3 ((c25Fix S).map τ.toMonoidHom) := by rw [hc, c25Fix_map_conj]
      _ = (dPart 3 (c25Fix S)).map τ.toMonoidHom :=
        dPart_map_equiv (τ : P ≃* P) 3 (c25Fix S)
      _ ≤ Big.map τ.toMonoidHom := Subgroup.map_mono hmem
  intro x _
  have hx : τ x ∈ Big.map τ.toMonoidHom := hle (h (Subgroup.mem_top (τ x)))
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
  have : y = x := τ.injective hyx
  rw [← this]
  exact hy

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
