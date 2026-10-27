module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Equivariance
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

@[expose] def GenBelow {Y : Type*} [Group Y] (A : Subgroup (MulAut Y)) : Prop :=
  ⊤ ≤ ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), c25Fix S

theorem genBelow_mono {Y : Type*} [Group Y] [Finite Y] {A A' : Subgroup (MulAut Y)} (h : A ≤ A')
    (hA' : GenBelow A') : GenBelow A := by
  refine hA'.trans (iSup₂_le fun S' hS' => ?_)
  obtain ⟨hSA', hc⟩ := hS'
  have hpos : 0 < Nat.card S' := Nat.card_pos
  have e1 := Subgroup.relIndex_mul_card (H := S') (K := A')
  rw [inf_of_le_left hSA'] at e1
  have hApos : 0 < Nat.card A' := Nat.card_pos
  have hne : S'.relIndex A' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e1
    omega
  have h3 : S'.relIndex A' ≤ 3 := by
    by_contra hlt
    push_neg at hlt
    have : 4 * Nat.card S' ≤ S'.relIndex A' * Nat.card S' := Nat.mul_le_mul_right _ hlt
    omega
  have h4 : S'.relIndex A ≤ S'.relIndex A' := Subgroup.relIndex_le_of_le_right h hne
  have e2 := Subgroup.relIndex_mul_card (H := S') (K := A)
  refine le_iSup₂_of_le (S' ⊓ A) ⟨inf_le_right, ?_⟩ ?_
  · rw [← e2]
    exact Nat.mul_le_mul_right _ (h4.trans h3)
  · intro y hy α hα
    exact hy α hα.1


theorem c25Fix_map_congr' {Q P : Type*} [Group Q] [Group P] (ε : Q ≃* P)
    (T : Subgroup (MulAut Q)) :
    c25Fix (T.map (MulAut.congr ε).toMonoidHom) = (c25Fix T).map ε.toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, mem_c25Fix]
  constructor
  · intro hy
    refine ⟨ε.symm y, fun s hs => ?_, by simp⟩
    have h : ε (s (ε.symm y)) = y := hy _ ⟨s, hs, rfl⟩
    exact ε.injective (by rw [h]; simp)
  · rintro ⟨x, hx, rfl⟩ _ ⟨s, hs, rfl⟩
    show ε (s (ε.symm (ε x))) = ε x
    rw [MulEquiv.symm_apply_apply]
    exact congrArg ε (hx s hs)

theorem genBelow_of_congr {Q P : Type*} [Group Q] [Group P] (ε : Q ≃* P)
    (A : Subgroup (MulAut Q)) (h : GenBelow (A.map (MulAut.congr ε).toMonoidHom)) :
    GenBelow A := by
  set c : MulAut Q →* MulAut P := (MulAut.congr ε).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.congr ε).injective
  have hcsurj : Function.Surjective c := (MulAut.congr ε).surjective
  set Big := ⨆ (S : Subgroup (MulAut Q)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S),
    c25Fix S with hBig
  have hcardA : Nat.card (A.map c) = Nat.card A := Subgroup.card_map_of_injective hcinj
  have hle : (⨆ (S : Subgroup (MulAut P))
      (_ : S ≤ A.map c ∧ Nat.card (A.map c) ≤ 3 * Nat.card S), c25Fix S) ≤
        Big.map ε.toMonoidHom := by
    refine iSup₂_le fun S' hS' => ?_
    set S : Subgroup (MulAut Q) := S'.comap c with hS
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
    have hmem : c25Fix S ≤ Big :=
      le_iSup₂_of_le S ⟨hSA, by rw [hcard, ← hcardA]; exact hS'.2⟩ le_rfl
    calc c25Fix S' = c25Fix (S.map c) := by rw [hSS']
      _ = (c25Fix S).map ε.toMonoidHom := by rw [hc, c25Fix_map_congr']
      _ ≤ Big.map ε.toMonoidHom := Subgroup.map_mono hmem
  intro x _
  have hx : ε x ∈ Big.map ε.toMonoidHom := hle (h (Subgroup.mem_top (ε x)))
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
  have : y = x := ε.injective hyx
  rw [← this]
  exact hy

theorem genBelow_of_conj {P : Type*} [Group P] (τ : MulAut P) (A : Subgroup (MulAut P))
    (h : GenBelow (A.map (MulAut.conj τ).toMonoidHom)) : GenBelow A := by
  set c : MulAut P →* MulAut P := (MulAut.conj τ).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj τ).injective
  have hcsurj : Function.Surjective c := (MulAut.conj τ).surjective
  set Big := ⨆ (S : Subgroup (MulAut P)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S),
    c25Fix S with hBig
  have hcardA : Nat.card (A.map c) = Nat.card A := Subgroup.card_map_of_injective hcinj
  have hle : (⨆ (S : Subgroup (MulAut P))
      (_ : S ≤ A.map c ∧ Nat.card (A.map c) ≤ 3 * Nat.card S), c25Fix S) ≤
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
    have hmem : c25Fix S ≤ Big :=
      le_iSup₂_of_le S ⟨hSA, by rw [hcard, ← hcardA]; exact hS'.2⟩ le_rfl
    calc c25Fix S' = c25Fix (S.map c) := by rw [hSS']
      _ = (c25Fix S).map τ.toMonoidHom := by rw [hc, c25Fix_map_conj]
      _ ≤ Big.map τ.toMonoidHom := Subgroup.map_mono hmem
  intro x _
  have hx : τ x ∈ Big.map τ.toMonoidHom := hle (h (Subgroup.mem_top (τ x)))
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
  have : y = x := τ.injective hyx
  rw [← this]
  exact hy


theorem genBelow_of_covering {Y : Type*} [Group Y] [Finite Y] (𝓜 : Set (Subgroup (MulAut Y)))
    (hcov : ∀ A : Subgroup (MulAut Y), IsElemAbelian 3 A →
      ∃ M ∈ 𝓜, ∃ τ : MulAut Y, A.map (MulAut.conj τ).toMonoidHom ≤ M)
    (hM : ∀ M ∈ 𝓜, GenBelow M) :
    ∀ A : Subgroup (MulAut Y), IsElemAbelian 3 A → GenBelow A := by
  intro A hA
  obtain ⟨M, hM', τ, hτ⟩ := hcov A hA
  exact genBelow_of_conj τ A (genBelow_mono hτ (hM M hM'))


end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
