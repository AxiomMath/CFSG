module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerB1
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp coe_fieldSp)
open CFSG.SeitzReduction.E6Pilot (IsAutConj IsAutConjIn)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

variable {K : Type} [Field K]

theorem map_fieldSp_longRootSp2 {n : ℕ} (σ : K ≃+* K) (k : Fin n) :
    (longRootSp2 K n k).map (fieldSp n K σ).toMonoidHom = longRootSp2 K n k := by
  have hle : ∀ τ : K ≃+* K,
      (longRootSp2 K n k).map (fieldSp n K τ).toMonoidHom ≤ longRootSp2 K n k := by
    intro τ
    rintro _ ⟨g, hg, rfl⟩
    rw [longRootSp2_eq_suppGroup] at hg ⊢
    intro r t hrt
    change (((fieldSp n K τ g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t = _
    rw [coe_fieldSp, Matrix.map_apply]
    have h := hg r t hrt
    change ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t = _ at h
    rw [h, Matrix.one_apply]
    split_ifs <;> simp
  refine le_antisymm (hle σ) ?_
  intro g hg
  have hg' := hle σ⁻¹ ⟨g, hg, rfl⟩
  refine ⟨fieldSp n K σ⁻¹ g, hg', ?_⟩
  change fieldSp n K σ (fieldSp n K σ⁻¹ g) = g
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem isAutConj_longRootSp2 [Finite K] [CharP K 2] {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    IsAutConj (longRootSp2 K n k) := by
  intro α
  obtain ⟨s, σ, h⟩ := F4Pilot.exists_eq_conj_mul_fieldSp hn α
  refine ⟨s, ?_⟩
  have e : (longRootSp2 K n k).map α.toMonoidHom =
      ((longRootSp2 K n k).map (fieldSp n K σ).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext g
    simp [h g, MulAut.conj_apply]
  rw [e, map_fieldSp_longRootSp2]

theorem map_complSpEquiv_longRootSp2 {m : ℕ} (p : Fin (m + 1)) (l : Fin m) :
    ((longRootSp2 K m l).map (complSpEquiv (K := K) p).toMonoidHom).map (complSp K p).subtype =
      longRootSp2 K (m + 1) (p.succAbove l) := by
  rw [Subgroup.map_map, longRootSp2, longRootSp2, MonoidHom.range_eq_map, MonoidHom.range_eq_map,
    Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun A => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, coe_complSpEquiv_apply, spEmbed_longBlock]

theorem isAutConjIn_complSp_longRootSp2 [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) :
    IsAutConjIn (complSp K (1 : Fin (n + 3))) (longRootSp2 K (n + 3) 0) := by
  have h := (isAutConj_longRootSp2 (K := K) (n := n + 2) (by omega) 0).isAutConjIn_map
    (complSpEquiv (K := K) (1 : Fin (n + 3)))
  have hs : (1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) = 0 := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · rw [Fin.lt_def]
      simp
  rwa [map_complSpEquiv_longRootSp2, hs] at h

section TwoPlanes

variable (n : ℕ)

@[expose] def planes12 : Fin (n + 1) → Fin (n + 3) :=
  (1 : Fin (n + 3)).succAbove ∘ (1 : Fin (n + 2)).succAbove

theorem planes12_injective : Function.Injective (planes12 n) :=
  Fin.succAbove_right_injective.comp Fin.succAbove_right_injective

theorem planes12_zero : planes12 n 0 = 0 := by
  simp [planes12, Fin.succAbove_ne_zero_zero]

theorem planes12_ne_one (i : Fin (n + 1)) : planes12 n i ≠ 1 :=
  Fin.succAbove_ne _ _

theorem planes12_ne_two (i : Fin (n + 1)) : planes12 n i ≠ 2 := by
  intro h
  have h1 := Fin.succAbove_ne (1 : Fin (n + 2)) i
  set x := (1 : Fin (n + 2)).succAbove i with hx
  have h2 : (1 : Fin (n + 3)).succAbove x = 2 := h
  apply h1
  rw [Fin.ext_iff] at h2 ⊢
  rw [Fin.succAbove] at h2
  split_ifs at h2 with hlt
  · rw [Fin.lt_def] at hlt
    simp only [Fin.val_castSucc, Fin.val_one] at hlt h2
    rw [Fin.val_two] at h2
    omega
  · simp only [Fin.val_succ, Fin.val_two] at h2
    simp only [Fin.val_one]
    omega

variable (K) in
@[expose] noncomputable def spCompl12 : Subgroup (StatedSp (n + 3) K) :=
  (spEmbed (K := K) (planes12 n) (planes12_injective n)).range

variable (K) in
@[expose] noncomputable def spCompl12Equiv : StatedSp (n + 1) K ≃* spCompl12 K n :=
  MonoidHom.ofInjective (spEmbed_injective (K := K) (planes12_injective n))

theorem map_spCompl12Equiv_longRootSp2 :
    ((longRootSp2 K (n + 1) 0).map (spCompl12Equiv K n).toMonoidHom).map (spCompl12 K n).subtype =
      longRootSp2 K (n + 3) 0 := by
  rw [Subgroup.map_map, longRootSp2, longRootSp2, MonoidHom.range_eq_map, MonoidHom.range_eq_map,
    Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun A => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom]
  change spEmbed (planes12 n) (planes12_injective n) (longBlock K (n + 1) 0 A) = _
  rw [spEmbed_longBlock, planes12_zero]

theorem longRootSp2_le_spCompl12 : longRootSp2 K (n + 3) 0 ≤ spCompl12 K n := by
  rw [← map_spCompl12Equiv_longRootSp2]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem spCompl12_le_centralizer_twoCentralElt (a b : K) :
    spCompl12 K n ≤ centralizer ({twoCentralElt (n + 3) 1 2 a b} : Set (StatedSp (n + 3) K)) := by
  rintro _ ⟨g, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have hmem : ∀ x : Fin (n + 3),
      (Sum.inl x ∈ Set.range (Sum.map (planes12 n) (planes12 n)) → x ≠ 1 ∧ x ≠ 2) ∧
      (Sum.inr x ∈ Set.range (Sum.map (planes12 n) (planes12 n)) → x ≠ 1 ∧ x ≠ 2) := by
    intro x
    constructor
    · rintro ⟨u, hu⟩
      rcases u with u | u
      · simp only [Sum.map_inl, Sum.inl.injEq] at hu
        subst hu
        exact ⟨planes12_ne_one n u, planes12_ne_two n u⟩
      · simp at hu
    · rintro ⟨u, hu⟩
      rcases u with u | u
      · simp at hu
      · simp only [Sum.map_inr, Sum.inr.injEq] at hu
        subst hu
        exact ⟨planes12_ne_one n u, planes12_ne_two n u⟩
  have hz : twoCentralElt (n + 3) 1 2 a b ∈
      suppGroup (Set.range (Sum.map (planes12 n) (planes12 n)))ᶜ := by
    intro r t hrt
    rw [mat_twoCentralElt]
    rcases r with x | x <;> rcases t with y | y
    · simp [Matrix.one_apply]
    · rw [fromBlocks_apply₁₂, twoCentralMat_apply, Matrix.one_apply_ne Sum.inl_ne_inr]
      rw [Set.mem_compl_iff, Set.mem_compl_iff, not_and_or, not_not, not_not] at hrt
      rcases hrt with hx | hy
      · obtain ⟨h1, h2⟩ := (hmem x).1 hx
        simp [Ne.symm h1, Ne.symm h2]
      · obtain ⟨h1, h2⟩ := (hmem y).2 hy
        simp [Ne.symm h1, Ne.symm h2]
    · simp
    · simp [Matrix.one_apply]
  exact (commute_suppGroup_compl (isSupp_spEmbed (planes12_injective n) g) hz).eq

theorem commutator_spCompl12 [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅spCompl12 K n, spCompl12 K n⁆ = spCompl12 K n := by
  have : Group.IsPerfect (StatedSp (n + 1) K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp (n + 1) K
      (Or.inl (exists_finset_card_four hK))
  rw [spCompl12, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem spCompl12_le_perfectCore_centralizer_spRep [Finite K] (hK : 4 ≤ Nat.card K)
    (κ : SpTwoCentral) :
    spCompl12 K n ≤
      perfectCore (centralizer ({spRep (K := K) n κ} : Set (StatedSp (n + 3) K))) :=
  le_perfectCore_of_perfect (spCompl12_le_centralizer_twoCentralElt n _ _)
    (commutator_spCompl12 n hK)

theorem isAutConjIn_spCompl12_longRootSp2 [Finite K] [CharP K 2] (hn : 2 ≤ n) :
    IsAutConjIn (spCompl12 K n) (longRootSp2 K (n + 3) 0) := by
  have h := (isAutConj_longRootSp2 (K := K) (n := n + 1) (by omega) 0).isAutConjIn_map
    (spCompl12Equiv K n)
  rwa [map_spCompl12Equiv_longRootSp2] at h

end TwoPlanes

end CFSG.SeitzReduction.SymplecticPilot
