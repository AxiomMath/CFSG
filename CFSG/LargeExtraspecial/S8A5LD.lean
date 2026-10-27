module

public import CFSG.LargeExtraspecial.S8A5LC
public import CFSG.LargeExtraspecial.S9TIXC

public section

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.CGT.Timmesfeld75

universe u

variable {Γ : Type u} [Group Γ]

namespace PairDataE

variable {M A N : Subgroup Γ} {t x : Γ} (P : PairDataE M A N t x)
include P

theorem isTIIn_A [Finite Γ] : S9.TIX.IsTIIn A (A ⊔ conjSubgroup x A) := by
  intro h hX hne
  have hM := P.sup_le_M hX
  have hE := P.sup_le_normalizer_E hX
  have htE : t ∈ Epair A x := mem_sup_left P.t_mem_F
  have h1 : h * t * h⁻¹ ∈ Epair A x := (mem_normalizer_iff.mp hE _).mp htE
  have hcomm := P.comm_E h1 htE
  have hht : h * t * h⁻¹ = t := by
    by_contra hne'
    exact hne (P.hP1 h hM hcomm hne' (Or.inl h1))
  have hht' : h * t = t * h := by
    calc h * t = h * t * h⁻¹ * h := by group
      _ = t * h := by rw [hht]
  have hle : conjSubgroup h (A ⊓ normalizer (conjSubgroup x A : Set Γ)) ≤
      A ⊓ normalizer (conjSubgroup x A : Set Γ) := by
    intro f hf
    have hf' := mem_conjSubgroup.mp hf
    have e : f = h * (h⁻¹ * f * h) * h⁻¹ := by group
    rw [e]
    exact P.E_inf_N_le P.F₁_inf_N ((mem_normalizer_iff.mp hE _).mp (mem_sup_left hf'))
      (P.hNorm h hM hht' _ (P.hAN hf'.1))
  have heq : conjSubgroup h (A ⊓ normalizer (conjSubgroup x A : Set Γ)) =
      A ⊓ normalizer (conjSubgroup x A : Set Γ) :=
    Subgroup.eq_of_le_of_card_ge hle (S9.TIX.card_conjSubgroup h _).ge
  obtain ⟨a, haF, hat⟩ := P.exists_not_mem_zpowers P.h2
  have haA : a ∈ A ⊓ conjSubgroup h A := by
    refine ⟨haF.1, ?_⟩
    have haF' := haF
    rw [← heq] at haF'
    exact Subgroup.map_mono inf_le_left haF'
  exact P.hK h hM hht' a haA hat

theorem mix [Finite Γ] : ∀ h ∈ A ⊔ conjSubgroup x A,
    conjSubgroup h A ⊓ conjSubgroup x A ≠ ⊥ → conjSubgroup h A = conjSubgroup x A := by
  intro h hX hne
  have hhinvX := inv_mem hX
  have hM := P.sup_le_M hhinvX
  have hE := P.sup_le_normalizer_E hhinvX
  have hyM : h⁻¹ * x ∈ M := M.mul_mem hM P.hxM
  have hyA : conjSubgroup (h⁻¹ * x) A = conjSubgroup h⁻¹ (conjSubgroup x A) :=
    S9.TIX.conjSubgroup_mul _ _ _
  have hne' : A ⊓ conjSubgroup (h⁻¹ * x) A ≠ ⊥ := by
    intro hbot
    apply hne
    have h1 := congrArg (conjSubgroup h) hbot
    rw [conjSubgroup_inf, hyA, conjSubgroup_conj_inv] at h1
    rw [h1]
    exact conjSubgroup_eq_bot_iff.mpr rfl
  have hσE : x * t * x⁻¹ ∈ Epair A x := mem_sup_right P.σ_mem_F₁
  have htE : t ∈ Epair A x := mem_sup_left P.t_mem_F
  have h1 : h⁻¹ * (x * t * x⁻¹) * h⁻¹⁻¹ ∈ Epair A x := (mem_normalizer_iff.mp hE _).mp hσE
  rw [show h⁻¹ * (x * t * x⁻¹) * h⁻¹⁻¹ = (h⁻¹ * x) * t * (h⁻¹ * x)⁻¹ by group] at h1
  have hcomm := P.comm_E h1 htE
  have hyt : (h⁻¹ * x) * t * (h⁻¹ * x)⁻¹ = t := by
    by_contra hne''
    exact hne' (P.hP1 _ hyM hcomm hne'' (Or.inl h1))
  have hyt' : (h⁻¹ * x) * t = t * (h⁻¹ * x) := by
    calc (h⁻¹ * x) * t = (h⁻¹ * x) * t * (h⁻¹ * x)⁻¹ * (h⁻¹ * x) := by group
      _ = t * (h⁻¹ * x) := by rw [hyt]
  have hle : conjSubgroup h⁻¹ (conjSubgroup x A ⊓ normalizer (A : Set Γ)) ≤
      A ⊓ conjSubgroup (h⁻¹ * x) A := by
    intro f hf
    have hf' := mem_conjSubgroup.mp hf
    rw [inv_inv] at hf'
    have hfy : f ∈ conjSubgroup (h⁻¹ * x) A := by
      rw [hyA, mem_conjSubgroup, inv_inv]
      exact hf'.1
    refine ⟨?_, hfy⟩
    have hfE : f ∈ Epair A x := by
      have := (mem_normalizer_iff.mp hE _).mp (mem_sup_right hf')
      rwa [show h⁻¹ * (h * f * h⁻¹) * h⁻¹⁻¹ = f by group] at this
    have hfN : f ∈ N := by
      have h2 := mem_conjSubgroup.mp hfy
      have e : f = (h⁻¹ * x) * ((h⁻¹ * x)⁻¹ * f * (h⁻¹ * x)) * (h⁻¹ * x)⁻¹ := by group
      rw [e]
      exact P.hNorm _ hyM hyt' _ (P.hAN h2)
    exact (P.E_inf_N_le P.F₁_inf_N hfE hfN).1
  have hcard : 2 < Nat.card (conjSubgroup h⁻¹ (conjSubgroup x A ⊓ normalizer (A : Set Γ))) := by
    rw [S9.TIX.card_conjSubgroup, PairData.F₁_eq, S9.TIX.card_conjSubgroup]
    exact P.h2'
  obtain ⟨a, ha, hat⟩ := P.exists_not_mem_zpowers hcard
  have hK := P.hK _ hyM hyt' a (hle ha) hat
  rw [hyA] at hK
  have h3 := congrArg (conjSubgroup h) hK
  rw [conjSubgroup_conj_inv] at h3
  exact h3.symm

theorem isTIIn_A₁ [Finite Γ] :
    S9.TIX.IsTIIn (conjSubgroup x A) (A ⊔ conjSubgroup x A) := by
  have h := isTIIn_conjSubgroup P.symm.isTIIn_A x
  rwa [conjSubgroup_sup, conjSubgroup_conj_inv, sup_comm] at h

theorem setup [Finite Γ] : S9.TIX.Setup A (conjSubgroup x A)
    (A ⊓ normalizer (conjSubgroup x A : Set Γ)) (conjSubgroup x A ⊓ normalizer (A : Set Γ))
    (Epair A x) where
  sqA := P.hsq
  sqAb := P.hsq₁
  card := (S9.TIX.card_conjSubgroup x A).symm
  tiA := P.isTIIn_A
  tiAb := P.isTIIn_A₁
  mix := P.mix
  hL := rfl
  hLb := rfl
  hM := rfl
  ne_bot := fun h => P.ht1 (by
    have := P.t_mem_F
    rw [h, mem_bot] at this
    exact this)
  ne := fun h => by
    have h4 := P.h4
    rw [h] at h4
    have : 0 < Nat.card A := Nat.card_pos
    omega

theorem exists_conj_ne [Finite Γ] (hTI : S9.TIPairInput.{u}) :
    ∃ y ∈ M, y * t * y⁻¹ ∈ A ∧ y * t * y⁻¹ ≠ t := by
  obtain ⟨y, hy, hyA, hne⟩ := P.setup.exists_conj_ne_of_tiPairInput hTI P.h4 P.t_mem_F P.ht1
  exact ⟨y, P.sup_le_M hy, hyA, hne⟩

end PairDataE

end CFSG.LargeExtraspecial.S8
