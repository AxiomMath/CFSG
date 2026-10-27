module

public import CFSG.LargeExtraspecial.S8CBFCrit
public import CFSG.Sporadic.SmallOddCore.J2Local

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier (j2P j2PermEquiv)

section Ambient

variable {G : Type*} [Group G]

@[expose] def SixtyDatum (H : Subgroup G) (τ : G) : Prop :=
  ∃ Q : Subgroup G, Q ≤ H ⊓ centralizer ({τ} : Set G) ∧
    (∀ c ∈ H ⊓ centralizer ({τ} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧
    Nat.card ↥(H ⊓ centralizer ({τ} : Set G)) = 60 * Nat.card Q

theorem SixtyDatum.toRel [Finite G] {H : Subgroup G} {τ : G} (h : SixtyDatum H τ) :
    RelNormalTwoDatum H τ := by
  obtain ⟨Q, hQC, hQn, hQ2, hcard⟩ := h
  exact ⟨Q, hQC, hQn, hQ2, fun P hP hP2 =>
    commutator_le_of_card_eq_sixty_mul hQC hQn hQ2 hcard hP hP2⟩

end Ambient

theorem sixtyDatum_j2_t₁ : SixtyDatum j2P (tp 315 (j2CentTbl 17)) := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨-, hDC1, hC1D, -, hC1cent⟩ := j2_D_facts
  have hr := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hC1 : genOf 315 j2C1Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set _) := by
    have h := hr.2.2.2.1
    dsimp only [Sporadic.SmallOddCore.j2C] at h
    rw [genOf, j2C1Gens]
    exact h
  have hcard : Nat.card ↥(j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set _)) = 240 := by
    have h := hr.2.2.2.2.1
    dsimp only at h
    exact h
  set D := genOf 315 j2DGens
  set C₁ := genOf 315 j2C1Gens
  refine ⟨C₁ ⊓ centralizer (D : Set (Equiv.Perm (Fin 315))), hC1 ▸ inf_le_left, ?_,
    isPGroup_two_of_card (k := 2) (by rw [hC1cent]; norm_num), by rw [hcard, hC1cent]⟩
  rw [← hC1]
  intro c hc q hq
  refine mem_inf.mpr ⟨C₁.mul_mem (C₁.mul_mem hc (mem_inf.mp hq).1) (C₁.inv_mem hc), ?_⟩
  rw [mem_centralizer_iff]
  intro d hd
  have hd' : c⁻¹ * d * c ∈ D := by
    have := (mem_normalizer_iff''.mp (hC1D hc)) d
    exact this.mp hd
  have hqd := (mem_centralizer_iff.mp (mem_inf.mp hq).2) _ hd'
  calc d * (c * q * c⁻¹) = c * ((c⁻¹ * d * c) * q) * c⁻¹ := by group
    _ = c * (q * (c⁻¹ * d * c)) * c⁻¹ := by rw [hqd]
    _ = c * q * c⁻¹ * d := by group

theorem sixtyDatum_j2_t₂ : SixtyDatum j2P (tp 315 (j2CentTbl 31)) := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨hQcard, hQC2, hC2Q, -⟩ := j2_Q_facts
  have hr := hrows _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hC2 : genOf 315 j2C2Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _) := by
    have h := hr.2.2.2.1
    dsimp only [Sporadic.SmallOddCore.j2C] at h
    rw [genOf, j2C2Gens]
    exact h
  have hcard : Nat.card ↥(j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _)) = 1920 := by
    have h := hr.2.2.2.2.1
    dsimp only at h
    exact h
  refine ⟨genOf 315 j2QGens, hC2 ▸ hQC2, ?_,
    isPGroup_two_of_card (k := 5) (by rw [hQcard]; norm_num), by rw [hcard, hQcard]⟩
  rw [← hC2]
  intro c hc q hq
  exact (mem_normalizer_iff.mp (hC2Q hc) q).mp hq

theorem relNormalTwoDatum_j2P {τ : Equiv.Perm (Fin 315)} (hτP : τ ∈ j2P) (hτ : orderOf τ = 2) :
    RelNormalTwoDatum j2P τ := by
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover τ (j2P_le_j2R hτP) hτ
  have htrP : tp 315 r.rep ∈ j2P := by
    have := j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) hτP) hg
    rwa [show g⁻¹ * (g * tp 315 r.rep * g⁻¹) * g = tp 315 r.rep by group] at this
  have hrows' := hrows
  simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := (hrows' _ List.mem_cons_self).2.2.1
    exact absurd htrP (this.1 rfl)
  · dsimp only
    exact sixtyDatum_j2_t₁.toRel.conj hg
  · dsimp only
    exact sixtyDatum_j2_t₂.toRel.conj hg

theorem invCentSectAbelianSylow_of_isSporadic_J2 {Y : Type} [Group Y] [Finite Y]
    (h : NativeSporadic.IsSporadic Y .J2) : InvCentSectAbelianSylow Y := by
  obtain ⟨e₀⟩ := h
  let e : Y ≃* j2P := e₀.trans j2PermEquiv
  refine invCentSectAbelianSylow_of_normalTwoDatum fun y hy => NormalTwoDatum.of_mulEquiv e ?_
  have hτ : orderOf ((e y : j2P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
  exact normalTwoDatum_of_rel (relNormalTwoDatum_j2P (e y).2 hτ)

end CFSG.LargeExtraspecial.S8
