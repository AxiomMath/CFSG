module

public import CFSG.CGT.PushingUpLit.SolKNA.BranchC4Frame

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open C4Aux
open CFSG.RankThree.GF2n (card_conjSubgroup conjSubgroup_eq_self_iff)

variable {G : Type} [Group G]

@[expose] def Lemma18Trans (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (R : Subgroup G) (g : G) (Z : Subgroup G), g ∈ Z → R ≤ Z → IsPGroup 2 R →
    (∀ z ∈ Z, R ⊓ conjSubgroup z R = ⊥ ∨ R ⊓ conjSubgroup z R = R) →
    ∀ (T C N : Subgroup G), T = conjSubgroup g R ⊓ Subgroup.normalizer (R : Set G) → T ≠ ⊥ →
      R ⊓ conjSubgroup g R = ⊥ → C = R ⊓ Subgroup.centralizer (T : Set G) →
      (∀ x ∈ R, x * x ∈ C) → (∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ C) →
      (∀ c ∈ C, ∀ x ∈ R, c * x = x * c) → Nonempty (↥C ≃* ↥T) → (∀ x ∈ T, x * x = 1) →
      C ≠ R → C.relIndex R = 4 → Nat.card ↥T = 4 → N = C ⊔ T →
      R ⊔ conjSubgroup g R ≤ Subgroup.normalizer (N : Set G) →
      (∀ x ∈ conjSubgroup g R, x * x ∈ T) →
      (∀ x ∈ conjSubgroup g R, ∀ y ∈ conjSubgroup g R, x * y * x⁻¹ * y⁻¹ ∈ T) →
      (∀ t ∈ T, ∀ x ∈ conjSubgroup g R, t * x = x * t) →
      ∀ z ∈ C, z ≠ 1 → ∀ z' ∈ C, z' ≠ 1 →
        ∃ k ∈ R ⊔ conjSubgroup g R, k ∈ Subgroup.normalizer (R : Set G) ∧ k * z * k⁻¹ = z'

namespace C4Data

variable [Finite G] {R T W Z P : Subgroup G} {c x : G} (D : C4Data R T W Z P c x)
include D

theorem sq_mem_Z {h : G} (hh : h ∈ W) : h * h ∈ Z := by
  rw [D.Z_eq]
  exact D.A.sq_mem_N hh

theorem comm_mem_Z {a b : G} (ha : a ∈ W) (hb : b ∈ W) : a * b * a⁻¹ * b⁻¹ ∈ Z := by
  rw [D.Z_eq]
  exact D.A.comm_mem_N ha hb

theorem Z_central {n h : G} (hn : n ∈ Z) (hh : h ∈ W) : n * h = h * n := by
  rw [D.Z_eq] at hn
  exact D.A.N_central hn hh

theorem fix_c {y : G} (hy : y ∈ Subgroup.normalizer ((W ⊓ R : Subgroup G) : Set G)) :
    y * c * y⁻¹ = c := by
  obtain ⟨h, hh, hhZ⟩ : ∃ h ∈ W ⊓ R, h ∉ Z := by
    by_contra hcon
    have hle : W ⊓ R ≤ Z := fun h hh => by_contra fun hZ => hcon ⟨h, hh, hZ⟩
    have := Subgroup.card_le_of_le hle
    rw [D.card_H, D.card_Z] at this
    omega
  have hsq := D.sq h hh hhZ
  have hyh : y * h * y⁻¹ ∈ W ⊓ R := (Subgroup.mem_normalizer_iff.mp hy h).mp hh
  by_cases hz : y * h * y⁻¹ ∈ Z
  · exfalso
    have h1 := D.Z_sq hz
    have h2 : h * h = 1 := by
      calc h * h = y⁻¹ * ((y * h * y⁻¹) * (y * h * y⁻¹)) * y := by group
        _ = 1 := by rw [h1]; group
    exact D.c_ne (by rw [← hsq]; exact h2)
  · have := D.sq _ hyh hz
    calc y * c * y⁻¹ = y * (h * h) * y⁻¹ := by rw [hsq]
      _ = (y * h * y⁻¹) * (y * h * y⁻¹) := by group
      _ = c := this

theorem N_H_le_N_R : Subgroup.normalizer ((W ⊓ R : Subgroup G) : Set G) ≤
    Subgroup.normalizer (R : Set G) := fun _ hy =>
  normalizer_of_tight D.tight D.A.two_R (D.Z_le_R D.c_mem) D.c_ne
    (by rw [D.fix_c hy]; exact D.Z_le_R D.c_mem)

theorem tiRel : ∀ y ∈ Subgroup.normalizer (P : Set G),
    (W ⊓ R) ⊓ conjSubgroup y (W ⊓ R) = ⊥ ∨ (W ⊓ R) ⊓ conjSubgroup y (W ⊓ R) = W ⊓ R := by
  intro y hy
  by_cases hbot : (W ⊓ R) ⊓ conjSubgroup y (W ⊓ R) = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ (W ⊓ R) ⊓ conjSubgroup y (W ⊓ R), u ≠ 1 := by
    by_contra hcon
    exact hbot ((Subgroup.eq_bot_iff_forall _).mpr fun u hu =>
      by_contra fun h => hcon ⟨u, hu, h⟩)
  have hyN : y ∈ Subgroup.normalizer (R : Set G) := by
    have h1 : y⁻¹ * u * y ∈ W ⊓ R := mem_conjSubgroup.mp hu.2
    have := normalizer_of_tight (x := y⁻¹) D.tight D.A.two_R hu.1.2 hu1 (by simpa using h1.2)
    exact ((Subgroup.normalizer (R : Set G)).inv_mem_iff).mp this
  have hconj : conjSubgroup y R = R := conjSubgroup_eq_self_iff.mpr hyN
  have hle : conjSubgroup y (W ⊓ R) ≤ R := by
    have := conjSubgroup_mono (g := y) (inf_le_right : W ⊓ R ≤ R)
    rwa [hconj] at this
  by_cases heq : conjSubgroup y (W ⊓ R) = W ⊓ R
  · rw [heq, inf_idem]
  · exfalso
    have hsup := sup_eq_of_index_two inf_le_right hle D.A.card_R
      (by rw [card_conjSubgroup]) heq
    apply D.not_R_le_normalizer_P
    rw [← hsup]
    refine sup_le D.H_le_normalizer_P ?_
    intro v hv
    have hv' : y⁻¹ * v * y ∈ W ⊓ R := mem_conjSubgroup.mp hv
    have hvN : y⁻¹ * v * y ∈ Subgroup.normalizer (P : Set G) := D.H_le_normalizer_P hv'
    have e : v = y * (y⁻¹ * v * y) * y⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hvN) (Subgroup.inv_mem _ hy)

theorem conj_R_inf_normalizer
    (hbasic : ¬ conjSubgroup x R ≤ Subgroup.normalizer (R : Set G) →
      ∀ T' : Subgroup G, T' = conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G) → T' ≠ ⊥ →
        Nat.card ↥(R ⊓ Subgroup.normalizer (T' : Set G)) = Nat.card ↥T' ∧
          R ⊓ Subgroup.normalizer (T' : Set G) = R ⊓ Subgroup.centralizer (T' : Set G)) :
    conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G) = conjSubgroup x Z := by
  set T' := conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G) with hT'
  have hZxT : conjSubgroup x Z ≤ T' :=
    le_inf (conjSubgroup_mono D.Z_le_R) (D.Zx_le_P.trans D.P_le_normalizer_R)
  have hT'0 : T' ≠ ⊥ := by
    intro hbot
    have hle : conjSubgroup x Z ≤ ⊥ := hbot ▸ hZxT
    have := Subgroup.card_le_of_le hle
    rw [D.card_Zx, Subgroup.card_bot] at this
    omega
  obtain ⟨hcard, hcent⟩ := hbasic D.not_conj_R_le_normalizer T' hT' hT'0
  have hle : R ⊓ Subgroup.normalizer (T' : Set G) ≤ Z := by
    rw [hcent]
    intro r hr
    exact D.cent_Zx hr.1 fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hr.2 u (hZxT hu)).symm
  have h1 := Subgroup.card_le_of_le hle
  rw [hcard, D.card_Z] at h1
  exact (Subgroup.eq_of_le_of_card_ge hZxT (by rw [D.card_Zx]; exact h1)).symm

theorem conj_H_inf_normalizer
    (hRx : conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G) = conjSubgroup x Z) :
    conjSubgroup x (W ⊓ R) ⊓ Subgroup.normalizer ((W ⊓ R : Subgroup G) : Set G) =
      conjSubgroup x Z := by
  refine le_antisymm (fun v hv => ?_) (le_inf ?_ ?_)
  · rw [← hRx]
    exact ⟨conjSubgroup_mono inf_le_right hv.1, D.N_H_le_N_R hv.2⟩
  · exact conjSubgroup_mono D.Z_le_H
  · exact D.Zx_le_P.trans D.P_le_normalizer_H

theorem cent_eq :
    (W ⊓ R) ⊓ Subgroup.centralizer ((conjSubgroup x Z : Subgroup G) : Set G) = Z := by
  refine le_antisymm (fun r hr => ?_) (le_inf D.Z_le_H fun z hz => ?_)
  · exact D.cent_Zx hr.1.2 fun u hu => (Subgroup.mem_centralizer_iff.mp hr.2 u hu).symm
  · exact Subgroup.mem_centralizer_iff.mpr fun u hu => D.P_comm (D.Zx_le_P hu) (D.Z_le_P hz)

end C4Data

end CFSG.CGT.PushingUpLit.SolKNA
