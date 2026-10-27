module

public import CFSG.CGT.PushingUpLit.SolKNA.BranchC4Frame
public import CFSG.CGT.PushingUpLit.SolKNA.Lemma14

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.PushingUpLit.SolKAb (IsCommSubgroup)

open CFSG.RankThree.GF2n (exists_mul_of_mem_sup)

open C4Aux

variable {G : Type} [Group G]

section Certs


variable [Finite G]

theorem exists_x_normalizer_P {R T W R₁ : Subgroup G} (A : AData R T W) (hT4 : Nat.card ↥T = 4)
    (tight : TightlyEmbedded R) (tight₁ : TightlyEmbedded R₁) (h2₁ : IsPGroup 2 R₁)
    (hRR₁ : R ⊓ R₁ = ⊥) (hTR₁ : T ≤ R₁) (hcard : Nat.card ↥R₁ = Nat.card ↥R)
    (hR₁N : ∀ y ∈ R₁, y ∈ Subgroup.normalizer (R : Set G) → y ∈ T) :
    ∃ x, x ∈ Subgroup.normalizer (((R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T : Subgroup G) :
        Set G) ∧ x ∉ Subgroup.normalizer (R : Set G) := by
  set Z : Subgroup G := R ⊓ Subgroup.normalizer (T : Set G) with hZdef
  have hcardZ : Nat.card ↥Z = 4 := by rw [hZdef, A.card_N_eq, hT4]
  have hcardR : Nat.card ↥R = 32 := by
    rw [A.card_R, A.card_H, hT4]
    norm_num
  have hZR : Z ≤ R := inf_le_left
  have hZ2 : IsPGroup 2 ↥Z := A.two_R.to_le hZR
  have hZ1 : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardZ
    omega
  obtain ⟨t₀, ht₀, ht₀1⟩ : ∃ t ∈ T, t ≠ 1 := exists_ne_one_of_ne_bot A.T_ne
  have hZN₁ : Z ≤ Subgroup.normalizer (R₁ : Set G) := by
    intro z hz
    have hzt : z * t₀ * z⁻¹ = t₀ := by
      have := A.N_comm hz ht₀
      rw [this]
      group
    exact normalizer_of_tight tight₁ h2₁ (hTR₁ ht₀) ht₀1 (by rw [hzt]; exact hTR₁ ht₀)
  have hZR₁ : Z ⊓ R₁ = ⊥ := by
    rw [eq_bot_iff]
    calc Z ⊓ R₁ ≤ R ⊓ R₁ := inf_le_inf hZR le_rfl
      _ = ⊥ := hRR₁
      _ ≤ ⊥ := le_rfl
  have hcomm : IsCommSubgroup Z := fun a ha b hb =>
    comm_of_sq_eq_one (fun n hn => A.elem_N hn) ha hb
  have hnc : ¬ IsCyclic ↥Z := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Z)
    have hg2 : g ^ 2 = 1 := by
      rw [pow_two]
      exact Subtype.ext (A.elem_N g.2)
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
    rw [hg, hcardZ] at this
    omega
  have hN₁ : R₁ ⊓ Subgroup.normalizer (Z : Set G) = T := by
    refine le_antisymm (fun y hy => ?_) (le_inf hTR₁ A.T_le_normalizer_N)
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := exists_ne_one_of_ne_bot hZ1
    have hyz : y * z * y⁻¹ ∈ R := hZR ((Subgroup.mem_normalizer_iff.mp hy.2 z).mp hz)
    exact hR₁N y hy.1 (normalizer_of_tight tight A.two_R (hZR hz) hz1 hyz)
  have hTI : ∀ x ∈ R₁ ⊔ Z, Z ⊓ rightConjugate Z x ≠ ⊥ → rightConjugate Z x = Z := by
    intro x hx hne
    obtain ⟨s, hs, z₀, hz₀, rfl⟩ := exists_mul_of_mem_sup hZN₁ hx
    obtain ⟨y, hy, hy1⟩ := exists_ne_one_of_ne_bot hne
    have hxR : (s * z₀) * y * (s * z₀)⁻¹ ∈ R := hZR ((mem_rightConjugate_iff Z _ y).mp hy.2)
    have hN : s * z₀ ∈ Subgroup.normalizer (R : Set G) :=
      normalizer_of_tight tight A.two_R (hZR hy.1) hy1 hxR
    have hz₀N : z₀ ∈ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer (hZR hz₀)
    have hsN : s ∈ Subgroup.normalizer (R : Set G) := by
      have e : s = (s * z₀) * z₀⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hN (Subgroup.inv_mem _ hz₀N)
    have hsT : s ∈ T := hR₁N s hs hsN
    exact (rightConjugate_eq_self_iff Z _).mpr
      (Subgroup.mul_mem _ (A.T_le_normalizer_N hsT) (Subgroup.le_normalizer hz₀))
  have hγ : Nat.card ↥(R₁ ⊓ Subgroup.normalizer (Z : Set G)) ≤ Nat.card ↥Z := by
    rw [hN₁, hT4, hcardZ]
  rcases lemma14 h2₁ hZ2 hZ1 hZN₁ hZR₁ hcomm hnc hTI hγ with hle | hB | ⟨W₁, A₁⟩
  · exfalso
    have h1 : R₁ = T := (inf_of_le_left hle).symm.trans hN₁
    have := hcard
    rw [h1, hT4, hcardR] at this
    omega
  · exfalso
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := exists_ne_one_of_ne_bot hZ1
    have hle := hB.relIndex_le_card hz hz1
    rw [hN₁, hT4] at hle
    have h1 := Subgroup.relIndex_mul_card (H := T) (K := R₁)
    rw [inf_of_le_left hTR₁, hT4, hcard, hcardR] at h1
    omega
  · have hW₁P : W₁ ≤ Subgroup.normalizer ((Z ⊔ T : Subgroup G) : Set G) := by
      have h := A₁.W_le_normalizer_P
      rw [hN₁, sup_comm] at h
      exact h
    have hcardP : Nat.card ↥(Z ⊔ T : Subgroup G) = 16 := by
      have := A.card_P
      rw [← hZdef, hT4] at this
      exact this
    have hW₁P' : ¬ W₁ ≤ Z ⊔ T := by
      intro hle
      have h1 := Subgroup.card_le_of_le hle
      rw [A₁.card_W, hcardZ, hcardP] at h1
      omega
    obtain ⟨x, hxW, hxP⟩ : ∃ x ∈ W₁, x ∉ Z ⊔ T := by
      by_contra hcon
      exact hW₁P' fun w hw => by_contra fun h => hcon ⟨w, hw, h⟩
    refine ⟨x, hW₁P hxW, fun hxN => hxP ?_⟩
    obtain ⟨s, hs, z₀, hz₀, rfl⟩ := exists_mul_of_mem_sup hZN₁ (A₁.W_le hxW)
    have hz₀N : z₀ ∈ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer (hZR hz₀)
    have hsN : s ∈ Subgroup.normalizer (R : Set G) := by
      have e : s = (s * z₀) * z₀⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hz₀N)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hR₁N s hs hsN))
      (Subgroup.mem_sup_left hz₀)

end Certs

end CFSG.CGT.PushingUpLit.SolKNA
