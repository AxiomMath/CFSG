module

public import CFSG.ClassicalInvolution.Q3.Q3T7F25M5
public import CFSG.ClassicalInvolution.Asc77.AscT7DRCoord

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7F25

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

namespace Asc77

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem c25_19_of_sylow_at (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (h2 : ∃ t' ∈ (S : Subgroup G),
    (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R') (h17 : Nat.card ↥(S : Subgroup G)
        = 2 * Nat.card ↥(R ⊔ R') ∨ Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')) :
    Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') ∨ TwoSubgroupsFourGenerated G := by
  by_cases h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')
  · exact Or.inl h4
  · refine Or.inr ?_
    have hidx : Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R') := by
      rcases h17 with h | h
      · exact h
      · exact absurd h h4
    obtain ⟨t', ht'S, hg, hconj⟩ := h2
    exact T7DR.tf4_of_index_two hyp hidx ht'S hg hconj

theorem c25_21_of_sylow_coord_at (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (h20 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') → ∃ a b s t' : G, a ∈ R ∧ b ∈ R
        ∧ Subgroup.closure ({a, b} : Set G) = R ∧ b * a * b⁻¹ = a⁻¹ ∧ (∃ k : ℤ, b * b = a ^ k)
            ∧ s ∈ (S : Subgroup G) ∧ t' ∈ (S : Subgroup G) ∧ (∃ g : G, g * z * g⁻¹ = t')
                ∧ conjSub t' R = R' ∧ Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G)
                    ∧ s * s = 1 ∧ s * t' = t' * s ∧ s * a * s⁻¹ = a⁻¹ ∧ s * b * s⁻¹ = b * a) :
    Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') → TwoSubgroupsFourGenerated G := by
  intro h4
  obtain ⟨a, b, s, t', haR, hbR, -, hbab, hk, hs, ht', hg, hconj, hSgen, hs2, hst, hsa, hsb⟩ :=
    h20 h4
  exact (T7DR.tf4_of_index_four hyp haR hbR hbab hk hs ht' hg hconj hSgen hs2 hst hsa hsb)

theorem c25_20_coord_of_at (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (h : Nat.card ↥(S : Subgroup G)
    = 4 * Nat.card ↥(R ⊔ R') → ∃ s t' : G, s ∈ (S : Subgroup G) ∧ t' ∈ (S : Subgroup G) ∧
        (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R' ∧ s * s = 1 ∧ s * t' = t' * s ∧ conjSub s R
            = R ∧ (∃ r ∈ R, ⁅s, r⁆ ∉ T7DR.squaresSub R) ∧ Subgroup.closure
                (((R ⊔ R' : Subgroup G) : Set G) ∪ {s, t'}) = (S : Subgroup G)) :
    Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') → ∃ a b s t' : G, a ∈ R ∧ b ∈ R
        ∧ Subgroup.closure ({a, b} : Set G) = R ∧ b * a * b⁻¹ = a⁻¹ ∧ (∃ k : ℤ, b * b = a ^ k)
            ∧ s ∈ (S : Subgroup G) ∧ t' ∈ (S : Subgroup G) ∧ (∃ g : G, g * z * g⁻¹ = t')
                ∧ conjSub t' R = R' ∧ Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G)
                    ∧ s * s = 1 ∧ s * t' = t' * s ∧ s * a * s⁻¹ = a⁻¹ ∧ s * b * s⁻¹ = b * a := by
  intro h4
  obtain ⟨s, t', hsS, ht'S, hg, hconj, hs2, hst, hsR, hnt, hgen⟩ :=
    h h4
  have hsetting : Hyp23Setting Ω K K' z := hyp.std.setting
  have hquat : IsQuatSub R := hsetting.stand.hyp.isQuatSub_of_mem_RSet hyp.hR.1
  have hsR' : ∀ r ∈ R, s * r * s⁻¹ ∈ R := fun r hr => by
    have := conj_mem_conjSub (n := s) hr
    rwa [hsR] at this
  obtain ⟨a, b, haR, hbR, hclos, hbab, hk, hsa, hsb⟩ := T7DR.exists_coord hquat hs2 hsR' hnt
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hSclos : Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hRS haR
      · exact hRS hbR
      · exact hsS
      · exact ht'S
    · rw [← hgen, Subgroup.closure_le]
      have hRc : R ≤ Subgroup.closure ({a, b, s, t'} : Set G) := by
        rw [← hclos]
        exact Subgroup.closure_mono (fun x hx => by
          rcases hx with rfl | hx
          · simp
          · rw [Set.mem_singleton_iff] at hx
            subst hx
            simp)
      have ht'c : t' ∈ Subgroup.closure ({a, b, s, t'} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hsc : s ∈ Subgroup.closure ({a, b, s, t'} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hR'c : R' ≤ Subgroup.closure ({a, b, s, t'} : Set G) := by
        intro x hx
        have hx' : x ∈ conjSub t' R := by rw [hconj]; exact hx
        rw [mem_conjSub_iff] at hx'
        have h1 := hRc hx'
        have : x = t' * (t'⁻¹ * x * t') * t'⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht'c h1) (Subgroup.inv_mem _ ht'c)
      rintro x (hx | hx)
      · exact (sup_le hRc hR'c) hx
      · rcases hx with rfl | hx
        · exact hsc
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact ht'c
  exact ⟨a, b, s, t', haR, hbR, hclos, hbab, hk, hsS, ht'S, hg, hconj, hSclos, hs2, hst, hsa, hsb⟩

theorem c25_17_idx_of_norm_at (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (h : Nat.card ↥((S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) ≤ 2 * Nat.card ↥(R ⊔ R')) :
    Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R') ∨ Nat.card ↥(S : Subgroup G)
        = 4 * Nat.card ↥(R ⊔ R') := by
  have hS := T7ER.card_eq_two_mul_normalizer hyp
  have hle : R ⊔ R' ≤ (S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) :=
    le_inf (sup_le hyp.hR.2.2 hyp.hR'.2.2) (T7ER.sup_le_normalizer hyp)
  have hbound := h
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card ↥(R ⊔ R') := Nat.card_pos
  have hm2 : m ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(R ⊔ R') * m := by nlinarith
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card ↥((S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) := Nat.card_pos
    omega
  have hm12 : m = 1 ∨ m = 2 := by omega
  rcases hm12 with rfl | rfl
  · left
    rw [hS, hm]
    ring
  · right
    rw [hS, hm]
    ring

namespace T7G2
open CFSG.ClassicalInvolution.Asc77.T7G2
open CFSG.ClassicalInvolution.Asc77.T7F2 CFSG.ClassicalInvolution.Asc77.T7DR

theorem c25_20_of_ex_at (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (h11 : (S : Subgroup G)
    ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) = Subgroup.zpowers z) (h16 : ∀ a ∈
        (S : Subgroup G), ¬ IsFAut R' a) (hex : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')
            → ∃ t' ∈ (S : Subgroup G), t' * t' = 1 ∧ (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R
                = R' ∧ ∃ s ∈ (S : Subgroup G), conjSub s R = R ∧ s ∉ R ⊔ R' ∧ s * t' = t' * s
                    ∧ s * s = 1) :
    Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') → ∃ s t' : G, s ∈ (S : Subgroup G) ∧ t' ∈
        (S : Subgroup G) ∧ (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R' ∧ s * s = 1 ∧ s * t'
            = t' * s ∧ conjSub s R = R ∧ (∃ r ∈ R, ⁅s, r⁆ ∉ T7DR.squaresSub R) ∧ Subgroup.closure
                (((R ⊔ R' : Subgroup G) : Set G) ∪ {s, t'}) = (S : Subgroup G) := by
  intro h4
  obtain ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, s, hsS, hsR, hsn, hst', hs2⟩ :=
    hex h4
  have hT : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t' := ⟨hyp, ht'S, ht'2, ht'R⟩
  obtain ⟨hC', hC, hP', hP, hidx⟩ := struct hT h11 h16 h4
  have hsN : s ∈ Nsub S R := mem_Nsub.mpr ⟨hsS, hsR⟩
  have hti := hT.ht'inv
  refine ⟨s, t', hsS, ht'S, ⟨g, hg⟩, ht'R, hs2, hst', hsR, ?_, ?_⟩
  ·
    have hF : ∀ y ∈ Nsub S R, ¬ IsFAut R' y := fun y hy =>
      h16 y (mem_Nsub.mp hy).1
    have hN2 : IsPGroup 2 ↥(Nsub S R) := S.isPGroup'.to_le (show Nsub S R ≤ _ from inf_le_left)
    have hm : t' * s * t'⁻¹ ∈ Nsub S R := hT.N_conj hsN
    have hmn : t' * s * t'⁻¹ ∉ R' ⊔ (Nsub S R ⊓ Subgroup.centralizer (R' : Set G)) := by
      have heq : Nsub S R ⊓ Subgroup.centralizer (R' : Set G) = Csub S R' := by
        ext x
        constructor
        · rintro ⟨hxN, hxc⟩
          exact mem_Csub.mpr ⟨(mem_Nsub.mp hxN).1,
            fun r hr => Subgroup.mem_centralizer_iff.mp hxc r hr⟩
        · intro hx
          exact ⟨hT.C'_le_N hx, Subgroup.mem_centralizer_iff.mpr (mem_Csub.mp hx).2⟩
      rw [heq]
      have hPeq : R' ⊔ Csub S R' = R ⊔ R' := hP'
      rw [hPeq]
      intro hmem
      apply hsn
      have h1 := conj_mem_RR hT ht'S hmem
      have e : t' * (t' * s * t'⁻¹) * t'⁻¹ = s := by
        calc t' * (t' * s * t'⁻¹) * t'⁻¹ = (t' * t') * s * (t'⁻¹ * t'⁻¹) := by group
          _ = s := by rw [ht'2, hti, ht'2]; group
      rw [e] at h1
      exact h1
    obtain ⟨r', hr', hnot⟩ := exists_comm_not_mem hT.hqR' hT.hzR' hT.R'_le_N hN2
      (fun y hy => hT.conj_R'_of_mem_N hy) hF hm hmn
    have hr : t'⁻¹ * r' * t' ∈ R := by
      have : r' ∈ conjSub t' R := by rw [ht'R]; exact hr'
      exact mem_conjSub_iff.mp this
    refine ⟨t'⁻¹ * r' * t', hr, fun hmem => hnot ?_⟩
    have hconjR : ∀ r ∈ R, t' * r * t'⁻¹ ∈ R' := fun r hr => by
      have := conj_mem_conjSub (n := t') hr
      rwa [ht'R] at this
    have h1 := squaresSub_conj_mem hconjR hmem
    have e : t' * ⁅s, t'⁻¹ * r' * t'⁆ * t'⁻¹ = ⁅t' * s * t'⁻¹, r'⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e] at h1
    exact h1
  ·
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · exact (sup_le hT.hRS hT.hR'S) hx
      · rcases hx with rfl | hx
        · exact hsS
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact ht'S
    · intro x hx
      have hclN : ∀ y ∈ Nsub S R,
          y ∈ Subgroup.closure (((R ⊔ R' : Subgroup G) : Set G) ∪ {s, t'}) := by
        intro y hy
        by_cases hyR : y ∈ R ⊔ R'
        · exact Subgroup.subset_closure (Or.inl hyR)
        · have hs1 : s⁻¹ ∉ R ⊔ R' := fun h1 => hsn (by simpa using (R ⊔ R').inv_mem h1)
          have hmem : s⁻¹ * y ∈ R ⊔ R' :=
            (mul_mem_iff_of_relIndex_two hidx ((Nsub S R).inv_mem hsN) hy).mpr
              (iff_of_false hs1 hyR)
          have e : y = s * (s⁻¹ * y) := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
            (Subgroup.subset_closure (Or.inl hmem))
      have ht'c : t' ∈ Subgroup.closure (((R ⊔ R' : Subgroup G) : Set G) ∪ {s, t'}) :=
        Subgroup.subset_closure (Or.inr (Or.inr rfl))
      rcases hT.S_cover hx with hxN | htxN
      · exact hclN x hxN
      · have e : x = t'⁻¹ * (t' * x) := by group
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.closure _).inv_mem ht'c) (hclN _ htxN)

end T7G2

end Asc77

end CFSG.ClassicalInvolution.T7F25
