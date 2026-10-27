module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartPure

public section

namespace CFSG.OddStandard.ChengHeld.M1b

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

section Rho


theorem repPerm_conj_T0 {i : ℕ} (hi : i < 36) (t : Equiv.Perm (Fin 42)) :
    repPerm i * t * (repPerm i)⁻¹ ∈ T0 ↔ t ∈ T0 := by
  refine conj_T0_iff (fun t ht => ?_) t
  obtain ⟨k, hk, rfl⟩ := exists_tg ht
  rw [conj_tg hi hk]
  exact tg_mem_T0 _ (alpha_lt hi hk)

theorem repPerm_inv_conj_T0 {i : ℕ} (hi : i < 36) (x : Equiv.Perm (Fin 42)) :
    (repPerm i)⁻¹ * x * repPerm i ∈ T0 ↔ x ∈ T0 := by
  have := repPerm_conj_T0 hi ((repPerm i)⁻¹ * x * repPerm i)
  rw [show repPerm i * ((repPerm i)⁻¹ * x * repPerm i) * (repPerm i)⁻¹ = x by group] at this
  exact this.symm

end Rho

theorem repPerm_comm_r4 (hC : ChCoverParts) {i : ℕ} (hi : i = 4 ∨ i = 5) :
    repPerm i * repPerm 3 = repPerm 3 * repPerm i := by
  have h := hC.comm
  rw [commOK, List.all_eq_true] at h
  have h1 := h i (by rcases hi with rfl | rfl <;> simp)
  have hi36 : i < 36 := by rcases hi with rfl | rfl <;> norm_num
  have hy := (tabRep_repTab hi36).comp (tabRep_repTab (i := 3) (by norm_num))
  have hy' := (tabRep_repTab (i := 3) (by norm_num)).comp (tabRep_repTab hi36)
  exact (hy.beq_iff hy').1 (by simpa using h1)

section Ker

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}
  (d : Datum A)

theorem zStarIn_eq (h : Hyp G A) : zStarIn A = A ⊓ centralizer (A : Set G) := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a ∈ center ↥A := by rwa [h.fusionZStar_eq_center] at ha
    rw [mem_center_iff] at ha'
    refine ⟨a.2, mem_centralizer_iff.2 fun g hg => ?_⟩
    exact congrArg Subtype.val (ha' ⟨g, hg⟩)
  · rintro ⟨hzA, hzC⟩
    exact mem_zStarIn_of_mem_center h hzA hzC

theorem ker_card (P : Pos d) (h : Hyp G A) :
    Nat.card ↥P.q.ker = Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) ∧
      (IsCyclic ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) → IsCyclic ↥P.q.ker) := by
  obtain ⟨ζ, -⟩ := exists_zeta (S_isSylowTwoIn d) P.isQ.ker
  have hEq : d.S ⊓ zStarIn A = d.X ⊓ A ⊓ centralizer (A : Set G) := by
    rw [zStarIn_eq h]
    ext z
    simp only [Datum.S, mem_inf]
    tauto
  have hcard : Nat.card ↥(d.S ⊓ zStarIn A) = Nat.card ↥P.q.ker := Nat.card_congr ζ.toEquiv
  rw [hEq] at hcard
  refine ⟨hcard.symm, fun hc => ?_⟩
  rw [← hEq] at hc
  exact isCyclic_of_surjective ζ.toMonoidHom ζ.surjective

end Ker

section Twist

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}
  (d : Datum A)

theorem exists_pos_twist (P : Pos d) (hC : ChCoverParts)
    (hno : ∀ k : ℕ, (k = 1 ∨ k = 2) → ∀ y : G, y ∈ d.X → ∀ s : G, s ∈ d.S →
      ∀ hys : y * s ∈ d.X, ¬ Pure d P.l k (y * s) hys)
    {i : ℕ} (hi : i = 0 ∨ i = 4 ∨ i = 5) {l' : Cover →* Jhat A}
    (hl' : IsQSetting ((MulAut.conj (repPerm i)⁻¹).toMonoidHom.comp P.q) l') :
    ∃ P' : Pos d, P'.l = l' := by
  have hi36 : i < 36 := by rcases hi with rfl | rfl | rfl <;> norm_num
  have hcomm : repPerm i * repPerm 3 = repPerm 3 * repPerm i := by
    rcases hi with rfl | rfl | rfl
    · rw [repPerm_zero, one_mul, mul_one]
    · exact repPerm_comm_r4 hC (Or.inl rfl)
    · exact repPerm_comm_r4 hC (Or.inr rfl)
  refine ⟨⟨(MulAut.conj (repPerm i)⁻¹).toMonoidHom.comp P.q, l', hl', fun e => ?_,
    fun y hy => ?_⟩, rfl⟩
  · have h1 : ((MulAut.conj (repPerm i)⁻¹).toMonoidHom.comp P.q) e =
        (repPerm i)⁻¹ * P.q e * repPerm i := by simp
    rw [h1, repPerm_inv_conj_T0 hi36, P.hT]
  · obtain ⟨k, hk4, t, ht, hreal, s, hs, hys, hp⟩ := pure_exists d P hy
    have hk03 : k = 0 ∨ k = 3 := by
      by_contra hne
      push Not at hne
      exact hno k (by omega) y hy s hs hys hp
    have hvc : repPerm i * repPerm k = repPerm k * repPerm i := by
      rcases hk03 with rfl | rfl
      · simp [repPerm_zero]
      · exact hcomm
    refine ⟨(repPerm i)⁻¹ * (wordPerm (tg t) * repPerm k) * repPerm i, ?_, fun e => ?_⟩
    · refine ⟨(repPerm i)⁻¹ * wordPerm (tg t) * repPerm i,
        (repPerm_inv_conj_T0 hi36 _).2 (tg_mem_T0 t ht), repPerm k, ?_, ?_⟩
      · rcases hk03 with rfl | rfl
        · exact Or.inl repPerm_zero
        · rw [repPerm_three]
          exact Or.inr (Or.inr (Or.inr rfl))
      · calc (repPerm i)⁻¹ * (wordPerm (tg t) * repPerm k) * repPerm i
            = (repPerm i)⁻¹ * wordPerm (tg t) * (repPerm k * repPerm i) := by group
          _ = (repPerm i)⁻¹ * wordPerm (tg t) * (repPerm i * repPerm k) := by rw [hvc]
          _ = (repPerm i)⁻¹ * wordPerm (tg t) * repPerm i * repPerm k := by group
    · have h1 : ((MulAut.conj (repPerm i)⁻¹).toMonoidHom.comp P.q) e =
          (repPerm i)⁻¹ * P.q e * repPerm i := by simp
      have h2 : ((MulAut.conj (repPerm i)⁻¹).toMonoidHom.comp P.q)
          (betaHat A (d.X_sylow.le hy) e) =
          (repPerm i)⁻¹ * P.q (betaHat A (d.X_sylow.le hy) e) * repPerm i := by
        simp
      rw [h1, h2, hreal e]
      group

theorem exists_pos_std4 (h : Hyp G A) (hC : ChCoverParts)
    (hc4 : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4)
    (hcyc : IsCyclic ↥(d.X ⊓ A ⊓ centralizer (A : Set G))) :
    ∃ (P : Pos d) (α : ℕ), α ≤ 1 ∧ ∀ a b : ZMod 4, zz P.l a b = 1 ↔ inK (kapOf α) a b := by
  obtain ⟨P₀⟩ := exists_pos h d
  have hA : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr h.commutator_eq_top)
  have hE : commutator (Jhat A) = ⊤ := commutator_jhat hA
  obtain ⟨hk, hkc⟩ := ker_card d P₀ h
  have h4 : Nat.card ↥P₀.q.ker = 4 := hk.trans hc4
  have hc : IsCyclic ↥P₀.q.ker := hkc hcyc
  by_cases hFG : ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ ∃ (y : G) (hy : y ∈ d.X) (s : G) (hs : s ∈ d.S)
      (hys : y * s ∈ d.X), Pure d P₀.l k (y * s) hys
  · obtain ⟨k, hk12, y, hy, s, hs, hys, hp⟩ := hFG
    obtain ⟨α, hα, hstd⟩ := std_of_FG hC P₀.isQ hc h4 hk12
      (β := betaHat A (d.X_sylow.le hys)) hp
    exact ⟨P₀, α, hα, hstd⟩
  · obtain ⟨i, hi, l', hl', α, hα, hstd⟩ := std_after_twist hC hE P₀.isQ hc h4
    obtain ⟨P', rfl⟩ := exists_pos_twist d P₀ hC
      (fun k hk y hy s hs hys hp => hFG ⟨k, hk, y, hy, s, hs, hys, hp⟩) (i := i)
      (by simpa using hi) hl'
    exact ⟨P', α, hα, hstd⟩

theorem exists_pos_std2 (h : Hyp G A) (hC : ChCoverParts)
    (hc2 : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 2) :
    ∃ P : Pos d, ∀ a b : ZMod 4, zz P.l a b = 1 ↔ b.val % 2 = 0 := by
  obtain ⟨P₀⟩ := exists_pos h d
  have hA : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr h.commutator_eq_top)
  have hE : commutator (Jhat A) = ⊤ := commutator_jhat hA
  obtain ⟨hk, -⟩ := ker_card d P₀ h
  have h2 : Nat.card ↥P₀.q.ker = 2 := hk.trans hc2
  by_cases hFG : ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ ∃ (y : G) (hy : y ∈ d.X) (s : G) (hs : s ∈ d.S)
      (hys : y * s ∈ d.X), Pure d P₀.l k (y * s) hys
  · obtain ⟨k, hk12, y, hy, s, hs, hys, hp⟩ := hFG
    exact ⟨P₀, std2_of_FG hC P₀.isQ h2 hk12 (β := betaHat A (d.X_sylow.le hys)) hp⟩
  · obtain ⟨i, hi, l', hl', hstd⟩ := std2_after_twist hC hE P₀.isQ h2
    obtain ⟨P', rfl⟩ := exists_pos_twist d P₀ hC
      (fun k hk y hy s hs hys hp => hFG ⟨k, hk, y, hy, s, hs, hys, hp⟩) (i := i)
      (by simpa using hi) hl'
    exact ⟨P', hstd⟩

end Twist

end CFSG.OddStandard.ChengHeld.M1b
