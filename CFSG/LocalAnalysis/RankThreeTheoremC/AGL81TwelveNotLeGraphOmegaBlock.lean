module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeU42O8Levi
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusHat

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Omega

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.OmegaMinusEight

theorem card_GL_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : m = 1) :
    Nat.card (GL (Fin m) K) = 1 := by
  subst hm
  haveI := Fintype.ofFinite K
  have h := Matrix.card_GL_field (n := 1) (𝔽 := K)
  rw [← Nat.card_eq_fintype_card, hK] at h
  rw [h]
  decide

theorem card_GL_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : m = 2) :
    Nat.card (GL (Fin m) K) = 6 := by
  subst hm
  haveI := Fintype.ofFinite K
  have h := Matrix.card_GL_field (n := 2) (𝔽 := K)
  rw [← Nat.card_eq_fintype_card, hK] at h
  rw [h]
  decide

theorem prod_card_GL_dvd_six {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {s : ℕ}
    {d : Fin (s + 1) → ℕ} (hd : OrthCuts 3 d) (hlast : d (Fin.last s) = 3)
    (h3 : ∀ l : Fin s, d l.succ - d l.castSucc ≠ 3) :
    ∏ l : Fin s, Nat.card (GL (Fin (d l.succ - d l.castSucc)) K) ∣ 6 := by
  have hpos : ∀ l : Fin s, 1 ≤ d l.succ - d l.castSucc := fun l => by
    have := hd.mono (Fin.castSucc_lt_succ (i := l))
    omega
  have hle : ∀ l : Fin s, d l.succ ≤ 3 := fun l => by
    have := hd.mono.monotone (Fin.le_last l.succ)
    omega
  have hle2 : ∀ l : Fin s, d l.succ - d l.castSucc ≤ 2 := fun l => by
    have := hle l
    have := h3 l
    omega
  have hone : ∀ l l' : Fin s, l ≠ l' → d l.succ - d l.castSucc = 2 →
      d l'.succ - d l'.castSucc = 2 → False := by
    intro l l' hne h1 h2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hd.mono.monotone (Fin.succ_le_castSucc_iff.2 hlt)
      have := hle l'
      omega
    · have := hd.mono.monotone (Fin.succ_le_castSucc_iff.2 hlt)
      have := hle l
      omega
  by_cases hex : ∃ l₀ : Fin s, d l₀.succ - d l₀.castSucc = 2
  · obtain ⟨l₀, hl₀⟩ := hex
    rw [Finset.prod_eq_single l₀]
    · rw [card_GL_two hK hl₀]
    · intro l _ hne
      have h1 : d l.succ - d l.castSucc = 1 := by
        have := hpos l
        have := hle2 l
        by_contra hcon
        exact hone l l₀ hne (by omega) hl₀
      exact card_GL_one hK h1
    · intro h
      exact absurd (Finset.mem_univ l₀) h
  · push Not at hex
    rw [Finset.prod_eq_one]
    · exact one_dvd _
    · intro l _
      have h1 : d l.succ - d l.castSucc = 1 := by
        have := hpos l
        have := hle2 l
        have := hex l
        omega
      exact card_GL_one hK h1

theorem commutator_range_toGL_of_eq_three {K : Type} [Field K] {m : ℕ} (hm : m = 3) :
    ⁅(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range,
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range⁆ =
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range := by
  subst hm
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
  have h0 : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)), ⊤⁆ = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  have h1 := Subgroup.map_commutator (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) ⊤
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K)
  rw [h0, ← MonoidHom.range_eq_map] at h1
  exact h1.symm

theorem card_range_toGL_of_eq_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {m : ℕ} (hm : m = 3) :
    Nat.card ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range = 168 := by
  subst hm
  rw [← Nat.card_congr (slEquivToGLRange (K := K) 3).toEquiv]
  have h := Matrix.card_SL_mul_card_units (n := Fin 3) (R := K)
  rw [Nat.card_units, hK, card_GL_three hK] at h
  omega

section Lift

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {K : Type} [Field K] [Finite K]
  [CharP K 2] {b c : K} {s : ℕ} {d : Fin (s + 1) → ℕ}

theorem exists_perfect_of_le_range (C : OmCover Y P 3 K b c d) (hd : OrthCuts 3 d)
    {S' : Subgroup (∀ j, orthLeviGroup K 3 d j)} (hle : S' ≤ (orthLeviHom b c hd).range)
    (hperf : ⁅S', S'⁆ = S') :
    ∃ J : Subgroup A, J ≤ P ∧ ⁅J, J⁆ = J ∧ Nat.card S' ∣ Nat.card J := by
  classical
  haveI : Finite ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))) :=
    Finite.of_equiv _ C.ρ.symm.toEquiv
  obtain ⟨W, hWperf, hWmap⟩ := exists_perfect_map_eq (orthLeviHom b c hd) hle hperf
  refine ⟨(W.map C.toP).map P.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hWperf]
  · rw [Subgroup.card_map_of_injective P.subtype_injective,
      Subgroup.card_map_of_injective C.toP_injective]
    have h1 : Nat.card ↥(W.map (orthLeviHom b c hd)) ∣ Nat.card W :=
      Subgroup.card_map_dvd W (orthLeviHom b c hd)
    rwa [hWmap] at h1

theorem exists_perfect_of_block (C : OmCover Y P 3 K b c d) (hd : OrthCuts 3 d)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hK : Nat.card K = 2) {l : Fin s}
    (hl : d l.succ - d l.castSucc = 3) :
    ∃ J : Subgroup A, J ≤ P ∧ ⁅J, J⁆ = J ∧ 3 ∣ Nat.card J := by
  classical
  set S : Subgroup (orthLeviGroup K 3 d (.inl l)) := orthLeviBlock K 3 d b c (.inl l) with hS
  have hperfS : ⁅S, S⁆ = S := commutator_range_toGL_of_eq_three hl
  have hcardS : Nat.card S = 168 := card_range_toGL_of_eq_three hK hl
  set S' : Subgroup (∀ j, orthLeviGroup K 3 d j) :=
    S.map (MonoidHom.mulSingle (orthLeviGroup K 3 d) (.inl l)) with hS'
  have hS'perf : ⁅S', S'⁆ = S' := by
    rw [hS', ← Subgroup.map_commutator, hperfS]
  have hS'le : S' ≤ (orthLeviHom b c hd).range := by
    refine le_trans ?_ (pi_orthLeviBlock_le_range hd le_rfl
      (commutator_orthogonalGroup_quadTail_minus (by norm_num) hirr))
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_pi]
    intro j _
    by_cases hj : j = .inl l
    · subst hj
      rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
      exact hx
    · rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
      exact one_mem _
  obtain ⟨J, hJP, hJperf, hJdvd⟩ := exists_perfect_of_le_range C hd hS'le hS'perf
  refine ⟨J, hJP, hJperf, ?_⟩
  rw [hS', Subgroup.card_map_of_injective
    (Pi.mulSingle_injective (M := orthLeviGroup K 3 d) (Sum.inl l : Fin s ⊕ Unit)), hcardS] at hJdvd
  exact (by norm_num : 3 ∣ 168).trans hJdvd

end Lift

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Omega
