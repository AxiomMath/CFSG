module

public import CFSG.ClassicalInvolution.Q3.Q3MFO4Core
public import CFSG.ClassicalInvolution.Asc77.AscCX9X2
public import CFSG.ClassicalInvolution.Q3.Q3NMDiag

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFO4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4 CFSG.ClassicalInvolution.Asc77.CX.MF2L
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_eq_bot_of_odd_mem_sub {H N : Subgroup G} (hNH : N ≤ H)
    (hodd : ∀ g ∈ H, Odd (orderOf g) → g ∈ N) (hN : oddCoreIn N = ⊥) : oddCoreIn H = ⊥ := by
  have h1 : oddCoreIn H ≤ N := fun g hg =>
    hodd g (oddCoreIn_le H hg) (Odd.of_dvd_nat (odd_card_oddCoreIn H)
      (Subgroup.orderOf_dvd_natCard _ hg))
  have h2 : oddCoreIn H ≤ oddCoreIn N :=
    le_oddCoreIn_of_normalizes h1 (hNH.trans (normalizer_oddCoreIn H)) (odd_card_oddCoreIn H)
  rw [hN] at h2
  exact le_bot_iff.mp h2

end OddCore

section Graph

variable {F : Type} [Field F] [Finite F]

theorem ker_le_center {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    ((proj 4 F).comp (kappa hm hn)).ker ≤ Subgroup.center (StatedSp 2 F) := by
  intro x hx
  have hx' : kappa hm hn x ∈ (proj 4 F).ker := hx
  rw [ker_proj] at hx'
  have hc := (scalars_eq_center 4 F).le hx'
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  apply kappa_injective hm hn
  rw [map_mul, map_mul, hc (kappa hm hn y)]

theorem isSim_pow {M : Matrix (Fin 4) (Fin 4) F} {g : SL(4, F)} {c : F} (h : IsSim M g c) :
    ∀ k : ℕ, IsSim M (g ^ k) (c ^ k)
  | 0 => by simpa using IsSim.one M
  | k + 1 => by
    rw [pow_succ, pow_succ]
    exact (isSim_pow h k).mul h

theorem isSim_of_scalar {M : Matrix (Fin 4) (Fin 4) F} {g : SL(4, F)} {u : F}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = u • 1) : IsSim M g (u * u) := by
  unfold IsSim
  rw [hg]
  simp [smul_smul]

theorem spForm_ne_zero {m n : F} (hm : m ≠ 0) : spForm m n ≠ 0 := by
  intro h
  apply hm
  have := congrFun (congrFun h 0) 1
  simpa [spForm] using this

theorem isSim_one_of_odd (hF : Nat.card F = 3) {m n : F} (hm : m ≠ 0) {g : SL(4, F)} {c : F}
    (hc0 : c ≠ 0) (hc : IsSim (spForm m n) g c) (hodd : Odd (orderOf (proj 4 F g))) : c = 1 := by
  set k := orderOf (proj 4 F g) with hk
  have hk1 : (proj 4 F g) ^ k = 1 := pow_orderOf_eq_one _
  have hk2 : g ^ k ∈ scalars 4 F := by
    rw [← proj_eq_one_iff, map_pow]
    exact hk1
  obtain ⟨s, -, hs⟩ := mem_scalars.mp hk2
  have hs' : ((g ^ k : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = (s : F) • 1 := by
    rw [hs, Matrix.scalar_apply, ← smul_one_eq_diagonal]
  have h1 := isSim_pow hc k
  have h2 := isSim_of_scalar (M := spForm m n) hs'
  have h3 : c ^ k = (s : F) * s := by
    have h4 : (c ^ k) • spForm m n = ((s : F) * s) • spForm m n := h1.symm.trans h2
    rw [← sub_eq_zero, ← sub_smul] at h4
    exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right (spForm_ne_zero hm))
  have hss : (s : F) * s = 1 := by
    rcases eq_zero_or_one_or_neg_one_of_card hF (s : F) with h | h | h
    · exact absurd h s.ne_zero
    · rw [h]; ring
    · rw [h]; ring
  rcases eq_zero_or_one_or_neg_one_of_card hF c with h | h | h
  · exact absurd h hc0
  · exact h
  · exfalso
    have h5 : (-1 : F) ^ k = 1 := by rw [← h, h3, hss]
    rw [hodd.neg_one_pow] at h5
    exact two_ne_zero_of_card hF (by linear_combination -h5)

theorem oddCoreIn_fixed_graph (hF : Nat.card F = 3) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0)
    (A : GL (Fin 4) F) (hA : (A : Matrix (Fin 4) (Fin 4) F) = spForm m n)
    (hq : CFSG.Open.IsQuasisimple (StatedSp 2 F))
    (hZ : IsPGroup 2 (Subgroup.center (StatedSp 2 F))) :
    oddCoreIn (fixedSubgroup (conjAut 4 F A * dualAut 4 F)) = ⊥ := by
  have hN : oddCoreIn ((proj 4 F).comp (kappa hm hn)).range = ⊥ :=
    oddCoreIn_range_eq_bot_of_isQuasisimple _ hq hZ (ker_le_center hm hn)
  refine oddCoreIn_eq_bot_of_odd_mem_sub (N := ((proj 4 F).comp (kappa hm hn)).range) ?_ ?_ hN
  · rintro _ ⟨x, rfl⟩
    have hg : kappa hm hn x ∈ spM (A : Matrix (Fin 4) (Fin 4) F) := by
      rw [hA]
      exact kappa_mem_spM hm hn x
    have h1 := slConj_eq_of_mem_spM A hg
    show (conjAut 4 F A * dualAut 4 F) (proj 4 F (kappa hm hn x)) = proj 4 F (kappa hm hn x)
    rw [MulAut.mul_apply, dualAut_proj, conjAut_proj, h1]
  · intro y hy hodd
    obtain ⟨g, rfl⟩ := proj_surjective 4 F y
    have hy' : (conjAut 4 F A * dualAut 4 F) (proj 4 F g) = proj 4 F g := hy
    rw [MulAut.mul_apply, dualAut_proj, conjAut_proj] at hy'
    obtain ⟨c, hc0, hc⟩ := mem_simM_of_proj_eq A hy'
    rw [hA] at hc
    have hc1 := isSim_one_of_odd hF hm hc0 hc hodd
    rw [hc1] at hc
    have hg : g ∈ spM (spForm m n) := by
      rw [mem_spM]
      have h := hc
      unfold IsSim at h
      rwa [one_smul] at h
    rw [← kappa_range hm hn] at hg
    obtain ⟨x, rfl⟩ := hg
    exact ⟨x, rfl⟩

end Graph

section Main

variable {F : Type} [Field F] [Finite F]

@[expose] def projEquiv : projectiveSL 4 F ≃* (SL(4, F) ⧸ Subgroup.center SL(4, F)) :=
  QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 4 F)

theorem congr_conjAut (A : GL (Fin 4) F) :
    MulAut.congr (projEquiv (F := F)).symm (autToCentralQuotient SL(4, F) (conjSLAut A)) =
      conjAut 4 F A := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective 4 F x
  show (projEquiv (F := F)).symm (autToCentralQuotient SL(4, F) (conjSLAut A)
      ((projEquiv (F := F)) (proj 4 F g))) = conjAut 4 F A (proj 4 F g)
  have h1 : (projEquiv (F := F)) (proj 4 F g) = QuotientGroup.mk g := rfl
  rw [h1, autToCentralQuotient_mk, conjAut_proj]
  have h2 : conjSLAut A g =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A g := by
    apply Subtype.ext
    rw [conjSLAut_coe, coe_slConjugation]
  rw [h2]
  rfl

theorem oddCoreIn_fixed_eq_bot_proj4 (hF : Nat.card F = 3)
    (hSL : CFSG.Open.IsQuasisimple SL(4, F)) (hSLZ : IsPGroup 2 (Subgroup.center SL(4, F)))
    (hSp : CFSG.Open.IsQuasisimple (StatedSp 2 F))
    (hSpZ : IsPGroup 2 (Subgroup.center (StatedSp 2 F)))
    (ρ : MulAut (projectiveSL 4 F)) (hρ2 : ρ * ρ = 1)
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, ρ (proj 4 F r) = proj 4 F r) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hρ⟩ := hgen ρ
  have hσ := ringEquiv_eq_refl hF σ
  subst hσ
  have hσ1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
  interval_cases ε
  ·
    have hρ' : ρ = conjAut 4 F A := by rw [hρ, hσ1, pow_zero, mul_one, mul_one]
    subst hρ'
    have hAA := core_zero hF A hfix hρ2
    by_cases hD : conjSLAut A = 1
    · have hone : conjAut 4 F A = 1 := by
        ext x
        obtain ⟨g, rfl⟩ := proj_surjective 4 F x
        rw [conjAut_proj, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        have h := congrArg (fun φ : MulAut SL(4, F) => (φ g : Matrix (Fin 4) (Fin 4) F)) hD
        simp only [conjSLAut_coe, MulAut.one_apply] at h
        rw [coe_slConjugation]
        exact h
      have hTop : oddCoreIn (⊤ : Subgroup (projectiveSL 4 F)) = ⊥ := by
        have h := oddCoreIn_range_eq_bot_of_isQuasisimple (proj 4 F) hSL hSLZ
          (by rw [ker_proj]; exact (scalars_eq_center 4 F).le)
        rwa [MonoidHom.range_eq_top_of_surjective _ (proj_surjective 4 F)] at h
      have hfx : fixedSubgroup (1 : MulAut (projectiveSL 4 F)) = ⊤ := by
        ext x
        simp [mem_fixedSubgroup_iff]
      rw [hone, hfx]
      exact hTop
    · have h := oddCoreIn_fixed_conjInvol_eq_bot hF A hAA hD
      have h' := oddCoreIn_fixed_congr_eq_bot' (projEquiv (F := F)).symm _ h
      rwa [congr_conjAut] at h'
  ·
    have hρ' : ρ = conjAut 4 F A * dualAut 4 F := by rw [hρ, hσ1, pow_one, mul_one]
    subst hρ'
    obtain ⟨m, n, hm, hn, hAm⟩ := core_one hF A hfix hρ2
    exact oddCoreIn_fixed_graph hF hm hn A hAm hSp hSpZ

end Main

end CFSG.ClassicalInvolution.Q3.Q3MFO4
