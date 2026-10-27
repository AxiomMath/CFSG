module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLinUniMat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonSylow
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreLinMat

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore CFSG.SectionRank.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F]

theorem mem_scalars_iff_toGL {n : ℕ} (s : SpecialLinearGroup (Fin n) F) :
    s ∈ LinearFlag.scalars n F ↔
      ∃ c : Fˣ, SpecialLinearGroup.toGL s = GeneralLinearGroup.scalar (Fin n) c := by
  rw [LinearFlag.mem_scalars]
  constructor
  · rintro ⟨c, -, hs⟩
    refine ⟨c, Units.ext ?_⟩
    rw [SpecialLinearGroup.coe_GL_coe_matrix, hs, GeneralLinearGroup.coe_scalar]
  · rintro ⟨c, hc⟩
    have hmat : (s : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) (c : F) := by
      have := congrArg Units.val hc
      rwa [SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar] at this
    refine ⟨c, ?_, hmat⟩
    have h1 : (s : Matrix (Fin n) (Fin n) F).det = 1 := s.2
    rw [hmat, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
    exact Units.ext (by simpa using h1)

theorem exists_lift_linear {K' : Type} [Group K'] [Finite F] {f n : ℕ} [Fact f.Prime]
    (hf2 : f ≠ 2) (hfn : f ∣ n) (hn : 4 ≤ n) (hfF : f ∣ Nat.card F - 1)
    (ψ : SpecialLinearGroup (Fin n) F →* K') (hψ : Function.Surjective ψ)
    (hker : ∀ s, ψ s = 1 ↔ s ∈ LinearFlag.scalars n F)
    {z : K'} (hz : orderOf z = f) (S : Sylow f K') (hzS : z ∈ (S : Subgroup K'))
    (hcen : ∀ s ∈ (S : Subgroup K'), z * s = s * z) :
    ∃ A : SpecialLinearGroup (Fin n) F, A ^ f = 1 ∧ ψ A = z := by
  classical
  haveI := Fintype.ofFinite F
  have hp : f.Prime := Fact.out
  have hFc : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  have hfF' : f ∣ Fintype.card F - 1 := by rwa [hFc]
  have hF1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have hCa : Nat.card (unitsPPart F f) = f ^ padicValNat f (Fintype.card F - 1) :=
    card_unitsPPart F f
  have ha : 1 ≤ padicValNat f (Fintype.card F - 1) := one_le_padicValNat_of_dvd hF1.ne' hfF'
  have hrange : (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F).range =
      CFSG.Open.StatedSL n F := (CFSG.Open.StatedAPI.statedSL_eq_range_toGL n F).symm
  have hcF : ¬ f ∣ Fintype.card F := fun h => by
    have h1 : f ∣ Fintype.card F - (Fintype.card F - 1) := Nat.dvd_sub h hfF'
    rw [Nat.sub_sub_self Fintype.card_pos] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have h1 : ((Fintype.card F - 1 : ℕ) : ZMod f) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hfF'
  have hF1' : ((Fintype.card F : ℕ) : ZMod f) = 1 := by
    have : Fintype.card F = (Fintype.card F - 1) + 1 := (Nat.sub_add_cancel Fintype.card_pos).symm
    rw [this, Nat.cast_add, h1, Nat.cast_one, zero_add]
  have hΓ : (Nat.card (⊤ : Subgroup (GL (Fin n) F))).factorization f =
      padicValNat f (Fintype.card F - 1) * n + padicValNat f n.factorial := by
    rw [Subgroup.card_top, factorization_card_GL (hp.odd_of_ne_two hf2) F hcF n, hF1',
      orderOf_one, pow_one, Nat.div_one]
  refine exists_lift_of_cover hf2 hfn hn hCa ha SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective ?_ ?_ ?_ ?_ ψ hψ (fun s => (hker s).trans
      (mem_scalars_iff_toGL s)) hz S hzS hcen
  · intro x hx
    rw [hrange] at hx
    exact (det_eq_one_iff x).2 (CFSG.Open.StatedAPI.det_of_mem_statedSL hx)
  · intro t ht
    rw [hrange]
    apply diagHom_mem_statedSL
    have := congrArg Subtype.val ht
    simpa using this
  · intro H hH hHp
    obtain ⟨g, hg⟩ := exists_conj_monomial_GL hf2 hfF' (by omega : 1 ≤ n) H hHp
    refine ⟨g, fun x hx => ?_, hg⟩
    rw [hrange]
    exact conj_mem_statedSL g x (hrange ▸ hH hx)
  · obtain ⟨H, -, hHdet, hHp, hHc⟩ := exists_pGroup_ker_det hCa ⊤ hΓ
    refine ⟨H, fun x hx => ?_, hHp, ?_⟩
    · rw [hrange]
      exact CFSG.Open.StatedAPI.mem_statedSL_iff.2 ((det_eq_one_iff x).1 (hHdet x hx))
    · refine le_trans (Nat.pow_le_pow_right hp.pos ?_) hHc
      have h2 : padicValNat f (Fintype.card F - 1) * n =
          padicValNat f (Fintype.card F - 1) * (n - 1) + padicValNat f (Fintype.card F - 1) := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU
