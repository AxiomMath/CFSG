module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLinUniMat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonSylow
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreUniMat

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore CFSG.SectionRank.OddCover Matrix
open CFSG.Open CFSG.Quasithin CFSG.GroupTheory.WeirSylow
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

variable {F : Type} [Field F]

theorem exists_lift_unitary {K' : Type} [Group K'] [Finite F] {q f n : ℕ} [Fact f.Prime]
    (hf2 : f ≠ 2) (hfn : f ∣ n) (hn : 4 ≤ n) (hF : Nat.card F = q ^ 2) (hfq : f ∣ q + 1)
    (ψ : StatedSU n q F →* K') (hψ : Function.Surjective ψ)
    (hker : ∀ s : StatedSU n q F, ψ s = 1 ↔ (s : GL (Fin n) F) ∈ StatedScalars (Fin n) F)
    {z : K'} (hz : orderOf z = f) (S : Sylow f K') (hzS : z ∈ (S : Subgroup K'))
    (hcen : ∀ s ∈ (S : Subgroup K'), z * s = s * z) :
    ∃ A : StatedSU n q F, A ^ f = 1 ∧ ψ A = z := by
  classical
  haveI := Fintype.ofFinite F
  have hp : f.Prime := Fact.out
  have hFq : Fintype.card F = q ^ 2 := by rwa [← Nat.card_eq_fintype_card]
  have hq2 : 2 ≤ q := two_le_of_card_eq_sq hFq
  obtain ⟨f₀, hqf, hdata⟩ := exists_unitaryFieldData F hFq
  have hCa : Nat.card (unitsPPart F f) = f ^ padicValNat f (q + 1) :=
    card_unitsPPart_of_dvd_add_one hf2 hFq hfq
  have ha : 1 ≤ padicValNat f (q + 1) := one_le_padicValNat_of_dvd (by omega) hfq
  have hrange : (StatedSU n q F).subtype.range = StatedSU n q F := Subgroup.range_subtype _
  have hcq : ¬ f ∣ q := fun h => by
    have h1 : f ∣ q + 1 - q := Nat.dvd_sub hfq h
    rw [Nat.add_sub_cancel_left] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hq1 : (q : ZMod f) + 1 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).2 hfq
  have hneg : -(q : ZMod f) = 1 := neg_eq_of_add_eq_zero_right hq1
  have hval : padicValInt f ((-(q : ℤ)) ^ 1 - 1) = padicValNat f (q + 1) := by
    rw [pow_one, show -(q : ℤ) - 1 = -((q + 1 : ℕ) : ℤ) by push_cast; ring, padicValInt,
      Int.natAbs_neg, Int.natAbs_natCast]
  have hΓ : (Nat.card (StatedGU n q F)).factorization f =
      padicValNat f (q + 1) * n + padicValNat f n.factorial := by
    rw [factorization_card_statedGU (hp.odd_of_ne_two hf2) F hFq hcq (by omega : 1 ≤ n), hneg,
      orderOf_one, hval, Nat.div_one]
  refine exists_lift_of_cover hf2 hfn hn hCa ha (StatedSU n q F).subtype
    Subtype.val_injective ?_ ?_ ?_ ?_ ψ hψ (fun s => (hker s).trans ?_) hz S hzS hcen
  · intro x hx
    rw [hrange] at hx
    exact (det_eq_one_iff x).2 (CFSG.Open.StatedAPI.det_of_mem_statedSL
      (CFSG.Open.StatedAPI.statedSU_le_statedSL n q F hx))
  · intro t ht
    rw [hrange]
    apply diagHom_mem_statedSU (by omega)
    · have := congrArg Subtype.val ht
      simpa using this
    · intro i
      exact pow_add_one_eq_one_of_mem_unitsPPart hf2 hFq hfq (t i).2
  · intro H hH hHp
    rw [hrange] at hH
    have hHU : H ≤ StatedGU n q F := fun x hx => statedSU_le_statedGU (hH hx)
    obtain ⟨g, hgU, hg⟩ := exists_conj_monomial_GU hf2 hFq hfq (by omega : 1 ≤ n) H hHU hHp
    refine ⟨g, fun x hx => ?_, hg⟩
    rw [hrange]
    have hxGU : x ∈ StatedGU n q F := statedSU_le_statedGU (hH hx)
    have hSL : g * x * g⁻¹ ∈ StatedSL n F :=
      conj_mem_statedSL g x (CFSG.Open.StatedAPI.statedSU_le_statedSL n q F (hH hx))
    exact mem_statedSU_of_mem_statedGU hdata hqf
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgU hxGU) (Subgroup.inv_mem _ hgU))
      (CFSG.Open.StatedAPI.det_of_mem_statedSL hSL)
  · obtain ⟨H, hHle, hHdet, hHp, hHc⟩ := exists_pGroup_ker_det hCa (StatedGU n q F) hΓ
    refine ⟨H, fun x hx => ?_, hHp, ?_⟩
    · rw [hrange]
      exact mem_statedSU_of_mem_statedGU hdata hqf (hHle hx) ((det_eq_one_iff x).1 (hHdet x hx))
    · refine le_trans (Nat.pow_le_pow_right hp.pos ?_) hHc
      have h2 : padicValNat f (q + 1) * n =
          padicValNat f (q + 1) * (n - 1) + padicValNat f (q + 1) := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
  · rw [StatedScalars, MonoidHom.mem_range]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU
