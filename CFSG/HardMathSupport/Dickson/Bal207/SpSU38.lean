module

public import CFSG.HardMathSupport.Dickson.Bal207.SU38Frame
public import CFSG.HardMathSupport.Dickson.Bal207.SpFC
import CFSG.HardMathSupport.Dickson.Bal207.SU38Block
import CFSG.HardMathSupport.Dickson.Bal207.UniOrder
import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.Bal207.Uni CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem five_dvd_card_statedProj {s k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ k) (hk : k = 1 ∨ k = 3) (hs : 2 ≤ s) :
    5 ∣ Nat.card (StatedProj (StatedSp s F)) := by
  haveI := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := k) (by rw [Fintype.card_eq_nat_card, hF])
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo]
  refine Dvd.dvd.mul_left ?_ _
  refine Nat.dvd_trans ?_ (Finset.dvd_prod_of_mem (fun j => Nat.card F ^ (2 * j) - 1)
    (Finset.mem_Icc.mpr ⟨by norm_num, hs⟩ : 2 ∈ Finset.Icc 1 s))
  show 5 ∣ Nat.card F ^ (2 * 2) - 1
  rw [hF]
  rcases hk with rfl | rfl <;> norm_num

theorem su38FrameSp_of_griess (hGA : GriessAllModelsStatement)
    (G : ∀ (S : Type) [Group S], MulAut S → Prop) : SU38FrameSp G := by
  intro Y _ _ _ K B A ctx hK _ a haA ha1 J hJ hJU hBJ
  obtain ⟨F, _, _, f, r, hF, hf, hr, hne, ⟨e⟩⟩ := exists_psp_of_famSp hK
  have hKq : CFSG.Open.IsQuasisimple ↥K := ctx.comp.2.2
  have hZ := famSp_coprime_center hGA hKq hK
  have haB : a ∈ B := ctx.le haA
  have hBK : B ≤ Subgroup.normalizer (K : Set Y) := ctx.norm
  have hβ3 : uniAut e ⟨a, hBK haB⟩ ^ 3 = 1 := by
    have h3 : (⟨a, hBK haB⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ 3 = 1 :=
      Subtype.ext (ctx.scp.2.1.2 a haB)
    rw [← map_pow, h3, map_one]
  have hβ1 : uniAut e ⟨a, hBK haB⟩ ≠ 1 := fun h1 =>
    not_mem_centralizer_of_inf_eq_bot ctx.disj haA ha1
      (mem_centralizer_of_uniAut_eq_one e hKq.1 (hBK haB) h1)
  have hlay := (compShape_psp hF hf hr hne _ hβ3 hβ1).layer
  obtain ⟨hcomp, hJc, -⟩ := uni_component e Nat.prime_three hKq hZ (hBK haB) hlay hJ
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hcard := uni_card_su38 hJU
  rcases spComp_cases ctx.scp hBK hF hf hr hne e haB hβ1 hJK hcomp.2.2 hJc with h1 | h2 | h3
  · exfalso
    obtain ⟨s, k, F', _, _, hF', hk, hs, -, ⟨eJ⟩⟩ := h1
    have h5 := five_dvd_card_statedProj hF' hk hs
    rw [← Nat.card_congr eJ.toEquiv, hcard] at h5
    norm_num at h5
  · exfalso
    rw [hcard] at h2
    norm_num at h2
  · obtain ⟨E, _, f', h, n, hf', hn, hne', ι, hι, hJι, x, hx, P, hP⟩ := h3
    have hZP := CFSG.RankThree.PartOne.KCUnitaryRegular.center_primeFormP_eq_bot h (C := 1)
      CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one hn hne'
    have hker := ker_eq_center_of_surjective _ (blockHom_surjective e h hJK hι hJι P)
      (ker_blockHom_le_center e h hJK hι hJι hcomp.2.2.1 P) hZP
    have hcP : Nat.card (primeFormP h (oneGram E n)) = 5515776 := by
      rw [← Nat.card_congr (centerQuotientEquivOfHom _ (blockHom_surjective e h hJK hι hJι P)
        hker).toEquiv, hcard]
    obtain ⟨hf3, hn3⟩ := uni_nine_cases hf' (uni_eq_nine_of_card h (by omega) hcP)
    subst hn3 hf3
    exact Or.inr (su38Toral_of_block ctx.scp hBK hZ e hcomp.2.2 hJK hBJ h rfl hf'
      (by norm_num) hι hJι x hx P hP)

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
