module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YCDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQD4Core
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQD4Fld
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FAut
import CFSG.GroupTheory.PLayer.CenterQuotientAction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}

private noncomputable def selfEquiv (cfg : QUCfg 3 S B T x b) (hZ : Subgroup.center ↥S = ⊥) :
    PSimple 3 S ≃* ↥S :=
  (qu_pSimpleEquiv cfg.core).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)

omit [Finite Ω] in
private theorem conjAut_pow_three {y : Ω} (hy : y ∈ Subgroup.normalizer (S : Set Ω))
    (h3 : y ^ 3 = 1) : D4T.conjAut S y hy ^ 3 = 1 := by
  change D4T.conjHom S ⟨y, hy⟩ ^ 3 = 1
  rw [← map_pow, show (⟨y, hy⟩ : ↥(Subgroup.normalizer (S : Set Ω))) ^ 3 = 1 from
    Subtype.ext h3, map_one]

theorem QUCfg.notCentralOut_of_outer (cfg : QUCfg 3 S B T x b)
    (hS8 : StatedClassicalModel (PSimple 3 S) .POmegaPlus 4 2 3)
    (hbS : b ∈ Subgroup.normalizer (S : Set Ω))
    (hbc : ¬ D4Y.NotCentralOut (D4T.conjAut S b hbS))
    (hbo : ∀ a : ↥S, MulAut.conj a ≠ D4T.conjAut S b hbS) {e : Ω} (he : e ∈ B)
    (heS : e ∈ Subgroup.normalizer (S : Set Ω))
    (heJ : e ∈ Subgroup.normalizer (Ipart 3 S b : Set Ω))
    (hout : chevAut 3 (Ipart 3 S b) ⟨e, heJ⟩ ∉ D4T.innerAut (PSimple 3 (Ipart 3 S b))) :
    D4Y.NotCentralOut (D4T.conjAut S e heS) := by
  by_contra hNC
  have hZ := cfg.center_eq_bot_of_d4eight hS8
  have hSm : StatedClassicalModel ↥S .POmegaPlus 4 2 3 := by
    obtain ⟨h1, K, _, _, hK, ⟨θ⟩⟩ := hS8
    exact ⟨h1, K, inferInstance, inferInstance, hK, ⟨(selfEquiv cfg hZ).symm.trans θ⟩⟩
  have hcomm : D4T.conjAut S b hbS * D4T.conjAut S e heS =
      D4T.conjAut S e heS * D4T.conjAut S b hbS := by
    change D4T.conjHom S ⟨b, hbS⟩ * D4T.conjHom S ⟨e, heS⟩ =
      D4T.conjHom S ⟨e, heS⟩ * D4T.conjHom S ⟨b, hbS⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (isElemAbelian_commute cfg.elem cfg.hb he))
  obtain ⟨c, m, hc, hce⟩ := d4eight_eq_conj_mul_pow hSm
    (conjAut_pow_three hbS (cfg.elem.2 b cfg.hb)) (conjAut_pow_three heS (cfg.elem.2 e he))
    hcomm hbc hNC hbo
  have hBN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 cfg.normal).symm ▸ Subgroup.mem_top g
  have hmap := CFSG.glaPLayer_fixSubgroup_map_eq Nat.prime_three hBN ⟨b, cfg.hb⟩
  rw [show CFSG.normalizerConjAutOfMem S B hBN ⟨b, cfg.hb⟩ = D4T.conjAut S b hbS from
    MulEquiv.ext fun _ => rfl] at hmap
  have hcJ : (c : Ω) ∈ Ipart 3 S b := by
    change (c : Ω) ∈ GLAPLayer 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω))
    rw [← hmap]
    exact ⟨c, hc, rfl⟩
  have hact : ∀ k ∈ Ipart 3 S b, e * k * e⁻¹ = (c : Ω) * k * (c : Ω)⁻¹ := by
    intro k hk
    obtain ⟨hkS, hkb⟩ := Subgroup.mem_inf.1
      ((sSup_le fun _ hL => hL.1 : Ipart 3 S b ≤ S ⊓ Subgroup.centralizer ({b} : Set Ω)) hk)
    have h0 : D4T.conjAut S b hbS ⟨k, hkS⟩ = ⟨k, hkS⟩ := Subtype.ext (by
      show b * k * b⁻¹ = k
      rw [(Subgroup.mem_centralizer_singleton_iff.1 hkb).symm, mul_inv_cancel_right])
    have hpow : ∀ n : ℕ, (D4T.conjAut S b hbS ^ n) ⟨k, hkS⟩ = ⟨k, hkS⟩ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, h0, ih]
    have h1 : ((D4T.conjAut S e heS ⟨k, hkS⟩ : ↥S) : Ω) =
        (((MulAut.conj c * D4T.conjAut S b hbS ^ m) ⟨k, hkS⟩ : ↥S) : Ω) := by
      rw [← hce]
    rw [MulAut.mul_apply, hpow, MulAut.conj_apply] at h1
    exact h1
  apply hout
  refine MonoidHom.mem_range.2 ⟨chevQuotHom 3 (Ipart 3 S b) ⟨c, hcJ⟩, ?_⟩
  ext y
  obtain ⟨k, rfl⟩ := chevQuotHom_surjective 3 (Ipart 3 S b) y
  rw [chevAut_chevQuotHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hact k k.2).symm

end CFSG.LocalAnalysis.GLTheoremA.S265

end
