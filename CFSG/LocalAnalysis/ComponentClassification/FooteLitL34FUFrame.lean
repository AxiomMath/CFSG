module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PRho
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsReal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Normal
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Walter.J1
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

variable {X : Type} [Group X] [Finite X]

theorem eq_two_zero_of_fixed : ∀ c d : ZMod 4, c + 3 * d = c → 3 * d = d → c + c = 0 →
    d + d = 0 → ¬ (c = 0 ∧ d = 0) → c = 2 ∧ d = 0 := by
  decide

theorem exists_field_frame16
    {β : X} {K P : Subgroup X}
    (hK : ⁅K, K⁆ = K) (hL34 : IsL34Type (K ⧸ Open.fusionZStar K))
    (hβN : β ∈ normalizer (K : Set X)) (hfield : HarrisLit.EndB.IsL34Field K β)
    (h16 : Nat.card (zStarIn K) = 16 * Nat.card (oddIn K)) (hP : IsSylowTwoIn P K)
    (hβP : β ∈ normalizer (P : Set X)) :
    ∃ (q : Jhat K →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat K), IsQSetting q l ∧
      (∀ e, q (betaHat K hβN e) = r₂ * q e * r₂⁻¹) ∧
      (∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ K, jq K ⟨p, hp⟩ = e) ∧
      (∀ w, betaHat K hβN (l (cv w)) = l (cv (substWord (aut 1) w))) ∧
      (∀ c d : ZMod 4, betaHat K hβN (zz l c d) = zz l (c + 3 * d) (3 * d)) ∧
      ∀ c d : ZMod 4, zz l c d = 1 → c = 0 ∧ d = 0 := by
  obtain ⟨-, hβ2, hβK, hcount⟩ := hfield
  obtain ⟨q, l, hQS, hβq, hT0⟩ := exists_field_standard hK hL34 hβN hβ2 hβK hcount hP hβP
  have hβl : ∀ w, betaHat K hβN (l (cv w)) = l (cv (substWord (aut 1) w)) :=
    beta_cv_of hQS.ker_le hQS.ql (fun e => by rw [L34P.repPerm_one]; exact hβq e)
      (abPerm_uA (by norm_num)) (abPerm_uB (by norm_num))
  obtain ⟨a1, a2, a3, a4⟩ := L34P.alphaZ_r₂
  have hzz : ∀ c d : ZMod 4, betaHat K hβN (zz l c d) = zz l (c + 3 * d) (3 * d) := by
    intro c d
    rw [beta_zz hQS (by norm_num) hβl, a1, a2, a3, a4]
    congr 1 <;> push_cast <;> ring
  have hmem : ∀ c d : ZMod 4, zz l c d ∈ center (Jhat K) := fun c d => by
    rw [← hQS.ker]
    exact zz_mem_ker hQS c d
  set f : ZMod 4 × ZMod 4 → center (Jhat K) := fun c => ⟨zz l c.1 c.2, hmem c.1 c.2⟩ with hf
  have hfsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rw [← hQS.ker] at hz
    obtain ⟨a, b, rfl⟩ := (mem_ker_iff hQS.ql hQS.lsurj hQS.three).1 hz
    exact ⟨((a : ZMod 4), (b : ZMod 4)), Subtype.ext (zz_ofNat a b)⟩
  have hcard : Nat.card (center (Jhat K)) = 16 := by
    have h := card_center_jhat K
    rw [h16] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hfinj : Function.Injective f :=
    (hfsurj.bijective_of_nat_card_le (by rw [hcard]; simp)).1
  refine ⟨q, l, hQS, hβq, hT0, hβl, hzz, fun c d hcd => ?_⟩
  have h1 : f (c, d) = f (0, 0) := Subtype.ext (by rw [hf]; simp only [zz_zero]; exact hcd)
  have h2 := hfinj h1
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

omit [Finite X] in
theorem eq_zz_two_of_fixed
    {K : Subgroup X} {β : X} {hβN : β ∈ normalizer (K : Set X)}
    {q : Jhat K →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat K} (hQS : IsQSetting q l)
    (hzz : ∀ c d : ZMod 4, betaHat K hβN (zz l c d) = zz l (c + 3 * d) (3 * d))
    (hinj : ∀ c d : ZMod 4, zz l c d = 1 → c = 0 ∧ d = 0) {e : Jhat K}
    (he : e ∈ center (Jhat K)) (heβ : betaHat K hβN e = e) (he2 : e * e = 1) (he1 : e ≠ 1) :
    e = zz l 2 0 := by
  have hk : e ∈ q.ker := by rw [hQS.ker]; exact he
  obtain ⟨a, b, rfl⟩ := (mem_ker_iff hQS.ql hQS.lsurj hQS.three).1 hk
  rw [← zz_ofNat] at heβ he2 he1 ⊢
  set c : ZMod 4 := (a : ZMod 4)
  set d : ZMod 4 := (b : ZMod 4)
  have hzzeq : ∀ c d c' d' : ZMod 4, zz l c d = zz l c' d' → c = c' ∧ d = d' := by
    intro c d c' d' h
    have h1 : zz l (c - c') (d - d') = 1 := by
      rw [sub_eq_add_neg, sub_eq_add_neg, ← zz_mul, ← zz_inv, h, mul_inv_cancel]
    obtain ⟨h2, h3⟩ := hinj _ _ h1
    exact ⟨sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩
  rw [hzz] at heβ
  obtain ⟨hc, hd⟩ := hzzeq _ _ _ _ heβ
  rw [zz_mul] at he2
  obtain ⟨hc2, hd2⟩ := hinj _ _ he2
  have hne : ¬ (c = 0 ∧ d = 0) := by
    rintro ⟨h1, h2⟩
    apply he1
    rw [h1, h2, zz_zero]
  obtain ⟨h1, h2⟩ := eq_two_zero_of_fixed c d hc hd hc2 hd2 hne
  rw [h1, h2]

theorem eq_of_mem_zStarIn
    {K : Subgroup X} {β : X} {hβN : β ∈ normalizer (K : Set X)}
    {q : Jhat K →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat K} (hQS : IsQSetting q l)
    (hzz : ∀ c d : ZMod 4, betaHat K hβN (zz l c d) = zz l (c + 3 * d) (3 * d))
    (hinj : ∀ c d : ZMod 4, zz l c d = 1 → c = 0 ∧ d = 0) {z w : X} (hz : z ∈ zStarIn K)
    (hw : w ∈ zStarIn K) (hz2 : orderOf z = 2) (hw2 : orderOf w = 2) (hzβ : z * β = β * z)
    (hwβ : w * β = β * w) (hzw : z * w = w * z) : z = w := by
  have hzK : z ∈ K := map_subtype_le _ hz
  have hwK : w ∈ K := map_subtype_le _ hw
  have key : ∀ {u : X} (huK : u ∈ K), u ∈ zStarIn K → orderOf u = 2 → u * β = β * u →
      jq K ⟨u, huK⟩ = zz l 2 0 := by
    intro u huK hu hu2 huβ
    have huu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
    refine eq_zz_two_of_fixed hQS hzz hinj ((mem_zStarIn_iff huK).mp hu) ?_ ?_ ?_
    · rw [betaHat_jq]
      congr 1
      apply Subtype.ext
      rw [coe_conjJ]
      calc β⁻¹ * u * β = β⁻¹ * (u * β) := by group
        _ = β⁻¹ * (β * u) := by rw [huβ]
        _ = u := by group
    · rw [← map_mul]
      have : (⟨u, huK⟩ : K) * ⟨u, huK⟩ = 1 := Subtype.ext huu
      rw [this, map_one]
    · intro h1
      have := L34P.eq_one_of_mem_oddIn_of_pow huK (k := 1) (by rw [pow_one, pow_two, huu]) h1
      rw [this, orderOf_one] at hu2
      exact absurd hu2 (by norm_num)
  have hzw' : (z * w⁻¹) ^ (2 ^ 1) = 1 := by
    have hzz' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
    have hww' : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww'
    rw [hwi, pow_one, pow_two]
    calc z * w * (z * w) = z * (w * z) * w := by group
      _ = z * (z * w) * w := by rw [hzw]
      _ = (z * z) * (w * w) := by group
      _ = 1 := by rw [hzz', hww', one_mul]
  have hmemK : z * w⁻¹ ∈ K := mul_mem hzK (inv_mem hwK)
  have h1 : jq K ⟨z * w⁻¹, hmemK⟩ = 1 := by
    have e1 : (⟨z * w⁻¹, hmemK⟩ : K) = ⟨z, hzK⟩ * (⟨w, hwK⟩ : K)⁻¹ := rfl
    rw [e1, map_mul, map_inv, key hzK hz hz2 hzβ, key hwK hw hw2 hwβ, mul_inv_cancel]
  have := L34P.eq_one_of_mem_oddIn_of_pow hmemK hzw' h1
  exact mul_inv_eq_one.mp this

end CFSG.ComponentClassification.TBLit.L34FU
