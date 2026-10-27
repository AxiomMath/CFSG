module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Walter.JRAssembly

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec10L104_mem_twoCoreIn_of_mem_pCore {X : Subgroup G} {x : ↥X}
    (hx : x ∈ CFSG.pCore 2 ↥X) : (x : G) ∈ twoCoreIn X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

private theorem sec10L104_mem_pCore_of_map {X : Subgroup G} (e : ↥X ≃* SL23) {x : ↥X}
    (hx : e x ∈ CFSG.pCore 2 SL23) : x ∈ CFSG.pCore 2 ↥X := by
  rw [← CFSG.pCore_map_iso 2 e] at hx
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hx
  have hyx : y = x := e.injective hye
  rwa [hyx] at hy

private theorem sec10L104_symm_mem_twoCoreIn {X : Subgroup G} (e : ↥X ≃* SL23) {y : SL23}
    (hy : y ^ 4 = 1) : ((e.symm y : ↥X) : G) ∈ twoCoreIn X := by
  refine sec10L104_mem_twoCoreIn_of_mem_pCore (sec10L104_mem_pCore_of_map e ?_)
  rw [e.apply_symm_apply, sl23_pCore_eq_Q8, mem_sl23Q8]
  exact hy

private theorem sec10L104_map_invol {X : Subgroup G} (e : ↥X ≃* SL23) {w : G} (hw : w ∈ X)
    (hw2 : orderOf w = 2) : e ⟨w, hw⟩ = -1 := by
  have hsq : (⟨w, hw⟩ : ↥X) * ⟨w, hw⟩ = 1 := by
    apply Subtype.ext
    change (w : G) * w = 1
    have h := pow_orderOf_eq_one w
    rw [hw2] at h
    simpa [pow_two] using h
  have hsq' : e ⟨w, hw⟩ * e ⟨w, hw⟩ = 1 := by
    rw [← map_mul, hsq, map_one]
  rcases sl23_unique_involution _ hsq' with h | h
  · exfalso
    have hw1 : (⟨w, hw⟩ : ↥X) = 1 := by
      apply e.injective
      rw [h, map_one]
    have hwG : w = 1 := by simpa using congrArg Subtype.val hw1
    have : orderOf w = 1 := by rw [hwG]; exact orderOf_one
    omega
  · exact h

theorem sec10L104_cent_Qi [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ a ∈ K1, (∀ b ∈ twoCoreIn K1, a * b = b * a) → a ∈ zpowers z := by
  obtain ⟨e⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  intro a ha hacentral
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  have hez : e ⟨z, hzK1⟩ = -1 := sec10L104_map_invol e hzK1 hz2
  have hcomm : ∀ y : SL23, y ^ 4 = 1 → e ⟨a, ha⟩ * y = y * e ⟨a, ha⟩ := by
    intro y hy
    have hm := sec10L104_symm_mem_twoCoreIn e hy
    have hc := hacentral _ hm
    have hc' : (⟨a, ha⟩ : ↥K1) * e.symm y = e.symm y * ⟨a, ha⟩ := Subtype.ext hc
    have h2 := congrArg e hc'
    rw [map_mul, map_mul, e.apply_symm_apply] at h2
    exact h2
  have hcases : e ⟨a, ha⟩ = 1 ∨ e ⟨a, ha⟩ = -1 :=
    (by decide : ∀ x : SL23, (∀ y : SL23, y ^ 4 = 1 → x * y = y * x) → x = 1 ∨ x = -1) _ hcomm
  rcases hcases with h | h
  · have h1 : (⟨a, ha⟩ : ↥K1) = 1 := e.injective (by rw [h, map_one])
    have ha1 : a = 1 := congrArg Subtype.val h1
    rw [ha1]
    exact Subgroup.one_mem _
  · have h1 : (⟨a, ha⟩ : ↥K1) = ⟨z, hzK1⟩ := e.injective (by rw [h, hez])
    have haz : a = z := congrArg Subtype.val h1
    rw [haz]
    exact Subgroup.mem_zpowers z

theorem sec10L104_cent_Q [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ k ∈ K1 ⊔ K2, (∀ q ∈ secQ K1 K2, k * q = q * k) → k ∈ zpowers z := by
  intro k hk hkc
  have hsup := sec10KS_twoCore_sup hP5 hC5 hpsp hctx
  have hc12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  obtain ⟨a, ha, b, hb, hkab⟩ := exists_mul_of_mem_sup_of_commute hc12 hk
  have haZ : a ∈ zpowers z := by
    refine sec10L104_cent_Qi hP5 hC5 hpsp hctx a ha (fun q hq => ?_)
    have hqQ : q ∈ secQ K1 K2 := by rw [hsup]; exact Subgroup.mem_sup_left hq
    have h1 := hkc q hqQ
    have hbq : b * q = q * b := (hc12 q (twoCoreIn_le_self K1 hq) b hb).symm
    rw [hkab] at h1
    calc a * q = a * q * b * b⁻¹ := by group
      _ = a * (q * b) * b⁻¹ := by rw [mul_assoc a q b]
      _ = a * (b * q) * b⁻¹ := by rw [hbq]
      _ = (a * b) * q * b⁻¹ := by group
      _ = q * (a * b) * b⁻¹ := by rw [h1]
      _ = q * a := by group
  have hbZ : b ∈ zpowers z := by
    refine sec10L104_cent_Qi hP5 hC5 hpsp hctx.swap b hb (fun q hq => ?_)
    have hqQ : q ∈ secQ K1 K2 := by rw [hsup]; exact Subgroup.mem_sup_right hq
    have h1 := hkc q hqQ
    have haq : a * q = q * a := hc12 a ha q (twoCoreIn_le_self K2 hq)
    rw [hkab] at h1
    calc b * q = a⁻¹ * (a * b * q) := by group
      _ = a⁻¹ * (q * (a * b)) := by rw [h1]
      _ = a⁻¹ * (q * a) * b := by group
      _ = a⁻¹ * (a * q) * b := by rw [haq]
      _ = q * b := by group
  rw [hkab]
  exact Subgroup.mul_mem _ haZ hbZ

theorem sec10L104_conj_Q {K1 K2 : Subgroup G} :
    ∀ k ∈ K1 ⊔ K2, ∀ q ∈ secQ K1 K2, k * q * k⁻¹ ∈ secQ K1 K2 := by
  intro k hk q hq
  have h := (Subgroup.normal_subgroupOf_iff (twoCoreIn_le_self (K1 ⊔ K2))).mp
    (normal_subgroupOf_twoCoreIn (K1 ⊔ K2))
  exact h q k hq hk

theorem sec10L104_eq_one_of_odd_two {x : G} (hodd : Odd (orderOf x))
    (h2 : ∃ m : ℕ, x ^ (2 ^ m) = 1) : x = 1 := by
  obtain ⟨m, hm⟩ := h2
  have hdvd : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  have hcop : Nat.Coprime (orderOf x) (2 ^ m) :=
    (Nat.coprime_two_right.mpr hodd).pow_right m
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)

end CFSG.OddStandard.SmallF3.Omega
