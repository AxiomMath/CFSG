module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Real
public import Certificates.Certificate22244
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOddFour
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuActDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem pow32_eq_one_of_commute_sq
    {ρ : Equiv.Perm (Fin 42)} (hρR : ρ ∈ R) (hρr : ρ * r₄ = r₄ * ρ)
    (hsq : ∀ s ∈ S, s * r₄ = r₄ * s → ρ * (s * s) = s * s * ρ) : ρ ^ 32 = 1 := by
  have hE : Enumerates (Subgroup.centralizer {r₄} ⊓ R) KuAct.centR₄.toList := by
    have := enumerates_R.filter (fun t => comp 42 t r₄T == comp 42 r₄T t)
      (K := Subgroup.centralizer {r₄}) fun t g ht => by
        rw [(ht.comp tabRep_r₄).beq_iff (tabRep_r₄.comp ht), Subgroup.mem_centralizer_singleton_iff]
    simpa only [KuAct.centR₄, centTabs, Array.toList_filter] using this
  obtain ⟨t, ht, hrep⟩ := hE.complete ρ
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hρr, hρR⟩
  have hall := Array.all_eq_true_iff_forall_mem.mp Certificates.certificate22244 t
    (Array.mem_toList_iff.mp ht)
  have hsqall : (KuAct.sqC₄.all fun q => comp 42 t q == comp 42 q t) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro q hq
    obtain ⟨s, hs, rfl⟩ := Array.mem_map.mp hq
    obtain ⟨σ, hσ, hσrep⟩ := enumerates_C₄.sound s (Array.mem_toList_iff.mpr hs)
    have hσr : σ * r₄ = r₄ * σ := Subgroup.mem_centralizer_singleton_iff.mp hσ.1
    exact ((hrep.comp (hσrep.comp hσrep)).beq_iff ((hσrep.comp hσrep).comp hrep)).mpr
      (hsq σ hσ.2 hσr)
  rw [hsqall, Bool.not_true, Bool.false_or] at hall
  have h2 := hrep.comp hrep
  have h4 := h2.comp h2
  have h8 := h4.comp h4
  have h16 := h8.comp h8
  have h32 : TabRep (KuAct.pow32Tab t) _ := h16.comp h16
  have hpow : TabRep (KuAct.pow32Tab t) (ρ ^ 32) := by
    convert h32 using 1
    rw [show (32 : ℕ) = 2 * 2 * 2 * 2 * 2 by norm_num, pow_mul, pow_mul, pow_mul, pow_mul]
    simp only [sq]
  exact (hpow.beq_iff TabRep.idTab).mp hall

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem betaHat_jq_eq_of_commutator_le {x : G} {J Y : Subgroup G}
    (hYN : Y ≤ normalizer (J : Set G)) (hle : ⁅J ⊓ centralizer ({x} : Set G), Y⁆ ≤ oddIn J)
    {y : G} (hy : y ∈ Y) {j : J} (hj : (j : G) ∈ centralizer ({x} : Set G)) :
    betaHat J (hYN hy) (jq J j) = jq J j := by
  rw [betaHat_jq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have h1 : ⁅(j : G)⁻¹, y⁻¹⁆⁻¹ ∈ oddIn J := inv_mem (hle (commutator_mem_commutator
    (mem_inf.mpr ⟨inv_mem j.2, inv_mem hj⟩) (inv_mem hy)))
  obtain ⟨o, ho, hoe⟩ := h1
  have hj' : (conjJ J (hYN hy) j)⁻¹ * j = o := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
    rw [Subgroup.coe_subtype] at hoe
    rw [hoe, commutatorElement_def]
    group
  rw [hj']
  exact ho

omit [Finite G] in
theorem betaHat_comm {J : Subgroup G} {x y : G} (hxN : x ∈ normalizer (J : Set G))
    (hyN : y ∈ normalizer (J : Set G)) (hxy : x * y = y * x) (e : Jhat J) :
    betaHat J hxN (betaHat J hyN e) = betaHat J hyN (betaHat J hxN e) := by
  obtain ⟨j, rfl⟩ := jq_surjective J e
  rw [betaHat_jq, betaHat_jq, betaHat_jq, betaHat_jq]
  congr 1
  apply Subtype.ext
  simp only [coe_conjJ]
  have e1 : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hxy]
  calc x⁻¹ * (y⁻¹ * (j : G) * y) * x = (x⁻¹ * y⁻¹) * j * (y * x) := by group
    _ = (y⁻¹ * x⁻¹) * j * (x * y) := by rw [e1, hxy]
    _ = y⁻¹ * (x⁻¹ * (j : G) * x) * y := by group

theorem not_commutator_le_of_l34
    {a x : G}
    {J Y : Subgroup G} (htri : GSUnbalancingTriple a x J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hYodd : Odd (Nat.card Y))
    (hYN : Y ≤ normalizer (J : Set G)) (hYx : Y ≤ centralizer ({x} : Set G))
    (hJY : ¬ ⁅J, Y⁆ ≤ oddIn J) : ¬ ⁅J ⊓ centralizer ({x} : Set G), Y⁆ ≤ oddIn J := by
  intro hle
  obtain ⟨hx2, hJ, -, -⟩ := triple_facts htri
  have hU := l34UnbalancingUnitaryStep G a x J htri hL
  have hxN : x ∈ normalizer (J : Set G) := hU.1
  obtain ⟨q, hqS, hqsurj, hqker, -, hβ⟩ := exists_unitary_realization hJ hL hU
  obtain ⟨ψ, hψR, hψ⟩ := GrS4.exists_realization_hom hYN hqS hqsurj hqker
  have hψ1 : ∀ y (hy : y ∈ Y), ψ ⟨y, hy⟩ = 1 := by
    intro y hy
    have hyN := hYN hy
    set ρ := ψ ⟨y, hy⟩ with hρ
    have hρe : ∀ e, q (betaHat J hyN e) = ρ⁻¹ * q e * ρ := fun e => hψ ⟨y, hy⟩ e
    have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp (hYx hy)).symm
    have hρr : ρ * r₄ = r₄ * ρ := by
      have h1 : r₄ * ρ⁻¹ = ρ⁻¹ * r₄ := GrS4.realization_unique hqsurj
        (R.mul_mem r₄_mem_R (R.inv_mem (hψR _))) (R.mul_mem (R.inv_mem (hψR _)) r₄_mem_R)
        (β := fun e => betaHat J hxN (betaHat J hyN e)) (fun e => by
          rw [hβ, hρe]
          group) (fun e => by
          show q (betaHat J hxN (betaHat J hyN e)) = _
          rw [betaHat_comm hxN hyN hxy, hρe, hβ]
          group)
      calc ρ * r₄ = ρ * (r₄ * ρ⁻¹) * ρ := by group
        _ = ρ * (ρ⁻¹ * r₄) * ρ := by rw [h1]
        _ = r₄ * ρ := by group
    have hsq : ∀ s ∈ S, s * r₄ = r₄ * s → ρ * (s * s) = s * s * ρ := by
      intro s hs hsr
      obtain ⟨e, rfl⟩ := hqsurj s hs
      have hz : e⁻¹ * betaHat J hxN e ∈ center (Jhat J) := by
        rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hβ, ← hsr]
        group
      set z := e⁻¹ * betaHat J hxN e with hzdef
      have hez : betaHat J hxN e = e * z := by rw [hzdef]; group
      have hzc : ∀ g, g * z = z * g := fun g => (mem_center_iff.mp hz g)
      have hbz : betaHat J hxN z = z⁻¹ := by
        have h1 := betaHat_betaHat J hxN hx2 e
        rw [hez, map_mul, hez] at h1
        calc betaHat J hxN z = (e * z)⁻¹ * (e * z * betaHat J hxN z) := by group
          _ = z⁻¹ := by rw [h1]; group
      have hfix : betaHat J hxN (e * e * z) = e * e * z := by
        rw [map_mul, map_mul, hez, hbz]
        calc e * z * (e * z) * z⁻¹ = e * (z * e) * z * z⁻¹ := by group
          _ = e * e * z := by rw [← hzc e]; group
      obtain ⟨j, hjk, hjx⟩ := exists_fixed_lift hxN hx2 hfix
      have hjc : (j : G) ∈ centralizer ({x} : Set G) := mem_centralizer_of_conj_eq (by
        have := congrArg Subtype.val hjx
        rwa [coe_conjJ] at this)
      have hyfix := betaHat_jq_eq_of_commutator_le hYN hle hy hjc
      rw [hjk] at hyfix
      have h1 := hρe (e * e * z)
      rw [hyfix] at h1
      have hqz : q z = 1 := by rw [← MonoidHom.mem_ker, hqker]; exact hz
      rw [map_mul, map_mul, hqz, mul_one] at h1
      calc ρ * (q e * q e) = ρ * (ρ⁻¹ * (q e * q e) * ρ) := by rw [← h1]
        _ = q e * q e * ρ := by group
    have h32 := pow32_eq_one_of_commute_sq (hψR _) hρr hsq
    have hpow : ρ ^ orderOf y = 1 := by
      have h1 : (⟨y, hy⟩ : Y) ^ orderOf y = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
      rw [hρ, ← map_pow, h1, map_one]
    have hyodd : Odd (orderOf y) := hYodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hy)
    have hcop : Nat.Coprime 2 (orderOf ρ) :=
      (Nat.coprime_two_left.mpr hyodd).coprime_dvd_right (orderOf_dvd_of_pow_eq_one hpow)
    exact eq_one_of_coprime_of_pow (k := 5) hcop (by
      rw [show (2 : ℕ) ^ 5 = 32 by norm_num]
      exact h32)
  apply hJY
  rw [← closure_conj_commutator_eq_commutator J Y, closure_le]
  rintro _ ⟨j', hj', y, hy, rfl⟩
  have hyK : y ∈ coreActionKernel J :=
    GrS4.mem_coreActionKernel_of_realization_eq_one hJ (hYN hy) hqker fun e => by
      rw [hψ ⟨y, hy⟩ e, hψ1 y hy, inv_one, one_mul, mul_one]
  exact (mem_coreActionKernel.mp hyK).2 j' hj'

end CFSG.ComponentClassification.GrSLit.L34Facts

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34KuActionL34_holds :
    L34KuActionL34 :=
  fun _ _ _ _ _ _ _ htri hL hYodd hYN hYx hJY =>
    L34Facts.not_commutator_le_of_l34 htri hL hYodd hYN hYx hJY

end CFSG.ComponentClassification.GrSLit.GrS5S
