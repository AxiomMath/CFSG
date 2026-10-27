module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCompTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

theorem mem_centralizerResidual_of_mk_mem_KBar {β y : X} (hyM : y ∈ centralizer ({β} : Set X))
    (hy2 : y ^ 2 = 1) (hyc : ∀ k ∈ centralizerResidual L β, k * y = y * k)
    (hyK : (QuotientGroup.mk ⟨y, hyM⟩ : MBar β) ∈ Standing.Setup42.KBar L β) :
    y ∈ centralizerResidual L β := by
  obtain ⟨⟨k, hkM⟩, hkK, hk⟩ := hyK
  have hkK' : k ∈ centralizerResidual L β := hkK
  have hmem : (⟨k, hkM⟩ : ↥(centralizer ({β} : Set X)))⁻¹ * ⟨y, hyM⟩ ∈ pPrimeCore 2 _ :=
    QuotientGroup.eq.mp hk
  obtain ⟨m, hm⟩ : Odd (orderOf (k⁻¹ * y)) := by
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    have h1 : orderOf (k⁻¹ * y) =
        orderOf ((⟨k, hkM⟩ : ↥(centralizer ({β} : Set X)))⁻¹ * ⟨y, hyM⟩) :=
      Subgroup.orderOf_coe ((⟨k, hkM⟩ : ↥(centralizer ({β} : Set X)))⁻¹ * ⟨y, hyM⟩)
    rw [h1]
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hdvd
  have hc : Commute k⁻¹ y := Commute.inv_left (hyc k hkK')
  have h1 : (k⁻¹ * y) ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
  have hy' : y ^ (2 * m + 1) = y := by rw [pow_succ, pow_mul, hy2, one_pow, one_mul]
  rw [hc.mul_pow, hy', inv_pow] at h1
  rw [← inv_mul_eq_one.mp h1]
  exact pow_mem hkK' _

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem orderOf_tBar (hσ : Setup42 h hS w z) (i j : ℕ) : orderOf (hσ.tBar i j) = 2 := by
  have ht2 : t ^ 2 = 1 := by
    rw [← h.config.orderOf_eq]
    exact pow_orderOf_eq_one t
  have hsq : hσ.tBar i j ^ 2 = 1 := by
    rw [tBar, ← QuotientGroup.mk_pow]
    rw [show (⟨t, hσ.t_mem_centralizer_beta i j⟩ :
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) ^ 2 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow, ht2, Subgroup.coe_one]), QuotientGroup.mk_one]
  refine orderOf_eq_prime hsq fun h1 => ?_
  rw [tBar, QuotientGroup.eq_one_iff] at h1
  have hdvd := Subgroup.orderOf_dvd_natCard _ h1
  rw [Subgroup.orderOf_mk, h.config.orderOf_eq] at hdvd
  exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)

theorem isTwoComponentIn_KBar (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    IsTwoComponentIn (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
      (centralizer ({hσ.tBar i j} : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set K := centralizerResidual L β with hK
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  have hF1 := hσ.layerIn_centralizer_tBar hFC hKC i j
  have hKM : K ≤ M := K_le_centralizer_beta i j
  refine ⟨?_, ?_, ?_⟩
  · rw [← hF1]
    exact map_subtype_le _
  · have h1 : (KBar L β).subgroupOf (centralizer ({hσ.tBar i j} : Set (MBar β))) =
        pLayer ↥(centralizer ({hσ.tBar i j} : Set (MBar β))) 2 := by
      rw [← hF1]
      exact comap_map_eq_self_of_injective (subtype_injective _) _
    rw [h1]
    have := CatalogueBPrimeJoin.pLayer_characteristic
      (G := ↥(centralizer ({hσ.tBar i j} : Set (MBar β)))) (p := 2)
    exact (inferInstance :
      (pLayer ↥(centralizer ({hσ.tBar i j} : Set (MBar β))) 2).Normal).isSubnormal
  · have hKperf : Group.IsPerfect ↥K := isPerfect_perfectResidual_map _
    let e := subgroupOfEquivOfLe hKM
    have hperf' : Group.IsPerfect ↥(K.subgroupOf M) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    refine ⟨Group.IsPerfect.ofSurjective (f := π.subgroupMap (K.subgroupOf M))
      (π.subgroupMap_surjective _), ?_⟩
    obtain ⟨e₂⟩ := GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv π
      GSThmB.OddQuot.not_two_dvd_card_ker (K.subgroupOf M)
    have hL := hσ.lieModel_bar_K hFC hKC i j
    have := isSimpleGroup_of_lieModel_psl2 hL
    have hq : IsQuasisimple (Bar K) :=
      (LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_of_lieModel_psl2 hL)).1
    let e' : ↥(K.subgroupOf M) ⧸ pPrimeCore 2 ↥(K.subgroupOf M) ≃* Bar K :=
      QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
    exact LocalCores.isQuasisimple_of_mulEquiv (e'.symm.trans e₂) hq

theorem le_KBar_of_isComponent (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ)
    {J : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} (hJ : IsComponent J)
    (hJt : J ≤ centralizer ({hσ.tBar i j} : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    J ≤ KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← hσ.layerIn_centralizer_tBar hFC hKC i j]
  exact le_layerIn_of_isComponent (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hJ hJt

theorem tBar_not_mem_KBar (hσ : Setup42 h hS w z) (i j : ℕ) :
    hσ.tBar i j ∉ KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  intro hK
  have ht2 : t ^ 2 = 1 := by
    rw [← h.config.orderOf_eq]
    exact pow_orderOf_eq_one t
  have htK := mem_centralizerResidual_of_mk_mem_KBar (hσ.t_mem_centralizer_beta i j) ht2
    (fun k hk => mem_centralizer_singleton_iff.mp
      (h.config.le_centralizer (centralizerResidual_le hk).1)) hK
  exact h.config.not_mem (centralizerResidual_le htK).1

theorem tBar_mul_betaBar_not_mem_KBar (hσ : Setup42 h hS w z) (i j : ℕ) :
    hσ.tBar i j * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∉
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  intro hK
  have htM := hσ.t_mem_centralizer_beta i j
  have hβM : β ∈ centralizer ({β} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have htb2 : (t * β) ^ 2 = 1 := by
    have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
    exact hσ.sq_eq_one_of_mem_X (mul_mem htX (beta_mem_X i j))
  have hc : ∀ k ∈ centralizerResidual L β, k * (t * β) = t * β * k := by
    intro k hk
    have h1 : Commute k t := mem_centralizer_singleton_iff.mp
      (h.config.le_centralizer (centralizerResidual_le hk).1)
    have h2 : Commute k β := mem_centralizer_singleton_iff.mp (centralizerResidual_le hk).2
    exact (h1.mul_right h2).eq
  have hK' : (QuotientGroup.mk ⟨t * β, mul_mem htM hβM⟩ : MBar β) ∈ KBar L β := hK
  have htβK := mem_centralizerResidual_of_mk_mem_KBar (mul_mem htM hβM) htb2 hc hK'
  have htβL : t * β ∈ L := (centralizerResidual_le htβK).1
  apply hσ.rho_beta_not_mem_inn i j
  have hρ : h.rho ⟨β, hσ.beta_mem_H i j⟩ = h.rho ⟨t * β, h.config.le_centralizer htβL⟩ := by
    rw [show (⟨t * β, h.config.le_centralizer htβL⟩ : ↥(centralizer ({t} : Set X))) =
      ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ * ⟨β, hσ.beta_mem_H i j⟩ from rfl, map_mul,
      h.rho_t, one_mul]
  rw [hρ]
  exact ⟨QuotientGroup.mk ⟨t * β, htβL⟩, (h.rho_of_mem ⟨t * β, htβL⟩).symm⟩

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
