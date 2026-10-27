module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4DiagMem
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.Single

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem exists_commute_conj_of_odd {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hk : Odd (orderOf (a * b * (a * b)))) :
    ∃ y ∈ zpowers (a * b * (a * b)), a * (y⁻¹ * b * y) = y⁻¹ * b * y * a := by
  set ρ : X := a * b with hρ
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hb' : b = a * ρ := by rw [hρ, ← mul_assoc, ha, one_mul]
  have haρ : a * ρ * a⁻¹ = ρ⁻¹ := by
    rw [hai, hρ, mul_inv_rev, hai, hbi]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  have hconj : ∀ n : ℤ, a * ρ ^ n = ρ ^ (-n) * a := by
    intro n
    have h1 : a * ρ ^ n * a⁻¹ = ρ ^ (-n) := by
      rw [← conj_zpow, haρ, inv_zpow, zpow_neg]
    calc a * ρ ^ n = a * ρ ^ n * a⁻¹ * a := by group
      _ = ρ ^ (-n) * a := by rw [h1]
  obtain ⟨q, hq⟩ := hk
  have hσ : (ρ * ρ) ^ (2 * q + 1) = 1 := by rw [← hq]; exact pow_orderOf_eq_one _
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = (q : ℤ) * (q + 1) := ⟨_, rfl⟩
  have hρ1 : ρ ^ (2 * (4 * j + 1)) = 1 := by
    have e : (2 : ℤ) * (4 * j + 1) = ((2 * ((2 * q + 1) * (2 * q + 1)) : ℕ) : ℤ) := by
      rw [hj]
      push_cast
      ring
    rw [e, zpow_natCast, pow_mul, pow_two, pow_mul, hσ, one_pow]
  refine ⟨(ρ * ρ) ^ j, zpow_mem (mem_zpowers _) _, ?_⟩
  have hy : (ρ * ρ) ^ j = ρ ^ (2 * j) := by rw [← zpow_two, ← zpow_mul]
  rw [hy]
  have hby : (ρ ^ (2 * j))⁻¹ * b * ρ ^ (2 * j) = a * ρ ^ (4 * j + 1) := by
    have h1 : ρ ^ (-(2 * j)) * a = a * ρ ^ (2 * j) := (hconj (2 * j)).symm
    calc (ρ ^ (2 * j))⁻¹ * b * ρ ^ (2 * j) = ρ ^ (-(2 * j)) * a * ρ * ρ ^ (2 * j) := by
          rw [zpow_neg, hb']; group
      _ = a * ρ ^ (2 * j) * ρ * ρ ^ (2 * j) := by rw [h1]
      _ = a * ρ ^ (4 * j + 1) := by
          rw [mul_assoc a, mul_assoc a, ← zpow_add_one, ← zpow_add,
            show 2 * j + 1 + 2 * j = 4 * j + 1 by ring]
  rw [hby]
  have h1 : a * (a * ρ ^ (4 * j + 1)) = ρ ^ (4 * j + 1) := by rw [← mul_assoc, ha, one_mul]
  have h2 : a * ρ ^ (4 * j + 1) * a = ρ ^ (-(4 * j + 1)) := by
    rw [hconj, mul_assoc, ha, mul_one]
  rw [h1, h2]
  have h3 : ρ ^ (4 * j + 1) * ρ ^ (4 * j + 1) = 1 := by
    rw [← zpow_add, show 4 * j + 1 + (4 * j + 1) = 2 * (4 * j + 1) by ring]
    exact hρ1
  calc ρ ^ (4 * j + 1) = (ρ ^ (4 * j + 1))⁻¹ := eq_inv_of_mul_eq_one_left h3
    _ = ρ ^ (-(4 * j + 1)) := (zpow_neg ρ _).symm

omit [Finite X] in
theorem subgroupOf_map_subtype_eq_self {M : Subgroup X} (L : Subgroup M) :
    (L.map M.subtype).subgroupOf M = L := by
  rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]

theorem le_of_le_sup_oddIn {F K C : Subgroup X} (hFC : F ≤ C) (hKC : K ≤ C)
    (hCK : C ≤ normalizer (K : Set X)) (hF : ⁅F, F⁆ = F) (hle : F ≤ K ⊔ oddIn C) : F ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Odd (Nat.card (pPrimeCore 2 C)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hRK : pPrimeCore 2 C ≤ normalizer ((K.subgroupOf C : Subgroup C) : Set C) := by
    intro r _
    rw [mem_normalizer_iff]
    intro k
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hCK r.2) k
  have hTKR : F.subgroupOf C ≤ K.subgroupOf C ⊔ pPrimeCore 2 C := by
    intro y hy
    have h1 : y ∈ (K ⊔ oddIn C).subgroupOf C := hle hy
    unfold oddIn at h1
    rwa [subgroupOf_sup hKC (map_subtype_le _), subgroupOf_map_subtype_eq_self] at h1
  intro f hf
  exact le_of_perfect_le_sup_of_odd hR hRK (GrS4.isPerfect_subgroupOf hFC hF) hTKR
    (show (⟨f, hFC hf⟩ : C) ∈ F.subgroupOf C from hf)

theorem normalizer_le_of_mem (hMax : MaximalTwoComponentInput) (hFixL : SolomonFixedLayerStep)
    {a : X} {J W K : Subgroup X} (hs : SingleComponentSetting X a J W K)
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hbase : L34BaseSetting X) (haJ : a ∈ J) :
    normalizer (W : Set X) ≤ normalizer (K : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup X := hs.simple
  set M : Subgroup X := normalizer (W : Set X) with hM
  have hgs : GSMaximalSetting X a J := hs.toGSMaximalSetting
  have hJa : J ≤ centralizer ({a} : Set X) := hs.le_centralizer
  have hJc := hs.isPComponent
  have hCaN : centralizer ({a} : Set X) ≤ normalizer (J : Set X) :=
    GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs
  have hKM : K ≤ M := hs.le_normalizer
  have hKc := hs.isPComponent_K
  have hJK : J ≤ K := GrS4.le_of_singleComponentSetting hs
  have hKJ : K = J ⊔ oddIn K := GrS4.eq_sup_oddIn_of_singleComponentSetting hs
  have hOJ : oddIn J = J ⊓ oddIn M := GrS4.oddIn_eq_inf_of_singleComponentSetting hs
  have hOK : oddIn K ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc
  have haK : a ∈ K := hJK haJ
  have haa : a * a = 1 := by rw [← pow_two, ← hs.orderOf_eq, pow_orderOf_eq_one]
  intro m hm
  by_contra hmK
  set K' : Subgroup X := conjugate K m with hK'
  have hne : K ≠ K' := fun e => hmK (UnbalancedLayer.mem_normalizer_of_conjugate_eq e.symm)
  have hK'M : K' ≤ M := UnbalancedCorr.conjugate_le_of_mem hKM hm
  have hK'c : IsPComponent 2 (K'.subgroupOf M) :=
    UnbalancedCorr.isPComponent_conjugate_subgroupOf hm hKc
  have hKK' : ⁅K, K'⁆ ≤ oddIn K ⊓ oddIn K' := GrS5.commutator_le_inf_oddIn hKM hK'M hKc hK'c hne
  have hK'core : K' ≤ coreActionKernel K := le_coreActionKernel_of_ne hKM hK'M hKc hK'c hne
  set b₀ : X := m⁻¹ * a * m with hb₀
  have hb₀K' : b₀ ∈ K' := conj_mem_conjugate haK m
  have hb₀b₀ : b₀ * b₀ = 1 := by
    rw [hb₀, show m⁻¹ * a * m * (m⁻¹ * a * m) = m⁻¹ * (a * a) * m by group, haa]
    group
  have hσ : a * b₀ * (a * b₀) ∈ oddIn K' := by
    have h1 := (hKK' (commutator_mem_commutator haK hb₀K')).2
    have e : ⁅a, b₀⁆ = a * b₀ * (a * b₀) := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_right haa,
        inv_eq_of_mul_eq_one_right hb₀b₀]
      group
    rwa [e] at h1
  have hσodd : Odd (orderOf (a * b₀ * (a * b₀))) :=
    (UnbalancedCorr.odd_card_map_pPrimeCore K').of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hσ)
  obtain ⟨y, hyσ, hab⟩ := exists_commute_conj_of_odd haa hb₀b₀ hσodd
  have hyO : y ∈ oddIn K' := (zpowers_le.mpr hσ) hyσ
  have hyK' : y ∈ K' := map_subtype_le _ hyO
  set g : X := m * y with hg
  have hbg : y⁻¹ * b₀ * y = g⁻¹ * a * g := by rw [hb₀, hg]; group
  rw [hbg] at hab
  set b : X := g⁻¹ * a * g with hb
  have hKg : conjugate K g = K' := by
    rw [hg, ← conjugate_conjugate, ← hK']
    exact Single.conjugate_eq_of_mem_normalizer (le_normalizer hyK')
  have hbK' : b ∈ K' := by rw [← hKg]; exact conj_mem_conjugate haK g
  have hbCa : b ∈ centralizer ({a} : Set X) := mem_centralizer_singleton_iff.mpr hab.symm
  have hbN : b ∈ normalizer (J : Set X) := hCaN hbCa
  have hbJ : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ oddIn J := by
    intro j hj
    have h1 : j⁻¹ * b⁻¹ * j * b ∈ oddIn K := (mem_coreActionKernel.mp (hK'core hbK')).2 j (hJK hj)
    have h2 : j⁻¹ * b⁻¹ * j * b ∈ J := by
      have h3 := (mem_normalizer_iff.mp (inv_mem hbN) j).mp hj
      rw [inv_inv] at h3
      rw [show j⁻¹ * b⁻¹ * j * b = j⁻¹ * (b⁻¹ * j * b) by group]
      exact mul_mem (inv_mem hj) h3
    rw [hOJ]
    exact mem_inf.mpr ⟨h2, hOK h1⟩
  have hbcore : b ∈ coreActionKernel J := ⟨hbN, hbJ⟩
  have hb2 : orderOf b = 2 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective a
    simpa [MulAut.conj_apply, hs.orderOf_eq, hb] using this
  have hbP : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  obtain ⟨hsF, hnF, hoF⟩ := GrS4.fstar_facts_of_gsMaximalSetting hgs
  have hFle := hFixL X hsF hnF hoF hs.kProper a J hs.orderOf_eq hJa hJc hs.maximal hL34 hbase g hab
    hbN hbJ
  set F : Subgroup X := gsFixedLayer J b with hF
  have hFJ : F ≤ J ⊓ centralizer ({b} : Set X) := map_subtype_le _
  have hFp : ⁅F, F⁆ = F := by
    rw [hF, gsFixedLayer, ← map_commutator, pLayer_two_isPerfect]
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hJa)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hJc)
  have hFsup : F ⊔ oddIn J = J := by
    have h1 := (GSLit.fixedLayer_sup_pPrimeCore hJq (zpowers_le.mpr hbcore) hbP).1
    rwa [GSLit.fixedLayer_zpowers] at h1
  have hJ'C : conjugate J g ≤ centralizer ({b} : Set X) := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 := mem_centralizer_singleton_iff.mp (hJa hx)
    rw [mem_centralizer_singleton_iff, hb]
    calc x * (g⁻¹ * a * g) = g⁻¹ * ((g * x * g⁻¹) * a) * g := by group
      _ = g⁻¹ * (a * (g * x * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * a * g * x := by group
  have hCJ' : centralizer ({b} : Set X) ≤ normalizer ((conjugate J g : Subgroup X) : Set X) := by
    intro c hc
    have hc' : g * c * g⁻¹ ∈ centralizer ({a} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := mem_centralizer_singleton_iff.mp hc
      rw [hb] at h1
      calc g * c * g⁻¹ * a = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by rw [h1]
        _ = a * (g * c * g⁻¹) := by group
    have hn := hCaN hc'
    rw [mem_normalizer_iff]
    intro x
    rw [mem_conjugate_iff, mem_conjugate_iff, mem_normalizer_iff.mp hn (g * x * g⁻¹),
      show g * c * g⁻¹ * (g * x * g⁻¹) * (g * c * g⁻¹)⁻¹ = g * (c * x * c⁻¹) * g⁻¹ by group]
  have hFJ' : F ≤ conjugate J g := le_of_le_sup_oddIn (hFJ.trans inf_le_right) hJ'C hCJ' hFp
    (hFle.trans (sup_comm _ _).le)
  have hFK' : F ≤ K' := by
    rw [← hKg]
    exact hFJ'.trans (map_mono hJK)
  have hFO : F ≤ oddIn J := by
    have h1 : F ≤ oddIn K := by
      rw [← hFp]
      exact (commutator_mono ((hFJ.trans inf_le_left).trans hJK) hFK').trans
        (hKK'.trans inf_le_left)
    rw [hOJ]
    exact le_inf (hFJ.trans inf_le_left) (h1.trans hOK)
  have hJO : J ≤ oddIn J := by
    have h := sup_le hFO (le_refl (oddIn J))
    rwa [hFsup] at h
  exact GrS4.not_odd_card_of_isPComponent hJa hJc
    ((UnbalancedCorr.odd_card_map_pPrimeCore J).of_dvd_nat (card_dvd_of_le hJO))

end CFSG.ComponentClassification.GrSLit.Single
