module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleSFL
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.Single

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem false_of_commute_conj_mem_coreActionKernel (hMax : MaximalTwoComponentInput)
    (hFixL : SolomonFixedLayerStep) {a : X} {J W K : Subgroup X}
    (hs : SingleComponentSetting X a J W K) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hbase : L34BaseSetting X) {g : X}
    (hg : g ∈ normalizer (W : Set X)) (hgK : conjugate K g ≠ K)
    (hab : a * (g⁻¹ * a * g) = g⁻¹ * a * g * a) (hbK : g⁻¹ * a * g ∈ coreActionKernel K) :
    False := by
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
  have hOJ : oddIn J = J ⊓ oddIn M := GrS4.oddIn_eq_inf_of_singleComponentSetting hs
  have hOK : oddIn K ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc
  have hne : K ≠ conjugate K g := fun e => hgK e.symm
  have hK'M : conjugate K g ≤ M := UnbalancedCorr.conjugate_le_of_mem hKM hg
  have hK'c : IsPComponent 2 ((conjugate K g).subgroupOf M) :=
    UnbalancedCorr.isPComponent_conjugate_subgroupOf hg hKc
  have hKK' : ⁅K, conjugate K g⁆ ≤ oddIn K ⊓ oddIn (conjugate K g) :=
    GrS5.commutator_le_inf_oddIn hKM hK'M hKc hK'c hne
  set b : X := g⁻¹ * a * g with hb
  have hbCa : b ∈ centralizer ({a} : Set X) := mem_centralizer_singleton_iff.mpr hab.symm
  have hbN : b ∈ normalizer (J : Set X) := hCaN hbCa
  have hbJ : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ oddIn J := by
    intro j hj
    have h1 : j⁻¹ * b⁻¹ * j * b ∈ oddIn K := (mem_coreActionKernel.mp hbK).2 j (hJK hj)
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
  have hFK' : F ≤ conjugate K g := hFJ'.trans (map_mono hJK)
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

theorem false_of_conj_mem_coreActionKernel (hMax : MaximalTwoComponentInput)
    (hFixL : SolomonFixedLayerStep) {a : X} {J W K : Subgroup X}
    (hs : SingleComponentSetting X a J W K) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hbase : L34BaseSetting X) {g : X}
    (hg : g ∈ normalizer (W : Set X)) (hgK : conjugate K g ≠ K)
    (hbK : g⁻¹ * a * g ∈ coreActionKernel K)
    (hodd : Odd (orderOf (a * (g⁻¹ * a * g) * (a * (g⁻¹ * a * g))))) : False := by
  have haa : a * a = 1 := by rw [← pow_two, ← hs.orderOf_eq, pow_orderOf_eq_one]
  set b₀ : X := g⁻¹ * a * g with hb₀
  have hb₀b₀ : b₀ * b₀ = 1 := by
    rw [hb₀, show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, haa]
    group
  obtain ⟨y, hyσ, hab⟩ := exists_commute_conj_of_odd haa hb₀b₀ hodd
  have haK : a ∈ coreActionKernel K := GrS4.mem_coreActionKernel_of_singleComponentSetting hMax hs
  have haN : a ∈ normalizer (K : Set X) := (mem_coreActionKernel.mp haK).1
  have hb₀N : b₀ ∈ normalizer (K : Set X) := (mem_coreActionKernel.mp hbK).1
  have hyN : y ∈ normalizer (K : Set X) :=
    (zpowers_le.mpr (mul_mem (mul_mem haN hb₀N) (mul_mem haN hb₀N))) hyσ
  have haM : a ∈ normalizer (W : Set X) := GrS4.centralizer_le_of_singleComponentSetting hMax hs
    (mem_centralizer_singleton_iff.mpr rfl)
  have hb₀M : b₀ ∈ normalizer (W : Set X) := mul_mem (mul_mem (inv_mem hg) haM) hg
  have hyM : y ∈ normalizer (W : Set X) :=
    (zpowers_le.mpr (mul_mem (mul_mem haM hb₀M) (mul_mem haM hb₀M))) hyσ
  have e : (g * y)⁻¹ * a * (g * y) = y⁻¹ * b₀ * y := by rw [hb₀]; group
  refine false_of_commute_conj_mem_coreActionKernel hMax hFixL hs hL34 hbase (mul_mem hg hyM) ?_
    (by rw [e]; exact hab) ?_
  ·
    intro h
    apply hgK
    have h1 : conjugate K g = conjugate (conjugate K (g * y)) y⁻¹ := by
      rw [UnbalancedLayer.conjugate_conjugate, mul_inv_cancel_right]
    rw [h1, h, Single.conjugate_eq_of_mem_normalizer (inv_mem hyN)]
  ·
    rw [e]
    have h1 := UnbalancedLayer.conj_mem_coreActionKernel (inv_mem hyN) hbK
    rwa [inv_inv] at h1

end CFSG.ComponentClassification.GrSLit.Single
