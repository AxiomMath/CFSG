module

public import CFSG.GH74.Generic.BProg.B3.S3Boot152

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.GH74.GLS.Th2.Bal CFSG.Assembly.Dichotomy
open scoped commutatorElement

namespace S3Boot154

variable {G : Type} [Group G] [Finite G]

theorem inf_pPrimeCoreOf_le {J M : Subgroup G} (hJM : J ≤ M) :
    J ⊓ pPrimeCoreOf 2 M ≤ pPrimeCoreOf 2 J := by
  set N : Subgroup ↥J := (pPrimeCoreOf 2 M).subgroupOf J with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    exact CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore (hJM g.2) hn
  have hodd : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) :=
    Nat.coprime_two_left.mp (coprime_card_pPrimeCoreOf _)
  have hcop : Nat.Coprime 2 (Nat.card ↥N) := by
    refine Nat.coprime_two_left.mpr (Odd.of_dvd_nat hodd ?_)
    exact Subgroup.card_comap_dvd_of_injective (pPrimeCoreOf 2 M) J.subtype J.subtype_injective
  have hle : N ≤ pPrimeCore 2 ↥J := CFSG.le_pPrimeCore_of_normal_coprime hNn hcop
  intro y hy
  exact ⟨⟨y, hy.1⟩, hle (Subgroup.mem_subgroupOf.mpr hy.2), rfl⟩

theorem exists_obs_element {x : G} {K A B M : Subgroup G} (h : Boot15B G x K A B M) {a : G}
    {D J : Subgroup G} (hobs : Obs32 A a D J) :
    ∃ w ∈ pPrimeCoreOf 2 M, w ∈ centralizer ({a} : Set G) ∧ w ∈ normalizer (J : Set G) ∧
      w ∉ centralizerSection J (pPrimeCoreOf 2 J) := by
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := h.B_E4.2.1
  have hγ : gammaK 2 B 3 ≤ M := (prop41_52 h.B_E4 h.bal52.1 h.bal52.2).2.1.trans h.M_norm
  have hBM : B ≤ M := (S3Boot152.le_gammaK_self hBel (by rw [h.B_rank]; norm_num)).trans hγ
  have hAM : A ≤ M := h.AB.trans hBM
  have hA : IsE 3 ⊤ A := isE3_of_isSource2 h.src
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hA.2.1
  obtain ⟨hAc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hAel
  have hYM : ∀ d ∈ A, d ≠ 1 → pPrimeCoreOf 2 (centralizer ({d} : Set G)) ≤ M := fun d hd hd1 =>
    S3Boot152.pPrimeCoreOf_centralizer_le hBel h.B_rank hγ (h.AB hd)
  have hDA : D ≤ A := hobs.D_le.1
  have hD1 : ∃ d ∈ D, d ≠ 1 := exists_ne_one_of_isE_one hobs.D_le
  have hA1 : ∃ d ∈ A, d ≠ 1 := by
    obtain ⟨d, hd, hd1⟩ := hD1
    exact ⟨d, hDA hd, hd1⟩
  rcases hobs.unbal with ⟨hr2, hnle⟩ | ⟨hr1, c, hc, b, hbA, hcb⟩
  · obtain ⟨c, hc, hcn⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    refine ⟨c, ?_, hc.2, Obs32.AG_inf_le_normalizer hobs hc, hcn⟩
    have hD2 : IsE 2 A D := ⟨hDA, hobs.D_le.2.1, by omega⟩
    have h1 : thetaHalf 1 D ≤ thetaHalfPrime A :=
      le_iSup₂_of_le D hD2 (le_iSup_of_le hr2 le_rfl)
    have h2 : AG D ≤ thetaHalf 1 D := le_sup_right
    exact lemma153 h (h1 (h2 hc.1))
  · have hbC : b ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hobs.y_cent b hbA)
    have hcomm : ⁅c, b⁆ = c * (b * c⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hconj : b * c⁻¹ * b⁻¹ ∈ AG D ⊓ centralizer ({a} : Set G) :=
      ⟨conj_mem_AG (fun d hd => hAc b hbA d (hDA hd)) ((AG D).inv_mem hc.1),
        (centralizer ({a} : Set G)).mul_mem
          ((centralizer ({a} : Set G)).mul_mem hbC ((centralizer ({a} : Set G)).inv_mem hc.2))
          ((centralizer ({a} : Set G)).inv_mem hbC)⟩
    refine ⟨⁅c, b⁆, ?_, ?_, ?_, hcb⟩
    · have h0 : ⁅AG D, A⁆ ≤ thetaHalf 1 A := le_sup_of_le_left (le_iSup₂_of_le D hobs.D_le le_rfl)
      have h1 : ⁅c, b⁆ ∈ thetaHalf 1 A := h0 (Subgroup.commutator_mem_commutator hc.1 hbA)
      have h2 := S3Boot152.thetaHalf_le_map_subgroupOf hAM hA1 hAel hYM h1
      exact Subgroup.map_mono h.locM h2
    · rw [hcomm]
      exact (centralizer ({a} : Set G)).mul_mem hc.2 hconj.2
    · rw [hcomm]
      exact (normalizer (J : Set G)).mul_mem (Obs32.AG_inf_le_normalizer hobs hc)
        (Obs32.AG_inf_le_normalizer hobs hconj)

theorem not_le_of_obs_element {M J : Subgroup G} {w : G} (hwM : w ∈ pPrimeCoreOf 2 M)
    (hwN : w ∈ normalizer (J : Set G)) (hw : w ∉ centralizerSection J (pPrimeCoreOf 2 J)) :
    ¬ J ≤ M := by
  intro hJM
  apply hw
  refine ⟨hwN, TwoThin.mem_normalizer_pPrimeCoreOf hwN, fun k hk => ?_⟩
  have h1 : ⁅k, w⁆ ∈ J := by
    have hcomm : ⁅k, w⁆ = k * (w * k⁻¹ * w⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hcomm]
    exact J.mul_mem hk ((Subgroup.mem_normalizer_iff.mp hwN k⁻¹).mp (J.inv_mem hk))
  have h2 : ⁅k, w⁆ ∈ pPrimeCoreOf 2 M := by
    have hcomm : ⁅k, w⁆ = (k * w * k⁻¹) * w⁻¹ := by
      simp only [commutatorElement_def]
    rw [hcomm]
    exact (pPrimeCoreOf 2 M).mul_mem
      (CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore (hJM hk) hwM)
      ((pPrimeCoreOf 2 M).inv_mem hwM)
  exact inf_pPrimeCoreOf_le hJM ⟨h1, h2⟩

end S3Boot154

section SD11

variable {G : Type} [Group G] [Finite G]

theorem lemma154_p2 (hKG : BootKG G) {x a : G} {K A B M D J : Subgroup G}
    (h : Boot15B G x K A B M) (haA : a ∈ A) (hobs : Obs32 A a D J) : False := by
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := h.B_E4.2.1
  have hγ : gammaK 2 B 3 ≤ M := (prop41_52 h.B_E4 h.bal52.1 h.bal52.2).2.1.trans h.M_norm
  obtain ⟨w, hwM, hwC, hwN, hw⟩ := S3Boot154.exists_obs_element h hobs
  have hJM : ¬ J ≤ M := S3Boot154.not_le_of_obs_element hwM hwN hw
  have hiso : Nonempty ((↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7)) :=
    hKG.a7id x K A B M a D J h haA hobs ⟨w, hwM, hwC, hwN, hw⟩
  have ha1 : a ≠ 1 := by
    intro h1
    have := hobs.y_ord
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have haK : a ∉ K := by
    intro haK
    exact hJM ((h.a7 a ⟨haA, haK⟩ ha1 D J hobs hiso).trans hγ)
  exact hKG.excl x K A B M a D J h haA hobs hiso haK

theorem prop151_p2 (hKG : BootKG G) {x : G} {K A B M : Subgroup G} (h : Boot15B G x K A B M) :
    IsBal32 A := by
  by_contra hnot
  obtain ⟨a, D, J, haA, hobs⟩ := exists_obs32 (isE3_of_isSource2 h.src) hnot
  exact lemma154_p2 hKG h haA hobs

end SD11

end CFSG.GH74.Generic.BProg.B3
