module

import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section General

variable {Y : Type*} [Group Y]

theorem mul_comm_of_inf_eq_bot_of_le_normalizer {A B : Subgroup Y}
    (hAB : A ≤ Subgroup.normalizer (B : Set Y)) (hBA : B ≤ Subgroup.normalizer (A : Set Y))
    (hbot : A ⊓ B = ⊥) {a b : Y} (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ A := by
    have h3 := A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hBA hb) a⁻¹).mp (A.inv_mem ha))
    simpa only [mul_assoc] using h3
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := Subgroup.mem_inf.mpr
    ⟨h2, B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAB ha) b).mp hb) (B.inv_mem hb)⟩
  rw [hbot, Subgroup.mem_bot] at h1
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem le_of_not_le_centralizer {K N : Subgroup Y} [IsSimpleGroup K]
    (hKN : K ≤ Subgroup.normalizer (N : Set Y)) (hNK : N ≤ Subgroup.normalizer (K : Set Y))
    (hC : ¬ N ≤ Subgroup.centralizer (K : Set Y)) : K ≤ N := by
  by_cases hbot : N ⊓ K = ⊥
  · refine absurd (fun n hn => Subgroup.mem_centralizer_iff.mpr fun k hk => ?_) hC
    exact (mul_comm_of_inf_eq_bot_of_le_normalizer hNK hKN hbot hn hk).symm
  · have h := eq_of_le_normalizer_of_isSimpleGroup inf_le_right
      ((le_inf hKN Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf) hbot
    exact h.symm.le.trans inf_le_left

theorem isSimpleGroup_of_center_eq_bot {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hZ : Subgroup.center L = ⊥) : IsSimpleGroup L := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

end General

section Reduced

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.normalizer_sup_zpowers_le_of_ne (h : ReducedNongeneration p Y Rb Y₀)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    {t₁ t₂ : Y} (ht₁ : t₁ ∈ (Rb : Subgroup Y) ⊓ L₁) (ht₁p : orderOf t₁ = p)
    (ht₂ : t₂ ∈ (Rb : Subgroup Y) ⊓ L₂) (ht₂p : orderOf t₂ = p) :
    Subgroup.normalizer ((Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ : Subgroup Y) : Set Y) ≤
      Y₀ := by
  have hp := h.prime
  have h₁₂ := le_centralizer_of_component_ne h₁ h₂ hne
  have ht₂C : t₂ ∉ Subgroup.zpowers t₁ := by
    intro ht
    have h1 := h.eq_one_of_mem_centralizer_of_isCyclic h₂ (hcyc L₂ h₂) ht₂.2
      (Subgroup.zpowers_le.mpr (h₁₂ ht₁.2) ht)
    rw [h1, orderOf_one] at ht₂p
    exact hp.one_lt.ne ht₂p
  have hQR : Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ ≤ Rb :=
    sup_le (Subgroup.zpowers_le.mpr ht₁.1) (Subgroup.zpowers_le.mpr ht₂.1)
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp ht₁p (ht₂p ▸ pow_orderOf_eq_one t₂) ht₂C
      (Subgroup.mem_centralizer_iff.mp (h₁₂ ht₁.2) t₂ ht₂.2).symm
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂))
  have hC := h.three_le_pRank_inf_centralizer_sup_zpowers ht₁p ht₂p
    (fun v hv => h.conj_mem_zpowers_of_component h₁ (hcyc L₁ h₁) ht₁ hv)
    (fun v hv => h.conj_mem_zpowers_of_component h₂ (hcyc L₂ h₂) ht₂ hv)
  exact (normalizer_le_weakCore p hQR hQ2 (hC.trans (pRank_mono p hp le_sup_right))).trans
    h.weakCore_le

theorem ReducedNongeneration.top_le_sup_layer (h : ReducedNongeneration p Y Rb Y₀)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂) :
    (⊤ : Subgroup Y) ≤ Y₀ ⊔ CFSG.layer Y := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨t₁, ht₁, ht₁p, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb h₁
  obtain ⟨t₂, ht₂, ht₂p, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb h₂
  have hmem : ∀ L : Subgroup Y, IsComponentOf L ⊤ → ∀ t ∈ L, orderOf t = p → ∀ g : Y,
      g * t * g⁻¹ ∈ (Rb : Subgroup Y) →
        g * t * g⁻¹ ∈ Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ := by
    intro L hL t htL ht g hg
    have hgt : g * t * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨t, htL, rfl⟩
    rcases h.eq_or_eq_of_isComponentOf h₁ h₂ hne
        ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL) with
      heq | heq
    · have := hcyc L₁ h₁
      exact Subgroup.mem_sup_left (conj_mem_zpowers_of_isCyclic (T := (Rb : Subgroup Y) ⊓ L₁)
        (ht.trans ht₁p.symm) ht₁ ⟨hg, heq ▸ hgt⟩)
    · have := hcyc L₂ h₂
      exact Subgroup.mem_sup_right (conj_mem_zpowers_of_isCyclic (T := (Rb : Subgroup Y) ⊓ L₂)
        (ht.trans ht₂p.symm) ht₂ ⟨hg, heq ▸ hgt⟩)
  have hNQ := h.normalizer_sup_zpowers_le_of_ne hcyc h₁ h₂ hne ht₁ ht₁p ht₂ ht₂p
  have hN : Subgroup.normalizer (((Rb : Subgroup Y) ⊓ CFSG.layer Y : Subgroup Y) : Set Y) ≤ Y₀ :=
    fun g hg => hNQ (mem_normalizer_sup_zpowers
      (hmem L₁ h₁ t₁ ht₁.2 ht₁p g ((Subgroup.mem_normalizer_iff.mp hg t₁).mp
        ⟨ht₁.1, le_layer_of_isComponentOf h₁ ht₁.2⟩).1)
      (hmem L₂ h₂ t₂ ht₂.2 ht₂p g ((Subgroup.mem_normalizer_iff.mp hg t₂).mp
        ⟨ht₂.1, le_layer_of_isComponentOf h₂ ht₂.2⟩).1))
  obtain ⟨S, hS⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (Subgroup.Normal.isSubnormal (inferInstance : (CFSG.layer Y).Normal))
  have htop := Sylow.normalizer_sup_eq_top S
  rw [hS] at htop
  rw [← htop]
  exact sup_le_sup_right hN _

end Reduced

section Layer

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_component_not_le_centralizer
    (hZ : ∀ K : Subgroup Y, IsComponentOf K ⊤ → Subgroup.center K = ⊥) {A : Subgroup Y}
    (hAE : A ≤ CFSG.layer Y) (hA : A ≠ ⊥) :
    ∃ K : Subgroup Y, IsComponentOf K ⊤ ∧ ¬ A ≤ Subgroup.centralizer (K : Set Y) := by
  by_contra hall
  push Not at hall
  have hAC : A ≤ Subgroup.centralizer (CFSG.layer Y : Set Y) :=
    Subgroup.le_centralizer_iff.mp (sSup_le fun K hK =>
      Subgroup.le_centralizer_iff.mp (hall K ((CFSG.isComponent_iff_open K).mp hK)))
  refine hA (eq_bot_iff.mpr fun a ha => ?_)
  obtain ⟨x, rfl⟩ := CFSG.LocalCores.exists_layerMul_eq (hAE ha)
  have hx := (CFSG.LocalCores.layerMul_mem_centralizer_iff x).mp (hAC ha)
  have h1 : x = 1 := funext fun K => by
    have h2 := hx K
    rw [hZ K.1 ((CFSG.isComponent_iff_open K.1).mp K.2), Subgroup.mem_bot] at h2
    exact h2
  rw [h1, map_one]
  exact Subgroup.one_mem _

theorem commutator_eq_self_of_le_layer
    (hZ : ∀ K : Subgroup Y, IsComponentOf K ⊤ → Subgroup.center K = ⊥) {N : Subgroup Y}
    (hN : N.Normal) (hNE : N ≤ CFSG.layer Y) : ⁅N, N⁆ = N := by
  refine le_antisymm (Subgroup.commutator_le_self N) fun n hn => ?_
  obtain ⟨x, rfl⟩ := CFSG.LocalCores.exists_layerMul_eq (hNE hn)
  refine CFSG.LocalCores.layerMul_mem x fun K => ?_
  have hK := (CFSG.isComponent_iff_open K.1).mp K.2
  have : IsSimpleGroup K.1 := isSimpleGroup_of_center_eq_bot hK (hZ K.1 hK)
  have hKN : K.1 ≤ Subgroup.normalizer (N : Set Y) :=
    le_top.trans (Subgroup.normalizer_eq_top (H := N)).ge
  have hNK : N ≤ Subgroup.normalizer (K.1 : Set Y) :=
    hNE.trans (CFSG.LocalCores.layer_le_normalizer K.2)
  by_cases hKle : K.1 ≤ N
  · have hperf : ⁅K.1, K.1⁆ = K.1 :=
      Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hK.2.2.1)
    exact Subgroup.commutator_mono hKle hKle (hperf.symm ▸ (x K).2)
  · have hbot : N ⊓ K.1 = ⊥ := by
      by_contra hne
      exact hKle ((eq_of_le_normalizer_of_isSimpleGroup inf_le_right ((le_inf hKN
        Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf) hne).symm.le.trans
        inf_le_left)
    have hc : x K ∈ Subgroup.center K.1 := Subgroup.mem_center_iff.mpr fun k => Subtype.ext
      ((CFSG.LocalCores.commute_layerMul_iff x K k.2).mp
        (mul_comm_of_inf_eq_bot_of_le_normalizer hKN hNK (inf_comm N K.1 ▸ hbot) k.2 hn)).eq
    rw [hZ K.1 hK, Subgroup.mem_bot] at hc
    rw [hc]
    exact Subgroup.one_mem _

end Layer

section Closure

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.le_centralizer_of_le (h : ReducedNongeneration p Y Rb Y₀)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y)) (hKY₀ : K ≤ Y₀) {A : Subgroup Y}
    (hAR : A ≤ Rb) (hAY₀ : Y₀ ≤ Subgroup.normalizer (A : Set Y)) :
    A ≤ Subgroup.centralizer (K : Set Y) := by
  have : IsSimpleGroup K := isSimpleGroup_of_center_eq_bot hK (h.center_eq_bot_of_isCyclic hK hcyc)
  by_contra hC
  have hKA := le_of_not_le_centralizer (hKY₀.trans hAY₀)
    (hAR.trans (h.sylow_le_normalizer_component hK)) hC
  have : IsCyclic K := Subgroup.isCyclic_of_le (le_inf (hKA.trans hAR) le_rfl)
  have : Group.IsPerfect K := Group.isPerfect_def.mpr hK.2.2.1
  have : Subsingleton K := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact not_subsingleton K ‹_›

theorem ReducedNongeneration.exists_component_le_of_normal (h : ReducedNongeneration p Y Rb Y₀)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {A N : Subgroup Y} (hAE : A ≤ CFSG.layer Y) (hAR : A ≤ Rb) (hA : A ≠ ⊥)
    (hAY₀ : Y₀ ≤ Subgroup.normalizer (A : Set Y)) (hN : N.Normal) (hAN : A ≤ N)
    (hNE : N ≤ CFSG.layer Y) : ∃ K : Subgroup Y, IsComponentOf K ⊤ ∧ K ≤ N ∧ ¬ K ≤ Y₀ := by
  obtain ⟨K, hK, hAK⟩ := exists_component_not_le_centralizer
    (fun K hK => h.center_eq_bot_of_isCyclic hK (hcyc K hK)) hAE hA
  have : IsSimpleGroup K :=
    isSimpleGroup_of_center_eq_bot hK (h.center_eq_bot_of_isCyclic hK (hcyc K hK))
  refine ⟨K, hK, le_of_not_le_centralizer (le_top.trans (Subgroup.normalizer_eq_top (H := N)).ge)
    (hNE.trans (CFSG.LocalCores.layer_le_normalizer ((CFSG.isComponent_iff_open K).mpr hK)))
    fun hNC => hAK (hAN.trans hNC), fun hKY₀ => hAK (h.le_centralizer_of_le hK (hcyc K hK) hKY₀
    hAR hAY₀)⟩

theorem ReducedNongeneration.le_nclIn_of_normal (h : ReducedNongeneration p Y Rb Y₀)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {A N : Subgroup Y} (hAE : A ≤ CFSG.layer Y) (hA : A ≠ ⊥)
    (hAY₀ : Y₀ ≤ Subgroup.normalizer (A : Set Y)) (hN : N.Normal) (hAN : A ≤ N)
    (hmin : ∀ W : Subgroup Y, W.Normal → A ≤ W → N ≤ W) : N ≤ nclIn N A := by
  have : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
  have hNE : N ≤ CFSG.layer Y := hmin _ inferInstance hAE
  have hZ : ∀ K : Subgroup Y, IsComponentOf K ⊤ → Subgroup.center K = ⊥ :=
    fun K hK => h.center_eq_bot_of_isCyclic hK (hcyc K hK)
  have hAW : A ≤ nclIn N A := le_nclIn hAN
  have hNW : N ≤ Subgroup.normalizer (nclIn N A : Set Y) := le_normalizer_nclIn N A
  have hYN : ∀ K : Subgroup Y, K ≤ Subgroup.normalizer (N : Set Y) := fun K =>
    le_top.trans (Subgroup.normalizer_eq_top (H := N)).ge
  have hconj : ∀ S : Subgroup Y, (∀ g ∈ S, ∀ a ∈ A, g * a * g⁻¹ ∈ A) →
      S ≤ Subgroup.normalizer (nclIn N A : Set Y) := by
    intro S hS
    refine le_normalizer_of_forall_mul_mul_inv_mem fun g hg w hw => ?_
    have hle : nclIn N A ≤ (nclIn N A).comap (MulAut.conj g).toMonoidHom := by
      refine nclIn_le_of_forall_conj_mem fun c hc a ha => ?_
      have hgc : g * c * g⁻¹ ∈ N := hN.conj_mem c hc g
      have e : (MulAut.conj g).toMonoidHom (c * a * c⁻¹) =
          g * c * g⁻¹ * (g * a * g⁻¹) * (g * c * g⁻¹)⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [Subgroup.mem_comap, e]
      exact (Subgroup.mem_normalizer_iff.mp (hNW hgc) _).mp (hAW (hS g hg a ha))
    have h1 := hle hw
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have hY₀W : Y₀ ≤ Subgroup.normalizer (nclIn N A : Set Y) :=
    hconj Y₀ fun x hx a ha => (Subgroup.mem_normalizer_iff.mp (hAY₀ hx) a).mp ha
  have hKW : ∀ K : Subgroup Y, IsComponentOf K ⊤ →
      K ≤ Subgroup.normalizer (nclIn N A : Set Y) := by
    intro K hK
    have : IsSimpleGroup K := isSimpleGroup_of_center_eq_bot hK (hZ K hK)
    by_cases hAK : A ≤ Subgroup.centralizer (K : Set Y)
    · refine hconj K fun k hk a ha => ?_
      rw [Subgroup.mem_centralizer_iff.mp (hAK ha) k hk, mul_inv_cancel_right]
      exact ha
    · exact (le_of_not_le_centralizer (hYN K)
        (hNE.trans (CFSG.LocalCores.layer_le_normalizer ((CFSG.isComponent_iff_open K).mpr hK)))
        fun hNC => hAK (hAN.trans hNC)).trans hNW
  by_cases htwo : ∃ L₁ L₂ : Subgroup Y, IsComponentOf L₁ ⊤ ∧ IsComponentOf L₂ ⊤ ∧ L₁ ≠ L₂
  · obtain ⟨L₁, L₂, h₁, h₂, hne⟩ := htwo
    have hWn : (nclIn N A).Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp
      ((h.top_le_sup_layer hcyc h₁ h₂ hne).trans (sup_le hY₀W
        (sSup_le fun K hK => hKW K ((CFSG.isComponent_iff_open K).mp hK)))))
    exact hmin _ hWn hAW
  · push Not at htwo
    obtain ⟨L, hL, hAL⟩ := exists_component_not_le_centralizer hZ hAE hA
    have : IsSimpleGroup L := isSimpleGroup_of_center_eq_bot hL (hZ L hL)
    have hEL : CFSG.layer Y ≤ L := sSup_le fun K hK =>
      (htwo K L ((CFSG.isComponent_iff_open K).mp hK) hL).le
    have hLN : L ≤ N := le_of_not_le_centralizer (hYN L) (hNE.trans (hEL.trans
      Subgroup.le_normalizer)) fun hNC => hAL (hAN.trans hNC)
    have heq := eq_of_le_normalizer_of_isSimpleGroup ((nclIn_le_self N A).trans (hNE.trans hEL))
      (hLN.trans hNW) fun hb => hA (le_bot_iff.mp (hb ▸ hAW))
    rw [heq]
    exact hNE.trans hEL

end Closure

end CFSG.AGLEmbedding
