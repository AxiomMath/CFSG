module

public import CFSG.GH74.GLS.SP.Local.SPLCt0
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen2

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section CtA2b

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

theorem Ict_le_pLayer (hs : SPLSetup D.toSPLNot0) : D.Ict ≤ pLayerOf 2 D.Ct :=
  CFSG.GH74.GLS.Stage1.Thm2.Recip.le_pLayerOf_of_isPCompIn_inf (s := D.z) (t := D.t)
    hs.syl.z_inv (mem_centralizer_singleton_iff.mpr (z_comm_t' D hs)) (I_comp D hs)

theorem pLayer_Ct_normal : ∀ c ∈ D.Ct, ∀ l ∈ pLayerOf 2 D.Ct, c * l * c⁻¹ ∈ pLayerOf 2 D.Ct := by
  intro c hc l hl
  have h := CFSG.GH74.GLS.Stage1.Thm2.Recip.pLayerOf_map_conj_le (X := D.Ct) hc
  have : MulAut.conj c l ∈ (pLayerOf 2 D.Ct).map (MulAut.conj c).toMonoidHom := ⟨l, hl, rfl⟩
  simpa [MulAut.conj_apply] using h this

theorem Ict_le_normalizer_Act (hs : SPLSetup D.toSPLNot0) : D.Ict ≤ normalizer (D.Act : Set G) := by
  intro i hi
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha; exact Act_normal D i (Ict_le_Ct D hs hi) a ha
  · intro ha
    have h := Act_normal D i⁻¹ (D.Ct.inv_mem (Ict_le_Ct D hs hi)) _ ha
    have e : i⁻¹ * (i * a * i⁻¹) * i⁻¹⁻¹ = a := by group
    rwa [e] at h

theorem pLayer_decomp (hs : SPLSetup D.toSPLNot0) (hK1 : SPLPumpAt D) {l : G}
    (hl : l ∈ pLayerOf 2 D.Ct) :
    ∃ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, ∃ i ∈ D.Ict, l = a * i := by
  obtain ⟨a, ha, i, hi, rfl⟩ := mem_sup_of_le_normalizer (Ict_le_normalizer_Act D hs) (hK1 hl)
  refine ⟨a, ⟨?_, ha⟩, i, hi, rfl⟩
  have h1 : a = (a * i) * i⁻¹ := by group
  rw [h1]
  exact Subgroup.mul_mem _ hl (Subgroup.inv_mem _ (Ict_le_pLayer D hs hi))

theorem commutator_pLayer (hs : SPLSetup D.toSPLNot0) (hK1 : SPLPumpAt D)
    (hcomm : ∀ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, ∀ i ∈ D.Ict, a * i = i * a) :
    ⁅pLayerOf 2 D.Ct, pLayerOf 2 D.Ct⁆ = D.Ict := by
  apply le_antisymm
  · rw [commutator_le]
    intro l₁ hl₁ l₂ hl₂
    obtain ⟨a₁, ha₁, i₁, hi₁, rfl⟩ := pLayer_decomp D hs hK1 hl₁
    obtain ⟨a₂, ha₂, i₂, hi₂, rfl⟩ := pLayer_decomp D hs hK1 hl₂
    have h1 : a₁ * i₂ = i₂ * a₁ := hcomm a₁ ha₁ i₂ hi₂
    have h2 : a₂ * i₁ = i₁ * a₂ := hcomm a₂ ha₂ i₁ hi₁
    have h3 : a₁ * a₂ = a₂ * a₁ := Act_comm D hs a₁ ha₁.2 a₂ ha₂.2
    have e1 : a₁ * i₁ = i₁ * a₁ := hcomm a₁ ha₁ i₁ hi₁
    have e2 : a₂ * i₂ = i₂ * a₂ := hcomm a₂ ha₂ i₂ hi₂
    rw [e1, e2, spl_commutator_mul_of_central h1 h2 h3]
    rw [commutatorElement_def]
    exact D.Ict.mul_mem (D.Ict.mul_mem (D.Ict.mul_mem hi₁ hi₂) (D.Ict.inv_mem hi₁))
      (D.Ict.inv_mem hi₂)
  · calc D.Ict = ⁅D.Ict, D.Ict⁆ := (Ict_perfect D hs).symm
      _ ≤ ⁅pLayerOf 2 D.Ct, pLayerOf 2 D.Ct⁆ :=
        commutator_mono (Ict_le_pLayer D hs) (Ict_le_pLayer D hs)

theorem Ict_normal_Ct (hs : SPLSetup D.toSPLNot0) (hK1 : SPLPumpAt D)
    (hcomm : ∀ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, ∀ i ∈ D.Ict, a * i = i * a) :
    ∀ c ∈ D.Ct, ∀ i ∈ D.Ict, c * i * c⁻¹ ∈ D.Ict := by
  intro c hc i hi
  have hcomm' := commutator_pLayer D hs hK1 hcomm
  rw [← hcomm'] at hi ⊢
  have hle : ⁅pLayerOf 2 D.Ct, pLayerOf 2 D.Ct⁆ ≤
      (⁅pLayerOf 2 D.Ct, pLayerOf 2 D.Ct⁆).comap (MulAut.conj c).toMonoidHom := by
    rw [commutator_le]
    intro l₁ hl₁ l₂ hl₂
    have h := Subgroup.commutator_mem_commutator (pLayer_Ct_normal D c hc l₁ hl₁)
      (pLayer_Ct_normal D c hc l₂ hl₂)
    have e : (MulAut.conj c).toMonoidHom ⁅l₁, l₂⁆ = ⁅c * l₁ * c⁻¹, c * l₂ * c⁻¹⁆ := by
      simp [MulAut.conj_apply, commutatorElement_def]
      group
    rw [Subgroup.mem_comap, e]; exact h
  have := hle hi
  simpa [MulAut.conj_apply] using this

theorem Act_comm_Ict (hs : SPLSetup D.toSPLNot0) (hK1 : SPLPumpAt D)
    (hcomm : ∀ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, ∀ i ∈ D.Ict, a * i = i * a) :
    ∀ a ∈ D.Act, ∀ i ∈ D.Ict, a * i = i * a := by
  intro a ha i hi
  have h1 : a * i * a⁻¹ ∈ D.Ict := Ict_normal_Ct D hs hK1 hcomm a (Act_le_Ct D ha) i hi
  have h2 : a * i * a⁻¹ * i⁻¹ ∈ D.Ict := D.Ict.mul_mem h1 (D.Ict.inv_mem hi)
  have h3 : i * a⁻¹ * i⁻¹ ∈ D.Act :=
    Act_normal D i (Ict_le_Ct D hs hi) a⁻¹ (D.Act.inv_mem ha)
  have h4 : a * i * a⁻¹ * i⁻¹ ∈ D.Act := by
    have : a * i * a⁻¹ * i⁻¹ = a * (i * a⁻¹ * i⁻¹) := by group
    rw [this]; exact D.Act.mul_mem ha h3
  have h5 : a * i * a⁻¹ * i⁻¹ ∈ D.Act ⊓ D.Ict := ⟨h4, h2⟩
  rw [Act_inf_Ict D hs, Subgroup.mem_bot] at h5
  calc a * i = (a * i * a⁻¹ * i⁻¹) * (i * a) := by group
    _ = i * a := by rw [h5, one_mul]

theorem Ict_eq_Ez (hs : SPLSetup D.toSPLNot0) (hK1 : SPLPumpAt D)
    (hcomm : ∀ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, ∀ i ∈ D.Ict, a * i = i * a) :
    D.Ict = IVK.Ez D.t := by
  have hIct : D.Ict ≤ D.Ct := Ict_le_Ct D hs
  have hnormI := Ict_normal_Ct D hs hK1 hcomm
  have hnorm : (D.Ict.subgroupOf D.Ct).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnormI g g.2 a ha⟩
  have hcomp : CFSG.IsComponent (D.Ict.subgroupOf D.Ct) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hIct).symm
      (Ict_quasisimple D hs), hnorm.isSubnormal⟩
  show D.Ict = (CFSG.layer ↥D.Ct).map D.Ct.subtype
  apply le_antisymm
  · rw [← Subgroup.map_subgroupOf_eq_of_le hIct]
    exact Subgroup.map_mono (CFSG.LocalCores.component_le_layer hcomp)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    have hKeq : (K.map D.Ct.subtype).subgroupOf D.Ct = K :=
      Subgroup.comap_map_eq_self_of_injective D.Ct.subtype_injective K
    have hK2 : IsPCompIn 2 D.Ct (K.map D.Ct.subtype) := by
      refine ⟨Subgroup.map_subtype_le K, ?_⟩
      rw [hKeq]
      exact CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hK
    have hKL : K.map D.Ct.subtype ≤ pLayerOf 2 D.Ct := le_sSup hK2
    have hKperf : ⁅K.map D.Ct.subtype, K.map D.Ct.subtype⁆ = K.map D.Ct.subtype := by
      rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hK.1.1]
    have hKI : K.map D.Ct.subtype ≤ D.Ict := by
      calc K.map D.Ct.subtype = ⁅K.map D.Ct.subtype, K.map D.Ct.subtype⁆ := hKperf.symm
        _ ≤ ⁅pLayerOf 2 D.Ct, pLayerOf 2 D.Ct⁆ := commutator_mono hKL hKL
        _ = D.Ict := commutator_pLayer D hs hK1 hcomm
    intro x hx
    exact hKI ⟨x, hx, rfl⟩

theorem ctA_of_layer (hs : SPLSetup D.toSPLNot0) (hK1 : SPLPumpAt D) {u : G} (hu : SPLCtU D u)
    (hA0 : IsCyclic ↥(D.Act ⊓ centralizer ({u} : Set G)) ∧
      Nat.card ↥(D.Act ⊓ centralizer ({u} : Set G)) ∣ D.e)
    (hcomm : ∀ a ∈ pLayerOf 2 D.Ct ⊓ D.Act, ∀ i ∈ D.Ict, a * i = i * a) : SPLCtA D := by
  have hAI := Act_comm_Ict D hs hK1 hcomm
  have hAu : D.Act ⊓ centralizer ({u} : Set G) = D.Act := by
    apply inf_eq_left.mpr
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hAI a ha u hu.mem_I)
  rw [hAu] at hA0
  exact ⟨Ict_normal_Ct D hs hK1 hcomm, hAI, hA0.1, hA0.2, Ict_eq_Ez D hs hK1 hcomm⟩

end CtA2b

end CFSG.GH74.GLS.SP.Local
