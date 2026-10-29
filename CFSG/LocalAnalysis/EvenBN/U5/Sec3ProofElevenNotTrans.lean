module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofThirteenB

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

section S311bGeneric

variable {Q : Type*} [Group Q] [Finite Q]

theorem s311b_sylow_split {D₁ D₂ T : Subgroup Q}
    (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x) (hi : D₁ ⊓ D₂ = ⊥)
    (hT : IsSylowOf 2 T (D₁ ⊔ D₂)) :
    IsSylowOf 2 (T ⊓ D₁) D₁ ∧ IsSylowOf 2 (T ⊓ D₂) D₂ ∧ T = (T ⊓ D₁) ⊔ (T ⊓ D₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN₁ : D₁ ⊔ D₂ ≤ normalizer (D₁ : Set Q) := sup_le Subgroup.le_normalizer
    (fun y hy => Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun u hu => hc u hu y hy))
  have hN₂ : D₁ ⊔ D₂ ≤ normalizer (D₂ : Set Q) := sup_le
    (fun x hx => Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun u hu => (hc x hx u hu).symm)) Subgroup.le_normalizer
  have h₁ := hT.inf_of_le_normalizer le_sup_left hN₁
  have h₂ := hT.inf_of_le_normalizer le_sup_right hN₂
  refine ⟨h₁, h₂, ?_⟩
  have hle : (T ⊓ D₁) ⊔ (T ⊓ D₂) ≤ T := sup_le inf_le_left inf_le_left
  have hcT : ∀ x ∈ T ⊓ D₁, ∀ y ∈ T ⊓ D₂, x * y = y * x := fun x hx y hy =>
    hc x (Subgroup.mem_inf.1 hx).2 y (Subgroup.mem_inf.1 hy).2
  have hbot : (T ⊓ D₁) ⊓ (T ⊓ D₂) = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have : z ∈ D₁ ⊓ D₂ := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).1).2,
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hz).2).2⟩
    rwa [hi] at this
  have hcard12 : Nat.card ↥(D₁ ⊔ D₂) = Nat.card D₁ * Nat.card D₂ := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute D₁ D₂ hc).1
    rwa [hi, Subgroup.card_bot, mul_one] at this
  have hcardT : Nat.card ↥((T ⊓ D₁) ⊔ (T ⊓ D₂)) = Nat.card ↥(T ⊓ D₁) * Nat.card ↥(T ⊓ D₂) := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (T ⊓ D₁) (T ⊓ D₂) hcT).1
    rwa [hbot, Subgroup.card_bot, mul_one] at this
  have hcard : Nat.card ↥T = Nat.card ↥((T ⊓ D₁) ⊔ (T ⊓ D₂)) := by
    rw [hT.card_eq, hcardT, h₁.card_eq, h₂.card_eq, hcard12, ← pow_add,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

theorem s311b_nonab_transfer {D₁ D₂ T₁ T₂ : Subgroup Q} (σ : Q ≃* Q)
    (hσ : D₁.map σ.toMonoidHom = D₂) (h₁ : IsSylowOf 2 T₁ D₁) (h₂ : IsSylowOf 2 T₂ D₂)
    (hn : ∃ x ∈ T₁, ∃ y ∈ T₁, x * y ≠ y * x) : ∃ x ∈ T₂, ∃ y ∈ T₂, x * y ≠ y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₁' : IsSylowOf 2 (T₁.map σ.toMonoidHom) D₂ := by
    have := s313b_isSylowOf_map h₁ σ.toMonoidHom
    rwa [hσ] at this
  obtain ⟨g, -, hg⟩ := Prelim.exists_conj_of_isSylowOf h₁' h₂
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  refine ⟨g * σ x * g⁻¹, ?_, g * σ y * g⁻¹, ?_, fun h => hxy ?_⟩
  · rw [hg]
    exact ⟨σ x, ⟨x, hx, rfl⟩, by simp [MulAut.conj_apply]⟩
  · rw [hg]
    exact ⟨σ y, ⟨y, hy, rfl⟩, by simp [MulAut.conj_apply]⟩
  · have h1 : σ x * σ y = σ y * σ x := by
      have h2 : g * σ x * g⁻¹ * (g * σ y * g⁻¹) = g * σ y * g⁻¹ * (g * σ x * g⁻¹) := h
      have h3 : g * (σ x * σ y) * g⁻¹ = g * (σ y * σ x) * g⁻¹ := by
        calc g * (σ x * σ y) * g⁻¹ = g * σ x * g⁻¹ * (g * σ y * g⁻¹) := by group
          _ = g * σ y * g⁻¹ * (g * σ x * g⁻¹) := h2
          _ = g * (σ y * σ x) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h3)
    apply σ.injective
    rw [map_mul, map_mul]
    exact h1

end S311bGeneric

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

def s311bImg (d : Data G h) (Z : Subgroup G) : Subgroup (s313bQ d) :=
  (Z.subgroupOf (s313bH d)).map (QuotientGroup.mk' (s313bO d))

theorem s311bmem_img_iff {Z : Subgroup G} (hZ : Z ≤ s313bH d) {x : s313bQ d} :
    x ∈ s311bImg d Z ↔ ∃ z ∈ Z, s313bTh d z = x := by
  constructor
  · rintro ⟨⟨z, hzH⟩, hz, rfl⟩
    exact ⟨z, hz, s313bTh_of_mem hzH⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hZ hz⟩, hz, (s313bTh_of_mem (hZ hz)).symm⟩


def S311bOdd (d : Data G h) (Y : Subgroup G) : Prop :=
  d.E ≤ Y ∧ Y ≤ d.L₂ ∧ d.L₂ ≤ normalizer (Y : Set G) ∧ Odd (d.E.relIndex Y)

def S311bTyp (d : Data G h) (g : G) : Prop :=
  ∃ N : Subgroup G, N ≤ d.L₂ ∧ d.L₂ ≤ normalizer (N : Set G) ∧
    (∀ Y, S311bOdd d Y → ¬ N ≤ Y) ∧ ∃ Y, S311bOdd d Y ∧ ∀ n ∈ N, n * g * n⁻¹ * g⁻¹ ∈ Y

theorem s311bOdd_map_conj {j : G} (hjE : j ∈ normalizer (d.E : Set G))
    (hjL : j ∈ normalizer (d.L₂ : Set G)) {Y : Subgroup G} (hY : S311bOdd d Y) :
    S311bOdd d (Y.map (MulAut.conj j).toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    have hE' : j⁻¹ * e * j ∈ d.E := by
      have := (mem_normalizer_iff.1 (inv_mem hjE) e).1 he
      simpa using this
    refine ⟨j⁻¹ * e * j, hY.1 hE', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hjL y).1 (hY.2.1 hy)
  · intro l hl
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    have hl' : j⁻¹ * l * j ∈ d.L₂ := by
      have := (mem_normalizer_iff.1 (inv_mem hjL) l).1 hl
      simpa using this
    have := (mem_normalizer_iff.1 (hY.2.2.1 hl') y).1 hy
    refine ⟨_, this, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [← map_conj_eq_of_mem_normalizer hjE,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj j).injective]
    exact hY.2.2.2

theorem s311bTyp_conj {j : G} (hjE : j ∈ normalizer (d.E : Set G))
    (hjL : j ∈ normalizer (d.L₂ : Set G)) {g : G} (hg : S311bTyp d g) :
    S311bTyp d (j * g * j⁻¹) := by
  obtain ⟨N, hNL, hNn, hNY, Y, hY, hcomm⟩ := hg
  have hjE' : j⁻¹ ∈ normalizer (d.E : Set G) := inv_mem hjE
  have hjL' : j⁻¹ ∈ normalizer (d.L₂ : Set G) := inv_mem hjL
  refine ⟨N.map (MulAut.conj j).toMonoidHom, ?_, ?_, ?_,
    Y.map (MulAut.conj j).toMonoidHom, s311bOdd_map_conj hjE hjL hY, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact (mem_normalizer_iff.1 hjL n).1 (hNL hn)
  · intro l hl
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨n, hn, rfl⟩ := hz
    have hl' : j⁻¹ * l * j ∈ d.L₂ := by
      have := (mem_normalizer_iff.1 hjL' l).1 hl
      simpa using this
    have := (mem_normalizer_iff.1 (hNn hl') n).1 hn
    refine ⟨_, this, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro Y' hY' hle
    have hY'' := s311bOdd_map_conj hjE' hjL' hY'
    refine hNY _ hY'' fun n hn => ?_
    have := hle ⟨n, hn, rfl⟩
    refine ⟨_, this, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro _ ⟨n, hn, rfl⟩
    refine ⟨_, hcomm n hn, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem s311bTyp_mul_left {w g : G} (hw : w ∈ d.E) (hg : S311bTyp d (w * g)) : S311bTyp d g := by
  obtain ⟨N, hNL, hNn, hNY, Y, hY, hcomm⟩ := hg
  refine ⟨N, hNL, hNn, hNY, Y, hY, fun n hn => ?_⟩
  have hnE : n ∈ normalizer (d.E : Set G) := d.L₂_le_normalizer_E (hNL hn)
  have hnw : n * w⁻¹ * n⁻¹ ∈ d.E := (mem_normalizer_iff.1 hnE w⁻¹).1 (inv_mem hw)
  have e : n * g * n⁻¹ * g⁻¹ = (n * w⁻¹ * n⁻¹) * (n * (w * g) * n⁻¹ * (w * g)⁻¹) * w := by group
  rw [e]
  exact mul_mem (mul_mem (hY.1 hnw) (hcomm n hn)) (hY.1 hw)


section S311b

variable (hp : d.ProductCaseHyp) (k : d.Know10) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k hS hP

theorem s311b_L₂_eq : d.L₂ = d.E ⊔ d.M₂ := k.s8.1

theorem s311b_M₂_le_L₂ : d.M₂ ≤ d.L₂ := (s311b_L₂_eq hp k hS hP) ▸ le_sup_right

theorem s311b_M₂_le_normalizer_E : d.M₂ ≤ normalizer (d.E : Set G) :=
  (s311b_M₂_le_L₂ hp k hS hP).trans d.L₂_le_normalizer_E

theorem s311b_E_le_S : d.E ≤ S := (k.s9_1 S hS hP).1.symm ▸ le_sup_left

theorem s311b_E_inf_M₂ : d.E ⊓ d.M₂ = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := k.s10_1 S hS hP
  have h2 := (k.s10_2 S hS hP).2.1.1
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : z ∈ d.E ⊓ (S ⊓ d.M₂) :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).1, Subgroup.mem_inf.2
      ⟨s311b_E_le_S hp k hS hP (Subgroup.mem_inf.1 hz).1, (Subgroup.mem_inf.1 hz).2⟩⟩
  rw [← h2, h11.2] at hz'
  exact hz'

end S311b

section S311bOddLemmas

variable (hp : d.ProductCaseHyp) (k : d.Know10) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k hS hP

theorem s311b_K_le_normalizer_E : s313bK d ≤ normalizer (d.E : Set G) :=
  (s313bK_le_M₂).trans (s311b_M₂_le_normalizer_E hp k hS hP)

theorem s311bOdd_Ohat : S311bOdd d (d.E ⊔ s313bK d) := by
  have hEL : d.E ≤ d.L₂ := d.E_le_L₂
  have hKL : s313bK d ≤ d.L₂ := s313bK_le_M₂.trans (s311b_M₂_le_L₂ hp k hS hP)
  refine ⟨le_sup_left, sup_le hEL hKL, ?_, ?_⟩
  · rw [s311b_L₂_eq hp k hS hP]
    refine sup_le (fun e he => Subgroup.le_normalizer (mem_sup_left he)) fun m hm => ?_
    exact Common.mem_normalizer_sup (s311b_M₂_le_normalizer_E hp k hS hP hm)
      (s313bM₂_le_normalizer_K hm)
  · have h1 := Subgroup.relIndex_mul_card d.E (d.E ⊔ s313bK d)
    rw [inf_eq_left.2 (le_sup_left : d.E ≤ d.E ⊔ s313bK d)] at h1
    have h2 := Common.card_sup_mul_card_inf_eq (s311b_K_le_normalizer_E hp k hS hP)
    have hbot : d.E ⊓ s313bK d = ⊥ := by
      refine eq_bot_iff.2 fun z hz => ?_
      have : z ∈ d.E ⊓ d.M₂ := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).1,
        s313bK_le_M₂ (Subgroup.mem_inf.1 hz).2⟩
      rwa [s311b_E_inf_M₂ hp k hS hP] at this
    rw [hbot, Subgroup.card_bot, mul_one] at h2
    have hE : 0 < Nat.card d.E := Nat.card_pos
    have h3 : d.E.relIndex (d.E ⊔ s313bK d) = Nat.card (s313bK d) := by
      refine Nat.eq_of_mul_eq_mul_right hE ?_
      rw [h1, h2, mul_comm]
    rw [h3]
    exact s313bK_odd

theorem s311b_inf_le_K {Y : Subgroup G} (hY : S311bOdd d Y) : Y ⊓ d.M₂ ≤ s313bK d := by
  obtain ⟨D₁, D₂, hs₁, hn₁, hs₂, hn₂, hc, hi, hsup⟩ := s313b_layer_product hp
  set Z : Subgroup G := Y ⊓ d.M₂ with hZ
  have hZM : Z ≤ d.M₂ := inf_le_right
  have hZH : Z ≤ s313bH d := hZM.trans (s313bM₂_le_H d)
  have hM₂Y : d.M₂ ≤ normalizer (Y : Set G) :=
    (s311b_M₂_le_L₂ hp k hS hP).trans hY.2.2.1
  have hZodd : Odd (Nat.card Z) := by
    have hZE : Z ≤ normalizer (d.E : Set G) := hZM.trans (s311b_M₂_le_normalizer_E hp k hS hP)
    have h2 := Common.card_sup_mul_card_inf_eq hZE
    have hbot : d.E ⊓ Z = ⊥ := by
      refine eq_bot_iff.2 fun z hz => ?_
      have : z ∈ d.E ⊓ d.M₂ := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).1,
        hZM (Subgroup.mem_inf.1 hz).2⟩
      rwa [s311b_E_inf_M₂ hp k hS hP] at this
    rw [hbot, Subgroup.card_bot, mul_one] at h2
    have hle : d.E ⊔ Z ≤ Y := sup_le hY.1 inf_le_left
    have h3 := Subgroup.card_dvd_of_le hle
    have h4 := Subgroup.relIndex_mul_card d.E Y
    rw [inf_eq_left.2 hY.1] at h4
    rw [h2, ← h4, mul_comm (d.E.relIndex Y)] at h3
    have h5 : Nat.card Z ∣ d.E.relIndex Y := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h3
    exact Odd.of_dvd_nat hY.2.2.2 h5
  set T := s311bImg d Z with hT
  have hTle : T ≤ D₁ ⊔ D₂ := by
    rw [hsup]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := (s311bmem_img_iff hZH).1 hx
    exact s313b_th_mem_layer hp (hZM hz)
  have hTn : D₁ ⊔ D₂ ≤ normalizer (T : Set (s313bQ d)) := by
    rw [hsup]
    intro x hx
    obtain ⟨m, hm, rfl⟩ := s313b_exists_th_eq hp hx
    refine mem_normalizer_fintype fun t ht => ?_
    obtain ⟨z, hz, rfl⟩ := (s311bmem_img_iff hZH).1 ht
    refine (s311bmem_img_iff hZH).2 ⟨m * z * m⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hM₂Y hm) z).1 (Subgroup.mem_inf.1 hz).1,
        mul_mem (mul_mem hm (hZM hz)) (inv_mem hm)⟩
    · exact s313bTh_conj (s313bM₂_le_H d hm) (hZH hz)
  have hTodd : Odd (Nat.card T) := by
    have h1 : Nat.card T ∣ Nat.card (Z.subgroupOf (s313bH d)) :=
      (Z.subgroupOf (s313bH d)).card_map_dvd (QuotientGroup.mk' (s313bO d))
    have h2 : Nat.card (Z.subgroupOf (s313bH d)) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
    rw [h2] at h1
    exact Odd.of_dvd_nat hZodd h1
  have hT1 : T = ⊥ := s313b_odd_normal_trivial hs₁ hn₁ hs₂ hn₂ hc hTle hTn hTodd
  intro z hz
  have hzM : z ∈ d.M₂ := hZM hz
  refine s313bmem_K_iff.2 ⟨hzM, ?_⟩
  have : s313bTh d z ∈ T := (s311bmem_img_iff hZH).2 ⟨z, hz, rfl⟩
  rw [hT1] at this
  exact this

theorem s311bTyp_of_normal {D' : Subgroup (s313bQ d)} (hD'le : D' ≤ CFSG.layer (s313bQ d))
    (hD'n : CFSG.layer (s313bQ d) ≤ normalizer (D' : Set (s313bQ d))) (hD'1 : D' ≠ ⊥)
    {x : G} (hx : x ∈ d.M₂) (hxc : ∀ u ∈ D', u * s313bTh d x = s313bTh d x * u) :
    S311bTyp d x := by
  have hPre_le : s313bPre d D' ≤ d.M₂ := s313bPre_le_M₂ D'
  have hPreE : s313bPre d D' ≤ normalizer (d.E : Set G) :=
    hPre_le.trans (s311b_M₂_le_normalizer_E hp k hS hP)
  have hM₂Pre : d.M₂ ≤ normalizer ((s313bPre d D' : Subgroup G) : Set G) := by
    intro m hm
    refine mem_normalizer_fintype fun p hp' => ?_
    obtain ⟨hpM, hpD⟩ := s313bmem_Pre_iff.1 hp'
    refine s313bmem_Pre_iff.2 ⟨mul_mem (mul_mem hm hpM) (inv_mem hm), ?_⟩
    rw [s313bTh_conj (s313bM₂_le_H d hm) (s313bM₂_le_H d hpM)]
    have hm' : s313bTh d m ∈ normalizer (D' : Set (s313bQ d)) :=
      hD'n (s313b_th_mem_layer hp hm)
    exact (mem_normalizer_iff.1 hm' _).1 hpD
  refine ⟨d.E ⊔ s313bPre d D', sup_le d.E_le_L₂ (hPre_le.trans (s311b_M₂_le_L₂ hp k hS hP)),
    ?_, ?_, d.E ⊔ s313bK d, s311bOdd_Ohat hp k hS hP, ?_⟩
  · rw [s311b_L₂_eq hp k hS hP]
    refine sup_le (fun e he => Subgroup.le_normalizer (mem_sup_left he)) fun m hm => ?_
    exact Common.mem_normalizer_sup (s311b_M₂_le_normalizer_E hp k hS hP hm) (hM₂Pre hm)
  · intro Y hY hle
    obtain ⟨u₀, hu₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD'1
    obtain ⟨m₀, hm₀, hm₀u⟩ := s313b_exists_th_eq hp (hD'le u₀.2)
    have hm₀N : m₀ ∈ d.E ⊔ s313bPre d D' :=
      mem_sup_right (s313bmem_Pre_iff.2 ⟨hm₀, hm₀u ▸ u₀.2⟩)
    have hK := s311b_inf_le_K hp k hS hP hY (Subgroup.mem_inf.2 ⟨hle hm₀N, hm₀⟩)
    have := (s313bmem_K_iff.1 hK).2
    rw [hm₀u] at this
    exact hu₀1 (Subtype.ext this)
  · intro n hn
    obtain ⟨e, he, m, hm, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hPreE hn
    obtain ⟨hmM, hmD⟩ := s313bmem_Pre_iff.1 hm
    have hxE : x ∈ normalizer (d.E : Set G) := s311b_M₂_le_normalizer_E hp k hS hP hx
    have hc : m * x * m⁻¹ * x⁻¹ ∈ s313bK d := by
      refine s313bmem_K_iff.2 ⟨mul_mem (mul_mem (mul_mem hmM hx) (inv_mem hmM)) (inv_mem hx), ?_⟩
      rw [s313bTh_comm (s313bM₂_le_H d hmM) (s313bM₂_le_H d hx)]
      have := hxc _ hmD
      rw [this]
      group
    have hf : x * e⁻¹ * x⁻¹ ∈ d.E := (mem_normalizer_iff.1 hxE e⁻¹).1 (inv_mem he)
    have e1 : e * m * x * (e * m)⁻¹ * x⁻¹ = e * (m * x * m⁻¹ * x⁻¹) * (x * e⁻¹ * x⁻¹) := by
      group
    rw [show e * m * x * (e * m)⁻¹ * x⁻¹ = e * (m * x * m⁻¹ * x⁻¹) * (x * e⁻¹ * x⁻¹) from e1]
    exact mul_mem (mul_mem (mem_sup_left he) (mem_sup_right hc)) (mem_sup_left hf)

theorem s311b_not_Typ {D₁ D₂ : Subgroup (s313bQ d)} (hs₁ : IsSimpleGroup D₁)
    (hn₁ : ∃ x y : D₁, x * y ≠ y * x) (hs₂ : IsSimpleGroup D₂)
    (hn₂ : ∃ x y : D₂, x * y ≠ y * x) (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x)
    (hsup : D₁ ⊔ D₂ = CFSG.layer (s313bQ d)) {y : G} (hy : y ∈ d.M₂)
    {a b : s313bQ d} (ha : a ∈ D₁) (hb : b ∈ D₂) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hyab : s313bTh d y = a * b) : ¬ S311bTyp d y := by
  rintro ⟨N, hNL, hNn, hNY, Y₀, hY₀, hcomm⟩
  have hM₂E := s311b_M₂_le_normalizer_E hp k hS hP
  have hNÔ : ¬ N ≤ d.E ⊔ s313bK d := hNY _ (s311bOdd_Ohat hp k hS hP)
  obtain ⟨n₀, hn₀N, hn₀Ô⟩ := SetLike.not_le_iff_exists.1 hNÔ
  have hn₀L : n₀ ∈ d.L₂ := hNL hn₀N
  rw [s311b_L₂_eq hp k hS hP] at hn₀L
  obtain ⟨e, he, m₀, hm₀, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hM₂E hn₀L
  have hNE : N ≤ normalizer (d.E : Set G) := hNL.trans d.L₂_le_normalizer_E
  have hENn : d.L₂ ≤ normalizer ((d.E ⊔ N : Subgroup G) : Set G) :=
    fun g hg => Common.mem_normalizer_sup (d.L₂_le_normalizer_E hg) (hNn hg)
  set NM : Subgroup G := (d.E ⊔ N) ⊓ d.M₂ with hNM
  have hNMM : NM ≤ d.M₂ := inf_le_right
  have hNMH : NM ≤ s313bH d := hNMM.trans (s313bM₂_le_H d)
  have hm₀NM : m₀ ∈ NM := Subgroup.mem_inf.2 ⟨by
    have := mul_mem (inv_mem (mem_sup_left he : e ∈ d.E ⊔ N)) (mem_sup_right hn₀N : e * m₀ ∈ d.E ⊔ N)
    simpa using this, hm₀⟩
  have hth1 : s313bTh d m₀ ≠ 1 := by
    intro h1
    exact hn₀Ô (mul_mem (mem_sup_left he) (mem_sup_right (s313bmem_K_iff.2 ⟨hm₀, h1⟩)))
  set T := s311bImg d NM with hT
  have hthT : s313bTh d m₀ ∈ T := (s311bmem_img_iff hNMH).2 ⟨m₀, hm₀NM, rfl⟩
  have hT1 : T ≠ ⊥ := by
    intro hb'
    rw [hb', Subgroup.mem_bot] at hthT
    exact hth1 hthT
  have hTle : T ≤ D₁ ⊔ D₂ := by
    rw [hsup]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := (s311bmem_img_iff hNMH).1 hx
    exact s313b_th_mem_layer hp (hNMM hz)
  have hTn : D₁ ⊔ D₂ ≤ normalizer (T : Set (s313bQ d)) := by
    rw [hsup]
    intro x hx
    obtain ⟨m, hm, rfl⟩ := s313b_exists_th_eq hp hx
    refine mem_normalizer_fintype fun t ht => ?_
    obtain ⟨z, hz, rfl⟩ := (s311bmem_img_iff hNMH).1 ht
    refine (s311bmem_img_iff hNMH).2 ⟨m * z * m⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hENn ((s311b_M₂_le_L₂ hp k hS hP) hm)) z).1
          (Subgroup.mem_inf.1 hz).1, mul_mem (mul_mem hm (hNMM hz)) (inv_mem hm)⟩
    · exact s313bTh_conj (s313bM₂_le_H d hm) (hNMH hz)
  have hcen : ∀ t ∈ T, t * (a * b) = (a * b) * t := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := (s311bmem_img_iff hNMH).1 ht
    obtain ⟨hzEN, hzM⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨e', he', n, hn, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hNE hzEN
    have hyE : y ∈ normalizer (d.E : Set G) := hM₂E hy
    have hf : y * e'⁻¹ * y⁻¹ ∈ d.E := (mem_normalizer_iff.1 hyE e'⁻¹).1 (inv_mem he')
    have e1 : e' * n * y * (e' * n)⁻¹ * y⁻¹ = e' * (n * y * n⁻¹ * y⁻¹) * (y * e'⁻¹ * y⁻¹) := by
      group
    have hY : e' * n * y * (e' * n)⁻¹ * y⁻¹ ∈ Y₀ := by
      rw [e1]
      exact mul_mem (mul_mem (hY₀.1 he') (hcomm n hn)) (hY₀.1 hf)
    have hYM : e' * n * y * (e' * n)⁻¹ * y⁻¹ ∈ d.M₂ :=
      mul_mem (mul_mem (mul_mem hzM hy) (inv_mem hzM)) (inv_mem hy)
    have hK := s311b_inf_le_K hp k hS hP hY₀ (Subgroup.mem_inf.2 ⟨hY, hYM⟩)
    have h1 := (s313bmem_K_iff.1 hK).2
    rw [s313bTh_comm (s313bM₂_le_H d hzM) (s313bM₂_le_H d hy), hyab] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  exact s313b_not_centralizes hs₁ hn₁ hs₂ hn₂ hc hTle hTn hT1 ha hb ha1 hb1 hcen

end S311bOddLemmas

section S311bFacts

variable (hp : d.ProductCaseHyp) (k : d.Know10) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k hS hP

theorem s311b_S_le_normalizer_E : S ≤ normalizer (d.E : Set G) :=
  hS.le.trans d.L₂_le_normalizer_E

theorem s311b_D_le_S : d.D ≤ S := (k.s9_1 S hS hP).1.symm ▸ le_sup_right

theorem s311b_R₂_le_D : S ⊓ d.M₂ ≤ d.D := by
  have h1 := (k.s9a S hS hP).cD₂
  have h2 := (k.s10_2 S hS hP).2.1.1
  intro x hx
  have hx' : x ∈ S ⊓ centralizer (d.I₂ : Set G) := by rw [h2]; exact hx
  rw [← h1] at hx'
  exact (Subgroup.mem_inf.1 hx').1

theorem s311b_F_central {f' y : G} (hf : f' ∈ d.F) (hy : y ∈ d.D) : f' * y = y * f' := by
  have h := (k.s9_2 S hS hP).2.2.2.1
  rw [← h] at hf
  exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hf).2 y hy).symm

theorem s311b_F_le_D : d.F ≤ d.D := by
  have h := (k.s9_2 S hS hP).2.2.2.1
  rw [← h]
  exact inf_le_left

theorem s311b_I₂_le_I₆ : d.I₂ ≤ d.I₆ := by
  refine d.pull_mono ?_
  intro t ht
  have h := mem_I₂sub.1 ht
  exact mem_I₆sub.2 ⟨h.1, h.2.1.trans h.2.2⟩

theorem s311b_C₆_le_R₂ : S ⊓ centralizer (d.I₆ : Set G) ≤ S ⊓ d.M₂ := by
  have h2 := (k.s10_2 S hS hP).2.1.1
  rw [← h2]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (fun x hx => s311b_I₂_le_I₆ hp k hS hP hx))

theorem s311b_F_inf_M₂_le : d.F ⊓ d.M₂ ≤ S ⊓ centralizer (d.I₆ : Set G) := by
  obtain ⟨-, -, ⟨hF6, -⟩, -⟩ := k.s10_1 S hS hP
  intro x hx
  obtain ⟨hxF, hxM⟩ := Subgroup.mem_inf.1 hx
  have hC6F : S ⊓ centralizer (d.I₆ : Set G) ≤ d.F := hF6 ▸ le_sup_right
  have hWF : d.W ≤ d.F := hF6 ▸ le_sup_left
  have hFD := s311b_F_le_D hp k hS hP
  have hC6N : S ⊓ centralizer (d.I₆ : Set G) ≤ normalizer (d.W : Set G) := by
    intro c hc
    refine mem_normalizer_fintype fun w hw => ?_
    have : c * w * c⁻¹ = w := by
      have := s311b_F_central hp k hS hP (hC6F hc) (hFD (hWF hw))
      calc c * w * c⁻¹ = w * c * c⁻¹ := by rw [this]
        _ = w := by group
    rw [this]; exact hw
  rw [hF6] at hxF
  obtain ⟨w, hw, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hC6N hxF
  have hcM : c ∈ d.M₂ := (s311b_C₆_le_R₂ hp k hS hP hc).2
  have hwM : w ∈ d.M₂ := by
    have : w = (w * c) * c⁻¹ := by group
    rw [this]
    exact mul_mem hxM (inv_mem hcM)
  have hwEM : w ∈ d.E ⊓ d.M₂ := Subgroup.mem_inf.2 ⟨d.W_le_E hw, hwM⟩
  rw [s311b_E_inf_M₂ hp k hS hP, Subgroup.mem_bot] at hwEM
  rw [hwEM, one_mul]
  exact hc

theorem s311b_card_F_inf_M₂_le : Nat.card (d.F ⊓ d.M₂ : Subgroup G) ≤ (2 ^ f) ^ 2 := by
  calc Nat.card (d.F ⊓ d.M₂ : Subgroup G)
      ≤ Nat.card (S ⊓ centralizer (d.I₆ : Set G) : Subgroup G) :=
        Subgroup.card_le_of_le (s311b_F_inf_M₂_le hp k hS hP)
    _ = (2 ^ f) ^ 2 := (k.s10_o S hS hP).c₆

theorem s311b_R₂_nonab : ∃ x ∈ S ⊓ d.M₂, ∃ y ∈ S ⊓ d.M₂, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hZ₀ : d.F ⊓ d.M₂ = CFSG.centerIn (S ⊓ d.M₂) := (k.s10_2 S hS hP).2.2.2.2.1
  have hle : (S ⊓ d.M₂) ≤ d.F ⊓ d.M₂ := by
    intro x hx
    rw [hZ₀]
    exact ⟨hx, mem_centralizer_iff.2 fun y hy => hcon y hy x hx⟩
  have h1 := Subgroup.card_le_of_le hle
  have h2 : Nat.card (S ⊓ d.M₂ : Subgroup G) = (2 ^ f) ^ 6 := by
    rw [← (k.s10_2 S hS hP).2.1.1]
    exact (k.s10_o S hS hP).c₂
  have h3 := s311b_card_F_inf_M₂_le hp k hS hP
  have hf2 : 2 ≤ f := hp.hyp.setting.two_le
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have h4 : (2 ^ f) ^ 2 < (2 ^ f) ^ 6 := Nat.pow_lt_pow_right hq (by norm_num)
  omega

theorem s311b_central_of_mem_EF {m e f' : G} (hm : m ∈ S ⊓ d.M₂) (he : e ∈ d.E) (hf : f' ∈ d.F)
    (hmef : m = e * f') : ∀ c ∈ S ⊓ d.M₂, c * m = m * c := by
  intro c hc
  have hcD : c ∈ d.D := s311b_R₂_le_D hp k hS hP hc
  have hcf : f' * c = c * f' := s311b_F_central hp k hS hP hf hcD
  have hcN : c ∈ normalizer (d.E : Set G) :=
    s311b_S_le_normalizer_E hp k hS hP (Subgroup.mem_inf.1 hc).1
  have hcf' : c⁻¹ * f' = f' * c⁻¹ := by
    calc c⁻¹ * f' = c⁻¹ * (f' * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * f') * c⁻¹ := by rw [hcf]
      _ = f' * c⁻¹ := by group
  have e1 : c * m * c⁻¹ * m⁻¹ = (c * e * c⁻¹) * e⁻¹ := by
    rw [hmef]
    calc c * (e * f') * c⁻¹ * (e * f')⁻¹ = c * e * (f' * c⁻¹) * f'⁻¹ * e⁻¹ := by group
      _ = c * e * (c⁻¹ * f') * f'⁻¹ * e⁻¹ := by rw [← hcf']
      _ = (c * e * c⁻¹) * e⁻¹ := by group
  have h1 : c * m * c⁻¹ * m⁻¹ ∈ d.E := by
    rw [e1]
    exact mul_mem ((mem_normalizer_iff.1 hcN e).1 he) (inv_mem he)
  have h2 : c * m * c⁻¹ * m⁻¹ ∈ d.M₂ :=
    mul_mem (mul_mem (mul_mem hc.2 hm.2) (inv_mem hc.2)) (inv_mem hm.2)
  have h3 : c * m * c⁻¹ * m⁻¹ ∈ d.E ⊓ d.M₂ := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [s311b_E_inf_M₂ hp k hS hP, Subgroup.mem_bot] at h3
  calc c * m = c * m * c⁻¹ * m⁻¹ * m * c := by group
    _ = m * c := by rw [h3]; group

end S311bFacts

section S311bLayer

variable (hp : d.ProductCaseHyp)
include hp

theorem s311b_layer_swap :
    ∃ D₁ D₂ : Subgroup (s313bQ d), IsSimpleGroup D₁ ∧ (∃ x y : D₁, x * y ≠ y * x) ∧
      IsSimpleGroup D₂ ∧ (∃ x y : D₂, x * y ≠ y * x) ∧
      (∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x) ∧ D₁ ⊓ D₂ = ⊥ ∧
      D₁ ⊔ D₂ = CFSG.layer (s313bQ d) ∧
      ∃ g : s313bQ d, D₁.map (MulAut.conj g).toMonoidHom = D₂ := by
  obtain ⟨⟨-, -, -, hncl, -, halt, -⟩, -⟩ := (hp.hyp.sec3_3_two hp.gms).1
  rcases halt with ⟨hA, -⟩ | ⟨⟨D₁, D₂, -, -, -, hs₁, hn₁, hs₂, hn₂, hsup, hinf, hcomm, hmap, -⟩, -⟩
  · exfalso
    have h1 := hA.1
    rw [hncl] at h1
    exact hp.caseB h1
  · refine ⟨D₁, D₂, hs₁, hn₁, hs₂, hn₂, fun x hx y hy => ?_, hinf, hsup.trans hncl, ?_⟩
    · have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hx
      exact (mem_centralizer_iff.1 this y hy).symm
    · exact ⟨_, hmap⟩

theorem s311b_img_sylow (k : d.Know10) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
    (hP : d.P ≤ S) : IsSylowOf 2 (s311bImg d (S ⊓ d.M₂)) (CFSG.layer (s313bQ d)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRsyl : IsSylowOf 2 (S ⊓ d.M₂) d.M₂ := (k.s10_2 S hS hP).2.1.2
  have hRH : S ⊓ d.M₂ ≤ s313bH d := hRsyl.le.trans (s313bM₂_le_H d)
  have h1 : IsSylowOf 2 ((S ⊓ d.M₂).subgroupOf (s313bH d)) (d.M₂.subgroupOf (s313bH d)) := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (s313bH d)).1 ?_
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hRH, inf_eq_left.2 (s313bM₂_le_H d)]
    exact hRsyl
  have h2 := s313b_isSylowOf_map h1 (QuotientGroup.mk' (s313bO d))
  rw [s313b_map_M₂ hp] at h2
  exact h2

end S311bLayer

section S311bKey

variable (hp : d.ProductCaseHyp) (k : d.Know10) {S : Subgroup G} (hS : IsSylowOf 2 S d.L₂)
  (hP : d.P ≤ S)
include hp k hS hP

theorem s311b_key :
    ∃ D₁ D₂ : Subgroup (s313bQ d), IsSimpleGroup D₁ ∧ (∃ u v : D₁, u * v ≠ v * u) ∧
      IsSimpleGroup D₂ ∧ (∃ u v : D₂, u * v ≠ v * u) ∧ (∀ u ∈ D₁, ∀ v ∈ D₂, u * v = v * u) ∧
      D₁ ⊓ D₂ = ⊥ ∧ D₁ ⊔ D₂ = CFSG.layer (s313bQ d) ∧
      ∃ x y : G, x ∈ S ⊓ d.M₂ ∧ y ∈ S ⊓ d.M₂ ∧ (∃ x' ∈ S ⊓ d.M₂, x * x' ≠ x' * x) ∧
        (∃ y' ∈ S ⊓ d.M₂, y * y' ≠ y' * y) ∧ s313bTh d x ∈ D₁ ∧
        ∀ m' ∈ S ⊓ d.M₂, (∀ c ∈ S ⊓ d.M₂, c * m' = m' * c) →
          ∃ a' b', a' ∈ D₁ ∧ b' ∈ D₂ ∧ a' ≠ 1 ∧ b' ≠ 1 ∧ s313bTh d (m' * y) = a' * b' := by
  obtain ⟨D₁, D₂, hs₁, hn₁, hs₂, hn₂, hc, hi, hsup, g, hg⟩ := s311b_layer_swap hp
  refine ⟨D₁, D₂, hs₁, hn₁, hs₂, hn₂, hc, hi, hsup, ?_⟩
  have hRsyl : IsSylowOf 2 (S ⊓ d.M₂) d.M₂ := (k.s10_2 S hS hP).2.1.2
  have hRM : S ⊓ d.M₂ ≤ d.M₂ := hRsyl.le
  have hRH : S ⊓ d.M₂ ≤ s313bH d := hRM.trans (s313bM₂_le_H d)
  have hRK : (S ⊓ d.M₂) ⊓ s313bK d = ⊥ := s313b_inf_bot_of_odd hRsyl.isPGroup s313bK_odd
  have hTsyl : IsSylowOf 2 (s311bImg d (S ⊓ d.M₂)) (D₁ ⊔ D₂) := by
    rw [hsup]; exact s311b_img_sylow hp k hS hP
  obtain ⟨hT₁, hT₂, hTeq⟩ := s311b_sylow_split hc hi hTsyl
  have hθnc : ∀ r r' : G, r ∈ S ⊓ d.M₂ → r' ∈ S ⊓ d.M₂ → r * r' ≠ r' * r →
      s313bTh d r * s313bTh d r' ≠ s313bTh d r' * s313bTh d r := by
    intro r r' hr hr' hne h
    apply hne
    have hc1 : r * r' * r⁻¹ * r'⁻¹ ∈ (S ⊓ d.M₂) ⊓ s313bK d := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (mul_mem hr hr') (inv_mem hr)) (inv_mem hr'),
        s313bmem_K_iff.2 ⟨mul_mem (mul_mem (mul_mem (hRM hr) (hRM hr')) (inv_mem (hRM hr)))
          (inv_mem (hRM hr')), ?_⟩⟩
      rw [s313bTh_comm (hRH hr) (hRH hr'), h]
      group
    rw [hRK, Subgroup.mem_bot] at hc1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hc1)
  have hθc : ∀ r r' : G, r ∈ S ⊓ d.M₂ → r' ∈ S ⊓ d.M₂ → r * r' = r' * r →
      s313bTh d r * s313bTh d r' = s313bTh d r' * s313bTh d r := by
    intro r r' hr hr' h
    rw [← s313bTh_mul (hRH hr) (hRH hr'), ← s313bTh_mul (hRH hr') (hRH hr), h]
  have hcT : ∀ u ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₁, ∀ v ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₂, u * v = v * u :=
    fun u hu v hv => hc u (Subgroup.mem_inf.1 hu).2 v (Subgroup.mem_inf.1 hv).2
  have hfac : ∀ t ∈ s311bImg d (S ⊓ d.M₂), ∃ t₁ ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₁,
      ∃ t₂ ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₂, t = t₁ * t₂ := by
    intro t ht
    have ht' : t ∈ ((s311bImg d (S ⊓ d.M₂) ⊓ D₁) ⊔ (s311bImg d (S ⊓ d.M₂) ⊓ D₂) :
        Subgroup (s313bQ d)) := hTeq ▸ ht
    rw [← SetLike.mem_coe, (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcT).2] at ht'
    obtain ⟨t₁, h₁, t₂, h₂, hh⟩ := ht'
    exact ⟨t₁, h₁, t₂, h₂, hh.symm⟩
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := s311b_R₂_nonab hp k hS hP
  have hone : (∃ u ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₁, ∃ v ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₁, u * v ≠ v * u) ∨
      (∃ u ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₂, ∃ v ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₂, u * v ≠ v * u) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hab1, hab2⟩ := hcon
    have hxT : s313bTh d x₀ ∈ s311bImg d (S ⊓ d.M₂) := (s311bmem_img_iff hRH).2 ⟨x₀, hx₀, rfl⟩
    have hyT : s313bTh d y₀ ∈ s311bImg d (S ⊓ d.M₂) := (s311bmem_img_iff hRH).2 ⟨y₀, hy₀, rfl⟩
    obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := hfac _ hxT
    obtain ⟨v₁, hv₁, v₂, hv₂, hv⟩ := hfac _ hyT
    apply hθnc x₀ y₀ hx₀ hy₀ hxy₀
    rw [hu, hv]
    have e1 : u₁ * v₁ = v₁ * u₁ := hab1 u₁ hu₁ v₁ hv₁
    have e2 : u₂ * v₂ = v₂ * u₂ := hab2 u₂ hu₂ v₂ hv₂
    have e3 : u₂ * v₁ = v₁ * u₂ := (hcT v₁ hv₁ u₂ hu₂).symm
    have e4 : v₂ * u₁ = u₁ * v₂ := hcT u₁ hu₁ v₂ hv₂ |>.symm
    calc u₁ * u₂ * (v₁ * v₂) = u₁ * (u₂ * v₁) * v₂ := by group
      _ = u₁ * (v₁ * u₂) * v₂ := by rw [e3]
      _ = (u₁ * v₁) * (u₂ * v₂) := by group
      _ = (v₁ * u₁) * (v₂ * u₂) := by rw [e1, e2]
      _ = v₁ * (u₁ * v₂) * u₂ := by group
      _ = v₁ * (v₂ * u₁) * u₂ := by rw [e4]
      _ = v₁ * v₂ * (u₁ * u₂) := by group
  have hg' : D₂.map (MulAut.conj g).symm.toMonoidHom = D₁ := by
    rw [← hg, Subgroup.map_map]
    have : ((MulAut.conj g).symm.toMonoidHom).comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id _ := by
      ext x; simp
    rw [this, Subgroup.map_id]
  have hboth : (∃ u ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₁, ∃ v ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₁, u * v ≠ v * u) ∧
      (∃ u ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₂, ∃ v ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₂, u * v ≠ v * u) := by
    rcases hone with h1 | h2
    · exact ⟨h1, s311b_nonab_transfer (MulAut.conj g) hg hT₁ hT₂ h1⟩
    · exact ⟨s311b_nonab_transfer (MulAut.conj g).symm hg' hT₂ hT₁ h2, h2⟩
  obtain ⟨⟨a, ha, a', ha', haa'⟩, ⟨b, hb, b', hb', hbb'⟩⟩ := hboth
  have hlift : ∀ t ∈ s311bImg d (S ⊓ d.M₂), ∃ r ∈ S ⊓ d.M₂, s313bTh d r = t := fun t ht =>
    (s311bmem_img_iff hRH).1 ht
  obtain ⟨x, hx, hxa⟩ := hlift a (Subgroup.mem_inf.1 ha).1
  obtain ⟨x', hx', hxa'⟩ := hlift a' (Subgroup.mem_inf.1 ha').1
  obtain ⟨y, hy, hyab⟩ := hlift (a * b) (mul_mem (Subgroup.mem_inf.1 ha).1 (Subgroup.mem_inf.1 hb).1)
  have haD : a ∈ D₁ := (Subgroup.mem_inf.1 ha).2
  have ha'D : a' ∈ D₁ := (Subgroup.mem_inf.1 ha').2
  have hbD : b ∈ D₂ := (Subgroup.mem_inf.1 hb).2
  have hb'D : b' ∈ D₂ := (Subgroup.mem_inf.1 hb').2
  refine ⟨x, y, hx, hy, ⟨x', hx', fun h => haa' ?_⟩, ⟨x', hx', fun h => ?_⟩, hxa ▸ haD, ?_⟩
  · have := hθc x x' hx hx' h
    rwa [hxa, hxa'] at this
  · have := hθc y x' hy hx' h
    rw [hyab, hxa'] at this
    apply haa'
    have hba' : a' * b = b * a' := hc a' ha'D b hbD
    have h5 : (a * a') * b = (a' * a) * b := by
      calc (a * a') * b = a * (a' * b) := by group
        _ = a * (b * a') := by rw [hba']
        _ = a * b * a' := by group
        _ = a' * (a * b) := this
        _ = (a' * a) * b := by group
    exact mul_right_cancel h5
  · intro m' hm' hcen
    have hm'H : m' ∈ s313bH d := hRH hm'
    have hzT : s313bTh d m' ∈ s311bImg d (S ⊓ d.M₂) := (s311bmem_img_iff hRH).2 ⟨m', hm', rfl⟩
    obtain ⟨z₁, hz₁, z₂, hz₂, hz⟩ := hfac _ hzT
    have hzc : ∀ t ∈ s311bImg d (S ⊓ d.M₂), t * s313bTh d m' = s313bTh d m' * t := by
      intro t ht
      obtain ⟨r, hr, rfl⟩ := (s311bmem_img_iff hRH).1 ht
      rw [← s313bTh_mul (hRH hr) hm'H, ← s313bTh_mul hm'H (hRH hr), hcen r hr]
    have hz₁c : ∀ u ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₁, u * z₁ = z₁ * u := by
      intro u hu
      have h1 := hzc u (Subgroup.mem_inf.1 hu).1
      rw [hz] at h1
      have h2 : z₂ * u = u * z₂ := (hcT u hu z₂ hz₂).symm
      have h3 : (u * z₁) * z₂ = (z₁ * u) * z₂ := by
        calc (u * z₁) * z₂ = u * (z₁ * z₂) := by group
          _ = (z₁ * z₂) * u := h1
          _ = z₁ * (z₂ * u) := by group
          _ = z₁ * (u * z₂) := by rw [h2]
          _ = (z₁ * u) * z₂ := by group
      exact mul_right_cancel h3
    have hz₂c : ∀ u ∈ s311bImg d (S ⊓ d.M₂) ⊓ D₂, u * z₂ = z₂ * u := by
      intro u hu
      have h1 := hzc u (Subgroup.mem_inf.1 hu).1
      rw [hz] at h1
      have h2 : u * z₁ = z₁ * u := (hcT z₁ hz₁ u hu).symm
      have h3 : z₁ * (u * z₂) = z₁ * (z₂ * u) := by
        calc z₁ * (u * z₂) = (z₁ * u) * z₂ := by group
          _ = (u * z₁) * z₂ := by rw [h2]
          _ = u * (z₁ * z₂) := by group
          _ = (z₁ * z₂) * u := h1
          _ = z₁ * (z₂ * u) := by group
      exact mul_left_cancel h3
    have hz₁D : z₁ ∈ D₁ := (Subgroup.mem_inf.1 hz₁).2
    have hz₂D : z₂ ∈ D₂ := (Subgroup.mem_inf.1 hz₂).2
    refine ⟨z₁ * a, z₂ * b, mul_mem hz₁D haD, mul_mem hz₂D hbD, ?_, ?_, ?_⟩
    · intro h1
      apply haa'
      have ha_inv : a = z₁⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hc1 := hz₁c a' ha'
      rw [ha_inv]
      calc z₁⁻¹ * a' = z₁⁻¹ * (a' * z₁) * z₁⁻¹ := by group
        _ = z₁⁻¹ * (z₁ * a') * z₁⁻¹ := by rw [hc1]
        _ = a' * z₁⁻¹ := by group
    · intro h1
      apply hbb'
      have hb_inv : b = z₂⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hc1 := hz₂c b' hb'
      rw [hb_inv]
      calc z₂⁻¹ * b' = z₂⁻¹ * (b' * z₂) * z₂⁻¹ := by group
        _ = z₂⁻¹ * (z₂ * b') * z₂⁻¹ := by rw [hc1]
        _ = b' * z₂⁻¹ := by group
    · rw [s313bTh_mul hm'H (hRH hy), hz, hyab]
      have e : z₂ * a = a * z₂ := (hcT a ha z₂ hz₂).symm
      calc z₁ * z₂ * (a * b) = z₁ * (z₂ * a) * b := by group
        _ = z₁ * (a * z₂) * b := by rw [e]
        _ = (z₁ * a) * (z₂ * b) := by group

end S311bKey

theorem sec311NotTrans_of_hyp (hp : d.ProductCaseHyp) (k : d.Know10) : d.Sec311NotTrans := by
  intro S hS hP J _ hJle htr
  obtain ⟨D₁, D₂, hs₁, hn₁, hs₂, hn₂, hc, hi, hsup, x, y, hx, hy, ⟨x', hx', hxx'⟩,
    ⟨y', hy', hyy'⟩, hthx, hycen⟩ := s311b_key hp k hS hP
  have hJE : ∀ j ∈ J, j ∈ normalizer (d.E : Set G) := fun j hj =>
    ((hJle.trans inf_le_left).trans inf_le_right) hj
  have hJL : ∀ j ∈ J, j ∈ normalizer (d.L₂ : Set G) := fun j hj =>
    d.normalizer_E_le_normalizer_L₂ (hJE j hj)
  have hxD : x ∈ d.D := s311b_R₂_le_D hp k hS hP hx
  have hyD : y ∈ d.D := s311b_R₂_le_D hp k hS hP hy
  have hFN : d.F ≤ normalizer ((d.E ⊓ d.D : Subgroup G) : Set G) := by
    intro g hg
    have hgD : g ∈ d.D := s311b_F_le_D hp k hS hP hg
    have hgE : g ∈ normalizer (d.E : Set G) :=
      s311b_S_le_normalizer_E hp k hS hP (s311b_D_le_S hp k hS hP hgD)
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨hzE, hzD⟩ := Subgroup.mem_inf.1 hz
    exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hgE z).1 hzE, d.D.mul_mem (d.D.mul_mem hgD hzD)
      (d.D.inv_mem hgD)⟩
  have hQcen : ∀ z ∈ S ⊓ d.M₂, z ∈ (d.E ⊓ d.D) ⊔ d.F → ∀ c ∈ S ⊓ d.M₂, c * z = z * c := by
    intro z hz hzQ
    obtain ⟨e, he, f', hf', hzef⟩ := exists_mul_of_mem_sup_of_le_normalizer hFN hzQ
    exact s311b_central_of_mem_EF hp k hS hP hz (Subgroup.mem_inf.1 he).1 hf' hzef
  have hxQ : x ∉ (d.E ⊓ d.D) ⊔ d.F := fun hxQ =>
    hxx' ((hQcen x hx hxQ x' hx').symm)
  have hyQ : y ∉ (d.E ⊓ d.D) ⊔ d.F := fun hyQ =>
    hyy' ((hQcen y hy hyQ y' hy').symm)
  obtain ⟨j, hj, hjxy⟩ := htr x hxD hxQ y hyD hyQ
  have hD₂le : D₂ ≤ CFSG.layer (s313bQ d) := hsup ▸ le_sup_right
  have hD₂n : CFSG.layer (s313bQ d) ≤ normalizer (D₂ : Set (s313bQ d)) := by
    rw [← hsup]
    refine sup_le (fun g hg => Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun u hu => (hc g hg u hu).symm)) Subgroup.le_normalizer
  have hTx : S311bTyp d x :=
    s311bTyp_of_normal hp k hS hP hD₂le hD₂n (s313b_ne_bot_of_nonab hn₂) hx.2
      (fun u hu => (hc _ hthx u hu).symm)
  have hTj := s311bTyp_conj (hJE j hj) (hJL j hj) hTx
  obtain ⟨e₀, he₀, f₀, hf₀, hu⟩ := exists_mul_of_mem_sup_of_le_normalizer hFN hjxy
  have hjx : j * x * j⁻¹ = e₀ * (f₀ * y) := by
    calc j * x * j⁻¹ = ((j * x * j⁻¹) * y⁻¹) * y := by group
      _ = e₀ * f₀ * y := by rw [hu]
      _ = e₀ * (f₀ * y) := by group
  rw [hjx] at hTj
  have hTf := s311bTyp_mul_left (Subgroup.mem_inf.1 he₀).1 hTj
  have hf₀S : f₀ ∈ S := s311b_D_le_S hp k hS hP (s311b_F_le_D hp k hS hP hf₀)
  have hf₀L : f₀ ∈ d.E ⊔ d.M₂ := (s311b_L₂_eq hp k hS hP) ▸ hS.le hf₀S
  obtain ⟨e₁, he₁, m₁, hm₁, hfm⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer (s311b_M₂_le_normalizer_E hp k hS hP) hf₀L
  have hTm : S311bTyp d (m₁ * y) := by
    refine s311bTyp_mul_left he₁ ?_
    rw [← mul_assoc, ← hfm]
    exact hTf
  have hm₁S : m₁ ∈ S := by
    have : m₁ = e₁⁻¹ * f₀ := by rw [hfm]; group
    rw [this]
    exact mul_mem (inv_mem (s311b_E_le_S hp k hS hP he₁)) hf₀S
  have hm₁R : m₁ ∈ S ⊓ d.M₂ := Subgroup.mem_inf.2 ⟨hm₁S, hm₁⟩
  have hm₁cen : ∀ c ∈ S ⊓ d.M₂, c * m₁ = m₁ * c :=
    s311b_central_of_mem_EF hp k hS hP hm₁R (inv_mem he₁) hf₀ (by rw [hfm]; group)
  obtain ⟨a', b', ha', hb', ha1, hb1, hθ⟩ := hycen m₁ hm₁R hm₁cen
  exact s311b_not_Typ hp k hS hP hs₁ hn₁ hs₂ hn₂ hc hsup (mul_mem hm₁ hy.2) ha' hb' ha1 hb1 hθ hTm

end Data

namespace CaseBParts

theorem sec311NotTrans : Sec311NotTransStatement :=
  fun _ _ _ _ _ _ _ _ hp k => Data.sec311NotTrans_of_hyp hp k

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
