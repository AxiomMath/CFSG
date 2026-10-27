module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173

variable {Ω : Type} [Group Ω] {S B : Subgroup Ω} {Γ : Type} [Group Γ] {G₀ Ghat : Subgroup Γ}

namespace S172DModel

variable (M : S172DModel S B G₀ Ghat)

private lemma piImg_eq_map (X : Subgroup Ω) :
    M.piImg X = (X.subgroupOf S).map (G₀.subtype.comp M.π) := by
  rw [S172DModel.piImg, Subgroup.map_map]

theorem piImg_le_normalizer_piImg_closureIn [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) :
    M.piImg N ≤ Subgroup.normalizer (M.piImg (closureIn K N) : Set Γ) := by
  have hKS : K ≤ S := (hcfg.std.2.2.2.2.2.1.1).trans inf_le_left
  haveI : S.Normal := hcfg.normal
  have hNS : N ≤ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hXle : closureIn K N ≤ S :=
    CFSG.LocalAnalysis.GLTheoremA.S12.closureIn_le_of_le_normalizer hKS hNS
  have hNnorm : N ≤ Subgroup.normalizer (closureIn K N : Set Ω) := le_normalizer_closureIn K N
  let f : ↥S →* Γ := G₀.subtype.comp M.π
  have hsub : N.subgroupOf S ≤
      Subgroup.normalizer ((closureIn K N).subgroupOf S : Set ↥S) := by
    intro n hn
    rw [Subgroup.mem_subgroupOf] at hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (hNnorm hn) (y : Ω)).mp hy
      simpa using h1
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have hn' : ((n : ↥S) : Ω)⁻¹ ∈ N := N.inv_mem hn
      have hz : ((n : ↥S) : Ω) * (y : Ω) * ((n : ↥S) : Ω)⁻¹ ∈ closureIn K N := by
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hy
      have h1 := (Subgroup.mem_normalizer_iff.mp (hNnorm hn')
        (((n : ↥S) : Ω) * (y : Ω) * ((n : ↥S) : Ω)⁻¹)).mp hz
      have e : ((n : ↥S) : Ω)⁻¹ * (((n : ↥S) : Ω) * (y : Ω) * ((n : ↥S) : Ω)⁻¹) *
          (((n : ↥S) : Ω)⁻¹)⁻¹ = (y : Ω) := by group
      rwa [e] at h1
  calc M.piImg N = (N.subgroupOf S).map f := by rw [piImg_eq_map M]
    _ ≤ (Subgroup.normalizer ((closureIn K N).subgroupOf S)).map f := Subgroup.map_mono hsub
    _ ≤ Subgroup.normalizer (((closureIn K N).subgroupOf S).map f) :=
        Subgroup.le_normalizer_map f
    _ = Subgroup.normalizer (M.piImg (closureIn K N)) := by rw [piImg_eq_map M]

private lemma piImg_ne_bot_of_commutator_ne_bot (M : S172DModel S B G₀ Ghat)
    {T N K : Subgroup Ω} (hTS : T ≤ S) (hXle : closureIn K N ≤ S)
    (hne : ⁅closureIn K N, T⁆ ≠ ⊥) : M.piImg T ≠ ⊥ := by
  intro hbot
  have hTZ : ∀ t : Ω, ∀ ht : t ∈ T, (⟨t, hTS ht⟩ : ↥S) ∈ Subgroup.center ↥S := by
    intro t ht
    have h1 : ((M.π ⟨t, hTS ht⟩ : ↥G₀) : Γ) ∈ M.piImg T :=
      (mem_piImg M).2 ⟨⟨t, hTS ht⟩, ht, rfl⟩
    rw [hbot] at h1
    have h2 : M.π ⟨t, hTS ht⟩ = 1 := Subtype.ext (Subgroup.mem_bot.1 h1)
    have h3 : (⟨t, hTS ht⟩ : ↥S) ∈ M.π.ker := h2
    rw [M.ker_π] at h3
    exact h3
  have hcomm : ⁅closureIn K N, T⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha t ht
    have haS : a ∈ S := hXle ha
    have h1 : a * t = t * a :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 (hTZ t ht) ⟨a, haS⟩)
    rw [commutatorElement_def, h1]
    simp
  exact hne hcomm

private lemma conj_mem_piImg (M : S172DModel S B G₀ Ghat) {T X : Subgroup Ω}
    (hTS : T ≤ S) (hTnorm : X ⊔ B ≤ Subgroup.normalizer (T : Set Ω))
    (b : ↥B) {r : Γ} (hr : r ∈ M.piImg T) :
    ((M.β b : ↥Ghat) : Γ) * r * ((M.β b : ↥Ghat) : Γ)⁻¹ ∈ M.piImg T := by
  obtain ⟨t, htT, htEq⟩ := (mem_piImg M).1 hr
  have hb : (b : Ω) ∈ Subgroup.normalizer (T : Set Ω) := hTnorm (Subgroup.mem_sup_right b.2)
  have hbt : (b : Ω) * (t : Ω) * (b : Ω)⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp hb (t : Ω)).mp htT
  have hS : (b : Ω) * (t : Ω) * (b : Ω)⁻¹ ∈ S := hTS hbt
  have hc := M.conj b⁻¹ t ⟨(b : Ω) * (t : Ω) * (b : Ω)⁻¹, hS⟩ (by simp)
  refine (mem_piImg M).2 ⟨⟨_, hS⟩, hbt, ?_⟩
  rw [← htEq]
  simpa using hc

private lemma barB_le_normalizer_piImg (M : S172DModel S B G₀ Ghat) {T X : Subgroup Ω}
    (hTS : T ≤ S) (hTnorm : X ⊔ B ≤ Subgroup.normalizer (T : Set Ω)) :
    M.barB ≤ Subgroup.normalizer (M.piImg T : Set Γ) := by
  intro y hy
  obtain ⟨b, rfl⟩ := (mem_barB M).1 hy
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact conj_mem_piImg M hTS hTnorm b hr
  · intro hr
    have h1 := conj_mem_piImg M hTS hTnorm b⁻¹ hr
    have e : ((M.β b⁻¹ : ↥Ghat) : Γ) = ((M.β b : ↥Ghat) : Γ)⁻¹ := by
      rw [map_inv]
      rfl
    rw [e] at h1
    have e2 : ((M.β b : ↥Ghat) : Γ)⁻¹ *
        (((M.β b : ↥Ghat) : Γ) * r * ((M.β b : ↥Ghat) : Γ)⁻¹) *
          (((M.β b : ↥Ghat) : Γ)⁻¹)⁻¹ = r := by group
    rwa [e2] at h1

private lemma piImg_le_normalizer_piImg (M : S172DModel S B G₀ Ghat) {T X : Subgroup Ω}
    (hTS : T ≤ S) (hXle : X ≤ S) (hTnorm : X ⊔ B ≤ Subgroup.normalizer (T : Set Ω)) :
    M.piImg X ≤ Subgroup.normalizer (M.piImg T : Set Γ) := by
  have hconj : ∀ a : ↥S, (a : Ω) ∈ X → ∀ r ∈ M.piImg T,
      ((M.π a : ↥G₀) : Γ) * r * ((M.π a : ↥G₀) : Γ)⁻¹ ∈ M.piImg T := by
    intro a ha r hr
    obtain ⟨t, htT, htEq⟩ := (mem_piImg M).1 hr
    have haS : (a : Ω) ∈ S := hXle ha
    have haN : (a : Ω) ∈ Subgroup.normalizer (T : Set Ω) :=
      hTnorm (Subgroup.mem_sup_left ha)
    have hat : (a : Ω) * (t : Ω) * (a : Ω)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp haN (t : Ω)).mp htT
    have haS' : (a : Ω) * (t : Ω) * (a : Ω)⁻¹ ∈ S := hTS hat
    have hc : ((M.π ⟨(a : Ω) * (t : Ω) * (a : Ω)⁻¹, haS'⟩ : ↥G₀) : Γ) =
        ((M.π a : ↥G₀) : Γ) * ((M.π t : ↥G₀) : Γ) * ((M.π a : ↥G₀) : Γ)⁻¹ := by
      have e : (⟨(a : Ω) * (t : Ω) * (a : Ω)⁻¹, haS'⟩ : ↥S) = a * t * a⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e, map_mul, map_mul, map_inv]
      rfl
    refine (mem_piImg M).2 ⟨⟨_, haS'⟩, hat, ?_⟩
    rw [← htEq]
    exact hc
  intro z hz
  obtain ⟨a, haX, rfl⟩ := (mem_piImg M).1 hz
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact hconj a haX r hr
  · intro hr
    have h1 := hconj a⁻¹ (X.inv_mem haX)
      (((M.π a : ↥G₀) : Γ) * r * ((M.π a : ↥G₀) : Γ)⁻¹) hr
    have e : ((M.π a⁻¹ : ↥G₀) : Γ) = ((M.π a : ↥G₀) : Γ)⁻¹ := by
      rw [map_inv]
      rfl
    rw [e] at h1
    have e2 : ((M.π a : ↥G₀) : Γ)⁻¹ *
        (((M.π a : ↥G₀) : Γ) * r * ((M.π a : ↥G₀) : Γ)⁻¹) *
          (((M.π a : ↥G₀) : Γ)⁻¹)⁻¹ = r := by group
    rwa [e2] at h1

theorem exists_twoGroup_normalized_by_piImg_sup_barB [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) :
    ∃ R : Subgroup Γ, R ≠ ⊥ ∧ IsPGroup 2 R ∧ R ≤ G₀ ∧
      M.piImg (closureIn K N) ⊔ M.barB ≤ Subgroup.normalizer (R : Set Γ) := by
  obtain ⟨T, hTS, hT2, hTnorm, hTne⟩ := hcfg.hc
  have hKS : K ≤ S := (hcfg.std.2.2.2.2.2.1.1).trans inf_le_left
  haveI : S.Normal := hcfg.normal
  have hNS : N ≤ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hXle : closureIn K N ≤ S :=
    CFSG.LocalAnalysis.GLTheoremA.S12.closureIn_le_of_le_normalizer hKS hNS
  have hR2 : IsPGroup 2 (M.piImg T) := by
    intro r
    obtain ⟨t, htT, htEq⟩ := (mem_piImg M).1 r.2
    obtain ⟨k, hk⟩ := hT2 ⟨t, htT⟩
    refine ⟨k, ?_⟩
    have hr : r = ⟨((M.π t : ↥G₀) : Γ), by rw [htEq]; exact r.2⟩ :=
      Subtype.ext htEq.symm
    rw [hr]
    apply Subtype.ext
    have hk' : (t : ↥S) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    calc ((M.π t : ↥G₀) : Γ) ^ 2 ^ k = ((M.π t ^ 2 ^ k : ↥G₀) : Γ) := by
          rw [Subgroup.coe_pow]
      _ = ((M.π (t ^ 2 ^ k) : ↥G₀) : Γ) := by rw [map_pow]
      _ = 1 := by rw [hk']; simp
  have hRle : M.piImg T ≤ G₀ := Subgroup.map_subtype_le _
  exact ⟨M.piImg T, piImg_ne_bot_of_commutator_ne_bot M hTS hXle hTne, hR2, hRle,
    sup_le (piImg_le_normalizer_piImg M hTS hXle hTnorm)
      (barB_le_normalizer_piImg M hTS hTnorm)⟩

end S172DModel

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
