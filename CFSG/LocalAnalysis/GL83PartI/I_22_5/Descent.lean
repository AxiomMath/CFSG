module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Norm

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G]

theorem cj_eq_of_orbit {p : ℕ} {K K' : Subgroup G} {b : G} {i j : ZMod p}
    (h : cj (b ^ i.val) K = cj (b ^ j.val) K') : K' = cj (b ^ ((i.val : ℤ) - j.val)) K := by
  have h1 := congrArg (cj (b ^ j.val)⁻¹) h
  rw [cj_inv_cj, ← cj_mul, inv_pow_mul_pow_eq_zpow] at h1
  exact h1.symm

variable {p : ℕ} [Fact p.Prime] {B : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem cj_zpow_normSub {K : Subgroup G} {b : G} (hc : NormComm p K b) (hb : b ^ p = 1) (n : ℤ) :
    cj (b ^ n) (normSub hc) = normSub hc := by
  refine cj_eq_of_comm fun z hz => ?_
  exact ((Commute.zpow_left (show Commute b z from mem_normSub_comm hc hb hz) n)).eq

theorem IsFam.isFam_normFam (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦) {b : G}
    (hb : b ∈ B) (hbA : b ∉ stab B K₀) {B' : Subgroup G} (hB'B : B' ≤ B)
    (hsup : B ≤ B' ⊔ Subgroup.zpowers b) : IsFam p B' (normFam hF b hb) := by
  refine ⟨elem_mono hF.elem hB'B, ⟨_, normSub_mem_normFam hF hK₀ hb hbA⟩, ?_, ?_, ?_, ?_⟩
  · rintro M ⟨K, hK, hbA', rfl⟩
    exact isQuasisimple_normSub _ (hF.quasi K hK)
  · rintro M ⟨K, hK, hbA₁, rfl⟩ M' ⟨K', hK', hbA₂, rfl⟩ hne
    refine hF.normSub_comm hK hK' hb hbA₁ hbA₂ ?_
    intro i j hij
    have hK'eq := cj_eq_of_orbit hij
    subst hK'eq
    exact hne (hF.normSub_zpow hK hb hbA₁ _ hbA₂).symm
  · rintro M ⟨K, hK, hbA₁, rfl⟩ c hc
    have hcB : c ∈ B := hB'B hc
    have hbA' := hF.not_mem_stab hK (hF.smul_mem K hK c hcB) hbA₁
    exact ⟨cj c K, hF.smul_mem K hK c hcB, hbA', (hF.normSub_conj hK hb hcB hbA₁ hbA').symm⟩
  · rintro M ⟨K, hK, hbA₁, rfl⟩ M' ⟨K', hK', hbA₂, rfl⟩
    obtain ⟨c, hcB, hcK⟩ := hF.trans K hK K' hK'
    have hcomm : ∀ h ∈ B', ∀ k ∈ Subgroup.zpowers b, h * k = k * h :=
      zpowers_commute fun h hh => hF.mul_comm_of_mem (hB'B hh) hb
    obtain ⟨c', hc', y, hy, hcy⟩ := (mem_sup_of_commute hcomm).1 (hsup hcB)
    refine ⟨c', hc', ?_⟩
    subst hcK
    rw [hF.normSub_conj hK hb hcB hbA₁ hbA₂, ← hcy, cj_mul]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [cj_zpow_normSub _ (hF.elem.2 b hb)]

theorem IsFam.stab_normSub_le (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦) {b : G}
    (hb : b ∈ B) (hbA : b ∉ stab B K₀) {B' : Subgroup G} (hAB' : stab B K₀ ≤ B')
    (hB'B : B' ≤ B) (hbB' : b ∉ B') :
    stab B' (normSub (hF.normComm hK₀ hb hbA)) ≤ stab B K₀ := by
  intro c hc
  rw [stab, Subgroup.mem_inf] at hc
  obtain ⟨hcB', hcN⟩ := hc
  have hcB : c ∈ B := hB'B hcB'
  have hcN' : cj c (normSub (hF.normComm hK₀ hb hbA)) = normSub (hF.normComm hK₀ hb hbA) :=
    cj_eq_iff_mem_normalizer.2 hcN
  have hcK₀ : cj c K₀ ∈ 𝒦 := hF.smul_mem K₀ hK₀ c hcB
  have hbA₂ : b ∉ stab B (cj c K₀) := hF.not_mem_stab hK₀ hcK₀ hbA
  have horb : ∃ i j : ZMod p, cj (b ^ i.val) K₀ = cj (b ^ j.val) (cj c K₀) := by
    by_contra hne
    have hne' : ∀ i j : ZMod p, cj (b ^ i.val) K₀ ≠ cj (b ^ j.val) (cj c K₀) :=
      fun i j h => hne ⟨i, j, h⟩
    have hcomm := hF.normSub_comm hK₀ hcK₀ hb hbA hbA₂ hne'
    rw [hF.normSub_conj hK₀ hb hcB hbA hbA₂, hcN'] at hcomm
    obtain ⟨x, y, hxy⟩ := quasisimple_nonabelian
      (isQuasisimple_normSub (hF.normComm hK₀ hb hbA) (hF.quasi K₀ hK₀))
    exact hxy (Subtype.ext (hcomm x x.2 y y.2))
  obtain ⟨i, j, hij⟩ := horb
  have hord : orderOf b = p := hF.orderOf_eq hb hbA
  have h1 : cj ((b ^ i.val)⁻¹ * b ^ j.val * c) K₀ = K₀ := by
    have := congrArg (cj (b ^ i.val)⁻¹) hij
    rw [cj_inv_cj, ← cj_mul, ← cj_mul] at this
    exact this.symm
  have hbi : b ^ i.val ∈ B := B.pow_mem hb _
  have hbj : b ^ j.val ∈ B := B.pow_mem hb _
  have ha : (b ^ i.val)⁻¹ * b ^ j.val * c ∈ stab B K₀ :=
    mem_stab.2 ⟨B.mul_mem (B.mul_mem (B.inv_mem hbi) hbj) hcB, h1⟩
  have hc_eq : c = b ^ ((i.val : ℤ) - j.val) * ((b ^ i.val)⁻¹ * b ^ j.val * c) := by
    rw [← inv_pow_mul_pow_eq_zpow]
    group
  have hbn : b ^ ((i.val : ℤ) - j.val) ∈ B' := by
    have : b ^ ((i.val : ℤ) - j.val) = c * ((b ^ i.val)⁻¹ * b ^ j.val * c)⁻¹ := by
      rw [← inv_pow_mul_pow_eq_zpow]
      group
    rw [this]
    exact B'.mul_mem hcB' (B'.inv_mem (hAB' ha))
  have hdvd := (zpow_mem_iff_dvd hord hbB' _).1 hbn
  have hdvd' : (orderOf b : ℤ) ∣ (i.val : ℤ) - j.val := by
    rw [hord]
    exact hdvd
  have hb1 : b ^ ((i.val : ℤ) - j.val) = 1 := orderOf_dvd_iff_zpow_eq_one.1 hdvd'
  rw [hb1, one_mul] at hc_eq
  rw [hc_eq]
  exact ha

theorem IsFam.cen_le_cen_normSub (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦) {b : G}
    (hb : b ∈ B) (hbA : b ∉ stab B K₀) {B' : Subgroup G} (hAB' : stab B K₀ ≤ B') :
    cen B K₀ ≤ cen B' (normSub (hF.normComm hK₀ hb hbA)) := by
  intro c hc
  have hcB' : c ∈ B' := hAB' (cen_le_stab B K₀ hc)
  obtain ⟨hcB, hcK⟩ := mem_cen.1 hc
  refine mem_cen.2 ⟨hcB', fun z hz => ?_⟩
  exact commute_normSub (hF.normComm hK₀ hb hbA) (hF.mul_comm_of_mem hcB hb) hcK hz

theorem IsFam.layer_normFam_le (hF : IsFam p B 𝒦) {b : G} (hb : b ∈ B) :
    layer (normFam hF b hb) ≤ layer 𝒦 ⊓ Subgroup.centralizer ({b} : Set G) := by
  refine iSup₂_le fun M hM => ?_
  obtain ⟨K, hK, hbA, rfl⟩ := hM
  refine le_inf (normSub_le_layer hF hK hb _) fun z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.1 hw]
  exact mem_normSub_comm _ (hF.elem.2 b hb) hz

theorem IsFam.cj_mem_normFam (hF : IsFam p B 𝒦) {b : G} (hb : b ∈ B) {c : G} (hc : c ∈ B)
    {M : Subgroup G} (hM : M ∈ normFam hF b hb) : cj c M ∈ normFam hF b hb := by
  obtain ⟨K, hK, hbA₁, rfl⟩ := hM
  have hbA' := hF.not_mem_stab hK (hF.smul_mem K hK c hc) hbA₁
  exact ⟨cj c K, hF.smul_mem K hK c hc, hbA', (hF.normSub_conj hK hb hc hbA₁ hbA').symm⟩

@[expose] def normAll (hF : IsFam p B 𝒦) (K₀ : Subgroup G) : Set (Subgroup G) :=
  {M | ∃ b, ∃ hb : b ∈ B, ∃ _ : b ∉ stab B K₀, M ∈ normFam hF b hb}

@[expose] def normJoin (hF : IsFam p B 𝒦) (K₀ : Subgroup G) : Subgroup G :=
  ⨆ M ∈ normAll hF K₀, M

theorem le_normJoin (hF : IsFam p B 𝒦) {K₀ M : Subgroup G} (hM : M ∈ normAll hF K₀) :
    M ≤ normJoin hF K₀ :=
  le_iSup₂ (f := fun M (_ : M ∈ normAll hF K₀) => M) M hM

theorem layer_normFam_le_normJoin (hF : IsFam p B 𝒦) {K₀ : Subgroup G} {b : G} (hb : b ∈ B)
    (hbA : b ∉ stab B K₀) : layer (normFam hF b hb) ≤ normJoin hF K₀ :=
  iSup₂_le fun _ hM => le_normJoin hF ⟨b, hb, hbA, hM⟩

theorem IsFam.cj_normJoin_le (hF : IsFam p B 𝒦) (K₀ : Subgroup G) {c : G} (hc : c ∈ B) :
    cj c (normJoin hF K₀) ≤ normJoin hF K₀ := by
  rw [normJoin, cj_iSup]
  refine iSup_le fun M => ?_
  rw [cj_iSup]
  refine iSup_le fun hM => ?_
  obtain ⟨b, hb, hbA, hMb⟩ := hM
  exact le_normJoin hF ⟨b, hb, hbA, hF.cj_mem_normFam hb hc hMb⟩

theorem IsFam.layer_le_normJoin (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦)
    (h : K₀ ≤ normJoin hF K₀) : layer 𝒦 ≤ normJoin hF K₀ := by
  refine iSup₂_le fun K hK => ?_
  obtain ⟨c, hc, rfl⟩ := hF.trans K₀ hK₀ K hK
  exact (cj_mono c h).trans (hF.cj_normJoin_le K₀ hc)

end GL83.CompFam
