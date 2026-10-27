module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.InducedAux
import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Basic
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaModel

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaHeart

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

@[expose] def Coatom {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2) : Prop :=
  ∀ t : GL ι (ZMod 2), IsTransvection t →
    (∀ x, Q (Matrix.mulVec (t : Matrix ι ι (ZMod 2)) x) = Q x) →
    t ∈ Subgroup.normalizer (StatedOmega Q : Set (GL ι (ZMod 2))) →
    ∀ H : Subgroup (GL ι (ZMod 2)), H ≤ StatedOmega Q →
      (∀ g ∈ StatedOmega Q, t * g * t⁻¹ = g → g ∈ H) → (∃ g ∈ H, t * g * t⁻¹ ≠ g) →
        H = StatedOmega Q

theorem comm_mem_kerAct (h : Setup28 W K S) {a : X} (hS2 : ∀ s ∈ S, s ∈ kerAct W K S ∨ a⁻¹ * s ∈ kerAct W K S)
    {k : X} (hk : k ∈ K) (hka : a * k * a⁻¹ * k⁻¹ ∈ W) : ∀ s ∈ S, ⁅k, s⁆ ∈ kerAct W K S := by
  intro s hs
  have hW1 : ∀ x ∈ W, x ∈ kerAct W K S := fun x hx => s0_w_le_kerAct h hx
  have hWc : ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ W := fun w hw => by
    have h1 : ⁅k, w⁆ = ⁅w, k⁆⁻¹ := (commutatorElement_inv w k).symm
    rw [h1]
    exact W.inv_mem (hw.2 k hk)
  rcases hS2 s hs with hsW | hsa
  · exact hW1 _ (hWc s hsW)
  · set w := a⁻¹ * s with hw
    have hs' : s = a * w := by rw [hw]; group
    have h1 : ⁅k, a * w⁆ = ⁅k, a⁆ * (a * ⁅k, w⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    have hka' : ⁅k, a⁆ ∈ W := by
      have : ⁅k, a⁆ = ⁅a, k⁆⁻¹ := (commutatorElement_inv a k).symm
      rw [this]
      exact W.inv_mem hka
    rw [hs', h1]
    exact hW1 _ (W.mul_mem hka' (Subgroup.Normal.conj_mem inferInstance _ (hWc w hsa) a))

theorem centMax_of_model {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (hcoat : Coatom Q) (h : Setup28 W K S) (hR : Red28 W K S) {V U₁ U₂ : Subgroup X}
    (sf : SingleFactor K V U₁ U₂) (hZ : Subgroup.center ↥(bar W K) = ⊥) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (hS2 : ∀ s ∈ S, s ∈ kerAct W K S ∨ a⁻¹ * s ∈ kerAct W K S)
    (hΩ : OmegaModelWith Q W K a U₁ U₂) : CentMax W K S a := by
  obtain ⟨θ, t, hθs, hθW, htr, hQt, htn, hθa⟩ := OmegaModel.model_equiv Q hR sf hZ hΩ
  intro H hHK hP hex
  have hak : ∀ k : ↥K, a * (k : X) * a⁻¹ ∈ K := fun k =>
    (Subgroup.mem_normalizer_iff.mp (h.hN haS) k).1 k.2
  have hkey : ∀ k : ↥K, t * ((θ k : ↥(StatedOmega Q)) : GL ι (ZMod 2)) * t⁻¹ =
      ((θ k : ↥(StatedOmega Q)) : GL ι (ZMod 2)) → a * (k : X) * a⁻¹ * (k : X)⁻¹ ∈ W := by
    intro k hk
    have h1 := hθa k ⟨a * k * a⁻¹, hak k⟩ rfl
    rw [hk] at h1
    have h2 : θ ⟨a * k * a⁻¹, hak k⟩ = θ k := Subtype.ext h1
    have h3 : θ (⟨a * k * a⁻¹, hak k⟩ * k⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
    exact (hθW _).mp h3
  set HK : Subgroup ↥K := H.subgroupOf K with hHK'
  set H' : Subgroup (GL ι (ZMod 2)) := (HK.map θ).map (StatedOmega Q).subtype with hH'
  have hmem' : ∀ g, g ∈ H' ↔ ∃ k : ↥K, (k : X) ∈ H ∧ ((θ k : ↥(StatedOmega Q)) : GL ι (ZMod 2)) = g := by
    intro g
    simp only [hH', hHK', Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨θ k, ⟨k, hk, rfl⟩, rfl⟩
  have hH'Ω : H' ≤ StatedOmega Q := by
    rintro g hg
    obtain ⟨k, -, rfl⟩ := (hmem' g).1 hg
    exact (θ k).2
  have hHC : ∀ g ∈ StatedOmega Q, t * g * t⁻¹ = g → g ∈ H' := by
    intro g hg hgt
    obtain ⟨k, hk⟩ := hθs ⟨g, hg⟩
    have hk' : ((θ k : ↥(StatedOmega Q)) : GL ι (ZMod 2)) = g := by rw [hk]
    refine (hmem' g).2 ⟨k, ?_, hk'⟩
    refine hP _ k.2 (comm_mem_kerAct h hS2 k.2 (hkey k (by rw [hk', hgt])))
  have hne : ∃ g ∈ H', t * g * t⁻¹ ≠ g := by
    obtain ⟨k₀, hk₀H, hk₀⟩ := hex
    have hk₀K : k₀ ∈ K := hHK hk₀H
    refine ⟨((θ ⟨k₀, hk₀K⟩ : ↥(StatedOmega Q)) : GL ι (ZMod 2)),
      (hmem' _).2 ⟨⟨k₀, hk₀K⟩, hk₀H, rfl⟩, fun hgt => hk₀ ?_⟩
    have := hkey ⟨k₀, hk₀K⟩ hgt
    have h1 : ⁅k₀, a⁆ = ⁅a, k₀⁆⁻¹ := (commutatorElement_inv a k₀).symm
    rw [h1]
    exact s0_w_le_kerAct h (W.inv_mem this)
  have hEq := hcoat t htr hQt htn H' hH'Ω hHC hne
  intro k hk
  have hmem : ((θ ⟨k, hk⟩ : ↥(StatedOmega Q)) : GL ι (ZMod 2)) ∈ H' := by
    rw [hEq]; exact (θ ⟨k, hk⟩).2
  obtain ⟨h₁, hh₁H, hh₁⟩ := (hmem' _).1 hmem
  have hθeq : θ h₁ = θ ⟨k, hk⟩ := Subtype.ext hh₁
  have h2 : θ (h₁⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hθeq, inv_mul_cancel]
  have hW' : (h₁ : X)⁻¹ * k ∈ W := (hθW _).mp h2
  have hPW : (h₁ : X)⁻¹ * k ∈ H := by
    refine hP _ (K.mul_mem (K.inv_mem h₁.2) hk) fun s hs => ?_
    have h3 : ⁅(h₁ : X)⁻¹ * k, s⁆ ∈ W := by
      have h4 : ⁅(h₁ : X)⁻¹ * k, s⁆ = ((h₁ : X)⁻¹ * k) * (s * ((h₁ : X)⁻¹ * k)⁻¹ * s⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h4]
      exact W.mul_mem hW' (Subgroup.Normal.conj_mem inferInstance _ (W.inv_mem hW') s)
    exact s0_w_le_kerAct h h3
  have := H.mul_mem hh₁H hPW
  rwa [mul_inv_cancel_left] at this

@[expose] def Three {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2) : Prop :=
  ∀ t : GL ι (ZMod 2), IsTransvection t →
    (∀ x, Q (Matrix.mulVec (t : Matrix ι ι (ZMod 2)) x) = Q x) →
    ∃ g ∈ StatedOmega Q, g ≠ 1 ∧ g ^ 3 = 1 ∧ t * g * t⁻¹ = g⁻¹

theorem threeElt_of_model {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (hthree : Three Q) (h : Setup28 W K S) (hR : Red28 W K S) {V U₁ U₂ : Subgroup X}
    (sf : SingleFactor K V U₁ U₂) (hZ : Subgroup.center ↥(bar W K) = ⊥) {a : X} (haS : a ∈ S)
    (hΩ : OmegaModelWith Q W K a U₁ U₂) : ThreeElt W K S a := by
  obtain ⟨θ, t, hθs, hθW, htr, hQt, htn, hθa⟩ := OmegaModel.model_equiv Q hR sf hZ hΩ
  obtain ⟨g, hgΩ, hg1, hg3, hgt⟩ := hthree t htr hQt
  have hak : ∀ k : ↥K, a * (k : X) * a⁻¹ ∈ K := fun k =>
    (Subgroup.mem_normalizer_iff.mp (h.hN haS) k).1 k.2
  obtain ⟨k₁, hk₁⟩ := hθs ⟨g, hgΩ⟩
  have hθk₁ : ((θ k₁ : ↥(StatedOmega Q)) : GL ι (ZMod 2)) = g := by rw [hk₁]
  have hk13 : θ (k₁ ^ 3) = 1 := Subtype.ext (by rw [map_pow, Subgroup.coe_pow, hθk₁, hg3]; rfl)
  have hk13W : ((k₁ ^ 3 : ↥K) : X) ∈ W := (hθW _).mp hk13
  obtain ⟨j, hj⟩ := h.hW ⟨(k₁ : X) ^ 3, by simpa using hk13W⟩
  have hj' : ((k₁ : X) ^ 3) ^ (2 ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  set pK : ↥K := k₁ ^ (4 ^ j) with hpK
  have hpX : ((pK : ↥K) : X) = (k₁ : X) ^ (4 ^ j) := by rw [hpK, Subgroup.coe_pow]
  have hp3 : ((pK : ↥K) : X) ^ 3 = 1 := by
    rw [hpX, ← pow_mul, mul_comm, pow_mul, show 4 ^ j = 2 ^ j * 2 ^ j by
      rw [← mul_pow]; norm_num, pow_mul, hj', one_pow]
  have hpow : g ^ (4 ^ j) = g := by
    rw [pow_eq_pow_mod _ hg3]
    have : 4 ^ j % 3 = 1 := by rw [Nat.pow_mod]; simp
    rw [this, pow_one]
  have hθp : ((θ pK : ↥(StatedOmega Q)) : GL ι (ZMod 2)) = g := by
    rw [hpK, map_pow, Subgroup.coe_pow, hθk₁, hpow]
  have hW_of : ∀ y : ↥K, θ y = 1 ↔ (y : X) ∈ W := hθW
  have hnotW : ((pK : ↥K) : X) ∉ W := fun hpW => hg1 (by
    have := (hW_of pK).mpr hpW
    rw [← hθp, this]; rfl)
  refine ⟨(pK : X), pK.2, hp3, fun hp1 => hnotW ?_, ?_, ?_, ?_⟩
  · have : (pK : X) ∈ K ⊓ kerAct W K S := ⟨pK.2, hp1⟩
    rw [hR.k_w1] at this
    exact this.2
  ·
    have hq : ((⟨a * (pK : X) * a⁻¹, hak pK⟩ * pK : ↥K) : X) = a * (pK : X) * a⁻¹ * (pK : X) := rfl
    have h1 := hθa pK ⟨a * (pK : X) * a⁻¹, hak pK⟩ rfl
    have h2 : θ (⟨a * (pK : X) * a⁻¹, hak pK⟩ * pK : ↥K) = 1 := by
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, h1, hθp, hgt]
      simp
    rw [← hq]
    exact s0_w_le_kerAct h ((hW_of _).mp h2)
  ·
    intro hca
    set rK : ↥K := pK * ⟨a * ((pK⁻¹ : ↥K) : X) * a⁻¹, hak pK⁻¹⟩ with hrK
    have hr : ((rK : ↥K) : X) = ⁅(pK : X), a⁆ := by
      rw [hrK]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    have hrW1 : ((rK : ↥K) : X) ∈ K ⊓ kerAct W K S := ⟨rK.2, hr ▸ hca⟩
    rw [hR.k_w1] at hrW1
    have h1 := hθa pK⁻¹ ⟨a * ((pK⁻¹ : ↥K) : X) * a⁻¹, hak pK⁻¹⟩ rfl
    have h2 : ((θ rK : ↥(StatedOmega Q)) : GL ι (ZMod 2)) = g * g := by
      rw [hrK, map_mul, Subgroup.coe_mul, h1, map_inv, Subgroup.coe_inv, hθp]
      have : t * g⁻¹ * t⁻¹ = (t * g * t⁻¹)⁻¹ := by group
      rw [this, hgt, inv_inv]
    have h3 : θ rK = 1 := (hW_of rK).mpr hrW1.2
    rw [h3] at h2
    have h4 : g * g = 1 := by rw [← h2]; rfl
    apply hg1
    calc g = g ^ 3 * (g * g)⁻¹ := by group
      _ = 1 := by rw [hg3, h4]; simp
  ·
    intro hpz
    have : toBar W K pK ∈ Subgroup.center ↥(bar W K) := (InducedAux.zPre_iff pK).mp hpz
    rw [hZ, Subgroup.mem_bot] at this
    exact hnotW (InducedAux.toBar_eq_one_iff.mp this)

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaHeart
