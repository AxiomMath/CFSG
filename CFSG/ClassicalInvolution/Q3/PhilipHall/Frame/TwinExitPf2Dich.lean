module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecQuot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Descent

variable {A : Type} [Group A] [Finite A] {X H : Subgroup A}

theorem eq_of_eqX (hHX : H ≤ X) (x y : ↥H)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨(x : A), hHX x.2⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨(y : A), hHX y.2⟩) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥H) x =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H) y := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h ⊢
  have h1 : ((x : A)⁻¹ * (y : A)) ∈ oddCoreOf X := by
    obtain ⟨n, hn, e⟩ := (⟨_, h, rfl⟩ : _ ∈ (classicalInvolutionOddCore ↥X).map X.subtype)
    exact ⟨n, hn, by simpa using e⟩
  exact mem_oddCore_of_mem_oddCoreOf hHX (y := x⁻¹ * y) (by simpa using h1)

theorem comm_of_commX (hHX : H ≤ X) (x y : ↥H)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨(x : A), hHX x.2⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨(y : A), hHX y.2⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨(y : A), hHX y.2⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨(x : A), hHX x.2⟩) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥H) x *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) y =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H) y *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) x := by
  have h1 := eq_of_eqX hHX (x * y) (y * x) (by
    have e1 : (⟨((x * y : ↥H) : A), hHX (x * y).2⟩ : ↥X) =
        ⟨(x : A), hHX x.2⟩ * ⟨(y : A), hHX y.2⟩ := rfl
    have e2 : (⟨((y * x : ↥H) : A), hHX (y * x).2⟩ : ↥X) =
        ⟨(y : A), hHX y.2⟩ * ⟨(x : A), hHX x.2⟩ := rfl
    rw [e1, e2, map_mul, map_mul]
    exact h)
  simpa only [map_mul] using h1

end Descent

section Main

variable {A : Type} [Group A] [Finite A] {Λ : Set (Subgroup A)} {X H : Subgroup A}

@[expose] noncomputable def imgOf (X L : Subgroup A) :
    Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X) :=
  (L.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))

theorem imgOf_conj (X : Subgroup A) {L : Subgroup A} (x : ↥X) :
    conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) x) (imgOf X L) =
      imgOf X (conjSub (x : A) L) := by
  unfold imgOf
  rw [← AscQuot.map_conjSub, conjSub_subgroupOf]

theorem mem_imgOf_iff {L : Subgroup A} {y : ↥X ⧸ classicalInvolutionOddCore ↥X} :
    y ∈ imgOf X L ↔ ∃ a : ↥X, (a : A) ∈ L ∧ QuotientGroup.mk' (classicalInvolutionOddCore ↥X) a = y := by
  unfold imgOf
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem false_of_imgOf_eq (hΛ : HypOmegaGen Λ) {K₁ K₂ : Subgroup A} (hK₁ : K₁ ∈ Λ) (hK₂ : K₂ ∈ Λ)
    (hne : K₁ ≠ K₂) {t : A} (ht₁ : IsUniqueInvolution K₁ t) (ht₂ : IsUniqueInvolution K₂ t)
    (hK₁X : K₁ ≤ X) (hK₂X : K₂ ≤ X) (hM : imgOf X K₁ = imgOf X K₂) : False := by
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΔ : HypOmegaGen (quotFamily (restrictFamily Λ X) (classicalInvolutionOddCore ↥X)) :=
    TwinEdge.hypOmegaGen_quotFamily_odd (hypOmegaGen_restrict hΛ X) hN
  have hmem : ∀ {L : Subgroup A}, L ∈ Λ → L ≤ X →
      imgOf X L ∈ quotFamily (restrictFamily Λ X) (classicalInvolutionOddCore ↥X) :=
    fun hL hLX => ⟨_, subgroupOf_mem_restrictFamily hL hLX, rfl⟩
  have hΛX := hypOmegaGen_restrict hΛ X
  have hK₁X' := subgroupOf_mem_restrictFamily hK₁ hK₁X
  have hK₂X' := subgroupOf_mem_restrictFamily hK₂ hK₂X
  have hne' : K₁.subgroupOf X ≠ K₂.subgroupOf X := subgroupOf_ne_of_ne hK₂X hK₁X hne
  have hcomm := Sec6Gen.comm_le_oddCore_of_twin hΛX hK₁X' hK₂X' hne'
    (isUniqueInvolution_subgroupOf ht₁ hK₁X) (isUniqueInvolution_subgroupOf ht₂ hK₂X)
  have hM1 := hmem hK₁ hK₁X
  obtain ⟨R₀, hR₀, hR₀s, -⟩ := exists_mem_RSet_ge hM1 (isPGroup_two_bot (G := ↥X ⧸ classicalInvolutionOddCore ↥X)) bot_le
  obtain ⟨x, hx, y, hy, hxy⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΔ hR₀).exists_not_commute
  have hxM : x ∈ imgOf X K₁ := hR₀s.1 hx
  have hyM : y ∈ imgOf X K₂ := hM ▸ hR₀s.1 hy
  obtain ⟨a₂, ha₂, rfl⟩ := mem_imgOf_iff.mp hxM
  obtain ⟨b₂, hb₂, rfl⟩ := mem_imgOf_iff.mp hyM
  have hcm : ⁅a₂, b₂⁆ ∈ oddCoreOf (K₁.subgroupOf X) :=
    (hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr ha₂)
      (Subgroup.mem_subgroupOf.mpr hb₂))).1
  have hodd1 : Odd (Nat.card ↥(classicalInvolutionOddCore ↥X ⊓ K₁.subgroupOf X)) :=
    odd_natCard_inf hN _
  have hcm' : ⁅QuotientGroup.mk' (classicalInvolutionOddCore ↥X) a₂,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) b₂⁆ ∈ oddCoreOf (imgOf X K₁) := by
    have : oddCoreOf (imgOf X K₁) =
        (oddCoreOf (K₁.subgroupOf X)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) :=
      oddCoreOf_map_mk_of_odd hodd1
    rw [this, ← map_commutatorElement]
    exact Subgroup.mem_map_of_mem _ hcm
  have hmemR : ⁅QuotientGroup.mk' (classicalInvolutionOddCore ↥X) a₂,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) b₂⁆ ∈ R₀ := by
    rw [commutatorElement_def]
    exact R₀.mul_mem (R₀.mul_mem (R₀.mul_mem hx hy) (R₀.inv_mem hx)) (R₀.inv_mem hy)
  have h3 : IsPGroup 2 (Subgroup.zpowers ⁅QuotientGroup.mk' (classicalInvolutionOddCore ↥X) a₂,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) b₂⁆) :=
    hR₀s.2.1.to_le (Subgroup.zpowers_le.mpr hmemR)
  have h4' := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard (imgOf X K₁)) hcm' h3
  exact hxy (commutatorElement_eq_one_iff_mul_comm.mp h4')


theorem dichotomy_abstract (hΛ : HypOmegaGen Λ)
    (h4 : ∀ J ∈ quotFamily (restrictFamily Λ X) (classicalInvolutionOddCore ↥X),
      ∀ L ∈ quotFamily (restrictFamily Λ X) (classicalInvolutionOddCore ↥X),
      (¬ ∃ g : ↥X ⧸ classicalInvolutionOddCore ↥X, conjSub g J = L) → Commutes J L)
    {K₁ K₂ : Subgroup A} (hK₁ : K₁ ∈ Λ) (hK₂ : K₂ ∈ Λ) (hne : K₁ ≠ K₂) {t : A}
    (ht₁ : IsUniqueInvolution K₁ t) (ht₂ : IsUniqueInvolution K₂ t)
    (hH : K₁ ≤ H) (hXeq : X = H ⊔ K₂) (hnorm : K₂ ≤ Subgroup.normalizer (H : Set A))
    (hgen : (⨆ g : ↥H, conjSub g (K₁.subgroupOf H)) = ⊤) (htH : t ∈ H) :
    (∀ g : ↥H, QuotientGroup.mk' (classicalInvolutionOddCore ↥H) g *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) ⟨t, htH⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H) ⟨t, htH⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) g) ∨
    (∃ h : ↥H, conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) h)
        ((K₁.subgroupOf H).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥H))) ≠
        (K₁.subgroupOf H).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)) ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H) h *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥H) ⟨t, htH⟩ *
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) h)⁻¹ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) ⟨t, htH⟩) := by
  have hHX : H ≤ X := hXeq ▸ le_sup_left
  have hK₂X : K₂ ≤ X := hXeq ▸ le_sup_right
  have hK₁X : K₁ ≤ X := hH.trans hHX
  have hXnorm : X ≤ Subgroup.normalizer (H : Set A) :=
    hXeq ▸ sup_le Subgroup.le_normalizer hnorm
  have hΔ : HypOmegaGen (quotFamily (restrictFamily Λ X) (classicalInvolutionOddCore ↥X)) :=
    TwinEdge.hypOmegaGen_quotFamily_odd (hypOmegaGen_restrict hΛ X)
      (CFSG.ComponentClassification.OddCore.odd_card ↥X)
  have hmem : ∀ {L : Subgroup A}, L ∈ Λ → L ≤ X →
      imgOf X L ∈ quotFamily (restrictFamily Λ X) (classicalInvolutionOddCore ↥X) :=
    fun hL hLX => ⟨_, subgroupOf_mem_restrictFamily hL hLX, rfl⟩
  have hconjH : ∀ h : ↥H, conjSub (h : A) K₁ ≤ H := by
    intro h
    have := conjSub_mono (n := (h : A)) hH
    rwa [conjSub_eq_self_of_mem h.2] at this
  have htX : t ∈ X := hHX htH
  by_cases hall : ∀ h : ↥H, Commutes (imgOf X (conjSub (h : A) K₁)) (imgOf X K₂)
  · left
    have hZ : (⨆ g : ↥H, conjSub g (K₁.subgroupOf H)) ≤
        (Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore ↥H) ⟨t, htH⟩} :
          Set (↥H ⧸ classicalInvolutionOddCore ↥H))).comap
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)) := by
      refine iSup_le fun g => ?_
      intro x hx
      have hxA : (x : A) ∈ conjSub (g : A) K₁ := by
        have h1 := hx
        rw [conjSub_subgroupOf] at h1
        exact Subgroup.mem_subgroupOf.mp h1
      have hxX : (x : A) ∈ X := hHX x.2
      have hu : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (⟨(x : A), hxX⟩ : ↥X) ∈
          imgOf X (conjSub (g : A) K₁) := mem_imgOf_iff.mpr ⟨_, hxA, rfl⟩
      have hv : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (⟨t, htX⟩ : ↥X) ∈ imgOf X K₂ :=
        mem_imgOf_iff.mpr ⟨_, ht₂.mem, rfl⟩
      have hcomm := hall g _ hu _ hv
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (comm_of_commX hHX x ⟨t, htH⟩ hcomm).symm
    intro g
    have hg := hZ (by rw [hgen]; exact Subgroup.mem_top g)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hg
    exact (hg _ (Set.mem_singleton _)).symm
  · right
    push Not at hall
    obtain ⟨h, hnc⟩ := hall
    have hJ₀ := hmem (hΛ.conjInvariant (h : A) K₁ hK₁) ((hconjH h).trans hHX)
    have hL₀ := hmem hK₂ hK₂X
    obtain ⟨gb, hgb⟩ : ∃ g : ↥X ⧸ classicalInvolutionOddCore ↥X,
        conjSub g (imgOf X (conjSub (h : A) K₁)) = imgOf X K₂ := by
      by_contra hng
      exact hnc (h4 _ hJ₀ _ hL₀ hng)
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective _ gb
    have hg0 : ((g₀⁻¹ : ↥X) : A) ∈ H ⊔ K₂ := hXeq ▸ (g₀⁻¹).2
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ H, ∃ b ∈ K₂, ((g₀⁻¹ : ↥X) : A) = a * b := by
      have hx' : ((g₀⁻¹ : ↥X) : A) ∈ ((H ⊔ K₂ : Subgroup A) : Set A) := hg0
      rw [Subgroup.coe_mul_of_right_le_normalizer_left H K₂ hnorm] at hx'
      obtain ⟨a, ha, b, hb, e⟩ := hx'
      exact ⟨a, ha, b, hb, e.symm⟩
    have haX : a ∈ X := hHX ha
    have hJ₀eq : imgOf X (conjSub (h : A) K₁) = imgOf X (conjSub a K₂) := by
      have h1 : imgOf X (conjSub (h : A) K₁) =
          conjSub ((QuotientGroup.mk' (classicalInvolutionOddCore ↥X) g₀)⁻¹) (imgOf X K₂) := by
        rw [← hgb, conjSub_inv_conjSub]
      rw [h1, ← map_inv, imgOf_conj, hab, conjSub_mul, conjSub_eq_self_of_mem hb]
    set h' : ↥H := (⟨a, ha⟩ : ↥H)⁻¹ * h with hh'
    have hstar : imgOf X (conjSub (h' : A) K₁) = imgOf X K₂ := by
      have h1 : imgOf X (conjSub (h' : A) K₁) =
          conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (⟨a⁻¹, hHX (inv_mem ha)⟩ : ↥X))
            (imgOf X (conjSub (h : A) K₁)) := by
        rw [imgOf_conj, show ((h' : ↥H) : A) = a⁻¹ * (h : A) from rfl, conjSub_mul]
      rw [h1, hJ₀eq, imgOf_conj, conjSub_inv_conjSub]
    have hN : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
      CFSG.ComponentClassification.OddCore.odd_card ↥X
    have hh'X : (conjSub (h' : A) K₁) ≤ X := (hconjH h').trans hHX
    refine ⟨h', ?_, ?_⟩
    · intro hEq
      have hle : imgOf X (conjSub (h' : A) K₁) ≤ imgOf X K₁ := by
        intro y hy
        obtain ⟨a₁, ha₁, rfl⟩ := mem_imgOf_iff.mp hy
        have haH : (a₁ : A) ∈ H := (hconjH h') ha₁
        have h1 : (⟨(a₁ : A), haH⟩ : ↥H) ∈ conjSub h' (K₁.subgroupOf H) := by
          rw [conjSub_subgroupOf]; exact Subgroup.mem_subgroupOf.mpr ha₁
        have h2 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)) h1
        rw [AscQuot.map_conjSub, hEq] at h2
        obtain ⟨k, hk, hke⟩ := h2
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hke
        have hodd := mem_oddCoreOf_of_mem_oddCore hHX hXnorm hke
        refine mem_imgOf_iff.mpr ⟨⟨(k : A), hHX k.2⟩, Subgroup.mem_subgroupOf.mp hk, ?_⟩
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        obtain ⟨hX', hmem'⟩ := mem_oddCoreOf_iff.mp hodd
        exact hmem'
      have hc2 : imgOf X (conjSub (h' : A) K₁) =
          conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)
            (⟨(h' : A), hHX h'.2⟩ : ↥X)) (imgOf X K₁) :=
        (imgOf_conj X (L := K₁) (⟨(h' : A), hHX h'.2⟩ : ↥X)).symm
      have hcard : Nat.card (imgOf X K₁) ≤ Nat.card (imgOf X (conjSub (h' : A) K₁)) := by
        rw [hc2, AscL62.natCard_conjSub]
      have hEq' := Subgroup.eq_of_le_of_card_ge hle hcard
      have hM : imgOf X K₁ = imgOf X K₂ := hEq'.symm.trans hstar
      exact false_of_imgOf_eq hΛ hK₁ hK₂ hne ht₁ ht₂ hK₁X hK₂X hM
    ·
      have hz1 := isUniqueInvolution_map_mk_of_odd
        (odd_natCard_inf hN ((conjSub (h' : A) K₁).subgroupOf X))
        (isUniqueInvolution_subgroupOf (ht₁.conj (h' : A)) hh'X)
      have hz2 := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN (K₂.subgroupOf X))
        (isUniqueInvolution_subgroupOf ht₂ hK₂X)
      have hz1' : IsUniqueInvolution (imgOf X K₂)
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)
            (⟨(h' : A) * t * (h' : A)⁻¹, hh'X (ht₁.conj (h' : A)).mem⟩ : ↥X)) := by
        rw [← hstar]; exact hz1
      have hEq := hz2.eq hz1'
      have := eq_of_eqX hHX (⟨t, htH⟩ : ↥H) (h' * ⟨t, htH⟩ * h'⁻¹) hEq
      rw [map_mul, map_mul, map_inv] at this
      exact this.symm

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2
