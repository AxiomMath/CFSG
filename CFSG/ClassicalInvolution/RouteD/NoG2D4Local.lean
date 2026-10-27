module

public import CFSG.ClassicalInvolution.RouteD.NoG2D4Model
public import CFSG.ClassicalInvolution.RouteD.GapsR2

public section

namespace CFSG.ClassicalInvolution.RouteD.G2D4

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem nonempty_mulEquiv_locImg [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) :
    Nonempty (locImg Ω x L ≃* SL(2, GaloisField p f)) := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hLY := le_centralizingLayer hL
  let e := Subgroup.subgroupOfEquivOfLe hLY
  have hO : classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x)) = ⊥ := by
    have h1 : Subgroup.map e.toMonoidHom
        (classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x))) =
        classicalInvolutionOddCore ↥L := CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [hex L hL.1] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hinf := inf_oddCore_eq_bot hO
  set ψ : L.subgroupOf (locLayer Ω x) →* locQuot Ω x :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))).comp
      (L.subgroupOf (locLayer Ω x)).subtype with hψ
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hker : (a : ↥(locLayer Ω x)) ∈ (L.subgroupOf (locLayer Ω x)) ⊓
        classicalInvolutionOddCore ↥(locLayer Ω x) :=
      ⟨a.2, (QuotientGroup.eq_one_iff _).mp ha⟩
    rw [hinf, Subgroup.mem_bot] at hker
    exact Subtype.ext hker
  have hrange : ψ.range = locImg Ω x L := by
    unfold locImg
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e'⟩ := hz.nonempty_equiv_sl2 (hex L hL.1)
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans ((MonoidHom.ofInjective hinj).symm.trans
    (e.trans e'))⟩

theorem card_center_locImg_dvd_two [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) :
    Nat.card (Subgroup.center (locImg Ω x L)) ∣ 2 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_locImg hΩ hex hL
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact card_center_sl2_dvd_two

theorem tag_ne_of_commuting_triple [Finite G] {Ω : Set (Subgroup G)} (hp2 : p ≠ 2)
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {x : G}
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {i : Fin D.card}
    {N₁ N₂ N₃ : Subgroup G} (h₁ : N₁ ∈ Gaps.compMembers Ω x D i)
    (h₂ : N₂ ∈ Gaps.compMembers Ω x D i) (h₃ : N₃ ∈ Gaps.compMembers Ω x D i)
    (c₁₂ : Commutes N₁ N₂) (c₁₃ : Commutes N₁ N₃) (c₂₃ : Commutes N₂ N₃) :
    D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
  by_contra hcon
  have ht : D.tag i = .G2 ∨ D.tag i = .trialityD4 := by
    by_cases h : D.tag i = .G2
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra h'
      exact hcon ⟨h, h'⟩
  exact false_of_three_commuting_sl2 hp2 ht (D.admissible i) (D.exp_eq i) (D.hom i)
    h₁.2 h₂.2 h₃.2 (commutes_locImg_of_commutes c₁₂) (commutes_locImg_of_commutes c₁₃)
    (commutes_locImg_of_commutes c₂₃) (card_locImg hΩ hex h₁.1) (card_locImg hΩ hex h₂.1)
    (card_locImg hΩ hex h₃.1) (card_center_locImg_dvd_two hΩ hex h₁.1)
    (card_center_locImg_dvd_two hΩ hex h₂.1)

section Involutions

theorem mk_ne_one_of_involution [Finite G] {Ω : Set (Subgroup G)} {x : G} {w : G}
    (hw : w ∈ locLayer Ω x) (hord : orderOf w = 2) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hw⟩ ≠ 1 := by
  intro h
  have hO : (⟨w, hw⟩ : ↥(locLayer Ω x)) ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
    (QuotientGroup.eq_one_iff _).mp h
  have h3 : orderOf (⟨⟨w, hw⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hord
  have h4 := orderOf_dvd_natCard (⟨⟨w, hw⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
  rw [h3] at h4
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
    (even_iff_two_dvd.mpr h4)

theorem eq_of_mk_eq_of_involutions [Finite G] {Ω : Set (Subgroup G)} {x : G}
    (hP1 : LocalOddCentral Ω {x}) {w₁ w₂ : G} (h₁ : w₁ ∈ locLayer Ω x) (h₂ : w₂ ∈ locLayer Ω x)
    (o₁ : w₁ * w₁ = 1) (o₂ : w₂ * w₂ = 1)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w₁, h₁⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w₂, h₂⟩) : w₁ = w₂ := by
  set u : ↥(locLayer Ω x) := ⟨w₁, h₁⟩ with hu
  set v : ↥(locLayer Ω x) := ⟨w₂, h₂⟩ with hv
  have huu : u * u = 1 := Subtype.ext o₁
  have hvv : v * v = 1 := Subtype.ext o₂
  have haO : u⁻¹ * v ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := QuotientGroup.eq.mp h
  have hcent : ∀ g : ↥(locLayer Ω x), g * (u⁻¹ * v) = (u⁻¹ * v) * g := fun g =>
    Subgroup.mem_center_iff.mp (hP1 haO) g
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have huv : u * v = v * u := by
    have h1 := hcent u
    rw [mul_inv_cancel_left] at h1
    calc u * v = u * (u⁻¹ * v * u) := by rw [← h1]
      _ = v * u := by group
  have hsq : (u⁻¹ * v) * (u⁻¹ * v) = 1 := by
    rw [hui]
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [huu, hvv, mul_one]
  have hord : orderOf (⟨u⁻¹ * v, haO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 1 := by
    have h2 : orderOf (⟨u⁻¹ * v, haO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using hsq))
    have h3 := orderOf_dvd_natCard (⟨u⁻¹ * v, haO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h4 | h4
    · exact h4
    · rw [h4] at h3
      exact absurd (even_iff_two_dvd.mpr h3)
        (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
  have h1 : u⁻¹ * v = 1 := by
    have := orderOf_eq_one_iff.mp hord
    exact congrArg Subtype.val this
  have : u = v := inv_mul_eq_one.mp h1
  exact congrArg Subtype.val this

theorem image_involution_facts [Finite G] {Ω : Set (Subgroup G)} {x : G} {N : Subgroup G} {w : G}
    (hN : N ∈ centralizingMembers Ω {x}) (hw : IsClassicalMember p f N w) :
    ∃ hwY : w ∈ locLayer Ω x,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ ∈ locImg Ω x N ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ = 1 ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ ≠ 1 ∧
      ∀ y ∈ locImg Ω x N,
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ * y =
          y * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ := by
  have hwY : w ∈ locLayer Ω x := le_centralizingLayer hN hw.mem
  refine ⟨hwY, ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr hw.mem, rfl⟩, ?_,
    mk_ne_one_of_involution hwY hw.orderOf_eq_two, ?_⟩
  · rw [← map_mul]
    have : (⟨w, hwY⟩ : ↥(locLayer Ω x)) * ⟨w, hwY⟩ = 1 := by
      apply Subtype.ext
      have h2 : w ^ 2 = 1 := by rw [← hw.orderOf_eq_two]; exact pow_orderOf_eq_one w
      simpa [pow_two] using h2
    rw [this, map_one]
  · rintro _ ⟨n, hn, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have := Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isClassicalMember hw hnN)
    exact this.symm

end Involutions

section Shared

theorem eq_involution_of_commuting_in_g2d4 [Finite G] (hSI : G2D4SharedInvolution p)
    (hp2 : p ≠ 2) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {i : Fin D.card} (ht : D.tag i = .G2 ∨ D.tag i = .trialityD4) {c b₁ b₂ : Subgroup G}
    {w₀ w₁ w₂ : G} (hc : c ∈ Gaps.compMembers Ω x D i) (hb₁ : b₁ ∈ Gaps.compMembers Ω x D i)
    (hb₂ : b₂ ∈ Gaps.compMembers Ω x D i) (hw₀ : IsClassicalMember p f c w₀)
    (hw₁ : IsClassicalMember p f b₁ w₁) (hw₂ : IsClassicalMember p f b₂ w₂)
    (cb₁ : Commutes c b₁) (cb₂ : Commutes c b₂) : w₁ = w₂ := by
  have hinj : Function.Injective (D.hom i) :=
    injective_of_ker_le_center hp2 ht (D.rank i) (D.admissible i).2.1 (D.hom i)
      (D.ker_le_center i)
  obtain ⟨hw₀Y, hw₀m, hw₀sq, hw₀1, -⟩ := image_involution_facts hc.1 hw₀
  obtain ⟨hw₁Y, hw₁m, hw₁sq, hw₁1, hw₁c⟩ := image_involution_facts hb₁.1 hw₁
  obtain ⟨hw₂Y, hw₂m, hw₂sq, hw₂1, hw₂c⟩ := image_involution_facts hb₂.1 hw₂
  have hperf : ∀ {N : Subgroup G}, N ∈ centralizingMembers Ω {x} →
      ⁅locImg Ω x N, locImg Ω x N⁆ = locImg Ω x N := by
    intro N hN
    refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
      (Gaps.locImg_le_commutator hΩ hN)
    exact (locImg Ω x N).mul_mem ((locImg Ω x N).mul_mem ((locImg Ω x N).mul_mem ha hb)
      ((locImg Ω x N).inv_mem ha)) ((locImg Ω x N).inv_mem hb)
  have e₁ := eq_of_central_involutions hSI hp2 ht (D.admissible i) (D.hom i) hinj hb₁.2
    (hperf hb₁.1) (hc.2 hw₀m) hw₀sq hw₀1
    (fun y hy => commutes_locImg_of_commutes cb₁ _ hw₀m y hy) hw₁m hw₁1 hw₁c
  have e₂ := eq_of_central_involutions hSI hp2 ht (D.admissible i) (D.hom i) hinj hb₂.2
    (hperf hb₂.1) (hc.2 hw₀m) hw₀sq hw₀1
    (fun y hy => commutes_locImg_of_commutes cb₂ _ hw₀m y hy) hw₂m hw₂1 hw₂c
  have osq : ∀ {N : Subgroup G} {w : G}, IsClassicalMember p f N w → w * w = 1 := by
    intro N w hw
    have h2 : w ^ 2 = 1 := by rw [← hw.orderOf_eq_two]; exact pow_orderOf_eq_one w
    simpa [pow_two] using h2
  exact eq_of_mk_eq_of_involutions hP1 hw₁Y hw₂Y (osq hw₁) (osq hw₂) (e₁.trans e₂.symm)

end Shared

end CFSG.ClassicalInvolution.RouteD.G2D4
