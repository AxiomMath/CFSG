module

public import CFSG.ClassicalInvolution.Asc77.AscT8YB2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY

namespace T8ZZ

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J W : Subgroup G} {z t : G}

theorem layerCenter_of_centralE (F : FrameData Ω W K J z t) {Y : Subgroup G}
    (hz : ∀ i : Fin 4, F.zz i ∈ Y) (V : Subgroup G)
    (hVdef : V = Subgroup.closure ({F.zz 0 * F.zz 1, F.zz 0 * F.zz 2} : Set G))
    (hVab : IsElemAbelian2 V 2) (hVY : V ≤ Y)
    (h01 : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨F.zz 0, hz 0⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨F.zz 1, hz 1⟩ ∈
        Subgroup.center (↥Y ⧸ classicalInvolutionOddCore ↥Y))
    (h02 : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨F.zz 0, hz 0⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨F.zz 2, hz 2⟩ ∈
        Subgroup.center (↥Y ⧸ classicalInvolutionOddCore ↥Y))
    (hcard : Nat.card (Subgroup.center (↥Y ⧸ classicalInvolutionOddCore ↥Y)) ≤ 4) :
    V ≤ zStarOf Y ∧ zStarOf Y ≤ V ⊔ oddCoreOf Y := by
  classical
  set N := classicalInvolutionOddCore ↥Y with hN
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card _
  have ha : V ≤ zStarOf Y := by
    rw [hVdef, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · refine ⟨⟨F.zz 0 * F.zz 1, Y.mul_mem (hz 0) (hz 1)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (QuotientGroup.mk' N) (⟨F.zz 0 * F.zz 1, Y.mul_mem (hz 0) (hz 1)⟩ : ↥Y) =
          QuotientGroup.mk' N ⟨F.zz 0, hz 0⟩ * QuotientGroup.mk' N ⟨F.zz 1, hz 1⟩ := by
        rw [← map_mul]
        rfl
      rw [e]
      exact h01
    · refine ⟨⟨F.zz 0 * F.zz 2, Y.mul_mem (hz 0) (hz 2)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : (QuotientGroup.mk' N) (⟨F.zz 0 * F.zz 2, Y.mul_mem (hz 0) (hz 2)⟩ : ↥Y) =
          QuotientGroup.mk' N ⟨F.zz 0, hz 0⟩ * QuotientGroup.mk' N ⟨F.zz 2, hz 2⟩ := by
        rw [← map_mul]
        rfl
      rw [e]
      exact h02
  refine ⟨ha, ?_⟩
  have hcardV : Nat.card V = 2 ^ 2 := hVab.1
  have hV2 : IsPGroup 2 V := IsPGroup.of_card hcardV
  have hVY : V ≤ Y := hVY
  set Vy : Subgroup ↥Y := V.subgroupOf Y with hVy
  have hVy2 : IsPGroup 2 Vy := hV2.comap_subtype
  have hVy_card : Nat.card Vy = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVY).toEquiv).trans (by rw [hcardV]; norm_num)
  set q : ↥Y →* ((↥Y ⧸ N)) := QuotientGroup.mk' N with hq
  have hinj : Set.InjOn q (Vy : Set ↥Y) := by
    intro a ha' b hb hab
    have h1 : a⁻¹ * b ∈ N := QuotientGroup.eq.mp hab
    have h2 : IsPGroup 2 (Subgroup.zpowers (a⁻¹ * b)) :=
      hVy2.to_le (Subgroup.zpowers_le.mpr (Vy.mul_mem (Vy.inv_mem ha') hb))
    have h3 : a⁻¹ * b = 1 := eq_one_of_isPGroup_of_mem_odd hodd h1 h2
    exact inv_mul_eq_one.mp h3
  set Vq : Subgroup ((↥Y ⧸ N)) := Vy.map q with hVq
  have hVq_card : Nat.card Vq = 4 := by
    have h := Nat.card_image_of_injOn hinj
    have e : (Vq : Set ((↥Y ⧸ N))) = q '' (Vy : Set ↥Y) := Subgroup.coe_map q Vy
    have h2 : Nat.card Vq = Nat.card (q '' (Vy : Set ↥Y)) :=
      congrArg (fun s : Set ((↥Y ⧸ N)) => Nat.card ↥s) e
    rw [h2, h]
    exact hVy_card
  have hVq_le : Vq ≤ Subgroup.center ((↥Y ⧸ N)) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨h, hh, hhv⟩ := ha (Subgroup.mem_subgroupOf.mp hv)
    have hhv' : h = v := Subtype.ext hhv
    subst hhv'
    exact Subgroup.mem_comap.mp hh
  have hVq_eq : Vq = Subgroup.center ((↥Y ⧸ N)) :=
    Subgroup.eq_of_le_of_card_ge hVq_le (by rw [hVq_card]; exact hcard)
  intro w hw
  obtain ⟨h, hh, rfl⟩ := hw
  have hqh : q h ∈ Vq := by
    rw [hVq_eq]
    exact Subgroup.mem_comap.mp hh
  obtain ⟨v, hv, hvh⟩ := hqh
  have h1 : v⁻¹ * h ∈ N := QuotientGroup.eq.mp hvh
  have e : (Y.subtype h : G) = (v : G) * ((v⁻¹ * h : ↥Y) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hv) ⟨v⁻¹ * h, h1, rfl⟩

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
