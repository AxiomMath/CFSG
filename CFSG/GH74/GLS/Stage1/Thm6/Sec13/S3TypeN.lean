module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Y
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3ModelN
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Gen
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Orbit

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

structure NabFacts (P : Subgroup G) : Prop where
  card : Nat.card P = 64
  comm_central : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, ⁅a, b⁆ * c = c * ⁅a, b⁆
  central_card : ∀ Z : Subgroup G, Z ≤ P → (∀ z ∈ Z, ∀ c ∈ P, z * c = c * z) → Nat.card Z ≤ 4
  Q : ∀ w ∈ P, (∃ h ∈ P, w * h ≠ h * w) → ∀ z ∈ P, (∀ c ∈ P, z * c = c * z) →
    ∃ h ∈ P, ⁅w, h⁆ = z

theorem NabFacts.of_model [Finite G] {P : Subgroup G} (hN : NabModel ↥P) : NabFacts P := by
  refine ⟨hN.card, ?_, ?_, ?_⟩
  · intro a ha b hb c hc
    have := congrArg Subtype.val (hN.comm_central ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩)
    simpa [commutatorElement_def] using this
  · intro Z hZP hZ
    have h := hN.central_card (Z.subgroupOf P) (by
      intro z hz c
      apply Subtype.ext
      exact hZ z.1 hz c.1 c.2)
    have e : Nat.card (Z.subgroupOf P) = Nat.card Z :=
      Nat.card_congr (subgroupOfEquivOfLe hZP).toEquiv
    rwa [e] at h
  · intro w hw hnc z hz hzc
    obtain ⟨h0, hh0, hne⟩ := hnc
    obtain ⟨h, hh⟩ := hN.Q ⟨w, hw⟩ ⟨⟨h0, hh0⟩, fun h' => hne (congrArg Subtype.val h')⟩ ⟨z, hz⟩
      (fun c => Subtype.ext (hzc c.1 c.2))
    refine ⟨h.1, h.2, ?_⟩
    have := congrArg Subtype.val hh
    simpa [commutatorElement_def] using this

namespace NabFacts

variable {P V : Subgroup G} (hF : NabFacts P) (hVP : V ≤ P) (hV4 : Nat.card V = 4)
  (hVsq : ∀ v ∈ V, v * v = 1) (hVc : ∀ v ∈ V, ∀ a ∈ P, v * a = a * v)
include hF hVP hV4 hVc

theorem center_eq [Finite G] : P ⊓ centralizer (P : Set G) = V := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · intro v hv
    refine ⟨hVP hv, ?_⟩
    show v ∈ centralizer (P : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    exact (hVc v hv a ha).symm
  · have h := hF.central_card (P ⊓ centralizer (P : Set G)) inf_le_left (by
      intro z hz c hc
      have := mem_centralizer_iff.1 hz.2 c hc
      exact this.symm)
    rw [hV4]
    exact h

theorem mem_V_of_central [Finite G] {z : G} (hzP : z ∈ P) (hz : ∀ c ∈ P, z * c = c * z) :
    z ∈ V := by
  rw [← hF.center_eq hVP hV4 hVc]
  refine ⟨hzP, ?_⟩
  show z ∈ centralizer (P : Set G)
  rw [mem_centralizer_iff]
  intro c hc
  exact (hz c hc).symm

theorem comm_mem_V [Finite G] {a b : G} (ha : a ∈ P) (hb : b ∈ P) : ⁅a, b⁆ ∈ V := by
  apply hF.mem_V_of_central hVP hV4 hVc
  · simp only [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  · exact fun c hc => hF.comm_central a ha b hb c hc

include hVsq in
theorem sq_mem_V [Finite G] {a : G} (ha : a ∈ P) : a * a ∈ V := by
  apply hF.mem_V_of_central hVP hV4 hVc (P.mul_mem ha ha)
  intro b hb
  have hc : ⁅a, b⁆ ∈ V := hF.comm_mem_V hVP hV4 hVc ha hb
  have hcc : ⁅a, b⁆ * ⁅a, b⁆ = 1 := hVsq _ hc
  have hca : ⁅a, b⁆ * a = a * ⁅a, b⁆ := hF.comm_central a ha b hb a ha
  have h1 : a * b = ⁅a, b⁆ * (b * a) := by simp only [commutatorElement_def]; group
  calc a * a * b = a * (a * b) := by group
    _ = a * (⁅a, b⁆ * (b * a)) := by rw [h1]
    _ = (a * ⁅a, b⁆) * (b * a) := by group
    _ = (⁅a, b⁆ * a) * (b * a) := by rw [← hca]
    _ = ⁅a, b⁆ * (a * b) * a := by group
    _ = ⁅a, b⁆ * (⁅a, b⁆ * (b * a)) * a := by rw [h1]
    _ = (⁅a, b⁆ * ⁅a, b⁆) * (b * a) * a := by group
    _ = b * (a * a) := by rw [hcc]; group

theorem data [Finite G] : ∃ D : Subgroup G, DData V P D := by
  refine ⟨V, le_rfl, Or.inr rfl, fun a ha b hb => hF.comm_mem_V hVP hV4 hVc ha hb, ?_⟩
  rw [hV4, hF.card]

theorem Qv [Finite G] : ∀ w ∈ P, w * w = 1 → w ∉ V → ∀ z ∈ V, ∃ h ∈ P, ⁅w, h⁆ = z := by
  intro w hw hw2 hwV z hz
  apply hF.Q w hw
  · by_contra hcon
    push Not at hcon
    exact hwV (hF.mem_V_of_central hVP hV4 hVc hw (fun c hc => hcon c hc))
  · exact hVP hz
  · intro c hc
    exact hVc z hz c hc

theorem exists_square_ne_one [Finite G] : ∃ a ∈ P, a * a ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hi : ∀ g ∈ P, g⁻¹ = g := fun g hg => inv_eq_of_mul_eq_one_right (hcon g hg)
  have hPV : P ≤ V := by
    intro a ha
    apply hF.mem_V_of_central hVP hV4 hVc ha
    intro c hc
    calc a * c = (a * c)⁻¹ := (hi _ (P.mul_mem ha hc)).symm
      _ = c⁻¹ * a⁻¹ := mul_inv_rev a c
      _ = c * a := by rw [hi a ha, hi c hc]
  have := Subgroup.card_le_of_le hPV
  rw [hF.card, hV4] at this
  omega

include hVsq in
theorem cover [Finite G] : ∀ u ∈ P, u * u = 1 → ∃ A : Subgroup G, A ≤ P ∧ u ∈ A ∧
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ 16 ≤ Nat.card A := by
  intro u hu hu2
  obtain ⟨w, hwP, hwV, huw⟩ : ∃ w ∈ P, w ∉ V ∧ (u ∈ V ∨ u = w) := by
    by_cases huV : u ∈ V
    · have hnle : ¬ P ≤ V := by
        intro h
        have := Subgroup.card_le_of_le h
        rw [hF.card, hV4] at this
        omega
      obtain ⟨w, hwP, hwV⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
      exact ⟨w, hwP, hwV, Or.inl huV⟩
    · exact ⟨u, hu, huV, Or.inr rfl⟩
  have hcls : cls P w ⊆ (fun v => v * w) '' (V : Set G) := by
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨h * w * h⁻¹ * w⁻¹, ?_, by show h * w * h⁻¹ * w⁻¹ * w = h * w * h⁻¹; group⟩
    exact hF.comm_mem_V hVP hV4 hVc hh hwP
  have hclscard : Nat.card (cls P w) ≤ 4 := by
    have h1 : Nat.card (cls P w) = (cls P w).ncard := (Nat.card_coe_set_eq _).symm
    have h2 : (cls P w).ncard ≤ ((fun v => v * w) '' (V : Set G)).ncard :=
      Set.ncard_le_ncard hcls (Set.toFinite _)
    have h3 : ((fun v => v * w) '' (V : Set G)).ncard ≤ (V : Set G).ncard :=
      Set.ncard_image_le (Set.toFinite _)
    have h4 : (V : Set G).ncard = Nat.card V := Nat.card_coe_set_eq _
    omega
  have horb := card_cls_mul' P w
  have hC16 : 16 ≤ Nat.card ↥(P ⊓ centralizer ({w} : Set G)) := by
    have hpos : 0 < Nat.card ↥(P ⊓ centralizer ({w} : Set G)) := Nat.card_pos
    have h1 : Nat.card P ≤ 4 * Nat.card ↥(P ⊓ centralizer ({w} : Set G)) := by
      calc Nat.card P = Nat.card (cls P w) * Nat.card ↥(P ⊓ centralizer ({w} : Set G)) :=
            horb.symm
        _ ≤ 4 * Nat.card ↥(P ⊓ centralizer ({w} : Set G)) := Nat.mul_le_mul_right _ hclscard
    rw [hF.card] at h1
    omega
  have hwn : ∀ q ∈ V, w * q * w⁻¹ ∈ V := by
    intro q hq
    have := hVc q hq w hwP
    have e : w * q * w⁻¹ = q := by
      calc w * q * w⁻¹ = (q * w) * w⁻¹ := by rw [this]
        _ = q := by group
    rw [e]; exact hq
  have hww : w * w ∈ V := hF.sq_mem_V hVP hV4 hVsq hVc hwP
  have hK8 : Nat.card ↥(V ⊔ zpowers w) = 8 := by
    have := card_sup_zpowers_sq hww hwn hwV
    rw [hV4] at this
    exact this
  obtain ⟨z, hzP, hzC, hzK⟩ : ∃ z ∈ P, z * w = w * z ∧ z ∉ V ⊔ zpowers w := by
    by_contra hcon
    push Not at hcon
    have hle : P ⊓ centralizer ({w} : Set G) ≤ V ⊔ zpowers w := by
      rintro z ⟨hzP, hzC⟩
      apply hcon z hzP
      have := mem_centralizer_iff.1 hzC w rfl
      exact this.symm
    have := Subgroup.card_le_of_le hle
    omega
  have hcomS : ∀ a ∈ (V : Set G) ∪ {w, z}, ∀ b ∈ (V : Set G) ∪ {w, z}, a * b = b * a := by
    have hmemP : ∀ a ∈ (V : Set G) ∪ {w, z}, a ∈ P := by
      intro a ha
      rcases ha with ha | ha
      · exact hVP ha
      · rcases ha with rfl | ha
        · exact hwP
        · rw [Set.mem_singleton_iff] at ha
          rw [ha]; exact hzP
    intro a ha b hb
    rcases ha with ha | ha
    · exact hVc a ha b (hmemP b hb)
    · rcases hb with hb | hb
      · exact (hVc b hb a (hmemP a (Or.inr ha))).symm
      · rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · rfl
        · rw [Set.mem_singleton_iff] at hb
          rw [hb]; exact hzC.symm
        · rw [Set.mem_singleton_iff] at ha
          rw [ha]; exact hzC
        · rw [Set.mem_singleton_iff] at ha hb
          rw [ha, hb]
  let A : Subgroup G := Subgroup.closure ((V : Set G) ∪ {w, z})
  have hAP : A ≤ P := by
    rw [Subgroup.closure_le]
    intro a ha
    rcases ha with ha | ha
    · exact hVP ha
    · rcases ha with rfl | ha
      · exact hwP
      · rw [Set.mem_singleton_iff] at ha
        rw [ha]; exact hzP
  have hKA : V ⊔ zpowers w ≤ A := by
    refine sup_le ?_ ?_
    · intro v hv
      exact Subgroup.subset_closure (Or.inl hv)
    · rw [zpowers_le]
      exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hzA : z ∈ A := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hlt : V ⊔ zpowers w < A := lt_of_le_of_ne hKA (fun h => hzK (by rw [h]; exact hzA))
  have hc1 := Subgroup.card_lt_of_lt hlt
  have hd1 := Subgroup.card_dvd_of_le hKA
  obtain ⟨m, hm⟩ := hd1
  rw [hK8] at hc1 hm
  have hm2 : 2 ≤ m := by
    by_contra hlm
    have : m ≤ 1 := by omega
    have := Nat.mul_le_mul_left 8 this
    omega
  refine ⟨A, hAP, ?_, ?_, ?_⟩
  · rcases huw with huV | rfl
    · exact Subgroup.subset_closure (Or.inl huV)
    · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · intro a ha b hb
    have hpair : ((V : Set G) ∪ {w, z}).Pairwise Commute := fun a ha b hb _ => hcomS a ha b hb
    have hmc : IsMulCommutative ↥A := Subgroup.isMulCommutative_closure hpair
    have := hmc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  · have := Nat.mul_le_mul_left 8 hm2
    omega

include hVsq in
theorem yfacts [Finite G] : YFacts V P :=
  ⟨hF.data hVP hV4 hVc, hF.Qv hVP hV4 hVc, hF.cover hVP hV4 hVsq hVc,
    hF.exists_square_ne_one hVP hV4 hVc, ⟨3, by norm_num, by rw [hF.card]; norm_num⟩⟩

end NabFacts

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
