module

public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.Asc77.WP1Section17

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace AscThmA

open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def ThmAOn (Ω : Set (Subgroup G)) : Prop :=
  ∀ J ∈ Ω, ∀ L : Subgroup G, IsComponent L → ∀ k ∈ J, conjSub k L = L

theorem thmA_on [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h613 : Comm613On Ω) {K : Subgroup G} (hK : K ∈ Ω) {L : Subgroup G} (hL : IsComponent L)
    {k : G} (hk : k ∈ K) : conjSub k L = L := by
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  have hEn : (layer G).Normal := normal_layer
  by_cases hzE : z ∈ layer G
  · rcases le_or_commutator_le_oddCoreOf hp hq hΩ hK hz (layer G) with hKE | hcomm
    · exact mem_normalizer_iff_conjSub_eq.mp (layer_le_normalizer hL (hKE hk))
    · by_contra hne
      have hL' : IsComponent (conjSub k L) := isComponent_conjSub hL k
      have hLc : ⁅L, conjSub k L⁆ = ⊥ := by
        rcases distinct_components_commute hL hL' with h | h
        · exact absurd h.symm hne
        · exact h
      have hLk : ∀ y ∈ L, ∀ w ∈ conjSub k L, y * w = w * y := fun y hy w hw =>
        (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLc hy) w hw).symm
      obtain ⟨x, hx⟩ := exists_layerMul_eq hzE
      set a : G := (x ⟨L, hL⟩ : G) with ha
      have haL : a ∈ L := (x ⟨L, hL⟩).2
      have hacom : Commute a z := by
        rw [← hx]
        exact (commute_layerMul_iff x ⟨L, hL⟩ haL).mpr (Commute.refl a)
      have haEH : a ∈ layer G ⊓ Subgroup.centralizer ({z} : Set G) :=
        ⟨component_le_layer hL haL, Subgroup.mem_centralizer_singleton_iff.mpr hacom.eq⟩
      have ha2 : ∀ y ∈ L, y * (a * a) = (a * a) * y := by
        intro y hy
        have hz2 : layerMul G (x * x) = 1 := by
          rw [map_mul, hx]
          exact hz.sq
        have h1 : Commute y (layerMul G (x * x)) := by rw [hz2]; exact Commute.one_right y
        exact ((commute_layerMul_iff (x * x) ⟨L, hL⟩ hy).mp h1).eq
      have hka := hcomm (Subgroup.commutator_mem_commutator hk haEH)
      have hbL : ∀ y ∈ L, y * (k * a * k⁻¹) = (k * a * k⁻¹) * y := fun y hy =>
        hLk y hy _ (conj_mem_conjSub haL)
      have hcdef : ⁅k, a⁆ = (k * a * k⁻¹) * a⁻¹ := by rw [commutatorElement_def]
      set m : ℕ := orderOf ⁅k, a⁆ with hm
      have hmodd : Odd m :=
        (oddCoreOf_odd_natCard (Subgroup.centralizer ({z} : Set G))).of_dvd_nat
          (Subgroup.orderOf_dvd_natCard _ hka)
      have hba : Commute (k * a * k⁻¹) a := (hLk a haL _ (conj_mem_conjSub haL)).symm
      have hcomm_ba : Commute (k * a * k⁻¹) a⁻¹ := hba.inv_right
      have hpow : (k * a * k⁻¹) ^ m = a ^ m := by
        have h1 : ⁅k, a⁆ ^ m = 1 := pow_orderOf_eq_one _
        rw [hcdef, hcomm_ba.mul_pow, inv_pow] at h1
        exact mul_inv_eq_one.mp h1
      have ham : ∀ y ∈ L, y * a ^ m = a ^ m * y := by
        intro y hy
        rw [← hpow]
        exact ((show Commute y (k * a * k⁻¹) from hbL y hy).pow_right m).eq
      obtain ⟨j, hj⟩ := hmodd
      have hacen : ∀ y ∈ L, y * a = a * y := by
        intro y hy
        have h1 : Commute y (a ^ m) := ham y hy
        have h2 : Commute y ((a * a) ^ j) := ((show Commute y (a * a) from ha2 y hy).pow_right j)
        have h3 : a = ((a * a) ^ j)⁻¹ * a ^ m := by
          rw [hj, pow_succ, pow_mul, ← pow_two]
          group
        rw [h3]
        exact (h2.inv_right.mul_right h1).eq
      have hzL : ∀ y ∈ L, y * z = z * y := by
        intro y hy
        rw [← hx]
        exact ((commute_layerMul_iff x ⟨L, hL⟩ hy).mpr (hacen y hy)).eq
      have hLEH : L ≤ layer G ⊓ Subgroup.centralizer ({z} : Set G) := fun y hy =>
        ⟨component_le_layer hL hy, Subgroup.mem_centralizer_singleton_iff.mpr (hzL y hy)⟩
      have hk2 : ∀ y ∈ L, IsPGroup 2 (Subgroup.zpowers y) → k * y = y * k := by
        intro y hy hy2
        have hcy : ⁅k, y⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
          hcomm (Subgroup.commutator_mem_commutator hk (hLEH hy))
        have hby : Commute (k * y * k⁻¹) y⁻¹ :=
          ((show Commute y (k * y * k⁻¹) from hLk y hy _ (conj_mem_conjSub hy)).symm).inv_right
        have hby2 : IsPGroup 2 (Subgroup.zpowers (k * y * k⁻¹)) := by
          obtain ⟨n, hn⟩ := hy2.exists_card_eq
          refine IsPGroup.of_card (n := n) ?_
          have hord : orderOf (k * y * k⁻¹) = orderOf y := by
            have := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective y
            simpa using this
          rw [Nat.card_zpowers, hord, ← Nat.card_zpowers]
          exact hn
        have hyi2 : IsPGroup 2 (Subgroup.zpowers y⁻¹) := by
          rw [Subgroup.zpowers_inv]
          exact hy2
        have hc2 : IsPGroup 2 (Subgroup.zpowers ⁅k, y⁆) := by
          rw [commutatorElement_def]
          exact isPGroup_zpowers_mul hby hby2 hyi2
        have h1 := eq_one_of_isPGroup_of_mem_odd
          (oddCoreOf_odd_natCard (Subgroup.centralizer ({z} : Set G))) hcy hc2
        rw [commutatorElement_def] at h1
        calc k * y = (k * y * k⁻¹ * y⁻¹) * (y * k) := by group
          _ = y * k := by rw [h1, one_mul]
      have hLk' : L ≤ Subgroup.centralizer ({k} : Set G) := by
        refine le_of_forall_isSylow2In_of_isPerfect hL.1.1 fun V hV y hy => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hk2 y (hV.1 hy) (hV.2.1.to_le (Subgroup.zpowers_le.mpr hy))).symm
      have hkc : ∀ y ∈ L, k * y = y * k := fun y hy =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hLk' hy)).symm
      have hZL : Commutes (Subgroup.zpowers k) L := by
        intro a ha y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact (Commute.zpow_left (show Commute k y from hkc y hy) n).eq
      exact hne (conjSub_eq_of_mem_of_commutes (Subgroup.mem_zpowers k) hZL)
  · have hV : ∀ V : Subgroup G, IsSylow2In V K → V ≤ Subgroup.centralizer (layer G : Set G) := by
      intro V hV
      have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
      have hVE : V ⊓ layer G = ⊥ :=
        inf_eq_bot_of_uniqueInvolution_not_mem hz hV.1 hV.2.1 hzE
      have h1 : ⁅V, layer G⁆ ≤ oddCoreOf (layer G) := h613 V hVR (layer G) hEn hVE
      have h2 : ⁅V, layer G⁆ = ⊥ :=
        commutator_eq_bot_of_le_oddCoreOf (𝒮 := {K | IsComponent K}) (fun B hB => hB) hEn h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
    have hKc : K ≤ Subgroup.centralizer (layer G : Set G) :=
      hΩ.le_of_forall_isSylow2In hK hV
    have hKL : Commutes K L := fun y hy w hw =>
      (Subgroup.mem_centralizer_iff.mp (hKc hy) w (component_le_layer hL hw)).symm
    exact conjSub_eq_of_mem_of_commutes hk hKL

theorem thmAOn_of_comm613On [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h613 : Comm613On Ω) : ThmAOn Ω :=
  fun _ hK _ hL _ hk => thmA_on hp hq hΩ h613 hK hL hk

end AscThmA

open AscThmA in
theorem lThmA_of_l6_13 {p f : ℕ} [Fact p.Prime] (h : L6_13 p f) : LThmA p f := by
  intro hp hq G _ _ Ω hΩ K hK L hL k hk
  exact thmA_on hp hq hΩ (comm613On_of_l6_13 h hp hq hΩ) hK
    ((CFSG.isComponent_iff_open L).mpr hL) hk

end CFSG.ClassicalInvolution.Asc77
