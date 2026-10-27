module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.LocalOfData

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem map_center_eq_zpowers_of_card {H : Subgroup G} {z : G} (hz : orderOf z = 2) (hzH : z ∈ H)
    (hzc : ∀ h ∈ H, h * z = z * h) (hH : Nat.card (center ↥H) = 2) :
    (center ↥H).map H.subtype = zpowers z := by
  have hzmem : (⟨z, hzH⟩ : ↥H) ∈ center ↥H :=
    mem_center_iff.2 fun h => Subtype.ext (hzc h h.2)
  symm
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 ⟨_, hzmem, rfl⟩) ?_
  rw [Subgroup.card_map_of_injective H.subtype_injective, hH, Nat.card_zpowers, hz]

theorem isExtraspecialPGroup_of_sq_mem_zpowers {U : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hzU : z ∈ U) (hzc : ∀ u ∈ U, u * z = z * u) (hsq : ∀ u ∈ U, u ^ 2 ∈ zpowers z)
    (hcent : ∀ c ∈ U, (∀ u ∈ U, c * u = u * c) → c ∈ zpowers z)
    (hnab : ∃ u ∈ U, u ∉ zpowers z) :
    IsExtraspecialPGroup 2 ↥U ∧ (center ↥U).map U.subtype = zpowers z := by
  have hww : ∀ w ∈ zpowers z, w * w = 1 := fun w hw => by
    rcases eq_one_or_eq_of_mem_zpowers_two hz hw with h | h
    · rw [h, one_mul]
    · rw [h, ← sq, ← hz]
      exact pow_orderOf_eq_one z
  have hwc : ∀ w ∈ zpowers z, ∀ u ∈ U, u * w = w * u := fun w hw u hu => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    exact (Commute.zpow_right (hzc u hu) k).eq
  have hle : zpowers z ≤ U := zpowers_le.2 hzU
  have hext : IsExtraspecialPGroup 2 ↥U := by
    have hP2 : IsPGroup 2 ↥U := by
      intro u
      refine ⟨2, Subtype.ext ?_⟩
      show (u : G) ^ 2 ^ 2 = 1
      have h4 : (u : G) ^ 2 ^ 2 = ((u : G) ^ 2) * ((u : G) ^ 2) := by
        rw [← pow_add]
        rfl
      rw [h4]
      exact hww _ (hsq u u.2)
    refine CFSG.RankThree.PartOne.PlaneCommuting.isExtraspecialPGroup_of_pairing hP2
      (Z := (zpowers z).subgroupOf U) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hz]
    · intro u hu
      rw [mem_subgroupOf] at hu
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hu
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : G) * u = u * y
      rw [← hk]
      exact (Commute.zpow_right (hzc y y.2) k).eq
    · intro u v
      rw [mem_subgroupOf]
      show ⁅(u : G), (v : G)⁆ ∈ zpowers z
      have h1 : (v : G) * ((u : G) ^ 2)⁻¹ = ((u : G) ^ 2)⁻¹ * v :=
        hwc _ (inv_mem (hsq u u.2)) v v.2
      have key : ⁅(u : G), (v : G)⁆ =
          ((u : G) * v) ^ 2 * ((u : G) ^ 2)⁻¹ * ((v : G) ^ 2)⁻¹ := by
        rw [commutatorElement_def]
        calc (u : G) * v * (u : G)⁻¹ * (v : G)⁻¹
            = (u : G) * v * u * (((u : G) ^ 2)⁻¹ * v) * ((v : G) ^ 2)⁻¹ := by group
          _ = (u : G) * v * u * ((v : G) * ((u : G) ^ 2)⁻¹) * ((v : G) ^ 2)⁻¹ := by rw [h1]
          _ = ((u : G) * v) ^ 2 * ((u : G) ^ 2)⁻¹ * ((v : G) ^ 2)⁻¹ := by
            rw [sq ((u : G) * v)]
            group
      rw [key]
      exact mul_mem (mul_mem (hsq _ (U.mul_mem u.2 v.2)) (inv_mem (hsq u u.2)))
        (inv_mem (hsq v v.2))
    · intro u
      rw [mem_subgroupOf]
      exact hsq u u.2
    · intro c hc
      rw [mem_subgroupOf]
      exact hcent c c.2 fun u hu => congrArg Subtype.val (hc ⟨u, hu⟩)
    · obtain ⟨u, hu, hnu⟩ := hnab
      exact ⟨⟨u, hu⟩, fun h => hnu (mem_subgroupOf.1 h)⟩
  exact ⟨hext, map_center_eq_zpowers_of_card hz hzU hzc hext.2.2.2⟩

omit [Finite G] in
theorem exists_eq_or_eq_mul_of_mem_sup_zpowers_of_orderOf_eq_two {R : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hR : ∀ r ∈ R, r * t = t * r) {g : G} (hg : g ∈ R ⊔ zpowers t) :
    ∃ a ∈ R, g = a ∨ g = a * t := by
  have hcomm : ∀ a ∈ R, ∀ b ∈ zpowers t, a * b = b * a := fun a ha b hb => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hR a ha) k).eq
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    CFSG.RankThree.PartOne.PlaneCommuting.exists_mul_of_mem_sup hcomm hg
  rcases eq_one_or_eq_of_mem_zpowers_two ht hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

theorem card_sup_zpowers_of_orderOf_eq_two {R : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htn : t ∉ R) (hR : ∀ r ∈ R, r * t = t * r) :
    Nat.card ↥(R ⊔ zpowers t) = 2 * Nat.card ↥R := by
  have hcomm : ∀ a ∈ R, ∀ b ∈ zpowers t, a * b = b * a := fun a ha b hb => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hR a ha) k).eq
  have h := CFSG.RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hcomm
  have hdisj : R ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgR, hgt⟩
    rcases eq_one_or_eq_of_mem_zpowers_two ht hgt with rfl | rfl
    · exact one_mem _
    · exact absurd hgR htn
  rw [hdisj, Subgroup.card_bot, Nat.card_zpowers, ht] at h
  omega

omit [Finite G] in
theorem exists_eq_or_eq_mul_of_mem_sup_zpowers_of_sq {N : Subgroup G} {x : G}
    (hxN : ∀ r ∈ N, x * r * x⁻¹ ∈ N) (hx2 : x ^ 2 ∈ N) {g : G} (hg : g ∈ N ⊔ zpowers x) :
    ∃ r ∈ N, g = r ∨ g = r * x := by
  have hxN' : ∀ r ∈ N, x⁻¹ * r * x ∈ N := fun r hr => by
    have h2 : (x ^ 2)⁻¹ * (x * r * x⁻¹) * x ^ 2 ∈ N :=
      mul_mem (mul_mem (inv_mem hx2) (hxN r hr)) hx2
    rwa [show (x ^ 2)⁻¹ * (x * r * x⁻¹) * x ^ 2 = x⁻¹ * r * x by group] at h2
  have hnorm : zpowers x ≤ normalizer (N : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro r
    refine ⟨hxN r, fun hr => ?_⟩
    have := hxN' _ hr
    rwa [show x⁻¹ * (x * r * x⁻¹) * x = r by group] at this
  have hg' : g ∈ (N : Set G) * (zpowers x : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
    exact hg
  obtain ⟨r, hr, y, hy, rfl⟩ := Set.mem_mul.1 hg'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · refine ⟨r * (x ^ 2) ^ m, mul_mem hr (zpow_mem hx2 m), Or.inl ?_⟩
    rw [zpow_mul, zpow_ofNat]
  · refine ⟨r * (x ^ 2) ^ m, mul_mem hr (zpow_mem hx2 m), Or.inr ?_⟩
    rw [zpow_add_one, zpow_mul, ← mul_assoc, zpow_ofNat]

theorem isExtraspecialPGroup_sup_zpowers_of_acts {R0 : Subgroup G} {z t x : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hR0 : IsExtraspecialPGroup 2 ↥R0)
    (hcard : Nat.card R0 = 2 ^ 23) (hcen : (center ↥R0).map R0.subtype = zpowers z)
    (htR0 : ∀ r ∈ R0, r * t = t * r) (htn : t ∉ R0)
    (hxz : x * z = z * x) (hxt : x * t * x⁻¹ = t * z)
    (hxR : ∀ r ∈ R0 ⊔ zpowers t, x * r * x⁻¹ * r⁻¹ ∈ zpowers z)
    (hx2 : x ^ 2 ∈ R0 ⊔ zpowers t) (hxn : x ∉ R0 ⊔ zpowers t) :
    IsExtraspecialPGroup 2 ↥(R0 ⊔ zpowers t ⊔ zpowers x) ∧
      Nat.card ↥(R0 ⊔ zpowers t ⊔ zpowers x) = 2 ^ 25 ∧
      (center ↥(R0 ⊔ zpowers t ⊔ zpowers x)).map (R0 ⊔ zpowers t ⊔ zpowers x).subtype =
        zpowers z := by
  have hzR : z ∈ R0 := by
    have : z ∈ (center ↥R0).map R0.subtype := hcen ▸ mem_zpowers z
    obtain ⟨c, -, rfl⟩ := this
    exact c.2
  have hzcA : ∀ a ∈ R0, a * z = z * a := by
    intro a ha
    have : z ∈ (center ↥R0).map R0.subtype := hcen ▸ mem_zpowers z
    obtain ⟨c, hc, rfl⟩ := this
    exact congrArg Subtype.val (mem_center_iff.1 hc ⟨a, ha⟩)
  have hAcen : ∀ a ∈ R0, (∀ a' ∈ R0, a * a' = a' * a) → a ∈ zpowers z := by
    intro a ha h
    have : (⟨a, ha⟩ : ↥R0) ∈ center ↥R0 := mem_center_iff.2 fun a' =>
      Subtype.ext (h a' a'.2).symm
    rw [← hcen]
    exact ⟨_, this, rfl⟩
  have hAsq : ∀ a ∈ R0, a ^ 2 ∈ zpowers z := by
    intro a ha
    have h := hR0.sq_mem_center ⟨a, ha⟩
    have h' : (((⟨a, ha⟩ : ↥R0) ^ 2 : ↥R0) : G) ∈ (center ↥R0).map R0.subtype := ⟨_, h, rfl⟩
    rw [hcen] at h'
    exact h'
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz
    omega
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    omega
  have hzz : z * z = 1 := by
    rw [← sq, ← hz]
    exact pow_orderOf_eq_one z
  have htt : t * t = 1 := by
    rw [← sq, ← ht]
    exact pow_orderOf_eq_one t
  have htz : t * z = z * t := (htR0 z hzR).symm
  have htzne : t ≠ z := fun h => htn (by rw [h]; exact hzR)
  have hxw : ∀ w ∈ zpowers z, x * w = w * x := fun w hw => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    exact (Commute.zpow_right hxz k).eq
  have hww : ∀ w ∈ zpowers z, w * w = 1 := fun w hw => by
    rcases eq_one_or_eq_of_mem_zpowers_two hz hw with h | h
    · rw [h, one_mul]
    · rw [h]
      exact hzz
  have hR1dec : ∀ g ∈ R0 ⊔ zpowers t, ∃ a ∈ R0, g = a ∨ g = a * t := fun g hg =>
    exists_eq_or_eq_mul_of_mem_sup_zpowers_of_orderOf_eq_two ht htR0 hg
  have hzR1 : z ∈ R0 ⊔ zpowers t := mem_sup_left hzR
  have htR1 : t ∈ R0 ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hwR1 : zpowers z ≤ R0 ⊔ zpowers t := zpowers_le.2 hzR1
  have hzcR1 : R0 ⊔ zpowers t ≤ centralizer {z} :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.2 (hzcA a ha))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 htz))
  have htcR1 : R0 ⊔ zpowers t ≤ centralizer {t} :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.2 (htR0 a ha))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hR1sq : ∀ r ∈ R0 ⊔ zpowers t, r ^ 2 ∈ zpowers z := by
    intro r hr
    obtain ⟨a, ha, h | h⟩ := hR1dec r hr
    · rw [h]
      exact hAsq a ha
    · rw [h, (show Commute a t from htR0 a ha).mul_pow, sq t, htt, mul_one]
      exact hAsq a ha
  have hwr_comm : ∀ w ∈ zpowers z, ∀ r ∈ R0 ⊔ zpowers t, r * w = w * r := fun w hw r hr => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    exact (Commute.zpow_right (mem_centralizer_singleton_iff.1 (hzcR1 hr)) k).eq
  have hconj : ∀ r ∈ R0 ⊔ zpowers t, ∃ w ∈ zpowers z, x * r * x⁻¹ = w * r := fun r hr =>
    ⟨x * r * x⁻¹ * r⁻¹, hxR r hr, by group⟩
  have hxN : ∀ r ∈ R0 ⊔ zpowers t, x * r * x⁻¹ ∈ R0 ⊔ zpowers t := by
    intro r hr
    obtain ⟨w, hw, hwr⟩ := hconj r hr
    rw [hwr]
    exact mul_mem (hwR1 hw) hr
  have hxt' : x * t = t * z * x := by
    calc x * t = (x * t * x⁻¹) * x := by group
      _ = t * z * x := by rw [hxt]
  have haz : ∀ a ∈ R0, ∀ g : G, (g = a ∨ g = a * t) → (∀ b ∈ R0, g * b = b * g) →
      a ∈ zpowers z := by
    intro a ha g hg hgb
    refine hAcen a ha fun b hb => ?_
    rcases hg with rfl | rfl
    · exact hgb b hb
    · have h2 : a * b * t = b * a * t := by
        calc a * b * t = a * (b * t) := mul_assoc _ _ _
          _ = a * (t * b) := by rw [htR0 b hb]
          _ = a * t * b := (mul_assoc _ _ _).symm
          _ = b * (a * t) := hgb b hb
          _ = b * a * t := (mul_assoc _ _ _).symm
      exact mul_right_cancel h2
  have hs : ∀ a ∈ zpowers z, ∀ g : G, (g = a ∨ g = a * t) → x * g = g * x → g = a := by
    intro a ha g hg hxg
    rcases hg with rfl | rfl
    · rfl
    · exfalso
      apply hz1
      have h1 : a * (t * z * x) = a * (t * x) := by
        calc a * (t * z * x) = a * (x * t) := by rw [hxt']
          _ = a * x * t := (mul_assoc _ _ _).symm
          _ = x * a * t := by rw [hxw a ha]
          _ = x * (a * t) := mul_assoc _ _ _
          _ = a * t * x := hxg
          _ = a * (t * x) := mul_assoc _ _ _
      simpa [mul_assoc] using mul_left_cancel h1
  have hx2c : ∀ r ∈ R0 ⊔ zpowers t, x ^ 2 * r = r * x ^ 2 := by
    intro r hr
    obtain ⟨w, hw, hwr⟩ := hconj r hr
    have hxwx : x * w * x⁻¹ = w := by
      rw [hxw w hw]
      group
    have key : x ^ 2 * r * (x ^ 2)⁻¹ = r := by
      calc x ^ 2 * r * (x ^ 2)⁻¹ = x * (x * r * x⁻¹) * x⁻¹ := by
            rw [pow_two]
            group
        _ = x * (w * r) * x⁻¹ := by rw [hwr]
        _ = (x * w * x⁻¹) * (x * r * x⁻¹) := by group
        _ = w * (w * r) := by rw [hxwx, hwr]
        _ = (w * w) * r := (mul_assoc _ _ _).symm
        _ = r := by rw [hww w hw, one_mul]
    exact mul_inv_eq_iff_eq_mul.1 key
  have hx2z : x ^ 2 ∈ zpowers z := by
    obtain ⟨a, ha, h⟩ := hR1dec _ hx2
    have haz' := haz a ha (x ^ 2) h fun b hb => hx2c b (mem_sup_left hb)
    have hxx : x * x ^ 2 = x ^ 2 * x := by group
    rw [hs a haz' (x ^ 2) h hxx]
    exact haz'
  have hUdec : ∀ g ∈ R0 ⊔ zpowers t ⊔ zpowers x, ∃ r ∈ R0 ⊔ zpowers t, g = r ∨ g = r * x :=
    fun g hg => exists_eq_or_eq_mul_of_mem_sup_zpowers_of_sq hxN hx2 hg
  have hUsq : ∀ u ∈ R0 ⊔ zpowers t ⊔ zpowers x, u ^ 2 ∈ zpowers z := by
    intro u hu
    obtain ⟨r, hr, h | h⟩ := hUdec u hu
    · rw [h]
      exact hR1sq r hr
    · rw [h]
      obtain ⟨w, hw, hwr⟩ := hconj r hr
      have : (r * x) ^ 2 = w * r ^ 2 * x ^ 2 := by
        calc (r * x) ^ 2 = r * (x * r * x⁻¹) * x ^ 2 := by rw [sq (r * x)]; group
          _ = r * (w * r) * x ^ 2 := by rw [hwr]
          _ = (r * w) * r * x ^ 2 := by group
          _ = (w * r) * r * x ^ 2 := by rw [hwr_comm w hw r hr]
          _ = w * r ^ 2 * x ^ 2 := by
            rw [pow_two r]
            group
      rw [this]
      exact mul_mem (mul_mem hw (hR1sq r hr)) hx2z
  have hcent : ∀ c ∈ R0 ⊔ zpowers t ⊔ zpowers x,
      (∀ u ∈ R0 ⊔ zpowers t ⊔ zpowers x, c * u = u * c) → c ∈ zpowers z := by
    intro c hc hcc
    have hcx : c * x = x * c := hcc x (mem_sup_right (mem_zpowers x))
    have hct : c * t = t * c := hcc t (mem_sup_left htR1)
    have hcb : ∀ b ∈ R0, c * b = b * c := fun b hb => hcc b (mem_sup_left (mem_sup_left hb))
    obtain ⟨r, hr, hcr | hcr⟩ := hUdec c hc
    · obtain ⟨a, ha, har⟩ := hR1dec r hr
      have hc' : c = a ∨ c = a * t := by
        rw [hcr]
        exact har
      have haz' := haz a ha c hc' hcb
      rw [hs a haz' c hc' hcx.symm]
      exact haz'
    · exfalso
      apply hz1
      have hrt : r * t = t * r := mem_centralizer_singleton_iff.1 (htcR1 hr)
      rw [hcr] at hct
      have h1 : r * (t * z * x) = r * (t * x) := by
        calc r * (t * z * x) = r * (x * t) := by rw [hxt']
          _ = r * x * t := (mul_assoc _ _ _).symm
          _ = t * (r * x) := hct
          _ = t * r * x := (mul_assoc _ _ _).symm
          _ = r * t * x := by rw [hrt]
          _ = r * (t * x) := mul_assoc _ _ _
      simpa [mul_assoc] using mul_left_cancel h1
  have hcardR1 : Nat.card ↥(R0 ⊔ zpowers t) = 2 ^ 24 := by
    rw [card_sup_zpowers_of_orderOf_eq_two ht htn htR0, hcard]
    norm_num
  have hxU : x ∈ R0 ⊔ zpowers t ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  have hcardU : Nat.card ↥(R0 ⊔ zpowers t ⊔ zpowers x) = 2 ^ 25 := by
    have hR1U : R0 ⊔ zpowers t ≤ R0 ⊔ zpowers t ⊔ zpowers x := le_sup_left
    have hN : ((R0 ⊔ zpowers t).subgroupOf (R0 ⊔ zpowers t ⊔ zpowers x)).index = 2 := by
      rw [index_eq_two_iff]
      refine ⟨⟨x, hxU⟩, fun b => ?_⟩
      obtain ⟨r, hr, hb | hb⟩ := hUdec b b.2
      · refine Or.inr ⟨mem_subgroupOf.2 (hb ▸ hr), fun h => hxn ?_⟩
        have h' : (b : G) * x ∈ R0 ⊔ zpowers t := mem_subgroupOf.1 h
        rw [hb] at h'
        simpa using mul_mem (inv_mem hr) h'
      · refine Or.inl ⟨mem_subgroupOf.2 ?_, fun h => hxn ?_⟩
        · show (b : G) * x ∈ R0 ⊔ zpowers t
          rw [hb, mul_assoc, ← sq]
          exact mul_mem hr hx2
        · have h' : (b : G) ∈ R0 ⊔ zpowers t := mem_subgroupOf.1 h
          rw [hb] at h'
          simpa using mul_mem (inv_mem hr) h'
    have h := Subgroup.card_mul_index
      ((R0 ⊔ zpowers t).subgroupOf (R0 ⊔ zpowers t ⊔ zpowers x))
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR1U).toEquiv, hcardR1] at h
    omega
  have hzU : z ∈ R0 ⊔ zpowers t ⊔ zpowers x := mem_sup_left hzR1
  have hzcU : ∀ u ∈ R0 ⊔ zpowers t ⊔ zpowers x, u * z = z * u := fun u hu =>
    mem_centralizer_singleton_iff.1
      (sup_le hzcR1 (zpowers_le.2 (mem_centralizer_singleton_iff.2 hxz)) hu)
  have hnab : ∃ u ∈ R0 ⊔ zpowers t ⊔ zpowers x, u ∉ zpowers z := by
    refine ⟨t, mem_sup_left htR1, fun h => ?_⟩
    rcases eq_one_or_eq_of_mem_zpowers_two hz h with h | h
    · exact ht1 h
    · exact htzne h
  obtain ⟨hext, hcenter⟩ := isExtraspecialPGroup_of_sq_mem_zpowers hz hzU hzcU hUsq hcent hnab
  exact ⟨hext, hcardU, hcenter⟩

end CFSG.EvenSporadicStandard.TwoB
