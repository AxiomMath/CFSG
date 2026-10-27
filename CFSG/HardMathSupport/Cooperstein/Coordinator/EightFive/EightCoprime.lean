module

public import CFSG.Quasithin.Background.CommVCommute
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem inf_fixV_le_of_fixV_autSec_eq_bot {X : Subgroup (MulAut V)} {Y₀ Y₁ : Subgroup V}
    (h : fixV (autSec X Y₁ Y₀) = ⊥) : Y₁ ⊓ fixV X ≤ Y₀ := by
  rintro c ⟨hc1, hc⟩
  have hmem : (QuotientGroup.mk (⟨c, hc1⟩ : ↥Y₁) : Sec Y₁ Y₀) ∈
      fixV (autQuot (autSub X Y₁) (Y₀.subgroupOf Y₁)) := by
    refine mk_mem_fixV_autQuot.2 fun φ hφ _ => ?_
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
    have hgc : resHom Y₁ g ⟨c, hc1⟩ = ⟨c, hc1⟩ := Subtype.ext (hc g hg)
    rw [hgc, mul_inv_cancel]
    exact Subgroup.one_mem _
  change _ ∈ fixV (autSec X Y₁ Y₀) at hmem
  rw [h, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

theorem pow_odd_eq_self (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : Odd m) (v : V) : v ^ m = v := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, hV v, one_pow, one_mul]

theorem odd_card_autSub {X : Subgroup (MulAut V)} (hX : Odd (Nat.card X)) {W : Subgroup V}
    (hXW : X ≤ stabSub W) : Odd (Nat.card (autSub X W)) :=
  Odd.of_dvd_nat hX (Dvd.intro _ (card_autSub_mul hXW))

theorem odd_card_zpowers {x : MulAut V} {m : ℕ} (hm : Odd m) (hx : x ^ m = 1) :
    Odd (Nat.card (Subgroup.zpowers x)) := by
  rw [Nat.card_zpowers]
  exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hx)

theorem odd_card_zpowers_of_pow_three {x : MulAut V} (hx : x ^ 3 = 1) :
    Odd (Nat.card (Subgroup.zpowers x)) :=
  odd_card_zpowers (by decide) hx

variable [Finite V]

theorem map_mk_fixV_eq_fixV_autQuot (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA : Odd (Nat.card A)) {U : Subgroup V} (hAU : A ≤ stabSub U) :
    (fixV A).map (QuotientGroup.mk' U) = fixV (autQuot A U) := by
  refine le_antisymm ?_ fun q hq => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact mk_mem_fixV_autQuot.2 fun g hg _ => by
      show (g v * v⁻¹ : V) ∈ U
      rw [hv g hg, mul_inv_cancel]
      exact U.one_mem
  · obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    have hv := mk_mem_fixV_autQuot.1 hq
    refine ⟨avgMap A v, avgMap_mem_fixV A v, ?_⟩
    change (QuotientGroup.mk (avgMap A v) : V ⧸ U) = QuotientGroup.mk v
    rw [mk_eq_mk_iff]
    have := Fintype.ofFinite A
    have h1 : avgMap A v * v⁻¹ = ∏ g : A, ((g : MulAut V) v * v⁻¹) := by
      rw [avgMap_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, pow_odd_eq_self hV hA]
    rw [h1]
    exact U.prod_mem fun g _ => hv g g.2 (hAU g.2)

theorem card_fixV_eq_autQuot_mul (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA : Odd (Nat.card A)) {U : Subgroup V} (hAU : A ≤ stabSub U) :
    Nat.card (fixV A) = Nat.card (fixV (autQuot A U)) * Nat.card ↥(U ⊓ fixV A) := by
  have h1 := B1More.card_map_mul_card_inf_ker (fixV A) (QuotientGroup.mk' U)
  rw [map_mk_fixV_eq_fixV_autQuot hV hA hAU, QuotientGroup.ker_mk', inf_comm] at h1
  exact h1.symm

theorem card_inf_fixV_eq_autSec_mul (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hX : Odd (Nat.card X)) {Y₀ Y₁ : Subgroup V} (hY : Y₀ ≤ Y₁) (hX₀ : X ≤ stabSub Y₀)
    (hX₁ : X ≤ stabSub Y₁) :
    Nat.card ↥(Y₁ ⊓ fixV X) = Nat.card (fixV (autSec X Y₁ Y₀)) * Nat.card ↥(Y₀ ⊓ fixV X) := by
  have h1 := card_fixV_eq_autQuot_mul (B1.sq_eq_one_sub hV Y₁) (odd_card_autSub hX hX₁)
    (autSub_le_stabSub_subgroupOf (W := Y₁) hX₀)
  have h2 : Nat.card (fixV (autSub X Y₁)) = Nat.card ↥(Y₁ ⊓ fixV X) := by
    rw [← map_subtype_fixV_autSub hX₁, Subgroup.card_map_of_injective Y₁.subtype_injective]
  have h3 : Nat.card ↥(Y₀.subgroupOf Y₁ ⊓ fixV (autSub X Y₁)) = Nat.card ↥(Y₀ ⊓ fixV X) := by
    have h4 : (Y₀.subgroupOf Y₁ ⊓ fixV (autSub X Y₁)).map Y₁.subtype = Y₀ ⊓ fixV X := by
      rw [Subgroup.map_inf _ _ _ Y₁.subtype_injective, map_subtype_fixV_autSub hX₁,
        Subgroup.map_subgroupOf_eq_of_le hY, ← inf_assoc, inf_eq_left.2 hY]
    rw [← h4, Subgroup.card_map_of_injective Y₁.subtype_injective]
  rw [h2, h3] at h1
  exact h1

theorem fixV_autSec_eq_bot_iff (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hX : Odd (Nat.card X)) {Y₀ Y₁ : Subgroup V} (hY : Y₀ ≤ Y₁) (hX₀ : X ≤ stabSub Y₀)
    (hX₁ : X ≤ stabSub Y₁) : fixV (autSec X Y₁ Y₀) = ⊥ ↔ Y₁ ⊓ fixV X ≤ Y₀ := by
  refine ⟨inf_fixV_le_of_fixV_autSec_eq_bot, fun h => ?_⟩
  have h1 := card_inf_fixV_eq_autSec_mul hV hX hY hX₀ hX₁
  have h2 : Y₁ ⊓ fixV X = Y₀ ⊓ fixV X :=
    le_antisymm (le_inf h inf_le_right) (inf_le_inf_right _ hY)
  rw [h2] at h1
  have h3 : Nat.card (fixV (autSec X Y₁ Y₀)) = 1 := by
    have hpos : 0 < Nat.card ↥(Y₀ ⊓ fixV X) := Nat.card_pos
    have h4 : 1 * Nat.card ↥(Y₀ ⊓ fixV X) =
        Nat.card (fixV (autSec X Y₁ Y₀)) * Nat.card ↥(Y₀ ⊓ fixV X) := by rw [one_mul]; exact h1
    exact (Nat.eq_of_mul_eq_mul_right hpos h4).symm
  exact Subgroup.card_eq_one.1 h3

theorem fixV_sup_commV_eq_top (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hX : Odd (Nat.card X)) : fixV X ⊔ commV X = ⊤ := by
  have h := (coprime_decomp hX hV (W := ⊤) fun _ _ _ _ => Subgroup.mem_top _).1
  rw [top_inf_eq, ← commV_eq_commSub] at h
  rw [sup_comm, h]

theorem fixV_inf_commV_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hX : Odd (Nat.card X)) : fixV X ⊓ commV X = ⊥ := by
  have h := (coprime_decomp hX hV (W := ⊤) fun _ _ _ _ => Subgroup.mem_top _).2
  rw [top_inf_eq, ← commV_eq_commSub] at h
  rw [inf_comm, h]

theorem fixV_sup_commV_zpowers_eq_top (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hx : x ^ 3 = 1) : fixV (Subgroup.zpowers x) ⊔ commV (Subgroup.zpowers x) = ⊤ :=
  fixV_sup_commV_eq_top hV (odd_card_zpowers_of_pow_three hx)

theorem fixV_inf_commV_zpowers_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hx : x ^ 3 = 1) : fixV (Subgroup.zpowers x) ⊓ commV (Subgroup.zpowers x) = ⊥ :=
  fixV_inf_commV_eq_bot hV (odd_card_zpowers_of_pow_three hx)

theorem apply_mem_commV_zpowers_of_commute {x g : MulAut V} (hgx : g * x = x * g)
    {w : V} (hw : w ∈ commV (Subgroup.zpowers x)) : g w ∈ commV (Subgroup.zpowers x) :=
  CFSG.Quasithin.apply_mem_commV_zpowers_of_commute hgx hw

theorem commV_zpowers_le_of_commute (hV : ∀ v : V, v ^ 2 = 1) {x z : MulAut V}
    (hx : Odd (Nat.card (Subgroup.zpowers x))) (hz : Odd (Nat.card (Subgroup.zpowers z)))
    (hxz : x * z = z * x) (hfix : fixV (Subgroup.zpowers z) ≤ fixV (Subgroup.zpowers x)) :
    commV (Subgroup.zpowers x) ≤ commV (Subgroup.zpowers z) := by
  set W := commV (Subgroup.zpowers x) with hWdef
  have hW : ∀ g ∈ Subgroup.zpowers z, ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact apply_mem_commV_zpowers_of_commute (Commute.zpow_left hxz.symm k).eq hw
  obtain ⟨hsup, -⟩ := coprime_decomp hz hV hW
  have hbot : W ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
    rw [eq_bot_iff, ← fixV_inf_commV_eq_bot hV hx, inf_comm]
    exact inf_le_inf_right _ hfix
  rw [hbot, sup_bot_eq] at hsup
  rw [← hsup, commV_eq_commSub]
  exact commSub_mono le_top le_rfl

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
