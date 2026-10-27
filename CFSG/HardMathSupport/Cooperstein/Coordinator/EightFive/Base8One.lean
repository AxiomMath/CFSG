module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Fac
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Bookkeeping
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Shape

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

theorem exists_isChiefFac_above_of_perfect {V : Type*} [CommGroup V] [Finite V]
    {H L : Subgroup (MulAut V)} (hL : commutator ↥L = ⊤) (hLH : L ≤ H) {Y : Subgroup V}
    (hY : H ≤ stabSub Y) (hYL : ¬ IsCentralSec L Y ⊤) :
    ∃ Z₀ Z₁ : Subgroup V, IsChiefFac H Z₀ Z₁ ∧ Y ≤ Z₀ ∧ ¬ IsCentralSec L Z₀ Z₁ := by
  have := finite_subgroup (V := V)
  have htop : H ≤ stabSub (⊤ : Subgroup V) := fun _ _ _ => by simp only [Subgroup.mem_top]
  obtain ⟨Z₁, ⟨hZ₁, hYZ₁, hZ₁L⟩, hmin⟩ := Set.exists_min_image
    {Z : Subgroup V | H ≤ stabSub Z ∧ Y ≤ Z ∧ ¬ IsCentralSec L Y Z} (fun Z => Nat.card Z)
    (Set.toFinite _) ⟨⊤, htop, le_top, hYL⟩
  have hlt : Y < Z₁ := by
    refine lt_of_le_of_ne hYZ₁ fun h => hZ₁L ?_
    rw [← h]
    intro l hl y hy
    exact Y.mul_mem ((hY (hLH hl) y).2 hy) (Y.inv_mem hy)
  obtain ⟨Z₀, hYZ₀, hchief⟩ := exists_isChiefFac_of_lt hlt hY hZ₁
  refine ⟨Z₀, Z₁, hchief, hYZ₀, fun hc => hZ₁L ?_⟩
  have hZ₀ : IsCentralSec L Y Z₀ := by
    by_contra hZ₀L
    have hcard := hmin Z₀ ⟨hchief.stab₀, hYZ₀, hZ₀L⟩
    exact hchief.lt.ne (Subgroup.eq_of_le_of_card_ge hchief.le hcard)
  exact hZ₀.trans_of_perfect hL hc

theorem sixteen_le_card_of_isMatchingGroup {B : Subgroup (Perm (Fin 8))}
    (h : IsMatchingGroup B) : 16 ≤ Nat.card B := by
  obtain ⟨t, ht, ht2, rfl⟩ := h
  have h1 := card_FixP_le_card_matchingGroup ht ht2
  rw [card_FixP_eq] at h1
  have h2 := card_eq_two_mul_card_orb (card_orbit_matchingGroup ht ht2)
  rw [Nat.card_fin] at h2
  have h3 : Nat.card (Orb (matchingGroup t)) = 4 := by omega
  rw [h3] at h1
  exact h1

theorem exists_not_mem_alternatingGroup_of_isMatchingGroup {B : Subgroup (Perm (Fin 8))}
    (h : IsMatchingGroup B) : ∃ b ∈ B, b ∉ alternatingGroup (Fin 8) := by
  obtain ⟨t, ht, ht2, rfl⟩ := h
  refine ⟨swap 0 (t 0), swap_mem_matchingGroup 0, fun hmem => ?_⟩
  rw [Perm.mem_alternatingGroup, Perm.sign_swap (Ne.symm (ht 0))] at hmem
  exact absurd hmem (by decide)

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 8)}

omit [Finite V] in
theorem not_le_altPre_of_isMatchingGroup {A : Subgroup (MulAut V)}
    (h : IsMatchingGroup ((A.subgroupOf H).map ψ)) : ¬ A ≤ altPre ψ := by
  obtain ⟨_, ⟨x, hx, rfl⟩, hb⟩ := exists_not_mem_alternatingGroup_of_isMatchingGroup h
  intro hAL
  exact hb (coe_mem_altPre_iff.1 (hAL (Subgroup.mem_subgroupOf.1 hx)))

theorem NatSec.card_le_index {Y₀ Y₁ : Subgroup V} (hN : NatSec ψ Y₀ Y₁)
    (hψ : Function.Injective ψ) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    {B : Subgroup (MulAut V)} (hBH : B ≤ H) (hel : IsElemAbelian2 B)
    (hΔ : ¬ IsMatchingGroup ((B.subgroupOf H).map ψ)) :
    Nat.card B ≤ (fixV (autSec B Y₁ Y₀)).index := by
  have h := hN.card_mul_card_fixV_le (by norm_num) hψ hH₀ hH₁ hBH hel hΔ
  rw [← (fixV (autSec B Y₁ Y₀)).index_mul_card] at h
  exact Nat.le_of_mul_le_mul_right h Nat.card_pos

theorem NatSec.two_mul_index_eq {Y₀ Y₁ : Subgroup V} (hN : NatSec ψ Y₀ Y₁)
    (hψ : Function.Injective ψ) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    {B : Subgroup (MulAut V)} (hBH : B ≤ H) (hΔ : IsMatchingGroup ((B.subgroupOf H).map ψ)) :
    2 * (fixV (autSec B Y₁ Y₀)).index = Nat.card B := by
  have h := hN.card_mul_card_fixV_eq (by norm_num) hψ hH₀ hH₁ hBH hΔ
  rw [← (fixV (autSec B Y₁ Y₀)).index_mul_card, ← mul_assoc] at h
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm

theorem three_le_index_of_matching (hB42 : B42L42Core) (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 8) ≤ ψ.range)
    {A : Subgroup (MulAut V)} (hAoff : IsFFStarOffender H A) {Z₀ Z₁ : Subgroup V}
    (hZ : IsChiefFac H Z₀ Z₁) (hZL : ¬ IsCentralSec (altPre ψ) Z₀ Z₁)
    (hΔ : IsMatchingGroup ((A.subgroupOf H).map ψ)) : 3 ≤ (fixV (autSec A Z₁ Z₀)).index := by
  have hAL := not_le_altPre_of_isMatchingGroup hΔ
  rcases chief_cases hB42 hV hψ hA hAoff hZ hZL with ⟨-, hLH⟩ | hN | ⟨Y', g, hS, h16, -⟩
  · exact absurd (by rw [hLH]; exact hAoff.1) hAL
  · have h1 := hN.two_mul_index_eq hψ hZ.stab₀ hZ.stab₁ hAoff.1 hΔ
    have h2 := sixteen_le_card_of_isMatchingGroup hΔ
    rw [card_map_subgroupOf hψ hAoff.1] at h2
    omega
  · obtain ⟨a, haA, haL⟩ := Set.not_subset.1 hAL
    have h1 := card_sec_le_index_of_swap hS.le₀ hS.le₁ (hAoff.1.trans hZ.stab₀)
      (hAoff.1.trans hZ.stab₁) haA (hS.swap a (hAoff.1 haA) haL)
    omega

theorem false_of_natSec_of_chief (hB42 : B42L42Core) (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 8) ≤ ψ.range)
    {A : Subgroup (MulAut V)} (hAoff : IsFFStarOffender H A) {Y₀ Y₁ Z₀ Z₁ : Subgroup V}
    (hY : IsChiefFac H Y₀ Y₁) (hN : NatSec ψ Y₀ Y₁) (hZ : IsChiefFac H Z₀ Z₁)
    (hZL : ¬ IsCentralSec (altPre ψ) Z₀ Z₁)
    (hprod : (fixV (autSec A Y₁ Y₀)).index * (fixV (autSec A Z₁ Z₀)).index ≤ Nat.card A) :
    False := by
  have hF2 : 1 < (fixV (autSec A Z₁ Z₀)).index :=
    one_lt_index_fixV_autSec (by norm_num) hψ hA hZ.stab₀ hZ.stab₁ hZL hAoff.1 hAoff.2.1
  have hXpos : 0 < (fixV (autSec A Y₁ Y₀)).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  by_cases hΔ : IsMatchingGroup ((A.subgroupOf H).map ψ)
  · have h1 := hN.two_mul_index_eq hψ hY.stab₀ hY.stab₁ hAoff.1 hΔ
    have h3 := three_le_index_of_matching hB42 hV hψ hA hAoff hZ hZL hΔ
    have h4 := Nat.mul_le_mul_left (fixV (autSec A Y₁ Y₀)).index h3
    omega
  · have h1 := hN.card_le_index hψ hY.stab₀ hY.stab₁ hAoff.1 hAoff.2.2.1 hΔ
    have h4 := Nat.mul_le_mul h1 hF2
    have hpos : 0 < Nat.card A := Nat.card_pos
    omega

theorem natVia_of_natSec (hB42 : B42L42Core) (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 8) ≤ ψ.range)
    {A : Subgroup (MulAut V)} (hAoff : IsFFStarOffender H A) {Y₀ Y₁ : Subgroup V}
    (hY : IsChiefFac H Y₀ Y₁) (hN : NatSec ψ Y₀ Y₁) : NatVia ψ (commV H) := by
  set L := altPre ψ with hLdef
  have hperf := commutator_altPre_eq_top (by norm_num) hψ hA
  have h₀ : Y₀ ≤ fixV L := by
    by_contra hc
    obtain ⟨Z₀, Z₁, hZ, hZY, hZL⟩ := exists_isChiefFac_altPre (by norm_num) hψ hA hY.stab₀ hc
    refine false_of_natSec_of_chief hB42 hV hψ hA hAoff hY hN hZ hZL ?_
    rw [mul_comm]
    exact index_mul_index_le hAoff hZ.le hZY hY.le (hAoff.1.trans hZ.stab₁)
      (hAoff.1.trans hY.stab₁)
  have h₁ : IsCentralSec L Y₁ ⊤ := by
    by_contra hc
    obtain ⟨Z₀, Z₁, hZ, hYZ, hZL⟩ :=
      exists_isChiefFac_above_of_perfect hperf altPre_le hY.stab₁ hc
    exact false_of_natSec_of_chief hB42 hV hψ hA hAoff hY hN hZ hZL
      (index_mul_index_le hAoff hY.le hYZ hZ.le (hAoff.1.trans hY.stab₁)
        (hAoff.1.trans hZ.stab₁))
  obtain ⟨π, hπ, hker, heq⟩ := hN
  have hshape : NatShape L.subtype ((alternatingGroup (Fin 8)).subtype.comp (altPreHom ψ)) :=
    ⟨Y₀, Y₁, hY.le, fun l v hv => h₀ hv l l.2, fun l v => h₁ l l.2 v (Subgroup.mem_top v), π,
      hπ, hker, fun l u v huv => heq (Subgroup.inclusion altPre_le l) u v huv⟩
  have hnat := isAltNaturalSection_of_natShape (by norm_num) L (altPreHom ψ)
    (altPreHom_surjective hA) hshape
  exact (natVia_commV_of_isAltNaturalSection (by norm_num) hψ hA hnat).2

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
