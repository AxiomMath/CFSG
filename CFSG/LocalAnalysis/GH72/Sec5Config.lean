module

public import CFSG.LocalAnalysis.GH72.Sec5Roles
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.GH72.Sec4Bar
public import CFSG.LocalAnalysis.GH72.Sec5Tools

public section

namespace CFSG.GH72

open Subgroup
open scoped commutatorElement Pointwise

theorem exists_eq_zpowers_sup_zpowers {G : Type} [Group G] {X : Subgroup G} (hX : IsKleinFour X) :
    ∃ x ∈ X, ∃ x' ∈ X, orderOf x = 2 ∧ orderOf x' = 2 ∧ x * x' = x' * x ∧ x' ∉ zpowers x ∧
      zpowers x ⊔ zpowers x' = X := by
  have := hX
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX.card_four]; norm_num)
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.1 (by rw [hX.card_four]; norm_num)
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : X)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨x', hx', hx'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hX hx hx1'
  have hx'1 : x' ≠ 1 := fun h => hx'z (h ▸ one_mem _)
  have hc : x * x' = x' * x := by
    have h1 := mul_self_eq_one_of_isKleinFour hX (mul_mem hx hx')
    have h2 := mul_self_eq_one_of_isKleinFour hX hx
    have h3 := mul_self_eq_one_of_isKleinFour hX hx'
    calc x * x' = (x * x')⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = x'⁻¹ * x⁻¹ := mul_inv_rev _ _
      _ = x' * x := by rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]
  refine ⟨x, hx, x', hx', orderOf_eq_two_of_isKleinFour hX hx hx1',
    orderOf_eq_two_of_isKleinFour hX hx' hx'1, hc, hx'z, ?_⟩
  refine le_antisymm (sup_le (zpowers_le.mpr hx) (zpowers_le.mpr hx')) ?_
  intro z hz
  by_cases hzz : z ∈ zpowers x
  · exact mem_sup_left hzz
  · rcases eq_or_eq_mul_of_not_mem_zpowers hX hx hx1' hx' hx'z hz hzz with rfl | rfl
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem exists_zpowers_sup_zpowers_eq_of_mem {G : Type} [Group G] {X : Subgroup G}
    (hX : IsKleinFour X) {x : G} (hx : x ∈ X) (hx1 : x ≠ 1) :
    ∃ x' ∈ X, orderOf x' = 2 ∧ x * x' = x' * x ∧ x' ∉ zpowers x ∧ zpowers x ⊔ zpowers x' = X := by
  obtain ⟨x', hx', hx'z⟩ := exists_mem_not_mem_zpowers_of_isKleinFour hX hx hx1
  have hx'1 : x' ≠ 1 := fun h => hx'z (h ▸ one_mem _)
  have hc : x * x' = x' * x := by
    have h1 := mul_self_eq_one_of_isKleinFour hX (mul_mem hx hx')
    have h2 := mul_self_eq_one_of_isKleinFour hX hx
    have h3 := mul_self_eq_one_of_isKleinFour hX hx'
    calc x * x' = (x * x')⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = x'⁻¹ * x⁻¹ := mul_inv_rev _ _
      _ = x' * x := by rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]
  refine ⟨x', hx', orderOf_eq_two_of_isKleinFour hX hx' hx'1, hc, hx'z, ?_⟩
  refine le_antisymm (sup_le (zpowers_le.mpr hx) (zpowers_le.mpr hx')) ?_
  intro z hz
  by_cases hzz : z ∈ zpowers x
  · exact mem_sup_left hzz
  · rcases eq_or_eq_mul_of_not_mem_zpowers hX hx hx1 hx' hx'z hz hzz with rfl | rfl
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem mem_centralizer_of_commute_of_eq_sup {G : Type} [Group G] {X : Subgroup G} {x x' g : G}
    (hX : zpowers x ⊔ zpowers x' = X) (hgx : g ∈ C x) (hgx' : g ∈ C x') :
    g ∈ centralizer (X : Set G) := by
  have hle : X ≤ C g := by
    rw [← hX]
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff] at hgx ⊢
      exact hgx.symm
    · rw [mem_centralizer_singleton_iff] at hgx' ⊢
      exact hgx'.symm
  rw [mem_centralizer_iff]
  intro h hh
  exact (mem_centralizer_singleton_iff.mp (hle hh))

theorem zpowers_sup_zpowers_eq_of_not_mem {G : Type} [Group G] {X : Subgroup G}
    (hX : IsKleinFour X) {x x' : G} (hx : x ∈ X) (hx1 : x ≠ 1) (hx' : x' ∈ X)
    (hx'z : x' ∉ zpowers x) : zpowers x ⊔ zpowers x' = X := by
  refine le_antisymm (sup_le (zpowers_le.mpr hx) (zpowers_le.mpr hx')) ?_
  intro z hz
  by_cases hzz : z ∈ zpowers x
  · exact mem_sup_left hzz
  · rcases eq_or_eq_mul_of_not_mem_zpowers hX hx hx1 hx' hx'z hz hzz with rfl | rfl
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem mul_comm_of_isKleinFour {G : Type} [Group G] {X : Subgroup G} (hX : IsKleinFour X)
    {a b : G} (ha : a ∈ X) (hb : b ∈ X) : a * b = b * a := by
  have h1 := mul_self_eq_one_of_isKleinFour hX (mul_mem ha hb)
  have h2 := mul_self_eq_one_of_isKleinFour hX ha
  have h3 := mul_self_eq_one_of_isKleinFour hX hb
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]

theorem commutator_commutator_eq_of_isKleinFour {G : Type} [Group G] {B T : Subgroup G}
    (hB : IsKleinFour B) (hT : Odd (Nat.card T)) (hBT : B ≤ normalizer (T : Set G)) :
    ⁅⁅T, B⁆, B⁆ = ⁅T, B⁆ := by
  obtain ⟨x, hx, x', hx', hxo, hx'o, -, -, hBeq⟩ := exists_eq_zpowers_sup_zpowers hB
  have hBE : B ≤ normalizer ((⁅T, B⁆ : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_commutator (hBT hy) (le_normalizer hy)
  refine le_antisymm (commutator_le_left_of_le_normalizer hBE) ?_
  calc ⁅T, B⁆ = ⁅T, zpowers x ⊔ zpowers x'⁆ := by rw [hBeq]
    _ = ⁅T, zpowers x⁆ ⊔ ⁅T, zpowers x'⁆ :=
      commutator_sup_eq_of_le_normalizer (zpowers_le.mpr (hBT hx)) (zpowers_le.mpr (hBT hx'))
    _ = ⁅⁅T, zpowers x⁆, zpowers x⁆ ⊔ ⁅⁅T, zpowers x'⁆, zpowers x'⁆ := by
      rw [commutator_commutator_zpowers_eq hT hxo (hBT hx),
        commutator_commutator_zpowers_eq hT hx'o (hBT hx')]
    _ ≤ ⁅⁅T, B⁆, B⁆ :=
      sup_le (commutator_mono (commutator_mono le_rfl (hBeq ▸ le_sup_left)) (hBeq ▸ le_sup_left))
        (commutator_mono (commutator_mono le_rfl (hBeq ▸ le_sup_right)) (hBeq ▸ le_sup_right))

theorem le_of_forall_inf_C_le_of_isKleinFour {G : Type} [Group G] [Finite G] {B V W : Subgroup G}
    (hB : IsKleinFour B) (hV : Odd (Nat.card V)) (hBV : B ≤ normalizer (V : Set G))
    (hle : ∀ b ∈ B, b ≠ 1 → V ⊓ C b ≤ W) : V ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 B :=
    { is_comm := ⟨fun a b => Subtype.ext (mul_comm_of_isKleinFour hB a.2 b.2)⟩
      exponent_dvd_p := by rw [hB.exponent_two] }
  let : MulDistribMulAction B V := Subgroup.conjMulDistribMulActionOfLeNormalizer B V hBV
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := B) (H := V)
    (by rw [hB.card_four]; norm_num)
    (fun h => (Nat.not_even_iff_odd.mpr hV) (even_iff_two_dvd.mpr h))
  have hle' : (⨆ (a : B) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) ≤
      W.comap V.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro v hv
    have hfix : a • v = v := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a v).mp hv
    have hc : (a : G) * v * (a : G)⁻¹ = v := congrArg Subtype.val hfix
    have hcomm : (v : G) ∈ C (a : G) := by
      rw [mem_centralizer_singleton_iff]
      calc (v : G) * a = a * v * (a : G)⁻¹ * a := by rw [hc]
        _ = a * v := by group
    exact hle a a.2 (fun h => ha (Subtype.ext h)) ⟨v.2, hcomm⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : V) ∈
      (⨆ (a : B) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) := by
    rw [hgen]
    exact mem_top _
  exact hle' hmem

section FixedPointFree

variable {G : Type} [Group G] {Y : Subgroup G} (hY : IsKleinFour Y) {u : G}
  (hu : u ∈ normalizer (Y : Set G)) (hfix : ∀ y ∈ Y, y ≠ 1 → u * y * u⁻¹ ≠ y)
include hY hu hfix

theorem conj_conj_eq_mul_of_fixedPointFree {y : G} (hyY : y ∈ Y) (hy1 : y ≠ 1) :
    u * (u * y * u⁻¹) * u⁻¹ = y * (u * y * u⁻¹) := by
  have hy₂ : u * y * u⁻¹ ∈ Y := (mem_normalizer_iff.mp hu y).mp hyY
  have hy₂1 : u * y * u⁻¹ ≠ 1 := fun h => hy1 (by
    have := congrArg (fun z => u⁻¹ * z * u) h
    simpa [mul_assoc] using this)
  have hy₃ : u * (u * y * u⁻¹) * u⁻¹ ∈ Y := (mem_normalizer_iff.mp hu _).mp hy₂
  have hy₂z : u * y * u⁻¹ ∉ zpowers y := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers (orderOf_eq_two_of_isKleinFour hY hyY hy1) h with h | h
    · exact hy₂1 h
    · exact hfix y hyY hy1 h
  have hy₃z : u * (u * y * u⁻¹) * u⁻¹ ∉ zpowers y := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers (orderOf_eq_two_of_isKleinFour hY hyY hy1) h with h | h
    · exact hy₂1 (by
        have := congrArg (fun z => u⁻¹ * z * u) h
        simpa [mul_assoc] using this)
    ·
      have hmul : y * (u * y * u⁻¹) ∈ Y := mul_mem hyY hy₂
      have hmul1 : y * (u * y * u⁻¹) ≠ 1 := fun h' => hfix y hyY hy1 (by
        rw [eq_inv_of_mul_eq_one_right h',
          inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_isKleinFour hY hyY)])
      refine hfix _ hmul hmul1 ?_
      calc u * (y * (u * y * u⁻¹)) * u⁻¹ = (u * y * u⁻¹) * (u * (u * y * u⁻¹) * u⁻¹) := by group
        _ = (u * y * u⁻¹) * y := by rw [h]
        _ = y * (u * y * u⁻¹) := mul_comm_of_isKleinFour hY hy₂ hyY
  rcases eq_or_eq_mul_of_not_mem_zpowers hY hyY hy1 hy₂ hy₂z hy₃ hy₃z with h | h
  · exact absurd (h.trans (by rfl)) (by
      intro h'
      exact hfix _ hy₂ hy₂1 h)
  · exact h

theorem pow_three_conj_eq_of_fixedPointFree {y : G} (hyY : y ∈ Y) :
    u ^ 3 * y * (u ^ 3)⁻¹ = y := by
  by_cases hy1 : y = 1
  · rw [hy1]; group
  have hy₂ : u * y * u⁻¹ ∈ Y := (mem_normalizer_iff.mp hu y).mp hyY
  have hy₂1 : u * y * u⁻¹ ≠ 1 := fun h => hy1 (by
    have := congrArg (fun z => u⁻¹ * z * u) h
    simpa [mul_assoc] using this)
  have h3 := conj_conj_eq_mul_of_fixedPointFree hY hu hfix hyY hy1
  have h3' := conj_conj_eq_mul_of_fixedPointFree hY hu hfix hy₂ hy₂1
  have hc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb =>
    mul_comm_of_isKleinFour hY ha hb
  have hsq : ∀ a ∈ Y, a * a = 1 := fun a ha => mul_self_eq_one_of_isKleinFour hY ha
  calc u ^ 3 * y * (u ^ 3)⁻¹ = u * (u * (u * y * u⁻¹) * u⁻¹) * u⁻¹ := by rw [pow_three]; group
    _ = u * (y * (u * y * u⁻¹)) * u⁻¹ := by rw [h3]
    _ = (u * y * u⁻¹) * (u * (u * y * u⁻¹) * u⁻¹) := by group
    _ = (u * y * u⁻¹) * (y * (u * y * u⁻¹)) := by rw [h3]
    _ = y * ((u * y * u⁻¹) * (u * y * u⁻¹)) := by
      rw [← mul_assoc, hc _ hy₂ y hyY, mul_assoc]
    _ = y := by rw [hsq _ hy₂, mul_one]

theorem pow_conj_ne_of_fixedPointFree {r : ℕ} (hr : ¬ 3 ∣ r) {y : G} (hyY : y ∈ Y)
    (hy1 : y ≠ 1) : u ^ r * y * (u ^ r)⁻¹ ≠ y := by
  have h3 : ∀ q : ℕ, ∀ z ∈ Y, u ^ (3 * q) * z * (u ^ (3 * q))⁻¹ = z := by
    intro q
    induction q with
    | zero => intro z _; simp
    | succ q ih =>
      intro z hz
      rw [show 3 * (q + 1) = 3 * q + 3 by ring, pow_add]
      calc u ^ (3 * q) * u ^ 3 * z * (u ^ (3 * q) * u ^ 3)⁻¹ =
          u ^ (3 * q) * (u ^ 3 * z * (u ^ 3)⁻¹) * (u ^ (3 * q))⁻¹ := by group
        _ = z := by rw [pow_three_conj_eq_of_fixedPointFree hY hu hfix hz, ih z hz]
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 3 ∧ r = 3 * q + s :=
    ⟨r / 3, r % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod r 3).symm⟩
  have hs0 : s ≠ 0 := fun h => hr (by rw [h, add_zero]; exact dvd_mul_right 3 q)
  have hsY : u ^ s * y * (u ^ s)⁻¹ ∈ Y := by
    have : u ^ s ∈ normalizer (Y : Set G) := pow_mem hu s
    exact (mem_normalizer_iff.mp this y).mp hyY
  rw [pow_add]
  have e : u ^ (3 * q) * u ^ s * y * (u ^ (3 * q) * u ^ s)⁻¹ =
      u ^ (3 * q) * (u ^ s * y * (u ^ s)⁻¹) * (u ^ (3 * q))⁻¹ := by group
  rw [e, h3 q _ hsY]
  interval_cases s
  · exact absurd rfl hs0
  · rw [pow_one]
    exact hfix y hyY hy1
  ·
    intro h
    have h2 := conj_conj_eq_mul_of_fixedPointFree hY hu hfix hyY hy1
    have e2 : u ^ 2 * y * (u ^ 2)⁻¹ = u * (u * y * u⁻¹) * u⁻¹ := by rw [sq]; group
    rw [e2, h2] at h
    have hy₂1 : u * y * u⁻¹ = 1 := by
      calc u * y * u⁻¹ = y⁻¹ * (y * (u * y * u⁻¹)) := by group
        _ = 1 := by rw [h, inv_mul_cancel]
    exact hy1 (by
      have := congrArg (fun z => u⁻¹ * z * u) hy₂1
      simpa [mul_assoc] using this)

end FixedPointFree

theorem O_inf_normalizer_le_O {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf p R (O H)) :
    O (H ⊓ normalizer (R : Set G)) ≤ O H := by
  have hKH : H ⊓ normalizer (R : Set G) ≤ H := inf_le_left
  have hfr := le_inf_normalizer_sup_of_isSylowOf hR (O_le H) (le_normalizer_O H)
  have hOKH : O (H ⊓ normalizer (R : Set G)) ≤ H := (O_le _).trans hKH
  have hMH : O (H ⊓ normalizer (R : Set G)) ⊔ O H ≤ H := sup_le hOKH (O_le H)
  have hKM : H ⊓ normalizer (R : Set G) ≤
      normalizer ((O (H ⊓ normalizer (R : Set G)) ⊔ O H : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_sup_of_mem (le_normalizer_O _ hk) (le_normalizer_O H (hKH hk))
  have hOM : O H ≤ normalizer ((O (H ⊓ normalizer (R : Set G)) ⊔ O H : Subgroup G) : Set G) := by
    intro o ho
    have hle : (O (H ⊓ normalizer (R : Set G)) ⊔ O H).map (MulAut.conj o).toMonoidHom ≤
        O (H ⊓ normalizer (R : Set G)) ⊔ O H := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ (le_sup_right.trans'
        (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_O H (O_le H ho))).le)
      rintro _ ⟨x, hx, rfl⟩
      change o * x * o⁻¹ ∈ O (H ⊓ normalizer (R : Set G)) ⊔ O H
      have e : o * x * o⁻¹ = x * (x⁻¹ * o * x * o⁻¹) := by group
      rw [e]
      refine mul_mem (mem_sup_left hx) (mem_sup_right ?_)
      have h1 : x⁻¹ * o * x ∈ O H := by
        have := (mem_normalizer_iff.mp (le_normalizer_O H (hOKH (inv_mem hx))) o).mp ho
        simpa using this
      exact mul_mem h1 (inv_mem ho)
    rw [mem_normalizer_iff_map_conj_eq]
    exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj o).injective])
  have hHM := hfr.trans (sup_le hKM hOM)
  have hodd : Odd (Nat.card (O (H ⊓ normalizer (R : Set G)) ⊔ O H : Subgroup G)) := by
    have h1 := relIndex_mul_card (H := O H) (K := O (H ⊓ normalizer (R : Set G)) ⊔ O H)
    rw [inf_of_le_left (le_sup_right : O H ≤ O (H ⊓ normalizer (R : Set G)) ⊔ O H)] at h1
    rw [← h1, ABGTheoremB.relIndex_sup_right_of_le_normalizer
      (fun x hx => le_normalizer_O H (hOKH hx))]
    exact (Odd.of_dvd_nat (odd_natCard_O _) (relIndex_dvd_card _ _)).mul (odd_natCard_O H)
  exact le_sup_left.trans (le_O_of_le_normalizer_of_odd hMH hHM hodd)

theorem center_eq_bot_of_isSimpleGroup_of_isKleinFour {X : Type} [Group X] [Finite X]
    {J V : Subgroup X} [IsSimpleGroup J] (hV : IsKleinFour V) (hVJ : V ≤ J) : center J = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center J) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : J, a * b = b * a := fun a b => by
      have hb : b ∈ center J := h ▸ mem_top b
      exact mem_center_iff.mp hb a
    obtain ⟨x, hxV, -, -, hxo, -⟩ := exists_eq_zpowers_sup_zpowers hV
    set x₀ : J := ⟨x, hVJ hxV⟩
    have hN : (zpowers x₀).Normal := ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
    have hx₀ : orderOf x₀ = 2 := by rw [Subgroup.orderOf_mk, hxo]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers x₀) with h1 | h1
    · have : x₀ = 1 := (mem_bot).mp (h1 ▸ mem_zpowers x₀)
      rw [this, orderOf_one] at hx₀
      norm_num at hx₀
    · have h2 : Nat.card J = 2 := by
        rw [← card_top (G := J), ← h1, Nat.card_zpowers, hx₀]
      have h3 := card_le_of_le hVJ
      rw [hV.card_four, h2] at h3
      norm_num at h3

namespace Sec5Roles

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A)

theorem X_inf_O_eq_bot (H : Subgroup G) : ρ.X ⊓ O H = ⊥ := by
  refine inf_eq_bot_of_coprime ?_
  rw [ρ.card_X, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact (Nat.coprime_two_left.mpr (odd_natCard_O _)).pow_left 2

theorem Y_inf_O_eq_bot (H : Subgroup G) : ρ.Y ⊓ O H = ⊥ := ρ.swap.X_inf_O_eq_bot H

theorem Y_le_centralizer_X : ρ.Y ≤ centralizer (ρ.X : Set G) := fun _ hy =>
  mem_centralizer_iff.mpr fun _ hx => ρ.comm (ρ.X_le_A hx) (ρ.Y_le_A hy)

theorem isPGroup_two_Y : IsPGroup 2 ρ.Y :=
  IsPGroup.of_card (n := 2) (by rw [ρ.card_Y]; norm_num)

theorem Y_le_centralizer_N₀ : ρ.Y ≤ centralizer (ρ.N₀ : Set G) :=
  le_centralizer_iff.mp ρ.N₀_le

theorem commutator_commutator_X_eq {T : Subgroup G} (hT : Odd (Nat.card T))
    (hXT : ρ.X ≤ normalizer (T : Set G)) : ⁅⁅T, ρ.X⁆, ρ.X⁆ = ⁅T, ρ.X⁆ :=
  commutator_commutator_eq_of_isKleinFour ρ.isKleinFour_X hT hXT

theorem exists_bar_W_of
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)))
    {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H ρ.N₀ (O ρ.N)) :
    ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ (bar H W).Normal ∧
      IsL2PGL2OrA7OrV4 (bar H W) ∧ O H ⊓ W = W ⊓ O ρ.N := by
  obtain ⟨W, hWHN, hXW, -, -, hWn, hker, htype, -, -⟩ := h1N H hH hAH hcov
  refine ⟨W, hWHN, hXW, ?_, ?_, hker⟩
  · rw [← bar_sup_O (hWHN.trans inf_le_left)]
    exact bar_normal hWn
  · rcases htype with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end Sec5Roles

namespace Sec5KConfig

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔨 : Sec5KConfig ρ p)

theorem A_le_normalizer_P : A ≤ normalizer (𝔨.P : Set G) := 𝔨.hP.2.2.1

theorem A_le_K : A ≤ 𝔨.K := 𝔨.hK.2.1

theorem K_eq_normalizer_V : 𝔨.K = normalizer (𝔨.V : Set G) := 𝔨.hK.2.2.2.2.1

theorem X_le_centralizer_V : ρ.X ≤ centralizer (𝔨.V : Set G) := 𝔨.hK.2.2.2.2.2

theorem Pstar_le_K₁ : 𝔨.Pstar ≤ 𝔨.K₁ := le_sup_left.trans 𝔨.hK₁.1

theorem A_le_K₁ : A ≤ 𝔨.K₁ := le_sup_right.trans 𝔨.hK₁.1

theorem K₁_le_K : 𝔨.K₁ ≤ 𝔨.K := 𝔨.hK₁.2.1

theorem Pstar_inf_O_K₁ : 𝔨.Pstar ⊓ O 𝔨.K₁ = 𝔨.V := 𝔨.hK₁.2.2.2

theorem V_le_Pstar : 𝔨.V ≤ 𝔨.Pstar := inf_le_left

theorem Pstar_le_P : 𝔨.Pstar ≤ 𝔨.P := inf_le_left

theorem Pstar_le_K : 𝔨.Pstar ≤ 𝔨.K := inf_le_right

theorem Pstar_le_normalizer_V : 𝔨.Pstar ≤ normalizer (𝔨.V : Set G) :=
  𝔨.Pstar_le_K.trans 𝔨.K_eq_normalizer_V.le

theorem K₁_le_normalizer_V : 𝔨.K₁ ≤ normalizer (𝔨.V : Set G) :=
  𝔨.K₁_le_K.trans 𝔨.K_eq_normalizer_V.le

theorem U_eq : 𝔨.U = 𝔨.Pstar ⊓ centralizer (ρ.X : Set G) := by
  change 𝔨.P ⊓ centralizer (ρ.X : Set G) ⊓ 𝔨.K = 𝔨.P ⊓ 𝔨.K ⊓ centralizer (ρ.X : Set G)
  rw [inf_right_comm]

theorem A_le_normalizer_Pstar : A ≤ normalizer (𝔨.Pstar : Set G) := fun _ ha =>
  inf_normalizer_le_normalizer_inf ⟨𝔨.A_le_normalizer_P ha, le_normalizer (𝔨.A_le_K ha)⟩

theorem commutator_Pstar_X_le_centralizer_V :
    ⁅𝔨.Pstar, ρ.X⁆ ≤ centralizer (𝔨.V : Set G) := by
  have hXV : ⁅ρ.X, 𝔨.V⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr 𝔨.X_le_centralizer_V
  rw [← commutator_eq_bot_iff_le_centralizer]
  refine commutator_commutator_eq_bot_of_rotate ?_ ?_
  · rw [hXV, commutator_bot_left]
  · rw [eq_bot_iff]
    refine (commutator_mono (commutator_le_left_of_le_normalizer 𝔨.Pstar_le_normalizer_V)
      le_rfl).trans ?_
    rw [commutator_comm, hXV]

include 𝔨 in
theorem odd_p : Odd p := 𝔨.hp.odd_of_ne_two 𝔨.hp2

include 𝔨 in
theorem odd_card_of_isPGroup {T : Subgroup G} (hT : IsPGroup p T) : Odd (Nat.card T) := by
  have : Fact p.Prime := ⟨𝔨.hp⟩
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rw [hn]
  exact 𝔨.odd_p.pow

theorem isPGroup_of_le_P {T : Subgroup G} (hT : T ≤ 𝔨.P) : IsPGroup p T :=
  𝔨.hP.2.1.to_le hT

theorem odd_card_of_le_P {T : Subgroup G} (hT : T ≤ 𝔨.P) : Odd (Nat.card T) :=
  𝔨.odd_card_of_isPGroup (𝔨.isPGroup_of_le_P hT)

theorem Pstar_le_U_sup_commutator : 𝔨.Pstar ≤ 𝔨.U ⊔ ⁅𝔨.Pstar, ρ.X⁆ := by
  obtain ⟨x, hx, x', hx', hxo, hx'o, hc, -, hXeq⟩ := exists_eq_zpowers_sup_zpowers ρ.isKleinFour_X
  have h := inf_C_C_sup_commutator_eq (𝔨.odd_card_of_le_P 𝔨.Pstar_le_P) hxo hx'o hc
    (𝔨.A_le_normalizer_Pstar (ρ.X_le_A hx)) (𝔨.A_le_normalizer_Pstar (ρ.X_le_A hx'))
  conv_lhs => rw [← h]
  refine sup_le ?_ (sup_le (le_sup_right.trans' (commutator_mono le_rfl
    (hXeq ▸ le_sup_left))) (le_sup_right.trans' (commutator_mono le_rfl (hXeq ▸ le_sup_right))))
  intro g hg
  refine mem_sup_left ?_
  rw [𝔨.U_eq]
  exact ⟨hg.1.1, mem_centralizer_of_commute_of_eq_sup hXeq hg.1.2 hg.2⟩

theorem covers_of_le_of_inf_centralizer_V_le
    (h48i : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L))
    (hXN₀ : ρ.X ≤ ρ.N₀)
    {M : Subgroup G} (hCM : 𝔨.K₁ ⊓ centralizer (𝔨.V : Set G) ≤ M) (hXM : ρ.X ≤ M) :
    Covers M ρ.N₀ (O ρ.N) := by
  obtain ⟨L, _, f, hf, hfker, hL⟩ := h48i
  have hXO : ρ.X ⊓ O ρ.N = ⊥ := ρ.X_inf_O_eq_bot _
  have hkerX : ρ.X.subgroupOf ρ.N₀ ⊓ f.ker = ⊥ := by
    rw [hfker, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx : (x : G) ∈ ρ.X ⊓ O ρ.N := ⟨hx1, hx2⟩
    rw [hXO, mem_bot] at hx
    exact (mem_bot).mpr (Subtype.ext hx)
  suffices h : ∃ B ≤ M ⊓ ρ.N₀, (B.subgroupOf ρ.N₀).map f = ⊤ by
    obtain ⟨B, hBM, hB⟩ := h
    exact (le_sup_of_map_eq_top f hfker hB).trans
      (sup_le_sup_right hBM _)
  rcases hL with hL | hL
  ·
    have := hL.isSimpleGroup (by norm_num)
    refine ⟨𝔨.K₁ ⊓ centralizer (𝔨.V : Set G) ⊓ ρ.N₀, inf_le_inf_right _ hCM, ?_⟩
    have hK₁top : ∀ l : L, ∃ k : ρ.N₀, (k : G) ∈ 𝔨.K₁ ∧ f k = l := by
      intro l
      obtain ⟨n, rfl⟩ := hf l
      have hn' : (n : G) ∈ ((𝔨.K₁ ⊓ ρ.N₀ ⊔ O ρ.N : Subgroup G) : Set G) := 𝔨.hK₁.2.2.1 n.2
      rw [coe_mul_of_left_le_normalizer_right _ _ (inf_le_right.trans ρ.N₀_le_normalizer_O_N)]
        at hn'
      obtain ⟨k, hk, o, ho, hko⟩ := Set.mem_mul.mp hn'
      have hoN : o ∈ ρ.N₀ := ρ.O_N_le_N₀ ho
      have hfo : f ⟨o, hoN⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hfker]
        exact ho
      refine ⟨⟨k, hk.2⟩, hk.1, ?_⟩
      have e : n = ⟨k, hk.2⟩ * ⟨o, hoN⟩ := Subtype.ext hko.symm
      rw [e, map_mul, hfo, mul_one]
    set T := ((𝔨.K₁ ⊓ centralizer (𝔨.V : Set G) ⊓ ρ.N₀).subgroupOf ρ.N₀).map f
    have hTn : T.Normal := by
      refine ⟨fun t ht l => ?_⟩
      obtain ⟨b, hb, rfl⟩ := mem_map.mp ht
      obtain ⟨k, hkK, rfl⟩ := hK₁top l
      refine mem_map.mpr ⟨k * b * k⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      rw [mem_subgroupOf] at hb ⊢
      obtain ⟨hbKV, hbN⟩ := mem_inf.mp hb
      obtain ⟨hbK, hbV⟩ := mem_inf.mp hbKV
      simp only [coe_mul, coe_inv]
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem (mul_mem hkK hbK) (inv_mem hkK), ?_⟩,
        mul_mem (mul_mem k.2 hbN) (inv_mem k.2)⟩
      exact conj_mem_centralizer_of_mem_normalizer (𝔨.K₁_le_normalizer_V hkK) hbV
    have hXT : (ρ.X.subgroupOf ρ.N₀).map f ≤ T := by
      refine map_mono fun x hx => ?_
      rw [mem_subgroupOf] at hx ⊢
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨𝔨.A_le_K₁ (ρ.X_le_A hx), 𝔨.X_le_centralizer_V hx⟩,
        hXN₀ hx⟩
    have hne : T ≠ ⊥ := by
      intro hT
      have h1 := card_map_of_inf_ker_eq_bot f _ hkerX
      have hX0 : (ρ.X.subgroupOf ρ.N₀).map f = ⊥ := eq_bot_iff.mpr (hT ▸ hXT)
      rw [Nat.card_congr (subgroupOfEquivOfLe hXN₀).toEquiv, ρ.card_X, hX0, card_bot] at h1
      norm_num at h1
    have := hTn
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal T).resolve_left hne
  ·
    refine ⟨ρ.X, le_inf hXM hXN₀, ?_⟩
    have := hL
    have : Finite L := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
    have hcard : Nat.card ((ρ.X.subgroupOf ρ.N₀).map f) = Nat.card L := by
      rw [card_map_of_inf_ker_eq_bot f _ hkerX,
        Nat.card_congr (subgroupOfEquivOfLe hXN₀).toEquiv, ρ.card_X, IsKleinFour.card_four]
    exact eq_top_of_card_eq _ hcard

theorem inf_normalizer_eq_Pstar_of
    (h48i : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L))
    (hXN₀ : ρ.X ≤ ρ.N₀)
    (U' : Subgroup G) (hU'V : U' ≤ 𝔨.V) (hU' : U' ≠ ⊥)
    (hAU' : A ≤ normalizer (U' : Set G)) (hUU' : 𝔨.U ≤ normalizer (U' : Set G)) :
    𝔨.P ⊓ normalizer (U' : Set G) = 𝔨.Pstar := by
  have hCV : centralizer (𝔨.V : Set G) ≤ normalizer (U' : Set G) :=
    (centralizer_le hU'V).trans (centralizer_le_normalizer _)
  have hPN : 𝔨.Pstar ≤ normalizer (U' : Set G) :=
    𝔨.Pstar_le_U_sup_commutator.trans
      (sup_le hUU' (𝔨.commutator_Pstar_X_le_centralizer_V.trans hCV))
  have hlocal : CFSG.IsPLocal p (normalizer (U' : Set G)) :=
    ⟨U', hU', 𝔨.isPGroup_of_le_P (hU'V.trans (𝔨.V_le_Pstar.trans 𝔨.Pstar_le_P)), rfl⟩
  have hcov := 𝔨.covers_of_le_of_inf_centralizer_V_le h48i hXN₀ (inf_le_right.trans hCV)
    (ρ.X_le_A.trans hAU')
  have hAT : A ≤ normalizer ((𝔨.P ⊓ normalizer (U' : Set G) : Subgroup G) : Set G) :=
    fun _ ha => inf_normalizer_le_normalizer_inf
      ⟨𝔨.A_le_normalizer_P ha, le_normalizer (hAU' ha)⟩
  have hcard := 𝔨.hKmax (normalizer (U' : Set G)) (𝔨.P ⊓ normalizer (U' : Set G)) hlocal hAU'
    hcov inf_le_right (𝔨.isPGroup_of_le_P inf_le_left) hAT
  exact (eq_of_le_of_card_ge (le_inf 𝔨.Pstar_le_P hPN) hcard).symm

theorem exists_W_K₁ : ∃ W : Subgroup G, W ≤ 𝔨.K₁ ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧
    (bar 𝔨.K₁ W).Normal ∧ IsL2PGL2OrA7OrV4 (bar 𝔨.K₁ W) ∧ Covers W ρ.N₀ (O ρ.N) ∧
    O 𝔨.K₁ ⊓ W = W ⊓ O ρ.N ∧ 𝔨.K₁ = W ⊔ 𝔨.Pstar ⊔ ρ.Y ⊔ O 𝔨.K₁ ∧
    (IsL2OrA7 (bar 𝔨.K₁ W) 5 ∨ bar 𝔨.K₁ W = bar 𝔨.K₁ ρ.X) := by
  obtain ⟨W, hWKN, hXW, hcov, hK₁eq, hWn, hker, htype⟩ := 𝔨.hK₁q.2
  refine ⟨W, hWKN, hXW, ?_, ?_, hcov, hker, hK₁eq, htype.imp_right And.left⟩
  · rw [← bar_sup_O (hWKN.trans inf_le_left)]
    exact bar_normal hWn
  · rcases htype with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem X_le_K₁ : ρ.X ≤ 𝔨.K₁ := ρ.X_le_A.trans 𝔨.A_le_K₁

theorem Y_le_K₁ : ρ.Y ≤ 𝔨.K₁ := ρ.Y_le_A.trans 𝔨.A_le_K₁

theorem commutator_Pstar_X_le_Pstar : ⁅𝔨.Pstar, ρ.X⁆ ≤ 𝔨.Pstar :=
  commutator_le_left_of_le_normalizer (ρ.X_le_A.trans 𝔨.A_le_normalizer_Pstar)

theorem X_le_normalizer_commutator_Pstar_X :
    ρ.X ≤ normalizer ((⁅𝔨.Pstar, ρ.X⁆ : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_commutator (𝔨.A_le_normalizer_Pstar (ρ.X_le_A hx)) (le_normalizer hx)

theorem isCyclic_bar_commutator_Pstar_X_of
    (hP2b5 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → IsCyclic K) :
    IsCyclic (bar 𝔨.K₁ ⁅𝔨.Pstar, ρ.X⁆) := by
  obtain ⟨W, -, hXW, hWn, hWt, -⟩ := 𝔨.exists_W_K₁
  have hXJ : bar 𝔨.K₁ ρ.X ≤ bar 𝔨.K₁ W := bar_mono hXW
  refine hP2b5 hWt
    (isKleinFour_bar ρ.isKleinFour_X 𝔨.X_le_K₁ (ρ.X_inf_O_eq_bot _)) hXJ ?_ ?_ ?_
  · rw [bar_commutator (𝔨.Pstar_le_K₁) 𝔨.X_le_K₁]
    exact (commutator_mono le_rfl hXJ).trans (commutator_le_right _ _)
  · exact (𝔨.odd_card_of_le_P (𝔨.commutator_Pstar_X_le_Pstar.trans 𝔨.Pstar_le_P)).of_dvd_nat
      (card_bar_dvd (𝔨.commutator_Pstar_X_le_Pstar.trans 𝔨.Pstar_le_K₁))
  · exact bar_le_normalizer 𝔨.X_le_normalizer_commutator_Pstar_X

theorem exists_commutator_commutator_le_of
    (hP2b6 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X)) :
    ∃ x ∈ ρ.X, x ≠ 1 ∧ ⁅⁅𝔨.Pstar, ρ.X⁆, zpowers x⁆ ≤ ⁅𝔨.Pstar, ρ.X⁆ ⊓ O 𝔨.K₁ := by
  obtain ⟨W, -, hXW, hWn, hWt, -⟩ := 𝔨.exists_W_K₁
  have hXJ : bar 𝔨.K₁ ρ.X ≤ bar 𝔨.K₁ W := bar_mono hXW
  have hEK₁ : ⁅𝔨.Pstar, ρ.X⁆ ≤ 𝔨.K₁ := 𝔨.commutator_Pstar_X_le_Pstar.trans 𝔨.Pstar_le_K₁
  obtain ⟨a, ha, ha1, hle⟩ := hP2b6 hWt
    (isKleinFour_bar ρ.isKleinFour_X 𝔨.X_le_K₁ (ρ.X_inf_O_eq_bot _)) hXJ
    (by rw [bar_commutator (𝔨.Pstar_le_K₁) 𝔨.X_le_K₁]
        exact (commutator_mono le_rfl hXJ).trans (commutator_le_right _ _))
    ((𝔨.odd_card_of_le_P (𝔨.commutator_Pstar_X_le_Pstar.trans 𝔨.Pstar_le_P)).of_dvd_nat
      (card_bar_dvd hEK₁))
    (bar_le_normalizer 𝔨.X_le_normalizer_commutator_Pstar_X)
  obtain ⟨k, hkX, rfl⟩ := mem_bar_iff.mp ha
  refine ⟨k, hkX, fun h => ha1 ?_, ?_⟩
  · rw [show k = 1 from Subtype.ext h, QuotientGroup.mk_one]
  rw [commutator_le]
  intro e he s hs
  rcases eq_one_or_eq_of_mem_zpowers
      (orderOf_eq_two_of_isKleinFour ρ.isKleinFour_X hkX (fun h => ha1 (by
        rw [show k = 1 from Subtype.ext h, QuotientGroup.mk_one]))) hs with rfl | rfl
  · rw [commutatorElement_one_right]
    exact one_mem _
  · refine ⟨commutator_zpowers_le_of_mem_normalizer
      (𝔨.X_le_normalizer_commutator_Pstar_X hkX) (commutator_mem_commutator he (mem_zpowers _)), ?_⟩
    have heK : e ∈ 𝔨.K₁ := hEK₁ he
    have hc := hle (mem_bar_iff.mpr ⟨⟨e, heK⟩, he, rfl⟩)
    rw [mem_centralizer_singleton_iff] at hc
    have h1 : (QuotientGroup.mk (⟨e, heK⟩ * k * ⟨e, heK⟩⁻¹ * k⁻¹) : Bar 𝔨.K₁) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hc]
      group
    rw [mk_eq_one_iff_mem_O] at h1
    simpa [commutatorElement_def] using h1

theorem exists_Pstar_le_C_of
    (hP2b6 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X)) :
    ∃ x ∈ ρ.X, x ≠ 1 ∧ 𝔨.Pstar ≤ C x := by
  obtain ⟨x, hxX, hx1, hEx⟩ := 𝔨.exists_commutator_commutator_le_of hP2b6
  have hxo : orderOf x = 2 := orderOf_eq_two_of_isKleinFour ρ.isKleinFour_X hxX hx1
  have hVx : 𝔨.V ≤ C x := fun v hv =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (𝔨.X_le_centralizer_V hxX) v hv)
  have hE₀V : ⁅𝔨.Pstar, ρ.X⁆ ⊓ O 𝔨.K₁ ≤ 𝔨.V := by
    rw [← 𝔨.Pstar_inf_O_K₁]
    exact inf_le_inf_right _ 𝔨.commutator_Pstar_X_le_Pstar
  have hbot := commutator_zpowers_eq_bot_of_le
    (𝔨.odd_card_of_le_P (𝔨.commutator_Pstar_X_le_Pstar.trans 𝔨.Pstar_le_P)) hxo
    (𝔨.X_le_normalizer_commutator_Pstar_X hxX) hEx (hE₀V.trans hVx)
  have hEC : ⁅𝔨.Pstar, ρ.X⁆ ≤ C x := by
    intro e he
    have h := commutator_mem_commutator he (mem_zpowers x)
    rw [hbot, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact mem_centralizer_singleton_iff.mpr h
  have hUC : 𝔨.U ≤ C x := by
    intro u hu
    rw [𝔨.U_eq] at hu
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hu.2 x hxX).symm
  exact ⟨x, hxX, hx1, 𝔨.Pstar_le_U_sup_commutator.trans (sup_le hUC hEC)⟩

theorem isCyclic_commutator_Pstar_X_of
    (hP2b5 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → IsCyclic K)
    (hP2b6 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X)) :
    IsCyclic (⁅𝔨.Pstar, ρ.X⁆ : Subgroup G) ∧
      ⁅𝔨.Pstar, ρ.X⁆ ⊓ centralizer (ρ.X : Set G) = ⊥ := by
  obtain ⟨x, hxX, hx1, hEx⟩ := 𝔨.exists_commutator_commutator_le_of hP2b6
  obtain ⟨x', hx'X, hx'o, -, -, hXeq⟩ :=
    exists_zpowers_sup_zpowers_eq_of_mem ρ.isKleinFour_X hxX hx1
  have hxo : orderOf x = 2 := orderOf_eq_two_of_isKleinFour ρ.isKleinFour_X hxX hx1
  have hEodd : Odd (Nat.card (⁅𝔨.Pstar, ρ.X⁆ : Subgroup G)) :=
    𝔨.odd_card_of_le_P (𝔨.commutator_Pstar_X_le_Pstar.trans 𝔨.Pstar_le_P)
  have hEK₁ : ⁅𝔨.Pstar, ρ.X⁆ ≤ 𝔨.K₁ := 𝔨.commutator_Pstar_X_le_Pstar.trans 𝔨.Pstar_le_K₁
  have hE₀V : ⁅𝔨.Pstar, ρ.X⁆ ⊓ O 𝔨.K₁ ≤ 𝔨.V := by
    rw [← 𝔨.Pstar_inf_O_K₁]
    exact inf_le_inf_right _ 𝔨.commutator_Pstar_X_le_Pstar
  have hVC : ∀ {z : G}, z ∈ ρ.X → 𝔨.V ≤ C z := fun hz v hv =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (𝔨.X_le_centralizer_V hz) v hv)
  have hxE := 𝔨.X_le_normalizer_commutator_Pstar_X hxX
  have hx'E := 𝔨.X_le_normalizer_commutator_Pstar_X hx'X
  have hEE₀ : ⁅𝔨.Pstar, ρ.X⁆ ≤
      normalizer ((⁅𝔨.Pstar, ρ.X⁆ ⊓ O 𝔨.K₁ : Subgroup G) : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hg, le_normalizer_O _ (hEK₁ hg)⟩
  have hPx := 𝔨.A_le_normalizer_Pstar (ρ.X_le_A hxX)
  have hPx' := 𝔨.A_le_normalizer_Pstar (ρ.X_le_A hx'X)
  have hPodd : Odd (Nat.card 𝔨.Pstar) := 𝔨.odd_card_of_le_P 𝔨.Pstar_le_P
  have hEXY : ⁅⁅𝔨.Pstar, ρ.X⁆, zpowers x⁆ ⊔ ⁅⁅𝔨.Pstar, ρ.X⁆, zpowers x'⁆ =
      ⁅𝔨.Pstar, ρ.X⁆ := by
    refine le_antisymm (sup_le (commutator_zpowers_le_of_mem_normalizer hxE)
      (commutator_zpowers_le_of_mem_normalizer hx'E)) ?_
    calc ⁅𝔨.Pstar, ρ.X⁆ = ⁅𝔨.Pstar, zpowers x ⊔ zpowers x'⁆ := by rw [hXeq]
      _ = ⁅𝔨.Pstar, zpowers x⁆ ⊔ ⁅𝔨.Pstar, zpowers x'⁆ :=
        commutator_sup_eq_of_le_normalizer (zpowers_le.mpr hPx) (zpowers_le.mpr hPx')
      _ = ⁅⁅𝔨.Pstar, zpowers x⁆, zpowers x⁆ ⊔ ⁅⁅𝔨.Pstar, zpowers x'⁆, zpowers x'⁆ := by
        rw [commutator_commutator_zpowers_eq hPodd hxo hPx,
          commutator_commutator_zpowers_eq hPodd hx'o hPx']
      _ ≤ ⁅⁅𝔨.Pstar, ρ.X⁆, zpowers x⁆ ⊔ ⁅⁅𝔨.Pstar, ρ.X⁆, zpowers x'⁆ :=
        sup_le_sup (commutator_mono (commutator_mono le_rfl (hXeq ▸ le_sup_left)) le_rfl)
          (commutator_mono (commutator_mono le_rfl (hXeq ▸ le_sup_right)) le_rfl)
  obtain ⟨e, he, hcyc⟩ := exists_le_inf_O_sup_zpowers_of_isCyclic_bar hEK₁
    (𝔨.isCyclic_bar_commutator_Pstar_X_of hP2b5)
  obtain ⟨-, hcy, hCy⟩ := eq_bot_and_isCyclic_of_commutator_le hEodd inf_le_left hEE₀ hxo hx'o hxE
    hx'E (hE₀V.trans (hVC hxX)) (hE₀V.trans (hVC hx'X)) hEx hEXY he hcyc
  refine ⟨hcy, eq_bot_iff.mpr ((le_inf inf_le_left fun g hg => ?_).trans hCy.le)⟩
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hg.2 x' hx'X).symm

theorem conj_mem_X_of_mem_K₁
    (hns : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5))
    {c : G} (hcK : c ∈ 𝔨.K₁) (hcA : c ∈ normalizer (A : Set G)) {x : G} (hx : x ∈ ρ.X) :
    c * x * c⁻¹ ∈ ρ.X := by
  obtain ⟨W, hWKN, hXW, hJn, -, hcov, hker, -⟩ := 𝔨.exists_W_K₁
  have : IsSimpleGroup (bar 𝔨.K₁ W) := by
    obtain ⟨L, _, ⟨e⟩, hL⟩ := quotIs_bar_inf ρ.O_N_le_N₀ ρ.N₀_le_normalizer_O_N
      (hWKN.trans inf_le_left) (hWKN.trans inf_le_right) hcov hker hns
    exact (hL.of_mulEquiv e.symm).isSimpleGroup (by norm_num)
  have hZ := center_eq_bot_of_isSimpleGroup_of_isKleinFour
    (isKleinFour_bar ρ.isKleinFour_X 𝔨.X_le_K₁ (ρ.X_inf_O_eq_bot _)) (bar_mono hXW)
  have haA : c * x * c⁻¹ ∈ A := (mem_normalizer_iff.mp hcA x).mp (ρ.X_le_A hx)
  have hXY : ρ.X ≤ normalizer (ρ.Y : Set G) :=
    (le_centralizer_iff.mp ρ.Y_le_centralizer_X).trans (centralizer_le_normalizer _)
  have haXY : c * x * c⁻¹ ∈ ((ρ.X : Set G) * (ρ.Y : Set G)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hXY, ρ.X_sup_Y]
    exact haA
  obtain ⟨x', hx', y', hy', hxy⟩ := Set.mem_mul.mp haXY
  have hcxK : c * x * c⁻¹ ∈ 𝔨.K₁ := mul_mem (mul_mem hcK (𝔨.X_le_K₁ hx)) (inv_mem hcK)
  have haJ : (QuotientGroup.mk ⟨c * x * c⁻¹, hcxK⟩ : Bar 𝔨.K₁) ∈ bar 𝔨.K₁ W := by
    have hxJ : (QuotientGroup.mk ⟨x, 𝔨.X_le_K₁ hx⟩ : Bar 𝔨.K₁) ∈ bar 𝔨.K₁ W :=
      mem_bar_iff.mpr ⟨_, hXW hx, rfl⟩
    have := hJn.conj_mem _ hxJ (QuotientGroup.mk ⟨c, hcK⟩)
    have e : (QuotientGroup.mk ⟨c * x * c⁻¹, hcxK⟩ : Bar 𝔨.K₁) = QuotientGroup.mk ⟨c, hcK⟩ *
        QuotientGroup.mk ⟨x, 𝔨.X_le_K₁ hx⟩ * (QuotientGroup.mk ⟨c, hcK⟩)⁻¹ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    rw [e]
    exact this
  have hyJ : (QuotientGroup.mk ⟨y', 𝔨.Y_le_K₁ hy'⟩ : Bar 𝔨.K₁) ∈
      bar 𝔨.K₁ W := by
    have hx'J : (QuotientGroup.mk ⟨x', 𝔨.X_le_K₁ hx'⟩ : Bar 𝔨.K₁) ∈
        bar 𝔨.K₁ W := mem_bar_iff.mpr ⟨_, hXW hx', rfl⟩
    have e : (QuotientGroup.mk ⟨y', 𝔨.Y_le_K₁ hy'⟩ : Bar 𝔨.K₁) =
        (QuotientGroup.mk ⟨x', 𝔨.X_le_K₁ hx'⟩)⁻¹ * QuotientGroup.mk ⟨c * x * c⁻¹, hcxK⟩ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hxy]
      group
    rw [e]
    exact mul_mem (inv_mem hx'J) haJ
  have hcen : (⟨_, hyJ⟩ : bar 𝔨.K₁ W) ∈ center (bar 𝔨.K₁ W) := by
    rw [mem_center_iff]
    rintro ⟨g, hg⟩
    obtain ⟨k, hk, rfl⟩ := mem_bar_iff.mp hg
    apply Subtype.ext
    change QuotientGroup.mk k * QuotientGroup.mk ⟨y', 𝔨.Y_le_K₁ hy'⟩ =
      (QuotientGroup.mk ⟨y', 𝔨.Y_le_K₁ hy'⟩ : Bar 𝔨.K₁) * QuotientGroup.mk k
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp (ρ.Y_le_centralizer_N₀ hy') _
      (mem_inf.mp (hWKN hk)).2)
  rw [hZ, mem_bot] at hcen
  have hy1 : (QuotientGroup.mk ⟨y', 𝔨.Y_le_K₁ hy'⟩ : Bar 𝔨.K₁) = 1 := congrArg Subtype.val hcen
  rw [mk_eq_one_iff_mem_O] at hy1
  have hy'1 : y' ∈ ρ.Y ⊓ O 𝔨.K₁ := ⟨hy', hy1⟩
  rw [ρ.Y_inf_O_eq_bot, mem_bot] at hy'1
  rw [← hxy, hy'1, mul_one]
  exact hx'

theorem card_commutator_map_le_of
    (hns : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5)) (hXN₀ : ρ.X ≤ ρ.N₀)
    (h45 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A H P₁ →
      IsMaxInvIn p A H P₂ → ∃ g ∈ H ⊓ normalizer (A : Set G),
        P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (hK₁ : 𝔨.K₁ ≠ ⊤)
    {L : Type} [Group L] (f : ρ.N₀ →* L) (hf : Function.Surjective f)
    (hfker : f.ker = (O ρ.N).subgroupOf ρ.N₀) (F : Subgroup L) (hF : IsPGroup p F)
    (hXF : (ρ.X.subgroupOf ρ.N₀).map f ≤ normalizer (F : Set L)) :
    Nat.card (⁅F, (ρ.X.subgroupOf ρ.N₀).map f⁆ : Subgroup L) ≤
      Nat.card (⁅𝔨.Pstar, ρ.X⁆ : Subgroup G) := by
  have : Fact p.Prime := ⟨𝔨.hp⟩
  have : Finite L := Finite.of_surjective f hf
  set Z₁ : Subgroup G := 𝔨.K₁ ⊓ (F.comap f).map ρ.N₀.subtype with hZ₁
  have hZ₁N : Z₁ ≤ ρ.N₀ := inf_le_right.trans (map_subtype_le _)
  have hmemZ₁ : ∀ {n : G} (hn : n ∈ ρ.N₀), n ∈ 𝔨.K₁ → f ⟨n, hn⟩ ∈ F → n ∈ Z₁ :=
    fun {n} hn hnK hnF => ⟨hnK, ⟨n, hn⟩, hnF, rfl⟩
  have hZ₁F : ∀ {n : G} (hn : n ∈ Z₁), f ⟨n, hZ₁N hn⟩ ∈ F := by
    rintro n ⟨-, ⟨m, hm, rfl⟩⟩
    exact hm
  have hZ₁map : (Z₁.subgroupOf ρ.N₀).map f = F := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      exact hZ₁F hn
    · intro l hl
      obtain ⟨n, rfl⟩ := hf l
      have hn' : (n : G) ∈ ((𝔨.K₁ ⊓ ρ.N₀ ⊔ O ρ.N : Subgroup G) : Set G) :=
        𝔨.hK₁.2.2.1 n.2
      rw [coe_mul_of_left_le_normalizer_right _ _ (inf_le_right.trans ρ.N₀_le_normalizer_O_N)]
        at hn'
      obtain ⟨k, hk, o, ho, hko⟩ := Set.mem_mul.mp hn'
      have hoN : o ∈ ρ.N₀ := ρ.O_N_le_N₀ ho
      have hfo : f ⟨o, hoN⟩ = 1 := by
        rw [← MonoidHom.mem_ker, hfker]
        exact ho
      have e : n = ⟨k, hk.2⟩ * ⟨o, hoN⟩ := Subtype.ext hko.symm
      have hfk : f ⟨k, hk.2⟩ = f n := by rw [e, map_mul, hfo, mul_one]
      exact ⟨⟨k, hk.2⟩, hmemZ₁ hk.2 hk.1 (hfk ▸ hl), hfk⟩
  have hAZ₁ : A ≤ normalizer (Z₁ : Set G) := by
    refine ρ.X_sup_Y.symm.le.trans (sup_le ?_ ?_)
    · intro x hx
      refine mem_normalizer_fintype fun z hz => ?_
      have hzN := hZ₁N hz
      have hxN := hXN₀ hx
      refine hmemZ₁ (mul_mem (mul_mem hxN hzN) (inv_mem hxN))
        (mul_mem (mul_mem (𝔨.X_le_K₁ hx) hz.1) (inv_mem (𝔨.X_le_K₁ hx))) ?_
      have hfx : f ⟨x, hxN⟩ ∈ normalizer (F : Set L) := hXF ⟨⟨x, hxN⟩, hx, rfl⟩
      have h1 := (mem_normalizer_iff.mp hfx _).mp (hZ₁F hz)
      have e : f ⟨x * z * x⁻¹, mul_mem (mul_mem hxN hzN) (inv_mem hxN)⟩ =
          f ⟨x, hxN⟩ * f ⟨z, hzN⟩ * (f ⟨x, hxN⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact h1
    · exact fun y hy => centralizer_le_normalizer _
        (centralizer_le hZ₁N (ρ.Y_le_centralizer_N₀ hy))
  have hZ₁odd : Odd (Nat.card Z₁) := by
    have h1 := relIndex_mul_card (H := f.ker) (K := Z₁.subgroupOf ρ.N₀)
    rw [relIndex_ker, hZ₁map, Nat.card_congr (subgroupOfEquivOfLe hZ₁N).toEquiv] at h1
    rw [← h1]
    obtain ⟨k, hk⟩ := hF.exists_card_eq
    refine (hk ▸ 𝔨.odd_p.pow).mul ?_
    have h2 : Nat.card (f.ker) = Nat.card (O ρ.N) := by
      rw [hfker]
      exact Nat.card_congr (subgroupOfEquivOfLe ρ.O_N_le_N₀).toEquiv
    exact (h2 ▸ odd_natCard_O _).of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨S, hSsyl, hAS⟩ := CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_coprime
    Nat.prime_two 𝔨.hp ρ.isPGroup_A hAZ₁ hZ₁odd.not_two_dvd_nat
  have hSZ₁ : S ≤ Z₁ := hSsyl.le
  have hSp : IsPGroup p S := hSsyl.isPGroup
  have hSN : S ≤ ρ.N₀ := hSZ₁.trans hZ₁N
  have hSmap : (S.subgroupOf ρ.N₀).map f = F := by
    obtain ⟨Q, hQ⟩ := hSsyl
    set ψ : Z₁ →* L := f.comp (inclusion hZ₁N) with hψ
    have hψr : ψ.range = F := by rw [hψ, MonoidHom.range_comp, inclusion_range, hZ₁map]
    have hsurj : Function.Surjective ψ.rangeRestrict := MonoidHom.rangeRestrict_surjective ψ
    have hpr : IsPGroup p ψ.range := hψr ▸ hF
    have htop : (Q.mapSurjective hsurj : Subgroup ψ.range) = ⊤ :=
      ((Q.mapSurjective hsurj).3 (hpr.of_equiv topEquiv.symm) le_top).symm
    rw [Sylow.coe_mapSurjective] at htop
    have hQψ : (Q : Subgroup Z₁).map ψ = F := by
      have h1 : ((Q : Subgroup Z₁).map ψ.rangeRestrict).map ψ.range.subtype =
          (⊤ : Subgroup ψ.range).map ψ.range.subtype := by rw [htop]
      rw [map_map, MonoidHom.subtype_comp_rangeRestrict, ← MonoidHom.range_eq_map,
        range_subtype] at h1
      rw [h1, hψr]
    have hQS : (Q : Subgroup Z₁).map (inclusion hZ₁N) = S.subgroupOf ρ.N₀ := by
      ext ⟨n, hn⟩
      rw [mem_subgroupOf, ← hQ, mem_map, mem_map]
      constructor
      · rintro ⟨q, hq, hqn⟩
        exact ⟨q, hq, congrArg Subtype.val hqn⟩
      · rintro ⟨q, hq, hqn⟩
        exact ⟨q, hq, Subtype.ext hqn⟩
    rw [← hQS, map_map]
    exact hQψ
  have hcomm : ⁅F, (ρ.X.subgroupOf ρ.N₀).map f⁆ =
      ((⁅S, ρ.X⁆).subgroupOf ρ.N₀).map f := by
    rw [← hSmap, ← map_commutator]
    congr 1
    apply map_injective ρ.N₀.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hSN, map_subgroupOf_eq_of_le hXN₀,
      map_subgroupOf_eq_of_le (commutator_le_of_le hSN hXN₀)]
  obtain ⟨S', hS', hSS'⟩ := exists_isMaxInvIn_ge_of_le (hSZ₁.trans inf_le_left) hSp hAS
  obtain ⟨c, hc, hcS'⟩ := h45 𝔨.K₁ hK₁ 𝔨.A_le_K₁ 𝔨.Pstar S'
    ((𝔨.hK.2.2.2.1).of_le 𝔨.Pstar_le_K₁ 𝔨.K₁_le_K) hS'
  have hcK : c ∈ 𝔨.K₁ := (mem_inf.mp hc).1
  have hcA : c ∈ normalizer (A : Set G) := (mem_inf.mp hc).2
  have hXc : ρ.X.map (MulAut.conj c).toMonoidHom = ρ.X :=
    eq_of_le_of_card_ge (by
      rintro _ ⟨x, hx, rfl⟩
      exact 𝔨.conj_mem_X_of_mem_K₁ hns hcK hcA hx)
      (by rw [card_map_of_injective (MulAut.conj c).injective])
  have hle : ⁅S, ρ.X⁆ ≤ (⁅𝔨.Pstar, ρ.X⁆).map (MulAut.conj c).toMonoidHom := by
    rw [map_commutator, hcS', hXc]
    exact commutator_mono hSS' le_rfl
  rw [hcomm]
  calc Nat.card (((⁅S, ρ.X⁆).subgroupOf ρ.N₀).map f) ≤
        Nat.card ((⁅S, ρ.X⁆).subgroupOf ρ.N₀) :=
      Nat.le_of_dvd Nat.card_pos (card_map_dvd _ _)
    _ = Nat.card (⁅S, ρ.X⁆ : Subgroup G) :=
      Nat.card_congr (subgroupOfEquivOfLe (commutator_le_of_le hSN hXN₀)).toEquiv
    _ ≤ Nat.card ((⁅𝔨.Pstar, ρ.X⁆).map (MulAut.conj c).toMonoidHom) := card_le_of_le hle
    _ = Nat.card (⁅𝔨.Pstar, ρ.X⁆ : Subgroup G) :=
      card_map_of_injective (MulAut.conj c).injective

include 𝔨 in
theorem isCyclic_commutator_X_of
    (hP2b5 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → IsCyclic K)
    (hP2b6 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X))
    {K' T : Subgroup G} (hXK' : ρ.X ≤ K') {J : Subgroup (Bar K')} (hJn : J.Normal)
    (hXJ : bar K' ρ.X ≤ J) (hJ : IsL2PGL2OrA7OrV4 J) (hTK' : T ≤ K') (hTp : IsPGroup p T)
    (hXT : ρ.X ≤ normalizer (T : Set G))
    (hE₀ : ⁅T, ρ.X⁆ ⊓ O K' ≤ centralizer (ρ.X : Set G)) :
    IsCyclic (⁅T, ρ.X⁆ : Subgroup G) ∧ ⁅T, ρ.X⁆ ⊓ O K' = ⊥ ∧
      ⁅T, ρ.X⁆ ⊓ centralizer (ρ.X : Set G) = ⊥ := by
  have hET : ⁅T, ρ.X⁆ ≤ T := commutator_le_left_of_le_normalizer hXT
  have hEK' : ⁅T, ρ.X⁆ ≤ K' := hET.trans hTK'
  have hXE : ρ.X ≤ normalizer ((⁅T, ρ.X⁆ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_commutator (hXT hx) (le_normalizer hx)
  have hEodd : Odd (Nat.card (⁅T, ρ.X⁆ : Subgroup G)) := 𝔨.odd_card_of_isPGroup (hTp.to_le hET)
  have hEJ : bar K' ⁅T, ρ.X⁆ ≤ J := by
    rw [bar_commutator hTK' hXK']
    exact (commutator_mono le_rfl hXJ).trans (commutator_le_right _ _)
  have hXb := isKleinFour_bar ρ.isKleinFour_X hXK' (ρ.X_inf_O_eq_bot _)
  have hEbodd := hEodd.of_dvd_nat (card_bar_dvd hEK')
  have hXEb := bar_le_normalizer (H := K') hXE
  have hcyc := hP2b5 hJ hXb hXJ hEJ hEbodd hXEb
  obtain ⟨a, ha, ha1, hle⟩ := hP2b6 hJ hXb hXJ hEJ hEbodd hXEb
  obtain ⟨k, hkX, rfl⟩ := mem_bar_iff.mp ha
  have hk1 : (k : G) ≠ 1 := fun h =>
    ha1 (by rw [show k = 1 from Subtype.ext h, QuotientGroup.mk_one])
  have hko : orderOf (k : G) = 2 := orderOf_eq_two_of_isKleinFour ρ.isKleinFour_X hkX hk1
  have hEk : ⁅⁅T, ρ.X⁆, zpowers (k : G)⁆ ≤ ⁅T, ρ.X⁆ ⊓ O K' := by
    rw [commutator_le]
    intro e he s hs
    rcases eq_one_or_eq_of_mem_zpowers hko hs with rfl | rfl
    · rw [commutatorElement_one_right]
      exact one_mem _
    · refine ⟨commutator_zpowers_le_of_mem_normalizer (hXE hkX)
        (commutator_mem_commutator he (mem_zpowers _)), ?_⟩
      have heK : e ∈ K' := hEK' he
      have hc := hle (mem_bar_iff.mpr ⟨⟨e, heK⟩, he, rfl⟩)
      rw [mem_centralizer_singleton_iff] at hc
      have h1 : (QuotientGroup.mk (⟨e, heK⟩ * k * ⟨e, heK⟩⁻¹ * k⁻¹) : Bar K') = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv, hc]
        group
      rw [mk_eq_one_iff_mem_O] at h1
      simpa [commutatorElement_def] using h1
  obtain ⟨x', hx'X, hx'o, -, -, hXeq⟩ :=
    exists_zpowers_sup_zpowers_eq_of_mem ρ.isKleinFour_X hkX hk1
  have hC : ∀ {z : G}, z ∈ ρ.X → ⁅T, ρ.X⁆ ⊓ O K' ≤ C z := fun hz w hw =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hE₀ hw) _ hz).symm
  have hTx := hXT hkX
  have hTx' := hXT hx'X
  have hTodd : Odd (Nat.card T) := 𝔨.odd_card_of_isPGroup hTp
  have hEXY : ⁅⁅T, ρ.X⁆, zpowers (k : G)⁆ ⊔ ⁅⁅T, ρ.X⁆, zpowers x'⁆ = ⁅T, ρ.X⁆ := by
    refine le_antisymm (sup_le (commutator_zpowers_le_of_mem_normalizer (hXE hkX))
      (commutator_zpowers_le_of_mem_normalizer (hXE hx'X))) ?_
    calc ⁅T, ρ.X⁆ = ⁅T, zpowers (k : G) ⊔ zpowers x'⁆ := by rw [hXeq]
      _ = ⁅T, zpowers (k : G)⁆ ⊔ ⁅T, zpowers x'⁆ :=
        commutator_sup_eq_of_le_normalizer (zpowers_le.mpr hTx) (zpowers_le.mpr hTx')
      _ = ⁅⁅T, zpowers (k : G)⁆, zpowers (k : G)⁆ ⊔ ⁅⁅T, zpowers x'⁆, zpowers x'⁆ := by
        rw [commutator_commutator_zpowers_eq hTodd hko hTx,
          commutator_commutator_zpowers_eq hTodd hx'o hTx']
      _ ≤ ⁅⁅T, ρ.X⁆, zpowers (k : G)⁆ ⊔ ⁅⁅T, ρ.X⁆, zpowers x'⁆ :=
        sup_le_sup (commutator_mono (commutator_mono le_rfl (hXeq ▸ le_sup_left)) le_rfl)
          (commutator_mono (commutator_mono le_rfl (hXeq ▸ le_sup_right)) le_rfl)
  have hEE₀ : ⁅T, ρ.X⁆ ≤ normalizer ((⁅T, ρ.X⁆ ⊓ O K' : Subgroup G) : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hg, le_normalizer_O _ (hEK' hg)⟩
  obtain ⟨e, he, hcyc'⟩ := exists_le_inf_O_sup_zpowers_of_isCyclic_bar hEK' hcyc
  obtain ⟨hbot, hcy, hCy⟩ := eq_bot_and_isCyclic_of_commutator_le hEodd inf_le_left hEE₀ hko hx'o
    (hXE hkX) (hXE hx'X) (hC hkX) (hC hx'X) hEk hEXY he hcyc'
  refine ⟨hcy, hbot, eq_bot_iff.mpr ((le_inf inf_le_left fun g hg => ?_).trans hCy.le)⟩
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hg.2 x' hx'X).symm

include 𝔨 in
theorem normalizer_ne_top_of_isPGroup {T : Subgroup G} (hT : IsPGroup p T) (hT1 : T ≠ ⊥) :
    normalizer (T : Set G) ≠ ⊤ :=
  ρ.ne_top_of_isPLocal 𝔨.hp 𝔨.hp2 ⟨T, hT1, hT, rfl⟩

theorem K_ne_top : 𝔨.K ≠ ⊤ := ρ.ne_top_of_isPLocal 𝔨.hp 𝔨.hp2 𝔨.hK.1

theorem K₁_ne_top : 𝔨.K₁ ≠ ⊤ := fun h => 𝔨.K_ne_top (eq_top_iff.mpr (h ▸ 𝔨.K₁_le_K))

theorem commutator_inf_normalizer_le_Pstar_of
    (hXN₀ : ρ.X ≤ ρ.N₀)
    (h45 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A H P₁ →
      IsMaxInvIn p A H P₂ → ∃ g ∈ H ⊓ normalizer (A : Set G),
        P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h56 : ∀ K : Subgroup G, CFSG.IsPLocal p K → A ≤ K → Covers K ρ.N₀ (O ρ.N) →
      ¬ Sec4Setting.PConstrainedWrt p A K ρ.X)
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)))
    (hP2b5 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → IsCyclic K)
    (hP2b6 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2PGL2OrA7OrV4 L →
      IsKleinFour V → V ≤ L → ∀ {K : Subgroup X}, K ≤ L → Odd (Nat.card K) →
      V ≤ normalizer (K : Set X) → ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X))
    (U' : Subgroup G) (hU'V : U' ≤ 𝔨.V) (hU' : U' ≠ ⊥) (hAU' : A ≤ normalizer (U' : Set G))
    (hns : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5)) :
    ⁅𝔨.P ⊓ normalizer (U' : Set G), ρ.X⁆ ≤ 𝔨.Pstar := by
  have : Fact p.Prime := ⟨𝔨.hp⟩
  have h48i : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) := by
    obtain ⟨L, i, f, hf, hk, hL⟩ := hns
    exact ⟨L, i, f, hf, hk, Or.inl hL⟩
  have hU'P : U' ≤ 𝔨.P := hU'V.trans (𝔨.V_le_Pstar.trans 𝔨.Pstar_le_P)
  have hlocal : CFSG.IsPLocal p (normalizer (U' : Set G)) :=
    ⟨U', hU', 𝔨.isPGroup_of_le_P hU'P, rfl⟩
  have hK'top := 𝔨.normalizer_ne_top_of_isPGroup (𝔨.isPGroup_of_le_P hU'P) hU'
  have hCV : centralizer (𝔨.V : Set G) ≤ normalizer (U' : Set G) :=
    (centralizer_le hU'V).trans (centralizer_le_normalizer _)
  have hXK' : ρ.X ≤ normalizer (U' : Set G) := ρ.X_le_A.trans hAU'
  have hcov := 𝔨.covers_of_le_of_inf_centralizer_V_le h48i hXN₀ (inf_le_right.trans hCV) hXK'
  obtain ⟨W, hWKN, hXW, hJn, hJ, hker⟩ := ρ.exists_bar_W_of h1N hK'top hAU' hcov
  have hWK : W ≤ normalizer (U' : Set G) := hWKN.trans inf_le_left
  have hWN : W ≤ ρ.N₀ := hWKN.trans inf_le_right
  have hTK' : 𝔨.P ⊓ normalizer (U' : Set G) ≤ normalizer (U' : Set G) := inf_le_right
  have hTp : IsPGroup p (𝔨.P ⊓ normalizer (U' : Set G) : Subgroup G) :=
    𝔨.isPGroup_of_le_P inf_le_left
  have hXT : ρ.X ≤ normalizer ((𝔨.P ⊓ normalizer (U' : Set G) : Subgroup G) : Set G) :=
    fun x hx => inf_normalizer_le_normalizer_inf ⟨𝔨.A_le_normalizer_P (ρ.X_le_A hx),
      le_normalizer (hXK' hx)⟩
  have hAX : A ≤ normalizer (ρ.X : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx =>
      congrArg Subtype.val (ρ.hA.1.1.is_comm.comm ⟨x, ρ.X_le_A hx⟩ ⟨a, ha⟩))
  have hAT : A ≤ normalizer ((𝔨.P ⊓ normalizer (U' : Set G) : Subgroup G) : Set G) :=
    fun a ha => inf_normalizer_le_normalizer_inf ⟨𝔨.A_le_normalizer_P ha,
      le_normalizer (hAU' ha)⟩
  have hET' : ⁅𝔨.P ⊓ normalizer (U' : Set G), ρ.X⁆ ≤ 𝔨.P ⊓ normalizer (U' : Set G) :=
    commutator_le_left_of_le_normalizer hXT
  have hEK' : ⁅𝔨.P ⊓ normalizer (U' : Set G), ρ.X⁆ ≤ normalizer (U' : Set G) := hET'.trans hTK'
  have hE₀ : ⁅𝔨.P ⊓ normalizer (U' : Set G), ρ.X⁆ ⊓ O (normalizer (U' : Set G)) ≤
      centralizer (ρ.X : Set G) := by
    have hnot := h56 _ hlocal hAU' hcov
    have hAO : A ≤ normalizer ((O (normalizer (U' : Set G)) : Subgroup G) : Set G) :=
      hAU'.trans (le_normalizer_O _)
    have hAE : A ≤ normalizer ((⁅𝔨.P ⊓ normalizer (U' : Set G), ρ.X⁆ ⊓
        O (normalizer (U' : Set G)) : Subgroup G) : Set G) := fun a ha =>
      inf_normalizer_le_normalizer_inf ⟨mem_normalizer_commutator (hAT ha) (hAX ha), hAO ha⟩
    obtain ⟨R, hR, hER, hAR⟩ := CFSG.ABGTheoremB.exists_isSylowOf_normalized_ge_of_coprime
      Nat.prime_two 𝔨.hp ρ.isPGroup_A hAO (odd_natCard_O _).not_two_dvd_nat inf_le_right
      (hTp.to_le (inf_le_left.trans hET')) hAE
    by_contra hc
    refine hnot ⟨R, hR, hAR, fun hXR => hc ?_⟩
    exact hER.trans (le_centralizer_iff.mp hXR)
  obtain ⟨-, hEO, -⟩ := 𝔨.isCyclic_commutator_X_of hP2b5 hP2b6 hXK' hJn (bar_mono hXW) hJ hTK' hTp
    hXT hE₀
  have hEE : ⁅𝔨.Pstar, ρ.X⁆ ≤ ⁅𝔨.P ⊓ normalizer (U' : Set G), ρ.X⁆ := by
    have hET : ⁅𝔨.Pstar, ρ.X⁆ ≤ 𝔨.P ⊓ normalizer (U' : Set G) :=
      le_inf (𝔨.commutator_Pstar_X_le_Pstar.trans 𝔨.Pstar_le_P)
        (𝔨.commutator_Pstar_X_le_centralizer_V.trans hCV)
    rw [← ρ.commutator_commutator_X_eq (𝔨.odd_card_of_le_P 𝔨.Pstar_le_P)
      (ρ.X_le_A.trans 𝔨.A_le_normalizer_Pstar)]
    exact commutator_mono hET le_rfl
  have hns' := hns
  obtain ⟨L, _, f, hf, hfker, -⟩ := hns
  have : Finite L := Finite.of_surjective f hf
  set K' := normalizer (U' : Set G) with hK'
  set Es := ⁅𝔨.P ⊓ K', ρ.X⁆ with hEs
  set Z₁ := W ⊓ (Es ⊔ O K') with hZ₁def
  have hZ₁ : Z₁ ≤ W := inf_le_left
  have hZ₁N : Z₁ ≤ ρ.N₀ := hZ₁.trans hWN
  have hZ₁K : Z₁ ≤ K' := hZ₁.trans hWK
  have hZ₂ : ⁅Z₁, ρ.X⁆ ≤ W := commutator_le_of_le hZ₁ hXW
  have hFsp : IsPGroup p ((Z₁.subgroupOf ρ.N₀).map f) := by
    have h1 := card_bar_eq_card_map f hfker hWK hWN hker hZ₁
    have h2 : bar K' Z₁ ≤ bar K' Es := by
      rw [← bar_sup_O hEK']
      exact bar_mono inf_le_right
    have hp' : IsPGroup p (bar K' Es) := IsPGroup.bar (hTp.to_le hET') hEK'
    obtain ⟨n, hn⟩ := (hp'.to_le h2).exists_card_eq
    exact IsPGroup.of_card (h1 ▸ hn)
  have hXZ₁ : ∀ x ∈ ρ.X, ∀ z ∈ Z₁, x * z * x⁻¹ ∈ Z₁ := by
    intro x hx z hz
    have hxK := hXK' hx
    obtain ⟨hzW, hzE⟩ := mem_inf.mp hz
    refine mem_inf.mpr ⟨mul_mem (mul_mem (hXW hx) hzW) (inv_mem (hXW hx)), ?_⟩
    have hxEO : x ∈ normalizer ((Es ⊔ O K' : Subgroup G) : Set G) :=
      mem_normalizer_sup_of_mem (mem_normalizer_commutator (hXT hx) (le_normalizer hx))
        (le_normalizer_O _ hxK)
    exact (mem_normalizer_iff.mp hxEO z).mp hzE
  have hXFs : (ρ.X.subgroupOf ρ.N₀).map f ≤
      normalizer (((Z₁.subgroupOf ρ.N₀).map f : Subgroup L) : Set L) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_normalizer_fintype fun l hl => ?_
    obtain ⟨z, hz, rfl⟩ := hl
    refine ⟨x * z * x⁻¹, hXZ₁ x hx z hz, by simp only [map_mul, map_inv]⟩
  have hS1 := 𝔨.card_commutator_map_le_of hns' hXN₀ h45 𝔨.K₁_ne_top f hf hfker _ hFsp hXFs
  have hcommF : ⁅(Z₁.subgroupOf ρ.N₀).map f, (ρ.X.subgroupOf ρ.N₀).map f⁆ =
      ((⁅Z₁, ρ.X⁆).subgroupOf ρ.N₀).map f := by
    rw [← map_commutator]
    congr 1
    apply map_injective ρ.N₀.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hZ₁N, map_subgroupOf_eq_of_le hXN₀,
      map_subgroupOf_eq_of_le (hZ₂.trans hWN)]
  have hEJ : bar K' Es ≤ bar K' W := by
    rw [bar_commutator hTK' hXK']
    exact (commutator_mono le_rfl (bar_mono hXW)).trans (commutator_le_right _ _)
  have hEsZ₁ : bar K' Es ≤ bar K' Z₁ := by
    intro y hy
    obtain ⟨n, hn, hne⟩ := mem_bar_iff.mp (hEJ hy)
    obtain ⟨e, he, rfl⟩ := mem_bar_iff.mp hy
    have h1 : (QuotientGroup.mk (n⁻¹ * e) : Bar K') = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hne, inv_mul_cancel]
    rw [mk_eq_one_iff_mem_O] at h1
    refine mem_bar_iff.mpr ⟨n, mem_inf.mpr ⟨hn, ?_⟩, hne⟩
    have e1 : (n : G) = e * ((n⁻¹ * e : K') : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rw [e1]
    exact mul_mem (mem_sup_left he) (mem_sup_right (inv_mem h1))
  have hEsX : ⁅Es, ρ.X⁆ = Es := ρ.commutator_commutator_X_eq (𝔨.odd_card_of_isPGroup hTp) hXT
  have hEsZ₂ : bar K' Es ≤ bar K' ⁅Z₁, ρ.X⁆ := by
    calc bar K' Es = bar K' ⁅Es, ρ.X⁆ := by rw [hEsX]
      _ = ⁅bar K' Es, bar K' ρ.X⁆ := bar_commutator hEK' hXK'
      _ ≤ ⁅bar K' Z₁, bar K' ρ.X⁆ := commutator_mono hEsZ₁ le_rfl
      _ = bar K' ⁅Z₁, ρ.X⁆ := (bar_commutator hZ₁K hXK').symm
  have hcardEs : Nat.card Es ≤ Nat.card (⁅𝔨.Pstar, ρ.X⁆ : Subgroup G) := by
    calc Nat.card Es = Nat.card (bar K' Es) := (card_bar_of_inf_O_eq_bot hEK' hEO).symm
      _ ≤ Nat.card (bar K' ⁅Z₁, ρ.X⁆) := card_le_of_le hEsZ₂
      _ = Nat.card (((⁅Z₁, ρ.X⁆).subgroupOf ρ.N₀).map f) :=
        card_bar_eq_card_map f hfker hWK hWN hker hZ₂
      _ = Nat.card (⁅(Z₁.subgroupOf ρ.N₀).map f,
          (ρ.X.subgroupOf ρ.N₀).map f⁆ : Subgroup L) := by rw [hcommF]
      _ ≤ _ := hS1
  have heq : ⁅𝔨.Pstar, ρ.X⁆ = Es := eq_of_le_of_card_ge hEE hcardEs
  rw [← heq]
  exact 𝔨.commutator_Pstar_X_le_Pstar

end Sec5KConfig

namespace Sec5ConfigR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔠 : Sec5ConfigR ρ p)

theorem P_le_H₀ : 𝔠.P ≤ 𝔠.H₀ := le_sup_left.trans 𝔠.hH₀.1

theorem A_le_H₀ : A ≤ 𝔠.H₀ := le_sup_right.trans 𝔠.hH₀.1

theorem Q_le_P : 𝔠.Q ≤ 𝔠.P := inf_le_left

theorem Q_le_O_H₀ : 𝔠.Q ≤ O 𝔠.H₀ := inf_le_right

theorem mem_normalizer_Q {g : G} (hg : g ∈ 𝔠.H₀) (hgP : g ∈ normalizer (𝔠.P : Set G)) :
    g ∈ normalizer (𝔠.Q : Set G) :=
  inf_normalizer_le_normalizer_inf ⟨hgP, le_normalizer_O _ hg⟩

theorem P_le_H₁ : 𝔠.P ≤ 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) := fun _ hg =>
  ⟨𝔠.P_le_H₀ hg, 𝔠.mem_normalizer_Q (𝔠.P_le_H₀ hg) (le_normalizer hg)⟩

theorem A_le_H₁ : A ≤ 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) := fun _ ha =>
  ⟨𝔠.A_le_H₀ ha, 𝔠.mem_normalizer_Q (𝔠.A_le_H₀ ha) (𝔠.A_le_normalizer_P ha)⟩

theorem A_le_normalizer_Q : A ≤ normalizer (𝔠.Q : Set G) := fun _ ha => (𝔠.A_le_H₁ ha).2

theorem P_le_normalizer_Q : 𝔠.P ≤ normalizer (𝔠.Q : Set G) := fun _ hg => (𝔠.P_le_H₁ hg).2

theorem Y_le_H₁ : ρ.Y ≤ 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) := ρ.Y_le_A.trans 𝔠.A_le_H₁

theorem exists_W_H₁ : ∃ W : Subgroup G, W ≤ 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) ⊓ ρ.M₀ ∧
    ρ.Y ≤ W ∧ (bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) W).Normal ∧
    IsL2OrA7 (bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) W) 5 := by
  obtain ⟨W, hWHM, hYW, -, hWn, -, htype⟩ := 𝔠.hH₁.2.2.2
  refine ⟨W, hWHM, hYW, ?_, htype⟩
  have hWH : W ≤ 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) := hWHM.trans inf_le_left
  rw [← bar_sup_O hWH]
  exact bar_normal hWn

theorem exists_three_element_of
    (hP2b12 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2OrA7 L 5 →
      IsKleinFour V → V ≤ L → ∃ u ∈ L ⊓ normalizer (V : Set X), (∃ n : ℕ, orderOf u = 3 ^ n) ∧
        ∀ a ∈ V, a ≠ 1 → u * a * u⁻¹ ≠ a) :
    ∃ u ∈ (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ⊓ centralizer (ρ.X : Set G),
      u ∈ normalizer (ρ.Y : Set G) ∧ (∃ n : ℕ, orderOf u = 3 ^ n) ∧
      ∀ y ∈ ρ.Y, y ≠ 1 → u * y * u⁻¹ ≠ y := by
  obtain ⟨W, hWHM, hYW, hWn, hWt⟩ := 𝔠.exists_W_H₁
  have hYJ : bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ρ.Y ≤
      bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) W := bar_mono hYW
  obtain ⟨ub, ⟨hubJ, hubN⟩, -, hubfix⟩ := hP2b12 hWt
    (isKleinFour_bar ρ.isKleinFour_Y 𝔠.Y_le_H₁ (ρ.Y_inf_O_eq_bot _)) hYJ
  obtain ⟨m, hmJ, rfl⟩ := mem_bar_iff.mp hubJ
  have hmB : (m : G) ∈ 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) ⊓ centralizer (ρ.X : Set G) :=
    ⟨m.2, ρ.M₀_le (mem_inf.mp (hWHM hmJ)).2⟩
  have hm : ∀ y ∈ ρ.Y, ∃ y' ∈ ρ.Y,
      y'⁻¹ * ((m : G) * y * (m : G)⁻¹) ∈ O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) := by
    intro y hy
    have hyb : (QuotientGroup.mk ⟨y, 𝔠.Y_le_H₁ hy⟩ : Bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G))) ∈
        bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ρ.Y := mem_bar_iff.mpr ⟨_, hy, rfl⟩
    obtain ⟨y', hy', hy'e⟩ := mem_bar_iff.mp ((mem_normalizer_iff.mp hubN _).mp hyb)
    refine ⟨y', hy', ?_⟩
    have h2 : (QuotientGroup.mk (y'⁻¹ * (m * ⟨y, 𝔠.Y_le_H₁ hy⟩ * m⁻¹)) :
        Bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G))) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy'e, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      group
    rw [mk_eq_one_iff_mem_O] at h2
    simpa using h2
  obtain ⟨n, hnB, hnY, hnm⟩ := exists_mem_normalizer_of_conj_mem inf_le_left
    (le_inf 𝔠.Y_le_H₁ ρ.Y_le_centralizer_X) ρ.isPGroup_two_Y hmB hm
  have hnfix : ∀ y ∈ ρ.Y, y ≠ 1 → n * y * n⁻¹ ≠ y := by
    intro y hy hy1 h
    have hmk : (QuotientGroup.mk ⟨n, hnB.1⟩ : Bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G))) =
        QuotientGroup.mk m := by
      rw [QuotientGroup.eq]
      exact (mem_O_iff_mem_oddCore _).mp (by simpa using hnm)
    refine hubfix (QuotientGroup.mk ⟨y, 𝔠.Y_le_H₁ hy⟩) (mem_bar_iff.mpr ⟨_, hy, rfl⟩)
      (fun h1 => hy1 ?_) ?_
    · rw [mk_eq_one_iff_mem_O] at h1
      have h1' : y ∈ ρ.Y ⊓ O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) := ⟨hy, h1⟩
      rwa [ρ.Y_inf_O_eq_bot, mem_bot] at h1'
    · rw [← hmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext h
  have hn0 : orderOf n ≠ 0 := (orderOf_pos n).ne'
  obtain ⟨a, r, hr, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  have hr0 : r ≠ 0 := fun h => hn0 (by rw [hor, h, mul_zero])
  refine ⟨n ^ r, pow_mem hnB r, pow_mem hnY r, ⟨a, ?_⟩,
    fun y hy hy1 => pow_conj_ne_of_fixedPointFree ρ.isKleinFour_Y hnY hnfix hr hy hy1⟩
  rw [orderOf_pow' (x := n) hr0, hor, Nat.gcd_mul_left_left,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hr0)]

theorem not_Q_le_C_of
    (hP2b12 : ∀ {X : Type} [Group X] [Finite X] {L V : Subgroup X}, IsL2OrA7 L 5 →
      IsKleinFour V → V ≤ L → ∃ u ∈ L ⊓ normalizer (V : Set X), (∃ n : ℕ, orderOf u = 3 ^ n) ∧
        ∀ a ∈ V, a ≠ 1 → u * a * u⁻¹ ≠ a) :
    ∀ y ∈ ρ.Y, y ≠ 1 → ¬ 𝔠.Q ≤ C y := by
  intro y hy hy1 hQy
  obtain ⟨u, ⟨⟨-, huQ⟩, -⟩, huY, -, hufix⟩ := 𝔠.exists_three_element_of hP2b12
  have hy₂ : u * y * u⁻¹ ∈ ρ.Y := (mem_normalizer_iff.mp huY y).mp hy
  have hQy₂ : 𝔠.Q ≤ C (u * y * u⁻¹) := by
    intro q hq
    have hq' : u⁻¹ * q * u ∈ 𝔠.Q := by
      have := (mem_normalizer_iff.mp (inv_mem huQ) q).mp hq
      simpa using this
    have hc := mem_centralizer_singleton_iff.mp (hQy hq')
    rw [mem_centralizer_singleton_iff]
    calc q * (u * y * u⁻¹) = u * ((u⁻¹ * q * u) * y) * u⁻¹ := by group
      _ = u * (y * (u⁻¹ * q * u)) * u⁻¹ := by rw [hc]
      _ = u * y * u⁻¹ * q := by group
  have hy₂1 : u * y * u⁻¹ ≠ 1 := fun h => hy1 (by
    have := congrArg (fun z => u⁻¹ * z * u) h
    simpa [mul_assoc] using this)
  have hy₂z : u * y * u⁻¹ ∉ zpowers y := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers (orderOf_eq_two_of_isKleinFour ρ.isKleinFour_Y hy hy1) h
      with h | h
    · exact hy₂1 h
    · exact hufix y hy hy1 h
  apply 𝔠.hH₁.1
  rw [← zpowers_sup_zpowers_eq_of_not_mem ρ.isKleinFour_Y hy hy1 hy₂ hy₂z]
  refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
  · rw [mem_centralizer_iff]
    intro q hq
    exact mem_centralizer_singleton_iff.mp (hQy hq)
  · rw [mem_centralizer_iff]
    intro q hq
    exact mem_centralizer_singleton_iff.mp (hQy₂ hq)

theorem isSylowOf_Q : CFSG.ABGLocalTools.IsSylowOf p 𝔠.Q (O 𝔠.H₀) :=
  isSylowOf_inf_O_of_isMaxInvIn 𝔠.hp ρ.isPGroup_A (fun _ ha => le_normalizer (𝔠.A_le_H₀ ha))
    (𝔠.hP.of_le 𝔠.P_le_H₀ le_top)

theorem Q_le_O_H₁ : 𝔠.Q ≤ O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) :=
  le_O_of_le_normalizer_of_odd (le_inf (𝔠.Q_le_O_H₀.trans (O_le _)) le_normalizer) inf_le_right
    (𝔠.odd_card_of_le_P 𝔠.Q_le_P)

theorem O_H₁_le_O_H₀ : O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ≤ O 𝔠.H₀ := by
  have : Fact p.Prime := ⟨𝔠.hp⟩
  exact O_inf_normalizer_le_O 𝔠.isSylowOf_Q

theorem R_inf_O_H₁ : 𝔠.R ⊓ O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) = 𝔠.R ⊓ 𝔠.Q :=
  le_antisymm (le_inf inf_le_left fun _ hx =>
      ⟨inf_le_left (b := centralizer (ρ.X : Set G)) hx.1, 𝔠.O_H₁_le_O_H₀ hx.2⟩)
    (inf_le_inf_left _ 𝔠.Q_le_O_H₁)

end Sec5ConfigR

end CFSG.GH72
