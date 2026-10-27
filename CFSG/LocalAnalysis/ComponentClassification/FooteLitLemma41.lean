module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma42
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma41Tools

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_ne_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) (v : G) :
    ∃ w ∈ V, w ≠ 1 ∧ w ≠ v := by
  by_contra h
  push Not at h
  have hsub : (V : Set G) ⊆ {1, v} := fun w hw => by
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (h w hw hw1)
  have h1 : Nat.card V ≤ 2 := by
    calc Nat.card V = Nat.card ↥(V : Set G) := rfl
      _ = (V : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, v} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({v} : Set G).ncard + 1 := Set.ncard_insert_le 1 {v}
      _ = 2 := by rw [Set.ncard_singleton]
  rw [hV.card_four] at h1
  omega

omit [Finite G] in
theorem commutator_le_commutator_zpowers {V Y : Subgroup G} (hV : IsKleinFour V) {v w : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) (hw : w ∈ V) (hw1 : w ≠ 1) (hwv : w ≠ v)
    (hYv : Y ≤ centralizer ({v} : Set G)) (hvY : v ∈ normalizer (Y : Set G)) :
    ⁅Y, V⁆ ≤ ⁅Y, zpowers w⁆ := by
  have : IsKleinFour V := hV
  have hvw : v * w = w * v := congrArg Subtype.val (isMulCommutative_iff.mp
    (@IsKleinFour.isMulCommutative V _ hV) ⟨v, hv⟩ ⟨w, hw⟩)
  have hvz : v ∈ normalizer ((zpowers w : Subgroup G) : Set G) := by
    apply mem_normalizer_of_map_conj_eq
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hvw,
      mul_inv_cancel_right]
  have hvC : v ∈ normalizer ((⁅Y, zpowers w⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le_normalizers (zpowers_le.mpr hvY) (zpowers_le.mpr hvz)
      (mem_zpowers v)
  rw [commutator_le]
  intro y hy u hu
  have hyv : y * v = v * y := mem_centralizer_singleton_iff.mp (hYv hy)
  by_cases hu1 : u = 1
  · rw [hu1, commutatorElement_def, mul_one, mul_inv_cancel, inv_one, mul_one]
    exact one_mem _
  by_cases huv : u = v
  · rw [huv, commutatorElement_def, hyv, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  by_cases huw : u = w
  · rw [huw]
    exact commutator_mem_commutator hy (mem_zpowers w)
  have hu' : (⟨u, hu⟩ : V) = ⟨v, hv⟩ * ⟨w, hw⟩ :=
    IsKleinFour.eq_mul_of_ne_all (fun h => hv1 (congrArg Subtype.val h))
      (fun h => hw1 (congrArg Subtype.val h)) (fun h => hwv (congrArg Subtype.val h).symm)
      (fun h => hu1 (congrArg Subtype.val h)) (fun h => huv (congrArg Subtype.val h))
      (fun h => huw (congrArg Subtype.val h))
  have hu'' : u = v * w := congrArg Subtype.val hu'
  have e1 : ⁅y, u⁆ = v * ⁅y, w⁆ * v⁻¹ := by
    rw [hu'', commutatorElement_def, commutatorElement_def]
    calc y * (v * w) * y⁻¹ * (v * w)⁻¹ = (y * v) * w * y⁻¹ * w⁻¹ * v⁻¹ := by group
      _ = v * (y * w * y⁻¹ * w⁻¹) * v⁻¹ := by rw [hyv]; group
  rw [e1]
  exact (mem_normalizer_iff.mp hvC _).mp (commutator_mem_commutator hy (mem_zpowers w))

theorem inf_centralizer_le_oddCoreIn_of_forall (hLB : FooteLBalanceInput) {V : Subgroup G}
    (hV : IsKleinFour V) {a : G} (ha : orderOf a = 2)
    (haV : V ≤ centralizer ({a} : Set G))
    (hcomp : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → w ≠ v → ∀ J : Subgroup G,
      J ≤ centralizer ({v} : Set G) → IsPComponent 2 (J.subgroupOf (centralizer ({v} : Set G))) →
      conjugate J a = J → a ∉ coreActionKernel J →
      ⁅⁅oddCoreOfCentralizer a ⊓ centralizer ({v} : Set G), zpowers w⁆,
        ⁅oddCoreOfCentralizer a ⊓ centralizer ({v} : Set G), zpowers w⁆⁆ ≤ coreActionKernel J) :
    ⁅oddCoreOfCentralizer a, V⁆ ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer (V : Set G)) := by
  have : IsKleinFour V := hV
  set O := oddCoreOfCentralizer a with hO
  set Z := ⁅O, V⁆ with hZ
  have hsqV : ∀ x ∈ V, x * x = 1 := fun x hx =>
    congrArg Subtype.val (@IsKleinFour.mul_self V _ hV ⟨x, hx⟩)
  have hcommV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (isMulCommutative_iff.mp (@IsKleinFour.isMulCommutative V _ hV)
      ⟨x, hx⟩ ⟨y, hy⟩)
  have hVO : V ≤ normalizer (O : Set G) := fun x hx => mem_normalizer_oddCoreOfCentralizer (haV hx)
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreOfCentralizer a
  have hZO : Z ≤ O := commutator_le_self_of_le_normalizer hVO
  have hZodd : Odd (Nat.card Z) := Odd.of_dvd_nat hOodd (card_dvd_of_le hZO)
  have hVZ : V ≤ normalizer (Z : Set G) := le_normalizer_commutator_of_le_normalizers hVO
    le_normalizer
  have hZZ : ⁅Z, V⁆ = Z := commutator_commutator_eq_of_isKleinFour hV hVO hOodd
  rw [inf_centralizer_eq_iSup_of_isKleinFour hV hVZ hZodd hZZ]
  refine iSup₂_le fun v hv => iSup_le fun hv1 => ?_
  obtain ⟨w, hw, hw1, hwv⟩ := exists_ne_of_isKleinFour hV v
  have hav : a * v = v * a := (mem_centralizer_singleton_iff.mp (haV hv)).symm
  set Y := O ⊓ centralizer ({v} : Set G) with hY
  have hYv : Y ≤ centralizer ({v} : Set G) := inf_le_right
  have hvY : v ∈ normalizer (Y : Set G) := mem_normalizer_inf' (hVO hv)
    (mem_normalizer_centralizer_singleton rfl)
  have hwY : w ∈ normalizer (Y : Set G) := mem_normalizer_inf' (hVO hw)
    (mem_normalizer_centralizer_singleton (hcommV w hw v hv))
  have hYodd : Odd (Nat.card Y) := Odd.of_dvd_nat hOodd (card_dvd_of_le inf_le_left)
  set X := ⁅Y, zpowers w⁆ with hX
  have hXY : X ≤ Y := commutator_le_self_of_le_normalizer (zpowers_le.mpr hwY)
  have h1 : ⁅Z ⊓ centralizer ({v} : Set G), V⁆ ⊓ centralizer (V : Set G) ≤ ⁅X, X⁆ := by
    have h2 : ⁅Z ⊓ centralizer ({v} : Set G), V⁆ ≤ X :=
      (commutator_mono (inf_le_inf_right _ hZO) le_rfl).trans
        (commutator_le_commutator_zpowers hV hv hv1 hw hw1 hwv hYv hvY)
    have h3 : centralizer (V : Set G) ≤ centralizer ({w} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw)
    exact (inf_le_inf h2 h3).trans
      (inf_centralizer_le_commutator_of_involution (hsqV w hw) hYodd hwY)
  have hX'X : ⁅X, X⁆ ≤ X := commutator_le_left_of_le_normalizer le_normalizer
  have hX'O : ⁅X, X⁆ ≤ oddCoreOfCentralizer v := by
    refine le_oddCoreOfCentralizer_of_le_coreActionKernel ha hav (hX'X.trans hXY)
      fun J hJv hJ => ?_
    by_cases hJa : conjugate J a ≠ J ∨ a ∈ coreActionKernel J
    · exact (hX'X.trans hXY).trans (le_coreActionKernel_of_balance hLB ha hav hJv hJ hJa)
    · push Not at hJa
      exact hcomp v hv hv1 w hw hw1 hwv J hJv hJ hJa.1 hJa.2
  have hCVv : centralizer (V : Set G) ≤ centralizer ({v} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv)
  have h4 : oddCoreOfCentralizer v ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer (V : Set G)) :=
    le_oddCoreIn inf_le_right (fun x hx => mem_normalizer_inf'
      (mem_normalizer_oddCoreOfCentralizer (hCVv hx)) (le_normalizer hx))
      (Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer v) (card_dvd_of_le inf_le_left))
  intro x hx
  exact h4 (mem_inf.mpr ⟨hX'O (h1 hx), (mem_inf.mp hx).2⟩)

end CFSG.ComponentClassification.FooteLit
