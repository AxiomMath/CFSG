module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma43Core
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitBalanceCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOuterTools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_oddCoreOfCentralizer_of_le_coreActionKernel {a b : G} (ha : orderOf a = 2)
    (hab : a * b = b * a) {X : Subgroup G}
    (hX : X ≤ oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G))
    (hcomp : ∀ J : Subgroup G, J ≤ centralizer ({b} : Set G) →
      IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))) → X ≤ coreActionKernel J) :
    X ≤ oddCoreOfCentralizer b := by
  set C := centralizer ({b} : Set G) with hC
  have haC : a ∈ C := mem_centralizer_singleton_iff.mpr hab
  set a' : C := ⟨a, haC⟩ with ha'def
  have ha' : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hXC : X ≤ C := hX.trans inf_le_right
  have hX' : X.subgroupOf C ≤ oddCoreOfCentralizer a' := by
    intro x hx
    have h1 := oddCoreOfCentralizer_inf_le C a' (hX hx)
    exact (Subgroup.mem_map_iff_mem C.subtype_injective).mp h1
  have hcomp' : ∀ L : Subgroup C, IsPComponent 2 L → ⁅X.subgroupOf C, L⁆ ≤ oddCoreIn L := by
    intro L hL
    have hJC : L.map C.subtype ≤ C := map_subtype_le L
    have hLL : (L.map C.subtype).subgroupOf C = L :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective L
    have hJ : IsPComponent 2 ((L.map C.subtype).subgroupOf C) := by rwa [hLL]
    have hXJ := hcomp _ hJC hJ
    rw [commutator_le]
    intro x hx l hl
    have hxK : x⁻¹ ∈ coreActionKernel L := by
      have h1 := (mem_coreActionKernel_subgroupOf_iff hJC x⁻¹).mpr
        (hXJ (show ((x⁻¹ : C) : G) ∈ X from inv_mem hx))
      rwa [hLL] at h1
    have h2 := hxK.2 l⁻¹ (inv_mem hl)
    have h3 : ⁅x, l⁆ = ((l⁻¹)⁻¹ * (x⁻¹)⁻¹ * l⁻¹ * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h3]
    exact inv_mem h2
  have h := le_pPrimeCore_of_commutator_le ha' hX' hcomp'
  intro x hx
  exact ⟨⟨x, hXC hx⟩, h (show (⟨x, hXC hx⟩ : C) ∈ X.subgroupOf C from hx), rfl⟩

theorem le_inf_centralizer_sup_oddCoreIn {P J : Subgroup G} (hP : IsPGroup 2 P)
    (hPJ : P ≤ coreActionKernel J) : J ≤ (J ⊓ centralizer (P : Set G)) ⊔ oddCoreIn J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : ¬ 2 ∣ Nat.card (oddCoreIn J) := fun h2 =>
    (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn J)) (even_iff_two_dvd.mpr h2)
  have hPO : P ≤ normalizer ((oddCoreIn J : Subgroup G) : Set G) := fun u hu =>
    mem_normalizer_oddCoreIn (hPJ hu).1
  intro j hj
  obtain ⟨n, hn, hjn⟩ := exists_mul_mem_centralizer hP hO hPO (y := j) fun u hu => by
    have h1 := (hPJ (inv_mem hu)).2 j hj
    rw [inv_inv] at h1
    rw [show j⁻¹ * (u * j * u⁻¹) = j⁻¹ * u * j * u⁻¹ by group]
    exact h1
  have hnJ : n ∈ J := map_subtype_le _ hn
  have e1 : j = (j * n) * n⁻¹ := by group
  rw [e1]
  exact mul_mem (mem_sup_left (mem_inf.mpr ⟨mul_mem hj hnJ, hjn⟩)) (mem_sup_right (inv_mem hn))

theorem le_coreActionKernel_of_le_oddCoreIn_centralizer {V J U : Subgroup G}
    (hV : IsPGroup 2 V) (hVJ : V ≤ coreActionKernel J)
    (hU : U ≤ oddCoreIn (centralizer (V : Set G))) (hUJ : U ≤ normalizer (J : Set G)) :
    U ≤ coreActionKernel J := by
  set W := oddCoreIn (centralizer (V : Set G)) with hW
  set R := oddCoreIn J ⊔ (J ⊓ W) with hR
  have hWC : W ≤ centralizer (V : Set G) := map_subtype_le _
  have hJW : J ⊓ W ≤ normalizer ((oddCoreIn J : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (le_normalizer (mem_inf.mp hx).1)
  have hRodd : Odd (Nat.card R) := by
    rw [hR, sup_comm]
    exact odd_card_sup_of_le_normalizer hJW
      (Odd.of_dvd_nat (odd_card_oddCoreIn _) (card_dvd_of_le inf_le_right)) (odd_card_oddCoreIn J)
  have hcov := le_inf_centralizer_sup_oddCoreIn hV hVJ
  have hJU : ⁅J, U⁆ ≤ R := by
    rw [commutator_le]
    intro j hj u hu
    have hj' := hcov hj
    have hcomm : (J ⊓ centralizer (V : Set G)) ≤ normalizer ((oddCoreIn J : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_oddCoreIn (le_normalizer (mem_inf.mp hx).1)
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hcomm] at hj'
    obtain ⟨c, hc, o, ho, rfl⟩ := hj'
    obtain ⟨hcJ, hcV⟩ := mem_inf.mp hc
    have hoJ : o ∈ J := map_subtype_le _ ho
    have e1 : ⁅c * o, u⁆ = (c * ⁅o, u⁆ * c⁻¹) * ⁅c, u⁆ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    have huO : u ∈ normalizer ((oddCoreIn J : Subgroup G) : Set G) :=
      mem_normalizer_oddCoreIn (hUJ hu)
    have h1 : ⁅o, u⁆ ∈ oddCoreIn J := by
      rw [show ⁅o, u⁆ = o * (u * o⁻¹ * u⁻¹) by rw [commutatorElement_def]; group]
      exact mul_mem ho ((mem_normalizer_iff.mp huO o⁻¹).mp (inv_mem ho))
    have h2 : c * ⁅o, u⁆ * c⁻¹ ∈ oddCoreIn J :=
      (mem_normalizer_iff.mp (mem_normalizer_oddCoreIn (le_normalizer hcJ)) _).mp h1
    have h3 : ⁅c, u⁆ ∈ J := by
      rw [show ⁅c, u⁆ = c * (u * c⁻¹ * u⁻¹) by rw [commutatorElement_def]; group]
      exact mul_mem hcJ ((mem_normalizer_iff.mp (hUJ hu) c⁻¹).mp (inv_mem hcJ))
    have hcW : c ∈ normalizer (W : Set G) := mem_normalizer_oddCoreIn (le_normalizer hcV)
    have h4 : ⁅c, u⁆ ∈ W := by
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp hcW u).mp (hU hu)) (inv_mem (hU hu))
    exact mul_mem (mem_sup_left h2) (mem_sup_right (mem_inf.mpr ⟨h3, h4⟩))
  have hJUO : ⁅J, U⁆ ≤ oddCoreIn J := le_oddCoreIn
    (commutator_le_left_of_le_normalizer hUJ) (le_normalizer_commutator J U)
    (Odd.of_dvd_nat hRodd (card_dvd_of_le hJU))
  intro u hu
  refine ⟨hUJ hu, fun j hj => ?_⟩
  have h1 : j⁻¹ * u⁻¹ * j * u = ⁅j⁻¹, u⁻¹⁆ := by rw [commutatorElement_def, inv_inv, inv_inv]
  rw [h1]
  exact hJUO (commutator_mem_commutator (inv_mem hj) (inv_mem hu))

omit [Finite G] in
theorem footeTheta_inf_centralizer_le {V : Subgroup G} {a : G}
    (h41 : ⁅oddCoreOfCentralizer a, V⁆ ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer (V : Set G))) :
    footeTheta V a ⊓ centralizer (V : Set G) ≤ oddCoreIn (centralizer (V : Set G)) := by
  intro x hx
  obtain ⟨hxθ, hxV⟩ := mem_inf.mp hx
  set A := ⁅oddCoreOfCentralizer a, V⁆ with hA
  set B := oddCoreOfCentralizer a ⊓ oddCoreIn (centralizer (V : Set G)) with hB
  have hBA : B ≤ normalizer (A : Set G) := fun y hy =>
    le_normalizer_commutator _ V (mem_inf.mp hy).1
  have hxBA : x ∈ B ⊔ A := by rw [sup_comm]; exact hxθ
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right B A hBA] at hxBA
  obtain ⟨y, hy, z, hz, rfl⟩ := hxBA
  have hyO : y ∈ oddCoreIn (centralizer (V : Set G)) := (mem_inf.mp hy).2
  have hyV : y ∈ centralizer (V : Set G) := map_subtype_le _ hyO
  have hzV : z ∈ centralizer (V : Set G) := by
    have h1 := mul_mem (inv_mem hyV) hxV
    rwa [inv_mul_cancel_left] at h1
  exact mul_mem hyO (h41 (mem_inf.mpr ⟨hz, hzV⟩))

theorem foote_lemma_4_2 (hLB : FooteLBalanceInput) {E V : Subgroup G}
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (hEc : IsMulCommutative E) (hV : IsKleinFour V)
    (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G))
    (h41 : ∀ a ∈ E, a ≠ 1 → ⁅oddCoreOfCentralizer a, V⁆ ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer (V : Set G)))
    (K : G → Subgroup G) (hK : ∀ b ∈ E, b ≠ 1 → IsTwoComponentAt b (K b))
    (hVK : ∀ b ∈ E, b ≠ 1 → V ≤ K b)
    (hEK : ∀ a ∈ E, ∀ b ∈ E, b ≠ 1 → a ∈ coreActionKernel (K b)) :
    ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      footeTheta V a ⊓ centralizer ({b} : Set G) ≤ footeTheta V b := by
  intro a ha ha1 b hb hb1
  have hord : ∀ x ∈ E, x ≠ 1 → orderOf x = 2 := fun x hx hx1 => orderOf_eq_prime (hexp x hx) hx1
  have hVc : ∀ x ∈ E, V ≤ centralizer ({x} : Set G) := fun x hx v hv =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hVE x hx)) v hv)
  have hab : a * b = b * a := congrArg Subtype.val (isMulCommutative_iff.mp hEc ⟨a, ha⟩ ⟨b, hb⟩)
  have hVV : ∀ v ∈ V, v ∈ centralizer (V : Set G) := fun v hv => mem_centralizer_iff.mpr
    fun u hu => congrArg Subtype.val (isMulCommutative_iff.mp
      (@IsKleinFour.isMulCommutative V _ hV) ⟨u, hu⟩ ⟨v, hv⟩)
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  set Y := footeTheta V a ⊓ centralizer ({b} : Set G) with hY
  have hYa : Y ≤ oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G) :=
    inf_le_inf_right _ (footeTheta_le (hVc a ha))
  have hYodd : Odd (Nat.card Y) :=
    Odd.of_dvd_nat (odd_card_footeTheta (hVc a ha)) (card_dvd_of_le inf_le_left)
  have hVY : V ≤ normalizer (Y : Set G) := fun v hv => mem_normalizer_inf'
    (mem_normalizer_of_map_conj_eq (map_conj_footeTheta
      ((mem_centralizer_singleton_iff.mp (hVc a ha hv))) (hVV v hv)))
    (mem_normalizer_centralizer_singleton (mem_centralizer_singleton_iff.mp (hVc b hb hv)))
  have hθV := footeTheta_inf_centralizer_le (h41 a ha ha1)
  have hYO : Y ≤ oddCoreOfCentralizer b := by
    refine le_oddCoreOfCentralizer_of_le_coreActionKernel (hord a ha ha1) hab hYa
      fun J hJb hJ => ?_
    obtain ⟨-, hKb, hKpc⟩ := hK b hb hb1
    by_cases hJK : J = K b
    · rw [hJK]
      exact hYa.trans (le_coreActionKernel_of_balance hLB (hord a ha ha1) hab hKb hKpc
        (Or.inr (hEK a ha b hb hb1)))
    · have hVJ : V ≤ coreActionKernel J :=
        (hVK b hb hb1).trans (GSThmB.B5a.le_coreActionKernel_of_ne hJb hKb hJ hKpc hJK)
      have hYN : Y ≤ normalizer (J : Set G) :=
        hYa.trans (oddCoreOfCentralizer_inf_le_normalizer hLB (hord a ha ha1) hab hJb hJ)
      refine (le_commutator_sup_inf_centralizer hVp hVY hYodd).trans (sup_le ?_ ?_)
      · rw [commutator_le]
        intro y hy v hv
        rw [commutatorElement_def]
        exact mul_mem (conj_mem_coreActionKernel (hYN hy) (hVJ hv)) (inv_mem (hVJ hv))
      · exact le_coreActionKernel_of_le_oddCoreIn_centralizer hVp hVJ
          (fun x hx => hθV (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).1).1, (mem_inf.mp hx).2⟩))
          (inf_le_left.trans hYN)
  refine (le_commutator_sup_inf_centralizer hVp hVY hYodd).trans (sup_le ?_ ?_)
  · exact (commutator_mono hYO le_rfl).trans le_sup_left
  · intro x hx
    obtain ⟨hxY, hxV⟩ := mem_inf.mp hx
    exact mem_sup_right (mem_inf.mpr ⟨hYO hxY, hθV (mem_inf.mpr ⟨(mem_inf.mp hxY).1, hxV⟩)⟩)

end CFSG.ComponentClassification.FooteLit
