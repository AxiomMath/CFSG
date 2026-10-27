module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLCen
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
open scoped commutatorElement

section Odd

theorem exists_odd_lift {G H : Type} [Group G] [Finite G] [Group H] (ψ : G →* H) {y : H}
    (hy : y ∈ ψ.range) (hodd : Odd (orderOf y)) : ∃ w : G, ψ w = y ∧ Odd (orderOf w) := by
  obtain ⟨w₀, rfl⟩ := hy
  obtain ⟨a, m, hm, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w₀).ne'
  have h2r : ¬ 2 ∣ orderOf (ψ w₀) := fun h => by
    have := Nat.odd_iff.mp hodd
    omega
  have hcop : Nat.Coprime (2 ^ a) (orderOf (ψ w₀)) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2r)
  obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(w₀ ^ 2 ^ a) ^ s, ?_, ?_⟩
  · rw [map_pow, map_pow, hs]
  · have h1 : orderOf (w₀ ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (by positivity) ⟨m, ho⟩, ho]
      exact Nat.mul_div_cancel_left m (by positivity)
    have h3 : orderOf ((w₀ ^ 2 ^ a) ^ s) ∣ m := by
      rw [← h1]
      exact orderOf_pow_dvd s
    exact hm.of_dvd_nat h3

theorem comm_eq_one_of_odd {G : Type} [Group G] {w x : G} (hw : Odd (orderOf w))
    (hc : w * x * w⁻¹ * x⁻¹ ∈ Subgroup.center G) (h2 : ∃ j : ℕ, (w * x * w⁻¹ * x⁻¹) ^ (2 ^ j) = 1) :
    w * x * w⁻¹ * x⁻¹ = 1 := by
  set c := w * x * w⁻¹ * x⁻¹ with hcdef
  obtain ⟨j, hj⟩ := h2
  have hxw : x * w⁻¹ * x⁻¹ = w⁻¹ * c := by rw [hcdef]; group
  have hr : (x * w⁻¹ * x⁻¹) ^ (orderOf w) = 1 := by
    rw [conj_pow, inv_pow, pow_orderOf_eq_one, inv_one, mul_one, mul_inv_cancel]
  have hcomm : Commute w⁻¹ c := Subgroup.mem_center_iff.mp hc w⁻¹
  rw [hxw, hcomm.mul_pow, inv_pow, pow_orderOf_eq_one, inv_one, one_mul] at hr
  have h2r : ¬ 2 ∣ orderOf w := fun h => by
    have := Nat.odd_iff.mp hw
    omega
  have hcop : Nat.Coprime (orderOf w) (2 ^ j) :=
    (Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2r)).symm
  have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hr)
    (orderOf_dvd_of_pow_eq_one hj)
  exact orderOf_eq_one_iff.mp h1

end Odd

section Solvable

theorem not_isSolvable_map {G H : Type} [Group G] [Group H] (ψ : G →* H)
    (hker : ∀ x : G, ψ x = 1 → x ∈ Subgroup.center G) {E : Subgroup G}
    (hE : ¬ Group.IsSolvable ↥E) : ¬ Group.IsSolvable ↥(E.map ψ) := by
  intro hs
  apply hE
  let g : ↥E →* ↥(E.map ψ) := ψ.subgroupMap E
  have hcent : ∀ a : ↥g.ker, ((a : ↥E) : G) ∈ Subgroup.center G := by
    intro a
    apply hker
    have h1 := MonoidHom.mem_ker.mp a.2
    exact congrArg Subtype.val h1
  haveI : Group.IsSolvable ↥g.ker := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subtype.ext ((Subgroup.mem_center_iff.mp (hcent a) ((b : ↥E) : G)).symm))
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])

end Solvable

section Cover

variable {G : Type} [Group G] [Finite G]

theorem exists_surj_secImage_of_cover {X E E₀ : Subgroup G} (hE₀X : E₀ ≤ X) (hE₀E : E₀ ≤ E)
    (hcov : E ≤ oddCoreOf E ⊔ E₀) {Q : Type} [Group Q] (π : ↥E →* Q) (hπs : Function.Surjective π)
    (hπO : classicalInvolutionOddCore ↥E ≤ π.ker) :
    ∃ σ : ↥(secImage X E₀) →* Q, Function.Surjective σ := by
  set N := classicalInvolutionOddCore ↥X with hN
  let ι : ↥(E₀.subgroupOf X) →* ↥(secImage X E₀) :=
    (QuotientGroup.mk' N).subgroupMap (E₀.subgroupOf X)
  have hι : Function.Surjective ι := MonoidHom.subgroupMap_surjective _ _
  let e1 : ↥(E₀.subgroupOf X) ≃* ↥E₀ := Subgroup.subgroupOfEquivOfLe hE₀X
  let π₀ : ↥(E₀.subgroupOf X) →* Q :=
    π.comp ((Subgroup.inclusion hE₀E).comp e1.toMonoidHom)
  have hπ₀ : ∀ (x : ↥(E₀.subgroupOf X)) (hx : ((x : ↥X) : G) ∈ E),
      π₀ x = π ⟨((x : ↥X) : G), hx⟩ := fun x hx => rfl
  have hker : ι.ker ≤ π₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxE₀ : ((x : ↥X) : G) ∈ E₀ := Subgroup.mem_subgroupOf.mp x.2
    have hxN : (x : ↥X) ∈ N := by
      have h1 : QuotientGroup.mk' N (x : ↥X) = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hxO : ((x : ↥X) : G) ∈ oddCoreOf X := mem_oddCoreOf_iff.mpr ⟨(x : ↥X).2, hxN⟩
    have hN'le : oddCoreOf X ⊓ E₀ ≤ oddCoreOf E := inf_oddCoreOf_le_of_cover hE₀E hE₀X hcov
    obtain ⟨hxE, hxEO⟩ := mem_oddCoreOf_iff.mp (hN'le ⟨hxO, hxE₀⟩)
    rw [hπ₀ x hxE]
    exact hπO hxEO
  have hπ₀s : Function.Surjective π₀ := by
    intro s
    obtain ⟨y, rfl⟩ := hπs s
    have hyE : (y : G) ∈ ((oddCoreOf E ⊔ E₀ : Subgroup G) : Set G) := hcov y.2
    have hBN : E₀ ≤ Subgroup.normalizer (oddCoreOf E : Set G) :=
      hE₀E.trans (Sec7.le_normalizer_oddCoreOf E)
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN] at hyE
    obtain ⟨o, ho, w, hw, hyow⟩ := hyE
    refine ⟨⟨⟨w, hE₀X hw⟩, Subgroup.mem_subgroupOf.mpr hw⟩, ?_⟩
    obtain ⟨hoE, hoEO⟩ := mem_oddCoreOf_iff.mp ho
    have hyeq : y = ⟨o, hoE⟩ * ⟨w, hE₀E hw⟩ := Subtype.ext hyow.symm
    rw [hπ₀ _ (hE₀E hw), hyeq, map_mul, hπO hoEO, one_mul]
  refine ⟨MonoidHom.liftOfSurjective ι hι ⟨π₀, hker⟩, fun s => ?_⟩
  obtain ⟨x, rfl⟩ := hπ₀s s
  exact ⟨ι x, MonoidHom.liftOfRightInverse_comp_apply ι _ _ ⟨π₀, hker⟩ x⟩

theorem centMod_of_central_cover {X E H : Subgroup G} (hHE : H ≤ E) (hHX : H ≤ X)
    (hcov : E ≤ oddCoreOf E ⊔ H) {a : G} (haX : a ∈ X)
    (hcen : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨a, haX⟩ ∈ Subgroup.center (SecQuot X))
    (haH : ∀ y ∈ H, a * y * a⁻¹ ∈ H) (haO : ∀ o ∈ oddCoreOf E, a * o * a⁻¹ ∈ oddCoreOf E) :
    ∀ z ∈ E, a * z * a⁻¹ * z⁻¹ ∈ oddCoreOf E := by
  have hOEn : E ≤ Subgroup.normalizer (oddCoreOf E : Set G) := Sec7.le_normalizer_oddCoreOf E
  have hinfN : oddCoreOf X ⊓ H ≤ oddCoreOf E := inf_oddCoreOf_le_of_cover hHE hHX hcov
  intro z hz
  have hz' : z ∈ ((oddCoreOf E ⊔ H : Subgroup G) : Set G) := hcov hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hHE.trans hOEn)] at hz'
  obtain ⟨o, ho, h, hh, rfl⟩ := hz'
  have hcomm : a * h * a⁻¹ * h⁻¹ ∈ oddCoreOf E := by
    have h1 := comm_mem_oddCore_of_central (h := ⟨h, hHX hh⟩) hcen
    have h2 : a * h * a⁻¹ * h⁻¹ ∈ oddCoreOf X :=
      mem_oddCoreOf_iff.mpr ⟨((⟨a, haX⟩ * ⟨h, hHX hh⟩ * ⟨a, haX⟩⁻¹ * ⟨h, hHX hh⟩⁻¹ : ↥X)).2, h1⟩
    have h3 : a * h * a⁻¹ * h⁻¹ ∈ H := H.mul_mem (haH h hh) (H.inv_mem hh)
    exact hinfN ⟨h2, h3⟩
  have hao : a * o * a⁻¹ ∈ oddCoreOf E := haO o ho
  have e : a * (o * h) * a⁻¹ * (o * h)⁻¹ = (a * o * a⁻¹) * (a * h * a⁻¹ * h⁻¹) * o⁻¹ := by group
  rw [e]
  exact (oddCoreOf E).mul_mem ((oddCoreOf E).mul_mem hao hcomm) ((oddCoreOf E).inv_mem ho)

end Cover

section EaLemmas

variable {G : Type} [Group G]

theorem conj_mem_Ea {Φ : Set (Subgroup G)} (hΦ : ∀ L ∈ Φ, ∀ g : G, conjSub g L ∈ Φ) (g a : G) {x : G}
    (hx : x ∈ Ea Φ a) : g * x * g⁻¹ ∈ Ea Φ (g * a * g⁻¹) := by
  have h : Ea Φ a ≤ (Ea Φ (g * a * g⁻¹)).comap (MulAut.conj g).toMonoidHom := by
    refine Ea_le fun L hL hLa => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h2 : conjSub g L ≤ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
      intro y hy
      rw [mem_conjSub_iff] at hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hLa hy)
      calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
        _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = g * a * g⁻¹ * y := by group
    exact le_Ea (hΦ L hL g) h2
  exact h hx

theorem Ea_mul_central (Φ : Set (Subgroup G)) {a z : G} (hz : z ∈ Subgroup.center G) :
    Ea Φ (a * z) = Ea Φ a := by
  have key : ∀ L : Subgroup G, L ≤ Subgroup.centralizer ({a * z} : Set G) ↔
      L ≤ Subgroup.centralizer ({a} : Set G) := by
    intro L
    constructor
    · intro h x hx
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hx)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzc := Subgroup.mem_center_iff.mp hz x
      calc x * a = (x * (a * z)) * z⁻¹ := by group
        _ = ((a * z) * x) * z⁻¹ := by rw [h1]
        _ = a * (z * x) * z⁻¹ := by group
        _ = a * (x * z) * z⁻¹ := by rw [hzc]
        _ = a * x := by group
    · intro h x hx
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hx)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzc := Subgroup.mem_center_iff.mp hz x
      calc x * (a * z) = (x * a) * z := by group
        _ = (a * x) * z := by rw [h1]
        _ = a * (x * z) := by group
        _ = a * (z * x) := by rw [hzc]
        _ = (a * z) * x := by group
  apply le_antisymm
  · exact Ea_le fun L hL h => le_Ea hL ((key L).mp h)
  · exact Ea_le fun L hL h => le_Ea hL ((key L).mpr h)

end EaLemmas

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
