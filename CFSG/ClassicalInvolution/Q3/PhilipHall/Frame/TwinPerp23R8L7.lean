module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOut
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLT237
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZO2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section L7

@[expose] def P23E8L7Sec (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
      ∀ Z : Subgroup Y, P23ZData t u e Z → ∀ f ∈ p23Orb Z t e, f ≠ e →
        aSub R Z e ⊓ aSub R Z f ≠ ⊥ →
          ∃ P₀ P₀' : Subgroup Y, IsSylow2In P₀ (tightCore R) ∧ IsSylow2In P₀' K' ∧
            P₀ ≤ Subgroup.centralizer ((aSub R Z e ⊓ aSub R Z f : Subgroup Y) : Set Y) ∧
            P₀' ≤ Subgroup.centralizer ((aSub R Z e ⊓ aSub R Z f : Subgroup Y) : Set Y) ∧
            ∃ w ∈ rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f),
              (∀ x ∈ P₀, w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f))) ∧
              (∀ x ∈ P₀', w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f))) ∧
              (w * e * w⁻¹)⁻¹ * f ∈ oddCoreOf (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f))

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem eq_one_of_odd_orderOf_of_isPGroup {Q : Type*} [Group Q] {P : Subgroup Q} (hP : IsPGroup 2 P)
    {q : Q} (hq : q ∈ P) (hodd : Odd (orderOf q)) : q = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨q, hq⟩
  have h1 : q ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  rcases j with _ | j
  · exact orderOf_eq_one_iff.mp (by simpa using hj)
  · rw [hj] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩))

theorem map_piC_sylow_eq {C P J : Subgroup Y} (hP : IsSylow2In P J) (hJC : J ≤ C)
    (h2 : IsPGroup 2 ↥((J.subgroupOf C).map (F7I.piC C))) :
    (P.subgroupOf C).map (F7I.piC C) = (J.subgroupOf C).map (F7I.piC C) := by
  have hs := isSylow2In_map_mk (N := classicalInvolutionOddCore ↥C)
    (CFSG.ComponentClassification.OddCore.odd_card ↥C) (hP.subgroupOf hJC)
  exact (hs.2.2 _ le_rfl h2 hs.1).symm

theorem p23_comm_twins_of_odd (hc : P23Cfg n Y R S t K' W u e g)
    (heC : e ∈ Subgroup.centralizer ({t} : Set Y)) {P₀ P₀' : Subgroup Y}
    (hP₀ : IsSylow2In P₀ (tightCore R)) (hP₀' : IsSylow2In P₀' K') {w : Y}
    (hw : w ∈ Subgroup.centralizer ({t} : Set Y))
    (h₁ : ∀ x ∈ P₀, Odd (orderOf (w * x * w⁻¹ * x⁻¹)))
    (h₂ : ∀ x ∈ P₀', Odd (orderOf (w * x * w⁻¹ * x⁻¹))) :
    ∀ l ∈ tightCore R ⊔ K', w * l * w⁻¹ * l⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := by
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hz : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have hKC : tightCore R ≤ C := le_centralizer_of_unique hz
  have hK'C : K' ≤ C :=
    le_centralizer_of_unique (isUniqueInvolution_of_mem_twinSet hz hc.std.hK')
  obtain ⟨c, hcw⟩ : ∃ c : ↥C, (c : Y) = w := ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨-, -, hcK, hcK', -, -, hcomm, -⟩ := p23_twin_q8 hc hCdef htC heC
  have hperm := p23_twin_perm hc hCdef (F7I.piC C c)
  have himg : (P₀.subgroupOf C).map (F7I.piC C) = ((tightCore R).subgroupOf C).map (F7I.piC C) :=
    map_piC_sylow_eq hP₀ hKC (IsPGroup.of_card (n := 3) (by rw [hcK]; norm_num))
  have himg' : (P₀'.subgroupOf C).map (F7I.piC C) = (K'.subgroupOf C).map (F7I.piC C) :=
    map_piC_sylow_eq hP₀' hK'C (IsPGroup.of_card (n := 3) (by rw [hcK']; norm_num))
  set Kb := ((tightCore R).subgroupOf C).map (F7I.piC C) with hKb
  set Kb' := (K'.subgroupOf C).map (F7I.piC C) with hKb'
  have hKb2 : IsPGroup 2 Kb := IsPGroup.of_card (n := 3) (by rw [hcK]; norm_num)
  have hKb'2 : IsPGroup 2 Kb' := IsPGroup.of_card (n := 3) (by rw [hcK']; norm_num)
  have hnorm : Kb ≤ Subgroup.normalizer (Kb' : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) :=
    fun x hx => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm)
  have hT2 : IsPGroup 2 ↥(Kb ⊔ Kb') := hKb2.to_sup_of_normal_right' hKb'2 hnorm
  have hmemconj : ∀ (H : Subgroup (↥C ⧸ classicalInvolutionOddCore ↥C))
      (x : ↥C ⧸ classicalInvolutionOddCore ↥C),
      x ∈ H → F7I.piC C c * x * (F7I.piC C c)⁻¹ ∈ conjSub (F7I.piC C c) H := by
    intro H x hx
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hx
  have hconjK : ∀ x ∈ Kb, F7I.piC C c * x * (F7I.piC C c)⁻¹ ∈ Kb ⊔ Kb' := by
    intro x hx
    have hm := hmemconj Kb x hx
    rcases hperm with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1] at hm; exact Subgroup.mem_sup_left hm
    · rw [h1] at hm; exact Subgroup.mem_sup_right hm
  have hconjK' : ∀ x ∈ Kb', F7I.piC C c * x * (F7I.piC C c)⁻¹ ∈ Kb ⊔ Kb' := by
    intro x hx
    have hm := hmemconj Kb' x hx
    rcases hperm with ⟨-, h2⟩ | ⟨-, h2⟩
    · rw [h2] at hm; exact Subgroup.mem_sup_right hm
    · rw [h2] at hm; exact Subgroup.mem_sup_left hm
  have hcomm_of : ∀ (x : Y) (hxC : x ∈ C), Odd (orderOf (w * x * w⁻¹ * x⁻¹)) →
      F7I.piC C ⟨x, hxC⟩ ∈ Kb ⊔ Kb' →
      F7I.piC C c * F7I.piC C ⟨x, hxC⟩ * (F7I.piC C c)⁻¹ ∈ Kb ⊔ Kb' →
      F7I.piC C c * F7I.piC C ⟨x, hxC⟩ = F7I.piC C ⟨x, hxC⟩ * F7I.piC C c := by
    intro x hxC hodd hx hgx
    have hqeq : F7I.piC C (c * ⟨x, hxC⟩ * c⁻¹ * (⟨x, hxC⟩ : ↥C)⁻¹) =
        F7I.piC C c * F7I.piC C ⟨x, hxC⟩ * (F7I.piC C c)⁻¹ * (F7I.piC C ⟨x, hxC⟩)⁻¹ := by
      simp only [map_mul, map_inv]
    have hqT : F7I.piC C (c * ⟨x, hxC⟩ * c⁻¹ * (⟨x, hxC⟩ : ↥C)⁻¹) ∈ Kb ⊔ Kb' := by
      rw [hqeq]
      exact Subgroup.mul_mem _ hgx (Subgroup.inv_mem _ hx)
    have hqodd : Odd (orderOf (F7I.piC C (c * ⟨x, hxC⟩ * c⁻¹ * (⟨x, hxC⟩ : ↥C)⁻¹))) := by
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd (F7I.piC C) _)
      rw [← Subgroup.orderOf_coe]
      simpa [hcw] using hodd
    have hq1 := eq_one_of_odd_orderOf_of_isPGroup hT2 hqT hqodd
    rw [hqeq] at hq1
    calc F7I.piC C c * F7I.piC C ⟨x, hxC⟩
        = (F7I.piC C c * F7I.piC C ⟨x, hxC⟩ * (F7I.piC C c)⁻¹ * (F7I.piC C ⟨x, hxC⟩)⁻¹) *
            (F7I.piC C ⟨x, hxC⟩ * F7I.piC C c) := by group
      _ = F7I.piC C ⟨x, hxC⟩ * F7I.piC C c := by rw [hq1, one_mul]
  have hcentKb : ∀ y ∈ Kb, F7I.piC C c * y = y * F7I.piC C c := by
    intro y hy
    rw [← himg] at hy
    obtain ⟨⟨x, hxC⟩, hxP, rfl⟩ := hy
    have hxKb : F7I.piC C ⟨x, hxC⟩ ∈ Kb := by
      rw [← himg]; exact Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, hxP, rfl⟩
    exact hcomm_of x hxC (h₁ x (Subgroup.mem_subgroupOf.mp hxP)) (Subgroup.mem_sup_left hxKb)
      (hconjK _ hxKb)
  have hcentKb' : ∀ y ∈ Kb', F7I.piC C c * y = y * F7I.piC C c := by
    intro y hy
    rw [← himg'] at hy
    obtain ⟨⟨x, hxC⟩, hxP, rfl⟩ := hy
    have hxKb : F7I.piC C ⟨x, hxC⟩ ∈ Kb' := by
      rw [← himg']; exact Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, hxP, rfl⟩
    exact hcomm_of x hxC (h₂ x (Subgroup.mem_subgroupOf.mp hxP)) (Subgroup.mem_sup_right hxKb)
      (hconjK' _ hxKb)
  set H : Subgroup Y :=
    ((Subgroup.centralizer ({F7I.piC C c} : Set (↥C ⧸ classicalInvolutionOddCore ↥C))).comap
      (F7I.piC C)).map C.subtype with hHdef
  have hle : ∀ L : Subgroup Y, L ≤ C → (∀ y ∈ (L.subgroupOf C).map (F7I.piC C),
      F7I.piC C c * y = y * F7I.piC C c) → L ≤ H := by
    intro L hLC hL k hk
    refine ⟨⟨k, hLC hk⟩, Subgroup.mem_comap.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr ?_), rfl⟩
    exact (hL _ (F7I.mem_map_piC.mpr ⟨⟨k, hLC hk⟩, hk, rfl⟩)).symm
  intro l hl
  obtain ⟨l', hl', rfl⟩ := sup_le (hle _ hKC hcentKb) (hle _ hK'C hcentKb') hl
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hl')
  have h2 : F7I.piC C (c * l' * c⁻¹ * l'⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [← h1]
    group
  have h3 := (F7I.piC_eq_one_iff _).mp h2
  simpa [hcw] using h3

theorem p23_mOrb_of_sec (hc : P23Cfg n Y R S t K' W u e g) {H P₀ P₀' : Subgroup Y}
    (hP₀ : IsSylow2In P₀ (tightCore R)) (hP₀' : IsSylow2In P₀' K') (hP₀H : P₀ ≤ H) (hP₀'H : P₀' ≤ H)
    {f w : Y} (he2 : e * e = 1) (hf2 : f * f = 1) (heC : e ∈ Subgroup.centralizer ({t} : Set Y))
    (hfC : f ∈ Subgroup.centralizer ({t} : Set Y)) (hfH : f ∈ H)
    (h₁ : ∀ x ∈ P₀, w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf H) (h₂ : ∀ x ∈ P₀', w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf H)
    (h₃ : (w * e * w⁻¹)⁻¹ * f ∈ oddCoreOf H) : P23MOrb R K' t e f := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hK₀ : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have htP : t ∈ P₀ := LemL.mem_sylow_of_isUniqueInvolution hC.hyp hK₀ hP₀ hz
  have htH : t ∈ H := hP₀H htP
  have hNodd : Odd (Nat.card ↥(oddCoreOf H)) := oddCoreOf_odd_natCard H
  have hab : t⁻¹ * (w * t * w⁻¹) ∈ oddCoreOf H := by
    have h := T7R.conj_mem_oddCoreOf (H.inv_mem htH) (h₁ t htP)
    rwa [show t⁻¹ * (w * t * w⁻¹ * t⁻¹) * t⁻¹⁻¹ = t⁻¹ * (w * t * w⁻¹) by group] at h
  have hwt2 : (w * t * w⁻¹) * (w * t * w⁻¹) = 1 := by
    calc (w * t * w⁻¹) * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  obtain ⟨v, hv, hvt⟩ := ClsM.exists_mem_conj_of_odd hNodd hz.sq hwt2 hab
  have hw₀C : v * w ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc v * w * t = v * (w * t * w⁻¹) * v⁻¹ * (v * w) := by group
      _ = t * (v * w) := by rw [← hvt]
  have hb1 : f⁻¹ * ((v * w) * e * (v * w)⁻¹) ∈ oddCoreOf H := by
    have h4 := T7R.conj_mem_oddCoreOf (H.inv_mem hfH) hv
    have h5 := (oddCoreOf H).inv_mem h₃
    have h6 := (oddCoreOf H).inv_mem hv
    have h7 := (oddCoreOf H).mul_mem ((oddCoreOf H).mul_mem h4 h5) h6
    rwa [show f⁻¹ * v * f⁻¹⁻¹ * ((w * e * w⁻¹)⁻¹ * f)⁻¹ * v⁻¹ =
      f⁻¹ * ((v * w) * e * (v * w)⁻¹) by group] at h7
  have hb2 : f⁻¹ * ((v * w) * e * (v * w)⁻¹) ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hfC)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hw₀C heC) (Subgroup.inv_mem _ hw₀C))
  have hNt : Odd (Nat.card ↥(oddCoreOf H ⊓ Subgroup.centralizer ({t} : Set Y))) :=
    hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hb22 : ((v * w) * e * (v * w)⁻¹) * ((v * w) * e * (v * w)⁻¹) = 1 := by
    calc ((v * w) * e * (v * w)⁻¹) * ((v * w) * e * (v * w)⁻¹) = (v * w) * (e * e) * (v * w)⁻¹ := by
          group
      _ = 1 := by rw [he2]; group
  obtain ⟨v', hv', hfv⟩ := ClsM.exists_mem_conj_of_odd hNt hf2 hb22 ⟨hb1, hb2⟩
  have hw₁C : v' * (v * w) ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mul_mem _ hv'.2 hw₀C
  have hfw₁ : f = (v' * (v * w)) * e * (v' * (v * w))⁻¹ := by rw [hfv]; group
  have hvv : v' * v ∈ oddCoreOf H := (oddCoreOf H).mul_mem hv'.1 hv
  have hcomm₁ : ∀ x ∈ H, w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf H →
      (v' * (v * w)) * x * (v' * (v * w))⁻¹ * x⁻¹ ∈ oddCoreOf H := by
    intro x hx hwx
    have h8 := T7R.conj_mem_oddCoreOf hx ((oddCoreOf H).inv_mem hvv)
    have h9 := (oddCoreOf H).mul_mem ((oddCoreOf H).mul_mem hvv hwx) h8
    rwa [show v' * v * (w * x * w⁻¹ * x⁻¹) * (x * (v' * v)⁻¹ * x⁻¹) =
      (v' * (v * w)) * x * (v' * (v * w))⁻¹ * x⁻¹ by group] at h9
  have hoddN : ∀ y ∈ oddCoreOf H, Odd (orderOf y) := fun y hy =>
    hNodd.of_dvd_nat (by rw [← Subgroup.orderOf_mk y hy]; exact orderOf_dvd_natCard _)
  have hM := p23_comm_twins_of_odd hc heC hP₀ hP₀' hw₁C
    (fun x hx => hoddN _ (hcomm₁ x (hP₀H hx) (h₁ x hx)))
    (fun x hx => hoddN _ (hcomm₁ x (hP₀'H hx) (h₂ x hx)))
  exact ⟨v' * (v * w), hw₁C, hM, 1, Subgroup.one_mem _, by rw [hfw₁]; group⟩

theorem p23E8OL7_of_sec (h : P23E8L7Sec n) : P23E8OL7 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 Z hZd f hf hne
  by_cases hfe : f = e
  · subst hfe
    refine ⟨1, Subgroup.one_mem _, fun l _ => ?_, 1, Subgroup.one_mem _, by group⟩
    rw [show (1 : Y) * l * 1⁻¹ * l⁻¹ = 1 by group]
    exact Subgroup.one_mem _
  obtain ⟨P₀, P₀', hP₀, hP₀', hP₀V, hP₀'V, w, -, h₁, h₂, h₃⟩ :=
    h hcit hP Y R S t K' W u e g hc hno hA5 hA6 Z hZd f hf hfe hne
  have hK₀ : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hVZ : aSub R Z e ⊓ aSub R Z f ≤ Z := inf_le_left.trans (aSub_le R Z e)
  have hfX := (LemL.p23_cover_V hc hZd hVZ hf inf_le_right).1
  obtain ⟨m, hm, hfm⟩ := id hf
  have hfZ : f ∈ Z := by
    rw [hfm]
    exact (Subgroup.mem_normalizer_iff.mp hm.2 e).mp hZd.he
  exact p23_mOrb_of_sec hc hP₀ hP₀'
    (LemL.le_rLayerSub_of_mem (mem_RSet_of_isSylow2In hK₀ hP₀) hP₀V)
    (LemL.le_rLayerSub_of_mem (mem_RSet_of_isSylow2In hK'Ω hP₀') hP₀'V)
    (hZd.sq e hZd.he) (hZd.sq f hfZ) (hZd.le_t hZd.he) (hZd.le_t hfZ) hfX h₁ h₂ h₃

end L7

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
