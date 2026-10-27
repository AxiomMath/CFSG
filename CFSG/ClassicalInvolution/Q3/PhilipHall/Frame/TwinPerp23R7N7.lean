module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7N0
import CFSG.ClassicalInvolution.Asc77.AscOddCoreNormalEng
import CFSG.ClassicalInvolution.AschTight.Sec7L714F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Vocab

variable {Y : Type} [Group Y]

@[expose] def CentMod (J : Subgroup Y) (a : Y) : Prop :=
  ∀ b ∈ J, a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf J

end Vocab

namespace F7M

variable {Y : Type} [Group Y] [Finite Y]

theorem ncard_le_two_mul (H : Subgroup Y) {X : Set Y} (c : Y)
    (hX : X ⊆ (H : Set Y) ∪ (fun h => c * h) '' (H : Set Y)) : X.ncard ≤ 2 * Nat.card H := by
  have h1 := Set.ncard_le_ncard hX (Set.toFinite _)
  have h2 := Set.ncard_union_le (H : Set Y) ((fun h => c * h) '' (H : Set Y))
  have h3 : ((fun h => c * h) '' (H : Set Y)).ncard = (H : Set Y).ncard :=
    Set.ncard_image_of_injective _ (mul_right_injective c)
  have h4 : Nat.card H = (H : Set Y).ncard := Nat.card_coe_set_eq _
  omega

theorem conjSub_eq_self_of_comm {Q : Type} [Group Q] {A : Subgroup Q} {n : Q}
    (h : ∀ x ∈ A, n * x = x * n) : conjSub n A = A := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have h1 := h _ hx
    have e : x = n⁻¹ * x * n := by
      calc x = n * (n⁻¹ * x * n) * n⁻¹ := by group
        _ = (n⁻¹ * x * n) * n * n⁻¹ := by rw [h1]
        _ = n⁻¹ * x * n := by group
    rw [e]
    exact hx
  · intro hx
    have h1 := h x hx
    have h2 : n⁻¹ * x * n = x := by
      calc n⁻¹ * x * n = n⁻¹ * (x * n) := by group
        _ = n⁻¹ * (n * x) := by rw [h1]
        _ = x := by group
    rw [h2]
    exact hx

theorem oddCoreOf_inf_le {C J : Subgroup Y} (hJC : J ≤ C) : oddCoreOf C ⊓ J ≤ oddCoreOf J := by
  refine AscFusion.le_oddCoreOf_of_normal_odd_gen inf_le_right ?_
    (Odd.of_dvd_nat (odd_natCard_oddCoreOf C) (Subgroup.card_dvd_of_le inf_le_left))
  intro j hj
  have hjO : j ∈ Subgroup.normalizer (oddCoreOf C : Set Y) := Sec7.le_normalizer_oddCoreOf C (hJC hj)
  have hjJ : j ∈ Subgroup.normalizer (J : Set Y) := Subgroup.le_normalizer hj
  rw [Subgroup.mem_normalizer_iff] at hjO hjJ ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact and_congr (hjO x) (hjJ x)

theorem centMod_of_comm_image {C J : Subgroup Y} (hJC : J ≤ C) {a : Y} (haC : a ∈ C)
    (hJ : conjSub a J = J)
    (hcomm : ∀ x ∈ (J.subgroupOf C).map (F7I.piC C), F7I.piC C ⟨a, haC⟩ * x = x * F7I.piC C ⟨a, haC⟩) :
    CentMod J a := by
  intro b hb
  have hbC := hJC hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ J := by
    have h : a * b * a⁻¹ ∈ conjSub a J := conj_mem_conjSub hb
    rw [hJ] at h
    exact J.mul_mem h (J.inv_mem hb)
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ oddCoreOf C := by
    have hbA : F7I.piC C ⟨b, hbC⟩ ∈ (J.subgroupOf C).map (F7I.piC C) :=
      ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have hc := hcomm _ hbA
    have h3 : F7I.piC C (⟨a, haC⟩ * ⟨b, hbC⟩ * (⟨a, haC⟩ : ↥C)⁻¹ * (⟨b, hbC⟩ : ↥C)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    exact (F7I.piC_eq_one_iff _).mp h3
  exact oddCoreOf_inf_le hJC ⟨h2, h1⟩

end F7M

section Steps


variable {n : ℕ}

@[expose] def P23E7W714 (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ Z : Subgroup Y, P23ZData t u e Z → ∀ w ∈ Z,
          w ∈ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) →
            CentMod (conjSub g (tightCore R)) w ∨ CentMod (conjSub g (tightCore R)) (w * t)

@[expose] def P23ECent (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ a : Y, a * a = 1 → a ∈ Subgroup.centralizer ({e} : Set Y) → CentMod (tightCore R) a →
          CentMod K' a → CentMod (conjSub g (tightCore R)) a → CentModE R e a

section Facts

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z : Subgroup Y}

theorem P23ZData.centMod (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) {a : Y}
    (ha : a ∈ Z) : CentMod (tightCore R) a ∧ CentMod K' a := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWt : W ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  have htC : t ∈ C := hWt hd.hzW
  have heC : e ∈ C := hWt heW
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hKC : tightCore R ≤ C := le_centralizer_of_unique hz
  have hK'C : K' ≤ C := le_centralizer_of_unique hz'
  set A := ((tightCore R).subgroupOf C).map (F7I.piC C) with hAdef
  set B := (K'.subgroupOf C).map (F7I.piC C) with hBdef
  obtain ⟨-, -, -, -, hAnc, -, hAB, heA, heB, -⟩ := p23_twin_q8 hc hCdef htC heC
  have hperm : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _) ∨
      (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _)
    rw [hAdef, hBdef, F7I.conjSub_map_piC, F7I.conjSub_map_piC]
    rcases p23_conj_twins hc c.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
  have hcAB := F7N.conj_cent_of_perm hperm heA heB
  set π := F7I.piC C with hπ
  set Mb := Subgroup.centralizer ((A : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) ∪ B) with hMb
  have hMbA : ∀ q ∈ Mb, ∀ x ∈ A, q * x = x * q := fun q hq x hx =>
    ((Subgroup.mem_centralizer_iff.mp hq) x (Or.inl hx)).symm
  have hMbB : ∀ q ∈ Mb, ∀ x ∈ B, q * x = x * q := fun q hq x hx =>
    ((Subgroup.mem_centralizer_iff.mp hq) x (Or.inr hx)).symm
  have htcen : ∀ x : ↥C ⧸ classicalInvolutionOddCore ↥C, π ⟨t, htC⟩ * x = x * π ⟨t, htC⟩ := by
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) x
    have hct : (c : Y) * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
    have h : (⟨t, htC⟩ : ↥C) * c = c * ⟨t, htC⟩ := Subtype.ext hct.symm
    change π _ * π c = π c * π _
    rw [← map_mul, ← map_mul, h]
  set Mc : Subgroup Y := (Mb.comap π).map C.subtype with hMcdef
  have hOM : oddCoreOf C ≤ Mc := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c, ?_, rfl⟩
    change π c ∈ Mb
    rw [(F7I.piC_eq_one_iff c).mpr ⟨c, hc, rfl⟩]
    exact Mb.one_mem
  have hQM : Subgroup.closure (({t} : Set Y) ∪ {f | ∃ c ∈ C, f = c * e * c⁻¹}) ≤ Mc := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | ⟨c, hcC, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨⟨x, htC⟩, ?_, rfl⟩
      change π ⟨x, htC⟩ ∈ Mb
      rw [Subgroup.mem_centralizer_iff]
      intro h _
      exact (htcen h).symm
    · refine ⟨⟨c, hcC⟩ * ⟨e, heC⟩ * (⟨c, hcC⟩ : ↥C)⁻¹, ?_, rfl⟩
      change π (⟨c, hcC⟩ * ⟨e, heC⟩ * (⟨c, hcC⟩ : ↥C)⁻¹) ∈ Mb
      rw [map_mul, map_mul, map_inv, Subgroup.mem_centralizer_iff]
      rintro h (hh | hh)
      · exact ((hcAB (π ⟨c, hcC⟩)).1 h hh).symm
      · exact ((hcAB (π ⟨c, hcC⟩)).2 h hh).symm
  have haM : a ∈ Mc := (hZ.cover.trans (sup_le hOM hQM)) ha
  obtain ⟨c, hcM, hca⟩ := haM
  have haC : a ∈ C := hca ▸ c.2
  have hc' : c = ⟨a, haC⟩ := Subtype.ext hca
  rw [hc'] at hcM
  have hA' := hMbA _ hcM
  have hB' := hMbB _ hcM
  have hAB' : A ≠ B := by
    intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := hAnc
    have hyB : y ∈ B := by rw [← h]; exact hy
    exact hxy (hAB x hx y hyB)
  rcases p23_conj_twins hc haC with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨F7M.centMod_of_comm_image hKC haC h1 hA', F7M.centMod_of_comm_image hK'C haC h2 hB'⟩
  · exfalso
    apply hAB'
    have h3 := F7I.conjSub_map_piC (C := C) (H := tightCore R) ⟨a, haC⟩
    rw [F7M.conjSub_eq_self_of_comm hA'] at h3
    rw [h3]
    change ((conjSub a (tightCore R)).subgroupOf C).map (F7I.piC C) = B
    rw [h1]

theorem P23ZData.card_le_two_mul_normalizer (hc : P23Cfg n Y R S t K' W u e g)
    (hZ : P23ZData t u e Z) :
    Nat.card Z ≤
      2 * Nat.card ↥(Z ⊓ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y)) := by
  have hd := hc.data
  set Kg := conjSub g (tightCore R) with hKg
  set Kg' := conjSub g K' with hKg'
  have hsw : ∀ c ∈ Z, (conjSub c Kg = Kg ∧ conjSub c Kg' = Kg') ∨
      (conjSub c Kg = Kg' ∧ conjSub c Kg' = Kg) := by
    intro c hcZ
    have hcu : c * u = u * c := (Subgroup.mem_centralizer_singleton_iff.mp (hZ.le_u hcZ))
    have hce : c * e = e * c := (Subgroup.mem_centralizer_singleton_iff.mp (hZ.le_cent hZ.he hcZ))
    have hcue : c * (u * e) = (u * e) * c := by
      calc c * (u * e) = (c * u) * e := by group
        _ = u * (c * e) := by rw [hcu]; group
        _ = u * (e * c) := by rw [hce]
        _ = (u * e) * c := by group
    have hdt : g⁻¹ * c * g ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : c * (g * t * g⁻¹) = (g * t * g⁻¹) * c := by rw [hd.hgt]; exact hcue
      calc g⁻¹ * c * g * t = g⁻¹ * (c * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * c) * g := by rw [h1]
        _ = t * (g⁻¹ * c * g) := by group
    have hcg : c * g = g * (g⁻¹ * c * g) := by group
    have key : ∀ H : Subgroup Y, conjSub c (conjSub g H) = conjSub g (conjSub (g⁻¹ * c * g) H) := by
      intro H
      rw [← conjSub_mul, ← conjSub_mul, hcg]
    rcases p23_conj_twins hc hdt with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨by rw [hKg, key, h1], by rw [hKg', key, h2]⟩
    · right
      exact ⟨by rw [hKg, hKg', key, h1], by rw [hKg, hKg', key, h2]⟩
  set N := Z ⊓ Subgroup.normalizer ((Kg : Subgroup Y) : Set Y) with hNdef
  have hmemN : ∀ c ∈ Z, conjSub c Kg = Kg → c ∈ N := fun c hcZ h =>
    ⟨hcZ, mem_normalizer_iff_conjSub_eq.mpr h⟩
  by_cases hall : ∀ c ∈ Z, conjSub c Kg = Kg
  · have hZN : Z ≤ N := fun c hcZ => hmemN c hcZ (hall c hcZ)
    have := Subgroup.card_le_of_le hZN
    omega
  · push Not at hall
    obtain ⟨c₀, hc₀Z, hc₀⟩ := hall
    have hc₀' : conjSub c₀ Kg = Kg' := by
      rcases hsw c₀ hc₀Z with h | h
      · exact absurd h.1 hc₀
      · exact h.1
    have hsub : (Z : Set Y) ⊆ (N : Set Y) ∪ (fun h => c₀ * h) '' (N : Set Y) := by
      intro c hcZ
      rcases hsw c hcZ with h | h
      · exact Or.inl (hmemN c hcZ h.1)
      · right
        refine ⟨c₀⁻¹ * c, hmemN _ (Z.mul_mem (Z.inv_mem hc₀Z) hcZ) ?_, by group⟩
        rw [conjSub_mul, h.1, ← hc₀', conjSub_inv_conjSub]
    have h1 := F7M.ncard_le_two_mul N c₀ hsub
    have h2 : Nat.card Z = (Z : Set Y).ncard := Nat.card_coe_set_eq _
    omega

end Facts

theorem p23E7N7_of_leaves (h714 : P23E7W714 n) (hcent : P23ECent n) : P23E7N7 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ Z hZd
  set A := aSub R Z e with hAdef
  have hZe : Z ≤ Subgroup.centralizer ({e} : Set Y) := hZd.le_cent hZd.he
  set N := Z ⊓ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) with hNdef
  have hstep : ∀ w ∈ Z, w ∈ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) →
      CentModE R e w ∨ CentModE R e (w * t) := by
    intro w hw hwN
    have hw2 : w * w = 1 := hZd.sq w hw
    have hwt : w * t ∈ Z := Z.mul_mem hw hZd.ht
    rcases h714 hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd w hw hwN with h | h
    · left
      obtain ⟨hK, hK'⟩ := hZd.centMod hc hw
      exact hcent hcit hP Y R S t K' W u e g hc hno hE hZ w hw2 (hZe hw) hK hK' h
    · right
      obtain ⟨hK, hK'⟩ := hZd.centMod hc hwt
      exact hcent hcit hP Y R S t K' W u e g hc hno hE hZ (w * t) (hZd.sq _ hwt) (hZe hwt) hK hK' h
  have hsub : (N : Set Y) ⊆ (A : Set Y) ∪ (fun h => t * h) '' (A : Set Y) := by
    rintro w ⟨hwZ, hwN⟩
    rcases hstep w hwZ hwN with h | h
    · exact Or.inl ((mem_aSub_iff hZe).mpr ⟨hwZ, h⟩)
    · right
      have hwt : w * t ∈ Z := Z.mul_mem hwZ hZd.ht
      refine ⟨w * t, (mem_aSub_iff hZe).mpr ⟨hwt, h⟩, ?_⟩
      show t * (w * t) = w
      rw [← mul_assoc, ← hZd.comm w hwZ t hZd.ht, mul_assoc, hZd.sq t hZd.ht, mul_one]
  have h1 := F7M.ncard_le_two_mul A t hsub
  have h2 : Nat.card N = (N : Set Y).ncard := Nat.card_coe_set_eq _
  have h3 := hZd.card_le_two_mul_normalizer hc
  rw [← hNdef] at h3
  have h4 := relIndex_mul_card_of_le (aSub_le R Z e)
  have h5 : 0 < Nat.card A := Nat.card_pos
  rw [← hAdef] at h4
  have h6 : A.relIndex Z * Nat.card A ≤ 4 * Nat.card A := by omega
  exact Nat.le_of_mul_le_mul_right h6 h5

theorem p23E7Not9C_of_w714 (h714 : P23E7W714 n) (hcent : P23ECent n) (h1 : P23E7LL1 n)
    (h2 : P23E7LL2 n) (h3 : P23E7LL3 n) : P23E7Not9C n :=
  p23E7Not9C_of_leaves (p23E7N7_of_leaves h714 hcent) h1 h2 h3

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
