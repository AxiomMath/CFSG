module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Phi
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7M1
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23CtBase
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

namespace F7J

variable {Q : Type} [Group Q] [Finite Q]

theorem comm_mul_left_of_commute {a b c : Q} (hab : a * b = b * a) (hac : a * c = c * a)
    (ha2 : a * a = 1) : (a * b) * (a * c) * (a * b)⁻¹ * (a * c)⁻¹ = b * c * b⁻¹ * c⁻¹ := by
  have hca : a⁻¹ * c⁻¹ = c⁻¹ * a⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hac]
  calc (a * b) * (a * c) * (a * b)⁻¹ * (a * c)⁻¹ = a * (b * a) * c * b⁻¹ * a⁻¹ * c⁻¹ * a⁻¹ := by
        group
    _ = a * (a * b) * c * b⁻¹ * a⁻¹ * c⁻¹ * a⁻¹ := by rw [hab]
    _ = (a * a) * b * c * b⁻¹ * (a⁻¹ * c⁻¹) * a⁻¹ := by group
    _ = (a * a) * b * c * b⁻¹ * (c⁻¹ * a⁻¹) * a⁻¹ := by rw [hca]
    _ = (a * a) * (b * c * b⁻¹ * c⁻¹) * (a * a)⁻¹ := by group
    _ = b * c * b⁻¹ * c⁻¹ := by rw [ha2]; group

theorem mem_pCoreOf_of_conj_comm {M : Subgroup Q} {x : Q} (hxM : x ∈ M) (hx2 : x * x = 1)
    (hcomm : ∀ m ∈ M, x * (m * x * m⁻¹) = (m * x * m⁻¹) * x) : x ∈ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Set Q := {y | ∃ m ∈ M, y = m * x * m⁻¹} with hXdef
  set N := Subgroup.closure X with hNdef
  have hXc : ∀ y ∈ X, ∀ z ∈ X, y * z = z * y := by
    rintro _ ⟨m₁, hm₁, rfl⟩ _ ⟨m₂, hm₂, rfl⟩
    have h := hcomm (m₁⁻¹ * m₂) (M.mul_mem (M.inv_mem hm₁) hm₂)
    calc m₁ * x * m₁⁻¹ * (m₂ * x * m₂⁻¹)
        = m₁ * (x * ((m₁⁻¹ * m₂) * x * (m₁⁻¹ * m₂)⁻¹)) * m₁⁻¹ := by group
      _ = m₁ * (((m₁⁻¹ * m₂) * x * (m₁⁻¹ * m₂)⁻¹) * x) * m₁⁻¹ := by rw [h]
      _ = m₂ * x * m₂⁻¹ * (m₁ * x * m₁⁻¹) := by group
  have hNc := F7I.closure_comm hXc
  have hN2 : ∀ y ∈ N, y * y = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨m, -, rfl⟩ := hy
      calc m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    | one => exact mul_one 1
    | mul y z hy hz ihy ihz =>
      calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [hNc z hz y hy]
        _ = (y * y) * (z * z) := by group
        _ = 1 := by rw [ihy, ihz, one_mul]
    | inv y hy ih =>
      rw [← mul_inv_rev, ih, inv_one]
  have hNp : IsPGroup 2 N := by
    intro y
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (hN2 y y.2)
  have hNM : N ≤ M := by
    rw [hNdef, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    exact M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)
  have hconj : ∀ m ∈ M, ∀ y ∈ N, m * y * m⁻¹ ∈ N := by
    intro m hm y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨m₁, hm₁, rfl⟩ := hy
      refine Subgroup.subset_closure ⟨m * m₁, M.mul_mem hm hm₁, ?_⟩
      group
    | one => rw [mul_one, mul_inv_cancel]; exact N.one_mem
    | mul y z _ _ ihy ihz =>
      have e : m * (y * z) * m⁻¹ = (m * y * m⁻¹) * (m * z * m⁻¹) := by group
      rw [e]
      exact N.mul_mem ihy ihz
    | inv y _ ih =>
      have e : m * y⁻¹ * m⁻¹ = (m * y * m⁻¹)⁻¹ := by group
      rw [e]
      exact N.inv_mem ih
  have hMN : M ≤ Subgroup.normalizer (N : Set Q) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj m hm y
    · intro hy
      have := hconj m⁻¹ (M.inv_mem hm) _ hy
      have e : m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y := by group
      rwa [e] at this
  have hxN : x ∈ N := Subgroup.subset_closure ⟨1, M.one_mem, by group⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNM hMN hNp hxN

theorem pCoreOf_normal {M : Subgroup Q} (hMn : M.Normal) : (pCoreOf 2 M).Normal := by
  haveI := CFSG.LieType.BorelTits.pCore_characteristic 2 (G := ↥M)
  refine ⟨fun x hx g => ?_⟩
  have hg : g ∈ Subgroup.normalizer ((M : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hMn.conj_mem h hh g, fun hh => ?_⟩
    have := hMn.conj_mem _ hh g⁻¹
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at this
  have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (CFSG.Open.pCore 2 ↥M) hg
  exact (Subgroup.mem_normalizer_iff.mp this x).mp hx

theorem conj_comm_of_mbar {M : Subgroup Q} (hMn : M.Normal) {eb : Q} (heM : eb ∈ M)
    (he2 : eb * eb = 1) (hcomm : ∀ m ∈ M, eb * (m * eb * m⁻¹) = (m * eb * m⁻¹) * eb)
    (T : Sylow 2 Q) (hT : ∀ x ∈ (T : Subgroup Q), x * eb = eb * x) (q : Q) :
    eb * (q * eb * q⁻¹) = (q * eb * q⁻¹) * eb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := q * eb * q⁻¹ with hf
  have hfM : f ∈ M := hMn.conj_mem eb heM q
  have hf2 : f * f = 1 := by
    rw [hf]
    calc q * eb * q⁻¹ * (q * eb * q⁻¹) = q * (eb * eb) * q⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have hfc : ∀ m ∈ M, f * (m * f * m⁻¹) = (m * f * m⁻¹) * f := by
    intro m hm
    have h := hcomm (q⁻¹ * m * q) (by
      have := hMn.conj_mem m hm q⁻¹
      rwa [inv_inv] at this)
    rw [hf]
    calc q * eb * q⁻¹ * (m * (q * eb * q⁻¹) * m⁻¹)
        = q * (eb * ((q⁻¹ * m * q) * eb * (q⁻¹ * m * q)⁻¹)) * q⁻¹ := by group
      _ = q * (((q⁻¹ * m * q) * eb * (q⁻¹ * m * q)⁻¹) * eb) * q⁻¹ := by rw [h]
      _ = m * (q * eb * q⁻¹) * m⁻¹ * (q * eb * q⁻¹) := by group
  have hfO := mem_pCoreOf_of_conj_comm hfM hf2 hfc
  haveI := pCoreOf_normal hMn
  have hfT : f ∈ (T : Subgroup Q) :=
    IsPGroup.le_sylow_of_normal (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) T hfO
  exact (hT f hfT).symm

end F7J



section AE

variable {n : ℕ}

@[expose] def P23E8UEComm (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → SecAE R u 5 →
      ∀ m ∈ Subgroup.centralizer ({u} : Set Y),
        (u * e) * (m * (u * e) * m⁻¹) * (u * e)⁻¹ * (m * (u * e) * m⁻¹)⁻¹ ∈
          oddCoreOf (Subgroup.centralizer ({u} : Set Y))

theorem p23E8PhiAE_of_comm (hU : P23E8UEComm n) : P23E8PhiAE n := by
  intro hcit hP Y _ _ R S t K' W u e g hc _ hAE5 _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  have huC : u ∈ C := hWt hd.huW
  set A := ((tightCore R).subgroupOf C).map (F7I.piC C) with hAdef
  set B := (K'.subgroupOf C).map (F7I.piC C) with hBdef
  obtain ⟨qA, -, -, -, -, -, -, heA, heB, b₁, b', hub, ha, hb, -⟩ := p23_twin_q8 hc hCdef htC heC
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
  have hu' : (⟨u, huC⟩ : ↥C) = b₁ * b' := Subtype.ext hub.symm
  set M := Subgroup.centralizer ((A : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) ∪ B) with hMdef
  have hmemM : ∀ w, (∀ a ∈ A, w * a = a * w) → (∀ a ∈ B, w * a = a * w) → w ∈ M := by
    intro w hwA hwB
    rw [Subgroup.mem_centralizer_iff]
    rintro h (hh | hh)
    · exact (hwA h hh).symm
    · exact (hwB h hh).symm
  have hMcomm : ∀ w ∈ M, (∀ a ∈ A, w * a = a * w) ∧ (∀ a ∈ B, w * a = a * w) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff] at hw
    exact ⟨fun a ha => (hw a (Or.inl ha)).symm, fun a ha => (hw a (Or.inr ha)).symm⟩
  have hMn : M.Normal := by
    constructor
    intro w hw q
    obtain ⟨hwA, hwB⟩ := hMcomm w hw
    have key : ∀ y : ↥C ⧸ classicalInvolutionOddCore ↥C, (q⁻¹ * y * q ∈ A ∨ q⁻¹ * y * q ∈ B) →
        q * w * q⁻¹ * y = y * (q * w * q⁻¹) := by
      intro y hy
      have h1 : w * (q⁻¹ * y * q) = (q⁻¹ * y * q) * w := by
        rcases hy with hy | hy
        · exact hwA _ hy
        · exact hwB _ hy
      calc q * w * q⁻¹ * y = q * (w * (q⁻¹ * y * q)) * q⁻¹ := by group
        _ = q * ((q⁻¹ * y * q) * w) * q⁻¹ := by rw [h1]
        _ = y * (q * w * q⁻¹) := by group
    have hmem : ∀ (H : Subgroup (↥C ⧸ classicalInvolutionOddCore ↥C)) y, y ∈ H →
        q⁻¹ * y * q ∈ conjSub q⁻¹ H := by
      intro H y hy
      rw [mem_conjSub_iff]
      have e : q⁻¹⁻¹ * (q⁻¹ * y * q) * q⁻¹ = y := by group
      rw [e]
      exact hy
    apply hmemM
    · intro y hy
      apply key
      rcases hperm q⁻¹ with ⟨h1, -⟩ | ⟨h1, -⟩
      · left; rw [← h1]; exact hmem A y hy
      · right; rw [← h1]; exact hmem A y hy
    · intro y hy
      apply key
      rcases hperm q⁻¹ with ⟨-, h1⟩ | ⟨-, h1⟩
      · right; rw [← h1]; exact hmem B y hy
      · left; rw [← h1]; exact hmem B y hy
  have hlift : ∀ w ∈ M, ∃ c' : ↥C, (c' : Y) * u = u * c' ∧ F7I.piC C c' = w := by
    intro w hw
    obtain ⟨hwA, hwB⟩ := hMcomm w hw
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) w
    change ∃ c' : ↥C, (c' : Y) * u = u * c' ∧ F7I.piC C c' = F7I.piC C c
    change ∀ a ∈ A, F7I.piC C c * a = a * F7I.piC C c at hwA
    change ∀ a ∈ B, F7I.piC C c * a = a * F7I.piC C c at hwB
    have hwu : F7I.piC C c * F7I.piC C ⟨u, huC⟩ = F7I.piC C ⟨u, huC⟩ * F7I.piC C c := by
      rw [hu', map_mul]
      calc F7I.piC C c * (F7I.piC C b₁ * F7I.piC C b')
          = (F7I.piC C c * F7I.piC C b₁) * F7I.piC C b' := by group
        _ = (F7I.piC C b₁ * F7I.piC C c) * F7I.piC C b' := by rw [hwA _ ha]
        _ = F7I.piC C b₁ * (F7I.piC C c * F7I.piC C b') := by group
        _ = F7I.piC C b₁ * (F7I.piC C b' * F7I.piC C c) := by rw [hwB _ hb]
        _ = _ := by group
    have huu : (⟨u, huC⟩ : ↥C) * ⟨u, huC⟩ = 1 := Subtype.ext hd.hu2
    have hprod : F7I.piC C (⟨u, huC⟩ * (c * ⟨u, huC⟩ * c⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hwu, mul_inv_cancel_right, ← map_mul, huu,
        map_one]
    have hO1 : u * ((c : Y) * u * (c : Y)⁻¹) ∈ oddCoreOf C := (F7I.piC_eq_one_iff _).mp hprod
    have hodd : Odd (orderOf (u * ((c : Y) * u * (c : Y)⁻¹))) :=
      Odd.of_dvd_nat (oddCoreOf_odd_natCard C) (Subgroup.orderOf_dvd_natCard _ hO1)
    have hx2 : ((c : Y) * u * (c : Y)⁻¹) * (c * u * c⁻¹) = 1 := by
      calc ((c : Y) * u * (c : Y)⁻¹) * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
        _ = 1 := by rw [hd.hu2, mul_one]; simp
    obtain ⟨k, hk⟩ := T3Core.exists_conj_of_mul_mem_odd hd.hu2 hx2 hodd
    have hgO : (u * ((c : Y) * u * (c : Y)⁻¹)) ^ k ∈ oddCoreOf C := (oddCoreOf C).pow_mem hO1 k
    have hgC : (u * ((c : Y) * u * (c : Y)⁻¹)) ^ k ∈ C := oddCoreOf_le_self C hgO
    refine ⟨⟨_, C.inv_mem hgC⟩ * c, ?_, ?_⟩
    · show ((u * ((c : Y) * u * (c : Y)⁻¹)) ^ k)⁻¹ * c * u = u * (((u * ((c : Y) * u * (c : Y)⁻¹)) ^ k)⁻¹ * c)
      set gg := (u * ((c : Y) * u * (c : Y)⁻¹)) ^ k
      calc gg⁻¹ * c * u = gg⁻¹ * ((c : Y) * u * (c : Y)⁻¹) * c := by group
        _ = gg⁻¹ * (gg * u * gg⁻¹) * c := by rw [hk]
        _ = u * (gg⁻¹ * c) := by group
    · rw [map_mul, (F7I.piC_eq_one_iff _).mpr ((oddCoreOf C).inv_mem hgO), one_mul]
  set X := oddCoreOf (Subgroup.centralizer ({u} : Set Y)) ⊓ C with hXdef
  have hXC : X ≤ C := inf_le_right
  set P := (X.subgroupOf C).map (F7I.piC C) with hPdef
  have hPodd : Odd (Nat.card P) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv]
    exact Odd.of_dvd_nat (oddCoreOf_odd_natCard _) (Subgroup.card_dvd_of_le inf_le_left)
  have hMP : M ≤ Subgroup.normalizer (P : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) := by
    intro w hw
    obtain ⟨c', hc'u, rfl⟩ := hlift w hw
    have hc'U : (c' : Y) ∈ Subgroup.centralizer ({u} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hc'u
    have hcX : conjSub (c' : Y) X = X := by
      apply mem_normalizer_iff_conjSub_eq.mp
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := Subgroup.mem_normalizer_iff.mp
        (Sec7.le_normalizer_oddCoreOf (Subgroup.centralizer ({u} : Set Y)) hc'U) h
      have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer c'.2) h
      constructor
      · rintro ⟨ha1, ha2⟩
        exact ⟨h1.mp ha1, h2.mp ha2⟩
      · rintro ⟨ha1, ha2⟩
        exact ⟨h1.mpr ha1, h2.mpr ha2⟩
    apply mem_normalizer_iff_conjSub_eq.mpr
    rw [hPdef, F7I.conjSub_map_piC, hcX]
  set ee := F7I.piC C ⟨e, heC⟩ with hee
  have heM : ee ∈ M := hmemM _ heA heB
  have hee2 : ee * ee = 1 := by
    rw [hee, ← map_mul]
    have : (⟨e, heC⟩ : ↥C) * ⟨e, heC⟩ = 1 := Subtype.ext hd.he2
    rw [this, map_one]
  have hcommM : ∀ m ∈ M, ee * (m * ee * m⁻¹) = (m * ee * m⁻¹) * ee := by
    intro m hm
    obtain ⟨m', hm'u, rfl⟩ := hlift m hm
    have hm'U : (m' : Y) ∈ Subgroup.centralizer ({u} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hm'u
    set f : ↥C := m' * ⟨e, heC⟩ * m'⁻¹ with hfdef
    set w1 : ↥C := ⟨e, heC⟩ * f * ⟨e, heC⟩⁻¹ * f⁻¹ with hw1
    have hue : u * e = e * u := hWab u hd.huW e heW
    have huf : u * (f : Y) = (f : Y) * u := by
      show u * ((m' : Y) * e * (m' : Y)⁻¹) = ((m' : Y) * e * (m' : Y)⁻¹) * u
      have hmu' : (m' : Y)⁻¹ * u = u * (m' : Y)⁻¹ := by
        calc (m' : Y)⁻¹ * u = (m' : Y)⁻¹ * (u * m') * (m' : Y)⁻¹ := by group
          _ = (m' : Y)⁻¹ * ((m' : Y) * u) * (m' : Y)⁻¹ := by rw [hm'u]
          _ = u * (m' : Y)⁻¹ := by group
      calc u * ((m' : Y) * e * (m' : Y)⁻¹) = (u * m') * e * (m' : Y)⁻¹ := by group
        _ = (m' * u) * e * (m' : Y)⁻¹ := by rw [hm'u]
        _ = m' * (u * e) * (m' : Y)⁻¹ := by group
        _ = m' * (e * u) * (m' : Y)⁻¹ := by rw [hue]
        _ = (m' : Y) * e * (u * (m' : Y)⁻¹) := by group
        _ = (m' : Y) * e * ((m' : Y)⁻¹ * u) := by rw [hmu']
        _ = ((m' : Y) * e * (m' : Y)⁻¹) * u := by group
    have hmue : (m' : Y) * (u * e) * (m' : Y)⁻¹ = u * f := by
      show (m' : Y) * (u * e) * (m' : Y)⁻¹ = u * ((m' : Y) * e * (m' : Y)⁻¹)
      calc (m' : Y) * (u * e) * (m' : Y)⁻¹ = ((m' : Y) * u) * e * (m' : Y)⁻¹ := by group
        _ = (u * m') * e * (m' : Y)⁻¹ := by rw [hm'u]
        _ = u * ((m' : Y) * e * (m' : Y)⁻¹) := by group
    have hw1X : (w1 : Y) ∈ X := by
      refine ⟨?_, w1.2⟩
      have e1 : (w1 : Y) = (u * e) * ((m' : Y) * (u * e) * (m' : Y)⁻¹) * (u * e)⁻¹ *
          ((m' : Y) * (u * e) * (m' : Y)⁻¹)⁻¹ := by
        rw [hmue, F7J.comm_mul_left_of_commute hue huf hd.hu2]
        rfl
      rw [e1]
      exact hU hcit hP Y R S t K' W u e g hc hAE5 _ hm'U
    have hw1P : F7I.piC C w1 ∈ P := F7I.mem_map_piC.mpr ⟨w1, hw1X, rfl⟩
    have hw1M : F7I.piC C w1 ∈ M := by
      rw [hw1, hfdef]
      simp only [map_mul, map_inv]
      have hm'M : F7I.piC C m' ∈ M := hm
      exact M.mul_mem (M.mul_mem (M.mul_mem heM (M.mul_mem (M.mul_mem hm'M heM) (M.inv_mem hm'M)))
        (M.inv_mem heM)) (M.inv_mem (M.mul_mem (M.mul_mem hm'M heM) (M.inv_mem hm'M)))
    have h1 := F7I.eq_one_of_odd_normalized (F7I.quot_odd_normal_eq_bot C) hMn hPodd hMP hw1P hw1M
    rw [hw1, hfdef] at h1
    simp only [map_mul, map_inv] at h1
    set mm := F7I.piC C m'
    calc ee * (mm * ee * mm⁻¹)
        = (ee * (mm * ee * mm⁻¹) * ee⁻¹ * (mm * ee * mm⁻¹)⁻¹) * ((mm * ee * mm⁻¹) * ee) := by group
      _ = (mm * ee * mm⁻¹) * ee := by rw [h1, one_mul]
  obtain ⟨S₂, hS₂, hS₂N⟩ := p23_exists_sylow_normW hc
  have hS₂e : S₂ ≤ Subgroup.centralizer ({e} : Set Y) :=
    hS₂N.trans (normalizer_le_centralizer_e hd)
  obtain ⟨Q₂, hQ₂⟩ := CtDec.exists_sylow_subgroupOf hS₂
  let T : Sylow 2 (↥C ⧸ classicalInvolutionOddCore ↥C) :=
    Q₂.mapSurjective (QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C))
  have hT : ∀ x ∈ (T : Subgroup _), x * ee = ee * x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyS : (y : Y) ∈ S₂ := by
      have : y ∈ (Q₂ : Subgroup ↥C) := hy
      rw [hQ₂] at this
      exact Subgroup.mem_subgroupOf.mp this
    have hye : (y : Y) * e = e * y := Subgroup.mem_centralizer_singleton_iff.mp (hS₂e hyS)
    have : y * ⟨e, heC⟩ = ⟨e, heC⟩ * y := Subtype.ext hye
    change F7I.piC C y * F7I.piC C ⟨e, heC⟩ = F7I.piC C ⟨e, heC⟩ * F7I.piC C y
    rw [← map_mul, this, map_mul]
  have hcc : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C, ee * (q * ee * q⁻¹) = (q * ee * q⁻¹) * ee :=
    F7J.conj_comm_of_mbar hMn heM hee2 hcommM T hT
  have hcc2 : ∀ γ δ : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (γ * ee * γ⁻¹) * (δ * ee * δ⁻¹) = (δ * ee * δ⁻¹) * (γ * ee * γ⁻¹) := by
    intro γ δ
    have h := hcc (γ⁻¹ * δ)
    calc (γ * ee * γ⁻¹) * (δ * ee * δ⁻¹)
        = γ * (ee * ((γ⁻¹ * δ) * ee * (γ⁻¹ * δ)⁻¹)) * γ⁻¹ := by group
      _ = γ * (((γ⁻¹ * δ) * ee * (γ⁻¹ * δ)⁻¹) * ee) * γ⁻¹ := by rw [h]
      _ = (δ * ee * δ⁻¹) * (γ * ee * γ⁻¹) := by group
  apply F7I.closure_comm
  rintro _ ⟨x, ⟨c, hcC, hx⟩, rfl⟩ _ ⟨y, ⟨d, hdC, hy⟩, rfl⟩
  have ex : x = ⟨c, hcC⟩ * ⟨e, heC⟩ * ⟨c, hcC⟩⁻¹ := Subtype.ext (by rw [hx, one_mul]; rfl)
  have ey : y = ⟨d, hdC⟩ * ⟨e, heC⟩ * ⟨d, hdC⟩⁻¹ := Subtype.ext (by rw [hy, one_mul]; rfl)
  change F7I.piC C x * F7I.piC C y = F7I.piC C y * F7I.piC C x
  rw [ex, ey]
  simp only [map_mul, map_inv]
  exact hcc2 _ _

theorem p23E8Phi_of_comm (hT : Thm4RTwinBelow 3 n) (hU : P23E8UEComm n) : P23E8Phi n :=
  p23E8Phi_of_ae hT (p23E8PhiAE_of_comm hU)

end AE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
