module

public import CFSG.ClassicalInvolution.Q3.Q3YSComp
public import CFSG.ClassicalInvolution.Q3.Q3YComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

section Quat

def qw : SL(2, ZMod 3) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

def qu : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem qw_mul_self : qw * qw = -1 := by decide +kernel

theorem qw_not_comm : qw * qu ≠ qu * qw := by decide +kernel

theorem neg_one_central : ∀ g : SL(2, ZMod 3), g * (-1) = (-1) * g := by decide +kernel

theorem neg_one_ne_one : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide +kernel

theorem neg_one_mul_self : (-1 : SL(2, ZMod 3)) * (-1) = 1 := by decide +kernel

end Quat

section Algebra

theorem false_of_klein_twin {X : Type} [Group X] {C : Subgroup X} {zb : X}
    (hz2 : zb * zb = 1) (hzc : ∀ g : X, g * zb = zb * g)
    (hBD : ∀ p q : X, p ∈ C → q ∈ C → p * p = 1 → q * q = 1 → p ≠ 1 → q ≠ 1 → p ≠ q →
      p * q = q * p → zb = p ∨ zb = q ∨ zb = p * q)
    {x w a b : X} (hxC : x ∈ C) (haC : a ∈ C) (hbC : b ∈ C) (hxx : x * x = zb)
    (hxw : x * w ≠ w * x) (hax : a * x = x * a) (hbx : b * x = x * b) (haw : a * w = w * a)
    (hbw : b * w = w * b) (hab : a * b = b * a) (haa : a * a = b * b)
    (hnca : ¬ ∀ g : X, g * a = a * g) (hncb : ¬ ∀ g : X, g * b = b * g)
    (hncab : ¬ ∀ g : X, g * (a * b) = (a * b) * g) (hne : a ≠ b)
    (hζc : ∀ g : X, g * (a * a) = (a * a) * g) (hζ2 : (a * a) * (a * a) = 1) : False := by
  have hc2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = (a * a) * (b * b) := by
          calc (a * b) * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [← hab]
            _ = (a * a) * (b * b) := by group
      _ = (a * a) * (a * a) := by rw [← haa]
      _ = 1 := hζ2
  have hc1 : a * b ≠ 1 := fun h => hncab (fun g => by rw [h]; simp)
  have hcC : a * b ∈ C := C.mul_mem haC hbC
  have haaC : a * a ∈ C := C.mul_mem haC haC
  by_cases hζ : a * a = 1
  · have hb2 : b * b = 1 := by rw [← haa]; exact hζ
    have ha1 : a ≠ 1 := fun h => hnca (fun g => by rw [h]; simp)
    have hb1 : b ≠ 1 := fun h => hncb (fun g => by rw [h]; simp)
    rcases hBD a b haC hbC hζ hb2 ha1 hb1 hne hab with h | h | h
    · exact hnca (fun g => h ▸ hzc g)
    · exact hncb (fun g => h ▸ hzc g)
    · exact hncab (fun g => h ▸ hzc g)
  · have hzeta : zb = a * a := by
      have hcne : a * b ≠ a * a := fun h => hncab (fun g => by rw [h]; exact hζc g)
      rcases hBD (a * b) (a * a) hcC haaC hc2 hζ2 hc1 hζ hcne (hζc (a * b)) with h | h | h
      · exact (hncab (fun g => h ▸ hzc g)).elim
      · exact h
      · exfalso
        have hcz : a * b = zb * (a * a) := by
          calc a * b = (a * b) * ((a * a) * (a * a)) := by rw [hζ2, mul_one]
            _ = ((a * b) * (a * a)) * (a * a) := by group
            _ = zb * (a * a) := by rw [← h]
        refine hncab (fun g => ?_)
        rw [hcz]
        calc g * (zb * (a * a)) = (g * zb) * (a * a) := by group
          _ = (zb * g) * (a * a) := by rw [hzc g]
          _ = zb * (g * (a * a)) := by group
          _ = zb * ((a * a) * g) := by rw [hζc g]
          _ = (zb * (a * a)) * g := by group
    have hp2 : (x * a) * (x * a) = 1 := by
      calc (x * a) * (x * a) = x * (a * x) * a := by group
        _ = x * (x * a) * a := by rw [hax]
        _ = (x * x) * (a * a) := by group
        _ = zb * zb := by rw [hxx, ← hzeta]
        _ = 1 := hz2
    have hq2 : (x * b) * (x * b) = 1 := by
      calc (x * b) * (x * b) = x * (b * x) * b := by group
        _ = x * (x * b) * b := by rw [hbx]
        _ = (x * x) * (b * b) := by group
        _ = zb * zb := by rw [hxx, ← haa, ← hzeta]
        _ = 1 := hz2
    have hp1 : x * a ≠ 1 := by
      intro h
      have hxa : x = a⁻¹ := eq_inv_of_mul_eq_one_left h
      apply hxw
      rw [hxa]
      exact (Commute.inv_left (show Commute a w from haw)).eq
    have hq1 : x * b ≠ 1 := by
      intro h
      have hxb : x = b⁻¹ := eq_inv_of_mul_eq_one_left h
      apply hxw
      rw [hxb]
      exact (Commute.inv_left (show Commute b w from hbw)).eq
    have hpqne : x * a ≠ x * b := fun h => hne (mul_left_cancel h)
    have hpq : (x * a) * (x * b) = (x * b) * (x * a) := by
      calc (x * a) * (x * b) = x * (a * x) * b := by group
        _ = x * (x * a) * b := by rw [hax]
        _ = (x * x) * (a * b) := by group
        _ = (x * x) * (b * a) := by rw [hab]
        _ = x * (x * b) * a := by group
        _ = x * (b * x) * a := by rw [hbx]
        _ = (x * b) * (x * a) := by group
    rcases hBD (x * a) (x * b) (C.mul_mem hxC haC) (C.mul_mem hxC hbC) hp2 hq2 hp1 hq1 hpqne
      hpq with h | h | h
    · apply hxw
      have hx : x = zb * a⁻¹ := by rw [h]; group
      have hcomm : a⁻¹ * w = w * a⁻¹ := (Commute.inv_left (show Commute a w from haw)).eq
      rw [hx]
      calc zb * a⁻¹ * w = zb * (a⁻¹ * w) := by group
        _ = zb * (w * a⁻¹) := by rw [hcomm]
        _ = (zb * w) * a⁻¹ := by group
        _ = (w * zb) * a⁻¹ := by rw [← hzc w]
        _ = w * (zb * a⁻¹) := by group
    · apply hxw
      have hx : x = zb * b⁻¹ := by rw [h]; group
      have hcomm : b⁻¹ * w = w * b⁻¹ := (Commute.inv_left (show Commute b w from hbw)).eq
      rw [hx]
      calc zb * b⁻¹ * w = zb * (b⁻¹ * w) := by group
        _ = zb * (w * b⁻¹) := by rw [hcomm]
        _ = (zb * w) * b⁻¹ := by group
        _ = (w * zb) * b⁻¹ := by rw [← hzc w]
        _ = w * (zb * b⁻¹) := by group
    · apply hc1
      have hprod : (x * a) * (x * b) = zb * (a * b) := by
        calc (x * a) * (x * b) = x * (a * x) * b := by group
          _ = x * (x * a) * b := by rw [hax]
          _ = (x * x) * (a * b) := by group
          _ = zb * (a * b) := by rw [hxx]
      rw [hprod] at h
      have h' : zb * (a * b) = zb * 1 := by rw [mul_one]; exact h.symm
      exact mul_left_cancel h'

end Algebra

structure KleinQuat (M : Type*) [Group M] (y y' : M) : Prop where
  comm : y * y' = y' * y
  sq_eq : y * y = y' * y'
  sq_central : y * y ∈ Subgroup.center M
  sq_sq : (y * y) * (y * y) = 1
  not_central : y ∉ Subgroup.center M
  not_central' : y' ∉ Subgroup.center M
  prod_not_central : y * y' ∉ Subgroup.center M

section Lie


variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem exists_quaternion_of_sl23 [Finite X] (D : LieSystemData3 ι X Φ) {i : ι}
    (hi : D.kind i = CompData.sl23) :
    ∃ x z₂ : X, x ∈ (D.hom i).range ∧ z₂ ∈ (D.hom i).range ∧ x * x = z₂ ∧ z₂ * z₂ = 1 ∧
      z₂ ≠ 1 ∧ (∀ g : X, g * z₂ = z₂ * g) ∧ ∃ w ∈ (D.hom i).range, x * w ≠ w * x := by
  have hinj : Function.Injective (D.hom i) := by
    obtain ⟨R, hR, hRΦ⟩ := D.meets i
    have hRtop : R = ⊤ := Q3Y.eq_top_of_mem_fund_sl23 hi hR
    have hcard := D.card_eq _ hRΦ
    rw [hRtop, Subgroup.map_top] at hcard
    have hG : Nat.card (D.kind i).G = 24 := by
      rw [hi]
      exact natCard_sl2Three
    have h1 := Subgroup.card_ker_mul_card_range (D.hom i)
    rw [hcard, hG] at h1
    have hk : Nat.card (D.hom i).ker = 1 := by omega
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.card_eq_one.mp hk
  have key : ∀ c : CompData, c = CompData.sl23 → ∀ φ : c.G →* X, Function.Injective φ →
      ∃ x z₂ : X, x ∈ φ.range ∧ z₂ ∈ φ.range ∧ x * x = z₂ ∧ z₂ * z₂ = 1 ∧ z₂ ≠ 1 ∧
        (∀ y ∈ φ.range, y * z₂ = z₂ * y) ∧ ∃ w ∈ φ.range, x * w ≠ w * x := by
    rintro c rfl φ hφ
    refine ⟨φ qw, φ (-1), ⟨_, rfl⟩, ⟨_, rfl⟩, ?_, ?_, ?_, ?_, φ qu, ⟨_, rfl⟩, ?_⟩
    · rw [← map_mul, qw_mul_self]
    · rw [← map_mul, neg_one_mul_self, map_one]
    · intro h1
      exact neg_one_ne_one (hφ (by rw [h1, map_one]))
    · rintro _ ⟨g, rfl⟩
      rw [← map_mul, ← map_mul, neg_one_central g]
    · intro h1
      exact qw_not_comm (hφ (by rw [map_mul, map_mul, h1]))
  obtain ⟨x, z₂, hx, hz, h1, h2, h3, h4, w, hw, h5⟩ := key _ hi (D.hom i) hinj
  exact ⟨x, z₂, hx, hz, h1, h2, h3, central_of_central_in_range D hz h4, w, hw, h5⟩

theorem not_central_image (D : LieSystemData3 ι X Φ) {i : ι}
    (hZ₂ : ∀ f : (D.kind i).G, (∀ m : (D.kind i).G, ⁅f, m⁆ ∈ Subgroup.center (D.kind i).G) →
      f ∈ Subgroup.center (D.kind i).G)
    {f : (D.kind i).G} (hf : f ∉ Subgroup.center (D.kind i).G) :
    ¬ ∀ g : X, g * D.hom i f = D.hom i f * g := by
  intro hall
  apply hf
  refine hZ₂ f fun m => ?_
  refine D.ker_le_center i ?_
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact (hall (D.hom i m)).symm

theorem even_card_comp (D : LieSystemData3 ι X Φ) (i : ι) : Even (Nat.card (D.kind i).G) := by
  obtain ⟨R, -, hRΦ⟩ := D.meets i
  have h24 := D.card_eq _ hRΦ
  have h1 : Nat.card (R.map (D.hom i)) ∣ Nat.card R := Subgroup.card_map_dvd R (D.hom i)
  have h2 : Nat.card R ∣ Nat.card (D.kind i).G := Subgroup.card_subgroup_dvd_card R
  have h3 : 24 ∣ Nat.card (D.kind i).G := h24 ▸ h1.trans h2
  exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) h3)

theorem inv_mul_mem_center_of_hom_eq (D : LieSystemData3 ι X Φ) {i : ι}
    {f f' : (D.kind i).G} (h : D.hom i f = D.hom i f') :
    f⁻¹ * f' ∈ Subgroup.center (D.kind i).G :=
  D.ker_le_center i (by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel])

theorem false_of_twin [Finite X] (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (D : LieSystemData3 ι X Φ) {i₀ : ι} {zb : X} (h : BDLoc D i₀ zb) {i₁ i₂ : ι}
    (h₁₀ : i₁ ≠ i₀) (h₂₀ : i₂ ≠ i₀) (h₁₂ : i₁ ≠ i₂) (hk₁ : D.kind i₁ ≠ CompData.sl23)
    (hk₂ : D.kind i₂ = CompData.sl23)
    (hZ₂ : ∀ f : (D.kind i₁).G, (∀ m : (D.kind i₁).G, ⁅f, m⁆ ∈ Subgroup.center (D.kind i₁).G) →
      f ∈ Subgroup.center (D.kind i₁).G)
    (hpair : ∃ y y' : (D.kind i₁).G, KleinQuat (D.kind i₁).G y y') : False := by
  obtain ⟨x₂, z₂, hx₂, hz₂, hxx, hzz, hz₂1, hz₂c, w₂, hw₂, hxw⟩ :=
    exists_quaternion_of_sl23 D hk₂
  have hcomm12 : ∀ a ∈ (D.hom i₁).range, ∀ b ∈ (D.hom i₂).range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₁ i₂ h₁₂ a b
  have hC₁ := range_le_centralizer_of_ne D h₁₀
  have hC₂ := range_le_centralizer_of_ne D h₂₀
  by_cases hzb : z₂ = zb
  · obtain ⟨y, y', hK⟩ := hpair
    have hmem : ∀ f : (D.kind i₁).G,
        D.hom i₁ f ∈ Subgroup.centralizer ((D.hom i₀).range : Set X) := fun f => hC₁ ⟨f, rfl⟩
    refine false_of_klein_twin (C := Subgroup.centralizer ((D.hom i₀).range : Set X))
      h.mul_self h.central
      (fun p q hp hq hp2 hq2 hp1 hq1 hpq hc =>
        eq_or_eq_or_eq_mul_of_bdLoc h hp hq hp2 hq2 hp1 hq1 hpq hc)
      (x := x₂) (w := w₂) (a := D.hom i₁ y) (b := D.hom i₁ y') (hC₂ hx₂) (hmem y) (hmem y')
      (hxx.trans hzb) hxw (hcomm12 _ ⟨y, rfl⟩ x₂ hx₂) (hcomm12 _ ⟨y', rfl⟩ x₂ hx₂)
      (hcomm12 _ ⟨y, rfl⟩ w₂ hw₂) (hcomm12 _ ⟨y', rfl⟩ w₂ hw₂) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul, ← map_mul, hK.comm]
    · rw [← map_mul, ← map_mul, hK.sq_eq]
    · exact not_central_image D hZ₂ hK.not_central
    · exact not_central_image D hZ₂ hK.not_central'
    · intro hall
      exact not_central_image D hZ₂ hK.prod_not_central (by simpa only [map_mul] using hall)
    · intro hyy
      have hc := inv_mul_mem_center_of_hom_eq D hyy
      apply hK.prod_not_central
      have e : y * y' = (y * y) * (y⁻¹ * y') := by group
      rw [e]
      exact Subgroup.mul_mem _ hK.sq_central hc
    · have hζr : D.hom i₁ y * D.hom i₁ y ∈ (D.hom i₁).range := ⟨y * y, by rw [map_mul]⟩
      refine central_of_central_in_range D hζr ?_
      rintro _ ⟨m, rfl⟩
      have e := Subgroup.mem_center_iff.mp hK.sq_central m
      calc D.hom i₁ m * (D.hom i₁ y * D.hom i₁ y) = D.hom i₁ (m * (y * y)) := by
            simp only [map_mul]
        _ = D.hom i₁ ((y * y) * m) := by rw [e]
        _ = (D.hom i₁ y * D.hom i₁ y) * D.hom i₁ m := by simp only [map_mul]
    · calc (D.hom i₁ y * D.hom i₁ y) * (D.hom i₁ y * D.hom i₁ y)
          = D.hom i₁ ((y * y) * (y * y)) := by simp only [map_mul]
        _ = 1 := by rw [hK.sq_sq, map_one]
  · obtain ⟨c, hcR, hc2, hc1, y₀, -, hcy₀⟩ := exists_noncentral_involution hMFZ D i₁ hk₁
    have hcd : z₂ * c = c * z₂ := (hz₂c c).symm
    have hne : z₂ ≠ c := fun hzc => hcy₀ (by rw [← hzc]; exact (hz₂c y₀).symm)
    rcases eq_or_eq_or_eq_mul_of_bdLoc h (hC₂ hz₂) (hC₁ hcR) hzz hc2 hz₂1 hc1 hne hcd with
      h1 | h1 | h1
    · exact hzb h1.symm
    · exact hcy₀ (by rw [← h1]; exact (h.central y₀).symm)
    · have hcz : c = z₂ * zb := by
        calc c = (z₂ * z₂) * c := by rw [hzz, one_mul]
          _ = z₂ * (z₂ * c) := mul_assoc _ _ _
          _ = z₂ * zb := by rw [← h1]
      refine hcy₀ ?_
      rw [hcz]
      calc z₂ * zb * y₀ = z₂ * (zb * y₀) := mul_assoc _ _ _
        _ = z₂ * (y₀ * zb) := by rw [← h.central y₀]
        _ = (z₂ * y₀) * zb := (mul_assoc _ _ _).symm
        _ = (y₀ * z₂) * zb := by rw [← hz₂c y₀]
        _ = y₀ * (z₂ * zb) := mul_assoc _ _ _

theorem shape_of_bdLoc [Finite X] (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (D : LieSystemData3 ι X Φ) {i₀ : ι} {zb : X} (h : BDLoc D i₀ zb)
    (hk₀ : D.kind i₀ = CompData.sl23) (hnot : ∃ i, D.kind i ≠ CompData.sl23)
    (hZ₂ : ∀ i, D.kind i ≠ CompData.sl23 → ∀ f : (D.kind i).G,
      (∀ m : (D.kind i).G, ⁅f, m⁆ ∈ Subgroup.center (D.kind i).G) →
        f ∈ Subgroup.center (D.kind i).G)
    (hFour : ∀ i, D.kind i ≠ CompData.sl23 → D.kind i ≠ CompData.model .PSp 2 →
      Even (Nat.card (D.kind i).G) →
      ∃ F : Subgroup (D.kind i).G, IsElemAbelian 2 F ∧ Nat.card F = 4 ∧
        F ⊓ Subgroup.center (D.kind i).G = ⊥)
    (hSp : ∀ i, D.kind i = CompData.model .PSp 2 →
      ∃ y y' : (D.kind i).G, KleinQuat (D.kind i).G y y') :
    ∃ i₁ : ι, D.kind i₁ = CompData.model .PSp 2 ∧ (∀ i, i ≠ i₁ → D.kind i = CompData.sl23) ∧
      Nat.card ι = 1 + 1 := by
  obtain ⟨i₁, hi₁⟩ := hnot
  have hne₀ : ∀ i, D.kind i ≠ CompData.sl23 → i ≠ i₀ := fun i hi e => hi (e ▸ hk₀)
  have hsp : D.kind i₁ = CompData.model .PSp 2 := by
    by_contra hne
    obtain ⟨F, hF, hcard, hFZ⟩ := hFour i₁ hi₁ hne (even_card_comp D i₁)
    exact false_of_comp_fourGroup D h (hne₀ i₁ hi₁) (hZ₂ i₁ hi₁) hF hcard hFZ
  have huniq : ∀ i, D.kind i ≠ CompData.sl23 → i = i₁ := by
    intro i hi
    by_contra hne
    exact false_of_two_nonA1 hMFZ D h (hne₀ i hi) (hne₀ i₁ hi₁) hne hi hi₁
  have hrest : ∀ i, i ≠ i₁ → i = i₀ := by
    intro i hi
    by_contra hne
    have hk : D.kind i = CompData.sl23 := by
      by_contra hk
      exact hi (huniq i hk)
    exact false_of_twin hMFZ D h (hne₀ i₁ hi₁) hne (Ne.symm hi) hi₁ hk (hZ₂ i₁ hi₁)
      (hSp i₁ hsp)
  have hi₀₁ : i₀ ≠ i₁ := fun e => hi₁ (e ▸ hk₀)
  refine ⟨i₁, hsp, fun i hi => ?_, ?_⟩
  · rw [hrest i hi]
    exact hk₀
  · have h2 : Nat.card ι = 2 := by
      refine Nat.card_eq_two_iff.mpr ⟨i₀, i₁, hi₀₁, Set.eq_univ_of_forall fun i => ?_⟩
      by_cases hi : i = i₁
      · exact Or.inr hi
      · exact Or.inl (hrest i hi)
    simpa using h2

end Lie

end CFSG.ClassicalInvolution.Q3.Q3YS
