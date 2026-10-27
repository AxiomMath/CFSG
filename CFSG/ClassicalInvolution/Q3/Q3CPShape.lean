module

public import CFSG.ClassicalInvolution.Q3.Q3CPQuat
public import CFSG.ClassicalInvolution.Q3.Q3YSMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}


structure BDNbhd (zb : X) : Prop where
  ne_one : zb ≠ 1
  mul_self : zb * zb = 1
  central : ∀ x : X, x * zb = zb * x
  mem : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 → zb ∈ F

@[expose] def ShapeThin (D : LieSystemData3 ι X Φ) : Prop :=
  ∃ i₀ : ι, (∀ i, i = i₀) ∧ D.kind i₀ = CompData.sl23

@[expose] def ShapeDoubleOr (D : LieSystemData3 ι X Φ) (zb : X) : Prop :=
  ∃ i j : ι, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧ D.kind i = CompData.sl23 ∧ D.kind j = CompData.sl23 ∧
    ∃ ζi ζj : X, ζi ∈ (D.hom i).range ∧ ζj ∈ (D.hom j).range ∧ ζi ≠ ζj ∧ ζi * ζi = 1 ∧
      ζj * ζj = 1 ∧ ζi ≠ 1 ∧ ζj ≠ 1 ∧ (∀ g : X, g * ζi = ζi * g) ∧ (∀ g : X, g * ζj = ζj * g) ∧
      (∀ u ∈ (D.hom i).range, u * u = 1 → u = 1 ∨ u = ζi) ∧
      (∀ u ∈ (D.hom j).range, u * u = 1 → u = 1 ∨ u = ζj) ∧ (zb = ζi ∨ zb = ζj ∨ zb = ζi * ζj)

@[expose] def ShapeDouble (D : LieSystemData3 ι X Φ) (zb : X) : Prop :=
  ∃ i j : ι, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧ D.kind i = CompData.sl23 ∧ D.kind j = CompData.sl23 ∧
    ∃ ζi ζj : X, ζi ∈ (D.hom i).range ∧ ζj ∈ (D.hom j).range ∧ ζi ≠ ζj ∧ ζi * ζi = 1 ∧
      ζj * ζj = 1 ∧ ζi ≠ 1 ∧ ζj ≠ 1 ∧ (∀ g : X, g * ζi = ζi * g) ∧ (∀ g : X, g * ζj = ζj * g) ∧
      (∀ u ∈ (D.hom i).range, u * u = 1 → u = 1 ∨ u = ζi) ∧
      (∀ u ∈ (D.hom j).range, u * u = 1 → u = 1 ∨ u = ζj) ∧ zb = ζi * ζj

theorem ShapeDoubleOr.exact {D : LieSystemData3 ι X Φ} {zb : X} (h : ShapeDoubleOr D zb)
    (hne : ∀ (i : ι) (ζ : X), D.kind i = CompData.sl23 → ζ ∈ (D.hom i).range →
      (∀ u ∈ (D.hom i).range, u * u = 1 → u = 1 ∨ u = ζ) → zb ≠ ζ) : ShapeDouble D zb := by
  obtain ⟨i, j, hij, hk, hi, hj, ζi, ζj, hζi, hζj, hne', h2i, h2j, h1i, h1j, hci, hcj, hui, huj,
    hz⟩ := h
  refine ⟨i, j, hij, hk, hi, hj, ζi, ζj, hζi, hζj, hne', h2i, h2j, h1i, h1j, hci, hcj, hui, huj, ?_⟩
  rcases hz with e | e | e
  · exact absurd e (hne i ζi hi hζi hui)
  · exact absurd e (hne j ζj hj hζj huj)
  · exact e

@[expose] def ShapeSp4 (D : LieSystemData3 ι X Φ) (zb : X) : Prop :=
  ∃ i₁ : ι, (∀ i, i = i₁) ∧ D.kind i₁ = CompData.model .PSp 2 ∧
    ∃ f ∈ Subgroup.center (D.kind i₁).G, D.hom i₁ f = zb

def qi : SL(2, ZMod 3) := ⟨!![2, 2; 2, 1], by decide⟩

def qj : SL(2, ZMod 3) := ⟨!![2, 1; 1, 1], by decide⟩

theorem qi_sq : qi * qi = -1 := by decide +kernel

theorem qj_sq : qj * qj = -1 := by decide +kernel

theorem qi_qj : qi * qj = (-1) * (qj * qi) := by decide +kernel

theorem neg_one_sq' : (-1 : SL(2, ZMod 3)) * (-1) = 1 := by decide +kernel

theorem neg_one_ne' : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide +kernel

theorem neg_one_cen' : ∀ g : SL(2, ZMod 3), g * (-1) = (-1) * g := by decide +kernel

theorem sq_eq_one_cases' : ∀ s : SL(2, ZMod 3), s * s = 1 → s = 1 ∨ s = -1 := by decide +kernel

variable [Finite X]

theorem injective_hom_of_sl23 (D : LieSystemData3 ι X Φ) {i : ι} (hi : D.kind i = CompData.sl23) :
    Function.Injective (D.hom i) := by
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

theorem exists_quatPair_of_sl23 (D : LieSystemData3 ι X Φ) {i : ι}
    (hi : D.kind i = CompData.sl23) :
    ∃ x y ζ : X, x ∈ (D.hom i).range ∧ y ∈ (D.hom i).range ∧ ζ ∈ (D.hom i).range ∧
      QuatPair x y ζ ∧ ∀ u ∈ (D.hom i).range, u * u = 1 → u = 1 ∨ u = ζ := by
  have hinj := injective_hom_of_sl23 D hi
  have key : ∀ c : CompData, c = CompData.sl23 → ∀ φ : c.G →* X, Function.Injective φ →
      ∃ x y ζ : X, x ∈ φ.range ∧ y ∈ φ.range ∧ ζ ∈ φ.range ∧ x * x = ζ ∧ y * y = ζ ∧
        x * y = ζ * (y * x) ∧ ζ * ζ = 1 ∧ ζ ≠ 1 ∧ (∀ u ∈ φ.range, u * ζ = ζ * u) ∧
        ∀ u ∈ φ.range, u * u = 1 → u = 1 ∨ u = ζ := by
    rintro c rfl φ hφ
    refine ⟨φ qi, φ qj, φ (-1), ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, qi_sq]
    · rw [← map_mul, qj_sq]
    · have := congrArg φ qi_qj
      simpa only [map_mul] using this
    · rw [← map_mul, neg_one_sq', map_one]
    · intro h1
      exact neg_one_ne' (hφ (h1.trans (map_one φ).symm))
    · rintro _ ⟨g, rfl⟩
      rw [← map_mul, ← map_mul, neg_one_cen' g]
    · rintro _ ⟨s, rfl⟩ hs
      rw [← map_mul] at hs
      have : s * s = 1 := hφ (hs.trans (map_one φ).symm)
      rcases sq_eq_one_cases' s this with h | h
      · left
        rw [h, map_one]
      · right
        rw [h]
  obtain ⟨x, y, ζ, hx, hy, hζ, h1, h2, h3, h4, h5, h6, h7⟩ := key _ hi (D.hom i) hinj
  exact ⟨x, y, ζ, hx, hy, hζ, ⟨h1, h2, h3, h4, h5, Q3YS.central_of_central_in_range D hζ h6⟩, h7⟩

theorem crossComm_of_ne (D : LieSystemData3 ι X Φ) {i j : ι} (hij : i ≠ j) {x y x' y' : X}
    (hx : x ∈ (D.hom i).range) (hy : y ∈ (D.hom i).range) (hx' : x' ∈ (D.hom j).range)
    (hy' : y' ∈ (D.hom j).range) :
    x * x' = x' * x ∧ x * y' = y' * x ∧ y * x' = x' * y ∧ y * y' = y' * y := by
  have hc : ∀ a ∈ (D.hom i).range, ∀ b ∈ (D.hom j).range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i j hij a b
  exact ⟨hc x hx x' hx', hc x hx y' hy', hc y hy x' hx', hc y hy y' hy'⟩

theorem range_eq_top_of_forall_eq (D : LieSystemData3 ι X Φ) {i₁ : ι} (hall : ∀ i, i = i₁) :
    (D.hom i₁).range = ⊤ := by
  have h1 : (⨆ i, (D.hom i).range) = (D.hom i₁).range :=
    le_antisymm (iSup_le fun i => by rw [hall i]) (le_iSup (fun i => (D.hom i).range) i₁)
  rw [← h1]
  exact D.generate

theorem image_fourGroup (D : LieSystemData3 ι X Φ) {i : ι} {F : Subgroup (D.kind i).G}
    (hF : IsElemAbelian 2 F) (hcard : Nat.card F = 4)
    (hFZ : F ⊓ Subgroup.center (D.kind i).G = ⊥) :
    IsElemAbelian 2 (F.map (D.hom i)) ∧ Nat.card (F.map (D.hom i)) = 4 := by
  have hker : ∀ x ∈ F, D.hom i x = 1 → x = 1 := by
    intro x hx hx1
    have hxc : x ∈ Subgroup.center (D.kind i).G := D.ker_le_center i (MonoidHom.mem_ker.mpr hx1)
    have hmem : x ∈ F ⊓ Subgroup.center (D.kind i).G := ⟨hx, hxc⟩
    rw [hFZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  refine ⟨Q3Y.isElemAbelian_map (D.hom i) hF, ?_⟩
  rw [Q3YS.card_map_eq_of_forall (D.hom i) F hker, hcard]

theorem false_of_comp_fourGroup' (D : LieSystemData3 ι X Φ) {zb : X} (h : BDNbhd zb) {i : ι}
    (hZ₂ : ∀ f : (D.kind i).G, (∀ m : (D.kind i).G, ⁅f, m⁆ ∈ Subgroup.center (D.kind i).G) →
      f ∈ Subgroup.center (D.kind i).G)
    {F : Subgroup (D.kind i).G} (hF : IsElemAbelian 2 F) (hcard : Nat.card F = 4)
    (hFZ : F ⊓ Subgroup.center (D.kind i).G = ⊥) : False := by
  obtain ⟨hE, hEcard⟩ := image_fourGroup D hF hcard hFZ
  obtain ⟨f, hfF, hfz⟩ := h.mem _ hE hEcard
  have hfc : f ∈ Subgroup.center (D.kind i).G := by
    refine hZ₂ f fun m => ?_
    refine D.ker_le_center i ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hfz, commutatorElement_eq_one_iff_commute]
    exact (h.central (D.hom i m)).symm
  have hmem : f ∈ F ⊓ Subgroup.center (D.kind i).G := ⟨hfF, hfc⟩
  rw [hFZ, Subgroup.mem_bot] at hmem
  rw [hmem, map_one] at hfz
  exact h.ne_one hfz.symm

theorem exists_fourGroup_of_exotic (hFour : Q3YS.ModelFourGroup3On fun _ => True)
    (D : LieSystemData3 ι X Φ) {i : ι} (hi : D.kind i ≠ CompData.sl23)
    (hi' : D.kind i ≠ CompData.model .PSp 2) :
    ∃ F : Subgroup (D.kind i).G, IsElemAbelian 2 F ∧ Nat.card F = 4 ∧
      F ⊓ Subgroup.center (D.kind i).G = ⊥ :=
  Q3YS.fourGroup_of_valid hFour (D.kind i) (D.valid i) hi hi' (Q3YS.even_card_comp D i)

theorem false_of_exotic (hFour : Q3YS.ModelFourGroup3On fun _ => True) (D : LieSystemData3 ι X Φ)
    {zb : X} (h : BDNbhd zb) {i : ι} (hi : D.kind i ≠ CompData.sl23)
    (hi' : D.kind i ≠ CompData.model .PSp 2) : False := by
  obtain ⟨F, hF, hcard, hFZ⟩ := exists_fourGroup_of_exotic hFour D hi hi'
  exact false_of_comp_fourGroup' D h (Q3YS.zTwo_of_valid (D.kind i) (D.valid i) hi) hF hcard hFZ

theorem exists_fourGroup_of_kleinQuat (D : LieSystemData3 ι X Φ) {i : ι}
    {y y' : (D.kind i).G} (hK : Q3YS.KleinQuat (D.kind i).G y y') :
    ∃ F : Subgroup X, IsElemAbelian 2 F ∧ Nat.card F = 4 := by
  set e := D.hom i with he
  have hc : ∀ m : (D.kind i).G, e m = 1 → m ∈ Subgroup.center (D.kind i).G := fun m hm =>
    D.ker_le_center i (MonoidHom.mem_ker.mpr hm)
  have hyyc := hK.sq_central
  have hy1 : e y ≠ 1 := fun h1 => hK.not_central (hc y h1)
  have hy1' : e y' ≠ 1 := fun h1 => hK.not_central' (hc y' h1)
  have hyy' : e y * e y' = e y' * e y := by rw [← map_mul, ← map_mul, hK.comm]
  by_cases hζ : e (y * y) = 1
  · have hp : e y * e y = 1 := by rw [← map_mul, hζ]
    have hq : e y' * e y' = 1 := by rw [← map_mul, ← hK.sq_eq, hζ]
    have hne : e y ≠ e y' := by
      intro h1
      apply hK.prod_not_central
      have h2 : e (y⁻¹ * y') = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
      have e1 : y * y' = (y * y) * (y⁻¹ * y') := by group
      rw [e1]
      exact Subgroup.mul_mem _ hyyc (hc _ h2)
    exact ⟨Subgroup.closure {e y, e y'}, Q3Y.isElemAbelian_closure_pair hp hq hyy',
      Balance.Bootstrap.card_closure_pair_eq_four hp hq hy1 hy1' hne hyy'⟩
  · have hp1 : e (y * y') ≠ 1 := fun h1 => hK.prod_not_central (hc _ h1)
    have hsq : (y * y') * (y * y') = (y * y) * (y * y) := by
      calc (y * y') * (y * y') = y * (y' * y) * y' := by group
        _ = y * (y * y') * y' := by rw [← hK.comm]
        _ = (y * y) * (y' * y') := by group
        _ = (y * y) * (y * y) := by rw [← hK.sq_eq]
    have hp : e (y * y') * e (y * y') = 1 := by rw [← map_mul, hsq, hK.sq_sq, map_one]
    have hq : e (y * y) * e (y * y) = 1 := by rw [← map_mul, hK.sq_sq, map_one]
    have hne : e (y * y') ≠ e (y * y) := by
      intro h1
      apply hK.prod_not_central
      have h2 : e ((y * y)⁻¹ * (y * y')) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
      have e1 : y * y' = (y * y) * ((y * y)⁻¹ * (y * y')) := by group
      rw [e1]
      exact Subgroup.mul_mem _ hyyc (hc _ h2)
    have hcomm : e (y * y') * e (y * y) = e (y * y) * e (y * y') := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.mp hyyc (y * y')
    exact ⟨Subgroup.closure {e (y * y'), e (y * y)}, Q3Y.isElemAbelian_closure_pair hp hq hcomm,
      Balance.Bootstrap.card_closure_pair_eq_four hp hq hp1 hζ hne hcomm⟩

theorem false_of_two_nonSl (hMFZ : RouteD.Gaps.FundNoncentral 3) (D : LieSystemData3 ι X Φ)
    {zb : X} (h : BDNbhd zb) {i j : ι} (hij : i ≠ j) (hki : D.kind i ≠ CompData.sl23)
    (hkj : D.kind j ≠ CompData.sl23) : False := by
  obtain ⟨c, hcR, hc2, hc1, y, hyR, hcy⟩ := Q3YS.exists_noncentral_involution hMFZ D i hki
  obtain ⟨d, hdR, hd2, hd1, w, hwR, hdw⟩ := Q3YS.exists_noncentral_involution hMFZ D j hkj
  have hcomm : ∀ a ∈ (D.hom i).range, ∀ b ∈ (D.hom j).range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i j hij a b
  have hcd : c * d = d * c := hcomm c hcR d hdR
  have hcne : c ≠ d := by
    intro hcd'
    exact hcy (by rw [hcd']; exact (hcomm y hyR d hdR).symm)
  rcases Q3YS.eq_or_eq_or_eq_mul_of_forall_fourGroup (C := ⊤) h.ne_one
      (fun F hF hc _ => h.mem F hF hc) (Subgroup.mem_top c) (Subgroup.mem_top d) hc2 hd2 hc1 hd1
      hcne hcd with h1 | h1 | h1
  · exact hcy (by rw [← h1]; exact (h.central y).symm)
  · exact hdw (by rw [← h1]; exact (h.central w).symm)
  · have hcz : c = zb * d := by
      calc c = c * (d * d) := by rw [hd2, mul_one]
        _ = (c * d) * d := (mul_assoc _ _ _).symm
        _ = zb * d := by rw [← h1]
    refine hcy ?_
    calc c * y = (zb * d) * y := by rw [hcz]
      _ = zb * (d * y) := mul_assoc _ _ _
      _ = zb * (y * d) := by rw [← hcomm y hyR d hdR]
      _ = (zb * y) * d := (mul_assoc _ _ _).symm
      _ = (y * zb) * d := by rw [h.central y]
      _ = y * (zb * d) := mul_assoc _ _ _
      _ = y * c := by rw [hcz]

theorem false_of_sp_sl23 (hMFZ : RouteD.Gaps.FundNoncentral 3) (D : LieSystemData3 ι X Φ)
    {zb : X} (h : BDNbhd zb) {i₁ i₂ : ι} (h₁₂ : i₁ ≠ i₂) (hk₁ : D.kind i₁ ≠ CompData.sl23)
    (hk₂ : D.kind i₂ = CompData.sl23)
    (hZ₂ : ∀ f : (D.kind i₁).G, (∀ m : (D.kind i₁).G, ⁅f, m⁆ ∈ Subgroup.center (D.kind i₁).G) →
      f ∈ Subgroup.center (D.kind i₁).G)
    (hpair : ∃ y y' : (D.kind i₁).G, Q3YS.KleinQuat (D.kind i₁).G y y') : False := by
  obtain ⟨x₂, z₂, hx₂, hz₂, hxx, hzz, hz₂1, hz₂c, w₂, hw₂, hxw⟩ :=
    Q3YS.exists_quaternion_of_sl23 D hk₂
  have hcomm12 : ∀ a ∈ (D.hom i₁).range, ∀ b ∈ (D.hom i₂).range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₁ i₂ h₁₂ a b
  have hBD : ∀ p q : X, p ∈ (⊤ : Subgroup X) → q ∈ (⊤ : Subgroup X) → p * p = 1 → q * q = 1 →
      p ≠ 1 → q ≠ 1 → p ≠ q → p * q = q * p → zb = p ∨ zb = q ∨ zb = p * q :=
    fun p q hp hq hp2 hq2 hp1 hq1 hpq hc =>
      Q3YS.eq_or_eq_or_eq_mul_of_forall_fourGroup (C := ⊤) h.ne_one
        (fun F hF hc' _ => h.mem F hF hc') hp hq hp2 hq2 hp1 hq1 hpq hc
  by_cases hzb : z₂ = zb
  · obtain ⟨y, y', hK⟩ := hpair
    refine Q3YS.false_of_klein_twin (C := ⊤) h.mul_self h.central hBD
      (x := x₂) (w := w₂) (a := D.hom i₁ y) (b := D.hom i₁ y') (Subgroup.mem_top _)
      (Subgroup.mem_top _) (Subgroup.mem_top _) (hxx.trans hzb) hxw
      (hcomm12 _ ⟨y, rfl⟩ x₂ hx₂) (hcomm12 _ ⟨y', rfl⟩ x₂ hx₂) (hcomm12 _ ⟨y, rfl⟩ w₂ hw₂)
      (hcomm12 _ ⟨y', rfl⟩ w₂ hw₂) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul, ← map_mul, hK.comm]
    · rw [← map_mul, ← map_mul, hK.sq_eq]
    · exact Q3YS.not_central_image D hZ₂ hK.not_central
    · exact Q3YS.not_central_image D hZ₂ hK.not_central'
    · intro hall
      exact Q3YS.not_central_image D hZ₂ hK.prod_not_central (by simpa only [map_mul] using hall)
    · intro hyy
      have hc := Q3YS.inv_mul_mem_center_of_hom_eq D hyy
      apply hK.prod_not_central
      have e : y * y' = (y * y) * (y⁻¹ * y') := by group
      rw [e]
      exact Subgroup.mul_mem _ hK.sq_central hc
    · have hζr : D.hom i₁ y * D.hom i₁ y ∈ (D.hom i₁).range := ⟨y * y, by rw [map_mul]⟩
      refine Q3YS.central_of_central_in_range D hζr ?_
      rintro _ ⟨m, rfl⟩
      have e := Subgroup.mem_center_iff.mp hK.sq_central m
      calc D.hom i₁ m * (D.hom i₁ y * D.hom i₁ y) = D.hom i₁ (m * (y * y)) := by
            simp only [map_mul]
        _ = D.hom i₁ ((y * y) * m) := by rw [e]
        _ = (D.hom i₁ y * D.hom i₁ y) * D.hom i₁ m := by simp only [map_mul]
    · calc (D.hom i₁ y * D.hom i₁ y) * (D.hom i₁ y * D.hom i₁ y)
          = D.hom i₁ ((y * y) * (y * y)) := by simp only [map_mul]
        _ = 1 := by rw [hK.sq_sq, map_one]
  · obtain ⟨c, hcR, hc2, hc1, y₀, -, hcy₀⟩ := Q3YS.exists_noncentral_involution hMFZ D i₁ hk₁
    have hcd : z₂ * c = c * z₂ := (hz₂c c).symm
    have hne : z₂ ≠ c := fun hzc => hcy₀ (by rw [← hzc]; exact (hz₂c y₀).symm)
    rcases hBD z₂ c (Subgroup.mem_top _) (Subgroup.mem_top _) hzz hc2 hz₂1 hc1 hne hcd with
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

section Quat

variable {x y x' y' ζ ζ' : X}

theorem quatPair_prod_fourGroup (h : QuatPair x y ζ) (h' : QuatPair x' y' ζ)
    (hxx' : x * x' = x' * x) (hxy' : x * y' = y' * x) (hyx' : y * x' = x' * y)
    (hyy' : y * y' = y' * y) :
    ∃ F : Subgroup X, IsElemAbelian 2 F ∧ Nat.card F = 4 := by
  have ha2 := quatPair_prod_sq_a h h' hxx'
  have hb2 := quatPair_prod_sq_b h h' hyy'
  have hab := quatPair_prod_comm h h' hxy' hyx'
  have hane := quatPair_prod_a_ne h hyx'
  have hbne := quatPair_prod_b_ne h hxy'
  have ha1 : x * x' ≠ 1 := fun h1 => hane (by rw [h1]; simp)
  have hb1 : y * y' ≠ 1 := fun h1 => hbne (by rw [h1]; simp)
  have hax : (x * x') * x = x * (x * x') := by
    calc (x * x') * x = x * (x' * x) := by group
      _ = x * (x * x') := by rw [← hxx']
  have hne : x * x' ≠ y * y' := fun h1 => hbne (by rw [← h1]; exact hax)
  exact ⟨Subgroup.closure {x * x', y * y'}, Q3Y.isElemAbelian_closure_pair ha2 hb2 hab,
    Balance.Bootstrap.card_closure_pair_eq_four ha2 hb2 ha1 hb1 hne hab⟩

theorem zeta_ne_of_bd {zb : X} (h : BDNbhd zb) (hQ : QuatPair x y ζ) (hQ' : QuatPair x' y' ζ')
    (hxx' : x * x' = x' * x) (hxy' : x * y' = y' * x) (hyx' : y * x' = x' * y)
    (hyy' : y * y' = y' * y) : ζ ≠ ζ' := by
  intro hζ
  subst hζ
  have ha2 := quatPair_prod_sq_a hQ hQ' hxx'
  have hb2 := quatPair_prod_sq_b hQ hQ' hyy'
  have hab := quatPair_prod_comm hQ hQ' hxy' hyx'
  have hane := quatPair_prod_a_ne hQ hyx'
  have hbne := quatPair_prod_b_ne hQ hxy'
  have habne := quatPair_prod_ab_ne hQ hxx' hxy'
  have ha1 : x * x' ≠ 1 := fun h1 => hane (by rw [h1]; simp)
  have hb1 : y * y' ≠ 1 := fun h1 => hbne (by rw [h1]; simp)
  have hax : (x * x') * x = x * (x * x') := by
    calc (x * x') * x = x * (x' * x) := by group
      _ = x * (x * x') := by rw [← hxx']
  have hne : x * x' ≠ y * y' := fun h1 => hbne (by rw [← h1]; exact hax)
  rcases Q3Y.bd_pair_of_forall_fourGroup h.ne_one h.mem ha2 hb2 ha1 hb1 hne hab with h1 | h1 | h1
  · exact hane (by rw [← h1]; exact (h.central y).symm)
  · exact hbne (by rw [← h1]; exact (h.central x).symm)
  · exact habne (by rw [← h1]; exact (h.central x).symm)

theorem bd_of_zeta_ne {zb : X} (h : BDNbhd zb) (hQ : QuatPair x y ζ) (hQ' : QuatPair x' y' ζ')
    (hne : ζ ≠ ζ') : zb = ζ ∨ zb = ζ' ∨ zb = ζ * ζ' :=
  Q3Y.bd_pair_of_forall_fourGroup h.ne_one h.mem hQ.zz hQ'.zz hQ.ne hQ'.ne hne (hQ.cen ζ').symm

theorem exists_fourGroup_of_zeta_ne (hQ : QuatPair x y ζ) (hQ' : QuatPair x' y' ζ')
    (hne : ζ ≠ ζ') : ∃ F : Subgroup X, IsElemAbelian 2 F ∧ Nat.card F = 4 :=
  ⟨Subgroup.closure {ζ, ζ'}, Q3Y.isElemAbelian_closure_pair hQ.zz hQ'.zz (hQ.cen ζ').symm,
    Balance.Bootstrap.card_closure_pair_eq_four hQ.zz hQ'.zz hQ.ne hQ'.ne hne (hQ.cen ζ').symm⟩

end Quat

theorem exists_fourGroup_of_two_sl23 (D : LieSystemData3 ι X Φ) {i j : ι} (hij : i ≠ j)
    (hi : D.kind i = CompData.sl23) (hj : D.kind j = CompData.sl23) :
    ∃ F : Subgroup X, IsElemAbelian 2 F ∧ Nat.card F = 4 := by
  obtain ⟨x, y, ζ, hx, hy, -, hQ, -⟩ := exists_quatPair_of_sl23 D hi
  obtain ⟨x', y', ζ', hx', hy', -, hQ', -⟩ := exists_quatPair_of_sl23 D hj
  obtain ⟨c1, c2, c3, c4⟩ := crossComm_of_ne D hij hx hy hx' hy'
  by_cases hζ : ζ = ζ'
  · subst hζ
    exact quatPair_prod_fourGroup hQ hQ' c1 c2 c3 c4
  · exact exists_fourGroup_of_zeta_ne hQ hQ' hζ

theorem zb_eq_of_triple {zb : X} (h : BDNbhd zb) {s xk yk ζk : X} (hQ : QuatPair xk yk ζk)
    (hs2 : s * s = 1) (hrel : s * yk = ζk * (yk * s)) : zb = ζk := by
  have hnc : s * yk ≠ yk * s := by
    intro hc
    apply hQ.ne
    have h2 : ζk * (yk * s) = 1 * (yk * s) := by rw [← hrel, hc, one_mul]
    exact mul_right_cancel h2
  have hs1 : s ≠ 1 := fun h1 => hnc (by rw [h1]; simp)
  have hsζ : s ≠ ζk := fun h1 => hnc (by rw [h1]; exact (hQ.cen yk).symm)
  rcases Q3Y.bd_pair_of_forall_fourGroup h.ne_one h.mem hs2 hQ.zz hs1 hQ.ne hsζ (hQ.cen s)
    with h1 | h1 | h1
  · exact absurd (by rw [← h1]; exact (h.central yk).symm) hnc
  · exact h1
  · exfalso
    have hz := h.central yk
    rw [h1] at hz
    apply hnc
    have e : (yk * s) * ζk = (s * yk) * ζk := by
      calc (yk * s) * ζk = yk * (s * ζk) := by group
        _ = (s * ζk) * yk := hz
        _ = s * (ζk * yk) := by group
        _ = s * (yk * ζk) := by rw [← hQ.cen yk]
        _ = (s * yk) * ζk := by group
    exact (mul_right_cancel e).symm

theorem false_of_three {zb : X} (h : BDNbhd zb) {x₁ y₁ x₂ y₂ x₃ y₃ ζ₁ ζ₂ ζ₃ : X}
    (h₁ : QuatPair x₁ y₁ ζ₁) (h₂ : QuatPair x₂ y₂ ζ₂) (h₃ : QuatPair x₃ y₃ ζ₃)
    (c12 : x₁ * x₂ = x₂ * x₁ ∧ x₁ * y₂ = y₂ * x₁ ∧ y₁ * x₂ = x₂ * y₁ ∧ y₁ * y₂ = y₂ * y₁)
    (c13 : x₁ * x₃ = x₃ * x₁ ∧ x₁ * y₃ = y₃ * x₁ ∧ y₁ * x₃ = x₃ * y₁ ∧ y₁ * y₃ = y₃ * y₁)
    (c23 : x₂ * x₃ = x₃ * x₂ ∧ x₂ * y₃ = y₃ * x₂ ∧ y₂ * x₃ = x₃ * y₂ ∧ y₂ * y₃ = y₃ * y₂) :
    False := by
  have n12 := zeta_ne_of_bd h h₁ h₂ c12.1 c12.2.1 c12.2.2.1 c12.2.2.2
  have n13 := zeta_ne_of_bd h h₁ h₃ c13.1 c13.2.1 c13.2.2.1 c13.2.2.2
  have n23 := zeta_ne_of_bd h h₂ h₃ c23.1 c23.2.1 c23.2.2.1 c23.2.2.2
  have A12 := bd_of_zeta_ne h h₁ h₂ n12
  have A13 := bd_of_zeta_ne h h₁ h₃ n13
  have A23 := bd_of_zeta_ne h h₂ h₃ n23
  have hprod : ζ₁ * ζ₂ * ζ₃ = 1 := by
    have key23 : ζ₁ = ζ₂ * ζ₃ → ζ₁ * ζ₂ * ζ₃ = 1 := by
      intro e
      rw [e]
      calc ζ₂ * ζ₃ * ζ₂ * ζ₃ = ζ₂ * (ζ₃ * ζ₂) * ζ₃ := by group
        _ = ζ₂ * (ζ₂ * ζ₃) * ζ₃ := by rw [h₂.cen ζ₃]
        _ = (ζ₂ * ζ₂) * (ζ₃ * ζ₃) := by group
        _ = 1 := by rw [h₂.zz, h₃.zz, one_mul]
    have key13 : ζ₂ = ζ₁ * ζ₃ → ζ₁ * ζ₂ * ζ₃ = 1 := by
      intro e
      rw [e]
      calc ζ₁ * (ζ₁ * ζ₃) * ζ₃ = (ζ₁ * ζ₁) * (ζ₃ * ζ₃) := by group
        _ = 1 := by rw [h₁.zz, h₃.zz, one_mul]
    have key12 : ζ₁ * ζ₂ = ζ₃ → ζ₁ * ζ₂ * ζ₃ = 1 := by
      intro e
      rw [e, h₃.zz]
    rcases A12 with e | e | e
    · rcases A23 with f | f | f
      · exact absurd (e.symm.trans f) n12
      · exact absurd (e.symm.trans f) n13
      · exact key23 (e.symm.trans f)
    · rcases A13 with f | f | f
      · exact absurd (e.symm.trans f) n12.symm
      · exact absurd (e.symm.trans f) n23
      · exact key13 (e.symm.trans f)
    · rcases A13 with f | f | f
      · exfalso
        have : ζ₁ * ζ₂ = ζ₁ * 1 := by rw [mul_one]; exact e.symm.trans f
        exact h₂.ne (mul_left_cancel this)
      · exact key12 (e.symm.trans f)
      · exfalso
        have : ζ₁ * ζ₂ = ζ₁ * ζ₃ := e.symm.trans f
        exact n23 (mul_left_cancel this)
  have hs2 : (x₁ * x₂ * x₃) * (x₁ * x₂ * x₃) = 1 := by
    have hc12 : Commute x₁ x₂ := c12.1
    have hc13 : Commute x₁ x₃ := c13.1
    have hc23 : Commute x₂ x₃ := c23.1
    have hc : Commute (x₁ * x₂) x₃ := hc13.mul_left hc23
    have e : (x₁ * x₂ * x₃) ^ 2 = x₁ ^ 2 * x₂ ^ 2 * x₃ ^ 2 := by
      rw [Commute.mul_pow hc, Commute.mul_pow hc12]
    rw [← pow_two, e, pow_two x₁, pow_two x₂, pow_two x₃, h₁.xx, h₂.xx, h₃.xx, hprod]
  have hrel1 : (x₁ * x₂ * x₃) * y₁ = ζ₁ * (y₁ * (x₁ * x₂ * x₃)) := by
    calc (x₁ * x₂ * x₃) * y₁ = x₁ * x₂ * (x₃ * y₁) := by group
      _ = x₁ * x₂ * (y₁ * x₃) := by rw [← c13.2.2.1]
      _ = x₁ * (x₂ * y₁) * x₃ := by group
      _ = x₁ * (y₁ * x₂) * x₃ := by rw [← c12.2.2.1]
      _ = (x₁ * y₁) * x₂ * x₃ := by group
      _ = (ζ₁ * (y₁ * x₁)) * x₂ * x₃ := by rw [h₁.xy]
      _ = ζ₁ * (y₁ * (x₁ * x₂ * x₃)) := by group
  have hrel2 : (x₁ * x₂ * x₃) * y₂ = ζ₂ * (y₂ * (x₁ * x₂ * x₃)) := by
    calc (x₁ * x₂ * x₃) * y₂ = x₁ * x₂ * (x₃ * y₂) := by group
      _ = x₁ * x₂ * (y₂ * x₃) := by rw [← c23.2.2.1]
      _ = x₁ * (x₂ * y₂) * x₃ := by group
      _ = x₁ * (ζ₂ * (y₂ * x₂)) * x₃ := by rw [h₂.xy]
      _ = (x₁ * ζ₂) * (y₂ * x₂) * x₃ := by group
      _ = (ζ₂ * x₁) * (y₂ * x₂) * x₃ := by rw [← h₂.cen x₁]
      _ = ζ₂ * (x₁ * y₂) * x₂ * x₃ := by group
      _ = ζ₂ * (y₂ * x₁) * x₂ * x₃ := by rw [c12.2.1]
      _ = ζ₂ * (y₂ * (x₁ * x₂ * x₃)) := by group
  exact n12 ((zb_eq_of_triple h h₁ hs2 hrel1).symm.trans (zb_eq_of_triple h h₂ hs2 hrel2))

theorem kleinQuat_of_sp4 (hSp : Q3YS.Sp4KleinQuat3) :
    ∀ c : CompData, c = CompData.model .PSp 2 → ∃ y y' : c.G, Q3YS.KleinQuat c.G y y' := by
  rintro c rfl
  exact hSp

theorem shape_of_noFourGroup [Nonempty ι] (hFour : Q3YS.ModelFourGroup3On fun _ => True)
    (hSp : Q3YS.Sp4KleinQuat3) (D : LieSystemData3 ι X Φ)
    (hno : ∀ F : Subgroup X, IsElemAbelian 2 F → Nat.card F = 4 → False) : ShapeThin D := by
  have hsl : ∀ i, D.kind i = CompData.sl23 := by
    intro i
    by_contra hi
    by_cases hsp : D.kind i = CompData.model .PSp 2
    · obtain ⟨y, y', hK⟩ := kleinQuat_of_sp4 hSp _ hsp
      obtain ⟨F, hF, hcard⟩ := exists_fourGroup_of_kleinQuat D hK
      exact hno F hF hcard
    · obtain ⟨F, hF, hcard, hFZ⟩ := exists_fourGroup_of_exotic hFour D hi hsp
      obtain ⟨hE, hEcard⟩ := image_fourGroup D hF hcard hFZ
      exact hno _ hE hEcard
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨i₀, fun i => ?_, hsl i₀⟩
  by_contra hne
  obtain ⟨F, hF, hcard⟩ := exists_fourGroup_of_two_sl23 D hne (hsl i) (hsl i₀)
  exact hno F hF hcard

theorem shape_of_bdNbhd [Nonempty ι] (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (hFour : Q3YS.ModelFourGroup3On fun _ => True) (hSp : Q3YS.Sp4KleinQuat3)
    (D : LieSystemData3 ι X Φ) {zb : X} (h : BDNbhd zb) :
    ShapeThin D ∨ ShapeDoubleOr D zb ∨ ShapeSp4 D zb := by
  have hcomp : ∀ i, D.kind i = CompData.sl23 ∨ D.kind i = CompData.model .PSp 2 := by
    intro i
    by_contra hcon
    push Not at hcon
    exact false_of_exotic hFour D h hcon.1 hcon.2
  by_cases hex : ∃ i₁, D.kind i₁ ≠ CompData.sl23
  · obtain ⟨i₁, hne₁⟩ := hex
    have hsp : D.kind i₁ = CompData.model .PSp 2 := (hcomp i₁).resolve_left hne₁
    have hZ₂ := Q3YS.zTwo_of_valid (D.kind i₁) (D.valid i₁) hne₁
    have hall : ∀ i, i = i₁ := by
      intro i
      by_contra hne
      by_cases hi : D.kind i = CompData.sl23
      · exact false_of_sp_sl23 hMFZ D h (Ne.symm hne) hne₁ hi hZ₂ (kleinQuat_of_sp4 hSp _ hsp)
      · exact false_of_two_nonSl hMFZ D h hne hi hne₁
    right
    right
    have hrange : (D.hom i₁).range = ⊤ := range_eq_top_of_forall_eq D hall
    obtain ⟨g, hg⟩ : zb ∈ (D.hom i₁).range := by
      rw [hrange]
      exact Subgroup.mem_top _
    refine ⟨i₁, hall, hsp, g, ?_, hg⟩
    refine hZ₂ g fun m => ?_
    refine D.ker_le_center i₁ ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hg, commutatorElement_eq_one_iff_commute]
    exact (h.central (D.hom i₁ m)).symm
  · push Not at hex
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    by_cases hone : ∀ i, i = i₀
    · exact Or.inl ⟨i₀, hone, hex i₀⟩
    · push Not at hone
      obtain ⟨j, hj⟩ := hone
      obtain ⟨x₁, y₁, ζ₁, hx₁, hy₁, hζ₁, hQ₁, hu₁⟩ := exists_quatPair_of_sl23 D (hex i₀)
      obtain ⟨x₂, y₂, ζ₂, hx₂, hy₂, hζ₂, hQ₂, hu₂⟩ := exists_quatPair_of_sl23 D (hex j)
      have c12 := crossComm_of_ne D (Ne.symm hj) hx₁ hy₁ hx₂ hy₂
      have hk : ∀ k, k = i₀ ∨ k = j := by
        intro k
        by_contra hcon
        push Not at hcon
        obtain ⟨x₃, y₃, ζ₃, hx₃, hy₃, hζ₃, hQ₃, -⟩ := exists_quatPair_of_sl23 D (hex k)
        exact false_of_three h hQ₁ hQ₂ hQ₃ c12
          (crossComm_of_ne D (Ne.symm hcon.1) hx₁ hy₁ hx₃ hy₃)
          (crossComm_of_ne D (Ne.symm hcon.2) hx₂ hy₂ hx₃ hy₃)
      have hne := zeta_ne_of_bd h hQ₁ hQ₂ c12.1 c12.2.1 c12.2.2.1 c12.2.2.2
      exact Or.inr (Or.inl ⟨i₀, j, Ne.symm hj, hk, hex i₀, hex j, ζ₁, ζ₂, hζ₁, hζ₂, hne, hQ₁.zz,
        hQ₂.zz, hQ₁.ne, hQ₂.ne, hQ₁.cen, hQ₂.cen, hu₁, hu₂, bd_of_zeta_ne h hQ₁ hQ₂ hne⟩)

end CFSG.ClassicalInvolution.Q3.Q3CP
