module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Not9
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Struct
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoCase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.AE

section Abstract

theorem eq_of_trivial_mod_ker {Q : Type} [Group Q] (hperf : Group.IsPerfect Q) (σ : Q ≃* Q)
    (hc : ∀ x : Q, x⁻¹ * σ x ∈ Subgroup.center Q) : ∀ x : Q, σ x = x := by
  let δ : Q →* Q :=
    { toFun := fun x => x⁻¹ * σ x
      map_one' := by simp
      map_mul' := fun x x' => by
        have h1 := Subgroup.mem_center_iff.mp (hc x) (x'⁻¹)
        calc (x * x')⁻¹ * σ (x * x') = x'⁻¹ * (x⁻¹ * σ x) * σ x' := by
              rw [map_mul]; group
          _ = (x⁻¹ * σ x) * x'⁻¹ * σ x' := by rw [h1]
          _ = (x⁻¹ * σ x) * (x'⁻¹ * σ x') := by group }
  have hker : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ δ.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have h2 := Subgroup.mem_center_iff.mp (hc g₂) (δ g₁)
    exact commutatorElement_eq_one_iff_mul_comm.mpr h2
  intro x
  have hperf' : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := hperf.commutator_eq_top
  have hx : x ∈ δ.ker := hker (by rw [hperf']; exact Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  exact (inv_mul_eq_one.mp hx).symm

end Abstract


section Transfer

theorem surjective_of_ker_le {X Q₁ Q₂ : Type} [Group X] [Group Q₁] [Group Q₂] [Finite X] [Finite Q₁]
    [Finite Q₂] (fA : X →* Q₁) (fB : X →* Q₂) (hA : Function.Surjective fA)
    (hker : fB.ker ≤ fA.ker) (hcard : Nat.card Q₂ ≤ Nat.card Q₁) : Function.Surjective fB := by
  have h1 : fA.ker.index = Nat.card Q₁ := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hA]
    exact Subgroup.card_top
  have h2 : fB.ker.index = Nat.card fB.range := Subgroup.index_ker fB
  have h3 : fA.ker.index ∣ fB.ker.index := Subgroup.index_dvd_of_le hker
  have h4 : fA.ker.index ≤ fB.ker.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) h3
  have h5 : fB.range = ⊤ := Subgroup.eq_top_of_le_card _ (by
    rw [← h2]
    omega)
  exact MonoidHom.range_eq_top.mp h5

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_oddCore_iff_val (A : Subgroup Y) (z : ↥A) :
    z ∈ classicalInvolutionOddCore ↥A ↔ (z : Y) ∈ oddCoreOf A := by
  constructor
  · intro h
    exact ⟨z, h, rfl⟩
  · rintro ⟨z', hz', hzz'⟩
    have : z' = z := Subtype.ext hzz'
    rwa [this] at hz'

theorem cover_transfer (A B : Subgroup Y) (ψ : ↥A ≃* ↥B) (hcov : A ≤ oddCoreOf A ⊔ (A ⊓ B)) :
    B ≤ oddCoreOf B ⊔ (A ⊓ B) := by
  classical
  set X : Subgroup Y := A ⊓ B with hX
  set OA := classicalInvolutionOddCore ↥A with hOA
  set OB := classicalInvolutionOddCore ↥B with hOB
  let ιA : ↥X →* ↥A := Subgroup.inclusion inf_le_left
  let ιB : ↥X →* ↥B := Subgroup.inclusion inf_le_right
  let fA : ↥X →* ↥A ⧸ OA := (QuotientGroup.mk' OA).comp ιA
  let fB : ↥X →* ↥B ⧸ OB := (QuotientGroup.mk' OB).comp ιB
  have hAN : ∀ x ∈ A, ∀ o ∈ oddCoreOf A, x * o * x⁻¹ ∈ oddCoreOf A := fun x hx o ho =>
    (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf A hx) o).mp ho
  have hBN : ∀ x ∈ B, ∀ o ∈ oddCoreOf B, x * o * x⁻¹ ∈ oddCoreOf B := fun x hx o ho =>
    (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf B hx) o).mp ho
  have hfA : Function.Surjective fA := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective OA q
    have ha : (a : Y) ∈ ((oddCoreOf A ⊔ X : Subgroup Y) : Set Y) := hcov a.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (inf_le_left.trans (Sec7.le_normalizer_oddCoreOf A))] at ha
    obtain ⟨o, ho, x, hx, hax⟩ := ha
    refine ⟨⟨x, hx⟩, ?_⟩
    show QuotientGroup.mk' OA ⟨x, hx.1⟩ = QuotientGroup.mk' OA a
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_oddCore_iff_val]
    have : (((⟨x, hx.1⟩ : ↥A)⁻¹ * a : ↥A) : Y) = x⁻¹ * o * x := by
      show x⁻¹ * (a : Y) = _
      rw [← hax]
      group
    rw [this]
    have := hAN x⁻¹ (A.inv_mem hx.1) o ho
    simpa using this
  have hcardB : Nat.card (↥B ⧸ OB) ≤ Nat.card (↥A ⧸ OA) := by
    have e : (↥A ⧸ OA) ≃* (↥B ⧸ OB) :=
      QuotientGroup.congr OA OB ψ (TwinPerpV3.classicalInvolutionOddCore_map_equiv ψ)
    exact le_of_eq (Nat.card_congr e.toEquiv).symm
  have hker : fB.ker ≤ fA.ker := by
    have hkerB : fB.ker = OB.comap ιB := by
      show ((QuotientGroup.mk' OB).comp ιB).ker = _
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    set Nq : Subgroup (↥A ⧸ OA) := fB.ker.map fA with hNq
    have hnorm : Nq.Normal := Subgroup.Normal.map (MonoidHom.normal_ker fB) fA hfA
    have hodd : Odd (Nat.card Nq) := by
      have h1 : Nat.card Nq ∣ Nat.card fB.ker := Subgroup.card_map_dvd _ _
      have h2 : Nat.card fB.ker ∣ Nat.card OB := by
        rw [hkerB]
        have hle : (OB.comap ιB).map ιB ≤ OB := Subgroup.map_comap_le _ _
        have := Subgroup.card_dvd_of_le hle
        rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)] at this
      exact (CFSG.ComponentClassification.OddCore.odd_card ↥B).of_dvd_nat (h1.trans h2)
    have hle : Nq ≤ classicalInvolutionOddCore (↥A ⧸ OA) := le_sSup ⟨hnorm, hodd⟩
    have hbot : classicalInvolutionOddCore (↥A ⧸ OA) = ⊥ :=
      CFSG.ComponentClassification.OddCore.quotient_corefree ↥A
    intro x hx
    have := hle ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hfB : Function.Surjective fB := surjective_of_ker_le fA fB hfA hker hcardB
  intro b hb
  obtain ⟨x, hx⟩ := hfB (QuotientGroup.mk' OB ⟨b, hb⟩)
  have hx' : QuotientGroup.mk' OB (ιB x) = QuotientGroup.mk' OB ⟨b, hb⟩ := hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_oddCore_iff_val] at hx'
  have h1 : (x : Y)⁻¹ * b ∈ oddCoreOf B := hx'
  have h2 : (x : Y) * ((x : Y)⁻¹ * b) ∈ X ⊔ oddCoreOf B :=
    Subgroup.mul_mem_sup x.2 h1
  rw [mul_inv_cancel_left, sup_comm] at h2
  exact h2

end Transfer


section Trivial


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem mem_zpowers_of_sq {y v : Y} (hy2 : y * y = 1) (hv : v ∈ Subgroup.zpowers y) :
    v = 1 ∨ v = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hy2' : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy2
  rw [zpow_eq_zpow_emod k hy2']
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem centralizer_zpowers_eq' {G : Type} [Group G] (y : G) :
    Subgroup.centralizer (Subgroup.zpowers y : Set G) = Subgroup.centralizer ({y} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem rLayerSub_zpowers {G : Type} [Group G] (Ω : Set (Subgroup G)) (y : G) :
    rLayerSub Ω (Subgroup.zpowers y) = rLayer Ω y := by
  unfold rLayerSub rLayer
  simp only [centralizer_zpowers_eq']

theorem false_of_trivial (hc : P23Cfg n Y R S t K' W u e g)
    (D : AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {c' : Y}
    (hyC : c' * e * c'⁻¹ ∈ Subgroup.centralizer ({e} : Set Y))
    (hy2 : (c' * e * c'⁻¹) * (c' * e * c'⁻¹) = 1) (hne : c' * e * c'⁻¹ ≠ e)
    (hid : ∀ q : SecQ R e,
      TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨c' * e * c'⁻¹, hyC⟩ q = q) : False := by
  classical
  set y := c' * e * c'⁻¹ with hydef
  set E := rLayer (Om R) e with hEdef
  have hΩ := hΩ_of hc
  have heE : e ∈ E := (t_e_mem_rLayer hc).2
  have hEO : ∀ a ∈ E, ∀ o ∈ oddCoreOf E, a * o * a⁻¹ ∈ oddCoreOf E := fun a ha o ho =>
    (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf E ha) o).mp ho
  have hVE : ∀ a ∈ E, y * a * y⁻¹ * a⁻¹ ∈ oddCoreOf E := by
    intro a ha
    have hyx : y * a * y⁻¹ ∈ E := by
      have := conj_mem_conjSub (n := y) ha
      rwa [conjSub_rLayer_eq hΩ hyC] at this
    have h1 := (piE_eq_iff hc ⟨a, ha⟩ ⟨y * a * y⁻¹, hyx⟩).mp
      (by rw [← secAut_piE hc hyC ⟨a, ha⟩ hyx]; exact (hid _).symm)
    have h2 : a⁻¹ * (y * a * y⁻¹) ∈ oddCoreOf E := h1
    have h3 := hEO a ha _ h2
    have : a * (a⁻¹ * (y * a * y⁻¹)) * a⁻¹ = y * a * y⁻¹ * a⁻¹ := by group
    rwa [this] at h3
  have hV2 : IsPGroup 2 (Subgroup.zpowers y) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hy2
  have hcov : E ≤ oddCoreOf E ⊔ (E ⊓ rLayerSub (Om R) (Subgroup.zpowers y)) :=
    F7C.rLayer_le_cover hΩ hV2 (Subgroup.zpowers_le.mpr hyC) (by
      intro v hv a ha
      rcases mem_zpowers_of_sq hy2 hv with rfl | rfl
      · simpa using (oddCoreOf E).one_mem
      · exact hVE a ha)
  have hey : e ∈ rLayerSub (Om R) (Subgroup.zpowers y) :=
    F7C.mem_rLayerSub_of_cover hcov heE (hc2e_of hc)
  have hsubeq : rLayerSub (Om R) (Subgroup.zpowers y) = conjSub c' E := by
    rw [rLayerSub_zpowers, hydef]
    exact rLayer_conj (R := R) c' e
  rw [hsubeq] at hcov hey
  have heEy : e ∈ conjSub c' E := hey
  have hyEy : y ∈ conjSub c' E := conj_mem_conjSub (n := c') heE
  have hcov' := cover_transfer E (conjSub c' E) (Twin1711.conjSubEquiv E c') hcov
  have hOEy : ∀ a ∈ conjSub c' E, ∀ o ∈ oddCoreOf (conjSub c' E), a * o * a⁻¹ ∈ oddCoreOf (conjSub c' E) :=
    fun a ha o ho => (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf _ ha) o).mp ho
  have hEC : E ≤ Subgroup.centralizer ({e} : Set Y) := F7C.rLayer_le_centralizer e
  have hcentE : ∀ x ∈ E, e * x * e⁻¹ = x := fun x hx => by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEC hx)]
    group
  have hP8 : ∀ a ∈ conjSub c' E, e * a * e⁻¹ * a⁻¹ ∈ oddCoreOf (conjSub c' E) := by
    intro a ha
    have ha' : a ∈ ((oddCoreOf (conjSub c' E) ⊔ (E ⊓ conjSub c' E) : Subgroup Y) : Set Y) := hcov' ha
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (inf_le_right.trans (Sec7.le_normalizer_oddCoreOf _))] at ha'
    obtain ⟨o, ho, x, hx, rfl⟩ := ha'
    have h1 : e * (o * x) * e⁻¹ * (o * x)⁻¹ = (e * o * e⁻¹) * o⁻¹ := by
      have hx' := hcentE x hx.1
      calc e * (o * x) * e⁻¹ * (o * x)⁻¹ = (e * o * e⁻¹) * (e * x * e⁻¹) * x⁻¹ * o⁻¹ := by group
        _ = (e * o * e⁻¹) * o⁻¹ := by rw [hx']; group
    rw [h1]
    exact (oddCoreOf (conjSub c' E)).mul_mem (hOEy e heEy o ho) ((oddCoreOf (conjSub c' E)).inv_mem ho)
  have hE₂ : c'⁻¹ * e * c' ∈ E := mem_conjSub_iff.mp heEy
  set e₂ := c'⁻¹ * e * c' with he₂def
  have he₂2 : e₂ * e₂ = 1 := by
    calc e₂ * e₂ = c'⁻¹ * (e * e) * c' := by rw [he₂def]; group
      _ = 1 := by rw [hc.data.he2]; group
  have he₂inv : e₂⁻¹ = e₂ := inv_eq_of_mul_eq_one_right he₂2
  have hP9 : ∀ a₂ ∈ E, e₂ * a₂ * e₂⁻¹ * a₂⁻¹ ∈ oddCoreOf E := by
    intro a₂ ha₂
    have ha : c' * a₂ * c'⁻¹ ∈ conjSub c' E := conj_mem_conjSub ha₂
    have h1 := hP8 _ ha
    rw [AscE184Sect.oddCoreOf_conjSub, mem_conjSub_iff] at h1
    have : c'⁻¹ * (e * (c' * a₂ * c'⁻¹) * e⁻¹ * (c' * a₂ * c'⁻¹)⁻¹) * c' =
        e₂ * a₂ * e₂⁻¹ * a₂⁻¹ := by
      rw [he₂def]
      group
    rwa [this] at h1
  set ē₂ : SecQ R e := piE hc ⟨e₂, hE₂⟩ with hē₂def
  set ē : SecQ R e := piE hc ⟨e, heE⟩ with hēdef
  have hē₂c : ē₂ ∈ Subgroup.center (SecQ R e) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨a, rfl⟩ := piE_surjective hc q
    rw [hē₂def, ← map_mul, ← map_mul, piE_eq_iff hc]
    have h1 := hP9 ((a : Y)⁻¹) (E.inv_mem a.2)
    show ((a : Y) * e₂)⁻¹ * (e₂ * (a : Y)) ∈ oddCoreOf E
    have h2 : ((a : Y) * e₂)⁻¹ * (e₂ * (a : Y)) = e₂ * (a : Y)⁻¹ * e₂⁻¹ * (a : Y)⁻¹⁻¹ := by
      rw [mul_inv_rev, he₂inv, inv_inv]
      group
    rwa [h2]
  have hēc : ē ∈ Subgroup.center (SecQ R e) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨a, rfl⟩ := piE_surjective hc q
    rw [hēdef, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (a : Y) * e = e * (a : Y)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEC a.2)
  have he2' : e * e = 1 := hc.data.he2
  have hē₂sq : ē₂ * ē₂ = 1 := by
    rw [hē₂def, ← map_mul]
    have : (⟨e₂, hE₂⟩ * ⟨e₂, hE₂⟩ : ↥E) = 1 := Subtype.ext he₂2
    rw [this, map_one]
  have hē₂1 : ē₂ ≠ 1 := by
    intro h
    have h1 : e₂ ∈ oddCoreOf E := (piE_eq_one_iff hc _).mp h
    have h2 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard E) h1
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one he₂2)
    apply hc.data.he1
    have : c' * e₂ * c'⁻¹ = e := by rw [he₂def]; group
    rw [← this, h2]
    group
  have hē1 : ē ≠ 1 := by
    intro h
    have h1 : e ∈ oddCoreOf E := (piE_eq_one_iff hc _).mp h
    exact hc.data.he1 (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard E) h1
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one he2'))
  have hēeq : ē₂ = ē := D.eq_of_central_involutions hē₂c hēc hē₂sq hē₂1 hē1
  have h3 : e₂⁻¹ * e ∈ oddCoreOf E := (piE_eq_iff hc ⟨e₂, hE₂⟩ ⟨e, heE⟩).mp hēeq
  have h4 : (e₂⁻¹ * e) * (e₂⁻¹ * e) = 1 := by
    have hc2 : e * e₂ = e₂ * e := by
      have := hcentE e₂ hE₂
      calc e * e₂ = e * e₂ * e⁻¹ * e := by group
        _ = e₂ * e := by rw [this]
    rw [he₂inv]
    calc (e₂ * e) * (e₂ * e) = e₂ * (e * e₂) * e := by group
      _ = e₂ * (e₂ * e) * e := by rw [hc2]
      _ = (e₂ * e₂) * (e * e) := by group
      _ = 1 := by rw [he₂2, he2', one_mul]
  have h5 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard E) h3
    (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one h4)
  have h6 : e₂ = e := by
    have := congrArg (fun z => e₂ * z) h5
    simpa using this.symm
  apply hne
  have h7 : e = c' * e₂ * c'⁻¹ := by rw [he₂def]; group
  calc y = c' * e * c'⁻¹ := hydef
    _ = c' * e₂ * c'⁻¹ := by rw [h6]
    _ = e := h7.symm

end Trivial

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
