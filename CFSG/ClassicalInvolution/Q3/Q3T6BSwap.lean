module

public import CFSG.ClassicalInvolution.Uniform.U4Bstar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4

variable {F : Type} [Group F] [Finite F]

structure Swap (X : Subgroup F) (x y : F) : Prop where
  member : Mem3 X x
  sq : y * y = 1
  comm : y * x = x * y
  moves : conjSub y X ≠ X

@[expose] def diag (y e : F) : F := e * (y * e * y⁻¹)

structure SwapSylow (X : Subgroup F) (y : F) (R : Subgroup F) : Prop where
  twoGroup : IsPGroup 2 R
  mem : y ∈ R
  sylow : IsSylow2In (R ⊓ X) X
  commute : ∀ q ∈ R ⊓ X, ∀ q' ∈ R ⊓ conjSub y X, q * q' = q' * q
  conj : ∀ q ∈ R ⊓ X, y * q * y⁻¹ ∈ R ⊓ conjSub y X

namespace Swap

variable {X : Subgroup F} {x y : F}

theorem inv_eq (h : Swap X x y) : y⁻¹ = y := inv_eq_of_mul_eq_one_right h.sq

theorem not_mem_normalizer (h : Swap X x y) : y ∉ Subgroup.normalizer (X : Set F) :=
  fun hy => h.moves (conjSub_eq_of_mem_normalizer hy)

theorem twin (h : Swap X x y) : Mem3 (conjSub y X) x := h.member.conj_of_commute h.comm

theorem exists_swapSylow (h : Swap X x y) : ∃ R : Subgroup F, SwapSylow X y R := by
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    Balance.isPGroup_zpowers_of_mul_self_eq_one h.sq
  have hne : conjSub y⁻¹ X ≠ X := by
    rw [h.inv_eq]
    exact h.moves
  have hn : y * y ∈ Subgroup.normalizer (X : Set F) := by
    rw [h.sq]
    exact Subgroup.one_mem _
  obtain ⟨R, hR2, hyR, -, hRX, -, hcomm, hconj⟩ :=
    exists_twin_sylow h.member hy2 h.comm hne hn
  rw [h.inv_eq] at hcomm hconj
  refine ⟨R, hR2, hyR, hRX, hcomm, fun q hq => ?_⟩
  have := hconj q hq
  rw [h.inv_eq]
  exact this

end Swap

namespace SwapSylow

variable {X : Subgroup F} {x y : F} {R : Subgroup F}

theorem comm_conj (hR : SwapSylow X y R) {e : F} (he : e ∈ R ⊓ X) :
    e * (y * e * y⁻¹) = (y * e * y⁻¹) * e :=
  hR.commute e he _ (hR.conj e he)

end SwapSylow

section Diag

variable {X : Subgroup F} {x y : F} {R : Subgroup F}

theorem conj_sq (hyx : y * x = x * y) {e : F} (he2 : e * e = x) :
    (y * e * y⁻¹) * (y * e * y⁻¹) = x := by
  calc (y * e * y⁻¹) * (y * e * y⁻¹) = y * (e * e) * y⁻¹ := by group
    _ = y * x * y⁻¹ := by rw [he2]
    _ = x := by rw [hyx]; group

theorem diag_mul_self (hxx : x * x = 1) (hyx : y * x = x * y) {e : F} (he2 : e * e = x)
    (hc : e * (y * e * y⁻¹) = (y * e * y⁻¹) * e) : diag y e * diag y e = 1 := by
  unfold diag
  calc e * (y * e * y⁻¹) * (e * (y * e * y⁻¹))
      = e * ((y * e * y⁻¹) * e) * (y * e * y⁻¹) := by group
    _ = e * (e * (y * e * y⁻¹)) * (y * e * y⁻¹) := by rw [← hc]
    _ = (e * e) * ((y * e * y⁻¹) * (y * e * y⁻¹)) := by group
    _ = 1 := by rw [he2, conj_sq hyx he2, hxx]

theorem diag_comm_y (hy2 : y * y = 1) {e : F} (hc : e * (y * e * y⁻¹) = (y * e * y⁻¹) * e) :
    y * diag y e = diag y e * y := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyy : y * (y * e * y⁻¹) * y⁻¹ = e := by
    rw [hyi]
    calc y * (y * e * y) * y = (y * y) * e * (y * y) := by group
      _ = e := by rw [hy2]; group
  have hconj : y * diag y e * y⁻¹ = diag y e := by
    unfold diag
    calc y * (e * (y * e * y⁻¹)) * y⁻¹
        = (y * e * y⁻¹) * (y * (y * e * y⁻¹) * y⁻¹) := by group
      _ = (y * e * y⁻¹) * e := by rw [hyy]
      _ = e * (y * e * y⁻¹) := hc.symm
  calc y * diag y e = (y * diag y e * y⁻¹) * y := by group
    _ = diag y e * y := by rw [hconj]

theorem diag_comm_x {e : F} (hex : e * x = x * e) (hex' : (y * e * y⁻¹) * x = x * (y * e * y⁻¹)) :
    x * diag y e = diag y e * x := by
  unfold diag
  calc x * (e * (y * e * y⁻¹)) = (x * e) * (y * e * y⁻¹) := by group
    _ = (e * x) * (y * e * y⁻¹) := by rw [hex]
    _ = e * (x * (y * e * y⁻¹)) := by group
    _ = e * ((y * e * y⁻¹) * x) := by rw [hex']
    _ = e * (y * e * y⁻¹) * x := by group

theorem diag_mul (hR : SwapSylow X y R) {e f : F} (he : e ∈ R ⊓ X) (hf : f ∈ R ⊓ X) :
    diag y e * diag y f = diag y (e * f) := by
  have hcf : (y * e * y⁻¹) * f = f * (y * e * y⁻¹) := (hR.commute f hf _ (hR.conj e he)).symm
  unfold diag
  calc e * (y * e * y⁻¹) * (f * (y * f * y⁻¹))
      = e * ((y * e * y⁻¹) * f) * (y * f * y⁻¹) := by group
    _ = e * (f * (y * e * y⁻¹)) * (y * f * y⁻¹) := by rw [hcf]
    _ = (e * f) * (y * (e * f) * y⁻¹) := by group

theorem four_le_orderOf {g : F} (hg2 : IsPGroup 2 (Subgroup.zpowers g)) (hg : g * g ≠ 1) :
    4 ≤ orderOf g := by
  obtain ⟨n, hn⟩ := hg2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h1 : orderOf g ∣ 2 := by
      rw [hn]
      calc 2 ^ n ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
        _ = 2 := by norm_num
    exact hg (by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp h1)
  rw [hn]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2

namespace SwapSylow

variable {X : Subgroup F} {x y : F} {R : Subgroup F}

theorem not_mem_conj (h : Swap X x y) (hR : SwapSylow X y R) {e : F} (he : e ∈ R ⊓ X)
    (he2 : e * e = x) : e ∉ conjSub y X := by
  intro heY
  have hep : IsPGroup 2 (Subgroup.zpowers e) :=
    hR.twoGroup.to_le (Subgroup.zpowers_le.mpr he.1)
  have h4 : 4 ≤ orderOf e := four_le_orderOf hep (by rw [he2]; exact h.member.ne_one)
  exact h.moves (Mem3.eq_of_mem_of_mem_same h.twin h.member heY he.2 hep h4)

theorem diag_mem_normalizer (h : Swap X x y) {e : F} (he : e ∈ X) :
    diag y e ∈ Subgroup.normalizer (X : Set F) := by
  unfold diag
  refine Subgroup.mul_mem _ (Subgroup.le_normalizer he) ?_
  exact h.twin.le_normalizer_of_same h.member (conj_mem_conjSub he)

theorem diag_ne (h : Swap X x y) (hR : SwapSylow X y R) {e : F} (he : e ∈ R ⊓ X)
    (he2 : e * e = x) :
    diag y e ≠ 1 ∧ diag y e ≠ x ∧ diag y e ≠ y ∧ diag y e ≠ x * y := by
  have hnm := not_mem_conj h hR he he2
  have he'Y : y * e * y⁻¹ ∈ conjSub y X := conj_mem_conjSub he.2
  have hxN : x ∈ Subgroup.normalizer (X : Set F) := Subgroup.le_normalizer h.member.mem
  have hdN := diag_mem_normalizer h he.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1
    apply hnm
    have h2 : y * e * y⁻¹ = e⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [← inv_mem_iff, ← h2]
    exact he'Y
  · intro h1
    apply hnm
    have h2 : y * e * y⁻¹ = e := by
      have : e * (y * e * y⁻¹) = e * e := by rw [he2]; exact h1
      exact mul_left_cancel this
    rw [← h2]
    exact he'Y
  · intro h1
    rw [h1] at hdN
    exact h.not_mem_normalizer hdN
  · intro h1
    rw [h1] at hdN
    apply h.not_mem_normalizer
    have := Subgroup.mul_mem _ ((Subgroup.normalizer (X : Set F)).inv_mem hxN) hdN
    rwa [inv_mul_cancel_left] at this

end SwapSylow

end Diag

section Chain

variable {X : Subgroup F} {x y : F} {R : Subgroup F}

theorem conj_y_eq (hxx : x * x = 1) (hyx : y * x = x * y) {e : F} (he2 : e * e = x) :
    e * y * e⁻¹ = diag y e * x * y := by
  have he'2 := conj_sq hyx he2
  have hinv : (y * e * y⁻¹)⁻¹ = (y * e * y⁻¹) * x :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, he'2, hxx])
  have h1 : y * e⁻¹ * y⁻¹ = (y * e * y⁻¹)⁻¹ := by group
  unfold diag
  calc e * y * e⁻¹ = e * (y * e⁻¹ * y⁻¹) * y := by group
    _ = e * ((y * e * y⁻¹) * x) * y := by rw [h1, hinv]
    _ = e * (y * e * y⁻¹) * x * y := by group

theorem diag_conj (h : Swap X x y) (hR : SwapSylow X y R) {e f : F} (he : e ∈ R ⊓ X)
    (hf : f ∈ R ⊓ X) (he2 : e * e = x) (hfe : f * e * f⁻¹ = e⁻¹) :
    f * diag y e * f⁻¹ = x * diag y e := by
  have hxx := h.member.mul_self
  have hex : e * x = x * e := h.member.mul_comm_of_mem he.2
  have hc : f * (y * e * y⁻¹) = (y * e * y⁻¹) * f := hR.commute f hf _ (hR.conj e he)
  have hfe' : f * (y * e * y⁻¹) * f⁻¹ = y * e * y⁻¹ := by rw [hc]; group
  have heinv : e⁻¹ = e * x := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, he2, hxx])
  unfold diag
  calc f * (e * (y * e * y⁻¹)) * f⁻¹ = (f * e * f⁻¹) * (f * (y * e * y⁻¹) * f⁻¹) := by group
    _ = e⁻¹ * (y * e * y⁻¹) := by rw [hfe, hfe']
    _ = (e * x) * (y * e * y⁻¹) := by rw [heinv]
    _ = (x * e) * (y * e * y⁻¹) := by rw [hex]
    _ = x * (e * (y * e * y⁻¹)) := by group

theorem SwapSylow.exists_anticomm (h : Swap X x y) (hR : SwapSylow X y R) :
    ∃ e ∈ R ⊓ X, ∃ f ∈ R ⊓ X, e * e = x ∧ f * f = x ∧ f * e * f⁻¹ = e⁻¹ := by
  have hcard : Nat.card (R ⊓ X : Subgroup F) = 8 := by
    rw [Uniform.natCard_isSylow2In_eq hR.sylow, Nat.card_congr h.member.equiv.toEquiv,
      natCard_sl2Three]
    have : (Nat.factorization 24) 2 = 3 := by decide +kernel
    rw [this]
    norm_num
  obtain ⟨k₁, hk₁, ⟨eQ⟩⟩ := h.member.isQuatSub_of_isSylow2In hR.sylow
  have hk : k₁ = 1 := by
    have : NeZero (2 ^ k₁) := ⟨by positivity⟩
    have h4 : Nat.card (R ⊓ X : Subgroup F) = 4 * 2 ^ k₁ := by
      rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have h2 : 2 ^ k₁ = 2 ^ 1 := by omega
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hk
  have hKx := h.member.isUniqueInvolution
  have hsq : ∀ i : ZMod (2 * 2 ^ 1), ((eQ.symm (QuaternionGroup.xa i) : ↥(R ⊓ X)) : F) *
      ((eQ.symm (QuaternionGroup.xa i) : ↥(R ⊓ X)) : F) = x := by
    intro i
    have hx4 : orderOf (eQ.symm (QuaternionGroup.xa i)) = 4 := by
      rw [MulEquiv.orderOf_eq]
      exact QuaternionGroup.orderOf_xa i
    have ha4 : orderOf ((eQ.symm (QuaternionGroup.xa i) : ↥(R ⊓ X)) : F) = 4 := by
      rw [Subgroup.orderOf_coe]
      exact hx4
    exact mul_self_eq_of_orderOf_four hKx (hR.sylow.1 (eQ.symm (QuaternionGroup.xa i)).2) ha4
  refine ⟨((eQ.symm (QuaternionGroup.xa 0) : ↥(R ⊓ X)) : F),
    (eQ.symm (QuaternionGroup.xa 0)).2, ((eQ.symm (QuaternionGroup.xa 1) : ↥(R ⊓ X)) : F),
    (eQ.symm (QuaternionGroup.xa 1)).2, hsq 0, hsq 1, ?_⟩
  have key : eQ.symm (QuaternionGroup.xa 1) * eQ.symm (QuaternionGroup.xa 0) *
      (eQ.symm (QuaternionGroup.xa 1))⁻¹ = (eQ.symm (QuaternionGroup.xa 0))⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
  have := congrArg Subtype.val key
  simpa using this

theorem conj_inv_y_eq (hxx : x * x = 1) (hyx : y * x = x * y) {e : F} (he2 : e * e = x) :
    e⁻¹ * y * e = diag y e * x * y := by
  have h1 := conj_y_eq hxx hyx he2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hee : e⁻¹ * e⁻¹ = x := by rw [← mul_inv_rev, he2, hxi]
  have hexc : e * x = x * e := by
    calc e * x = e * (e * e) := by rw [he2]
      _ = (e * e) * e := (mul_assoc _ _ _).symm
      _ = x * e := by rw [he2]
  have hδx : x * diag y e = diag y e * x := by
    unfold diag
    have hxe' : (y * e * y⁻¹) * x = x * (y * e * y⁻¹) := by
      have := conj_sq hyx he2
      calc (y * e * y⁻¹) * x = (y * e * y⁻¹) * ((y * e * y⁻¹) * (y * e * y⁻¹)) := by rw [this]
        _ = ((y * e * y⁻¹) * (y * e * y⁻¹)) * (y * e * y⁻¹) := (mul_assoc _ _ _).symm
        _ = x * (y * e * y⁻¹) := by rw [this]
    exact diag_comm_x hexc hxe'
  calc e⁻¹ * y * e = (e⁻¹ * e⁻¹) * (e * y * e⁻¹) * (e * e) := by group
    _ = x * (diag y e * x * y) * x := by rw [hee, h1, he2]
    _ = (x * diag y e) * x * (y * x) := by group
    _ = (diag y e * x) * x * (x * y) := by rw [hδx, hyx]
    _ = diag y e * (x * x) * x * y := by group
    _ = diag y e * x * y := by rw [hxx, mul_one]

theorem exists_conj_diag_eq_y (h : Swap X x y) (hR : SwapSylow X y R) {e f : F} (he : e ∈ R ⊓ X)
    (hf : f ∈ R ⊓ X) (he2 : e * e = x) (hfe : f * e * f⁻¹ = e⁻¹) {a : F}
    (haδ : a * diag y e = diag y e * a) (hax : a * x * a⁻¹ = x * y) :
    ∃ g : F, g * diag y e * g⁻¹ = y ∧ g * x * g⁻¹ = diag y e * y := by
  have hxx := h.member.mul_self
  have hc := hR.comm_conj he
  have hex : e * x = x * e := h.member.mul_comm_of_mem he.2
  have hfx : f * x = x * f := h.member.mul_comm_of_mem hf.2
  have hδx : x * diag y e = diag y e * x :=
    diag_comm_x hex (h.twin.mul_comm_of_mem (conj_mem_conjSub he.2))
  have hδy : y * diag y e = diag y e * y := diag_comm_y h.sq hc
  have h1 := diag_conj h hR he hf he2 hfe
  have h2 : a * (x * diag y e) * a⁻¹ = x * y * diag y e := by
    calc a * (x * diag y e) * a⁻¹ = (a * x * a⁻¹) * (a * diag y e * a⁻¹) := by group
      _ = (x * y) * diag y e := by rw [hax, haδ]; group
  have h3 : x * y * diag y e = diag y e * x * y := by
    calc x * y * diag y e = x * (y * diag y e) := mul_assoc _ _ _
      _ = x * (diag y e * y) := by rw [hδy]
      _ = (x * diag y e) * y := (mul_assoc _ _ _).symm
      _ = (diag y e * x) * y := by rw [hδx]
  have h4 : e⁻¹ * (diag y e * x * y) * e = y := by
    rw [← conj_y_eq hxx h.comm he2]
    group
  refine ⟨e⁻¹ * a * f, ?_, ?_⟩
  · calc e⁻¹ * a * f * diag y e * (e⁻¹ * a * f)⁻¹
        = e⁻¹ * (a * (f * diag y e * f⁻¹) * a⁻¹) * e := by group
      _ = e⁻¹ * (diag y e * x * y) * e := by rw [h1, h2, h3]
      _ = y := h4
  · have hexi : e⁻¹ * x * e = x := by
      calc e⁻¹ * x * e = e⁻¹ * (x * e) := mul_assoc _ _ _
        _ = e⁻¹ * (e * x) := by rw [hex]
        _ = x := inv_mul_cancel_left e x
    have hfxf : f * x * f⁻¹ = x := by rw [hfx]; group
    calc e⁻¹ * a * f * x * (e⁻¹ * a * f)⁻¹ = e⁻¹ * (a * (f * x * f⁻¹) * a⁻¹) * e := by group
      _ = e⁻¹ * (x * y) * e := by rw [hfxf, hax]
      _ = (e⁻¹ * x * e) * (e⁻¹ * y * e) := by group
      _ = x * (diag y e * x * y) := by rw [hexi, conj_inv_y_eq hxx h.comm he2]
      _ = (x * diag y e) * x * y := by group
      _ = diag y e * x * x * y := by rw [hδx]
      _ = diag y e * y := by rw [mul_assoc (diag y e) x x, hxx, mul_one]

end Chain

end CFSG.ClassicalInvolution.Q3.Q3T6B
