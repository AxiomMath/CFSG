module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WLocalW
public import CFSG.LocalAnalysis.OddStandard.Seitz77WLocalLift4

public section

namespace CFSG.OddStandard.Seitz77

open CFSG.ComponentClassification.PSL3Four CFSG.Open Subgroup
open scoped commutatorElement

namespace WLocal

@[expose] def restrictAut {Q : Type} [Group Q] (W : Subgroup Q) (φ : MulAut Q)
    (h : ∀ x ∈ W, φ x ∈ W) : W →* W :=
  (φ.toMonoidHom.comp W.subtype).codRestrict W (fun x => h x x.2)

end WLocal

namespace Config25

variable {Q : Type} [Group Q] [Finite Q] {V : Subgroup Q} {t : Q} (c : Config25 Q V t)

include c

theorem mem_V_of_delta_eq_one {W : Subgroup Q} (hVW : V ≤ W) (htW : t ∉ W) {x : Q} (hx : x ∈ W)
    (h : c.delta x = 1) : x ∈ V := by
  rcases c.mem_sup_iff.mp ((c.delta_eq_one_iff x).mp h) with h' | ⟨v, hv, rfl⟩
  · exact h'
  · exfalso
    apply htW
    have e : t = v⁻¹ * (v * t) := by group
    rw [e]
    exact W.mul_mem (W.inv_mem (hVW hv)) hx

theorem mem_V_of_sq_eq_one {W : Subgroup Q} (hVW : V ≤ W) (htW : t ∉ W)
    (hchar : ∀ φ : MulAut Q, ∀ x ∈ W, φ x ∈ W) {w₀ : Q} (hw₀ : w₀ ∈ W) (hw₀2 : w₀ * w₀ ≠ 1)
    {w : Q} (hw : w ∈ W) (hw2 : w * w = 1) : w ∈ V := by
  by_contra hwV
  have hδw : c.delta w ≠ 1 := fun h => hwV (c.mem_V_of_delta_eq_one hVW htW hw h)
  have hδw₀ : c.delta w₀ ≠ 1 := fun h =>
    hw₀2 (c.V_sq (c.mem_V_of_delta_eq_one hVW htW hw₀ h))
  have hne : ∀ x : Q, c.delta x ≠ 1 → Multiplicative.toAdd (c.delta x) ≠ 0 :=
    fun x hx h => hx (toAdd_eq_zero.mp h)
  obtain ⟨a, b, c', e, hword⟩ := WFacts.trans_words _ _ (hne _ hδw₀) (hne _ hδw)
  have hact := (c.acts_up a).mul ((c.acts_low b).mul ((c.acts_up c').mul (c.acts_low e)))
  set φ : MulAut Q := c.αUp (Multiplicative.ofAdd a) * (c.αLow (Multiplicative.ofAdd b) *
    (c.αUp (Multiplicative.ofAdd c') * c.αLow (Multiplicative.ofAdd e))) with hφ
  have h1 : c.delta (φ w₀) = c.delta w := by
    rw [hact.delta_apply]
    simp only [Function.comp_apply]
    rw [hword, ofAdd_toAdd]
  have h2 : w⁻¹ * φ w₀ ∈ W := W.mul_mem (W.inv_mem hw) (hchar φ w₀ hw₀)
  have h3 : c.delta (w⁻¹ * φ w₀) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h4 : w⁻¹ * φ w₀ ∈ V := c.mem_V_of_delta_eq_one hVW htW h2 h3
  have h5 : (φ w₀) * (φ w₀) = 1 := by
    have e1 : φ w₀ = w * (w⁻¹ * φ w₀) := by group
    rw [e1]
    calc w * (w⁻¹ * φ w₀) * (w * (w⁻¹ * φ w₀))
        = w * ((w⁻¹ * φ w₀) * w) * (w⁻¹ * φ w₀) := by group
      _ = w * (w * (w⁻¹ * φ w₀)) * (w⁻¹ * φ w₀) := by rw [c.V_comm h4 w]
      _ = (w * w) * ((w⁻¹ * φ w₀) * (w⁻¹ * φ w₀)) := by group
      _ = 1 := by rw [hw2, c.V_sq h4, one_mul]
  apply hw₀2
  apply φ.injective
  rw [map_mul, h5, map_one]

theorem sq_eq_one_of_char [V.Normal] {W : Subgroup Q} (hindex : W.index = 2)
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hVW : V ≤ W) (htW : t ∉ W)
    (hchar : ∀ φ : MulAut Q, W.map φ.toMonoidHom = W)
    (hsurj : ∀ v ∈ V, ∃ w ∈ W, ⁅t, w⁆ = v) : ∀ x ∈ W, x * x = 1 := by
  by_contra hne
  obtain ⟨w₀, hw₀'⟩ := not_forall.mp hne
  obtain ⟨hw₀, hw₀2⟩ := not_imp.mp hw₀'
  have hcharx : ∀ φ : MulAut Q, ∀ x ∈ W, φ x ∈ W := fun φ x hx => by
    rw [← hchar φ]; exact Subgroup.mem_map_of_mem _ hx
  have hdich : ∀ w ∈ W, w * w = 1 → w ∈ V := fun w hw hw2 =>
    c.mem_V_of_sq_eq_one hVW htW hcharx hw₀ hw₀2 hw hw2
  have hcardW : Nat.card W = 256 := by
    have h := Subgroup.card_mul_index W
    rw [hindex, c.card_Q] at h
    omega
  let _ : CommGroup W :=
    { (inferInstance : Group ↥W) with mul_comm := fun x y => Subtype.ext (hcomm x x.2 y y.2) }
  let δ : W →* Multiplicative F4V := c.delta.comp W.subtype
  have hδsurj : Function.Surjective δ := by
    intro y
    obtain ⟨w, hwW, hw⟩ := hsurj (c.ι.symm y : Q) (c.ι.symm y).2
    refine ⟨⟨w, hwW⟩, ?_⟩
    show c.delta w = y
    rw [c.delta_apply]
    have : (⟨⁅t, w⁆, c.comm_mem w⟩ : V) = c.ι.symm y := Subtype.ext hw
    rw [this, MulEquiv.apply_symm_apply]
  have h2 : ∀ x : W, x * x = 1 → δ x = 1 := by
    intro x hx
    have hx' : (x : Q) * x = 1 := congrArg Subtype.val hx
    exact c.V_le_ker_delta (hdich x x.2 hx')
  let a : W →* W := WLocal.restrictAut W (c.αUp (Multiplicative.ofAdd 1)) (hcharx _)
  let b : W →* W := WLocal.restrictAut W (c.αUp (Multiplicative.ofAdd F4.ω)) (hcharx _)
  have hAA : ∀ γ : F4, γ + γ = 0 → ∀ x : Q,
      c.αUp (Multiplicative.ofAdd γ) (c.αUp (Multiplicative.ofAdd γ) x) = x := by
    intro γ hγ x
    have : c.αUp (Multiplicative.ofAdd γ) * c.αUp (Multiplicative.ofAdd γ) = 1 := by
      rw [← map_mul, ← ofAdd_add, hγ, ofAdd_zero, map_one]
    simpa using congrArg (fun φ : MulAut Q => φ x) this
  have hAB : ∀ x : Q, c.αUp (Multiplicative.ofAdd 1) (c.αUp (Multiplicative.ofAdd F4.ω) x) =
      c.αUp (Multiplicative.ofAdd F4.ω) (c.αUp (Multiplicative.ofAdd 1) x) := by
    intro x
    have : c.αUp (Multiplicative.ofAdd 1) * c.αUp (Multiplicative.ofAdd F4.ω) =
        c.αUp (Multiplicative.ofAdd F4.ω) * c.αUp (Multiplicative.ofAdd 1) := by
      rw [← map_mul c.αUp, ← map_mul c.αUp, mul_comm]
    simpa using congrArg (fun φ : MulAut Q => φ x) this
  refine Lift4.no_commuting_lifts_mul hcardW δ hδsurj h2 a b ?_ ?_ ?_ ?_ ?_
  · exact fun x => Subtype.ext (hAA 1 WFacts.one_add_one x)
  · exact fun x => Subtype.ext (hAA F4.ω WFacts.omega_add_omega x)
  · exact fun x => Subtype.ext (hAB x)
  · exact fun x => (c.acts_up 1).delta_apply x
  · exact fun x => (c.acts_up F4.ω).delta_apply x

end Config25

theorem Config25.exists_W {Q : Type} [Group Q] [Finite Q] {V : Subgroup Q} {t : Q}
    (c : Config25 Q V t) :
    ∃ W : Subgroup Q, W.index = 2 ∧ IsElemAbelian 2 W ∧ V ≤ W ∧ t ∉ W ∧
      (∀ φ : MulAut Q, W.map φ.toMonoidHom = W) ∧
      (∀ W' : Subgroup Q, W'.index = 2 → (∀ x ∈ W', ∀ y ∈ W', x * y = y * x) → W' = W) ∧
      (∀ v ∈ V, ∃ w ∈ W, ⁅t, w⁆ = v) := by
  have := c.V_normal
  obtain ⟨C, hCB, -, -, -, hCsurj, hCinj⟩ := c.modData.exists_complement'
  have hindex : (c.Wsub C).index = 2 := c.index_Wsub hCsurj hCinj
  have hcomm : ∀ x ∈ c.Wsub C, ∀ y ∈ c.Wsub C, x * y = y * x :=
    fun x hx y hy => c.comm_Wsub hCB hx hy
  have hVW : V ≤ c.Wsub C := c.V_le_Wsub
  have htW : t ∉ c.Wsub C := c.t_not_mem_Wsub hCinj
  have hchar : ∀ φ : MulAut Q, (c.Wsub C).map φ.toMonoidHom = c.Wsub C := fun φ =>
    WLocal.map_eq_of_index_two_comm V c.center_le c.card_Q c.card_V hindex hcomm φ
  have hsurj := c.exists_mem_Wsub hCsurj
  refine ⟨c.Wsub C, hindex, ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, ?_⟩, hVW, htW, hchar,
    fun W' h1 h2 => WLocal.unique_index_two_comm V c.center_le c.card_Q c.card_V hindex h1 hcomm h2,
    hsurj⟩
  intro x hx
  rw [pow_two]
  exact c.sq_eq_one_of_char hindex hcomm hVW htW hchar hsurj x hx

end CFSG.OddStandard.Seitz77
