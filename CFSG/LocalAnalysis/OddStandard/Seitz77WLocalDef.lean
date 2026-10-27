module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WModule
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.Seitz77

open CFSG.ComponentClassification.PSL3Four CFSG.Open Subgroup
open scoped commutatorElement

structure Config25 (Q : Type) [Group Q] [Finite Q] (V : Subgroup Q) (t : Q) where
  card_Q : Nat.card Q = 2 ^ 9
  V_central : V ≤ center Q
  card_V : Nat.card V = 16
  elem_V : IsElemAbelian 2 V
  t_sq : t * t = 1
  t_not_mem : t ∉ V
  centralizer_t : centralizer ({t} : Set Q) = V ⊔ zpowers t
  comm_mem : ∀ x : Q, ⁅t, x⁆ ∈ V
  ι : ↥V ≃* Multiplicative F4V
  αUp : Multiplicative F4 →* MulAut Q
  αLow : Multiplicative F4 →* MulAut Q
  αTor : MulAut Q
  αTor_cube : αTor ^ 3 = 1
  fix_t : (∀ γ, αUp γ t = t) ∧ (∀ γ, αLow γ t = t) ∧ αTor t = t
  act_up : ∀ (γ : F4) (v : F4V),
    αUp (Multiplicative.ofAdd γ) (ι.symm (Multiplicative.ofAdd v) : Q) =
      (ι.symm (Multiplicative.ofAdd (cUp γ v)) : Q)
  act_low : ∀ (γ : F4) (v : F4V),
    αLow (Multiplicative.ofAdd γ) (ι.symm (Multiplicative.ofAdd v) : Q) =
      (ι.symm (Multiplicative.ofAdd (cLow γ v)) : Q)
  act_tor : ∀ v : F4V,
    αTor (ι.symm (Multiplicative.ofAdd v) : Q) = (ι.symm (Multiplicative.ofAdd (dTor v)) : Q)

theorem WFacts.card_F4V : Nat.card (Multiplicative F4V) = 16 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Fin 2 → F4) = 16
  rw [Fintype.card_fun, F4.card_eq]
  simp

namespace Config25

variable {Q : Type} [Group Q] [Finite Q] {V : Subgroup Q} {t : Q} (c : Config25 Q V t)

include c

theorem V_comm {v : Q} (hv : v ∈ V) (x : Q) : v * x = x * v := by
  have := Subgroup.mem_center_iff.mp (c.V_central hv) x
  exact this.symm

theorem V_normal : V.Normal :=
  Subgroup.normal_of_le_center c.V_central

theorem V_sq {v : Q} (hv : v ∈ V) : v * v = 1 := by
  have := c.elem_V.2 v hv
  rwa [pow_two] at this

theorem V_inv {v : Q} (hv : v ∈ V) : v⁻¹ = v := by
  rw [inv_eq_iff_mul_eq_one]; exact c.V_sq hv

theorem zpow_t (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact c.t_sq
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left; rw [hm, zpow_mul, h2, one_zpow]
  · right; rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem mem_sup_iff {x : Q} : x ∈ V ⊔ zpowers t ↔ x ∈ V ∨ ∃ v ∈ V, x = v * t := by
  have := c.V_normal
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rcases c.zpow_t k with h | h
    · left; rw [h, mul_one]; exact hy
    · right; exact ⟨y, hy, by rw [h]⟩
  · rintro (hx | ⟨v, hv, rfl⟩)
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

theorem card_sup_le : Nat.card ↥(V ⊔ zpowers t) ≤ 32 := by
  have hsub : ((V ⊔ zpowers t : Subgroup Q) : Set Q) ⊆
      (V : Set Q) ∪ (fun v => v * t) '' (V : Set Q) := by
    intro x hx
    rcases c.mem_sup_iff.mp hx with h | ⟨v, hv, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, rfl⟩
  have h1 : Nat.card ↥(V ⊔ zpowers t) ≤
      Set.ncard ((V : Set Q) ∪ (fun v => v * t) '' (V : Set Q)) := by
    have e : Nat.card ↥(V ⊔ zpowers t) = Set.ncard ((V ⊔ zpowers t : Subgroup Q) : Set Q) :=
      Nat.card_coe_set_eq ((V ⊔ zpowers t : Subgroup Q) : Set Q)
    rw [e]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : Set.ncard ((V : Set Q) ∪ (fun v => v * t) '' (V : Set Q)) ≤ 32 := by
    refine (Set.ncard_union_le _ _).trans ?_
    have h3 : Set.ncard ((fun v => v * t) '' (V : Set Q)) ≤ Set.ncard (V : Set Q) :=
      Set.ncard_image_le (Set.toFinite _)
    have h4 : Set.ncard (V : Set Q) = 16 := by
      rw [← c.card_V]; exact Nat.card_coe_set_eq (V : Set Q)
    omega
  exact h1.trans h2

@[expose] def delta : Q →* Multiplicative F4V where
  toFun x := c.ι ⟨⁅t, x⁆, c.comm_mem x⟩
  map_one' := by
    have : (⟨⁅t, (1 : Q)⁆, c.comm_mem 1⟩ : V) = 1 := by
      apply Subtype.ext; simp
    rw [this, map_one]
  map_mul' x y := by
    have h : (⟨⁅t, x * y⁆, c.comm_mem (x * y)⟩ : V) =
        ⟨⁅t, x⁆, c.comm_mem x⟩ * ⟨⁅t, y⁆, c.comm_mem y⟩ := by
      apply Subtype.ext
      show ⁅t, x * y⁆ = ⁅t, x⁆ * ⁅t, y⁆
      have e : ⁅t, x * y⁆ = ⁅t, x⁆ * (x * ⁅t, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e, ← c.V_comm (c.comm_mem y) x, mul_assoc, mul_inv_cancel, mul_one]
    rw [h, map_mul]

theorem delta_apply (x : Q) : c.delta x = c.ι ⟨⁅t, x⁆, c.comm_mem x⟩ := rfl

theorem delta_eq_one_iff (x : Q) : c.delta x = 1 ↔ x ∈ V ⊔ zpowers t := by
  rw [← c.centralizer_t, Subgroup.mem_centralizer_iff, c.delta_apply,
    map_eq_one_iff _ c.ι.injective, Subtype.ext_iff]
  simp only [Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm, Set.mem_singleton_iff,
    forall_eq]

theorem delta_surjective : Function.Surjective c.delta := by
  have hker : c.delta.ker = V ⊔ zpowers t := by
    ext x; rw [MonoidHom.mem_ker, c.delta_eq_one_iff]
  have h1 := Subgroup.card_ker_mul_card_range c.delta
  rw [hker, c.card_Q] at h1
  have h2 : Nat.card c.delta.range ≤ 16 := by
    rw [← WFacts.card_F4V]; exact Subgroup.card_le_card_group _
  have h3 := c.card_sup_le
  have h4 : 2 ^ 9 ≤ 32 * Nat.card c.delta.range := by
    rw [← h1]; exact Nat.mul_le_mul_right _ h3
  have h5 : Nat.card c.delta.range = 16 := by omega
  have h6 : c.delta.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h5, WFacts.card_F4V])
  exact MonoidHom.range_eq_top.mp h6

structure Acts (φ : MulAut Q) (f : F4V → F4V) : Prop where
  fix : φ t = t
  act : ∀ v : F4V, φ (c.ι.symm (Multiplicative.ofAdd v) : Q) =
    (c.ι.symm (Multiplicative.ofAdd (f v)) : Q)

variable {c} {φ ψ : MulAut Q} {f g : F4V → F4V}

theorem Acts.mem_V (h : c.Acts φ f) {v : Q} (hv : v ∈ V) : φ v ∈ V := by
  have e : v = (c.ι.symm (Multiplicative.ofAdd (Multiplicative.toAdd (c.ι ⟨v, hv⟩))) : Q) := by
    rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
  rw [e, h.act]
  exact Subtype.property _

theorem Acts.delta_apply (h : c.Acts φ f) (x : Q) :
    c.delta (φ x) = Multiplicative.ofAdd (f (Multiplicative.toAdd (c.delta x))) := by
  set v₀ := Multiplicative.toAdd (c.delta x) with hv₀
  have h1 : (⟨⁅t, x⁆, c.comm_mem x⟩ : V) = c.ι.symm (Multiplicative.ofAdd v₀) := by
    rw [hv₀, ofAdd_toAdd, c.delta_apply, MulEquiv.symm_apply_apply]
  have h2 : ⁅t, φ x⁆ = (c.ι.symm (Multiplicative.ofAdd (f v₀)) : Q) := by
    have e : ⁅t, φ x⁆ = φ ⁅t, x⁆ := by rw [map_commutatorElement, h.fix]
    have e' : ⁅t, x⁆ = (c.ι.symm (Multiplicative.ofAdd v₀) : Q) := congrArg Subtype.val h1
    rw [e, e', h.act]
  rw [c.delta_apply]
  have h3 : (⟨⁅t, φ x⁆, c.comm_mem (φ x)⟩ : V) = c.ι.symm (Multiplicative.ofAdd (f v₀)) :=
    Subtype.ext h2
  rw [h3, MulEquiv.apply_symm_apply]

theorem Acts.mul (h : c.Acts φ f) (h' : c.Acts ψ g) : c.Acts (φ * ψ) (f ∘ g) :=
  ⟨by rw [MulAut.mul_apply, h'.fix, h.fix], fun v => by rw [MulAut.mul_apply, h'.act, h.act]; rfl⟩

theorem acts_up (γ : F4) : c.Acts (c.αUp (Multiplicative.ofAdd γ)) (cUp γ) :=
  ⟨c.fix_t.1 _, c.act_up γ⟩

theorem acts_low (γ : F4) : c.Acts (c.αLow (Multiplicative.ofAdd γ)) (cLow γ) :=
  ⟨c.fix_t.2.1 _, c.act_low γ⟩

theorem acts_tor : c.Acts c.αTor dTor := ⟨c.fix_t.2.2, c.act_tor⟩

theorem center_le : center Q ≤ V := by
  intro z hz
  have hzc := Subgroup.mem_center_iff.mp hz
  have h1 : z ∈ V ⊔ zpowers t := by
    rw [← c.delta_eq_one_iff, c.delta_apply]
    have : (⟨⁅t, z⁆, c.comm_mem z⟩ : V) = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm]
      exact hzc t
    rw [this, map_one]
  rcases c.mem_sup_iff.mp h1 with h | ⟨v, hv, rfl⟩
  · exact h
  · exfalso
    have ht : ∀ x : Q, t * x = x * t := by
      intro x
      have e3 : v * (x * t) = v * (t * x) := by
        calc v * (x * t) = (v * x) * t := by rw [mul_assoc]
          _ = (x * v) * t := by rw [c.V_comm hv x]
          _ = x * (v * t) := by rw [mul_assoc]
          _ = (v * t) * x := hzc x
          _ = v * (t * x) := by rw [mul_assoc]
      exact (mul_left_cancel e3).symm
    have hone : ∀ x : Q, c.delta x = 1 := by
      intro x
      rw [c.delta_apply]
      have : (⟨⁅t, x⁆, c.comm_mem x⟩ : V) = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm]
        exact ht x
      rw [this, map_one]
    obtain ⟨x, hx⟩ := c.delta_surjective (Multiplicative.ofAdd ![(1 : F4), 0])
    have := hone x
    rw [hx, ofAdd_eq_one] at this
    exact WFacts.three_indep.1 this

open Classical in
@[expose] noncomputable def coord (c : Config25 Q V t) (x : Q) : F4V :=
  if h : x ∈ V then Multiplicative.toAdd (c.ι ⟨x, h⟩) else 0

theorem coord_of_mem {x : Q} (h : x ∈ V) : c.coord x = Multiplicative.toAdd (c.ι ⟨x, h⟩) := by
  simp [coord, h]

theorem coord_mul {v w : Q} (hv : v ∈ V) (hw : w ∈ V) :
    c.coord (v * w) = c.coord v + c.coord w := by
  rw [c.coord_of_mem (V.mul_mem hv hw), c.coord_of_mem hv, c.coord_of_mem hw]
  have : (⟨v * w, V.mul_mem hv hw⟩ : V) = ⟨v, hv⟩ * ⟨w, hw⟩ := rfl
  rw [this, map_mul, toAdd_mul]

theorem coord_one : c.coord 1 = 0 := by
  rw [c.coord_of_mem V.one_mem]
  have : (⟨1, V.one_mem⟩ : V) = 1 := rfl
  rw [this, map_one, toAdd_one]

theorem coord_eq_zero_iff {v : Q} (hv : v ∈ V) : c.coord v = 0 ↔ v = 1 := by
  rw [c.coord_of_mem hv]
  constructor
  · intro h
    have h1 : c.ι ⟨v, hv⟩ = 1 := by
      rw [← ofAdd_toAdd (c.ι ⟨v, hv⟩), h, ofAdd_zero]
    have h2 : (⟨v, hv⟩ : V) = 1 := c.ι.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  · rintro rfl
    have : (⟨1, hv⟩ : V) = 1 := rfl
    rw [this, map_one, toAdd_one]

theorem coord_inj {v w : Q} (hv : v ∈ V) (hw : w ∈ V) (h : c.coord v = c.coord w) : v = w := by
  rw [c.coord_of_mem hv, c.coord_of_mem hw] at h
  have : c.ι ⟨v, hv⟩ = c.ι ⟨w, hw⟩ := Multiplicative.toAdd.injective h
  exact congrArg Subtype.val (c.ι.injective this)

theorem coord_ι_symm (w : F4V) : c.coord (c.ι.symm (Multiplicative.ofAdd w) : Q) = w := by
  rw [c.coord_of_mem (Subtype.property _)]
  simp

theorem delta_eq_ofAdd_coord (x : Q) : c.delta x = Multiplicative.ofAdd (c.coord ⁅t, x⁆) := by
  rw [c.delta_apply, c.coord_of_mem (c.comm_mem x), ofAdd_toAdd]

theorem Acts.coord_apply (h : c.Acts φ f) {v : Q} (hv : v ∈ V) :
    c.coord (φ v) = f (c.coord v) := by
  have e : v = (c.ι.symm (Multiplicative.ofAdd (c.coord v)) : Q) := by
    rw [c.coord_of_mem hv, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have h1 : φ v = (c.ι.symm (Multiplicative.ofAdd (f (c.coord v))) : Q) := by
    conv_lhs => rw [e]
    exact h.act _
  rw [h1, c.coord_ι_symm]

end Config25

end CFSG.OddStandard.Seitz77
