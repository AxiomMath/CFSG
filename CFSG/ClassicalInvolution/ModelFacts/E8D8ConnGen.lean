module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E8D8

open CFSG.ClassicalInvolution.Generic

variable {K : Type*} [Group K]

theorem commutes_conjSub_iff (g : K) (A B : Subgroup K) :
    Commutes (conjSub g A) (conjSub g B) ↔ Commutes A B := by
  constructor
  · intro h a ha b hb
    have := h (g * a * g⁻¹) ⟨a, ha, rfl⟩ (g * b * g⁻¹) ⟨b, hb, rfl⟩
    have e : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      simpa only [mul_assoc, inv_mul_cancel_left] using this
    exact mul_left_cancel (mul_right_cancel e)
  · rintro h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := h a ha b hb
    change g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [this]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem conjSub_eq_self_of_mem {T : Subgroup K} {x : K} (hx : x ∈ T) : conjSub x T = T := by
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have h1 := T.mul_mem (T.mul_mem hx h) (T.inv_mem hx)
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rwa [e] at h1
  · intro h
    exact T.mul_mem (T.mul_mem (T.inv_mem hx) h) hx

theorem conjSub_eq_self_of_commutes {S T : Subgroup K} (h : Commutes S T) {x : K} (hx : x ∈ T) :
    conjSub x S = S := by
  have hc : ∀ s ∈ S, x⁻¹ * s * x = s := fun s hs => by
    rw [mul_assoc, h s hs x hx, inv_mul_cancel_left]
  have hc' : ∀ s ∈ S, x * s * x⁻¹ = s := fun s hs => by
    rw [mul_assoc, h s hs x⁻¹ (T.inv_mem hx), mul_inv_cancel_left]
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro hy
    have e : y = x⁻¹ * y * x :=
      calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
        _ = x⁻¹ * y * x := hc' _ hy
    rw [e]
    exact hy
  · intro hy
    rw [hc y hy]
    exact hy

theorem reflTransGen_symm_of_symm {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a)
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hr _ _ hbc) ih

theorem reflTransGen_of_generated {Fund : Set (Subgroup K)}
    (hconj : ∀ R ∈ Fund, ∀ g : K, conjSub g R ∈ Fund)
    (hsingle : ∀ R ∈ Fund, ∀ R' ∈ Fund, ∃ g : K, R' = conjSub g R)
    (hgen : (⊤ : Subgroup K) ≤ ⨆ R ∈ Fund, R) (A B : Fund) :
    Relation.ReflTransGen (fun X Y : Fund => ¬ Commutes X.1 Y.1) A B := by
  let act : K → Fund → Fund := fun g S => ⟨conjSub g S.1, hconj S.1 S.2 g⟩
  have act_one : ∀ S, act 1 S = S := fun S => Subtype.ext (conjSub_one S.1)
  have act_mul : ∀ g h S, act (g * h) S = act g (act h S) := fun g h S =>
    Subtype.ext (conjSub_mul g h S.1)
  have hsymm : ∀ {X Y : Fund}, Relation.ReflTransGen (fun X Y : Fund => ¬ Commutes X.1 Y.1) X Y →
      Relation.ReflTransGen (fun X Y : Fund => ¬ Commutes X.1 Y.1) Y X :=
    fun {X Y} h => reflTransGen_symm_of_symm
      (fun X Y hXY hYX => hXY fun a ha b hb => (hYX b hb a ha).symm) h
  have key : ∀ (T : Fund) (x : K), x ∈ T.1 → ∀ S : Fund,
      Relation.ReflTransGen (fun X Y : Fund => ¬ Commutes X.1 Y.1) S (act x S) := by
    intro T x hx S
    by_cases h : Commutes S.1 T.1
    · have : act x S = S := Subtype.ext (conjSub_eq_self_of_commutes h hx)
      rw [this]
    · refine Relation.ReflTransGen.head (b := T) h (Relation.ReflTransGen.single ?_)
      intro hc
      have h1 := (commutes_conjSub_iff x⁻¹ T.1 (conjSub x S.1)).mpr hc
      rw [conjSub_eq_self_of_mem (T.1.inv_mem hx), conjSub_inv_conjSub] at h1
      exact h fun a ha b hb => (h1 b hb a ha).symm
  let N : Subgroup K :=
    { carrier := {g | ∀ S : Fund,
        Relation.ReflTransGen (fun X Y : Fund => ¬ Commutes X.1 Y.1) S (act g S)}
      one_mem' := fun S => by rw [act_one]
      mul_mem' := fun {g h} hg hh S => by
        rw [act_mul]
        exact (hh S).trans (hg (act h S))
      inv_mem' := fun {g} hg S => by
        have := hg (act g⁻¹ S)
        rw [← act_mul, mul_inv_cancel, act_one] at this
        exact hsymm this }
  have hN : N = ⊤ := by
    refine eq_top_iff.mpr (hgen.trans (iSup₂_le fun R hR x hx => ?_))
    exact key ⟨R, hR⟩ x hx
  obtain ⟨g, hg⟩ := hsingle A.1 A.2 B.1 B.2
  have hB : B = act g A := Subtype.ext hg
  have hgN : g ∈ N := by rw [hN]; exact Subgroup.mem_top g
  rw [hB]
  exact hgN A

end CFSG.ClassicalInvolution.ModelFacts.E8D8
