module

public import CFSG.ClassicalInvolution.Q3.AE.Bar

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

open CFSG.ClassicalInvolution.Q3.AE

@[expose] def Hn (n : ℕ) : Subgroup (AEQ n) := (aeSub n).map (mkQ n)

@[expose] def PermMembers {n : ℕ} (H : Subgroup (AEQ n)) (σ : ↥H →* ↥H) : Prop :=
  ∀ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool), ∃ (β' : Finset (Fin n)) (hβ' : β'.card = 4)
    (c' : Bool), ∀ x : ↥H, (x : AEQ n) ∈ memBar β hβ c → (σ x : AEQ n) ∈ memBar β' hβ' c'

@[expose] def AEAut (n : ℕ) : Prop :=
  ∀ (H : Subgroup (AEQ n)), H = Hn n → ∀ σ : ↥H →* ↥H, Function.Bijective σ → PermMembers H σ →
    ∃ w : Wr n, ∀ x : ↥H, (σ x : AEQ n) = mkQ n w * (x : AEQ n) * (mkQ n w)⁻¹

@[expose] def AEPerm (n : ℕ) : Prop :=
  ∀ (α : Finset (Fin n)) (hα : α.card = 4) (w : Wr n),
    (∃ a : ℕ, ∀ x ∈ Hn n, mkQ n (w ^ 3 ^ a) * x * (mkQ n (w ^ 3 ^ a))⁻¹ = x) →
    (∀ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool), (Disjoint α β ∨ β = α) →
      ∀ x ∈ memBar β hβ c, mkQ n w * x * (mkQ n w)⁻¹ = x) →
    n = 7 ∨ ∀ x ∈ Hn n, mkQ n w * x * (mkQ n w)⁻¹ = x

@[expose] def AEThree (n : ℕ) : Prop :=
  ∀ (α : Finset (Fin n)) (hα : α.card = 4) (H : Subgroup (AEQ n)), H = Hn n → ∀ σ : ↥H →* ↥H,
    (∃ a : ℕ, ∀ r, (⇑σ)^[3 ^ a] r = r) → PermMembers H σ →
    (∀ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool), (Disjoint α β ∨ β = α) →
      ∀ x : ↥H, (x : AEQ n) ∈ memBar β hβ c → σ x = x) →
    n = 7 ∨ ∀ r, σ r = r

@[expose] def IsMember {n : ℕ} (M : Subgroup (AEQ n)) : Prop :=
  ∃ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool), M = memBar β hβ c

@[expose] def IsBlock {n : ℕ} (B : Set (Subgroup (AEQ n))) : Prop :=
  (∀ M ∈ B, IsMember M) ∧ ∀ s ∈ Hn n, (fun M => M.map (MulAut.conj s).toMonoidHom) '' B = B ∨
      Disjoint ((fun M => M.map (MulAut.conj s).toMonoidHom) '' B) B

theorem memBar_le_Hn {n : ℕ} (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool) :
    memBar β hβ c ≤ Hn n := by
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨w, ?_, rfl⟩
  cases c
  · exact memKStar_le_aeSub _ hw
  · exact memK_le_aeSub _ hw

theorem aeThree_of_aut_perm {n : ℕ} (hA : AEAut n) (hP : AEPerm n) : AEThree n := by
  intro α hα H hH σ ⟨a, ha⟩ hperm hcent
  have hk : 3 ^ a = (3 ^ a - 1) + 1 := by
    have : 0 < 3 ^ a := Nat.pow_pos (by norm_num)
    omega
  have hid : (⇑σ)^[3 ^ a] = id := funext ha
  have hid1 : (⇑σ)^[3 ^ a - 1] ∘ ⇑σ = id := by
    rw [← Function.iterate_succ, Nat.succ_eq_add_one, ← hk]; exact hid
  have hid2 : ⇑σ ∘ (⇑σ)^[3 ^ a - 1] = id := by
    rw [← Function.iterate_succ', Nat.succ_eq_add_one, ← hk]; exact hid
  have hbij : Function.Bijective σ :=
    ⟨Function.Injective.of_comp (f := (⇑σ)^[3 ^ a - 1]) (by rw [hid1]; exact Function.injective_id),
     Function.Surjective.of_comp (g := (⇑σ)^[3 ^ a - 1]) (by rw [hid2]; exact Function.surjective_id)⟩
  obtain ⟨w, hw⟩ := hA H hH σ hbij hperm
  have hit : ∀ (k : ℕ) (x : ↥H), (((⇑σ)^[k] x : ↥H) : AEQ n) =
      mkQ n (w ^ k) * (x : AEQ n) * (mkQ n (w ^ k))⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', hw, ih, pow_succ', map_mul]
      group
  have hcent' : ∀ (β : Finset (Fin n)) (hβ : β.card = 4) (c : Bool), (Disjoint α β ∨ β = α) →
      ∀ x ∈ memBar β hβ c, mkQ n w * x * (mkQ n w)⁻¹ = x := by
    intro β hβ c hd x hx
    have hxH : x ∈ H := by rw [hH]; exact memBar_le_Hn β hβ c hx
    have := hcent β hβ c hd ⟨x, hxH⟩ hx
    have h2 := congrArg Subtype.val this
    rw [hw] at h2
    exact h2
  have hor := hP α hα w ⟨a, fun x hx => by
      have hxH : x ∈ H := by rw [hH]; exact hx
      have h1 := hit (3 ^ a) ⟨x, hxH⟩
      rw [ha ⟨x, hxH⟩] at h1
      exact h1.symm⟩ hcent'
  rcases hor with h7 | hall
  · exact Or.inl h7
  · right
    intro r
    apply Subtype.ext
    rw [hw]
    exact hall r (by rw [← hH]; exact r.2)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8
