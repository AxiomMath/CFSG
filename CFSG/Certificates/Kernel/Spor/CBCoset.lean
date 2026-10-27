module

public import CFSG.Certificates.Kernel.Spor.CBComm

public section

namespace CFSG.KS.CB

open CFSG.KC.Enum CFSG.ONSchreier.Native

@[expose] noncomputable def cfK (U Ui X A : Nat → Nat) (STEP₁ INV₁ : Nat → Nat → Nat)
    (PAR₁ LAB₁ : Nat → Nat) (m₁ : Nat) (STEP₂ : Nat → Nat → Nat) (PAR₂ LAB₂ : Nat → Nat)
    (m₂ b₁ b₂ k₁ : Nat) : Bool :=
  strictB (trInvK PAR₁ LAB₁ INV₁ m₁ k₁ (Ui (X (U (trK STEP₁ PAR₁ LAB₁ m₁ k₁ b₁))))) fun v =>
    allN m₂ fun k₂ => !(Nat.beq (A k₂) v &&
      Nat.beq (U (trK STEP₁ PAR₁ LAB₁ m₁ k₁ (trK STEP₂ PAR₂ LAB₂ m₂ k₂ (X b₂))))
        (X (U (trK STEP₁ PAR₁ LAB₁ m₁ k₁ (trK STEP₂ PAR₂ LAB₂ m₂ k₂ b₂)))))

theorem strictB_app' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem cosetTest_false {n m₁ m₂ r₁ r₂ i₁ i₂ b₀ b₁ b₂ : Nat} {levels : Array CLevel}
    {stepsAll : Array (Array (Array Nat))} {u x : Array Nat}
    {PTS₁ POS₁ PAR₁ LAB₁ PTS₂ POS₂ PAR₂ LAB₂ U Ui X A : Nat → Nat}
    {STEP₁ INV₁ STEP₂ : Nat → Nat → Nat}
    (hL₁ : levels[i₁]! = ⟨Array.ofFn (n := m₁) fun k => PTS₁ k.val,
      Array.ofFn (n := n) fun z => POS₁ z.val, Array.ofFn (n := m₁) fun k => PAR₁ k.val,
      Array.ofFn (n := m₁) fun k => LAB₁ k.val⟩)
    (hL₂ : levels[i₂]! = ⟨Array.ofFn (n := m₂) fun k => PTS₂ k.val,
      Array.ofFn (n := n) fun z => POS₂ z.val, Array.ofFn (n := m₂) fun k => PAR₂ k.val,
      Array.ofFn (n := m₂) fun k => LAB₂ k.val⟩)
    (hm₁ : ∀ k < m₁, PAR₁ k < m₁ ∧ LAB₁ k < r₁) (hm₂ : ∀ k < m₂, PAR₂ k < m₂ ∧ LAB₂ k < r₂)
    (hs₁ : ∀ j < r₁, ∀ y < n, ((stepsAll[i₁]!)[j]!)[y]! = STEP₁ j y ∧ STEP₁ j y < n ∧
      INV₁ j y < n ∧ INV₁ j (STEP₁ j y) = y ∧ STEP₁ j (INV₁ j y) = y)
    (hs₂ : ∀ j < r₂, ∀ y < n, ((stepsAll[i₂]!)[j]!)[y]! = STEP₂ j y ∧ STEP₂ j y < n)
    (hf₂ : ∀ j < r₂, STEP₂ j b₁ = b₁)
    (hu : ∀ p < n, u[p]! = U p ∧ U p < n ∧ Ui (U p) = p)
    (hx : ∀ p < n, x[p]! = X p ∧ X p < n) (hb : b₁ < n ∧ b₂ < n)
    (hA : ∀ k < m₂, A k = trK STEP₂ PAR₂ LAB₂ m₂ k (X b₁))
    {k₁ : Nat} (hk₁ : k₁ < m₁)
    (h : cfK U Ui X A STEP₁ INV₁ PAR₁ LAB₁ m₁ STEP₂ PAR₂ LAB₂ m₂ b₁ b₂ k₁ = true)
    {k₂ : Nat} (hk₂ : k₂ < m₂) :
    (#[b₀, b₁, b₂].all fun p => u[tr2App levels stepsAll i₁ i₂ k₁ k₂ x[p]!]! ==
      x[u[tr2App levels stepsAll i₁ i₂ k₁ k₂ p]!]!) = false := by
  obtain ⟨hb₁, hb₂⟩ := hb
  have hs₁' : ∀ j < r₁, ∀ y < n, ((stepsAll[i₁]!)[j]!)[y]! = STEP₁ j y ∧ STEP₁ j y < n :=
    fun j hj y hy => ⟨(hs₁ j hj y hy).1, (hs₁ j hj y hy).2.1⟩
  have hlt₁ := trK_lt hm₁ (fun j hj y hy => (hs₁ j hj y hy).2.1)
  have hlt₂ := trK_lt hm₂ (fun j hj y hy => (hs₂ j hj y hy).2)
  have hT : ∀ p < n, tr2App levels stepsAll i₁ i₂ k₁ k₂ p =
      trK STEP₁ PAR₁ LAB₁ m₁ k₁ (trK STEP₂ PAR₂ LAB₂ m₂ k₂ p) := by
    intro p hp
    unfold tr2App
    rw [hL₁, hL₂, Array.size_ofFn, Array.size_ofFn, trApp_eqK hm₂ hs₂ _ _ _ hk₂ hp,
      trApp_eqK hm₁ hs₁' _ _ _ hk₁ (hlt₂ _ _ _ hk₂ hp)]
  have f₁ : trK STEP₂ PAR₂ LAB₂ m₂ k₂ b₁ = b₁ := trK_fix hm₂ hf₂ _ _ hk₂
  have hinv₁ := trInvK_trK (n := n) hm₁
    (fun j hj y hy => ⟨(hs₁ j hj y hy).2.1, (hs₁ j hj y hy).2.2.2.1⟩)
  rw [Bool.eq_false_iff]
  intro hall
  simp only [List.all_toArray, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hall
  obtain ⟨-, e₁, e₂⟩ := hall
  have xb₁ := hx b₁ hb₁
  have xb₂ := hx b₂ hb₂
  have ht₁ := hlt₁ m₁ k₁ b₁ hk₁ hb₁
  rw [xb₁.1, hT _ xb₁.2, hT _ hb₁, f₁, (hu _ ht₁).1, (hx _ (hu _ ht₁).2.1).1,
    ← hA k₂ hk₂] at e₁
  have hAlt : A k₂ < n := by
    rw [hA k₂ hk₂]
    exact hlt₂ _ _ _ hk₂ xb₁.2
  have hT₂ := hlt₁ m₁ k₁ _ hk₁ hAlt
  rw [(hu _ hT₂).1] at e₁
  have hv : A k₂ = trInvK PAR₁ LAB₁ INV₁ m₁ k₁ (Ui (X (U (trK STEP₁ PAR₁ LAB₁ m₁ k₁ b₁)))) := by
    rw [← e₁, (hu _ hT₂).2.2, hinv₁ m₁ k₁ _ hk₁ hAlt]
  have hp₂ := hlt₁ m₁ k₁ _ hk₁ (hlt₂ m₂ k₂ _ hk₂ xb₂.2)
  have hq₂ := hlt₁ m₁ k₁ _ hk₁ (hlt₂ m₂ k₂ _ hk₂ hb₂)
  rw [xb₂.1, hT _ xb₂.2, hT _ hb₂, (hu _ hp₂).1, (hu _ hq₂).1, (hx _ (hu _ hq₂).2.1).1] at e₂
  unfold cfK at h
  rw [strictB_app'] at h
  have h' := CFSG.KS.allN_spec h k₂ hk₂
  rw [hv, Nat.beq_refl, Bool.true_and, e₂, Nat.beq_refl] at h'
  exact absurd h' (by decide)

end CFSG.KS.CB

end
