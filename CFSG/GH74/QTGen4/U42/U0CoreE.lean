module

public import CFSG.GH74.QTGen4.U42.U0CoreD
public import Mathlib.GroupTheory.Index
public meta import CFSG.GH74.QTGen4.U42.U0CoreD
public meta import CFSG.Quasithin.H13.A5Setting
public meta import CFSG.Quasithin.Background.G2A5
public meta import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin.A5Model CFSG.QuasithinUnique CFSG.Quasithin.H13.A5

theorem c4_pact_fix4 : ∀ σ : Equiv.Perm (Fin 5), σ 4 = 4 → ∀ w : W5, c4 (pact σ w) = c4 w := by
  decide +kernel

theorem left_c4_mul {u v : Mc} (hu : InK4 u.right) :
    c4 (u * v).left = c4 u.left * c4 v.left := by
  rw [SemidirectProduct.mul_left, map_mul, c4_pact_fix4 _ (InK4_four _ hu)]

theorem left_mem_W3_of_right_one {X : Subgroup Mc}
    (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hXV : ¬ Wc ≤ X) {x : Mc} (hx : x ∈ X)
    (h1 : x.right = 1) : c4 x.left = 1 := by
  by_contra hc
  have hu : (SemidirectProduct.inl x.left : Mc) ∈ X := by
    have e : (SemidirectProduct.inl x.left : Mc) = x := by
      ext <;> simp [h1]
    rw [e]
    exact hx
  exact hXV (wc_le_of_c4_ne_one hXB hu hc)

theorem left_c4_eq_of_right_eq {X : Subgroup Mc}
    (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hXV : ¬ Wc ≤ X) {x y : Mc}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x.right = y.right) : c4 x.left = c4 y.left := by
  have hz : x * y⁻¹ ∈ X := X.mul_mem hx (X.inv_mem hy)
  have hz1 : (x * y⁻¹).right = 1 := by simp [hxy]
  have h1 := left_mem_W3_of_right_one hXB hXV hz hz1
  have key := left_c4_mul (u := x * y⁻¹) (v := y) (Or.inl hz1)
  rw [inv_mul_cancel_right, h1, one_mul] at key
  exact key

theorem left_conj_inr (c : Equiv.Perm (Fin 5)) (hc4 : c 4 = 4) (x : Mc) :
    c4 (SemidirectProduct.inr c * x * (SemidirectProduct.inr c)⁻¹).left = c4 x.left := by
  have hl : (SemidirectProduct.inr c * x * (SemidirectProduct.inr c)⁻¹).left
      = pact c x.left := by
    simp [SemidirectProduct.mul_left]
  rw [hl, c4_pact_fix4 c hc4]

theorem conjB_mem {X : Subgroup Mc} (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) {x : Mc}
    (hx : x ∈ X) (c : Equiv.Perm (Fin 5)) (hc1 : c.sign = 1) (hc4 : c 4 = 4) :
    SemidirectProduct.inr c * x * (SemidirectProduct.inr c)⁻¹ ∈ X :=
  hXB _ (inr_mem_Bc hc1 hc4) x hx

theorem conjB_right (x : Mc) (c : Equiv.Perm (Fin 5)) :
    (SemidirectProduct.inr c * x * (SemidirectProduct.inr c)⁻¹).right = c * x.right * c⁻¹ := by
  simp

theorem InD_even_InK4 : ∀ σ : Equiv.Perm (Fin 5), InD σ → σ.sign = 1 → InK4 σ := by
  decide +kernel

theorem odd_conj : ∀ τ : Equiv.Perm (Fin 5), InD τ → τ.sign ≠ 1 →
    ∃ c : Equiv.Perm (Fin 5), c.sign = 1 ∧ c 4 = 4 ∧ ¬ InD (c * τ * c⁻¹) := by
  decide +kernel

theorem right_InK4 {X : Subgroup Mc} (hXT : X ≤ Thc)
    (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) : ∀ x ∈ X, InK4 x.right := by
  intro x hx
  have hD : InD x.right := hXT hx
  by_cases hs : x.right.sign = 1
  · exact InD_even_InK4 _ hD hs
  · obtain ⟨c, hc1, hc4, hbad⟩ := odd_conj _ hD hs
    have hmem := conjB_mem hXB hx c hc1 hc4
    have hD' : InD (c * x.right * c⁻¹) := by
      rw [← conjB_right x c]
      exact hXT hmem
    exact (hbad hD').elim

def K4s : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | InK4 σ}
  one_mem' := Or.inl rfl
  mul_mem' := fun ha hb => InK4_mul _ _ ha hb
  inv_mem' := fun ha => InK4_inv _ ha

instance : DecidablePred (· ∈ K4s) := fun x => inferInstanceAs (Decidable (InK4 x))

theorem card_K4s : Nat.card K4s = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def rightOf (X : Subgroup Mc) : X →* Equiv.Perm (Fin 5) :=
  (SemidirectProduct.rightHom : Mc →* Equiv.Perm (Fin 5)).comp X.subtype

theorem right_surj {X : Subgroup Mc} (hK : ∀ x ∈ X, InK4 x.right)
    (hX : Nat.card X = 32) (hW : ∀ x ∈ X, x.right = 1 → c4 x.left = 1) :
    ∀ τ, InK4 τ → ∃ x ∈ X, x.right = τ := by
  have hNR := Subgroup.card_ker_mul_card_range (rightOf X)
  rw [hX] at hNR
  have hmem : ∀ n : (rightOf X).ker, ((n : X) : Mc).left ∈ W3 := by
    intro n
    have h1 : ((n : X) : Mc).right = 1 := MonoidHom.mem_ker.1 n.2
    exact mem_W3.2 (hW _ (n : X).2 h1)
  have hker : Nat.card (rightOf X).ker ≤ 8 := by
    rw [← card_W3]
    refine Nat.card_le_card_of_injective
      (fun n : (rightOf X).ker => (⟨((n : X) : Mc).left, hmem n⟩ : W3)) ?_
    intro n m hnm
    have hl : ((n : X) : Mc).left = ((m : X) : Mc).left := congrArg Subtype.val hnm
    have hr1 : ((n : X) : Mc).right = 1 := MonoidHom.mem_ker.1 n.2
    have hr2 : ((m : X) : Mc).right = 1 := MonoidHom.mem_ker.1 m.2
    refine Subtype.ext (Subtype.ext ?_)
    exact SemidirectProduct.ext hl (hr1.trans hr2.symm)
  have hR : 4 ≤ Nat.card (rightOf X).range := by
    by_contra h
    push_neg at h
    have h8 := Nat.mul_le_mul_right (Nat.card (rightOf X).range) hker
    linarith
  have hle : (rightOf X).range ≤ K4s := by
    intro σ hσ
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hσ
    exact hK x.1 x.2
  have hEq : (rightOf X).range = K4s :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_K4s]; exact hR)
  intro τ hτ
  have hτm : τ ∈ (rightOf X).range := by
    rw [hEq]
    exact hτ
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hτm
  exact ⟨x.1, x.2, hx⟩

theorem U0_unique {X : Subgroup Mc} (hXT : X ≤ Thc) (hX : Nat.card X = 32)
    (hXB : ∀ b ∈ Bc, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hXV : ¬ Wc ≤ X) : X = U0 := by
  have hK := right_InK4 hXT hXB
  have hW : ∀ x ∈ X, x.right = 1 → c4 x.left = 1 :=
    fun x hx h1 => left_mem_W3_of_right_one hXB hXV hx h1
  have hsurj := right_surj hK hX hW
  obtain ⟨a, ha, hra⟩ := hsurj CFSG.Quasithin.A5Model.pa (Or.inr (Or.inl rfl))
  obtain ⟨b, hb, hrb⟩ := hsurj CFSG.Quasithin.A5Model.pb (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨cb, hcb1, hcb4, hcb⟩ : ∃ c : Equiv.Perm (Fin 5), c.sign = 1 ∧ c 4 = 4 ∧
      c * CFSG.Quasithin.A5Model.pa * c⁻¹ = CFSG.Quasithin.A5Model.pb := by
    decide +kernel
  obtain ⟨cc, hcc1, hcc4, hcc⟩ : ∃ c : Equiv.Perm (Fin 5), c.sign = 1 ∧ c 4 = 4 ∧
      c * CFSG.Quasithin.A5Model.pa * c⁻¹ = CFSG.Quasithin.A5Model.pc := by
    decide +kernel
  have hpq : CFSG.Quasithin.A5Model.pa * CFSG.Quasithin.A5Model.pb
      = CFSG.Quasithin.A5Model.pc := by
    decide +kernel
  have hyb : (SemidirectProduct.inr cb * a * (SemidirectProduct.inr cb)⁻¹).right
      = CFSG.Quasithin.A5Model.pb := by
    rw [conjB_right, hra, hcb]
  have hyc : (SemidirectProduct.inr cc * a * (SemidirectProduct.inr cc)⁻¹).right
      = CFSG.Quasithin.A5Model.pc := by
    rw [conjB_right, hra, hcc]
  have hab : (a * b).right = CFSG.Quasithin.A5Model.pc := by
    rw [SemidirectProduct.mul_right, hra, hrb, hpq]
  have eb : c4 b.left = c4 a.left := by
    have h1 := left_c4_eq_of_right_eq hXB hXV (conjB_mem hXB ha cb hcb1 hcb4) hb
      (by rw [hyb, hrb])
    rw [left_conj_inr cb hcb4] at h1
    exact h1.symm
  have h2 := left_c4_eq_of_right_eq hXB hXV (X.mul_mem ha hb)
    (conjB_mem hXB ha cc hcc1 hcc4) (by rw [hab, hyc])
  rw [left_conj_inr cc hcc4] at h2
  have hm := left_c4_mul (u := a) (v := b) (hK a ha)
  have he : c4 a.left = 1 := by
    have h3 : c4 a.left = c4 a.left * c4 a.left := by
      have h4 := hm
      rw [h2, eb] at h4
      exact h4
    exact mul_left_cancel (a := c4 a.left) (h3.symm.trans (mul_one _).symm)
  have hall : ∀ x ∈ X, c4 x.left = 1 := by
    intro x hx
    rcases hK x hx with h | h | h | h
    · exact left_mem_W3_of_right_one hXB hXV hx h
    · rw [left_c4_eq_of_right_eq hXB hXV hx ha (by rw [h, hra]), he]
    · rw [left_c4_eq_of_right_eq hXB hXV hx hb (by rw [h, hrb]), eb, he]
    · rw [left_c4_eq_of_right_eq hXB hXV hx (X.mul_mem ha hb) (by rw [h, hab]), h2, he]
  have hle : X ≤ U0 := by
    intro x hx
    exact (show x.left ∈ W3 ∧ InK4 x.right from ⟨mem_W3.2 (hall x hx), hK x hx⟩)
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [card_U0, hX]))

end CFSG.GH74.QTGen4.U42
