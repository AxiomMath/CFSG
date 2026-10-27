module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53B
public import CFSG.LocalAnalysis.ComponentClassification.Foote5GH74

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem not_isConj_of_center {S P : Subgroup G} (hS : IsPGroup 2 S) {x y : G}
    (hP : IsSylowOf 2 P (centralizer ({x} : Set G))) (hlt : Nat.card P < Nat.card S)
    (hyZ : ∀ s ∈ S, s * y = y * s) : ¬ IsConj x y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hxy
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hle : conjugate S c ≤ centralizer ({x} : Set G) := by
    refine conjugate_le_of_forall fun s hs => mem_centralizer_singleton_iff.mpr ?_
    have h1 := hyZ s hs
    rw [← hc] at h1
    calc c⁻¹ * s * c * x = c⁻¹ * (s * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * s) * c := by rw [h1]
      _ = x * (c⁻¹ * s * c) := by group
  have h1 : Nat.card (conjugate S c) ≤ twoPart (centralizer ({x} : Set G)) :=
    card_le_twoPart (hS.map _) hle
  rw [card_conjugate_eq_card] at h1
  have h2 : Nat.card P = twoPart (centralizer ({x} : Set G)) := hP.card_eq
  omega

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem mem_coreActionKernel_footeF_of_commute {v e : G} (hvQ : v ∈ Q) (hv2 : orderOf v = 2)
    (heQ : e ∈ Q) (hve : v * e = e * v) : e ∈ coreActionKernel (footeF L₀ v) := by
  obtain ⟨hfix, hLb, -, -, -, -⟩ := h.footeF_data hvQ hv2
  rw [← hfix]
  exact mem_coreActionKernel_footeFixed hve (h.Q_le heQ) (hfix ▸ hLb)

theorem conj_mem_Q_of_conj_mem_Q {a v v' : G} (hvQ : v ∈ Q) (hv'Q : v' ∈ Q)
    (hv2 : orderOf v = 2) (hvv' : v * v' = v' * v) (hu : a⁻¹ * v * a ∈ Q)
    (hy : a⁻¹ * v' * a ∈ S) : a⁻¹ * v' * a ∈ Q := by
  have hu2 : orderOf (a⁻¹ * v * a) = 2 := by
    rw [show a⁻¹ * v * a = a⁻¹ * v * a⁻¹⁻¹ by rw [inv_inv], orderOf_conj', hv2]
  obtain ⟨hfix, -, -, -, -, -⟩ := h.footeF_data hu hu2
  have hyC : a⁻¹ * v' * a ∈ coreActionKernel (footeF L₀ (a⁻¹ * v * a)) := by
    rw [footeF_conj h.sec4.huniq]
    refine mem_coreActionKernel_conjugate ?_
    rw [show a * (a⁻¹ * v' * a) * a⁻¹ = v' by group]
    exact h.mem_coreActionKernel_footeF_of_commute hvQ hv2 hv'Q hvv'
  refine h.mem_Q_of_mem_coreActionKernel_footeFixed hu hu2 hy ?_ (by rw [hfix]; exact hyC)
  refine mem_centralizer_singleton_iff.mpr ?_
  calc a⁻¹ * v' * a * (a⁻¹ * v * a) = a⁻¹ * (v' * v) * a := by group
    _ = a⁻¹ * (v * v') * a := by rw [hvv']
    _ = a⁻¹ * v * a * (a⁻¹ * v' * a) := by group

theorem exists_a {w : G} (hwQ : w ∈ Q) (hw2 : orderOf w = 2) (hng : ¬ Good53 S L Q w)
    (hS₀ : IsSylowOf 2 (S ⊓ centralizer ({w} : Set G)) (centralizer ({w} : Set G))) :
    ∃ a : G, a⁻¹ * w * a ∈ S ⊓ centralizer ({w} : Set G) ∧
      a⁻¹ * z * a ∈ S ⊓ centralizer ({w} : Set G) ∧
      a⁻¹ * w * a ∉ Q ∧ a⁻¹ * z * a ∉ Q ∧ a⁻¹ * (w * z) * a ∉ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.sec4.simple
  have hw22 : w * w = 1 := by rw [← sq, ← hw2, pow_orderOf_eq_one]
  have hz22 : z * z = 1 := by rw [← sq, ← h.z2, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hw2; omega
  have hz1 : z ≠ 1 := fun h1 => by have := h.z2; rw [h1, orderOf_one] at this; omega
  have hwZ : ¬ ∀ s ∈ S, s * w = w * s := fun hZ =>
    hng ⟨1, one_mem _, by simpa using hwQ, by simpa using hZ⟩
  have hwz : w ≠ z := fun h1 => hwZ (h1 ▸ h.zS)
  have hcwz : w * z = z * w := h.zS w (h.QS hwQ)
  have hlt : Nat.card ↥(S ⊓ centralizer ({w} : Set G)) < Nat.card S := by
    refine card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h1 => hwZ fun s hs => ?_)
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp (h1.symm ▸ hs :
      s ∈ S ⊓ centralizer ({w} : Set G))).2
  have hzw : ¬ IsConj w z := not_isConj_of_center h.isPGroup_S hS₀ hlt h.zS
  obtain ⟨x', hx'S₀, hx'c, hx'w, hx'wz⟩ := exists_conj_mem_ne h.nonabelian hw2 hS₀ (w * z)
  obtain ⟨c, hc⟩ := isConj_iff.mp hx'c
  set W := GorensteinWalter.kleinFourOfCommutingInvolutions w z hw22 hz22 hcwz with hW
  have hWmem : ∀ e, e ∈ W ↔ e = w * z ∨ e = w ∨ e = z ∨ e = 1 := fun e => by
    change e ∈ ({w * z, w, z, 1} : Set G) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hx'S : x' ∈ S := (mem_inf.mp hx'S₀).1
  have hx'w' : x' * w = w * x' := mem_centralizer_singleton_iff.mp (mem_inf.mp hx'S₀).2
  have hWx' : ∀ e ∈ W, e * x' = x' * e := by
    intro e he
    rcases (hWmem e).mp he with rfl | rfl | rfl | rfl
    · rw [mul_assoc, (h.zS x' hx'S).symm, ← mul_assoc, ← hx'w', mul_assoc]
    · exact hx'w'.symm
    · exact (h.zS x' hx'S).symm
    · rw [one_mul, mul_one]
  have hWc : conjugate W c ≤ centralizer ({w} : Set G) := by
    refine conjugate_le_of_forall fun e he => mem_centralizer_singleton_iff.mpr ?_
    have h1 := hWx' e he
    rw [← hc] at h1
    calc c⁻¹ * e * c * w = c⁻¹ * (e * (c * w * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * w * c⁻¹) * e) * c := by rw [h1]
      _ = w * (c⁻¹ * e * c) := by group
  have hW2 : IsPGroup 2 W := (h.isPGroup_Q.to_le fun e he => by
    rcases (hWmem e).mp he with rfl | rfl | rfl | rfl
    · exact mul_mem hwQ h.zQ
    · exact hwQ
    · exact h.zQ
    · exact one_mem _)
  obtain ⟨k, hkw, hk⟩ := exists_conj_le_of_isSylowOf hS₀ hWc (hW2.map _)
  set a := c * k with ha
  have hWa : ∀ e ∈ W, a⁻¹ * e * a ∈ S ⊓ centralizer ({w} : Set G) := by
    intro e he
    have h1 := hk _ (conj_mem_conjugate he c)
    rwa [show k⁻¹ * (c⁻¹ * e * c) * k = a⁻¹ * e * a by rw [ha]; group] at h1
  have hwa := hWa w ((hWmem w).mpr (Or.inr (Or.inl rfl)))
  have hza := hWa z ((hWmem z).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hwza := hWa (w * z) ((hWmem _).mpr (Or.inl rfl))
  have hx'a : a * w * a⁻¹ = x' := by
    rw [ha, ← hc, show c * k * w * (c * k)⁻¹ = c * (k * w * k⁻¹) * c⁻¹ by group,
      mem_centralizer_singleton_iff.mp hkw, mul_inv_cancel_right]
  have hW4 : IsKleinFour W :=
    GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions w z hw22 hz22 hw1 hz1 hwz hcwz
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsKleinFour.isMulCommutative (G := W)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hWsq : ∀ x ∈ W, x * x = 1 := fun x hx =>
    congrArg Subtype.val (IsKleinFour.mul_self (G := W) ⟨x, hx⟩)
  have hWQ : ∀ x ∈ W, x ∈ Q := fun x hx => by
    rcases (hWmem x).mp hx with rfl | rfl | rfl | rfl
    · exact mul_mem hwQ h.zQ
    · exact hwQ
    · exact h.zQ
    · exact one_mem _
  have hwW : w ∈ W := (hWmem w).mpr (Or.inr (Or.inl rfl))
  have hzW : z ∈ W := (hWmem z).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hwzW : w * z ∈ W := (hWmem _).mpr (Or.inl rfl)
  have hwz1 : w * z ≠ 1 := fun h1 => hwz (by
    calc w = w * z * z := by rw [mul_assoc, hz22, mul_one]
      _ = z := by rw [h1, one_mul])
  have hord : ∀ x ∈ W, x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    orderOf_eq_prime (by rw [sq]; exact hWsq x hx) hx1
  have hinj : ∀ e₁ e₂ : G, a⁻¹ * e₁ * a = a⁻¹ * e₂ * a → e₁ = e₂ := fun e₁ e₂ h1 => by
    have h2 := congrArg (fun x => a * x * a⁻¹) h1
    simpa only [show ∀ e : G, a * (a⁻¹ * e * a) * a⁻¹ = e from fun e => by group] using h2
  have hin : ∀ e ∈ W, e ≠ 1 → a⁻¹ * e * a ∈ Q →
      a⁻¹ * e * a = w ∨ a⁻¹ * e * a = z ∨ a⁻¹ * e * a = w * z := by
    intro e he he1 heQ
    have h1 := hWa e he
    have h2 : a⁻¹ * e * a * (a⁻¹ * e * a) = 1 := by
      rw [show a⁻¹ * e * a * (a⁻¹ * e * a) = a⁻¹ * (e * e) * a by group, hWsq e he]; group
    rcases h.mem_W hwQ hw22 hw1 hwz heQ h2 (mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2)
      with h3 | h3 | h3 | h3
    · exact absurd (hinj e 1 (by rw [h3]; group)) he1
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h3)
  have hnotall : ¬ (a⁻¹ * w * a ∈ Q ∧ a⁻¹ * z * a ∈ Q ∧ a⁻¹ * (w * z) * a ∈ Q) := by
    rintro ⟨h1, h2, h3⟩
    have hx : ∀ e, a⁻¹ * e * a = w → x' = e := fun e he => by
      rw [← hx'a, ← he]; group
    have hA1 : a⁻¹ * w * a ≠ w := fun he => hx'w (hx w he)
    have hA2 : a⁻¹ * z * a ≠ w := fun he => hzw (hx z he ▸ hx'c)
    have hA3 : a⁻¹ * (w * z) * a ≠ w := fun he => hx'wz (hx _ he)
    have hA12 : a⁻¹ * w * a ≠ a⁻¹ * z * a := fun he => hwz (hinj _ _ he)
    have hA13 : a⁻¹ * w * a ≠ a⁻¹ * (w * z) * a := fun he => hz1 (by
      have h4 := hinj _ _ he
      calc z = w⁻¹ * (w * z) := by group
        _ = 1 := by rw [← h4, inv_mul_cancel])
    have hA23 : a⁻¹ * z * a ≠ a⁻¹ * (w * z) * a := fun he => hw1 (by
      have h4 := hinj _ _ he
      calc w = w * z * z⁻¹ := by group
        _ = 1 := by rw [← h4, mul_inv_cancel])
    rcases hin w hwW hw1 h1 with e1 | e1 | e1 <;>
    rcases hin z hzW hz1 h2 with e2 | e2 | e2 <;>
    rcases hin _ hwzW hwz1 h3 with e3 | e3 | e3 <;>
    first
      | exact hA1 e1
      | exact hA2 e2
      | exact hA3 e3
      | exact hA12 (e1.trans e2.symm)
      | exact hA13 (e1.trans e3.symm)
      | exact hA23 (e2.trans e3.symm)
  have hall : ∀ v ∈ W, ∀ v' ∈ W, v ≠ 1 → a⁻¹ * v * a ∈ Q → a⁻¹ * v' * a ∈ Q :=
    fun v hv v' hv' hv1 hu => h.conj_mem_Q_of_conj_mem_Q (hWQ v hv) (hWQ v' hv')
      (hord v hv hv1) (hWcomm v hv v' hv') hu (mem_inf.mp (hWa v' hv')).1
  refine ⟨a, hwa, hza, fun h1 => hnotall ⟨h1, hall w hwW z hzW hw1 h1,
    hall w hwW _ hwzW hw1 h1⟩, fun h1 => hnotall ⟨hall z hzW w hwW hz1 h1, h1,
    hall z hzW _ hwzW hz1 h1⟩, fun h1 => hnotall ⟨hall _ hwzW w hwW hwz1 h1,
    hall _ hwzW z hzW hwz1 h1, h1⟩⟩

end Sec5

end CFSG.ComponentClassification.Foote5
