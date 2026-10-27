module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Tim77Weak

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {H : Type} [Group H]

section Conj

theorem rightConjugate_normalizer (X : Subgroup H) (a : H) :
    rightConjugate (normalizer (X : Set H)) a = normalizer (rightConjugate X a : Set H) :=
  map_equiv_normalizer_eq X (MulAut.conj a⁻¹)

theorem rightConjugate_tim77I' (Q : Subgroup H) (a b : H) :
    rightConjugate (tim77I Q (b * a⁻¹)) a = rightConjugate Q a ⊓ rightConjugate Q b := by
  rw [tim77I, GoldschmidtFour.rightConjugate_inf, rightConjugate_mul, inv_mul_cancel_right]

theorem rightConjugate_tim77D' (Q : Subgroup H) (a b : H) :
    rightConjugate (tim77D Q (b * a⁻¹)) a =
      rightConjugate Q b ⊓ normalizer (rightConjugate Q a : Set H) := by
  rw [tim77D, GoldschmidtFour.rightConjugate_inf, rightConjugate_mul, inv_mul_cancel_right,
    rightConjugate_normalizer]

theorem rightConjugate_lt_rightConjugate {X Y : Subgroup H} (a : H) :
    rightConjugate X a < rightConjugate Y a ↔ X < Y := by
  have hinj : Function.Injective (MulAut.conj a⁻¹).toMonoidHom := (MulAut.conj a⁻¹).injective
  simp only [lt_iff_le_not_ge, rightConjugate, map_le_map_iff_of_injective hinj]

end Conj

section Lex

theorem tim77I_le_D (Q : Subgroup H) (h : H) : tim77I Q h ≤ tim77D Q h :=
  fun _ hx => ⟨hx.2, le_normalizer hx.1⟩

theorem tim77I_le_B (Q : Subgroup H) (h : H) : tim77I Q h ≤ tim77B Q h :=
  fun _ hx => ⟨hx.1, le_normalizer hx.2⟩

theorem tim77I_lt_D_iff (Q : Subgroup H) (h : H) : tim77I Q h < tim77D Q h ↔ ¬ tim77D Q h ≤ Q := by
  refine ⟨fun hlt hDQ => hlt.not_ge fun d hd => ⟨hDQ hd, hd.1⟩, fun hDQ => ?_⟩
  exact lt_of_le_of_ne (tim77I_le_D Q h) fun he => hDQ (he ▸ inf_le_left)

noncomputable def tim77Key (Q : Subgroup H) (g : H) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (Nat.card (tim77I Q g), toLex (Nat.card (tim77D Q g), Nat.card (tim77B Q g)))

@[expose] def Tim77LexMax (Q : Subgroup H) (h : H) : Prop :=
  tim77I Q h < tim77D Q h ∧
    ∀ g : H, tim77I Q g < tim77D Q g → tim77Key Q g ≤ tim77Key Q h

theorem exists_tim77LexMax [Finite H] {Q : Subgroup H} (hne : ∃ g : H, tim77I Q g < tim77D Q g) :
    ∃ h : H, Tim77LexMax Q h := by
  obtain ⟨h, hh, hmax⟩ := Set.exists_max_image {g : H | tim77I Q g < tim77D Q g} (tim77Key Q)
    (Set.toFinite _) hne
  exact ⟨h, hh, hmax⟩

variable {Q : Subgroup H} {h g : H}

theorem tim77Key_le_iff :
    tim77Key Q g ≤ tim77Key Q h ↔ Nat.card (tim77I Q g) < Nat.card (tim77I Q h) ∨
      Nat.card (tim77I Q g) = Nat.card (tim77I Q h) ∧
        (Nat.card (tim77D Q g) < Nat.card (tim77D Q h) ∨
          Nat.card (tim77D Q g) = Nat.card (tim77D Q h) ∧
            Nat.card (tim77B Q g) ≤ Nat.card (tim77B Q h)) := by
  simp only [tim77Key, Prod.Lex.toLex_le_toLex]

theorem Tim77LexMax.card_I_le (hL : Tim77LexMax Q h) (hg : tim77I Q g < tim77D Q g) :
    Nat.card (tim77I Q g) ≤ Nat.card (tim77I Q h) := by
  rcases tim77Key_le_iff.mp (hL.2 g hg) with h1 | ⟨h1, -⟩ <;> omega

theorem Tim77LexMax.card_D_le (hL : Tim77LexMax Q h) (hg : tim77I Q g < tim77D Q g)
    (hI : Nat.card (tim77I Q g) = Nat.card (tim77I Q h)) :
    Nat.card (tim77D Q g) ≤ Nat.card (tim77D Q h) := by
  rcases tim77Key_le_iff.mp (hL.2 g hg) with h1 | ⟨-, h2 | ⟨h2, -⟩⟩ <;> omega

theorem Tim77LexMax.card_B_le (hL : Tim77LexMax Q h) (hg : tim77I Q g < tim77D Q g)
    (hI : Nat.card (tim77I Q g) = Nat.card (tim77I Q h))
    (hD : Nat.card (tim77D Q g) = Nat.card (tim77D Q h)) :
    Nat.card (tim77B Q g) ≤ Nat.card (tim77B Q h) := by
  rcases tim77Key_le_iff.mp (hL.2 g hg) with h1 | ⟨-, h2 | ⟨-, h3⟩⟩ <;> omega

theorem Tim77LexMax.card_inf_le (hL : Tim77LexMax Q h) {a b : H}
    (hab : rightConjugate Q a ⊓ rightConjugate Q b <
      rightConjugate Q b ⊓ normalizer (rightConjugate Q a : Set H)) :
    Nat.card (rightConjugate Q a ⊓ rightConjugate Q b : Subgroup H) ≤ Nat.card (tim77I Q h) := by
  rw [← rightConjugate_tim77I', ← rightConjugate_tim77D', rightConjugate_lt_rightConjugate] at hab
  rw [← rightConjugate_tim77I', rightConjugate_card]
  exact hL.card_I_le hab

theorem Tim77LexMax.card_inf_normalizer_le (hL : Tim77LexMax Q h) {a b : H}
    (hab : rightConjugate Q a ⊓ rightConjugate Q b <
      rightConjugate Q b ⊓ normalizer (rightConjugate Q a : Set H))
    (hI : Nat.card (rightConjugate Q a ⊓ rightConjugate Q b : Subgroup H) =
      Nat.card (tim77I Q h)) :
    Nat.card (rightConjugate Q b ⊓ normalizer (rightConjugate Q a : Set H) : Subgroup H) ≤
      Nat.card (tim77D Q h) := by
  rw [← rightConjugate_tim77I', ← rightConjugate_tim77D', rightConjugate_lt_rightConjugate] at hab
  rw [← rightConjugate_tim77I', rightConjugate_card] at hI
  rw [← rightConjugate_tim77D', rightConjugate_card]
  exact hL.card_D_le hab hI

end Lex

section RelCent

def relCent (I : Subgroup H) (T : Set H) : Subgroup H where
  carrier := {g | g ∈ normalizer (I : Set H) ∧ ∀ t ∈ T, g * t * g⁻¹ * t⁻¹ ∈ I}
  mul_mem' := by
    rintro a b ⟨ha, hat⟩ ⟨hb, hbt⟩
    refine ⟨mul_mem ha hb, fun t ht => ?_⟩
    have h1 : a * (b * t * b⁻¹ * t⁻¹) * a⁻¹ ∈ I := (mem_normalizer_iff.mp ha _).mp (hbt t ht)
    have e : a * b * t * (a * b)⁻¹ * t⁻¹ =
        (a * (b * t * b⁻¹ * t⁻¹) * a⁻¹) * (a * t * a⁻¹ * t⁻¹) := by group
    rw [e]
    exact mul_mem h1 (hat t ht)
  one_mem' := ⟨one_mem _, fun t _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, hat⟩
    refine ⟨inv_mem ha, fun t ht => ?_⟩
    have h1 : a⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ * a⁻¹⁻¹ ∈ I :=
      (mem_normalizer_iff.mp (inv_mem ha) _).mp (inv_mem (hat t ht))
    have e : a⁻¹ * t * a⁻¹⁻¹ * t⁻¹ = a⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem mem_relCent {I : Subgroup H} {T : Set H} {g : H} :
    g ∈ relCent I T ↔ g ∈ normalizer (I : Set H) ∧ ∀ t ∈ T, g * t * g⁻¹ * t⁻¹ ∈ I :=
  Iff.rfl

theorem le_rightConjugate_of_mem_normalizer {I A : Subgroup H} {c : H} (hIA : I ≤ A)
    (hc : c ∈ normalizer (I : Set H)) : I ≤ rightConjugate A c := fun i hi => by
  rw [mem_rightConjugate_iff]
  exact hIA ((mem_normalizer_iff.mp hc i).mp hi)

theorem mem_rightConjugate_of_mem_relCent {I A : Subgroup H} {T : Set H} {c t : H}
    (hIA : I ≤ A) (hc : c ∈ relCent I T) (htT : t ∈ T) (htA : t ∈ A) : t ∈ rightConjugate A c := by
  rw [mem_rightConjugate_iff]
  have e : c * t * c⁻¹ = (c * t * c⁻¹ * t⁻¹) * t := by group
  rw [e]
  exact A.mul_mem (hIA (hc.2 t htT)) htA

theorem conj_commutator_eq {d y t : H} (hdt : d * t = t * d) :
    d * y * d⁻¹ * t * (d * y * d⁻¹)⁻¹ * t⁻¹ = d * (y * t * y⁻¹ * t⁻¹) * d⁻¹ := by
  have hdd : d⁻¹ * t * d = t := by rw [mul_assoc, ← hdt, inv_mul_cancel_left]
  calc d * y * d⁻¹ * t * (d * y * d⁻¹)⁻¹ * t⁻¹
      = d * (y * (d⁻¹ * t * d) * y⁻¹ * (d⁻¹ * t * d)⁻¹) * d⁻¹ := by group
    _ = d * (y * t * y⁻¹ * t⁻¹) * d⁻¹ := by rw [hdd]

theorem commutator_mem_tim77I {Q : Subgroup H} {h b d : H} (hb : b ∈ tim77B Q h)
    (hd : d ∈ tim77D Q h) : b * d * b⁻¹ * d⁻¹ ∈ tim77I Q h := by
  refine ⟨?_, ?_⟩
  · have : d * b⁻¹ * d⁻¹ ∈ Q := (mem_normalizer_iff.mp hd.2 _).mp (Q.inv_mem hb.1)
    have h1 := Q.mul_mem hb.1 this
    simpa [mul_assoc] using h1
  · have h1 : b * d * b⁻¹ ∈ rightConjugate Q h := (mem_normalizer_iff.mp hb.2 d).mp hd.1
    exact (rightConjugate Q h).mul_mem h1 ((rightConjugate Q h).inv_mem hd.1)

end RelCent

namespace Tim77Hyp

variable {S Q : Subgroup H} (hQ : Tim77Hyp S Q)
include hQ

theorem comm_of_mem_rightConjugate (a : H) {x y : H} (hx : x ∈ rightConjugate Q a)
    (hy : y ∈ rightConjugate Q a) : x * y = y * x := by
  rw [mem_rightConjugate_iff] at hx hy
  have h1 : (a * x * a⁻¹) * (a * y * a⁻¹) = (a * y * a⁻¹) * (a * x * a⁻¹) :=
    congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  have h2 : a * (x * y) * a⁻¹ = a * (y * x) * a⁻¹ := by
    calc a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      _ = (a * y * a⁻¹) * (a * x * a⁻¹) := h1
      _ = a * (y * x) * a⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h2)

theorem mul_self_of_mem_rightConjugate (a : H) {x : H} (hx : x ∈ rightConjugate Q a) :
    x * x = 1 := by
  rw [mem_rightConjugate_iff] at hx
  have h1 : (a * x * a⁻¹) ^ 2 = 1 := hQ.elem.2 _ hx
  have e : (a * x * a⁻¹) ^ 2 = a * (x * x) * a⁻¹ := by
    rw [pow_two]
    group
  rw [e] at h1
  exact conj_eq_one_iff.mp h1

theorem rightConjugate_le_normalizer {I : Subgroup H} (a : H) (hI : I ≤ rightConjugate Q a) :
    rightConjugate Q a ≤ normalizer (I : Set H) := fun _ hy =>
  centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ hi =>
    hQ.comm_of_mem_rightConjugate a (hI hi) hy)

theorem self_le_normalizer_of_le {I : Subgroup H} (hI : I ≤ Q) : Q ≤ normalizer (I : Set H) := by
  have h := hQ.rightConjugate_le_normalizer (I := I) 1 (by rw [rightConjugate_one]; exact hI)
  rwa [rightConjugate_one] at h

end Tim77Hyp

namespace Tim77LexMax

variable [Finite H] {S Q : Subgroup H} {h : H}

theorem mem_D_of_mem_B (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) {y : H}
    (hyB : y ∈ tim77B Q h) (hyI : y ∉ tim77I Q h) {r : H} (hr : r ∈ rightConjugate Q h)
    (hry : r * y * r⁻¹ * y⁻¹ ∈ tim77I Q h) : r ∈ tim77D Q h := by
  have hIQ : tim77I Q h ≤ Q := inf_le_left
  have hIR : tim77I Q h ≤ rightConjugate Q h := inf_le_right
  have hQN := hQ.self_le_normalizer_of_le hIQ
  have hRN := hQ.rightConjugate_le_normalizer h hIR
  set E : Subgroup H := rightConjugate Q h ⊓ relCent (tim77I Q h) {y} with hE
  have hDE : tim77D Q h ≤ E := fun d hd => by
    refine mem_inf.2 ⟨hd.1, mem_relCent.2 ⟨hRN hd.1, fun t ht => ?_⟩⟩
    rw [Set.mem_singleton_iff.mp ht]
    have h1 := inv_mem (commutator_mem_tim77I hyB hd)
    convert h1 using 1
    group
  have hQK : rightConjugate Q 1 ≤ relCent (tim77I Q h) {y} := by
    rw [rightConjugate_one]
    intro q hq
    refine mem_relCent.2 ⟨hQN hq, fun t ht => ?_⟩
    have hqy : q * y = y * q := congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨q, hq⟩ ⟨y, hyB.1⟩)
    rw [Set.mem_singleton_iff.mp ht, hqy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hEP : IsPGroup 2 E := (hQ.isPGroup_rightConjugate h).to_le inf_le_left
  obtain ⟨c, hcK, hcN⟩ := hQ.exists_le_normalizer hQK hEP inf_le_right
  rw [one_mul] at hcN
  have hIc : tim77I Q h ≤ rightConjugate Q c :=
    le_rightConjugate_of_mem_normalizer hIQ (mem_relCent.1 hcK).1
  have hyc : y ∈ rightConjugate Q c :=
    mem_rightConjugate_of_mem_relCent hIQ hcK rfl hyB.1
  by_contra hrD
  by_cases hEc : E ≤ rightConjugate Q c
  ·
    have hD' : tim77D Q h ≤ tim77D Q c := fun d hd => ⟨hEc (hDE hd), hd.2⟩
    have hΓ : tim77I Q c < tim77D Q c := (tim77I_lt_D_iff _ _).2 fun hle =>
      (tim77I_lt_D_iff Q h).1 hL.1 (hD'.trans hle)
    have hlt : tim77I Q h < tim77I Q c :=
      lt_of_le_of_ne (fun i hi => ⟨hi.1, hIc hi⟩) fun he => hyI (he ▸ ⟨hyB.1, hyc⟩)
    exact (card_lt_of_lt hlt).not_ge (hL.card_I_le hΓ)
  ·
    have hER : E ≤ rightConjugate Q h ⊓ normalizer (rightConjugate Q c : Set H) :=
      fun e he => ⟨(mem_inf.mp he).1, hcN he⟩
    have hΓ : rightConjugate Q c ⊓ rightConjugate Q h <
        rightConjugate Q h ⊓ normalizer (rightConjugate Q c : Set H) := by
      refine lt_of_le_of_ne (fun z hz => ⟨hz.2, le_normalizer hz.1⟩) fun he => hEc ?_
      exact hER.trans (he ▸ inf_le_left)
    have hI' : tim77I Q h ≤ rightConjugate Q c ⊓ rightConjugate Q h := le_inf hIc hIR
    have e1 := le_antisymm (hL.card_inf_le hΓ) (card_le_of_le hI')
    have hED : E = tim77D Q h :=
      (eq_of_le_of_card_ge hDE ((card_le_of_le hER).trans (hL.card_inf_normalizer_le hΓ e1))).symm
    exact hrD (hED ▸ mem_inf.2 ⟨hr, mem_relCent.2 ⟨hRN hr, fun t ht => by
      rw [Set.mem_singleton_iff.mp ht]
      exact hry⟩⟩)

theorem mem_B_of_mem_D (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) {x : H}
    (hxD : x ∈ tim77D Q h) (hxI : x ∉ tim77I Q h) {q : H} (hq : q ∈ Q)
    (hqx : q * x * q⁻¹ * x⁻¹ ∈ tim77I Q h) : q ∈ tim77B Q h := by
  have hIQ : tim77I Q h ≤ Q := inf_le_left
  have hIR : tim77I Q h ≤ rightConjugate Q h := inf_le_right
  have hQN := hQ.self_le_normalizer_of_le hIQ
  have hRN := hQ.rightConjugate_le_normalizer h hIR
  set C : Subgroup H := Q ⊓ relCent (tim77I Q h) {x} with hC
  have hBC : tim77B Q h ≤ C := fun b hb => mem_inf.2 ⟨hb.1, mem_relCent.2 ⟨hQN hb.1,
    fun t ht => by rw [Set.mem_singleton_iff.mp ht]; exact commutator_mem_tim77I hb hxD⟩⟩
  have hDC : tim77D Q h ≤ normalizer (C : Set H) := fun d hd =>
    GoldschmidtFour.mem_normalizer_of_conj_mem fun y hy => by
      have hyQ : y ∈ Q := (mem_inf.mp hy).1
      have hyK := mem_relCent.1 (mem_inf.mp hy).2
      refine mem_inf.2 ⟨(mem_normalizer_iff.mp hd.2 y).mp hyQ, mem_relCent.2 ⟨mul_mem (mul_mem
        (hRN hd.1) hyK.1) (inv_mem (hRN hd.1)), fun t ht => ?_⟩⟩
      rw [Set.mem_singleton_iff.mp ht,
        conj_commutator_eq (hQ.comm_of_mem_rightConjugate h hd.1 hxD.1)]
      exact (mem_normalizer_iff.mp (hRN hd.1) _).mp (hyK.2 x rfl)
  have hP : IsPGroup 2 (C ⊔ tim77D Q h : Subgroup H) :=
    (hQ.isPGroup.to_le inf_le_left).to_sup_of_normal_left'
      ((hQ.isPGroup_rightConjugate h).to_le inf_le_left) hDC
  have hRK : rightConjugate Q h ≤ relCent (tim77I Q h) {x} := fun r hr =>
    mem_relCent.2 ⟨hRN hr, fun t ht => by
      rw [Set.mem_singleton_iff.mp ht, hQ.comm_of_mem_rightConjugate h hr hxD.1,
        mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _⟩
  have hPK : C ⊔ tim77D Q h ≤ relCent (tim77I Q h) {x} :=
    sup_le inf_le_right fun d hd => hRK hd.1
  obtain ⟨c, hcK, hcN⟩ := hQ.exists_le_normalizer hRK hP hPK
  have hIR' : tim77I Q h ≤ rightConjugate Q (h * c) := by
    rw [← rightConjugate_mul]
    exact le_rightConjugate_of_mem_normalizer hIR (mem_relCent.1 hcK).1
  have hxR' : x ∈ rightConjugate Q (h * c) := by
    rw [← rightConjugate_mul]
    exact mem_rightConjugate_of_mem_relCent hIR hcK rfl hxD.1
  by_cases hDR' : tim77D Q h ≤ rightConjugate Q (h * c)
  ·
    have hD' : tim77D Q h ≤ tim77D Q (h * c) := fun d hd => ⟨hDR' hd, hd.2⟩
    have hI' : tim77I Q h ≤ tim77I Q (h * c) := fun i hi => ⟨hi.1, hIR' hi⟩
    have hC' : C ≤ tim77B Q (h * c) := fun y hy => ⟨(mem_inf.mp hy).1, hcN (mem_sup_left hy)⟩
    have hΓ : tim77I Q (h * c) < tim77D Q (h * c) := (tim77I_lt_D_iff _ _).2 fun hle =>
      (tim77I_lt_D_iff Q h).1 hL.1 (hD'.trans hle)
    have e1 : Nat.card (tim77I Q (h * c)) = Nat.card (tim77I Q h) :=
      le_antisymm (hL.card_I_le hΓ) (card_le_of_le hI')
    have e2 : Nat.card (tim77D Q (h * c)) = Nat.card (tim77D Q h) :=
      le_antisymm (hL.card_D_le hΓ e1) (card_le_of_le hD')
    have hCB : tim77B Q h = C :=
      eq_of_le_of_card_ge hBC ((card_le_of_le hC').trans (hL.card_B_le hΓ e1 e2))
    rw [hCB]
    exact mem_inf.2 ⟨hq, mem_relCent.2 ⟨hQN hq, fun t ht => by
      rw [Set.mem_singleton_iff.mp ht]
      exact hqx⟩⟩
  ·
    exfalso
    have hDN : tim77D Q h ≤
        rightConjugate Q h ⊓ normalizer (rightConjugate Q (h * c) : Set H) :=
      fun d hd => ⟨hd.1, hcN (mem_sup_right hd)⟩
    have hΓ : rightConjugate Q (h * c) ⊓ rightConjugate Q h <
        rightConjugate Q h ⊓ normalizer (rightConjugate Q (h * c) : Set H) := by
      refine lt_of_le_of_ne (fun z hz => ⟨hz.2, le_normalizer hz.1⟩) fun he => hDR' ?_
      exact hDN.trans (he ▸ inf_le_left)
    have hlt : tim77I Q h < rightConjugate Q (h * c) ⊓ rightConjugate Q h :=
      lt_of_le_of_ne (le_inf hIR' hIR) fun he => hxI (he ▸ ⟨hxR', hxD.1⟩)
    exact (card_lt_of_lt hlt).not_ge (hL.card_inf_le hΓ)

end Tim77LexMax

end CFSG.ComponentClassification.AS81
