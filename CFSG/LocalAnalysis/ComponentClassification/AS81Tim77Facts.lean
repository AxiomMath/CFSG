module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Tim77Lex

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {H : Type} [Group H]

section Basic

theorem tim77D_le_normalizer_tim77B (Q : Subgroup H) (h : H) :
    tim77D Q h ≤ normalizer (tim77B Q h : Set H) := by
  intro d hd
  have h1 : d ∈ normalizer (Q : Set H) := hd.2
  have h2 : d ∈ normalizer (normalizer (rightConjugate Q h : Set H) : Set H) :=
    le_normalizer (le_normalizer hd.1)
  rw [mem_normalizer_iff] at h1 h2 ⊢
  intro x
  exact ⟨fun hx => ⟨(h1 x).mp hx.1, (h2 x).mp hx.2⟩, fun hx => ⟨(h1 x).mpr hx.1, (h2 x).mpr hx.2⟩⟩

theorem commutator_commute_of_mem {A : Subgroup H} (hA : IsElemAbelian 2 A) {a t : H}
    (ha : a ∈ A) (htN : t ∈ normalizer (A : Set H)) (htt : t * t = 1) :
    (a * t * a⁻¹ * t⁻¹) * t * (a * t * a⁻¹ * t⁻¹)⁻¹ * t⁻¹ = 1 := by
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hA.2 x hx
  have ha' : t * a⁻¹ * t⁻¹ ∈ A := (mem_normalizer_iff.mp htN _).mp (inv_mem ha)
  have hcomm : (t * a⁻¹ * t⁻¹) * a = a * (t * a⁻¹ * t⁻¹) :=
    congrArg Subtype.val (hA.1.is_comm.comm ⟨_, ha'⟩ ⟨a, ha⟩)
  have e : (a * t * a⁻¹ * t⁻¹) * t * (a * t * a⁻¹ * t⁻¹)⁻¹ * t⁻¹ =
      (a * (t * a⁻¹ * t⁻¹)) * ((t * (t * a⁻¹ * t⁻¹)⁻¹ * t⁻¹) * (t * a⁻¹ * t⁻¹)) := by group
  have e2 : t * (t * a⁻¹ * t⁻¹)⁻¹ * t⁻¹ = a := by
    calc t * (t * a⁻¹ * t⁻¹)⁻¹ * t⁻¹ = (t * t) * a * (t * t)⁻¹ := by group
      _ = a := by rw [htt]; group
  rw [e, e2]
  calc a * (t * a⁻¹ * t⁻¹) * (a * (t * a⁻¹ * t⁻¹))
      = a * ((t * a⁻¹ * t⁻¹) * a) * (t * a⁻¹ * t⁻¹) := by group
    _ = (a * a) * ((t * a⁻¹ * t⁻¹) * (t * a⁻¹ * t⁻¹)) := by rw [hcomm]; group
    _ = 1 := by rw [hsq a ha, hsq _ ha', one_mul]

theorem card_le_of_inj_mod [Finite H] {B D I : Subgroup H} (hIB : I ≤ B) (hID : I ≤ D)
    (f : H → H) (hf : ∀ d ∈ D, f d ∈ B)
    (hmul : ∀ d ∈ D, ∀ e ∈ D, (f d)⁻¹ * f (d * e) * (f e)⁻¹ ∈ I)
    (hfI : ∀ i ∈ I, f i ∈ I) (hker : ∀ d ∈ D, f d ∈ I → d ∈ I) :
    Nat.card D ≤ Nat.card B := by
  have hrel : ∀ d ∈ D, ∀ e ∈ D, (f d)⁻¹ * f (d * e) ∈ I ↔ e ∈ I := by
    intro d hd e he
    have h1 := hmul d hd e he
    constructor
    · intro h2
      apply hker e he
      have : f e = ((f d)⁻¹ * f (d * e) * (f e)⁻¹)⁻¹ * ((f d)⁻¹ * f (d * e)) := by group
      rw [this]
      exact mul_mem (inv_mem h1) h2
    · intro h2
      have : (f d)⁻¹ * f (d * e) = ((f d)⁻¹ * f (d * e) * (f e)⁻¹) * f e := by group
      rw [this]
      exact mul_mem h1 (hfI e h2)
  have hrel' : ∀ d d' : ↥D, (f d)⁻¹ * f d' ∈ I ↔ (d : H)⁻¹ * d' ∈ I := by
    intro d d'
    have := hrel d d.2 ((d : H)⁻¹ * d') (mul_mem (inv_mem d.2) d'.2)
    rwa [mul_inv_cancel_left] at this
  let Φ : ↥D ⧸ I.subgroupOf D → ↥B ⧸ I.subgroupOf B :=
    Quotient.map' (fun d : ↥D => (⟨f d, hf d d.2⟩ : ↥B)) (fun d d' hdd' => by
      rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hdd' ⊢
      simpa using (hrel' d d').2 (by simpa using hdd'))
  have hΦ : ∀ d : ↥D, Φ (d : ↥D ⧸ I.subgroupOf D) = ((⟨f d, hf d d.2⟩ : ↥B) : _) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H d => ?_
    induction y using QuotientGroup.induction_on with | H d' => ?_
    rw [hΦ, hΦ, QuotientGroup.eq, mem_subgroupOf] at hxy
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa using (hrel' d d').1 (by simpa using hxy)
  have hcD : Nat.card D = Nat.card (↥D ⧸ I.subgroupOf D) * Nat.card I := by
    rw [card_eq_card_quotient_mul_card_subgroup (I.subgroupOf D),
      Nat.card_congr (subgroupOfEquivOfLe hID).toEquiv]
  have hcB : Nat.card B = Nat.card (↥B ⧸ I.subgroupOf B) * Nat.card I := by
    rw [card_eq_card_quotient_mul_card_subgroup (I.subgroupOf B),
      Nat.card_congr (subgroupOfEquivOfLe hIB).toEquiv]
  rw [hcD, hcB]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective Φ hinj)

theorem mem_tim77M_iff {Q : Subgroup H} {h m : H} :
    m ∈ tim77M Q h ↔ ∃ b ∈ tim77B Q h, ∃ d ∈ tim77D Q h, b * d = m := by
  have hcoe := coe_mul_of_right_le_normalizer_left (tim77B Q h) (tim77D Q h)
    (tim77D_le_normalizer_tim77B Q h)
  rw [← SetLike.mem_coe, hcoe, Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem tim77M_le_tim77L (Q : Subgroup H) (h : H) : tim77M Q h ≤ tim77L Q h :=
  sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

theorem Tim77Hyp.isElemAbelian_rightConjugate {S Q : Subgroup H} (hQ : Tim77Hyp S Q) (a : H) :
    IsElemAbelian 2 (rightConjugate Q a) :=
  ⟨⟨⟨fun x y => Subtype.ext (hQ.comm_of_mem_rightConjugate a x.2 y.2)⟩⟩,
    fun x hx => by rw [sq]; exact hQ.mul_self_of_mem_rightConjugate a hx⟩

end Basic

namespace Tim77LexMax

variable [Finite H] {S Q : Subgroup H} {h : H}

theorem commutator_mem_B (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) {q d : H} (hq : q ∈ Q)
    (hd : d ∈ tim77D Q h) : q * d * q⁻¹ * d⁻¹ ∈ tim77B Q h := by
  by_cases hdI : d ∈ tim77I Q h
  · have hqd : q * d = d * q :=
      congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨q, hq⟩ ⟨d, hdI.1⟩)
    rw [hqd, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · refine Tim77LexMax.mem_B_of_mem_D hQ hL hd hdI ?_ ?_
    · have : d * q⁻¹ * d⁻¹ ∈ Q := (mem_normalizer_iff.mp hd.2 _).mp (inv_mem hq)
      simpa [mul_assoc] using mul_mem hq this
    · rw [commutator_commute_of_mem hQ.elem hq hd.2 (hQ.mul_self_of_mem_rightConjugate h hd.1)]
      exact one_mem _

theorem commutator_mem_D (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) {r y : H}
    (hr : r ∈ rightConjugate Q h) (hy : y ∈ tim77B Q h) : r * y * r⁻¹ * y⁻¹ ∈ tim77D Q h := by
  by_cases hyI : y ∈ tim77I Q h
  · rw [hQ.comm_of_mem_rightConjugate h hr hyI.2, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · refine Tim77LexMax.mem_D_of_mem_B hQ hL hy hyI ?_ ?_
    · have : y * r⁻¹ * y⁻¹ ∈ rightConjugate Q h :=
        (mem_normalizer_iff.mp hy.2 _).mp (inv_mem hr)
      simpa [mul_assoc] using mul_mem hr this
    · have hyy : y * y = 1 := by
        have h1 := hQ.mul_self_of_mem_rightConjugate 1 (by rw [rightConjugate_one]; exact hy.1)
        exact h1
      rw [commutator_commute_of_mem (hQ.isElemAbelian_rightConjugate h) hr hy.2 hyy]
      exact one_mem _

theorem normal (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) :
    tim77L Q h ≤ normalizer (tim77M Q h : Set H) := by
  have hBM : tim77B Q h ≤ tim77M Q h := le_sup_left
  have hDM : tim77D Q h ≤ tim77M Q h := le_sup_right
  refine sup_le (fun q hq => GoldschmidtFour.mem_normalizer_of_conj_mem fun m hm => ?_)
    (fun r hr => GoldschmidtFour.mem_normalizer_of_conj_mem fun m hm => ?_)
  · have hle : tim77M Q h ≤ (tim77M Q h).comap (MulAut.conj q).toMonoidHom := by
      refine sup_le (fun b hb => ?_) (fun d hd => ?_)
      · have hqb : q * b = b * q := congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨q, hq⟩ ⟨b, hb.1⟩)
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hqb, mul_inv_cancel_right]
        exact hBM hb
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          show q * d * q⁻¹ = (q * d * q⁻¹ * d⁻¹) * d by group]
        exact mul_mem (hBM (commutator_mem_B hQ hL hq hd)) (hDM hd)
    simpa using hle hm
  · have hle : tim77M Q h ≤ (tim77M Q h).comap (MulAut.conj r).toMonoidHom := by
      refine sup_le (fun b hb => ?_) (fun d hd => ?_)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          show r * b * r⁻¹ = (r * b * r⁻¹ * b⁻¹) * b by group]
        exact mul_mem (hDM (commutator_mem_D hQ hL hr hb)) (hBM hb)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          hQ.comm_of_mem_rightConjugate h hr hd.1, mul_inv_cancel_right]
        exact hDM hd
    simpa using hle hm

theorem fix (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) {x : H} (hx : x ∈ Q)
    (hxB : x ∉ tim77B Q h) {m : H} (hm : m ∈ tim77M Q h)
    (hxm : x * m * x⁻¹ * m⁻¹ ∈ tim77I Q h) : m ∈ tim77B Q h := by
  obtain ⟨b, hb, d, hd, rfl⟩ := mem_tim77M_iff.mp hm
  have hxb : x * b = b * x := congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨x, hx⟩ ⟨b, hb.1⟩)
  have hcb : b * (x * d * x⁻¹ * d⁻¹) = (x * d * x⁻¹ * d⁻¹) * b :=
    congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨b, hb.1⟩ ⟨_, (commutator_mem_B hQ hL hx hd).1⟩)
  have e : x * (b * d) * x⁻¹ * (b * d)⁻¹ = x * d * x⁻¹ * d⁻¹ := by
    calc x * (b * d) * x⁻¹ * (b * d)⁻¹ = (x * b) * d * x⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = b * (x * d * x⁻¹ * d⁻¹) * b⁻¹ := by rw [hxb]; group
      _ = x * d * x⁻¹ * d⁻¹ := by rw [hcb, mul_inv_cancel_right]
  rw [e] at hxm
  by_cases hdI : d ∈ tim77I Q h
  · exact mul_mem hb (tim77I_le_B Q h hdI)
  · exact absurd (Tim77LexMax.mem_B_of_mem_D hQ hL hd hdI hx hxm) hxB

theorem lt_B (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) : tim77B Q h < Q := by
  refine lt_of_le_of_ne (inf_le_left : tim77B Q h ≤ Q) fun hBQ => ?_
  have hQN : rightConjugate Q 1 ≤ normalizer (rightConjugate Q h : Set H) := by
    rw [rightConjugate_one]
    exact fun q hq => (hBQ.ge hq).2
  have hRQ := hQ.eq_of_le_normalizer hQN
  rw [rightConjugate_one] at hRQ
  refine (tim77I_lt_D_iff Q h).1 hL.1 fun d hd => ?_
  rw [hRQ]
  exact hd.1

theorem lt_D_R (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) : tim77D Q h < rightConjugate Q h := by
  refine lt_of_le_of_ne (inf_le_left : tim77D Q h ≤ rightConjugate Q h) fun hDR => ?_
  have hRN : rightConjugate Q h ≤ normalizer (rightConjugate Q 1 : Set H) := by
    rw [rightConjugate_one, ← hDR]
    exact inf_le_right
  have hRQ := hQ.eq_of_le_normalizer hRN
  rw [rightConjugate_one] at hRQ
  refine (tim77I_lt_D_iff Q h).1 hL.1 fun d hd => ?_
  rw [← hRQ]
  exact hd.1

omit [Finite H] in
theorem le_center (hQ : Tim77Hyp S Q) : tim77I Q h ≤ centralizer (tim77L Q h : Set H) := by
  rw [le_centralizer_iff]
  refine sup_le (fun q hq => mem_centralizer_iff.mpr fun i hi =>
    congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨i, hi.1⟩ ⟨q, hq⟩)) (fun r hr =>
    mem_centralizer_iff.mpr fun i hi => hQ.comm_of_mem_rightConjugate h hi.2 hr)

omit [Finite H] in
theorem elem (hQ : Tim77Hyp S Q) {x y : H} (hx : x ∈ tim77M Q h)
    (hy : y ∈ tim77M Q h) : x * y * x⁻¹ * y⁻¹ ∈ tim77I Q h ∧ x * x ∈ tim77I Q h := by
  have hsq : ∀ m ∈ tim77M Q h, m * m ∈ tim77I Q h := by
    intro m hm
    obtain ⟨b, hb, d, hd, rfl⟩ := mem_tim77M_iff.mp hm
    have hbb : b * b = 1 := by
      have h1 := hQ.mul_self_of_mem_rightConjugate 1 (by rw [rightConjugate_one]; exact hb.1)
      exact h1
    have hdd : d * d = 1 := hQ.mul_self_of_mem_rightConjugate h hd.1
    have e : (b * d) * (b * d) = (b * d * b⁻¹ * d⁻¹) * (d * (b * b) * d) := by group
    rw [e, hbb, mul_one, hdd, mul_one]
    exact commutator_mem_tim77I hb hd
  have hyL : y ∈ tim77L Q h := tim77M_le_tim77L Q h hy
  refine ⟨?_, hsq x hx⟩
  have e : x * y * x⁻¹ * y⁻¹ = ((x * y) * (x * y)) * (y⁻¹ * (x * x)⁻¹ * y) * (y * y)⁻¹ := by
    group
  rw [e]
  have hc : y⁻¹ * (x * x)⁻¹ * y = (x * x)⁻¹ := by
    have h1 := mem_centralizer_iff.mp (le_center hQ (inv_mem (hsq x hx))) y hyL
    rw [mul_assoc, ← h1, inv_mul_cancel_left]
  rw [hc]
  exact mul_mem (mul_mem (hsq _ (mul_mem hx hy)) (inv_mem (hsq x hx))) (inv_mem (hsq y hy))

theorem card_eq (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) :
    Nat.card (tim77B Q h) = Nat.card (tim77D Q h) := by
  obtain ⟨x, hx, hxB⟩ := IsConcreteLE.exists_of_lt (lt_B hQ hL)
  obtain ⟨r, hr, hrD⟩ := IsConcreteLE.exists_of_lt (lt_D_R hQ hL)
  refine le_antisymm ?_ ?_
  · refine card_le_of_inj_mod (tim77I_le_D Q h) (tim77I_le_B Q h) (fun b => r * b * r⁻¹ * b⁻¹)
      (fun b hb => commutator_mem_D hQ hL hr hb) (fun b hb c hc => ?_) (fun i hi => ?_)
      (fun b hb hbI => ?_)
    · have e : (r * b * r⁻¹ * b⁻¹)⁻¹ * (r * (b * c) * r⁻¹ * (b * c)⁻¹) *
          (r * c * r⁻¹ * c⁻¹)⁻¹ = b * (r * c * r⁻¹ * c⁻¹) * b⁻¹ * (r * c * r⁻¹ * c⁻¹)⁻¹ := by
        group
      rw [e]
      exact commutator_mem_tim77I hb (commutator_mem_D hQ hL hr hc)
    · show r * i * r⁻¹ * i⁻¹ ∈ tim77I Q h
      rw [hQ.comm_of_mem_rightConjugate h hr hi.2, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · by_contra hbI'
      exact hrD (Tim77LexMax.mem_D_of_mem_B hQ hL hb hbI' hr hbI)
  · refine card_le_of_inj_mod (tim77I_le_B Q h) (tim77I_le_D Q h) (fun d => x * d * x⁻¹ * d⁻¹)
      (fun d hd => commutator_mem_B hQ hL hx hd) (fun d hd e he => ?_) (fun i hi => ?_)
      (fun d hd hdI => ?_)
    · have e' : (x * d * x⁻¹ * d⁻¹)⁻¹ * (x * (d * e) * x⁻¹ * (d * e)⁻¹) *
          (x * e * x⁻¹ * e⁻¹)⁻¹ = ((x * e * x⁻¹ * e⁻¹) * d * (x * e * x⁻¹ * e⁻¹)⁻¹ * d⁻¹)⁻¹ := by
        group
      rw [e']
      exact inv_mem (commutator_mem_tim77I (commutator_mem_B hQ hL hx he) hd)
    · show x * i * x⁻¹ * i⁻¹ ∈ tim77I Q h
      have hxi : x * i = i * x := congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨x, hx⟩ ⟨i, hi.1⟩)
      rw [hxi, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · by_contra hdI'
      exact hxB (Tim77LexMax.mem_B_of_mem_D hQ hL hd hdI' hx hdI)

theorem cases (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) :
    2 * Nat.card (tim77B Q h) = Nat.card Q ∨
      4 * Nat.card (tim77I Q h) ≤ Nat.card (tim77D Q h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h4 : 4 * Nat.card (tim77I Q h) ≤ Nat.card (tim77D Q h)
  · exact Or.inr h4
  left
  have hkD := relIndex_mul_card (tim77I Q h) (tim77D Q h)
  rw [inf_eq_left.mpr (tim77I_le_D Q h)] at hkD
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ((hQ.isPGroup_rightConjugate h).to_le
    (inf_le_left : tim77D Q h ≤ rightConjugate Q h))
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show (tim77I Q h).relIndex (tim77D Q h) ∣ 2 ^ n from hn ▸ Dvd.intro _ hkD)
  have hlt := card_lt_of_lt hL.1
  have hI0 : 0 < Nat.card (tim77I Q h) := Nat.card_pos
  have hk2 : (tim77I Q h).relIndex (tim77D Q h) = 2 := by
    rw [hm] at hkD ⊢
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · rw [pow_zero, one_mul] at hkD
        omega
      · rfl
    · have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      nlinarith
  have hkB := relIndex_mul_card (tim77I Q h) (tim77B Q h)
  rw [inf_eq_left.mpr (tim77I_le_B Q h), card_eq hQ hL, ← hkD, hk2] at hkB
  have hkB2 : (tim77I Q h).relIndex (tim77B Q h) = 2 := by
    have := Nat.eq_of_mul_eq_mul_right hI0 hkB
    exact this
  have hidx : ((tim77I Q h).subgroupOf (tim77B Q h)).index = 2 := hkB2
  obtain ⟨x, hx, hxB⟩ := IsConcreteLE.exists_of_lt (lt_B hQ hL)
  obtain ⟨d, hd, hdI⟩ := IsConcreteLE.exists_of_lt hL.1
  have hnot : ∀ y ∈ Q, y ∉ tim77B Q h → y * d * y⁻¹ * d⁻¹ ∉ tim77I Q h := fun y hy hyB hyd =>
    hyB (Tim77LexMax.mem_B_of_mem_D hQ hL hd hdI hy hyd)
  have hxy : ∀ y ∈ Q, y ∉ tim77B Q h → x * y ∈ tim77B Q h := by
    intro y hy hyB
    have hu := commutator_mem_B hQ hL hx hd
    have hv := commutator_mem_B hQ hL hy hd
    have huv : (⟨_, hu⟩ : ↥(tim77B Q h)) * ⟨_, hv⟩ ∈ (tim77I Q h).subgroupOf (tim77B Q h) := by
      rw [mul_mem_iff_of_index_two hidx, mem_subgroupOf, mem_subgroupOf]
      exact iff_of_false (hnot x hx hxB) (hnot y hy hyB)
    rw [mem_subgroupOf] at huv
    have hvx : x * (y * d * y⁻¹ * d⁻¹) = (y * d * y⁻¹ * d⁻¹) * x :=
      congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨x, hx⟩ ⟨_, hv.1⟩)
    have huv' : (y * d * y⁻¹ * d⁻¹) * (x * d * x⁻¹ * d⁻¹) =
        (x * d * x⁻¹ * d⁻¹) * (y * d * y⁻¹ * d⁻¹) :=
      congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨_, hv.1⟩ ⟨_, hu.1⟩)
    refine Tim77LexMax.mem_B_of_mem_D hQ hL hd hdI (mul_mem hx hy) ?_
    have e : x * y * d * (x * y)⁻¹ * d⁻¹ =
        (x * (y * d * y⁻¹ * d⁻¹) * x⁻¹) * (x * d * x⁻¹ * d⁻¹) := by group
    rw [e, hvx, mul_inv_cancel_right, huv']
    simpa using huv
  have hkQ : (tim77B Q h).relIndex Q = 2 := by
    refine relIndex_eq_two_iff.mpr ⟨x, hx, fun b hb => ?_⟩
    by_cases hbB : b ∈ tim77B Q h
    · have hbx : b * x ∉ tim77B Q h := fun h' => hxB (by
        have := mul_mem (inv_mem hbB) h'
        rwa [inv_mul_cancel_left] at this)
      simp [hbx, hbB]
    · have hbx : b * x ∈ tim77B Q h := by
        have hbx' : b * x = x * b := congrArg Subtype.val (hQ.elem.1.is_comm.comm ⟨b, hb⟩ ⟨x, hx⟩)
        rw [hbx']
        exact hxy b hb hbB
      simp [hbx, hbB]
  have hQc := relIndex_mul_card (tim77B Q h) Q
  rw [inf_eq_left.mpr (inf_le_left : tim77B Q h ≤ Q), hkQ] at hQc
  exact hQc

theorem tim77Facts (hQ : Tim77Hyp S Q) (hL : Tim77LexMax Q h) : Tim77Facts Q h where
  normal := normal hQ hL
  elem := fun _ hx _ hy => elem hQ hx hy
  lt_D := hL.1
  lt_B := lt_B hQ hL
  le_center := le_center hQ
  fix := fun _ hx hxB _ hm hxm => fix hQ hL hx hxB hm hxm
  fixD := fun _ hd hdI _ hx hxd => Tim77LexMax.mem_B_of_mem_D hQ hL hd hdI hx hxd
  card_eq := card_eq hQ hL
  cases := cases hQ hL

end Tim77LexMax

theorem Tim77Hyp.exists_tim77Facts [Finite H] {S Q : Subgroup H} (hQ : Tim77Hyp S Q)
    (hns : ∃ x ∈ Q, ∃ h : H, h⁻¹ * x * h ∈ S ∧ h⁻¹ * x * h ∉ Q) : ∃ h : H, Tim77Facts Q h := by
  obtain ⟨g, hg⟩ := hQ.exists_not_le hns
  obtain ⟨h, hL⟩ := exists_tim77LexMax ⟨g, (tim77I_lt_D_iff Q g).2 hg⟩
  exact ⟨h, Tim77LexMax.tim77Facts hQ hL⟩

theorem tim77Lemma24 : Tim77Lemma24 :=
  fun _ _ _ _ _ hS hQS hQ hw hns => (Tim77Hyp.mk hS hQS hQ hw).exists_tim77Facts hns

end CFSG.ComponentClassification.AS81
