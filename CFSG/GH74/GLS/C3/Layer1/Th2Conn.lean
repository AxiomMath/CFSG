module

public import CFSG.GH74.GLS.C3.Layer1.Th2Shape
public import CFSG.GH74.GLS.C3.Layer1.Th2L74
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.StronglyEmbedded.SteinbergBURankTwoOddCore

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

structure CommDisj (P Q : Subgroup G) : Prop where
  comm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p
  inf : P ⊓ Q = ⊥

namespace CommDisj

variable {P Q : Subgroup G} (h : CommDisj P Q)

include h in
theorem eq_one_of_mem {x : G} (hxP : x ∈ P) (hxQ : x ∈ Q) : x = 1 := by
  have : x ∈ P ⊓ Q := ⟨hxP, hxQ⟩
  rw [h.inf, Subgroup.mem_bot] at this
  exact this

include h in
theorem mul_cancel {p p' q q' : G} (hp : p ∈ P) (hp' : p' ∈ P) (hq : q ∈ Q) (hq' : q' ∈ Q)
    (e : p * q = p' * q') : p = p' ∧ q = q' := by
  have h1 : p'⁻¹ * p = q' * q⁻¹ := by
    calc p'⁻¹ * p = p'⁻¹ * (p * q) * q⁻¹ := by group
      _ = p'⁻¹ * (p' * q') * q⁻¹ := by rw [e]
      _ = q' * q⁻¹ := by group
  have h2 : p'⁻¹ * p = 1 :=
    h.eq_one_of_mem (P.mul_mem (P.inv_mem hp') hp) (h1 ▸ Q.mul_mem hq' (Q.inv_mem hq))
  have hpp : p = p' := by
    calc p = p' * (p'⁻¹ * p) := by group
      _ = p' := by rw [h2, mul_one]
  subst hpp
  exact ⟨rfl, mul_left_cancel e⟩

include h in
theorem symm : CommDisj Q P :=
  ⟨fun q hq p hp => (h.comm p hp q hq).symm, by rw [inf_comm]; exact h.inf⟩

@[expose] def projP (A : Subgroup G) : Subgroup G where
  carrier := {p | p ∈ P ∧ ∃ q ∈ Q, p * q ∈ A}
  one_mem' := ⟨P.one_mem, 1, Q.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haP, qa, hqa, ha⟩ ⟨hbP, qb, hqb, hb⟩
    refine ⟨P.mul_mem haP hbP, qa * qb, Q.mul_mem hqa hqb, ?_⟩
    have : a * b * (qa * qb) = (a * qa) * (b * qb) := by
      calc a * b * (qa * qb) = a * (b * qa) * qb := by group
        _ = a * (qa * b) * qb := by rw [h.comm b hbP qa hqa]
        _ = (a * qa) * (b * qb) := by group
    rw [this]; exact A.mul_mem ha hb
  inv_mem' := by
    rintro a ⟨haP, qa, hqa, ha⟩
    refine ⟨P.inv_mem haP, qa⁻¹, Q.inv_mem hqa, ?_⟩
    have : a⁻¹ * qa⁻¹ = (a * qa)⁻¹ := by
      calc a⁻¹ * qa⁻¹ = (qa * a)⁻¹ := by group
        _ = (a * qa)⁻¹ := by rw [h.comm a haP qa hqa]
    rw [this]; exact A.inv_mem ha

@[expose] def projQ (A : Subgroup G) : Subgroup G where
  carrier := {q | q ∈ Q ∧ ∃ p ∈ P, p * q ∈ A}
  one_mem' := ⟨Q.one_mem, 1, P.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haQ, pa, hpa, ha⟩ ⟨hbQ, pb, hpb, hb⟩
    refine ⟨Q.mul_mem haQ hbQ, pa * pb, P.mul_mem hpa hpb, ?_⟩
    have : pa * pb * (a * b) = (pa * a) * (pb * b) := by
      calc pa * pb * (a * b) = pa * (pb * a) * b := by group
        _ = pa * (a * pb) * b := by rw [← h.comm pb hpb a haQ]
        _ = (pa * a) * (pb * b) := by group
    rw [this]; exact A.mul_mem ha hb
  inv_mem' := by
    rintro a ⟨haQ, pa, hpa, ha⟩
    refine ⟨Q.inv_mem haQ, pa⁻¹, P.inv_mem hpa, ?_⟩
    have : pa⁻¹ * a⁻¹ = (pa * a)⁻¹ := by
      rw [mul_inv_rev]; exact h.comm _ (P.inv_mem hpa) _ (Q.inv_mem haQ)
    rw [this]; exact A.inv_mem ha

theorem mem_projP_iff {A : Subgroup G} {p : G} : p ∈ h.projP A ↔ p ∈ P ∧ ∃ q ∈ Q, p * q ∈ A :=
  Iff.rfl

theorem mem_projQ_iff {A : Subgroup G} {q : G} : q ∈ h.projQ A ↔ q ∈ Q ∧ ∃ p ∈ P, p * q ∈ A :=
  Iff.rfl

theorem projP_le_left (A : Subgroup G) : h.projP A ≤ P := fun _ hx => hx.1

theorem projQ_le_right (A : Subgroup G) : h.projQ A ≤ Q := fun _ hx => hx.1

theorem mem_projP {A : Subgroup G} {p q : G} (hp : p ∈ P) (hq : q ∈ Q) (hA : p * q ∈ A) :
    p ∈ h.projP A := ⟨hp, q, hq, hA⟩

theorem mem_projQ {A : Subgroup G} {p q : G} (hp : p ∈ P) (hq : q ∈ Q) (hA : p * q ∈ A) :
    q ∈ h.projQ A := ⟨hq, p, hp, hA⟩

theorem le_projP_sup_projQ {A : Subgroup G} (hA : A ≤ P ⊔ Q) : A ≤ h.projP A ⊔ h.projQ A := by
  intro a ha
  obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute h.comm (hA ha)
  exact Subgroup.mul_mem_sup (h.mem_projP hp hq ha) (h.mem_projQ hp hq ha)

theorem isElementaryAbelian_projP {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) :
    CFSG.IsElementaryAbelian 2 ↥(h.projP A) := by
  obtain ⟨hAc, hAs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hA
  refine C3.Layer1.Back.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
  · obtain ⟨huP, qu, hqu, hu⟩ := hu
    obtain ⟨hvP, qv, hqv, hv⟩ := hv
    have h1 := hAc _ hu _ hv
    have e1 : u * qu * (v * qv) = (u * v) * (qu * qv) := by
      calc u * qu * (v * qv) = u * (qu * v) * qv := by group
        _ = u * (v * qu) * qv := by rw [← h.comm v hvP qu hqu]
        _ = (u * v) * (qu * qv) := by group
    have e2 : v * qv * (u * qu) = (v * u) * (qv * qu) := by
      calc v * qv * (u * qu) = v * (qv * u) * qu := by group
        _ = v * (u * qv) * qu := by rw [← h.comm u huP qv hqv]
        _ = (v * u) * (qv * qu) := by group
    rw [e1, e2] at h1
    exact (h.mul_cancel (P.mul_mem huP hvP) (P.mul_mem hvP huP) (Q.mul_mem hqu hqv)
      (Q.mul_mem hqv hqu) h1).1
  · obtain ⟨huP, qu, hqu, hu⟩ := hu
    have h1 := hAs _ hu
    have e1 : u * qu * (u * qu) = (u * u) * (qu * qu) := by
      calc u * qu * (u * qu) = u * (qu * u) * qu := by group
        _ = u * (u * qu) * qu := by rw [← h.comm u huP qu hqu]
        _ = (u * u) * (qu * qu) := by group
    rw [e1] at h1
    have := (h.mul_cancel (P.mul_mem huP huP) P.one_mem (Q.mul_mem hqu hqu) Q.one_mem
      (by rw [h1, mul_one])).1
    exact this

theorem isElementaryAbelian_projQ {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) :
    CFSG.IsElementaryAbelian 2 ↥(h.projQ A) := by
  obtain ⟨hAc, hAs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hA
  refine C3.Layer1.Back.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
  · obtain ⟨huQ, pu, hpu, hu⟩ := hu
    obtain ⟨hvQ, pv, hpv, hv⟩ := hv
    have h1 := hAc _ hu _ hv
    have e1 : pu * u * (pv * v) = (pu * pv) * (u * v) := by
      calc pu * u * (pv * v) = pu * (u * pv) * v := by group
        _ = pu * (pv * u) * v := by rw [h.comm pv hpv u huQ]
        _ = (pu * pv) * (u * v) := by group
    have e2 : pv * v * (pu * u) = (pv * pu) * (v * u) := by
      calc pv * v * (pu * u) = pv * (v * pu) * u := by group
        _ = pv * (pu * v) * u := by rw [h.comm pu hpu v hvQ]
        _ = (pv * pu) * (v * u) := by group
    rw [e1, e2] at h1
    exact (h.mul_cancel (P.mul_mem hpu hpv) (P.mul_mem hpv hpu) (Q.mul_mem huQ hvQ)
      (Q.mul_mem hvQ huQ) h1).2
  · obtain ⟨huQ, pu, hpu, hu⟩ := hu
    have h1 := hAs _ hu
    have e1 : pu * u * (pu * u) = (pu * pu) * (u * u) := by
      calc pu * u * (pu * u) = pu * (u * pu) * u := by group
        _ = pu * (pu * u) * u := by rw [h.comm pu hpu u huQ]
        _ = (pu * pu) * (u * u) := by group
    rw [e1] at h1
    exact (h.mul_cancel (P.mul_mem hpu hpu) P.one_mem (Q.mul_mem huQ huQ) Q.one_mem
      (by rw [h1, mul_one])).2

include h in
theorem isElementaryAbelian_sup' {U E : Subgroup G} (hU : CFSG.IsElementaryAbelian 2 ↥U)
    (hE : CFSG.IsElementaryAbelian 2 ↥E) (hUP : U ≤ P) (hEQ : E ≤ Q) :
    CFSG.IsElementaryAbelian 2 ↥(U ⊔ E) :=
  isElementaryAbelian_sup hU hE fun k hk l hl => h.comm k (hUP hk) l (hEQ hl)

include h in
theorem card_sup [Finite G] {U E : Subgroup G} (hU : U ≤ P) (hE : E ≤ Q) :
    Nat.card ↥(U ⊔ E) = Nat.card ↥U * Nat.card ↥E := by
  have comm : ∀ (m : U) (n : E), Commute (U.subtype m) (E.subtype n) :=
    fun m n => h.comm m (hU m.2) n (hE n.2)
  have hinj : Function.Injective (MonoidHom.noncommCoprod U.subtype E.subtype comm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨U.subtype_injective, E.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.disjoint_def]
    intro x hxU hxE
    exact h.eq_one_of_mem (hU hxU) (hE hxE)
  have hrange := MonoidHom.noncommCoprod_range U.subtype E.subtype comm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

include h in
theorem pRank_sup [Finite G] {U E : Subgroup G} (hUel : CFSG.IsElementaryAbelian 2 ↥U)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hU : U ≤ P) (hE : E ≤ Q) :
    pRank 2 ↥(U ⊔ E) = pRank 2 ↥U + pRank 2 ↥E := by
  have hW := h.isElementaryAbelian_sup' hUel hEel hU hE
  have hc := h.card_sup hU hE
  rw [C3.Layer1.Back.card_eq_two_pow_pRank hW, C3.Layer1.Back.card_eq_two_pow_pRank hUel,
    C3.Layer1.Back.card_eq_two_pow_pRank hEel, ← pow_add] at hc
  exact Nat.pow_right_injective le_rfl hc

include h in
theorem isS_sup {U E : Subgroup G} (hU : IsS P U) (hE : IsS Q E) : IsS (P ⊔ Q) (U ⊔ E) := by
  obtain ⟨hUP, hUel, hUeq⟩ := hU
  obtain ⟨hEQ, hEel, hEeq⟩ := hE
  have hel := h.isElementaryAbelian_sup' hUel hEel hUP hEQ
  have hle : U ⊔ E ≤ P ⊔ Q := sup_le_sup hUP hEQ
  refine ⟨hle, hel, le_antisymm ?_ ?_⟩
  · refine le_omega1_of_isElementaryAbelian hel (le_inf hle ?_)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (C3.Layer1.Back.forall_of_isElementaryAbelian hel).1 c hc b hb
  · refine (Subgroup.closure_le _).2 ?_
    rintro u ⟨⟨huPQ, huC⟩, hu2⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute h.comm huPQ
    have e : p * q * (p * q) = (p * p) * (q * q) := by
      calc p * q * (p * q) = p * (q * p) * q := by group
        _ = p * (p * q) * q := by rw [← h.comm p hp q hq]
        _ = (p * p) * (q * q) := by group
    have hsq := h.mul_cancel (P.mul_mem hp hp) P.one_mem (Q.mul_mem hq hq) Q.one_mem
      (by rw [← e, hu2, mul_one])
    have hpU : p ∈ P ⊓ centralizer (U : Set G) := by
      refine ⟨hp, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro u' hu'
      have h1 : u' * (p * q) = p * q * u' := huC u' (Subgroup.mem_sup_left hu')
      have h2 : u' * p * q = p * u' * q := by
        calc u' * p * q = u' * (p * q) := by group
          _ = p * q * u' := h1
          _ = p * (q * u') := by group
          _ = p * (u' * q) := by rw [← h.comm u' (hUP hu') q hq]
          _ = p * u' * q := by group
      exact mul_right_cancel h2
    have hqE : q ∈ Q ⊓ centralizer (E : Set G) := by
      refine ⟨hq, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro e' he'
      have h1 : e' * (p * q) = p * q * e' := huC e' (Subgroup.mem_sup_right he')
      have h2 : p * e' * q = p * q * e' := by
        calc p * e' * q = p * (e' * q) := by group
          _ = (p * e') * q := by group
          _ = (e' * p) * q := by rw [h.comm p hp e' (hEQ he')]
          _ = e' * (p * q) := by group
          _ = p * q * e' := h1
      have h3 : e' * q = q * e' := by
        have := mul_left_cancel (a := p) (by simpa [mul_assoc] using h2)
        exact this
      exact h3
    have hpU' : p ∈ U := by
      rw [hUeq]; exact Subgroup.subset_closure ⟨hpU, hsq.1⟩
    have hqE' : q ∈ E := by
      rw [hEeq]; exact Subgroup.subset_closure ⟨hqE, hsq.2⟩
    exact Subgroup.mul_mem_sup hpU' hqE'

theorem isS_proj {B : Subgroup G} (hB : IsS (P ⊔ Q) B) :
    B = h.projP B ⊔ h.projQ B ∧ IsS P (h.projP B) ∧ IsS Q (h.projQ B) := by
  obtain ⟨hBle, hBel, hBeq⟩ := hB
  have hUel := h.isElementaryAbelian_projP hBel
  have hEel := h.isElementaryAbelian_projQ hBel
  have hsup := h.isElementaryAbelian_sup' hUel hEel (h.projP_le_left B) (h.projQ_le_right B)
  have hB1 : B ≤ h.projP B ⊔ h.projQ B := h.le_projP_sup_projQ hBle
  have hBeq' : B = h.projP B ⊔ h.projQ B := by
    refine le_antisymm hB1 ?_
    have h2 : h.projP B ⊔ h.projQ B ≤ omega1 ((P ⊔ Q) ⊓ centralizer (B : Set G)) := by
      refine le_omega1_of_isElementaryAbelian hsup
        (le_inf (sup_le_sup (h.projP_le_left B) (h.projQ_le_right B)) ?_)
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (C3.Layer1.Back.forall_of_isElementaryAbelian hsup).1 c (hB1 hc) b hb
    exact h2.trans hBeq.ge
  refine ⟨hBeq', ⟨h.projP_le_left B, hUel, le_antisymm ?_ ?_⟩, ⟨h.projQ_le_right B, hEel, le_antisymm ?_ ?_⟩⟩
  · refine le_omega1_of_isElementaryAbelian hUel (le_inf (h.projP_le_left B) ?_)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (C3.Layer1.Back.forall_of_isElementaryAbelian hUel).1 c hc b hb
  · refine (Subgroup.closure_le _).2 ?_
    rintro u ⟨⟨huP, huC⟩, hu2⟩
    have huB : u ∈ omega1 ((P ⊔ Q) ⊓ centralizer (B : Set G)) := by
      refine Subgroup.subset_closure ⟨⟨Subgroup.mem_sup_left huP, Subgroup.mem_centralizer_iff.2 ?_⟩, hu2⟩
      intro b hb
      have hb' : b ∈ h.projP B ⊔ h.projQ B := hBeq' ▸ hb
      obtain ⟨p', hp', q', hq', rfl⟩ := exists_mul_of_mem_sup_of_commute
        (fun k hk l hl => h.comm k ((h.projP_le_left B) hk) l ((h.projQ_le_right B) hl)) hb'
      have hc1 : p' * u = u * p' := (Subgroup.mem_centralizer_iff.1 huC) p' hp'
      calc p' * q' * u = p' * (q' * u) := by group
        _ = p' * (u * q') := by rw [h.comm u huP q' ((h.projQ_le_right B) hq')]
        _ = (p' * u) * q' := by group
        _ = (u * p') * q' := by rw [hc1]
        _ = u * (p' * q') := by group
    rw [← hBeq] at huB
    exact h.mem_projP huP Q.one_mem (by simpa using huB)
  · refine le_omega1_of_isElementaryAbelian hEel (le_inf (h.projQ_le_right B) ?_)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (C3.Layer1.Back.forall_of_isElementaryAbelian hEel).1 c hc b hb
  · refine (Subgroup.closure_le _).2 ?_
    rintro u ⟨⟨huQ, huC⟩, hu2⟩
    have huB : u ∈ omega1 ((P ⊔ Q) ⊓ centralizer (B : Set G)) := by
      refine Subgroup.subset_closure ⟨⟨Subgroup.mem_sup_right huQ, Subgroup.mem_centralizer_iff.2 ?_⟩, hu2⟩
      intro b hb
      have hb' : b ∈ h.projP B ⊔ h.projQ B := hBeq' ▸ hb
      obtain ⟨p', hp', q', hq', rfl⟩ := exists_mul_of_mem_sup_of_commute
        (fun k hk l hl => h.comm k ((h.projP_le_left B) hk) l ((h.projQ_le_right B) hl)) hb'
      have hc1 : q' * u = u * q' := (Subgroup.mem_centralizer_iff.1 huC) q' hq'
      calc p' * q' * u = p' * (q' * u) := by group
        _ = p' * (u * q') := by rw [hc1]
        _ = (p' * u) * q' := by group
        _ = (u * p') * q' := by rw [← h.comm p' ((h.projP_le_left B) hp') u huQ]
        _ = u * (p' * q') := by group
    rw [← hBeq] at huB
    exact h.mem_projQ P.one_mem huQ (by simpa using huB)

end CommDisj

theorem RConnN.mono_r {r r' n : ℕ} {X A B : Subgroup G} (hrr : r ≤ r') (h : RConnN r' n X A B) :
    RConnN r n X A B := by
  have h' : Relation.ReflTransGen (ConnStep r' n X) A B := h
  clear h
  show Relation.ReflTransGen (ConnStep r n X) A B
  induction h' with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.tail ih ⟨isE_mono_rank hstep.1 hrr, hstep.2.1, hstep.2.2⟩


theorem connStep_mono [Finite G] {r n : ℕ} {X Y A B : Subgroup G} (hXY : X ≤ Y)
    (h : ConnStep r n X A B) : ConnStep r n Y A B := by
  obtain ⟨hE, hcomm, hcase⟩ := h
  refine ⟨⟨hE.1.trans hXY, hE.2.1, hE.2.2⟩, hcomm, ?_⟩
  rcases hcase with hEq | hr
  · exact Or.inl hEq
  · exact Or.inr (hr.trans (C3.Layer1.Back.pRank_mono'
      (le_inf (inf_le_left.trans hXY) inf_le_right)))

theorem RConnN.mono_container [Finite G] {r n : ℕ} {X Y A B : Subgroup G} (hXY : X ≤ Y)
    (h : RConnN r n X A B) : RConnN r n Y A B :=
  (Relation.ReflTransGen.mono (r := ConnStep r n X) (p := ConnStep r n Y)
    (fun _ _ hstep => connStep_mono hXY hstep)) A B h

theorem isS_of_isFourSub [Finite G] {P U : Subgroup G} (hP : RankTwoShape P) (hU : IsFourSub P U) :
    IsS P U := by
  obtain ⟨hUP, hUel, hUcard⟩ := hU
  refine ⟨hUP, hUel, le_antisymm ?_ ?_⟩
  · refine le_omega1_of_isElementaryAbelian hUel (le_inf hUP ?_)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (C3.Layer1.Back.forall_of_isElementaryAbelian hUel).1 c hc b hb
  · refine (Subgroup.closure_le _).2 ?_
    rintro u ⟨⟨huP, huC⟩, hu2⟩
    have huc : ∀ b ∈ U, b * u = u * b := fun b hb => Subgroup.mem_centralizer_iff.1 huC b hb
    have hW : CFSG.IsElementaryAbelian 2 ↥(U ⊔ zpowers u) := by
      refine isElementaryAbelian_sup hUel ?_ ?_
      · have hu2' : u ^ 2 = 1 := by rw [pow_two]; exact hu2
        exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hu2'
      · intro b hb z hz
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hz
        exact (Commute.zpow_right (huc b hb) m).eq
    have hWP : U ⊔ zpowers u ≤ P := sup_le hUP (zpowers_le.2 huP)
    have hcard := hP.1 _ hWP hW
    have heq : U = U ⊔ zpowers u :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hUcard]; exact hcard)
    have : u ∈ U ⊔ zpowers u := Subgroup.mem_sup_right (mem_zpowers u)
    rwa [← heq] at this

theorem pRank_of_isFourSub [Finite G] {P U : Subgroup G} (hU : IsFourSub P U) : pRank 2 ↥U = 2 := by
  have h := C3.Layer1.Back.card_eq_two_pow_pRank hU.2.1
  rw [hU.2.2] at h
  have : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥U := by simpa using h
  exact (Nat.pow_right_injective le_rfl this).symm

theorem mem_of_isS_of_central {Q E : Subgroup G} (hE : IsS Q E) {z : G} (hzQ : z ∈ Q) (hz2 : z * z = 1)
    (hzc : ∀ q ∈ Q, z * q = q * z) : z ∈ E := by
  obtain ⟨hEQ, -, hEeq⟩ := hE
  rw [hEeq]
  exact Subgroup.subset_closure ⟨⟨hzQ, Subgroup.mem_centralizer_iff.2 fun e he => (hzc e (hEQ he)).symm⟩, hz2⟩

theorem exists_central_involution [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) (hne : Q ≠ ⊥) :
    ∃ z ∈ Q, orderOf z = 2 ∧ ∀ q ∈ Q, z * q = q * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hnt : (⊤ : Subgroup ↥Q) ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro q hq
    have : (⟨q, hq⟩ : ↥Q) ∈ (⊤ : Subgroup ↥Q) := trivial
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hnt
  have hZp : IsPGroup 2 ↥((⊤ : Subgroup ↥Q) ⊓ Subgroup.center ↥Q) := hQ.to_subgroup _
  have hZ2 : 2 ∣ Nat.card ↥((⊤ : Subgroup ↥Q) ⊓ Subgroup.center ↥Q) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZp
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hZ
      rw [← Subgroup.card_eq_one]
      simpa using hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
  refine ⟨((z : ↥Q) : G), (z : ↥Q).2, ?_, fun t ht => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  · have hc := (Subgroup.mem_center_iff.1 z.2.2) ⟨t, ht⟩
    exact congrArg Subtype.val hc.symm

theorem mul_self_eq_one_of_orderOf_eq_two {z : G} (hz : orderOf z = 2) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [hz, pow_two] at this

theorem connStep_of_le_elem [Finite G] {r n : ℕ} {X W A' A'' : Subgroup G} (hW : IsE n X W)
    (h' : A' ≤ W) (h'' : A'' ≤ W) (hr : IsE r X A'') : ConnStep r n X A' A'' := by
  obtain ⟨hWX, hWel, hWn⟩ := hW
  obtain ⟨hWc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hWel
  refine ⟨hr, fun a ha b hb => hWc a (h' ha) b (h'' hb), Or.inr ?_⟩
  have hle : W ≤ X ⊓ centralizer ((A' ⊔ A'' : Subgroup G) : Set G) := by
    refine le_inf hWX ?_
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hWc g ((sup_le h' h'') hg) w hw
  exact hWn.trans (C3.Layer1.Back.pRank_mono' hle)

theorem exists_isS_two_le [Finite G] {Q W E₀ : Subgroup G} (hWQ : W ≤ Q)
    (hWel : CFSG.IsElementaryAbelian 2 ↥W) (hE₀ : IsS Q E₀) (hE₀rk : 2 ≤ pRank 2 ↥E₀) {z : G}
    (hzQ : z ∈ Q) (hz1 : z ≠ 1) (hz2 : z * z = 1) (hzc : ∀ q ∈ Q, z * q = q * z) :
    ∃ E : Subgroup G, W ≤ E ∧ IsS Q E ∧ 2 ≤ pRank 2 ↥E := by
  have hzu : CFSG.IsElementaryAbelian 2 ↥(zpowers z) := by
    have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
    exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hz2'
  have hW' : CFSG.IsElementaryAbelian 2 ↥(W ⊔ zpowers z) := by
    refine isElementaryAbelian_sup hWel hzu ?_
    intro w hw t ht
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ht
    exact (Commute.zpow_right (hzc w (hWQ hw)).symm m).eq
  obtain ⟨E₁, hWE₁, hE₁⟩ := exists_maximal_elemAbelian (X := Q) (sup_le hWQ (zpowers_le.2 hzQ)) hW'
  by_cases hrk : 2 ≤ pRank 2 ↥E₁
  · exact ⟨E₁, le_sup_left.trans hWE₁, hE₁, hrk⟩
  · refine ⟨E₀, ?_, hE₀, hE₀rk⟩
    have hzE₁ : z ∈ E₁ := mem_of_isS_of_central hE₁ hzQ hz2 hzc
    have hzE₀ : z ∈ E₀ := mem_of_isS_of_central hE₀ hzQ hz2 hzc
    have hcardE₁ : Nat.card ↥E₁ ≤ 2 := by
      rw [C3.Layer1.Back.card_eq_two_pow_pRank hE₁.2.1]
      calc 2 ^ pRank 2 ↥E₁ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    have hcardz : Nat.card ↥(zpowers z) = 2 := by
      rw [Nat.card_zpowers]
      have : orderOf z = 2 := by
        refine orderOf_eq_prime ?_ hz1
        rw [pow_two]; exact hz2
      exact this
    have hz_le : zpowers z ≤ E₁ := zpowers_le.2 hzE₁
    have hEq : zpowers z = E₁ :=
      Subgroup.eq_of_le_of_card_ge hz_le (by rw [hcardz]; exact hcardE₁)
    calc W ≤ W ⊔ zpowers z := le_sup_left
      _ ≤ E₁ := hWE₁
      _ = zpowers z := hEq.symm
      _ ≤ E₀ := zpowers_le.2 hzE₀

section Conn4

variable [Finite G]

theorem exists_isFourSub_of_two_le_pRank {H : Subgroup G}
    (hrk : 2 ≤ CFSG.pRank 2 ↥H) :
    ∃ F : Subgroup G, F ≤ H ∧ IsFourSub H F := by
  obtain ⟨A, hAel, hAcard⟩ :=
    CFSG.StronglyEmbedded.SteinbergBU.exists_four_group_of_two_le_pRank (G := ↥H) hrk
  refine ⟨A.map H.subtype, Subgroup.map_subtype_le A, ?_⟩
  refine ⟨Subgroup.map_subtype_le A, ?_, ?_⟩
  · exact CFSG.IsElementaryAbelian.map (p := 2) (A := A) H.subtype
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hAcard]
    norm_num

theorem eq_of_isS_of_le_elem {Q E E' : Subgroup G} (hE : IsS Q E) (hE'Q : E' ≤ Q)
    (hE'el : CFSG.IsElementaryAbelian 2 ↥E') (hEE' : E ≤ E') : E' = E := by
  obtain ⟨-, -, hEeq⟩ := hE
  have hE'cent : E' ≤ centralizer (E : Set G) := by
    intro e' he'
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((C3.Layer1.Back.forall_of_isElementaryAbelian hE'el).1 e' he' e (hEE' he)).symm
  have hE'le : E' ≤ omega1 (Q ⊓ centralizer (E : Set G)) :=
    le_omega1_of_isElementaryAbelian hE'el (le_inf hE'Q hE'cent)
  rw [← hEeq] at hE'le
  exact le_antisymm hE'le hEE'

theorem eq_of_isS_of_pRank_two_comm {Q E F : Subgroup G} (hE : IsS Q E)
    (hErank : CFSG.pRank 2 ↥E = 2) (hF : IsFourSub Q F)
    (hcomm : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e) : F = E := by
  have hJel : CFSG.IsElementaryAbelian 2 ↥(E ⊔ F) :=
    isElementaryAbelian_sup hE.2.1 hF.2.1 hcomm
  have hJleQ : E ⊔ F ≤ Q := sup_le hE.1 hF.1
  have hJeq : E ⊔ F = E := eq_of_isS_of_le_elem hE hJleQ hJel le_sup_left
  have hFleE : F ≤ E := hJeq ▸ le_sup_right
  have hEcard : Nat.card ↥E = 4 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hE.2.1, hErank]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge hFleE (by rw [hEcard, hF.2.2])

theorem isS_pRank_three_of_isConn2 {Q E : Subgroup G} (hQp : IsPGroup 2 ↥Q)
    (hQconn : IsConn2 Q) (hQrk : 3 ≤ CFSG.pRank 2 ↥Q) (hE : IsS Q E) :
    3 ≤ CFSG.pRank 2 ↥E := by
  have hQne : Q ≠ ⊥ := by
    intro hQ0
    obtain ⟨W, hWQ, hWel, hWrk⟩ := exists_elemAbelian_pRank Q
    have hWbot : W = ⊥ := le_bot_iff.mp (by rwa [hQ0] at hWQ)
    have hcard : Nat.card ↥W = 1 := by rw [hWbot]; simp
    have hcardrank : Nat.card ↥W = 2 ^ CFSG.pRank 2 ↥W :=
      C3.Layer1.Back.card_eq_two_pow_pRank hWel
    have hpow : 2 ^ CFSG.pRank 2 ↥W = 2 ^ 0 := by
      rw [pow_zero, ← hcardrank, hcard]
    have hrank : CFSG.pRank 2 ↥W = 0 := Nat.pow_right_injective le_rfl hpow
    have hQrank0 : CFSG.pRank 2 ↥Q = 0 := by
      rw [← hWrk, hrank]
    omega
  obtain ⟨z, hzQ, hz2, hzc⟩ := exists_central_involution hQp hQne
  have hzsq : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  have hzE : z ∈ E := mem_of_isS_of_central hE hzQ hzsq hzc
  have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers z) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [pow_two]; exact hzsq)
  obtain ⟨W, hWQ, hWel, hWrk⟩ := exists_elemAbelian_pRank Q
  have hWel' : CFSG.IsElementaryAbelian 2 ↥W := hWel
  have hWz : CFSG.IsElementaryAbelian 2 ↥(W ⊔ zpowers z) := by
    refine isElementaryAbelian_sup hWel' hzel ?_
    intro w hw t ht
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ht
    exact (Commute.zpow_right (hzc w (hWQ hw)).symm m).eq
  set H : Subgroup G := W ⊔ zpowers z with hHdef
  have hHleQ : H ≤ Q := sup_le hWQ (zpowers_le.2 hzQ)
  have hHel : CFSG.IsElementaryAbelian 2 ↥H := hWz
  have hzH : z ∈ H := Subgroup.mem_sup_right (mem_zpowers z)
  have hHrk : 3 ≤ CFSG.pRank 2 ↥H := by
    have hle : CFSG.pRank 2 ↥W ≤ CFSG.pRank 2 ↥H :=
      C3.Layer1.Back.pRank_mono' (le_sup_left : W ≤ H)
    have hWge : 3 ≤ CFSG.pRank 2 ↥W := by
      rw [hWrk]
      exact hQrk
    omega
  obtain ⟨F, hFH, hFfourH⟩ :=
    exists_isFourSub_of_two_le_pRank (H := H) (by omega)
  have hFQ : F ≤ Q := hFH.trans hHleQ
  have hFfourQ : IsFourSub Q F := ⟨hFQ, hFfourH.2.1, hFfourH.2.2⟩
  by_contra hnot
  push Not at hnot
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := hE.2.1
  by_cases h1 : CFSG.pRank 2 ↥E ≤ 1
  ·
    have hEcard_le : Nat.card ↥E ≤ 2 := by
      rw [C3.Layer1.Back.card_eq_two_pow_pRank hEel]
      calc 2 ^ CFSG.pRank 2 ↥E ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 := by norm_num
    have hzcard : Nat.card ↥(zpowers z) = 2 := by
      rw [Nat.card_zpowers, hz2]
    have hzeq : zpowers z = E :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hzE)
        (by rw [hzcard]; exact hEcard_le)
    have hEeq : E = zpowers z := hzeq.symm
    have hEH : E ≤ H := hEeq.le.trans (zpowers_le.2 hzH)
    have hHE : H = E := eq_of_isS_of_le_elem hE hHleQ hHel hEH
    rw [hHE] at hHrk
    omega
  · push Not at h1
    have hErank : CFSG.pRank 2 ↥E = 2 := by omega
    have hEcard : Nat.card ↥E = 4 := by
      rw [C3.Layer1.Back.card_eq_two_pow_pRank hEel, hErank]
      norm_num
    have hEfourQ : IsFourSub Q E := ⟨hE.1, hEel, hEcard⟩
    have hchain := hQconn E F hEfourQ hFfourQ
    have hcollapse : ∀ {A' : Subgroup G},
        Relation.ReflTransGen
          (fun A' B' : Subgroup G => IsFourSub Q B' ∧
            ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) E A' → A' = E := by
      intro A' hA'
      induction hA' with
      | refl => rfl
      | tail _ hstep ih =>
          have hbE : _ = E := ih
          subst hbE
          exact eq_of_isS_of_pRank_two_comm hE hErank hstep.1 hstep.2
    have hFE : F = E := hcollapse hchain
    have hEH : E ≤ H := hFE ▸ hFH
    have hHE : H = E := eq_of_isS_of_le_elem hE hHleQ hHel hEH
    rw [hHE] at hHrk
    omega


theorem connected_two_group_rank_three_centralizer [Finite G] {Q : Subgroup G}
    (hQp : IsPGroup 2 ↥Q) (hQconn : IsConn2 Q)
    (hQrk : 3 ≤ CFSG.pRank 2 ↥Q) :
    ∀ u ∈ Q, orderOf u = 2 →
      3 ≤ CFSG.pRank 2 ↥(Subgroup.centralizer ({u} : Set G)) := by
  intro u hu hu2
  have hWel : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers u) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one
      (by rw [pow_two]; exact mul_self_eq_one_of_orderOf_eq_two hu2)
  obtain ⟨E, huE, hE⟩ := exists_maximal_elemAbelian (X := Q)
    (Subgroup.zpowers_le.2 hu) hWel
  have hE3 : 3 ≤ CFSG.pRank 2 ↥E :=
    isS_pRank_three_of_isConn2 hQp hQconn hQrk hE
  have heE : u ∈ E := huE (mem_zpowers u)
  haveI : CFSG.IsElementaryAbelian 2 ↥E := hE.2.1
  have hEcent : E ≤ Subgroup.centralizer ({u} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hx⟩ ⟨u, heE⟩)
  exact hE3.trans (C3.Layer1.Back.pRank_mono' hEcent)

theorem conn_fixed_four {D Q : Subgroup G} (hDQ : CommDisj D Q) (hD4 : IsFourSub ⊤ D)
    (hQp : IsPGroup 2 ↥Q) (hQconn : IsConn2 Q) (hQrk : 3 ≤ CFSG.pRank 2 ↥Q)
    {B A : Subgroup G}
    (hB : B ∈ {B' : Subgroup G | ∃ E : Subgroup G,
      IsS Q E ∧ 3 ≤ CFSG.pRank 2 ↥E ∧ B' = D ⊔ E})
    (hA : IsE 4 (⨆ B' ∈ {B' : Subgroup G | ∃ E : Subgroup G,
      IsS Q E ∧ 3 ≤ CFSG.pRank 2 ↥E ∧ B' = D ⊔ E}, B') A) :
    RConnN 4 5 (⨆ B' ∈ {B' : Subgroup G | ∃ E : Subgroup G,
      IsS Q E ∧ 3 ≤ CFSG.pRank 2 ↥E ∧ B' = D ⊔ E}, B') A B := by
  set BT : Set (Subgroup G) :=
    {B' : Subgroup G | ∃ E : Subgroup G, IsS Q E ∧ 3 ≤ CFSG.pRank 2 ↥E ∧ B' = D ⊔ E}
    with hBTdef
  set X : Subgroup G := ⨆ B' ∈ BT, B' with hXdef
  have hle_X : ∀ B' ∈ BT, B' ≤ X := fun B' hB' =>
    le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ BT) => B) B' hB'
  have hX_le : X ≤ D ⊔ Q := by
    refine iSup₂_le fun B' hB' => ?_
    obtain ⟨E, hE, -, rfl⟩ := hB'
    exact sup_le le_sup_left (hE.1.trans le_sup_right)
  obtain ⟨hAX, hAel, hArk⟩ := hA
  have fourLift_mem : ∀ {V : Subgroup G}, IsFourSub Q V → IsE 4 X (D ⊔ V) := by
    intro V hV
    obtain ⟨E, hVE, hE⟩ := exists_maximal_elemAbelian (X := Q) hV.1 hV.2.1
    have hErk : 3 ≤ CFSG.pRank 2 ↥E := isS_pRank_three_of_isConn2 hQp hQconn hQrk hE
    have hDEBT : D ⊔ E ∈ BT := ⟨E, hE, hErk, rfl⟩
    have hDEX : D ⊔ E ≤ X := hle_X _ hDEBT
    have hDVle : D ⊔ V ≤ D ⊔ E := sup_le_sup le_rfl hVE
    have hDVel : CFSG.IsElementaryAbelian 2 ↥(D ⊔ V) :=
      hDQ.isElementaryAbelian_sup' hD4.2.1 hV.2.1 le_rfl hV.1
    have hDVrk : 4 ≤ CFSG.pRank 2 ↥(D ⊔ V) := by
      rw [hDQ.pRank_sup hD4.2.1 hV.2.1 le_rfl hV.1,
        pRank_of_isFourSub hD4, pRank_of_isFourSub (P := Q) hV]
    exact ⟨hDVle.trans hDEX, hDVel, hDVrk⟩
  have hBX : B ≤ X := hle_X B hB
  obtain ⟨E₀, hE₀, hE₀rk, hBeq⟩ := hB
  have hBrk0 : 5 ≤ CFSG.pRank 2 ↥(D ⊔ E₀) := by
    rw [hDQ.pRank_sup hD4.2.1 hE₀.2.1 le_rfl hE₀.1, pRank_of_isFourSub hD4]
    omega
  have hBel0 : CFSG.IsElementaryAbelian 2 ↥(D ⊔ E₀) :=
    hDQ.isElementaryAbelian_sup' hD4.2.1 hE₀.2.1 le_rfl hE₀.1
  have hB5 : IsE 5 X B := by
    refine ⟨hBX, ?_, ?_⟩
    · rwa [hBeq]
    · rwa [hBeq]
  have hB4 : IsE 4 X B := isE_mono_rank hB5 (by norm_num)
  have hAprojQ : CFSG.IsElementaryAbelian 2 ↥(hDQ.projQ A) :=
    hDQ.isElementaryAbelian_projQ hAel
  obtain ⟨E'', hAQE'', hE''⟩ :=
    exists_maximal_elemAbelian (X := Q) (hDQ.projQ_le_right A) hAprojQ
  have hE''rk : 3 ≤ CFSG.pRank 2 ↥E'' :=
    isS_pRank_three_of_isConn2 hQp hQconn hQrk hE''
  have hAPQ : A ≤ D ⊔ Q := hAX.trans hX_le
  have hAle_proj : A ≤ D ⊔ hDQ.projQ A :=
    (hDQ.le_projP_sup_projQ hAPQ).trans (sup_le_sup (hDQ.projP_le_left A) le_rfl)
  have hAle_DE'' : A ≤ D ⊔ E'' :=
    hAle_proj.trans (sup_le_sup le_rfl hAQE'')
  have hDE''BT : D ⊔ E'' ∈ BT := ⟨E'', hE'', hE''rk, rfl⟩
  have hDE''X : D ⊔ E'' ≤ X := hle_X _ hDE''BT
  have hDE''el : CFSG.IsElementaryAbelian 2 ↥(D ⊔ E'') :=
    hDQ.isElementaryAbelian_sup' hD4.2.1 hE''.2.1 le_rfl hE''.1
  have hDE''rk : 5 ≤ CFSG.pRank 2 ↥(D ⊔ E'') := by
    rw [hDQ.pRank_sup hD4.2.1 hE''.2.1 le_rfl hE''.1, pRank_of_isFourSub hD4]
    omega
  have hDE''5 : IsE 5 X (D ⊔ E'') := ⟨hDE''X, hDE''el, hDE''rk⟩
  have hDE''4 : IsE 4 X (D ⊔ E'') := isE_mono_rank hDE''5 (by norm_num)
  obtain ⟨V'', hV''E'', hV''fourE''⟩ :=
    exists_isFourSub_of_two_le_pRank (H := E'') (by omega)
  have hV''Q : V'' ≤ Q := hV''E''.trans hE''.1
  have hV''four : IsFourSub Q V'' := ⟨hV''Q, hV''fourE''.2.1, hV''fourE''.2.2⟩
  obtain ⟨V0, hV0E₀, hV0fourE₀⟩ :=
    exists_isFourSub_of_two_le_pRank (H := E₀) (by omega)
  have hV0Q : V0 ≤ Q := hV0E₀.trans hE₀.1
  have hV0four : IsFourSub Q V0 := ⟨hV0Q, hV0fourE₀.2.1, hV0fourE₀.2.2⟩
  have hsA : ConnStep 4 5 X A (D ⊔ E'') :=
    connStep_of_le_elem hDE''5 hAle_DE'' le_rfl hDE''4
  have hsV'' : ConnStep 4 5 X (D ⊔ E'') (D ⊔ V'') :=
    connStep_of_le_elem hDE''5 le_rfl (sup_le_sup le_rfl hV''E'') (fourLift_mem hV''four)
  have hsEnd : ConnStep 4 5 X (D ⊔ V0) B := by
    refine connStep_of_le_elem hB5 ?_ le_rfl hB4
    rw [hBeq]
    exact sup_le_sup le_rfl hV0E₀
  have hchain := hQconn V'' V0 hV''four hV0four
  have lift_step : ∀ {a c : Subgroup G}, IsFourSub Q a → IsFourSub Q c →
      (∀ x ∈ a, ∀ y ∈ c, x * y = y * x) → ConnStep 4 5 X (D ⊔ a) (D ⊔ c) := by
    intro a c ha4 hc4 hcomm
    by_cases heq : a = c
    · rw [heq]
      refine ⟨fourLift_mem hc4, ?_, Or.inl rfl⟩
      intro x hx y hy
      exact ((C3.Layer1.Back.forall_of_isElementaryAbelian
        (fourLift_mem hc4).2.1).1 x hx y hy)
    · have hJQ : a ⊔ c ≤ Q := sup_le ha4.1 hc4.1
      have hJel : CFSG.IsElementaryAbelian 2 ↥(a ⊔ c) :=
        isElementaryAbelian_sup ha4.2.1 hc4.2.1 hcomm
      obtain ⟨Eij, hJEij, hEij⟩ :=
        exists_maximal_elemAbelian (X := Q) hJQ hJel
      have hEijrk : 3 ≤ CFSG.pRank 2 ↥Eij :=
        isS_pRank_three_of_isConn2 hQp hQconn hQrk hEij
      have hWBT : D ⊔ Eij ∈ BT := ⟨Eij, hEij, hEijrk, rfl⟩
      have hWX : D ⊔ Eij ≤ X := hle_X _ hWBT
      have hWel : CFSG.IsElementaryAbelian 2 ↥(D ⊔ Eij) :=
        hDQ.isElementaryAbelian_sup' hD4.2.1 hEij.2.1 le_rfl hEij.1
      have hWrk : 5 ≤ CFSG.pRank 2 ↥(D ⊔ Eij) := by
        rw [hDQ.pRank_sup hD4.2.1 hEij.2.1 le_rfl hEij.1,
          pRank_of_isFourSub hD4]
        omega
      have hW5 : IsE 5 X (D ⊔ Eij) := ⟨hWX, hWel, hWrk⟩
      have hleft : D ⊔ a ≤ D ⊔ Eij :=
        sup_le_sup le_rfl (le_sup_left.trans hJEij)
      have hright : D ⊔ c ≤ D ⊔ Eij :=
        sup_le_sup le_rfl (le_sup_right.trans hJEij)
      exact connStep_of_le_elem hW5 hleft hright (fourLift_mem hc4)
  have hlift_aux : ∀ {a : Subgroup G},
      Relation.ReflTransGen
        (fun A' B' : Subgroup G => IsFourSub Q B' ∧
          ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) a V0 →
      IsFourSub Q a →
      Relation.ReflTransGen (ConnStep 4 5 X) (D ⊔ a) (D ⊔ V0) := by
    intro a hchain_a ha4
    refine Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => IsFourSub Q a →
        Relation.ReflTransGen (ConnStep 4 5 X) (D ⊔ a) (D ⊔ V0))
      hchain_a ?_ ?_ ha4
    · intro _; exact Relation.ReflTransGen.refl
    · intro b c hbc htail ih hb4
      exact Relation.ReflTransGen.head (lift_step hb4 hbc.1 hbc.2) (ih hbc.1)
  have hchainLift : Relation.ReflTransGen (ConnStep 4 5 X) (D ⊔ V'') (D ⊔ V0) :=
    hlift_aux hchain hV''four
  exact Relation.ReflTransGen.head hsA
    (Relation.ReflTransGen.head hsV''
      (hchainLift.trans (Relation.ReflTransGen.single hsEnd)))

end Conn4

theorem conn_core [Finite G] {P Q : Subgroup G} (h : CommDisj P Q) (hP : RankTwoShape P)
    (hQ : IsPGroup 2 ↥Q) (𝒰 : Set (Subgroup G)) (h𝒰 : ∀ U ∈ 𝒰, IsFourSub P U)
    {BT : Set (Subgroup G)}
    (hBT : ∀ B, B ∈ BT ↔ ∃ U ∈ 𝒰, ∃ E : Subgroup G, IsS Q E ∧ 2 ≤ pRank 2 ↥E ∧ B = U ⊔ E)
    (hcov : ∀ A : Subgroup G, A ≤ (⨆ B ∈ BT, B) → CFSG.IsElementaryAbelian 2 ↥A →
      ∃ U ∈ 𝒰, h.projP A ≤ U)
    {B : Subgroup G} (hB : B ∈ BT) {A : Subgroup G} (hA : IsE 3 (⨆ B ∈ BT, B) A) :
    RConnN 3 4 (⨆ B ∈ BT, B) A B := by
  set X : Subgroup G := ⨆ B ∈ BT, B with hX
  have hle_X : ∀ B' ∈ BT, B' ≤ X := fun B' hB' =>
    le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ BT) => B) B' hB'
  have hX_le : X ≤ P ⊔ Q := by
    refine iSup₂_le fun B' hB' => ?_
    obtain ⟨U, hU, E, hE, -, rfl⟩ := (hBT B').1 hB'
    exact sup_le_sup (h𝒰 U hU).1 hE.1
  obtain ⟨hAX, hAel, -⟩ := hA
  obtain ⟨U₀, hU₀, E₀, hE₀, hE₀rk, hBeq⟩ := (hBT B).1 hB
  have hU₀P := h𝒰 U₀ hU₀
  have hQne : Q ≠ ⊥ := by
    intro hQ0
    have hE₀bot : E₀ = ⊥ := by
      rw [eq_bot_iff, ← hQ0]; exact hE₀.1
    have hcard := C3.Layer1.Back.card_eq_two_pow_pRank hE₀.2.1
    have h4 : (2 : ℕ) ^ 2 ≤ Nat.card ↥E₀ := by
      rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) hE₀rk
    rw [hE₀bot, Subgroup.card_bot] at h4
    omega
  obtain ⟨zQ, hzQ, hzQ2, hzQc⟩ := exists_central_involution hQ hQne
  have hzQsq := mul_self_eq_one_of_orderOf_eq_two hzQ2
  have hzQ1 : zQ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hzQ2
    omega
  have hzQE₀ : zQ ∈ E₀ := mem_of_isS_of_central hE₀ hzQ hzQsq hzQc
  have hAPQ : A ≤ P ⊔ Q := hAX.trans hX_le
  obtain ⟨U', hU', hUA⟩ := hcov A hAX hAel
  have hU'P := h𝒰 U' hU'
  obtain ⟨E'', hEA, hE'', hE''rk⟩ := exists_isS_two_le (Q := Q) (W := h.projQ A) (E₀ := E₀)
    (h.projQ_le_right A) (h.isElementaryAbelian_projQ hAel) hE₀ hE₀rk hzQ hzQ1 hzQsq hzQc
  obtain ⟨z, hzU', hzU₀, hz2⟩ := hP.2.2 U' U₀ hU'P hU₀P
  have hzsq := mul_self_eq_one_of_orderOf_eq_two hz2
  have hzP : z ∈ P := hU'P.1 hzU'
  have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers z) := by
    have : z ^ 2 = 1 := by rw [pow_two]; exact hzsq
    exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one this
  have hzQel : CFSG.IsElementaryAbelian 2 ↥(zpowers zQ) := by
    have : zQ ^ 2 = 1 := by rw [pow_two]; exact hzQsq
    exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one this
  have hzpP : zpowers z ≤ P := zpowers_le.2 hzP
  have hzQpQ : zpowers zQ ≤ Q := zpowers_le.2 hzQ
  have hrz : pRank 2 ↥(zpowers z) = 1 := by
    have hc : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers]; exact hz2
    have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hzel
    rw [hc] at h2
    have : (2 : ℕ) ^ 1 = 2 ^ pRank 2 ↥(zpowers z) := by simpa using h2
    exact (Nat.pow_right_injective le_rfl this).symm
  have hrzQ : pRank 2 ↥(zpowers zQ) = 1 := by
    have hc : Nat.card ↥(zpowers zQ) = 2 := by rw [Nat.card_zpowers]; exact hzQ2
    have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hzQel
    rw [hc] at h2
    have : (2 : ℕ) ^ 1 = 2 ^ pRank 2 ↥(zpowers zQ) := by simpa using h2
    exact (Nat.pow_right_injective le_rfl this).symm
  have hr₂ := pRank_of_isFourSub hU'P
  have hr₀ := pRank_of_isFourSub hU₀P
  have hA₁BT : U' ⊔ E'' ∈ BT := (hBT _).2 ⟨U', hU', E'', hE'', hE''rk, rfl⟩
  have hA₃BT : U₀ ⊔ E'' ∈ BT := (hBT _).2 ⟨U₀, hU₀, E'', hE'', hE''rk, rfl⟩
  have hA₅BT : U₀ ⊔ E₀ ∈ BT := hBeq ▸ hB
  have hA₁X := hle_X _ hA₁BT
  have hA₃X := hle_X _ hA₃BT
  have hA₅X := hle_X _ hA₅BT
  have hA₁el := h.isElementaryAbelian_sup' hU'P.2.1 hE''.2.1 hU'P.1 hE''.1
  have hA₃el := h.isElementaryAbelian_sup' hU₀P.2.1 hE''.2.1 hU₀P.1 hE''.1
  have hA₅el := h.isElementaryAbelian_sup' hU₀P.2.1 hE₀.2.1 hU₀P.1 hE₀.1
  have hA₂el := h.isElementaryAbelian_sup' hzel hE''.2.1 hzpP hE''.1
  have hA₄el := h.isElementaryAbelian_sup' hU₀P.2.1 hzQel hU₀P.1 hzQpQ
  have hr₁ : pRank 2 ↥(U' ⊔ E'') = 2 + pRank 2 ↥E'' := by
    rw [h.pRank_sup hU'P.2.1 hE''.2.1 hU'P.1 hE''.1, hr₂]
  have hr₃ : pRank 2 ↥(U₀ ⊔ E'') = 2 + pRank 2 ↥E'' := by
    rw [h.pRank_sup hU₀P.2.1 hE''.2.1 hU₀P.1 hE''.1, hr₀]
  have hr₅ : pRank 2 ↥(U₀ ⊔ E₀) = 2 + pRank 2 ↥E₀ := by
    rw [h.pRank_sup hU₀P.2.1 hE₀.2.1 hU₀P.1 hE₀.1, hr₀]
  have hr₂' : pRank 2 ↥(zpowers z ⊔ E'') = 1 + pRank 2 ↥E'' := by
    rw [h.pRank_sup hzel hE''.2.1 hzpP hE''.1, hrz]
  have hr₄ : pRank 2 ↥(U₀ ⊔ zpowers zQ) = 2 + 1 := by
    rw [h.pRank_sup hU₀P.2.1 hzQel hU₀P.1 hzQpQ, hr₀, hrzQ]
  have hzE'' : zQ ∈ E'' := mem_of_isS_of_central hE'' hzQ hzQsq hzQc
  have hAle₁ : A ≤ U' ⊔ E'' :=
    (h.le_projP_sup_projQ hAPQ).trans (sup_le_sup hUA hEA)
  have hA₂le₁ : zpowers z ⊔ E'' ≤ U' ⊔ E'' := sup_le_sup (zpowers_le.2 hzU') le_rfl
  have hA₂le₃ : zpowers z ⊔ E'' ≤ U₀ ⊔ E'' := sup_le_sup (zpowers_le.2 hzU₀) le_rfl
  have hA₄le₃ : U₀ ⊔ zpowers zQ ≤ U₀ ⊔ E'' := sup_le_sup le_rfl (zpowers_le.2 hzE'')
  have hA₄le₅ : U₀ ⊔ zpowers zQ ≤ U₀ ⊔ E₀ := sup_le_sup le_rfl (zpowers_le.2 hzQE₀)
  have hIsE : ∀ (m : ℕ) (W : Subgroup G), W ≤ X → CFSG.IsElementaryAbelian 2 ↥W → m ≤ pRank 2 ↥W →
      IsE m X W := fun m W h1 h2 h3 => ⟨h1, h2, h3⟩
  have hE''2 : 2 ≤ pRank 2 ↥E'' := hE''rk
  have hs1 : ConnStep 3 4 X A (U' ⊔ E'') :=
    connStep_of_le_elem (hIsE 4 _ hA₁X hA₁el (by omega)) hAle₁ le_rfl
      (hIsE 3 _ hA₁X hA₁el (by omega))
  have hs2 : ConnStep 3 4 X (U' ⊔ E'') (zpowers z ⊔ E'') :=
    connStep_of_le_elem (hIsE 4 _ hA₁X hA₁el (by omega)) le_rfl hA₂le₁
      (hIsE 3 _ (hA₂le₁.trans hA₁X) hA₂el (by omega))
  have hs3 : ConnStep 3 4 X (zpowers z ⊔ E'') (U₀ ⊔ E'') :=
    connStep_of_le_elem (hIsE 4 _ hA₃X hA₃el (by omega)) hA₂le₃ le_rfl
      (hIsE 3 _ hA₃X hA₃el (by omega))
  have hs4 : ConnStep 3 4 X (U₀ ⊔ E'') (U₀ ⊔ zpowers zQ) :=
    connStep_of_le_elem (hIsE 4 _ hA₃X hA₃el (by omega)) le_rfl hA₄le₃
      (hIsE 3 _ (hA₄le₃.trans hA₃X) hA₄el (by omega))
  have hs5 : ConnStep 3 4 X (U₀ ⊔ zpowers zQ) B := by
    rw [hBeq]
    exact connStep_of_le_elem (hIsE 4 _ hA₅X hA₅el (by omega)) hA₄le₅ le_rfl
      (hIsE 3 _ hA₅X hA₅el (by omega))
  rw [hBeq]
  exact Relation.ReflTransGen.head hs1 (Relation.ReflTransGen.head hs2
    (Relation.ReflTransGen.head hs3 (Relation.ReflTransGen.head hs4
      (Relation.ReflTransGen.single (by rw [← hBeq]; exact hs5)))))

theorem le_pRank_of_le_card [Finite G] {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) {k : ℕ}
    (hk : 2 ^ k ≤ Nat.card ↥A) : k ≤ pRank 2 ↥A := by
  rw [C3.Layer1.Back.card_eq_two_pow_pRank hA] at hk
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hk

theorem card_le_two_mul_inf [Finite G] {T R A : Subgroup G} (hRT : R ≤ T)
    (hT : Nat.card ↥T ≤ 2 * Nat.card ↥R) (hAT : A ≤ T) :
    Nat.card ↥A ≤ 2 * Nat.card ↥(R ⊓ A) := by
  have h := Subgroup.card_mul_index (R.subgroupOf T)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRT).toEquiv] at h
  have hpos : 0 < Nat.card ↥R := Nat.card_pos
  have hne : R.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : R.relIndex T ≤ 2 := by
    have hT' : Nat.card ↥R * (R.subgroupOf T).index ≤ Nat.card ↥R * 2 := by
      rw [h]; omega
    exact Nat.le_of_mul_le_mul_left hT' hpos
  have h2 : (R ⊓ A).relIndex A ≤ 2 := by
    rw [Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right hAT hne).trans h1
  have h3 := Subgroup.card_mul_index ((R ⊓ A).subgroupOf A)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ⊓ A ≤ A)).toEquiv] at h3
  have h4 : ((R ⊓ A).subgroupOf A).index ≤ 2 := h2
  calc Nat.card ↥A = Nat.card ↥(R ⊓ A) * ((R ⊓ A).subgroupOf A).index := h3.symm
    _ ≤ Nat.card ↥(R ⊓ A) * 2 := Nat.mul_le_mul_left _ h4
    _ = 2 * Nat.card ↥(R ⊓ A) := by ring

theorem conn_core_T [Finite G] {P Q T : Subgroup G} (h : CommDisj P Q)
    (hPel : CFSG.IsElementaryAbelian 2 ↥P) (hP4 : Nat.card ↥P = 4) (hQ : IsPGroup 2 ↥Q)
    (hRT : P ⊔ Q ≤ T)
    (hidx : ∀ A : Subgroup G, A ≤ T → Nat.card ↥A ≤ 2 * Nat.card ↥((P ⊔ Q) ⊓ A))
    {E₀ : Subgroup G} (hE₀ : IsS Q E₀) (hE₀rk : 2 ≤ pRank 2 ↥E₀)
    {B : Subgroup G} (hB : IsSn 4 T B) {A : Subgroup G}
    (hA : IsE 4 (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 T B''}, B') A) :
    RConnN 3 4 (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 T B''}, B') A B := by
  set BT : Set (Subgroup G) := {B'' : Subgroup G | IsSn 4 T B''} with hBTdef
  set X : Subgroup G := ⨆ B' ∈ BT, B' with hX
  have hle_X : ∀ B' ∈ BT, B' ≤ X := fun B' hB' =>
    le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ BT) => B) B' hB'
  have hXT : X ≤ T := iSup₂_le fun B' hB' => hB'.1.1
  have hBBT : B ∈ BT := hB
  obtain ⟨hAX, hAel, hArk⟩ := hA
  have hrP : pRank 2 ↥P = 2 := by
    have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hPel
    rw [hP4] at h2
    have : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥P := by simpa using h2
    exact (Nat.pow_right_injective le_rfl this).symm
  have hQne : Q ≠ ⊥ := by
    intro hQ0
    have hE₀bot : E₀ = ⊥ := by
      rw [eq_bot_iff, ← hQ0]; exact hE₀.1
    have hcard := C3.Layer1.Back.card_eq_two_pow_pRank hE₀.2.1
    have h4 : (2 : ℕ) ^ 2 ≤ Nat.card ↥E₀ := by
      rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) hE₀rk
    rw [hE₀bot, Subgroup.card_bot] at h4
    omega
  obtain ⟨zQ, hzQ, hzQ2, hzQc⟩ := exists_central_involution hQ hQne
  have hzQsq := mul_self_eq_one_of_orderOf_eq_two hzQ2
  have hzQ1 : zQ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hzQ2
    omega
  have hzQel : CFSG.IsElementaryAbelian 2 ↥(zpowers zQ) := by
    have : zQ ^ 2 = 1 := by rw [pow_two]; exact hzQsq
    exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one this
  have hzQpQ : zpowers zQ ≤ Q := zpowers_le.2 hzQ
  have hrzQ : pRank 2 ↥(zpowers zQ) = 1 := by
    have hc : Nat.card ↥(zpowers zQ) = 2 := by rw [Nat.card_zpowers]; exact hzQ2
    have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hzQel
    rw [hc] at h2
    have : (2 : ℕ) ^ 1 = 2 ^ pRank 2 ↥(zpowers zQ) := by simpa using h2
    exact (Nat.pow_right_injective le_rfl this).symm
  have claimW : ∀ F : Subgroup G, F ≤ Q → CFSG.IsElementaryAbelian 2 ↥F →
      ∃ W : Subgroup G, P ⊔ F ≤ W ∧ IsE 4 X W := by
    intro F hFQ hFel
    obtain ⟨E₁, hFE₁, hE₁, hE₁rk⟩ := exists_isS_two_le (Q := Q) (W := F) (E₀ := E₀) hFQ hFel hE₀
      hE₀rk hzQ hzQ1 hzQsq hzQc
    have hPE₁el := h.isElementaryAbelian_sup' hPel hE₁.2.1 le_rfl hE₁.1
    have hPE₁T : P ⊔ E₁ ≤ T := (sup_le_sup le_rfl hE₁.1).trans hRT
    obtain ⟨W, hPEW, hW⟩ := exists_maximal_elemAbelian hPE₁T hPE₁el
    have hWrk : 4 ≤ pRank 2 ↥W := by
      have h1 : pRank 2 ↥(P ⊔ E₁) = 2 + pRank 2 ↥E₁ := by
        rw [h.pRank_sup hPel hE₁.2.1 le_rfl hE₁.1, hrP]
      have := C3.Layer1.Back.pRank_mono' hPEW
      omega
    have hWBT : W ∈ BT := ⟨hW, hWrk⟩
    exact ⟨W, (sup_le_sup le_rfl hFE₁).trans hPEW, hle_X W hWBT, hW.2.1, hWrk⟩
  have hZ₀el := h.isElementaryAbelian_sup' hPel hzQel le_rfl hzQpQ
  have hZ₀rk : pRank 2 ↥(P ⊔ zpowers zQ) = 3 := by
    rw [h.pRank_sup hPel hzQel le_rfl hzQpQ, hrP, hrzQ]
  obtain ⟨W₀, hZ₀W₀, hW₀⟩ := claimW (zpowers zQ) hzQpQ hzQel
  have hZ₀X : P ⊔ zpowers zQ ≤ X := hZ₀W₀.trans hW₀.1
  have hconnV : ∀ V : Subgroup G, V ≤ P ⊔ Q → CFSG.IsElementaryAbelian 2 ↥V →
      ∃ W : Subgroup G, V ≤ W ∧ P ⊔ zpowers zQ ≤ W ∧ IsE 4 X W := by
    intro V hVR hVel
    have hFel : CFSG.IsElementaryAbelian 2 ↥(h.projQ V ⊔ zpowers zQ) := by
      refine isElementaryAbelian_sup (h.isElementaryAbelian_projQ hVel) hzQel ?_
      intro q hq t ht
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ht
      exact (Commute.zpow_right (hzQc q (h.projQ_le_right V hq)).symm m).eq
    obtain ⟨W, hW, hWE⟩ := claimW (h.projQ V ⊔ zpowers zQ) (sup_le (h.projQ_le_right V) hzQpQ) hFel
    refine ⟨W, ?_, ?_, hWE⟩
    · exact (h.le_projP_sup_projQ hVR).trans
        ((sup_le_sup (h.projP_le_left V) le_sup_left).trans hW)
    · exact (sup_le_sup le_rfl le_sup_right).trans hW
  have hrk3 : ∀ C : Subgroup G, C ≤ T → CFSG.IsElementaryAbelian 2 ↥C → 4 ≤ pRank 2 ↥C →
      3 ≤ pRank 2 ↥((P ⊔ Q) ⊓ C) := by
    intro C hCT hCel hCrk
    have h1 := hidx C hCT
    have hel : CFSG.IsElementaryAbelian 2 ↥((P ⊔ Q) ⊓ C) := elemAbelian_of_le hCel inf_le_right
    have h2 : 2 ^ 4 ≤ Nat.card ↥C := by
      rw [C3.Layer1.Back.card_eq_two_pow_pRank hCel]
      exact Nat.pow_le_pow_right (by norm_num) hCrk
    exact le_pRank_of_le_card hel (by omega)
  have hA₁rk := hrk3 A (hAX.trans hXT) hAel hArk
  have hB₁rk := hrk3 B hB.1.1 hB.1.2.1 hB.2
  have hA₁el : CFSG.IsElementaryAbelian 2 ↥((P ⊔ Q) ⊓ A) := elemAbelian_of_le hAel inf_le_right
  have hB₁el : CFSG.IsElementaryAbelian 2 ↥((P ⊔ Q) ⊓ B) := elemAbelian_of_le hB.1.2.1 inf_le_right
  have hs1 : ConnStep 3 4 X A ((P ⊔ Q) ⊓ A) :=
    connStep_of_le_elem ⟨hAX, hAel, hArk⟩ le_rfl inf_le_right
      ⟨inf_le_right.trans hAX, hA₁el, hA₁rk⟩
  obtain ⟨W₂, hA₁W₂, hZW₂, hW₂⟩ := hconnV ((P ⊔ Q) ⊓ A) inf_le_left hA₁el
  have hs2 : ConnStep 3 4 X ((P ⊔ Q) ⊓ A) (P ⊔ zpowers zQ) :=
    connStep_of_le_elem hW₂ hA₁W₂ hZW₂ ⟨hZ₀X, hZ₀el, by omega⟩
  obtain ⟨W₃, hB₁W₃, hZW₃, hW₃⟩ := hconnV ((P ⊔ Q) ⊓ B) inf_le_left hB₁el
  have hs3 : ConnStep 3 4 X (P ⊔ zpowers zQ) ((P ⊔ Q) ⊓ B) :=
    connStep_of_le_elem hW₃ hZW₃ hB₁W₃ ⟨inf_le_right.trans (hle_X B hBBT), hB₁el, hB₁rk⟩
  have hs4 : ConnStep 3 4 X ((P ⊔ Q) ⊓ B) B :=
    connStep_of_le_elem ⟨hle_X B hBBT, hB.1.2.1, hB.2⟩ inf_le_right le_rfl
      ⟨hle_X B hBBT, hB.1.2.1, by have := hB.2; omega⟩
  exact Relation.ReflTransGen.head hs1 (Relation.ReflTransGen.head hs2
    (Relation.ReflTransGen.head hs3 (Relation.ReflTransGen.single hs4)))

theorem isConn2_of_four_extend [Finite G] {Q : Subgroup G}
    (hQp : IsPGroup 2 ↥Q)
    (hext : ∀ A : Subgroup G, IsFourSub Q A → ∃ E : Subgroup G, A ≤ E ∧ IsE 3 Q E) :
    IsConn2 Q := by
  intro A B hA hB
  obtain ⟨EA, hAEA, hEA⟩ := hext A hA
  have hEAfull : IsE 3 Q EA := hEA
  obtain ⟨hEAQ, hEAel, hEArank⟩ := hEA
  have hQ3 : 3 ≤ pRank 2 ↥Q := hEArank.trans (C3.Layer1.Back.pRank_mono' hEAQ)
  have hQ3open : 3 ≤ CFSG.Open.twoRank ↥Q := by
    rw [CFSG.Open.twoRank, ← CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥Q]
    exact hQ3
  obtain ⟨V, hVnormal, hVab, hVcard⟩ :=
    CFSG.ProperTwoGeneratedCore.high_two_rank_normal_four ↥Q hQp hQ3open
  have : V.Normal := hVnormal
  set C : Subgroup ↥Q := Subgroup.centralizer (V : Set ↥Q) with hCdef
  have hCindex : C.index ≤ 2 := by
    have h := (CFSG.ProperTwoGeneratedCore.normal_four_centralizer_index
      (G := ↥Q) hQp V hVab hVcard).2.2
    simpa [hCdef] using h
  let U : Subgroup G := V.map Q.subtype
  let R : Subgroup G := C.map Q.subtype
  have hRQ : R ≤ Q := Subgroup.map_subtype_le C
  have hcardQ : Nat.card ↥Q ≤ 2 * Nat.card ↥R := by
    have hmul := Subgroup.card_mul_index C
    have hcardR : Nat.card ↥R = Nat.card ↥C := by
      rw [Subgroup.card_map_of_injective Q.subtype_injective]
    calc Nat.card ↥Q = Nat.card ↥C * C.index := hmul.symm
      _ ≤ Nat.card ↥C * 2 := Nat.mul_le_mul_left _ hCindex
      _ = 2 * Nat.card ↥R := by rw [hcardR]; ring
  have hUQ : U ≤ Q := Subgroup.map_subtype_le V
  have hUel : CFSG.IsElementaryAbelian 2 ↥U := by
    have hVab' : CFSG.IsElementaryAbelian 2 ↥V :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).2 hVab
    exact CFSG.IsElementaryAbelian.map (p := 2) (A := V) Q.subtype
  have hUcard : Nat.card ↥U = 4 := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hVcard]
  have hUfour : IsFourSub Q U := ⟨hUQ, hUel, hUcard⟩
  have hcentR : ∀ f ∈ R, ∀ u ∈ U, f * u = u * f := by
    intro f hf u hu
    rw [Subgroup.mem_map] at hf hu
    obtain ⟨c, hcC, rfl⟩ := hf
    obtain ⟨v, hvV, rfl⟩ := hu
    have hc := Subgroup.mem_centralizer_iff.1 hcC v hvV
    exact (congrArg (fun x : ↥Q => (x : G)) hc).symm
  have exists_F : ∀ {A' E : Subgroup G}, IsFourSub Q A' → A' ≤ E → IsE 3 Q E →
      ∃ F : Subgroup G, F ≤ E ∧ F ≤ R ∧ IsFourSub Q F ∧
        (∀ a ∈ A', ∀ f ∈ F, a * f = f * a) := by
    intro A' E hA' hA'E hE
    obtain ⟨hEQ, hEel, hErank⟩ := hE
    have hcard : Nat.card ↥E ≤ 2 * Nat.card ↥(R ⊓ E) :=
      card_le_two_mul_inf hRQ hcardQ hEQ
    have hEcard : 8 ≤ Nat.card ↥E := by
      simpa using CFSG.GH74.GLS.Th2Sig8.two_pow_le_card hEel hErank
    have hREcard : 4 ≤ Nat.card ↥(R ⊓ E) := by omega
    have hREel : CFSG.IsElementaryAbelian 2 ↥(R ⊓ E) :=
      CFSG.GH74.GLS.Th2Sig8.isElementaryAbelian_of_le hEel inf_le_right
    have hRErank : 2 ≤ pRank 2 ↥(R ⊓ E) :=
      le_pRank_of_le_card hREel (k := 2) (by simpa using hREcard)
    obtain ⟨F, hFRE, hFfourRE⟩ := exists_isFourSub_of_two_le_pRank (H := R ⊓ E) hRErank
    refine ⟨F, hFRE.trans inf_le_right, hFRE.trans inf_le_left,
      ⟨(hFRE.trans inf_le_left).trans hRQ, hFfourRE.2.1, hFfourRE.2.2⟩, ?_⟩
    intro a ha f hf
    exact CFSG.GH74.GLS.Th2Sig8.mul_comm_of_isElementaryAbelian hEel (hA'E ha) (hFRE.trans inf_le_right hf)
  obtain ⟨FA, hFAE, hFAR, hFA4, hFAcomm⟩ := exists_F hA hAEA hEAfull
  obtain ⟨EB, hBEB, hEB⟩ := hext B hB
  obtain ⟨FB, hFBE, hFBR, hFB4, hFBcomm⟩ := exists_F hB hBEB hEB
  have step1 : (fun A' B' : Subgroup G => IsFourSub Q B' ∧
      ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) A FA :=
    ⟨hFA4, fun a ha f hf => CFSG.GH74.GLS.Th2Sig8.mul_comm_of_isElementaryAbelian hEAel (hAEA ha) (hFAE hf)⟩
  have step2 : (fun A' B' : Subgroup G => IsFourSub Q B' ∧
      ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) FA U :=
    ⟨hUfour, fun f hf u hu => hcentR f (hFAR hf) u hu⟩
  have step3 : (fun A' B' : Subgroup G => IsFourSub Q B' ∧
      ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) U FB :=
    ⟨hFB4, fun u hu f hf => (hcentR f (hFBR hf) u hu).symm⟩
  have step4 : (fun A' B' : Subgroup G => IsFourSub Q B' ∧
      ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) FB B :=
    ⟨hB, fun f hf b hb => CFSG.GH74.GLS.Th2Sig8.mul_comm_of_isElementaryAbelian hEB.2.1 (hFBE hf) (hBEB hb)⟩
  exact Relation.ReflTransGen.head step1
    (Relation.ReflTransGen.head step2
      (Relation.ReflTransGen.head step3
        (Relation.ReflTransGen.single step4)))


theorem isConn2_of_centralizer_pRank [Finite G] {Q : Subgroup G}
    (hQp : IsPGroup 2 ↥Q)
    (hcent : ∀ u ∈ Q, orderOf u = 2 →
      3 ≤ pRank 2 ↥(Q ⊓ Subgroup.centralizer ({u} : Set G))) :
    IsConn2 Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isConn2_of_four_extend hQp ?_
  intro A hA
  have hAfull : IsFourSub Q A := hA
  obtain ⟨hAQ, hAel, hAcard⟩ := hA
  have hQne : Q ≠ ⊥ := by
    intro hQ0
    have hAle : A ≤ ⊥ := hQ0 ▸ hAQ
    have hle := Subgroup.card_le_of_le hAle
    rw [Subgroup.card_bot] at hle
    omega
  obtain ⟨z, hzQ, hz2, hzc⟩ := exists_central_involution hQp hQne
  have hzsq : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have hz1 : z ≠ 1 := by
    intro hz1eq
    rw [hz1eq, orderOf_one] at hz2
    omega
  have hzel : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers z) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [pow_two]; exact hzsq)
  by_cases hzA : z ∈ A
  · obtain ⟨a, haA, ha1, haz⟩ : ∃ a ∈ A, a ≠ 1 ∧ a ≠ z := by
      let : Fintype ↥A := Fintype.ofFinite ↥A
      have hAcard' : Fintype.card ↥A = 4 := by
        rw [← Nat.card_eq_fintype_card]; exact hAcard
      let s : Finset ↥A := {⟨1, A.one_mem⟩, ⟨z, hzA⟩}
      have hne : (⟨1, A.one_mem⟩ : ↥A) ≠ ⟨z, hzA⟩ := by
        intro h
        exact hz1 (congrArg Subtype.val h).symm
      have hscard : s.card = 2 := by
        simp [s, hne]
      have hlt : s.card < (Finset.univ : Finset ↥A).card := by
        rw [Finset.card_univ, hAcard', hscard]
        norm_num
      obtain ⟨b, -, hbnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      refine ⟨b.1, b.2, ?_, ?_⟩
      · intro hb1
        have hb : b = ⟨1, A.one_mem⟩ := Subtype.ext (by simpa using hb1)
        exact hbnot (by simp [s, hb])
      · intro hbz
        have hb : b = ⟨z, hzA⟩ := Subtype.ext (by simpa using hbz)
        exact hbnot (by simp [s, hb])
    have haQ : a ∈ Q := hAQ haA
    have ha2 : orderOf a = 2 :=
      orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a haA) ha1
    let X : Subgroup G := Q ⊓ Subgroup.centralizer ({a} : Set G)
    have hX3 : 3 ≤ pRank 2 ↥X := hcent a haQ ha2
    obtain ⟨H, hHX, hHel, hHrank⟩ := exists_elemAbelian_pRank X
    have hH3 : 3 ≤ pRank 2 ↥H := by rw [hHrank]; exact hX3
    have hza : z ∉ Subgroup.zpowers a := by
      intro hzpow
      have h := (mem_zpowers_iff_mem_range_orderOf (x := a) (y := z)).1 hzpow
      rw [ha2] at h
      simp only [Finset.mem_image, Finset.mem_range] at h
      obtain ⟨k, hk, hka⟩ := h
      interval_cases k
      · rw [pow_zero] at hka
        exact hz1 hka.symm
      · rw [pow_one] at hka
        exact haz hka
    have hAopen : CFSG.Open.IsElemAbelian 2 A :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).1 hAel
    have hAzpowers : Subgroup.zpowers a ⊔ Subgroup.zpowers z ≤ A :=
      sup_le (Subgroup.zpowers_le.2 haA) (Subgroup.zpowers_le.2 hzA)
    have hAcard4 : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers z) = 4 := by
      have h := (CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_mem_isElemAbelian
        (p := 2) hAopen haA hzA ha2 hz2 hza).2
      simpa using h
    have hAeq : A = Subgroup.zpowers a ⊔ Subgroup.zpowers z :=
      (Subgroup.eq_of_le_of_card_ge hAzpowers (by rw [hAcard4, hAcard])).symm
    have hH_a : ∀ h ∈ H, ∀ t ∈ Subgroup.zpowers a, h * t = t * h := by
      intro h hh t ht
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      have hha : h * a = a * h := by
        have hc : h ∈ Subgroup.centralizer ({a} : Set G) := (hHX hh).2
        exact (Subgroup.mem_centralizer_iff.1 hc a (by simp)).symm
      exact (Commute.zpow_right hha m).eq
    have hH_z : ∀ h ∈ H, ∀ t ∈ Subgroup.zpowers z, h * t = t * h := by
      intro h hh t ht
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      have hhz : h * z = z * h := (hzc h (hHX hh).1).symm
      exact (Commute.zpow_right hhz m).eq
    have haz_sq : a * a = 1 := mul_self_eq_one_of_orderOf_eq_two ha2
    have hzael : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers a) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [pow_two]; exact haz_sq)
    have ha_z : ∀ t ∈ Subgroup.zpowers a, ∀ s ∈ Subgroup.zpowers z,
        t * s = s * t := by
      intro t ht s hs
      exact CFSG.GH74.GLS.Th2Sig8.mul_comm_of_isElementaryAbelian hAel
        (Subgroup.zpowers_le.2 haA ht) (Subgroup.zpowers_le.2 hzA hs)
    let E : Subgroup G := (H ⊔ Subgroup.zpowers a) ⊔ Subgroup.zpowers z
    have hE1 : CFSG.IsElementaryAbelian 2 ↥(H ⊔ Subgroup.zpowers a) :=
      isElementaryAbelian_sup hHel hzael hH_a
    have hcomm2 : ∀ x ∈ H ⊔ Subgroup.zpowers a, ∀ s ∈ Subgroup.zpowers z,
        x * s = s * x := by
      intro x hx s hs
      obtain ⟨h, hh, t, ht, rfl⟩ :=
        exists_mul_of_mem_sup_of_commute (fun x hx y hy => hH_a x hx y hy) hx
      calc h * t * s = h * (t * s) := by group
        _ = h * (s * t) := by rw [ha_z t ht s hs]
        _ = (h * s) * t := by group
        _ = (s * h) * t := by rw [hH_z h hh s hs]
        _ = s * (h * t) := by group
    have hEel : CFSG.IsElementaryAbelian 2 ↥E :=
      isElementaryAbelian_sup hE1 hzel hcomm2
    have hE1Q : H ⊔ Subgroup.zpowers a ≤ Q :=
      sup_le (hHX.trans inf_le_left) (Subgroup.zpowers_le.2 haQ)
    have hEQ : E ≤ Q := sup_le hE1Q (Subgroup.zpowers_le.2 hzQ)
    have hHleE : H ≤ E := le_sup_left.trans le_sup_left
    have hErk : 3 ≤ pRank 2 ↥E := hH3.trans (C3.Layer1.Back.pRank_mono' hHleE)
    have hAE : A ≤ E := by
      rw [hAeq]
      exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
    exact ⟨E, hAE, hEQ, hEel, hErk⟩
  · have hdisj : Disjoint A (Subgroup.zpowers z) :=
      CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint A z hz2 hzA
    have hcommAz : ∀ a ∈ A, ∀ t ∈ Subgroup.zpowers z, a * t = t * a := by
      intro a ha t ht
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      have hcomm : Commute a z := (hzc a (hAQ ha)).symm
      exact (Commute.zpow_right hcomm m).eq
    have hcd : CommDisj A (Subgroup.zpowers z) :=
      ⟨hcommAz, disjoint_iff.mp hdisj⟩
    let E : Subgroup G := A ⊔ Subgroup.zpowers z
    have hEel : CFSG.IsElementaryAbelian 2 ↥E :=
      hcd.isElementaryAbelian_sup' hAel hzel le_rfl le_rfl
    have hzrank : pRank 2 ↥(Subgroup.zpowers z) = 1 := by
      have hcardz : Nat.card ↥(Subgroup.zpowers z) = 2 := by
        rw [Nat.card_zpowers, hz2]
      have hc := C3.Layer1.Back.card_eq_two_pow_pRank hzel
      rw [hcardz] at hc
      have hpow : (2 : ℕ) ^ 1 = 2 ^ pRank 2 ↥(Subgroup.zpowers z) := by simpa using hc
      exact (Nat.pow_right_injective le_rfl hpow).symm
    have hErk : 3 ≤ pRank 2 ↥E := by
      change 3 ≤ pRank 2 ↥(A ⊔ Subgroup.zpowers z)
      have hrank := hcd.pRank_sup hAel hzel le_rfl le_rfl
      rw [pRank_of_isFourSub hAfull, hzrank] at hrank
      omega
    have hEQ : E ≤ Q := sup_le hAQ (Subgroup.zpowers_le.2 hzQ)
    exact ⟨E, le_sup_left, hEQ, hEel, hErk⟩

theorem isConn2_sylow_of_central_involution_centerless_normal
    {Γ : Type} [Group Γ] [Finite Γ] {x : Γ} {H Q : Subgroup Γ}
    (hx2 : orderOf x = 2) (hxc : x ∈ Subgroup.center Γ)
    (hH : H.Normal) (hHbar : Subgroup.center (kBar H) = ⊥)
    (hH2 : 2 ≤ CFSG.pRank 2 ↥H) (hQ : IsSylowOf 2 Q ⊤) :
    IsConn2 Q ∧ 3 ≤ CFSG.pRank 2 ↥Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxH : x ∉ H := by
    intro hxHmem
    let xH : ↥H := ⟨x, hxHmem⟩
    have hxbar_center : (QuotientGroup.mk xH : kBar H) ∈ Subgroup.center (kBar H) := by
      rw [Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H h =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          exact congrArg (fun z : ↥H => (z : kBar H))
            (Subtype.ext (Subgroup.mem_center_iff.1 hxc (h : Γ)))
    have hxbar_one : (QuotientGroup.mk xH : kBar H) = 1 := by
      rw [hHbar] at hxbar_center
      simpa using hxbar_center
    have hxcore : xH ∈ CFSG.pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff xH).mp hxbar_one
    have hdvd : orderOf xH ∣ Nat.card (CFSG.pPrimeCore 2 ↥H) :=
      Subgroup.orderOf_dvd_natCard _ hxcore
    have hxH2 : orderOf xH = 2 := by
      rw [← Subgroup.orderOf_coe (a := xH)]
      exact hx2
    have h2dvd : 2 ∣ Nat.card (CFSG.pPrimeCore 2 ↥H) := hxH2 ▸ hdvd
    have hcop : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 ↥H)) :=
      CFSG.pPrimeCore_coprime_card
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop) h2dvd
  have hQp : IsPGroup 2 ↥Q := (CFSG.ABGLocalTools.isSylowOf_iff.mp hQ).2.1
  have hQH : IsSylowOf 2 (Q ⊓ H) H :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hQ le_top
      (by rw [Subgroup.normalizer_eq_top (H := H)])
  have hrankQH : CFSG.pRank 2 ↥(Q ⊓ H) = CFSG.pRank 2 ↥H := by
    obtain ⟨S, hS⟩ := hQH
    calc CFSG.pRank 2 ↥(Q ⊓ H)
        = CFSG.pRank 2 ↥((S : Subgroup ↥H).map H.subtype) := by rw [hS]
      _ = CFSG.pRank 2 (S : Subgroup ↥H) :=
          (CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two
            (Subgroup.equivMapOfInjective (S : Subgroup ↥H) H.subtype
              H.subtype_injective)).symm
      _ = CFSG.pRank 2 ↥H := (CFSG.SectionRank.pRank_sylow S).2
  have hQHrank : 2 ≤ CFSG.pRank 2 ↥(Q ⊓ H) := by
    rw [hrankQH]; exact hH2
  obtain ⟨F, hFQH, hFfour⟩ := exists_isFourSub_of_two_le_pRank (H := Q ⊓ H) hQHrank
  have hFQ : F ≤ Q := hFQH.trans inf_le_left
  have hFfourQ : IsFourSub Q F := ⟨hFQ, hFfour.2.1, hFfour.2.2⟩
  have hNne : H.subgroupOf Q ≠ ⊥ := by
    intro hNbot
    have hcardN : Nat.card ↥(H.subgroupOf Q) = 1 := by rw [hNbot]; simp
    have hcardQH : Nat.card ↥(Q ⊓ H) = Nat.card ↥(H.subgroupOf Q) := by
      have h1 : Nat.card ↥(Q ⊓ H) = Nat.card ↥((Q ⊓ H).subgroupOf Q) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
      rw [show (Q ⊓ H).subgroupOf Q = H.subgroupOf Q by
        rw [inf_comm, Subgroup.inf_subgroupOf_right]] at h1
      exact h1
    have h4 : 4 ≤ Nat.card ↥(Q ⊓ H) := by
      calc 4 = Nat.card ↥F := hFfour.2.2.symm
        _ ≤ Nat.card ↥(Q ⊓ H) := Subgroup.card_le_of_le hFQH
    omega
  have : (H.subgroupOf Q).Normal := hH.subgroupOf Q
  have : Group.IsNilpotent ↥Q := hQp.isNilpotent
  have hMne : H.subgroupOf Q ⊓ Subgroup.center ↥Q ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hNne
  let M : Subgroup ↥Q := H.subgroupOf Q ⊓ Subgroup.center ↥Q
  have hMp : IsPGroup 2 ↥M := hQp.to_subgroup M
  obtain ⟨k, hk⟩ := hMp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hMne
    rw [← Subgroup.card_eq_one]
    simpa only [pow_zero] using hk
  have h2dvd : 2 ∣ Nat.card ↥M := by
    rw [hk]; exact dvd_pow_self 2 hk0
  obtain ⟨zM, hzM2⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  let z : Γ := zM.1.1
  have hzQ : z ∈ Q := zM.1.2
  have hzH : z ∈ H := Subgroup.mem_subgroupOf.mp zM.2.1
  have hz2 : orderOf z = 2 := by
    dsimp [z]
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hzM2
  have hzc : ∀ q ∈ Q, z * q = q * z := by
    intro q hq
    have hzc' := Subgroup.mem_center_iff.1 zM.2.2 ⟨q, hq⟩
    exact congrArg (fun w : ↥Q => (w : Γ)) hzc'.symm
  have hxQ : x ∈ Q := by
    have hxel : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers x) := by
      have hx1 : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hx2
      exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [pow_two]; exact hx1)
    have hxN : (Subgroup.zpowers x).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hxc)
    have : (Subgroup.zpowers x).Normal := hxN
    obtain ⟨S, hS⟩ := hQ
    let SΓ : Sylow 2 Γ := S.mapSurjective
      (show Function.Surjective ((⊤ : Subgroup Γ).subtype) from
        fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)
    have hSΓ : (SΓ : Subgroup Γ) = Q := by
      simpa [SΓ, Sylow.coe_mapSurjective] using hS
    have hxS : x ∈ (SΓ : Subgroup Γ) :=
      (CFSG.IsElementaryAbelian.isPGroup 2 ↥(Subgroup.zpowers x)).le_sylow_of_normal SΓ
        (Subgroup.mem_zpowers x)
    exact hSΓ ▸ hxS
  have hz1 : z ≠ 1 := by
    intro hz1eq
    rw [hz1eq, orderOf_one] at hz2
    omega
  have hzxne : z ≠ x := fun h => hxH (h ▸ hzH)
  have hxel : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers x) := by
    have hx1 : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hx2
    exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [pow_two]; exact hx1)
  have hzel : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers z) := by
    have hzsq : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
    exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [pow_two]; exact hzsq)
  have hzx : z ∉ Subgroup.zpowers x := by
    intro hzpow
    have h := (mem_zpowers_iff_mem_range_orderOf (x := x) (y := z)).1 hzpow
    rw [hx2] at h
    simp only [Finset.mem_image, Finset.mem_range] at h
    obtain ⟨k, hk, hka⟩ := h
    interval_cases k
    · rw [pow_zero] at hka
      exact hz1 hka.symm
    · rw [pow_one] at hka
      exact hzxne hka.symm
  have hcommxz : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute x z from
      (Subgroup.mem_center_iff.1 hxc z).symm) m n).eq
  have hdisjxz : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers z) :=
    CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint (Subgroup.zpowers x) z hz2 hzx
  have hcdZ : CommDisj (Subgroup.zpowers x) (Subgroup.zpowers z) :=
    ⟨hcommxz, disjoint_iff.mp hdisjxz⟩
  let Z0 : Subgroup Γ := Subgroup.zpowers x ⊔ Subgroup.zpowers z
  have hZ0el : CFSG.IsElementaryAbelian 2 ↥Z0 :=
    hcdZ.isElementaryAbelian_sup' hxel hzel le_rfl le_rfl
  have hZ0card : Nat.card ↥Z0 = 4 := by
    change Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z) = 4
    rw [hcdZ.card_sup le_rfl le_rfl, Nat.card_zpowers, Nat.card_zpowers, hx2, hz2]
  have hZ0Q : Z0 ≤ Q := by
    change Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ Q
    exact sup_le (Subgroup.zpowers_le.2 hxQ) (Subgroup.zpowers_le.2 hzQ)
  have hZ0four : IsFourSub Q Z0 := ⟨hZ0Q, hZ0el, hZ0card⟩
  have hZ0centQ : ∀ w ∈ Z0, ∀ q ∈ Q, w * q = q * w := by
    have hsub : Z0 ≤ Subgroup.centralizer (Q : Set Γ) := by
      change Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer (Q : Set Γ)
      refine sup_le ?_ ?_
      · intro a ha
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (Commute.zpow_left (show Commute x b from
          (Subgroup.mem_center_iff.1 hxc b).symm) m).eq.symm
      · intro a ha
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (Commute.zpow_left (hzc b hb) m).eq.symm
    intro w hw q hq
    exact (Subgroup.mem_centralizer_iff.1 (hsub hw) q hq).symm
  have hconn : IsConn2 Q := by
    intro A B hA hB
    have step1 : (fun A' B' : Subgroup Γ => IsFourSub Q B' ∧
        ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) A Z0 :=
      ⟨hZ0four, fun a ha w hw => (hZ0centQ w hw a (hA.1 ha)).symm⟩
    have step2 : (fun A' B' : Subgroup Γ => IsFourSub Q B' ∧
        ∀ a ∈ A', ∀ b ∈ B', a * b = b * a) Z0 B :=
      ⟨hB, fun w hw b hb => hZ0centQ w hw b (hB.1 hb)⟩
    exact Relation.ReflTransGen.head step1 (Relation.ReflTransGen.single step2)
  have hxF : x ∉ F := fun hmem => hxH (hFQH.trans inf_le_right hmem)
  have hxrank : pRank 2 ↥(Subgroup.zpowers x) = 1 := by
    have hcardx : Nat.card ↥(Subgroup.zpowers x) = 2 := by
      rw [Nat.card_zpowers, hx2]
    have hc := C3.Layer1.Back.card_eq_two_pow_pRank hxel
    rw [hcardx] at hc
    have hpow : (2 : ℕ) ^ 1 = 2 ^ pRank 2 ↥(Subgroup.zpowers x) := by simpa using hc
    exact (Nat.pow_right_injective le_rfl hpow).symm
  have hcommFx : ∀ f ∈ F, ∀ t ∈ Subgroup.zpowers x, f * t = t * f := by
    intro f hf t ht
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    exact (Commute.zpow_right (Subgroup.mem_center_iff.1 hxc f) m).eq
  have hdisjFx : Disjoint F (Subgroup.zpowers x) :=
    CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint F x hx2 hxF
  have hcdFx : CommDisj F (Subgroup.zpowers x) :=
    ⟨hcommFx, disjoint_iff.mp hdisjFx⟩
  have hExp : pRank 2 ↥(F ⊔ Subgroup.zpowers x) = 3 := by
    rw [hcdFx.pRank_sup hFfourQ.2.1 hxel le_rfl le_rfl,
      pRank_of_isFourSub hFfourQ, hxrank]
  have h3Q : 3 ≤ pRank 2 ↥Q := by
    have hEQ : F ⊔ Subgroup.zpowers x ≤ Q :=
      sup_le hFQ (Subgroup.zpowers_le.2 hxQ)
    calc 3 = pRank 2 ↥(F ⊔ Subgroup.zpowers x) := hExp.symm
      _ ≤ pRank 2 ↥Q := C3.Layer1.Back.pRank_mono' hEQ
  exact ⟨hconn, h3Q⟩

end CFSG.GH74.GLS.Th2
