module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement

namespace EvenCoverPairing

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_eq (a a' b : G) :
    ⁅a * a', b⁆ = a * ⁅a', b⁆ * a⁻¹ * ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right_eq (a b b' : G) :
    ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem conj_eq_commutatorElement_mul (a b : G) : a * b * a⁻¹ = ⁅a, b⁆ * b := by
  simp only [commutatorElement_def]
  group

theorem conj_commutatorElement (g a b : G) :
    ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = g * ⁅a, b⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_eq_one_of_mem_center_left {a : G} (ha : a ∈ center G) (b : G) :
    ⁅a, b⁆ = 1 := by
  rw [commutatorElement_def, (mem_center_iff.mp ha b).symm]
  group

theorem commutatorElement_eq_one_of_mem_center_right (a : G) {b : G} (hb : b ∈ center G) :
    ⁅a, b⁆ = 1 := by
  rw [← commutatorElement_inv, commutatorElement_eq_one_of_mem_center_left hb, inv_one]

theorem conj_eq_self_of_mem_center (g : G) {a : G} (ha : a ∈ center G) : g * a * g⁻¹ = a := by
  rw [mem_center_iff.mp ha g, mul_inv_cancel_right]

theorem conj_mem_commutator {H K : Subgroup G} {g : G} (hH : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hK : ∀ x ∈ K, g * x * g⁻¹ ∈ K) {x : G} (hx : x ∈ ⁅H, K⁆) : g * x * g⁻¹ ∈ ⁅H, K⁆ := by
  have h := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  rw [map_commutator] at h
  refine commutator_mono ?_ ?_ h
  · rintro _ ⟨y, hy, rfl⟩
    simpa using hH y hy
  · rintro _ ⟨y, hy, rfl⟩
    simpa using hK y hy

theorem abelianization_of_eq_iff {Q : Subgroup G} (u u' : Q) :
    Abelianization.of u = Abelianization.of u' ↔ (u : G)⁻¹ * u' ∈ ⁅Q, Q⁆ := by
  have h : (u : G)⁻¹ * u' = Q.subtype (u⁻¹ * u') := rfl
  rw [h, ← map_subtype_commutator, mem_map_iff_mem Q.subtype_injective, ← Abelianization.ker_of,
    MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

theorem exists_zmod_two_functional {S D : Subgroup G} (hDS : D ≤ S)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x ^ 2 ∈ D) {c : G} (hcS : c ∈ S)
    (hcD : c ∉ D) :
    ∃ ρ : G → ZMod 2, (∀ x ∈ S, ∀ y ∈ S, ρ (x * y) = ρ x + ρ y) ∧ (∀ d ∈ D, ρ d = 0) ∧
      ρ c ≠ 0 := by
  classical
  let _ : CommGroup S :=
    { (inferInstance : Group S) with mul_comm := fun a b => Subtype.ext (hS a a.2 b b.2) }
  let D' : Subgroup S := D.subgroupOf S
  have h2 : ∀ a : Additive (S ⧸ D'), 2 • a = 0 := by
    intro a
    induction a using Additive.rec with
    | ofMul a =>
    induction a using QuotientGroup.induction_on with
    | H x =>
    rw [← ofMul_pow, ← QuotientGroup.mk_pow, ← ofMul_one]
    congr 1
    exact (QuotientGroup.eq_one_iff (N := D') _).mpr (hsq x x.2)
  let _ : Module (ZMod 2) (Additive (S ⧸ D')) := AddCommGroup.zmodModule h2
  have hne : Additive.ofMul (QuotientGroup.mk ⟨c, hcS⟩ : S ⧸ D') ≠ 0 := by
    intro h
    exact hcD ((QuotientGroup.eq_one_iff (N := D') _).mp (congrArg Additive.toMul h))
  have := (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).not.mpr hne
  push Not at this
  obtain ⟨φ, hφ⟩ := this
  refine ⟨fun x => if h : x ∈ S then φ (Additive.ofMul (QuotientGroup.mk ⟨x, h⟩ : S ⧸ D'))
    else 0, fun x hx y hy => ?_, fun d hd => ?_, ?_⟩
  · simp only [hx, hy, S.mul_mem hx hy, dite_true]
    rw [← map_add, ← ofMul_mul, ← QuotientGroup.mk_mul]
    rfl
  · simp only [hDS hd, dite_true]
    rw [show (QuotientGroup.mk ⟨d, hDS hd⟩ : S ⧸ D') = 1 from
      (QuotientGroup.eq_one_iff (N := D') _).mpr hd, ofMul_one, map_zero]
  · simpa only [hcS, dite_true] using hφ

end Commutators

section Preimage

variable {E J : Type*} [Group E] [Group J] {η : E →* J} {Q : Subgroup J}

theorem map_comap_commutator (hη : Function.Surjective η) :
    ⁅Q.comap η, Q.comap η⁆.map η = ⁅Q, Q⁆ := by
  rw [map_commutator, map_comap_eq_self_of_surjective hη]

theorem commutator_commutator_comap_le_ker (hη : Function.Surjective η)
    (hQ : ⁅⁅Q, Q⁆, Q⁆ = ⊥) : ⁅⁅Q.comap η, Q.comap η⁆, Q.comap η⁆ ≤ η.ker := by
  rw [← Subgroup.map_eq_bot_iff, map_commutator, map_comap_commutator hη,
    map_comap_eq_self_of_surjective hη, hQ]

theorem mem_commutator_comap_iff (hη : Function.Surjective η)
    (hker : η.ker ≤ ⁅Q.comap η, Q.comap η⁆) {a : E} :
    a ∈ ⁅Q.comap η, Q.comap η⁆ ↔ η a ∈ ⁅Q, Q⁆ := by
  constructor
  · intro h
    rw [← map_comap_commutator hη]
    exact mem_map_of_mem η h
  · intro h
    rw [← map_comap_commutator hη] at h
    obtain ⟨r, hr, hra⟩ := h
    have hk : r⁻¹ * a ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hra, inv_mul_cancel]
    have := mul_mem hr (hker hk)
    rwa [mul_inv_cancel_left] at this

theorem commutator_commutator_comap_eq_bot
    (hD : ⁅⁅Q.comap η, Q.comap η⁆, Q.comap η⁆ ≤ center E) :
    ⁅⁅Q.comap η, Q.comap η⁆, ⁅Q.comap η, Q.comap η⁆⁆ = ⊥ := by
  have hD' : ⁅⁅⁅Q.comap η, Q.comap η⁆, Q.comap η⁆, Q.comap η⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    exact hD.trans (center_le_centralizer _)
  refine commutator_commutator_eq_bot_of_rotate ?_ hD'
  rwa [commutator_comm (Q.comap η) ⁅Q.comap η, Q.comap η⁆]

end Preimage

section Lifts

variable {E J : Type*} [Group E] [Group J] {η : E →* J} {Q : Subgroup J}

theorem exists_lift_abelianization (hη : Function.Surjective η) (x : Abelianization Q) :
    ∃ s : E, ∃ hs : η s ∈ Q, Abelianization.of (⟨η s, hs⟩ : Q) = x := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨s, hs⟩ := hη q
  exact ⟨s, hs ▸ q.2, by rw [show (⟨η s, hs ▸ q.2⟩ : Q) = q from Subtype.ext hs]; rfl⟩

theorem inv_mul_mem_of_abelianization_of_eq (hη : Function.Surjective η)
    (hker : η.ker ≤ ⁅Q.comap η, Q.comap η⁆) {a a' : E} (ha : η a ∈ Q) (ha' : η a' ∈ Q)
    (h : Abelianization.of (⟨η a, ha⟩ : Q) = Abelianization.of ⟨η a', ha'⟩) :
    a⁻¹ * a' ∈ ⁅Q.comap η, Q.comap η⁆ := by
  rw [abelianization_of_eq_iff] at h
  rw [mem_commutator_comap_iff hη hker, map_mul, map_inv]
  exact h

theorem conj_inv_mul_mem_of_lift (hη : Function.Surjective η)
    (hker : η.ker ≤ ⁅Q.comap η, Q.comap η⁆) {t : J} (htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q) {g : E}
    (hg : η g = t) {s s' : E} (hs : η s ∈ Q) (hs' : η s' ∈ Q) {a : J} (ha : a ∈ Q)
    (hta : t * a * t⁻¹ ∈ Q) (h1 : Abelianization.of (⟨η s, hs⟩ : Q) = Abelianization.of ⟨a, ha⟩)
    (h2 : Abelianization.of (⟨η s', hs'⟩ : Q) = Abelianization.of ⟨t * a * t⁻¹, hta⟩) :
    (g * s * g⁻¹)⁻¹ * s' ∈ ⁅Q.comap η, Q.comap η⁆ := by
  rw [abelianization_of_eq_iff] at h1 h2
  rw [mem_commutator_comap_iff hη hker]
  simp only [map_mul, map_inv, hg] at h1 h2 ⊢
  have h3 := inv_mem h2
  rw [mul_inv_rev, inv_inv] at h3
  rw [show (t * η s * t⁻¹)⁻¹ * η s' = t * ((η s)⁻¹ * a) * t⁻¹ * ((t * a * t⁻¹)⁻¹ * η s') by
    group]
  exact mul_mem (conj_mem_commutator htQ htQ h1) h3

theorem inv_mul_mem_of_abelianization_of_eq_mul (hη : Function.Surjective η)
    (hker : η.ker ≤ ⁅Q.comap η, Q.comap η⁆) {s s' s'' : E} (hs : η s ∈ Q) (hs' : η s' ∈ Q)
    (hs'' : η s'' ∈ Q) (h : Abelianization.of (⟨η s'', hs''⟩ : Q) =
      Abelianization.of (⟨η s, hs⟩ : Q) * Abelianization.of (⟨η s', hs'⟩ : Q)) :
    (s * s')⁻¹ * s'' ∈ ⁅Q.comap η, Q.comap η⁆ := by
  refine inv_mul_mem_of_abelianization_of_eq hη hker ((Q.comap η).mul_mem hs hs') hs'' ?_
  have e : (⟨η (s * s'), (Q.comap η).mul_mem hs hs'⟩ : Q) = ⟨η s, hs⟩ * ⟨η s', hs'⟩ :=
    Subtype.ext (map_mul η _ _)
  rw [e, map_mul, h]

end Lifts

section Averaging

variable {E J : Type*} [Group E] [Group J]

theorem commutator_le_self (P : Subgroup E) : ⁅P, P⁆ ≤ P :=
  commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem sq_mem_commutator_commutator {P : Subgroup E} (hDcen : ⁅⁅P, P⁆, P⁆ ≤ center E)
    (hsqP : ∀ b ∈ P, b ^ 2 ∈ ⁅P, P⁆) (hcomm : ∀ x ∈ ⁅P, P⁆, ∀ y ∈ ⁅P, P⁆, x * y = y * x) :
    ∀ x ∈ ⁅P, P⁆, x ^ 2 ∈ ⁅⁅P, P⁆, P⁆ := by
  intro x hx
  rw [Subgroup.commutator_def P P] at hx
  induction hx using closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have hab : ⁅a, b⁆ ∈ ⁅P, P⁆ := commutator_mem_commutator ha hb
    have hz : ⁅⁅a, b⁆, b⁆ ∈ ⁅⁅P, P⁆, P⁆ := commutator_mem_commutator hab hb
    have h1 : ⁅a, b ^ 2⁆ = ⁅a, b⁆ * (⁅⁅a, b⁆, b⁆⁻¹ * ⁅a, b⁆) := by
      rw [sq, commutatorElement_mul_right_eq, conj_eq_commutatorElement_mul, commutatorElement_inv]
    have hc := mem_center_iff.mp (inv_mem (hDcen hz)) ⁅a, b⁆
    have h2 : ⁅a, b⁆ ^ 2 = ⁅⁅a, b⁆, b⁆ * ⁅a, b ^ 2⁆ := by
      calc ⁅a, b⁆ ^ 2 = ⁅⁅a, b⁆, b⁆ * (⁅⁅a, b⁆, b⁆⁻¹ * ⁅a, b⁆ * ⁅a, b⁆) := by rw [sq]; group
        _ = ⁅⁅a, b⁆, b⁆ * (⁅a, b⁆ * ⁅⁅a, b⁆, b⁆⁻¹ * ⁅a, b⁆) := by rw [hc]
        _ = ⁅⁅a, b⁆, b⁆ * ⁅a, b ^ 2⁆ := by rw [h1]; group
    rw [h2]
    refine mul_mem hz ?_
    rw [← commutatorElement_inv]
    exact inv_mem (commutator_mem_commutator (hsqP b hb) ha)
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxP : x ∈ ⁅P, P⁆ := by rw [Subgroup.commutator_def]; exact hx
    have hyP : y ∈ ⁅P, P⁆ := by rw [Subgroup.commutator_def]; exact hy
    rw [(show Commute x y from hcomm x hxP y hyP).mul_pow]
    exact mul_mem ihx ihy
  | inv x hx ihx =>
    have hxP : x ∈ ⁅P, P⁆ := by rw [Subgroup.commutator_def]; exact hx
    rw [inv_pow]
    exact inv_mem ihx

theorem conj_eq_of_map_eq {η : E →* J} (hcen : η.ker ≤ center E) {g g' : E} (h : η g = η g')
    (x : E) : g * x * g⁻¹ = g' * x * g'⁻¹ := by
  have hk : g⁻¹ * g' ∈ η.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨k, hk', rfl⟩ : ∃ k ∈ η.ker, g' = g * k := ⟨g⁻¹ * g', hk, by group⟩
  have hkx : k * x = x * k := (mem_center_iff.mp (hcen hk') x).symm
  calc g * x * g⁻¹ = g * (x * k) * k⁻¹ * g⁻¹ := by group
    _ = g * k * x * (g * k)⁻¹ := by rw [← hkx]; group

variable {η : E →* J} {Q : Subgroup J}

theorem ker_le_commutator_commutator_comap [Finite J] (hη : Function.Surjective η)
    (hcen : η.ker ≤ center E) (hker : η.ker ≤ ⁅Q.comap η, Q.comap η⁆)
    (hD : ⁅⁅Q.comap η, Q.comap η⁆, Q.comap η⁆ ≤ η.ker) (hVsq : ∀ a ∈ Q, a ^ 2 ∈ ⁅Q, Q⁆)
    {T : Subgroup J} (hT : T ≤ normalizer (Q : Set J)) (hTodd : Odd (Nat.card T))
    (hpair : ∀ f : Abelianization Q → Abelianization Q → ZMod 2,
      (∀ x x' y, f (x * x') y = f x y + f x' y) → (∀ x y y', f x (y * y') = f x y + f x y') →
      (∀ t ∈ T, ∀ (a b : J) (ha : a ∈ Q) (hb : b ∈ Q) (hta : t * a * t⁻¹ ∈ Q)
        (htb : t * b * t⁻¹ ∈ Q), f (Abelianization.of ⟨t * a * t⁻¹, hta⟩)
          (Abelianization.of ⟨t * b * t⁻¹, htb⟩) =
          f (Abelianization.of ⟨a, ha⟩) (Abelianization.of ⟨b, hb⟩)) → f = 0) :
    η.ker ≤ ⁅⁅Q.comap η, Q.comap η⁆, Q.comap η⁆ := by
  classical
  set P := Q.comap η with hP
  have hDcen : ⁅⁅P, P⁆, P⁆ ≤ center E := hD.trans hcen
  have hcomm : ∀ x ∈ ⁅P, P⁆, ∀ y ∈ ⁅P, P⁆, x * y = y * x := fun x hx y hy => by
    have hxy : ⁅x, y⁆ ∈ ⁅⁅P, P⁆, ⁅P, P⁆⁆ := commutator_mem_commutator hx hy
    rw [commutator_commutator_comap_eq_bot hDcen, mem_bot] at hxy
    exact commutatorElement_eq_one_iff_mul_comm.mp hxy
  have hPP' : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ ⁅P, P⁆ := fun a ha b hb => commutator_mem_commutator ha hb
  have hDmem : ∀ r ∈ ⁅P, P⁆, ∀ b ∈ P, ⁅r, b⁆ ∈ ⁅⁅P, P⁆, P⁆ := fun r hr b hb =>
    commutator_mem_commutator hr hb
  have hDmem' : ∀ a ∈ P, ∀ r ∈ ⁅P, P⁆, ⁅a, r⁆ ∈ ⁅⁅P, P⁆, P⁆ := fun a ha r hr => by
    rw [← commutatorElement_inv]
    exact inv_mem (hDmem r hr a ha)
  have hDP' : ⁅⁅P, P⁆, P⁆ ≤ ⁅P, P⁆ := hD.trans hker
  have hP'P : ⁅P, P⁆ ≤ P := commutator_le_self P
  have hsqP : ∀ b ∈ P, b ^ 2 ∈ ⁅P, P⁆ := fun b hb =>
    (mem_commutator_comap_iff hη hker).mpr (by rw [map_pow]; exact hVsq _ hb)
  have hsq := sq_mem_commutator_commutator hDcen hsqP hcomm
  intro c hc
  by_contra hcD
  obtain ⟨ρ, hρadd, hρD, hρc⟩ := exists_zmod_two_functional hDP' hcomm hsq (hker hc) hcD
  choose tl htl using fun t : T => hη t
  have hTQ : ∀ t ∈ T, ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := fun t ht x hx =>
    (mem_normalizer_iff.mp (hT ht) x).mp hx
  have htlP : ∀ t : T, ∀ x ∈ P, tl t * x * (tl t)⁻¹ ∈ P := fun t x hx => by
    change η (tl t * x * (tl t)⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv, htl]
    exact hTQ t t.2 _ hx
  have htlP' : ∀ t : T, ∀ x ∈ ⁅P, P⁆, tl t * x * (tl t)⁻¹ ∈ ⁅P, P⁆ := fun t x hx =>
    conj_mem_commutator (htlP t) (htlP t) hx
  have htlD : ∀ t : T, ∀ x ∈ ⁅⁅P, P⁆, P⁆, tl t * x * (tl t)⁻¹ ∈ ⁅⁅P, P⁆, P⁆ := fun t x hx =>
    conj_mem_commutator (htlP' t) (htlP t) hx
  have : Fintype T := Fintype.ofFinite T
  set ρT : E → ZMod 2 := fun x => ∑ t : T, ρ (tl t * x * (tl t)⁻¹) with hρT
  have hρTadd : ∀ x ∈ ⁅P, P⁆, ∀ y ∈ ⁅P, P⁆, ρT (x * y) = ρT x + ρT y := fun x hx y hy => by
    simp only [hρT, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show tl t * (x * y) * (tl t)⁻¹ = (tl t * x * (tl t)⁻¹) * (tl t * y * (tl t)⁻¹) by group]
    exact hρadd _ (htlP' t x hx) _ (htlP' t y hy)
  have hρTD : ∀ d ∈ ⁅⁅P, P⁆, P⁆, ρT d = 0 := fun d hd =>
    Finset.sum_eq_zero fun t _ => hρD _ (htlD t d hd)
  have hρTc : ρT c = ρ c := by
    simp only [hρT, conj_eq_self_of_mem_center _ (hcen hc), Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, nsmul_eq_mul, ZMod.natCast_eq_one_iff_odd.mpr hTodd, one_mul]
  have hρTconj : ∀ s : T, ∀ x, ρT (tl s * x * (tl s)⁻¹) = ρT x := fun s x => by
    simp only [hρT]
    refine Fintype.sum_equiv (Equiv.mulRight s) _ _ fun t => ?_
    rw [Equiv.coe_mulRight, conj_eq_of_map_eq hcen (g := tl (t * s)) (g' := tl t * tl s)
      (by rw [map_mul, htl, htl, htl, Subgroup.coe_mul]) x]
    congr 1
    group
  have hg_left : ∀ a ∈ P, ∀ a' ∈ P, ∀ b ∈ P, ρT ⁅a * a', b⁆ = ρT ⁅a, b⁆ + ρT ⁅a', b⁆ := by
    intro a ha a' ha' b hb
    have h1 := hPP' a' ha' b hb
    have h2 := hDmem' a ha _ h1
    rw [commutatorElement_mul_left_eq, conj_eq_commutatorElement_mul,
      hρTadd _ (mul_mem (hDP' h2) h1) _ (hPP' a ha b hb), hρTadd _ (hDP' h2) _ h1, hρTD _ h2,
      zero_add, add_comm]
  have hg_right : ∀ a ∈ P, ∀ b ∈ P, ∀ b' ∈ P, ρT ⁅a, b * b'⁆ = ρT ⁅a, b⁆ + ρT ⁅a, b'⁆ := by
    intro a ha b hb b' hb'
    have h1 := hPP' a ha b' hb'
    have h2 := hDmem' b hb _ h1
    rw [commutatorElement_mul_right_eq, conj_eq_commutatorElement_mul,
      hρTadd _ (hPP' a ha b hb) _ (mul_mem (hDP' h2) h1), hρTadd _ (hDP' h2) _ h1, hρTD _ h2,
      zero_add]
  have hg_wd : ∀ a ∈ P, ∀ a' ∈ P, ∀ b ∈ P, ∀ b' ∈ P, a⁻¹ * a' ∈ ⁅P, P⁆ → b⁻¹ * b' ∈ ⁅P, P⁆ →
      ρT ⁅a', b'⁆ = ρT ⁅a, b⁆ := by
    intro a ha a' ha' b hb b' hb' hra hrb
    obtain ⟨r, hr, rfl⟩ : ∃ r ∈ ⁅P, P⁆, a' = a * r := ⟨a⁻¹ * a', hra, by group⟩
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ ⁅P, P⁆, b' = b * u := ⟨b⁻¹ * b', hrb, by group⟩
    rw [hg_left a ha r (hP'P hr) _ hb', hρTD _ (hDmem r hr _ hb'), add_zero,
      hg_right a ha b hb u (hP'P hu), hρTD _ (hDmem' a ha u hu), add_zero]
  choose sV hsV hsVx using exists_lift_abelianization (Q := Q) hη
  have himg := fun (a : E) (ha : η a ∈ Q) (a' : E) (ha' : η a' ∈ Q) =>
    inv_mul_mem_of_abelianization_of_eq hη hker ha ha'
  let f : Abelianization Q → Abelianization Q → ZMod 2 := fun x y => ρT ⁅sV x, sV y⁆
  have hmul : ∀ x x' : Abelianization Q, (sV x * sV x')⁻¹ * sV (x * x') ∈ ⁅P, P⁆ := by
    intro x x'
    refine himg _ (P.mul_mem (hsV x) (hsV x')) _ (hsV (x * x')) ?_
    have e : (⟨η (sV x * sV x'), P.mul_mem (hsV x) (hsV x')⟩ : Q) =
        ⟨η (sV x), hsV x⟩ * ⟨η (sV x'), hsV x'⟩ := Subtype.ext (map_mul η _ _)
    rw [e, map_mul, hsVx, hsVx, hsVx]
  have hf1 : ∀ x x' y, f (x * x') y = f x y + f x' y := by
    intro x x' y
    rw [← hg_left _ (hsV x) _ (hsV x') _ (hsV y)]
    exact hg_wd _ (P.mul_mem (hsV x) (hsV x')) _ (hsV (x * x')) _ (hsV y) _ (hsV y) (hmul x x')
      (by rw [inv_mul_cancel]; exact one_mem _)
  have hf2 : ∀ x y y', f x (y * y') = f x y + f x y' := by
    intro x y y'
    rw [← hg_right _ (hsV x) _ (hsV y) _ (hsV y')]
    exact hg_wd _ (hsV x) _ (hsV x) _ (P.mul_mem (hsV y) (hsV y')) _ (hsV (y * y'))
      (by rw [inv_mul_cancel]; exact one_mem _) (hmul y y')
  have hconjV : ∀ t (ht : t ∈ T) (a : J) (ha : a ∈ Q) (hta : t * a * t⁻¹ ∈ Q),
      (tl ⟨t, ht⟩ * sV (Abelianization.of ⟨a, ha⟩) * (tl ⟨t, ht⟩)⁻¹)⁻¹ *
        sV (Abelianization.of ⟨t * a * t⁻¹, hta⟩) ∈ ⁅P, P⁆ := fun t ht a ha hta =>
    conj_inv_mul_mem_of_lift hη hker (hTQ t ht) (htl ⟨t, ht⟩) (hsV _) (hsV _) ha hta (hsVx _)
      (hsVx _)
  have hf3 : ∀ t ∈ T, ∀ (a b : J) (ha : a ∈ Q) (hb : b ∈ Q) (hta : t * a * t⁻¹ ∈ Q)
      (htb : t * b * t⁻¹ ∈ Q), f (Abelianization.of ⟨t * a * t⁻¹, hta⟩)
        (Abelianization.of ⟨t * b * t⁻¹, htb⟩) =
        f (Abelianization.of ⟨a, ha⟩) (Abelianization.of ⟨b, hb⟩) := by
    intro t ht a b ha hb hta htb
    change ρT ⁅_, _⁆ = ρT ⁅_, _⁆
    rw [← hρTconj ⟨t, ht⟩ ⁅sV (Abelianization.of ⟨a, ha⟩), sV (Abelianization.of ⟨b, hb⟩)⁆,
      ← conj_commutatorElement]
    exact hg_wd _ (htlP ⟨t, ht⟩ _ (hsV _)) _ (hsV _) _ (htlP ⟨t, ht⟩ _ (hsV _)) _ (hsV _)
      (hconjV t ht a ha hta) (hconjV t ht b hb htb)
  have hf0 := hpair f hf1 hf2 hf3
  have hgab : ∀ a ∈ P, ∀ b ∈ P, ρT ⁅a, b⁆ = 0 := by
    intro a ha b hb
    have h := congrFun (congrFun hf0 (Abelianization.of ⟨η a, ha⟩)) (Abelianization.of ⟨η b, hb⟩)
    change ρT ⁅_, _⁆ = 0 at h
    rw [← h]
    exact (hg_wd _ ha _ (hsV _) _ hb _ (hsV _) (himg _ ha _ (hsV _) (hsVx _).symm)
      (himg _ hb _ (hsV _) (hsVx _).symm)).symm
  have hρT0 : ∀ x ∈ ⁅P, P⁆, ρT x = 0 := by
    intro x hx
    rw [Subgroup.commutator_def] at hx
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact hgab a ha b hb
    | one => exact hρTD 1 (one_mem _)
    | mul x y hx hy ihx ihy =>
      have hxP : x ∈ ⁅P, P⁆ := by rw [Subgroup.commutator_def]; exact hx
      have hyP : y ∈ ⁅P, P⁆ := by rw [Subgroup.commutator_def]; exact hy
      rw [hρTadd x hxP y hyP, ihx, ihy, add_zero]
    | inv x hx ihx =>
      have hxP : x ∈ ⁅P, P⁆ := by rw [Subgroup.commutator_def]; exact hx
      have h := hρTadd x hxP x⁻¹ (inv_mem hxP)
      rw [mul_inv_cancel, hρTD 1 (one_mem _), ihx, zero_add] at h
      exact h.symm
  exact hρc (hρTc ▸ hρT0 c (hker hc))

end Averaging

section Pairing

variable {E J : Type*} [Group E] [Group J]

open CFSG.Assembly in
theorem central_cover_kernel_pairing_of_ker_le [Finite J] {η : E →* J}
    (hη : Function.Surjective η) (hcen : η.ker ≤ center E) {Q : Subgroup J}
    (hker : η.ker ≤ ⁅Q.comap η, Q.comap η⁆) (hQ : ⁅⁅Q, Q⁆, Q⁆ = ⊥)
    (hVsq : ∀ a ∈ Q, a ^ 2 ∈ ⁅Q, Q⁆) {T : Subgroup J} (hT : T ≤ normalizer (Q : Set J))
    (hTodd : Odd (Nat.card T))
    (hpair : ∀ f : Abelianization Q → Abelianization Q → ZMod 2,
      (∀ x x' y, f (x * x') y = f x y + f x' y) → (∀ x y y', f x (y * y') = f x y + f x y') →
      (∀ t ∈ T, ∀ (a b : J) (ha : a ∈ Q) (hb : b ∈ Q) (hta : t * a * t⁻¹ ∈ Q)
        (htb : t * b * t⁻¹ ∈ Q), f (Abelianization.of ⟨t * a * t⁻¹, hta⟩)
          (Abelianization.of ⟨t * b * t⁻¹, htb⟩) =
          f (Abelianization.of ⟨a, ha⟩) (Abelianization.of ⟨b, hb⟩)) → f = 0) :
    η.ker = ⁅⁅Q.comap η, Q.comap η⁆, Q.comap η⁆ ∧ IsElemAbelian 2 η.ker ∧
    IsMulCommutative ↥⁅Q.comap η, Q.comap η⁆ ∧ ⁅Q.comap η, Q.comap η⁆.map η = ⁅Q, Q⁆ ∧
    Function.Bijective (Abelianization.map (η.subgroupComap Q)) ∧
    ∃ β : ↥⁅Q, Q⁆ → Abelianization Q → η.ker,
      (∀ r ∈ ⁅Q.comap η, Q.comap η⁆, ∀ (s : E) (hs : η s ∈ Q) (hr : η r ∈ ⁅Q, Q⁆),
        (β ⟨η r, hr⟩ (Abelianization.of ⟨η s, hs⟩) : E) = ⁅r, s⁆) ∧
      (∀ w w' v, β (w * w') v = β w v * β w' v) ∧ (∀ w v v', β w (v * v') = β w v * β w v') ∧
      closure (Set.range fun p : ↥⁅Q, Q⁆ × Abelianization Q => (β p.1 p.2 : E)) = η.ker ∧
      (∀ t ∈ T, ∀ (w : J) (hw : w ∈ ⁅Q, Q⁆) (htw : t * w * t⁻¹ ∈ ⁅Q, Q⁆) (a : J) (ha : a ∈ Q)
        (hta : t * a * t⁻¹ ∈ Q), β ⟨t * w * t⁻¹, htw⟩ (Abelianization.of ⟨t * a * t⁻¹, hta⟩) =
          β ⟨w, hw⟩ (Abelianization.of ⟨a, ha⟩)) ∧
      ∀ (a b c : J) (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q) (hab : ⁅a, b⁆ ∈ ⁅Q, Q⁆)
        (hbc : ⁅b, c⁆ ∈ ⁅Q, Q⁆) (hca : ⁅c, a⁆ ∈ ⁅Q, Q⁆),
        β ⟨⁅a, b⁆, hab⟩ (Abelianization.of ⟨c, hc⟩) * β ⟨⁅b, c⁆, hbc⟩ (Abelianization.of ⟨a, ha⟩) *
          β ⟨⁅c, a⁆, hca⟩ (Abelianization.of ⟨b, hb⟩) = 1 := by
  classical
  set P := Q.comap η with hP
  have hD : ⁅⁅P, P⁆, P⁆ ≤ η.ker := commutator_commutator_comap_le_ker hη hQ
  have hCD : η.ker = ⁅⁅P, P⁆, P⁆ :=
    le_antisymm (ker_le_commutator_commutator_comap hη hcen hker hD hVsq hT hTodd hpair) hD
  have hDcen : ⁅⁅P, P⁆, P⁆ ≤ center E := hD.trans hcen
  have hcomm1 : ∀ x ∈ ⁅P, P⁆, ∀ y ∈ ⁅P, P⁆, ⁅x, y⁆ = 1 := fun x hx y hy => by
    have hxy : ⁅x, y⁆ ∈ ⁅⁅P, P⁆, ⁅P, P⁆⁆ := commutator_mem_commutator hx hy
    rwa [commutator_commutator_comap_eq_bot hDcen, mem_bot] at hxy
  have hcomm : ∀ x ∈ ⁅P, P⁆, ∀ y ∈ ⁅P, P⁆, x * y = y * x := fun x hx y hy =>
    commutatorElement_eq_one_iff_mul_comm.mp (hcomm1 x hx y hy)
  have hPP' : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ ⁅P, P⁆ := fun a ha b hb => commutator_mem_commutator ha hb
  have hcenD : ∀ r ∈ ⁅P, P⁆, ∀ s ∈ P, ⁅r, s⁆ ∈ center E := fun r hr s hs =>
    hDcen (commutator_mem_commutator hr hs)
  have hsqP : ∀ b ∈ P, b ^ 2 ∈ ⁅P, P⁆ := fun b hb =>
    (mem_commutator_comap_iff hη hker).mpr (by rw [map_pow]; exact hVsq _ hb)
  have hwd : ∀ r ∈ ⁅P, P⁆, ∀ r' ∈ ⁅P, P⁆, η r = η r' → ∀ s ∈ P, ∀ s' ∈ P,
      s⁻¹ * s' ∈ ⁅P, P⁆ → ⁅r', s'⁆ = ⁅r, s⁆ := by
    intro r hr r' hr' hrr s hs s' hs' hss
    have hk : r⁻¹ * r' ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrr, inv_mul_cancel]
    obtain ⟨k, hk', rfl⟩ : ∃ k ∈ η.ker, r' = r * k := ⟨r⁻¹ * r', hk, by group⟩
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ ⁅P, P⁆, s' = s * u := ⟨s⁻¹ * s', hss, by group⟩
    rw [commutatorElement_mul_left_eq, commutatorElement_eq_one_of_mem_center_left (hcen hk'),
      mul_one, mul_inv_cancel, one_mul, commutatorElement_mul_right_eq, hcomm1 r hr u hu,
      mul_one, mul_inv_cancel, mul_one]
  have hWlift : ∀ w : ↥⁅Q, Q⁆, ∃ r ∈ ⁅P, P⁆, η r = w := fun w => by
    obtain ⟨r, hr, h⟩ := (map_comap_commutator hη).ge w.2
    exact ⟨r, hr, h⟩
  choose rW hrW hηrW using hWlift
  choose sV hsV hsVx using exists_lift_abelianization (Q := Q) hη
  let β : ↥⁅Q, Q⁆ → Abelianization Q → η.ker := fun w v =>
    ⟨⁅rW w, sV v⁆, hD (commutator_mem_commutator (hrW w) (hsV v))⟩
  have hβ : ∀ w v, (β w v : E) = ⁅rW w, sV v⁆ := fun _ _ => rfl
  have hform : ∀ r ∈ ⁅P, P⁆, ∀ (s : E) (hs : η s ∈ Q) (w : ↥⁅Q, Q⁆), η r = w →
      ∀ v, Abelianization.of (⟨η s, hs⟩ : Q) = v → (β w v : E) = ⁅r, s⁆ := by
    intro r hr s hs w hw v hv
    rw [hβ]
    exact hwd r hr (rW w) (hrW w) (hw.trans (hηrW w).symm) s hs (sV v) (hsV v)
      (inv_mul_mem_of_abelianization_of_eq hη hker hs (hsV v) (by rw [hsVx, hv]))
  refine ⟨hCD, ⟨⟨⟨fun a b => Subtype.ext (mem_center_iff.mp (hcen b.2) a)⟩⟩, fun x hx => ?_⟩,
    ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, map_comap_commutator hη, ⟨?_, ?_⟩,
    β, fun r hr s hs hr' => hform r hr s hs _ rfl _ rfl, fun w w' v => ?_, fun w v v' => ?_, ?_,
    fun t ht w hw htw a ha hta => ?_, fun a b c ha hb hc hab hbc hca => ?_⟩
  ·
    rw [hCD, Subgroup.commutator_def] at hx
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨r, hr, s, hs, rfl⟩ := hx
      have h := commutatorElement_mul_right_eq r s s
      rw [conj_eq_self_of_mem_center _ (hcenD r hr s hs), ← sq, ← sq,
        hcomm1 r hr _ (hsqP s hs)] at h
      exact h.symm
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      have hxD : x ∈ ⁅⁅P, P⁆, P⁆ := by rw [Subgroup.commutator_def]; exact hx
      rw [(show Commute x y from (mem_center_iff.mp (hDcen hxD) y).symm).mul_pow, ihx, ihy,
        one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  ·
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H p =>
    change Abelianization.map _ (Abelianization.of p) = 1 at hx
    rw [Abelianization.map_of, ← map_one Abelianization.of, abelianization_of_eq_iff] at hx
    have hp : (p : E) ∈ ⁅P, P⁆ := by
      rw [mem_commutator_comap_iff hη hker]
      have hx' : (η (p : E))⁻¹ * 1 ∈ ⁅Q, Q⁆ := hx
      simpa using hx'
    change Abelianization.of p = 1
    rw [← map_one Abelianization.of, abelianization_of_eq_iff]
    simpa using hp
  ·
    intro y
    obtain ⟨s, hs, hsy⟩ := exists_lift_abelianization (Q := Q) hη y
    exact ⟨Abelianization.of ⟨s, hs⟩, by rw [Abelianization.map_of]; exact hsy⟩
  ·
    apply Subtype.ext
    rw [Subgroup.coe_mul, hβ, hβ, hβ, hwd (rW w * rW w') (mul_mem (hrW w) (hrW w'))
      (rW (w * w')) (hrW _) (by rw [map_mul, hηrW, hηrW, hηrW, Subgroup.coe_mul]) (sV v)
      (hsV v) (sV v) (hsV v) (by rw [inv_mul_cancel]; exact one_mem _),
      commutatorElement_mul_left_eq, conj_eq_self_of_mem_center _ (hcenD _ (hrW w') _ (hsV v))]
    exact mem_center_iff.mp (hcenD _ (hrW w) _ (hsV v)) _
  ·
    apply Subtype.ext
    rw [Subgroup.coe_mul, hβ, hβ, hβ, hwd (rW w) (hrW w) (rW w) (hrW w) rfl
      (sV v * sV v') (P.mul_mem (hsV v) (hsV v')) (sV (v * v')) (hsV _)
      (inv_mul_mem_of_abelianization_of_eq_mul hη hker (hsV v) (hsV v') (hsV _)
        (by rw [hsVx, hsVx, hsVx])),
      commutatorElement_mul_right_eq, conj_eq_self_of_mem_center _ (hcenD _ (hrW w) _ (hsV v'))]
  ·
    refine le_antisymm ((closure_le _).mpr ?_) (hCD.le.trans ((Subgroup.commutator_def _ _).le.trans
      (closure_mono ?_)))
    · rintro _ ⟨p, rfl⟩
      exact (β p.1 p.2).2
    · rintro _ ⟨r, hr, s, hs, rfl⟩
      exact ⟨(⟨η r, (mem_commutator_comap_iff hη hker).mp hr⟩, Abelianization.of ⟨η s, hs⟩),
        hform r hr s hs _ rfl _ rfl⟩
  ·
    obtain ⟨g, hg⟩ := hη t
    have htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := fun x hx => (mem_normalizer_iff.mp (hT ht) x).mp hx
    have hgP : ∀ x ∈ P, g * x * g⁻¹ ∈ P := fun x hx => by
      change η (g * x * g⁻¹) ∈ Q
      rw [map_mul, map_mul, map_inv, hg]
      exact htQ _ hx
    have hgsV := hgP _ (hsV (Abelianization.of ⟨a, ha⟩))
    apply Subtype.ext
    rw [hform (g * rW ⟨w, hw⟩ * g⁻¹) (conj_mem_commutator hgP hgP (hrW _))
      (g * sV (Abelianization.of ⟨a, ha⟩) * g⁻¹) hgsV ⟨t * w * t⁻¹, htw⟩
      (by rw [map_mul, map_mul, map_inv, hg, hηrW]) _ ?_, conj_commutatorElement,
      conj_eq_self_of_mem_center _ (hcenD _ (hrW _) _ (hsV _))]
    rw [abelianization_of_eq_iff]
    have h0 := (abelianization_of_eq_iff _ _).mp (hsVx (Abelianization.of ⟨a, ha⟩))
    simp only [map_mul, map_inv, hg] at h0 ⊢
    rw [show (t * η (sV (Abelianization.of ⟨a, ha⟩)) * t⁻¹)⁻¹ * (t * a * t⁻¹) =
      t * ((η (sV (Abelianization.of ⟨a, ha⟩)))⁻¹ * a) * t⁻¹ by group]
    exact conj_mem_commutator htQ htQ h0
  ·
    obtain ⟨x, rfl⟩ := hη a
    obtain ⟨y, rfl⟩ := hη b
    obtain ⟨z, rfl⟩ := hη c
    have hJ : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, ⁅⁅x, y⁆, y * z * y⁻¹⁆ = ⁅⁅x, y⁆, z⁆ := by
      intro x hx y hy z hz
      rw [conj_eq_commutatorElement_mul, commutatorElement_mul_right_eq,
        hcomm1 _ (hPP' x hx y hy) _ (hPP' y hy z hz), one_mul,
        conj_eq_self_of_mem_center _ (hcenD _ (hPP' x hx y hy) z hz)]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul,
      hform ⁅x, y⁆ (hPP' x ha y hb) z hc ⟨_, hab⟩ (map_commutatorElement η x y) _ rfl,
      hform ⁅y, z⁆ (hPP' y hb z hc) x ha ⟨_, hbc⟩ (map_commutatorElement η y z) _ rfl,
      hform ⁅z, x⁆ (hPP' z hc x ha) y hb ⟨_, hca⟩ (map_commutatorElement η z x) _ rfl,
      Subgroup.coe_one, ← hJ x ha y hb z hc, ← hJ y hb z hc x ha, ← hJ z hc x ha y hb]
    exact commutatorElement_commutatorElement_conj_mul x y z

end Pairing

end EvenCoverPairing

open CFSG.Assembly EvenCoverPairing in
theorem even_central_two_cover_class_three_kernel_pairing {E J : Type*} [Group E] [Group J]
    [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J) (hη : Function.Surjective η)
    (hcen : η.ker ≤ center E) (hC2 : IsPGroup 2 η.ker) (Q : Sylow 2 J)
    (hQ : Group.nilpotencyClass (Q : Subgroup J) ≤ 2)
    (_hW : IsElemAbelian 2 ⁅(Q : Subgroup J), (Q : Subgroup J)⁆)
    (hV : IsElemAbelian 2 (⊤ : Subgroup (Abelianization (Q : Subgroup J))))
    (T : Subgroup J) (hT : T ≤ normalizer ((Q : Subgroup J) : Set J)) (hTodd : Odd (Nat.card T))
    (hpair : ∀ f : Abelianization (Q : Subgroup J) → Abelianization (Q : Subgroup J) → ZMod 2,
      (∀ x x' y, f (x * x') y = f x y + f x' y) → (∀ x y y', f x (y * y') = f x y + f x y') →
      (∀ t ∈ T, ∀ (a b : J) (ha : a ∈ (Q : Subgroup J)) (hb : b ∈ (Q : Subgroup J))
        (hta : t * a * t⁻¹ ∈ (Q : Subgroup J)) (htb : t * b * t⁻¹ ∈ (Q : Subgroup J)),
        f (Abelianization.of ⟨t * a * t⁻¹, hta⟩) (Abelianization.of ⟨t * b * t⁻¹, htb⟩) =
          f (Abelianization.of ⟨a, ha⟩) (Abelianization.of ⟨b, hb⟩)) → f = 0) :
    η.ker = ⁅⁅(Q : Subgroup J).comap η, (Q : Subgroup J).comap η⁆, (Q : Subgroup J).comap η⁆ ∧
    IsElemAbelian 2 η.ker ∧
    IsMulCommutative ↥⁅(Q : Subgroup J).comap η, (Q : Subgroup J).comap η⁆ ∧
    ⁅(Q : Subgroup J).comap η, (Q : Subgroup J).comap η⁆.map η =
      ⁅(Q : Subgroup J), (Q : Subgroup J)⁆ ∧
    Function.Bijective (Abelianization.map (η.subgroupComap (Q : Subgroup J))) ∧
    ∃ β : ↥⁅(Q : Subgroup J), (Q : Subgroup J)⁆ → Abelianization (Q : Subgroup J) → η.ker,
      (∀ r ∈ ⁅(Q : Subgroup J).comap η, (Q : Subgroup J).comap η⁆, ∀ (s : E)
        (hs : η s ∈ (Q : Subgroup J)) (hr : η r ∈ ⁅(Q : Subgroup J), (Q : Subgroup J)⁆),
        (β ⟨η r, hr⟩ (Abelianization.of ⟨η s, hs⟩) : E) = ⁅r, s⁆) ∧
      (∀ w w' v, β (w * w') v = β w v * β w' v) ∧ (∀ w v v', β w (v * v') = β w v * β w v') ∧
      closure (Set.range fun p : ↥⁅(Q : Subgroup J), (Q : Subgroup J)⁆ ×
        Abelianization (Q : Subgroup J) => (β p.1 p.2 : E)) = η.ker ∧
      (∀ t ∈ T, ∀ (w : J) (hw : w ∈ ⁅(Q : Subgroup J), (Q : Subgroup J)⁆)
        (htw : t * w * t⁻¹ ∈ ⁅(Q : Subgroup J), (Q : Subgroup J)⁆) (a : J)
        (ha : a ∈ (Q : Subgroup J)) (hta : t * a * t⁻¹ ∈ (Q : Subgroup J)),
        β ⟨t * w * t⁻¹, htw⟩ (Abelianization.of ⟨t * a * t⁻¹, hta⟩) =
          β ⟨w, hw⟩ (Abelianization.of ⟨a, ha⟩)) ∧
      ∀ (a b c : J) (ha : a ∈ (Q : Subgroup J)) (hb : b ∈ (Q : Subgroup J))
        (hc : c ∈ (Q : Subgroup J)) (hab : ⁅a, b⁆ ∈ ⁅(Q : Subgroup J), (Q : Subgroup J)⁆)
        (hbc : ⁅b, c⁆ ∈ ⁅(Q : Subgroup J), (Q : Subgroup J)⁆)
        (hca : ⁅c, a⁆ ∈ ⁅(Q : Subgroup J), (Q : Subgroup J)⁆),
        β ⟨⁅a, b⁆, hab⟩ (Abelianization.of ⟨c, hc⟩) * β ⟨⁅b, c⁆, hbc⟩ (Abelianization.of ⟨a, ha⟩) *
          β ⟨⁅c, a⁆, hca⟩ (Abelianization.of ⟨b, hb⟩) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : (Q : Subgroup J) ≤ η.range := by
    rw [MonoidHom.range_eq_top.mpr hη]
    exact le_top
  have hker : η.ker ≤ ⁅(Q : Subgroup J).comap η, (Q : Subgroup J).comap η⁆ := by
    have h := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived
      (Q.comapOfKerIsPGroup η hC2 hrange) η.ker hcen hC2
    rwa [map_subtype_commutator, Sylow.coe_comapOfKerIsPGroup] at h
  have hQ3 : ⁅⁅(Q : Subgroup J), (Q : Subgroup J)⁆, (Q : Subgroup J)⁆ = ⊥ := by
    have : Group.IsNilpotent (Q : Subgroup J) := Q.isPGroup'.isNilpotent
    have h := (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (n := 2)).mpr hQ
    have h2 : Subgroup.map (Q : Subgroup J).subtype ⁅⁅(⊤ : Subgroup (Q : Subgroup J)),
        (⊤ : Subgroup (Q : Subgroup J))⁆, (⊤ : Subgroup (Q : Subgroup J))⁆ = ⊥ := by
      rw [show ⁅⁅(⊤ : Subgroup (Q : Subgroup J)), (⊤ : Subgroup (Q : Subgroup J))⁆,
        (⊤ : Subgroup (Q : Subgroup J))⁆ =
        (⊤ : Subgroup (Q : Subgroup J)).lowerCentralSeries 2 by
          simp [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero], h,
        Subgroup.map_bot]
    rwa [map_commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2
  have hVsq : ∀ a ∈ (Q : Subgroup J), a ^ 2 ∈ ⁅(Q : Subgroup J), (Q : Subgroup J)⁆ := by
    intro a ha
    have h := hV.2 (Abelianization.of ⟨a, ha⟩) (mem_top _)
    rw [← map_pow, ← map_one Abelianization.of, eq_comm, abelianization_of_eq_iff] at h
    simpa using h
  exact central_cover_kernel_pairing_of_ker_le hη hcen hker hQ3 hVsq hT hTodd hpair

end CFSG.LocalAnalysis.ComponentInitial
