module

public import CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixedCentralizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement
open ExtraspecialFixed

theorem extraspecial_centralizer_of_centralizer {P : Type*} [Group P]
    (hc : commutator P ≤ center P) (h2 : Nat.card (center P) = 2) {y t : P}
    (ht : ∀ r : P, r * y = y * r → t * r = r * t) : t ∈ center P ∨ t * y⁻¹ ∈ center P := by
  have hcomm : ∀ a b : P, ⁅a, b⁆ ∈ center P := fun a b =>
    hc (commutatorElement_mem_commutator a b)
  have huniq : ∀ a b : P, a ∈ center P → b ∈ center P → a ≠ 1 → b ≠ 1 → a = b := by
    intro a b ha hb ha1 hb1
    have := eq_of_ne_one_of_card_eq_two h2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
      (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  have hsq : ∀ a : P, a ∈ center P → a * a = 1 := by
    intro a ha
    have := pow_two_eq_one_of_card_eq_two h2 ⟨a, ha⟩
    rw [sq] at this
    exact congrArg Subtype.val this
  by_cases htc : t ∈ center P
  · exact Or.inl htc
  right
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : P, ⁅r₀, t⁆ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply htc
    rw [mem_center_iff]
    intro g
    exact (commutatorElement_eq_one_iff_mul_comm.1 (hall g))
  have hr₀y : ⁅r₀, y⁆ ≠ 1 := by
    intro h
    apply hr₀
    rw [commutatorElement_eq_one_iff_mul_comm] at h ⊢
    exact (ht r₀ h).symm
  have heq : ∀ r : P, ⁅r, t⁆ = ⁅r, y⁆ := by
    intro r
    by_cases hry : ⁅r, y⁆ = 1
    · rw [hry, commutatorElement_eq_one_iff_mul_comm]
      exact (ht r (commutatorElement_eq_one_iff_mul_comm.1 hry)).symm
    · have h1 : ⁅r * r₀, y⁆ = 1 := by
        rw [commutatorElement_mul_left_of_mem_center (hcomm r₀ y),
          huniq _ _ (hcomm r y) (hcomm r₀ y) hry hr₀y, hsq _ (hcomm r₀ y)]
      have h2 : ⁅r * r₀, t⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (ht _ (commutatorElement_eq_one_iff_mul_comm.1 h1)).symm
      rw [commutatorElement_mul_left_of_mem_center (hcomm r₀ t)] at h2
      have h3 : ⁅r, t⁆ ≠ 1 := by
        intro h
        rw [h, one_mul] at h2
        exact hr₀ h2
      exact huniq _ _ (hcomm r t) (hcomm r y) h3 hry
  rw [mem_center_iff]
  intro g
  have h1 : ⁅g, y * y⁻¹⁆ = ⁅g, y⁆ * ⁅g, y⁻¹⁆ :=
    commutatorElement_mul_right_of_mem_center (hcomm g y⁻¹)
  rw [mul_inv_cancel, commutatorElement_one_right] at h1
  have h2 : ⁅g, t * y⁻¹⁆ = 1 := by
    rw [commutatorElement_mul_right_of_mem_center (hcomm g y⁻¹), heq g]
    exact h1.symm
  exact commutatorElement_eq_one_iff_mul_comm.1 h2

theorem two_centralizer_intersection_center {G : Type*} [Group G] [Finite G] {x : G}
    (hx : orderOf x = 2) {Q : Subgroup G} (hQH : Q ≤ centralizer ({x} : Set G))
    (hQn : (Q.subgroupOf (centralizer ({x} : Set G))).Normal)
    (hQe : CFSG.IsExtraspecialPGroup 2 Q) (hZQ : (center Q).map Q.subtype = zpowers x)
    (hker : ∀ h ∈ centralizer ({x} : Set G),
      (∀ q ∈ Q, h * q * h⁻¹ * q⁻¹ ∈ zpowers x) ↔ h ∈ Q)
    {y : G} (hyQ : y ∈ Q) (hy : orderOf y = 2) (hyx : y ∉ zpowers x) :
    (center ↥(centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) : Subgroup G)).map
        (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)).subtype =
      closure {x, y} ∧
    centralizer ((centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G) ⊓
        centralizer ({y} : Set G) = closure {x, y} := by
  obtain ⟨-, hcQ, -, hZ2⟩ := hQe
  have hxx : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  have hyy : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  have hpowC : ∀ g ∈ centralizer ({x} : Set G), ∀ z ∈ zpowers x, g * z = z * g := by
    rintro g hg _ ⟨k, rfl⟩
    exact ((Commute.zpow_right (mem_centralizer_singleton_iff.1 hg) k)).eq
  have hzsq : ∀ z ∈ zpowers x, z * z = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← zpow_add, ← two_mul, zpow_mul, show x ^ (2 : ℤ) = 1 by
      rw [zpow_ofNat, sq, hxx], one_zpow]
  have hcenter : ∀ q (hq : q ∈ Q), (⟨q, hq⟩ : Q) ∈ center Q ↔ q ∈ zpowers x := by
    intro q hq
    constructor
    · intro h
      rw [← hZQ]
      exact ⟨⟨q, hq⟩, h, rfl⟩
    · intro h
      rw [← hZQ] at h
      obtain ⟨z, hz, hzq⟩ := h
      have : z = ⟨q, hq⟩ := Subtype.ext hzq
      exact this ▸ hz
  have hZQx : ∀ z ∈ zpowers x, z ∈ Q := fun z hz => by
    rw [← hZQ] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact w.2
  have hZcomm : ∀ z ∈ zpowers x, ∀ g ∈ Q, g * z = z * g := by
    intro z hz g hg
    have h1 := (hcenter z (hZQx z hz)).2 hz
    exact congrArg Subtype.val (mem_center_iff.1 h1 ⟨g, hg⟩)
  have hcommQ : ∀ q ∈ Q, ∀ r ∈ Q, q * r * q⁻¹ * r⁻¹ ∈ zpowers x := by
    intro q hq r hr
    have h1 : ⁅(⟨q, hq⟩ : Q), (⟨r, hr⟩ : Q)⁆ ∈ center Q :=
      hcQ ▸ commutatorElement_mem_commutator _ _
    have h2 := (hcenter _ (⁅(⟨q, hq⟩ : Q), (⟨r, hr⟩ : Q)⁆).2).1 h1
    simpa [commutatorElement_def] using h2
  have hsqQ : ∀ q ∈ Q, q * q ∈ zpowers x := by
    intro q hq
    have h2 : ∀ z ∈ center Q, z ^ 2 = 1 := fun z hz => by
      have := pow_two_eq_one_of_card_eq_two hZ2 (⟨z, hz⟩ : center Q)
      simpa using congrArg Subtype.val this
    have h1 := sq_mem_center hcQ.le h2 ⟨q, hq⟩
    have h3 := (hcenter _ ((⟨q, hq⟩ : Q) ^ 2).2).1 h1
    simpa [sq] using h3
  set C := centralizer ({x} : Set G) with hCdef
  set D := C ⊓ centralizer ({y} : Set G) with hDdef
  have hyC : y ∈ C := hQH hyQ
  have hxD : x ∈ D := ⟨mem_centralizer_singleton_iff.2 rfl,
    mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hyC).symm⟩
  have hyD : y ∈ D := ⟨hyC, mem_centralizer_singleton_iff.2 rfl⟩
  have hZD : ∀ d ∈ D, (∀ e ∈ D, e * d = d * e) → d ∈ closure {x, y} := by
    intro d hdD hdc
    have hdC : d ∈ C := hdD.1
    have hdQy : ∀ r ∈ Q, r * y = y * r → d * r = r * d := by
      intro r hr hry
      exact (hdc r ⟨hQH hr, mem_centralizer_singleton_iff.2 hry⟩).symm
    have hdQ : d ∈ Q := by
      refine (hker d hdC).1 fun q hq => ?_
      have hq' : d * q * d⁻¹ ∈ Q := hQn.conj_mem ⟨q, hQH hq⟩ hq ⟨d, hdC⟩
      set c := q * y * q⁻¹ * y⁻¹ with hc
      have ht : ∀ r ∈ Q, r * y = y * r → (q⁻¹ * (d * q * d⁻¹)) * r = r * (q⁻¹ * (d * q * d⁻¹)) := by
        intro r hr hry
        have hdr : d * r = r * d := hdQy r hr hry
        have hqr := hcommQ q hq r hr
        have e1 : (d * q * d⁻¹) * r = (q * r * q⁻¹ * r⁻¹) * r * (d * q * d⁻¹) := by
          have h1 : d * q * d⁻¹ * r * (d * q * d⁻¹)⁻¹ * r⁻¹ = q * r * q⁻¹ * r⁻¹ := by
            have hdr' : d⁻¹ * r = r * d⁻¹ := by
              rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hdr, mul_assoc, mul_inv_cancel, mul_one]
            calc d * q * d⁻¹ * r * (d * q * d⁻¹)⁻¹ * r⁻¹
                = d * q * (d⁻¹ * r) * d * q⁻¹ * d⁻¹ * r⁻¹ := by group
              _ = d * (q * r * q⁻¹ * (d⁻¹ * r⁻¹ * d)) * d⁻¹ := by rw [hdr']; group
              _ = d * (q * r * q⁻¹ * r⁻¹) * d⁻¹ := by
                  rw [show d⁻¹ * r⁻¹ * d = r⁻¹ by
                    rw [← mul_inv_rev, ← hdr, mul_inv_rev, inv_mul_cancel_right]]
              _ = q * r * q⁻¹ * r⁻¹ := by
                  rw [hpowC d hdC _ hqr, mul_inv_cancel_right]
          calc (d * q * d⁻¹) * r = (d * q * d⁻¹ * r * (d * q * d⁻¹)⁻¹ * r⁻¹) * r *
                (d * q * d⁻¹) := by group
            _ = (q * r * q⁻¹ * r⁻¹) * r * (d * q * d⁻¹) := by rw [h1]
        have e2 : q * r = (q * r * q⁻¹ * r⁻¹) * r * q := by group
        generalize q * r * q⁻¹ * r⁻¹ = c' at e1 e2
        calc (q⁻¹ * (d * q * d⁻¹)) * r = q⁻¹ * (c' * r * (d * q * d⁻¹)) := by
              rw [mul_assoc, e1]
          _ = (q⁻¹ * (c' * r * q)) * q⁻¹ * (d * q * d⁻¹) := by group
          _ = (q⁻¹ * (q * r)) * q⁻¹ * (d * q * d⁻¹) := by rw [← e2]
          _ = r * (q⁻¹ * (d * q * d⁻¹)) := by group
      have htQ : q⁻¹ * (d * q * d⁻¹) ∈ Q := mul_mem (inv_mem hq) hq'
      rcases extraspecial_centralizer_of_centralizer hcQ.le hZ2 (y := ⟨y, hyQ⟩)
          (t := ⟨_, htQ⟩) (fun r hr => Subtype.ext (ht r r.2 (congrArg Subtype.val hr))) with
        h1 | h1
      ·
        have htx := (hcenter _ htQ).1 h1
        have : d * q * d⁻¹ * q⁻¹ = q⁻¹ * (d * q * d⁻¹) := by
          have hcomm := hZcomm _ htx q hq
          calc d * q * d⁻¹ * q⁻¹ = q * (q⁻¹ * (d * q * d⁻¹)) * q⁻¹ := by group
            _ = (q⁻¹ * (d * q * d⁻¹)) * q * q⁻¹ := by rw [hcomm]
            _ = q⁻¹ * (d * q * d⁻¹) := by group
        rw [this]
        exact htx
      ·
        exfalso
        have hzx := (hcenter _ (mul_mem htQ (inv_mem hyQ))).1 h1
        set z := q⁻¹ * (d * q * d⁻¹) * y⁻¹ with hz
        have hq'eq : d * q * d⁻¹ = q * z * y := by rw [hz]; group
        by_cases hqy : q * y = y * q
        · have hdq := hdQy q hq hqy
          have : z = y⁻¹ := by
            rw [hz, hdq, mul_inv_cancel_right, inv_mul_cancel, one_mul]
          exact hyx (by
            have := inv_mem (this ▸ hzx)
            simpa using this)
        · apply hqy
          have hsq1 : (d * q * d⁻¹) * (d * q * d⁻¹) = q * q := by
            have := hpowC d hdC _ (hsqQ q hq)
            calc (d * q * d⁻¹) * (d * q * d⁻¹) = d * (q * q) * d⁻¹ := by group
              _ = q * q := by rw [this, mul_inv_cancel_right]
          have hzq := hZcomm z hzx q hq
          have hzy := hZcomm z hzx y hyQ
          have hzz := hzsq z hzx
          set c' := y * q * y⁻¹ * q⁻¹ with hc'
          have hc'x := hcommQ y hyQ q hq
          have hc'q := hZcomm c' hc'x q hq
          have hyq : y * q = c' * q * y := by rw [hc']; group
          have hsq2 : (q * z * y) * (q * z * y) = c' * (q * q) := by
            calc (q * z * y) * (q * z * y) = (z * z) * (q * (y * q) * y) := by
                  calc (q * z * y) * (q * z * y) = q * (z * y) * q * (z * y) := by group
                    _ = q * (y * z) * q * (z * y) := by rw [← hzy]
                    _ = q * y * (z * q) * z * y := by group
                    _ = q * y * (q * z) * z * y := by rw [← hzq]
                    _ = q * y * q * (z * z) * y := by group
                    _ = (z * z) * (q * (y * q) * y) := by rw [hzz]; group
              _ = q * (c' * q * y) * y := by rw [hzz, one_mul, hyq]
              _ = (q * c') * q * (y * y) := by group
              _ = c' * (q * q) := by rw [hc'q, hyy, mul_one, mul_assoc]
          rw [hq'eq] at hsq1
          rw [hsq2] at hsq1
          have hc'1 : c' = 1 := mul_eq_right.1 hsq1
          rw [hc', mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc'1
          exact hc'1.symm
    rcases extraspecial_centralizer_of_centralizer hcQ.le hZ2 (y := ⟨y, hyQ⟩) (t := ⟨d, hdQ⟩)
        (fun r hr => Subtype.ext (hdQy r r.2 (congrArg Subtype.val hr))) with h1 | h1
    · have := (hcenter d hdQ).1 h1
      exact (zpowers_le.2 (subset_closure (Set.mem_insert x {y}))) this
    · have hz := (hcenter _ (mul_mem hdQ (inv_mem hyQ))).1 h1
      have hzc : d * y⁻¹ ∈ closure ({x, y} : Set G) :=
        (zpowers_le.2 (subset_closure (Set.mem_insert x {y}))) hz
      have hyc : y ∈ closure ({x, y} : Set G) :=
        subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))
      simpa using mul_mem hzc hyc
  have hxy_center : closure {x, y} ≤ (center D).map D.subtype := by
    rw [closure_le]
    intro w hw
    rcases hw with hw | hw
    · rw [hw]
      refine ⟨⟨x, hxD⟩, mem_center_iff.2 fun e => Subtype.ext ?_, rfl⟩
      exact mem_centralizer_singleton_iff.1 e.2.1
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      refine ⟨⟨y, hyD⟩, mem_center_iff.2 fun e => Subtype.ext ?_, rfl⟩
      exact mem_centralizer_singleton_iff.1 e.2.2
  have hcenterD : (center D).map D.subtype = closure {x, y} := by
    refine le_antisymm ?_ hxy_center
    rintro _ ⟨d, hd, rfl⟩
    exact hZD d d.2 fun e he => congrArg Subtype.val (mem_center_iff.1 hd ⟨e, he⟩)
  refine ⟨hcenterD, le_antisymm ?_ ?_⟩
  · rintro c ⟨hcD, hcy⟩
    have hcC : c ∈ C := by
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 hcD x hxD).symm
    exact hZD c ⟨hcC, hcy⟩ fun e he => mem_centralizer_iff.1 hcD e he
  · rw [closure_le]
    intro w hw
    rcases hw with hw | hw
    · rw [hw]
      refine ⟨mem_centralizer_iff.2 fun e he => ?_, ?_⟩
      · exact mem_centralizer_singleton_iff.1 he.1
      · exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hyC).symm
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      refine ⟨mem_centralizer_iff.2 fun e he => ?_, mem_centralizer_singleton_iff.2 rfl⟩
      exact mem_centralizer_singleton_iff.1 he.2

end CFSG.LocalAnalysis.ComponentInitial
