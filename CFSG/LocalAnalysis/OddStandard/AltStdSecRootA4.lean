module

public import CFSG.LocalAnalysis.OddStandard.SolomonAltRootA4

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Equiv.Perm Subgroup CFSG.OddStandard.SolomonAlt Function

theorem rootA4_pair_mem_alternating {α : Type*} [DecidableEq α] [Fintype α] {t : Perm α}
    {p q : α} (hp : t p ≠ p) (hq : t q ≠ q) :
    swap p (t p) * swap q (t q) ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (Ne.symm hp),
    Perm.sign_swap (Ne.symm hq)]
  decide

theorem rootA4_exchange_mem_alternating {α : Type*} [DecidableEq α] [Fintype α] (t : Perm α)
    {a b : α} (hba : b ≠ a) : swap a b * swap (t a) (t b) ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (Ne.symm hba),
    Perm.sign_swap (fun h => hba (t.injective h).symm)]
  decide

theorem rootA4_exchange_mem_centralizer {α : Type*} [DecidableEq α] {t : Perm α}
    (ht : t * t = 1) {a b : α} (ha : t a ≠ a) (hb : t b ≠ b) (hba : b ≠ a) (hbta : b ≠ t a) :
    swap a b * swap (t a) (t b) ∈ centralizer {t} := by
  rw [mem_centralizer_singleton_iff]
  ext x
  have h1 := apply_apply_of_mul_self ht a
  have h2 := apply_apply_of_mul_self ht b
  have h3 := apply_apply_of_mul_self ht x
  simp only [Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

theorem rootA4_exchange_apply_left {α : Type*} [DecidableEq α] {t : Perm α}
    (ht : t * t = 1) {a b : α} (ha : t a ≠ a) (hb : t b ≠ b) (hbta : b ≠ t a) :
    (swap a b * swap (t a) (t b)) a = b := by
  have h1 := apply_apply_of_mul_self ht a
  have h2 := apply_apply_of_mul_self ht b
  simp only [Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

theorem rootA4_exchange_apply_of_notMem {α : Type*} [DecidableEq α] {t : Perm α} {a b x : α}
    (hxa : x ≠ a) (hxta : x ≠ t a) (hxb : x ≠ b) (hxtb : x ≠ t b) :
    (swap a b * swap (t a) (t b)) x = x := by
  simp only [Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

theorem rootA4_false_of_pair_mem {α : Type*} [DecidableEq α] [Fintype α] {t : Perm α}
    (ht : t * t = 1) {X : Subgroup (Perm α)}
    (hn : ∀ c ∈ centralizer {t}, c ∈ alternatingGroup α → ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (h3 : ∀ s : Finset (Perm α), (∀ y ∈ s, y ∈ X ∧ y ≠ 1 ∧ y * y = 1) → s.card ≤ 3)
    {a b c d : α} (ha : t a ≠ a) (hb : t b ≠ b) (hc : t c ≠ c) (hd : t d ≠ d)
    (hba : b ≠ a) (hbta : b ≠ t a)
    (hc1 : c ∉ ({a, t a, b, t b} : Finset α))
    (hd1 : d ∉ ({a, t a, b, t b, c, t c} : Finset α))
    (hy : swap a (t a) * swap b (t b) ∈ X) : False := by
  classical
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1 hd1
  have key : ∀ σ ∈ centralizer {t}, σ ∈ alternatingGroup α → ∀ p q : α,
      swap p (t p) * swap q (t q) ∈ X →
      swap (σ p) (t (σ p)) * swap (σ q) (t (σ q)) ∈ X := by
    intro σ hσ hσA p q hpq
    have h := hn σ hσ hσA _ hpq
    have e : σ * (swap p (t p) * swap q (t q)) * σ⁻¹ =
        (σ * swap p (t p) * σ⁻¹) * (σ * swap q (t q) * σ⁻¹) := by group
    rw [e, conj_swap_of_mem_centralizer hσ, conj_swap_of_mem_centralizer hσ] at h
    exact h
  have h1 := apply_apply_of_mul_self ht a
  have h2 := apply_apply_of_mul_self ht b
  have h3' := apply_apply_of_mul_self ht c
  have h4 := apply_apply_of_mul_self ht d
  have hy2 : swap a (t a) * swap c (t c) ∈ X := by
    have σmem := rootA4_exchange_mem_centralizer ht hb hc (by grind) (by grind)
    have σalt := rootA4_exchange_mem_alternating t (a := b) (b := c) (by grind)
    have := key _ σmem σalt a b hy
    have e1 : (swap b c * swap (t b) (t c)) a = a :=
      rootA4_exchange_apply_of_notMem (by grind) (by grind) (by grind) (by grind)
    have e2 : (swap b c * swap (t b) (t c)) b = c :=
      rootA4_exchange_apply_left ht hb hc (by grind)
    rwa [e1, e2] at this
  have hy3 : swap a (t a) * swap d (t d) ∈ X := by
    have σmem := rootA4_exchange_mem_centralizer ht hb hd (by grind) (by grind)
    have σalt := rootA4_exchange_mem_alternating t (a := b) (b := d) (by grind)
    have := key _ σmem σalt a b hy
    have e1 : (swap b d * swap (t b) (t d)) a = a :=
      rootA4_exchange_apply_of_notMem (by grind) (by grind) (by grind) (by grind)
    have e2 : (swap b d * swap (t b) (t d)) b = d :=
      rootA4_exchange_apply_left ht hb hd (by grind)
    rwa [e1, e2] at this
  have hy4 : swap b (t b) * swap c (t c) ∈ X := by
    have σmem := rootA4_exchange_mem_centralizer ht ha hb hba hbta
    have σalt := rootA4_exchange_mem_alternating t (a := a) (b := b) hba
    have := key _ σmem σalt a c hy2
    have e1 : (swap a b * swap (t a) (t b)) a = b := rootA4_exchange_apply_left ht ha hb hbta
    have e2 : (swap a b * swap (t a) (t b)) c = c :=
      rootA4_exchange_apply_of_notMem (by grind) (by grind) (by grind) (by grind)
    rwa [e1, e2] at this
  have hd12 : swap a (t a) * swap b (t b) ≠ swap a (t a) * swap c (t c) := by
    intro h
    have := congrArg (fun f : Perm α => f b) h
    rw [pair_apply_right ht hba hbta, pair_apply_of_notMem ht (by grind) (by grind) (by grind)
      (by grind)] at this
    exact hb this
  have hd13 : swap a (t a) * swap b (t b) ≠ swap a (t a) * swap d (t d) := by
    intro h
    have := congrArg (fun f : Perm α => f b) h
    rw [pair_apply_right ht hba hbta, pair_apply_of_notMem ht (by grind) (by grind) (by grind)
      (by grind)] at this
    exact hb this
  have hd14 : swap a (t a) * swap b (t b) ≠ swap b (t b) * swap c (t c) := by
    intro h
    have := congrArg (fun f : Perm α => f a) h
    rw [pair_apply_left ht hba hbta, pair_apply_of_notMem ht (by grind) (by grind) (by grind)
      (by grind)] at this
    exact ha this
  have hd23 : swap a (t a) * swap c (t c) ≠ swap a (t a) * swap d (t d) := by
    intro h
    have := congrArg (fun f : Perm α => f c) h
    rw [pair_apply_right ht (by grind) (by grind), pair_apply_of_notMem ht (by grind) (by grind)
      (by grind) (by grind)] at this
    exact hc this
  have hd24 : swap a (t a) * swap c (t c) ≠ swap b (t b) * swap c (t c) := by
    intro h
    have := congrArg (fun f : Perm α => f a) h
    rw [pair_apply_left ht (by grind) (by grind), pair_apply_of_notMem ht (by grind) (by grind)
      (by grind) (by grind)] at this
    exact ha this
  have hd34 : swap a (t a) * swap d (t d) ≠ swap b (t b) * swap c (t c) := by
    intro h
    have := congrArg (fun f : Perm α => f a) h
    rw [pair_apply_left ht (by grind) (by grind), pair_apply_of_notMem ht (by grind) (by grind)
      (by grind) (by grind)] at this
    exact ha this
  have hcard : ({swap a (t a) * swap b (t b), swap a (t a) * swap c (t c),
      swap a (t a) * swap d (t d), swap b (t b) * swap c (t c)} : Finset (Perm α)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hd34]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hd23, hd24⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hd12, hd13, hd14⟩
  have hle := h3 {swap a (t a) * swap b (t b), swap a (t a) * swap c (t c),
      swap a (t a) * swap d (t d), swap b (t b) * swap c (t c)} (by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · refine ⟨hy, fun h => ha ?_, pair_mul_self ht hba hbta ha hb⟩
      have := congrArg (fun f : Perm α => f a) h
      simpa [pair_apply_left ht hba hbta] using this
    · refine ⟨hy2, fun h => ha ?_, pair_mul_self ht (by grind) (by grind) ha hc⟩
      have := congrArg (fun f : Perm α => f a) h
      simpa [pair_apply_left ht (by grind : c ≠ a) (by grind : c ≠ t a)] using this
    · refine ⟨hy3, fun h => ha ?_, pair_mul_self ht (by grind) (by grind) ha hd⟩
      have := congrArg (fun f : Perm α => f a) h
      simpa [pair_apply_left ht (by grind : d ≠ a) (by grind : d ≠ t a)] using this
    · refine ⟨hy4, fun h => hb ?_, pair_mul_self ht (by grind) (by grind) hb hc⟩
      have := congrArg (fun f : Perm α => f b) h
      simpa [pair_apply_left ht (by grind : c ≠ b) (by grind : c ≠ t b)] using this)
  omega

theorem rootA4_apply_eq_of_pow_three {α : Type*} [DecidableEq α] [Fintype α] {t : Perm α}
    (ht : t * t = 1) (h8 : 8 ≤ t.support.card) {X : Subgroup (Perm α)}
    (hX : X ≤ centralizer {t})
    (hn : ∀ c ∈ centralizer {t}, c ∈ alternatingGroup α → ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (h3 : ∀ s : Finset (Perm α), (∀ y ∈ s, y ∈ X ∧ y ≠ 1 ∧ y * y = 1) → s.card ≤ 3)
    {x : Perm α} (hx : x ∈ X) (hx3 : x ^ 3 = 1) : x ∈ fixMoved t := by
  rw [mem_fixMoved]
  intro a ha
  have hxC : x ∈ centralizer {t} := hX hx
  have hxt : ∀ q, t (x q) = x (t q) := apply_comm_of_mem_centralizer hxC
  have hx3a : ∀ q, x (x (x q)) = q := fun q => by
    simpa [pow_succ] using congrArg (fun f : Perm α => f q) hx3
  have hcyc : x a = a ∨ x a = t a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hxa, hxta⟩ := hcon
    obtain ⟨b, hb⟩ : ∃ b, x a = b := ⟨_, rfl⟩
    rw [hb] at hxa hxta
    have hbm : t b ≠ b := by
      rw [← hb, hxt]
      intro h
      exact ha (x.injective h)
    have hca : swap a (t a) ∈ centralizer {t} := swap_mem_centralizer ht a
    have hcb : swap b (t b) ∈ centralizer {t} := swap_mem_centralizer ht b
    have hcm : swap a (t a) * swap b (t b) ∈ centralizer {t} := (centralizer {t}).mul_mem hca hcb
    have hce : swap a (t a) * swap b (t b) ∈ alternatingGroup α :=
      rootA4_pair_mem_alternating ha hbm
    have hy : x * ((swap a (t a) * swap b (t b)) * x⁻¹ * (swap a (t a) * swap b (t b))⁻¹) ∈ X :=
      X.mul_mem hx (hn _ hcm hce x⁻¹ (X.inv_mem hx))
    have e1 : x * swap a (t a) * x⁻¹ = swap b (t b) := by
      rw [conj_swap_of_mem_centralizer hxC, hb]
    have e2 : x * swap b (t b) * x⁻¹ = swap (x b) (t (x b)) :=
      conj_swap_of_mem_centralizer hxC b
    have e : x * ((swap a (t a) * swap b (t b)) * x⁻¹ * (swap a (t a) * swap b (t b))⁻¹) =
        swap b (t b) * swap (x b) (t (x b)) * (swap b (t b) * swap a (t a)) := by
      calc x * ((swap a (t a) * swap b (t b)) * x⁻¹ * (swap a (t a) * swap b (t b))⁻¹)
          = (x * swap a (t a) * x⁻¹) * (x * swap b (t b) * x⁻¹) *
              (swap a (t a) * swap b (t b))⁻¹ := by group
        _ = swap b (t b) * swap (x b) (t (x b)) * (swap b (t b) * swap a (t a)) := by
          rw [e1, e2, mul_inv_rev, swap_inv, swap_inv]
    rw [e] at hy
    by_cases hb1 : x b = b ∨ x b = t b
    ·
      have hsw : swap (x b) (t (x b)) = swap b (t b) := by
        rcases hb1 with h | h
        · rw [h]
        · rw [h, apply_apply_of_mul_self ht, swap_comm]
      rw [hsw, swap_mul_self, one_mul] at hy
      have hy' : swap a (t a) * swap b (t b) ∈ X := by
        have := X.inv_mem hy
        rwa [mul_inv_rev, swap_inv, swap_inv] at this
      obtain ⟨c, d, hc, hd, hc1, hd1⟩ := exists_two_more h8 a b
      exact rootA4_false_of_pair_mem ht hn h3 ha hbm hc hd hxa hxta hc1 hd1 hy'
    · push Not at hb1
      obtain ⟨hb1a, hb1b⟩ := hb1
      by_cases ha1 : x b = a ∨ x b = t a
      ·
        have h := hx3a a
        rw [hb] at h
        rcases ha1 with h1 | h1
        · rw [h1, hb] at h
          exact hxa h
        · rw [h1, ← hxt, hb] at h
          have := apply_apply_of_mul_self ht b
          rw [h] at this
          exact hxta this.symm
      ·
        push Not at ha1
        obtain ⟨ha1a, ha1b⟩ := ha1
        have hpm : t (x b) ≠ x b := by
          rw [hxt]
          intro h
          exact hbm (x.injective h)
        have h1 := pair_mul_self ht hb1a hb1b hbm hpm
        have h2 : swap b (t b) * swap (x b) (t (x b)) * swap b (t b) =
            swap (x b) (t (x b)) := by
          have h1' : (swap b (t b) * swap (x b) (t (x b)) * swap b (t b)) *
              swap (x b) (t (x b)) = 1 := by
            rw [mul_assoc (swap b (t b) * swap (x b) (t (x b))) (swap b (t b))]
            exact h1
          rw [eq_inv_of_mul_eq_one_left h1', swap_inv]
        rw [← mul_assoc, h2] at hy
        have hy' : swap a (t a) * swap (x b) (t (x b)) ∈ X := by
          have := X.inv_mem hy
          rwa [mul_inv_rev, swap_inv, swap_inv] at this
        obtain ⟨c, d, hc, hd, hc1, hd1⟩ := exists_two_more h8 a (x b)
        exact rootA4_false_of_pair_mem ht hn h3 ha hpm hc hd ha1a ha1b hc1 hd1 hy'
  rcases hcyc with h | h
  · exact h
  · exfalso
    have h' : x (t a) = a := by
      rw [← hxt, h, apply_apply_of_mul_self ht]
    have := hx3a a
    rw [h, h', h] at this
    exact ha this

theorem rootA4_le_fixMoved {α : Type*} [DecidableEq α] [Fintype α] {t : Perm α}
    (ht : t * t = 1) (h8 : 8 ≤ t.support.card) {X : Subgroup (Perm α)}
    (hX : X ≤ centralizer {t})
    (hn : ∀ c ∈ centralizer {t}, c ∈ alternatingGroup α → ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (h3 : ∀ s : Finset (Perm α), (∀ y ∈ s, y ∈ X ∧ y ≠ 1 ∧ y * y = 1) → s.card ≤ 3)
    (e : X ≃* alternatingGroup (Fin 4)) : X ≤ fixMoved t := by
  let φ : alternatingGroup (Fin 4) →* Perm α := X.subtype.comp e.symm.toMonoidHom
  have hφX : ∀ g, φ g ∈ X := fun g => (e.symm g).2
  have hφ3 : ∀ g : alternatingGroup (Fin 4), (g : Perm (Fin 4)).IsThreeCycle → φ g ^ 3 = 1 := by
    intro g hg
    have : g ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hg.orderOf]
      exact pow_orderOf_eq_one _
    rw [← map_pow, this, map_one]
  have hcl : Subgroup.closure
      {g : alternatingGroup (Fin 4) | (g : Perm (Fin 4)).IsThreeCycle} = ⊤ :=
    alternatingGroup.closure_isThreeCycles_eq_top
  have hfix : (fixMoved t).comap φ = ⊤ := by
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    intro g hg
    exact rootA4_apply_eq_of_pow_three ht h8 hX hn h3 (hφX g) (hφ3 g hg)
  intro x hx
  have h1 := (Subgroup.eq_top_iff' _).1 hfix (e ⟨x, hx⟩)
  have hφx : φ (e ⟨x, hx⟩) = x := by simp [φ]
  simpa [hφx] using h1

theorem rootA4_root_alt_four_of_normal_alt_centralizer {α : Type*} [Fintype α] [DecidableEq α]
    {t : Perm α} (ht : t * t = 1) (h8 : 8 ≤ t.support.card) {X : Subgroup (Perm α)}
    (hX : X ≤ centralizer {t})
    (hXn : ∀ c ∈ centralizer {t}, c ∈ alternatingGroup α → ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (he : Nonempty (X ≃* alternatingGroup (Fin 4))) :
    Nat.card (Function.fixedPoints t) = 4 ∧
      X = (alternatingGroup (Function.fixedPoints t)).map Perm.ofSubtype := by
  obtain ⟨e⟩ := he
  have h3 : ∀ s : Finset (Perm α), (∀ y ∈ s, y ∈ X ∧ y ≠ 1 ∧ y * y = 1) → s.card ≤ 3 :=
    fun s hs => card_involutions_le_three e s hs
  have hle := rootA4_le_fixMoved ht h8 hX hXn h3 e
  obtain ⟨a, ha⟩ : ∃ a, t a ≠ a := by
    obtain ⟨a, ha⟩ := Finset.card_pos.1 (show 0 < t.support.card by omega)
    exact ⟨a, Perm.mem_support.1 ha⟩
  have hta : t (t a) ≠ t a := by
    rw [apply_apply_of_mul_self ht]
    exact Ne.symm ha
  have hs : swap a (t a) ∈ centralizer {t} := swap_mem_centralizer ht a
  have hfull : ∀ c ∈ centralizer {t}, ∀ x ∈ X, c * x * c⁻¹ ∈ X := by
    intro c hc x hx
    by_cases hcA : c ∈ alternatingGroup α
    · exact hXn c hc hcA x hx
    ·
      have hxm := mem_fixMoved.1 (hle hx)
      have hsx : swap a (t a) * x * (swap a (t a))⁻¹ = x := by
        have hxs : x * swap a (t a) * x⁻¹ = swap a (t a) := by
          rw [← swap_apply_apply, hxm a ha, hxm (t a) hta]
        have hcomm : x * swap a (t a) = swap a (t a) * x := mul_inv_eq_iff_eq_mul.1 hxs
        rw [← hcomm, mul_inv_cancel_right]
      have hodd : sign c = -1 := by
        rcases Int.units_eq_one_or (sign c) with h | h
        · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h) hcA
        · exact h
      have hc' : c * swap a (t a) ∈ alternatingGroup α := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, hodd, Perm.sign_swap (Ne.symm ha)]
        decide
      have h := hXn _ ((centralizer {t}).mul_mem hc hs) hc' x hx
      have e : c * swap a (t a) * x * (c * swap a (t a))⁻¹ =
          c * (swap a (t a) * x * (swap a (t a))⁻¹) * c⁻¹ := by group
      rw [e, hsx] at h
      exact h
  have hXnormal : (X.subgroupOf (centralizer {t})).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hfull g g.2 n hn
  exact root_alt_four_of_normal_centralizer ht h8 hX hXnormal ⟨e⟩

end CFSG.OddStandard.AltStdSec
