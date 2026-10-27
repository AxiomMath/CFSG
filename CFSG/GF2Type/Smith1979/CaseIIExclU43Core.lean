module

public import CFSG.GF2Type.Smith1979.CaseIIExclU43Radical

public section

namespace CFSG.GF2Type.Smith1979.Case2.U43Grp

namespace LiftSetup

variable {G X : Type} [Group G] [Group X] (D : LiftSetup G X)

theorem exists_two_nontrivial {S : Subgroup X} (h : Nat.card S = 8) :
    ∃ x ∈ S, ∃ x' ∈ S, x ≠ 1 ∧ x' ≠ 1 ∧ x ≠ x' := by
  classical
  have hn : (S : Set X).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact h
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ S, x ≠ 1 := by
    by_contra hc
    have hsub : (S : Set X) ⊆ {1} := fun s hs => by
      by_contra h1
      exact hc ⟨s, hs, h1⟩
    have := Set.ncard_le_ncard hsub (Set.finite_singleton 1)
    rw [Set.ncard_singleton, hn] at this
    omega
  obtain ⟨x', hx', hx'1, hxx'⟩ : ∃ x' ∈ S, x' ≠ 1 ∧ x' ≠ x := by
    by_contra hc
    have hsub : (S : Set X) ⊆ {1, x} := fun s hs => by
      by_cases h1 : s = 1
      · exact Or.inl h1
      · refine Or.inr ?_
        by_contra h2
        exact hc ⟨s, hs, h1, h2⟩
    have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hn] at h3
    have h2 := Set.ncard_insert_le (1 : X) ({x} : Set X)
    rw [Set.ncard_singleton] at h2
    omega
  exact ⟨x, hx, x', hx', hx1, hx'1, fun h => hxx' h.symm⟩

theorem lift_comm {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) (hS8 : Nat.card S = 8) (yl : G)
    {y : X} (hyl : D.ψ yl = y) (hy : orderOf y = 7) (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S)
    (hfpf : ∀ s ∈ S, y * s * y⁻¹ = s → s = 1) {s t : G} (hs : D.ψ s ∈ S) (ht : D.ψ t ∈ S) :
    s * t = t * s := by
  have hb := D.beta_eq_one hS2 hS8 yl hyl hy hyS hfpf hs ht
  have hz1 : D.ψ ((D.lift (D.ψ s))⁻¹ * s) = 1 := by
    rw [map_mul, map_inv, D.hlift, inv_mul_cancel]
  have hz2 : D.ψ ((D.lift (D.ψ t))⁻¹ * t) = 1 := by
    rw [map_mul, map_inv, D.hlift, inv_mul_cancel]
  have hs_eq : s = D.lift (D.ψ s) * ((D.lift (D.ψ s))⁻¹ * s) := by group
  have ht_eq : t = D.lift (D.ψ t) * ((D.lift (D.ψ t))⁻¹ * t) := by group
  have hc : cmG s t = 1 := by
    have e : cmG s t = cmG (D.lift (D.ψ s) * ((D.lift (D.ψ s))⁻¹ * s))
        (D.lift (D.ψ t) * ((D.lift (D.ψ t))⁻¹ * t)) := by
      rw [← hs_eq, ← ht_eq]
    rw [e, cmG_mul_central (D.ker_central _ hz1), cmG_mul_central_right (D.ker_central _ hz2)]
    exact hb
  simp only [cmG] at hc
  calc s * t = s * t * s⁻¹ * t⁻¹ * t * s := by group
    _ = t * s := by rw [hc]; group

theorem pow_four_of_mem {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) (hS8 : Nat.card S = 8)
    (yl : G) {y : X} (hyl : D.ψ yl = y) (hy : orderOf y = 7) (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S)
    (hfpf : ∀ s ∈ S, y * s * y⁻¹ = s → s = 1) {s : G} (hs : D.ψ s ∈ S) : s ^ 4 = 1 := by
  classical
  by_cases hA : ∃ w ∈ S, w ≠ 1 ∧ ∃ g : G, D.ψ g = w ∧ g ^ 4 = 1
  · obtain ⟨w, hwS, hw1, g, hgw, hg4⟩ := hA
    have hQ : ∀ x ∈ S, ∃ g' : G, D.ψ g' = x ∧ g' ^ 4 = 1 := by
      intro x hx
      by_cases hx1 : x = 1
      · exact ⟨1, by rw [hx1, map_one], by simp⟩
      obtain ⟨k, -, hk⟩ : ∃ k : ℕ, k < 7 ∧ x = y ^ k * w * (y ^ k)⁻¹ := by
        rcases orbit_of_ne_one hy hS8 hyS hfpf hwS hw1 hx with h | h
        · exact absurd h hx1
        · exact h
      rw [hk]
      clear hk hx hx1
      induction k with
      | zero => exact ⟨g, by simpa using hgw, by simpa using hg4⟩
      | succ k ih =>
        obtain ⟨g', hg'1, hg'2⟩ := ih
        refine ⟨yl * g' * yl⁻¹, ?_, ?_⟩
        · rw [map_mul, map_mul, map_inv, hyl, hg'1, pow_succ', mul_inv_rev]
          group
        · rw [conj_pow, hg'2]
          simp
    obtain ⟨g', hg'1, hg'2⟩ := hQ (D.ψ s) hs
    have hz : D.ψ (s * g'⁻¹) = 1 := by
      rw [map_mul, map_inv, hg'1, mul_inv_cancel]
    have hcomm : Commute (s * g'⁻¹) g' := D.ker_central _ hz g'
    have hsz : s = (s * g'⁻¹) * g' := by group
    rw [hsz, hcomm.mul_pow, hg'2, mul_one]
    exact D.ker_pow_four _ hz
  · exfalso
    have hneg4 : ∀ s : G, D.ψ s ∈ S → D.ψ s ≠ 1 → s ^ 4 = D.neg := by
      intro s hs' hs1
      have hs4ne : s ^ 4 ≠ 1 := fun h => hA ⟨D.ψ s, hs', hs1, s, rfl, h⟩
      have h1 := hS2 _ hs'
      have e4 : (D.ψ s) ^ 4 = (D.ψ s * D.ψ s) * (D.ψ s * D.ψ s) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      have e2 : (D.ψ s) ^ 2 = D.ψ s * D.ψ s := by
        simp only [pow_succ, pow_zero, one_mul]
      have hψ4 : D.ψ (s ^ 4) = 1 := by
        rw [map_pow, e4, h1, one_mul]
      have h2 : D.ψ (s ^ 2) = 1 := by
        rw [map_pow, e2, h1]
      have hsq : s ^ 4 * s ^ 4 = 1 := by
        have e : s ^ 4 * s ^ 4 = (s ^ 2) ^ 4 := by
          rw [← pow_mul, ← pow_add]
        rw [e]
        exact D.ker_pow_four _ h2
      rcases D.ker_sq _ hψ4 hsq with h | h
      · exact absurd h hs4ne
      · exact h
    obtain ⟨x, hx, x', hx', hx1, hx'1, hxx'⟩ := exists_two_nontrivial hS8
    have hxx'1 : x * x' ≠ 1 := by
      intro h
      apply hxx'
      symm
      calc x' = x⁻¹ * (x * x') := by group
        _ = x⁻¹ * 1 := by rw [h]
        _ = x := by rw [mul_one, inv_eq_of_mul_eq_one_right (hS2 x hx)]
    have hsx : D.ψ (D.lift x) = x := D.hlift x
    have hsx' : D.ψ (D.lift x') = x' := D.hlift x'
    have h4s := hneg4 (D.lift x) (by rw [hsx]; exact hx) (by rw [hsx]; exact hx1)
    have h4t := hneg4 (D.lift x') (by rw [hsx']; exact hx') (by rw [hsx']; exact hx'1)
    have hu := hneg4 (D.lift x * D.lift x')
      (by rw [map_mul, hsx, hsx']; exact S.mul_mem hx hx')
      (by rw [map_mul, hsx, hsx']; exact hxx'1)
    have hcomm : Commute (D.lift x) (D.lift x') :=
      D.lift_comm hS2 hS8 yl hyl hy hyS hfpf (by rw [hsx]; exact hx) (by rw [hsx']; exact hx')
    have h1 : (D.lift x * D.lift x') ^ 4 = 1 := by
      rw [hcomm.mul_pow, h4s, h4t, D.neg_mul_self]
    rw [h1] at hu
    exact D.neg_ne_one hu.symm

theorem sq_mul_central {t n : G} (hc : n * t = t * n) :
    (t * n) * (t * n) = (t * t) * (n * n) := by
  calc (t * n) * (t * n) = t * (n * t) * n := by group
    _ = t * (t * n) * n := by rw [hc]
    _ = (t * t) * (n * n) := by group

theorem nb_psi (b : Bool) : D.ψ (if b then D.neg else 1) = 1 := by
  cases b
  · simp
  · simpa using D.ker_neg

theorem nb_sq (b : Bool) : (if b then D.neg else 1) * (if b then D.neg else 1) = 1 := by
  cases b
  · simp
  · simpa using D.neg_mul_self

theorem nb_central (b : Bool) (g : G) :
    (if b then D.neg else 1) * g = g * (if b then D.neg else 1) := by
  cases b
  · simp
  · exact D.ker_central D.neg D.ker_neg g

theorem false_of_lift [Finite G] (D : LiftSetup G X) (hLA : ∀ A : Subgroup G,
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a * a = 1) → Nat.card A ≤ 8)
    {y : X} (hy : orderOf y = 7) {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1)
    (hS8 : Nat.card S = 8) (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S)
    (hfpf : ∀ s ∈ S, y * s * y⁻¹ = s → s = 1) : False := by
  obtain ⟨yl, hyl⟩ : ∃ yl : G, D.ψ yl = y := ⟨D.lift y, D.hlift y⟩
  obtain ⟨i, hi1, hi2⟩ := D.ker_sqrt
  let Sq : Subgroup G :=
    { carrier := {s : G | D.ψ s ∈ S ∧ s * s = 1}
      mul_mem' := by
        intro s t hs ht
        refine ⟨by rw [map_mul]; exact S.mul_mem hs.1 ht.1, ?_⟩
        have hc := D.lift_comm hS2 hS8 yl hyl hy hyS hfpf hs.1 ht.1
        calc s * t * (s * t) = s * (t * s) * t := by group
          _ = s * (s * t) * t := by rw [hc]
          _ = (s * s) * (t * t) := by group
          _ = 1 := by rw [hs.2, ht.2, one_mul]
      one_mem' := ⟨by rw [map_one]; exact S.one_mem, mul_one 1⟩
      inv_mem' := by
        intro s hs
        refine ⟨by rw [map_inv]; exact S.inv_mem hs.1, ?_⟩
        calc s⁻¹ * s⁻¹ = (s * s)⁻¹ := (mul_inv_rev s s).symm
          _ = 1 := by rw [hs.2, inv_one] }
  have hSqcomm : ∀ a ∈ Sq, ∀ b ∈ Sq, a * b = b * a :=
    fun a ha b hb => D.lift_comm hS2 hS8 yl hyl hy hyS hfpf ha.1 hb.1
  have hSqsq : ∀ a ∈ Sq, a * a = 1 := fun a ha => ha.2
  have hT : ∀ x : S, ∃ t : G, (D.ψ t ∈ S ∧ t * t = 1) ∧ D.ψ t = x.1 := by
    intro x
    obtain ⟨g, hg⟩ : ∃ g : G, D.ψ g = x.1 := ⟨D.lift x.1, D.hlift x.1⟩
    have hgS : D.ψ g ∈ S := by rw [hg]; exact x.2
    have hg4 : g ^ 4 = 1 := pow_four_of_mem D hS2 hS8 yl hyl hy hyS hfpf hgS
    have hcsq : g * g * (g * g) = 1 := by
      rw [← hg4]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    have hψgg : D.ψ (g * g) = 1 := by
      rw [map_mul, hg, hS2 x.1 x.2]
    rcases D.ker_sq (g * g) hψgg hcsq with h | h
    · exact ⟨g, ⟨hgS, h⟩, hg⟩
    · have hgi : i * g = g * i := D.ker_central i hi1 g
      have hsq : (g * i) * (g * i) = 1 := by
        calc g * i * (g * i) = g * (i * g) * i := by group
          _ = g * (g * i) * i := by rw [hgi]
          _ = (g * g) * (i * i) := by group
          _ = D.neg * D.neg := by rw [h, hi2]
          _ = 1 := D.neg_mul_self
      refine ⟨g * i, ⟨?_, hsq⟩, ?_⟩
      · rw [map_mul, hg, hi1, mul_one]
        exact x.2
      · rw [map_mul, hg, hi1, mul_one]
  choose T hTSq hTψ using hT
  have hf_mem : ∀ p : S × Bool, T p.1 * (if p.2 then D.neg else 1) ∈ Sq := by
    intro p
    refine ⟨?_, ?_⟩
    · rw [map_mul, hTψ p.1, nb_psi D p.2, mul_one]
      exact p.1.2
    · rw [sq_mul_central (nb_central D p.2 (T p.1)), (hTSq p.1).2, nb_sq D p.2, one_mul]
  let F : S × Bool → Sq := fun p => ⟨T p.1 * (if p.2 then D.neg else 1), hf_mem p⟩
  have hFinj : Function.Injective F := by
    rintro ⟨x, b⟩ ⟨x', b'⟩ h
    have h' : T x * (if b then D.neg else 1) = T x' * (if b' then D.neg else 1) :=
      congrArg Subtype.val h
    have hxx : x = x' := by
      apply Subtype.ext
      have h1 := congrArg D.ψ h'
      rw [map_mul, map_mul, hTψ, hTψ, nb_psi D b, nb_psi D b', mul_one, mul_one] at h1
      exact h1
    subst hxx
    have hb : (if b then D.neg else 1) = (if b' then D.neg else 1) := mul_left_cancel h'
    cases b <;> cases b'
    · rfl
    · exact absurd (by simpa using hb.symm) D.neg_ne_one
    · exact absurd (by simpa using hb) D.neg_ne_one
    · rfl
  have hcard : Nat.card (S × Bool) ≤ Nat.card Sq := Nat.card_le_card_of_injective F hFinj
  rw [Nat.card_prod, hS8, Nat.card_eq_fintype_card, Fintype.card_bool] at hcard
  have hle := hLA Sq hSqcomm hSqsq
  omega

end LiftSetup

end CFSG.GF2Type.Smith1979.Case2.U43Grp
