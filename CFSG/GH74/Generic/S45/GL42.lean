module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GH74.Generic.S45

open Subgroup MulAction

section Fixed

variable {T : Type} [Group T]

@[expose] def fixSub (S : Subgroup (MulAut T)) : Subgroup T where
  carrier := {t | ∀ f ∈ S, f t = t}
  one_mem' := fun f _ => map_one f
  mul_mem' := fun {a b} ha hb f hf => by rw [map_mul, ha f hf, hb f hf]
  inv_mem' := fun {a} ha f hf => by rw [map_inv, ha f hf]

theorem fix_mem_zpowers {g : MulAut T} {t : T} (ht : g t = t) : t ∈ fixSub (zpowers g) := by
  intro f hf
  have h1 : zpowers g ≤ MulAction.stabilizer (MulAut T) t := by
    rw [zpowers_le]
    exact MulAction.mem_stabilizer_iff.2 ht
  exact MulAction.mem_stabilizer_iff.1 (h1 hf)

theorem fix_eq_top_imp_one (g : MulAut T) (h : fixSub (zpowers g) = ⊤) : g = 1 := by
  apply MulEquiv.ext
  intro t
  have : t ∈ fixSub (zpowers g) := by rw [h]; trivial
  exact this g (mem_zpowers g)

variable [Finite T]

theorem card_fixSub_modEq (g : MulAut T) (p : ℕ) [Fact p.Prime] (hg : orderOf g = p) :
    Nat.card T ≡ Nat.card ↥(fixSub (zpowers g)) [MOD p] := by
  have hP : IsPGroup p ↥(zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have h := hP.card_modEq_card_fixedPoints T
  have : Nat.card (fixedPoints ↥(zpowers g) T) = Nat.card ↥(fixSub (zpowers g)) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun t => ?_)
    constructor
    · intro ht f hf
      exact ht ⟨f, hf⟩
    · intro ht f
      exact ht f f.2
  rwa [this] at h

theorem key5 : ∀ c : ℕ, c ∣ 16 → 16 ≡ c [MOD 5] → c = 1 ∨ c = 16 := by
  intro c h2 h1
  have hle : c ≤ 16 := Nat.le_of_dvd (by norm_num) h2
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos h2 (by norm_num)
  unfold Nat.ModEq at h1
  interval_cases c <;> omega

theorem key7 : ∀ c : ℕ, c ∣ 16 → 16 ≡ c [MOD 7] → c = 2 ∨ c = 16 := by
  intro c h2 h1
  have hle : c ≤ 16 := Nat.le_of_dvd (by norm_num) h2
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos h2 (by norm_num)
  unfold Nat.ModEq at h1
  interval_cases c <;> omega

theorem fix_five (hT : Nat.card T = 16) (g : MulAut T) (hg : orderOf g = 5) (t : T)
    (ht : g t = t) : t = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h1 := card_fixSub_modEq g 5 hg
  rw [hT] at h1
  have h2 : Nat.card ↥(fixSub (zpowers g)) ∣ 16 := hT ▸ Subgroup.card_subgroup_dvd_card _
  rcases key5 _ h2 h1 with h3 | h3
  · have hbot : fixSub (zpowers g) = ⊥ := Subgroup.card_eq_one.1 h3
    have := fix_mem_zpowers ht
    rw [hbot] at this
    exact (Subgroup.mem_bot).1 this
  · exfalso
    have htop : fixSub (zpowers g) = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hT]
      exact h3
    have : g = 1 := fix_eq_top_imp_one g htop
    rw [this, orderOf_one] at hg
    omega

theorem fix_seven (hT : Nat.card T = 16) (g : MulAut T) (hg : orderOf g = 7) :
    ∃ u : T, u ≠ 1 ∧ g u = u ∧ ∀ t : T, g t = t → t = 1 ∨ t = u := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h1 := card_fixSub_modEq g 7 hg
  rw [hT] at h1
  have h2 : Nat.card ↥(fixSub (zpowers g)) ∣ 16 := hT ▸ Subgroup.card_subgroup_dvd_card _
  rcases key7 _ h2 h1 with h3 | h3
  · obtain ⟨u, hu1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(fixSub (zpowers g)))).1 h3
    refine ⟨(u : T), fun h => hu1 (Subtype.ext h), ?_, ?_⟩
    · exact u.2 g (mem_zpowers g)
    · intro t ht
      by_cases ht1 : t = 1
      · exact Or.inl ht1
      · right
        have := huniq ⟨t, fix_mem_zpowers ht⟩ (fun h => ht1 (congrArg Subtype.val h))
        exact congrArg Subtype.val this
  · exfalso
    have htop : fixSub (zpowers g) = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hT]
      exact h3
    have : g = 1 := fix_eq_top_imp_one g htop
    rw [this, orderOf_one] at hg
    omega

end Fixed

section Abstract

variable {T : Type} [Group T] [Finite T] {H : Type} [Group H] [Finite H]

theorem commute_of_normalizer_five {Q : Subgroup H} (hQ : Nat.card Q = 5)
    {n : H} (hn : n ∈ normalizer (Q : Set H)) (hcop : Nat.Coprime (orderOf n) 4) {b : H}
    (hb : b ∈ Q) : n * b = b * n := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsCyclic Q := isCyclic_of_prime_card hQ
  have h4 : Nat.card (MulAut Q) = 4 := by
    rw [IsCyclic.card_mulAut, hQ]
    decide +kernel
  let n' : ↥(normalizer (Q : Set H)) := ⟨n, hn⟩
  have h1 : orderOf (Q.normalizerMonoidHom n') ∣ 4 := h4 ▸ orderOf_dvd_natCard _
  have h2 : orderOf (Q.normalizerMonoidHom n') ∣ orderOf n :=
    (orderOf_map_dvd Q.normalizerMonoidHom n').trans (by rw [Subgroup.orderOf_mk])
  have h3 : orderOf (Q.normalizerMonoidHom n') = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1
  have h5 : Q.normalizerMonoidHom n' = 1 := orderOf_eq_one_iff.1 h3
  have h6 := congrArg (fun f : MulAut Q => ((f ⟨b, hb⟩ : Q) : H)) h5
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h6
  exact mul_inv_eq_iff_eq_mul.1 h6

theorem sylow_card_seven (hH : Nat.card H = 315) (P : Sylow 7 H) : Nat.card P = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [P.card_eq_multiplicity, hH]
  have : (315 : ℕ).factorization 7 = 1 := by
    rw [Nat.factorization_def _ (by norm_num : Nat.Prime 7)]
    decide +kernel
  rw [this]; norm_num

theorem sylow_card_five (hH : Nat.card H = 315) (P : Sylow 5 H) : Nat.card P = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [P.card_eq_multiplicity, hH]
  have : (315 : ℕ).factorization 5 = 1 := by
    rw [Nat.factorization_def _ (by norm_num : Nat.Prime 5)]
    decide +kernel
  rw [this]; norm_num

theorem n7_cases (hH : Nat.card H = 315) :
    Nat.card (Sylow 7 H) = 1 ∨ Nat.card (Sylow 7 H) = 15 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 H) := inferInstance
  have h1 : Nat.card (Sylow 7 H) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 H
  have h2 : Nat.card (Sylow 7 H) ∣ (P : Subgroup H).index := P.card_dvd_index
  have h3 : (P : Subgroup H).index = 45 := by
    have := Subgroup.card_mul_index (P : Subgroup H)
    rw [sylow_card_seven hH P, hH] at this
    omega
  rw [h3] at h2
  have hle : Nat.card (Sylow 7 H) ≤ 45 := Nat.le_of_dvd (by norm_num) h2
  have hpos : 0 < Nat.card (Sylow 7 H) := Nat.pos_of_dvd_of_pos h2 (by norm_num)
  generalize Nat.card (Sylow 7 H) = n at *
  unfold Nat.ModEq at h1
  interval_cases n <;> omega

theorem n5_cases (hH : Nat.card H = 315) :
    Nat.card (Sylow 5 H) = 1 ∨ Nat.card (Sylow 5 H) = 21 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 H) := inferInstance
  have h1 : Nat.card (Sylow 5 H) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 H
  have h2 : Nat.card (Sylow 5 H) ∣ (P : Subgroup H).index := P.card_dvd_index
  have h3 : (P : Subgroup H).index = 63 := by
    have := Subgroup.card_mul_index (P : Subgroup H)
    rw [sylow_card_five hH P, hH] at this
    omega
  rw [h3] at h2
  have hle : Nat.card (Sylow 5 H) ≤ 63 := Nat.le_of_dvd (by norm_num) h2
  have hpos : 0 < Nat.card (Sylow 5 H) := Nat.pos_of_dvd_of_pos h2 (by norm_num)
  generalize Nat.card (Sylow 5 H) = n at *
  unfold Nat.ModEq at h1
  interval_cases n <;> omega

section Faithful

variable (φ : H →* MulAut T) (hφ : Function.Injective φ)
include hφ

omit [Finite H] in
theorem faithful_fix_five (hT : Nat.card T = 16) (b : H) (hb : orderOf b = 5) (t : T) (ht : φ b t = t) :
    t = 1 :=
  fix_five hT (φ b) (by rw [orderOf_injective φ hφ b, hb]) t ht

omit [Finite H] in
theorem faithful_fix_seven (hT : Nat.card T = 16) (a : H) (ha : orderOf a = 7) :
    ∃ u : T, u ≠ 1 ∧ φ a u = u ∧ ∀ t : T, φ a t = t → t = 1 ∨ t = u :=
  fix_seven hT (φ a) (by rw [orderOf_injective φ hφ a, ha])

omit [Finite H] in
theorem faithful_not_commute (hT : Nat.card T = 16) (a b : H) (ha : orderOf a = 7) (hb : orderOf b = 5) :
    a * b ≠ b * a := by
  intro hab
  obtain ⟨u, hu1, hau, huniq⟩ := faithful_fix_seven φ hφ hT a ha
  have h1 : φ a (φ b u) = φ b u := by
    have h2 : φ (a * b) u = φ (b * a) u := by rw [hab]
    simpa [map_mul, MulAut.mul_apply, hau] using h2
  rcases huniq _ h1 with h | h
  · apply hu1
    have : φ b u = φ b 1 := by rw [h, map_one]
    exact (φ b).injective this
  · exact hu1 (faithful_fix_five φ hφ hT b hb u h)

theorem n7_ne_one (hT : Nat.card T = 16) (hH : Nat.card H = 315) :
    Nat.card (Sylow 7 H) ≠ 1 := by
  intro h1
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := H) 7 (by rw [hH]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 (by rw [hH]; norm_num)
  obtain ⟨u, hu1, hau, huniq⟩ := faithful_fix_seven φ hφ hT a ha
  have hcardZ : Nat.card ↥(zpowers a) = 7 := by rw [Nat.card_zpowers, ha]
  have hPg : IsPGroup 7 ↥(zpowers a) := IsPGroup.of_card (n := 1) (by rw [hcardZ, pow_one])
  have hidx : ¬ 7 ∣ (zpowers a).index := by
    have := Subgroup.card_mul_index (zpowers a)
    rw [hcardZ, hH] at this
    have h45 : (zpowers a).index = 45 := by omega
    rw [h45]; norm_num
  let P : Sylow 7 H := hPg.toSylow hidx
  have hsub : Subsingleton (Sylow 7 H) := (Nat.card_eq_one_iff_unique.1 h1).1
  have hPn : (zpowers a).Normal := Sylow.normal_of_subsingleton P
  have hc : b⁻¹ * a * b ∈ zpowers a := by
    have := hPn.conj_mem a (mem_zpowers a) b⁻¹
    simpa using this
  have hfix : ∀ c ∈ zpowers a, φ c u = u := by
    intro c hc'
    have h1 : zpowers a ≤ (MulAction.stabilizer (MulAut T) u).comap φ := by
      rw [zpowers_le]
      exact MulAction.mem_stabilizer_iff.2 hau
    exact MulAction.mem_stabilizer_iff.1 (h1 hc')
  have h2 : φ a (φ b u) = φ b u := by
    have h3 : φ a (φ b u) = φ b (φ (b⁻¹ * a * b) u) := by
      have h5 : φ (a * b) = φ (b * (b⁻¹ * a * b)) := by congr 1; group
      calc φ a (φ b u) = φ (a * b) u := by simp [map_mul, MulAut.mul_apply]
        _ = φ (b * (b⁻¹ * a * b)) u := by rw [h5]
        _ = φ b (φ (b⁻¹ * a * b) u) := by simp [map_mul, MulAut.mul_apply]
    rw [h3, hfix _ hc]
  rcases huniq _ h2 with h | h
  · apply hu1
    have : φ b u = φ b 1 := by rw [h, map_one]
    exact (φ b).injective this
  · exact hu1 (faithful_fix_five φ hφ hT b hb u h)

theorem n5_ne_one (hT : Nat.card T = 16) (hH : Nat.card H = 315) :
    Nat.card (Sylow 5 H) ≠ 1 := by
  intro h1
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := H) 7 (by rw [hH]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 (by rw [hH]; norm_num)
  have hcardZ : Nat.card ↥(zpowers b) = 5 := by rw [Nat.card_zpowers, hb]
  have hPg : IsPGroup 5 ↥(zpowers b) := IsPGroup.of_card (n := 1) (by rw [hcardZ, pow_one])
  have hidx : ¬ 5 ∣ (zpowers b).index := by
    have := Subgroup.card_mul_index (zpowers b)
    rw [hcardZ, hH] at this
    have h63 : (zpowers b).index = 63 := by omega
    rw [h63]; norm_num
  let P : Sylow 5 H := hPg.toSylow hidx
  have hsub : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.1 h1).1
  have hPn : (zpowers b).Normal := Sylow.normal_of_subsingleton P
  have hn : a ∈ normalizer ((zpowers b : Subgroup H) : Set H) := by
    rw [Subgroup.normalizer_eq_top]; trivial
  have hcop : Nat.Coprime (orderOf a) 4 := by rw [ha]; norm_num
  exact faithful_not_commute φ hφ hT a b ha hb (commute_of_normalizer_five hcardZ hn hcop (mem_zpowers b))

end Faithful

end Abstract

section Count

variable {H : Type} [Group H] [Finite H]

theorem sylow_eq_of_mem (p : ℕ) [Fact p.Prime] {P P' : Sylow p H} (hP : Nat.card P = p)
    (hP' : Nat.card P' = p) {x : H} (hx : x ∈ (P : Subgroup H)) (hx' : x ∈ (P' : Subgroup H))
    (hx1 : x ≠ 1) : P = P' := by
  have key : ∀ Q : Sylow p H, Nat.card Q = p → x ∈ (Q : Subgroup H) →
      zpowers x = (Q : Subgroup H) := by
    intro Q hQ hxQ
    have h1 : orderOf x ∣ p := hQ ▸ Subgroup.orderOf_dvd_natCard (Q : Subgroup H) hxQ
    have h2 : orderOf x = p :=
      ((Nat.dvd_prime Fact.out).1 h1).resolve_left (fun h => hx1 (orderOf_eq_one_iff.1 h))
    apply Subgroup.eq_of_le_of_card_ge
    · rw [zpowers_le]; exact hxQ
    · rw [Nat.card_zpowers, h2]
      exact le_of_eq hQ
  exact Sylow.ext ((key P hP hx).symm.trans (key P' hP' hx'))

theorem exists_finset_prime_order (p : ℕ) [Fact p.Prime] (hp : ∀ P : Sylow p H, Nat.card P = p) :
    ∃ U : Finset H, (∀ x ∈ U, orderOf x = p) ∧ U.card = (p - 1) * Nat.card (Sylow p H) := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have : Fintype (Sylow p H) := Fintype.ofFinite _
  let t : Sylow p H → Finset H := fun P =>
    (Finset.univ.filter (fun x => x ∈ (P : Subgroup H))).erase 1
  have ht : ∀ P x, x ∈ t P ↔ x ≠ 1 ∧ x ∈ (P : Subgroup H) := by
    intro P x
    simp [t]
  have hdisj : ∀ P ∈ (Finset.univ : Finset (Sylow p H)), ∀ P' ∈ (Finset.univ : Finset (Sylow p H)),
      P ≠ P' → Disjoint (t P) (t P') := by
    intro P _ P' _ hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [ht] at hx hx'
    exact hne (sylow_eq_of_mem p (hp P) (hp P') hx.2 hx'.2 hx.1)
  refine ⟨Finset.univ.biUnion t, ?_, ?_⟩
  · intro x hx
    obtain ⟨P, -, hxP⟩ := Finset.mem_biUnion.1 hx
    rw [ht] at hxP
    have h1 : orderOf x ∣ p := hp P ▸ Subgroup.orderOf_dvd_natCard (P : Subgroup H) hxP.2
    exact ((Nat.dvd_prime Fact.out).1 h1).resolve_left (fun h => hxP.1 (orderOf_eq_one_iff.1 h))
  · rw [Finset.card_biUnion hdisj]
    have hcard : ∀ P : Sylow p H, (t P).card = p - 1 := by
      intro P
      have h1 : (Finset.univ.filter (fun x => x ∈ (P : Subgroup H))).card =
          Nat.card ↥(P : Subgroup H) := by
        rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
      simp only [t]
      rw [Finset.card_erase_of_mem (by simp), h1, hp P]
    simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Nat.card_eq_fintype_card, mul_comm]

theorem exists_family (hH : Nat.card H = 315) (h5 : Nat.card (Sylow 5 H) = 21) :
    ∃ V : Finset H, (∀ x ∈ V, x ^ 15 = 1 ∧ x ≠ 1) ∧ V.card = 12 * Nat.card (Sylow 5 H) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fintype H := Fintype.ofFinite H
  have : Fintype (Sylow 5 H) := Fintype.ofFinite _
  have hN : ∀ Q : Sylow 5 H, Nat.card ↥(normalizer ((Q : Subgroup H) : Set H)) = 15 := by
    intro Q
    have h1 := Sylow.card_eq_index_normalizer Q
    have h2 := Subgroup.card_mul_index (normalizer ((Q : Subgroup H) : Set H))
    rw [h5] at h1
    have h1' : (normalizer ((Q : Subgroup H) : Set H)).index = 21 := h1.symm
    rw [h1', hH] at h2
    omega
  have hex : ∀ Q : Sylow 5 H, ∃ c : H, orderOf c = 3 ∧ ∀ b ∈ (Q : Subgroup H), c * b = b * c := by
    intro Q
    obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(normalizer ((Q : Subgroup H) : Set H))) 3 (by rw [hN Q]; norm_num)
    refine ⟨(c' : H), by rw [Subgroup.orderOf_coe]; exact hc', fun b hb => ?_⟩
    have hcop : Nat.Coprime (orderOf (c' : H)) 4 := by
      rw [Subgroup.orderOf_coe, hc']; norm_num
    exact commute_of_normalizer_five (sylow_card_five hH Q) c'.2 hcop hb
  choose cQ hcQ using hex
  let B : Sylow 5 H → Finset H := fun Q =>
    (Finset.univ.filter (fun x => x ∈ (Q : Subgroup H))).erase 1
  let C : Sylow 5 H → Finset H := fun Q =>
    Finset.univ.filter (fun x => x ∈ zpowers (cQ Q))
  let V' : Sylow 5 H → Finset H := fun Q => (B Q ×ˢ C Q).image (fun p => p.1 * p.2)
  have hB : ∀ (Q : Sylow 5 H) (x : H), x ∈ B Q ↔ x ≠ 1 ∧ x ∈ (Q : Subgroup H) := by
    intro Q x; simp [B]
  have hC : ∀ (Q : Sylow 5 H) (x : H), x ∈ C Q ↔ x ∈ zpowers (cQ Q) := by
    intro Q x; simp [C]
  have hBcard : ∀ Q : Sylow 5 H, (B Q).card = 4 := by
    intro Q
    have h1 : (Finset.univ.filter (fun x => x ∈ (Q : Subgroup H))).card =
        Nat.card ↥(Q : Subgroup H) := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    simp only [B]
    rw [Finset.card_erase_of_mem (by simp), h1, sylow_card_five hH Q]
  have hCcard : ∀ Q : Sylow 5 H, (C Q).card = 3 := by
    intro Q
    have h1 : (Finset.univ.filter (fun x => x ∈ zpowers (cQ Q))).card =
        Nat.card ↥(zpowers (cQ Q)) := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    simp only [C]
    rw [h1, Nat.card_zpowers, (hcQ Q).1]
  have hinter : ∀ (Q : Sylow 5 H) (z : H), z ∈ (Q : Subgroup H) → z ∈ zpowers (cQ Q) → z = 1 := by
    intro Q z hzQ hzC
    have h1 : orderOf z ∣ 5 := (sylow_card_five hH Q) ▸ Subgroup.orderOf_dvd_natCard _ hzQ
    have h2 : orderOf z ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard (zpowers (cQ Q)) hzC
      rwa [Nat.card_zpowers, (hcQ Q).1] at this
    have h3 : orderOf z ∣ Nat.gcd 5 3 := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 5 3 = 1 := by norm_num
    rw [h4] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hcomm : ∀ (Q : Sylow 5 H) (c : H), c ∈ zpowers (cQ Q) →
      ∀ b ∈ (Q : Subgroup H), c * b = b * c := by
    intro Q c hc b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    have h : Commute (cQ Q) b := (hcQ Q).2 b hb
    exact (Commute.zpow_left h k).eq
  have hc3 : ∀ (Q : Sylow 5 H) (c : H), c ∈ zpowers (cQ Q) → c ^ 3 = 1 := by
    intro Q c hc
    have := Subgroup.orderOf_dvd_natCard (zpowers (cQ Q)) hc
    rw [Nat.card_zpowers, (hcQ Q).1] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hb5 : ∀ (Q : Sylow 5 H) (b : H), b ∈ (Q : Subgroup H) → b ^ 5 = 1 := by
    intro Q b hb
    have := Subgroup.orderOf_dvd_natCard (Q : Subgroup H) hb
    rw [sylow_card_five hH Q] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hcube : ∀ (Q : Sylow 5 H) (b c : H), b ∈ (Q : Subgroup H) → c ∈ zpowers (cQ Q) →
      (b * c) ^ 3 = b ^ 3 := by
    intro Q b c hb hc
    have hcm : Commute b c := (hcomm Q c hc b hb).symm
    rw [hcm.mul_pow, hc3 Q c hc, mul_one]
  have hb3 : ∀ (Q : Sylow 5 H) (b : H), b ∈ (Q : Subgroup H) → b ≠ 1 → b ^ 3 ≠ 1 := by
    intro Q b hb hb1 h3
    apply hb1
    have h2 : b ^ 2 = 1 := by
      calc b ^ 2 = b ^ 5 * (b ^ 3)⁻¹ := by group
        _ = 1 := by rw [hb5 Q b hb, h3]; simp
    calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  have hBC : ∀ (Q : Sylow 5 H) (b b' c c' : H), b ∈ B Q → b' ∈ B Q → c ∈ C Q → c' ∈ C Q →
      b * c = b' * c' → b = b' ∧ c = c' := by
    intro Q b b' c c' hb hb' hc hc' h
    rw [hB] at hb hb'
    rw [hC] at hc hc'
    have h1 : b'⁻¹ * b = c' * c⁻¹ := by
      have : b = b' * c' * c⁻¹ := by rw [← h]; group
      rw [this]; group
    have h2 : b'⁻¹ * b ∈ (Q : Subgroup H) := mul_mem (inv_mem hb'.2) hb.2
    have h3 : b'⁻¹ * b ∈ zpowers (cQ Q) := by rw [h1]; exact mul_mem hc' (inv_mem hc)
    have h4 := hinter Q _ h2 h3
    have hbb : b = b' := (inv_mul_eq_one.1 h4).symm
    refine ⟨hbb, ?_⟩
    rw [hbb] at h
    exact mul_left_cancel h
  have hmemV : ∀ (Q : Sylow 5 H) (x : H), x ∈ V' Q ↔
      ∃ b c, b ∈ B Q ∧ c ∈ C Q ∧ b * c = x := by
    intro Q x
    simp only [V', Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨b, c, ⟨hb, hc⟩, rfl⟩
      exact ⟨b, c, hb, hc, rfl⟩
    · rintro ⟨b, c, hb, hc, rfl⟩
      exact ⟨b, c, ⟨hb, hc⟩, rfl⟩
  have hV'card : ∀ Q : Sylow 5 H, (V' Q).card = 12 := by
    intro Q
    have hinj : Set.InjOn (fun p : H × H => p.1 * p.2)
        ((B Q ×ˢ C Q : Finset (H × H)) : Set (H × H)) := by
      rintro ⟨b, c⟩ hbc ⟨b', c'⟩ hbc' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hbc hbc'
      obtain ⟨h1, h2⟩ := hBC Q b b' c c' hbc.1 hbc'.1 hbc.2 hbc'.2 h
      rw [h1, h2]
    simp only [V']
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, hBcard, hCcard]
  have hV'prop : ∀ (Q : Sylow 5 H) (x : H), x ∈ V' Q →
      ∃ b ∈ (Q : Subgroup H), b ≠ 1 ∧ x ^ 3 = b ^ 3 := by
    intro Q x hx
    obtain ⟨b, c, hb, hc, rfl⟩ := (hmemV Q x).1 hx
    rw [hB] at hb
    rw [hC] at hc
    exact ⟨b, hb.2, hb.1, hcube Q b c hb.2 hc⟩
  have hV'disj : ∀ Q ∈ (Finset.univ : Finset (Sylow 5 H)),
      ∀ Q' ∈ (Finset.univ : Finset (Sylow 5 H)), Q ≠ Q' → Disjoint (V' Q) (V' Q') := by
    intro Q _ Q' _ hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨b, hb, hb1, hxb⟩ := hV'prop Q x hx
    obtain ⟨b', hb', hb1', hxb'⟩ := hV'prop Q' x hx'
    have hz : b ^ 3 = b' ^ 3 := hxb.symm.trans hxb'
    apply hne
    refine sylow_eq_of_mem 5 (sylow_card_five hH Q) (sylow_card_five hH Q') (x := b ^ 3) ?_ ?_
      (hb3 Q b hb hb1)
    · exact pow_mem hb 3
    · rw [hz]; exact pow_mem hb' 3
  refine ⟨Finset.univ.biUnion V', ?_, ?_⟩
  · intro x hx
    obtain ⟨Q, -, hxQ⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨b, hb, hb1, hxb⟩ := hV'prop Q x hxQ
    refine ⟨?_, ?_⟩
    · have : x ^ 15 = (x ^ 3) ^ 5 := by rw [← pow_mul]
      rw [this, hxb, ← pow_mul, mul_comm, pow_mul, hb5 Q b hb, one_pow]
    · intro h1
      rw [h1, one_pow] at hxb
      exact hb3 Q b hb hb1 hxb.symm
  · rw [Finset.card_biUnion hV'disj]
    simp only [hV'card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Nat.card_eq_fintype_card, mul_comm]

theorem count_contra (hH : Nat.card H = 315) (h7 : Nat.card (Sylow 7 H) = 15)
    (h5 : Nat.card (Sylow 5 H) = 21) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fintype H := Fintype.ofFinite H
  obtain ⟨U7, hU7ord, hU7card⟩ := exists_finset_prime_order 7 (sylow_card_seven hH)
  obtain ⟨V, hV, hVcard⟩ := exists_family hH h5
  rw [h7] at hU7card
  rw [h5] at hVcard
  have hd1 : Disjoint U7 V := by
    rw [Finset.disjoint_left]
    intro x hx hxV
    have h1 : orderOf x = 7 := hU7ord x hx
    have h2 : orderOf x ∣ 15 := orderOf_dvd_of_pow_eq_one (hV x hxV).1
    rw [h1] at h2
    omega
  have hd2 : (1 : H) ∉ U7 ∪ V := by
    intro h
    rcases Finset.mem_union.1 h with h | h
    · have := hU7ord 1 h
      rw [orderOf_one] at this
      omega
    · exact (hV 1 h).2 rfl
  have hcard : (insert 1 (U7 ∪ V)).card = 1 + (7 - 1) * 15 + 12 * 21 := by
    rw [Finset.card_insert_of_notMem hd2, Finset.card_union_of_disjoint hd1, hU7card, hVcard]
  have hle := Finset.card_le_univ (insert 1 (U7 ∪ V))
  rw [← Nat.card_eq_fintype_card, hH] at hle
  omega

end Count

theorem no_subgroup_card_315 (T : Type) [Group T] [Finite T] (hcard : Nat.card T = 16)
    (A : Subgroup (MulAut T)) : Nat.card ↥A ≠ 315 := by
  intro hA
  rcases n7_cases hA with h7 | h7
  · exact n7_ne_one A.subtype Subtype.val_injective hcard hA h7
  rcases n5_cases hA with h5 | h5
  · exact n5_ne_one A.subtype Subtype.val_injective hcard hA h5
  exact count_contra hA h7 h5

end CFSG.GH74.Generic.S45
