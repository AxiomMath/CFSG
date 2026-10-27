module

public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofA6Fin

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open CFSG.RankThree.PartTwo.Sec15.Push153B.A6

section Three

theorem f3b_check : Core.autL.all (fun u => !(Core.cmul u u == Core.cid) || u == Core.cid ||
    !(commC u tAddC) || !(Out21.A6.inM10C u)) = true := by
  decide +kernel

theorem conj_data {x : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {u : P10}
    (hu : u ∈ A6Models.autA6) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hux : u * x = x * u) :
    ∃ g ∈ A6Models.autA6, g * x * g⁻¹ = A6Models.tAdd ∧
      (g * u * g⁻¹) ∈ A6Models.autA6 ∧ (g * u * g⁻¹) * (g * u * g⁻¹) = 1 ∧ g * u * g⁻¹ ≠ 1 ∧
      (g * u * g⁻¹) * A6Models.tAdd = A6Models.tAdd * (g * u * g⁻¹) := by
  obtain ⟨g, hg, hgx⟩ := exists_conj_tAdd hx hx3 hx1
  refine ⟨g, hg, hgx, ?_, ?_, ?_, ?_⟩
  · exact A6Models.autA6.mul_mem (A6Models.autA6.mul_mem hg hu) (A6Models.autA6.inv_mem hg)
  · calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  · intro h
    apply hu1
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this
  · rw [← hgx]
    calc g * u * g⁻¹ * (g * x * g⁻¹) = g * (u * x) * g⁻¹ := by group
      _ = g * (x * u) * g⁻¹ := by rw [hux]
      _ = g * x * g⁻¹ * (g * u * g⁻¹) := by group

theorem f3c_check : Core.autL.all (fun u => !(Core.cmul u u == Core.cid) || u == Core.cid ||
    !(commC u tAddC) || t9c.any fun t => !(commC t u) &&
      cubeC (Core.cmul u (conjC t u)) == Core.cid) = true := by
  decide +kernel

theorem exists_conj_involution_prod_three {x : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {u : P10} (hu : u ∈ A6Models.autA6) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hux : u * x = x * u) :
    ∃ a ∈ A6Models.psl29, a * x = x * a ∧ (u * (a * u * a⁻¹)) ^ 3 = 1 ∧ a * u * a⁻¹ ≠ u := by
  obtain ⟨g, hg, hgx, hu', hu'2, hu'1, hu'x⟩ := conj_data hx hx3 hx1 hu hu2 hu1 hux
  set u' := g * u * g⁻¹ with hu'def
  have hf := List.all_eq_true.mp f3c_check (code u') (code_mem_autL hu')
  have e1 : (Core.cmul (code u') (code u') == Core.cid) = true := by
    rw [← code_mul, hu'2, code_one]; simp
  have e2 : (code u' == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]; exact hu'1
  have e3 : commC (code u') tAddC = true := by
    rw [← code_tAdd, commC_iff]; exact hu'x
  rw [e1, e2, e3] at hf
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    beq_iff_eq] at hf
  obtain ⟨tc, htc, hnc, hcube⟩ := hf
  have ht9 := List.all_eq_true.mp t9_check tc htc
  simp only [Bool.and_eq_true, beq_iff_eq] at ht9
  obtain ⟨⟨⟨htpsl, htcube⟩, htcomm⟩, -⟩ := ht9
  obtain ⟨tp, htppsl, rfl⟩ := exists_psl29_of_code (contains_iff.mp htpsl)
  have htp3 : tp ^ 3 = 1 := (cubeC_eq_cid_iff tp).mp htcube
  have htpx : tp * A6Models.tAdd = A6Models.tAdd * tp := by
    rw [← commC_iff, code_tAdd]; exact htcomm
  have htpinv : tp⁻¹ = tp * tp := inv_eq_sq htp3
  have hcubep : (u' * (tp * u' * (tp * tp))) ^ 3 = 1 := by
    rw [code_conjC, ← code_mul] at hcube
    exact (cubeC_eq_cid_iff _).mp hcube
  have hnc' : ¬ (tp * u' = u' * tp) := by
    intro h'
    have hc : commC (code tp) (code u') = true := (commC_iff _ _).mpr h'
    rw [hc] at hnc
    exact Bool.noConfusion hnc
  refine ⟨g⁻¹ * tp * g, ?_, ?_, ?_, ?_⟩
  · have := psl29_normal _ (A6Models.autA6.inv_mem hg) _ htppsl
    simpa using this
  · have hx' : x = g⁻¹ * A6Models.tAdd * g := by rw [← hgx]; group
    rw [hx']
    calc g⁻¹ * tp * g * (g⁻¹ * A6Models.tAdd * g) = g⁻¹ * (tp * A6Models.tAdd) * g := by group
      _ = g⁻¹ * (A6Models.tAdd * tp) * g := by rw [htpx]
      _ = g⁻¹ * A6Models.tAdd * g * (g⁻¹ * tp * g) := by group
  · have e : u * (g⁻¹ * tp * g * u * (g⁻¹ * tp * g)⁻¹) =
        g⁻¹ * (u' * (tp * u' * (tp * tp))) * g := by
      rw [← htpinv, hu'def]; group
    rw [e, show g⁻¹ * (u' * (tp * u' * (tp * tp))) * g =
      g⁻¹ * (u' * (tp * u' * (tp * tp))) * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hcubep]
    group
  · intro h
    apply hnc'
    have h1 : tp * u' * tp⁻¹ = u' := by
      calc tp * u' * tp⁻¹ = g * (g⁻¹ * tp * g * u * (g⁻¹ * tp * g)⁻¹) * g⁻¹ := by
            rw [hu'def]; group
        _ = g * u * g⁻¹ := by rw [h]
        _ = u' := hu'def.symm
    exact mul_inv_eq_iff_eq_mul.1 h1

theorem eq_one_of_mem_m10_involution {x : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {u : P10} (hu : u ∈ A6Models.autA6) (hum : u ∈ A6Models.m10) (hu2 : u * u = 1)
    (hux : u * x = x * u) : u = 1 := by
  by_contra hu1
  obtain ⟨g, hg, hgx, hu', hu'2, hu'1, hu'x⟩ := conj_data hx hx3 hx1 hu hu2 hu1 hux
  set u' := g * u * g⁻¹ with hu'def
  have hu'm : u' ∈ A6Models.m10 := m10_conj_mem hg hum
  have hf := List.all_eq_true.mp f3b_check (code u') (code_mem_autL hu')
  have e1 : (Core.cmul (code u') (code u') == Core.cid) = true := by
    rw [← code_mul, hu'2, code_one]; simp
  have e2 : (code u' == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]; exact hu'1
  have e3 : commC (code u') tAddC = true := by
    rw [← code_tAdd, commC_iff]; exact hu'x
  have e4 : Out21.A6.inM10C (code u') = true := (Out21.A6.mem_m10_iff_code u').mp hu'm
  rw [e1, e2, e3, e4] at hf
  simp at hf

end Three

theorem exists_autA6_of_code' {c : List ℕ} (hc : c ∈ Core.autL) :
    ∃ x ∈ A6Models.autA6, code x = c := by
  unfold Core.autL at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨y, hy, hc⟩ := hc
  rw [List.mem_map] at hc
  obtain ⟨r, hr, rfl⟩ := hc
  obtain ⟨y', hy', rfl⟩ := exists_psl29_of_code hy
  rw [← autRepsP_code] at hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  have hr'mem : r' ∈ A6Models.autA6 := by rw [autA6_eq]; exact autReps_mem_closure r' hr'
  exact ⟨y' * r', A6Models.autA6.mul_mem (psl29_le_autA6 hy') hr'mem, by rw [code_mul]⟩

section Five

@[expose] def x5C : List ℕ := [9, 4, 7, 2, 6, 3, 0, 8, 5, 1]

@[expose] def u5C : List ℕ := [3, 7, 9, 0, 8, 6, 5, 1, 4, 2]

@[expose] def c5L : List (List ℕ) := Core.autL.filter fun b => commC b x5C

theorem x5_check : Core.pslLit.contains x5C = true ∧ Core.cpow x5C 5 = Core.cid ∧
    (x5C == Core.cid) = false := by
  decide +kernel

theorem conj5_check : Core.pslLit.all (fun x => !(Core.cpow x 5 == Core.cid) || x == Core.cid ||
    Core.autL.any fun g => Core.cmul g x == Core.cmul x5C g) = true := by
  decide +kernel

theorem c5_exp_check : c5L.all (fun b => Core.cpow b 10 == Core.cid) = true := by
  decide +kernel

theorem c5_inv_check : c5L.all (fun b => !(Core.cmul b b == Core.cid) || b == Core.cid ||
    b == u5C) = true := by
  decide +kernel

theorem u5_check : Out21.A6.inPglC u5C = true ∧ Core.pslLit.contains u5C = false := by
  decide +kernel

theorem c5_psl_check : Core.pslLit.all (fun y => !(Core.cpow y 5 == Core.cid) || y == Core.cid ||
    !(commC y x5C) ||
      [Core.cpow x5C 1, Core.cpow x5C 2, Core.cpow x5C 3, Core.cpow x5C 4].contains y) = true := by
  decide +kernel

theorem pgl29_conj_mem {g m : P10} (hg : g ∈ A6Models.autA6) (hm : m ∈ A6Models.pgl29) :
    g * m * g⁻¹ ∈ A6Models.pgl29 := by
  have hle : A6Models.pgl29 ≤ A6Models.autA6 := Out21.A6.pgl29_le_autA6
  have hidx : (A6Models.pgl29.subgroupOf A6Models.autA6).index = 2 := by
    have h := Subgroup.card_mul_index (A6Models.pgl29.subgroupOf A6Models.autA6)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Out21.A6.card_pgl29,
      card_autA6] at h
    omega
  have hN := Subgroup.normal_of_index_eq_two hidx
  have := hN.conj_mem ⟨m, hle hm⟩ (Subgroup.mem_subgroupOf.mpr hm) ⟨g, hg⟩
  simpa using Subgroup.mem_subgroupOf.mp this

theorem five_facts {σ : P10} (hσ : σ ∈ A6Models.psl29) (hσ5 : σ ^ 5 = 1) (hσ1 : σ ≠ 1) :
    (∀ b ∈ A6Models.autA6, b * σ = σ * b → b ^ 10 = 1) ∧
    (∀ b ∈ A6Models.autA6, b * σ = σ * b → b * b = 1 → b ≠ 1 →
      b ∈ A6Models.pgl29 ∧ b ∉ A6Models.psl29) ∧
    (∀ b ∈ A6Models.autA6, ∀ b' ∈ A6Models.autA6, b * σ = σ * b → b' * σ = σ * b' →
      b * b = 1 → b' * b' = 1 → b ≠ 1 → b' ≠ 1 → b = b') ∧
    (∀ τ ∈ A6Models.psl29, τ ^ 5 = 1 → τ ≠ 1 → τ * σ = σ * τ → ∃ j : ℕ, τ = σ ^ j) := by
  obtain ⟨hx5psl, hx5pow, hx5ne⟩ := x5_check
  obtain ⟨x5, hx5, hx5code⟩ := exists_psl29_of_code (contains_iff.mp hx5psl)
  obtain ⟨g, hg, hgσ⟩ : ∃ g ∈ A6Models.autA6, g * σ * g⁻¹ = x5 := by
    have h := List.all_eq_true.mp conj5_check (code σ) ((mem_psl29_iff σ).mp hσ)
    have h5 : (Core.cpow (code σ) 5 == Core.cid) = true := by
      rw [← code_pow, hσ5, code_one]; simp
    have h1 : (code σ == Core.cid) = false := by
      rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]; exact hσ1
    rw [h5, h1] at h
    simp only [Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨gc, hgc, hge⟩ := h
    obtain ⟨g, hg, rfl⟩ := exists_autA6_of_code' hgc
    refine ⟨g, hg, ?_⟩
    have : g * σ = x5 * g := by
      apply code_injective
      rw [code_mul, code_mul, hx5code]
      exact hge
    rw [this, mul_inv_cancel_right]
  have hcomm : ∀ b : P10, b * σ = σ * b → (g * b * g⁻¹) * x5 = x5 * (g * b * g⁻¹) := by
    intro b h
    rw [← hgσ]
    calc g * b * g⁻¹ * (g * σ * g⁻¹) = g * (b * σ) * g⁻¹ := by group
      _ = g * (σ * b) * g⁻¹ := by rw [h]
      _ = g * σ * g⁻¹ * (g * b * g⁻¹) := by group
  have hmemC : ∀ b : P10, b ∈ A6Models.autA6 → b * σ = σ * b → code (g * b * g⁻¹) ∈ c5L := by
    intro b hb h
    have hb' : g * b * g⁻¹ ∈ A6Models.autA6 :=
      A6Models.autA6.mul_mem (A6Models.autA6.mul_mem hg hb) (A6Models.autA6.inv_mem hg)
    unfold c5L
    rw [List.mem_filter]
    refine ⟨code_mem_autL hb', ?_⟩
    rw [← hx5code, commC_iff]
    exact hcomm b h
  have hb'aut : ∀ b : P10, b ∈ A6Models.autA6 → g * b * g⁻¹ ∈ A6Models.autA6 := fun b hb =>
    A6Models.autA6.mul_mem (A6Models.autA6.mul_mem hg hb) (A6Models.autA6.inv_mem hg)
  have hinvb : ∀ b : P10, g⁻¹ * (g * b * g⁻¹) * g = b := fun b => by group
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb h
    have h1 := List.all_eq_true.mp c5_exp_check _ (hmemC b hb h)
    rw [beq_iff_eq, ← code_pow, ← code_one] at h1
    have h2 : (g * b * g⁻¹) ^ 10 = 1 := code_injective h1
    rw [conj_pow] at h2
    have := congrArg (fun y => g⁻¹ * y * g) h2
    simpa [mul_assoc] using this
  · intro b hb h hb2 hb1
    have hmem := hmemC b hb h
    have hb'2 : (g * b * g⁻¹) * (g * b * g⁻¹) = 1 := by
      calc g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
        _ = 1 := by rw [hb2]; group
    have hb'1 : g * b * g⁻¹ ≠ 1 := by
      intro h0
      apply hb1
      have := congrArg (fun y => g⁻¹ * y * g) h0
      simpa [mul_assoc] using this
    have hcode : code (g * b * g⁻¹) = u5C := by
      have h1 := List.all_eq_true.mp c5_inv_check _ hmem
      have e1 : (Core.cmul (code (g * b * g⁻¹)) (code (g * b * g⁻¹)) == Core.cid) = true := by
        rw [← code_mul, hb'2, code_one]; simp
      have e2 : (code (g * b * g⁻¹) == Core.cid) = false := by
        rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]; exact hb'1
      rw [e1, e2] at h1
      simpa using h1
    obtain ⟨hpgl, hpsl⟩ := u5_check
    refine ⟨?_, ?_⟩
    · have : g * b * g⁻¹ ∈ A6Models.pgl29 := by
        rw [Out21.A6.mem_pgl29_iff_code, hcode]; exact hpgl
      have := pgl29_conj_mem (A6Models.autA6.inv_mem hg) this
      simpa [mul_assoc] using this
    · intro hbpsl
      have h1 := psl29_normal g hg b hbpsl
      rw [mem_psl29_iff, hcode] at h1
      have h2 := contains_iff.mpr h1
      rw [hpsl] at h2
      exact Bool.noConfusion h2
  · intro b hb b' hb' h h' hb2 hb'2 hb1 hb'1
    have key : ∀ c : P10, c ∈ A6Models.autA6 → c * σ = σ * c → c * c = 1 → c ≠ 1 →
        code (g * c * g⁻¹) = u5C := by
      intro c hc hcσ hc2 hc1
      have hmem := hmemC c hc hcσ
      have hc'2 : (g * c * g⁻¹) * (g * c * g⁻¹) = 1 := by
        calc g * c * g⁻¹ * (g * c * g⁻¹) = g * (c * c) * g⁻¹ := by group
          _ = 1 := by rw [hc2]; group
      have hc'1 : g * c * g⁻¹ ≠ 1 := by
        intro h0
        apply hc1
        have := congrArg (fun y => g⁻¹ * y * g) h0
        simpa [mul_assoc] using this
      have h1 := List.all_eq_true.mp c5_inv_check _ hmem
      have e1 : (Core.cmul (code (g * c * g⁻¹)) (code (g * c * g⁻¹)) == Core.cid) = true := by
        rw [← code_mul, hc'2, code_one]; simp
      have e2 : (code (g * c * g⁻¹) == Core.cid) = false := by
        rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]; exact hc'1
      rw [e1, e2] at h1
      simpa using h1
    have := (key b hb h hb2 hb1).trans (key b' hb' h' hb'2 hb'1).symm
    have h3 := code_injective this
    have := congrArg (fun y => g⁻¹ * y * g) h3
    simpa [mul_assoc] using this
  · intro τ hτ hτ5 hτ1 hτσ
    have hτ' : g * τ * g⁻¹ ∈ A6Models.psl29 := psl29_normal g hg τ hτ
    have hτ'5 : (g * τ * g⁻¹) ^ 5 = 1 := by rw [conj_pow, hτ5, mul_one, mul_inv_cancel]
    have hτ'1 : g * τ * g⁻¹ ≠ 1 := by
      intro h0
      apply hτ1
      have := congrArg (fun y => g⁻¹ * y * g) h0
      simpa [mul_assoc] using this
    have hc := List.all_eq_true.mp c5_psl_check (code (g * τ * g⁻¹))
      ((mem_psl29_iff _).mp hτ')
    have e1 : (Core.cpow (code (g * τ * g⁻¹)) 5 == Core.cid) = true := by
      rw [← code_pow, hτ'5, code_one]; simp
    have e2 : (code (g * τ * g⁻¹) == Core.cid) = false := by
      rw [beq_eq_false_iff_ne, Ne, code_eq_cid_iff]; exact hτ'1
    have e3 : commC (code (g * τ * g⁻¹)) x5C = true := by
      rw [← hx5code, commC_iff]; exact hcomm τ hτσ
    rw [e1, e2, e3] at hc
    simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true', List.contains_iff_mem,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    have hpow : ∀ k : ℕ, code (x5 ^ k) = Core.cpow x5C k := fun k => by
      rw [code_pow, hx5code]
    have hback : ∀ j : ℕ, g * τ * g⁻¹ = x5 ^ j → τ = σ ^ j := by
      intro j hj
      have := congrArg (fun y => g⁻¹ * y * g) hj
      rw [← hgσ, conj_pow] at this
      simpa [mul_assoc] using this
    rcases hc with h | h | h | h
    · exact ⟨1, hback 1 (code_injective (h.trans (hpow 1).symm))⟩
    · exact ⟨2, hback 2 (code_injective (h.trans (hpow 2).symm))⟩
    · exact ⟨3, hback 3 (code_injective (h.trans (hpow 3).symm))⟩
    · exact ⟨4, hback 4 (code_injective (h.trans (hpow 4).symm))⟩

end Five

section Odd

theorem odd3_check : Core.autL.all (fun b => !(cubeC b == Core.cid) || Core.pslLit.contains b) =
    true := by
  decide +kernel

theorem odd5_check : Core.autL.all (fun b => !(Core.cpow b 5 == Core.cid) ||
    Core.pslLit.contains b) = true := by
  decide +kernel

theorem mem_psl29_of_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {b : P10}
    (hb : b ∈ A6Models.autA6) (hbp : b ^ p = 1) (hb1 : b ≠ 1) :
    b ∈ A6Models.psl29 ∧ (p = 3 ∨ p = 5) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hdvd : p ∣ 1440 := by
    have h := orderOf_dvd_natCard (⟨b, hb⟩ : ↥A6Models.autA6)
    rw [card_autA6, Subgroup.orderOf_mk, hord] at h
    exact h
  have hp35 : p = 3 ∨ p = 5 := by
    have h1 : p ∣ 2 ^ 5 * 3 ^ 2 * 5 := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (hp.dvd_of_dvd_pow h)) hp2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h)
  refine ⟨?_, hp35⟩
  rw [mem_psl29_iff]
  rcases hp35 with rfl | rfl
  · have h := List.all_eq_true.mp odd3_check (code b) (code_mem_autL hb)
    have h3 : (cubeC (code b) == Core.cid) = true := by
      rw [beq_iff_eq, cubeC_eq_cid_iff]; exact hbp
    rw [h3] at h
    simpa using h
  · have h := List.all_eq_true.mp odd5_check (code b) (code_mem_autL hb)
    have h5 : (Core.cpow (code b) 5 == Core.cid) = true := by
      rw [← code_pow, hbp, code_one]; simp
    rw [h5] at h
    simpa using h

end Odd

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
