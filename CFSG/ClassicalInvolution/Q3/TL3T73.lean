module

public import CFSG.ClassicalInvolution.Q3.TL3T47

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open CFSG.ClassicalInvolution.Q3.TC.Thin (permQ permQ_mkQ mul_self_of_mem_ker_permQ)

section Extend

variable {r k : ℕ}

@[expose] noncomputable def extendPerm (e : Fin r ↪ Fin k) :
    Equiv.Perm (Fin r) →* Equiv.Perm (Fin k) :=
  Equiv.Perm.extendDomainHom e.toEquivRange

theorem extendPerm_apply (e : Fin r ↪ Fin k) (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    extendPerm e σ (e i) = e (σ i) := by
  classical
  simpa [extendPerm] using Equiv.Perm.extendDomain_apply_image σ e.toEquivRange i

theorem extendPerm_apply_of_not_mem (e : Fin r ↪ Fin k) (σ : Equiv.Perm (Fin r)) {x : Fin k}
    (hx : x ∉ Set.range e) : extendPerm e σ x = x := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype σ e.toEquivRange hx

theorem extendPerm_injective (e : Fin r ↪ Fin k) : Function.Injective (extendPerm e) :=
  Equiv.Perm.extendDomainHom_injective _

theorem sign_extendPerm (e : Fin r ↪ Fin k) (σ : Equiv.Perm (Fin r)) :
    Equiv.Perm.sign (extendPerm e σ) = Equiv.Perm.sign σ := by
  classical
  exact Equiv.Perm.sign_extendDomain σ e.toEquivRange

theorem orderOf_extendPerm (e : Fin r ↪ Fin k) (σ : Equiv.Perm (Fin r)) :
    orderOf (extendPerm e σ) = orderOf σ :=
  orderOf_injective _ (extendPerm_injective e) σ

theorem exists_extendPerm_eq (e : Fin r ↪ Fin k) {σ : Equiv.Perm (Fin k)}
    (hσ : ∀ x ∉ Set.range e, σ x = x) : ∃ τ : Equiv.Perm (Fin r), extendPerm e τ = σ := by
  classical
  have hrange : ∀ i, ∃ j, e j = σ (e i) := by
    intro i
    by_contra h
    push Not at h
    have h1 := hσ (σ (e i)) (fun ⟨j, hj⟩ => h j hj)
    exact h i (σ.injective h1).symm
  choose f hf using hrange
  have hinj : Function.Injective f := fun i j hij =>
    e.injective (σ.injective (by rw [← hf, ← hf, hij]))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), Equiv.ext fun x => ?_⟩
  by_cases hx : x ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hx
    rw [extendPerm_apply]
    exact hf i
  · rw [extendPerm_apply_of_not_mem e _ hx, hσ x hx]

end Extend

@[expose] def kleinFour : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {x | x ^ 2 = 1 ∧ Equiv.Perm.sign x = 1}
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +revert
  inv_mem' := by
    intro a ha
    revert a
    decide +revert

theorem mem_kleinFour {x : Equiv.Perm (Fin 4)} :
    x ∈ kleinFour ↔ x ^ 2 = 1 ∧ Equiv.Perm.sign x = 1 := Iff.rfl

private instance : DecidablePred (· ∈ kleinFour) := fun _ => decidable_of_iff _ mem_kleinFour.symm

theorem natCard_kleinFour : Nat.card kleinFour = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

@[expose] noncomputable def kleinOn {k : ℕ} (A : Finset (Fin k)) :
    Subgroup (Equiv.Perm (Fin k)) :=
  if h : A.card = 4 then kleinFour.map (extendPerm (emb A h)) else ⊥

section Klein

variable {k r : ℕ} {A B : Finset (Fin k)}

theorem kleinOn_of_card_ne (hA : A.card ≠ 4) : kleinOn A = ⊥ := by
  rw [kleinOn, dif_neg hA]

theorem mem_kleinOn_iff (hA : A.card = 4) {σ : Equiv.Perm (Fin k)} :
    σ ∈ kleinOn A ↔ (∀ x ∉ A, σ x = x) ∧ σ ^ 2 = 1 ∧ Equiv.Perm.sign σ = 1 := by
  have hr : ∀ x, x ∈ Set.range (emb A hA) ↔ x ∈ A := fun x => by
    rw [range_emb]
    rfl
  rw [kleinOn, dif_pos hA, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨hτ2, hτs⟩ := mem_kleinFour.mp hτ
    refine ⟨fun x hx => extendPerm_apply_of_not_mem _ _ (fun h => hx ((hr x).mp h)), ?_, ?_⟩
    · rw [← map_pow, hτ2, map_one]
    · rw [sign_extendPerm]
      exact hτs
  · rintro ⟨hfix, hsq, hsign⟩
    obtain ⟨τ, rfl⟩ := exists_extendPerm_eq (emb A hA)
      fun x hx => hfix x (fun h => hx ((hr x).mpr h))
    refine ⟨τ, mem_kleinFour.mpr ⟨?_, ?_⟩, rfl⟩
    · exact extendPerm_injective (emb A hA) (by rw [map_pow, hsq, map_one])
    · rw [← sign_extendPerm (emb A hA) τ]
      exact hsign

theorem fix_of_mem_kleinOn {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ kleinOn A) {x : Fin k}
    (hx : x ∉ A) : σ x = x := by
  by_cases hA : A.card = 4
  · exact ((mem_kleinOn_iff hA).mp hσ).1 x hx
  · rw [kleinOn_of_card_ne hA, Subgroup.mem_bot] at hσ
    rw [hσ]
    rfl

theorem sign_of_mem_kleinOn {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ kleinOn A) :
    Equiv.Perm.sign σ = 1 := by
  by_cases hA : A.card = 4
  · exact ((mem_kleinOn_iff hA).mp hσ).2.2
  · rw [kleinOn_of_card_ne hA, Subgroup.mem_bot] at hσ
    rw [hσ, map_one]

theorem natCard_kleinOn (hA : A.card = 4) : Nat.card (kleinOn A) = 4 := by
  rw [kleinOn, dif_pos hA, Subgroup.card_map_of_injective (extendPerm_injective _),
    natCard_kleinFour]

private theorem fix_of_ne_one_kleinFour : ∀ τ : Equiv.Perm (Fin 4), τ ∈ kleinFour → τ ≠ 1 →
    ∀ i, τ i ≠ i := by
  decide +kernel

theorem moves_iff_of_mem_kleinOn {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ kleinOn A) (h1 : σ ≠ 1)
    (x : Fin k) : σ x ≠ x ↔ x ∈ A := by
  by_cases hA : A.card = 4
  · refine ⟨fun hx => by_contra fun hxA => hx (fix_of_mem_kleinOn hσ hxA), fun hx hσx => ?_⟩
    rw [kleinOn, dif_pos hA] at hσ
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ
    have hxr : x ∈ Set.range (emb A hA) := by
      rw [range_emb]
      exact hx
    obtain ⟨i, rfl⟩ := hxr
    rw [extendPerm_apply] at hσx
    refine fix_of_ne_one_kleinFour τ hτ (fun h => h1 (by rw [h, map_one])) i
      ((emb A hA).injective hσx)
  · rw [kleinOn_of_card_ne hA, Subgroup.mem_bot] at hσ
    exact absurd hσ h1

theorem eq_of_kleinOn_eq (hA : A.card = 4) (hB : B.card = 4) (h : kleinOn A = kleinOn B) :
    A = B := by
  have h1 : kleinOn A ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, natCard_kleinOn hA]
    norm_num
  obtain ⟨⟨σ, hσ⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
  have hσ1 : σ ≠ 1 := fun h' => hne (Subtype.ext h')
  have hσB : σ ∈ kleinOn B := h ▸ hσ
  ext x
  rw [← moves_iff_of_mem_kleinOn hσ hσ1 x, ← moves_iff_of_mem_kleinOn hσB hσ1 x]

theorem kleinOn_map_embedding (e : Fin r ↪ Fin k) (A : Finset (Fin r)) :
    kleinOn (A.map e) = (kleinOn A).map (extendPerm e) := by
  by_cases hA : A.card = 4
  · have hA' : (A.map e).card = 4 := by rw [Finset.card_map, hA]
    ext σ
    rw [mem_kleinOn_iff hA', Subgroup.mem_map]
    constructor
    · rintro ⟨hfix, hsq, hsign⟩
      obtain ⟨τ, rfl⟩ := exists_extendPerm_eq e fun x hx => hfix x fun hx' => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx'
        exact hx (Set.mem_range_self i)
      refine ⟨τ, (mem_kleinOn_iff hA).mpr ⟨fun i hi => ?_, ?_, ?_⟩, rfl⟩
      · apply e.injective
        rw [← extendPerm_apply]
        exact hfix _ fun h => hi (by obtain ⟨j, hj, hje⟩ := Finset.mem_map.mp h
                                     rwa [← e.injective hje])
      · exact extendPerm_injective e (by rw [map_pow, hsq, map_one])
      · rw [← sign_extendPerm e τ]
        exact hsign
    · rintro ⟨τ, hτ, rfl⟩
      obtain ⟨hfix, hsq, hsign⟩ := (mem_kleinOn_iff hA).mp hτ
      refine ⟨fun x hx => ?_, by rw [← map_pow, hsq, map_one], by rw [sign_extendPerm]; exact hsign⟩
      by_cases hxr : x ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hxr
        rw [extendPerm_apply, hfix i fun hi => hx (Finset.mem_map_of_mem e hi)]
      · exact extendPerm_apply_of_not_mem e τ hxr
  · rw [kleinOn_of_card_ne hA, kleinOn_of_card_ne (by rwa [Finset.card_map]), Subgroup.map_bot]

theorem kleinOn_map (σ : Equiv.Perm (Fin k)) (A : Finset (Fin k)) :
    kleinOn (A.map σ.toEmbedding) = (kleinOn A).map (MulAut.conj σ).toMonoidHom := by
  by_cases hA : A.card = 4
  · have hA' : (A.map σ.toEmbedding).card = 4 := by rw [Finset.card_map, hA]
    ext x
    rw [Subgroup.mem_map_equiv, mem_kleinOn_iff hA', mem_kleinOn_iff hA, MulAut.conj_symm_apply]
    have hsq : (σ⁻¹ * x * σ) ^ 2 = σ⁻¹ * x ^ 2 * σ := by
      simpa using (conj_pow (a := σ⁻¹) (b := x) (i := 2))
    have hsign : Equiv.Perm.sign (σ⁻¹ * x * σ) = Equiv.Perm.sign x := by
      rw [map_mul, map_mul, map_inv, mul_comm (Equiv.Perm.sign σ)⁻¹ _, mul_assoc, inv_mul_cancel,
        mul_one]
    rw [hsq, hsign]
    refine and_congr ?_ (and_congr ?_ Iff.rfl)
    · constructor
      · intro h z hz
        have h1 : σ z ∉ A.map σ.toEmbedding := fun hmem => hz (by
          obtain ⟨w, hw, hwz⟩ := Finset.mem_map.mp hmem
          rwa [← σ.injective hwz])
        have := h (σ z) h1
        show σ.symm (x (σ z)) = z
        rw [this]
        exact σ.symm_apply_apply z
      · intro h y hy
        have h1 : σ⁻¹ y ∉ A := fun hmem => hy (Finset.mem_map.mpr ⟨_, hmem, by simp⟩)
        have := h _ h1
        have h2 : σ (σ⁻¹ (x (σ (σ⁻¹ y)))) = σ (σ⁻¹ y) := congrArg σ this
        simpa using h2
    · constructor
      · intro h
        rw [h, mul_one, inv_mul_cancel]
      · intro h
        calc x ^ 2 = σ * (σ⁻¹ * x ^ 2 * σ) * σ⁻¹ := by group
          _ = 1 := by rw [h]; group
  · rw [kleinOn_of_card_ne hA, kleinOn_of_card_ne (by rwa [Finset.card_map]), Subgroup.map_bot]

end Klein

section Members

private theorem embedPerm_eq_extendPerm {n : ℕ} (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin 4)) :
    embedPerm ι σ = extendPerm ι σ := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [embedPerm_apply, extendPerm_apply]
  · rw [embedPerm_of_not_mem ι σ hx, extendPerm_apply_of_not_mem ι σ hx]

private theorem map_permHom_kQ : kQ.map (permHom 4) = kleinFour := by
  ext τ
  rw [Subgroup.mem_map, mem_kleinFour]
  exact (by decide +kernel : ∀ τ : Equiv.Perm (Fin 4),
    (∃ a ∈ kList, a.perm = τ) ↔ (τ ^ 2 = 1 ∧ Equiv.Perm.sign τ = 1)) τ

private theorem map_permHom_kQStar : kQStar.map (permHom 4) = kleinFour := by
  ext τ
  rw [Subgroup.mem_map, mem_kleinFour]
  exact (by decide +kernel : ∀ τ : Equiv.Perm (Fin 4),
    (∃ a ∈ kStarList, a.perm = τ) ↔ (τ ^ 2 = 1 ∧ Equiv.Perm.sign τ = 1)) τ

theorem map_permQ_memBar {k : ℕ} (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) :
    (memBar α h b).map (permQ k) = kleinOn α := by
  have hcomp : (permQ k).comp (mkQ k) = permHom k := MonoidHom.ext fun a => permQ_mkQ a
  have hemb : (permHom k).comp (embed (emb α h)) = (extendPerm (emb α h)).comp (permHom 4) :=
    MonoidHom.ext fun a => embedPerm_eq_extendPerm _ _
  rw [memBar, Subgroup.map_map, hcomp, memAt, kleinOn, dif_pos h]
  cases b
  · rw [cond_false, memKStar, Subgroup.map_map, hemb, ← Subgroup.map_map, map_permHom_kQStar]
  · rw [cond_true, memK, Subgroup.map_map, hemb, ← Subgroup.map_map, map_permHom_kQ]

end Members

section Products

private theorem exists_five_dvd_orderOf_iff_of_nine_le {n : ℕ} (hn : 9 ≤ n)
    {A B : Finset (Fin n)} (hA : A.card = 4) (hB : B.card = 4) :
    (∃ x ∈ kleinOn A, ∃ y ∈ kleinOn B, 5 ∣ orderOf (x * y)) ↔ (A ∩ B).card = 3 := by
  constructor
  · rintro ⟨x, hx, y, hy, h5⟩
    rw [← map_permQ_memBar A hA true] at hx
    rw [← map_permQ_memBar B hB true] at hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul] at h5
    exact card_inter_eq_three_of_dvd hn hg hg' (h5.trans (orderOf_map_dvd _ _))
  · intro h3
    obtain ⟨b, b', g, hg, g', hg', h5⟩ := (adjInv_of_nine_le hn A hA B hB).mp h3
    refine ⟨permQ n g, ?_, permQ n g', ?_, ?_⟩
    · rw [← map_permQ_memBar A hA b]
      exact Subgroup.mem_map_of_mem _ hg
    · rw [← map_permQ_memBar B hB b']
      exact Subgroup.mem_map_of_mem _ hg'
    · rw [← map_mul]
      set m := orderOf (permQ n (g * g')) with hm
      have h1 : (g * g') ^ m ∈ (permQ n).ker := by
        rw [MonoidHom.mem_ker, map_pow, hm, pow_orderOf_eq_one]
      have h2 : (g * g') ^ (m + m) = 1 := by
        rw [pow_add]
        exact mul_self_of_mem_ker_permQ h1
      have h3 := h5 ▸ orderOf_dvd_of_pow_eq_one h2
      omega

theorem exists_five_dvd_orderOf_iff {k : ℕ} {A B : Finset (Fin k)} (hA : A.card = 4)
    (hB : B.card = 4) :
    (∃ x ∈ kleinOn A, ∃ y ∈ kleinOn B, 5 ∣ orderOf (x * y)) ↔ (A ∩ B).card = 3 := by
  let e : Fin k ↪ Fin (k + 9) := Fin.castLEEmb (by omega)
  have hA' : (A.map e).card = 4 := by rw [Finset.card_map, hA]
  have hB' : (B.map e).card = 4 := by rw [Finset.card_map, hB]
  have h9 := exists_five_dvd_orderOf_iff_of_nine_le (by omega : 9 ≤ k + 9) hA' hB'
  rw [← Finset.map_inter, Finset.card_map, kleinOn_map_embedding, kleinOn_map_embedding] at h9
  rw [← h9]
  constructor
  · rintro ⟨x, hx, y, hy, h5⟩
    refine ⟨extendPerm e x, Subgroup.mem_map_of_mem _ hx, extendPerm e y,
      Subgroup.mem_map_of_mem _ hy, ?_⟩
    rwa [← map_mul, orderOf_extendPerm]
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, h5⟩
    refine ⟨x, hx, y, hy, ?_⟩
    rwa [← map_mul, orderOf_extendPerm] at h5

private theorem pow_cases_five : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 →
    τ ^ 1 = 1 ∨ τ ^ 2 = 1 ∨ τ ^ 3 = 1 ∨ τ ^ 5 = 1 := by
  decide +kernel

theorem orderOf_of_support_five {k : ℕ} {σ : Equiv.Perm (Fin k)}
    (hσ : Equiv.Perm.sign σ = 1) {S : Finset (Fin k)} (hS : S.card = 5)
    (hfix : ∀ x ∉ S, σ x = x) :
    orderOf σ = 1 ∨ orderOf σ = 2 ∨ orderOf σ = 3 ∨ orderOf σ = 5 := by
  have hr : Set.range (S.orderEmbOfFin hS).toEmbedding = (S : Set (Fin k)) :=
    Finset.range_orderEmbOfFin S hS
  obtain ⟨τ, rfl⟩ := exists_extendPerm_eq (S.orderEmbOfFin hS).toEmbedding fun x hx =>
    hfix x fun h => hx (by rw [hr]; exact h)
  rw [sign_extendPerm] at hσ
  rw [orderOf_extendPerm]
  rcases pow_cases_five τ hσ with h | h | h | h
  · have := Nat.dvd_one.mp (orderOf_dvd_of_pow_eq_one h)
    omega
  · rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h) with h' | h' <;> omega
  · rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h) with h' | h' <;> omega
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one h) with
      h' | h' <;> omega

theorem exists_orderOf_eq_four_star {k : ℕ} {T : Finset (Fin k)} (hT : T.card = 3)
    {x₁ x₂ x₃ : Fin k} (h₁ : x₁ ∉ T) (h₂ : x₂ ∉ T) (h₃ : x₃ ∉ T) (h₁₂ : x₁ ≠ x₂)
    (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃) :
    ∃ x ∈ kleinOn (insert x₁ T), ∃ y ∈ kleinOn (insert x₂ T), ∃ w ∈ kleinOn (insert x₃ T),
      orderOf (x * y * w) = 4 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h₁ h₂ h₃
  let e : Fin 6 ↪ Fin k := ⟨![a, b, c, x₁, x₂, x₃], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  have hs₁ : ({0, 1, 2, 3} : Finset (Fin 6)).map e = insert x₁ {a, b, c} := by
    ext z
    simp [e]
    tauto
  have hs₂ : ({0, 1, 2, 4} : Finset (Fin 6)).map e = insert x₂ {a, b, c} := by
    ext z
    simp [e]
    tauto
  have hs₃ : ({0, 1, 2, 5} : Finset (Fin 6)).map e = insert x₃ {a, b, c} := by
    ext z
    simp [e]
    tauto
  have hx₀ : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 6)) ∈
      kleinOn ({0, 1, 2, 3} : Finset (Fin 6)) :=
    (mem_kleinOn_iff (by decide)).mpr (by decide +kernel)
  have hy₀ : (Equiv.swap 0 1 * Equiv.swap 2 4 : Equiv.Perm (Fin 6)) ∈
      kleinOn ({0, 1, 2, 4} : Finset (Fin 6)) :=
    (mem_kleinOn_iff (by decide)).mpr (by decide +kernel)
  have hw₀ : (Equiv.swap 0 1 * Equiv.swap 2 5 : Equiv.Perm (Fin 6)) ∈
      kleinOn ({0, 1, 2, 5} : Finset (Fin 6)) :=
    (mem_kleinOn_iff (by decide)).mpr (by decide +kernel)
  refine ⟨extendPerm e (Equiv.swap 0 1 * Equiv.swap 2 3), ?_,
    extendPerm e (Equiv.swap 0 1 * Equiv.swap 2 4), ?_,
    extendPerm e (Equiv.swap 0 1 * Equiv.swap 2 5), ?_, ?_⟩
  · rw [← hs₁, kleinOn_map_embedding]
    exact Subgroup.mem_map_of_mem _ hx₀
  · rw [← hs₂, kleinOn_map_embedding]
    exact Subgroup.mem_map_of_mem _ hy₀
  · rw [← hs₃, kleinOn_map_embedding]
    exact Subgroup.mem_map_of_mem _ hw₀
  · rw [← map_mul, ← map_mul, orderOf_extendPerm]
    have h4 : orderOf (((Equiv.swap 0 1 * Equiv.swap 2 3) * (Equiv.swap 0 1 * Equiv.swap 2 4) *
        (Equiv.swap 0 1 * Equiv.swap 2 5) : Equiv.Perm (Fin 6))) = 2 ^ (1 + 1) :=
      orderOf_eq_prime_pow (by decide +kernel) (by decide +kernel)
    simpa using h4

end Products

end CFSG.ClassicalInvolution.Q3.AE
