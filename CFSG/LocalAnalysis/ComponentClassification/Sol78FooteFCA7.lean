module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFCB

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.Foote5

theorem cycleType_of_odd_involution {π : Perm (Fin 7)} (h2 : π * π = 1) (hodd : sign π = -1) :
    π.cycleType = Multiset.replicate 1 2 ∨ π.cycleType = Multiset.replicate 3 2 := by
  have h1 : π ≠ 1 := fun h => by
    rw [h, Perm.sign_one] at hodd
    exact absurd hodd (by decide)
  have hord : orderOf π = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨n, hn⟩ := cycleType_prime_order (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsum : 2 * (n + 1) ≤ 7 := by
    have h3 := sum_cycleType_le π
    rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at h3
    linarith
  have hsign := sign_of_cycleType π
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate, hodd] at hsign
  have hodd' : Odd (n + 1) := by
    rcases Nat.even_or_odd (n + 1) with he | ho
    · exfalso
      have h4 : Even ((n + 1) * 2 + (n + 1)) := by
        obtain ⟨k, hk⟩ := he
        exact ⟨(n + 1) + k, by rw [hk]; ring⟩
      rw [h4.neg_one_pow] at hsign
      exact absurd hsign (by decide)
    · exact ho
  rw [hn]
  have : n + 1 = 1 ∨ n + 1 = 3 := by
    obtain ⟨k, hk⟩ := hodd'
    omega
  rcases this with h | h <;> rw [h] <;> simp

abbrev Pair4 := {s : Finset (Fin 4) // s.card = 2}

@[expose] noncomputable def pairHom : Perm (Fin 4) →* Perm Pair4 where
  toFun g := g.finsetCongr.subtypeEquiv fun s => by rw [Equiv.finsetCongr_apply, Finset.card_map]
  map_one' := Equiv.ext fun s => Subtype.ext (by
    ext x
    simp only [Equiv.subtypeEquiv_apply, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    rfl)
  map_mul' g h := Equiv.ext fun s => Subtype.ext (by
    ext x
    simp only [Equiv.subtypeEquiv_apply, Equiv.finsetCongr_apply, Finset.mem_map_equiv,
      Perm.mul_apply]
    rfl)

theorem pairHom_apply_val (g : Perm (Fin 4)) (s : Pair4) :
    ((pairHom g s : Pair4) : Finset (Fin 4)) = (s : Finset (Fin 4)).map g.toEmbedding := rfl

@[expose] def pairCompl : Perm Pair4 where
  toFun s := ⟨(s : Finset (Fin 4))ᶜ, by rw [Finset.card_compl, s.2]; rfl⟩
  invFun s := ⟨(s : Finset (Fin 4))ᶜ, by rw [Finset.card_compl, s.2]; rfl⟩
  left_inv s := Subtype.ext (compl_compl _)
  right_inv s := Subtype.ext (compl_compl _)

theorem pairCompl_apply_val (s : Pair4) :
    ((pairCompl s : Pair4) : Finset (Fin 4)) = (s : Finset (Fin 4))ᶜ := rfl

theorem pairHom_mul_pairCompl (g : Perm (Fin 4)) : pairHom g * pairCompl = pairCompl * pairHom g :=
  Equiv.ext fun s => Subtype.ext (by
    rw [Perm.mul_apply, Perm.mul_apply, pairHom_apply_val, pairCompl_apply_val,
      pairCompl_apply_val, pairHom_apply_val]
    ext x
    simp [Finset.mem_map_equiv])

theorem pairHom_injective : Function.Injective pairHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [mem_bot]
  have hfix : ∀ s : Finset (Fin 4), s.card = 2 → s.map g.toEmbedding = s := fun s hs => by
    have h := congrArg (fun φ : Perm Pair4 => ((φ ⟨s, hs⟩ : Pair4) : Finset (Fin 4))) hg
    simpa [pairHom_apply_val] using h
  ext i
  obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    revert i
    decide
  have hmem : ∀ x : Fin 4, x ≠ i → g i = i ∨ g i = x := fun x hx => by
    have h1 := hfix {i, x} (Finset.card_pair hx.symm)
    have h2 : g i ∈ ({i, x} : Finset (Fin 4)).map g.toEmbedding :=
      Finset.mem_map_of_mem _ (by simp)
    rw [h1] at h2
    simpa using h2
  rcases hmem j hij.symm with h | h
  · rw [h]; rfl
  · rcases hmem k hik.symm with h' | h'
    · rw [h']; rfl
    · exact absurd (h.symm.trans h') hjk

theorem card_pair4 : Fintype.card Pair4 = 6 := by decide

theorem cycleType_pairCompl : pairCompl.cycleType = Multiset.replicate 3 2 := by
  have hsq : pairCompl * pairCompl = 1 := Equiv.ext fun s => Subtype.ext (compl_compl _)
  have hne : ∀ s : Pair4, pairCompl s ≠ s := fun s h => by
    have h1 := congrArg Subtype.val h
    rw [pairCompl_apply_val] at h1
    have h2 := s.2
    have h3 : (s : Finset (Fin 4)) ∩ (s : Finset (Fin 4))ᶜ = ∅ := Finset.inter_compl _
    rw [h1, Finset.inter_self] at h3
    rw [h3] at h2
    simp at h2
  have h1 : pairCompl ≠ 1 := fun h => by
    obtain ⟨s⟩ : Nonempty Pair4 := ⟨⟨{0, 1}, by decide⟩⟩
    exact hne s (by rw [h]; rfl)
  have hord : orderOf pairCompl = 2 := orderOf_eq_prime (by rw [sq]; exact hsq) h1
  obtain ⟨n, hn⟩ := cycleType_prime_order (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsupp : pairCompl.support = Finset.univ := by
    ext s
    simp [mem_support, hne s]
  have h2 := sum_cycleType pairCompl
  rw [hn, Multiset.sum_replicate, smul_eq_mul, hsupp, Finset.card_univ, card_pair4] at h2
  rw [hn, show n + 1 = 3 by omega]

@[expose] noncomputable def pairEquiv : Pair4 ≃ {x : Fin 7 // x ≠ 6} :=
  Fintype.equivOfCardEq (by rw [card_pair4]; decide)

@[expose] noncomputable def fourEquiv : Fin 4 ≃ {x : Fin 7 // x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 6} :=
  Fintype.equivOfCardEq (by decide)

theorem exists_alternatingFour_of_hom {ψ : Perm (Fin 4) →* Perm (Fin 7)}
    (hψ : Function.Injective ψ)
    (hA : ∀ g ∈ alternatingGroup (Fin 4), ψ g ∈ alternatingGroup (Fin 7))
    {π₀ : Perm (Fin 7)} (hc : ∀ g, ψ g * π₀ = π₀ * ψ g) :
    ∃ X : Subgroup (alternatingGroup (Fin 7)), (∀ x ∈ X, π₀ * (x : Perm (Fin 7)) = x * π₀) ∧
      Nonempty (X ≃* alternatingGroup (Fin 4)) := by
  set ψ' : alternatingGroup (Fin 4) →* alternatingGroup (Fin 7) :=
    (ψ.comp (alternatingGroup (Fin 4)).subtype).codRestrict _ fun g => hA g g.2 with hψ'
  have hinj : Function.Injective ψ' := fun g h hgh => Subtype.ext (hψ (congrArg Subtype.val hgh))
  refine ⟨ψ'.range, ?_, ⟨(MonoidHom.ofInjective hinj).symm⟩⟩
  rintro _ ⟨g, rfl⟩
  exact (hc g).symm

theorem edge_facts :
    Function.Injective ((extendDomainHom pairEquiv).comp pairHom) ∧
      (∀ g ∈ alternatingGroup (Fin 4),
        (extendDomainHom pairEquiv).comp pairHom g ∈ alternatingGroup (Fin 7)) ∧
      (∀ g, (extendDomainHom pairEquiv).comp pairHom g * pairCompl.extendDomain pairEquiv =
        pairCompl.extendDomain pairEquiv * (extendDomainHom pairEquiv).comp pairHom g) := by
  refine ⟨(extendDomainHom_injective pairEquiv).comp pairHom_injective, fun g hg => ?_,
    fun g => ?_⟩
  ·
    have hle : alternatingGroup (Fin 4) ≤
        (alternatingGroup (Fin 7)).comap ((extendDomainHom pairEquiv).comp pairHom) := by
      rw [← closure_three_cycles_eq_alternating, closure_le]
      intro c hc
      rw [SetLike.mem_coe, mem_comap, mem_alternatingGroup]
      set u := sign ((extendDomainHom pairEquiv).comp pairHom c)
      have h3 : u ^ 3 = 1 := by
        rw [← map_pow, ← map_pow, ← hc.orderOf, pow_orderOf_eq_one, map_one, map_one]
      have hsq : u ^ 2 = 1 := Int.units_sq u
      calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, hsq]; group
    exact hle hg
  · change (pairHom g).extendDomain pairEquiv * pairCompl.extendDomain pairEquiv =
      pairCompl.extendDomain pairEquiv * (pairHom g).extendDomain pairEquiv
    rw [extendDomain_mul, extendDomain_mul, pairHom_mul_pairCompl]

theorem four_facts :
    Function.Injective (extendDomainHom fourEquiv) ∧
      (∀ g ∈ alternatingGroup (Fin 4), extendDomainHom fourEquiv g ∈ alternatingGroup (Fin 7)) ∧
      (∀ g, extendDomainHom fourEquiv g * swap 0 1 = swap 0 1 * extendDomainHom fourEquiv g) := by
  refine ⟨extendDomainHom_injective fourEquiv, fun g hg => ?_, fun g => ?_⟩
  · rw [mem_alternatingGroup] at hg ⊢
    change sign (g.extendDomain fourEquiv) = 1
    rw [sign_extendDomain, hg]
  · change g.extendDomain fourEquiv * swap 0 1 = swap 0 1 * g.extendDomain fourEquiv
    have h0 : g.extendDomain fourEquiv 0 = 0 :=
      extendDomain_apply_not_subtype g fourEquiv (by decide)
    have h1 : g.extendDomain fourEquiv 1 = 1 :=
      extendDomain_apply_not_subtype g fourEquiv (by decide)
    rw [mul_swap_eq_swap_mul, h0, h1]

theorem exists_alternatingFour_commute {π : Perm (Fin 7)} (h2 : π * π = 1)
    (hodd : sign π = -1) :
    ∃ X : Subgroup (alternatingGroup (Fin 7)), (∀ x ∈ X, π * (x : Perm (Fin 7)) = x * π) ∧
      Nonempty (X ≃* alternatingGroup (Fin 4)) := by
  have key : ∀ π₀ : Perm (Fin 7), IsConj π₀ π →
      (∃ X : Subgroup (alternatingGroup (Fin 7)), (∀ x ∈ X, π₀ * (x : Perm (Fin 7)) = x * π₀) ∧
        Nonempty (X ≃* alternatingGroup (Fin 4))) →
      ∃ X : Subgroup (alternatingGroup (Fin 7)), (∀ x ∈ X, π * (x : Perm (Fin 7)) = x * π) ∧
        Nonempty (X ≃* alternatingGroup (Fin 4)) := by
    rintro π₀ hconj ⟨X₀, hX₀, ⟨eX⟩⟩
    obtain ⟨σ, rfl⟩ := isConj_iff.mp hconj
    set φ := AutL2Facts.a7Conj σ with hφ
    refine ⟨X₀.map φ.toMonoidHom, ?_, ⟨(X₀.equivMapOfInjective _ φ.injective).symm.trans eX⟩⟩
    rintro _ ⟨x, hx, rfl⟩
    change σ * π₀ * σ⁻¹ * ((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * (σ * π₀ * σ⁻¹)
    rw [hφ, AutL2Facts.a7Conj_apply]
    calc σ * π₀ * σ⁻¹ * (σ * (x : Perm (Fin 7)) * σ⁻¹) = σ * (π₀ * x) * σ⁻¹ := by group
      _ = σ * (x * π₀) * σ⁻¹ := by rw [hX₀ x hx]
      _ = σ * (x : Perm (Fin 7)) * σ⁻¹ * (σ * π₀ * σ⁻¹) := by group
  rcases cycleType_of_odd_involution h2 hodd with h | h
  · refine key (swap 0 1) (isConj_iff_cycleType_eq.mpr ?_) ?_
    · rw [h, (isCycle_swap (by decide)).cycleType, card_support_swap (by decide)]
      rfl
    · obtain ⟨hinj, hA, hc⟩ := four_facts
      exact exists_alternatingFour_of_hom hinj hA hc
  · refine key (pairCompl.extendDomain pairEquiv) (isConj_iff_cycleType_eq.mpr ?_) ?_
    · rw [h, cycleType_extendDomain, cycleType_pairCompl]
    · obtain ⟨hinj, hA, hc⟩ := edge_facts
      exact exists_alternatingFour_of_hom hinj hA hc

theorem fieldCentralizer_a_alt7 {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 7))
    {β : MulAut Y} (hβ2 : β * β = 1) (hβ : β ∉ innAut5 Y) :
    ∃ X : Subgroup Y, (∀ x ∈ X, β x = x) ∧ Nonempty (X ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨π, hπ⟩ := AutL2Facts.exists_a7Conj_eq (MulAut.congr e β)
  have hodd : sign π = -1 := by
    rcases Int.units_eq_one_or (sign π) with h | h
    · exfalso
      apply hβ
      have hA : π ∈ alternatingGroup (Fin 7) := mem_alternatingGroup.mpr h
      refine ⟨e.symm ⟨π, hA⟩, ?_⟩
      apply (MulAut.congr e).injective
      rw [← hπ, AutL2Facts.a7Conj_of_mem hA, AutL2Facts.congr_conj_eq, MulEquiv.apply_symm_apply]
    · exact h
  have h2 : π * π = 1 := by
    apply LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
      (by rw [Fintype.card_fin]; norm_num)
    intro g hg
    have h1 : AutL2Facts.a7Conj (π * π) = 1 := by
      rw [map_mul, hπ, ← map_mul, hβ2, map_one]
    have h3 := congrArg (fun φ : MulAut (alternatingGroup (Fin 7)) =>
      ((φ ⟨g, hg⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7))) h1
    simp only [AutL2Facts.a7Conj_apply, MulAut.one_apply] at h3
    calc π * π * g = π * π * g * (π * π)⁻¹ * (π * π) := by group
      _ = g * (π * π) := by rw [h3]
  obtain ⟨X, hX, ⟨eX⟩⟩ := exists_alternatingFour_commute h2 hodd
  refine ⟨X.map e.symm.toMonoidHom, ?_, ⟨(X.equivMapOfInjective _ e.symm.injective).symm.trans eX⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 : (MulAut.congr e β) x = x := by
    rw [← hπ]
    apply Subtype.ext
    rw [AutL2Facts.a7Conj_apply, hX x hx]
    group
  have h2 := congrArg e.symm h1
  simpa [MulAut.congr_apply] using h2

theorem fieldCentralizer_b_alt7 {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* alternatingGroup (Fin 7)) {W : Subgroup Y} (hW : IsKleinFour W) {γ : MulAut Y}
    (hγ : ∀ w ∈ W, γ w = w → w = 1) {E : Subgroup (MulAut Y)}
    (hE : ∀ α ∈ E, α * γ = γ * α ∧ ∀ w ∈ W, α w = w) : ¬ IsKleinFour E :=
  not_isKleinFour_of_centralizer (Or.inl ⟨e⟩) (conj_injective_of_footeSimpleType (Or.inl ⟨e⟩))
    (fun _ haa haW => mem_of_centralizes_kleinFour_alt7 e hW haa haW) hγ hE

end CFSG.ComponentClassification.Sol78
