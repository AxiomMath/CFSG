module

public import CFSG.Quasithin.H13.A7SectionRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Equiv Equiv.Perm

theorem exists_hom_elemAbelian_commute_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ (N : ℕ) (α : Type) [Fintype α] [DecidableEq α], Fintype.card α = N →
      ∀ σ : Perm α, σ ^ p = 1 →
        ∃ (B : Type) (_ : Group B) (F : B →* Perm α), (∀ a b : B, a * b = b * a) ∧
          (∀ a : B, a ^ p = 1) ∧ Nat.card B = p ^ (N / p) ∧ Function.Injective F ∧
          ∀ b, Commute (F b) σ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro α _ _ hcard σ hσ
  by_cases hσ1 : σ = 1
  · subst hσ1
    obtain ⟨B, _, hc, hp', hB, F, hF, -⟩ :=
      CFSG.Quasithin.H13.A7.exists_elementary_alternating (n := N) (p := p) hp2 (N / p)
        (Nat.div_mul_le_self N p)
    let e0 : α ≃ Fin N := Fintype.equivFinOfCardEq hcard
    exact ⟨B, inferInstance, e0.symm.permCongrHom.toMonoidHom.comp
      ((alternatingGroup (Fin N)).subtype.comp F), hc, hp', hB,
      e0.symm.permCongrHom.injective.comp (Subtype.val_injective.comp hF),
      fun b => Commute.one_right _⟩
  · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra h
      push Not at h
      exact hσ1 (Equiv.ext h)
    set c : Perm α := σ.cycleOf x with hcdef
    have hcycle : c.IsCycle := isCycle_cycleOf σ hx
    have hcmem : c ∈ σ.cycleFactorsFinset := by
      rw [hcdef, cycleOf_mem_cycleFactorsFinset_iff, mem_support]
      exact hx
    have hdisj : Disjoint (σ * c⁻¹) c := disjoint_mul_inv_of_mem_cycleFactorsFinset hcmem
    have hcx : c x ≠ x := by
      rw [hcdef, cycleOf_apply_self]
      exact hx
    have hord : orderOf c = p := by
      have hd : orderOf c ∣ p :=
        (orderOf_cycleOf_dvd_orderOf σ x).trans (orderOf_dvd_of_pow_eq_one hσ)
      rcases (Nat.dvd_prime hp.out).1 hd with h1 | h1
      · exfalso
        have hc1 : c = 1 := orderOf_eq_one_iff.1 h1
        exact hcx (by rw [hc1]; rfl)
      · exact h1
    have hcp : c ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one c
    have hsupp : c.support.card = p := by rw [← hcycle.orderOf, hord]
    have hpN : p ≤ N := by
      rw [← hcard, ← hsupp]
      exact Finset.card_le_univ _
    set σ' : Perm α := σ * c⁻¹ with hσ'
    have hcomm : Commute σ' c := hdisj.commute
    have hσσ' : σ = σ' * c := by rw [hσ']; group
    have hσ'p : σ' ^ p = 1 := by
      have h1 : σ ^ p = σ' ^ p * c ^ p := by rw [hσσ', hcomm.mul_pow]
      rw [hσ, hcp, mul_one] at h1
      exact h1.symm
    let Q : α → Prop := fun y => c y = y
    haveI : DecidablePred Q := fun y => inferInstanceAs (Decidable (c y = y))
    have hcQ : ∀ y, Q (σ' y) ↔ Q y := by
      intro y
      have h1 : σ' (c y) = c (σ' y) := by
        have := congrArg (fun f : Perm α => f y) hcomm.eq
        simpa using this
      change c (σ' y) = σ' y ↔ c y = y
      rw [← h1]
      exact ⟨fun h => σ'.injective h, fun h => by rw [h]⟩
    have hσ'Q : ∀ y, σ' y ≠ y → Q y := by
      intro y hy
      rcases hdisj y with h | h
      · exact absurd h hy
      · exact h
    set σ'' : Perm {y // Q y} := σ'.subtypePerm hcQ with hσ''
    have hof : ofSubtype σ'' = σ' := ofSubtype_subtypePerm hcQ hσ'Q
    have hσ''p : σ'' ^ p = 1 := by
      apply ofSubtype_injective (p := Q)
      rw [map_pow, hof, hσ'p, map_one]
    have hcard' : Fintype.card {y // Q y} = N - p := by
      rw [Fintype.card_subtype, ← hcard, ← hsupp, ← Finset.card_compl]
      congr 1
      ext y
      simp [Q, mem_support]
    obtain ⟨B', _, F', hc', hp', hB', hF', hFσ''⟩ :=
      ih (N - p) (by have := hp.out.pos; omega) {y // Q y} hcard' σ'' hσ''p
    set G : B' →* Perm α := (ofSubtype (p := Q)).comp F' with hG
    have hGinj : Function.Injective G := ofSubtype_injective.comp hF'
    have hGc : ∀ b, Commute (G b) c := by
      intro b
      refine Disjoint.commute fun z => ?_
      by_cases hz : Q z
      · exact Or.inr hz
      · exact Or.inl (ofSubtype_apply_of_not_mem _ hz)
    have hy1 : c ∉ G.range := by
      rintro ⟨b, hb⟩
      have h1 : G b x = x := ofSubtype_apply_of_not_mem _ hcx
      rw [hb] at h1
      exact hcx h1
    obtain ⟨F'', hF''i, hF''c, hF''p, hF''card, hF''form⟩ :=
      CFSG.SectionRank.exists_extend hc' hp' hB' G hGinj hcp hy1 hGc
    refine ⟨B' × Subgroup.zpowers c, inferInstance, F'', hF''c, hF''p, ?_, hF''i, ?_⟩
    · rw [hF''card]
      congr 1
      have h1 : N / p = (N - p) / p + 1 := by
        conv_lhs => rw [← Nat.sub_add_cancel hpN]
        exact Nat.add_div_right _ hp.out.pos
      omega
    · intro a
      obtain ⟨b, n, hbn⟩ := hF''form a
      rw [hbn, hσσ']
      have hGσ' : Commute (G b) σ' := by
        have := (hFσ'' b).map (ofSubtype (p := Q))
        rwa [hof] at this
      exact (hGσ'.mul_left ((hcomm.symm).pow_left n)).mul_right
        ((hGc b).mul_left ((Commute.refl c).pow_left n))

end CFSG.LocalAnalysis.RankFourTheoremC
