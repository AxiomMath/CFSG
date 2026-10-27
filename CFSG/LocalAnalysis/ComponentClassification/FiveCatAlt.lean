module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatDefs
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigPerm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpNotLie

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem eq_of_factorial_div_two_eq_aux {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : a.factorial / 2 = b.factorial / 2) : a = b := by
  have h2a : 2 ∣ a.factorial := Nat.dvd_factorial (by norm_num) ha
  have h2b : 2 ∣ b.factorial := Nat.dvd_factorial (by norm_num) hb
  have h1 : a.factorial = b.factorial := by
    rw [← Nat.div_mul_cancel h2a, ← Nat.div_mul_cancel h2b, h]
  exact (Nat.factorial_inj (by omega)).mp h1

private theorem sixty_le_card {P : Type} [Group P] [Finite P] {Z : Subgroup P} [Z.Normal]
    (e : P ⧸ Z ≃* alternatingGroup (Fin 5)) : 60 ≤ Nat.card P := by
  have h1 : Nat.card (P ⧸ Z) = 60 := by
    rw [card_of_mulEquiv_alt (by norm_num) e]
    decide
  exact h1 ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)

private theorem eq_one_of_commute_threeCycles {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ω₀ : Ω}
    (h5 : 5 ≤ Fintype.card Ω) {y : Perm Ω} (hy : y ω₀ = ω₀)
    (hc : ∀ a b d : Ω, a ≠ ω₀ → b ≠ ω₀ → d ≠ ω₀ → a ≠ b → b ≠ d → a ≠ d →
      y * (swap a b * swap b d) = (swap a b * swap b d) * y) : y = 1 := by
  refine Equiv.ext fun x => ?_
  rw [Perm.one_apply]
  by_cases hx : x = ω₀
  · rw [hx]
    exact hy
  have hcard : 2 < (((Finset.univ : Finset Ω).erase ω₀).erase x).card := by
    rw [Finset.card_erase_of_mem (by simp [hx]), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.mp hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha hb hd
  have hcyc : ∀ u v : Ω, u ≠ ω₀ → v ≠ ω₀ → u ≠ x → v ≠ x → u ≠ v →
      y x = x ∨ y x = u ∨ y x = v := by
    intro u v hu hv hux hvx huv
    have hyc := hc x u v hx hu hv (Ne.symm hux) huv (Ne.symm hvx)
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have h4 := congrArg (fun f : Perm Ω => f x) hyc
    simp only [Perm.mul_apply] at h4
    rw [swap_apply_of_ne_of_ne (Ne.symm hux) (Ne.symm hvx), swap_apply_left,
      swap_apply_of_ne_of_ne h2 h3, swap_apply_of_ne_of_ne h1 h2] at h4
    exact hux (y.injective h4)
  rcases hcyc a b ha.2 hb.2 ha.1 hb.1 hab with h1 | h1 | h1
  · exact h1
  · rcases hcyc b d hb.2 hd.2 hb.1 hd.1 hbd with h2 | h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hab
    · exact absurd (h1.symm.trans h2) had
  · rcases hcyc a d ha.2 hd.2 ha.1 hd.1 had with h2 | h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hab.symm
    · exact absurd (h1.symm.trans h2) hbd

private theorem false_of_alt_six {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (θ : S ≃* alternatingGroup (Fin 6)) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P)
    (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 5)) : False := by
  classical
  have hσ1 : σ ≠ 1 := h.ne_one
  obtain ⟨hσ2, hPF, -, hPtop⟩ := h
  have hS : Nat.card S = 360 := by
    rw [card_of_mulEquiv_alt (by norm_num) θ]
    decide
  have hP60 : 60 ≤ Nat.card P := sixty_le_card eP
  have hPfix : ∀ p ∈ P, σ p = p := fun p hp =>
    LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff.mp (hPF hp)
  letI : Fintype (S ⧸ P) := Fintype.ofFinite _
  let ρ : S →* Perm (S ⧸ P) := MulAction.toPermHom S (S ⧸ P)
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P.normalCore with h0 | h1
    · exact h0
    · exact absurd (top_le_iff.mp (h1 ▸ P.normalCore_le)) hPtop
  have hindex : Nat.card (S ⧸ P) * Nat.card P = 360 := by
    rw [← hS]
    exact P.index_mul_card
  have hΩ6 : Nat.card (S ⧸ P) = 6 := by
    have hle : Nat.card (S ⧸ P) ≤ 6 := by
      by_contra hcon
      have : 7 * 60 ≤ Nat.card (S ⧸ P) * Nat.card P := Nat.mul_le_mul (by omega) hP60
      omega
    have hge : 360 ≤ Nat.card (Perm (S ⧸ P)) := hS ▸ Nat.card_le_card_of_injective ρ hρinj
    rw [Nat.card_perm] at hge
    by_contra hne
    have h5 : Nat.card (S ⧸ P) ≤ 5 := by omega
    have h1 := Nat.factorial_le h5
    have h120 : (5 : ℕ).factorial = 120 := by decide
    omega
  have hΩcard : Fintype.card (S ⧸ P) = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact hΩ6
  have hrange : Nat.card ρ.range = 360 := by
    rw [← hS]
    exact (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  have hidx : ρ.range.index ≤ 2 := by
    have h1 := ρ.range.index_mul_card
    rw [hrange, Nat.card_perm, hΩ6] at h1
    have h720 : (6 : ℕ).factorial = 720 := by decide
    omega
  have hAlt : alternatingGroup (S ⧸ P) ≤ ρ.range :=
    Perm.alternatingGroup_le_of_index_le_two hidx
  obtain ⟨f, hf⟩ : ∃ f : S ⧸ P → S ⧸ P, ∀ g : S, f (g : S ⧸ P) = ((σ g : S) : S ⧸ P) := by
    refine ⟨fun ω => ((σ ω.out : S) : S ⧸ P), fun g => ?_⟩
    obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul P g
    show ((σ (g : S ⧸ P).out : S) : S ⧸ P) = _
    rw [hp, map_mul, hPfix p p.2]
    exact QuotientGroup.mk_mul_of_mem _ p.2
  have hff : Function.Involutive f := by
    intro ω
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    rw [hf, hf, hσ2]
  let s : Perm (S ⧸ P) := Function.Involutive.toPerm f hff
  have hskey : ∀ (g : S) (ω : S ⧸ P), s (g • ω) = σ g • s ω := by
    intro g ω
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ω
    change f (((g * x : S) : S ⧸ P)) = σ g • f (x : S ⧸ P)
    rw [hf, hf]
    change ((σ (g * x) : S) : S ⧸ P) = ((σ g * σ x : S) : S ⧸ P)
    rw [map_mul]
  have hs0 : s ((1 : S) : S ⧸ P) = ((1 : S) : S ⧸ P) := by
    change f _ = _
    rw [hf, map_one]
  have hsc : ∀ q ∈ P, s * ρ q = ρ q * s := by
    intro q hq
    ext ω
    change s (q • ω) = q • s ω
    rw [hskey, hPfix q hq]
  have hs1 : s = 1 := by
    refine eq_one_of_commute_threeCycles (ω₀ := ((1 : S) : S ⧸ P)) (by omega) hs0 ?_
    intro a b d ha hb hd hab hbd had
    have hgA : (swap a b * swap b d : Perm (S ⧸ P)) ∈ alternatingGroup (S ⧸ P) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hbd]
      rfl
    obtain ⟨q, hq⟩ := hAlt hgA
    have hgω : (swap a b * swap b d : Perm (S ⧸ P)) ((1 : S) : S ⧸ P) = ((1 : S) : S ⧸ P) := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hb) (Ne.symm hd),
        swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)]
    have hqP : q ∈ P := by
      have h1 : ((q * 1 : S) : S ⧸ P) = ((1 : S) : S ⧸ P) := by
        change ρ q ((1 : S) : S ⧸ P) = _
        rw [hq]
        exact hgω
      rw [QuotientGroup.eq] at h1
      have h2 : q⁻¹ ∈ P := by simpa using h1
      exact inv_mem_iff.mp h2
    rw [← hq]
    exact hsc q hqP
  apply hσ1
  refine MulEquiv.ext fun g => ?_
  apply hρinj
  ext ω
  have h1 := hskey g ω
  rw [hs1] at h1
  simp only [Perm.one_apply] at h1
  exact h1.symm

private theorem alt_five_layer {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    {σ : MulAut (alternatingGroup (Fin n))} {P : Subgroup (alternatingGroup (Fin n))}
    (h : ProperFixedComponent σ P)
    (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 5)) :
    ∃ τ : Perm (Fin n), orderOf τ = 2 ∧ σ = MulAut.conjNormal τ ∧ P = fixAlt τ ∧
      ∃ k : ℕ, n = 7 + 2 * k := by
  obtain ⟨τ, hτ2, hστ, hdeg, ⟨eA⟩⟩ :=
    exists_involution_of_properFixedComponent_alternating hn hn6 h
  have hΩ5 : (Finset.univ.filter fun x => τ x = x).card = 5 := by
    have h1 := card_of_mulEquiv_alt (m := 5) (by norm_num) (eA.symm.trans eP)
    have : Nontrivial ↥(Finset.univ.filter fun x => τ x = x) := by
      rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]
      omega
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_coe] at h1
    exact eq_of_factorial_div_two_eq_aux (by omega) (by norm_num) h1
  have hsum : (Finset.univ.filter fun x => τ x = x).card + τ.support.card = n := by
    have hsupp : τ.support = Finset.univ.filter fun x => ¬ τ x = x := rfl
    rw [hsupp, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (σ := τ) (by rw [hτ2]; exact Nat.prime_two)
  have heven : τ.support.card = 2 * (k + 1) := by
    rw [← Equiv.Perm.sum_cycleType, hk, hτ2, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : P ≤ fixAlt τ := by
    have hPF : P ≤ fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ) := by
      rw [← hστ]
      exact h.2.1
    have hPc : IsPComponent 2
        (P.subgroupOf (fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ))) := by
      rw [← hστ]
      exact h.2.2.1
    intro x hx
    rw [mem_fixAlt]
    intro ω hω
    rw [Finset.mem_compl, Perm.mem_support, not_not]
    by_contra hcon
    exact (Perm.mem_support.mp hω) (support_of_isPComponent_fixed_conj hτ2 hPF hPc x hx ω hcon)
  have hcardfix : Nat.card (fixAlt τ) = 60 := by
    have h5 : n - τ.support.card = 5 := by omega
    rw [card_fixAlt (by omega), h5]
    decide
  exact ⟨τ, hτ2, hστ, Subgroup.eq_of_le_of_card_ge hle (by rw [hcardfix]; exact sixty_le_card eP),
    k, by omega⟩

theorem fivePump_alt : FivePumpAltClause := by
  intro S _ _ hs _ ⟨n, hn, ⟨θ⟩⟩ σ P hP _ ⟨eP⟩ _
  haveI := hs
  by_cases hn6 : n = 6
  · subst hn6
    exact (false_of_alt_six θ hP eP).elim
  obtain ⟨hP', ⟨e⟩⟩ := hP.map θ
  obtain ⟨-, -, -, -, k, hk⟩ := alt_five_layer hn hn6 hP' (e.symm.trans eP)
  exact Or.inl ⟨n, ⟨k + 3, by omega⟩, by omega, ⟨θ⟩⟩

theorem fiveTwoLayer_alt : FiveTwoLayerAltClause := by
  intro S _ _ hs _ ⟨n, hn, ⟨θ⟩⟩ σ P₁ P₂ h₁ h₂ hne _ _ ⟨e₁⟩ ⟨e₂⟩ _
  haveI := hs
  by_cases hn6 : n = 6
  · subst hn6
    exact (false_of_alt_six θ h₁ e₁).elim
  obtain ⟨h₁', ⟨f₁⟩⟩ := h₁.map θ
  obtain ⟨h₂', ⟨f₂⟩⟩ := h₂.map θ
  obtain ⟨τ₁, -, hστ₁, hP₁, -⟩ := alt_five_layer hn hn6 h₁' (f₁.symm.trans e₁)
  obtain ⟨τ₂, -, hστ₂, hP₂, -⟩ := alt_five_layer hn hn6 h₂' (f₂.symm.trans e₂)
  have hττ : τ₁ = τ₂ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).1
      (hστ₁.symm.trans hστ₂)
  exact absurd (Subgroup.map_injective θ.injective (hP₁.trans (hττ ▸ hP₂.symm))) hne

end CFSG.ComponentClassification.SolMax.FiveCat
