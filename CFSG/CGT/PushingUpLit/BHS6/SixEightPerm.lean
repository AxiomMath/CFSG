module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS

variable {n : ℕ}

theorem exists_fixed_of_swaps (hn : Odd n) {T' : Set (Equiv.Perm (Fin n))}
    (hs : ∀ t ∈ T', t.IsSwap) (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) :
    ∃ c, ∀ t ∈ T', t c = c := by
  classical
  by_contra h
  push Not at h
  have hfin : T'.Finite := Set.toFinite T'
  have hU : hfin.toFinset.biUnion Equiv.Perm.support = Finset.univ := by
    refine Finset.eq_univ_iff_forall.2 fun m => ?_
    obtain ⟨t, htT, htm⟩ := h m
    exact Finset.mem_biUnion.2 ⟨t, hfin.mem_toFinset.2 htT, Equiv.Perm.mem_support.2 htm⟩
  have hd : (↑hfin.toFinset : Set (Equiv.Perm (Fin n))).PairwiseDisjoint Equiv.Perm.support := by
    intro t ht t' ht' hne
    have ht1 := hfin.mem_toFinset.1 ht
    have ht2 := hfin.mem_toFinset.1 ht'
    exact disjoint_support_of_commute (hs t ht1) (hs t' ht2) (hc t ht1 t' ht2) hne
  have hcard := Finset.card_biUnion hd
  rw [hU, Finset.card_univ, Fintype.card_fin] at hcard
  have h2 : ∑ t ∈ hfin.toFinset, t.support.card = ∑ t ∈ hfin.toFinset, 2 :=
    Finset.sum_congr rfl fun t ht =>
      Equiv.Perm.card_support_eq_two.2 (hs t (hfin.mem_toFinset.1 ht))
  rw [h2, Finset.sum_const, smul_eq_mul] at hcard
  obtain ⟨k, hk⟩ := hn
  omega

theorem mem_normalizer_zpowers_of_conj {α : Type*} [Group α] {d a : α}
    (h1 : a * d * a⁻¹ ∈ Subgroup.zpowers d) (h2 : a⁻¹ * d * a ∈ Subgroup.zpowers d) :
    a ∈ Subgroup.normalizer (Subgroup.zpowers d : Set α) := by
  have key : ∀ b : α, b * d * b⁻¹ ∈ Subgroup.zpowers d →
      ∀ h ∈ Subgroup.zpowers d, b * h * b⁻¹ ∈ Subgroup.zpowers d := by
    intro b hb h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hb k
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key a h1 h, fun hh => ?_⟩
  have := key a⁻¹ (by simpa using h2) _ hh
  simpa [mul_assoc] using this

theorem injective_triple {a b c : Fin n} (h01 : a ≠ b) (h02 : a ≠ c) (h12 : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

theorem exists_tri {a b c : Fin n} (h01 : a ≠ b) (h02 : a ≠ c) (h12 : b ≠ c) :
    ∃ p : Fin 3 → Fin n, Function.Injective p ∧ p 0 = a ∧ p 1 = b ∧ p 2 = c :=
  ⟨![a, b, c], injective_triple h01 h02 h12, rfl, rfl, rfl⟩

theorem closure_le_normalizer_zpowers_cyc {T' : Set (Equiv.Perm (Fin n))}
    (hs : ∀ t ∈ T', t.IsSwap) (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t)
    {t₀ : Equiv.Perm (Fin n)} (ht₀ : t₀ ∈ T') {x : Fin n} (hx : t₀ x ≠ x) {c : Fin n}
    (hcfix : ∀ t ∈ T', t c = c) :
    Subgroup.closure T' ≤
      Subgroup.normalizer (Subgroup.zpowers (cyc x (t₀ x) c) : Set (Equiv.Perm (Fin n))) := by
  classical
  refine (Subgroup.closure_le _).2 fun t ht => ?_
  have e1 : t₀ = Equiv.swap x (t₀ x) := eq_swap_of_isSwap_apply_ne (hs t₀ ht₀) hx
  have hy : t₀ (t₀ x) = x := by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (t₀ x)) e1
    simpa using this
  have hxy : x ≠ t₀ x := hx.symm
  have hxc : x ≠ c := fun h => hx (h ▸ hcfix t₀ ht₀)
  have hyc : t₀ x ≠ c := fun h => hxc (by
    have h1 := hcfix t₀ ht₀
    rw [← h, hy] at h1
    exact h1.trans h)
  by_cases htt : t = t₀
  · subst htt
    have hinv : t⁻¹ = t := by
      rw [e1, Equiv.swap_inv]
    have hconj : t * cyc x (t x) c * t⁻¹ = (cyc x (t x) c)⁻¹ := by
      rw [conj_cyc, hy, hcfix t ht, cyc_inv, cyc_swap12 hxy hxc hyc]
    have hconj' : t⁻¹ * cyc x (t x) c * t = (cyc x (t x) c)⁻¹ := by
      rw [hinv]
      rw [hinv] at hconj
      exact hconj
    have hdinv : (cyc x (t x) c)⁻¹ ∈ Subgroup.zpowers (cyc x (t x) c) :=
      Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    exact mem_normalizer_zpowers_of_conj (by rw [hconj]; exact hdinv)
      (by rw [hconj']; exact hdinv)
  · have hfx : t x = x := apply_eq_of_commute_swap (hs t₀ ht₀) (hs t ht) (hc t₀ ht₀ t ht)
      (Ne.symm htt) hx
    have hfy : t (t₀ x) = t₀ x :=
      apply_eq_of_commute_swap (hs t₀ ht₀) (hs t ht) (hc t₀ ht₀ t ht) (Ne.symm htt) (by
        rw [hy]
        exact hxy)
    have hd : t * cyc x (t₀ x) c * t⁻¹ = cyc x (t₀ x) c := by
      rw [conj_cyc, hfx, hfy, hcfix t ht]
    have hd' : t⁻¹ * cyc x (t₀ x) c * t = cyc x (t₀ x) c := by
      have h1 : t * cyc x (t₀ x) c = cyc x (t₀ x) c * t := mul_inv_eq_iff_eq_mul.1 hd
      calc t⁻¹ * cyc x (t₀ x) c * t = t⁻¹ * (cyc x (t₀ x) c * t) := by rw [mul_assoc]
        _ = t⁻¹ * (t * cyc x (t₀ x) c) := by rw [h1]
        _ = cyc x (t₀ x) c := inv_mul_cancel_left _ _
    exact mem_normalizer_zpowers_of_conj (by rw [hd]; exact Subgroup.mem_zpowers _)
      (by rw [hd']; exact Subgroup.mem_zpowers _)

theorem cyc_mem_alternatingGroup {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    cyc i j k ∈ alternatingGroup (Fin n) :=
  Equiv.Perm.mem_alternatingGroup.2 (cyc_isThreeCycle hij hik hjk).sign

end CFSG.CGT.PushingUpLit.BHS6
