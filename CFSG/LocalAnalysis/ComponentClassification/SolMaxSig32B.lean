module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpAltComp
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem card_support_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (ε : α ≃ β) (g : Perm α) :
    (ε.permCongr g).support.card = g.support.card := by
  have h : (ε.permCongr g).support = g.support.map ε.toEmbedding := by
    ext b
    simp only [Perm.mem_support, Finset.mem_map_equiv, ne_eq, permCongr_apply,
      ← Equiv.eq_symm_apply]
  rw [h, Finset.card_map]

theorem card_support_ofSubtype {α : Type*} [Fintype α] [DecidableEq α] {p : α → Prop}
    [DecidablePred p] [Fintype (Subtype p)] (u : Perm (Subtype p)) :
    (Perm.ofSubtype u).support.card = u.support.card := by
  rw [Perm.support_ofSubtype, Finset.card_map]
  convert rfl

theorem card_support_mulEquiv_alt {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {k : ℕ} (hα : Fintype.card α = k) (hβ : Fintype.card β = k) (hk : 7 ≤ k)
    (φ : alternatingGroup α ≃* alternatingGroup β) (g : alternatingGroup α) :
    ((φ g : alternatingGroup β) : Perm β).support.card = (g : Perm α).support.card := by
  classical
  let εα : α ≃ Fin k := Fintype.equivFinOfCardEq hα
  let εβ : β ≃ Fin k := Fintype.equivFinOfCardEq hβ
  let ψ : alternatingGroup (Fin k) ≃* alternatingGroup (Fin k) :=
    (εα.altCongrHom.symm.trans φ).trans εβ.altCongrHom
  obtain ⟨π, hπ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj k
    (by omega) (by omega)).2 ψ
  have hψ : ∀ x : alternatingGroup (Fin k),
      ((ψ x : alternatingGroup (Fin k)) : Perm (Fin k)) = π * x * π⁻¹ := by
    intro x
    rw [← hπ]
    rfl
  have h1 : ψ (εα.altCongrHom g) = εβ.altCongrHom (φ g) := by
    change εβ.altCongrHom (φ (εα.altCongrHom.symm (εα.altCongrHom g))) = _
    rw [MulEquiv.symm_apply_apply]
  have h2 : ((εβ.altCongrHom (φ g) : alternatingGroup (Fin k)) : Perm (Fin k)) =
      π * εα.permCongr (g : Perm α) * π⁻¹ := by
    rw [← h1, hψ]
    rfl
  have h3 : ((εβ.altCongrHom (φ g) : alternatingGroup (Fin k)) : Perm (Fin k)) =
      εβ.permCongr ((φ g : alternatingGroup β) : Perm β) := rfl
  rw [← card_support_permCongr εβ, ← h3, h2, Perm.card_support_conj, card_support_permCongr]

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sq_apply_mem_pair {σ w : Perm α} (hσ : σ * σ = 1) (h4 : σ.support.card ≤ 4)
    (hw : w * σ = σ * w) {x : α} (hx : x ∈ σ.support) : w (w x) = x ∨ w (w x) = σ x := by
  have hσσ : ∀ z, σ (σ z) = z := fun z => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  have hwσ : ∀ z, w (σ z) = σ (w z) := fun z => by rw [← Perm.mul_apply, hw, Perm.mul_apply]
  have hmem : ∀ z ∈ σ.support, w z ∈ σ.support := by
    intro z hz
    rw [Perm.mem_support] at hz ⊢
    intro h
    apply hz
    apply w.injective
    rw [hwσ, h]
  have hx' : σ x ≠ x := Perm.mem_support.mp hx
  by_cases hc : w x = x ∨ w x = σ x
  · left
    rcases hc with h | h
    · rw [h, h]
    · rw [h, hwσ, h, hσσ]
  · push Not at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hu : w x ∈ σ.support := hmem x hx
    have hu' : σ (w x) ≠ w x := Perm.mem_support.mp hu
    have hux : σ (w x) ≠ x := by
      intro h
      apply hc2
      have h' := congrArg σ h
      rwa [hσσ] at h'
    have hux' : σ (w x) ≠ σ x := fun h => hc1 (σ.injective h)
    have hsub : ({x, σ x, w x, σ (w x)} : Finset α) ⊆ σ.support := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact hx
      · exact Perm.mem_support.mpr (by rw [hσσ]; exact hx'.symm)
      · exact hu
      · exact Perm.mem_support.mpr (by rw [hσσ]; exact hu'.symm)
    have hcard : ({x, σ x, w x, σ (w x)} : Finset α).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hu'.symm]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hc2, Ne.symm hux'⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hx'.symm, Ne.symm hc1, Ne.symm hux⟩
    have heq : ({x, σ x, w x, σ (w x)} : Finset α) = σ.support :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact h4)
    have hwu : w (w x) ∈ σ.support := hmem _ hu
    rw [← heq] at hwu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwu
    rcases hwu with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (w.injective h) hc1
    · exfalso
      apply hc2
      apply w.injective
      rw [h, hwσ]

theorem apply_eq_of_odd_commute {σ y : Perm α} (hσ : σ * σ = 1) (h4 : σ.support.card ≤ 4)
    (hy : y * σ = σ * y) (hodd : Odd (orderOf y)) {x : α} (hx : x ∈ σ.support) : y x = x := by
  obtain ⟨j, hj⟩ := hodd
  have hw2 : y ^ (j + 1) * y ^ (j + 1) = y := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hwσ : y ^ (j + 1) * σ = σ * y ^ (j + 1) := (Commute.pow_left hy (j + 1)).eq
  have h1 := sq_apply_mem_pair hσ h4 hwσ hx
  rw [← Perm.mul_apply, hw2] at h1
  rcases h1 with h | h
  · exact h
  · exfalso
    have hyσ : y (σ x) = x := by
      rw [← Perm.mul_apply, hy, Perm.mul_apply, h, ← Perm.mul_apply, hσ, Perm.one_apply]
    have key : ∀ i : ℕ, (y ^ (2 * i + 1)) x = σ x := by
      intro i
      induction i with
      | zero => simpa using h
      | succ i ih =>
        rw [show 2 * (i + 1) + 1 = 2 + (2 * i + 1) by ring, pow_add, Perm.mul_apply, ih, sq,
          Perm.mul_apply, hyσ, h]
    have h2 := key j
    rw [← hj, pow_orderOf_eq_one, Perm.one_apply] at h2
    exact (Perm.mem_support.mp hx) h2.symm

variable {n : ℕ}

theorem eq_one_of_commute_fixAlt {τ y : Perm (Fin n)} (hfix : ∀ x ∈ τ.support, y x = x)
    (h4 : 4 ≤ n - τ.support.card)
    (hc : ∀ b ∈ fixAlt τ, y * (b : Perm (Fin n)) = (b : Perm (Fin n)) * y) : y = 1 := by
  classical
  refine Equiv.ext fun x => ?_
  rw [Perm.one_apply]
  by_cases hx : x ∈ τ.support
  · exact hfix x hx
  · have hcard : 2 < ((τ.supportᶜ).erase x).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_compl.mpr hx), Finset.card_compl,
        Fintype.card_fin]
      omega
    obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.mp hcard
    rw [Finset.mem_erase, Finset.mem_compl] at ha hb hd
    have hcyc : ∀ u v : Fin n, u ≠ x → v ≠ x → u ≠ v → u ∉ τ.support → v ∉ τ.support →
        y x = x ∨ y x = u ∨ y x = v := by
      intro u v hux hvx huv hu hv
      have hnd : [x, u, v].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
          not_or, List.nodup_nil, and_true, not_false_eq_true]
        exact ⟨⟨hux.symm, hvx.symm⟩, huv⟩
      set c : Perm (Fin n) := swap x u * swap u v with hcdef
      have hcs : c.support = {x, u, v} := Perm.support_swap_mul_swap hnd
      have hcA : c ∈ alternatingGroup (Fin n) := by
        rw [Perm.mem_alternatingGroup, hcdef, Perm.sign_mul, Perm.sign_swap hux.symm,
          Perm.sign_swap huv]
        rfl
      have hcF : (⟨c, hcA⟩ : alternatingGroup (Fin n)) ∈ fixAlt τ := by
        rw [mem_fixAlt]
        change c.support ⊆ τ.supportᶜ
        rw [hcs]
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rw [Finset.mem_compl]
        rcases hz with rfl | rfl | rfl
        · exact hx
        · exact hu
        · exact hv
      have hyc := hc _ hcF
      change y * c = c * y at hyc
      have hxc : x ∈ c.support := by rw [hcs]; simp
      have hyxc : y x ∈ c.support := by
        rw [Perm.mem_support] at hxc ⊢
        intro h
        apply hxc
        apply y.injective
        rw [← Perm.mul_apply, hyc, Perm.mul_apply, h]
      rw [hcs] at hyxc
      simpa using hyxc
    rcases hcyc a b ha.1 hb.1 hab ha.2 hb.2 with h1 | h1 | h1
    · exact h1
    · rcases hcyc b d hb.1 hd.1 hbd hb.2 hd.2 with h2 | h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hab
      · exact absurd (h1.symm.trans h2) had
    · rcases hcyc a d ha.1 hd.1 had ha.2 hd.2 with h2 | h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) (Ne.symm hab)
      · exact absurd (h1.symm.trans h2) hbd

theorem exists_fixAlt_equiv (τ : Perm (Fin n)) :
    ∃ φ : alternatingGroup ↥(τ.supportᶜ : Finset (Fin n)) ≃* fixAlt τ, ∀ a,
      (((φ a : fixAlt τ) : alternatingGroup (Fin n)) : Perm (Fin n)) =
        Perm.ofSubtype (a : Perm ↥(τ.supportᶜ : Finset (Fin n))) :=
  ⟨MonoidHom.ofInjective alternatingGroup.ofSubtype_injective, fun _ => rfl⟩

theorem even_card_alternatingGroup {β : Type*} [Fintype β] [DecidableEq β]
    (h4 : 4 ≤ Fintype.card β) : Even (Nat.card (alternatingGroup β)) := by
  have : Nontrivial β := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial h4
  rw [hc, show (4 : ℕ).factorial = 24 by rfl]
  exact ⟨6 * c, by omega⟩

theorem isSimpleGroup_fixAlt {τ : Perm (Fin n)} (h5 : 5 ≤ n - τ.support.card) :
    IsSimpleGroup (fixAlt τ) := by
  have hcard : 5 ≤ Nat.card ↥(τ.supportᶜ : Finset (Fin n)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    exact h5
  have : IsSimpleGroup (alternatingGroup ↥(τ.supportᶜ : Finset (Fin n))) :=
    alternatingGroup.isSimpleGroup hcard
  exact MulEquiv.isSimpleGroup (fixAltEquiv τ).symm

theorem card_fixAlt {τ : Perm (Fin n)} (h2 : 2 ≤ n - τ.support.card) :
    Nat.card (fixAlt τ) = (n - τ.support.card).factorial / 2 := by
  have hcard : Fintype.card ↥(τ.supportᶜ : Finset (Fin n)) = n - τ.support.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have : Nontrivial ↥(τ.supportᶜ : Finset (Fin n)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rw [← Nat.card_congr (fixAltEquiv τ).toEquiv, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, hcard]

theorem eq_bot_of_odd_of_commute {τ : Perm (Fin n)} (hτ : τ * τ = 1) (h4 : τ.support.card ≤ 4)
    (h5 : 5 ≤ n - τ.support.card) {N : Subgroup (alternatingGroup (Fin n))}
    (hodd : Odd (Nat.card N)) (hc : ∀ g ∈ N, (g : Perm (Fin n)) * τ = τ * g)
    (hn : ∀ b ∈ fixAlt τ, ∀ g ∈ N, b * g * b⁻¹ ∈ N) : N = ⊥ := by
  classical
  have hle : N ≤ fixAlt τ := by
    intro g hg
    have hog : Odd (orderOf (g : Perm (Fin n))) := by
      rw [Subgroup.orderOf_coe]
      have h1 : orderOf g ∣ Nat.card N := by
        rw [← Subgroup.orderOf_mk g hg]
        exact orderOf_dvd_natCard _
      exact hodd.of_dvd_nat h1
    rw [mem_fixAlt]
    intro z hz
    rw [Finset.mem_compl]
    intro hzτ
    exact (Perm.mem_support.mp hz) (apply_eq_of_odd_commute hτ h4 (hc g hg) hog hzτ)
  have : IsSimpleGroup (fixAlt τ) := isSimpleGroup_fixAlt h5
  have hnorm : (N.subgroupOf (fixAlt τ)).Normal := by
    constructor
    intro g hg b
    rw [mem_subgroupOf] at hg ⊢
    exact hn b b.2 g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (fixAlt τ)) with h | h
  · rwa [subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hle] at h
  · exfalso
    rw [subgroupOf_eq_top] at h
    have hF : fixAlt τ ≤ N := h
    have h1 : Nat.card (fixAlt τ) ∣ Nat.card N := card_dvd_of_le hF
    have h2 : Even (Nat.card (fixAlt τ)) := by
      rw [Nat.card_congr (fixAltEquiv τ).symm.toEquiv]
      exact even_card_alternatingGroup (by
        rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
        omega)
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat h1)) h2

theorem card_support_of_le_fixAlt {r k : ℕ} (hk : 7 ≤ k) {τ : Perm (Fin r)}
    (hτk : r - τ.support.card = k) {P : Subgroup (alternatingGroup (Fin r))}
    (hP : P ≤ fixAlt τ) {β : Type*} [Fintype β] [DecidableEq β] (hβ : Fintype.card β = k)
    (ψ : alternatingGroup β ≃* P) (g : alternatingGroup β) :
    (((ψ g : P) : alternatingGroup (Fin r)) : Perm (Fin r)).support.card =
      (g : Perm β).support.card := by
  classical
  have : Nontrivial β := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hPc : Nat.card P = k.factorial / 2 := by
    rw [← Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, hβ]
  have hFc : Nat.card (fixAlt τ) = k.factorial / 2 := by
    rw [card_fixAlt (by omega), hτk]
  have hPeq : P = fixAlt τ := eq_of_le_of_card_ge hP (by rw [hPc, hFc])
  have hcard : Fintype.card ↥(τ.supportᶜ : Finset (Fin r)) = k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hτk]
  obtain ⟨φ, hφ⟩ := exists_fixAlt_equiv τ
  let Ψ : alternatingGroup β ≃* alternatingGroup ↥(τ.supportᶜ : Finset (Fin r)) :=
    (ψ.trans (MulEquiv.subgroupCongr hPeq)).trans φ.symm
  have hΨ : (((ψ g : P) : alternatingGroup (Fin r)) : Perm (Fin r)) =
      Perm.ofSubtype ((Ψ g : alternatingGroup ↥(τ.supportᶜ : Finset (Fin r))) :
        Perm ↥(τ.supportᶜ : Finset (Fin r))) := by
    have h1 : φ (Ψ g) = MulEquiv.subgroupCongr hPeq (ψ g) := by
      change φ (φ.symm _) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [← hφ, h1]
    rfl
  rw [hΨ, card_support_ofSubtype]
  exact card_support_mulEquiv_alt hβ hcard hk Ψ g

end CFSG.ComponentClassification.SolMax
