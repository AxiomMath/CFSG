module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36E

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem eq_bot_of_perfect_of_isNilpotent {G : Type*} [Group G] [Group.IsNilpotent G]
    (h : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = (⊤ : Subgroup G)) : (⊤ : Subgroup G) = ⊥ := by
  obtain ⟨k, hk⟩ :=
    Subgroup.nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent G)
  have hall : ∀ j, (⊤ : Subgroup G).lowerCentralSeries j = ⊤ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Subgroup.lowerCentralSeries_succ, ih, h]
  rw [← hall k, hk]

theorem conj_mem_oddGen {C : Subgroup X} {g x : X} (hg : g ∈ C) (hx : x ∈ oddGen C) :
    g * x * g⁻¹ ∈ oddGen C := by
  change x ∈ Subgroup.closure _ at hx
  induction hx using closure_induction with
  | mem y hy =>
    refine mem_oddGen (mul_mem (mul_mem hg hy.1) (inv_mem hg)) ?_
    rw [show g * y * g⁻¹ = MulAut.conj g y from rfl, MulEquiv.orderOf_eq]
    exact hy.2
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul y z _ _ hy hz =>
    have h : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [h]
    exact mul_mem hy hz
  | inv y _ hy =>
    have h : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [h]
    exact inv_mem hy

theorem oddGen_eq_of_perfect [Finite X] {L : Subgroup X} (hL : ⁅L, L⁆ = L) : oddGen L = L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (oddGen_le L) ?_
  set K : Subgroup ↥L := (oddGen L).subgroupOf L with hKdef
  have hKn : K.Normal := ⟨fun x hx g => by
    rw [hKdef, mem_subgroupOf] at hx ⊢
    exact conj_mem_oddGen g.2 hx⟩
  have h2 : IsPGroup 2 (↥L ⧸ K) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, c, hc, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hKdef, mem_subgroupOf]
    refine mem_oddGen (x ^ 2 ^ a).2 ?_
    have h1 : (x ^ 2 ^ a) ^ c = 1 := by rw [← pow_mul, ← hord, pow_orderOf_eq_one]
    rw [Subgroup.orderOf_coe]
    exact hc.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  have hperf : ⁅(⊤ : Subgroup (↥L ⧸ K)), (⊤ : Subgroup (↥L ⧸ K))⁆ = (⊤ : Subgroup (↥L ⧸ K)) := by
    have hLtop : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
      apply map_injective L.subtype_injective
      rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
      exact hL
    have h3 := congrArg (Subgroup.map (QuotientGroup.mk' K)) hLtop
    rw [map_commutator, ← MonoidHom.range_eq_map, QuotientGroup.range_mk'] at h3
    exact h3
  have : Group.IsNilpotent (↥L ⧸ K) := h2.isNilpotent
  have hbot := eq_bot_of_perfect_of_isNilpotent hperf
  intro x hx
  have h4 : ((⟨x, hx⟩ : ↥L) : ↥L ⧸ K) ∈ (⊥ : Subgroup (↥L ⧸ K)) := by
    rw [← hbot]
    exact mem_top _
  rw [mem_bot, QuotientGroup.eq_one_iff, hKdef, mem_subgroupOf] at h4
  exact h4

theorem exists_equiv_of_mulEquiv_alt {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {k : ℕ} (hα : Fintype.card α = k) (hβ : Fintype.card β = k) (hk : 7 ≤ k)
    (φ : alternatingGroup α ≃* alternatingGroup β) :
    ∃ ε : α ≃ β, ∀ g : alternatingGroup α,
      ((φ g : alternatingGroup β) : Perm β) = ε.permCongr (g : Perm α) := by
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
  refine ⟨(εα.trans π).trans εβ.symm, fun g => ?_⟩
  have h1 : ψ (εα.altCongrHom g) = εβ.altCongrHom (φ g) := by
    change εβ.altCongrHom (φ (εα.altCongrHom.symm (εα.altCongrHom g))) = _
    rw [MulEquiv.symm_apply_apply]
  have h2 : εβ.permCongr ((φ g : alternatingGroup β) : Perm β) =
      π * εα.permCongr (g : Perm α) * π⁻¹ := by
    have h3 : ((εβ.altCongrHom (φ g) : alternatingGroup (Fin k)) : Perm (Fin k)) =
        εβ.permCongr ((φ g : alternatingGroup β) : Perm β) := rfl
    rw [← h3, ← h1, hψ]
    rfl
  ext b
  have h4 := congrArg (fun p : Perm (Fin k) => p (εβ b)) h2
  simp only [Equiv.permCongr_apply, Perm.mul_apply, Equiv.symm_apply_apply,
    Perm.inv_def] at h4
  simp only [Equiv.permCongr_apply, Equiv.trans_apply, Equiv.symm_trans_apply,
    Equiv.symm_symm]
  rw [← h4, Equiv.symm_apply_apply]

theorem exists_support_of_mulEquiv_fixAlt {r k : ℕ} {τ : Perm (Fin r)} {Y : Type*} [Fintype Y]
    [DecidableEq Y] (hk : 7 ≤ k) (hY : Fintype.card Y = k) (hτk : r - τ.support.card = k)
    (Φ : alternatingGroup Y ≃* fixAlt τ) (DY : Finset Y) :
    ∃ DN : Finset (Fin r), DN.card = DY.card ∧ DN ⊆ τ.supportᶜ ∧
      ∀ g : alternatingGroup Y, (∀ y ∉ DY, (g : Perm Y) y = y) →
        ∀ ω ∉ DN, (((Φ g : fixAlt τ) : alternatingGroup (Fin r)) : Perm (Fin r)) ω = ω := by
  classical
  obtain ⟨φ, hφ⟩ := exists_fixAlt_equiv τ
  have hcard : Fintype.card ↥(τ.supportᶜ : Finset (Fin r)) = k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hτk]
  obtain ⟨ε, hε⟩ := exists_equiv_of_mulEquiv_alt hY hcard hk (Φ.trans φ.symm)
  have hΦ : ∀ g : alternatingGroup Y,
      (((Φ g : fixAlt τ) : alternatingGroup (Fin r)) : Perm (Fin r)) =
        Perm.ofSubtype (ε.permCongr (g : Perm Y)) := by
    intro g
    have h1 : φ ((Φ.trans φ.symm) g) = Φ g := by
      change φ (φ.symm (Φ g)) = Φ g
      rw [MulEquiv.apply_symm_apply]
    rw [← h1, hφ, hε]
  refine ⟨(DY.map ε.toEmbedding).map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_map]
  · intro ω hω
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hω
    obtain ⟨w, -, rfl⟩ := hω
    exact w.2
  · intro g hg ω hω
    rw [hΦ]
    by_cases hωF : ω ∈ (τ.supportᶜ : Finset (Fin r))
    · have h1 : ε.symm ⟨ω, hωF⟩ ∉ DY := by
        intro h
        apply hω
        simp only [Finset.mem_map, Function.Embedding.coe_subtype]
        exact ⟨⟨ω, hωF⟩, ⟨_, h, by simp⟩, rfl⟩
      rw [Perm.ofSubtype_apply_of_mem _ hωF, Equiv.permCongr_apply, hg _ h1,
        Equiv.apply_symm_apply]
    · exact Perm.ofSubtype_apply_of_not_mem _ hωF

theorem sq_card_alt_gt (k : ℕ) (hk : 5 ≤ k) :
    (k + 2).factorial / 2 < (k.factorial / 2) * (k.factorial / 2) := by
  have h4 : (k + 2) * (k + 1) * 2 < k.factorial := by
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ j hj ih =>
      rw [Nat.factorial_succ]
      have h1 : j + 3 < (j + 1) * (j + 1) := by nlinarith
      calc (j + 1 + 2) * (j + 1 + 1) * 2 = (j + 3) * ((j + 2) * 2) := by ring
        _ < ((j + 1) * (j + 1)) * ((j + 2) * 2) := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
        _ = (j + 1) * ((j + 2) * (j + 1) * 2) := by ring
        _ ≤ (j + 1) * j.factorial := Nat.mul_le_mul_left _ ih.le
  have hev : 2 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  obtain ⟨a, ha⟩ := hev
  have h2 : (k + 2).factorial = (k + 2) * (k + 1) * k.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [h2, ha, Nat.mul_div_cancel_left a (by norm_num)]
  have h3 : (k + 2) * (k + 1) * (2 * a) / 2 = (k + 2) * (k + 1) * a := by
    rw [show (k + 2) * (k + 1) * (2 * a) = 2 * ((k + 2) * (k + 1) * a) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  rw [h3]
  have hka : (k + 2) * (k + 1) < a := by
    rw [ha] at h4
    linarith
  have ha0 : 0 < a := by omega
  nlinarith

end CFSG.ComponentClassification.SolMax
