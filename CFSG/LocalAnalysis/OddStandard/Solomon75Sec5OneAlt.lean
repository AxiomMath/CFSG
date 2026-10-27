module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneJhat
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Cor43Perm

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG
open scoped commutatorElement

open AhatData

variable {n : ℕ} {K : Type} [Group K] [Finite K]


@[expose] noncomputable def actC {C : CoverSetup n K} {α : MulAut K} {σ : Perm (Fin n)}
    (h : C.Induces α σ) : ↥(fixSub α) →* Perm σ.cycleFactorsFinset :=
  (Equiv.Perm.OnCycleFactors.toPermHom σ).comp
    ((C.ρ.comp (fixSub α).subtype).codRestrict (centralizer {σ})
      (fun x => mem_centralizer_singleton_iff.2 (h.ρ_comm_of_mem_fixSub x.2)))

omit [Finite K] in
theorem coe_actC_apply {C : CoverSetup n K} {α : MulAut K} {σ : Perm (Fin n)}
    (h : C.Induces α σ) (x : ↥(fixSub α)) (c : σ.cycleFactorsFinset) :
    ((actC h x c : σ.cycleFactorsFinset) : Perm (Fin n)) =
      C.ρ (x : K) * (c : Perm (Fin n)) * (C.ρ (x : K))⁻¹ := rfl

theorem alt_le_range_actC {C : CoverSetup n K} {α : MulAut K} {σ : Perm (Fin n)}
    (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ} (hk : σ.support.card = 2 * k) :
    alternatingGroup σ.cycleFactorsFinset ≤ (actC h).range := by
  classical
  let S : Set (Perm (Fin n)) := {g | g * σ = σ * g ∧ Odd (orderOf g)}
  have hQA : Subgroup.closure S ≤ alternatingGroup (Fin n) := by
    rw [Subgroup.closure_le]
    rintro g ⟨-, hg⟩
    rw [SetLike.mem_coe, Perm.mem_alternatingGroup]
    have h1 : sign g ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rcases Int.units_eq_one_or (sign g) with h2 | h2
    · exact h2
    · rw [h2, Odd.neg_one_pow hg] at h1
      exact absurd h1 (by decide)
  have hQσ : ∀ q ∈ Subgroup.closure S, q * σ = σ * q := by
    intro q hq
    have : Subgroup.closure S ≤ Subgroup.centralizer {σ} := by
      rw [Subgroup.closure_le]
      rintro g ⟨hg, -⟩
      exact mem_centralizer_singleton_iff.2 hg
    exact mem_centralizer_singleton_iff.1 (this hq)
  have hlift := h.exists_mem_fixSub_of_odd_generated hQA hQσ rfl (fun g hg => hg.2)
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro τ hτ
  have hτ3 : τ.IsThreeCycle := hτ
  have hτr : τ ∈ (Equiv.Perm.OnCycleFactors.toPermHom σ).range := by
    rw [Equiv.Perm.OnCycleFactors.mem_range_toPermHom_iff]
    intro c
    rw [card_support_eq_two_of_mem_cycleFactorsFinset hσ hk (τ c).2,
      card_support_eq_two_of_mem_cycleFactorsFinset hσ hk c.2]
  obtain ⟨g, hg⟩ := hτr
  have hopos : 0 < orderOf (g : Perm (Fin n)) := orderOf_pos _
  obtain ⟨j, u, hu, hou⟩ := Nat.exists_eq_two_pow_mul_odd hopos.ne'
  have hgp : ((g ^ 4 ^ j : ↥(centralizer {σ})) : Perm (Fin n)) ∈ S := by
    refine ⟨mem_centralizer_singleton_iff.1 (g ^ 4 ^ j).2, ?_⟩
    have hdvd : orderOf ((g ^ 4 ^ j : ↥(centralizer {σ})) : Perm (Fin n)) ∣ u := by
      rw [orderOf_dvd_iff_pow_eq_one, Subgroup.coe_pow, ← pow_mul]
      calc (g : Perm (Fin n)) ^ (4 ^ j * u) = ((g : Perm (Fin n)) ^ (2 ^ j * u)) ^ 2 ^ j := by
            rw [← pow_mul]
            congr 1
            have h44 : (4 : ℕ) ^ j = 2 ^ j * 2 ^ j := by
              rw [← mul_pow]
              norm_num
            rw [h44]
            ring
        _ = 1 := by rw [← hou, pow_orderOf_eq_one, one_pow]
    exact hu.of_dvd_nat hdvd
  obtain ⟨x, hx, hxρ⟩ := hlift _ (Subgroup.subset_closure hgp)
  refine ⟨⟨x, hx⟩, ?_⟩
  have h1 : (⟨C.ρ x, mem_centralizer_singleton_iff.2 (h.ρ_comm_of_mem_fixSub hx)⟩ :
      ↥(centralizer {σ})) = g ^ 4 ^ j := Subtype.ext hxρ
  show Equiv.Perm.OnCycleFactors.toPermHom σ _ = τ
  show Equiv.Perm.OnCycleFactors.toPermHom σ
    (⟨C.ρ x, mem_centralizer_singleton_iff.2 (h.ρ_comm_of_mem_fixSub hx)⟩ :
      ↥(centralizer {σ})) = τ
  rw [h1, map_pow, hg]
  have h3 : τ ^ 3 = 1 := by rw [← Equiv.Perm.IsThreeCycle.orderOf hτ3]; exact pow_orderOf_eq_one τ
  have h4 : 4 ^ j % 3 = 1 := by
    rw [Nat.pow_mod]
    simp
  have : 4 ^ j = 3 * (4 ^ j / 3) + 1 := by omega
  rw [this, pow_succ, pow_mul, h3, one_pow, one_mul]

theorem exists_act_alt (hn : 8 ≤ n) (C : CoverSetup n K) {α : MulAut K} {σ : Perm (Fin n)}
    (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ} (hk : σ.support.card = 2 * k) (hk5 : 5 ≤ k) :
    ∃ (Cyc : Type) (_ : Fintype Cyc) (_ : DecidableEq Cyc)
      (π : ↥(Subgroup.closure {x | x ∈ fixSub α ∧ x * x = 1}) →* Perm Cyc),
      Fintype.card Cyc = k ∧ alternatingGroup Cyc ≤ π.range := by
  have hkn : 2 * k ≤ n := by
    have := Finset.card_le_univ σ.support
    simpa [hk] using this
  obtain ⟨g, hg⟩ := exists_conj_stdInv (h := hkn) hσ hk
  set C' : CoverSetup n K := C.conjPerm g with hC'
  have hI : C'.Induces α (stdInv n k hkn) := by
    have := h.conjPerm g
    rwa [hg] at this
  set σ' : Perm (Fin n) := stdInv n k hkn with hσ'
  have hσ'2 : σ' * σ' = 1 := stdInv_mul_self
  have hk' : σ'.support.card = 2 * k := card_support_stdInv
  set J₁ : Subgroup K := Subgroup.closure {x | x ∈ fixSub α ∧ x * x = 1} with hJ₁
  have hJ₁fix : J₁ ≤ fixSub α := (Subgroup.closure_le _).2 fun x hx => hx.1
  refine ⟨↥σ'.cycleFactorsFinset, inferInstance, inferInstance,
    (actC hI).comp (Subgroup.inclusion hJ₁fix), card_cycleFactorsFinset_of_involution hσ'2 hk',
    ?_⟩
  have hπapp : ∀ x : ↥J₁, ∀ c : ↥σ'.cycleFactorsFinset,
      ((actC hI (Subgroup.inclusion hJ₁fix x) c : ↥σ'.cycleFactorsFinset) : Perm (Fin n)) =
        C'.ρ (x : K) * (c : Perm (Fin n)) * (C'.ρ (x : K))⁻¹ := fun x c => rfl
  have hAlt : alternatingGroup σ'.cycleFactorsFinset ≤ (actC hI).range :=
    alt_le_range_actC hI hσ'2 hk'
  have h5 : 5 ≤ Nat.card ↥σ'.cycleFactorsFinset := by
    rw [Nat.card_eq_fintype_card, card_cycleFactorsFinset_of_involution hσ'2 hk']; exact hk5
  by_contra hnot
  set R : Subgroup (Perm ↥σ'.cycleFactorsFinset) :=
    ((actC hI).comp (Subgroup.inclusion hJ₁fix)).range with hR
  have hRT : R ≤ (actC hI).range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion hJ₁fix x, rfl⟩
  have hconjJ : ∀ y ∈ fixSub α, ∀ j ∈ J₁, y * j * y⁻¹ ∈ J₁ := by
    intro y hy j hj
    induction hj using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact mul_mem (mul_mem hy hx.1) (inv_mem hy)
      · have : y * x * y⁻¹ * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
        rw [this, hx.2]; group
    | one => simp
    | mul a b _ _ ha hb =>
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]; exact mul_mem ha hb
    | inv a _ ha =>
      have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem ha
  have hnorm : ∀ r k, r ∈ R → k ∈ (actC hI).range → k * r * k⁻¹ ∈ R := by
    rintro _ _ ⟨j, rfl⟩ ⟨y, rfl⟩
    refine ⟨⟨(y : K) * (j : K) * (y : K)⁻¹, hconjJ _ y.2 _ j.2⟩, ?_⟩
    show actC hI (Subgroup.inclusion hJ₁fix ⟨(y : K) * (j : K) * (y : K)⁻¹, _⟩) =
      actC hI y * actC hI (Subgroup.inclusion hJ₁fix j) * (actC hI y)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hRbot : R = ⊥ :=
    eq_bot_of_normal_of_not_alt_le h5 hAlt hRT ((Subgroup.normal_subgroupOf_iff hRT).2 hnorm) hnot
  have hk4 : 4 ≤ k := by omega
  have hv1 : (swap (0 : Fin 8) 2 * swap 1 3 * swap 4 6 * swap 5 7) ∈ T8 :=
    Subgroup.subset_closure (by simp [T8gens])
  obtain ⟨x, hxfix, hxρ⟩ := exists_lift_T8 hn hkn hk4 C' hI _ hv1
  have hsq : C'.ρ x * C'.ρ x = 1 := by
    rw [hxρ, ← map_mul]
    have : (swap (0 : Fin 8) 2 * swap 1 3 * swap 4 6 * swap 5 7) *
        (swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7) = 1 := by decide
    rw [this, map_one]
  have hx2 : x * x = 1 := (C'.sq_eq_one_iff_dvd hn hsq).2 (by
    rw [hxρ, card_support_lift8]
    decide)
  have hxJ : x ∈ J₁ := Subgroup.subset_closure ⟨hxfix, hx2⟩
  have hπx : ((actC hI).comp (Subgroup.inclusion hJ₁fix)) ⟨x, hxJ⟩ = 1 := by
    have : ((actC hI).comp (Subgroup.inclusion hJ₁fix)) ⟨x, hxJ⟩ ∈ R := ⟨⟨x, hxJ⟩, rfl⟩
    rw [hRbot] at this
    exact Subgroup.mem_bot.1 this
  set a : Fin n := Fin.castLE hn (0 : Fin 8) with ha
  set b : Fin n := Fin.castLE hn (1 : Fin 8) with hb
  have hinj := Fin.castLE_injective hn
  have hab : a ≠ b := fun e => absurd (hinj e) (by decide)
  have hc' : swap a b ∈ σ'.cycleFactorsFinset := by
    rw [Equiv.Perm.mem_cycleFactorsFinset_iff]
    refine ⟨isCycle_swap hab, fun y hy => ?_⟩
    rw [Equiv.Perm.support_swap hab] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · rw [swap_apply_left]
      exact (stdInv_castLE hn hkn hk4 (a := (0 : Fin 8)) (b := 1) (by decide) (by decide)).symm
    · rw [swap_apply_right]
      exact (stdInv_castLE hn hkn hk4 (a := (1 : Fin 8)) (b := 0) (by decide) (by decide)).symm
  have h1 := congrArg (fun w : Perm ↥σ'.cycleFactorsFinset =>
    ((w ⟨swap a b, hc'⟩ : ↥σ'.cycleFactorsFinset) : Perm (Fin n))) hπx
  simp only [MonoidHom.comp_apply, Perm.one_apply] at h1
  rw [coe_actC_apply] at h1
  have h1' : C'.ρ x * swap a b * (C'.ρ x)⁻¹ = swap a b := h1
  rw [hxρ] at h1'
  have hinv : (lift8 hn (swap (0 : Fin 8) 2 * swap 1 3 * swap 4 6 * swap 5 7))⁻¹ =
      lift8 hn (swap (0 : Fin 8) 2 * swap 1 3 * swap 4 6 * swap 5 7) := by
    rw [← map_inv]
    congr 1
    exact inv_eq_of_mul_eq_one_right (by decide)
  rw [hinv] at h1'
  have h2 := congrArg (fun w : Perm (Fin n) => w a) h1'
  have e0 : lift8 hn (swap (0 : Fin 8) 2 * swap 1 3 * swap 4 6 * swap 5 7) a =
      Fin.castLE hn (2 : Fin 8) := by
    rw [ha, lift8_apply_castLE]; congr 1
  have e2 : lift8 hn (swap (0 : Fin 8) 2 * swap 1 3 * swap 4 6 * swap 5 7)
      (Fin.castLE hn (2 : Fin 8)) = a := by
    rw [ha, lift8_apply_castLE]; congr 1
  have hn2a : Fin.castLE hn (2 : Fin 8) ≠ a := fun e => absurd (hinj e) (by decide)
  have hn2b : Fin.castLE hn (2 : Fin 8) ≠ b := fun e => absurd (hinj e) (by decide)
  simp only [Perm.mul_apply] at h2
  rw [e0, swap_apply_of_ne_of_ne hn2a hn2b, e2, swap_apply_left] at h2
  exact hab h2

end CFSG.OddStandard.Solomon75
