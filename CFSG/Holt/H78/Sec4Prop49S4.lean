module

public import CFSG.Holt.H78.Sec4Prop49End
import CFSG.Holt.H78.Sec4Prop49S6L71

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open Equiv
open scoped Pointwise

section HypSE


@[expose] def SEFieldFixBound : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (M : Subgroup (Perm Ψ)), IsNaturalSE M →
    ∀ {a b : Ψ}, a ≠ b → ∀ x ∈ Subgroup.normalizer (M : Set (Perm Ψ)), x a = a → x b = b →
      (∃ δ ∈ holtDelta M Ψ a b, x δ ≠ δ) →
        ((holtDelta M Ψ a b ∩ {δ | x δ = δ}).ncard + 1) ^ 2 ≤ (holtDelta M Ψ a b).ncard + 1

@[expose] def SEChainUnitary : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (M : Subgroup (Perm Ψ)) (n e : ℕ),
    IsBenderAction M Ψ n 3 e → ∀ {a b : Ψ}, a ≠ b → holtDelta M Ψ a b ⊆ holtDelta' M Ψ a b

end HypSE

section Helpers

private theorem isSolvable_range_of_isSolvable_inducedPerm {G Ω : Type*} [Group G]
    [MulAction G Ω] {K : Subgroup G} {Λ : Set Ω} (hK : K ≤ stabilizer G Λ)
    (hsol : Group.IsSolvable (inducedPerm K Λ hK)) {N : Type*} [Group N] (ψ : K →* N)
    (hψ : ∀ k : K, (∀ δ ∈ Λ, (k : G) • δ = δ) → ψ k = 1) : Group.IsSolvable ψ.range := by
  set f := inducedHom K Λ hK with hf
  have hker : f.ker ≤ ψ.rangeRestrict.ker := fun k hk => by
    rw [MonoidHom.mem_ker, ← Subtype.coe_inj, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one]
    exact hψ k fun δ hδ => (mem_fixingSubgroup_iff G).mp (inducedHom_eq_one_iff.mp hk) δ hδ
  set φ : K ⧸ f.ker →* ψ.range := QuotientGroup.lift f.ker ψ.rangeRestrict hker
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨k, hk⟩ := ψ.rangeRestrict_surjective x
    exact ⟨QuotientGroup.mk k, hk⟩
  have : Group.IsSolvable f.range := hsol
  have e := QuotientGroup.quotientKerEquivRange f
  have : Group.IsSolvable (K ⧸ f.ker) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.isSolvable_of_surjective hφ

end Helpers

section Tool

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

@[expose] def twoPointJHom (hG : IsStarGroup G Ω) (α β : Ω) :
    Subgroup.closure (longInvSwap G Ω α β) →*
      jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) where
  toFun w := ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β w.2),
    twoPointElt_mem_jHull hG w.2⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (twoPointHom G Ω α β)))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul (twoPointHom G Ω α β)
    ⟨x, closure_longInvSwap_le_stabilizer_pair α β x.2⟩
    ⟨y, closure_longInvSwap_le_stabilizer_pair α β y.2⟩))

omit [DecidableEq Ω] in
@[simp] theorem coe_twoPointJHom_apply (hG : IsStarGroup G Ω) {α β : Ω}
    (w : Subgroup.closure (longInvSwap G Ω α β)) (δ : holtDelta G Ω α β) :
    ((((twoPointJHom hG α β w : twoPointSection G Ω α β) : Perm (holtDelta G Ω α β)) δ :
      holtDelta G Ω α β) : Ω) = (w : G) • (δ : Ω) := rfl

omit [DecidableEq Ω] in
theorem HoltData.rho_twoPointJHom_coord (hG : IsStarGroup G Ω) {α β : Ω}
    (D' : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) (k : D'.ι)
    (w : Subgroup.closure (longInvSwap G Ω α β)) (δ : holtDelta G Ω α β) :
    D'.ρ k (twoPointJHom hG α β w) (D'.coord δ k) =
      D'.coord ((twoPointJHom hG α β w : twoPointSection G Ω α β) • δ) k :=
  (D'.coord_smul _ δ k).symm

end Tool

section ToolL

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.false_of_isTypeL_of_realize (hS : Sec4Setting G Ω)
    (hL48 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      ∀ (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i : D.ι),
        IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i)))
    {α β γ : Ω} (hαβ : α ≠ β) {s : G} (hs : IsTypeL G Ω γ s) (hsα : s • α = α)
    (hsβ : s • β = β) (D' : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) (k : D'.ι)
    (h5 : 5 ≤ Fintype.card (D'.Ψc k)) {Λ : Set Ω}
    (hΛ : Λ ⊆ holtDelta G Ω α β ∩ fixSet Ω (Subgroup.zpowers s))
    (honto : ∀ p : D'.Ψc k, ∃ δ : holtDelta G Ω α β, (δ : Ω) ∈ Λ ∧ D'.coord δ k = p)
    (hreal : ∀ e ∈ longInv (Perm (D'.Ψc k)) (D'.Ψc k),
      ∃ y : Subgroup.closure (longInvSwap G Ω α β), (y : G) ∈ longInvSwap G Ω α β ∧
        (y : G) ∈ stabilizer G Λ ∧ D'.ρ k (twoPointJHom hS.star α β y) = e) :
    False := by
  classical
  set X := Subgroup.closure (longInvSwap G Ω α β ∩
    (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup G) : Set G) : Set G)) with hX
  have hXle : X ≤ Subgroup.closure (longInvSwap G Ω α β) :=
    Subgroup.closure_mono Set.inter_subset_left
  set ψ : X →* Perm (D'.Ψc k) :=
    (D'.ρ k).comp ((twoPointJHom hS.star α β).comp (Subgroup.inclusion hXle)) with hψ
  have key : ∀ (w w' : Subgroup.closure (longInvSwap G Ω α β)) (δ : holtDelta G Ω α β),
      (w : G) • (δ : Ω) = (w' : G) • (δ : Ω) →
        D'.ρ k (twoPointJHom hS.star α β w) (D'.coord δ k) =
          D'.ρ k (twoPointJHom hS.star α β w') (D'.coord δ k) := fun w w' δ h => by
    rw [D'.rho_twoPointJHom_coord, D'.rho_twoPointJHom_coord]
    exact congrArg (fun ε => D'.coord ε k) (Subtype.ext ((coe_twoPointJHom_apply _ _ _).trans
      (h.trans (coe_twoPointJHom_apply _ _ _).symm)))
  have hsol : Group.IsSolvable ψ.range := by
    refine isSolvable_range_of_isSolvable_inducedPerm _
      (hS.isSolvable_jSection_of_isTypeL hL48 hs hsα hsβ) ψ fun x hx => ?_
    refine Equiv.ext fun p => ?_
    obtain ⟨δ, hδΛ, rfl⟩ := honto p
    exact key (Subgroup.inclusion hXle x) 1 δ ((hx δ (hΛ hδΛ)).trans (one_smul G _).symm) |>.trans
      (by rw [map_one, map_one])
  have hne : Nonempty (D'.Ψc k) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨δ₀, hδ₀, -⟩ := honto (Classical.arbitrary _)
  have hV : IsPGroup 2 (Subgroup.zpowers s) :=
    isPGroup_zpowers_of_orderOf_eq_two hs.orderOf_eq_two
  have hVαβ : Subgroup.zpowers s ≤ stabilizer G α ⊓ stabilizer G β :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
      ⟨mem_stabilizer_iff.mpr hsα, mem_stabilizer_iff.mpr hsβ⟩)
  have hsub : longInv (Perm (D'.Ψc k)) (D'.Ψc k) ⊆ ψ.range := by
    intro e he
    obtain ⟨y, hy, hyΛ, hye⟩ := hreal e he
    obtain ⟨c, hc, hcV, hcΛ⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn hαβ hV hVαβ
      ⟨_, hδ₀⟩ (fun δ hδ => (hΛ hδ).2) hy hyΛ
    refine ⟨⟨c, Subgroup.subset_closure ⟨hc, hcV⟩⟩, Equiv.ext fun p => ?_⟩
    obtain ⟨δ, hδΛ, rfl⟩ := honto p
    rw [← hye]
    exact key ⟨c, hXle (Subgroup.subset_closure ⟨hc, hcV⟩)⟩ y δ (hcΛ δ hδΛ)
  exact not_isSolvable_of_longInv_perm_subset (D'.odd_card_Ψc k) h5 hsub hsol

end ToolL

section K3

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G}

structure P49K3 (hS : Sec4Setting G Ω) (C : P49Config G Ω α v) where
  D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)
  j₀ : D'.ι
  alt : D'.M j₀ = alternatingGroup (D'.Ψc j₀)
  card_eq : Fintype.card (D'.Ψc j₀) = 7
  fix_three :
    (Finset.univ.filter fun ψ => D'.ρ j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card = 3
  fix_one : ∀ j, j ≠ j₀ →
    (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card = 1
  se : ∀ j, j ≠ j₀ → IsNaturalSE (D'.M j)

private theorem exists_eq_three_of_prod_eq_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (h : ∏ j, f j = 3) : ∃ j₀, f j₀ = 3 ∧ ∀ j, j ≠ j₀ → f j = 1 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, f j₀ ≠ 1 := by
    by_contra hno
    have hno' : ∀ j, f j = 1 := fun j => by
      by_contra hj
      exact hno ⟨j, hj⟩
    rw [Finset.prod_eq_one fun j _ => hno' j] at h
    omega
  have hdvd : f j₀ ∣ 3 := h ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ j₀)
  have h3 : f j₀ = 3 := ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hj₀
  refine ⟨j₀, h3, fun j hj => ?_⟩
  have hsub : f j₀ * f j ∣ 3 := by
    rw [← Finset.prod_pair (Ne.symm hj), ← h]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
  rw [h3] at hsub
  have hsub' : 3 * f j ∣ 3 * 1 := by rwa [mul_one]
  exact Nat.eq_one_of_dvd_one (Nat.dvd_of_mul_dvd_mul_left (k := 3) (by norm_num) hsub')

theorem P49Config.nonempty_p49K3 (hS : Sec4Setting G Ω) (h96 : P49Step96 G Ω)
    (C : P49Config G Ω α v)
    (h3 : ∃ γ₁ γ₂ γ₃ : holtDelta G Ω α C.β,
      (γ₁ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧ (γ₂ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
      (γ₃ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
      γ₂ ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₁ ∧
      γ₃ ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₁ ∧
      γ₃ ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₂ ∧
      ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
        δ ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₁ ∨
        δ ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₂ ∨
        δ ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₃) :
    Nonempty (P49K3 hS C) := by
  classical
  obtain ⟨γ₁, γ₂, γ₃, h1, h2, h3', h12, h13, h23, hcov⟩ := h3
  obtain ⟨D'⟩ := hS.holtData_twoPoint (C.three_le_card_holtDelta hS)
  set F : ∀ j, Finset (D'.Ψc j) := fun j =>
    Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ with hF
  have hmemF : ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      D'.coord δ ∈ Fintype.piFinset F := fun δ hδ =>
    Fintype.mem_piFinset.mpr fun j =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (C.mem_fixSet_iff_rho hS D' δ).mp hδ j⟩
  have hpi : Fintype.piFinset F = {D'.coord γ₁, D'.coord γ₂, D'.coord γ₃} := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨δ, rfl⟩ := D'.coord_surjective x
      have hδ : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) :=
        (C.mem_fixSet_iff_rho hS D' δ).mpr fun j =>
          (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hx j)).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hcov δ hδ with h | h | h
      · exact Or.inl ((D'.coord_eq_iff _ _).mpr h).symm
      · exact Or.inr (Or.inl ((D'.coord_eq_iff _ _).mpr h).symm)
      · exact Or.inr (Or.inr ((D'.coord_eq_iff _ _).mpr h).symm)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      exacts [hmemF _ h1, hmemF _ h2, hmemF _ h3']
  have hd : ∀ {ε ε' : holtDelta G Ω α C.β},
      ε' ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) ε →
        D'.coord ε ≠ D'.coord ε' := fun h he => h ((D'.coord_eq_iff _ _).mp he)
  have hprod : ∏ j, (F j).card = 3 := by
    rw [← Fintype.card_piFinset, hpi, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hd h12, hd h13⟩), Finset.card_pair (hd h23)]
  obtain ⟨j₀, hj₀, hj⟩ := exists_eq_three_of_prod_eq_three (fun j => (F j).card) hprod
  obtain ⟨hSE, hmod, -, -⟩ := C.prop_2_3 D' hS
  have hfac : ∀ j, (F j).card ≠ 1 → D'.M j = alternatingGroup (D'.Ψc j) ∧
      7 ≤ Fintype.card (D'.Ψc j) := fun j hj1 => by
    rcases D'.factor j with hA | hA
    · exact hA
    · exact absurd (hSE j hA) hj1
  obtain ⟨hA, h7⟩ := hfac j₀ (by rw [hj₀]; omega)
  have hm₀ := hmod j₀
  have hle : Fintype.card (D'.Ψc j₀) < 9 := by
    by_contra h9
    exact h96 C.ne D' j₀ hA (by omega)
  refine ⟨⟨D', j₀, hA, ?_, hj₀, hj, fun j hj' => ?_⟩⟩
  · change (F j₀).card % 4 = _ at hm₀
    rw [hj₀] at hm₀
    omega
  · rcases D'.factor j with ⟨hA', h7'⟩ | hse
    · have hmj := hmod j
      change (F j).card % 4 = _ at hmj
      rw [hj j hj'] at hmj
      exact (h96 C.ne D' j hA' (by omega)).elim
    · exact hse

end K3

section Real

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem HoltData.mem_range_rho_of_alternating {K X : Type*} [Group K] [Finite K]
    [MulAction K X] (D : HoltData K X) {k : D.ι} (hk : D.M k = alternatingGroup (D.Ψc k))
    {e : Perm (D.Ψc k)} (he : e ∈ longInv (Perm (D.Ψc k)) (D.Ψc k)) : e ∈ (D.ρ k).range := by
  rw [D.range_rho]
  have ht := D.rho_mem_longInv D.t_mem k
  have hs : e * (D.ρ k D.tHull)⁻¹ ∈ D.M k := by
    rw [hk, Equiv.Perm.mem_alternatingGroup, map_mul, map_inv,
      sign_eq_of_mem_longInv_perm he ht, mul_inv_cancel]
  have he' : e = e * (D.ρ k D.tHull)⁻¹ * D.ρ k D.tHull := by group
  rw [he']
  exact mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

omit [FaithfulSMul G Ω] in
theorem Sec4Setting.exists_mem_longInvSwap_rho_eq_of_twoPoint (hS : Sec4Setting G Ω)
    {α β : Ω} (hαβ : α ≠ β) (h3 : 3 ≤ Nat.card (holtDelta G Ω α β))
    (D' : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) (Y : ∀ j, Perm (D'.Ψc j))
    (hY : ∀ j, Y j ∈ (D'.ρ j).range ∧ Y j ∈ longInv (Perm (D'.Ψc j)) (D'.Ψc j)) :
    ∃ c : Subgroup.closure (longInvSwap G Ω α β), (c : G) ∈ longInvSwap G Ω α β ∧
      ∀ j, D'.ρ j (twoPointJHom hS.star α β c) = Y j := by
  obtain ⟨u, hu, hρ⟩ := (D'.exists_mem_longInv_rho_eq_iff Y).mpr hY
  obtain ⟨c, hc, hcu⟩ := (hS.mem_longInv_twoPointSection_iff hαβ h3 u).mp hu
  refine ⟨⟨c, Subgroup.subset_closure hc⟩, hc, fun j => ?_⟩
  have hu' : twoPointJHom hS.star α β ⟨c, Subgroup.subset_closure hc⟩ = u :=
    Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (hcu δ).symm))
  rw [hu', hρ j]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mul_pow_odd_eq_conj {X : Type*} [Group X] {x z : X} (hx : x * x = 1) (hz : z * z = 1)
    (j : ℕ) : x * (x * z) ^ (2 * j + 1) = ((x * z) ^ j)⁻¹ * z * (x * z) ^ j := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h1 : x * (x * z) * x⁻¹ = (x * z)⁻¹ := by
    rw [mul_inv_rev, hxinv, hzinv, ← mul_assoc, hx, one_mul]
  have hn : x * (x * z) ^ j = ((x * z) ^ j)⁻¹ * x := by
    have h2 : x * (x * z) ^ j * x⁻¹ = ((x * z) ^ j)⁻¹ := by
      rw [← conj_pow, h1, inv_pow]
    calc x * (x * z) ^ j = x * (x * z) ^ j * x⁻¹ * x := by group
      _ = ((x * z) ^ j)⁻¹ * x := by rw [h2]
  have hpow : (x * z) ^ (2 * j + 1) = (x * z) ^ j * ((x * z) * (x * z) ^ j) := by
    rw [← pow_succ', ← pow_add, show j + (j + 1) = 2 * j + 1 by ring]
  rw [hpow, ← mul_assoc, hn, mul_assoc ((x * z) ^ j)⁻¹ x, ← mul_assoc x (x * z),
    ← mul_assoc x x z, hx, one_mul, mul_assoc]

end Real

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {hS : Sec4Setting G Ω} {C : P49Config G Ω α v}

theorem P49K3.false_of_isTypeL_of_mem_twoPointKernel (K : P49K3 hS C)
    (hL48 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      ∀ (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i : D.ι),
        IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i)))
    {p : Ω} {z : G} (hz : IsTypeL G Ω p z) (hzK : z ∈ twoPointKernel G Ω α C.β) : False := by
  classical
  have hzαβ := Subgroup.mem_inf.mp (twoPointKernel_le_inf hzK)
  have hzΔ := (mem_fixingSubgroup_iff G).mp (twoPointKernel_le_fixingSubgroup hzK)
  have h3 := C.three_le_card_holtDelta hS
  refine hS.false_of_isTypeL_of_realize hL48 C.ne hz (mem_stabilizer_iff.mp hzαβ.1)
    (mem_stabilizer_iff.mp hzαβ.2) K.D' K.j₀ (by rw [K.card_eq]; norm_num)
    (Λ := holtDelta G Ω α C.β) (fun δ hδ => ⟨hδ, mem_fixSet_zpowers_iff.mpr (hzΔ δ hδ)⟩)
    (fun p => ?_) (fun e he => ?_)
  · obtain ⟨ω, hω⟩ := K.D'.exists_coord_apply_eq K.j₀ p
    exact ⟨ω, ω.2, hω⟩
  · obtain ⟨c, hc, hρ⟩ := hS.exists_mem_longInvSwap_rho_eq_of_twoPoint C.ne h3 K.D'
      (Function.update (fun j => K.D'.ρ j K.D'.tHull) K.j₀ e) fun j => by
        rcases eq_or_ne j K.j₀ with rfl | hj
        · rw [Function.update_self]
          exact ⟨K.D'.mem_range_rho_of_alternating K.alt he, he⟩
        · rw [Function.update_of_ne hj]
          exact ⟨⟨_, rfl⟩, K.D'.rho_mem_longInv K.D'.t_mem j⟩
    exact ⟨c, hc, closure_longInvSwap_le_stabilizer α C.β c.2, by
      rw [hρ, Function.update_self]⟩

theorem P49K3.exists_commute_lift (K : P49K3 hS C)
    (hL48 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      ∀ (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i : D.ι),
        IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i)))
    {x y : twoPointSection G Ω α C.β}
    (hx : x ∈ longInv (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
    (hy : y ∈ longInv (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) (hxy : x * y = y * x) :
    ∃ c ∈ longInvSwap G Ω α C.β, ∃ c' ∈ longInvSwap G Ω α C.β, c * c' = c' * c ∧
      (∀ δ : holtDelta G Ω α C.β, ((x : Perm (holtDelta G Ω α C.β)) δ : Ω) = c • (δ : Ω)) ∧
      ∀ δ : holtDelta G Ω α C.β, ((y : Perm (holtDelta G Ω α C.β)) δ : Ω) = c' • (δ : Ω) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := C.three_le_card_holtDelta hS
  obtain ⟨T, -, hT⟩ := exists_fusionIsSylowIn_ge (p := 2) (IsPGroup.of_bot (G := G))
    (bot_le (a := twoPointKernel G Ω α C.β))
  have hTK : T ≤ twoPointKernel G Ω α C.β := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  have hTαβ : T ≤ stabilizer G α ⊓ stabilizer G C.β := hTK.trans twoPointKernel_le_inf
  have hTΔ : holtDelta G Ω α C.β ⊆ fixSet Ω T := fun δ hδ t ht =>
    (mem_fixingSubgroup_iff G).mp (twoPointKernel_le_fixingSubgroup (hTK ht)) δ hδ
  obtain ⟨δ₀, -, hδ₀, -, -⟩ := C.exists_mem_holtDelta_ne hS
  have hlift : ∀ {u : twoPointSection G Ω α C.β},
      u ∈ longInv (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) →
      ∃ c ∈ longInvSwap G Ω α C.β, c ∈ Subgroup.centralizer (T : Set G) ∧
        ∀ δ : holtDelta G Ω α C.β, ((u : Perm (holtDelta G Ω α C.β)) δ : Ω) = c • (δ : Ω) := by
    intro u hu
    obtain ⟨c₀, hc₀, hc₀u⟩ := (hS.mem_longInv_twoPointSection_iff C.ne h3 u).mp hu
    obtain ⟨c, hc, hcT, hcΔ⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn C.ne hT2 hTαβ
      ⟨_, hδ₀⟩ hTΔ hc₀ (closure_longInvSwap_le_stabilizer α C.β (Subgroup.subset_closure hc₀))
    exact ⟨c, hc, hcT, fun δ => (hc₀u δ).trans (hcΔ δ δ.2).symm⟩
  obtain ⟨c, hc, hcT, hcx⟩ := hlift hx
  obtain ⟨c₁, hc₁, hc₁T, hc₁y⟩ := hlift hy
  have hcc : c * c = 1 := mul_self_eq_one_of_mem_longInv hc.1
  have hc₁c₁ : c₁ * c₁ = 1 := mul_self_eq_one_of_mem_longInv hc₁.1
  have hxx : x * x = 1 := mul_self_eq_one_of_mem_longInv hx
  have hyy : y * y = 1 := mul_self_eq_one_of_mem_longInv hy
  set ρ := c * c₁ with hρ
  have hρα : ρ ∈ stabilizer G α := mem_stabilizer_iff.mpr (by
    rw [hρ, mul_smul, hc₁.2, smul_eq_of_mem_longInvSwap hc])
  have hρβ : ρ ∈ stabilizer G C.β := mem_stabilizer_iff.mpr (by
    rw [hρ, mul_smul, smul_eq_of_mem_longInvSwap hc₁, hc.2])
  have hρT : ρ ∈ Subgroup.centralizer (T : Set G) := mul_mem hcT hc₁T
  have hρΔ : ∀ (n : ℕ) (δ : holtDelta G Ω α C.β),
      ρ ^ n • (δ : Ω) = ((((x * y) ^ n : twoPointSection G Ω α C.β) :
        Perm (holtDelta G Ω α C.β)) δ : Ω) := fun n => by
    induction n with
    | zero => intro δ; simp
    | succ n ih =>
      intro δ
      rw [pow_succ', mul_smul, ih, pow_succ', Subgroup.coe_mul, Perm.mul_apply, Subgroup.coe_mul,
        Perm.mul_apply, hρ, mul_smul, ← hc₁y, ← hcx]
  have hxy2 : (x * y) ^ 2 = 1 := by
    have h : x * y * (x * y) = x * x * (y * y) := by
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = x * x * (y * y) := by group
    rw [sq, h, hxx, hyy, one_mul]
  have hρ2K : ρ ^ 2 ∈ twoPointKernel G Ω α C.β := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨pow_mem hρα 2, pow_mem hρβ 2⟩, ?_⟩
    refine (mem_fixingSubgroup_iff G).mpr fun δ hδ => ?_
    rw [hρΔ 2 ⟨δ, hδ⟩, hxy2]
    rfl
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (ρ ^ 2)).ne'
  set z := (ρ ^ 2) ^ m with hz
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) := by
    have hzpow : z ^ (2 ^ a) = 1 := by
      rw [hz, ← pow_mul, mul_comm, ← hN, pow_orderOf_eq_one]
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hzpow)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hb])
  have hzK : z ∈ twoPointKernel G Ω α C.β := pow_mem hρ2K m
  have hzC : z ∈ Subgroup.centralizer (T : Set G) := pow_mem (pow_mem hρT 2) m
  have hzT : z ∈ T := by
    have hle : Subgroup.zpowers z ≤ Subgroup.normalizer (T : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hzC)
    have hP := hT.2.2 (T ⊔ Subgroup.zpowers z) (sup_le hTK (Subgroup.zpowers_le.mpr hzK))
      (IsPGroup.to_sup_of_normal_left' hT2 hz2 hle) le_sup_left
    rw [← hP]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  obtain ⟨j, rfl⟩ := hm
  set c' := c * ρ ^ (2 * j + 1) with hc'
  have hc'conj : c' = (ρ ^ j)⁻¹ * c₁ * ρ ^ j := mul_pow_odd_eq_conj hcc hc₁c₁ j
  have hc'J : c' ∈ longInv G Ω := by
    rw [hc'conj]
    simpa using conj_mem_longInv hc₁.1 (ρ ^ j)⁻¹
  have hc'α : c' • α = C.β := by
    rw [hc', mul_smul, mem_stabilizer_iff.mp (pow_mem hρα _), hc.2]
  have hxyodd : (x * y) ^ (2 * j + 1) = x * y := by
    rw [pow_succ, pow_mul, hxy2, one_pow, one_mul]
  have hc'y : ∀ δ : holtDelta G Ω α C.β,
      ((y : Perm (holtDelta G Ω α C.β)) δ : Ω) = c' • (δ : Ω) := fun δ => by
    have hxxy : (x : Perm (holtDelta G Ω α C.β))
        (((x * y : twoPointSection G Ω α C.β) : Perm (holtDelta G Ω α C.β)) δ) =
          (y : Perm (holtDelta G Ω α C.β)) δ := by
      rw [Subgroup.coe_mul, Perm.mul_apply, ← Perm.mul_apply, ← Subgroup.coe_mul, hxx]
      rfl
    rw [hc', mul_smul, hρΔ, hxyodd, ← hcx, hxxy]
  have hc'c' : c' * c' = 1 := mul_self_eq_one_of_mem_longInv hc'J
  have hcc' : c * c' = ρ ^ (2 * j + 1) := by rw [hc', ← mul_assoc, hcc, one_mul]
  have hzeq : (c * c') ^ 2 = z := by rw [hcc', hz, ← pow_mul, ← pow_mul, mul_comm]
  have hinv : c * ρ * c⁻¹ = ρ⁻¹ := by
    rw [hρ, mul_inv_rev, inv_eq_of_mul_eq_one_right hcc, inv_eq_of_mul_eq_one_right hc₁c₁,
      ← mul_assoc, hcc, one_mul]
  have hzinv : c * z * c⁻¹ = z⁻¹ := by
    rw [hz, ← conj_pow, ← conj_pow, hinv, inv_pow, inv_pow]
  have hzc : c * z * c⁻¹ = z := by
    rw [← Subgroup.mem_centralizer_iff.mp hcT z hzT, mul_inv_cancel_right]
  have hzz : z = z⁻¹ := hzc.symm.trans hzinv
  have hc'inv : c' * c = (c * c')⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hc'c', inv_eq_of_mul_eq_one_right hcc]
  by_cases hz1 : z = 1
  · refine ⟨c, hc, c', ⟨hc'J, hc'α⟩, ?_, hcx, hc'y⟩
    have h1 : c * c' * (c * c') = 1 := by rw [← sq, hzeq, hz1]
    rw [hc'inv]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  · exfalso
    set x' := c' * c * c'⁻¹ with hx'
    have hx'J : x' ∈ longInv G Ω := conj_mem_longInv hc.1 c'
    have hcx' : c * x' = z := by
      rw [hx', inv_eq_of_mul_eq_one_right hc'c', ← hzeq, sq]
      group
    have hx'c : x' * c = z := by
      rw [hx', inv_eq_of_mul_eq_one_right hc'c',
        show c' * c * c' * c = (c' * c) * (c' * c) by group, hc'inv, ← mul_inv_rev, ← sq,
        hzeq, ← hzz]
    obtain ⟨p₀, hp₀, -⟩ := hc.1.2
    have hcp : c ∈ longInvAt G Ω p₀ := ⟨hc.1, hp₀⟩
    have hcomm : Commute c x' := hcx'.trans hx'c.symm
    have hx'p : x' ∈ longInvAt G Ω p₀ := ⟨hx'J, by
      have h : c • (x' • p₀) = x' • p₀ := by rw [← mul_smul, hcomm.eq, mul_smul, hp₀]
      exact hc.1.2.unique h hp₀⟩
    have hzαβ := Subgroup.mem_inf.mp (hTαβ hzT)
    have hzJ : z ∉ longInv G Ω := fun h =>
      C.ne (h.2.unique (mem_stabilizer_iff.mp hzαβ.1) (mem_stabilizer_iff.mp hzαβ.2))
    have hne : c ≠ x' := fun h => hz1 (by rw [← hcx', ← h, hcc])
    exact K.false_of_isTypeL_of_mem_twoPointKernel hL48 ⟨c, hcp, x', hx'p, hne, hcomm, hcx', hzJ⟩
      hzK

end Lift

end CFSG.Holt.H78
