module

import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible
import CFSG.FeitThompson.Representations.InvariantDetectingCharsQuotientDegree
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.CyclicComplementUnlistedInduceIrreducible

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalInduction (conjClassFun conjClassFun_apply)

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L} [K.Normal]
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

theorem le_inertiaGroup_iff_forall (A : Subgroup L) (θ : ↥K → ℂ) :
    A ≤ inertiaGroup K θ ↔ ∀ x ∈ A, ∀ k : ↥K, θ (MulAut.conjNormal x⁻¹ k) = θ k := by
  refine ⟨fun hle x hx k => ?_, fun hall x hx => ?_⟩
  · have h2 := congrFun (mem_inertiaGroup.1 (hle hx)) k
    rwa [conjClassFun_apply] at h2
  · rw [mem_inertiaGroup]
    funext k
    rw [conjClassFun_apply]
    exact hall x hx k

theorem le_inertiaGroup_iff_forall_conj (A : Subgroup L) (θ : ↥K → ℂ) :
    A ≤ inertiaGroup K θ ↔
      ∀ x ∈ A, ∀ k k' : ↥K, (k' : L) = x⁻¹ * (k : L) * x → θ k' = θ k := by
  rw [le_inertiaGroup_iff_forall]
  refine ⟨fun hall x hx k k' hk' => ?_, fun hall x hx k => hall x hx k _ ?_⟩
  · have hcoe : (MulAut.conjNormal x⁻¹ k : ↥K) = k' := by
      refine Subtype.ext ?_
      rw [MulAut.conjNormal_apply, hk']
      group
    rw [← hcoe]
    exact hall x hx k
  · rw [MulAut.conjNormal_apply]
    group

theorem apply_zpow_eq_of_apply_eq {H : Type*} [Group H] {α : MulAut H} {θ : H → ℂ}
    (hθ : ∀ x : H, θ (α x) = θ x) (n : ℤ) (x : H) : θ ((α ^ n) x) = θ x := by
  have hnat : ∀ m : ℕ, ∀ y : H, θ ((α ^ m) y) = θ y := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih => intro y; rw [pow_succ, MulAut.mul_apply, ih, hθ]
  have hinv : ∀ y : H, θ (α⁻¹ y) = θ y := fun y => by
    rw [← hθ (α⁻¹ y), MulAut.apply_inv_self]
  have hnatinv : ∀ m : ℕ, ∀ y : H, θ ((α⁻¹ ^ m) y) = θ y := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih => intro y; rw [pow_succ, MulAut.mul_apply, ih, hinv]
  obtain ⟨m, hm⟩ := n.eq_nat_or_neg
  rcases hm with rfl | rfl
  · rw [zpow_natCast]; exact hnat m x
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact hnatinv m x

namespace IsPrimeCyclicTIHyp

theorem inf_inertiaGroup_eq_bot_of_not_le (hq : (Nat.card ↥W₁).Prime) {θ : ↥K → ℂ}
    (hnot : ¬ W₁ ≤ inertiaGroup K θ) : W₁ ⊓ inertiaGroup K θ = ⊥ := by
  have : Fact (Nat.card ↥W₁).Prime := ⟨hq⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card
    ((W₁ ⊓ inertiaGroup K θ).subgroupOf W₁) with hbot | htop
  · refine le_antisymm (fun x hx => ?_) bot_le
    have hx1 : x ∈ W₁ := (Subgroup.mem_inf.1 hx).1
    have hmem : (⟨x, hx1⟩ : ↥W₁) ∈ (W₁ ⊓ inertiaGroup K θ).subgroupOf W₁ :=
      Subgroup.mem_subgroupOf.2 hx
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (by simpa using congrArg Subtype.val hmem)
  · refine absurd (fun x hx => ?_) hnot
    have hmem : (⟨x, hx⟩ : ↥W₁) ∈ (W₁ ⊓ inertiaGroup K θ).subgroupOf W₁ :=
      htop ▸ Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hmem
    exact (Subgroup.mem_inf.1 hmem).2

theorem inertiaGroup_eq_of_not_le (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hq : (Nat.card ↥W₁).Prime) {θ : ↥K → ℂ} (hθ : θ ∈ classFun ↥K)
    (hnot : ¬ W₁ ≤ inertiaGroup K θ) : inertiaGroup K θ = K := by
  refine le_antisymm (fun g hg => ?_) (le_inertiaGroup K hθ)
  obtain ⟨k, hk, w, hw, rfl⟩ := h.exists_decomp g
  have hkI : k ∈ inertiaGroup K θ := le_inertiaGroup K hθ hk
  have hwI : w ∈ inertiaGroup K θ := by
    have hm := (inertiaGroup K θ).mul_mem ((inertiaGroup K θ).inv_mem hkI) hg
    simpa using hm
  have hw1 : w = 1 := by
    have hmem : w ∈ W₁ ⊓ inertiaGroup K θ := Subgroup.mem_inf.2 ⟨hw, hwI⟩
    rw [inf_inertiaGroup_eq_bot_of_not_le hq hnot] at hmem
    exact Subgroup.mem_bot.1 hmem
  rw [hw1, mul_one]
  exact hk

theorem natCard_invariant_Irr [Finite L] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hq : (Nat.card ↥W₁).Prime) :
    Nat.card {χ : ↑(Irr ↥K) // W₁ ≤ inertiaGroup K (χ : ↥K → ℂ)} = Nat.card ↥W₂ := by
  classical
  obtain ⟨b, hbgen⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top W₁).1 h.isCyclic_left
  have hbW : b ∈ W₁ := hbgen ▸ Subgroup.mem_zpowers b
  have hb1 : b ≠ 1 := by
    intro h0
    rw [h0, Subgroup.zpowers_one_eq_bot] at hbgen
    exact h.left_ne_bot hbgen.symm
  have hcW : b⁻¹ ∈ W₁ := W₁.inv_mem hbW
  have hc1 : b⁻¹ ≠ 1 := by simpa using hb1
  set α : MulAut ↥K := MulAut.conjNormal (b⁻¹ : L) with hα
  have hfixmem : ∀ x : ↥K, α x = x → (x : L) ∈ W₂ := by
    intro x hx
    have hxc : (b⁻¹ : L) * (x : L) * (b⁻¹ : L)⁻¹ = (x : L) := by
      have hv := congrArg Subtype.val hx
      rwa [hα, MulAut.conjNormal_apply] at hv
    have hmem : (x : L) ∈ K ⊓ Subgroup.centralizer {(b⁻¹ : L)} := by
      refine Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hv := congrArg (fun z : L => z * (b⁻¹ : L)) hxc
      simpa [mul_assoc] using hv.symm
    rwa [h.centralizer_eq _ hcW hc1] at hmem
  have hmemfix : ∀ x : ↥K, (x : L) ∈ W₂ → α x = x := by
    intro x hx
    have hmem : (x : L) ∈ K ⊓ Subgroup.centralizer {(b⁻¹ : L)} := by
      rw [h.centralizer_eq _ hcW hc1]; exact hx
    have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hmem).2
    refine Subtype.ext ?_
    rw [hα, MulAut.conjNormal_apply, ← hcomm]
    group
  have hfix : autFixedSubgroup α = W₂.subgroupOf K := by
    ext x
    rw [mem_autFixedSubgroup, Subgroup.mem_subgroupOf]
    exact ⟨hfixmem x, hmemfix x⟩
  have hbq : α ^ (Nat.card ↥W₁) = 1 := by
    have hord : orderOf (b⁻¹ : L) ∣ Nat.card ↥W₁ := Subgroup.orderOf_dvd_natCard W₁ hcW
    have hpow : (b⁻¹ : L) ^ (Nat.card ↥W₁) = 1 := orderOf_dvd_iff_pow_eq_one.1 hord
    rw [hα, ← map_pow, hpow, map_one]
  have hqK : ¬ (Nat.card ↥W₁) ∣ Nat.card ↥K := by
    intro hdvd
    have h1 : Nat.card ↥W₁ ∣ Nat.gcd (Nat.card ↥K) (Nat.card ↥W₁) := Nat.dvd_gcd hdvd dvd_rfl
    rw [h.coprime_natCard] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.1 h1)
  have hcomm : ∀ x y : autFixedSubgroup α, x * y = y * x := by
    intro x y
    have hx : ((x : ↥K) : L) ∈ W₂ := hfixmem _ (mem_autFixedSubgroup.1 x.2)
    have hy : ((y : ↥K) : L) ∈ W₂ := hfixmem _ (mem_autFixedSubgroup.1 y.2)
    refine Subtype.ext (Subtype.ext ?_)
    push_cast
    exact h.commute_of_mem_sup (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_right hy)
  have hcount := natCard_fixed_Irr_eq_natCard_autFixedSubgroup (K := ↥K) (b := α) hq hqK hbq hcomm
  have hiff : ∀ χ : ↑(Irr ↥K), irrAut α χ = χ ↔ W₁ ≤ inertiaGroup K (χ : ↥K → ℂ) := by
    intro χ
    rw [irrAut_eq_self_iff, le_inertiaGroup_iff_forall]
    refine ⟨fun hall x hx k => ?_, fun hall k => hall b hbW k⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hbgen ▸ hx : x ∈ Subgroup.zpowers b)
    have hαn : MulAut.conjNormal ((b ^ n : L)⁻¹) = α ^ n := by
      rw [hα, ← map_zpow]
      exact congrArg _ (by group)
    rw [hαn]
    exact apply_zpow_eq_of_apply_eq hall n k
  rw [← Nat.card_congr (Equiv.subtypeEquivRight hiff), hcount, hfix,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.right_le).toEquiv]

section Fintype

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem le_inertiaGroup_primeTIres (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    W₁ ≤ inertiaGroup K (h.primeTIres σ j) := by
  rw [h.inertiaGroup_primeTIres_eq_top hσ j]; exact le_top

theorem exists_primeTIres_eq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hq : (Nat.card ↥W₁).Prime)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) (hinv : W₁ ≤ inertiaGroup K θ) :
    ∃ j : Irr ↥W₂, θ = h.primeTIres σ j := by
  classical
  have := h.isCyclicTIPair.isMulCommutative_right
  have hfin : Finite ↑(Irr ↥K) := finite_Irr.to_subtype
  set T := {χ : ↑(Irr ↥K) // W₁ ≤ inertiaGroup K (χ : ↥K → ℂ)} with hT
  set F : ↑(Irr ↥W₂) → T := fun j =>
    ⟨⟨h.primeTIres σ j, h.primeTIres_mem_Irr hσ j⟩, h.le_inertiaGroup_primeTIres hσ j⟩ with hF
  have hinj : Function.Injective F := fun j k hjk =>
    h.primeTIres_injective hσ (congrArg (fun t : T => ((t : ↑(Irr ↥K)) : ↥K → ℂ)) hjk)
  have hcards : Nat.card ↑(Irr ↥W₂) = Nat.card T := by
    rw [hT, h.natCard_invariant_Irr hq, card_Irr_eq_card_of_isMulCommutative]
  obtain ⟨j, hj⟩ := ((Nat.bijective_iff_injective_and_card F).2 ⟨hinj, hcards⟩).2 ⟨⟨θ, hθ⟩, hinv⟩
  exact ⟨j, (congrArg (fun t : T => ((t : ↑(Irr ↥K)) : ↥K → ℂ)) hj).symm⟩

theorem existsUnique_primeTIres_eq_of_le_inertiaGroup (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hq : (Nat.card ↥W₁).Prime)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) (hinv : W₁ ≤ inertiaGroup K θ) :
    ∃! j : Irr ↥W₂, θ = h.primeTIres σ j := by
  obtain ⟨j, hj⟩ := h.exists_primeTIres_eq hσ hq hθ hinv
  exact ⟨j, hj, fun k hk => h.primeTIres_injective hσ (hk.symm.trans hj)⟩

theorem le_inertiaGroup_iff_exists_primeTIres_eq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hq : (Nat.card ↥W₁).Prime)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) :
    W₁ ≤ inertiaGroup K θ ↔ ∃ j : Irr ↥W₂, θ = h.primeTIres σ j := by
  refine ⟨h.exists_primeTIres_eq hσ hq hθ, ?_⟩
  rintro ⟨j, rfl⟩
  exact h.le_inertiaGroup_primeTIres hσ j

omit [Fintype ↥(W₁ ⊔ W₂)] in
theorem indClassFun_mem_Irr_of_not_le_inertiaGroup (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hq : (Nat.card ↥W₁).Prime) {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K)
    (hnot : ¬ W₁ ≤ inertiaGroup K θ) : indClassFun K θ ∈ Irr L :=
  indClassFun_mem_Irr_of_inertiaGroup_eq hθ
    (h.inertiaGroup_eq_of_not_le hq (Irr_subset_classFun hθ) hnot)

theorem exists_primeTIres_eq_or_indClassFun_mem_Irr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hq : (Nat.card ↥W₁).Prime)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) :
    (∃! j : Irr ↥W₂, θ = h.primeTIres σ j) ∨ indClassFun K θ ∈ Irr L := by
  by_cases hinv : W₁ ≤ inertiaGroup K θ
  · exact Or.inl (h.existsUnique_primeTIres_eq_of_le_inertiaGroup hσ hq hθ hinv)
  · exact Or.inr (h.indClassFun_mem_Irr_of_not_le_inertiaGroup hq hθ hinv)

omit [K.Normal] in
theorem indClassFun_primeTIres_eq_primeTIrow [Fintype ↑(Irr ↥W₁)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    indClassFun K (h.primeTIres σ j) = h.primeTIrow σ j :=
  h.indClassFun_primeTIres hσ j

omit [K.Normal] in
theorem indClassFun_primeTIres_notMem_Irr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hq : (Nat.card ↥W₁).Prime) (j : Irr ↥W₂) :
    indClassFun K (h.primeTIres σ j) ∉ Irr L := by
  intro hmem
  have h1 := cfInner_self_of_mem_Irr hmem
  rw [h.cfInner_self_indClassFun_primeTIres hσ j] at h1
  have hone : (Nat.card ↥W₁ : ℕ) = 1 := by exact_mod_cast h1
  exact hq.one_lt.ne' hone

omit [K.Normal] in
theorem cfInner_indClassFun_primeTIirr_eq_zero (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K)
    (hne : ∀ j : Irr ↥W₂, θ ≠ h.primeTIres σ j) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    cfInner (indClassFun K θ) (h.primeTIirr σ i j) = 0 := by
  have : Fintype ↥K := Fintype.ofFinite _
  rw [cfInner_indClassFun K θ (Irr_subset_classFun (h.primeTIirr_mem_Irr hσ i j)),
    h.resClassFun_primeTIirr i j]
  exact cfInner_eq_zero_of_mem_Irr hθ (h.primeTIres_mem_Irr hσ j) (hne j)

end Fintype

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
