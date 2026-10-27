module

public import CFSG.FeitThompson.Representations.FrobeniusKernelInductionIrreducible
public import CFSG.FeitThompson.Representations.LinearIrreduciblesKillDerived
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.FrattiniQuotientAutomorphismKernelPGroup
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Representations.ComplementActsFreelyKernelCharacters
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open SemidirectProduct
open NormalInduction (conjClassFun)

variable {K E : Type*} [Group K] [Group E] {φ : E →* MulAut K}

theorem isInvariantSubgroup_commutator (φ : E →* MulAut K) :
    IsInvariantSubgroup φ (commutator K) :=
  isInvariantSubgroup_of_characteristic φ (commutator K)

noncomputable def derivedQuotAut (φ : E →* MulAut K) : E →* MulAut (K ⧸ commutator K) :=
  (isInvariantSubgroup_commutator φ).quotientAut

@[simp] theorem derivedQuotAut_mk (u : E) (k : K) :
    derivedQuotAut φ u (QuotientGroup.mk k) = (QuotientGroup.mk (φ u k) : K ⧸ commutator K) :=
  (isInvariantSubgroup_commutator φ).quotientAut_mk u k

theorem inr_mul_inl (u : E) (k : K) :
    (inr u : K ⋊[φ] E) * inl k = inl (φ u k) * inr u := by
  rw [inl_aut, map_inv]
  group

theorem mem_centralizer_inr_iff (u : E) (k : K) :
    (inl k : K ⋊[φ] E) ∈ Subgroup.centralizer {(inr u : K ⋊[φ] E)} ↔ φ u k = k := by
  rw [Subgroup.mem_centralizer_singleton_iff, inr_mul_inl]
  exact ⟨fun h => (inl_injective (mul_right_cancel h)).symm, fun h => by rw [h]⟩

theorem mem_map_inl_commutator_iff {x : K ⋊[φ] E} :
    x ∈ (commutator K).map (inl : K →* K ⋊[φ] E) ↔ x.left ∈ commutator K ∧ x.right = 1 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨hk, by simp⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x.left, h1, SemidirectProduct.ext (by simp) (by simp [h2])⟩

theorem centralizer_inr_le_map_inl_commutator_iff (u : E) :
    Subgroup.centralizer {(inr u : K ⋊[φ] E)} ⊓ (inl : K →* K ⋊[φ] E).range
        ≤ (commutator K).map (inl : K →* K ⋊[φ] E) ↔
      ∀ k : K, φ u k = k → k ∈ commutator K := by
  constructor
  · intro h k hk
    have hx : (inl k : K ⋊[φ] E) ∈ Subgroup.centralizer {(inr u : K ⋊[φ] E)} ⊓
        (inl : K →* K ⋊[φ] E).range := ⟨(mem_centralizer_inr_iff u k).2 hk, ⟨k, rfl⟩⟩
    simpa using (mem_map_inl_commutator_iff.1 (h hx)).1
  · rintro h x ⟨hc, k, rfl⟩
    exact Subgroup.mem_map_of_mem _ (h k ((mem_centralizer_inr_iff u k).1 hc))

noncomputable def derivedQuotHom (φ : E →* MulAut K) :
    K ⋊[φ] E →* (K ⧸ commutator K) ⋊[derivedQuotAut φ] E :=
  SemidirectProduct.map (QuotientGroup.mk' (commutator K)) (MonoidHom.id E) fun u => by
    ext k
    exact (derivedQuotAut_mk u k).symm

@[simp] theorem derivedQuotHom_left (x : K ⋊[φ] E) :
    (derivedQuotHom φ x).left = QuotientGroup.mk x.left := (rfl)

@[simp] theorem derivedQuotHom_right (x : K ⋊[φ] E) :
    (derivedQuotHom φ x).right = x.right := (rfl)

theorem derivedQuotHom_surjective : Function.Surjective (derivedQuotHom φ) := by
  intro y
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (s := commutator K) y.left
  refine ⟨inl k * inr y.right, SemidirectProduct.ext ?_ ?_⟩ <;> simp [hk]

theorem ker_derivedQuotHom :
    (derivedQuotHom φ).ker = (commutator K).map (inl : K →* K ⋊[φ] E) := by
  ext x
  rw [MonoidHom.mem_ker, mem_map_inl_commutator_iff]
  constructor
  · intro h
    refine ⟨?_, by simpa using congrArg SemidirectProduct.right h⟩
    simpa [QuotientGroup.eq_one_iff] using congrArg SemidirectProduct.left h
  · rintro ⟨h1, h2⟩
    refine SemidirectProduct.ext ?_ (by simpa using h2)
    simpa [QuotientGroup.eq_one_iff] using h1

instance instNormalMapInlCommutator : ((commutator K).map (inl : K →* K ⋊[φ] E)).Normal :=
  ker_derivedQuotHom (φ := φ) ▸ (derivedQuotHom φ).normal_ker

theorem map_inl_commutator_lt_range_inl [Group.IsSolvable K] [Nontrivial K] :
    (commutator K).map (inl : K →* K ⋊[φ] E) < (inl : K →* K ⋊[φ] E).range := by
  rw [MonoidHom.range_eq_map]
  exact (Subgroup.map_lt_map_iff_of_injective inl_injective).2
    (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := K))

noncomputable def quotientMapInlCommutatorEquiv (φ : E →* MulAut K) :
    (K ⋊[φ] E) ⧸ ((commutator K).map (inl : K →* K ⋊[φ] E)) ≃*
      (K ⧸ commutator K) ⋊[derivedQuotAut φ] E :=
  (QuotientGroup.quotientMulEquivOfEq (ker_derivedQuotHom (φ := φ)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ derivedQuotHom_surjective)

@[simp] theorem quotientMapInlCommutatorEquiv_mk (x : K ⋊[φ] E) :
    quotientMapInlCommutatorEquiv φ (QuotientGroup.mk x) = derivedQuotHom φ x := (rfl)

theorem quotientMapInlCommutatorEquiv_mk_inl (k : K) :
    quotientMapInlCommutatorEquiv φ (QuotientGroup.mk (inl k))
      = inl (QuotientGroup.mk k : K ⧸ commutator K) := by
  rw [quotientMapInlCommutatorEquiv_mk]
  exact SemidirectProduct.ext (by simp) (by simp)

theorem quotientMapInlCommutatorEquiv_mk_inr (u : E) :
    quotientMapInlCommutatorEquiv φ (QuotientGroup.mk (inr u)) = inr u := by
  rw [quotientMapInlCommutatorEquiv_mk]
  exact SemidirectProduct.ext (by simp) (by simp)

theorem injective_mk_comp_inr :
    Function.Injective
      ((QuotientGroup.mk' ((commutator K).map (inl : K →* K ⋊[φ] E))).comp inr) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_map_inl_commutator_iff] at hu
  simpa using hu.2

theorem natCard_range_mk_comp_inr :
    Nat.card
        ((QuotientGroup.mk' ((commutator K).map (inl : K →* K ⋊[φ] E))).comp inr).range
      = Nat.card E :=
  (Nat.card_congr (MonoidHom.ofInjective injective_mk_comp_inr).toEquiv).symm

theorem nontrivial_quotient_commutator [Group.IsSolvable K] [Nontrivial K] :
    Nontrivial (K ⧸ commutator K) :=
  QuotientGroup.nontrivial_iff.2 (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := K)).ne

theorem fixedPointFree_derivedQuotAut [Finite K] [Finite E] [Group.IsSolvable K]
    (hcop : (Nat.card K).Coprime (Nat.card E))
    (hC : ∀ u : E, u ≠ 1 → ∀ k : K, φ u k = k → k ∈ commutator K) {u : E} (hu : u ≠ 1) :
    MonoidHom.FixedPointFree (derivedQuotAut φ u) := by
  intro x hx
  set A : Subgroup E := Subgroup.zpowers u
  set ρ : ↥A →* MulAut K := φ.comp A.subtype
  have hAcomm : IsMulCommutative ↥A := Subgroup.zpowers_isMulCommutative u
  have hAsolv : Group.IsSolvable ↥A :=
    Group.isSolvable_of_comm fun a b => hAcomm.is_comm.comm a b
  have hN : IsInvariantSubgroup ρ (commutator K) := isInvariantSubgroup_of_characteristic _ _
  have hcopA : (Nat.card ↥A).Coprime (Nat.card K) :=
    hcop.symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card A)
  have hfix : ∀ b : ↥A, hN.quotientAut b x = x := by
    intro b
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective (s := commutator K) x
    obtain ⟨n, hn⟩ := b.2
    rw [hN.quotientAut_mk]
    have h : derivedQuotAut φ (b : E) (QuotientGroup.mk k) = QuotientGroup.mk k := by
      rw [← hn, map_zpow]
      have hs : derivedQuotAut φ u ∈ MulAction.stabilizer (MulAut (K ⧸ commutator K))
          (QuotientGroup.mk k : K ⧸ commutator K) := hx
      simpa [MulAction.mem_stabilizer_iff] using Subgroup.zpow_mem _ hs n
    rw [derivedQuotAut_mk] at h
    exact h
  obtain ⟨v, hv, hvx⟩ := exists_mem_fixedPoints_range_mk_eq hN hcopA hfix
  rw [mem_fixedPoints_range_iff] at hv
  have hvu : φ u (v : K) = v := hv ⟨u, Subgroup.mem_zpowers u⟩
  rw [← hvx]
  exact (QuotientGroup.eq_one_iff _).2 (hC u hu _ hvu)

theorem exists_irr_quotient_commutator [Finite K] {θ : K → ℂ} (hθ : θ ∈ Irr K) (hθ1 : θ ≠ 1)
    (hker : (commutator K : Set K) ⊆ charValueKernel θ) :
    ∃ θ₀ ∈ Irr (K ⧸ commutator K), θ₀ ≠ 1 ∧
      θ₀ ∘ (QuotientGroup.mk : K → K ⧸ commutator K) = θ := by
  obtain ⟨θ₀, hθ₀, hcomp⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn (N := commutator K)
    (mem_irrTrivialOn.2 ⟨hθ, fun n hn => mem_charValueKernel.1 (hker hn)⟩)
  refine ⟨θ₀, hθ₀, ?_, hcomp⟩
  intro h
  rw [h] at hcomp
  exact hθ1 (by rw [← hcomp]; rfl)

theorem eq_one_of_comp_eq_self_of_commutator_subset [Finite K] [Finite E] [Nontrivial K]
    [Group.IsSolvable K] (hcop : (Nat.card K).Coprime (Nat.card E))
    (hC : ∀ u : E, u ≠ 1 → ∀ k : K, φ u k = k → k ∈ commutator K) {θ : K → ℂ} (hθ : θ ∈ Irr K)
    (hθ1 : θ ≠ 1) (hker : (commutator K : Set K) ⊆ charValueKernel θ) {u : E}
    (h : ∀ k : K, θ (φ u k) = θ k) : u = 1 := by
  obtain ⟨θ₀, hθ₀, hθ₀1, hcomp⟩ := exists_irr_quotient_commutator hθ hθ1 hker
  have : Nontrivial (K ⧸ commutator K) := nontrivial_quotient_commutator
  refine eq_one_of_comp_eq_self_of_ne_one (φ := derivedQuotAut φ)
    (fun v hv => fixedPointFree_derivedQuotAut hcop hC hv) hθ₀ hθ₀1 ?_
  intro x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective (s := commutator K) x
  rw [derivedQuotAut_mk]
  have h1 : θ₀ (QuotientGroup.mk (φ u k)) = θ (φ u k) := congrFun hcomp _
  have h2 : θ₀ (QuotientGroup.mk k) = θ k := congrFun hcomp _
  rw [h1, h2, h k]

theorem inertiaGroup_kernelClassFun_of_commutator_subset [Finite K] [Finite E] [Nontrivial K]
    [Group.IsSolvable K] (hcop : (Nat.card K).Coprime (Nat.card E))
    (hC : ∀ u : E, u ≠ 1 → ∀ k : K, φ u k = k → k ∈ commutator K) {θ : K → ℂ} (hθ : θ ∈ Irr K)
    (hθ1 : θ ≠ 1) (hker : (commutator K : Set K) ⊆ charValueKernel θ) :
    inertiaGroup ((inl : K →* K ⋊[φ] E).range) (kernelClassFun φ θ)
      = (inl : K →* K ⋊[φ] E).range := by
  refine le_antisymm (fun t ht => ?_)
    (le_inertiaGroup _ (kernelClassFun_mem_classFun (Irr_subset_classFun hθ)))
  rw [mem_inertiaGroup, conjClassFun_kernelClassFun t (Irr_subset_classFun hθ)] at ht
  have h1 : θ ∘ (φ t.right).symm = θ := kernelClassFun_injective ht
  have h2 : ∀ x : K, θ (φ t.right⁻¹ x) = θ x := by
    intro x
    have h := congrFun h1 x
    rwa [map_inv, show ((φ t.right)⁻¹ : MulAut K) x = (φ t.right).symm x from rfl]
  have h3 : t.right⁻¹ = 1 :=
    eq_one_of_comp_eq_self_of_commutator_subset hcop hC hθ hθ1 hker h2
  rw [range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  simpa using inv_eq_one.1 h3

variable [Fintype K] [Fintype E]

theorem cfInner_self_indClassFun_kernelClassFun_of_commutator_subset [Nontrivial K]
    [Group.IsSolvable K] (hcop : (Nat.card K).Coprime (Nat.card E))
    (hC : ∀ u : E, u ≠ 1 → ∀ k : K, φ u k = k → k ∈ commutator K) {θ : K → ℂ} (hθ : θ ∈ Irr K)
    (hθ1 : θ ≠ 1) (hker : (commutator K : Set K) ⊆ charValueKernel θ) :
    cfInner (indClassFun (inl : K →* K ⋊[φ] E).range (kernelClassFun φ θ))
        (indClassFun (inl : K →* K ⋊[φ] E).range (kernelClassFun φ θ)) = 1 := by
  rw [cfInner_self_indClassFun _ (kernelClassFun_mem_Irr hθ),
    inertiaGroup_kernelClassFun_of_commutator_subset hcop hC hθ hθ1 hker,
    Subgroup.relIndex_self]
  simp

theorem indClassFun_kernelClassFun_mem_Irr_of_commutator_subset [Nontrivial K]
    [Group.IsSolvable K] (hcop : (Nat.card K).Coprime (Nat.card E))
    (hC : ∀ u : E, u ≠ 1 → ∀ k : K, φ u k = k → k ∈ commutator K) {θ : K → ℂ} (hθ : θ ∈ Irr K)
    (hθ1 : θ ≠ 1) (hker : (commutator K : Set K) ⊆ charValueKernel θ) :
    indClassFun (inl : K →* K ⋊[φ] E).range (kernelClassFun φ θ) ∈ Irr (K ⋊[φ] E) := by
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam
    ((inl : K →* K ⋊[φ] E).range)
    ((mem_indFam _).2 ⟨kernelClassFun φ θ, kernelClassFun_mem_Irr hθ, rfl⟩)
  refine mem_Irr.2 ⟨W, ?_, hW⟩
  rw [isIrreducible_iff_cfInner_self_eq_one, ← fdRepCharacter_eq W, hW]
  exact cfInner_self_indClassFun_kernelClassFun_of_commutator_subset hcop hC hθ hθ1 hker

theorem indClassFun_kernelClassFun_one_of_commutator_subset {θ : K → ℂ} (hθ : θ ∈ Irr K)
    (hker : (commutator K : Set K) ⊆ charValueKernel θ) :
    indClassFun (inl : K →* K ⋊[φ] E).range (kernelClassFun φ θ) 1 = (Nat.card E : ℂ) := by
  rw [indClassFun_kernelClassFun_one,
    Irr.apply_one_eq_one_of_commutator_subset_charValueKernel hθ hker, mul_one]

end CFSG.FeitThompson
