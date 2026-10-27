module

public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup
public import CFSG.LocalAnalysis.ComponentInitial.CentralPrimeKernelFixedCore
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalInvolutionOddCore

public section

namespace CFSG.ComponentClassification.SymmetricLocal

open Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem oddCore_eq_pPrimeCore_two (G : Type*) [Group G] :
    CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem pPrimeCore_eq_bot_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (p : ℕ)
    (e : G ≃* G') (h : CFSG.pPrimeCore p G' = ⊥) : CFSG.pPrimeCore p G = ⊥ := by
  have hmap := CFSG.pPrimeCore_map_iso p e
  rw [h] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

theorem fixedSubgroup_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (β : MulAut G) :
    (fixedSubgroup β).map e.toMonoidHom = fixedSubgroup (e.symm.trans (β.trans e)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : β x = x := hx
    change e (β (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx']
  · intro hy
    have hy' : e (β (e.symm y)) = y := hy
    refine ⟨e.symm y, ?_, by simp⟩
    change β (e.symm y) = e.symm y
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact hy'

theorem card_fixed_ne_three_of_sign {n : ℕ} (hn4 : n % 4 ≠ 1) {σ : Perm (Fin n)}
    (hσ2 : σ ^ 2 = 1) (hsign : Perm.sign σ = -1) : Nat.card {x // σ x = x} ≠ 3 := by
  intro h3
  have hfix : Fintype.card (Function.fixedPoints σ) = 3 := by
    rw [← Nat.card_eq_fintype_card, ← h3]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have hs := Perm.sign_of_pow_two_eq_one hσ2
  rw [hsign, hfix, Fintype.card_fin] at hs
  have hodd : Odd ((n - 3) / 2) := by
    rcases Nat.even_or_odd ((n - 3) / 2) with he | ho
    · rw [he.neg_one_pow] at hs
      exact absurd hs (by decide)
    · exact ho
  have hsupp : σ.support.card = n - 3 := by
    have h1 := Perm.card_fixedPoints σ
    rw [hfix, Fintype.card_fin, Perm.sum_cycleType] at h1
    have h2 : σ.support.card ≤ n := by
      have := Finset.card_le_univ σ.support
      rwa [Fintype.card_fin] at this
    omega
  have h2dvd := Perm.two_dvd_card_support hσ2
  rw [hsupp] at h2dvd
  obtain ⟨j, hj⟩ := hodd
  obtain ⟨c, hc⟩ := h2dvd
  omega

theorem perfect_central_two_cover_alternating_outer_fixed_odd_core {n : ℕ} (hn : 7 ≤ n)
    (hn4 : n % 4 ≠ 1) {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (hZ : IsPGroup 2 (Subgroup.center H))
    (hiso : Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin n)))
    (β : MulAut H) (hβ : β * β = 1) (hβout : β ∉ (MulAut.conj : H →* MulAut H).range) :
    CFSG.oddCore (fixedSubgroup β) = ⊥ := by
  obtain ⟨θ⟩ := hiso
  set βbar : MulAut (H ⧸ Subgroup.center H) := PerfectAutomorphisms.onCenterQuotient β
    with hβbar
  have hβbar_mk : ∀ y : H, βbar (y : H ⧸ Subgroup.center H) = ((β y : H) : H ⧸ Subgroup.center H) :=
    fun y => PerfectAutomorphisms.onCenterQuotient_apply_mk β y
  set α : MulAut (alternatingGroup (Fin n)) := θ.symm.trans (βbar.trans θ) with hα
  have hαapply : ∀ a, α a = θ (βbar (θ.symm a)) := fun _ => rfl
  have hββ : ∀ x, β (β x) = x := fun x => by
    have h := congrArg (fun γ : MulAut H => γ x) hβ
    simpa only [MulAut.mul_apply, MulAut.one_apply] using h
  have hβbar2 : ∀ q, βbar (βbar q) = q := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hβbar_mk, hβbar_mk, hββ]
  have hα2 : ∀ a, α (α a) = a := fun a => by
    rw [hαapply, hαapply, MulEquiv.symm_apply_apply, hβbar2, MulEquiv.apply_symm_apply]
  obtain ⟨σ, hσ⟩ :=
    CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le (Or.inr hn) α
  have hσσ : σ * σ = 1 := by
    refine LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
      (by rw [Fintype.card_fin]; omega) fun g hg => ?_
    have h := congrArg (fun a : alternatingGroup (Fin n) => (a : Perm (Fin n)))
      (hα2 ⟨g, hg⟩)
    simp only at h
    rw [hσ, hσ] at h
    calc σ * σ * g = (σ * (σ * g * σ⁻¹) * σ⁻¹) * (σ * σ) := by group
      _ = g * (σ * σ) := by rw [h]
  have hsign : Perm.sign σ = -1 := by
    refine (Int.units_eq_one_or (Perm.sign σ)).resolve_left fun hσA => hβout ?_
    set s : alternatingGroup (Fin n) := ⟨σ, hσA⟩ with hs
    have hαs : ∀ a, α a = s * a * s⁻¹ := fun a => Subtype.ext (hσ a)
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (θ.symm s)
    have hβbar_conj : βbar = MulAut.conj (h : H ⧸ Subgroup.center H) := by
      ext q
      have hq : βbar q = θ.symm (α (θ q)) := by
        rw [hαapply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      rw [hq, hαs, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, hh, MulAut.conj_apply]
    have hconj : PerfectAutomorphisms.centerQuotientHom H (MulAut.conj h) =
        MulAut.conj (h : H ⧸ Subgroup.center H) := by
      ext q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      change PerfectAutomorphisms.onCenterQuotient (MulAut.conj h)
        ((QuotientGroup.mk' (Subgroup.center H)) y) = _
      rw [PerfectAutomorphisms.onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply]
      rfl
    have hinj := LocalAnalysis.ComponentInitial.perfect_central_quotient_automorphism_faithful H
    refine ⟨h, hinj ?_⟩
    rw [hconj]
    exact hβbar_conj.symm
  have hσ1 : σ ≠ 1 := fun h => by
    rw [h, map_one] at hsign
    exact absurd hsign (by decide)
  have hσ2 : orderOf σ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hfix3 := card_fixed_ne_three_of_sign hn4 (by rw [sq]; exact hσσ) hsign
  have hcoreA := (involution_permutation_centralizer_odd_core
    (H := alternatingGroup (Fin n)) le_rfl hσ2).1 hfix3
  have hfixA : (fixedSubgroup α).map (alternatingGroup (Fin n)).subtype =
      alternatingGroup (Fin n) ⊓ Subgroup.centralizer ({σ} : Set (Perm (Fin n))) := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : α a = a := ha
      have h := congrArg (fun b : alternatingGroup (Fin n) => (b : Perm (Fin n))) ha'
      rw [hσ] at h
      refine ⟨a.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (a : Perm (Fin n)) * σ = σ * a * σ⁻¹ * σ := by rw [h]
        _ = σ * a := by group
    · rintro ⟨hgA, hgC⟩
      refine ⟨⟨g, hgA⟩, ?_, rfl⟩
      change α ⟨g, hgA⟩ = ⟨g, hgA⟩
      apply Subtype.ext
      rw [hσ]
      have hgσ : g * σ = σ * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
      calc σ * g * σ⁻¹ = g * σ * σ⁻¹ := by rw [hgσ]
        _ = g := by group
  have hcoreα : CFSG.pPrimeCore 2 (fixedSubgroup α) = ⊥ := by
    refine pPrimeCore_eq_bot_of_mulEquiv 2
      (((fixedSubgroup α).equivMapOfInjective _
        (alternatingGroup (Fin n)).subtype_injective).trans (MulEquiv.subgroupCongr hfixA)) ?_
    rw [← oddCore_eq_pPrimeCore_two]
    exact hcoreA
  have hcoreβbar : CFSG.pPrimeCore 2 (fixedSubgroup βbar) = ⊥ :=
    pPrimeCore_eq_bot_of_mulEquiv 2
      (((fixedSubgroup βbar).equivMapOfInjective _ θ.injective).trans
        (MulEquiv.subgroupCongr (fixedSubgroup_map_mulEquiv θ βbar))) hcoreα
  have hβZ : (Subgroup.center H).map (β : H →* H) = Subgroup.center H :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) β
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore_two]
  exact LocalAnalysis.ComponentInitial.central_prime_kernel_fixed_group_prime_complement_core
    (Subgroup.center H) le_rfl hZ β hβZ hcoreβbar

end CFSG.ComponentClassification.SymmetricLocal
