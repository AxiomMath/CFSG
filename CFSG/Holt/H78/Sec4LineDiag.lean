module

public import CFSG.Holt.H78.Sec4LineCoord
public import CFSG.Holt.H78.AltModelAut
public import CFSG.Holt.H78.Sec4AltSylow
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartSwap
import CFSG.Holt.PermFacts

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open Equiv Equiv.Perm
open scoped Pointwise

section TwoActions

variable {K : Type*} [Group K] {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem sign_map_commutatorElement (ρ : K →* Perm X) [Fintype X] [DecidableEq X] (a b : K) :
    sign (ρ (a * b * a⁻¹ * b⁻¹)) = 1 := by
  have h : ∀ u v : ℤˣ, u * v * u⁻¹ * v⁻¹ = 1 := fun u v => by
    rw [mul_right_comm u, mul_inv_cancel, one_mul, mul_inv_cancel]
  simpa only [map_mul, map_inv] using h (sign (ρ a)) (sign (ρ b))

omit [Fintype Y] [DecidableEq Y] in
theorem sign_mul_self_perm (σ : Perm X) : sign (σ * σ) = 1 := by
  rw [Perm.sign_mul, Int.units_mul_self]

theorem ker_le_ker_of_alternatingGroup_le (ρ : K →* Perm X) (ρ' : K →* Perm Y)
    (h3 : 3 ≤ Fintype.card X) (h5 : 5 ≤ Fintype.card Y) (hA : alternatingGroup X ≤ ρ.range)
    (hA' : alternatingGroup Y ≤ ρ'.range) (hker : ρ'.ker ≤ ρ.ker) : ρ.ker ≤ ρ'.ker := by
  set A := alternatingGroup Y
  set N : Subgroup (Perm Y) := ρ.ker.map ρ' ⊓ A with hN
  have hsimple : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by
    rwa [Nat.card_eq_fintype_card])
  have hnorm : (N.subgroupOf A).Normal := ⟨fun n hn a => by
    obtain ⟨⟨m, hm, hmn⟩, hnA⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)
    obtain ⟨k, hk⟩ := hA' a.2
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
      ⟨⟨k * m * k⁻¹, MonoidHom.mem_ker.mpr ?_, ?_⟩, ?_⟩)
    · rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hm, mul_one, mul_inv_cancel]
    · simp only [map_mul, map_inv, hk, hmn, Subgroup.coe_mul, Subgroup.coe_inv]
    · exact A.mul_mem (A.mul_mem a.2 hnA) (A.inv_mem a.2)⟩
  have hbot : N = ⊥ := by
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
    · rw [eq_bot_iff]
      intro n hn
      have hmem : (⟨n, (Subgroup.mem_inf.mp hn).2⟩ : A) ∈ N.subgroupOf A :=
        Subgroup.mem_subgroupOf.mpr hn
      rw [h, Subgroup.mem_bot] at hmem
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
    · exfalso
      obtain ⟨a, b, c, hab, hac, hbc⟩ : ∃ a b c : X, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
        obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card X)
        obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (s := ({a, b} : Finset X)) (t := Finset.univ)
          (by rw [Finset.card_univ]; exact (Finset.card_le_two).trans_lt (by omega))
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
        exact ⟨a, b, c, hab, Ne.symm hc.1, Ne.symm hc.2⟩
      have h3c : (swap a b * swap a c).IsThreeCycle := isThreeCycle_swap_mul_swap_same hab hac hbc
      obtain ⟨k, hk⟩ := hA h3c.mem_alternatingGroup
      have hkA : ρ' (k * k) ∈ A := by
        rw [map_mul]
        exact sign_mul_self_perm _
      have hkk : (⟨ρ' (k * k), hkA⟩ : A) ∈ N.subgroupOf A := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨⟨m, hm, hmk⟩, -⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hkk)
      have hker' : k * k * m⁻¹ ∈ ρ'.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hmk, mul_inv_cancel]
      have h1 := MonoidHom.mem_ker.mp (hker hker')
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hm, inv_one, mul_one, map_mul, hk] at h1
      have h2 := h3c.orderOf
      rw [orderOf_eq_iff (by norm_num)] at h2
      exact h2.2 2 (by norm_num) (by norm_num) (by rw [pow_two]; exact h1)
  intro n hn
  have hc : ρ' n ∈ Subgroup.centralizer (A : Set (Perm Y)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨k, hk⟩ := hA' ha
    have hmem : ρ' (n * k * n⁻¹ * k⁻¹) ∈ N := Subgroup.mem_inf.mpr
      ⟨⟨n * k * n⁻¹ * k⁻¹, MonoidHom.mem_ker.mpr (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.mp hn, one_mul,
          inv_one, mul_one, mul_inv_cancel]), rfl⟩,
        sign_map_commutatorElement ρ' n k⟩
    rw [hbot, Subgroup.mem_bot, map_mul, map_mul, map_mul, map_inv, map_inv, hk] at hmem
    have := congrArg (· * (a * ρ' n)) hmem
    simp only [one_mul] at this
    rw [← this]
    group
  rw [centralizer_alternatingGroup_perm_eq_bot (by omega), Subgroup.mem_bot] at hc
  exact hc

omit [Fintype Y] [DecidableEq Y] in
theorem sign_eq_one_of_pow_three_eq_one {σ : Perm X} (hσ : σ ^ 3 = 1) : sign σ = 1 := by
  rcases Int.units_eq_one_or (sign σ) with h | h
  · exact h
  · have := congrArg sign hσ
    rw [map_pow, h, map_one] at this
    exact absurd this (by decide)

theorem coe_mem_alternatingGroup_of_hom {H : Subgroup (Perm X)} (f : H →* Perm Y)
    (hA : alternatingGroup X ≤ H) {σ : Perm X} (hσ : σ ∈ alternatingGroup X) :
    f ⟨σ, hA hσ⟩ ∈ alternatingGroup Y := by
  have hle : Subgroup.closure {σ : Perm X | σ.IsThreeCycle} ≤ H := by
    rw [closure_three_cycles_eq_alternating]
    exact hA
  have key : ∀ τ ∈ Subgroup.closure {σ : Perm X | σ.IsThreeCycle}, ∀ h : τ ∈ H,
      f ⟨τ, h⟩ ∈ alternatingGroup Y := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem c hc =>
      intro h
      refine sign_eq_one_of_pow_three_eq_one ?_
      rw [← map_pow]
      have hc3 : c.IsThreeCycle := hc
      have h3 : (⟨c, h⟩ : H) ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc3.orderOf, pow_orderOf_eq_one])
      rw [h3, map_one]
    | one => exact fun _ => (map_one f).symm ▸ Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
      intro h
      have h1 : (⟨a * b, h⟩ : H) = ⟨a, hle ha⟩ * ⟨b, hle hb⟩ := rfl
      rw [h1, map_mul]
      exact Subgroup.mul_mem _ (iha _) (ihb _)
    | inv a ha iha =>
      intro h
      have h1 : (⟨a⁻¹, h⟩ : H) = (⟨a, hle ha⟩ : H)⁻¹ := rfl
      rw [h1, map_inv]
      exact Subgroup.inv_mem _ (iha _)
  exact key σ (by rwa [closure_three_cycles_eq_alternating]) _

end TwoActions

section Diag

variable {K : Type*} [Group K] {P P' : Type*} [Group P] [Group P']

noncomputable def rangeEquivOfKerEq (ρ : K →* P) (ρ' : K →* P') (hker : ρ.ker = ρ'.ker) :
    ρ.range ≃* ρ'.range :=
  (QuotientGroup.quotientKerEquivRange ρ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange ρ'))

theorem rangeEquivOfKerEq_apply (ρ : K →* P) (ρ' : K →* P') (hker : ρ.ker = ρ'.ker) (k : K)
    (h : ρ k ∈ ρ.range) : (rangeEquivOfKerEq ρ ρ' hker ⟨ρ k, h⟩ : P') = ρ' k := by
  have e1 : (QuotientGroup.quotientKerEquivRange ρ).symm ⟨ρ k, h⟩ = (k : K ⧸ ρ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [rangeEquivOfKerEq, MulEquiv.trans_apply, e1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem rangeEquivOfKerEq_symm_apply (ρ : K →* P) (ρ' : K →* P') (hker : ρ.ker = ρ'.ker) (k : K)
    (h : ρ' k ∈ ρ'.range) : ((rangeEquivOfKerEq ρ ρ' hker).symm ⟨ρ' k, h⟩ : P) = ρ k := by
  have e1 : (rangeEquivOfKerEq ρ ρ' hker).symm ⟨ρ' k, h⟩ = ⟨ρ k, k, rfl⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (rangeEquivOfKerEq_apply ρ ρ' hker k _).symm
  rw [e1]

end Diag

section TwoActionsEquiv

variable {K : Type*} [Group K] {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

theorem exists_equiv_of_ker_eq (ρ : K →* Perm X) (ρ' : K →* Perm Y)
    (hcard : Fintype.card X = Fintype.card Y) (h5 : 5 ≤ Fintype.card X)
    (h6 : Fintype.card X ≠ 6) (hA : alternatingGroup X ≤ ρ.range)
    (hA' : alternatingGroup Y ≤ ρ'.range) (hker : ρ.ker = ρ'.ker) :
    ∃ φ : X ≃ Y, ∀ k x, φ (ρ k x) = ρ' k (φ x) := by
  set θ := rangeEquivOfKerEq ρ ρ' hker
  have hθ : ∀ a (ha : a ∈ alternatingGroup X),
      ((θ ⟨a, hA ha⟩ : ρ'.range) : Perm Y) ∈ alternatingGroup Y := fun a ha =>
    coe_mem_alternatingGroup_of_hom ((ρ'.range).subtype.comp θ.toMonoidHom) hA ha
  have hθ' : ∀ b (hb : b ∈ alternatingGroup Y),
      ((θ.symm ⟨b, hA' hb⟩ : ρ.range) : Perm X) ∈ alternatingGroup X := fun b hb =>
    coe_mem_alternatingGroup_of_hom ((ρ.range).subtype.comp θ.symm.toMonoidHom) hA' hb
  let e : X ≃ Y := Fintype.equivOfCardEq hcard
  let ψ : MulAut (alternatingGroup X) :=
    { toFun := fun a => ⟨e.symm.permCongr (θ ⟨a, hA a.2⟩ : Perm Y), by
        rw [mem_alternatingGroup, sign_permCongr, ← mem_alternatingGroup]; exact hθ a a.2⟩
      invFun := fun a => ⟨θ.symm ⟨e.permCongr a, hA' (by
          rw [mem_alternatingGroup, sign_permCongr, ← mem_alternatingGroup]; exact a.2)⟩, hθ' _
          (by rw [mem_alternatingGroup, sign_permCongr, ← mem_alternatingGroup]; exact a.2)⟩
      left_inv := fun a => by
        apply Subtype.ext
        simp only [← Equiv.permCongr_symm, Equiv.apply_symm_apply, Subtype.coe_eta,
          MulEquiv.symm_apply_apply]
      right_inv := fun a => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply, ← Equiv.permCongr_symm,
          Equiv.symm_apply_apply]
      map_mul' := fun a b => by
        apply Subtype.ext
        have : (⟨a * b, hA (a * b).2⟩ : ρ.range) = ⟨a, hA a.2⟩ * ⟨b, hA b.2⟩ := rfl
        simp only [this, map_mul, Subgroup.coe_mul, Equiv.permCongr_mul] }
  obtain ⟨σ, hσ⟩ := exists_perm_conj_eq_of_mulAut_alternatingGroup h5 h6 ψ
  set φ : X ≃ Y := σ.trans e
  have key : ∀ k, ρ k ∈ alternatingGroup X → φ.permCongr (ρ k) = ρ' k := fun k hk => by
    have h1 := hσ ⟨ρ k, hk⟩
    have h2 : (θ ⟨ρ k, hA hk⟩ : Perm Y) = ρ' k := rangeEquivOfKerEq_apply ρ ρ' hker k _
    change e.symm.permCongr (θ ⟨ρ k, hA hk⟩ : Perm Y) = σ * ρ k * σ⁻¹ at h1
    rw [h2] at h1
    ext y
    have h3 := congrArg (fun τ : Perm X => e (τ (e.symm y))) h1
    simp only [Equiv.permCongr_apply, Equiv.apply_symm_apply, Perm.mul_apply, Equiv.symm_symm,
      Perm.inv_def] at h3
    simp only [Equiv.permCongr_apply, φ, Equiv.trans_apply, Equiv.symm_trans_apply]
    exact h3.symm
  have hevenX : ∀ k, ρ' k ∈ alternatingGroup Y → ρ k ∈ alternatingGroup X := fun k hk => by
    have := hθ' (ρ' k) hk
    rwa [rangeEquivOfKerEq_symm_apply ρ ρ' hker k] at this
  refine ⟨φ, fun k x => ?_⟩
  have hcent : (φ.permCongr (ρ k))⁻¹ * ρ' k ∈
      Subgroup.centralizer (alternatingGroup Y : Set (Perm Y)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨kb, rfl⟩ := hA' hb
    have hkb := hevenX kb hb
    have hconj : ρ (k * kb * k⁻¹) ∈ alternatingGroup X := by
      rw [map_mul, map_mul, map_inv]
      exact (inferInstance : (alternatingGroup X).Normal).conj_mem _ hkb _
    have e1 := key kb hkb
    have e2 : φ.permCongr (ρ k * ρ kb * (ρ k)⁻¹) = ρ' k * ρ' kb * (ρ' k)⁻¹ := by
      have := key (k * kb * k⁻¹) hconj
      simpa only [map_mul, map_inv] using this
    have e3 : φ.permCongr (ρ k)⁻¹ = (φ.permCongr (ρ k))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← Equiv.permCongr_mul, inv_mul_cancel]
      ext y; simp
    rw [Equiv.permCongr_mul, Equiv.permCongr_mul, e1, e3] at e2
    calc ρ' kb * ((φ.permCongr (ρ k))⁻¹ * ρ' k)
        = (φ.permCongr (ρ k))⁻¹ * (φ.permCongr (ρ k) * ρ' kb * (φ.permCongr (ρ k))⁻¹) *
            ρ' k := by group
      _ = (φ.permCongr (ρ k))⁻¹ * ρ' k * ρ' kb := by rw [e2]; group
  rw [centralizer_alternatingGroup_perm_eq_bot (by omega), Subgroup.mem_bot,
    inv_mul_eq_one] at hcent
  rw [← hcent]
  simp

end TwoActionsEquiv

section Fpf

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

theorem two_mul_card_cycleType_of_forall_apply_ne {σ : Perm Y} (h2 : σ * σ = 1)
    (hf : ∀ y, σ y ≠ y) : 2 * Multiset.card σ.cycleType = Fintype.card Y := by
  have hct := CFSG.OddStandard.AltStdSec.cycleType_eq_replicate_of_mul_self h2
  have hsupp : σ.support = Finset.univ :=
    Finset.eq_univ_of_forall fun y => mem_support.mpr (hf y)
  have h := sum_cycleType σ
  rw [hct, Multiset.sum_replicate, hsupp, Finset.card_univ, smul_eq_mul] at h
  omega

theorem card_support_eq_two_mul_card_cycleType {σ : Perm Y} (h : σ * σ = 1) :
    σ.support.card = 2 * Multiset.card σ.cycleType := by
  rw [← sum_cycleType, CFSG.OddStandard.AltStdSec.cycleType_eq_replicate_of_mul_self h,
    Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate, mul_comm]

theorem sign_eq_neg_one_of_forall_apply_ne (hY : Fintype.card Y = 6) {σ : Perm Y}
    (h2 : σ * σ = 1) (hf : ∀ y, σ y ≠ y) : sign σ = -1 := by
  have hc := two_mul_card_cycleType_of_forall_apply_ne h2 hf
  have hsupp : σ.support = Finset.univ :=
    Finset.eq_univ_of_forall fun y => mem_support.mpr (hf y)
  rw [sign_of_cycleType, sum_cycleType, hsupp, Finset.card_univ, hY,
    show Multiset.card σ.cycleType = 3 by omega]
  decide

end Fpf

section SixPoints

variable {K : Type*} [Group K] {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

theorem isSwap_of_ker_eq_of_card_eq_six (ρ : K →* Perm X) (ρ' : K →* Perm Y)
    (hX : Fintype.card X = 6) (hY : Fintype.card Y = 6) (hA : alternatingGroup X ≤ ρ.range)
    (hA' : alternatingGroup Y ≤ ρ'.range) (hker : ρ.ker = ρ'.ker) {t : K}
    (ht : ρ t * ρ t = 1 ∧ ∀ x, ρ t x ≠ x) (ht' : ρ' t * ρ' t = 1 ∧ ∀ y, ρ' t y ≠ y) {k : K}
    (hk : (ρ k).IsSwap) : (ρ' k).IsSwap := by
  have hr : ρ.range = ⊤ := eq_top_of_alternatingGroup_le hA ⟨k, rfl⟩ hk.sign_eq
  have hr' : ρ'.range = ⊤ :=
    eq_top_of_alternatingGroup_le hA' ⟨t, rfl⟩ (sign_eq_neg_one_of_forall_apply_ne hY ht'.1 ht'.2)
  let θ₀ := rangeEquivOfKerEq ρ ρ' hker
  let θ : Perm X ≃* Perm Y := ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hr.symm)).trans
    θ₀).trans ((MulEquiv.subgroupCongr hr').trans Subgroup.topEquiv)
  have hθ : ∀ k', θ (ρ k') = ρ' k' := fun k' => rangeEquivOfKerEq_apply ρ ρ' hker k' _
  have hk1 : ρ k * ρ k = 1 := by
    obtain ⟨a, b, -, hab⟩ := hk
    rw [hab, swap_mul_self]
  have hk2 : ρ' k * ρ' k = 1 := by
    rw [← hθ, ← map_mul, hk1, map_one]
  have hc1 : Multiset.card (ρ k).cycleType = 1 := by
    have := card_support_eq_two_mul_card_cycleType hk1
    rw [card_support_eq_two.mpr hk] at this
    omega
  have hcen : Nat.card (Subgroup.centralizer ({ρ' k} : Set (Perm Y))) =
      Nat.card (Subgroup.centralizer ({ρ k} : Set (Perm X))) := by
    rw [← hθ k]
    exact CFSG.OddStandard.AltStdSec.natCard_centralizer_map θ (ρ k)
  rw [CFSG.OddStandard.AltStdSec.natCard_centralizer_involution hk2,
    CFSG.OddStandard.AltStdSec.natCard_centralizer_involution hk1, hX, hY, hc1] at hcen
  have ha : 2 * Multiset.card (ρ' k).cycleType ≤ 6 := by
    rw [← card_support_eq_two_mul_card_cycleType hk2, ← hY]
    exact Finset.card_le_univ _
  set a := Multiset.card (ρ' k).cycleType with ha_def
  have ha3 : a ≤ 3 := by omega
  interval_cases a
  · norm_num [Nat.factorial] at hcen
  · rw [← card_support_eq_two, card_support_eq_two_mul_card_cycleType hk2, ← ha_def]
  · norm_num [Nat.factorial] at hcen
  ·
    exfalso
    have hsupp : (ρ' k).support = Finset.univ := Finset.eq_of_subset_of_card_le
      (Finset.subset_univ _)
      (by rw [Finset.card_univ, hY, card_support_eq_two_mul_card_cycleType hk2, ← ha_def])
    have hfpf : ∀ y, ρ' k y ≠ y := fun y => mem_support.mp (hsupp ▸ Finset.mem_univ y)
    have hsupp_t : (ρ' t).support = Finset.univ :=
      Finset.eq_univ_of_forall fun y => mem_support.mpr (ht'.2 y)
    obtain ⟨g, hg, hgk⟩ := exists_mem_alternatingGroup_conj_eq_of_card_support_eq
      (by rw [pow_two]; exact ht'.1) (by rw [pow_two]; exact hk2) (by rw [hsupp_t, hsupp])
    obtain ⟨k₁, rfl⟩ := hA' hg
    have hker' : k₁ * t * k₁⁻¹ * k⁻¹ ∈ ρ.ker := by
      rw [hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hgk,
        mul_inv_cancel]
    have hρk : ρ k = ρ k₁ * ρ t * (ρ k₁)⁻¹ := by
      have := MonoidHom.mem_ker.mp hker'
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at this
      exact this.symm
    obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := (ρ k).support) (t := Finset.univ)
      (by rw [Finset.card_univ, hX, card_support_eq_two.mpr hk]; norm_num)
    have hfix : ρ k c = c := notMem_support.mp hc
    rw [hρk, Perm.mul_apply, Perm.mul_apply] at hfix
    exact ht.2 ((ρ k₁)⁻¹ c) (Perm.eq_inv_iff_eq.mpr hfix)

end SixPoints

section Lines

variable {G : Type*} [Group G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω]

omit [DecidableEq Ω] in
theorem closure_longInvAt_le_stabilizer_sdiff {x : Ω} {L : Set Ω} (hL : IsJClosed G Ω L)
    (hx : x ∈ L) : Subgroup.closure (longInvAt G Ω x) ≤ stabilizer G (L \ {x}) := fun k hk => by
  rw [mem_stabilizer_iff, Set.smul_set_sdiff, Set.smul_set_singleton,
    mem_stabilizer_iff.mp (closure_longInvAt_le_stabilizer hL hx hk),
    mem_stabilizer_iff.mp (closure_longInvAt_le_stabilizer_point x hk)]

theorem Realizes3.alternatingGroup_le_inducedPerm_sdiff {A : Subgroup G} {x : Ω} {L : Set Ω}
    [Fintype ↥(L \ {x})] (hAL : A ≤ stabilizer G (L \ {x})) (h : Realizes3 A x L) :
    alternatingGroup ↥(L \ {x}) ≤ inducedPerm A (L \ {x}) hAL := by
  rw [← closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  have hσ3 : σ.IsThreeCycle := hσ
  obtain ⟨p, hp⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos, hσ3.card_support]
    norm_num
  have hnd := hσ3.nodup_iff_mem_support.mpr hp
  have heq := hσ3.eq_swap_mul_swap_iff_mem_support.mpr hp
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h01, h02⟩, h12⟩ := hnd
  have hne : ∀ {u v : ↥(L \ {x})}, u ≠ v → (u : Ω) ≠ v := fun h h' => h (Subtype.ext h')
  have hmem : ∀ u : ↥(L \ {x}), (u : Ω) ∈ L := fun u => u.2.1
  have hnx : ∀ u : ↥(L \ {x}), (u : Ω) ≠ x := fun u => u.2.2
  obtain ⟨k, hk, hky⟩ := h p (hmem p) (σ p) (hmem _) (σ (σ p)) (hmem _) (hnx p) (hnx _) (hnx _)
    (hne h01) (hne h02) (hne h12.1)
  refine mem_inducedPerm.mpr ⟨k, hk, fun y => ?_⟩
  rw [hky y (hmem y)]
  conv_lhs => rw [heq]
  rw [Perm.mul_apply, coe_swap, coe_swap]
  rfl

omit [DecidableEq Ω] in
theorem inducedHom_sdiff_eq_one_iff {x : Ω} {L : Set Ω} {K : Subgroup G}
    (hKx : K ≤ stabilizer G x) (hKL : K ≤ stabilizer G (L \ {x})) {k : K} :
    inducedHom K (L \ {x}) hKL k = 1 ↔ ∀ y ∈ L, (k : G) • y = y := by
  rw [inducedHom_eq_one_iff, mem_fixingSubgroup_iff]
  refine ⟨fun h y hy => ?_, fun h y hy => h y hy.1⟩
  by_cases hyx : y = x
  · rw [hyx]
    exact hKx k.2
  · exact h y ⟨hy, hyx⟩

omit [DecidableEq Ω] in
theorem inducedHom_sdiff_of_mem_longInvAt {x : Ω} {L : Set Ω} {K : Subgroup G}
    (hKL : K ≤ stabilizer G (L \ {x})) {t : K} (ht : (t : G) ∈ longInvAt G Ω x) :
    inducedHom K (L \ {x}) hKL t * inducedHom K (L \ {x}) hKL t = 1 ∧
      ∀ y, inducedHom K (L \ {x}) hKL t y ≠ y := by
  refine ⟨?_, fun y hy => ?_⟩
  · rw [← map_mul]
    ext y
    have h2 : (t : G) * t = 1 := mul_self_eq_one_of_mem_longInv ht.1
    simp only [coe_inducedHom_apply, Subgroup.coe_mul, h2, one_smul, Perm.one_apply]
  · have h1 : (t : G) • (y : Ω) = y := congrArg Subtype.val hy
    have := ht.1.2.unique h1 ht.2
    exact y.2.2 this

omit [DecidableEq Ω] in
theorem card_sdiff_singleton {x : Ω} {L : Set Ω} [Fintype ↥(L \ {x})] [Finite L]
    (hx : x ∈ L) : Fintype.card ↥(L \ {x}) = L.ncard - 1 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem hx]

end Lines

section Diagonal

variable {G : Type*} [Group G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω] [Finite Ω]
  {x : Ω} {L L' : Set Ω}

theorem ker_eq_of_diag [Fintype ↥(L \ {x})] [Fintype ↥(L' \ {x})] (hL : IsLine G L)
    (hL' : IsLine G L') (hx : x ∈ L) (hx' : x ∈ L')
    (hdiag : ∀ h ∈ Subgroup.closure (longInvAt G Ω x), h ∈ fixingSubgroup G L' →
      ∀ y ∈ L, h • y = y) :
    (inducedHom _ (L \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL.jClosed hx)).ker =
      (inducedHom _ (L' \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL'.jClosed hx')).ker := by
  set K := Subgroup.closure (longInvAt G Ω x)
  have hKx := closure_longInvAt_le_stabilizer_point (G := G) x
  have h7 := hL.seven_le
  have h7' := hL'.seven_le
  have hc : Fintype.card ↥(L \ {x}) = L.ncard - 1 := card_sdiff_singleton hx
  have hc' : Fintype.card ↥(L' \ {x}) = L'.ncard - 1 := card_sdiff_singleton hx'
  have hle : (inducedHom K (L' \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL'.jClosed hx')).ker
      ≤ (inducedHom K (L \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL.jClosed hx)).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, inducedHom_sdiff_eq_one_iff hKx] at hk ⊢
    exact hdiag k k.2 ((mem_fixingSubgroup_iff G).mpr hk)
  exact le_antisymm (ker_le_ker_of_alternatingGroup_le _ _ (by omega) (by omega)
    ((hL.threeCycle x hx).alternatingGroup_le_inducedPerm_sdiff _)
    ((hL'.threeCycle x hx').alternatingGroup_le_inducedPerm_sdiff _) hle) hle

theorem exists_equiv_of_diag [Fintype ↥(L \ {x})] [Fintype ↥(L' \ {x})] (hL : IsLine G L)
    (hL' : IsLine G L') (hx : x ∈ L) (hx' : x ∈ L') (hcard : L.ncard = L'.ncard)
    (h7 : L.ncard ≠ 7)
    (hdiag : ∀ h ∈ Subgroup.closure (longInvAt G Ω x), h ∈ fixingSubgroup G L' →
      ∀ y ∈ L, h • y = y) :
    ∃ φ : ↥(L \ {x}) ≃ ↥(L' \ {x}), ∀ (k : Subgroup.closure (longInvAt G Ω x)) y,
      φ (inducedHom _ (L \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL.jClosed hx) k y) =
        inducedHom _ (L' \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL'.jClosed hx') k
          (φ y) := by
  have h7' := hL.seven_le
  have hc : Fintype.card ↥(L \ {x}) = L.ncard - 1 := card_sdiff_singleton hx
  have hc' : Fintype.card ↥(L' \ {x}) = L'.ncard - 1 := card_sdiff_singleton hx'
  exact exists_equiv_of_ker_eq _ _ (by omega) (by omega) (by omega)
    ((hL.threeCycle x hx).alternatingGroup_le_inducedPerm_sdiff _)
    ((hL'.threeCycle x hx').alternatingGroup_le_inducedPerm_sdiff _)
    (ker_eq_of_diag hL hL' hx hx' hdiag)

theorem isSwap_of_diag [Fintype ↥(L \ {x})] [Fintype ↥(L' \ {x})] (hL : IsLine G L)
    (hL' : IsLine G L') (hx : x ∈ L) (hx' : x ∈ L') (hcard : L.ncard = L'.ncard)
    (h7 : L.ncard = 7)
    (hdiag : ∀ h ∈ Subgroup.closure (longInvAt G Ω x), h ∈ fixingSubgroup G L' →
      ∀ y ∈ L, h • y = y) {k : Subgroup.closure (longInvAt G Ω x)}
    (hk : (inducedHom _ (L \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL.jClosed hx) k).IsSwap) :
    (inducedHom _ (L' \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL'.jClosed hx') k).IsSwap := by
  have hc : Fintype.card ↥(L \ {x}) = L.ncard - 1 := card_sdiff_singleton hx
  have hc' : Fintype.card ↥(L' \ {x}) = L'.ncard - 1 := card_sdiff_singleton hx'
  obtain ⟨t, ht, -⟩ := hL.exists_mem_longInvAt hx
  set t' : Subgroup.closure (longInvAt G Ω x) := ⟨t, Subgroup.subset_closure ht⟩
  exact isSwap_of_ker_eq_of_card_eq_six _ _ (by omega) (by omega)
    ((hL.threeCycle x hx).alternatingGroup_le_inducedPerm_sdiff _)
    ((hL'.threeCycle x hx').alternatingGroup_le_inducedPerm_sdiff _)
    (ker_eq_of_diag hL hL' hx hx' hdiag) (t := t')
    (inducedHom_sdiff_of_mem_longInvAt _ ht) (inducedHom_sdiff_of_mem_longInvAt _ ht) hk

end Diagonal

section Sylow

private theorem fusionIsSylowIn_inf_of_conj_mem'' {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {S H N : Subgroup X} (hS : fusionIsSylowIn p S H) (hNH : N ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) : fusionIsSylowIn p (S ⊓ N) N := by
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, fun P hPN hP hle => ?_⟩
  obtain ⟨R, hPR, hR⟩ := exists_fusionIsSylowIn_ge hP (hPN.trans hNH)
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hS hR
  have hconj : ∀ x ∈ P, k⁻¹ * x * k ∈ S ⊓ N := fun x hx => ⟨(hkR x).mp (hPR hx), by
    simpa using hN k⁻¹ (inv_mem hk) x (hPN hx)⟩
  have hcard : Nat.card P ≤ Nat.card ↥(S ⊓ N) := Nat.card_le_card_of_injective
    (fun x : P => (⟨k⁻¹ * x * k, hconj x x.2⟩ : ↥(S ⊓ N))) (fun x y h => by
      have h' := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at h'
      exact Subtype.ext h')
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem eq_one_or_eq_swap_of_mem_fixingSubgroup {X : Type*} [DecidableEq X] {Λ : Set X}
    {a b : X} (hab : a ≠ b) (hΛ : Λᶜ = {a, b}) {σ : Perm X}
    (hσ : σ ∈ fixingSubgroup (Perm X) Λ) : σ = 1 ∨ σ = swap a b := by
  rw [mem_fixingSubgroup_iff] at hσ
  have hcases : ∀ u, u ∈ Λ ∨ u = a ∨ u = b := fun u => by
    by_cases hu : u ∈ Λ
    · exact Or.inl hu
    · have : u ∈ Λᶜ := hu
      rw [hΛ] at this
      exact Or.inr this
  have haΛ : a ∈ Λᶜ := by rw [hΛ]; exact Set.mem_insert _ _
  have hbΛ : b ∈ Λᶜ := by rw [hΛ]; exact Set.mem_insert_of_mem _ rfl
  have hab' : ∀ u, u ∈ Λᶜ → σ u = a ∨ σ u = b := fun u hu => by
    have : σ u ∈ Λᶜ := fun h => hu (by
      have h' : σ (σ u) = σ u := hσ _ h
      rwa [σ.injective h'] at h)
    rw [hΛ] at this
    exact this
  rcases hab' a haΛ with ha | ha
  · left
    have hb : σ b = b := by
      rcases hab' b hbΛ with hb | hb
      · exact absurd (σ.injective (hb.trans ha.symm)) hab.symm
      · exact hb
    ext u
    rcases hcases u with h | rfl | rfl
    · exact hσ u h
    · exact ha
    · exact hb
  · right
    have hb : σ b = a := by
      rcases hab' b hbΛ with hb | hb
      · exact hb
      · exact absurd (σ.injective (hb.trans ha.symm)) hab.symm
    ext u
    rcases hcases u with h | rfl | rfl
    · rw [show σ u = u from hσ u h, swap_apply_of_ne_of_ne] <;> rintro rfl
      · exact haΛ h
      · exact hbΛ h
    · rw [ha, swap_apply_left]
    · rw [hb, swap_apply_right]

end Sylow

section FixedPoints

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω]
  [Finite Ω] {x : Ω} {L : Set Ω}

omit [Finite G] in
theorem IsLine.odd_ncard (hL : IsLine G L) (hx : x ∈ L) : Odd L.ncard := by
  classical
  have : Fintype ↥(L \ {x}) := Fintype.ofFinite _
  obtain ⟨t, ht, -⟩ := hL.exists_mem_longInvAt hx
  have h := inducedHom_sdiff_of_mem_longInvAt (closure_longInvAt_le_stabilizer_sdiff hL.jClosed hx)
    (t := ⟨t, Subgroup.subset_closure ht⟩) ht
  have h2 := two_mul_card_cycleType_of_forall_apply_ne h.1 h.2
  rw [card_sdiff_singleton hx] at h2
  have := hL.seven_le
  rw [Nat.odd_iff]
  omega

omit [Finite G] [DecidableEq Ω] [Finite Ω] in
theorem ncard_preimage_val_sdiff {Θ : Finset Ω} (hΘL : ∀ θ ∈ Θ, θ ∈ L ∧ θ ≠ x) :
    (((↑) : ↥(L \ {x}) → Ω) ⁻¹' (Θ : Set Ω)).ncard = Θ.card := by
  rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective, Set.ncard_coe_finset]
  intro θ hθ
  exact ⟨⟨θ, (hΘL θ hθ).1, (hΘL θ hθ).2⟩, rfl⟩

theorem mem_of_forall_smul_eq_of_nine_le [Fintype ↥(L \ {x})] (hL : IsLine G L) (hx : x ∈ L)
    (h9 : 9 ≤ L.ncard) {Θ : Finset Ω} (hΘ : Θ.card = 4) (hΘL : ∀ θ ∈ Θ, θ ∈ L ∧ θ ≠ x)
    {V : Subgroup G} (hV : fusionIsSylowIn 2 V
      (Subgroup.closure (longInvAt G Ω x) ⊓ fixingSubgroup G (Θ : Set Ω)))
    {y : Ω} (hy : y ∈ L) (hyx : y ≠ x) (hfix : ∀ v ∈ V, v • y = y) : y ∈ Θ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.closure (longInvAt G Ω x)
  set F := fixingSubgroup G (Θ : Set Ω)
  have hKL := closure_longInvAt_le_stabilizer_sdiff hL.jClosed hx
  have hKFL : K ⊓ F ≤ stabilizer G (L \ {x}) := inf_le_left.trans hKL
  have hV' := fusionIsSylowIn_inducedPerm (h := hKFL) hV
  set Θ' : Set ↥(L \ {x}) := ((↑) : ↥(L \ {x}) → Ω) ⁻¹' (Θ : Set Ω) with hΘ'
  set N := alternatingGroup ↥(L \ {x}) ⊓ fixingSubgroup (Perm ↥(L \ {x})) Θ'
  have hNle : N ≤ inducedPerm (K ⊓ F) (L \ {x}) hKFL := by
    intro σ hσ
    obtain ⟨k, hk, hkσ⟩ := mem_inducedPerm.mp
      ((hL.threeCycle x hx).alternatingGroup_le_inducedPerm_sdiff hKL (Subgroup.mem_inf.mp hσ).1)
    refine mem_inducedPerm.mpr ⟨k, ⟨hk, (mem_fixingSubgroup_iff G).mpr fun θ hθ => ?_⟩, hkσ⟩
    have hθ' := hΘL θ hθ
    have h1 := (mem_fixingSubgroup_iff _).mp (Subgroup.mem_inf.mp hσ).2 ⟨θ, hθ'.1, hθ'.2⟩ hθ
    rw [← hkσ ⟨θ, hθ'.1, hθ'.2⟩]
    exact congrArg Subtype.val h1
  have hNnorm : ∀ h ∈ inducedPerm (K ⊓ F) (L \ {x}) hKFL, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    have hhF : h ∈ fixingSubgroup (Perm ↥(L \ {x})) Θ' := by
      obtain ⟨k, hk, hkh⟩ := mem_inducedPerm.mp hh
      refine (mem_fixingSubgroup_iff _).mpr fun u hu => Subtype.ext ?_
      rw [Perm.smul_def, hkh]
      exact (mem_fixingSubgroup_iff G).mp (Subgroup.mem_inf.mp hk).2 _ hu
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (inferInstance : (alternatingGroup ↥(L \ {x})).Normal).conj_mem _
        (Subgroup.mem_inf.mp hn).1 _
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hhF (Subgroup.mem_inf.mp hn).2)
        (Subgroup.inv_mem _ hhF)
  have hVN := fusionIsSylowIn_inf_of_conj_mem'' hV' hNle hNnorm
  have hcard : Fintype.card ↥(L \ {x}) = L.ncard - 1 := card_sdiff_singleton hx
  have hodd := hL.odd_ncard hx
  have hcompl : Nat.card ↥Θ'ᶜ = L.ncard - 5 := by
    rw [Nat.card_coe_set_eq, Set.ncard_compl, Nat.card_eq_fintype_card, hcard,
      ncard_preimage_val_sdiff hΘL, hΘ]
    omega
  have heven : Even (Nat.card ↥Θ'ᶜ) := by
    rw [hcompl]
    exact Nat.Odd.sub_odd hodd (by decide)
  have hfixset := fixSet_eq_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup heven
    (by rw [hcompl]; omega) hVN
  have hmem : (⟨y, hy, hyx⟩ : ↥(L \ {x})) ∈ fixSet ↥(L \ {x})
      (inducedPerm V (L \ {x}) (hV.1.trans hKFL) ⊓ N) := by
    intro σ hσ
    obtain ⟨v, hv, hvσ⟩ := mem_inducedPerm.mp (Subgroup.mem_inf.mp hσ).1
    apply Subtype.ext
    rw [Perm.smul_def, hvσ]
    exact hfix v hv
  rw [hfixset] at hmem
  exact hmem

theorem exists_swap_of_eq_seven [Fintype ↥(L \ {x})] (hL : IsLine G L) (hx : x ∈ L)
    (h7 : L.ncard = 7) {Θ : Finset Ω} (hΘ : Θ.card = 4) (hΘL : ∀ θ ∈ Θ, θ ∈ L ∧ θ ≠ x)
    {V : Subgroup G} (hV : fusionIsSylowIn 2 V
      (Subgroup.closure (longInvAt G Ω x) ⊓ fixingSubgroup G (Θ : Set Ω))) :
    ∃ a b : ↥(L \ {x}), a ≠ b ∧ (((↑) : ↥(L \ {x}) → Ω) ⁻¹' (Θ : Set Ω))ᶜ = {a, b} ∧
      (∀ v (hv : v ∈ V), inducedHom _ (L \ {x}) (closure_longInvAt_le_stabilizer_sdiff
        hL.jClosed hx) ⟨v, (hV.1 hv).1⟩ = 1 ∨ inducedHom _ (L \ {x})
        (closure_longInvAt_le_stabilizer_sdiff hL.jClosed hx) ⟨v, (hV.1 hv).1⟩ = swap a b) ∧
      ∃ v, ∃ hv : v ∈ V, inducedHom _ (L \ {x}) (closure_longInvAt_le_stabilizer_sdiff
        hL.jClosed hx) ⟨v, (hV.1 hv).1⟩ = swap a b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.closure (longInvAt G Ω x)
  set F := fixingSubgroup G (Θ : Set Ω)
  have hKL := closure_longInvAt_le_stabilizer_sdiff hL.jClosed hx
  set ρ := inducedHom K (L \ {x}) hKL
  have hKFL : K ⊓ F ≤ stabilizer G (L \ {x}) := inf_le_left.trans hKL
  have hV' := fusionIsSylowIn_inducedPerm (h := hKFL) hV
  set Θ' : Set ↥(L \ {x}) := ((↑) : ↥(L \ {x}) → Ω) ⁻¹' (Θ : Set Ω) with hΘ'
  have hcard : Fintype.card ↥(L \ {x}) = 6 := by rw [card_sdiff_singleton hx, h7]
  have hc2 : Θ'ᶜ.ncard = 2 := by
    rw [Set.ncard_compl, Nat.card_eq_fintype_card, hcard, ncard_preimage_val_sdiff hΘL, hΘ]
  obtain ⟨a, b, hab, hab'⟩ := Set.ncard_eq_two.mp hc2
  have hVF : ∀ v (hv : v ∈ V), ρ ⟨v, (hV.1 hv).1⟩ ∈ fixingSubgroup (Perm ↥(L \ {x})) Θ' :=
    fun v hv => (mem_fixingSubgroup_iff _).mpr fun u hu => Subtype.ext
      ((mem_fixingSubgroup_iff G).mp (hV.1 hv).2 _ hu)
  have h1 : ∀ v (hv : v ∈ V), ρ ⟨v, (hV.1 hv).1⟩ = 1 ∨ ρ ⟨v, (hV.1 hv).1⟩ = swap a b :=
    fun v hv => eq_one_or_eq_swap_of_mem_fixingSubgroup hab hab' (hVF v hv)
  refine ⟨a, b, hab, hab', h1, ?_⟩
  by_contra hne'
  have hne : ∀ v (hv : v ∈ V), ρ ⟨v, (hV.1 hv).1⟩ ≠ swap a b := fun v hv h => hne' ⟨v, hv, h⟩
  have hbot : inducedPerm V (L \ {x}) (hV.1.trans hKFL) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    obtain ⟨v, hv, hvσ⟩ := mem_inducedPerm.mp hσ
    have hρv : ρ ⟨v, (hV.1 hv).1⟩ = 1 := (h1 v hv).resolve_right (hne v hv)
    rw [Subgroup.mem_bot]
    ext u
    rw [Perm.one_apply, hvσ]
    exact congrArg Subtype.val (congrArg (fun π : Perm ↥(L \ {x}) => π u) hρv)
  obtain ⟨t, ht, -⟩ := hL.exists_mem_longInvAt hx
  have hft := inducedHom_sdiff_of_mem_longInvAt hKL (t := ⟨t, Subgroup.subset_closure ht⟩) ht
  have htop : ρ.range = ⊤ := eq_top_of_alternatingGroup_le
    ((hL.threeCycle x hx).alternatingGroup_le_inducedPerm_sdiff hKL) ⟨_, rfl⟩
    (sign_eq_neg_one_of_forall_apply_ne hcard hft.1 hft.2)
  obtain ⟨k, hk⟩ : swap a b ∈ ρ.range := by rw [htop]; exact Subgroup.mem_top _
  have hswap : swap a b ∈ inducedPerm (K ⊓ F) (L \ {x}) hKFL := by
    refine mem_inducedPerm.mpr ⟨k, ⟨k.2, (mem_fixingSubgroup_iff G).mpr fun θ hθ => ?_⟩,
      fun u => by rw [← hk]; rfl⟩
    have hθ' := hΘL θ hθ
    have hθa : (⟨θ, hθ'.1, hθ'.2⟩ : ↥(L \ {x})) ≠ a := fun h => by
      have : a ∈ Θ'ᶜ := by rw [hab']; exact Set.mem_insert _ _
      exact this (h ▸ hθ)
    have hθb : (⟨θ, hθ'.1, hθ'.2⟩ : ↥(L \ {x})) ≠ b := fun h => by
      have : b ∈ Θ'ᶜ := by rw [hab']; exact Set.mem_insert_of_mem _ rfl
      exact this (h ▸ hθ)
    have := congrArg (fun π : Perm ↥(L \ {x}) => ((π ⟨θ, hθ'.1, hθ'.2⟩ : ↥(L \ {x})) : Ω)) hk
    rw [swap_apply_of_ne_of_ne hθa hθb] at this
    exact this
  have h2 : IsPGroup 2 (Subgroup.zpowers (swap a b)) :=
    isPGroup_zpowers_of_orderOf_eq_two (orderOf_eq_prime (by rw [pow_two, swap_mul_self])
      (fun h => hab (swap_eq_one_iff.mp h)))
  have heq := hV'.2.2 _ (Subgroup.zpowers_le.mpr hswap) h2 (by rw [hbot]; exact bot_le)
  rw [hbot] at heq
  have : swap a b ∈ (⊥ : Subgroup (Perm ↥(L \ {x}))) := heq ▸ Subgroup.mem_zpowers _
  exact hab (swap_eq_one_iff.mp (Subgroup.mem_bot.mp this))

theorem mem_of_forall_smul_eq_of_eq_seven [Fintype ↥(L \ {x})] (hL : IsLine G L) (hx : x ∈ L)
    (h7 : L.ncard = 7) {Θ : Finset Ω} (hΘ : Θ.card = 4) (hΘL : ∀ θ ∈ Θ, θ ∈ L ∧ θ ≠ x)
    {V : Subgroup G} (hV : fusionIsSylowIn 2 V
      (Subgroup.closure (longInvAt G Ω x) ⊓ fixingSubgroup G (Θ : Set Ω)))
    {y : Ω} (hy : y ∈ L) (hyx : y ≠ x) (hfix : ∀ v ∈ V, v • y = y) : y ∈ Θ := by
  by_contra hyΘ
  obtain ⟨a, b, hab, hab', -, v, hv, hvab⟩ := exists_swap_of_eq_seven hL hx h7 hΘ hΘL hV
  have hy' : (⟨y, hy, hyx⟩ : ↥(L \ {x})) ∈ (((↑) : ↥(L \ {x}) → Ω) ⁻¹' (Θ : Set Ω))ᶜ := hyΘ
  rw [hab'] at hy'
  have hfy := congrArg (fun π : Perm ↥(L \ {x}) => ((π ⟨y, hy, hyx⟩ : ↥(L \ {x})) : Ω)) hvab
  simp only [coe_inducedHom_apply] at hfy
  rw [hfix v hv] at hfy
  rcases hy' with h | h
  · rw [h, swap_apply_left] at hfy
    have hya : (a : Ω) = y := by rw [← h]
    exact hab (Subtype.ext (hya.trans hfy))
  · rw [Set.mem_singleton_iff] at h
    rw [h, swap_apply_right] at hfy
    have hyb : (b : Ω) = y := by rw [← h]
    exact hab (Subtype.ext (hfy.symm.trans hyb.symm))

end FixedPoints

section SecondLine

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω]
  [Finite Ω] {x : Ω} {L L' : Set Ω}

theorem ncard_fix_of_diag_of_nine_le [Fintype ↥(L \ {x})] [Fintype ↥(L' \ {x})]
    (hL : IsLine G L) (hL' : IsLine G L') (hx : x ∈ L) (hx' : x ∈ L')
    (hcard : L.ncard = L'.ncard) (h9 : 9 ≤ L.ncard)
    (hdiag : ∀ h ∈ Subgroup.closure (longInvAt G Ω x), h ∈ fixingSubgroup G L' →
      ∀ y ∈ L, h • y = y)
    {Θ : Finset Ω} (hΘ : Θ.card = 4) (hΘL : ∀ θ ∈ Θ, θ ∈ L ∧ θ ≠ x)
    {V : Subgroup G} (hV : fusionIsSylowIn 2 V
      (Subgroup.closure (longInvAt G Ω x) ⊓ fixingSubgroup G (Θ : Set Ω))) :
    {y : Ω | y ∈ L' ∧ y ≠ x ∧ ∀ v ∈ V, v • y = y}.ncard = 4 := by
  obtain ⟨φ, hφ⟩ := exists_equiv_of_diag hL hL' hx hx' hcard (by omega) hdiag
  set Θ' : Set ↥(L \ {x}) := ((↑) : ↥(L \ {x}) → Ω) ⁻¹' (Θ : Set Ω)
  have heq : {y : Ω | y ∈ L' ∧ y ≠ x ∧ ∀ v ∈ V, v • y = y} =
      (fun w => ((φ w : ↥(L' \ {x})) : Ω)) '' Θ' := by
    ext y
    constructor
    · rintro ⟨hy, hyx, hfix⟩
      refine ⟨φ.symm ⟨y, hy, hyx⟩, ?_, by simp⟩
      have hw : ∀ v ∈ V, v • ((φ.symm ⟨y, hy, hyx⟩ : ↥(L \ {x})) : Ω) =
          (φ.symm ⟨y, hy, hyx⟩ : ↥(L \ {x})) := fun v hv => by
        have h1 := hφ ⟨v, (hV.1 hv).1⟩ (φ.symm ⟨y, hy, hyx⟩)
        rw [Equiv.apply_symm_apply] at h1
        have h2 : inducedHom _ (L' \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL'.jClosed hx')
            ⟨v, (hV.1 hv).1⟩ ⟨y, hy, hyx⟩ = ⟨y, hy, hyx⟩ := Subtype.ext (hfix v hv)
        rw [h2, ← φ.eq_symm_apply] at h1
        exact congrArg Subtype.val h1
      exact mem_of_forall_smul_eq_of_nine_le hL hx h9 hΘ hΘL hV
        (φ.symm ⟨y, hy, hyx⟩).2.1 (φ.symm ⟨y, hy, hyx⟩).2.2 hw
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(φ w).2.1, (φ w).2.2, fun v hv => ?_⟩
      have h1 := hφ ⟨v, (hV.1 hv).1⟩ w
      have h2 : inducedHom _ (L \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL.jClosed hx)
          ⟨v, (hV.1 hv).1⟩ w = w :=
        Subtype.ext ((mem_fixingSubgroup_iff G).mp (hV.1 hv).2 _ hw)
      rw [h2] at h1
      exact (congrArg Subtype.val h1).symm
  rw [heq, Set.ncard_image_of_injective _ (fun a b h => φ.injective (Subtype.val_injective h)),
    ncard_preimage_val_sdiff hΘL, hΘ]

theorem ncard_fix_of_diag_of_eq_seven [Fintype ↥(L \ {x})] [Fintype ↥(L' \ {x})]
    (hL : IsLine G L) (hL' : IsLine G L') (hx : x ∈ L) (hx' : x ∈ L')
    (hcard : L.ncard = L'.ncard) (h7 : L.ncard = 7)
    (hdiag : ∀ h ∈ Subgroup.closure (longInvAt G Ω x), h ∈ fixingSubgroup G L' →
      ∀ y ∈ L, h • y = y)
    {Θ : Finset Ω} (hΘ : Θ.card = 4) (hΘL : ∀ θ ∈ Θ, θ ∈ L ∧ θ ≠ x)
    {V : Subgroup G} (hV : fusionIsSylowIn 2 V
      (Subgroup.closure (longInvAt G Ω x) ⊓ fixingSubgroup G (Θ : Set Ω))) :
    {y : Ω | y ∈ L' ∧ y ≠ x ∧ ∀ v ∈ V, v • y = y}.ncard = 4 := by
  classical
  set K := Subgroup.closure (longInvAt G Ω x)
  set ρ := inducedHom K (L \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL.jClosed hx)
  set ρ' := inducedHom K (L' \ {x}) (closure_longInvAt_le_stabilizer_sdiff hL'.jClosed hx')
  obtain ⟨a, b, hab, -, h1, v₀, hv₀, hv₀ab⟩ := exists_swap_of_eq_seven hL hx h7 hΘ hΘL hV
  have hker := ker_eq_of_diag hL hL' hx hx' hdiag
  have hsw : (ρ' ⟨v₀, (hV.1 hv₀).1⟩).IsSwap := isSwap_of_diag hL hL' hx hx' hcard h7 hdiag
    (by rw [hv₀ab]; exact ⟨a, b, hab, rfl⟩)
  obtain ⟨p, q, hpq, hpq'⟩ := hsw
  have h2 : ∀ v (hv : v ∈ V), ρ' ⟨v, (hV.1 hv).1⟩ = 1 ∨ ρ' ⟨v, (hV.1 hv).1⟩ = swap p q := by
    intro v hv
    rcases h1 v hv with h | h
    · left
      have : (⟨v, (hV.1 hv).1⟩ : K) ∈ ρ.ker := h
      rw [hker] at this
      exact this
    · right
      rw [← hpq']
      have : (⟨v₀, (hV.1 hv₀).1⟩ : K)⁻¹ * ⟨v, (hV.1 hv).1⟩ ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h, hv₀ab, inv_mul_cancel]
      rw [hker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
  have hcard' : Fintype.card ↥(L' \ {x}) = 6 := by rw [card_sdiff_singleton hx', ← hcard, h7]
  have heq : {y : Ω | y ∈ L' ∧ y ≠ x ∧ ∀ v ∈ V, v • y = y} =
      ((↑) : ↥(L' \ {x}) → Ω) '' ({p, q}ᶜ : Set ↥(L' \ {x})) := by
    ext y
    constructor
    · rintro ⟨hy, hyx, hfix⟩
      refine ⟨⟨y, hy, hyx⟩, ?_, rfl⟩
      have h3 : ρ' ⟨v₀, (hV.1 hv₀).1⟩ ⟨y, hy, hyx⟩ = ⟨y, hy, hyx⟩ := Subtype.ext (hfix v₀ hv₀)
      rw [hpq'] at h3
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [h, swap_apply_left] at h3
        exact hpq h3.symm
      · rw [h, swap_apply_right] at h3
        exact hpq h3
    · rintro ⟨u, hu, rfl⟩
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
      refine ⟨u.2.1, u.2.2, fun v hv => ?_⟩
      rcases h2 v hv with h | h
      · exact congrArg Subtype.val (congrArg (fun π : Perm ↥(L' \ {x}) => π u) h)
      · have := congrArg (fun π : Perm ↥(L' \ {x}) => ((π u : ↥(L' \ {x})) : Ω)) h
        rw [swap_apply_of_ne_of_ne hu.1 hu.2] at this
        exact this
  rw [heq, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_compl,
    Set.ncard_pair hpq, Nat.card_eq_fintype_card, hcard']

end SecondLine

section ThreeElement

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω]
  [Finite Ω] {x : Ω} {L : Set Ω}

theorem exists_mem_normalizer_pow_three (hL : IsLine G L) (hx : x ∈ L) {θ₁ θ₂ θ₃ θ₄ : Ω}
    (h₁ : θ₁ ∈ L) (h₂ : θ₂ ∈ L) (h₃ : θ₃ ∈ L) (h₄ : θ₄ ∈ L) (h₁x : θ₁ ≠ x) (h₂x : θ₂ ≠ x)
    (h₃x : θ₃ ≠ x) (h₁₂ : θ₁ ≠ θ₂) (h₁₃ : θ₁ ≠ θ₃) (h₁₄ : θ₁ ≠ θ₄) (h₂₃ : θ₂ ≠ θ₃)
    (h₂₄ : θ₂ ≠ θ₄) (h₃₄ : θ₃ ≠ θ₄) {V : Subgroup G} (hV : fusionIsSylowIn 2 V
      (Subgroup.closure (longInvAt G Ω x) ⊓
        fixingSubgroup G (({θ₁, θ₂, θ₃, θ₄} : Finset Ω) : Set Ω))) :
    ∃ g ∈ Subgroup.closure (longInvAt G Ω x), g ∈ Subgroup.normalizer (V : Set G) ∧
      (∃ n : ℕ, g ^ 3 ^ n = 1) ∧ g • θ₄ = θ₄ ∧ g • θ₁ ≠ θ₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.closure (longInvAt G Ω x)
  set Θ : Set Ω := (({θ₁, θ₂, θ₃, θ₄} : Finset Ω) : Set Ω) with hΘ
  set F := fixingSubgroup G Θ
  have hmemΘ : ∀ {θ}, θ ∈ Θ ↔ θ = θ₁ ∨ θ = θ₂ ∨ θ = θ₃ ∨ θ = θ₄ := fun {θ} => by
    simp [hΘ]
  have hm1 : θ₁ ∈ Θ := hmemΘ.mpr (Or.inl rfl)
  have hm2 : θ₂ ∈ Θ := hmemΘ.mpr (Or.inr (Or.inl rfl))
  have hm3 : θ₃ ∈ Θ := hmemΘ.mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hm4 : θ₄ ∈ Θ := hmemΘ.mpr (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨k, hkK, hk⟩ := hL.threeCycle x hx θ₁ h₁ θ₂ h₂ θ₃ h₃ h₁x h₂x h₃x h₁₂ h₁₃ h₂₃
  set c := cyc3 θ₁ θ₂ θ₃
  have hc1 : c θ₁ = θ₂ := cyc3_apply_left h₁₂ h₁₃
  have hc2 : c θ₂ = θ₃ := cyc3_apply_mid h₁₃ h₂₃
  have hc3 : c θ₃ = θ₁ := cyc3_apply_right θ₁ θ₂ θ₃
  have hc4 : c θ₄ = θ₄ := cyc3_apply_of_ne h₁₄.symm h₂₄.symm h₃₄.symm
  have hkΘ : ∀ θ ∈ Θ, k • θ = c θ := fun θ hθ => hk θ (by
    rcases hmemΘ.mp hθ with rfl | rfl | rfl | rfl <;> assumption)
  have hcΘ : ∀ θ ∈ Θ, c θ ∈ Θ := fun θ hθ => by
    rcases hmemΘ.mp hθ with rfl | rfl | rfl | rfl
    · rw [hc1]; exact hm2
    · rw [hc2]; exact hm3
    · rw [hc3]; exact hm1
    · rw [hc4]; exact hm4
  have hkΘ' : ∀ θ ∈ Θ, k⁻¹ • θ ∈ Θ := fun θ hθ => by
    rcases hmemΘ.mp hθ with rfl | rfl | rfl | rfl
    · rw [← hc3, ← hkΘ _ hm3, inv_smul_smul]; exact hm3
    · rw [← hc1, ← hkΘ _ hm1, inv_smul_smul]; exact hm1
    · rw [← hc2, ← hkΘ _ hm2, inv_smul_smul]; exact hm2
    · rw [← hc4, ← hkΘ _ hm4, inv_smul_smul]; exact hm4
  have hconj : ∀ a ∈ K, (∀ θ ∈ Θ, a⁻¹ • θ ∈ Θ) → ∀ z ∈ K ⊓ F, a * z * a⁻¹ ∈ K ⊓ F := by
    intro a ha haΘ z hz
    refine ⟨K.mul_mem (K.mul_mem ha hz.1) (K.inv_mem ha), (mem_fixingSubgroup_iff G).mpr
      fun θ hθ => ?_⟩
    rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hz.2 _ (haΘ θ hθ), smul_inv_smul]
  have hmapKF : (K ⊓ F).map (MulAut.conj k).toMonoidHom = K ⊓ F := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hconj k hkK hkΘ' z hz
    · intro z hz
      refine ⟨k⁻¹ * z * k⁻¹⁻¹, hconj k⁻¹ (K.inv_mem hkK) (fun θ hθ => by
        rw [inv_inv, hkΘ θ hθ]; exact hcΘ θ hθ) z hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hV' : fusionIsSylowIn 2 (V.map (MulAut.conj k).toMonoidHom) (K ⊓ F) := by
    have := fusionIsSylowIn_map (MulAut.conj k).toMonoidHom hV
    rwa [hmapKF] at this
  obtain ⟨y, hy, hyV⟩ := exists_mem_conj_of_fusionIsSylowIn hV hV'
  set g₀ := y⁻¹ * k
  have hg₀K : g₀ ∈ K := K.mul_mem (K.inv_mem hy.1) hkK
  have hg₀N : g₀ ∈ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have h1 : k * v * k⁻¹ ∈ V.map (MulAut.conj k).toMonoidHom := ⟨v, hv, rfl⟩
      have h2 := (hyV _).mp h1
      have e : g₀ * v * g₀⁻¹ = y⁻¹ * (k * v * k⁻¹) * y := by simp only [g₀]; group
      rw [e]
      exact h2
    · intro hv
      have e : g₀ * v * g₀⁻¹ = y⁻¹ * (k * v * k⁻¹) * y := by simp only [g₀]; group
      rw [e] at hv
      obtain ⟨w, hw, hwv⟩ := (hyV _).mpr hv
      have : w = v := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwv
        simpa using hwv
      rwa [← this]
  have hg₀Θ : ∀ θ ∈ Θ, g₀ • θ = c θ := fun θ hθ => by
    rw [mul_smul, hkΘ θ hθ, inv_smul_eq_iff]
    exact ((mem_fixingSubgroup_iff G).mp hy.2 _ (hcΘ θ hθ)).symm
  have hpowΘ : ∀ j : ℕ, ∀ θ ∈ Θ, g₀ ^ j • θ = (c ^ j) θ := by
    intro j
    induction j with
    | zero => intro θ _; simp
    | succ j ih =>
      intro θ hθ
      rw [pow_succ, mul_smul, hg₀Θ θ hθ, ih _ (hcΘ θ hθ), pow_succ]
      rfl
  obtain ⟨a, m, hm3', hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g₀).ne' 3
    (by norm_num)
  refine ⟨g₀ ^ m, K.pow_mem hg₀K m, Subgroup.pow_mem _ hg₀N m, ⟨a, ?_⟩, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
  · rw [hpowΘ m θ₄ hm4]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hc4 m
  · rw [hpowΘ m θ₁ hm1]
    have : Fintype Ω := Fintype.ofFinite Ω
    have h3c : c.IsThreeCycle := by
      have e : c = swap θ₂ θ₁ * swap θ₂ θ₃ := by simp only [c, cyc3, swap_comm θ₁ θ₂]
      rw [e]
      exact isThreeCycle_swap_mul_swap_same h₁₂.symm h₂₃ h₁₃
    rw [← pow_mod_orderOf, h3c.orderOf]
    have hm : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hm with h | h <;> rw [h]
    · rw [pow_one, hc1]
      exact h₁₂.symm
    · rw [pow_two, Perm.mul_apply, hc1, hc2]
      exact h₁₃.symm

end ThreeElement

section Data

variable (G : Type*) [Group G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω]

structure LineDiagData (x : Ω) (L : Set Ω) (Θ : Finset Ω) (V : Subgroup G) (g : G) (y' : Ω) :
    Prop where
  isLine : IsLine G L
  mem : x ∈ L
  card_Θ : Θ.card = 4
  mem_Θ : ∀ θ ∈ Θ, θ ∈ L ∧ θ ≠ x
  sylow : fusionIsSylowIn 2 V
    (Subgroup.closure (longInvAt G Ω x) ⊓ fixingSubgroup G (Θ : Set Ω))
  mem_Θ_of_fix : ∀ y ∈ L, y ≠ x → (∀ v ∈ V, v • y = y) → y ∈ Θ
  fix_y' : ∀ v ∈ V, v • y' = y'
  notMem_y' : y' ∉ L
  mem_normalizer : g ∈ Subgroup.normalizer (V : Set G)
  pow_eq_one : ∃ n : ℕ, g ^ 3 ^ n = 1
  smul_x : g • x = x
  smul_y' : g • y' = y'
  exists_fix : ∃ θ ∈ Θ, g • θ = θ
  exists_move : ∃ θ ∈ Θ, g • θ ≠ θ

variable {G} [Finite G] [Finite Ω]

theorem exists_lineDiagData {Λ : Set Ω} (hΛ : IsLine G Λ) {x : Ω} {L L' : Set Ω}
    (hL : L ∈ linesThrough G Λ x) (hL' : L' ∈ linesThrough G Λ x) (hne : L ≠ L')
    (hdiag : ∀ h ∈ Subgroup.closure (longInvAt G Ω x), h ∈ fixingSubgroup G L' →
      ∀ y ∈ L, h • y = y) :
    ∃ Θ V g y', LineDiagData G x L Θ V g y' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLl := hΛ.of_mem_linesThrough hL
  have hL'l := hΛ.of_mem_linesThrough hL'
  have hx := hL.2
  have hx' := hL'.2
  have hcard : L.ncard = L'.ncard := by
    obtain ⟨⟨g₁, h₁⟩, -⟩ := hL
    obtain ⟨⟨g₂, h₂⟩, -⟩ := hL'
    rw [← h₁, ← h₂, Set.ncard_smul_set, Set.ncard_smul_set]
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hax, hbx, hcx, hdx, hab, hac, had, hbc, hbd, hcd⟩ :=
    exists_four_of_seven_le hLl.seven_le x
  set Θ : Finset Ω := {a, b, c, d} with hΘdef
  have hΘ : Θ.card = 4 := by
    rw [hΘdef, Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  have hΘL : ∀ θ ∈ Θ, θ ∈ L ∧ θ ≠ x := by
    intro θ hθ
    simp only [hΘdef, Finset.mem_insert, Finset.mem_singleton] at hθ
    rcases hθ with rfl | rfl | rfl | rfl
    · exact ⟨ha, hax⟩
    · exact ⟨hb, hbx⟩
    · exact ⟨hc, hcx⟩
    · exact ⟨hd, hdx⟩
  obtain ⟨V, -, hV⟩ := exists_fusionIsSylowIn_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : ⊥ ≤ Subgroup.closure (longInvAt G Ω x) ⊓ fixingSubgroup G (Θ : Set Ω))
  have : Fintype ↥(L \ {x}) := Fintype.ofFinite _
  have : Fintype ↥(L' \ {x}) := Fintype.ofFinite _
  have hodd := hLl.odd_ncard hx
  have h7 := hLl.seven_le
  have h79 : L.ncard = 7 ∨ 9 ≤ L.ncard := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hfix : ∀ y ∈ L, y ≠ x → (∀ v ∈ V, v • y = y) → y ∈ Θ := by
    intro y hy hyx hf
    rcases h79 with h | h
    · exact mem_of_forall_smul_eq_of_eq_seven hLl hx h hΘ hΘL hV hy hyx hf
    · exact mem_of_forall_smul_eq_of_nine_le hLl hx h hΘ hΘL hV hy hyx hf
  set S' := {y : Ω | y ∈ L' ∧ y ≠ x ∧ ∀ v ∈ V, v • y = y} with hS'def
  have hS' : S'.ncard = 4 := by
    rcases h79 with h | h
    · exact ncard_fix_of_diag_of_eq_seven hLl hL'l hx hx' hcard h hdiag hΘ hΘL hV
    · exact ncard_fix_of_diag_of_nine_le hLl hL'l hx hx' hcard h hdiag hΘ hΘL hV
  obtain ⟨g, hgK, hgN, hg3, hgd, hga⟩ := exists_mem_normalizer_pow_three hLl hx ha hb hc hd
    hax hbx hcx hab hac had hbc hbd hcd hV
  have hgx : ∀ {h : G}, h ∈ Subgroup.closure (longInvAt G Ω x) → h • x = x := fun hh =>
    closure_longInvAt_le_stabilizer_point x hh
  have hgL' : ∀ {h : G}, h ∈ Subgroup.closure (longInvAt G Ω x) → h • L' = L' := fun hh =>
    closure_longInvAt_le_stabilizer hL'l.jClosed hx' hh
  have hmapS : ∀ {h : G}, h ∈ Subgroup.closure (longInvAt G Ω x) →
      h ∈ Subgroup.normalizer (V : Set G) → ∀ y ∈ S', h • y ∈ S' := by
    intro h hh hhN y ⟨hy, hyx, hyV⟩
    refine ⟨?_, fun h' => hyx (by rw [← hgx hh] at h'; exact smul_left_cancel _ h'), ?_⟩
    · rw [← hgL' hh]
      exact Set.smul_mem_smul_set hy
    · intro v hv
      have hv' : h⁻¹ * v * h ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhN) v).mp hv
        rwa [inv_inv] at this
      calc v • h • y = h • (h⁻¹ * v * h) • y := by simp [mul_smul]
        _ = h • y := by rw [hyV _ hv']
  have hgS : g ∈ stabilizer G S' := by
    rw [mem_stabilizer_iff]
    refine Set.Subset.antisymm ?_ fun y hy => ⟨g⁻¹ • y, hmapS (Subgroup.inv_mem _ hgK)
      (Subgroup.inv_mem _ hgN) y hy, smul_inv_smul g y⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmapS hgK hgN y hy
  have hP : IsPGroup 3 (Subgroup.zpowers g) := by
    obtain ⟨n, hn⟩ := hg3
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hn)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hmod := card_modEq_card_fixSet_inter_of_le_stabilizer hP
    (Subgroup.zpowers_le.mpr hgS : Subgroup.zpowers g ≤ stabilizer G S')
  obtain ⟨y', hy'g, hy'S⟩ : (fixSet Ω (Subgroup.zpowers g) ∩ S').Nonempty := by
    by_contra hne'
    rw [Set.not_nonempty_iff_eq_empty] at hne'
    rw [hne', Nat.card_coe_set_eq, Nat.card_coe_set_eq, hS', Set.ncard_empty] at hmod
    exact absurd hmod (by decide)
  have hy'L : y' ∉ L := fun hy' => hne (hLl.eq_of_mem_of_mem hL'l hx hx' hy' hy'S.1
    (Ne.symm hy'S.2.1))
  exact ⟨Θ, V, g, y', hLl, hx, hΘ, hΘL, hV, hfix, hy'S.2.2, hy'L, hgN, hg3, hgx hgK,
    hy'g g (Subgroup.mem_zpowers g), ⟨d, by simp [hΘdef], hgd⟩, ⟨a, by simp [hΘdef], hga⟩⟩

end Data

end CFSG.Holt.H78
