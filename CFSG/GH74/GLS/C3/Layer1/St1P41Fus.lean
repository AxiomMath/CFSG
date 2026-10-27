module

public import CFSG.GH74.KGroups.TwoM12Outer
public import Certificates.Certificate5152

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpElim

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

theorem inner5152_true : Inner5152 := Certificates.certificate5152

theorem permJ_mem (h : evalCodes [m12gA, m12gB] wordJ = permJ) : permJ ∈ NativeSporadic.M12 := by
  rw [← h]
  exact evalCodes_mem _ m12_gens_mem' wordJ

theorem exists_elemJ (h5152 : Inner5152) :
    ∃ J : NativeSporadic.M12, J * J = 1 ∧ J * elemZ = elemZ * J ∧ fixedCount J = 0 ∧
      elemZ * J ≠ 1 ∧ fixedCount (elemZ * J) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h5152
  have hmem : permJ ∈ NativeSporadic.M12 := permJ_mem h1
  obtain ⟨J, hJ⟩ : ∃ J : NativeSporadic.M12, (J : Equiv.Perm (Fin 12)) = permJ :=
    ⟨⟨permJ, hmem⟩, rfl⟩
  have hZ : (elemZ : Equiv.Perm (Fin 12)) = permZ := elemZ_coe
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_mul, hJ, h2, Subgroup.coe_one]
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hJ, hZ, h3]
  · unfold fixedCount
    rw [hJ]
    exact h5
  · intro h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_mul, hJ, hZ, Subgroup.coe_one] at h'
    have hzz : permZ * permZ = 1 := by rw [← sq]; exact permZ_sq
    apply h4
    calc permJ = permZ * (permZ * permJ) := by rw [← mul_assoc, hzz, one_mul]
      _ = permZ := by rw [h', mul_one]
  · unfold fixedCount
    rw [Subgroup.coe_mul, hJ, hZ]
    exact h6

theorem t_mul_eq_inv {L : Type} [Group L] {t ℓ : L} (ht : orderOf t = 2) (hℓ : ℓ ^ 2 = t) :
    t * ℓ = ℓ⁻¹ := by
  have ht2 : t * t = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.1 ht).1
  refine eq_inv_of_mul_eq_one_left ?_
  calc t * ℓ * ℓ = t * (ℓ * ℓ) := mul_assoc _ _ _
    _ = t * t := by rw [← sq, hℓ]
    _ = 1 := ht2

theorem orderOf_fixedCount_of_sq_eq
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.M12)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) {ℓ : L} (hℓ : ℓ ^ 2 = t) :
    orderOf (π ℓ) = 2 ∧ fixedCount (π ℓ) = 0 := by
  have ht1 : t ≠ 1 := (orderOf_eq_prime_iff.1 ht).2
  have ht2 : t * t = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.1 ht).1
  obtain ⟨hfc, hlift4, -⟩ := m12_double_cover_involution_lift_orders hLq ht hZ π hπ hker
  have hπt : π t = 1 := by
    have : t ∈ π.ker := hker ▸ mem_zpowers t
    exact this
  have hπℓ2 : π ℓ * π ℓ = 1 := by rw [← map_mul, ← sq, hℓ, hπt]
  have hπℓ1 : π ℓ ≠ 1 := by
    intro h
    have hmem : ℓ ∈ zpowers t := hker ▸ (h : ℓ ∈ π.ker)
    rcases eq_one_or_eq_of_mem_zpowers ht hmem with h1 | h1
    · rw [h1, one_pow] at hℓ
      exact ht1 hℓ.symm
    · rw [h1, sq, ht2] at hℓ
      exact ht1 hℓ.symm
  have hord : orderOf (π ℓ) = 2 := orderOf_eq_prime (by rw [sq]; exact hπℓ2) hπℓ1
  refine ⟨hord, ?_⟩
  rcases hfc _ hord with h4 | h0
  · exfalso
    have h2 := hlift4 ℓ hord h4
    have : ℓ ^ 2 = 1 := by rw [← h2, pow_orderOf_eq_one]
    rw [this] at hℓ
    exact ht1 hℓ.symm
  · exact h0

theorem exists_inverting
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.M12)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) {ℓ : L} (hℓ : ℓ ^ 2 = t) :
    ∃ j : L, j * ℓ * j⁻¹ = ℓ⁻¹ := by
  have h5152 : Inner5152 := inner5152_true
  have ht1 : t ≠ 1 := (orderOf_eq_prime_iff.1 ht).2
  have ht2 : t * t = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.1 ht).1
  obtain ⟨-, -, hlift0⟩ := m12_double_cover_involution_lift_orders hLq ht hZ π hπ hker
  obtain ⟨hord, hfix⟩ := orderOf_fixedCount_of_sq_eq hLq ht hZ π hπ hker hℓ
  have hπℓ2 : π ℓ * π ℓ = 1 := by rw [← sq, ← hord, pow_orderOf_eq_one]
  obtain ⟨g, hg⟩ := conj_elemZ_of_fixedCount_zero (π ℓ) hord hfix
  obtain ⟨J, hJ2, hJZ, hJ0, hZJ1, hZJ0⟩ := exists_elemJ h5152
  have hZ2 : elemZ * elemZ = 1 := by rw [← sq, ← orderOf_elemZ, pow_orderOf_eq_one]
  set j' : NativeSporadic.M12 := g * J * g⁻¹ with hj'
  have hjc : j' * π ℓ = π ℓ * j' := by
    rw [← hg]
    calc g * J * g⁻¹ * (g * elemZ * g⁻¹) = g * (J * elemZ) * g⁻¹ := by group
      _ = g * (elemZ * J) * g⁻¹ := by rw [hJZ]
      _ = g * elemZ * g⁻¹ * (g * J * g⁻¹) := by group
  have hj2 : j' * j' = 1 := by
    calc g * J * g⁻¹ * (g * J * g⁻¹) = g * (J * J) * g⁻¹ := by group
      _ = 1 := by rw [hJ2, mul_one, mul_inv_cancel]
  have hj0 : fixedCount j' = 0 := by rw [hj', fixedCount_conj]; exact hJ0
  have hj1 : j' ≠ 1 := by
    intro h
    have hJ1 : J = 1 := by
      calc J = g⁻¹ * (g * J * g⁻¹) * g := by group
        _ = 1 := by rw [← hj', h, mul_one, inv_mul_cancel]
    have h12 : fixedCount J = 12 := by
      rw [hJ1]
      unfold fixedCount
      simp
    rw [hJ0] at h12
    exact absurd h12 (by norm_num)
  have hjord : orderOf j' = 2 := orderOf_eq_prime (by rw [sq]; exact hj2) hj1
  have hprod : π ℓ * j' = g * (elemZ * J) * g⁻¹ := by
    rw [← hg, hj']
    group
  have hw0 : fixedCount (π ℓ * j') = 0 := by rw [hprod, fixedCount_conj]; exact hZJ0
  have hw1 : π ℓ * j' ≠ 1 := by
    intro h
    rw [hprod] at h
    apply hZJ1
    calc elemZ * J = g⁻¹ * (g * (elemZ * J) * g⁻¹) * g := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  have hwprod2 : (π ℓ * j') * (π ℓ * j') = 1 := by
    calc π ℓ * j' * (π ℓ * j') = π ℓ * (j' * π ℓ) * j' := by group
      _ = π ℓ * (π ℓ * j') * j' := by rw [hjc]
      _ = (π ℓ * π ℓ) * (j' * j') := by group
      _ = 1 := by rw [hπℓ2, hj2, one_mul]
  have hword : orderOf (π ℓ * j') = 2 := orderOf_eq_prime (by rw [sq]; exact hwprod2) hw1
  obtain ⟨ĵ, hĵ⟩ := hπ j'
  have hĵ2 : ĵ ^ 2 = t := (hlift0 ĵ (by rw [hĵ]; exact hjord) (by rw [hĵ]; exact hj0)).1
  have hℓĵ2 : (ℓ * ĵ) ^ 2 = t :=
    (hlift0 (ℓ * ĵ) (by rw [map_mul, hĵ]; exact hword) (by rw [map_mul, hĵ]; exact hw0)).1
  have hcker : ĵ * ℓ * ĵ⁻¹ * ℓ⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hĵ, hjc]
    group
  rcases eq_one_or_eq_of_mem_zpowers ht (hker ▸ hcker) with hc1 | hc1
  · exfalso
    have hcomm : ĵ * ℓ = ℓ * ĵ := by
      calc ĵ * ℓ = (ĵ * ℓ * ĵ⁻¹ * ℓ⁻¹) * (ℓ * ĵ) := by group
        _ = ℓ * ĵ := by rw [hc1, one_mul]
    have h1 : (ℓ * ĵ) ^ 2 = ℓ ^ 2 * ĵ ^ 2 := Commute.mul_pow hcomm.symm 2
    rw [h1, hℓ, hĵ2, ht2] at hℓĵ2
    exact ht1 hℓĵ2.symm
  · refine ⟨ĵ, ?_⟩
    calc ĵ * ℓ * ĵ⁻¹ = (ĵ * ℓ * ĵ⁻¹ * ℓ⁻¹) * ℓ := by group
      _ = t * ℓ := by rw [hc1]
      _ = ℓ⁻¹ := t_mul_eq_inv ht hℓ

theorem exists_conj_of_sq_eq
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.M12)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) {ℓ₁ ℓ₂ : L} (h₁ : ℓ₁ ^ 2 = t)
    (h₂ : ℓ₂ ^ 2 = t) : ∃ g : L, g * ℓ₁ * g⁻¹ = ℓ₂ := by
  obtain ⟨hord₁, hfix₁⟩ := orderOf_fixedCount_of_sq_eq hLq ht hZ π hπ hker h₁
  obtain ⟨hord₂, hfix₂⟩ := orderOf_fixedCount_of_sq_eq hLq ht hZ π hπ hker h₂
  obtain ⟨a, ha⟩ := conj_elemZ_of_fixedCount_zero (π ℓ₁) hord₁ hfix₁
  obtain ⟨b, hb⟩ := conj_elemZ_of_fixedCount_zero (π ℓ₂) hord₂ hfix₂
  obtain ⟨g, hg⟩ := hπ (b * a⁻¹)
  have hconj : π (g * ℓ₁ * g⁻¹) = π ℓ₂ := by
    rw [map_mul, map_mul, map_inv, hg, ← ha, ← hb]
    group
  have hmem : g * ℓ₁ * g⁻¹ * ℓ₂⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hconj, mul_inv_cancel]
  rcases eq_one_or_eq_of_mem_zpowers ht (hker ▸ hmem) with h1 | h1
  · exact ⟨g, mul_inv_eq_one.1 h1⟩
  · obtain ⟨j, hj⟩ := exists_inverting hLq ht hZ π hπ hker h₂
    have hg' : g * ℓ₁ * g⁻¹ = ℓ₂⁻¹ := by
      calc g * ℓ₁ * g⁻¹ = (g * ℓ₁ * g⁻¹ * ℓ₂⁻¹) * ℓ₂ := by group
        _ = t * ℓ₂ := by rw [h1]
        _ = ℓ₂⁻¹ := t_mul_eq_inv ht h₂
    refine ⟨j * g, ?_⟩
    calc j * g * ℓ₁ * (j * g)⁻¹ = j * (g * ℓ₁ * g⁻¹) * j⁻¹ := by group
      _ = j * ℓ₂⁻¹ * j⁻¹ := by rw [hg']
      _ = (j * ℓ₂ * j⁻¹)⁻¹ := by group
      _ = ℓ₂ := by rw [hj, inv_inv]

theorem exists_twisted_commutator_outer
    {L : Type} [Group L] [Finite L] {t : L} {π : L →* NativeSporadic.M12}
    (hc : CFSG.GH74.KGroups.TwoM12.IsCover t π) (hq : CFSG.Assembly.IsQuasisimple L)
    (σ : MulAut L) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hout : ¬ ∃ u : L, ∀ x : L, σ x = u * x * u⁻¹) {z : L} (hzσ : σ z = z) (hz2 : orderOf z = 2) :
    ∃ l : L, l * (σ l)⁻¹ = z := by
  classical
  have hσ2' : σ ^ 2 = 1 := by rw [sq]; exact hσ2
  have hσord : orderOf σ = 2 := orderOf_eq_prime hσ2' hσ1
  let s : ↥(zpowers σ) := ⟨σ, mem_zpowers σ⟩
  have hs2 : s * s = 1 := Subtype.ext hσ2
  have hs1 : s ≠ 1 := fun h => hσ1 (congrArg Subtype.val h)
  let ι : L →* CFSG.GH74.KGroups.TwoM12.Ext σ := SemidirectProduct.inl
  let L' : Subgroup (CFSG.GH74.KGroups.TwoM12.Ext σ) := ι.range
  have hι : Function.Injective ι := SemidirectProduct.inl_injective
  let eL : L ≃* L' := MonoidHom.ofInjective hι
  have hL'ker : L' = SemidirectProduct.rightHom.ker := SemidirectProduct.range_inl_eq_ker_rightHom
  have hL'N : L'.Normal := by rw [hL'ker]; exact MonoidHom.normal_ker _
  let p : CFSG.GH74.KGroups.TwoM12.Ext σ := SemidirectProduct.inr s
  have hpact : ∀ x : L, p * ι x * p⁻¹ = ι (σ x) := fun x => by
    have := SemidirectProduct.inl_aut (φ := (zpowers σ).subtype) s x
    simpa using this.symm
  have hp2 : p * p = 1 := by
    have h := map_mul (SemidirectProduct.inr : ↥(zpowers σ) →* CFSG.GH74.KGroups.TwoM12.Ext σ) s s
    rw [hs2, map_one] at h
    exact h.symm
  have hpL : p ∉ L' := by
    intro hp
    rw [hL'ker, MonoidHom.mem_ker] at hp
    have h1 : SemidirectProduct.rightHom p = s := SemidirectProduct.rightHom_inr s
    exact hs1 (h1.symm.trans hp)
  have hporder : orderOf p = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hp2) fun h => hpL (h ▸ L'.one_mem)
  let π' : L' →* NativeSporadic.M12 := π.comp eL.symm.toMonoidHom
  have hπ' : Function.Surjective π' := hc.surjective.comp eL.symm.surjective
  let t' : L' := eL t
  have ht' : orderOf t' = 2 := (MulEquiv.orderOf_eq eL t).trans hc.orderOf_t
  have hZ' : center L' = zpowers t' := by
    have h1 := Subgroup.map_center_eq eL
    rw [hc.center_eq, MonoidHom.map_zpowers] at h1
    exact h1.symm
  have hker' : π'.ker = zpowers t' := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : eL.symm x ∈ π.ker := hx
      rw [hc.ker_eq] at h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      apply eL.symm.injective
      rw [map_zpow, MulEquiv.symm_apply_apply]
      exact hk
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h1 : eL.symm (t' ^ k) ∈ π.ker := by
        rw [hc.ker_eq, map_zpow, MulEquiv.symm_apply_apply]
        exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
      exact h1
  have hkerZ' : π'.ker = center L' := hker'.trans hZ'.symm
  have hLq' : CFSG.Assembly.IsQuasisimple L' :=
    CFSG.GH74.KGroups.TwoM12.isQuasisimple_of_mulEquiv' eL hq
  have htH : ((t' : L') : CFSG.GH74.KGroups.TwoM12.Ext σ) = ι t := rfl
  have hCL : centralizer (L' : Set (CFSG.GH74.KGroups.TwoM12.Ext σ)) =
      zpowers ((t' : L') : CFSG.GH74.KGroups.TwoM12.Ext σ) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx
      have hcom : ∀ y : L, y * x.left = x.left * (x.right : MulAut L) y := fun y => by
        have h1 := congrArg SemidirectProduct.left (hx (ι y) ⟨y, rfl⟩)
        exact h1
      have hr : x.right = 1 ∨ x.right = s := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.right.2
        have h2 : (x.right : MulAut L) = σ ^ k := hk.symm
        have hmod : σ ^ k = σ ^ (k % 2) := by
          have := zpow_mod_orderOf σ k
          rw [hσord] at this
          simpa using this.symm
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · left
          apply Subtype.ext
          show (x.right : MulAut L) = 1
          rw [h2, hmod, h, zpow_zero]
        · right
          apply Subtype.ext
          show (x.right : MulAut L) = σ
          rw [h2, hmod, h, zpow_one]
      rcases hr with hr | hr
      · have hxl : x = ι x.left := by
          have := SemidirectProduct.inl_left_mul_inr_right x
          rw [hr, map_one, mul_one] at this
          exact this.symm
        have hlc : x.left ∈ center L := by
          rw [Subgroup.mem_center_iff]
          intro y
          have := hcom y
          rw [hr] at this
          simpa using this
        rw [hc.center_eq] at hlc
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hlc
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        rw [htH, ← map_zpow, hk]
        exact hxl.symm
      · exfalso
        apply hout
        refine ⟨x.left⁻¹, fun y => ?_⟩
        have h4 : y * x.left = x.left * σ y := by
          have := hcom y
          rw [hr] at this
          exact this
        calc σ y = x.left⁻¹ * (x.left * σ y) := by group
          _ = x.left⁻¹ * (y * x.left) := by rw [h4]
          _ = x.left⁻¹ * y * x.left⁻¹⁻¹ := by group
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      rw [htH, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hc.t_mem_center y]
  have hQ : Nonempty (L' ⧸ center L' ≃* NativeSporadic.M12) :=
    ⟨CFSG.ComponentClassification.CentralCover.quotientEquivOfKerEqCenter π' hπ' hkerZ'⟩
  obtain ⟨-, hconj, -⟩ :=
    ctss_m12_central_double_cover_external_involution_conjugacy_frontier hLq' ht' hZ' hQ hCL
  have hιz2 : ι z * ι z = 1 := by
    rw [← map_mul, ← sq, ← hz2, pow_orderOf_eq_one, map_one]
  have hpz : p * ι z * p⁻¹ = ι z := by rw [hpact z, hzσ]
  have hιzL : ι z ∈ L' := ⟨z, rfl⟩
  have hyL : p * ι z ∉ L' := fun hmem => hpL ((L'.mul_mem_cancel_right hιzL).1 hmem)
  have hy2 : p * ι z * (p * ι z) = 1 := by
    calc p * ι z * (p * ι z) = (p * ι z * p⁻¹) * (p * p) * ι z := by group
      _ = 1 := by rw [hpz, hp2, mul_one, hιz2]
  have hyord : orderOf (p * ι z) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hy2) fun h1 => hyL (h1 ▸ L'.one_mem)
  obtain ⟨l, hl⟩ := hconj p (p * ι z) hpL hporder hyL hyord
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : L, ι l₀ = (l : CFSG.GH74.KGroups.TwoM12.Ext σ) := l.2
  refine ⟨l₀, ?_⟩
  rw [← hl₀] at hl
  have h1 : ι l₀ * p * (ι l₀)⁻¹ = ι (l₀ * (σ l₀)⁻¹) * p := by
    have hinv : p * (ι l₀)⁻¹ * p⁻¹ = (ι (σ l₀))⁻¹ := by
      rw [← hpact l₀]
      group
    calc ι l₀ * p * (ι l₀)⁻¹ = ι l₀ * (p * (ι l₀)⁻¹ * p⁻¹) * p := by group
      _ = ι l₀ * (ι (σ l₀))⁻¹ * p := by rw [hinv]
      _ = ι (l₀ * (σ l₀)⁻¹) * p := by rw [map_mul, map_inv]
  have h2 : p * ι z = ι z * p := by
    calc p * ι z = (p * ι z * p⁻¹) * p := by group
      _ = ι z * p := by rw [hpz]
  rw [h1, h2] at hl
  exact hι (mul_right_cancel hl)

theorem exists_twisted_commutator
    {L : Type} [Group L] [Finite L] (h : CFSG.GH74.E2.Shape2M12 L) (σ : MulAut L) (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) {P : Subgroup L} (hP : ⁅P, P⁆ = P) (hP60 : Nat.card ↥P = 60)
    (hPσ : ∀ x ∈ P, σ x = x) {z : L} (hzP : z ∈ P) (hz2 : orderOf z = 2) :
    ∃ l : L, l * (σ l)⁻¹ = z := by
  obtain ⟨t, π, hc⟩ := CFSG.GH74.KGroups.TwoM12.exists_isCover h
  have hq : CFSG.Assembly.IsQuasisimple L := ⟨Group.isPerfect_def.1 h.1.1, h.1.2.1⟩
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := (orderOf_eq_prime_iff.1 hc.orderOf_t).2
  by_cases hin : ∃ u : L, ∀ x : L, σ x = u * x * u⁻¹
  · obtain ⟨u, hu⟩ := hin
    have huu : u * u ∈ center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : σ (σ g) = g := by
        have := congrArg (fun f : MulAut L => f g) hσ2
        simpa using this
      rw [hu, hu] at h1
      have h2 : u * (u * g * u⁻¹) * u⁻¹ = g := h1
      calc g * (u * u) = (u * (u * g * u⁻¹) * u⁻¹) * (u * u) := by rw [h2]
        _ = (u * u) * g := by group
    have hPu : ∀ x ∈ P, x * u = u * x := by
      intro x hx
      have h1 := hPσ x hx
      rw [hu] at h1
      calc x * u = (u * x * u⁻¹) * u := by rw [h1]
        _ = u * x := by group
    rcases eq_one_or_eq_of_mem_zpowers hc.orderOf_t (hc.center_eq ▸ huu) with h1 | h1
    ·
      exfalso
      have hπuu : π u * π u = 1 := by rw [← map_mul, h1, map_one]
      have hπu1 : π u ≠ 1 := by
        intro h1'
        have hu_ker : u ∈ π.ker := h1'
        rw [hc.ker_eq, ← hc.center_eq] at hu_ker
        apply hσ1
        ext x
        rw [hu, MulAut.one_apply]
        have := Subgroup.mem_center_iff.1 hu_ker x
        calc u * x * u⁻¹ = x * u * u⁻¹ := by rw [← this]
          _ = x := by group
      have hord : orderOf (π u) = 2 := orderOf_eq_prime (by rw [sq]; exact hπuu) hπu1
      obtain ⟨hfc, -, hlift0⟩ :=
        m12_double_cover_involution_lift_orders hq hc.orderOf_t hc.center_eq π hc.surjective hc.ker_eq
      have hfour : fixedCount (π u) = 4 := by
        rcases hfc _ hord with h4 | h0
        · exact h4
        · exfalso
          have hut := (hlift0 u hord h0).1
          rw [sq, h1] at hut
          exact ht1 hut.symm
      obtain ⟨g, hg⟩ := conj_elemR_of_fixedCount_four (π u) hord hfour
      obtain ⟨g', rfl⟩ := hc.surjective g
      obtain ⟨hP', hPu', hcard⟩ := CFSG.GH74.KGroups.TwoM12.conj_data (u := u) g' hP hPu
      have hu' : π (g'⁻¹ * u * g') = elemR := by
        rw [map_mul, map_mul, map_inv, ← hg]
        group
      have hle := CFSG.GH74.KGroups.TwoM12.card_le_two_of_comm_r hc hu' hP' hPu'
      rw [hcard, hP60] at hle
      omega
    ·
      have hu2 : u ^ 2 = t := by rw [sq]; exact h1
      have hzu : z * u = u * z := hPu z hzP
      have hzusq : (z * u) ^ 2 = t := by
        rw [Commute.mul_pow hzu, hu2, sq z, hzz, one_mul]
      obtain ⟨g, hg⟩ :=
        exists_conj_of_sq_eq hq hc.orderOf_t hc.center_eq π hc.surjective hc.ker_eq hu2 hzusq
      refine ⟨g, ?_⟩
      rw [hu g]
      calc g * (u * g * u⁻¹)⁻¹ = (g * u * g⁻¹) * u⁻¹ := by group
        _ = z * u * u⁻¹ := by rw [hg]
        _ = z := by group
  · exact exists_twisted_commutator_outer hc hq σ hσ2 hσ1 hin (hPσ z hzP) hz2

end CFSG.GH74.GLS.C3.Layer1.PumpElim
