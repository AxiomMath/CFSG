module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldTorus
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndOddQuot
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.Outer)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)

section Generic

variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
theorem odd_orderOf_of_mem_center (hZ : Odd (Nat.card (center M))) {z : M}
    (hz : z ∈ center M) : Odd (orderOf z) := by
  have h := orderOf_dvd_natCard (⟨z, hz⟩ : center M)
  rw [Subgroup.orderOf_mk] at h
  exact Odd.of_dvd_nat hZ h

omit [Finite M] in
theorem exists_fixed_mul_inv_mem_center (hZ : Odd (Nat.card (center M))) (β : MulAut M)
    (hβ : ∀ x, β (β x) = x) {m : M} (hm : β m * m⁻¹ ∈ center M) :
    ∃ m' : M, β m' = m' ∧ m' * m⁻¹ ∈ center M := by
  set z := β m * m⁻¹ with hzdef
  have hβm : β m = z * m := by rw [hzdef, inv_mul_cancel_right]
  have hβz : β z = z⁻¹ := by
    rw [hzdef, map_mul, map_inv, hβ, mul_inv_rev, inv_inv]
  obtain ⟨j, hj⟩ := odd_orderOf_of_mem_center hZ hm
  have hzn : z ^ (2 * j + 1) = 1 := by
    rw [← hj]
    exact pow_orderOf_eq_one z
  refine ⟨z ^ (j + 1) * m, ?_, ?_⟩
  · rw [map_mul, map_pow, hβz, hβm, inv_pow, ← mul_assoc]
    congr 1
    rw [inv_mul_eq_iff_eq_mul, ← pow_add, show j + 1 + (j + 1) = (2 * j + 1) + 1 by ring,
      pow_succ, hzn, one_mul]
  · rw [mul_inv_cancel_right]
    exact pow_mem hm _

omit [Finite M] in
theorem exists_sq_eq_one_mul_inv_mem_center (hZ : Odd (Nat.card (center M))) {m : M}
    (hm : m ^ 2 ∈ center M) : ∃ w : M, w ^ 2 = 1 ∧ w * m⁻¹ ∈ center M := by
  obtain ⟨j, hj⟩ := odd_orderOf_of_mem_center hZ hm
  have hzn : (m ^ 2) ^ (2 * j + 1) = 1 := by
    rw [← hj]
    exact pow_orderOf_eq_one _
  have hzj : (m ^ 2) ^ j ∈ center M := pow_mem hm j
  refine ⟨(m ^ 2) ^ j * m, ?_, by rw [mul_inv_cancel_right]; exact hzj⟩
  have hc : m * (m ^ 2) ^ j = (m ^ 2) ^ j * m := mem_center_iff.1 hzj m
  calc ((m ^ 2) ^ j * m) ^ 2 = (m ^ 2) ^ j * (m * (m ^ 2) ^ j) * m := by
        rw [sq, mul_assoc, mul_assoc, mul_assoc]
    _ = (m ^ 2) ^ j * ((m ^ 2) ^ j * m) * m := by rw [hc]
    _ = (m ^ 2) ^ (2 * j) * m ^ 2 := by
        rw [two_mul, pow_add, sq m, mul_assoc, mul_assoc, mul_assoc]
    _ = (m ^ 2) ^ (2 * j + 1) := (pow_succ _ _).symm
    _ = 1 := hzn

omit [Finite M] in
theorem eq_conj_of_mk_eq [Group.IsPerfect M] (β : MulAut M) (m : M)
    (h : ∀ x, (QuotientGroup.mk (β x) : M ⧸ center M) = QuotientGroup.mk (m * x * m⁻¹)) :
    ∀ x, β x = m * x * m⁻¹ := by
  have hφ := LinearPilot.eq_of_comp_eq_of_ker_le_center (S := M) (E := M) (Q := M ⧸ center M)
    (p := QuotientGroup.mk' (center M)) (by rw [QuotientGroup.ker_mk'])
    (φ := β.toMonoidHom) (ψ := (MulAut.conj m).toMonoidHom) (fun x => by
      simpa only [MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, MulAut.conj_apply] using h x)
  intro x
  have := DFunLike.congr_fun hφ x
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

omit [Finite M] in
theorem exists_commute_of_mk_commute (hZ : Odd (Nat.card (center M))) {w : M} (hw : w ^ 2 = 1)
    {m : M} (hm : (QuotientGroup.mk (w * m) : M ⧸ center M) = QuotientGroup.mk (m * w)) :
    ∃ m' : M, w * m' = m' * w ∧ m' * m⁻¹ ∈ center M := by
  have hww : ∀ x, MulAut.conj w (MulAut.conj w x) = x := fun x => by
    have hw' : w * w = 1 := by rw [← sq, hw]
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw'
    simp only [MulAut.conj_apply, hwi]
    rw [← mul_assoc, ← mul_assoc, hw', one_mul, mul_assoc, hw', mul_one]
  have hm' : MulAut.conj w m * m⁻¹ ∈ center M := by
    have h := QuotientGroup.eq.1 hm.symm
    set c := (m * w)⁻¹ * (w * m) with hcdef
    have hwm : w * m = (m * w) * c := by rw [hcdef]; group
    have hc' : (m * w) * c = c * (m * w) := mem_center_iff.1 h (m * w)
    have heq : w * m * w⁻¹ * m⁻¹ = c := by
      calc w * m * w⁻¹ * m⁻¹ = (w * m) * (m * w)⁻¹ := by group
        _ = (m * w) * c * (m * w)⁻¹ := by rw [hwm]
        _ = c * (m * w) * (m * w)⁻¹ := by rw [hc']
        _ = c := by group
    rw [MulAut.conj_apply, heq]
    exact h
  obtain ⟨m', hm'1, hm'2⟩ := exists_fixed_mul_inv_mem_center hZ (MulAut.conj w) hww hm'
  refine ⟨m', ?_, hm'2⟩
  rw [MulAut.conj_apply] at hm'1
  calc w * m' = w * m' * w⁻¹ * w := by group
    _ = m' * w := by rw [hm'1]

omit [Finite M] in
theorem mk_eq_of_mul_inv_mem_center {a b : M} (h : a * b⁻¹ ∈ center M) :
    (QuotientGroup.mk a : M ⧸ center M) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq, show a⁻¹ * b = b⁻¹ * (a * b⁻¹)⁻¹ * b⁻¹⁻¹ by group]
  exact (inferInstance : (center M).Normal).conj_mem _ (inv_mem h) b⁻¹

end Generic

section Action

variable {G : Type} [Group G]

theorem normalizerMonoidHom_apply_apply_of_orderOf {M : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htM : t ∈ normalizer (M : Set G)) (x : M) :
    M.normalizerMonoidHom ⟨t, htM⟩ (M.normalizerMonoidHom ⟨t, htM⟩ x) = x := by
  have h := congrArg (fun γ : MulAut M => γ x) (normalizerMonoidHom_sq_eq_one_of_orderOf ht htM)
  simpa [sq] using h

theorem map_subgroupOf_centralizer_eq_fixSubgroup {M : Subgroup G} {X : Type*} [Group X]
    (hZ : Odd (Nat.card (center M))) (eM : M ⧸ center M ≃* X) {t : G} (ht : orderOf t = 2)
    (htM : t ∈ normalizer (M : Set G)) :
    ((centralizer ({t} : Set G)).subgroupOf M).map
        (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))) =
      fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) := by
  set β := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβ : ∀ m : M, ((β m : M) : G) = t * m * t⁻¹ := fun m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ m
  have hfixiff : ∀ m : M, β m = m ↔ m ∈ (centralizer ({t} : Set G)).subgroupOf M := by
    intro m
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := congrArg Subtype.val h
      rw [hβ] at h1
      calc (m : G) * t = t * (m : G) * t⁻¹ * t := by rw [h1]
        _ = t * m := by group
    · intro h
      apply Subtype.ext
      rw [hβ, ← h, mul_inv_cancel_right]
  have hρ : ∀ m : M, normalizerQuotMulAut eM ⟨t, htM⟩ (eM (QuotientGroup.mk' (center M) m)) =
      eM (QuotientGroup.mk' (center M) (β m)) := fun m =>
    normalizerQuotMulAut_apply eM ⟨t, htM⟩ m
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    change normalizerQuotMulAut eM ⟨t, htM⟩ _ = _
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hρ, (hfixiff m).2 hm]
    rfl
  · intro c hc
    have hc' : normalizerQuotMulAut eM ⟨t, htM⟩ c = c := hc
    obtain ⟨q₁, rfl⟩ := eM.surjective c
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (center M) q₁
    rw [hρ] at hc'
    have hm : β m * m⁻¹ ∈ center M := by
      have h1 := eM.injective hc'
      have h2 := QuotientGroup.eq.1 h1.symm
      have h3 : β m * m⁻¹ = m * (m⁻¹ * β m) * m⁻¹ := by group
      rw [h3]
      exact (inferInstance : (center M).Normal).conj_mem _ h2 m
    obtain ⟨m', hm'1, hm'2⟩ := exists_fixed_mul_inv_mem_center hZ β
      (normalizerMonoidHom_apply_apply_of_orderOf ht htM) hm
    refine ⟨m', (hfixiff m').1 hm'1, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [mk_eq_of_mul_inv_mem_center hm'2]

theorem normalizerQuotMulAut_sq_eq_one {M : Subgroup G} {X : Type*} [Group X]
    (eM : M ⧸ center M ≃* X) {t : G} (ht : orderOf t = 2) (htM : t ∈ normalizer (M : Set G)) :
    normalizerQuotMulAut eM ⟨t, htM⟩ ^ 2 = 1 := by
  have ht2 : (⟨t, htM⟩ : normalizer (M : Set G)) ^ 2 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, ← ht, pow_orderOf_eq_one]; rfl)
  rw [← map_pow, ht2, map_one]

@[expose] noncomputable def coverConjugateEquiv (G₀ : Subgroup G) (g : G) :
    G₀ ≃* CFSG.conjugate G₀ g :=
  G₀.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

@[expose] noncomputable def coverConjugateQuotientCenterEquiv (G₀ : Subgroup G) (g : G) :
    G₀ ⧸ center G₀ ≃* CFSG.conjugate G₀ g ⧸ center (CFSG.conjugate G₀ g) :=
  QuotientGroup.congr (center G₀) (center (CFSG.conjugate G₀ g)) (coverConjugateEquiv G₀ g)
    (Subgroup.map_center_eq (coverConjugateEquiv G₀ g))

theorem commutator_conjugate_eq {G₀ : Subgroup G} (hG₀ : ⁅G₀, G₀⁆ = G₀) (g : G) :
    ⁅CFSG.conjugate G₀ g, CFSG.conjugate G₀ g⁆ = CFSG.conjugate G₀ g := by
  rw [CFSG.conjugate, ← map_commutator, hG₀]

theorem card_center_conjugate (G₀ : Subgroup G) (g : G) :
    Nat.card (center (CFSG.conjugate G₀ g)) = Nat.card (center G₀) := by
  rw [← Subgroup.map_center_eq (coverConjugateEquiv G₀ g),
    card_map_of_injective (coverConjugateEquiv G₀ g).injective]

end Action


section Quot

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_inner_quot_E6 (hset : StandardSetting G L) {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ⧸ center M ≃* adjointGroup .E6 K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    normalizerQuotMulAut eM ⟨t, htM⟩ ∉
      (MulAut.conj : adjointGroup .E6 K₂ →* MulAut (adjointGroup .E6 K₂)).range := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK₂
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  rintro ⟨c, hc⟩
  set β := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβ : ∀ m : M, ((β m : M) : G) = t * m * t⁻¹ := fun m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ m
  obtain ⟨q₀, hq₀⟩ := eM.surjective c
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q₀
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hMp
  have hkey : ∀ x : M,
      (QuotientGroup.mk (β x) : M ⧸ center M) = QuotientGroup.mk (m * x * m⁻¹) := by
    intro x
    apply eM.injective
    have h1 := normalizerQuotMulAut_apply eM ⟨t, htM⟩ x
    rw [← hc, MulAut.conj_apply, ← hq₀] at h1
    simp only [QuotientGroup.mk'_apply] at h1
    rw [← h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv]
  have hβm := eq_conj_of_mk_eq β m hkey
  have hm2 : m ^ 2 ∈ center M := by
    rw [mem_center_iff]
    intro g
    have h := normalizerMonoidHom_apply_apply_of_orderOf ht htM g
    rw [← hβdef, hβm (β g), hβm g] at h
    calc g * m ^ 2 = (m * (m * g * m⁻¹) * m⁻¹) * m ^ 2 := by rw [h]
      _ = m ^ 2 * g := by rw [sq]; group
  obtain ⟨w, hw2, hwm⟩ := exists_sq_eq_one_mul_inv_mem_center hZ hm2
  have hβw : ∀ x, β x = w * x * w⁻¹ := by
    intro x
    rw [hβm]
    have hz := mem_center_iff.1 hwm (m * x * m⁻¹)
    calc m * x * m⁻¹ = (m * x * m⁻¹) * (w * m⁻¹) * (w * m⁻¹)⁻¹ := by group
      _ = (w * m⁻¹) * (m * x * m⁻¹) * (w * m⁻¹)⁻¹ := by rw [hz]
      _ = w * x * w⁻¹ := by group
  obtain ⟨w', hw'2, hw'C⟩ : ∃ w' : M, w' ^ 2 = 1 ∧ w' ∉ center M ∧
      ∀ x : M, w' * x = x * w' → t * (x : G) * t⁻¹ = x := by
    by_cases hw1 : w = 1
    · have hcentral : ∀ x : M, t * (x : G) * t⁻¹ = x := fun x => by
        have h1 : β x = x := by rw [hβw, hw1, one_mul, inv_one, mul_one]
        rw [← hβ, h1]
      obtain ⟨u, hu⟩ : ∃ u : adjointGroup .E6 K₂, orderOf u = 2 :=
        ⟨_, orderOf_pinnedX_one_adjointGroup (τ := .E6) (Pi.single (0 : Fin 6) 1)⟩
      obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (eM.symm u)
      have hm₀2 : m₀ ^ 2 ∈ center M := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hm₀, ← map_pow, ← hu,
          pow_orderOf_eq_one, map_one]
      obtain ⟨w₀, hw₀2, hw₀m⟩ := exists_sq_eq_one_mul_inv_mem_center hZ hm₀2
      refine ⟨w₀, hw₀2, fun hw₀Z => ?_, fun x _ => hcentral x⟩
      have h1 : (QuotientGroup.mk w₀ : M ⧸ center M) = 1 := (QuotientGroup.eq_one_iff _).2 hw₀Z
      rw [mk_eq_of_mul_inv_mem_center hw₀m, hm₀] at h1
      have hu1 : u = 1 := by rw [← eM.apply_symm_apply u, h1, map_one]
      rw [hu1, orderOf_one] at hu
      exact absurd hu (by norm_num)
    · refine ⟨w, hw2, fun hwZ => ?_, fun x hx => ?_⟩
      · have h := odd_orderOf_of_mem_center hZ hwZ
        rw [orderOf_eq_prime hw2 hw1] at h
        exact absurd h (by decide)
      · have h1 : β x = x := by rw [hβw, hx, mul_inv_cancel_right]
        rw [← hβ, h1]
  set ŵ : adjointGroup .E6 K₂ := eM (QuotientGroup.mk w') with hŵdef
  have hŵ : orderOf ŵ = 2 := by
    refine orderOf_eq_prime ?_ fun h => hw'C.1 ?_
    · rw [hŵdef, ← map_pow, ← QuotientGroup.mk_pow, hw'2, QuotientGroup.mk_one, map_one]
    · rw [← QuotientGroup.eq_one_iff]
      apply eM.injective
      rw [map_one]
      exact h
  have hle : centralizer ({ŵ} : Set (adjointGroup .E6 K₂)) ≤
      (centralizer ({w'} : Set M)).map (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))) := by
    intro c hc
    obtain ⟨q₁, hq₁⟩ := eM.surjective c
    obtain ⟨m₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    have hcom : (QuotientGroup.mk (w' * m₁) : M ⧸ center M) = QuotientGroup.mk (m₁ * w') := by
      apply eM.injective
      have h := mem_centralizer_singleton_iff.1 hc
      rw [← hq₁] at h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul]
      exact h.symm
    obtain ⟨m', hm'w, hm'm⟩ := exists_commute_of_mk_commute hZ hw'2 hcom
    refine ⟨m', mem_centralizer_singleton_iff.2 hm'w.symm, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
    rw [mk_eq_of_mul_inv_mem_center hm'm, hq₁]
  have hleG : (centralizer ({w'} : Set M)).map M.subtype ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxw := mem_centralizer_singleton_iff.1 hx
    have h := hw'C.2 x hxw.symm
    rw [mem_centralizer_singleton_iff]
    change (x : G) * t = t * x
    calc (x : G) * t = t * (x : G) * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  have hdvd : 2 ^ (26 * (2 * f)) ∣ Nat.card (centralizer ({t} : Set G)) := by
    refine (two_pow_dvd_card_centralizer_E6 hK₂ hŵ).trans ?_
    refine (card_dvd_of_le hle).trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [← card_map_of_injective M.subtype_injective]
    exact card_dvd_of_le hleG
  have hb := factorization_card_le_of_le_centralizer_E6 hset.standard hK e ht hKt
    (le_refl (centralizer ({t} : Set G)))
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  omega


theorem inf_centralizer_eq_of_mem_normalizer_E6_cover (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (eM : M ⧸ center M ≃* adjointGroup .E6 K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    (∃ σ : K₂ ≃+* K₂, σ ^ 2 = 1 ∧ σ ≠ 1 ∧ (∀ c, σ c = c ^ (2 ^ f)) ∧
      ∃ φ : MulAut (adjointGroup .E6 K₂),
        φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = entrywiseAdjointAut .E6 σ) ∧
    M ⊓ centralizer ({t} : Set G) = L := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK₂
  have : Finite (adjointGroup .E6 K₂) := by
    have : Finite (ModGL Tag.E6 K₂) := finite_modGL
    infer_instance
  have hf : 1 ≤ f := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K₂ := by
    rw [hK₂]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨3, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).1⟩⟩
  have htC : t ∈ centralizer (L : Set G) := (hKt ▸ mem_zpowers t :
    t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).1
  set C := adjointGroup TwistTag.E6.tag K₂ with hCdef
  set α : MulAut C := normalizerQuotMulAut eM ⟨t, htM⟩ with hαdef
  have hα2 : α ^ 2 = 1 := normalizerQuotMulAut_sq_eq_one eM ht htM
  have hαo : α ∉ OuterAutomorphisms.inner C := not_inner_quot_E6 hset hK e ht hKt hMp hZ hK₂ eM htM
  set π₀ : M →* C := eM.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπ₀
  set Xm : Subgroup M := (centralizer ({t} : Set G)).subgroupOf M with hXm
  set X : Subgroup G := M ⊓ centralizer ({t} : Set G) with hXdef
  have hXmX : Xm.map M.subtype = X := by
    rw [hXm, subgroupOf_map_subtype, inf_comm]
  have hXt : X ≤ centralizer ({t} : Set G) := inf_le_right
  have hcardX : Nat.card Xm = Nat.card X := by
    rw [← hXmX, card_map_of_injective M.subtype_injective]
  have hfix : Xm.map π₀ = fixSubgroup α := map_subgroupOf_centralizer_eq_fixSubgroup hZ eM ht htM
  have hcardfix : Nat.card (fixSubgroup α) ∣ Nat.card X := by
    rw [← hfix, ← hcardX]
    exact Subgroup.card_map_dvd _ _
  have hPX : (perfectCore Xm).map M.subtype = perfectCore X := by
    rw [CFSG.Quasithin.map_perfectCore, hXmX]
  have hPfix : (perfectCore Xm).map π₀ = perfectCore (fixSubgroup α) := by
    rw [CFSG.Quasithin.map_perfectCore, hfix]
  have hPL : perfectCore X ≤ L :=
    std_perfect_le hset hOut htC ht (CFSG.Quasithin.perfectCore_perfect X)
      ((CFSG.Quasithin.perfectCore_le X).trans hXt)
  have hcardP : Nat.card (perfectCore (fixSubgroup α)) ∣ Nat.card L := by
    rw [← hPfix]
    refine (Subgroup.card_map_dvd _ _).trans ?_
    rw [← card_map_of_injective M.subtype_injective, hPX]
    exact card_dvd_of_le hPL
  have hgraph : ∀ β₀ : MulAut C, (∃ φ, φ * α * φ⁻¹ = β₀) →
      Nat.card K₂ ^ 20 ∣ Nat.card (fixSubgroup β₀) → False := by
    rintro β₀ ⟨φ, rfl⟩ hdvd
    rw [card_fixSubgroup_conj, hK₂, ← pow_mul] at hdvd
    have hb := factorization_card_le_of_le_centralizer_E6 hset.standard hK e ht hKt hXt
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1
      (hdvd.trans hcardfix)
    have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
    omega
  have hDL : ∀ β₀ : MulAut C, ∀ φ, φ * α * φ⁻¹ = β₀ →
      (⁅⁅fixSubgroup β₀, fixSubgroup β₀⁆, ⁅fixSubgroup β₀, fixSubgroup β₀⁆⁆ : Subgroup C) =
        ⁅fixSubgroup β₀, fixSubgroup β₀⁆ →
      Nat.card (⁅fixSubgroup β₀, fixSubgroup β₀⁆ : Subgroup C) ∣
        Nat.card (perfectCore (fixSubgroup α)) := by
    rintro β₀ φ rfl hperf
    set D : Subgroup C := ⁅fixSubgroup α, fixSubgroup α⁆ with hD
    have hDφ : D.map φ.toMonoidHom = ⁅fixSubgroup (φ * α * φ⁻¹), fixSubgroup (φ * α * φ⁻¹)⁆ :=
      map_commutator_fixSubgroup_conj φ α
    have hDD : ⁅D, D⁆ = D := by
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [map_commutator, hDφ, hperf]
    rw [← hDφ, card_map_of_injective φ.injective]
    exact card_dvd_of_le (CFSG.Quasithin.le_perfectCore_of_perfect
      (Subgroup.commutator_le_self _) hDD)
  have hLcard : Nat.card L = ordE6 (2 ^ f) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hK]
  rcases outer_involution_cases_E6 (by omega : 1 ≤ 2 * f) K₂ hK₂ α hα2 hαo with
    ⟨η, hη, ⟨φ, hφ⟩ | ⟨ht', φ, hφ⟩⟩ | ⟨σ, hσ2, hσ1, ⟨φ, hφ⟩ | ⟨φ, hφ⟩⟩
  · exact (hgraph η ⟨φ, hφ⟩ (card_pow_twenty_dvd_card_fixSubgroup_graph_E6 hq η hη).1).elim
  · exact (hgraph _ ⟨φ, hφ⟩ ((card_pow_twenty_dvd_card_fixSubgroup_graph_E6 hq η hη).2 ht')).elim
  ·
    obtain ⟨hD, hperf, hcard⟩ := commutator_fixSubgroup_field_E6 hf hK₂ σ hσ2 hσ1
    have hdvd := hDL _ φ hφ (by rw [hD]; exact hperf)
    rw [hD, hcard] at hdvd
    have hPeq : perfectCore X = L := by
      refine Subgroup.eq_of_le_of_card_ge hPL ?_
      rw [hLcard, ← hPX, card_map_of_injective M.subtype_injective]
      refine Nat.le_of_dvd Nat.card_pos (hdvd.trans ?_)
      rw [← hPfix]
      exact Subgroup.card_map_dvd _ _
    have hLX : L ≤ X := hPeq ▸ CFSG.Quasithin.perfectCore_le X
    have hLM : L ≤ M := hLX.trans inf_le_left
    have hinj : Xm ⊓ π₀.ker = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨hzX, hzk⟩
      have hzZ : z ∈ center M := by
        have h1 : eM (QuotientGroup.mk' (center M) z) = 1 := hzk
        rw [← QuotientGroup.ker_mk' (center M), MonoidHom.mem_ker]
        exact eM.injective (h1.trans (map_one eM).symm)
      have hzt : (z : G) ∈ centralizer ({t} : Set G) := mem_subgroupOf.1 hzX
      have hzL : (z : G) ∈ centralizer (L : Set G) := by
        rw [mem_centralizer_iff]
        intro l hl
        have h1 := mem_center_iff.1 hzZ ⟨l, hLM hl⟩
        exact (congrArg Subtype.val h1)
      have hzz : (z : G) ∈ zpowers t := hKt ▸ ⟨hzL, hzt⟩
      have hzodd := odd_orderOf_of_mem_center hZ hzZ
      have hdvd2 : orderOf z ∣ 2 := by
        rw [← Subgroup.orderOf_coe, ← ht]
        exact orderOf_dvd_of_mem_zpowers hzz
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h2
      · exact orderOf_eq_one_iff.1 h1
      · rw [h2] at hzodd
        exact absurd hzodd (by decide)
    set πX : Xm →* C := π₀.comp Xm.subtype with hπX
    have hπXinj : Function.Injective πX := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro z hz
      have hz' : (z : M) ∈ Xm ⊓ π₀.ker := ⟨z.2, hz⟩
      rw [hinj, mem_bot] at hz'
      exact (mem_bot).2 (Subtype.ext hz')
    have hπXrange : πX.range = Xm.map π₀ := by
      rw [hπX, MonoidHom.range_comp, range_subtype]
    have hcardXfix : Nat.card X = Nat.card (fixSubgroup α) := by
      rw [← hcardX, ← hfix, ← hπXrange]
      exact Nat.card_congr (MonoidHom.ofInjective hπXinj).toEquiv
    have hcardα : Nat.card (fixSubgroup α) = ordE6 (2 ^ f) := by
      rw [← card_fixSubgroup_conj φ α, hφ]
      exact card_fixSubgroup_entrywiseAdjointAut_E6 hf hK₂ σ hσ2 hσ1
    refine ⟨⟨σ, hσ2, hσ1, (field_involution_facts_E6 hf hK₂ σ hσ2 hσ1).1, φ, hφ⟩, ?_⟩
    refine (Subgroup.eq_of_le_of_card_ge hLX ?_).symm
    rw [hcardXfix, hcardα, hLcard]
  ·
    exfalso
    obtain ⟨hD, hperf, hcard⟩ := commutator_fixSubgroup_graphField_E6 hf hK₂ σ hσ2 hσ1
    have hdvd := hDL _ φ hφ (by rw [hD]; exact hperf)
    rw [hD, hcard] at hdvd
    have h := hdvd.trans hcardP
    rw [hLcard] at h
    exact not_ordTwistedE6_dvd_ordE6 hf h

theorem inf_centralizer_conjugate_eq_E6_cover (hset : StandardSetting G L) {f : ℕ} {K : Type}
    [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hG₀p : ⁅G₀, G₀⁆ = G₀) (hZ : Odd (Nat.card (center G₀))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (e₀ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K₂) (h : G)
    (htM : t ∈ normalizer (CFSG.conjugate G₀ h : Set G)) :
    CFSG.conjugate G₀ h ⊓ centralizer ({t} : Set G) = L :=
  (inf_centralizer_eq_of_mem_normalizer_E6_cover hset hK e ht hKt (commutator_conjugate_eq hG₀p h)
    (by rw [card_center_conjugate]; exact hZ) hK₂
    ((coverConjugateQuotientCenterEquiv G₀ h).symm.trans e₀) htM).2

end Quot

end CFSG.SeitzReduction.E6Pilot
