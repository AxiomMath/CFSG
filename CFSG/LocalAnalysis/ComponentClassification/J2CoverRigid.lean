module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverLift
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverData

public section

namespace CFSG.ComponentClassification.J2Cover.Rigid

open CFSG.ComponentClassification.CentralCover CFSG.ComponentClassification.J2Cover.Models

theorem betaP_not_mem_inner : betaP ∉ OuterAutomorphisms.inner Models.P := by
  rintro ⟨g, hg⟩
  have key : ∀ c : Perm315, c ∈ Subgroup.centralizer (Models.P : Set Perm315) → c = 1 := by
    intro c hc
    rw [P_eq_autP, centralizer_P] at hc
    exact Subgroup.mem_bot.1 hc
  have hc : (g : Perm315)⁻¹ * bOut ∈ Subgroup.centralizer (Models.P : Set Perm315) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun α : MulAut Models.P => ((α ⟨x, hx⟩ : Models.P) : Perm315)) hg
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, betaP_coe] at h1
    calc x * ((g : Perm315)⁻¹ * bOut)
        = (g : Perm315)⁻¹ * ((g : Perm315) * x * (g : Perm315)⁻¹) * bOut := by group
      _ = (g : Perm315)⁻¹ * (bOut * x * bOut⁻¹) * bOut := by rw [h1]
      _ = (g : Perm315)⁻¹ * bOut * x := by group
  apply bOut_not_mem
  rw [← inv_mul_eq_one.1 (key _ hc)]
  exact g.2

theorem betaP_mul_self : betaP * betaP = 1 :=
  MulEquiv.ext fun x => Subtype.ext (by
    rw [MulAut.mul_apply, betaP_coe, betaP_coe, bOut_conj_conj]
    rfl)

theorem card_outer_models : Nat.card (OuterAutomorphisms.Outer Models.P) = 2 := by
  rw [Nat.card_congr (OuterAutomorphisms.equivalence Lift.toModels.symm).toEquiv, card_outer_P]

theorem eq_of_ne_one_of_card_eq_two {G : Type*} [Group G] (hG : Nat.card G = 2) {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have := Fintype.ofFinite G
  by_contra hab
  have h3 : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha, Ne.symm hb⟩
  have h4 := Finset.card_le_univ ({1, a, b} : Finset G)
  rw [h3, ← Nat.card_eq_fintype_card, hG] at h4
  omega

theorem exists_mul_conj_eq_betaP {α : MulAut Models.P}
    (hα : α ∉ OuterAutomorphisms.inner Models.P) : ∃ g : Models.P, α * MulAut.conj g = betaP := by
  have h1 : (QuotientGroup.mk α : OuterAutomorphisms.Outer Models.P) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have h2 : (QuotientGroup.mk betaP : OuterAutomorphisms.Outer Models.P) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact betaP_not_mem_inner
  obtain ⟨g, hg⟩ := QuotientGroup.eq.1 (eq_of_ne_one_of_card_eq_two card_outer_models h1 h2)
  exact ⟨g, by rw [hg, mul_inv_cancel_left]⟩

theorem exists_lift_beta {H : Type*} [Group H] {L : Subgroup H} [L.Normal] [Group.IsPerfect L]
    (π : L →* Models.P) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center L)
    (hCL : Subgroup.centralizer (L : Set H) ≤ L) {h₀ : H} (hh₀ : h₀ ∉ L) :
    ∃ q : H, q ∉ L ∧ fullAction π hπ hker q = betaP := by
  obtain ⟨g, hg⟩ := exists_mul_conj_eq_betaP (fullAction_notMem_inner π hπ hker hCL hh₀)
  obtain ⟨l, rfl⟩ := hπ g
  refine ⟨h₀ * l, fun hq => hh₀ ?_, ?_⟩
  · have := L.mul_mem hq (L.inv_mem l.2)
    rwa [mul_inv_cancel_right] at this
  · rw [map_mul, fullAction_coe, hg]

theorem map_mem_center {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {x : G}
    (hx : x ∈ Subgroup.center G) : e x ∈ Subgroup.center G' := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  obtain ⟨w, rfl⟩ := e.surjective y
  rw [← map_mul, ← map_mul, hx w]

theorem center_facts_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h4 : Nat.card (Subgroup.center G') = 4) (hsq : ∀ x ∈ Subgroup.center G', x ^ 2 = 1)
    (hfix : ∀ φ : G' ≃* G', ∀ x ∈ Subgroup.center G', φ x = x) :
    Nat.card (Subgroup.center G) = 4 ∧ (∀ x ∈ Subgroup.center G, x ^ 2 = 1) ∧
      ∀ φ : G ≃* G, ∀ x ∈ Subgroup.center G, φ x = x := by
  refine ⟨?_, fun x hx => e.injective ?_, aut_fix_center_of_mulEquiv e hfix⟩
  · rw [← h4]
    exact Nat.card_congr (Subgroup.centerCongr e).toEquiv
  · rw [map_pow, hsq _ (map_mem_center e hx), map_one]

theorem center_facts_RfN :
    Nat.card (Subgroup.center RfN) = 4 ∧ (∀ x ∈ Subgroup.center RfN, x ^ 2 = 1) ∧
      ∀ φ : RfN ≃* RfN, ∀ x ∈ Subgroup.center RfN, φ x = x :=
  center_facts_of_mulEquiv rfEquiv card_center_Rf center_Rf_sq aut_fix_center_Rf

theorem center_facts_TepsN (ε : ZMod 2) :
    Nat.card (Subgroup.center (TepsN ε)) = 4 ∧ (∀ x ∈ Subgroup.center (TepsN ε), x ^ 2 = 1) ∧
      ∀ φ : TepsN ε ≃* TepsN ε, ∀ x ∈ Subgroup.center (TepsN ε), φ x = x := by
  rcases zmod_two_cases ε with rfl | rfl
  · exact center_facts_of_mulEquiv (tEquiv 0) card_center_T0 center_T0_sq aut_fix_center_T0
  · exact center_facts_of_mulEquiv (tEquiv 1) card_center_T1 center_T1_sq aut_fix_center_T1

theorem mk_zero_mem_center (ε : ZMod 2) {x : RfN} (hx : x ∈ Subgroup.center RfN) :
    (⟨x, 0⟩ : TepsN ε) ∈ Subgroup.center (TepsN ε) := by
  rw [Subgroup.mem_center_iff]
  intro p
  have hτ : TwistExt.tauPow (tDataN ε) p.e x = x := by
    rcases zmod_two_cases p.e with h | h
    · rw [h, TwistExt.tauPow_zero]
    · rw [h, TwistExt.tauPow_one]
      exact aut_fix_center_RfN tauN x hx
  refine TwistExt.ext ?_ (add_comm _ _)
  change p.x * TwistExt.tauPow (tDataN ε) p.e x * TwistExt.zPow (tDataN ε) (ε * p.e * 0) =
    x * TwistExt.tauPow (tDataN ε) 0 p.x * TwistExt.zPow (tDataN ε) (ε * 0 * p.e)
  simp only [hτ, TwistExt.tauPow_zero, mul_zero, zero_mul, TwistExt.zPow_zero, mul_one]
  exact Subgroup.mem_center_iff.1 hx p.x

@[expose] noncomputable def twistHom {H : Type*} [Group H] (j : RfN →* H) (q : H) (ε : ZMod 2)
    (hconj : ∀ y, q * j y * q⁻¹ = j (tauN y)) (hq : q ^ 2 = j (TwistExt.zPow (tDataN ε) ε)) :
    TepsN ε →* H :=
  MonoidHom.mk' (fun p => j p.x * q ^ p.e.val) fun p p' => by
    have K1 : ∀ (e : ZMod 2) (y : RfN),
        q ^ e.val * j y = j (TwistExt.tauPow (tDataN ε) e y) * q ^ e.val := by
      intro e y
      rcases zmod_two_cases e with rfl | rfl
      · rw [TwistExt.tauPow_zero, ZMod.val_zero, pow_zero, one_mul, mul_one]
      · rw [TwistExt.tauPow_one, zmod_two_val_one, pow_one]
        exact mul_inv_eq_iff_eq_mul.1 (hconj y)
    have K2 : ∀ e d : ZMod 2, q ^ e.val * q ^ d.val =
        j (TwistExt.zPow (tDataN ε) (ε * e * d)) * q ^ (e + d).val := by
      intro e d
      rcases zmod_two_cases e with rfl | rfl <;> rcases zmod_two_cases d with rfl | rfl
      · simp [TwistExt.zPow_zero]
      · simp [TwistExt.zPow_zero]
      · simp [TwistExt.zPow_zero]
      · rw [mul_one, mul_one, CentralCover.zmod_two_add_self, ZMod.val_zero, pow_zero, mul_one,
          zmod_two_val_one, pow_one, ← sq, hq]
    change j (p.x * TwistExt.tauPow (tDataN ε) p.e p'.x *
        TwistExt.zPow (tDataN ε) (ε * p.e * p'.e)) * q ^ (p.e + p'.e).val =
      j p.x * q ^ p.e.val * (j p'.x * q ^ p'.e.val)
    rw [map_mul, map_mul]
    calc j p.x * j (TwistExt.tauPow (tDataN ε) p.e p'.x) *
          j (TwistExt.zPow (tDataN ε) (ε * p.e * p'.e)) * q ^ (p.e + p'.e).val
        = j p.x * j (TwistExt.tauPow (tDataN ε) p.e p'.x) * (q ^ p.e.val * q ^ p'.e.val) := by
          rw [K2]
          simp only [mul_assoc]
      _ = j p.x * (q ^ p.e.val * j p'.x) * q ^ p'.e.val := by
          rw [K1]
          simp only [mul_assoc]
      _ = j p.x * q ^ p.e.val * (j p'.x * q ^ p'.e.val) := by simp only [mul_assoc]

theorem twistHom_apply {H : Type*} [Group H] (j : RfN →* H) (q : H) (ε : ZMod 2)
    (hconj : ∀ y, q * j y * q⁻¹ = j (tauN y)) (hq : q ^ 2 = j (TwistExt.zPow (tDataN ε) ε))
    (p : TepsN ε) : twistHom j q ε hconj hq p = j p.x * q ^ p.e.val :=
  rfl

theorem twistHom_mk_zero {H : Type*} [Group H] (j : RfN →* H) (q : H) (ε : ZMod 2)
    (hconj : ∀ y, q * j y * q⁻¹ = j (tauN y)) (hq : q ^ 2 = j (TwistExt.zPow (tDataN ε) ε))
    (x : RfN) : twistHom j q ε hconj hq ⟨x, 0⟩ = j x := by
  rw [twistHom_apply, ZMod.val_zero, pow_zero, mul_one]

theorem twistHom_injective {H : Type*} [Group H] (j : RfN →* H) (q : H) (ε : ZMod 2)
    (hconj : ∀ y, q * j y * q⁻¹ = j (tauN y)) (hq : q ^ 2 = j (TwistExt.zPow (tDataN ε) ε))
    (hj : Function.Injective j) (hqj : ∀ y, j y ≠ q) :
    Function.Injective (twistHom j q ε hconj hq) := by
  refine (injective_iff_map_eq_one _).2 fun p hp => ?_
  rw [twistHom_apply] at hp
  rcases zmod_two_cases p.e with he | he
  · rw [he, ZMod.val_zero, pow_zero, mul_one, ← map_one j] at hp
    exact TwistExt.ext (hj hp) he
  · rw [he, zmod_two_val_one, pow_one] at hp
    exact absurd (by rw [map_inv]; exact (eq_inv_of_mul_eq_one_right hp).symm) (hqj p.x⁻¹)

theorem isElementaryAbelian_center_of {G : Type*} [Group G]
    (h : ∀ w ∈ Subgroup.center G, w ^ 2 = 1) : IsElementaryAbelian 2 (Subgroup.center G) where
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun w =>
    Subtype.ext (by simpa using h w w.2)

theorem factorization_two_pow_mul_4725 (k : ℕ) : (2 ^ k * 4725).factorization 2 = k := by
  rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 4725)]
  simp

theorem exists_sylow_of_model {H M : Type*} [Group H] [Finite H] [Group M] (Ψ : M →* H)
    (hΨ : Function.Injective Ψ) (hcard : Nat.card M = 2 ^ (Nat.card H).factorization 2)
    (hM : Nat.card (Subgroup.center M) = 4 ∧ (∀ x ∈ Subgroup.center M, x ^ 2 = 1) ∧
      ∀ φ : M ≃* M, ∀ x ∈ Subgroup.center M, φ x = x)
    {t : H} (ht : t ∈ Subgroup.center H) (htΨ : t ∈ Ψ.range) {L : Subgroup H}
    (hinv : ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ m ∈ Subgroup.center M, Ψ m = k⁻¹ * u * k) :
    ∃ T : Sylow 2 H, IsElementaryAbelian 2 (Subgroup.center (T : Subgroup H)) ∧
      Nat.card (Subgroup.center (T : Subgroup H)) = 4 ∧
      (∀ φ : MulAut (T : Subgroup H), ∀ z ∈ Subgroup.center (T : Subgroup H), φ z = z) ∧
      (∃ z ∈ Subgroup.center (T : Subgroup H), (z : H) = t) ∧
      (∀ φ : MulAut (T : Subgroup H), ∀ x : (T : Subgroup H), (x : H) = t → φ x = x) ∧
      ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ z ∈ Subgroup.center (T : Subgroup H),
        (z : H) = k⁻¹ * u * k := by
  let e : M ≃* Ψ.range := MonoidHom.ofInjective hΨ
  have hT : Nat.card Ψ.range = 2 ^ (Nat.card H).factorization 2 := by
    rw [← hcard]
    exact (Nat.card_congr e.toEquiv).symm
  obtain ⟨h4, hsq, hfix⟩ := center_facts_of_mulEquiv e.symm hM.1 hM.2.1 hM.2.2
  have htc : ∀ x : Ψ.range, (x : H) = t → x ∈ Subgroup.center Ψ.range := fun x hx =>
    Subgroup.mem_center_iff.2 fun y => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hx]
      exact Subgroup.mem_center_iff.1 ht y)
  have key : IsElementaryAbelian 2 (Subgroup.center Ψ.range) ∧
      Nat.card (Subgroup.center Ψ.range) = 4 ∧
      (∀ φ : MulAut Ψ.range, ∀ z ∈ Subgroup.center Ψ.range, φ z = z) ∧
      (∃ z ∈ Subgroup.center Ψ.range, (z : H) = t) ∧
      (∀ φ : MulAut Ψ.range, ∀ x : Ψ.range, (x : H) = t → φ x = x) ∧
      ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ z ∈ Subgroup.center Ψ.range,
        (z : H) = k⁻¹ * u * k := by
    refine ⟨isElementaryAbelian_center_of hsq, h4, hfix, ⟨⟨t, htΨ⟩, htc _ rfl, rfl⟩,
      fun φ x hx => hfix φ x (htc x hx), fun u hu hu2 => ?_⟩
    obtain ⟨k, hk, m, hm, hΨm⟩ := hinv u hu hu2
    exact ⟨k, hk, e m, map_mem_center e hm, by rw [MonoidHom.ofInjective_apply]; exact hΨm⟩
  exact ⟨Sylow.ofCard Ψ.range hT, key⟩

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {t x : G} (ht : orderOf t = 2)
    (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h] <;> simp

end CFSG.ComponentClassification.J2Cover.Rigid

namespace CFSG.ComponentClassification.J2Cover

open CFSG.ComponentClassification.CentralCover CFSG.ComponentClassification.J2Cover.Models
open Rigid (betaP_mul_self exists_lift_beta center_facts_RfN center_facts_TepsN
  mk_zero_mem_center twistHom twistHom_mk_zero twistHom_injective exists_sylow_of_model
  factorization_two_pow_mul_4725 eq_one_or_eq_of_mem_zpowers)

theorem ctss_j2_central_double_cover_internal_sylow_data_frontier {H : Type*} [Group H]
    [Finite H] {L : Subgroup H} {t : H} (hLn : L.Normal) (hLq : CFSG.Assembly.IsQuasisimple L)
    (ht : orderOf t = 2) (hZ : (Subgroup.center L).map L.subtype = Subgroup.zpowers t)
    (hQ : Nonempty (L ⧸ Subgroup.center L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hCL : Subgroup.centralizer (L : Set H) = Subgroup.zpowers t) (hidx : L.index ≤ 2) :
    ∃ T : Sylow 2 H, IsElementaryAbelian 2 (Subgroup.center (T : Subgroup H)) ∧
      Nat.card (Subgroup.center (T : Subgroup H)) = 4 ∧
      (∀ φ : MulAut (T : Subgroup H), ∀ z ∈ Subgroup.center (T : Subgroup H), φ z = z) ∧
      (∃ z ∈ Subgroup.center (T : Subgroup H), (z : H) = t) ∧
      (∀ φ : MulAut (T : Subgroup H), ∀ x : (T : Subgroup H), (x : H) = t → φ x = x) ∧
      ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ z ∈ Subgroup.center (T : Subgroup H),
        (z : H) = k⁻¹ * u * k := by
  obtain ⟨e₀⟩ := hQ
  let eP : L ⧸ Subgroup.center L ≃* Models.P := (e₀.trans nativeEquivP).trans Lift.toModels
  obtain ⟨tL, htLc, htLt⟩ : t ∈ (Subgroup.center L).map L.subtype :=
    hZ ▸ Subgroup.mem_zpowers t
  have htLt' : (tL : H) = t := htLt
  have hZL : Subgroup.center L = Subgroup.zpowers tL := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hZ, MonoidHom.map_zpowers, htLt]
  have htL : orderOf tL = 2 := by rw [← Subgroup.orderOf_coe, htLt', ht]
  let π : L →* Models.P := eP.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπs : Function.Surjective π := eP.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = Subgroup.center L := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker = Subgroup.zpowers tL := hkerZ.trans hZL
  have hπ : IsCentralDoubleExt π tL := ⟨hπs, htLc, htL, hker⟩
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  have hcardL : Nat.card L = 1209600 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv,
      Models.card_P, hker, Nat.card_zpowers, htL]
  obtain ⟨⟨ι₀, hι₀, -⟩, -, h15⟩ := Lift.native_sylow_map_and_lift_orders hLq.1 hπ
  obtain ⟨ι, hιs, hιz, hιβ⟩ := transport_beta hπ ι₀ hι₀
  let j : RfN →* H := L.subtype.comp ((Sp.comap π).subtype.comp ι.symm.toMonoidHom)
  have hj : Function.Injective j :=
    L.subtype_injective.comp ((Sp.comap π).subtype_injective.comp ι.symm.injective)
  have hjt : j ⟨1, 1⟩ = t := by
    rw [← htLt']
    exact congrArg Subtype.val hιz
  have hjL : ∀ x, j x ∈ L := fun x => ((ι.symm x : Sp.comap π) : L).2
  have htH : t ∈ Subgroup.center H := by
    rw [← htLt']
    exact coe_mem_center_of_center_eq_zpowers hZL (by rw [← htL, pow_orderOf_eq_one])
  have hR : ∀ u ∈ L, orderOf u = 2 →
      ∃ k ∈ L, ∃ x ∈ Subgroup.center RfN, j x = k⁻¹ * u * k := by
    intro u hu hu2
    have huL2 : orderOf (⟨u, hu⟩ : L) = 2 := (Subgroup.orderOf_coe _).symm.trans hu2
    by_cases h1 : π ⟨u, hu⟩ = 1
    · have hmem : (⟨u, hu⟩ : L) ∈ Subgroup.zpowers tL := by
        rw [← hπ.ker_eq]
        exact h1
      rcases eq_one_or_eq_of_mem_zpowers htL hmem with h | h
      · rw [h, orderOf_one] at huL2
        exact absurd huL2 (by norm_num)
      · refine ⟨1, L.one_mem, ⟨1, 1⟩, CocycleExtension.mk_one_mem_center 1, ?_⟩
        rw [hjt, inv_one, one_mul, mul_one, ← htLt']
        exact (congrArg Subtype.val h).symm
    · have hπu : orderOf (π ⟨u, hu⟩) = 2 := by
        refine orderOf_eq_prime ?_ h1
        rw [← map_pow, ← huL2, pow_orderOf_eq_one, map_one]
      obtain ⟨g, hg⟩ := involution_conj_rep (π ⟨u, hu⟩) hπu
      rcases hg with ⟨-, hg⟩ | ⟨h15', -⟩
      · obtain ⟨l, rfl⟩ := hπs g
        have hy : π (l * ⟨u, hu⟩ * l⁻¹) = (zN : Models.P) := by
          rw [map_mul, map_mul, map_inv, hg, zN, coe_eS_symm]
        have hyS : l * ⟨u, hu⟩ * l⁻¹ ∈ Sp.comap π := by
          rw [Subgroup.mem_comap, hy]
          exact zN.2
        have hsnd : (ι ⟨_, hyS⟩).snd = zN := Subtype.ext ((hιs _).trans hy)
        refine ⟨(l : H)⁻¹, L.inv_mem l.2, ι ⟨_, hyS⟩, ?_, ?_⟩
        · rw [center_RfN']
          rcases zmod_two_cases (ι ⟨_, hyS⟩).fst with h0 | h0
          · exact Or.inr (Or.inl (CocycleExtension.ext h0 hsnd))
          · exact Or.inr (Or.inr (Or.inr (CocycleExtension.ext h0 hsnd)))
        · change (((ι.symm (ι ⟨_, hyS⟩) : Sp.comap π) : L) : H) = _
          rw [MulEquiv.symm_apply_apply, inv_inv]
          rfl
      · have h4 := (h15 ⟨u, hu⟩ hπu h15').2
        rw [huL2] at h4
        exact absurd h4 (by norm_num)
  rcases (show L.index = 1 ∨ L.index = 2 by
    have := L.index_ne_zero_of_finite
    omega) with h1 | h2
  · have hcardH : Nat.card H = 2 ^ 8 * 4725 := by
      rw [← L.card_mul_index, h1, hcardL]
      norm_num
    refine exists_sylow_of_model j hj ?_ center_facts_RfN htH ⟨⟨1, 1⟩, hjt⟩ hR
    rw [card_RfN, hcardH, factorization_two_pow_mul_4725]
    norm_num
  · have hcardH : Nat.card H = 2 ^ 9 * 4725 := by
      rw [← L.card_mul_index, h2, hcardL]
      norm_num
    have hCL' : Subgroup.centralizer (L : Set H) ≤ L := by
      rw [hCL, Subgroup.zpowers_le, ← htLt']
      exact tL.2
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : H, h₀ ∉ L := not_forall.1 fun hall => by
      have hL : L = ⊤ := eq_top_iff.2 fun x _ => hall x
      rw [hL, Subgroup.index_top] at h2
      exact absurd h2 (by norm_num)
    obtain ⟨q, hqL, hθq⟩ := exists_lift_beta π hπs hkerZ hCL' hh₀
    have hq2 : q ^ 2 ∈ Subgroup.zpowers t := by
      rw [← hCL, ← ker_fullAction π hπs hkerZ, MonoidHom.mem_ker, map_pow, hθq, sq,
        betaP_mul_self]
    obtain ⟨ε, hε⟩ : ∃ ε : ZMod 2, q ^ 2 = j (TwistExt.zPow (tDataN ε) ε) := by
      rcases eq_one_or_eq_of_mem_zpowers ht hq2 with h | h
      · exact ⟨0, by rw [h, TwistExt.zPow_zero, map_one]⟩
      · exact ⟨1, by rw [h, TwistExt.zPow_one]; exact hjt.symm⟩
    have hφ : ∀ x : L, π (MulAut.conjNormal q x) = betaP (π x) := fun x => by
      rw [← fullAction_apply π hπs hkerZ, hθq]
    have hconj : ∀ y : RfN, q * j y * q⁻¹ = j (tauN y) := by
      intro y
      have hy : π ((ι.symm y : Sp.comap π) : L) ∈ Sp := (ι.symm y).2
      have hφy : π (MulAut.conjNormal q ((ι.symm y : Sp.comap π) : L)) ∈ Sp := by
        rw [hφ]
        exact map_mem_of_inducing tauN_snd hy
      have h := hιβ (MulAut.conjNormal q) hφ _ hy hφy
      have hyx : ι ⟨_, hy⟩ = y := ι.apply_symm_apply y
      rw [hyx] at h
      have h' : ι.symm (tauN y) = ⟨_, hφy⟩ := by rw [← h, MulEquiv.symm_apply_apply]
      change q * (((ι.symm y : Sp.comap π) : L) : H) * q⁻¹ =
        (((ι.symm (tauN y) : Sp.comap π) : L) : H)
      rw [h', MulAut.conjNormal_apply]
    have hΨ := twistHom_injective j q ε hconj hε hj fun y hy => hqL (hy ▸ hjL y)
    refine exists_sylow_of_model _ hΨ ?_ (center_facts_TepsN ε) htH
      ⟨⟨⟨1, 1⟩, 0⟩, by rw [twistHom_mk_zero]; exact hjt⟩ fun u hu hu2 => ?_
    · rw [card_TepsN, hcardH, factorization_two_pow_mul_4725]
      norm_num
    · obtain ⟨k, hk, x, hx, hjx⟩ := hR u hu hu2
      exact ⟨k, hk, ⟨x, 0⟩, mk_zero_mem_center ε hx, by rw [twistHom_mk_zero]; exact hjx⟩

theorem internalSylowData_J2 : StandardRecognition.InternalSylowData .J2 := by
  intro H _ _ L t ⟨hLn, hLq, ht, hZ, hQ, hCL, hidx⟩
  obtain ⟨T, -, -, -, -, hfix, hinv⟩ :=
    ctss_j2_central_double_cover_internal_sylow_data_frontier hLn hLq ht hZ hQ hCL hidx
  exact ⟨T, hfix, hinv⟩

end CFSG.ComponentClassification.J2Cover
