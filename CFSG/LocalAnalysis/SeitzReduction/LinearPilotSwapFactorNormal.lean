module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUnique
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
import CFSG.RankThree.CentralLift.LinearScalarCover

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut)

section Multiplier

theorem sl_exists_section_of_two_pow {m f : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {E : Type*} [Group E]
    {π : E →* Matrix.SpecialLinearGroup (Fin (m + 1)) K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin (m + 1)) K →* E, ∀ g, π (σ g) = g := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating (by omega)
    (CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (by omega) (by omega)
      (by omega) (by omega)) hπ hcen

theorem card_ker_dvd_gcd_of_two_pow {m f : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {X : Type*} [Group X] [Group.IsPerfect X]
    (η : X →* projectiveSL (m + 1) K) (hη : Function.Surjective η) (hC : η.ker ≤ center X) :
    Nat.card η.ker ∣ Nat.gcd (m + 1) (Nat.card K - 1) := by
  set S := Matrix.SpecialLinearGroup (Fin (m + 1)) K
  set P := ((proj (m + 1) K).comp (MonoidHom.fst S X)).eqLocus (η.comp (MonoidHom.snd S X))
    with hP
  set ρ := (MonoidHom.fst S X).comp P.subtype with hρ
  have hmemP : ∀ y : S × X, y ∈ P ↔ proj (m + 1) K y.1 = η y.2 := fun _ => Iff.rfl
  have hρs : Function.Surjective ρ := by
    intro h
    obtain ⟨l, hl⟩ := hη (proj (m + 1) K h)
    exact ⟨⟨(h, l), (hmemP _).2 hl.symm⟩, rfl⟩
  have hρker : ∀ y : P, y ∈ ρ.ker ↔ (y : S × X).1 = 1 := fun _ => Iff.rfl
  have hkerη : ∀ y : P, y ∈ ρ.ker → (y : S × X).2 ∈ η.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, ← (hmemP _).1 y.2, (hρker y).1 hy, map_one]
  have hA : ρ.ker ≤ center P := by
    intro y hy
    rw [mem_center_iff]
    intro z
    have hc := mem_center_iff.1 (hC (hkerη y hy)) (z : S × X).2
    have h1 : (y : S × X).1 = 1 := (hρker y).1 hy
    refine Subtype.ext (Prod.ext ?_ hc)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Prod.fst_mul, Prod.fst_mul, h1, mul_one, one_mul]
  obtain ⟨s, hs⟩ := sl_exists_section_of_two_pow hm hK hf hρs hA
  set φ : S →* X := (MonoidHom.snd S X).comp (P.subtype.comp s) with hφ
  have hηφ : η.comp φ = proj (m + 1) K := by
    refine MonoidHom.ext fun g => ?_
    have hmem := (hmemP _).1 (s g).2
    have h1 : ((s g : P) : S × X).1 = g := hs g
    rw [h1] at hmem
    exact hmem.symm
  exact (CFSG.RankThree.CentralLift.exact_scalar_cover_map_of_comp_eq (by omega) hC
    hηφ).2.2.2.2.2.2

end Multiplier

section FixedOdd

variable {X : Type*} [Group X]

theorem card_eq_card_map_mk_mul_card_inf [Finite X] (H N : Subgroup X) [N.Normal] :
    Nat.card H = Nat.card (H.map (QuotientGroup.mk' N)) * Nat.card (H ⊓ N : Subgroup X) := by
  set φ := (QuotientGroup.mk' N).comp H.subtype with hφ
  have hrange : φ.range = H.map (QuotientGroup.mk' N) := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
  have hker : φ.ker.map H.subtype = H ⊓ N := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    change (N.subgroupOf H).map H.subtype = H ⊓ N
    rw [subgroupOf_map_subtype, inf_comm]
  have hk : Nat.card φ.ker = Nat.card (H ⊓ N : Subgroup X) := by
    rw [← hker, card_map_of_injective H.subtype_injective]
  rw [← card_ker_mul_card_range φ, hk, hrange, mul_comm]

theorem map_fixedSubgroup_mk_eq_of_odd [Finite X] {α : MulAut X} (hα : α * α = 1)
    (hZ : Odd (Nat.card (center X))) :
    (fixedSubgroup α).map (QuotientGroup.mk' (center X)) =
      fixedSubgroup (centerQuotientAut α) := by
  have hαα : ∀ x, α (α x) = x := fun x => by
    rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change centerQuotientAut α (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
    rw [F4Pilot.centerQuotientAut_mk]
    have hx' : α x = x := hx
    rw [hx']
  · intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center X) y
    have hy' : centerQuotientAut α (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x := hy
    rw [F4Pilot.centerQuotientAut_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hy'
    set w := x⁻¹ * α x with hw
    have hwZ : w ∈ center X := by
      have h1 := inv_mem hy'
      rw [mul_inv_rev, inv_inv] at h1
      exact h1
    have hαw : α w = w⁻¹ := by
      rw [hw, map_mul, map_inv, hαα, mul_inv_rev, inv_inv]
    obtain ⟨k, hk⟩ := hZ
    set N := Nat.card (center X) with hN
    have hwN : w ^ N = 1 := by
      have h1 : (⟨w, hwZ⟩ : center X) ^ N = 1 := pow_card_eq_one'
      exact congrArg Subtype.val h1
    set z := w ^ (k + 1) with hz
    have hzZ : z ∈ center X := pow_mem hwZ _
    have hαz : α z = z⁻¹ := by rw [hz, map_pow, hαw, inv_pow]
    have hwz : w * z⁻¹ = z := by
      have h2 : z * z = w := by
        rw [hz, ← pow_add, show k + 1 + (k + 1) = N + 1 by omega, pow_succ, hwN, one_mul]
      rw [← h2, mul_inv_cancel_right]
    refine ⟨x * z, ?_, ?_⟩
    · change α (x * z) = x * z
      rw [map_mul, hαz, show α x = x * w by rw [hw, mul_inv_cancel_left], mul_assoc, hwz]
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mul_inv_rev,
        mul_assoc, inv_mul_cancel, mul_one]
      exact inv_mem hzZ

theorem card_fixedSubgroup_eq_of_odd [Finite X] {α : MulAut X} (hα : α * α = 1)
    (hZ : Odd (Nat.card (center X))) :
    Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup (centerQuotientAut α)) *
      Nat.card (fixedSubgroup α ⊓ center X : Subgroup X) := by
  rw [card_eq_card_map_mk_mul_card_inf (fixedSubgroup α) (center X),
    map_fixedSubgroup_mk_eq_of_odd hα hZ]

theorem card_perfectCore_fixedSubgroup_eq [Finite X] (α : MulAut X) :
    Nat.card (perfectCore (fixedSubgroup α)) =
      Nat.card (perfectCore (fixedSubgroup (centerQuotientAut α))) *
        Nat.card (perfectCore (fixedSubgroup α) ⊓ center X : Subgroup X) := by
  rw [card_eq_card_map_mk_mul_card_inf (perfectCore (fixedSubgroup α)) (center X),
    perfectCore_fixedSubgroup_centerQuotientAut]

end FixedOdd

section Factor

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ker_eq_center_of_surjective {A L : Subgroup G} (hZL : center L = ⊥) {φ : A →* L}
    (hφ : Function.Surjective φ) (hφZ : φ.ker ≤ center A) : φ.ker = center A := by
  refine le_antisymm hφZ fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hc : φ z ∈ center L := by
    rw [mem_center_iff]
    intro l
    obtain ⟨a, rfl⟩ := hφ l
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz a]
  rw [hZL, mem_bot] at hc
  exact hc

theorem exists_factorAut {L : Subgroup G} (hZL : center L = ⊥) {n : ℕ} {K : Type} [Field K]
    [Finite K] (e : L ≃* projectiveSL n K) {A : Subgroup G} [Group.IsPerfect A] {φ : A →* L}
    (hφ : Function.Surjective φ) (hφZ : φ.ker ≤ center A) (hodd : Odd (Nat.card (center A)))
    {t : G} (htt : t * t = 1) (htA : t ∈ normalizer (A : Set G))
    (hnA : t ∉ centralizer (A : Set G)) :
    ∃ θ : MulAut (projectiveSL n K), θ * θ = 1 ∧ θ ≠ 1 ∧
      Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) = Nat.card (fixedSubgroup θ) *
        Nat.card ((A ⊓ centralizer ({t} : Set G)) ⊓ (center A).map A.subtype : Subgroup G) ∧
      Nat.card (perfectCore (A ⊓ centralizer ({t} : Set G))) =
        Nat.card (perfectCore (fixedSubgroup θ)) *
          Nat.card (perfectCore (A ⊓ centralizer ({t} : Set G)) ⊓ (center A).map A.subtype :
            Subgroup G) ∧
      ((∃ a ∈ A, ∃ b ∈ centralizer (A : Set G), t = a * b) →
        θ ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) := by
  set τ := A.normalizerMonoidHom ⟨t, htA⟩ with hτ
  have hτ2 : τ * τ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one A htA (by rw [sq]; exact htt)
  have hker := ker_eq_center_of_surjective hZL hφ hφZ
  set ψ : A ⧸ center A ≃* projectiveSL n K :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).trans e with hψ
  set θ := MulAut.congr ψ (centerQuotientAut τ) with hθ
  have hfix : (fixedSubgroup τ).map A.subtype = A ⊓ centralizer ({t} : Set G) :=
    F4Pilot.map_fixedSubgroup_normalizerMonoidHom A htA
  have hcore : (perfectCore (fixedSubgroup τ)).map A.subtype =
      perfectCore (A ⊓ centralizer ({t} : Set G)) := by
    rw [CFSG.Quasithin.map_perfectCore, hfix]
  refine ⟨θ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hθ, ← map_mul, ← centerQuotientAut_mul, hτ2, centerQuotientAut_one, map_one]
  · intro h1
    apply hnA
    have h2 : centerQuotientAut τ = 1 := (MulEquiv.map_eq_one_iff _).1 h1
    have h3 : τ = 1 := F4Pilot.eq_one_of_centerQuotientAut_eq_one h2
    rw [mem_centralizer_iff]
    intro a ha
    have h4 := congrArg (fun σ : MulAut A => ((σ ⟨a, ha⟩ : A) : G)) h3
    simp only [MulAut.one_apply] at h4
    rw [hτ, F4Pilot.coe_normalizerMonoidHom_mk_apply] at h4
    calc a * t = t * a * t⁻¹ * t := by rw [h4]
      _ = t * a := by group
  · rw [← hfix, card_map_of_injective A.subtype_injective, hθ, card_fixedSubgroup_congr,
      card_fixedSubgroup_eq_of_odd hτ2 hodd, ← map_inf _ _ _ A.subtype_injective,
      card_map_of_injective A.subtype_injective]
  · rw [← hcore, card_map_of_injective A.subtype_injective, hθ,
      card_perfectCore_fixedSubgroup_congr, card_perfectCore_fixedSubgroup_eq,
      ← map_inf _ _ _ A.subtype_injective, card_map_of_injective A.subtype_injective]
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hτa : τ = MulAut.conj (⟨a, ha⟩ : A) := by
      ext x
      rw [hτ, F4Pilot.coe_normalizerMonoidHom_mk_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, coe_inv]
      have hbx : (x : G) * b = b * x := mem_centralizer_iff.1 hb x x.2
      change a * b * x * (a * b)⁻¹ = a * x * a⁻¹
      calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
        _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hbx]
        _ = a * x * a⁻¹ := by group
    refine ⟨ψ (QuotientGroup.mk' (center A) ⟨a, ha⟩), ?_⟩
    rw [hθ, hτa, F4Pilot.centerQuotientAut_conj, mulAut_congr_conj]

end Factor

section Product

variable {G : Type} [Group G] [Finite G]

theorem mul_dvd_card_sup_of_commute {H₁ H₂ Z : Subgroup G}
    (hc : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) (hZ : H₁ ⊓ H₂ ≤ Z) {c₁ c₂ : ℕ}
    (h₁ : Nat.card H₁ = c₁ * Nat.card (H₁ ⊓ Z : Subgroup G)) (h₂ : c₂ ∣ Nat.card H₂) :
    c₁ * c₂ ∣ Nat.card (H₁ ⊔ H₂ : Subgroup G) := by
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H₁ H₂ hc).1
  obtain ⟨k, hk⟩ : Nat.card (H₁ ⊓ H₂ : Subgroup G) ∣ Nat.card (H₁ ⊓ Z : Subgroup G) :=
    Subgroup.card_dvd_of_le (le_inf inf_le_left hZ)
  obtain ⟨j, hj⟩ := h₂
  have hpos : 0 < Nat.card (H₁ ⊓ H₂ : Subgroup G) := Nat.card_pos
  have h : Nat.card (H₁ ⊔ H₂ : Subgroup G) = c₁ * c₂ * (k * j) := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hprod, h₁, hk, hj]
    ring
  exact ⟨k * j, h⟩

omit [Finite G] in
theorem eq_one_or_eq_self_of_mem_zpowers {t x : G} (ht : orderOf t = 2) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, h, zpow_one]

theorem card_dvd_card_mulAut_of_not_mem {L : Subgroup G}
    (hL : CFSG.Open.standardComponentIsStandard L) {n : ℕ} {K : Type*} [Field K]
    (e : L ≃* projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {D : Subgroup G}
    (hDt : D ≤ centralizer ({t} : Set G)) (htD : t ∉ D) :
    Nat.card D ∣ Nat.card (MulAut (projectiveSL n K)) := by
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  have hDN : D ≤ normalizer (L : Set G) :=
    hDt.trans (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht)
  set ρ := (normalizerAut e).comp (inclusion hDN) with hρ
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (inclusion hDN x : normalizer (L : Set G)) ∈ (normalizerAut e).ker := hx
    rw [ker_normalizerAut, mem_subgroupOf, coe_inclusion] at h1
    have h2 : (x : G) ∈ zpowers t := hKt ▸ mem_inf.2 ⟨h1, hDt x.2⟩
    rcases eq_one_or_eq_self_of_mem_zpowers ht h2 with h3 | h3
    · rw [mem_bot]
      exact Subtype.ext h3
    · exact absurd (h3 ▸ x.2) htD
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

end Product

@[expose] def LinearInvolutionPairExclusion (n : ℕ) (K : Type*) [Field K] : Prop :=
  ∀ θ₁ θ₂ : MulAut (projectiveSL n K), θ₁ * θ₁ = 1 → θ₁ ≠ 1 → θ₂ * θ₂ = 1 → θ₂ ≠ 1 →
    Nat.card (fixedSubgroup θ₁) * Nat.card (fixedSubgroup θ₂) ∣
      2 * Nat.card (MulAut (projectiveSL n K)) →
    ((θ₁ ∉ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ∨
        θ₂ ∉ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) →
      Nat.card (fixedSubgroup θ₁) * Nat.card (fixedSubgroup θ₂) ∣
        Nat.card (MulAut (projectiveSL n K))) →
    Nat.card (perfectCore (fixedSubgroup θ₁)) * Nat.card (perfectCore (fixedSubgroup θ₂)) ∣
      Nat.card (projectiveSL n K) → False

section Reduction

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem odd_card_center_of_surjective {L A : Subgroup G} (hZL : center L = ⊥) {m f : ℕ}
    (hm : 3 ≤ m) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* projectiveSL (m + 1) K) [Group.IsPerfect A] {φ : A →* L}
    (hφ : Function.Surjective φ) (hφZ : φ.ker ≤ center A) : Odd (Nat.card (center A)) := by
  set η := e.toMonoidHom.comp φ with hη
  have hηs : Function.Surjective η := e.surjective.comp hφ
  have hηker : η.ker = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hdvd := card_ker_dvd_gcd_of_two_pow hm hK hf η hηs (hηker ▸ hφZ)
  rw [hηker, ker_eq_center_of_surjective hZL hφ hφZ] at hdvd
  have hodd : Odd (Nat.card K - 1) := by
    rw [hK]
    obtain ⟨r, hr⟩ : ∃ r, f = r + 1 := ⟨f - 1, by omega⟩
    refine ⟨2 ^ r - 1, ?_⟩
    have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    rw [hr, pow_succ]
    omega
  exact Odd.of_dvd_nat hodd ((hdvd.trans (Nat.gcd_dvd_right _ _)))

omit [Finite G] in
theorem exists_surjective_map_conj {A L : Subgroup G} {φ : A →* L}
    (hφ : Function.Surjective φ) (hφZ : φ.ker ≤ center A) (g : G) :
    ∃ φ' : A.map (MulAut.conj g).toMonoidHom →* L, Function.Surjective φ' ∧
      φ'.ker ≤ center (A.map (MulAut.conj g).toMonoidHom) := by
  let E : A ≃* A.map (MulAut.conj g).toMonoidHom :=
    A.equivMapOfInjective _ (MulAut.conj g).injective
  refine ⟨φ.comp E.symm.toMonoidHom, hφ.comp E.symm.surjective, fun x hx => ?_⟩
  have h1 : E.symm x ∈ center A := hφZ hx
  rw [mem_center_iff] at h1 ⊢
  intro y
  apply E.symm.injective
  rw [map_mul, map_mul]
  exact h1 (E.symm y)

open scoped Pointwise in
theorem linearSwapFactorNormalInput_of_pairExclusion
    (hP : ∀ (m f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 3 ≤ m →
      Nat.card K = 2 ^ f → 2 ≤ f → LinearInvolutionPairExclusion (m + 1) K) :
    LinearSwapFactorNormalInput := by
  intro G _ _ L hset m f K _ _ _ hm hKc hf e t ht hKt A hq hφ g hAB htA htB hnA hnB
  obtain ⟨φ, hφs, hφZ⟩ := hφ
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv (by omega) e
  have hZL : center L = ⊥ := hset.center_eq_bot
  set B := A.map (MulAut.conj g).toMonoidHom with hB
  have : Group.IsPerfect A := ⟨hq.1⟩
  have hqB := isQuasisimple_map_conj hq g
  have : Group.IsPerfect B := ⟨hqB.1⟩
  obtain ⟨φB, hφBs, hφBZ⟩ := exists_surjective_map_conj hφs hφZ g
  have hoddA := odd_card_center_of_surjective hZL hm hKc hf e hφs hφZ
  have hoddB := odd_card_center_of_surjective hZL hm hKc hf e hφBs hφBZ
  obtain ⟨θA, hθA2, hθA1, hcA, hpA, hinA⟩ := exists_factorAut hZL e hφs hφZ hoddA htt htA hnA
  obtain ⟨θB, hθB2, hθB1, hcB, hpB, hinB⟩ := exists_factorAut hZL e hφBs hφBZ hoddB htt htB hnB
  have hBA : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.1 (hAB hy) x hx
  have hIZ : A ⊓ B ≤ (center A).map A.subtype := by
    rintro x ⟨hxA, hxB⟩
    refine ⟨⟨x, hxA⟩, mem_center_iff.2 fun y => Subtype.ext (hBA y y.2 x hxB), rfl⟩
  set CA := A ⊓ centralizer ({t} : Set G) with hCA
  set CB := B ⊓ centralizer ({t} : Set G) with hCB
  have hcomm : ∀ x ∈ CA, ∀ y ∈ CB, x * y = y * x := fun x hx y hy => hBA x hx.1 y hy.1
  have hIZC : CA ⊓ CB ≤ (center A).map A.subtype := fun x hx => hIZ ⟨hx.1.1, hx.2.1⟩
  have hC1 : Nat.card (fixedSubgroup θA) * Nat.card (fixedSubgroup θB) ∣
      Nat.card (CA ⊔ CB : Subgroup G) :=
    mul_dvd_card_sup_of_commute hcomm hIZC hcA ⟨_, hcB⟩
  have hDt : CA ⊔ CB ≤ centralizer ({t} : Set G) := sup_le inf_le_right inf_le_right
  have hD2 : Nat.card (CA ⊔ CB : Subgroup G) ∣
      2 * Nat.card (MulAut (projectiveSL (m + 1) K)) :=
    (Subgroup.card_dvd_of_le hDt).trans
      (card_centralizer_dvd_two_mul_card_mulAut hset.standardSetting.standard e ht hKt)
  have hC2 : (θA ∉ (MulAut.conj : projectiveSL (m + 1) K →* MulAut _).range ∨
      θB ∉ (MulAut.conj : projectiveSL (m + 1) K →* MulAut _).range) →
      Nat.card (fixedSubgroup θA) * Nat.card (fixedSubgroup θB) ∣
        Nat.card (MulAut (projectiveSL (m + 1) K)) := by
    intro hout
    refine hC1.trans (card_dvd_card_mulAut_of_not_mem hset.standardSetting.standard e ht hKt hDt
      fun htD => ?_)
    have hset' := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute CA CB hcomm).2
    have htD' : t ∈ (CA : Set G) * (CB : Set G) := by
      rw [← hset']
      exact htD
    obtain ⟨c, hc, d, hd, hcd⟩ := Set.mem_mul.1 htD'
    rcases hout with h | h
    · exact h (hinA ⟨c, hc.1, d, hAB hd.1, hcd.symm⟩)
    · refine h (hinB ⟨d, hd.1, c, ?_, ?_⟩)
      · rw [mem_centralizer_iff]
        intro y hy
        exact (hBA c hc.1 y hy).symm
      · rw [← hcd]
        exact hcomm c hc d hd
  set PA := perfectCore CA with hPA
  set PB := perfectCore CB with hPB
  have hPAL : PA ≤ L := std_perfect_le hset.standardSetting hOut htC ht
    (CFSG.Quasithin.perfectCore_perfect _) ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)
  have hPBL : PB ≤ L := std_perfect_le hset.standardSetting hOut htC ht
    (CFSG.Quasithin.perfectCore_perfect _) ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)
  have hPcomm : ∀ x ∈ PA, ∀ y ∈ PB, x * y = y * x := fun x hx y hy =>
    hcomm x (CFSG.Quasithin.perfectCore_le _ hx) y (CFSG.Quasithin.perfectCore_le _ hy)
  have hPIZ : PA ⊓ PB ≤ (center A).map A.subtype := fun x hx =>
    hIZC ⟨CFSG.Quasithin.perfectCore_le _ hx.1, CFSG.Quasithin.perfectCore_le _ hx.2⟩
  have hC3 : Nat.card (perfectCore (fixedSubgroup θA)) *
      Nat.card (perfectCore (fixedSubgroup θB)) ∣ Nat.card (PA ⊔ PB : Subgroup G) :=
    mul_dvd_card_sup_of_commute hPcomm hPIZ hpA ⟨_, hpB⟩
  have hPL : Nat.card (PA ⊔ PB : Subgroup G) ∣ Nat.card (projectiveSL (m + 1) K) := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_dvd_of_le (sup_le hPAL hPBL)
  exact hP m f K hm hKc hf θA θB hθA2 hθA1 hθB2 hθB1 (hC1.trans hD2) hC2 (hC3.trans hPL)

end Reduction

end CFSG.SeitzReduction.LinearPilot
