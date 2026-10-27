module

public import CFSG.CharacterTheory.TwoRankLowerBound.PrimePrimaryFactorization
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.PrimaryUniqueness
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.CosetConstantKernel
public import Mathlib.LinearAlgebra.PID

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

section GroupTheory

variable {M : Type*} [Group M]

theorem eq_one_of_mem_of_pow_two_pow_eq_one {O : Subgroup M} (hO : Odd (Nat.card O)) {w : M}
    (hw : w ∈ O) {k : ℕ} (hk : w ^ 2 ^ k = 1) : w = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) := (Nat.coprime_two_left.mpr hO).pow_left k
  have h1 : Nat.Coprime (orderOf w) (Nat.card O) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk) hcop
  exact orderOf_eq_one_iff.mp (h1.eq_one_of_dvd (O.orderOf_dvd_natCard hw))

theorem mem_zpowers_zpow_of_odd {w : M} {a : ℕ} (hw : w ^ 2 ^ a = 1) {h : ℤ} (hh : Odd h) :
    w ∈ Subgroup.zpowers (w ^ h) := by
  obtain ⟨k, rfl⟩ := hh
  have hcop : IsCoprime (2 * k + 1) ((2 : ℤ) ^ a) := by
    have h2 : IsCoprime (2 * k + 1) (2 : ℤ) := ⟨1, -k, by ring⟩
    exact h2.pow_right
  obtain ⟨s, t, hst⟩ := hcop
  refine Subgroup.mem_zpowers_iff.mpr ⟨s, ?_⟩
  have hw' : w ^ ((2 : ℤ) ^ a) = 1 := by
    rw [show ((2 : ℤ) ^ a) = ((2 ^ a : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hw]
  calc (w ^ (2 * k + 1)) ^ s = w ^ (s * (2 * k + 1)) * (w ^ ((2 : ℤ) ^ a)) ^ t := by
        rw [hw', one_zpow, mul_one, ← zpow_mul, mul_comm]
    _ = w ^ (s * (2 * k + 1) + t * 2 ^ a) := by rw [← zpow_mul, ← zpow_add, mul_comm t]
    _ = w := by rw [hst, zpow_one]

theorem orderOf_mk_eq_of_pow_two_pow_eq_one {O : Subgroup M} [O.Normal] (hO : Odd (Nat.card O))
    {w : M} {k : ℕ} (hw : w ^ 2 ^ k = 1) : orderOf (w : M ⧸ O) = orderOf w := by
  apply Nat.dvd_antisymm (orderOf_map_dvd (QuotientGroup.mk' O) w)
  apply orderOf_dvd_of_pow_eq_one
  apply eq_one_of_mem_of_pow_two_pow_eq_one hO (k := k)
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one (QuotientGroup.mk' O w)
  · rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]

theorem zpowers_eq_of_isPGroup_two {E F : Type*} [Group E] [Finite E] [Group F] (f : E →* F)
    (hf : ∀ e : E, f e = 1 → ∀ k : ℕ, e ^ 2 ^ k = 1 → e = 1) (S : Subgroup F) [Finite S]
    (hS : ∀ e, f e ∈ S) (w : E) (hcard : Nat.card S ≤ orderOf w) {Q : Subgroup E}
    (hQ : IsPGroup 2 Q) (hle : Subgroup.zpowers w ≤ Q) : Q = Subgroup.zpowers w := by
  have hinj : Function.Injective (fun q : Q => (⟨f q, hS q⟩ : S)) := by
    intro q₁ q₂ hq
    have hq' : f ((q₁ : E)⁻¹ * q₂) = 1 := by
      have h := congrArg Subtype.val hq
      simp only at h
      rw [map_mul, map_inv, h, inv_mul_cancel]
    obtain ⟨k, hk⟩ := hQ (q₁⁻¹ * q₂)
    have hk' : ((q₁ : E)⁻¹ * q₂) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    exact Subtype.ext (inv_mul_eq_one.mp (hf _ hq' k hk'))
  have h1 := Nat.card_le_card_of_injective _ hinj
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers]; omega)).symm

theorem exists_conj_eq_zpow_mul_of_mk_eq [Finite M] {O : Subgroup M} [O.Normal]
    (hO : Odd (Nat.card O)) {y : M} {a : ℕ} (hy : orderOf y = 2 ^ a) {h : ℤ} (hh : Odd h)
    {z : M ⧸ O} (hz : Odd (orderOf z)) (hzy : z ∈ Subgroup.centralizer {(y : M ⧸ O)})
    {x : M} (hx : (x : M ⧸ O) = (y : M ⧸ O) ^ h * z) :
    ∃ e v : M, e * x * e⁻¹ = y ^ h * v ∧ Odd (orderOf v) ∧ Commute v y := by
  obtain ⟨u, w, m, -, -, huw, hux, hu, hw⟩ := finite_prime_primary_factorization x 2 Nat.prime_two
  have hy2 : y ^ 2 ^ a = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hu2 : u ^ 2 ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp hu
  set yb : M ⧸ O := (y : M ⧸ O) with hyb
  have hyb2 : yb ^ 2 ^ a = 1 := by rw [hyb, ← QuotientGroup.mk_pow, hy2, QuotientGroup.mk_one]
  have hcommz : Commute (yb ^ h) z := by
    have hzc : Commute z yb := Subgroup.mem_centralizer_singleton_iff.mp hzy
    exact hzc.symm.zpow_left h
  have hordyh : orderOf (yb ^ h) ∣ 2 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyb2, one_zpow]
  have hαu : (u : M ⧸ O) = yb ^ h := by
    have hmul : (u : M ⧸ O) * (w : M ⧸ O) = yb ^ h * z := by
      rw [← hx, ← hux, QuotientGroup.mk_mul]
    exact (CFSG.LyonsUnitaryFour.primary_factorization_unique (p := 2)
      ((orderOf_map_dvd (QuotientGroup.mk' O) u).trans hu)
      (Nat.Coprime.coprime_dvd_right (orderOf_map_dvd (QuotientGroup.mk' O) w) hw)
      (huw.map (QuotientGroup.mk' O)) hordyh (Nat.coprime_two_left.mpr hz) hcommz hmul).1
  have hordyb : orderOf yb = 2 ^ a := by rw [hyb, orderOf_mk_eq_of_pow_two_pow_eq_one hO hy2, hy]
  have hordu : orderOf u = 2 ^ a := by
    rw [← orderOf_mk_eq_of_pow_two_pow_eq_one (O := O) hO hu2, hαu]
    apply Nat.dvd_antisymm hordyh
    rw [← hordyb]
    exact orderOf_dvd_of_mem_zpowers (mem_zpowers_zpow_of_odd hyb2 hh)
  let E : Subgroup M := (Subgroup.zpowers yb).comap (QuotientGroup.mk' O)
  have hyE : y ∈ E := Subgroup.mem_zpowers yb
  have huE : u ∈ E := by
    change (QuotientGroup.mk' O u) ∈ Subgroup.zpowers yb
    rw [QuotientGroup.mk'_apply, hαu]
    exact Subgroup.zpow_mem_zpowers yb h
  let f : E →* M ⧸ O := (QuotientGroup.mk' O).comp E.subtype
  have hfS : ∀ e : E, f e ∈ Subgroup.zpowers yb := fun e => e.2
  have hfker : ∀ e : E, f e = 1 → ∀ k : ℕ, e ^ 2 ^ k = 1 → e = 1 := by
    intro e he k hk
    apply Subtype.ext
    exact eq_one_of_mem_of_pow_two_pow_eq_one hO ((QuotientGroup.eq_one_iff _).mp he)
      (by simpa using congrArg Subtype.val hk)
  have hcardS : Nat.card (Subgroup.zpowers yb) = 2 ^ a := by rw [Nat.card_zpowers, hordyb]
  let yE : E := ⟨y, hyE⟩
  let uE : E := ⟨u, huE⟩
  have hyEord : orderOf yE = 2 ^ a := by rw [Subgroup.orderOf_mk, hy]
  have huEord : orderOf uE = 2 ^ a := by rw [Subgroup.orderOf_mk, hordu]
  let PS : Sylow 2 E :=
    { toSubgroup := Subgroup.zpowers yE
      isPGroup' := IsPGroup.of_card (by rw [Nat.card_zpowers, hyEord])
      is_maximal' := fun hQ hle =>
        zpowers_eq_of_isPGroup_two f hfker _ hfS yE (by rw [hcardS, hyEord]) hQ hle }
  let QS : Sylow 2 E :=
    { toSubgroup := Subgroup.zpowers uE
      isPGroup' := IsPGroup.of_card (by rw [Nat.card_zpowers, huEord])
      is_maximal' := fun hQ hle =>
        zpowers_eq_of_isPGroup_two f hfker _ hfS uE (by rw [hcardS, huEord]) hQ hle }
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq E QS PS
  have hmem : e * uE * e⁻¹ ∈ (PS : Subgroup E) := by
    rw [← he, Sylow.coe_subgroup_smul]
    have h := Subgroup.smul_mem_pointwise_smul uE (MulAut.conj e) (QS : Subgroup E)
      (Subgroup.mem_zpowers uE)
    simpa [MulAut.smul_def] using h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : y ^ k = (e : M) * u * (e : M)⁻¹ := by
    simpa [yE, uE] using congrArg Subtype.val hk
  have hαe : Commute (f e) (yb ^ h) := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hfS e)
    rw [← hj]
    exact Commute.zpow_zpow_self yb j h
  have hyk : y ^ k = y ^ h := by
    have h1 : ((y ^ k : M) : M ⧸ O) = yb ^ h := by
      rw [hk', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hαu]
      change f e * yb ^ h * (f e)⁻¹ = yb ^ h
      rw [hαe.eq, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : (y ^ h)⁻¹ * y ^ k = 1 := by
      apply eq_one_of_mem_of_pow_two_pow_eq_one hO (k := a)
      · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
          QuotientGroup.mk_zpow, inv_mul_cancel]
      · rw [← zpow_neg, ← zpow_add, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          hy2, one_zpow]
    exact (inv_mul_eq_one.mp h2).symm
  refine ⟨e, e * w * (e : M)⁻¹, ?_, ?_, ?_⟩
  · rw [← hux, ← hyk, hk']
    group
  · have h := MulEquiv.orderOf_eq (MulAut.conj (e : M)) w
    rw [MulAut.conj_apply] at h
    rw [h]
    exact Nat.coprime_two_left.mp hw
  · have hc1 : Commute ((e : M) * w * (e : M)⁻¹) (y ^ h) := by
      rw [← hyk, hk']
      have h := huw.symm.map (MulAut.conj (e : M))
      simpa [MulAut.conj_apply] using h
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_zpow_of_odd hy2 hh)
    rw [← hs]
    exact hc1.zpow_right s

end GroupTheory

section Character

variable {G : Type} [Group G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable abbrev fixedSpaceQuotientRepresentation (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] :
    Representation ℂ (K ⧸ O) (Representation.invariants ((ρ.comp K.subtype).comp O.subtype)) :=
  Representation.quotientToInvariants (ρ.comp K.subtype) O

theorem fixedSpaceQuotientRepresentation_apply (ρ : Representation ℂ G V) (K : Subgroup G)
    (O : Subgroup K) [O.Normal] (g : K)
    (v : Representation.invariants ((ρ.comp K.subtype).comp O.subtype)) :
    (fixedSpaceQuotientRepresentation ρ K O (g : K ⧸ O) v : V) = ρ g v :=
  rfl

theorem subgroupAverage_mem_invariants {L : Type*} [Group L] (σ : Representation ℂ L V)
    (H : Subgroup L) [Fintype H] (v : V) :
    CFSG.LyonsUnitaryFour.subgroupAverage σ H v ∈ Representation.invariants (σ.comp H.subtype) := by
  intro o
  have h := congrArg (fun F : Module.End ℂ V => F v)
    (CFSG.LyonsUnitaryFour.mul_subgroupAverage σ H (o : L) o.2)
  simpa using h

theorem subgroupAverage_apply_of_mem_invariants {L : Type*} [Group L] (σ : Representation ℂ L V)
    (H : Subgroup L) [Fintype H] {v : V} (hv : v ∈ Representation.invariants (σ.comp H.subtype)) :
    CFSG.LyonsUnitaryFour.subgroupAverage σ H v = v := by
  have hne : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hfix : ∀ o : H, σ o v = v := fun o => hv o
  unfold CFSG.LyonsUnitaryFour.subgroupAverage
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  simp_rw [hfix]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem finrank_invariants_eq_finrank_iff [FiniteDimensional ℂ V] {L : Type*} [Group L]
    (σ : Representation ℂ L V) (H : Subgroup L) :
    Module.finrank ℂ (Representation.invariants (σ.comp H.subtype)) = Module.finrank ℂ V ↔
      H ≤ MonoidHom.ker σ := by
  constructor
  · intro h o ho
    have htop := Submodule.eq_top_of_finrank_eq h
    rw [MonoidHom.mem_ker]
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Representation.invariants (σ.comp H.subtype) := htop ▸ Submodule.mem_top
    exact hv ⟨o, ho⟩
  · intro h
    have htop : Representation.invariants (σ.comp H.subtype) = ⊤ := by
      rw [eq_top_iff]
      intro v _ o
      have ho := h o.2
      rw [MonoidHom.mem_ker] at ho
      change σ o v = v
      rw [ho]
      rfl
    rw [htop, finrank_top]

variable [FiniteDimensional ℂ V]

theorem fixedSpaceQuotientRepresentation_character_one (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] :
    (fixedSpaceQuotientRepresentation ρ K O).character 1 =
      Module.finrank ℂ (Representation.invariants ((ρ.comp K.subtype).comp O.subtype)) :=
  Representation.char_one _

theorem fixedSpaceQuotientRepresentation_character_mk [Fintype G] (ρ : Representation ℂ G V)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (g : K) :
    (fixedSpaceQuotientRepresentation ρ K O).character (g : K ⧸ O) =
      (Nat.card O : ℂ)⁻¹ * ∑ o : O, ρ.character ((g : G) * ((o : K) : G)) := by
  set σ := ρ.comp K.subtype with hσ
  set W := Representation.invariants (σ.comp O.subtype) with hW
  set P := CFSG.LyonsUnitaryFour.subgroupAverage σ O with hP
  have hmaps : ∀ x, (σ g * P) x ∈ W := fun x =>
    Representation.le_comap_invariants σ O g (subgroupAverage_mem_invariants σ O x)
  have key := LinearMap.trace_restrict_eq_of_forall_mem W (σ g * P) hmaps
  calc (fixedSpaceQuotientRepresentation ρ K O).character (g : K ⧸ O)
      = LinearMap.trace ℂ W ((σ g * P).restrict (fun x _ => hmaps x)) := by
        change LinearMap.trace ℂ W ((σ g).restrict (Representation.le_comap_invariants σ O g)) = _
        congr 1
        refine LinearMap.ext fun v => Subtype.ext ?_
        change σ g v = σ g (P v)
        rw [subgroupAverage_apply_of_mem_invariants σ O v.2]
    _ = LinearMap.trace ℂ V (σ g * P) := key
    _ = _ := CFSG.LyonsUnitaryFour.trace_mul_subgroupAverage σ O g

theorem odd_kernel_fixed_space_character_preserves_cyclic_two_sections [Fintype G]
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (hO : Odd (Nat.card O))
    (y : K) (a : ℕ) (_ha : 1 ≤ a) (hy : orderOf y = 2 ^ a)
    (ρ : Representation ℂ G V) (c : ℂ)
    (hc : ∀ h : ℤ, Odd h → ∀ z : G, Odd (orderOf z) → z ∈ Subgroup.centralizer {(y : G)} →
      ρ.character ((y : G) ^ h * z) = c) :
    (∀ (g : K) (v : Representation.invariants ((ρ.comp K.subtype).comp O.subtype)),
        (fixedSpaceQuotientRepresentation ρ K O (g : K ⧸ O) v : V) = ρ g v) ∧
    (0 ≤ (fixedSpaceQuotientRepresentation ρ K O).character 1 ∧
      (fixedSpaceQuotientRepresentation ρ K O).character 1 ≤ ρ.character 1) ∧
    (∀ h : ℤ, Odd h → ∀ z : K ⧸ O, Odd (orderOf z) → z ∈ Subgroup.centralizer {(y : K ⧸ O)} →
      (fixedSpaceQuotientRepresentation ρ K O).character ((y : K ⧸ O) ^ h * z) = c ∧
      ∀ x : K ⧸ O,
        (fixedSpaceQuotientRepresentation ρ K O).character (x * ((y : K ⧸ O) ^ h * z) * x⁻¹) =
          c) ∧
    (∀ g : K, (fixedSpaceQuotientRepresentation ρ K O).character (g : K ⧸ O) =
      (Nat.card O : ℂ)⁻¹ * ∑ o : O, ρ.character ((g : G) * ((o : K) : G))) ∧
    ((fixedSpaceQuotientRepresentation ρ K O).character 1 = ρ.character 1 ↔
      O.map K.subtype ≤ MonoidHom.ker ρ) := by
  have hval : ∀ h : ℤ, Odd h → ∀ z : K ⧸ O, Odd (orderOf z) →
      z ∈ Subgroup.centralizer {(y : K ⧸ O)} →
      (fixedSpaceQuotientRepresentation ρ K O).character ((y : K ⧸ O) ^ h * z) = c := by
    intro h hh z hz hzy
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ((y : K ⧸ O) ^ h * z)
    rw [← hg, fixedSpaceQuotientRepresentation_character_mk]
    have hterm : ∀ o : O, ρ.character ((g : G) * ((o : K) : G)) = c := by
      intro o
      have hx : ((g * (o : K) : K) : K ⧸ O) = (y : K ⧸ O) ^ h * z := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (o : K)).mpr o.2, mul_one, hg]
      obtain ⟨e, v, hev, hv, hvy⟩ := exists_conj_eq_zpow_mul_of_mk_eq hO hy hh hz hzy hx
      have h1 : ρ.character ((g : G) * ((o : K) : G)) = ρ.character ((y : G) ^ h * (v : G)) := by
        rw [← Representation.char_conj ρ _ (e : G)]
        congr 1
        simpa using congrArg Subtype.val hev
      rw [h1]
      apply hc h hh (v : G)
      · rwa [Subgroup.orderOf_coe]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val hvy.eq
    rw [Finset.sum_congr rfl fun o _ => hterm o, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    have hne : (Nat.card O : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp
  refine ⟨fun g v => rfl, ⟨?_, ?_⟩, fun h hh z hz hzy => ⟨hval h hh z hz hzy, fun x => ?_⟩,
    fixedSpaceQuotientRepresentation_character_mk ρ K O, ?_⟩
  · rw [fixedSpaceQuotientRepresentation_character_one]
    exact_mod_cast Nat.zero_le _
  · rw [fixedSpaceQuotientRepresentation_character_one, Representation.char_one]
    exact_mod_cast Submodule.finrank_le _
  · rw [Representation.char_conj]
    exact hval h hh z hz hzy
  · rw [fixedSpaceQuotientRepresentation_character_one, Representation.char_one, Nat.cast_inj,
      finrank_invariants_eq_finrank_iff, Subgroup.map_le_iff_le_comap, MonoidHom.comap_ker]

end Character

end CFSG.Wreathed
