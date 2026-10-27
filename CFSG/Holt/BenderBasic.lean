module

public import CFSG.Holt.MaximalFixer
public import CFSG.Holt.PSL2Natural.Defs
import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences
import CFSG.Timmesfeld.Bridge.StrongEmbedding
import CFSG.Dihedral.BrauerSuzuki.Helpers
import CFSG.SignalizerFunctorTheorem.CatalogBridge.BenderSection
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingOddCore

public section

namespace CFSG.Holt

open MulAction CFSG.Open
open scoped MatrixGroups LinearAlgebra.Projectivization

variable {K : Type*} [Group K] {Ω : Type*} [MulAction K Ω]

theorem commute_of_sq_eq_one {V : Subgroup K} (hV2 : ∀ v ∈ V, v ^ 2 = 1) {v w : K}
    (hv : v ∈ V) (hw : w ∈ V) : Commute v w := by
  have key : ∀ x ∈ V, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV2 x hx)
  change v * w = w * v
  rw [← key _ (V.mul_mem hv hw), mul_inv_rev, key v hv, key w hw]

theorem exists_mem_ne_one_of_card_eq_four {V : Subgroup K} (hV : Nat.card V = 4) :
    ∃ v ∈ V, v ≠ 1 := by
  have hne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV
    omega
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨v, hv, fun h => hv1 (Subtype.ext h)⟩

theorem even_card_of_card_eq_four [Finite K] {V : Subgroup K} (hV : Nat.card V = 4) :
    Even (Nat.card K) := by
  have h := Subgroup.card_subgroup_dvd_card V
  rw [hV] at h
  exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) h)

theorem isPGroup_of_sq_eq_one {V : Subgroup K} (hV2 : ∀ v ∈ V, v ^ 2 = 1) : IsPGroup 2 V :=
  fun v => ⟨1, by rw [pow_one]; exact Subtype.ext (hV2 v v.2)⟩

theorem exists_le_stabilizer_of_fourGroup
    (hinv : ∀ g : K, orderOf g = 2 → ∃! ω : Ω, g • ω = ω)
    {V : Subgroup K} (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    ∃ α : Ω, V ≤ stabilizer K α := by
  obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_card_eq_four hV
  obtain ⟨α, hα⟩ := exists_fixes_exactly (hinv v (orderOf_eq_prime (hV2 v hvV) hv1))
  exact ⟨α, fun w hw => smul_eq_of_commute hα (commute_of_sq_eq_one hV2 hw hvV)⟩

theorem nontrivial_of_faithfulSMul [FaithfulSMul K Ω] {v : K} (hv : v ≠ 1) : Nontrivial Ω := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hv (eq_of_smul_eq_smul (α := Ω) fun ω => Subsingleton.elim _ _)

section Finite

variable [Finite K]

theorem eq_bot_of_normal_of_odd_card [FaithfulSMul K Ω] [IsPretransitive K Ω]
    (hinv : ∀ g : K, orderOf g = 2 → ∃! ω : Ω, g • ω = ω)
    {V : Subgroup K} (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    {R : Subgroup K} (hR : R.Normal) (hodd : Odd (Nat.card R)) : R = ⊥ := by
  obtain ⟨α, hVα⟩ := exists_le_stabilizer_of_fourGroup hinv hV hV2
  obtain ⟨v, -, hv1⟩ := exists_mem_ne_one_of_card_eq_four hV
  have : Nontrivial Ω := nontrivial_of_faithfulSMul hv1
  have hH := fusionStronglyEmbedded_stabilizer_of_forall_existsUnique
    (even_card_of_card_eq_four hV) hinv α
  have hRα : R ≤ stabilizer K α :=
    CFSG.BenderSuzuki.fourGroup_odd_subgroup_le_stronglyEmbedded
      (CFSG.ShultStronglyClosedTI.native_strong_embedding_of_order_conditions hH) hVα hV
      (fun u => Subtype.ext (hV2 u u.2)) Subgroup.le_normalizer_of_normal hodd
  refine (Subgroup.eq_bot_iff_forall R).mpr fun r hr =>
    eq_of_smul_eq_smul (α := Ω) fun ω => ?_
  obtain ⟨g, rfl⟩ := exists_smul_eq K α ω
  have h := hRα (hR.conj_mem r hr g⁻¹)
  rw [mem_stabilizer_iff, inv_inv, mul_smul, mul_smul, inv_smul_eq_iff] at h
  rw [one_smul, h]

theorem fusionOddCore_eq_bot [FaithfulSMul K Ω] [IsPretransitive K Ω]
    (hinv : ∀ g : K, orderOf g = 2 → ∃! ω : Ω, g • ω = ω)
    {V : Subgroup K} (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    fusionOddCore K = ⊥ := by
  unfold fusionOddCore
  exact sSup_eq_bot.mpr fun R hR => eq_bot_of_normal_of_odd_card hinv hV hV2 hR.1 hR.2

theorem le_of_isPGroup_of_odd_index {N : Subgroup K} [N.Normal] (hN : Odd N.index)
    {P : Subgroup K} (hP : IsPGroup 2 P) : P ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (hP.map (QuotientGroup.mk' N)).exists_card_eq
  have hdvd : Nat.card (P.map (QuotientGroup.mk' N)) ∣ Nat.card (K ⧸ N) :=
    Subgroup.card_subgroup_dvd_card _
  rw [hn] at hdvd
  have hn0 : n = 0 := by
    by_contra h0
    exact Nat.not_even_iff_odd.mpr (hN.of_dvd_nat hdvd) ((Nat.even_pow' h0).mpr even_two)
  rw [hn0, pow_zero] at hn
  have hbot := Subgroup.card_eq_one.mp hn
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

omit [Finite K] in
theorem isPretransitive_of_normal [Finite Ω] [IsPretransitive K Ω] {N : Subgroup K}
    (hN : N.Normal) {v : K} (hv : orderOf v = 2) (hvN : v ∈ N) (hfix : ∃! ω : Ω, v • ω = ω) :
    IsPretransitive N Ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := exists_fixes_exactly hfix
  apply isPretransitive_of_forall_exists_fixSet_eq_singleton 2
  intro δ
  obtain ⟨g, rfl⟩ := exists_smul_eq K α δ
  let d : N := ⟨g * v * g⁻¹, hN.conj_mem v hvN g⟩
  have hd : orderOf d = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_eq_of_isConj (isConj_iff.mpr ⟨g, rfl⟩)).symm.trans hv
  refine ⟨Subgroup.zpowers d, isPGroup_zpowers_of_orderOf_eq_two hd, ?_⟩
  ext ω
  rw [fixSet_zpowers, mem_fixedBy, Set.mem_singleton_iff, Subgroup.smul_def]
  exact conj_smul_eq_self_iff hα g ω

omit [Finite K] in
theorem false_of_fourGroup_le_isCyclic {V C : Subgroup K} (hV : Nat.card V = 4)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) [IsCyclic C] (hVC : V ≤ C) : False := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  let e := Subgroup.subgroupOfEquivOfLe hVC
  have : IsCyclic V := isCyclic_of_surjective e e.surjective
  exact CFSG.BenderSuzuki.noncyclic_of_card_four_and_sq_one hV
    (fun u => Subtype.ext (hV2 u u.2)) this

omit [Finite K] in
theorem not_forall_sylow_cyclic_or_quaternion {V : Subgroup K} (hV : Nat.card V = 4)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    ¬ ∀ S : Sylow 2 K, IsCyclic (S : Subgroup K) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  intro h
  obtain ⟨S, hVS⟩ := (isPGroup_of_sq_eq_one hV2).exists_le_sylow
  rcases h S with hcyc | ⟨r, -, ⟨e⟩⟩
  · exact false_of_fourGroup_le_isCyclic hV hV2 hVS
  · have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
    obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_card_eq_four hV
    refine false_of_fourGroup_le_isCyclic (C := Subgroup.zpowers v) hV hV2 fun w hw => ?_
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    · have hvw : (⟨w, hVS hw⟩ : (S : Subgroup K)) = ⟨v, hVS hvV⟩ :=
        CFSG.BrauerSuzuki.Helpers.unique_order_two_of_mulEquiv_quaternion e
          (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime (hV2 w hw) hw1)
          (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime (hV2 v hvV) hv1)
      rw [show w = v from congrArg Subtype.val hvw]
      exact Subgroup.mem_zpowers v

section Coset

variable {X : Type*} [Group X] [Finite X] {H : Subgroup X}

theorem odd_card_normalCore (hH : fusionStronglyEmbedded H) : Odd (Nat.card H.normalCore) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨g, hg⟩ : ∃ g : X, g ∉ H := by
    by_contra h
    push Not at h
    exact hH.1 (eq_top_iff.mpr fun g _ => h g)
  exact hg (CFSG.Timmesfeld.Bridge.mem_of_involution_mem hH (H.normalCore_le t.2)
    (H.normalCore_le ((inferInstance : H.normalCore.Normal).conj_mem _ t.2 g))
    (by rw [Subgroup.orderOf_coe, ht]))

theorem faithfulSMul_quotient (hH : fusionStronglyEmbedded H)
    (hO : ∀ R : Subgroup X, R.Normal → Odd (Nat.card R) → R = ⊥) :
    FaithfulSMul X (X ⧸ H) := by
  have hcore := hO _ inferInstance (odd_card_normalCore hH)
  refine ⟨fun {x y} h => ?_⟩
  have hmem : y⁻¹ * x ∈ H.normalCore := by
    rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker]
    refine Equiv.ext fun a => ?_
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, mul_smul, h a, inv_smul_smul]
    rfl
  rw [hcore, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem).symm

theorem existsUnique_fixed_quotient (hH : fusionStronglyEmbedded H) {t : X}
    (ht : orderOf t = 2) : ∃! y : X ⧸ H, t • y = y := by
  have key : ∀ a : X, t • (a : X ⧸ H) = a ↔ a⁻¹ * t * a ∈ H := by
    intro a
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
      ← H.inv_mem_iff (x := (t * a)⁻¹ * a)]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  obtain ⟨P, hPH⟩ := CFSG.Timmesfeld.Bridge.exists_sylow_le hH
  obtain ⟨g, hg⟩ := CFSG.Timmesfeld.Bridge.exists_conj_mem_sylow P (n := 1)
    (by rw [pow_one, ← ht, pow_orderOf_eq_one])
  refine ⟨((g⁻¹ : X) : X ⧸ H), (key _).mpr (by rw [inv_inv]; exact hPH hg), ?_⟩
  intro y hy
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [QuotientGroup.eq]
  refine CFSG.Timmesfeld.Bridge.mem_of_involution_mem hH (hPH hg) ?_
    ((orderOf_eq_of_isConj (isConj_iff.mpr ⟨g, rfl⟩)).symm.trans ht)
  convert (key b).mp hy using 1
  group

end Coset

end Finite

theorem isNaturalPSL2_of_equiv [FaithfulSMul K Ω] {N : Subgroup K} [IsPretransitive N Ω] {α : Ω}
    {f : ℕ} (ιe : N ≃* PSL(2, GaloisField 2 f))
    (φ : N ⧸ stabilizer N α ≃ ℙ (GaloisField 2 f) (Fin 2 → GaloisField 2 f))
    (hφ : ∀ (l : N) (x : N ⧸ stabilizer N α), φ (l • x) = ιe l • φ x) :
    IsNaturalPSL2 (N.map (MulAction.toPermHom K Ω)) f := by
  let ρ : N →* Equiv.Perm Ω := (MulAction.toPermHom K Ω).comp N.subtype
  have hρ : Function.Injective ρ := fun n m h =>
    Subtype.ext (eq_of_smul_eq_smul (α := Ω) fun ω => congrArg (fun π : Equiv.Perm Ω => π ω) h)
  have hrange : ρ.range = N.map (MulAction.toPermHom K Ω) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eΩ : N ⧸ stabilizer N α ≃ Ω := Equiv.ofBijective (MulAction.ofQuotientStabilizer N α)
    ⟨MulAction.injective_ofQuotientStabilizer N α, fun ω => by
      obtain ⟨n, rfl⟩ := exists_smul_eq N α ω
      exact ⟨(n : N ⧸ stabilizer N α), MulAction.ofQuotientStabilizer_mk N α n⟩⟩
  refine ⟨ιe.symm.trans ((MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr hrange)),
    φ.symm.trans eΩ, fun g p => ?_⟩
  obtain ⟨x, rfl⟩ := φ.surjective p
  obtain ⟨n, rfl⟩ := ιe.surjective g
  rw [← hφ]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  change MulAction.ofQuotientStabilizer N α (n • x) = ρ n (MulAction.ofQuotientStabilizer N α x)
  rw [MulAction.ofQuotientStabilizer_smul]
  rfl

variable (Ω) in
structure IsBenderNormal (N : Subgroup K) (q i : ℕ) : Prop where
  normal : N.Normal
  odd_index : Odd N.index
  model : (i = 1 ∧ ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (N ≃* PSL(2, GaloisField 2 f))) ∨
    (i = 2 ∧ ∃ a : ℕ, 1 ≤ a ∧ q = 2 ^ (2 * a + 1) ∧ Nonempty (N ≃* Sz a)) ∨
    (i = 3 ∧ ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (N ≃* PSU3 2 f))
  benderBorel : fusionBenderBorel N q i
  isPretransitive : IsPretransitive N Ω
  card_eq : Nat.card Ω = q ^ i + 1
  stabilizer_eq_normalizer : ∀ (ω : Ω) (Q : Sylow 2 N), (Q : Subgroup N) ≤ stabilizer N ω →
    stabilizer N ω = Subgroup.normalizer ((Q : Subgroup N) : Set N)
  natural : ∀ f : ℕ, i = 1 → q = 2 ^ f → IsNaturalPSL2 (N.map (MulAction.toPermHom K Ω)) f

namespace IsBenderNormal

variable {N : Subgroup K} {q i : ℕ}

theorem params (h : IsBenderNormal Ω N q i) : 4 ≤ q ∧ 2 ∣ q ∧ 1 ≤ i ∧ i ≤ 3 := by
  have key : ∀ f : ℕ, 2 ≤ f → 4 ≤ 2 ^ f ∧ 2 ∣ 2 ^ f := fun f hf =>
    ⟨by calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf,
      dvd_pow_self 2 (by omega)⟩
  rcases h.model with ⟨rfl, f, hf, rfl, -⟩ | ⟨rfl, a, ha, rfl, -⟩ | ⟨rfl, f, hf, rfl, -⟩
  · exact ⟨(key f hf).1, (key f hf).2, le_rfl, by norm_num⟩
  · exact ⟨(key _ (by omega)).1, (key _ (by omega)).2, by norm_num, by norm_num⟩
  · exact ⟨(key f hf).1, (key f hf).2, by norm_num, le_rfl⟩

theorem fusionIsBenderGroup (h : IsBenderNormal Ω N q i) : CFSG.Open.fusionIsBenderGroup N := by
  rcases h.model with ⟨-, f, hf, -, he⟩ | ⟨-, a, ha, -, he⟩ | ⟨-, f, hf, -, he⟩
  · exact Or.inl ⟨f, hf, he⟩
  · exact Or.inr (Or.inr ⟨a, ha, he⟩)
  · exact Or.inr (Or.inl ⟨f, hf, he⟩)

theorem odd_card (h : IsBenderNormal Ω N q i) : Odd (Nat.card Ω) := by
  obtain ⟨-, h2, h1, -⟩ := h.params
  rw [h.card_eq]
  exact (even_iff_two_dvd.mpr (dvd_pow h2 (by omega))).add_one

theorem exists_sylow_le_stabilizer [Finite K] [Finite Ω] (h : IsBenderNormal Ω N q i)
    (ω : Ω) : ∃ Q : Sylow 2 N, (Q : Subgroup N) ≤ stabilizer N ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.isPretransitive
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 N) := inferInstance
  obtain ⟨ω₀, hω₀⟩ := fixSet_nonempty_of_odd h.odd_card Q₀.isPGroup'
  obtain ⟨n, rfl⟩ := exists_smul_eq N ω₀ ω
  refine ⟨n • Q₀, fun x hx => ?_⟩
  have hx' := hω₀ _ (mem_smul_sylow_iff.mp hx)
  rw [mul_smul, mul_smul, inv_smul_eq_iff] at hx'
  exact hx'

theorem isSolvable_stabilizer [Finite K] [Finite Ω] (h : IsBenderNormal Ω N q i) (ω : Ω) :
    Group.IsSolvable (stabilizer N ω) := by
  obtain ⟨Q, hQ⟩ := h.exists_sylow_le_stabilizer ω
  rw [h.stabilizer_eq_normalizer ω Q hQ]
  exact CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_normalizer_of_benderBorel
    h.benderBorel Q

theorem isSolvable_stabilizer_inf [Finite K] [Finite Ω] (h : IsBenderNormal Ω N q i) (ω : Ω) :
    Group.IsSolvable ↥(stabilizer K ω ⊓ N) := by
  have := h.isSolvable_stabilizer ω
  have heq : stabilizer N ω = (stabilizer K ω ⊓ N).subgroupOf N := by
    rw [Subgroup.inf_subgroupOf_right, MulAction.stabilizer_subgroupOf]
  let e := (MulEquiv.subgroupCongr heq).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem le_of_isPGroup [Finite K] (h : IsBenderNormal Ω N q i) {P : Subgroup K}
    (hP : IsPGroup 2 P) : P ≤ N := by
  have := h.normal
  exact le_of_isPGroup_of_odd_index h.odd_index hP

theorem card_sylow [Finite K] (h : IsBenderNormal Ω N q i) (S : Sylow 2 K) :
    Nat.card (S : Subgroup K) = q ^ i := by
  have hSN := h.le_of_isPGroup S.isPGroup'
  rw [← (h.benderBorel (S.subtype hSN)).2.2.2.2, Sylow.coe_subtype]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv.symm

theorem card_center_sylow [Finite K] (h : IsBenderNormal Ω N q i) (S : Sylow 2 K) :
    Nat.card (Subgroup.center (S : Subgroup K)) = q := by
  have hSN := h.le_of_isPGroup S.isPGroup'
  rw [← (h.benderBorel (S.subtype hSN)).2.2.2.1, Sylow.coe_subtype]
  exact Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hSN)).toEquiv.symm

theorem four_le_card_center_sylow [Finite K] (h : IsBenderNormal Ω N q i) (S : Sylow 2 K) :
    4 ≤ Nat.card (Subgroup.center (S : Subgroup K)) :=
  (h.card_center_sylow S).symm ▸ h.params.1

theorem card_eq_card_sylow_add_one [Finite K] (h : IsBenderNormal Ω N q i) (S : Sylow 2 K) :
    Nat.card Ω = Nat.card (S : Subgroup K) + 1 := by
  rw [h.card_eq, h.card_sylow S]

theorem isSolvable_stabilizer_ambient [Finite K] [Finite Ω] (h : IsBenderNormal Ω N q i)
    (ω : Ω) : Group.IsSolvable (stabilizer K ω) := by
  have := h.normal
  have := h.isSolvable_stabilizer_inf ω
  have : Group.IsSolvable (K ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ h.odd_index
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (inf_le_left : stabilizer K ω ⊓ N ≤ stabilizer K ω))
    ((QuotientGroup.mk' N).comp (stabilizer K ω).subtype) fun x hx => ?_
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  exact ⟨⟨x, x.2, hx⟩, rfl⟩

end IsBenderNormal

end CFSG.Holt
