module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2323b2
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang.Family
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SmallField
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.LargeExtraspecial.S45QPhi
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141e
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141f

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2323b
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)

theorem nonempty_commutator_sub_equiv {S : Type} [Group S] (J : Subgroup S) :
    Nonempty (↥⁅J, J⁆ ≃* ↥(commutator ↥J)) :=
  ⟨(((commutator ↥J).equivMapOfInjective J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator J))).symm⟩

theorem nonempty_commutator_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (↥(commutator A) ≃* ↥(commutator B)) := by
  have h : (commutator A).map e.toMonoidHom = commutator B := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  exact ⟨(e.subgroupMap (commutator A)).trans (MulEquiv.subgroupCongr h)⟩

section Criteria

variable {S : Type} [Group S] [Finite S]

theorem isSubnormal_of_normal {M C : Subgroup S} (hMC : M ≤ C) (hMn : (M.subgroupOf C).Normal) :
    CFSG.Open.IsSubnormal M C :=
  CFSG.Open.IsSubnormal.step hMC hMn (CFSG.Open.IsSubnormal.refl _)

theorem twoInCoreLayer_of_normal {β : MulAut S} {p : ℕ} (hp : p.Prime) (M : Subgroup S)
    (hMC : M ≤ fixSubgroup β) (hMn : (M.subgroupOf (fixSubgroup β)).Normal)
    (hM2 : ∀ x ∈ fixSubgroup β, IsPGroup 2 ↥(Subgroup.zpowers x) → x ∈ M)
    (hM : CFSG.Open.IsQuasisimple ↥M ∨ Nat.Coprime p (Nat.card M)) : TwoInCoreLayer p β := by
  intro x hx hx2
  have hxM := hM2 x hx hx2
  have hsub := isSubnormal_of_normal hMC hMn
  rcases hM with hq | hcop
  · exact le_core_sup_layer_of_isComponentOf hp ⟨hMC, hsub, hq⟩ hxM
  · exact Subgroup.mem_sup_left (le_glaPPrimeCoreOf_of_isSubnormal hp hsub hcop hxM)

theorem twoInCoreLayer_of_normal' {β : MulAut S} {p : ℕ} (hp : p.Prime) (M : Subgroup ↥(fixSubgroup β))
    (hMn : M.Normal) (hM2 : ∀ g : ↥(fixSubgroup β), IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ M)
    (hM : CFSG.IsQuasisimple ↥M ∨ Nat.Coprime p (Nat.card M)) : TwoInCoreLayer p β := by
  set M' : Subgroup S := M.map (fixSubgroup β).subtype with hM'
  have hMC : M' ≤ fixSubgroup β := Subgroup.map_subtype_le M
  have hM'eq : M'.subgroupOf (fixSubgroup β) = M :=
    Subgroup.comap_map_eq_self_of_injective (fixSubgroup β).subtype_injective M
  refine twoInCoreLayer_of_normal hp M' hMC (hM'eq ▸ hMn) (fun x hx hx2 => ?_) ?_
  · obtain ⟨m, hm⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hx2
    exact ⟨⟨x, hx⟩, hM2 _ (Inputs141d.isPGroup_zpowers_of_pow (m := m) (Subtype.ext (by simpa using hm))), rfl⟩
  · rcases hM with hq | hcop
    · left
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv (M.equivMapOfInjective _ (fixSubgroup β).subtype_injective) hq)
    · right
      rwa [hM', Subgroup.card_map_of_injective (fixSubgroup β).subtype_injective]

theorem twoInCoreLayer_of_fixSubgroup_eq {β γ : MulAut S} {p : ℕ} (h : fixSubgroup β = fixSubgroup γ)
    (hβ : TwoInCoreLayer p β) : TwoInCoreLayer p γ := by
  intro x hx hx2
  rw [← h] at hx ⊢
  exact hβ x hx hx2

theorem twoInCoreLayer_of_pow_pow {β : MulAut S} {p r s : ℕ} (hrs : (β ^ r) ^ s = β)
    (h : TwoInCoreLayer p (β ^ r)) : TwoInCoreLayer p β :=
  twoInCoreLayer_of_fixSubgroup_eq
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_pow_eq_of_pow_pow' hrs) h

end Criteria

section FieldUntw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise


theorem exists_fixed_normal_two (τ : Tag) {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    ∃ J : Subgroup ↥(adjointGroup τ K), J ≤ fixSubgroup (entrywiseAdjointAut τ σ) ∧
      (J.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))).Normal ∧
      Nonempty (↥J ≃* ↥(adjointGroup τ (fixSubfield σ))) ∧
      ∀ x ∈ fixSubgroup (entrywiseAdjointAut τ σ), IsPGroup 2 ↥(Subgroup.zpowers x) → x ∈ J := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨-, hinj, -, hJΓ, hΓeq, hJnormal, -⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have : Finite (fixSubfield σ) := inferInstance
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun g hg => (hJΓ hg).1
  have hΓnorm : entrywiseFixedGroup τ σ ≤
      Subgroup.normalizer (fixedFieldImage τ σ : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJΓ).1 hJnormal
  have hfix : ∀ x : adjointGroup τ K,
      x ∈ fixSubgroup (entrywiseAdjointAut τ σ) ↔
        (x : ModGL τ K) ∈ entrywiseFixedGroup τ σ := fun x => by
    rw [mem_fixSubgroup, mem_entrywiseFixedGroup]
    constructor
    · intro h
      exact ⟨x.2, (coe_entrywiseAdjointAut τ σ x).symm.trans (congrArg Subtype.val h)⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext ((coe_entrywiseAdjointAut τ σ x).trans h)
  let J : Subgroup ↥(adjointGroup τ K) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
  have hJmem : ∀ x : adjointGroup τ K, x ∈ J ↔ (x : ModGL τ K) ∈ fixedFieldImage τ σ := fun x => Iff.rfl
  have hJle : J ≤ fixSubgroup (entrywiseAdjointAut τ σ) := fun x hx => (hfix x).2 (hJΓ ((hJmem x).1 hx))
  have hJn : (J.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).2 fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hJmem, hJmem]
    exact Subgroup.mem_normalizer_iff.1 (hΓnorm ((hfix g).1 hg)) (h : ModGL τ K)
  let eJ : J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans
      ((adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ hinj).symm
  refine ⟨J, hJle, hJn, ⟨eJ⟩, fun x hx hx2 => ?_⟩
  obtain ⟨m, hm⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hx2
  have hxΓ : (x : ModGL τ K) ∈ entrywiseFixedGroup τ σ := (hfix x).1 hx
  let N := (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)
  let y : ↥(entrywiseFixedGroup τ σ) := ⟨_, hxΓ⟩
  have hy2 : y ^ (2 ^ m) = 1 := by
    apply Subtype.ext
    have h1 := congrArg (fun z : adjointGroup τ K => (z : ModGL τ K)) hm
    simpa using h1
  have hmem : (y : ModGL τ K) ∈ (entrywiseFixedTorus τ σ : Set (ModGL τ K)) *
      (fixedFieldImage τ σ : Set (ModGL τ K)) := by
    rw [← hΓeq]
    exact hxΓ
  obtain ⟨t, ht, j, hj, htj⟩ := Set.mem_mul.1 hmem
  have htΓ : t ∈ entrywiseFixedGroup τ σ := ht.2
  have hjΓ : j ∈ entrywiseFixedGroup τ σ := hJΓ hj
  have hyeq : y = ⟨t, htΓ⟩ * ⟨j, hjΓ⟩ := Subtype.ext htj.symm
  have hjN : (⟨j, hjΓ⟩ : ↥(entrywiseFixedGroup τ σ)) ∈ N := hj
  have hqy : (QuotientGroup.mk y : ↥(entrywiseFixedGroup τ σ) ⧸ N) = QuotientGroup.mk ⟨t, htΓ⟩ := by
    rw [hyeq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hjN, mul_one]
  have ht1 : (⟨t, htΓ⟩ : ↥(entrywiseFixedGroup τ σ)) ^ (Nat.card K - 1) = 1 :=
    Subtype.ext (by
      simpa using pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ht.1))
  have hA : (QuotientGroup.mk y : ↥(entrywiseFixedGroup τ σ) ⧸ N) ^ (2 ^ m) = 1 := by
    rw [← QuotientGroup.mk_pow, hy2, QuotientGroup.mk_one]
  have hB : (QuotientGroup.mk y : ↥(entrywiseFixedGroup τ σ) ⧸ N) ^ (Nat.card K - 1) = 1 := by
    rw [hqy, ← QuotientGroup.mk_pow, ht1, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (2 ^ m) (Nat.card K - 1) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.2 Inputs141e.odd_card_sub_one)
  have h1 := (pow_gcd_eq_one (a := (QuotientGroup.mk y : ↥(entrywiseFixedGroup τ σ) ⧸ N))).2 ⟨hA, hB⟩
  rw [hcop.gcd_eq_one, pow_one, QuotientGroup.eq_one_iff] at h1
  exact (hJmem x).2 h1

theorem coprime_12096 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : p ≠ 7) : Nat.Coprime p 12096 := by
  rw [show (12096 : ℕ) = (2 ^ 6 * 3 ^ 3) * 7 by norm_num]
  refine Nat.Coprime.mul_right (coprime_two_pow_mul_three_pow hp hp5 6 3) ?_
  exact (Nat.coprime_primes hp (by norm_num)).2 hp7

theorem twoInCoreLayer_entrywiseAdjointAut (τ : Tag) {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hG2 : τ = .G2 → Nat.card (fixSubfield σ) = 2 → p ≠ 7) :
    TwoInCoreLayer p (entrywiseAdjointAut τ σ) := by
  classical
  obtain ⟨J, hJle, hJn, ⟨eJ⟩, hJ2⟩ := exists_fixed_normal_two τ σ
  refine twoInCoreLayer_of_normal hp J hJle hJn hJ2 ?_
  haveI : Finite (fixSubfield σ) := Subtype.finite
  by_cases hsmall : τ = .G2 ∧ Nat.card (fixSubfield σ) = 2
  · right
    obtain ⟨rfl, hk2⟩ := hsmall
    rw [Nat.card_congr eJ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk2]
    exact coprime_12096 hp hp5 (hG2 rfl hk2)
  · left
    have hk3 : τ = .G2 → 3 ≤ Nat.card (fixSubfield σ) := by
      intro h
      have h2' : 1 < Nat.card (fixSubfield σ) := Finite.one_lt_card
      have : Nat.card (fixSubfield σ) ≠ 2 := fun h' => hsmall ⟨h, h'⟩
      omega
    have hperf := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup τ
      (fixSubfield σ) hk3
    obtain ⟨hs, hnc⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isSimpleGroup_adjointGroup_of_perfect τ
        (fixSubfield σ) hperf
    haveI := hs
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1)

end FieldUntw

section FieldTwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley (subfieldRootGroupImage)
open scoped Pointwise commutatorElement


theorem twoInCoreLayer_fieldActor_twE6 {d m : ℕ} (hd : 1 ≤ d) (hm : 3 ≤ m) (hmodd : Odd m) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * d * m)) (κ : K ≃+* K)
    (hκ : ∀ c, κ c = c ^ 2 ^ (2 * d)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ (d * m))
    (σ₀ : fixSubfield κ ≃+* fixSubfield κ) (hσ₀ : ∀ c, (σ₀ c : K) = (c : K) ^ 2 ^ d) (ε : K ≃+* K)
    (hε : ∀ c, ε c = c ^ 2 ^ (d * (m + 1))) {p : ℕ} (hp : p.Prime) :
    TwoInCoreLayer p (fieldActor (t := TwistTag.E6) σ ε) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * d * m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, hJC, -, hder, hsimpleJ, hncJ, -⟩ :=
    CFSG.RankThree.Chevalley.twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      Nat.prime_two hd hm hmodd K hK κ hκ σ hσ σ₀ hσ₀ ε hε
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ with hJdef
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδdef
  set F := fixSubgroup δ with hFdef
  have hFeq : F = MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id ↥C) := Subgroup.ext fun _ => Iff.rfl
  have hder' : ⁅F, F⁆ = J.subgroupOf C := by rw [hFeq]; exact hder
  set ψ : K ≃+* K := σ * ε with hψdef
  have hψc : ∀ c, ψ c = c ^ 2 ^ d := by
    intro c
    show σ (ε c) = _
    rw [hε, hσ, ← pow_mul, ← pow_add, show d * (m + 1) + d * m = 2 * d * m + d by ring, pow_add,
      pow_mul, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hψι : ∀ c : fixSubfield κ, ψ.toRingHom ((fixSubfield κ).subtype c) =
      (fixSubfield κ).subtype (σ₀.toRingHom c) := fun c => by
    change ψ (c : K) = (σ₀ c : K)
    rw [hσ₀, hψc]
  have hpar : ∀ a, ∀ c ∈ orbitField TwistTag.E6 K ψ.toRingHom a,
      ∃ c₀ ∈ orbitField TwistTag.E6 (fixSubfield κ) σ₀.toRingHom a, (fixSubfield κ).subtype c₀ = c := by
    intro a c hc
    have h2 : ψ (ψ c) = c := by
      rw [mem_orbitField] at hc
      obtain ⟨n, hn⟩ := a
      have hn' : n < 4 := hn
      interval_cases n
      · rw [show (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 by decide, pow_two] at hc
        exact hc
      · rw [show (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 by decide, pow_two] at hc
        exact hc
      · rw [show (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 by decide, pow_one] at hc
        change ψ c = c at hc
        rw [hc, hc]
      · rw [show (TwistTag.E6.orbit ⟨3, by decide⟩).card = 1 by decide, pow_one] at hc
        change ψ c = c at hc
        rw [hc, hc]
    have hck : κ c = c := by
      rw [hψc, hψc, ← pow_mul, ← pow_add, show d + d = 2 * d by ring] at h2
      rw [hκ]
      exact h2
    obtain ⟨c₀, rfl⟩ : ∃ c₀ : fixSubfield κ, (fixSubfield κ).subtype c₀ = c := ⟨⟨c, hck⟩, rfl⟩
    refine ⟨c₀, ?_, rfl⟩
    rw [mem_orbitField] at hc ⊢
    apply (fixSubfield κ).subtype.injective
    rw [← ringHom_pow_apply_comm hψι, hc]
  have hCψJ : graphFixedRootGroup TwistTag.E6 K ψ.toRingHom ≤ J :=
    graphFixedRootGroup_le_map_baseChangeGL (ι := (fixSubfield κ).subtype) ψ.surjective hψι hpar
  have e1 : ↥(commutator ↥F) ≃* ↥(J.subgroupOf C) :=
    ((commutator ↥F).equivMapOfInjective F.subtype F.subtype_injective).trans
      (MulEquiv.subgroupCongr ((Subgroup.map_subtype_commutator F).trans hder'))
  haveI := hsimpleJ
  have hncJ' : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hncJ hcon
  have hqJ : CFSG.IsQuasisimple ↥J := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncJ').1
  have hq : CFSG.IsQuasisimple ↥(commutator ↥F) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans (Subgroup.subgroupOfEquivOfLe hJC)).symm hqJ
  refine twoInCoreLayer_of_normal' hp (commutator ↥F) inferInstance (fun g hg2 => ?_) (Or.inl hq)
  set y : ModGL TwistTag.E6.tag K := ((g : ↥C) : ModGL TwistTag.E6.tag K) with hydef
  have hgfix : δ (g : ↥C) = (g : ↥C) := mem_fixSubgroup.1 g.2
  have hyε : Units.map (entrywiseHom ε.toRingHom) y = y := by
    have h1 := congrArg (fun x : ↥C => (x : ModGL TwistTag.E6.tag K)) hgfix
    simp only [hδdef, coe_fieldActor] at h1
    exact h1
  have hyσ : y ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ (g : ↥C).2
  have hyψ : y ∈ twistedFixedGroup TwistTag.E6 K ψ.toRingHom := by
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hyσ.1, ?_⟩
    have e2 : Units.map (entrywiseHom ψ.toRingHom) y =
        Units.map (entrywiseHom σ.toRingHom) (Units.map (entrywiseHom ε.toRingHom) y) := by
      apply Units.ext
      change entrywise ψ.toRingHom (y : Module.End K (RootModule TwistTag.E6.tag K)) =
        entrywise σ.toRingHom (entrywise ε.toRingHom (y : Module.End K (RootModule TwistTag.E6.tag K)))
      rw [entrywise_entrywise]
      rfl
    have e3 : twistHom TwistTag.E6 K ψ.toRingHom y =
        twistHom TwistTag.E6 K σ.toRingHom (Units.map (entrywiseHom ε.toRingHom) y) := by
      simp only [twistHom, MonoidHom.comp_apply]
      rw [e2]
    rw [e3, hyε]
    exact ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hyσ).2
  have hmul : y ∈ (graphFixedTorus TwistTag.E6 K ψ.toRingHom : Set (ModGL TwistTag.E6.tag K)) *
      (graphFixedRootGroup TwistTag.E6 K ψ.toRingHom : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← coe_twistedFixedGroup_eq_mul ψ.surjective]
    exact hyψ
  obtain ⟨h, hh, c, hc, hhc⟩ := Set.mem_mul.1 hmul
  have hhN : h ∈ Subgroup.normalizer
      (graphFixedRootGroup TwistTag.E6 K ψ.toRingHom : Set (ModGL TwistTag.E6.tag K)) :=
    graphFixedTorus_le_normalizer hh
  have hh1 : h ^ (Nat.card K - 1) = 1 :=
    pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh.1)
  have hy2 : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    have h1 := hg2.map (C.subtype.comp F.subtype)
    rwa [MonoidHom.map_zpowers] at h1
  rw [← hhc] at hy2
  have hyC : y ∈ J := by
    rw [← hhc]
    exact hCψJ (Inputs141e.mem_of_two_of_mul hhN hh1 Inputs141e.odd_card_sub_one hc hy2)
  have h1 : (g : ↥C) ∈ ⁅F, F⁆ := by
    rw [hder']
    exact Subgroup.mem_subgroupOf.2 hyC
  rw [← Subgroup.map_subtype_commutator] at h1
  obtain ⟨g', hg', hgg'⟩ := h1
  rwa [← Subtype.ext hgg']

theorem twoInCoreLayer_twE6_field {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ : β ^ p = 1) (hη1 : Θ β ≠ 1) :
    TwoInCoreLayer p β := by
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order Nat.prime_two hf K
      hK' σ hσ Θ hΘ hp (by omega) β hβ hη1
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality Nat.prime_two
      (by omega : 1 ≤ 2 * f) hK'
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ 2 ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hdp : d * p = f := by rw [hd, mul_comm]
  have hKdp : Nat.card K = 2 ^ (2 * d * p) := by rw [hK', mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ 2 ^ (d * p) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ 2 ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hδ := twoInCoreLayer_fieldActor_twE6 hd1 (by omega) (hp.odd_of_ne_two (by omega)) K hKdp κ hκ σ hσdp
    (fixSubfieldRestrict T κ) hσ₀ ε hε hp
  rw [← hψ] at hδ
  exact twoInCoreLayer_of_pow_pow hrs (twoInCoreLayer_of_conj ψ hp hδ)

end FieldTwE6

section FieldTriD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem twoInCoreLayer_triD4_field {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K))
    (hΘ : ∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ)
    {β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hβ : β ^ p = 1)
    (hβ1 : β ≠ 1) (hβout : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    TwoInCoreLayer p β := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβ hβ1
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    CFSG.RankThree.Chevalley.triality_noninner_large_prime_field_descent_and_local_core_trivial
      hℓ hf K hK σ hσ Θ hΘ hp (by omega) ⊤ le_top ⟨β, Subgroup.mem_top _⟩ hβout
      (by rw [Subgroup.orderOf_mk]; exact hβord)
  have hh₀' : MulAut.conj h₀ * β * (MulAut.conj h₀)⁻¹ =
      fieldActor (t := TwistTag.D4) σ (Θ β) := hh₀
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h, mul_zero] at hff'
      omega
    · exact h
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega)
      (by rw [hφord, hff']; exact ⟨p, by ring⟩), hφord, hff',
      show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ β) = Subgroup.zpowers δc :=
    CFSG.RankThree.PartOne.CTP.zpowers_ringEquiv_eq_of_orderOf hℓ (by omega : 1 ≤ 3 * f) hK3
      hηord hδcord
  have hfix_eq : fixSubgroup (fieldActor (t := TwistTag.D4) σ (Θ β)) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = ℓ ^ (3 * f' * p) := by
    rw [hK3, hff']; congr 1; ring
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by
    rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, -, -, -, -, hfixJ, hsimpJ, hncJ, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd
      hp.two_le hm3 K hK' σ hσ' δc hδc
  haveI := hsimpJ
  have e3 : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)) ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  haveI hsimE : IsSimpleGroup ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)) :=
    e3.isSimpleGroup
  have hncE : ∃ a b : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)), a * b ≠ b * a := by
    simp only [not_forall, ne_eq] at hncJ
    obtain ⟨a, b, hab⟩ := hncJ
    refine ⟨e3.symm a, e3.symm b, fun h => hab ?_⟩
    have h' := congrArg e3 h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  have hδT : TwoInCoreLayer p (fieldActor (t := TwistTag.D4) σ δc) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2323b.twoInCoreLayer_of_isQuasisimple_fixSubgroup hp
      (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hncE)
  have hΘT : TwoInCoreLayer p (fieldActor (t := TwistTag.D4) σ (Θ β)) :=
    twoInCoreLayer_of_fixSubgroup_eq hfix_eq.symm hδT
  rw [← hh₀'] at hΘT
  exact twoInCoreLayer_of_conj (MulAut.conj h₀) hp hΘT

end FieldTriD4

section LangDefs

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] noncomputable def ratTwo {τ : Tag}
    {L : Type} [Field L] (Ψ : Set (Fin τ.rank → ℤ)) (M : Subgroup (ModGL τ L)) : Subgroup (ModGL τ L) :=
  Subgroup.closure {g | g ∈ rootSpan τ L Ψ ∧ g ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers g)}

end LangDefs

section LangDecomp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped Pointwise


theorem mem_of_two_of_odd_pow_mem {G : Type} [Group G] {H : Subgroup G} {g : G} {m N : ℕ}
    (hg : g ^ (2 ^ m) = 1) (hN : Odd N) (hgN : g ^ N ∈ H) : g ∈ H := by
  have h1 : g ^ (2 ^ m) ∈ H := by rw [hg]; exact one_mem _
  exact Inputs141e.mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hN)) h1 hgN

theorem eq_one_of_two_of_odd {G : Type} [Group G] {g : G} {m N : ℕ} (hg : g ^ (2 ^ m) = 1)
    (hN : Odd N) (hgN : g ^ N = 1) : g = 1 := by
  have h := mem_of_two_of_odd_pow_mem (H := ⊥) hg hN (by rw [hgN]; exact one_mem _)
  simpa using h

theorem mem_rootSpan_of_two_p {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hap : ∀ i, a i ^ p = 1)
    {k : ModGL τ (AlgebraicClosure K)} (hk : k ∈ toralCentralizer τ (AlgebraicClosure K) a)
    (hk2 : IsPGroup 2 ↥(Subgroup.zpowers k)) :
    k ∈ rootSpan τ (AlgebraicClosure K) (rootCharKernel a) := by
  classical
  obtain ⟨-, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ (AlgebraicClosure K) a
  have h3 : IsPGroup p (↥(toralCentralizer τ (AlgebraicClosure K) a) ⧸
      (toralRootGroup τ (AlgebraicClosure K) a).subgroupOf (toralCentralizer τ (AlgebraicClosure K) a)) :=
    (isPGroup_quotient hp hap).of_surjective φ hφ
  have hkM : k ∈ toralRootGroup τ (AlgebraicClosure K) a := by
    obtain ⟨m, hm⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hk2
    set x : ↥(toralCentralizer τ (AlgebraicClosure K) a) := ⟨k, hk⟩ with hxdef
    obtain ⟨n, hn⟩ := h3 (QuotientGroup.mk x)
    have hx2 : x ^ (2 ^ m) = 1 := Subtype.ext (by simpa using hm)
    have hA : (QuotientGroup.mk x : ↥(toralCentralizer τ (AlgebraicClosure K) a) ⧸
        (toralRootGroup τ (AlgebraicClosure K) a).subgroupOf (toralCentralizer τ (AlgebraicClosure K) a)) ^
          (2 ^ m) = 1 := by
      rw [← QuotientGroup.mk_pow, hx2, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (2 ^ m) (p ^ n) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    have h1 := (pow_gcd_eq_one (a := (QuotientGroup.mk x : ↥(toralCentralizer τ (AlgebraicClosure K) a) ⧸
        (toralRootGroup τ (AlgebraicClosure K) a).subgroupOf (toralCentralizer τ (AlgebraicClosure K) a)))).2
      ⟨hA, hn⟩
    rw [hcop.gcd_eq_one, pow_one, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hTU : torusGroup τ (AlgebraicClosure K) ≤ Subgroup.normalizer
      (rootSpan τ (AlgebraicClosure K) (rootCharKernel a) : Set (ModGL τ (AlgebraicClosure K))) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1
  have hmul : k ∈ (torusGroup τ (AlgebraicClosure K) : Set (ModGL τ (AlgebraicClosure K))) *
      (rootSpan τ (AlgebraicClosure K) (rootCharKernel a) : Set (ModGL τ (AlgebraicClosure K))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTU]
    exact hkM
  obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.1 hmul
  have htN := hTU ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨N, hN, hbN⟩ := Inputs141e.exists_odd_pow_eq_one hK2 b
  exact Inputs141e.mem_of_two_of_mul htN (rootDiagUnit_pow_eq_one_of_forall hbN) hN hu hk2

variable {τ : Tag} {K : Type} [Field K] [Finite K] {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)

theorem exists_odd_pow_of_mem_center_orbit (hK2 : ringChar K = 2) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {z : ModGL τ (AlgebraicClosure K)}
    (hzA : z ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i))
    (hzC : z ∈ Subgroup.centralizer
      (rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :
        Set (ModGL τ (AlgebraicClosure K)))) :
    ∃ N : ℕ, Odd N ∧ z ^ N = 1 := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hPA : P.A = rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :=
    outerOrbitFamily_A S hT i hs hmin
  have hzP : z ∈ P.A := hPA ▸ hzA
  have hzZ : z ∈ P.Z := by
    show z ∈ Subgroup.centralizer (P.A : Set (ModGL τ (AlgebraicClosure K)))
    rw [hPA]
    exact hzC
  obtain ⟨f, rfl⟩ := P.mem_A_iff.1 hzP
  have hfZ : ∀ k, ((f k : P.S k) : ModGL τ (AlgebraicClosure K)) ∈ P.Z :=
    fun k => Inputs141e.mem_Z_of_mu_mem_Z P f hzZ k
  have hsL := Inputs141e.exists_unit_sq_ne_one_of_isAlgClosed (L := AlgebraicClosure K)
  have htor : ∀ k, ∃ b : Fin τ.rank → (AlgebraicClosure K)ˣ,
      ((f k : P.S k) : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ b := by
    intro k
    obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
    have hSk : P.S k = rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j) := by
      rw [hP, outerOrbitFamily_S, hj]
    have hUS : unionRootSpan (AlgebraicClosure K) (rootCharHom a) ({j} : Set (KernelComponent (rootCharHom a))) =
        rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j) := by
      unfold unionRootSpan
      rw [unionRoots_singleton]
    have hmem : ((f k : P.S k) : ModGL τ (AlgebraicClosure K)) ∈
        unionRootSpan (AlgebraicClosure K) (rootCharHom a) ({j} : Set (KernelComponent (rootCharHom a))) := by
      rw [hUS, ← hSk]
      exact (f k).2
    have hcomm : ∀ x ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
        ({j} : Set (KernelComponent (rootCharHom a))),
        x * ((f k : P.S k) : ModGL τ (AlgebraicClosure K)) = ((f k : P.S k) : ModGL τ (AlgebraicClosure K)) * x := by
      intro x hx
      rw [hUS, ← hSk] at hx
      exact (P.mem_Z.1 (hfZ k)) x (P.S_le_A k hx)
    have htT := central_mem_unionTorus hsL hmem hcomm
    exact exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup htT)
  choose b hb using htor
  obtain ⟨N, hN, hbN⟩ := Inputs141e.exists_odd_pow_eq_one hK2 (fun ki : ZMod s × Fin τ.rank => b ki.1 ki.2)
  refine ⟨N, hN, ?_⟩
  have hfN : f ^ N = 1 := by
    funext k
    apply Subtype.ext
    simp only [Pi.pow_apply, SubgroupClass.coe_pow, Pi.one_apply, OneMemClass.coe_one]
    rw [hb k]
    exact rootDiagUnit_pow_eq_one_of_forall fun i => hbN (k, i)
  rw [← map_pow, hfN, map_one]

theorem mem_iSup_ratTwo (hK2 : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    {k : ModGL τ (AlgebraicClosure K)} (hk : k ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})
    (hk2 : IsPGroup 2 ↥(Subgroup.zpowers k)) :
    k ∈ ⨆ O : Set.range (rationalRoots S.ρ (rootCharHom a)), ratTwo O.1 S.D.model := by
  classical
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  have hform := S.frob.iform_eq
  have hΓ : S.Γ ≤ adjointGroup τ (AlgebraicClosure K) :=
    (Subgroup.commutator_le_self S.D.model).trans inf_le_left
  have hΓfix : ∀ x ∈ S.Γ, S.D.step x = x := fun x hx =>
    ((Subgroup.commutator_le_self S.D.model) hx).2
  have hkX : k ∈ toralCentralizer τ (AlgebraicClosure K) a :=
    Subgroup.mem_inf.2 ⟨hΓ (Subgroup.mem_inf.1 hk).1, (Subgroup.mem_inf.1 hk).2⟩
  have hkU := mem_rootSpan_of_two_p hK2 hp hp2 hap hkX hk2
  have hkF : S.D.step k = k := hΓfix k (Subgroup.mem_inf.1 hk).1
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ (AlgebraicClosure K) (rootCharHom a)).2.1
  haveI : Finite (Set.range (rationalRoots S.ρ (rootCharHom a))) := (Set.finite_range _).to_subtype
  haveI : Fintype (Set.range (rationalRoots S.ρ (rootCharHom a))) := Fintype.ofFinite _
  let A : Set.range (rationalRoots S.ρ (rootCharHom a)) → Subgroup (ModGL τ (AlgebraicClosure K)) :=
    fun O => rootSpan τ (AlgebraicClosure K) O.1
  have hc : ∀ O O', O ≠ O' → ∀ x ∈ A O, ∀ y ∈ A O', Commute x y := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
    exact commute_rootSpan_rationalRoots hker hform (fun h => hne (Subtype.ext h))
  have hF : ∀ O, ∀ x ∈ A O, S.D.step x ∈ A O := by
    rintro ⟨_, i, rfl⟩ x hx
    exact step_mem_rootSpan S (fun γ hγ => (rationalRoots_subset_kernelRoots hker i hγ).1)
      (rationalRoots_mapsTo i) hx
  have hU : ⨆ O, A O = rootSpan τ (AlgebraicClosure K) (rootCharKernel a) := by
    refine le_antisymm (iSup_le fun O => ?_) ?_
    · obtain ⟨_, i, rfl⟩ := O
      exact rootSpan_mono (rationalRoots_subset_kernelRoots hker i)
    · refine le_trans (iSup_componentRootSpan (AlgebraicClosure K) (χ := rootCharHom a)).ge (iSup_le fun i => ?_)
      have h : componentRootSpan (AlgebraicClosure K) (rootCharHom a) i ≤ A ⟨_, i, rfl⟩ :=
        rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩
      exact h.trans (le_iSup A ⟨_, i, rfl⟩)
  have hAadj : ∀ O, A O ≤ adjointGroup τ (AlgebraicClosure K) := fun O => rootSpan_le_adjointGroup _ O.1
  have hcomm : Pairwise fun O O' : Set.range (rationalRoots S.ρ (rootCharHom a)) =>
      ∀ x y : ModGL τ (AlgebraicClosure K), x ∈ A O → y ∈ A O' → Commute x y :=
    fun O O' hne x y hx hy => hc O O' hne x hx y hy
  set ν := Subgroup.noncommPiCoprod hcomm with hν
  have hrange : ν.range = ⨆ O, A O := Subgroup.noncommPiCoprod_range
  obtain ⟨f, hf⟩ : k ∈ ν.range := by rw [hrange, hU]; exact hkU
  obtain ⟨m, hm⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hk2
  have hcen : ∀ O, ∀ z ∈ A O, z ∈ Subgroup.centralizer (A O : Set (ModGL τ (AlgebraicClosure K))) →
      ∃ N : ℕ, Odd N ∧ z ^ N = 1 := by
    rintro ⟨_, i, rfl⟩ z hz hzC
    exact exists_odd_pow_of_mem_center_orbit S hK2 hT i hz hzC
  have hfm : ∀ O, ((f O : A O) : ModGL τ (AlgebraicClosure K)) ^ (2 ^ m) ∈
      Subgroup.centralizer (A O : Set (ModGL τ (AlgebraicClosure K))) := by
    intro O
    have h1 : ν (f ^ (2 ^ m)) = 1 := by rw [map_pow, hf, hm]
    have h2 := mem_centralizer_of_noncommPiCoprod_eq_one A hcomm (f ^ (2 ^ m)) h1 O
    simpa using h2
  have hodd : ∀ O, ∃ N : ℕ, Odd N ∧ (((f O : A O) : ModGL τ (AlgebraicClosure K)) ^ (2 ^ m)) ^ N = 1 :=
    fun O => hcen O _ (pow_mem (f O).2 _) (hfm O)
  choose N hN hfN using hodd
  set N₀ : ℕ := ∏ O, N O with hN₀def
  have hN₀ : Odd N₀ :=
    Finset.prod_induction _ Odd (fun _ _ h1 h2 => h1.mul h2) odd_one (fun O _ => hN O)
  have hfN₀ : ∀ O, (((f O : A O) : ModGL τ (AlgebraicClosure K)) ^ (2 ^ m)) ^ N₀ = 1 := by
    intro O
    obtain ⟨c, hc'⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ O)
    rw [← hN₀def] at hc'
    rw [hc', pow_mul, hfN O, one_pow]
  have hgcd : Nat.gcd N₀ (2 ^ m) = 1 := Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hN₀)
  set x : ℤ := Nat.gcdA N₀ (2 ^ m) with hx
  set y : ℤ := Nat.gcdB N₀ (2 ^ m) with hy
  have hxy : (N₀ : ℤ) * x + ((2 ^ m : ℕ) : ℤ) * y = 1 := by
    have h := Nat.gcd_eq_gcd_ab N₀ (2 ^ m)
    rw [hgcd, Nat.cast_one] at h
    exact h.symm
  let f₂ : ∀ O, A O := fun O => (f O) ^ ((N₀ : ℤ) * x)
  let b : ∀ O, A O := fun O => (f O) ^ (((2 ^ m : ℕ) : ℤ) * y)
  have hfb : f = f₂ * b := by
    funext O
    show f O = (f O) ^ ((N₀ : ℤ) * x) * (f O) ^ (((2 ^ m : ℕ) : ℤ) * y)
    rw [← zpow_add, hxy, zpow_one]
  have hf₂2 : f₂ ^ (2 ^ m) = 1 := by
    funext O
    apply Subtype.ext
    show (((f O) ^ ((N₀ : ℤ) * x)) ^ (2 ^ m) : A O).1 = 1
    rw [← zpow_natCast, ← zpow_mul, show (N₀ : ℤ) * x * ((2 ^ m : ℕ) : ℤ) = ((2 ^ m * N₀ : ℕ) : ℤ) * x by
      push_cast; ring, zpow_mul, zpow_natCast, pow_mul]
    have h1 : (((f O : A O)) ^ (2 ^ m)) ^ N₀ = 1 := Subtype.ext (by simpa using hfN₀ O)
    rw [h1, one_zpow]
    rfl
  have hbC : ∀ O, ((b O : A O) : ModGL τ (AlgebraicClosure K)) ∈
      Subgroup.centralizer (A O : Set (ModGL τ (AlgebraicClosure K))) := by
    intro O
    show (((f O) ^ (((2 ^ m : ℕ) : ℤ) * y) : A O) : ModGL τ (AlgebraicClosure K)) ∈ _
    rw [zpow_mul, zpow_natCast, Subgroup.coe_zpow, Subgroup.coe_pow]
    exact zpow_mem (hfm O) y
  have hbN : b ^ N₀ = 1 := by
    funext O
    apply Subtype.ext
    show (((f O) ^ (((2 ^ m : ℕ) : ℤ) * y)) ^ N₀ : A O).1 = 1
    rw [← zpow_natCast, ← zpow_mul, show ((2 ^ m : ℕ) : ℤ) * y * (N₀ : ℤ) = ((2 ^ m * N₀ : ℕ) : ℤ) * y by
      push_cast; ring, zpow_mul, zpow_natCast, pow_mul]
    have h1 : (((f O : A O)) ^ (2 ^ m)) ^ N₀ = 1 := Subtype.ext (by simpa using hfN₀ O)
    rw [h1, one_zpow]
    rfl
  have hbf : b * f₂ = f₂ * b := by
    funext O
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 (hbC O) _ (f₂ O).2).symm
  have hk₂ : k = ν f₂ := by
    have e1 : k = ν f₂ * ν b := by rw [← hf, hfb, map_mul]
    have hνc : Commute (ν f₂) (ν b) := by
      show ν f₂ * ν b = ν b * ν f₂
      rw [← map_mul, ← map_mul, hbf]
    have hb2 : (ν b) ^ (2 ^ m) = 1 := by
      have h1 : k ^ (2 ^ m) = (ν f₂) ^ (2 ^ m) * (ν b) ^ (2 ^ m) := by rw [e1, hνc.mul_pow]
      rw [hm, ← map_pow, hf₂2, map_one, one_mul] at h1
      exact h1.symm
    have hbN' : (ν b) ^ N₀ = 1 := by rw [← map_pow, hbN, map_one]
    rw [e1, eq_one_of_two_of_odd hb2 hN₀ hbN', mul_one]
  have hkey : ∀ O, S.D.step ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)) *
      ((f₂ O : A O) : ModGL τ (AlgebraicClosure K))⁻¹ ∈
      Subgroup.centralizer (A O : Set (ModGL τ (AlgebraicClosure K))) := by
    intro O
    let Ff : ∀ O, A O := fun O => ⟨S.D.step (f₂ O), hF O _ (f₂ O).2⟩
    have hFν : ν Ff = S.D.step (ν f₂) := by
      rw [hν, Subgroup.noncommPiCoprod_apply, Subgroup.noncommPiCoprod_apply]
      exact (Finset.map_noncommProd Finset.univ (fun O => ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)))
        _ S.D.step).symm
    have h1 : ν (Ff * f₂⁻¹) = 1 := by rw [map_mul, map_inv, hFν, ← hk₂, hkF, mul_inv_cancel]
    exact mem_centralizer_of_noncommPiCoprod_eq_one A hcomm (Ff * f₂⁻¹) h1 O
  have hfix : ∀ O, S.D.step ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)) =
      ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)) := by
    intro O
    set g : ModGL τ (AlgebraicClosure K) := ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)) with hg
    set w := S.D.step g * g⁻¹ with hw
    have hwA : w ∈ A O := mul_mem (hF O _ (f₂ O).2) (inv_mem (f₂ O).2)
    obtain ⟨N', hN', hwN⟩ := hcen O w hwA (hkey O)
    have hwg : Commute w g := (Subgroup.mem_centralizer_iff.1 (hkey O) g (f₂ O).2).symm
    have hg2 : g ^ (2 ^ m) = 1 := by
      have h1 := congrArg (fun φ : ∀ O, A O => ((φ O : A O) : ModGL τ (AlgebraicClosure K))) hf₂2
      simpa using h1
    have hFg : S.D.step g = w * g := by rw [hw]; group
    have hFgc : Commute (S.D.step g) g := by rw [hFg]; exact hwg.mul_left (Commute.refl g)
    have hw2 : w ^ (2 ^ m) = 1 := by
      rw [hw, (hFgc.inv_right).mul_pow, ← map_pow, hg2, map_one, inv_pow, hg2, inv_one, one_mul]
    have hw1 := eq_one_of_two_of_odd hw2 hN' hwN
    rw [hw] at hw1
    exact mul_inv_eq_one.1 hw1
  rw [hk₂, hν, Subgroup.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun O _ => Subgroup.mem_iSup_of_mem O (Subgroup.subset_closure ?_)
  refine ⟨(f₂ O).2, ⟨hAadj O (f₂ O).2, hfix O⟩, ?_⟩
  have hg2 : ((f₂ O : A O) : ModGL τ (AlgebraicClosure K)) ^ (2 ^ m) = 1 := by
    have h1 := congrArg (fun φ : ∀ O, A O => ((φ O : A O) : ModGL τ (AlgebraicClosure K))) hf₂2
    simpa using h1
  exact isPGroup_zpowers_of_pow_eq_one hg2

end LangDecomp

theorem cycFamily_norm_eq_self_of_eq_one {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s]
    (P : CFSG.HardMathSupport.Timmesfeld.LangTorus.CycFamily F s) (hs : s = 1) (y : P.S 0) : P.norm y = y := by
  classical
  subst hs
  have h1 : P.diag y = Pi.mulSingle 0 (P.diag y 0) := by
    funext k
    obtain rfl : k = 0 := Subsingleton.elim k 0
    rw [Pi.mulSingle_eq_same]
  show P.mu (P.diag y) = y
  rw [h1, P.mu_mulSingle]
  rfl

section LangInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped Pointwise commutatorElement


variable {τ : Tag} {K : Type} [Field K] [Finite K] {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)

theorem coprime_720 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp55 : p ≠ 5) : Nat.Coprime p 720 := by
  rw [show (720 : ℕ) = (2 ^ 4 * 3 ^ 2) * 5 by norm_num]
  refine Nat.Coprime.mul_right (coprime_two_pow_mul_three_pow hp hp5 4 2) ?_
  exact (Nat.coprime_primes hp Nat.prime_five).2 hp55

theorem b2_two_derived_equiv {K : Type} [Field K] (hK2 : ∀ x : K, x = 0 ∨ x = 1)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) {s l : Fin Tag.F4.rank → ℤ}
    (hss : CFSG.LieType.Steinberg.Adjoint.iform s s = 2) (hll : CFSG.LieType.Steinberg.Adjoint.iform l l = 4)
    (hsl : CFSG.LieType.Steinberg.Adjoint.iform s l = -2)
    (hΨ : componentRoots χ i = {s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)}) :
    Nonempty (↥(⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ : Subgroup (ModGL Tag.F4 K)) ≃*
      alternatingGroup (Fin 6)) := by
  classical
  have h2 : (2 : K) = 0 := by
    rcases hK2 (1 + 1) with h | h
    · rwa [one_add_one_eq_two] at h
    · exact absurd (by linear_combination h : (1 : K) = 0) one_ne_zero
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hΨc := isRootComponent_componentRoots (χ := χ) i
  have hs : IsRoot .F4 s := hΨc.isRoot s (by rw [hΨ]; simp)
  have hl : IsRoot .F4 l := hΨc.isRoot l (by rw [hΨ]; simp)
  have hrel := b2Rel_F4 (K := K) hs hl hss hll hsl
  obtain ⟨-, hb, -⟩ := f4_commutator_mixed hs hl hss hll hsl
  set S := componentRootSpan K χ i with hSdef
  have hSgen : S = Subgroup.closure ({xr K s, xr K (-s), xr K l, xr K (-l), xr K (s + l),
      xr K (-(s + l)), xr K (2 • s + l), xr K (-(2 • s + l))} : Set (ModGL Tag.F4 K)) := by
    apply le_antisymm
    · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      rcases hK2 c with rfl | rfl
      · rw [pinnedX_zero]
        exact one_mem _
      · apply Subgroup.subset_closure
        have hα' : α ∈ ({s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)} :
            Set (Fin Tag.F4.rank → ℤ)) := hΨ ▸ hα
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα' ⊢
        rcases hα' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [xr]
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      have hmem : ∀ γ : Fin Tag.F4.rank → ℤ, γ ∈ ({s, -s, l, -l, s + l, -(s + l), 2 • s + l,
          -(2 • s + l)} : Set (Fin Tag.F4.rank → ℤ)) → γ ∈ componentRoots χ i :=
        fun γ h => hΨ ▸ h
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact pinnedX_mem_rootSpan (hmem _ (by simp)) 1
  have hcox := b2_isCoxeterA hrel
  have h01 : b2t (xr K s) (xr K (-s)) (xr K l) (xr K (-l)) (xr K (s + l)) (xr K (-(s + l)))
      (xr K (2 • s + l)) (xr K (-(2 • s + l))) 0 ≠
      b2t (xr K s) (xr K (-s)) (xr K l) (xr K (-l)) (xr K (s + l)) (xr K (-(s + l)))
        (xr K (2 • s + l)) (xr K (-(2 • s + l))) 1 :=
    fun h => xr_ne_xr_neg hb (by simpa [b2t] using h.symm)
  obtain ⟨e, -⟩ := exists_mulEquiv_closure_five hcox h01
  have hS : S = Subgroup.closure (b2t (xr K s) (xr K (-s)) (xr K l) (xr K (-l))
      (xr K (s + l)) (xr K (-(s + l))) (xr K (2 • s + l)) (xr K (-(2 • s + l))) ''
      Set.Iio 5) := hSgen.trans (b2_closure_eq hrel)
  let Φ : ↥S ≃* Equiv.Perm (Fin 6) := (MulEquiv.subgroupCongr hS).trans e.symm
  have hle : ⁅S, S⁆ ≤ S := Subgroup.commutator_le_self S
  have himg := CFSG.LargeExtraspecial.S45Q.img_commutator Φ
  let ψ : ↥⁅S, S⁆ ≃* alternatingGroup (Fin 6) :=
    (CFSG.LargeExtraspecial.S45Q.imgEquiv Φ hle).trans (MulEquiv.subgroupCongr himg)
  exact ⟨ψ⟩

theorem ratTwo_inner_or (hK2 : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hG2 : τ = .G2 → 4 ≤ S.D.q) :
    ⁅ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model,
        ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model⁆ =
        ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model ∨
      Nat.Coprime p (Nat.card (ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model)) ∨
      (τ = .F4 ∧ S.D.q = 2 ∧ Nat.card (ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model) ∣ 720 ∧
        Nonempty (↥⁅ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model,
          ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model⁆ ≃* alternatingGroup (Fin 6))) := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model with hTdef
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hPA : P.A = rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :=
    outerOrbitFamily_A S hT i hs hmin
  have hP0 : P.S 0 = rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hPZ : P.Z = Subgroup.centralizer
      (rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    show Subgroup.centralizer (P.A : Set (ModGL τ (AlgebraicClosure K))) = _
    rw [hPA]
  have hUS : unionRootSpan (AlgebraicClosure K) (rootCharHom a) ({i} : Set (KernelComponent (rootCharHom a))) =
      rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
    unfold unionRootSpan
    rw [unionRoots_singleton]
  have hsL := Inputs141e.exists_unit_sq_ne_one_of_isAlgClosed (L := AlgebraicClosure K)
  have hinner := twistInner_of_twistKind_eq_innerT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hqe⟩ := exists_char_pow S
  have hr2 : r = 2 := CharP.eq (AlgebraicClosure K) hchar hL2
  subst hr2
  have hσ' : ∀ c, σ c = c ^ (2 ^ (e * s)) := fun c => by rw [hσ, hqe, ← pow_mul]
  have hes : 0 < e * s := Nat.mul_pos he hs0
  have hzA : ∀ x ∈ P.A, z * x * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
      intro x hx
      have hx' : x ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j) := by
        rw [hj]; exact hx
      have h2 := (hnorm j x).1 hx'
      rw [hj] at h2
      exact P.S_le_A k h2
    exact fun x hx => h hx
  have hZconj : ∀ X : ModGL τ (AlgebraicClosure K), z * X * z⁻¹ ∈ P.Z → X ∈ P.Z := by
    intro X hX
    rw [CycFamily.mem_Z] at hX ⊢
    intro x hx
    have h1 := hX _ (hzA x hx)
    have e1 : z * x * z⁻¹ * (z * X * z⁻¹) = z * (x * X) * z⁻¹ := by group
    have e2 : z * X * z⁻¹ * (z * x * z⁻¹) = z * (X * x) * z⁻¹ := by group
    rw [e1, e2] at h1
    simpa using h1
  have hZconj' : ∀ W ∈ P.Z, z⁻¹ * W * z ∈ P.Z := fun W hW =>
    hZconj _ (by rw [show z * (z⁻¹ * W * z) * z⁻¹ = W by group]; exact hW)
  have hYc : ∀ u ∈ P.Y, z⁻¹ * u * z ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ∧
      frobGL σ (z⁻¹ * u * z) * (z⁻¹ * u * z)⁻¹ ∈ P.Z := by
    intro u hu
    obtain ⟨hu0, huZ⟩ := P.mem_Y.1 hu
    rw [hP0] at hu0
    have e1 : z * (z⁻¹ * u * z) * z⁻¹ = u := by group
    have hv : z⁻¹ * u * z ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) :=
      (hnorm i (z⁻¹ * u * z)).2 (by rw [e1]; exact hu0)
    refine ⟨hv, ?_⟩
    have h1 := hz _ hv
    rw [e1] at h1
    have e2 : frobGL σ (z⁻¹ * u * z) * (z⁻¹ * u * z)⁻¹ =
        z⁻¹ * (iterHom S.D.step s u * u⁻¹) * z := by
      have e3 : frobGL σ (z⁻¹ * u * z) = z⁻¹ * iterHom S.D.step s u * z := by rw [h1]; group
      rw [e3]
      group
    rw [e2]
    exact hZconj' _ huZ
  have hcen : ∀ W ∈ P.Z, ∀ x ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
      ({i} : Set (KernelComponent (rootCharHom a))), x * W = W * x := by
    intro W hW x hx
    rw [hUS] at hx
    exact (P.mem_Z.1 hW) x (P.S_le_A 0 (by rw [hP0]; exact hx))
  have hCQS : ∀ x ∈ CQ σ i, z * x * z⁻¹ ∈ P.S 0 := fun x hx => by
    rw [hP0]
    exact (hnorm i x).1 (CQ_le_rootSpan σ i hx)
  let θ₀ : ↥(CQ σ i) →* P.S 0 :=
    ((MulAut.conj z).toMonoidHom.comp (CQ σ i).subtype).codRestrict (P.S 0) fun x => hCQS x x.2
  have hθ₀ : ∀ x : ↥(CQ σ i), ((θ₀ x : P.S 0) : ModGL τ (AlgebraicClosure K)) = z * x * z⁻¹ :=
    fun x => rfl
  let ν : ↥(CQ σ i) →* ModGL τ (AlgebraicClosure K) := P.norm.comp θ₀
  have hθfix : ∀ x : ↥(CQ σ i), iterHom S.D.step s ((θ₀ x : P.S 0) : ModGL τ (AlgebraicClosure K)) =
      θ₀ x := fun x => by
    rw [hθ₀, hz _ (CQ_le_rootSpan σ i x.2), frobGL_eq_self_of_mem_CQ σ i x.2]
  have hAadj : P.A ≤ adjointGroup τ (AlgebraicClosure K) := by
    rw [hPA]
    exact rootSpan_le_adjointGroup _ _
  have hTν : T ≤ ν.range := by
    rw [hTdef, ratTwo, Subgroup.closure_le]
    rintro g ⟨hgA, hgM, hg2⟩
    obtain ⟨m, hm⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hg2
    have hgP : g ∈ P.A := hPA ▸ hgA
    have hgF : S.D.step g = g := hgM.2
    obtain ⟨y, hyY, ζ, hζZ, hζA, rfl⟩ := P.exists_eq_zeta_norm hgP hgF
    obtain ⟨Nζ, hNζ, hζN⟩ := exists_odd_pow_of_mem_center_orbit S hK2 hT i (hPA ▸ hζA) (hPZ ▸ hζZ)
    obtain ⟨hvy, hvyZ⟩ := hYc (y : ModGL τ (AlgebraicClosure K)) hyY
    set h := z⁻¹ * (y : ModGL τ (AlgebraicClosure K)) * z with hhdef
    have hhS : h ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
        ({i} : Set (KernelComponent (rootCharHom a))) := hUS ▸ hvy
    have hcS : frobGL σ h * h⁻¹ ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
        ({i} : Set (KernelComponent (rootCharHom a))) :=
      mul_mem (frobGL_mem_rootSpan σ hhS) (inv_mem hhS)
    have hcT := central_mem_unionTorus hsL hcS (hcen _ hvyZ)
    obtain ⟨t, ht, x, hx, hyt, hφ⟩ := exists_decomp (σ := σ) hhS hcT (by group)
    have hn := torus_normalizes_CQ (σ := σ) ht (hcen _ hvyZ) hφ
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup ht)
    obtain ⟨Nt, hNt, hlN⟩ := Inputs141e.exists_odd_pow_eq_one hK2 l
    have htN : t ^ Nt = 1 := by rw [hl]; exact rootDiagUnit_pow_eq_one_of_forall hlN
    have htN' : t ∈ Subgroup.normalizer (CQ σ i : Set (ModGL τ (AlgebraicClosure K))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨fun hw => hn.1 w hw, fun hw => ?_⟩
      have h1 := hn.2 _ hw
      have e : t⁻¹ * (t * w * t⁻¹) * t = w := by group
      rwa [e] at h1
    have hhN : h ^ Nt ∈ CQ σ i := by
      have h1 := Inputs141e.mul_pow_mem_of_mem_normalizer htN' hx Nt
      rwa [htN, inv_one, one_mul, ← hyt] at h1
    set M := Nt * Nζ with hMdef
    have hM : Odd M := hNt.mul hNζ
    have hhM : h ^ M ∈ CQ σ i := by
      rw [hMdef, pow_mul]
      exact pow_mem hhN _
    have hyM : ((y ^ M : P.S 0) : ModGL τ (AlgebraicClosure K)) = z * h ^ M * z⁻¹ := by
      rw [SubgroupClass.coe_pow, hhdef, show z * (z⁻¹ * (y : ModGL τ (AlgebraicClosure K)) * z) ^ M * z⁻¹ =
        (z * (z⁻¹ * (y : ModGL τ (AlgebraicClosure K)) * z) * z⁻¹) ^ M by rw [conj_pow]]
      congr 1
      group
    have hθM : θ₀ ⟨h ^ M, hhM⟩ = y ^ M := by
      apply Subtype.ext
      rw [hθ₀, hyM]
    have hcomm : Commute ζ (P.norm y) := ((P.mem_Z.1 hζZ) _ (P.norm_mem_A y)).symm
    have hgM : (ζ * P.norm y) ^ M = ν ⟨h ^ M, hhM⟩ := by
      rw [hcomm.mul_pow, show ζ ^ M = 1 by rw [hMdef, mul_comm, pow_mul, hζN, one_pow], one_mul,
        ← map_pow]
      show P.norm (y ^ M) = P.norm (θ₀ ⟨h ^ M, hhM⟩)
      rw [hθM]
    exact mem_of_two_of_odd_pow_mem (H := ν.range) hm hM ⟨⟨h ^ M, hhM⟩, hgM.symm⟩
  have hνT : ν.range ≤ T := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨x, hxC⟩ := x
    induction hxC using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨γ, hγ, c, hc, rfl⟩ := hy
      have hfixA : ν ⟨pinnedX τ (AlgebraicClosure K) γ c, Subgroup.subset_closure ⟨γ, hγ, c, hc, rfl⟩⟩ ∈
          P.Afix := P.norm_mem_Afix (hθfix _)
      refine Subgroup.subset_closure ⟨hPA ▸ hfixA.1, ⟨hAadj hfixA.1, hfixA.2⟩, ?_⟩
      have h2 : (⟨pinnedX τ (AlgebraicClosure K) γ c, Subgroup.subset_closure ⟨γ, hγ, c, hc, rfl⟩⟩ :
          ↥(CQ σ i)) ^ (2 ^ 1) = 1 := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one, sq,
          ← pinnedX_add τ (AlgebraicClosure K) γ c c, CharTwo.add_self_eq_zero,
          pinnedX_zero τ (AlgebraicClosure K) γ]
      exact isPGroup_zpowers_of_pow_eq_one (m := 1) (by rw [← map_pow, h2, map_one])
    | one =>
      show ν 1 ∈ T
      rw [map_one]
      exact one_mem T
    | mul y y' hy hy' ihy ihy' =>
      have e : ν ⟨y * y', mul_mem hy hy'⟩ = ν ⟨y, hy⟩ * ν ⟨y', hy'⟩ := by rw [← map_mul]; rfl
      rw [e]
      exact mul_mem ihy ihy'
    | inv y hy ihy =>
      have e : ν ⟨y⁻¹, inv_mem hy⟩ = (ν ⟨y, hy⟩)⁻¹ := by rw [← map_inv]; rfl
      rw [e]
      exact inv_mem ihy
  have hTeq : T = ν.range := le_antisymm hTν hνT
  haveI : Finite (fixSubfield σ) := by
    obtain ⟨hfin, -⟩ := ncard_pow_eq_self (L := AlgebraicClosure K) 2 (e * s) hes
    have hset : (fixSubfield σ : Set (AlgebraicClosure K)) =
        {c : AlgebraicClosure K | c ^ (2 ^ (e * s)) = c} := by
      ext c
      show c ∈ fixSubfield σ ↔ _
      rw [mem_fixSubfield, hσ']
      rfl
    have h1 : (fixSubfield σ : Set (AlgebraicClosure K)).Finite := by rw [hset]; exact hfin
    exact h1.to_subtype
  haveI : Finite (ModGL τ (fixSubfield σ)) := finite_modGL
  haveI : Finite ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := Subtype.finite
  haveI : Finite ↥(CQ σ i) := by
    rw [CQ_eq_map]
    exact Finite.of_equiv _ ((componentRootSpan (fixSubfield σ) (rootCharHom a) i).equivMapOfInjective _
      (baseChangeGL_injective _)).toEquiv
  have hcardCQ : Nat.card ↥(CQ σ i) =
      Nat.card ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
    rw [CQ_eq_map, Subgroup.card_map_of_injective (baseChangeGL_injective _)]
  have hTdvd : Nat.card ↥T ∣ Nat.card ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
    rw [hTeq, ← hcardCQ]
    exact Subgroup.card_range_dvd ν
  have hperf_of : Group.IsPerfect (componentRootSpan (fixSubfield σ) (rootCharHom a) i) →
      ⁅T, T⁆ = T := by
    intro hperf
    have hperfCQ : Group.IsPerfect ↥(CQ σ i) := by
      refine Subgroup.isPerfect_iff.2 ?_
      rw [CQ_eq_map, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hperf]
    rw [hTeq, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      hperfCQ.commutator_eq_top]
  by_cases hQ : 4 ≤ 2 ^ (e * s)
  · obtain ⟨u, hu⟩ := exists_unit_sq_ne_one (L := AlgebraicClosure K) σ hσ' hes hQ
    exact Or.inl (hperf_of (isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
      (χ := rootCharHom a) hu i))
  ·
    have hes1 : e * s = 1 := by
      by_contra hne
      apply hQ
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (e * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have he1 : e = 1 := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · omega
      · have : e ∣ 1 := ⟨s, hes1.symm⟩
        exact Nat.eq_one_of_dvd_one this
    have hq2 : S.D.q = 2 := by rw [hqe, he1, pow_one]
    have hK2' : ∀ x : fixSubfield σ, x = 0 ∨ x = 1 := by
      intro x
      have hx : σ (x : AlgebraicClosure K) = x := x.2
      rw [hσ', hes1, pow_one, sq] at hx
      have h3 : (x : AlgebraicClosure K) * ((x : AlgebraicClosure K) - 1) = 0 := by
        rw [mul_sub, hx, mul_one, sub_self]
      rcases mul_eq_zero.1 h3 with h4 | h4
      · left
        exact Subtype.ext h4
      · right
        exact Subtype.ext (sub_eq_zero.1 h4)
    have hKcard : Nat.card (fixSubfield σ) = 2 := by
      obtain ⟨-, hcard⟩ := ncard_pow_eq_self (L := AlgebraicClosure K) 2 (e * s) hes
      have hset : (fixSubfield σ : Set (AlgebraicClosure K)) =
          {c : AlgebraicClosure K | c ^ (2 ^ (e * s)) = c} := by
        ext c
        show c ∈ fixSubfield σ ↔ _
        rw [mem_fixSubfield, hσ']
        rfl
      have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set (AlgebraicClosure K)).ncard :=
        Nat.card_coe_set_eq (fixSubfield σ : Set (AlgebraicClosure K))
      rw [h1, hset, hcard, hes1]
      norm_num
    have hKle : Nat.card (fixSubfield σ) ≤ 3 := by omega
    by_cases hrank : ∀ α ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
        δ = α ∨ δ = -α
    ·
      right; left
      obtain ⟨α₀, hα₀⟩ := Quotient.exists_rep i
      have hα : α₀.1 ∈ componentRoots (rootCharHom a) i := ⟨α₀.2, hα₀⟩
      have hle := componentRootSpan_le_range_of_rank_one (K := fixSubfield σ) i hα (hrank α₀.1 hα)
      have h1 : Nat.card ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) ∣ 216 := by
        have h2 : Nat.card ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) ∣
            Nat.card ↥(rootSL2 τ (fixSubfield σ) α₀.1).range := Subgroup.card_dvd_of_le hle
        exact h2.trans ((Subgroup.card_range_dvd _).trans (card_sl2_dvd_216 hKle))
      refine Nat.Coprime.coprime_dvd_right (hTdvd.trans h1) ?_
      rw [show (216 : ℕ) = 2 ^ 3 * 3 ^ 3 by norm_num]
      exact coprime_two_pow_mul_three_pow hp hp5 3 3
    · have hbig : ∃ α ∈ componentRoots (rootCharHom a) i, ∃ δ ∈ componentRoots (rootCharHom a) i,
          δ ≠ α ∧ δ ≠ -α := by
        push Not at hrank
        exact hrank
      have hτ' : ∀ τ : Tag, τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
        intro τ; cases τ <;> simp
      rcases hτ' τ with h | h | h | h | h | h
      · exfalso
        have := hG2 h
        omega
      · subst h
        by_cases hA2 : ∃ α ∈ componentRoots (rootCharHom a) i, ∃ δ ∈ componentRoots (rootCharHom a) i,
            δ ≠ α ∧ δ ≠ -α ∧ CFSG.LieType.Steinberg.Adjoint.iform α α =
              CFSG.LieType.Steinberg.Adjoint.iform δ δ ∧ CFSG.LieType.Steinberg.Adjoint.iform α δ ≠ 0
        · exact Or.inl (hperf_of (isPerfect_componentRootSpan_F4_two hK2' i hA2))
        · right; right
          push Not at hA2
          obtain ⟨s', l, hss, hll, hsl, hΨ⟩ := eq_b2Block_of_noA2 i hbig hA2
          have h720 := Inputs141e.card_componentRootSpan_b2_two hK2' i hss hll hsl hΨ
          rw [h720] at hTdvd
          refine ⟨rfl, hq2, hTdvd, ?_⟩
          have hs1 : s = 1 := Nat.eq_one_of_dvd_one ⟨e, by rw [mul_comm]; exact hes1.symm⟩
          have hνinj : Function.Injective ν := by
            intro x y hxy
            have hx := cycFamily_norm_eq_self_of_eq_one P hs1 (θ₀ x)
            have hy := cycFamily_norm_eq_self_of_eq_one P hs1 (θ₀ y)
            have h2 : ((θ₀ x : P.S 0) : ModGL Tag.F4 (AlgebraicClosure K)) =
                ((θ₀ y : P.S 0) : ModGL Tag.F4 (AlgebraicClosure K)) := by
              rw [← hx, ← hy]
              exact hxy
            rw [hθ₀, hθ₀] at h2
            exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
          obtain ⟨e1⟩ := nonempty_commutator_sub_equiv T
          obtain ⟨e2⟩ := nonempty_commutator_congr (((MulEquiv.subgroupCongr hTeq).trans
            (MonoidHom.ofInjective hνinj).symm).trans ((MulEquiv.subgroupCongr (CQ_eq_map (i := i) (σ := σ))).trans
              ((componentRootSpan (fixSubfield σ) (rootCharHom a) i).equivMapOfInjective _
                (baseChangeGL_injective _)).symm))
          obtain ⟨e3⟩ := nonempty_commutator_sub_equiv (componentRootSpan (fixSubfield σ) (rootCharHom a) i)
          obtain ⟨e4⟩ := b2_two_derived_equiv hK2' i hss hll hsl hΨ
          exact ⟨((e1.trans e2).trans e3.symm).trans e4⟩
      all_goals exact Or.inl (hperf_of (isPerfect_componentRootSpan_simplyLaced (by simp [h]) i hbig))


theorem ratTwo_inner (hK2 : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hexc : ¬ (τ = .F4 ∧ S.D.q = 2 ∧ p = 5)) (hG2 : τ = .G2 → 4 ≤ S.D.q) :
    ⁅ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model,
        ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model⁆ =
        ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model ∨
      Nat.Coprime p (Nat.card (ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model)) := by
  rcases ratTwo_inner_or S hK2 hp hp5 hT i hkind hG2 with h | h | ⟨hF4, hq2, h720, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · right
    have hp55 : p ≠ 5 := fun h5 => hexc ⟨hF4, hq2, h5⟩
    exact Nat.Coprime.coprime_dvd_right h720 (coprime_720 hp hp5 hp55)

end LangInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups in
@[expose] def LangOuterTwo : Prop :=
  ∀ (τ : Tag) (K : Type) [Field K] [Finite K],
    ringChar K = 2 → ∀ (p₀ : ℕ) (S : LangSetup τ (AlgebraicClosure K) p₀) (p : ℕ), p.Prime → 5 ≤ p →
    ∀ (a : Fin τ.rank → (AlgebraicClosure K)ˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ p = 1) →
      rootDiagUnit τ a ≠ 1 →
    ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i ≠ .inner →
      ⁅ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model,
          ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model⁆ =
          ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model ∨
        Nat.Coprime p (Nat.card (ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model))

section LangMain

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped Pointwise

theorem twoInCoreLayer_of_decomp {C : Type} [Group C] [Finite C] {G : Type*} [Group G] (ι : C →* G)
    (hι : Function.Injective ι) {β : MulAut C} {X : Subgroup G} (hX : (fixSubgroup β).map ι = X) {p : ℕ}
    (hp : p.Prime) (hlay : PerfectInLayer β)
    (h : ∀ k ∈ X, IsPGroup 2 ↥(Subgroup.zpowers k) → ∃ W N : Subgroup G, W ≤ X ∧ ⁅W, W⁆ = W ∧ N ≤ X ∧
      (N.subgroupOf X).Normal ∧ Nat.Coprime p (Nat.card N) ∧ k ∈ W ⊔ N) :
    TwoInCoreLayer p β := by
  intro x hx hx2
  have hkX : ι x ∈ X := hX ▸ Subgroup.mem_map_of_mem ι hx
  have hk2 : IsPGroup 2 ↥(Subgroup.zpowers (ι x)) := by
    have h1 := hx2.map ι
    rwa [MonoidHom.map_zpowers] at h1
  obtain ⟨W, N, hWX, hWp, hNX, hNn, hNc, hkWN⟩ := h (ι x) hkX hk2
  have hXr : X ≤ ι.range := by rw [← hX]; exact Subgroup.map_le_range ι _
  have hpre : ∀ {Y : Subgroup G}, Y ≤ X → (Y.comap ι).map ι = Y ∧ Y.comap ι ≤ fixSubgroup β := by
    intro Y hYX
    refine ⟨?_, fun y hy => ?_⟩
    · rw [Subgroup.map_comap_eq, inf_eq_right.2 (hYX.trans hXr)]
    · have h1 : ι y ∈ (fixSubgroup β).map ι := hX ▸ hYX hy
      obtain ⟨y', hy', hyy'⟩ := h1
      rwa [← hι hyy']
  obtain ⟨hWmap, hWfix⟩ := hpre hWX
  obtain ⟨hNmap, hNfix⟩ := hpre hNX
  have hW'p : ⁅W.comap ι, W.comap ι⁆ = W.comap ι := by
    apply Subgroup.map_injective hι
    rw [Subgroup.map_commutator, hWmap, hWp]
  have hW'le : W.comap ι ≤ GLAPPrimeCoreOf p (fixSubgroup β) ⊔ GLAPLayer p (fixSubgroup β) :=
    (hlay _ hWfix hW'p).trans (glaLayer_le_core_sup_layer hp _)
  have hN'n : ((N.comap ι).subgroupOf (fixSubgroup β)).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : ι c ∈ X := hX ▸ Subgroup.mem_map_of_mem ι c.2
    have hn' : ι n ∈ X := hNX hn
    have h1 : (⟨ι n, hn'⟩ : ↥X) ∈ N.subgroupOf X := hn
    have h2 := hNn.conj_mem _ h1 ⟨ι c, hc⟩
    rw [Subgroup.mem_subgroupOf] at h2
    show ι ((c : C) * n * (c : C)⁻¹) ∈ N
    simpa using h2
  have hN'c : Nat.Coprime p (Nat.card (N.comap ι)) := by
    rwa [← Subgroup.card_map_of_injective hι, hNmap]
  have hN'le : N.comap ι ≤ GLAPPrimeCoreOf p (fixSubgroup β) :=
    le_glaPPrimeCoreOf_of_isSubnormal hp (Inputs141f.isSubnormal_of_normal hNfix hN'n) hN'c
  have hxWN : x ∈ W.comap ι ⊔ N.comap ι := by
    have h1 : ι x ∈ (W.comap ι ⊔ N.comap ι).map ι := by rw [Subgroup.map_sup, hWmap, hNmap]; exact hkWN
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [← hι hyx]
  exact sup_le hW'le (hN'le.trans le_sup_left) hxWN


variable {τ : Tag} {K : Type} [Field K] [Finite K] {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)

theorem twoDecomp_langCentralizer (hout : LangOuterTwo) (hK2 : ringChar K = 2) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hinner : ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .inner →
      ⁅ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model,
          ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model⁆ =
          ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model ∨
        Nat.Coprime p (Nat.card (ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model)))
    {k : ModGL τ (AlgebraicClosure K)}
    (hk : k ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) (hk2 : IsPGroup 2 ↥(Subgroup.zpowers k)) :
    ∃ W N : Subgroup (ModGL τ (AlgebraicClosure K)), W ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
      ⁅W, W⁆ = W ∧ N ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
      (N.subgroupOf (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})).Normal ∧
      Nat.Coprime p (Nat.card N) ∧ k ∈ W ⊔ N := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Finite S.D.model := S.finite
  set L := AlgebraicClosure K
  set M := S.D.model with hMdef
  set d := rootDiagUnit τ a with hd
  set T : Set.range (rationalRoots S.ρ (rootCharHom a)) → Subgroup (ModGL τ L) :=
    fun O => ratTwo O.1 M with hTdef
  have hkT := mem_iSup_ratTwo S hK2 hp hp2 hT hap hk hk2
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  have hform := S.frob.iform_eq
  have hΓM : S.Γ ≤ M := Subgroup.commutator_le_self _
  have hMadj : M ≤ adjointGroup τ L := inf_le_left
  have hTA : ∀ O, T O ≤ rootSpan τ L O.1 ⊓ M := by
    intro O
    rw [hTdef]
    show ratTwo O.1 M ≤ _
    rw [ratTwo, Subgroup.closure_le]
    rintro g ⟨hgA, hgM, -⟩
    exact ⟨hgA, hgM⟩
  have hTC : ∀ O, T O ≤ Subgroup.centralizer {d} := by
    rintro ⟨_, i, rfl⟩
    exact (hTA _).trans (inf_le_left.trans
      (rootSpan_le_centralizer a (rationalRoots_subset_kernelRoots hker i)))
  have hshape : ∀ O, ⁅T O, T O⁆ = T O ∨ Nat.Coprime p (Nat.card (T O)) := by
    rintro ⟨_, i, rfl⟩
    by_cases hkind : twistKind S.ρ (rootCharHom a) i = .inner
    · exact hinner i hkind
    · exact hout τ K hK2 p₀ S p hp hp5 a hT hap h1 i hkind
  have hTsub : ∀ O, CFSG.Open.IsSubnormal (T O) (M ⊓ Subgroup.centralizer {d}) := by
    rintro ⟨_, i, rfl⟩
    have hΨ : rationalRoots S.ρ (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) :=
      rationalRoots_subset_kernelRoots hker i
    have hcl : ∀ γ (hγ : γ ∈ rationalRoots S.ρ (rootCharHom a) i) β
        (hβ : β ∈ kernelRoots (rootCharHom a)),
        (⟦⟨β, hβ⟩⟧ : KernelComponent (rootCharHom a)) = ⟦⟨γ, hΨ hγ⟩⟧ →
          β ∈ rationalRoots S.ρ (rootCharHom a) i :=
      fun γ hγ β hβ h => rationalRoots_closed hker hform i hγ hβ h
    have hnorm := rootSpan_le_normalizer_of_closed (L := L) hΨ hcl
    have hsub : ((rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i)).subgroupOf
        (toralCentralizer τ L a)).IsSubnormal :=
      isSubnormal_subgroupOf_step
        (iSup₂_le fun α hα => le_iSup₂_of_le (f := fun α (_ : α ∈ kernelRoots (rootCharHom a)) =>
          rootSubgroup τ L α) α (hΨ hα) le_rfl)
        (isSubnormal_kernelRootSpan a) fun y hy x hx =>
          (Subgroup.mem_normalizer_iff.1 (hnorm hy) x).1 hx
    have h2 := isSubnormal_inf_subgroupOf hsub M
    have hTC' : toralCentralizer τ L a ⊓ M = M ⊓ Subgroup.centralizer {d} := by
      ext x
      simp only [toralCentralizer, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hMadj h.1, h.2⟩, h.1⟩⟩
    rw [hTC'] at h2
    have h3 : ((T ⟨_, i, rfl⟩).subgroupOf (M ⊓ Subgroup.centralizer {d})).IsSubnormal := by
      refine isSubnormal_subgroupOf_step (hTA _) h2 fun y hy x hx => ?_
      have hle : T ⟨_, i, rfl⟩ ≤ (T ⟨_, i, rfl⟩).comap (MulAut.conj y).toMonoidHom := by
        show ratTwo (rationalRoots S.ρ (rootCharHom a) i) M ≤ _
        rw [ratTwo, Subgroup.closure_le]
        rintro g ⟨hgA, hgM, hg2⟩
        show (MulAut.conj y) g ∈ T ⟨_, i, rfl⟩
        rw [MulAut.conj_apply]
        refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
        · exact mul_mem (mul_mem hy.1 hgA) (inv_mem hy.1)
        · exact mul_mem (mul_mem hy.2 hgM) (inv_mem hy.2)
        · have h1 := hg2.map (MulAut.conj y).toMonoidHom
          rwa [MonoidHom.map_zpowers] at h1
      exact hle hx
    exact (CFSG.Open.IsSubnormal.iff_subgroupOf (le_inf ((hTA _).trans inf_le_right) (hTC _))).2 h3
  set W : Subgroup (ModGL τ L) := ⨆ (O) (_ : ⁅T O, T O⁆ = T O), T O with hWdef
  set N₀ : Subgroup (ModGL τ L) := ⨆ (O) (_ : ¬ ⁅T O, T O⁆ = T O), T O with hN₀def
  have hWX : W ≤ S.Γ ⊓ Subgroup.centralizer {d} := by
    refine iSup₂_le fun O hO => le_inf ?_ (hTC O)
    rw [← hO]
    exact (Subgroup.commutator_mono ((hTA O).trans inf_le_right) ((hTA O).trans inf_le_right))
  have hWp : ⁅W, W⁆ = W := by
    refine le_antisymm (Subgroup.commutator_le_self _) (iSup₂_le fun O hO => ?_)
    rw [← hO]
    have hle : T O ≤ W := le_iSup₂_of_le (f := fun O (_ : ⁅T O, T O⁆ = T O) => T O) O hO le_rfl
    exact Subgroup.commutator_mono hle hle
  set Y' : Subgroup ↥M := (M ⊓ Subgroup.centralizer {d}).subgroupOf M with hY'
  set X' : Subgroup ↥M := (S.Γ ⊓ Subgroup.centralizer {d}).subgroupOf M with hX'
  have hN₀O : N₀ ≤ (GLAPPrimeCoreOf p Y').map M.subtype := by
    refine iSup₂_le fun O hO => ?_
    have hleM : T O ≤ M := (hTA O).trans inf_le_right
    have hsub' := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_comap' M.subtype (hTsub O)
    have hcop : Nat.Coprime p (Nat.card ((T O).comap M.subtype)) := by
      have e1 : Nat.card ((T O).comap M.subtype) = Nat.card (T O) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleM).toEquiv
      rw [e1]
      exact (hshape O).resolve_left hO
    have h1 := le_glaPPrimeCoreOf_of_isSubnormal hp hsub' hcop
    intro x hx
    exact ⟨⟨x, hleM hx⟩, h1 hx, rfl⟩
  have hcommWN : ∀ w ∈ W, ∀ n ∈ N₀, w * n = n * w := by
    have hle : N₀ ≤ Subgroup.centralizer (W : Set (ModGL τ L)) := by
      refine iSup₂_le fun O hO => ?_
      rw [Subgroup.le_centralizer_iff]
      refine iSup₂_le fun O' hO' => ?_
      have hne : O' ≠ O := fun h => hO (h ▸ hO')
      rw [Subgroup.le_centralizer_iff]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨_, i, rfl⟩ := O
      obtain ⟨_, j, rfl⟩ := O'
      exact (commute_rootSpan_rationalRoots hker hform (fun h => hne (Subtype.ext h))
        y ((hTA _ hy).1) x ((hTA _ hx).1)).eq
    intro w hw n hn
    exact (Subgroup.mem_centralizer_iff.1 (hle hn) w hw)
  have hTle : (⨆ O, T O) ≤ W ⊔ N₀ := by
    refine iSup_le fun O => ?_
    by_cases hO : ⁅T O, T O⁆ = T O
    · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun O (_ : ⁅T O, T O⁆ = T O) => T O) O hO le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun O (_ : ¬ ⁅T O, T O⁆ = T O) => T O) O hO le_rfl)
  obtain ⟨w, hw, n, hn, rfl⟩ := Input183.mem_sup_of_commute hcommWN (hTle hkT)
  obtain ⟨n', hn'O, hn'n⟩ := hN₀O hn
  set N : Subgroup (ModGL τ L) := (GLAPPrimeCoreOf p Y' ⊓ X').map M.subtype with hNdef
  have hnX : n ∈ S.Γ ⊓ Subgroup.centralizer {d} := by
    have h1 : n = w⁻¹ * (w * n) := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hWX hw)) hk
  have hnN : n ∈ N := by
    refine ⟨n', ⟨hn'O, ?_⟩, hn'n⟩
    show ((n' : ↥M) : ModGL τ L) ∈ S.Γ ⊓ Subgroup.centralizer {d}
    have e1 : ((n' : ↥M) : ModGL τ L) = n := hn'n
    rw [e1]
    exact hnX
  refine ⟨W, N, hWX, hWp, ?_, ⟨fun x hx c => ?_⟩, ?_, ?_⟩
  · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact hx
  · rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨x', ⟨hx'1, hx'2⟩, hx'x⟩ := hx
    have hcX : (c : ModGL τ L) ∈ S.Γ ⊓ Subgroup.centralizer {d} := c.2
    have hcM : (c : ModGL τ L) ∈ M := hΓM (Subgroup.mem_inf.1 hcX).1
    have hc'Y : (⟨c, hcM⟩ : ↥M) ∈ Y' := Subgroup.mem_subgroupOf.2
      ⟨hcM, (Subgroup.mem_inf.1 hcX).2⟩
    refine ⟨⟨c, hcM⟩ * x' * (⟨c, hcM⟩ : ↥M)⁻¹,
      ⟨CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem _ hc'Y _ hx'1, ?_⟩, ?_⟩
    · have hx'X : ((x' : ↥M) : ModGL τ L) ∈ S.Γ ⊓ Subgroup.centralizer {d} := hx'2
      show (c : ModGL τ L) * (x' : ModGL τ L) * (c : ModGL τ L)⁻¹ ∈ S.Γ ⊓ Subgroup.centralizer {d}
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcX hx'X) (Subgroup.inv_mem _ hcX)
    · show (c : ModGL τ L) * (x' : ModGL τ L) * (c : ModGL τ L)⁻¹ = (c : ModGL τ L) * x * (c : ModGL τ L)⁻¹
      rw [show ((x' : ↥M) : ModGL τ L) = (x : ModGL τ L) from hx'x]
  · rw [hNdef, Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp Y')
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hnN)

theorem twoInCoreLayer_of_langSetup_of_inner
    (hout : LangOuterTwo)
    (hK2 : ringChar K = 2) {C : Type} [Group C] [Finite C] (ι : C →* ModGL τ (AlgebraicClosure K))
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) (hT : rootDiagUnit τ a ∈ S.D.torus)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hinner : ∀ i : KernelComponent (rootCharHom a), twistKind S.ρ (rootCharHom a) i = .inner →
      ⁅ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model,
          ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model⁆ =
          ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model ∨
        Nat.Coprime p (Nat.card (ratTwo (rationalRoots S.ρ (rootCharHom a) i) S.D.model))) :
    TwoInCoreLayer p β := by
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hι β _ hβ
  rw [hrange] at hfix
  have hlay := perfectInLayer_of_langSetup_of_prime S hp ι hι hrange β hβ hT hap h1
    (langSetup_hTame_of_prime S hp hpL (fun _ => Or.inl hp5) hT hap h1)
  exact twoInCoreLayer_of_decomp ι hι hfix hp hlay fun k hk hk2 =>
    twoDecomp_langCentralizer S hout hK2 hp hp5 hT hap h1 hinner hk hk2

theorem twoInCoreLayer_of_langSetup
    (hout : LangOuterTwo)
    (hK2 : ringChar K = 2) {C : Type} [Group C] [Finite C] (ι : C →* ModGL τ (AlgebraicClosure K))
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) (hT : rootDiagUnit τ a ∈ S.D.torus)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hexc : ¬ (τ = .F4 ∧ S.D.q = 2 ∧ p = 5)) (hG2 : τ = .G2 → 4 ≤ S.D.q) : TwoInCoreLayer p β :=
  twoInCoreLayer_of_langSetup_of_inner S hout hK2 ι hι hrange β hβ hT hp hp5 hap h1
    fun i hkind => ratTwo_inner S hK2 hp hp5 hT i hkind hexc hG2

end LangMain

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141f

end
