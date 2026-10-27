module

public import CFSG.Mathlib.RingTheory.UnitOrderOf

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141d2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FieldCopy
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SmallField
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Two
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallB2Root

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141c CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)

section OddOrder

variable {G : Type} [Group G]

theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {y : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : y ^ a ∈ H) (hb : y ^ b ∈ H) : y ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hy : y = (y ^ a) ^ (Nat.gcdA a b) * (y ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast y a, ← zpow_natCast y b, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [hy]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

theorem mul_pow_mem_of_mem_normalizer {N : Subgroup G} {t n : G}
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (hn : n ∈ N) (m : ℕ) :
    (t ^ m)⁻¹ * (t * n) ^ m ∈ N := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hconj : ∀ x ∈ N, t ^ (m + 1) * x * (t ^ (m + 1))⁻¹ ∈ N := fun x hx =>
      (Subgroup.mem_normalizer_iff.1 (pow_mem ht (m + 1)) x).1 hx
    have e : (t ^ (m + 1))⁻¹ * (t * n) ^ (m + 1) =
        ((t⁻¹ * ((t ^ m)⁻¹ * (t * n) ^ m) * t) * n) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    refine mul_mem ?_ hn
    have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem ht) _).1 ih
    simpa using h1

theorem mem_of_two_of_mul {N : Subgroup G} {t n : G} (ht : t ∈ Subgroup.normalizer (N : Set G))
    {m : ℕ} (htm : t ^ m = 1) (hm : Odd m) (hn : n ∈ N)
    (h2 : IsPGroup 2 ↥(Subgroup.zpowers (t * n))) : t * n ∈ N := by
  obtain ⟨e, he⟩ := exists_pow_eq_one_of_isPGroup h2
  have h1 : (t * n) ^ m ∈ N := by
    have := mul_pow_mem_of_mem_normalizer ht hn m
    rwa [htm, inv_one, one_mul] at this
  have h2' : (t * n) ^ (2 ^ e) ∈ N := by rw [he]; exact one_mem _
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hm)
  exact mem_of_pow_mem_of_coprime hcop h2' h1



end OddOrder

section GoodFixedConj

theorem goodFixed_of_conj_eq {S : Type} [Group S] {α δ ψ : MulAut S} (h : ψ * α * ψ⁻¹ = δ)
    (hδ : GoodFixed ↥(fixSubgroup δ)) : GoodFixed ↥(fixSubgroup α) := by
  have hc : MulAut.congr ψ α = δ := by
    rw [← h]
    exact MulEquiv.ext fun _ => rfl
  rw [← hc, Inputs141c.fixSubgroup_congr] at hδ
  exact goodFixed_of_mulEquiv ((fixSubgroup α).equivMapOfInjective ψ.toMonoidHom ψ.injective) hδ

theorem goodFixed_of_congr {S G : Type} [Group S] [Group G] (e : S ≃* G) {β : MulAut S}
    (h : GoodFixed ↥(fixSubgroup (MulAut.congr e β))) : GoodFixed ↥(fixSubgroup β) := by
  rw [Inputs141c.fixSubgroup_congr] at h
  exact goodFixed_of_mulEquiv ((fixSubgroup β).equivMapOfInjective e.toMonoidHom e.injective) h

end GoodFixedConj

section FieldUntw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise


theorem goodFixed_entrywiseAdjointAut_two (τ : Tag) {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) : GoodFixed ↥(fixSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨-, hinj, -, hJΓ, hΓeq, hJnormal, hcomm⟩ :=
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
  let J : Subgroup ↥(adjointGroup τ K) :=
    (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
  have hJmem : ∀ x : adjointGroup τ K,
      x ∈ J ↔ (x : ModGL τ K) ∈ fixedFieldImage τ σ := fun x => Iff.rfl
  have hJle : J ≤ fixSubgroup (entrywiseAdjointAut τ σ) := fun x hx =>
    (hfix x).2 (hJΓ ((hJmem x).1 hx))
  have hJn : (J.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).2 fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hJmem, hJmem]
    exact Subgroup.mem_normalizer_iff.1 (hΓnorm ((hfix g).1 hg)) (h : ModGL τ K)
  let eJ : J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans
      ((adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ hinj).symm
  have hsol : Group.IsSolvable
      (↥(fixSubgroup (entrywiseAdjointAut τ σ)) ⧸
        J.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    have hx : ((x : adjointGroup τ K) : ModGL τ K) ∈ entrywiseFixedGroup τ σ :=
      (hfix x.1).1 x.2
    have hy : ((y : adjointGroup τ K) : ModGL τ K) ∈ entrywiseFixedGroup τ σ :=
      (hfix y.1).1 y.2
    have hq := hcomm (QuotientGroup.mk ⟨_, hx⟩) (QuotientGroup.mk ⟨_, hy⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      hJmem]
    exact hq
  have h2 : ∀ g : ↥(fixSubgroup (entrywiseAdjointAut τ σ)), IsPGroup 2 ↥(Subgroup.zpowers g) →
      g ∈ J.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ)) := by
    intro g hg
    obtain ⟨m, hm⟩ := exists_pow_eq_one_of_isPGroup hg
    have hxΓ : ((g : adjointGroup τ K) : ModGL τ K) ∈ entrywiseFixedGroup τ σ :=
      (hfix g.1).1 g.2
    let N := (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)
    let x : ↥(entrywiseFixedGroup τ σ) := ⟨_, hxΓ⟩
    have hx2 : x ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      have h1 := congrArg (fun y : ↥(fixSubgroup (entrywiseAdjointAut τ σ)) =>
        ((y : adjointGroup τ K) : ModGL τ K)) hm
      simpa using h1
    have hmem : (x : ModGL τ K) ∈ (entrywiseFixedTorus τ σ : Set (ModGL τ K)) *
        (fixedFieldImage τ σ : Set (ModGL τ K)) := by
      rw [← hΓeq]
      exact hxΓ
    obtain ⟨t, ht, j, hj, htj⟩ := Set.mem_mul.1 hmem
    have htΓ : t ∈ entrywiseFixedGroup τ σ := ht.2
    have hjΓ : j ∈ entrywiseFixedGroup τ σ := hJΓ hj
    have hxeq : x = ⟨t, htΓ⟩ * ⟨j, hjΓ⟩ := Subtype.ext htj.symm
    have hjN : (⟨j, hjΓ⟩ : ↥(entrywiseFixedGroup τ σ)) ∈ N := hj
    have hqx : (QuotientGroup.mk x : ↥(entrywiseFixedGroup τ σ) ⧸ N) =
        QuotientGroup.mk ⟨t, htΓ⟩ := by
      rw [hxeq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hjN, mul_one]
    have ht1 : (⟨t, htΓ⟩ : ↥(entrywiseFixedGroup τ σ)) ^ (Nat.card K - 1) = 1 :=
      Subtype.ext (by
        simpa using pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ht.1))
    have hA : (QuotientGroup.mk x : ↥(entrywiseFixedGroup τ σ) ⧸ N) ^ (2 ^ m) = 1 := by
      rw [← QuotientGroup.mk_pow, hx2, QuotientGroup.mk_one]
    have hB : (QuotientGroup.mk x : ↥(entrywiseFixedGroup τ σ) ⧸ N) ^ (Nat.card K - 1) = 1 := by
      rw [hqx, ← QuotientGroup.mk_pow, ht1, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (2 ^ m) (Nat.card K - 1) :=
      Nat.Coprime.pow_left m (Nat.coprime_two_left.2 odd_card_sub_one)
    have h1 := (pow_gcd_eq_one (a := (QuotientGroup.mk x : ↥(entrywiseFixedGroup τ σ) ⧸ N))).2 ⟨hA, hB⟩
    rw [hcop.gcd_eq_one, pow_one, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.2 ((hJmem _).2 h1)
  by_cases hG2 : τ = .G2 ∧ Nat.card (fixSubfield σ) = 2
  ·
    obtain ⟨rfl, hk2⟩ := hG2
    right
    intro P hP
    have : Finite (ModGL Tag.G2 (fixSubfield σ)) := finite_modGL
    have hPJ : P ≤ J.subgroupOf (fixSubgroup (entrywiseAdjointAut .G2 σ)) := by
      haveI := hsol
      have hP0 : ⁅P.map (QuotientGroup.mk' (J.subgroupOf (fixSubgroup (entrywiseAdjointAut .G2 σ)))),
          P.map (QuotientGroup.mk' (J.subgroupOf (fixSubgroup (entrywiseAdjointAut .G2 σ))))⁆ =
          P.map (QuotientGroup.mk' (J.subgroupOf (fixSubgroup (entrywiseAdjointAut .G2 σ)))) := by
        rw [← Subgroup.map_commutator, hP]
      have hbot := eq_bot_of_perfect_of_isSolvable hP0
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
      exact hbot
    have h1 : Nat.card ↥P ≤ Nat.card ↥(J.subgroupOf (fixSubgroup (entrywiseAdjointAut .G2 σ))) :=
      Subgroup.card_le_of_le hPJ
    have h3 : Nat.card ↥(J.subgroupOf (fixSubgroup (entrywiseAdjointAut .G2 σ))) = 12096 := by
      rw [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hJle).trans eJ).toEquiv,
        CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk2]
      rfl
    omega
  · left
    have hk3 : τ = .G2 → 3 ≤ Nat.card (fixSubfield σ) := by
      intro h
      have h2' : 1 < Nat.card (fixSubfield σ) := Finite.one_lt_card
      have : Nat.card (fixSubfield σ) ≠ 2 := fun h' => hG2 ⟨h, h'⟩
      omega
    have hperf := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup τ
      (fixSubfield σ) hk3
    obtain ⟨hs, hnc⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isSimpleGroup_adjointGroup_of_perfect τ
        (fixSubfield σ) hperf
    haveI := hs
    have hq : CFSG.IsQuasisimple ↥(J.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hJle).trans eJ).symm
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
    exact ⟨_, hJn, hq, hsol, h2⟩

end FieldUntw

section FieldTwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley (subfieldRootGroupImage)
open scoped Pointwise commutatorElement


theorem goodFixed_fieldActor_twE6 {d m : ℕ} (hd : 1 ≤ d) (hm : 3 ≤ m) (hmodd : Odd m) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * d * m)) (κ : K ≃+* K)
    (hκ : ∀ c, κ c = c ^ 2 ^ (2 * d)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ (d * m))
    (σ₀ : fixSubfield κ ≃+* fixSubfield κ) (hσ₀ : ∀ c, (σ₀ c : K) = (c : K) ^ 2 ^ d) (ε : K ≃+* K)
    (hε : ∀ c, ε c = c ^ 2 ^ (d * (m + 1))) :
    GoodFixed ↥(fixSubgroup (fieldActor (t := TwistTag.E6) σ ε)) := by
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
  have hsol : Group.IsSolvable (↥F ⧸ commutator ↥F) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hxy : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hxy, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  left
  refine ⟨commutator ↥F, inferInstance, hq, hsol, fun g hg2 => ?_⟩
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
    exact hCψJ (mem_of_two_of_mul hhN hh1 odd_card_sub_one hc hy2)
  have h1 : (g : ↥C) ∈ ⁅F, F⁆ := by
    rw [hder']
    exact Subgroup.mem_subgroupOf.2 hyC
  rw [← Subgroup.map_subtype_commutator] at h1
  obtain ⟨g', hg', hgg'⟩ := h1
  rwa [← Subtype.ext hgg']

theorem goodFixed_twE6_field {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ : β ^ 3 = 1) (hη1 : Θ β ≠ 1) :
    GoodFixed ↥(fixSubgroup β) := by
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order Nat.prime_two hf K
      hK' σ hσ Θ hΘ Nat.prime_three (by norm_num) β hβ hη1
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality Nat.prime_two
      (by omega : 1 ≤ 2 * f) hK'
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ 2 ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hdp : d * 3 = f := by rw [hd, mul_comm]
  have hKdp : Nat.card K = 2 ^ (2 * d * 3) := by rw [hK', mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ 2 ^ (d * 3) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ 2 ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hδ := goodFixed_fieldActor_twE6 hd1 le_rfl (by decide) K hKdp κ hκ σ hσdp
    (fixSubfieldRestrict T κ) hσ₀ ε hε
  have hβr : GoodFixed ↥(fixSubgroup (β ^ r)) := goodFixed_of_conj_eq hψ hδ
  rwa [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_pow_eq_of_pow_pow' hrs] at hβr

end FieldTwE6

section Lang

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open scoped Pointwise

theorem card_dvd_of_isLThreeFour' {G : Type} [Group G] {J : Subgroup G}
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) : 20160 ∣ Nat.card ↥J := by
  have h1 := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hJt
  have h2 : Nat.card (barOf 3 J) = Nat.card (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) *
      Nat.card (Subgroup.center (barOf 3 J)) := Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card ↥J = Nat.card (barOf 3 J) * Nat.card (GLAPPrimeCore 3 ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [h3, h2, h1]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _

theorem isLThreeFour_barOf_of_mulEquiv {G H : Type} [Group G] [Group H] {J : Subgroup G}
    {R : Subgroup H} [Finite ↥J] (e : ↥J ≃* ↥R)
    (h : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) :
    IsLThreeFour (barOf 3 R ⧸ Subgroup.center (barOf 3 R)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥R := Finite.of_equiv _ e.toEquiv
  have hmap : (GLAPPrimeCore 3 ↥J).map (e : ↥J →* ↥R) = GLAPPrimeCore 3 ↥R := by
    apply le_antisymm
    · exact CFSG.map_pPrimeCore_le (e : ↥J →* ↥R) e.surjective
    · intro x hx
      have h1 := CFSG.map_pPrimeCore_le (e.symm : ↥R →* ↥J) e.symm.surjective ⟨x, hx, rfl⟩
      exact ⟨e.symm x, h1, by simp⟩
  let eb : barOf 3 J ≃* barOf 3 R := QuotientGroup.congr _ _ e hmap
  let ez : (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≃* (barOf 3 R ⧸ Subgroup.center (barOf 3 R)) :=
    QuotientGroup.congr _ _ eb (Subgroup.map_center_eq eb)
  exact Lemma1245.isLThreeFour_congr ez h


@[expose] def LangInnerTwo : Prop :=
  ∀ (τ : Tag) (K : Type) [Field K] [Finite K], ringChar K = 2 →
    ∀ (p₀ : ℕ) (S : LangSetup τ (AlgebraicClosure K) p₀)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ), rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ 3 = 1) → rootDiagUnit τ a ≠ 1 →
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        IsLThreeFour (barOf 3 (rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center (barOf 3 (rationalComponent S.ρ S.Γ (rootCharHom a) i))) →
        ∀ k ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}, IsPGroup 2 ↥(Subgroup.zpowers k) →
          ∃ j ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
            j⁻¹ * k ∈ Subgroup.centralizer
              (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL τ (AlgebraicClosure K)))


theorem structAt_of_langSetup (hres : LangInnerTwo) {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) {C : Type} [Group C]
    [Finite C] (ι : C →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι)
    (hrange : ι.range = S.Γ) (β : MulAut C) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {J : Subgroup C} (hJ : IsComponentOf J (fixSubgroup β))
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) :
    StructAt β J := by
  classical
  obtain ⟨i, hq, hJR⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S
    Nat.prime_three ι hι hrange β hβ hT hap h1 hTame hJ
  have hRt : IsLThreeFour (barOf 3 (rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center (barOf 3 (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :=
    isLThreeFour_barOf_of_mulEquiv ((J.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hJR)) hJt
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hι β _ hβ
  refine ⟨{J, fixSubgroup β ⊓ Subgroup.centralizer (J : Set C)}, ?_, ?_, ?_⟩
  · intro L hL L' hL' hne x hx y hy
    rcases hL with rfl | rfl <;> rcases hL' with rfl | rfl
    · exact absurd rfl hne
    · exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x hx
    · exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 y hy).symm
    · exact absurd rfl hne
  · intro k hk hk2
    have hk' : ι k ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
      rw [← hrange, ← hfix]
      exact ⟨k, hk, rfl⟩
    have hk2' : IsPGroup 2 ↥(Subgroup.zpowers (ι k)) := by
      have h := hk2.map ι
      rwa [MonoidHom.map_zpowers] at h
    obtain ⟨j', hj', hjk⟩ := hres τ K hK2 p₀ S a hT hap h1 i hq hRt (ι k) hk' hk2'
    rw [← hJR] at hj' hjk
    obtain ⟨j, hj, rfl⟩ := hj'
    have hc : j⁻¹ * k ∈ fixSubgroup β ⊓ Subgroup.centralizer (J : Set C) := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hJ.1 hj)) hk, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      apply hι
      have h := Subgroup.mem_centralizer_iff.1 hjk (ι x) ⟨x, hx, rfl⟩
      simp only [map_mul, map_inv]
      exact h
    have hkj : k = j * (j⁻¹ * k) := by group
    rw [hkj]
    have hJle : J ≤ sSup ({J, fixSubgroup β ⊓ Subgroup.centralizer (J : Set C)} : Set (Subgroup C)) :=
      le_sSup (Set.mem_insert _ _)
    have hCle : fixSubgroup β ⊓ Subgroup.centralizer (J : Set C) ≤
        sSup ({J, fixSubgroup β ⊓ Subgroup.centralizer (J : Set C)} : Set (Subgroup C)) :=
      le_sSup (Set.mem_insert_of_mem _ rfl)
    exact mul_mem (hJle hj) (hCle hc)
  · exact le_iSup₂_of_le J (Set.mem_insert _ _) (le_iSup_of_le hJ le_rfl)

theorem mem_rootSpan_of_two {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hap : ∀ i, a i ^ 3 = 1) {k : ModGL τ (AlgebraicClosure K)}
    (hk : k ∈ toralCentralizer τ (AlgebraicClosure K) a) (hk2 : IsPGroup 2 ↥(Subgroup.zpowers k)) :
    k ∈ rootSpan τ (AlgebraicClosure K) (rootCharKernel a) := by
  classical
  obtain ⟨-, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ (AlgebraicClosure K) a
  have h3 : IsPGroup 3 (↥(toralCentralizer τ (AlgebraicClosure K) a) ⧸
      (toralRootGroup τ (AlgebraicClosure K) a).subgroupOf (toralCentralizer τ (AlgebraicClosure K) a)) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isPGroup_quotient Nat.prime_three hap).of_surjective
      φ hφ
  have hkM : k ∈ toralRootGroup τ (AlgebraicClosure K) a := by
    obtain ⟨m, hm⟩ := exists_pow_eq_one_of_isPGroup hk2
    set x : ↥(toralCentralizer τ (AlgebraicClosure K) a) := ⟨k, hk⟩ with hxdef
    obtain ⟨n, hn⟩ := h3 (QuotientGroup.mk x)
    have hx2 : x ^ (2 ^ m) = 1 := Subtype.ext (by simpa using hm)
    have hA : (QuotientGroup.mk x : ↥(toralCentralizer τ (AlgebraicClosure K) a) ⧸
        (toralRootGroup τ (AlgebraicClosure K) a).subgroupOf (toralCentralizer τ (AlgebraicClosure K) a)) ^
          (2 ^ m) = 1 := by
      rw [← QuotientGroup.mk_pow, hx2, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (2 ^ m) (3 ^ n) := Nat.Coprime.pow _ _ (by norm_num)
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
  obtain ⟨N, hN, hbN⟩ := exists_odd_pow_eq_one hK2 b
  exact mem_of_two_of_mul htN
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hbN) hN hu hk2

@[expose] def LangOrbitTwo : Prop :=
  ∀ (τ : Tag) (K : Type) [Field K] [Finite K], ringChar K = 2 →
    ∀ (p₀ : ℕ) (S : LangSetup τ (AlgebraicClosure K) p₀)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ), rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ 3 = 1) → rootDiagUnit τ a ≠ 1 →
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        IsLThreeFour (barOf 3 (rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center (barOf 3 (rationalComponent S.ρ S.Γ (rootCharHom a) i))) →
        ∀ g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i),
          g⁻¹ * S.D.step g ∈ Subgroup.centralizer
            (rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :
              Set (ModGL τ (AlgebraicClosure K))) →
          (∃ m : ℕ, g ^ (2 ^ m) ∈ Subgroup.centralizer
            (rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :
              Set (ModGL τ (AlgebraicClosure K)))) →
          (∀ x ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i,
            g * x * g⁻¹ ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i) →
          ∃ j ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
            j⁻¹ * g ∈ Subgroup.centralizer
              (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL τ (AlgebraicClosure K)))

theorem langInnerTwo_of_orbitTwo (hres : LangOrbitTwo) : LangInnerTwo := by
  intro τ K _ _ hK2 p₀ S a hT hap h1 i hq h20 k hk hk2
  classical
  have hΓ : S.Γ ≤ adjointGroup τ (AlgebraicClosure K) :=
    (Subgroup.commutator_le_self S.D.model).trans inf_le_left
  have hΓfix : ∀ x ∈ S.Γ, S.D.step x = x := fun x hx =>
    ((Subgroup.commutator_le_self S.D.model) hx).2
  have hkX : k ∈ toralCentralizer τ (AlgebraicClosure K) a :=
    Subgroup.mem_inf.2 ⟨hΓ (Subgroup.mem_inf.1 hk).1, (Subgroup.mem_inf.1 hk).2⟩
  have hkU := mem_rootSpan_of_two hK2 hap hkX hk2
  have hker := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rho_mem_kernelRoots_of_mem_torus S hT
  have hform := S.frob.iform_eq
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ (AlgebraicClosure K) (rootCharHom a)).2.1
  let A : Set.range (rationalRoots S.ρ (rootCharHom a)) → Subgroup (ModGL τ (AlgebraicClosure K)) :=
    fun O => rootSpan τ (AlgebraicClosure K) O.1
  have hc : ∀ O O', O ≠ O' → ∀ x ∈ A O, ∀ y ∈ A O', Commute x y := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.commute_rootSpan_rationalRoots hker hform
      (fun h => hne (Subtype.ext h))
  have hF : ∀ O, ∀ x ∈ A O, S.D.step x ∈ A O := by
    rintro ⟨_, i, rfl⟩ x hx
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.step_mem_rootSpan S
      (fun γ hγ => (rationalRoots_subset_kernelRoots hker i hγ).1)
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rationalRoots_mapsTo i) hx
  have hU : rootSpan τ (AlgebraicClosure K) (rootCharKernel a) ≤ ⨆ O, A O := by
    refine le_trans (iSup_componentRootSpan (AlgebraicClosure K) (χ := rootCharHom a)).ge (iSup_le fun i => ?_)
    have h : componentRootSpan (AlgebraicClosure K) (rootCharHom a) i ≤ A ⟨_, i, rfl⟩ :=
      rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩
    exact h.trans (le_iSup A ⟨_, i, rfl⟩)
  set O0 : Set.range (rationalRoots S.ρ (rootCharHom a)) := ⟨_, i, rfl⟩ with hO0
  set B : Subgroup (ModGL τ (AlgebraicClosure K)) := ⨆ O : {O // O ≠ O0}, A O.1 with hBdef
  have hBC : B ≤ Subgroup.centralizer (A O0 : Set (ModGL τ (AlgebraicClosure K))) :=
    iSup_le fun O x hx => Subgroup.mem_centralizer_iff.2 fun y hy => (hc O0 O.1 (Ne.symm O.2) y hy x hx).eq
  have hsplit : (⨆ O, A O) ≤ A O0 ⊔ B := by
    refine iSup_le fun O => ?_
    by_cases hO : O = O0
    · rw [hO]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun O : {O // O ≠ O0} => A O.1) ⟨O, hO⟩)
  have hcomm : ∀ x ∈ A O0, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hBC hy) x hx
  obtain ⟨k₀, hk₀, c, hcB, hkc⟩ := Input183.mem_sup_of_commute hcomm (hsplit (hU hkU))
  have hFB : ∀ y ∈ B, S.D.step y ∈ B := by
    have hle : B ≤ B.comap S.D.step :=
      iSup_le fun O x hx => Subgroup.mem_comap.2 (Subgroup.mem_iSup_of_mem O (hF O.1 x hx))
    exact fun y hy => hle hy
  have hstepk : S.D.step k = k := hΓfix k (Subgroup.mem_inf.1 hk).1
  have hz : k₀⁻¹ * S.D.step k₀ = c * (S.D.step c)⁻¹ := by
    have e1 : S.D.step k₀ * S.D.step c = k₀ * c := by rw [← map_mul, ← hkc, hstepk]
    calc k₀⁻¹ * S.D.step k₀ = k₀⁻¹ * (S.D.step k₀ * S.D.step c) * (S.D.step c)⁻¹ := by group
      _ = k₀⁻¹ * (k₀ * c) * (S.D.step c)⁻¹ := by rw [e1]
      _ = c * (S.D.step c)⁻¹ := by group
  have hzC : k₀⁻¹ * S.D.step k₀ ∈ Subgroup.centralizer (A O0 : Set (ModGL τ (AlgebraicClosure K))) := by
    rw [hz]
    exact hBC (mul_mem hcB (inv_mem (hFB c hcB)))
  have hk₀2 : ∃ m : ℕ, k₀ ^ (2 ^ m) ∈ Subgroup.centralizer (A O0 : Set (ModGL τ (AlgebraicClosure K))) := by
    obtain ⟨m, hm⟩ := exists_pow_eq_one_of_isPGroup hk2
    refine ⟨m, ?_⟩
    have hcomm' : Commute k₀ c := hcomm k₀ hk₀ c hcB
    have e1 : k₀ ^ (2 ^ m) * c ^ (2 ^ m) = 1 := by rw [← hcomm'.mul_pow, ← hkc, hm]
    have e2 : k₀ ^ (2 ^ m) = (c ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left e1
    rw [e2]
    exact hBC (inv_mem (pow_mem hcB _))
  have hk₀N : ∀ x ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i,
      k₀ * x * k₀⁻¹ ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    intro x hx
    obtain ⟨hxA, hxΓ⟩ := Subgroup.mem_inf.1 hx
    have e1 : k₀ * x * k₀⁻¹ = k * x * k⁻¹ := by
      have hcx : c * x = x * c := (hcomm x hxA c hcB).symm
      rw [hkc]
      calc k₀ * x * k₀⁻¹ = k₀ * (x * c) * c⁻¹ * k₀⁻¹ := by group
        _ = k₀ * (c * x) * c⁻¹ * k₀⁻¹ := by rw [hcx]
        _ = k₀ * c * x * (k₀ * c)⁻¹ := by group
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hk₀ hxA) (inv_mem hk₀), ?_⟩
    rw [e1]
    exact mul_mem (mul_mem (Subgroup.mem_inf.1 hk).1 hxΓ) (inv_mem (Subgroup.mem_inf.1 hk).1)
  obtain ⟨j, hj, hjk₀⟩ := hres τ K hK2 p₀ S a hT hap h1 i hq h20 k₀ hk₀ hzC hk₀2 hk₀N
  refine ⟨j, hj, ?_⟩
  have hRA : (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL τ (AlgebraicClosure K))) ⊆
      (A O0 : Set (ModGL τ (AlgebraicClosure K))) := fun y hy =>
    (Subgroup.mem_inf.1 (Subgroup.commutator_le_self _ hy)).1
  have hcR : c ∈ Subgroup.centralizer
      (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL τ (AlgebraicClosure K))) :=
    Subgroup.centralizer_le hRA (hBC hcB)
  rw [hkc, ← mul_assoc]
  exact mul_mem hjk₀ hcR

end Lang

section Cyc

open CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s] (P : CycFamily F s)

theorem mem_Z_of_mu_mem_Z (g : ∀ k, P.S k) (hg : P.mu g ∈ P.Z) (k : ZMod s) : (g k : G) ∈ P.Z := by
  classical
  rw [P.mem_Z]
  intro a ha
  obtain ⟨h, rfl⟩ := P.mem_A_iff.1 ha
  have hg' : g = Pi.mulSingle k (g k) * Function.update g k 1 := by
    funext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
  have hh' : h = Pi.mulSingle k (h k) * Function.update h k 1 := by
    funext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
  have hdisj : ∀ (u v : ∀ j, P.S j), u k = 1 → Commute (P.mu (Pi.mulSingle k (v k))) (P.mu u) := by
    intro u v hu
    refine P.commute_mu_of_commute _ _ ?_
    funext j
    by_cases hj : j = k
    · subst hj
      simp [hu]
    · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj]
  have hgk : (g k : G) = P.mu g * (P.mu (Function.update g k 1))⁻¹ := by
    have h1 : P.mu g = (g k : G) * P.mu (Function.update g k 1) := by
      conv_lhs => rw [hg', map_mul, P.mu_mulSingle]
    rw [h1, mul_inv_cancel_right]
  have c1 : Commute (g k : G) (P.mu (Function.update h k 1)) := by
    have := hdisj (Function.update h k 1) g (by simp)
    rwa [P.mu_mulSingle] at this
  have c2 : Commute (g k : G) (h k : G) := by
    have c := hdisj (Function.update g k 1) h (by simp)
    rw [P.mu_mulSingle] at c
    have c0 : Commute (P.mu g) (h k : G) := ((P.mem_Z.1 hg) (h k) (P.S_le_A k (h k).2)).symm
    rw [hgk]
    exact c0.mul_left c.symm.inv_left
  have hmu : P.mu h = (h k : G) * P.mu (Function.update h k 1) := by
    conv_lhs => rw [hh', map_mul, P.mu_mulSingle]
  rw [hmu]
  exact (c2.mul_right c1).eq.symm

theorem exists_eq_zeta_norm_of_mod {x : G} (hxA : x ∈ P.A) (hx : F x * x⁻¹ ∈ P.Z) :
    ∃ y : P.S 0, (y : G) ∈ P.Y ∧ ∃ ζ ∈ P.Z, ζ ∈ P.A ∧ x = ζ * P.norm y := by
  obtain ⟨f, rfl⟩ := P.mem_A_iff.1 hxA
  set g : ∀ k, P.S k := P.shift f * f⁻¹ with hg
  have hgmu : P.mu g ∈ P.Z := by
    rw [hg, map_mul, map_inv, ← P.F_mu]
    exact hx
  have hgZ : ∀ k, (g k : G) ∈ P.Z := fun k => mem_Z_of_mu_mem_Z P g hgmu k
  have hgk : ∀ k, ((g k : P.S k) : G) =
      F ((f (k - 1) : P.S (k - 1)) : G) * ((f k : P.S k) : G)⁻¹ := by
    intro k
    simp [hg, P.coe_shift_apply]
  have hrec : ∀ k : ZMod s, ((f k : P.S k) : G) =
      ((g k : G))⁻¹ * F ((f (k - 1) : P.S (k - 1)) : G) := by
    intro k
    rw [hgk k]
    group
  have hclaim : ∀ n : ℕ, ∃ ζ ∈ P.Z, ((f (n : ZMod s) : P.S _) : G) =
      ζ * iterHom F n ((f 0 : P.S 0) : G) := by
    intro n
    induction n with
    | zero =>
      refine ⟨1, one_mem _, ?_⟩
      rw [P.val_apply_congr f (Nat.cast_zero (R := ZMod s))]
      simp
    | succ n ih =>
      obtain ⟨ζ, hζ, hζe⟩ := ih
      have hidx : ((n + 1 : ℕ) : ZMod s) - 1 = (n : ZMod s) := by
        rw [Nat.cast_succ]
        exact add_sub_cancel_right _ _
      refine ⟨((g ((n + 1 : ℕ) : ZMod s) : G))⁻¹ * F ζ,
        mul_mem (inv_mem (hgZ _)) (P.F_mem_Z hζ), ?_⟩
      rw [hrec, P.val_apply_congr f hidx, hζe, iterHom_succ, map_mul]
      group
  obtain ⟨ζs, hζsZ, hζs⟩ := hclaim s
  have h0 : ((f ((s : ℕ) : ZMod s) : P.S _) : G) = ((f 0 : P.S 0) : G) :=
    P.val_apply_congr f (ZMod.natCast_self s)
  rw [h0] at hζs
  refine ⟨f 0, ⟨(f 0).2, ?_⟩, P.mu (f * (P.diag (f 0))⁻¹), P.mu_mem_Z _ fun k => ?_, ?_, ?_⟩
  · have : iterHom F s ((f 0 : P.S 0) : G) * ((f 0 : P.S 0) : G)⁻¹ = ζs⁻¹ := by
      generalize iterHom F s ((f 0 : P.S 0) : G) = I at hζs ⊢
      rw [hζs]
      group
    rw [this]
    exact inv_mem hζsZ
  · obtain ⟨ζ, hζ, hζe⟩ := hclaim k.val
    have h1 : ((f ((k.val : ℕ) : ZMod s) : P.S _) : G) = ((f k : P.S k) : G) :=
      P.val_apply_congr f (ZMod.natCast_zmod_val k)
    rw [h1] at hζe
    simp only [Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, CycFamily.coe_diag_apply]
    rw [hζe]
    simpa using hζ
  · rw [← P.mu_range]
    exact ⟨_, rfl⟩
  · show P.mu f = P.mu (f * (P.diag (f 0))⁻¹) * P.mu (P.diag (f 0))
    rw [← map_mul, inv_mul_cancel_right]

theorem exists_conj_norm_of_mod {x : G} (hxA : x ∈ P.A) (hx : F x * x⁻¹ ∈ P.Z) :
    ∃ y : P.S 0, (y : G) ∈ P.Y ∧ (∀ c : P.S 0, x * P.norm c * x⁻¹ = P.norm (y * c * y⁻¹)) ∧
      ∀ n : ℕ, x ^ n ∈ P.Z → ((y : G)) ^ n ∈ P.Z := by
  obtain ⟨y, hyY, ζ, hζZ, hζA, rfl⟩ := exists_eq_zeta_norm_of_mod P hxA hx
  refine ⟨y, hyY, fun c => ?_, fun n hn => ?_⟩
  · have hc : Commute ζ (P.norm y * P.norm c * (P.norm y)⁻¹) :=
      ((P.mem_Z.1 hζZ) _ (mul_mem (mul_mem (P.norm_mem_A y) (P.norm_mem_A c))
        (inv_mem (P.norm_mem_A y)))).symm
    rw [map_mul, map_mul, map_inv]
    calc ζ * P.norm y * P.norm c * (ζ * P.norm y)⁻¹
        = (ζ * (P.norm y * P.norm c * (P.norm y)⁻¹)) * ζ⁻¹ := by group
      _ = ((P.norm y * P.norm c * (P.norm y)⁻¹) * ζ) * ζ⁻¹ := by rw [hc.eq]
      _ = P.norm y * P.norm c * (P.norm y)⁻¹ := by group
  · have hcy : Commute ζ (P.norm y) := ((P.mem_Z.1 hζZ) _ (P.norm_mem_A y)).symm
    have h1 : P.norm (y ^ n) ∈ P.Z := by
      have e : P.norm (y ^ n) = (ζ ^ n)⁻¹ * (ζ * P.norm y) ^ n := by
        rw [hcy.mul_pow, map_pow, inv_mul_cancel_left]
      rw [e]
      exact mul_mem (inv_mem (pow_mem hζZ n)) hn
    have h2 := mem_Z_of_mu_mem_Z P (P.diag (y ^ n)) h1 0
    simpa using h2

end Cyc

section Split

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

theorem exists_unit_sq_ne_one_of_isAlgClosed {L : Type} [Field L] [IsAlgClosed L] :
    ∃ u : Lˣ, u ^ 2 ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
  have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
  have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · simp [sub_eq_zero.1 h]
  · simp [eq_neg_of_add_eq_zero_left h]

theorem odd_two_pow_sub_one {e : ℕ} (he : 0 < e) : Odd (2 ^ e - 1) := by
  have h1 : 2 ^ e = 2 * 2 ^ (e - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
  exact ⟨2 ^ (e - 1) - 1, by omega⟩


theorem rootDiagUnit_pow_conj_pinnedX {τ : Tag} {L : Type} [Field L] (l : Fin τ.rank → Lˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (d : L) (n : ℕ) :
    rootDiagUnit τ l ^ n * pinnedX τ L γ d * (rootDiagUnit τ l ^ n)⁻¹ =
      pinnedX τ L γ ((rootChar l γ : L) ^ n * d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc rootDiagUnit τ l ^ (n + 1) * pinnedX τ L γ d * (rootDiagUnit τ l ^ (n + 1))⁻¹
        = rootDiagUnit τ l * (rootDiagUnit τ l ^ n * pinnedX τ L γ d * (rootDiagUnit τ l ^ n)⁻¹) *
            (rootDiagUnit τ l)⁻¹ := by rw [pow_succ']; group
      _ = pinnedX τ L γ ((rootChar l γ : L) ^ (n + 1) * d) := by
        rw [ih, rootDiagUnit_conj_pinnedX l hγ, pow_succ', mul_assoc]

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)

theorem exists_mem_CQ_of_twist_central [CharP L 2] (σ : L ≃+* L) {e : ℕ} (he : 0 < e)
    (hσ : ∀ c, σ c = c ^ (2 ^ e)) {y : ModGL τ L}
    (hy : y ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)))
    (hyc : ∀ a ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)),
      a * (frobGL σ y * y⁻¹) = (frobGL σ y * y⁻¹) * a)
    {m : ℕ} (hym : ∀ a ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)),
      a * y ^ (2 ^ m) = y ^ (2 ^ m) * a) :
    ∃ j ∈ CQ σ i, j⁻¹ * y ∈ Subgroup.centralizer (CQ σ i : Set (ModGL τ L)) := by
  classical
  have hsL := exists_unit_sq_ne_one_of_isAlgClosed (L := L)
  set c := frobGL σ y * y⁻¹ with hcdef
  have hcS : c ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) :=
    mul_mem (frobGL_mem_rootSpan σ hy) (inv_mem hy)
  have hcT := central_mem_unionTorus hsL hcS hyc
  obtain ⟨t, ht, x, hx, hyt, hφ⟩ := exists_decomp (σ := σ) hy hcT (by rw [hcdef]; group)
  have hn := torus_normalizes_CQ (σ := σ) ht hyc hφ
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup ht)
  have hfixchar := torus_fixed_char hl ht hyc hφ
  have hNodd : Odd (2 ^ e - 1) := odd_two_pow_sub_one he
  have htN : ∀ x ∈ CQ σ i, Commute x (t ^ (2 ^ e - 1)) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨γ, hγ, d, hd, rfl⟩ := hx
      have hγr := isRoot_of_mem_unionRoots hγ
      have hχ : (rootChar l γ : L) ^ (2 ^ e - 1) = 1 := by
        have h1 : (rootChar l γ : L) ^ (2 ^ e) = rootChar l γ := by
          rw [← hσ]
          exact hfixchar γ hγ
        have h0 : (rootChar l γ : L) ≠ 0 := (rootChar l γ).ne_zero
        have h3 : (rootChar l γ : L) ^ (2 ^ e - 1) * (rootChar l γ : L) = 1 * (rootChar l γ : L) := by
          rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, h1, one_mul]
        exact mul_right_cancel₀ h0 h3
      have h2 := rootDiagUnit_pow_conj_pinnedX l hγr d (2 ^ e - 1)
      rw [← hl, hχ, one_mul] at h2
      show pinnedX τ L γ d * t ^ (2 ^ e - 1) = t ^ (2 ^ e - 1) * pinnedX τ L γ d
      calc pinnedX τ L γ d * t ^ (2 ^ e - 1)
          = (t ^ (2 ^ e - 1) * pinnedX τ L γ d * (t ^ (2 ^ e - 1))⁻¹) * t ^ (2 ^ e - 1) := by rw [h2]
        _ = t ^ (2 ^ e - 1) * pinnedX τ L γ d := by group
    | one => exact Commute.one_left _
    | mul x y _ _ hx hy => exact hx.mul_left hy
    | inv x _ hx => exact hx.inv_left
  have htC : t ^ (2 ^ e - 1) ∈ Subgroup.centralizer (CQ σ i : Set (ModGL τ L)) :=
    Subgroup.mem_centralizer_iff.2 fun x hx => (htN x hx).eq
  have htN' : t ∈ Subgroup.normalizer (CQ σ i : Set (ModGL τ L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hn.1 w hw, fun hw => ?_⟩
    have h1 := hn.2 _ hw
    have e : t⁻¹ * (t * w * t⁻¹) * t = w := by group
    rwa [e] at h1
  have hCQS : CQ σ i ≤ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, d, -, rfl⟩
    exact pinnedX_mem_rootSpan hγ d
  have hym' : y ^ (2 ^ m) ∈ Subgroup.centralizer (CQ σ i : Set (ModGL τ L)) :=
    Subgroup.mem_centralizer_iff.2 fun a ha => hym a (hCQS ha)
  have h1 := mul_pow_mem_of_mem_normalizer htN' hx (2 ^ m)
  rw [← hyt] at h1
  have ht2 : t ^ (2 ^ m) ∈ CQ σ i ⊔ Subgroup.centralizer (CQ σ i : Set (ModGL τ L)) := by
    have e : t ^ (2 ^ m) = y ^ (2 ^ m) * ((t ^ (2 ^ m))⁻¹ * y ^ (2 ^ m))⁻¹ := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right hym') (Subgroup.mem_sup_left (inv_mem h1))
  have htP : t ∈ CQ σ i ⊔ Subgroup.centralizer (CQ σ i : Set (ModGL τ L)) :=
    mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hNodd)) ht2
      (Subgroup.mem_sup_right htC)
  have hyP : y ∈ CQ σ i ⊔ Subgroup.centralizer (CQ σ i : Set (ModGL τ L)) := by
    rw [hyt]
    exact mul_mem htP (Subgroup.mem_sup_left hx)
  have hcomm : ∀ a ∈ CQ σ i, ∀ b ∈ Subgroup.centralizer (CQ σ i : Set (ModGL τ L)), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb a ha
  obtain ⟨j, hj, w, hw, hjw⟩ := Input183.mem_sup_of_commute hcomm hyP
  refine ⟨j, hj, ?_⟩
  rw [hjw, inv_mul_cancel_left]
  exact hw

theorem card_componentRootSpan_b2_two {K : Type} [Field K] (hK2 : ∀ x : K, x = 0 ∨ x = 1)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) {s l : Fin Tag.F4.rank → ℤ}
    (hss : CFSG.LieType.Steinberg.Adjoint.iform s s = 2) (hll : CFSG.LieType.Steinberg.Adjoint.iform l l = 4)
    (hsl : CFSG.LieType.Steinberg.Adjoint.iform s l = -2)
    (hΨ : componentRoots χ i = {s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)}) :
    Nat.card ↥(componentRootSpan K χ i) = 720 := by
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
  rw [Nat.card_congr Φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

end Split

section OrbitInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

theorem not_isSolvable_of_isQuasisimple' {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  intro hs
  haveI := hq.1
  haveI : Nontrivial Q := by
    have := hq.2.1.toNontrivial
    exact (QuotientGroup.mk_surjective (s := Subgroup.center Q)).nontrivial
  exact Group.IsPerfect.not_isSolvable Q hs


theorem langOrbitTwo_inner {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) {p₀ : ℕ}
    (S : LangSetup τ (AlgebraicClosure K) p₀) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hRt : IsLThreeFour (barOf 3 (rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center (barOf 3 (rationalComponent S.ρ S.Γ (rootCharHom a) i))))
    {g : ModGL τ (AlgebraicClosure K)}
    (hg : g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i))
    (hgF : g⁻¹ * S.D.step g ∈ Subgroup.centralizer
      (rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :
        Set (ModGL τ (AlgebraicClosure K))))
    (hg2 : ∃ m : ℕ, g ^ (2 ^ m) ∈ Subgroup.centralizer
      (rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :
        Set (ModGL τ (AlgebraicClosure K)))) :
    ∃ j ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      j⁻¹ * g ∈ Subgroup.centralizer
        (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL τ (AlgebraicClosure K))) := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h20 := card_dvd_of_isLThreeFour' hRt
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hRdef
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
  have hsL := exists_unit_sq_ne_one_of_isAlgClosed (L := AlgebraicClosure K)
  have hgA : g ∈ P.A := hPA ▸ hg
  have hgZ : S.D.step g * g⁻¹ ∈ P.Z := by
    have hw : g⁻¹ * S.D.step g ∈ P.Z := hPZ ▸ hgF
    have e : S.D.step g * g⁻¹ = g * (g⁻¹ * S.D.step g) * g⁻¹ := by group
    rw [e, (P.mem_Z.1 hw) g hgA, mul_inv_cancel_right]
    exact hw
  obtain ⟨y₀, hy₀Y, hconj, hpow⟩ := exists_conj_norm_of_mod P hgA hgZ
  obtain ⟨m, hm⟩ := hg2
  have hy₀m : ((y₀ : ModGL τ (AlgebraicClosure K))) ^ (2 ^ m) ∈ P.Z := hpow _ (hPZ ▸ hm)
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
  have hRν : R ≤ ν.range := by
    have hΓM : S.Γ ≤ S.D.model := Subgroup.commutator_le_self _
    have hrsA : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ P.Afix := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      refine ⟨?_, (hΓM hx2).2⟩
      rw [hPA]
      exact hx1
    have hYC : ⁅P.Y, P.Y⁆ ≤ (CQ σ i).map (MulAut.conj z).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro u hu u' hu'
      obtain ⟨hv, hvZ⟩ := hYc u hu
      obtain ⟨hv', hvZ'⟩ := hYc u' hu'
      have hc := orbit_commutator_mem_CQT S hT i hs hmin σ hsL hv hv' hvZ hvZ'
      refine ⟨_, hc, ?_⟩
      show z * ⁅z⁻¹ * u * z, z⁻¹ * u' * z⁆ * z⁻¹ = ⁅u, u'⁆
      simp only [commutatorElement_def]
      group
    intro x hx
    have h1 := P.commutator_Afix_le (Subgroup.commutator_mono hrsA hrsA hx)
    obtain ⟨y, hyY, rfl⟩ := P.mem_normImage.1 h1
    obtain ⟨c, hc, hcy⟩ := hYC hyY
    refine ⟨⟨c, hc⟩, ?_⟩
    show P.norm (θ₀ ⟨c, hc⟩) = P.norm y
    congr 1
    exact Subtype.ext hcy
  set y : ModGL τ (AlgebraicClosure K) := (y₀ : ModGL τ (AlgebraicClosure K)) with hydef
  obtain ⟨hvy, hvyZ⟩ := hYc y hy₀Y
  set h := z⁻¹ * y * z with hhdef
  have hcen : ∀ W ∈ P.Z, ∀ x ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
      ({i} : Set (KernelComponent (rootCharHom a))), x * W = W * x := by
    intro W hW x hx
    rw [hUS] at hx
    exact (P.mem_Z.1 hW) x (P.S_le_A 0 (by rw [hP0]; exact hx))
  have hhm : h ^ (2 ^ m) = z⁻¹ * y ^ (2 ^ m) * z := by
    rw [hhdef]
    have e1 := map_pow (MulAut.conj z⁻¹) y (2 ^ m)
    simp only [MulAut.conj_apply, inv_inv] at e1
    exact e1.symm ▸ rfl
  obtain ⟨j₁, hj₁, hj₁c⟩ := exists_mem_CQ_of_twist_central i σ hes hσ' (hUS ▸ hvy)
    (hcen _ hvyZ) (m := m) (by rw [hhm]; exact hcen _ (hZconj' _ hy₀m))
  have hact : ∀ x : ↥(CQ σ i), g * ν x * g⁻¹ = ν ⟨j₁, hj₁⟩ * ν x * (ν ⟨j₁, hj₁⟩)⁻¹ := by
    intro x
    have hjx : h * (x : ModGL τ (AlgebraicClosure K)) * h⁻¹ = j₁ * x * j₁⁻¹ := by
      have hw := Subgroup.mem_centralizer_iff.1 hj₁c x x.2
      calc h * (x : ModGL τ (AlgebraicClosure K)) * h⁻¹
          = j₁ * ((j₁⁻¹ * h) * x * (j₁⁻¹ * h)⁻¹) * j₁⁻¹ := by group
        _ = j₁ * (x * (j₁⁻¹ * h) * (j₁⁻¹ * h)⁻¹) * j₁⁻¹ := by rw [← hw]
        _ = j₁ * x * j₁⁻¹ := by group
    have e1 : y₀ * θ₀ x * y₀⁻¹ = θ₀ (⟨j₁, hj₁⟩ * x * ⟨j₁, hj₁⟩⁻¹) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hθ₀]
      have e2 : (y₀ : ModGL τ (AlgebraicClosure K)) = z * h * z⁻¹ := by rw [hhdef, hydef]; group
      rw [e2]
      calc z * h * z⁻¹ * (z * (x : ModGL τ (AlgebraicClosure K)) * z⁻¹) * (z * h * z⁻¹)⁻¹
          = z * (h * x * h⁻¹) * z⁻¹ := by group
        _ = z * (j₁ * x * j₁⁻¹) * z⁻¹ := by rw [hjx]
    show g * P.norm (θ₀ x) * g⁻¹ = _
    rw [hconj, e1]
    show P.norm (θ₀ (⟨j₁, hj₁⟩ * x * ⟨j₁, hj₁⟩⁻¹)) = _
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    rfl
  have hRfin : Finite ↥R := by
    haveI : Finite S.D.model := S.finite
    have hle : R ≤ S.D.model :=
      (Subgroup.commutator_le_self _).trans (inf_le_right.trans (Subgroup.commutator_le_self _))
    exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
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
  have hcardCQ : Nat.card ↥(CQ σ i) =
      Nat.card ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
    rw [CQ_eq_map, Subgroup.card_map_of_injective (baseChangeGL_injective _)]
  haveI : Finite ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := Subtype.finite
  haveI : Finite ↥(CQ σ i) := by
    rw [CQ_eq_map]
    exact Finite.of_equiv _ ((componentRootSpan (fixSubfield σ) (rootCharHom a) i).equivMapOfInjective _
      (baseChangeGL_injective _)).toEquiv
  haveI : Finite ↥ν.range := Finite.of_surjective _ ν.rangeRestrict_surjective
  have hperf : Group.IsPerfect (componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
    by_cases hQ : 4 ≤ 2 ^ (e * s)
    · obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := AlgebraicClosure K) σ hσ' hes hQ
      exact isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ) (χ := rootCharHom a) ht i
    ·
      have hes1 : e * s = 1 := by
        by_contra hne
        apply hQ
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (e * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
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
      have hRC : Nat.card ↥R ≤ Nat.card ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
        have h2 : Nat.card ↥R ≤ Nat.card ↥ν.range := Subgroup.card_le_of_le hRν
        have h3 : Nat.card ↥ν.range ≤ Nat.card ↥(CQ σ i) :=
          Nat.card_le_card_of_surjective _ ν.rangeRestrict_surjective
        rw [hcardCQ] at h3
        omega
      have h20' := Nat.le_of_dvd Nat.card_pos h20
      by_cases hrank : ∀ α ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
          δ = α ∨ δ = -α
      · exfalso
        have hsolv : Group.IsSolvable ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
          CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_componentRootSpan_of_rank_one
            hKle i hrank
        have hsolvCQ : Group.IsSolvable ↥(CQ σ i) := by
          rw [CQ_eq_map]
          exact Group.isSolvable_of_surjective
            (f := ((componentRootSpan (fixSubfield σ) (rootCharHom a) i).equivMapOfInjective _
              (baseChangeGL_injective _)).toMonoidHom)
            ((componentRootSpan (fixSubfield σ) (rootCharHom a) i).equivMapOfInjective _
              (baseChangeGL_injective _)).surjective
        have hsolvν : Group.IsSolvable ↥ν.range := Group.isSolvable_of_surjective ν.rangeRestrict_surjective
        have hsolvR : Group.IsSolvable ↥R :=
          Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hRν)
            (Subgroup.inclusion_injective hRν)
        exact not_isSolvable_of_isQuasisimple' hq hsolvR
      · have hbig : ∃ α ∈ componentRoots (rootCharHom a) i, ∃ δ ∈ componentRoots (rootCharHom a) i,
            δ ≠ α ∧ δ ≠ -α := by
          push Not at hrank
          exact hrank
        have hτ' : ∀ τ : Tag, τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
          intro τ; cases τ <;> simp
        rcases hτ' τ with h | h | h | h | h | h
        ·
          exfalso
          subst h
          have hle : componentRootSpan (fixSubfield σ) (rootCharHom a) i ≤ adjointGroup .G2 (fixSubfield σ) :=
            rootSpan_le_adjointGroup _ _
          haveI : Finite ↥(adjointGroup Tag.G2 (fixSubfield σ)) := Subtype.finite
          have h12 : Nat.card ↥(adjointGroup Tag.G2 (fixSubfield σ)) = 12096 := by
            rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hKcard]
            rfl
          have h1 : Nat.card ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) ≤ 12096 :=
            (Subgroup.card_le_of_le hle).trans_eq h12
          omega
        · subst h
          by_cases hA2 : ∃ α ∈ componentRoots (rootCharHom a) i, ∃ δ ∈ componentRoots (rootCharHom a) i,
              δ ≠ α ∧ δ ≠ -α ∧ CFSG.LieType.Steinberg.Adjoint.iform α α =
                CFSG.LieType.Steinberg.Adjoint.iform δ δ ∧ CFSG.LieType.Steinberg.Adjoint.iform α δ ≠ 0
          · exact isPerfect_componentRootSpan_F4_two hK2' i hA2
          · exfalso
            push Not at hA2
            obtain ⟨s', l, hss, hll, hsl, hΨ⟩ := eq_b2Block_of_noA2 i hbig hA2
            have h720 := card_componentRootSpan_b2_two hK2' i hss hll hsl hΨ
            omega
        all_goals exact isPerfect_componentRootSpan_simplyLaced (by simp [h]) i hbig
  have hperfCQ : Group.IsPerfect ↥(CQ σ i) := by
    refine Subgroup.isPerfect_iff.2 ?_
    rw [CQ_eq_map, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hperf]
  have hjR : ν ⟨j₁, hj₁⟩ ∈ R := outer_norm_mem_rationalComponent S hT i hs hmin hperfCQ θ₀ hθfix _
  refine ⟨ν ⟨j₁, hj₁⟩, hjR, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨c, rfl⟩ := hRν hx
  have h1 := hact c
  calc ν c * ((ν ⟨j₁, hj₁⟩)⁻¹ * g)
      = (ν ⟨j₁, hj₁⟩)⁻¹ * (ν ⟨j₁, hj₁⟩ * ν c * (ν ⟨j₁, hj₁⟩)⁻¹) * g := by group
    _ = (ν ⟨j₁, hj₁⟩)⁻¹ * (g * ν c * g⁻¹) * g := by rw [h1]
    _ = (ν ⟨j₁, hj₁⟩)⁻¹ * g * ν c := by group

end OrbitInner

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e

end
