module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Invariants
public import CFSG.LocalAnalysis.EvenBN.Common.FreeSeries
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenTriality
public import CFSG.LocalAnalysis.SteinbergCCSymplecticFourRankThompson
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

theorem card_fixed_pow_two_pow {F : Type*} [Field F] [Finite F] [CharP F 2] {k : ℕ} (hk : 1 ≤ k)
    (hF : Nat.card F = (2 ^ k) ^ 2) : Nat.card {x : F // x ^ 2 ^ k = x} = 2 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  set r := 2 ^ k with hr
  have hr1 : 1 < r := Nat.one_lt_two_pow (by omega)
  let T : F →+ F :=
    { toFun := fun x => x + x ^ r
      map_zero' := by rw [zero_pow (by omega), add_zero]
      map_add' := fun x y => by rw [add_pow_char_pow]; ring }
  have hker : ∀ x, x ∈ T.ker ↔ x ^ r = x := fun x => by
    rw [AddMonoidHom.mem_ker]
    change x + x ^ r = 0 ↔ _
    rw [CharTwo.add_eq_zero, eq_comm]
  have hpow : ∀ x : F, x ^ r ^ 2 = x := fun x => by
    rw [← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hrange : ∀ y ∈ T.range, y ^ r = y := by
    rintro _ ⟨x, rfl⟩
    change (x + x ^ r) ^ r = x + x ^ r
    rw [add_pow_char_pow, ← pow_mul, ← sq, hpow, add_comm]
  have hle : Nat.card T.ker ≤ r := by
    have hp0 : (Polynomial.X ^ r - Polynomial.X : Polynomial F) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero F hr1
    have hdeg : (Polynomial.X ^ r - Polynomial.X : Polynomial F).natDegree = r :=
      FiniteField.X_pow_card_sub_X_natDegree_eq F hr1
    set Z := Finset.univ.filter (fun x : F => x ^ r = x)
    have hZ : Z.val ⊆ (Polynomial.X ^ r - Polynomial.X : Polynomial F).roots := by
      intro x hx
      rw [Polynomial.mem_roots hp0, Polynomial.IsRoot, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X]
      have hx' : x ^ r = x := (Finset.mem_filter.1 hx).2
      rw [hx', sub_self]
    have h1 := Polynomial.card_le_degree_of_subset_roots hZ
    rw [hdeg] at h1
    calc Nat.card T.ker = Z.card := by
          rw [← Nat.card_eq_finsetCard]
          exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
            rw [hker]; simp [Z])
      _ ≤ r := h1
  have hcard : Nat.card F = Nat.card T.ker * Nat.card T.range := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  have hsub : Nat.card T.range ≤ Nat.card T.ker :=
    AddSubgroup.card_le_of_le (fun y hy => (hker y).2 (hrange y hy))
  have hfix : Nat.card {x : F // x ^ r = x} = Nat.card T.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hker x).symm)
  rw [hfix]
  have h2 : r * r ≤ Nat.card T.ker * Nat.card T.ker := by
    rw [← sq, ← hF, hcard]
    exact Nat.mul_le_mul_left _ hsub
  exact le_antisymm hle (by nlinarith)

theorem mulAut_mul_conj_mul_inv {G : Type*} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem mulAutConj_range_normal {G : Type*} [Group G] :
    (MulAut.conj : G →* MulAut G).range.Normal :=
  ⟨by
    rintro _ ⟨g, rfl⟩ α
    exact ⟨α g, (mulAut_mul_conj_mul_inv α g).symm⟩⟩

theorem pow_mem_coordSet {A : Type*} [MonoidWithZero A] {r : ℕ} (hr : 1 ≤ r) {b : Bool} {x : A}
    (hx : x ∈ coordSet A b) : x ^ r ∈ coordSet A b := by
  cases b
  · rw [show x = 0 from hx, zero_pow (by omega)]
    rfl
  · trivial

theorem normal_subgroupOf_of_commutator_mem {G : Type*} [Group G] {K H : Subgroup G} (hKH : K ≤ H)
    (h : ∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ ∈ K) : (K.subgroupOf H).Normal :=
  (normal_subgroupOf_iff_le_normalizer hKH).2 (le_normalizer_of_commutator_le le_rfl
    (by rw [commutator_le]; exact fun x hx y hy => h x hx y (hKH hy)))

theorem isElementaryAbelian_quotient_of_sq_comm {G : Type*} [Group G] {K H : Subgroup G}
    [(K.subgroupOf H).Normal] (h : ∀ x ∈ H, ∀ y ∈ H, x * x ∈ K ∧ ⁅x, y⁆ ∈ K) :
    IsElementaryAbelian 2 (H ⧸ K.subgroupOf H) where
  is_comm := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have e : (((x * y)⁻¹ * (y * x) : H) : G) = ⁅(y : G)⁻¹, (x : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv]
      group
    rw [e]
    exact (h _ (inv_mem y.2) _ (inv_mem x.2)).2⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, Subgroup.coe_pow, sq]
    exact (h x x.2 x x.2).1

theorem sq_comm_mem_map {G G' : Type*} [Group G] [Group G'] {K H : Subgroup G} (f : G →* G')
    (h : ∀ x ∈ H, ∀ y ∈ H, x * x ∈ K ∧ ⁅x, y⁆ ∈ K) :
    ∀ x ∈ H.map f, ∀ y ∈ H.map f, x * x ∈ K.map f ∧ ⁅x, y⁆ ∈ K.map f := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact ⟨⟨x * x, (h x hx y hy).1, map_mul f x x⟩, ⟨⁅x, y⁆, (h x hx y hy).2,
    map_commutatorElement f x y⟩⟩

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

include d in
theorem center_eq_bot_of_data : center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_center_iff] at hz
  have hzN : z ∈ normalizer (d.S : Set X) := mem_normalizer_iff.2 fun h => by
    rw [← hz h, mul_inv_cancel_right]
  rw [d.normalizer_S] at hzN
  obtain ⟨x, hx, j, hj, rfl⟩ := d.mem_B_iff.1 hzN
  have hw₀ : d.w₀ ∈ d.weyl := d.weylWord_mem_weyl 11
  have hzB : x * j ∈ d.conjB d.w₀ := by
    rw [conjB, mem_conj_inv_smul, hz d.w₀, mul_inv_cancel_right]
    exact hzN
  have hjB : j ∈ d.conjB d.w₀ := by
    rw [conjB, mem_conj_inv_smul]
    exact (le_sup_right : d.J ≤ d.B) (d.conj_mem_J hw₀ hj)
  have hxB : x ∈ d.conjB d.w₀ := by
    simpa using mul_mem hzB (inv_mem hjB)
  have hx1 : x = 1 := by
    have h := mem_inf.2 ⟨hxB, hx⟩
    rwa [d.conjB_w₀_inf_S_eq_bot, mem_bot] at h
  subst hx1
  rw [one_mul] at hz ⊢
  obtain ⟨p, rfl⟩ := hj
  have h1 := d.torus_x₁ p 1
  rw [← hz (d.x₁ 1), mul_inv_cancel_right] at h1
  have h2 := d.torus_x₂ p 1
  rw [← hz (d.x₂ 1), mul_inv_cancel_right] at h2
  have hp2 : p.2 = 1 := Units.ext (by simpa using d.x₁_injective h1.symm)
  have hp1 : p.1 = 1 := Units.ext (by simpa using d.x₂_injective h2.symm)
  rw [show p = 1 from Prod.ext hp1 hp2, map_one]
  exact one_mem _

include d in
theorem mulAutConj_injective : Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgc : g ∈ center X := mem_center_iff.2 fun h => by
    have := congrArg (fun α : MulAut X => α h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc h * g = g * h * g⁻¹ * g := by rw [this]
      _ = g * h := by group
  rw [d.center_eq_bot_of_data, mem_bot] at hgc
  exact hgc

theorem orderOf_φ_eq_three_mul {f : ℕ} (hq : q = 2 ^ f) : orderOf d.φ = 3 * f := by
  have h := d.two_pow_orderOf_φ
  rw [show q ^ 3 = 2 ^ (3 * f) by rw [hq, ← pow_mul, mul_comm]] at h
  exact Nat.pow_right_injective le_rfl h

theorem zpowers_φ_inf_range_conj : zpowers d.φ ⊓ (MulAut.conj : X →* MulAut X).range = ⊥ := by
  have := d.finite
  rw [eq_bot_iff]
  rintro α ⟨hαφ, g, rfl⟩
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.2 hαφ : MulAut.conj g ∈ Submonoid.powers d.φ)
  rw [mem_bot, ← hn]
  exact d.φ_pow_eq_conj n g hn

theorem φ_pow_x₁ (k : ℕ) (a : d.Γ) : (d.φ ^ k) (d.x₁ a) = d.x₁ (a ^ 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, d.φ_x₁, ← pow_mul, ← pow_succ]

theorem φ_pow_x₂ (k : ℕ) (a : d.Γ₀) : (d.φ ^ k) (d.x₂ a) = d.x₂ (a ^ 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, d.φ_x₂, ← pow_mul, ← pow_succ]

theorem φ_pow_x₃ (k : ℕ) (a : d.Γ) : (d.φ ^ k) (d.x₃ a) = d.x₃ (a ^ 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, d.φ_x₃, ← pow_mul, ← pow_succ]

theorem φ_pow_x₄ (k : ℕ) (a : d.Γ) : (d.φ ^ k) (d.x₄ a) = d.x₄ (a ^ 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, d.φ_x₄, ← pow_mul, ← pow_succ]

theorem φ_pow_x₅ (k : ℕ) (a : d.Γ₀) : (d.φ ^ k) (d.x₅ a) = d.x₅ (a ^ 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, d.φ_x₅, ← pow_mul, ← pow_succ]

theorem φ_pow_x₆ (k : ℕ) (a : d.Γ₀) : (d.φ ^ k) (d.x₆ a) = d.x₆ (a ^ 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, d.φ_x₆, ← pow_mul, ← pow_succ]

@[expose] def powCo (r : ℕ) (a : d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀) :
    d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀ :=
  (a.1 ^ r, a.2.1 ^ r, a.2.2.1 ^ r, a.2.2.2.1 ^ r, a.2.2.2.2.1 ^ r, a.2.2.2.2.2 ^ r)

theorem φ_pow_nf (k : ℕ) (a : d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀) :
    (d.φ ^ k) (d.nf a) = d.nf (d.powCo (2 ^ k) a) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := a
  simp only [nf_apply, powCo, map_mul, d.φ_pow_x₁, d.φ_pow_x₂, d.φ_pow_x₃, d.φ_pow_x₄,
    d.φ_pow_x₅, d.φ_pow_x₆]

@[expose] def fixSet (A : Type*) [Monoid A] [Zero A] (b : Bool) (r : ℕ) : Set A :=
  coordSet A b ∩ {x | x ^ r = x}

@[expose] def fixBox (r : ℕ) (P : Fin 6 → Bool) : Set (d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀) :=
  fixSet d.Γ (P 0) r ×ˢ fixSet d.Γ₀ (P 1) r ×ˢ fixSet d.Γ (P 2) r ×ˢ fixSet d.Γ (P 3) r ×ˢ
    fixSet d.Γ₀ (P 4) r ×ˢ fixSet d.Γ₀ (P 5) r

theorem mem_fixBox_iff {r : ℕ} {P : Fin 6 → Bool} {a : d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀} :
    a ∈ d.fixBox r P ↔ a ∈ d.box P ∧ d.powCo r a = a := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := a
  simp only [fixBox, fixSet, box, powCo, Set.mem_prod, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Prod.mk.injEq]
  tauto

theorem powCo_mem_box {r : ℕ} (hr : 1 ≤ r) {P : Fin 6 → Bool}
    {a : d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀} (ha : a ∈ d.box P) : d.powCo r a ∈ d.box P := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := ha
  exact ⟨pow_mem_coordSet hr h₁, pow_mem_coordSet hr h₂, pow_mem_coordSet hr h₃,
    pow_mem_coordSet hr h₄, pow_mem_coordSet hr h₅, pow_mem_coordSet hr h₆⟩

theorem boxProd_inter_fixed (k : ℕ) (P : Fin 6 → Bool) :
    {g | g ∈ d.boxProd P ∧ (d.φ ^ k) g = g} = d.nf '' d.fixBox (2 ^ k) P := by
  ext g
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hfix⟩
    rw [d.φ_pow_nf] at hfix
    exact ⟨a, d.mem_fixBox_iff.2 ⟨ha, d.nf_injective hfix⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ha, hpow⟩ := d.mem_fixBox_iff.1 ha
    exact ⟨⟨a, ha, rfl⟩, by rw [d.φ_pow_nf, hpow]⟩

theorem pow_three_e_eq_iff {e : ℕ} (hq : q = 2 ^ (2 * e)) (x : d.Γ₀) :
    x ^ 2 ^ (3 * e) = x ↔ x ^ 2 ^ e = x := by
  have := Fintype.ofFinite d.Γ₀
  have hcard : Fintype.card d.Γ₀ = 2 ^ (2 * e) := by
    rw [← Nat.card_eq_fintype_card, d.card_Γ₀, hq]
  have hx : x ^ 2 ^ (2 * e) = x := by
    rw [← hcard, FiniteField.pow_card]
  rw [show 3 * e = 2 * e + e by ring, pow_add, pow_mul, hx]

theorem ncard_fixSet_Γ_sq {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) (b : Bool) :
    (fixSet d.Γ b (2 ^ (3 * e))).ncard ^ 2 = (coordSet d.Γ b).ncard := by
  cases b
  · have h : fixSet d.Γ false (2 ^ (3 * e)) = {0} := by
      ext x
      simp only [fixSet, coordSet, Bool.cond_false, Set.mem_inter_iff, Set.mem_singleton_iff,
        Set.mem_ofPred_eq]
      constructor
      · exact fun h => h.1
      · rintro rfl
        exact ⟨rfl, zero_pow (by positivity)⟩
    rw [h]
    simp [coordSet]
  · have hΓ : Nat.card d.Γ = (2 ^ (3 * e)) ^ 2 := by
      rw [d.card_Γ, hq, ← pow_mul, ← pow_mul]
      ring_nf
    have h := card_fixed_pow_two_pow (F := d.Γ) (by omega : 1 ≤ 3 * e) hΓ
    simp only [fixSet, coordSet, Bool.cond_true, Set.univ_inter]
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq, hΓ]
    change Nat.card {x : d.Γ // x ^ 2 ^ (3 * e) = x} ^ 2 = _
    rw [h]

theorem ncard_fixSet_Γ₀_sq {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) (b : Bool) :
    (fixSet d.Γ₀ b (2 ^ (3 * e))).ncard ^ 2 = (coordSet d.Γ₀ b).ncard := by
  cases b
  · have h : fixSet d.Γ₀ false (2 ^ (3 * e)) = {0} := by
      ext x
      simp only [fixSet, coordSet, Bool.cond_false, Set.mem_inter_iff, Set.mem_singleton_iff,
        Set.mem_ofPred_eq]
      constructor
      · exact fun h => h.1
      · rintro rfl
        exact ⟨rfl, zero_pow (by positivity)⟩
    rw [h]
    simp [coordSet]
  · have hΓ₀ : Nat.card d.Γ₀ = (2 ^ e) ^ 2 := by
      rw [d.card_Γ₀, hq, ← pow_mul, mul_comm]
    have h := card_fixed_pow_two_pow (F := d.Γ₀) he hΓ₀
    simp only [fixSet, coordSet, Bool.cond_true, Set.univ_inter]
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq, hΓ₀]
    change Nat.card {x : d.Γ₀ // x ^ 2 ^ (3 * e) = x} ^ 2 = _
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => d.pow_three_e_eq_iff hq x), h]

theorem ncard_fixBox_sq {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) (P : Fin 6 → Bool) :
    (d.fixBox (2 ^ (3 * e)) P).ncard ^ 2 = (d.box P).ncard := by
  simp only [fixBox, box, Set.ncard_prod, mul_pow, d.ncard_fixSet_Γ_sq he hq,
    d.ncard_fixSet_Γ₀_sq he hq]

@[expose] def rootChain : Fin 7 → Subgroup X :=
  ![⊥, d.V, d.Y, d.W, d.F, d.D, d.S]

@[expose] def rootChainPat : Fin 7 → Fin 6 → Bool :=
  ![fun _ => false, ![false, false, false, false, false, true],
    ![false, false, false, false, true, true], ![false, false, false, true, true, true],
    ![false, false, true, true, true, true], ![false, true, true, true, true, true],
    fun _ => true]

theorem nf_x₆ (a : d.Γ₀) : d.nf (0, 0, 0, 0, 0, a) = d.x₆ a := by
  simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, d.x₅_zero, one_mul]

theorem coe_rootChain (i : Fin 7) : (d.rootChain i : Set X) = d.boxProd (rootChainPat i) := by
  have key : ∀ (H : Subgroup X) (P : Fin 6 → Bool),
      (∀ g ∈ H, ∃ a ∈ d.box P, d.nf a = g) → (∀ j, P j = true → d.rootGroup j ≤ H) →
      (H : Set X) = d.boxProd P := fun H P h₁ h₂ => by
    ext g
    refine ⟨fun hg => h₁ g hg, ?_⟩
    rintro ⟨a, ha, rfl⟩
    exact d.sixProd_mem_of_mem_box h₂ ha
  fin_cases i
  · change ((⊥ : Subgroup X) : Set X) = d.boxProd (fun _ => false)
    rw [d.boxProd_false, coe_bot]
  · refine key _ _ (fun g hg => ?_) (fun j hj => ?_)
    · obtain ⟨a, rfl⟩ := hg
      exact ⟨(0, 0, 0, 0, 0, a), ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩, d.nf_x₆ a⟩
    · fin_cases j <;> (try exact absurd hj (by decide))
      exact le_rfl
  · refine key _ _ (fun g hg => ?_) (fun j hj => ?_)
    · obtain ⟨a₅, a₆, rfl⟩ := d.mem_Y_coords hg
      exact ⟨(0, 0, 0, 0, a₅, a₆), ⟨rfl, rfl, rfl, rfl, trivial, trivial⟩, rfl⟩
    · fin_cases j <;> (try exact absurd hj (by decide))
      exacts [d.U₅_le_Y, d.V_le_Y]
  · refine key _ _ (fun g hg => ?_) (fun j hj => ?_)
    · obtain ⟨a₄, a₅, a₆, rfl⟩ := d.mem_W_coords hg
      exact ⟨(0, 0, 0, a₄, a₅, a₆), ⟨rfl, rfl, rfl, trivial, trivial, trivial⟩, rfl⟩
    · fin_cases j <;> (try exact absurd hj (by decide))
      exacts [d.U₄_le_W, d.U₅_le_Y.trans d.Y_le_W, d.V_le_Y.trans d.Y_le_W]
  · refine key _ _ (fun g hg => ?_) (fun j hj => ?_)
    · obtain ⟨a₃, a₄, a₅, a₆, rfl⟩ := d.mem_F_coords hg
      exact ⟨(0, 0, a₃, a₄, a₅, a₆), ⟨rfl, rfl, trivial, trivial, trivial, trivial⟩, rfl⟩
    · fin_cases j <;> (try exact absurd hj (by decide))
      exacts [d.U₃_le_F, d.U₄_le_W.trans d.W_le_F, d.U₅_le_Y.trans (d.Y_le_W.trans d.W_le_F),
        d.V_le_Y.trans (d.Y_le_W.trans d.W_le_F)]
  · refine key _ _ (fun g hg => ?_) (fun j hj => ?_)
    · obtain ⟨a₂, a₃, a₄, a₅, a₆, rfl⟩ := d.mem_D_coords hg
      exact ⟨(0, a₂, a₃, a₄, a₅, a₆), ⟨rfl, trivial, trivial, trivial, trivial, trivial⟩, rfl⟩
    · fin_cases j <;> (try exact absurd hj (by decide))
      exacts [d.U₂_le_D, d.U₃_le_F.trans d.F_le_D, d.U₄_le_W.trans (d.W_le_F.trans d.F_le_D),
        d.U₅_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)),
        d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D))]
  · refine key _ _ (fun g hg => ?_) (fun j _ => d.rootGroup_le_S j)
    obtain ⟨a, rfl⟩ := d.mem_S.1 hg
    exact ⟨a, ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩, rfl⟩

theorem rootChain_le (i : Fin 6) : d.rootChain i.castSucc ≤ d.rootChain i.succ := by
  fin_cases i
  exacts [bot_le, d.V_le_Y, d.Y_le_W, d.W_le_F, d.F_le_D, d.D_le_S]

theorem rootChain_sq_comm (i : Fin 6) : ∀ x ∈ d.rootChain i.succ, ∀ y ∈ d.rootChain i.succ,
    x * x ∈ d.rootChain i.castSucc ∧ ⁅x, y⁆ ∈ d.rootChain i.castSucc := by
  have hW : ∀ x ∈ d.W, ∀ y ∈ d.W, x * x = 1 ∧ ⁅x, y⁆ = 1 := fun x hx y hy =>
    ⟨d.mul_self_eq_one_of_mem_W hx,
      commutatorElement_eq_one_iff_mul_comm.2 (d.mul_comm_of_mem_W hx hy)⟩
  fin_cases i
  · change ∀ x ∈ d.V, ∀ y ∈ d.V, x * x ∈ (⊥ : Subgroup X) ∧ ⁅x, y⁆ ∈ (⊥ : Subgroup X)
    intro x hx y hy
    obtain ⟨h1, h2⟩ := hW x (d.Y_le_W (d.V_le_Y hx)) y (d.Y_le_W (d.V_le_Y hy))
    rw [h1, h2]
    exact ⟨one_mem _, one_mem _⟩
  · change ∀ x ∈ d.Y, ∀ y ∈ d.Y, x * x ∈ d.V ∧ ⁅x, y⁆ ∈ d.V
    intro x hx y hy
    obtain ⟨h1, h2⟩ := hW x (d.Y_le_W hx) y (d.Y_le_W hy)
    rw [h1, h2]
    exact ⟨one_mem _, one_mem _⟩
  · change ∀ x ∈ d.W, ∀ y ∈ d.W, x * x ∈ d.Y ∧ ⁅x, y⁆ ∈ d.Y
    intro x hx y hy
    obtain ⟨h1, h2⟩ := hW x hx y hy
    rw [h1, h2]
    exact ⟨one_mem _, one_mem _⟩
  · change ∀ x ∈ d.F, ∀ y ∈ d.F, x * x ∈ d.W ∧ ⁅x, y⁆ ∈ d.W
    exact fun x hx y hy => ⟨d.mul_self_mem_W_of_mem_F hx,
      d.Y_le_W (d.V_le_Y (d.commutator_F_F (commutator_mem_commutator hx hy)))⟩
  · change ∀ x ∈ d.D, ∀ y ∈ d.D, x * x ∈ d.F ∧ ⁅x, y⁆ ∈ d.F
    intro x hx y hy
    refine ⟨?_, d.W_le_F (d.Y_le_W (d.V_le_Y
      (d.commutator_D_D (commutator_mem_commutator hx hy))))⟩
    obtain ⟨b, n, hn, rfl⟩ := d.mem_D_iff.1 hx
    rw [mul_mul_self_eq_commutatorElement (d.x₂_mul_self b)]
    exact mul_mem (d.W_le_F (d.Y_le_W (d.V_le_Y (d.commutator_D_D
      (commutator_mem_commutator (d.x₂_mem_D b) (d.F_le_D hn)))))) (d.W_le_F
      (d.mul_self_mem_W_of_mem_F hn))
  · change ∀ x ∈ d.S, ∀ y ∈ d.S, x * x ∈ d.D ∧ ⁅x, y⁆ ∈ d.D
    intro x hx y hy
    refine ⟨?_, d.F_le_D (d.commutator_S_S (commutator_mem_commutator hx hy))⟩
    obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hx
    rw [mul_mul_self_eq_commutatorElement (d.x₁_mul_self a)]
    exact mul_mem (d.F_le_D (d.commutator_S_D (commutator_mem_commutator
      (d.U₁_le_S (d.x₁_mem_U₁ a)) hn))) (mul_mem hn hn)

theorem φ_pow_mem_rootChain (k : ℕ) (i : Fin 7) {g : X} (hg : g ∈ d.rootChain i) :
    (d.φ ^ k) g ∈ d.rootChain i := by
  rw [← SetLike.mem_coe, d.coe_rootChain] at hg ⊢
  obtain ⟨a, ha, rfl⟩ := hg
  rw [d.φ_pow_nf]
  exact ⟨_, d.powCo_mem_box (Nat.one_le_two_pow) ha, rfl⟩

theorem card_rootChain_inf_fixed_sq {e : ℕ} (he : 1 ≤ e) (hq : q = 2 ^ (2 * e)) (i : Fin 7) :
    Nat.card ↥(d.rootChain i ⊓ (d.φ ^ (3 * e)).toMonoidHom.eqLocus (MonoidHom.id X)) ^ 2 =
      Nat.card (d.rootChain i) := by
  have hset : ((d.rootChain i ⊓ (d.φ ^ (3 * e)).toMonoidHom.eqLocus (MonoidHom.id X) :
      Subgroup X) : Set X) =
      {g | g ∈ d.boxProd (rootChainPat i) ∧ (d.φ ^ (3 * e)) g = g} := by
    ext g
    rw [coe_inf, Set.mem_inter_iff, d.coe_rootChain]
    rfl
  have h1 : Nat.card ↥(d.rootChain i ⊓ (d.φ ^ (3 * e)).toMonoidHom.eqLocus (MonoidHom.id X)) =
      (((d.rootChain i ⊓ (d.φ ^ (3 * e)).toMonoidHom.eqLocus (MonoidHom.id X) : Subgroup X) :
        Set X)).ncard := Nat.card_coe_set_eq _
  have h2 : Nat.card ↥(d.rootChain i) = ((d.rootChain i : Subgroup X) : Set X).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, h2, hset, d.boxProd_inter_fixed,
    Set.InjOn.ncard_image (d.normal_form.injOn.mono (Set.subset_univ _)),
    d.ncard_fixBox_sq he hq, d.coe_rootChain, d.ncard_boxProd, d.ncard_box]

include d in
theorem map_mulAutConj_inf_centralizer (H : Subgroup X) (α : MulAut X) :
    H.map (MulAut.conj : X →* MulAut X) ⊓ centralizer {α} =
      (H ⊓ α.toMonoidHom.eqLocus (MonoidHom.id X)).map (MulAut.conj : X →* MulAut X) := by
  ext β
  rw [mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, hc⟩
    refine ⟨g, ⟨hg, ?_⟩, rfl⟩
    apply d.mulAutConj_injective
    change MulAut.conj (α g) = MulAut.conj g
    rw [← mulAut_mul_conj_mul_inv, ← hc, mul_inv_cancel_right]
  · rintro ⟨g, ⟨hg, hfix⟩, rfl⟩
    refine ⟨⟨g, hg, rfl⟩, ?_⟩
    change α g = g at hfix
    have h := mulAut_mul_conj_mul_inv α g
    rw [hfix] at h
    calc MulAut.conj g * α = α * MulAut.conj g * α⁻¹ * α := by rw [h]
      _ = α * MulAut.conj g := by group

theorem yamada_3_13_1 {f : ℕ} (hf : Even f) (hq : q = 2 ^ f) :
    orderOf (d.φ ^ (3 * f / 2)) = 2 ∧
      d.φ ^ (3 * f / 2) ∉ (MulAut.conj : X →* MulAut X).range ∧
      {β : MulAut X | (∃ s ∈ d.S, β = d.φ ^ (3 * f / 2) * MulAut.conj s) ∧ orderOf β = 2} =
        {β | ∃ s ∈ d.S, β = (MulAut.conj s)⁻¹ * d.φ ^ (3 * f / 2) * MulAut.conj s} ∧
      Nat.card ↥(d.S ⊓ (d.φ ^ (3 * f / 2)).toMonoidHom.eqLocus (MonoidHom.id X)) = q ^ 6 := by
  classical
  have := d.finite
  obtain ⟨e, rfl⟩ := hf
  have he : 1 ≤ e := by
    have h2 := d.two_le_q
    by_contra h0
    rw [hq, show e = 0 by omega] at h2
    norm_num at h2
  have h3 : 3 * (e + e) / 2 = 3 * e := by omega
  have hq' : q = 2 ^ (2 * e) := by rw [hq, two_mul]
  rw [h3]
  set a := d.φ ^ (3 * e) with ha
  have hord : orderOf a = 2 := by
    rw [ha, orderOf_pow_of_dvd (by omega) (by rw [d.orderOf_φ_eq_three_mul hq]; exact ⟨2, by ring⟩),
      d.orderOf_φ_eq_three_mul hq, show 3 * (e + e) = 3 * e * 2 by ring,
      Nat.mul_div_cancel_left _ (by omega)]
  have hinn : a ∉ (MulAut.conj : X →* MulAut X).range := by
    rintro ⟨g, hg⟩
    have h1 := d.φ_pow_eq_conj (3 * e) g hg.symm
    rw [← ha] at h1
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  set V : Fin 7 → Subgroup (MulAut X) := fun i => (d.rootChain i).map MulAut.conj with hV
  have hV0 : V 0 = ⊥ := Subgroup.map_bot _
  have hVle : ∀ i : Fin 6, V i.castSucc ≤ V i.succ := fun i => map_mono (d.rootChain_le i)
  have haV : ∀ i, a ∈ normalizer (V i : Set (MulAut X)) := fun i =>
    mem_normalizer_fintype fun _ ⟨g, hg, hn⟩ => by
      rw [← hn]
      exact ⟨a g, d.φ_pow_mem_rootChain _ i hg, (mulAut_mul_conj_mul_inv a g).symm⟩
  have : ∀ i : Fin 6, ((V i.castSucc).subgroupOf (V i.succ)).Normal := fun i =>
    normal_subgroupOf_of_commutator_mem (hVle i) fun x hx y hy =>
      (sq_comm_mem_map MulAut.conj (d.rootChain_sq_comm i) x hx y hy).2
  have : ∀ i : Fin 6, IsElementaryAbelian 2 (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ)) :=
    fun i => isElementaryAbelian_quotient_of_sq_comm
      (sq_comm_mem_map MulAut.conj (d.rootChain_sq_comm i))
  have hcard : ∀ i : Fin 6,
      Nat.card (V i.succ ⊓ centralizer {a} : Subgroup (MulAut X)) ^ 2 = Nat.card (V i.succ) := by
    intro i
    rw [hV, d.map_mulAutConj_inf_centralizer, card_map_of_injective d.mulAutConj_injective,
      card_map_of_injective d.mulAutConj_injective, d.card_rootChain_inf_fixed_sq he hq']
  have hser := CFSG.LocalAnalysis.EvenBN.Common.involution_coset_eq_conj_orbit_of_card_sq
    (W := d.S.map MulAut.conj) hord V hV0 rfl hVle haV hcard
  refine ⟨hord, hinn, ?_, ?_⟩
  · ext β
    have hβ := Set.ext_iff.1 hser β
    simp only [Set.mem_ofPred_eq, mem_map] at hβ ⊢
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hβ2⟩
      obtain ⟨_, ⟨t, ht, rfl⟩, he'⟩ := hβ.1 ⟨⟨_, ⟨s, hs, rfl⟩, rfl⟩, hβ2⟩
      exact ⟨t, ht, he'⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨⟨_, ⟨s, hs, rfl⟩, he'⟩, hβ2⟩ := hβ.2 ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨⟨s, hs, he'⟩, hβ2⟩
  · have h := d.card_rootChain_inf_fixed_sq he hq' (Fin.last 6)
    change Nat.card ↥(d.S ⊓ a.toMonoidHom.eqLocus (MonoidHom.id X)) ^ 2 = Nat.card d.S at h
    rw [d.card_S, show q ^ 12 = (q ^ 6) ^ 2 by ring] at h
    exact Nat.pow_left_injective (by norm_num) h

end TrialityD4Data

section Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem lieModel_fixedSubgroup_outer_involution
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    LieModel ↥(fixedSubgroup β) .trialityD4 0 2 (f / 2) := by
  have hK' : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK'
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨⟨e, he⟩, δ, hδ, -, ψ, hψ, -⟩ :=
    even_triality_outer_involutions_canonical_field hf K hK σ hσ β hβ2 hβo
  have he1 : 1 ≤ e := by omega
  have hK6 : Nat.card K = 2 ^ (3 * e * 2) := by rw [hK', he]; ring_nf
  have hσ' : ∀ c, σ c = c ^ 2 ^ (e * 2) := fun c => by rw [hσ, he]; ring_nf
  have hδ' : ∀ c, δ c = c ^ 2 ^ (3 * e) := fun c => by
    rw [hδ, show 3 * f / 2 = 3 * e by omega]
  obtain ⟨-, -, hk, hres, -, hJC, hfixJ, -, -, -⟩ :=
    RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      Nat.prime_two he1 (le_refl 2) (by norm_num : Nat.Coprime 2 3) K hK6 σ hσ' δ hδ'
  have hc : MulAut.congr ψ β = fieldActor σ δ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr ψ β = ψ * β * ψ⁻¹).trans hψ
  have hF : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) =
      (trialityFieldImage σ δ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    change _ = (trialityFieldImage σ δ).comap
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
    rw [← hfixJ, Subgroup.comap_map_eq_self_of_injective
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective]
    rfl
  have hk' : Nat.card (fixSubfield δ) = (2 ^ e) ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ) c = c ^ ((2 ^ e) ^ 2) :=
    fun c => Subtype.ext (by rw [hres c, hσ', SubmonoidClass.coe_pow, ← pow_mul, mul_comm])
  let e₁ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥(trialityFieldImage σ δ) :=
    (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
  have hFc : fixedSubgroup (MulAut.congr ψ β) =
      (trialityFieldImage σ δ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [hc, hF]
  have hL := RankThree.PartOne.Sec66T.lieModel_graphFixedRootGroup_trialityD4 he1 hk'
    (fixSubfieldRestrict σ δ) (Or.inr hσ₀)
  rw [show f / 2 = e by omega]
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    ((((ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv ψ β).trans
      (MulEquiv.subgroupCongr hFc)).trans (Subgroup.subgroupOfEquivOfLe hJC)).trans
      e₁.symm).symm hL

end Models

end CFSG.LocalAnalysis.EvenBN.TrialityD4
