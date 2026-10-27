module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRRee
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPMI
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPMarking
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.Sporadic.Schreier.TitsIso
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsCert
public import CFSG.LieType.Ree.ReeHolds
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

namespace Res

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP CFSG.LocalAnalysis.GLTheoremA.FQ
  CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions
    large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.HardMathSupport.Lang.Coordinator
open scoped commutatorElement

section Part1


theorem ree_fix_equiv {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Type} [Group S]
    (eS : S ≃* DerivedCentralQuotient (reeFixedGroup .F4 K reeF4Perm
        fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)))
    (f : MulAut S) (hord : orderOf f = p) (hnot : f ∉ inner S) :
    p ∣ 2 * a + 1 ∧ ∃ b : ℕ, (2 * b + 1) * p = 2 * a + 1 ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k F4.prime), Nat.card k = 2 ^ (2 * b + 1) ∧
        Nonempty (↥(FP.fixSub f) ≃* ↥(F4.reeGamma k b)) := by
  have hR : ReeTitsModel S .twistedF4 2 (2 * a + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl, K, inferInstance,
      inferInstance, hK, ⟨eS⟩⟩
  obtain ⟨-, -, -, -, -, -, hmain⟩ := large_Ree_model_field_outer_group_and_inner_involutions _ 2
    (2 * a + 1) hR
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K F4.prime := charP_of_card_eq_prime_pow (p := 2) (f := 2 * a + 1) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨⟨e⟩, -⟩ := hmain a K rfl hK ⟨eS⟩
  have : Fact p.Prime := ⟨hp⟩
  have hfp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  set α' : MulAut (F4.reeGamma K a) := MulAut.congr e f with hα'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hfp, map_one]
  have hα'inn : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (F4.reeGamma K a) :=
    fun h => hnot (((congr_mem_inner_iff e f).mp h))
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : F4.reeGammaFieldAut K a 1 = 1 := by rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp β hβord α'
    hα'p ⟨x, hxβ⟩
  obtain ⟨b, hbp, hbcard, hfix⟩ := largeRee_fixed_data_of_odd hK hp hp2 β hβord
  have hpn : p ∣ 2 * a + 1 := ⟨2 * b + 1, by rw [← hbp, mul_comm]⟩
  have e₂ : ↥(FP.fixSub α') ≃* ↥(FP.fixSub (F4.reeGammaFieldAut K a β)) :=
    (MulEquiv.subgroupCongr (congrArg FP.fixSub hg)).trans
      (fixSubEquivConj (MulAut.conj g) (F4.reeGammaFieldAut K a β)).symm
  have e₃ : ↥(FP.fixSub (F4.reeGammaFieldAut K a β)) ≃* ↥(F4.reeGamma (fixSubfield β) b) :=
    ((((F4.reeGammaFieldAut K a β).toMonoidHom.eqLocus (MonoidHom.id _)).equivMapOfInjective
      (F4.reeGamma K a).subtype (F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr hfix)).trans
      ((F4.reeGamma (fixSubfield β) b).equivMapOfInjective _
        (baseChangeGL_injective (τ := F4.tag) (fixSubfield β).subtype)).symm
  have : Finite (fixSubfield β) := Subtype.finite
  haveI : Fintype (fixSubfield β) := Fintype.ofFinite _
  haveI : CharP (fixSubfield β) F4.prime := charP_of_card_eq_prime_pow (p := 2) (f := 2 * b + 1) (by
    rw [← Nat.card_eq_fintype_card, hbcard])
  exact ⟨hpn, b, hbp, fixSubfield β, inferInstance, inferInstance, inferInstance, hbcard,
    ⟨((fixSubEquivCongr e f).trans e₂).trans e₃⟩⟩

end Part1

section Part2

theorem chevSimple_titsD :
    IsChevSimple 2 CFSG.Sporadic.Schreier.Tits.titsD := by
  let K := ZMod 2
  have hK : Nat.card K = 2 := Nat.card_zmod 2
  have hR : ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 (by simpa using hK)⟩
  obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hR
  obtain ⟨d, hd, ⟨f⟩⟩ := index_of_reeTits_two (Or.inr rfl) hR
  exact Or.inl ⟨TauCeti.CFSGIndex.lie d, by simpa [onLie] using hd, ⟨eT.symm.trans f⟩⟩

theorem datumCore_reeGamma_zero {k : Type} [Field k] [Finite k] [CharP k F4.prime] (hk : Nat.card k = 2) :
    DatumCore ↥(F4.reeGamma k 0) := by
  haveI : Fact (Nat.card k = 2) := ⟨hk⟩
  have hk' : Nat.card k = 2 ^ (2 * 0 + 1) := by simpa using hk
  have hΓ := ReeTag.reeGamma_eq_reeFixedGroup (t := ReeTag.F4) (K := k) (a := 0)
  let eΓ : ↥(F4.reeGamma k 0) ≃* ↥(reeFixed ReeTag.F4 k 0) :=
    (MulEquiv.subgroupCongr (hΓ.trans (reeFixedGroup_eq_map_reeFixed ReeTag.F4 k 0))).trans
      ((reeFixed ReeTag.F4 k 0).equivMapOfInjective _ Subtype.val_injective).symm
  obtain ⟨eC⟩ := nonempty_commutator_equiv eΓ
  let eE : ↥(commutator ↥(F4.reeGamma k 0)) ≃* CFSG.Sporadic.Schreier.Tits.titsD :=
    eC.trans CFSG.Sporadic.Schreier.Tits.titsDerivedIso
  have hcard : Nat.card CFSG.Sporadic.Schreier.Tits.titsD = 17971200 :=
    CFSG.Sporadic.Schreier.Tits.card_titsD
  haveI : Finite CFSG.Sporadic.Schreier.Tits.titsD :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hs : IsSimpleGroup CFSG.Sporadic.Schreier.Tits.titsD :=
    CFSG.Sporadic.Schreier.Tits.titsD_simple
  have hΓcard : Nat.card ↥(F4.reeGamma k 0) = 35942400 := by
    have := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      0 k hk').1
    rw [this]
    norm_num
  refine ⟨commutator ↥(F4.reeGamma k 0), eE.isSimpleGroup_congr.2 hs, ?_, ?_,
    Or.inr (by rw [hΓcard, Nat.card_congr eE.toEquiv, hcard]),
    Or.inl (chevSimple_of_equiv eE chevSimple_titsD)⟩
  · obtain ⟨a, b, hab⟩ := nonab_of_simple hs (by rw [hcard]; norm_num)
    exact ⟨eE.symm a, eE.symm b,
      fun hh => hab (eE.symm.injective (by rw [map_mul, map_mul]; exact hh))⟩
  · intro T hT
    rw [← hT, commutator_def]
    exact Subgroup.commutator_mono le_top le_top

end Part2


section Part3


variable {G : Type} [Group G] [Finite G]

theorem fieldOn_outer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {b : G}
    (hF : FieldOn p b L) :
    indAut p L b hF.1 ^ p = 1 ∧
      indAut p L b hF.1 ∉ (MulAut.conj : PSimple p L →* MulAut (PSimple p L)).range := by
  have h := canon_marking_and_labelAll_simple' (P' := fun _ => RawInnBody p)
    (fun lab hlab => canonRawInn' hp hp2 hlab) hF.2
  obtain ⟨-, lab, hlab, R, _, I, F, θ, -, -, ⟨hP, hRI⟩⟩ := Canonical.largeEvenMarking_exists h
  obtain ⟨-, f, hf, u, hu, hord, he⟩ := fieldOn_data hF.1 θ hP
  obtain ⟨hmul, hinv, hconj, hFI⟩ := hRI
  have hnotI : u * f * u⁻¹ ∉ I := not_mem_of_conj_field hmul hinv hu (hFI f hf hord)
  have hnotInn : u * f * u⁻¹ ∉ (MulAut.conj : R →* MulAut R).range :=
    fun ⟨r, hr⟩ => hnotI (hr ▸ hconj r)
  refine ⟨?_, fun hh => hnotInn (he ▸ (congr_mem_range_conj θ _).2 hh)⟩
  have hfp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  apply (MulAut.congr θ).injective
  rw [map_pow, he, conj_pow, hfp, mul_one, mul_inv_cancel, map_one]

theorem twF4Core_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : TwF4Core p := by
  intro G _ _ L b hF ⟨lab₀, hlab₀, htag₀, hn₀, hM₀⟩ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hβp, hβi⟩ := fieldOn_outer hp hp2 hF
  set β := indAut p L b hF.1 with hβ
  have hβ1 : β ≠ 1 := fun h => hβi ⟨1, by rw [h]; ext x; simp⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨t, r, n⟩ := lab₀
  dsimp only at htag₀ hn₀
  subst htag₀
  subst n
  have hL : LieModel (PSimple p L) .twistedF4 0 2 p := hM₀
  obtain ⟨-, hadm, a, hfa, K, _, _, hK, ⟨e0⟩⟩ := hL.reeTitsModel (by simp [reeTitsTags])
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0
      exact absurd hfa (by simpa using hp.ne_one)
    · exact h0
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, b₀, hb, k, _, _, _, hk, ⟨eF⟩⟩ := ree_fix_equiv ha hK' hp hp2 e0 β hβord hβi
  have hb0 : b₀ = 0 := by
    have h1 : (2 * b₀ + 1) * p = 1 * p := by rw [hb, hfa, one_mul]
    have := Nat.eq_of_mul_eq_mul_right hp.pos h1
    omega
  subst hb0
  have hk2 : Nat.card k = 2 := by simpa using hk
  have hC : DatumCore ↥(FP.fixSub β) := datumCore_of_equiv eF (datumCore_reeGamma_zero hk2)
  exact coreSub_of_subfield ⟨le_rfl, Subgroup.commutator_le_of_le le_rfl le_rfl,
    by rw [Subgroup.relIndex_self]; exact odd_one⟩ hC

end Part3

end Res

end FR

end CFSG.LocalAnalysis.GLTheoremA
