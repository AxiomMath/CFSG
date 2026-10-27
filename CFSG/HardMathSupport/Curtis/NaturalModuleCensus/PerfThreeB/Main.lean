module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB.Flag
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeLinear
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB

open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.HardMathSupport.Curtis.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem nonempty_statedSp_mulEquiv_zmod_two' {K : Type} [Field K] [Finite K] (r : ℕ)
    (hK : Nat.card K = 2) : Nonempty (CFSG.Assembly.LowTwoRank.StatedSp r K ≃* CFSG.Assembly.LowTwoRank.StatedSp r (ZMod 2)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let e : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two h
  exact ⟨(MulEquiv.ofBijective (CFSG.ClassicalInvolution.Q3.Q3Z.spMap (n := r) e.toRingHom)
    ⟨CFSG.ClassicalInvolution.Q3.Q3Z.spMap_injective _,
      CFSG.ClassicalInvolution.Q3.Q3Z.spMap_surjective e⟩).symm⟩

theorem isClassicalOrG2Index_of_idxB {i : TauCeti.LieTypeIndex} (h : IdxB i) :
    IsClassicalOrG2Index i := by
  cases i <;> first | exact h | exact h.elim

section Void


theorem fixPerfThreeVoid_b (hGA : CFSG.Open.GriessAllModelsStatement) :
    FixPerfThreeVoid (IsLieOf IdxB) := by
  intro Y _ _ L J u hyp hX
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  have hidx2 := isClassicalOrG2IndexTwo_of_fixPerfThreeHyp hyp ⟨d, hv⟩
    (isClassicalOrG2Index_of_idxB hd) e
  have hq : CFSG.Open.IsQuasisimple ↥L := hyp.parab.comp.2.2
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  have hZ : Nat.card (Subgroup.center ↥L) = 1 := by
    obtain ⟨hd', hA, h2A⟩ := ToralCensus.rest_index (P := IdxB) (Or.inl rfl) hd
    exact ToralCensus.card_center_eq_one_of_index hGA ⟨d, hv⟩ hd' hA h2A e hyp.parab.odd
  have hZbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  cases d
  case B r q =>
    have hp2 : q.p = 2 := hd
    have hcard : q.card = 2 := hidx2
    have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hv
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvalid.1
    have hr : 3 ≤ r := by
      have h1 := hrange.1
      have h2 := hrange.2
      by_contra hlt
      have : r = 2 := by omega
      exact h2 ⟨this, hcard⟩
    have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp2 hr e
    rw [hp2] at hmodel
    obtain ⟨-, K, hK, hKfin, hcardK, ⟨e'⟩⟩ := hmodel
    have hcardK2 : Nat.card K = 2 := by
      rw [hcardK]
      have h2 := hcard
      rw [TauCeti.PrimePower.card_def, hp2] at h2
      exact h2
    have hf1 : 1 ≤ q.exponent := q.exponent_pos
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1
        hcardK
    have : NeZero r := ⟨by omega⟩
    have hout : ¬ 3 ∣ Nat.card (Outer ↥L) := by
      intro h3
      have h3' := h3.trans (card_outer_dvd_card_outer_centerQuotient ↥L)
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
        at h3'
      have hOutK := (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
        Nat.prime_two (f := 1) le_rfl hr (K := K) (by rw [hcardK2]; norm_num)).1
      have h1 : Nat.card (Outer (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp r K))) ∣ 1 := by simpa using hOutK
      have := Nat.dvd_one.mp (h3'.trans h1)
      omega
    have hu := mem_sup_centralizer_of_not_dvd_card_outer (p := 3) (k := 1) Nat.prime_three hout
      hyp.norm (by simpa using hyp.pow)
    obtain ⟨l, hl3, hlfix⟩ := exists_decomp_of_mem_sup_centralizer hu hyp.pow hyp.fix
    rw [hZbot, Subgroup.mem_bot] at hl3
    have hbij := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_symplectic_semilinear_normal_form
      (r := r) (K := K) hf1 hcardK).1
    let π : CFSG.Assembly.LowTwoRank.StatedSp r K ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp r K) := MulEquiv.ofBijective _ hbij
    obtain ⟨ψ⟩ := nonempty_statedSp_mulEquiv_zmod_two' (K := K) r hcardK2
    let φ0 : (↥L ⧸ Subgroup.center ↥L) ≃* CFSG.Assembly.LowTwoRank.StatedSp r (ZMod 2) := (e'.trans π.symm).trans ψ
    let ψ0 : ↥L →* CFSG.Assembly.LowTwoRank.StatedSp r (ZMod 2) :=
      φ0.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    have hinj : Function.Injective ψ0 := by
      refine (injective_iff_map_eq_one _).2 fun x hx => ?_
      have h1 : QuotientGroup.mk' (Subgroup.center ↥L) x = 1 := by
        apply φ0.injective
        simpa [ψ0] using hx
      have := (QuotientGroup.eq_one_iff _).1 h1
      rwa [hZbot, Subgroup.mem_bot] at this
    have hsurj : Function.Surjective ψ0 :=
      φ0.surjective.comp (QuotientGroup.mk'_surjective _)
    let φ : ↥L ≃* CFSG.Assembly.LowTwoRank.StatedSp r (ZMod 2) := MulEquiv.ofBijective ψ0 ⟨hinj, hsurj⟩
    have hker : φ.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 φ.injective
    obtain ⟨⟨T, hNT, -⟩, -⟩ := exists_sylow_normalizer_map_of_central_quotient φ.toMonoidHom
      φ.surjective (by rw [hker]; exact bot_le) (by rw [hker]; simp)
      (exists_sylow_normalizer_subgroupOf_of_compParab hyp.parab)
      (coprime_card_of_perf_subgroupOf hyp.perf)
    refine false_of_sylow_normalizer_le_centralizer (J := (J.subgroupOf L).map φ.toMonoidHom)
      ?_ T hNT (v := φ l) ?_ ?_
    · intro htop
      have := congrArg (Subgroup.comap φ.toMonoidHom) htop
      rw [Subgroup.comap_map_eq_self_of_injective φ.injective, Subgroup.comap_top,
        Subgroup.subgroupOf_eq_top] at this
      exact hyp.parab.ne_top (le_antisymm hyp.parab.parab.1 this)
    · rw [← map_pow, hl3, map_one]
    · intro g hg
      obtain ⟨g0, rfl⟩ := φ.surjective g
      refine ⟨g0, hlfix g0 ?_, rfl⟩
      apply φ.injective
      rw [map_mul, map_mul]
      exact hg
  all_goals exact hd.elim

end Void

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB
