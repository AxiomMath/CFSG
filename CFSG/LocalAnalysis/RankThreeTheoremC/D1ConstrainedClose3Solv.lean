module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem isSolvable_mulAut_of_card_one_or_nine {V : Type*} [Group V] [Finite V]
    (hcomm : ∀ a b : V, a * b = b * a) (hpow : ∀ a : V, a ^ 3 = 1)
    (hcard : Nat.card V = 1 ∨ Nat.card V = 3 ^ 2) : Group.IsSolvable (MulAut V) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hcard with h1 | h9
  · have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp h1).1
    have hsub : Subsingleton (MulAut V) :=
      ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    exact Group.isSolvable_of_isSolvable_injective
      (f := (1 : MulAut V →* Unit)) (Function.injective_of_subsingleton _)
  · obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow h9
    have hGL : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable
        (ZMod 3) (Or.inr (by rw [Nat.card_zmod]))
    exact Group.isSolvable_of_isSolvable_injective
      (f := (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom)
      (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective

theorem isSolvable_of_critical_three {X : Type*} [Group X] [Finite X] (Q : Subgroup X) [Q.Normal]
    (hQ : IsPGroup 3 Q) (hQc : Subgroup.centralizer (Q : Set X) ≤ Q)
    (C : Subgroup Q) (hC : C.Characteristic)
    (hfrat : (frattini C).map C.subtype ≤ (Subgroup.center C).map C.subtype)
    (hcent : Subgroup.centralizer (C : Set Q) = (Subgroup.center C).map C.subtype)
    (hcyc : IsCyclic (Subgroup.center C))
    (hrank : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → Open.pRank 3 N ≤ 2) :
    Group.IsSolvable X := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hCxn : (C.map Q.subtype).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact top_unique ((Subgroup.normalizer_eq_top Q).symm.le.trans
      (normalizer_le_normalizer_characteristic C hC))
  have hZx := map_map_center_eq_inf_centralizer C
  have hZxn : (((Subgroup.center C).map C.subtype).map Q.subtype).Normal := by
    rw [hZx]
    infer_instance
  have hZC : ((Subgroup.center C).map C.subtype).map Q.subtype ≤ C.map Q.subtype :=
    hZx.le.trans inf_le_left
  have hCQ : C.map Q.subtype ≤ Q := Subgroup.map_subtype_le C
  have hZp : IsPGroup 3 (((Subgroup.center C).map C.subtype).map Q.subtype) :=
    hQ.to_le (hZC.trans hCQ)
  have hZcyc : IsCyclic (((Subgroup.center C).map C.subtype).map Q.subtype) :=
    (((Subgroup.center C).equivMapOfInjective C.subtype C.subtype_injective).trans
      (((Subgroup.center C).map C.subtype).equivMapOfInjective Q.subtype
        Q.subtype_injective)).isCyclic.mp hcyc
  have hQZ : Q ⊓ Subgroup.centralizer ((C.map Q.subtype : Subgroup X) : Set X) ≤
      ((Subgroup.center C).map C.subtype).map Q.subtype := by
    rintro x ⟨hxQ, hxc⟩
    have hmem : (⟨x, hxQ⟩ : Q) ∈ Subgroup.centralizer (C : Set Q) :=
      Subgroup.mem_centralizer_iff.mpr fun c hc =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) _ ⟨c, hc, rfl⟩)
    rw [hcent] at hmem
    exact ⟨_, hmem, rfl⟩
  have hK := isPGroup_centralizer_of_selfCentralizing hp hQ hQc hZC (hZC.trans hCQ) hQZ
  have hfratC : frattini C ≤ Subgroup.center C :=
    (Subgroup.map_le_map_iff_of_injective C.subtype_injective).mp hfrat
  have hCp : IsPGroup 3 C := hQ.to_subgroup C
  have hcommC : commutator C ≤ Subgroup.center C :=
    (pGroup_commutator_le_frattini 3 hCp).trans hfratC
  have hpowC : ∀ c : C, c ^ 3 ∈ Subgroup.center C :=
    fun c => hfratC (pGroup_pow_mem_frattini 3 hCp c)
  have hCrank : Open.pRank 3 (⊤ : Subgroup C) ≤ 2 := by
    rw [← pRank_map_of_injective 3 hp (Q.subtype.comp C.subtype)
      (Q.subtype_injective.comp C.subtype_injective), ← Subgroup.map_map,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hrank _ hCxn (hQ.to_le hCQ)
  have hVcard := card_center_quotient_eq_one_or_sq hp2 hCp hcyc hcommC hpowC hCrank
  let : MulDistribMulAction X Q := MulDistribMulAction.compHom Q (MulAut.conjNormal (H := Q))
  let := characteristic_subgroup_mulDistribMulAction (acting := X) C
  let := characteristic_quotient_mulDistribMulAction (acting := X) (Subgroup.center C)
  have hρ : ∀ x ∈ (MulDistribMulAction.toMulAut X (C ⧸ Subgroup.center C)).ker,
      ∀ c ∈ C.map Q.subtype, c⁻¹ * (x * c * x⁻¹) ∈
        ((Subgroup.center C).map C.subtype).map Q.subtype := by
    rintro x hx _ ⟨q, hq, rfl⟩
    have hfix := congrArg (fun σ : MulAut (C ⧸ Subgroup.center C) =>
      σ (QuotientGroup.mk (⟨q, hq⟩ : C))) (MonoidHom.mem_ker.mp hx)
    change (QuotientGroup.mk (x • (⟨q, hq⟩ : C)) : C ⧸ Subgroup.center C) =
      QuotientGroup.mk ⟨q, hq⟩ at hfix
    exact ⟨_, ⟨_, QuotientGroup.eq.mp hfix.symm, rfl⟩, rfl⟩
  have hL := isPGroup_inf_centralizer_of_displacement hp hK hZp hρ
  let : IsMulCommutative (C ⧸ Subgroup.center C) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommC
  let : CommGroup (C ⧸ Subgroup.center C) := IsMulCommutative.instCommGroup
  have hVcomm : ∀ a b : C ⧸ Subgroup.center C, a * b = b * a := fun a b => mul_comm a b
  have hVpow : ∀ v : C ⧸ Subgroup.center C, v ^ 3 = 1 := by
    intro v
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center C) v
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hpowC c)
  have hVsolv : Group.IsSolvable (MulAut (C ⧸ Subgroup.center C)) :=
    isSolvable_mulAut_of_card_one_or_nine hVcomm hVpow hVcard
  set N : Subgroup X := Subgroup.centralizer
    ((((Subgroup.center C).map C.subtype).map Q.subtype : Subgroup X) : Set X) with hN
  have : N.Normal := Subgroup.normal_centralizer
  have hXN : Group.IsSolvable (X ⧸ N) := by
    have hc : commutator X ≤ N := by
      rw [commutator_eq_closure]
      refine (Subgroup.closure_le N).mpr ?_
      rintro _ ⟨x, y, rfl⟩
      exact commutatorElement_mem_centralizer_of_isCyclic hZcyc x y
    let : IsMulCommutative (X ⧸ N) := Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc
    let : CommGroup (X ⧸ N) := IsMulCommutative.instCommGroup
    infer_instance
  set ρ : X →* MulAut (C ⧸ Subgroup.center C) :=
    MulDistribMulAction.toMulAut X (C ⧸ Subgroup.center C) with hρdef
  have hLsolv : Group.IsSolvable ↥(ρ.ker ⊓ N) := by
    have : Group.IsNilpotent ↥(ρ.ker ⊓ N) := hL.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (ρ.ker ⊓ N).subtype (ρ.prod (QuotientGroup.mk' N))
    (by rw [Subgroup.range_subtype, MonoidHom.ker_prod, QuotientGroup.ker_mk'])

theorem isSolvable_primeCore_quotient_three {G : Type} [Group G] [Finite G] (P : Sylow 3 G)
    {M H : Subgroup G} (hPM : (P : Subgroup G) ≤ M) (hWM : GLBWeakCore 3 (P : Subgroup G) ≤ M)
    (hrank : 3 ≤ Open.pRank 3 (H ⊓ M)) (hescape : ¬ H ≤ M)
    (hcon : HasPrimeConstraint (G := H) 3) :
    Group.IsSolvable (H ⧸ primeComplementCore (G := H) 3) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : ((GLBPrimeCore 3 H).subgroupOf H).Normal := glbPrimeCore_normal 3 H
  obtain ⟨Q, hQn, hQp, hQc⟩ := exists_selfCentralizing_of_hasPrimeConstraint H hcon
  have : Q.Normal := hQn
  obtain ⟨C, hC, hfrat, -, hcent, hcyc, -⟩ :=
    escaping_primeCore_quotient_normal_pGroup_has_cyclic_critical_quotient 3 hp (by norm_num) P
      hPM hWM hrank hescape Q hQp
  have hX : Group.IsSolvable (H ⧸ (GLBPrimeCore 3 H).subgroupOf H) :=
    isSolvable_of_critical_three Q hQp hQc C hC hfrat hcent hcyc fun N _ hNp =>
      escaping_rank_three_primeCore_quotient_normal_primeSubgroup_rank_le_two 3 hp P hPM hWM hrank
        hescape N hNp
  let e : (H ⧸ (GLBPrimeCore 3 H).subgroupOf H) ≃* (H ⧸ primeComplementCore (G := H) 3) :=
    QuotientGroup.quotientMulEquivOfEq (glbPrimeCore_subgroupOf 3 H)
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

end CFSG.LocalAnalysis.RankThreeTheoremC
