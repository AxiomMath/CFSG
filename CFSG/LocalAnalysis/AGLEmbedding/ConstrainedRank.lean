module

public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRankAux
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRankForm

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem pRank_top_le_three_of_critical {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : Subgroup X) [Q.Normal] (hQ : IsPGroup p Q)
    (hQc : Subgroup.centralizer (Q : Set X) ≤ Q)
    (hrank : ∀ N : Subgroup X, N.Normal → IsPGroup p N → pRank p N ≤ 2)
    (C : Subgroup Q) (hC : C.Characteristic)
    (hfrat : (frattini C).map C.subtype ≤ (Subgroup.center C).map C.subtype)
    (hcent : Subgroup.centralizer (C : Set Q) = (Subgroup.center C).map C.subtype)
    (hcyc : IsCyclic (Subgroup.center C)) :
    pRank p (⊤ : Subgroup X) ≤ 3 := by
  have : Fact p.Prime := ⟨hp⟩
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
  have hZp : IsPGroup p (((Subgroup.center C).map C.subtype).map Q.subtype) :=
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
  have hCp : IsPGroup p C := hQ.to_subgroup C
  have hcommC : commutator C ≤ Subgroup.center C :=
    (pGroup_commutator_le_frattini p hCp).trans hfratC
  have hpowC : ∀ c : C, c ^ p ∈ Subgroup.center C :=
    fun c => hfratC (pGroup_pow_mem_frattini p hCp c)
  have hCrank : pRank p (⊤ : Subgroup C) ≤ 2 := by
    rw [← pRank_map_of_injective p hp (Q.subtype.comp C.subtype)
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
  obtain ⟨E, -, hE, hEcard⟩ := pRank_attained p hp (⊤ : Subgroup X)
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  let : IsMulCommutative (C ⧸ Subgroup.center C) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommC
  let : CommGroup (C ⧸ Subgroup.center C) := IsMulCommutative.instCommGroup
  let : MulDistribMulAction E (C ⧸ Subgroup.center C) :=
    MulDistribMulAction.compHom (C ⧸ Subgroup.center C) E.subtype
  have hVpow : ∀ v : C ⧸ Subgroup.center C, v ^ p = 1 := by
    intro v
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center C) v
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hpowC c)
  obtain ⟨k, hkindex, hkfix⟩ := exists_kernel_of_card_eq_one_or_sq hEp hVcard hVpow
  have hE₀ : k.map E.subtype ≤ (MulDistribMulAction.toMulAut X (C ⧸ Subgroup.center C)).ker := by
    rintro _ ⟨e, he, rfl⟩
    exact MonoidHom.mem_ker.mpr (MulEquiv.ext (hkfix e he))
  have hcommL : ∀ g : X, ∀ e ∈ k.map E.subtype, g * e * g⁻¹ * e⁻¹ ∈
      (MulDistribMulAction.toMulAut X (C ⧸ Subgroup.center C)).ker ⊓
        Subgroup.centralizer ((((Subgroup.center C).map C.subtype).map Q.subtype :
          Subgroup X) : Set X) := by
    intro g e he
    refine ⟨Subgroup.mul_mem _ ((MonoidHom.normal_ker _).conj_mem e (hE₀ he) g)
      (Subgroup.inv_mem _ (hE₀ he)), ?_⟩
    exact commutatorElement_mem_centralizer_of_isCyclic hZcyc g e
  have hSn := normal_sup_of_commutator_mem hcommL
  have hSp := IsPGroup.to_sup_of_normal_left hL ((hEp.to_subgroup k).map E.subtype)
  have hrankE := elementary_prime_index_subgroup_rank p hp hE _ hEcard k hkindex
  have hrankE₀ := (pRank_mono p hp (le_sup_right : k.map E.subtype ≤ _)).trans
    (hrank _ hSn hSp)
  omega

theorem exists_selfCentralizing_of_hasPrimeConstraint {G : Type*} [Group G] [Finite G] {p : ℕ}
    (H : Subgroup G)
    (hcon : HasPrimeConstraint (G := H) p) [((GLBPrimeCore p H).subgroupOf H).Normal] :
    ∃ Q : Subgroup (H ⧸ (GLBPrimeCore p H).subgroupOf H), Q.Normal ∧ IsPGroup p Q ∧
      Subgroup.centralizer (Q : Set (H ⧸ (GLBPrimeCore p H).subgroupOf H)) ≤ Q := by
  obtain ⟨N, hN, hNp, hNc⟩ := hcon
  let e : (H ⧸ (GLBPrimeCore p H).subgroupOf H) ≃* (H ⧸ primeComplementCore p) :=
    QuotientGroup.quotientMulEquivOfEq (glbPrimeCore_subgroupOf p H)
  refine ⟨N.comap e.toMonoidHom, hN.comap _, hNp.comap_of_injective _ e.injective, ?_⟩
  intro x hx
  apply hNc
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨y', rfl⟩ := e.surjective y
  have h := congrArg e ((Subgroup.mem_centralizer_iff.mp hx) y' hy)
  rwa [map_mul, map_mul] at h

theorem pRank_eq_pRank_top_primeCore_quotient {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (H : Subgroup G) [((GLBPrimeCore p H).subgroupOf H).Normal] :
    pRank p H = pRank p (⊤ : Subgroup (H ⧸ (GLBPrimeCore p H).subgroupOf H)) := by
  have h1 := pRank_map_of_injective p hp H.subtype H.subtype_injective ⊤
  have h2 := pRank_primeCore_quotient_map p hp H ⊤
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  exact h1.trans h2.symm

theorem pRank_le_three_of_escape_of_hasPrimeConstraint
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : Sylow p G) {M H : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (hrank : 3 ≤ pRank p (H ⊓ M)) (hescape : ¬ H ≤ M)
    (hcon : HasPrimeConstraint (G := H) p) :
    pRank p H ≤ 3 := by
  have : ((GLBPrimeCore p H).subgroupOf H).Normal := glbPrimeCore_normal p H
  obtain ⟨Q, hQn, hQp, hQc⟩ := exists_selfCentralizing_of_hasPrimeConstraint H hcon
  have : Q.Normal := hQn
  obtain ⟨C, hC, hfrat, -, hcent, hcyc, -⟩ :=
    escaping_primeCore_quotient_normal_pGroup_has_cyclic_critical_quotient p hp hp2 P hPM hWM
      hrank hescape Q hQp
  rw [pRank_eq_pRank_top_primeCore_quotient hp H]
  exact pRank_top_le_three_of_critical hp hp2 Q hQp hQc
    (fun N _ hNp => escaping_rank_three_primeCore_quotient_normal_primeSubgroup_rank_le_two p hp P
      hPM hWM hrank hescape N hNp) C hC hfrat hcent hcyc

theorem le_of_four_le_pRank_of_hasPrimeConstraint
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : Sylow p G) {M H : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (hrank : 4 ≤ pRank p (H ⊓ M))
    (hcon : HasPrimeConstraint (G := H) p) :
    H ≤ M := by
  by_contra hescape
  have hle := pRank_le_three_of_escape_of_hasPrimeConstraint hp hp2 P hPM hWM (by omega)
    hescape hcon
  have hmono := pRank_mono p hp (inf_le_left : H ⊓ M ≤ H)
  omega

end CFSG.AGLEmbedding
