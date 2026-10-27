module

public import CFSG.LocalAnalysis.Mason73.Fusion43
public import CFSG.LocalAnalysis.Mason73.Model44
public import CFSG.LocalAnalysis.Mason73.Component44
public import CFSG.LocalAnalysis.Mason73.Pullback44
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup CFSG.ClassicalInvolution.QuaternionStructure
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem exists_two_le_derivedSeries_succ_eq (H : Type*) [Group H] [Finite H] :
    ∃ m, 2 ≤ m ∧ derivedSeries H (m + 1) = derivedSeries H m := by
  obtain ⟨k, -, hk⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := H)
  have hstab : ∀ j, derivedSeries H (k + j) = derivedSeries H k := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← add_assoc, derivedSeries_succ, ih, ← derivedSeries_succ, ← hk]
  refine ⟨k + 2, by omega, ?_⟩
  rw [show k + 2 + 1 = k + 3 by omega, hstab 3, hstab 2]

theorem commutator_map_subtype_derivedSeries_eq_top {C : Subgroup G} {m : ℕ}
    (hm : derivedSeries C (m + 1) = derivedSeries C m) :
    commutator ((derivedSeries C m).map C.subtype) = ⊤ := by
  have hY : ⁅(derivedSeries C m).map C.subtype, (derivedSeries C m).map C.subtype⁆ =
      (derivedSeries C m).map C.subtype := by
    rw [← map_subtype_derivedSeries_succ, hm]
  exact Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hY)

theorem map_subtype_derivedSeries_subgroupOf_normal (C : Subgroup G) (m : ℕ) :
    (((derivedSeries C m).map C.subtype).subgroupOf C).Normal := by
  have h : ((derivedSeries C m).map C.subtype).subgroupOf C = derivedSeries C m :=
    comap_map_eq_self_of_injective C.subtype_injective _
  rw [h]
  exact derivedSeries_normal C m

theorem zT_mem_Q1 (hn : 2 ≤ n) : zT (n := n) (by omega) ∈ Q1 (n := n) (by omega) := by
  rw [zT_eq_pow hn]
  exact pow_mem (subset_closure (by simp)) _

theorem lemma44 [IsSimpleGroup G] (hn : 3 ≤ n)
    {ι : L4Model n →* G} (hι : Function.Injective ι) (S : Sylow 2 G) (hS : ι.range = S)
    (hDD : ∀ (Y : Type) [Group Y] [Finite Y], commutator Y = ⊤ →
      CFSG.Open.classicalInvolutionOddCore Y = ⊥ →
      ∀ (P : Sylow 2 Y) (m : ℕ), 2 ≤ m →
        Nonempty ((P : Subgroup Y) ≃* DihedralGroup (2 ^ m) × DihedralGroup (2 ^ m)) →
        ∃ L₁ L₂ : Subgroup Y, L₁.Normal ∧ L₂.Normal ∧ L₁ ⊓ L₂ = ⊥ ∧ L₁ ⊔ L₂ = ⊤ ∧
          ∀ L ∈ ({L₁, L₂} : Set (Subgroup Y)), Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
            ∃ p k : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 5 ≤ p ^ k ∧
              Nonempty (L ≃* PSL(2, GaloisField p k))) :
    ∃ z : G, orderOf z = 2 ∧ ∃ J : Subgroup G, z ∈ J ∧
      CFSG.Open.IsSubnormal J (Subgroup.centralizer ({z} : Set G)) ∧
      ∃ P : Sylow 2 J,
        (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((P : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
        CFSG.Open.classicalInvolutionWitness J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι', hι', hrange, -, -, hu, -⟩ := exists_normalized_embedding hn hι S hS
  have hS' : ι'.range = S := hrange.trans hS
  clear hι hrange hS ι
  set z : G := ι' (zT (n := n) (by omega)) with hzdef
  have hz2 : orderOf z = 2 := by
    rw [hzdef, orderOf_injective ι' hι', orderOf_zT (by omega)]
  set C := centralizer ({z} : Set G) with hCdef
  obtain ⟨m, hm2, hmst⟩ := exists_two_le_derivedSeries_succ_eq C
  set Y : Subgroup G := (derivedSeries C m).map C.subtype with hYdef
  have hYC : Y ≤ C := map_subtype_le _
  have hYperf : commutator Y = ⊤ := commutator_map_subtype_derivedSeries_eq_top hmst
  have hT2Y : ∀ t ∈ T2T (n := n) (by omega), ι' t ∈ Y := fun t ht =>
    T2T_le_comap_derivedSeries hn hι' S hS' hu m ht
  let ιY : T2T (n := n) (by omega) →* Y :=
    (ι'.comp (T2T (n := n) (by omega)).subtype).codRestrict Y fun t => hT2Y t t.2
  have hιY : Function.Injective ιY := fun a b hab =>
    Subtype.ext (hι' (congrArg Subtype.val hab))
  let κ : T2T (n := n) (by omega) →* Y ⧸ CFSG.oddCore Y :=
    (QuotientGroup.mk' (CFSG.oddCore Y)).comp ιY
  have hT2 : IsPGroup 2 (T2T (n := n) (by omega)) :=
    (IsPGroup.of_card (card_L4Model (n := n) (by omega))).to_subgroup _
  have hκ : Function.Injective κ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ht
    have hdvd : orderOf (ιY t) ∣ Nat.card (CFSG.oddCore Y) := Subgroup.orderOf_dvd_natCard _ ht
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hT2 t
    rw [orderOf_injective ιY hιY, hk] at hdvd
    have hodd := (odd_natCard_oddCore Y).of_dvd_nat hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' hk0).2 even_two)
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    rw [mem_bot]
    exact hk
  have hzP : zT (n := n) (by omega) ∈ T2T (n := n) (by omega) :=
    Q1_le_T2T (by omega) (zT_mem_Q1 (by omega))
  let z' : T2T (n := n) (by omega) := ⟨zT (n := n) (by omega), hzP⟩
  let Q₁' : Subgroup (T2T (n := n) (by omega)) :=
    (Q1 (n := n) (by omega)).subgroupOf (T2T (n := n) (by omega))
  let Q₂' : Subgroup (T2T (n := n) (by omega)) :=
    (Q2 (n := n) (by omega)).subgroupOf (T2T (n := n) (by omega))
  have hsup' : Q₁' ⊔ Q₂' = ⊤ := by
    apply map_injective (T2T (n := n) (by omega)).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (Q1_le_T2T (by omega)),
      map_subgroupOf_eq_of_le (Q2_le_T2T (by omega)), ← MonoidHom.range_eq_map, range_subtype,
      T2T_eq_sup hn]
  have hinf' : Q₁' ⊓ Q₂' = zpowers z' := by
    apply map_injective (T2T (n := n) (by omega)).subtype_injective
    rw [map_inf_eq _ _ _ (T2T (n := n) (by omega)).subtype_injective,
      map_subgroupOf_eq_of_le (Q1_le_T2T (by omega)),
      map_subgroupOf_eq_of_le (Q2_le_T2T (by omega)), Q1_inf_Q2 (by omega),
      MonoidHom.map_zpowers]
    rfl
  have hcomm' : Q₂' ≤ centralizer (Q₁' : Set (T2T (n := n) (by omega))) := by
    intro b hb
    rw [mem_centralizer_iff]
    intro a ha
    exact Subtype.ext (mem_centralizer_iff.1 (Q2_le_centralizer_Q1 (by omega) hb) a ha)
  have hzX : κ z' ∈ center (Y ⧸ CFSG.oddCore Y) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore Y) g
    change QuotientGroup.mk' _ y * QuotientGroup.mk' _ (ιY z') =
      QuotientGroup.mk' _ (ιY z') * QuotientGroup.mk' _ y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hYC y.2))
  have hz2X : orderOf (κ z') = 2 := by
    rw [orderOf_injective κ hκ, Subgroup.orderOf_mk, orderOf_zT (by omega)]
  have hcommX : Q₂'.map κ ≤ centralizer ((Q₁'.map κ : Subgroup (Y ⧸ CFSG.oddCore Y)) :
      Set (Y ⧸ CFSG.oddCore Y)) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (hcomm' hb) a ha]
  have hinfX : Q₁'.map κ ⊓ Q₂'.map κ = zpowers (κ z') := by
    rw [← map_inf_eq _ _ _ hκ, hinf', MonoidHom.map_zpowers]
  obtain ⟨Qs, hQs⟩ := isSylowOf_T2T hn hι' S hS' hu hm2
  have hQsr : (Qs : Subgroup Y) = ιY.range := by
    apply map_injective Y.subtype_injective
    rw [hQs, ← MonoidHom.range_comp]
    have : Y.subtype.comp ιY = ι'.comp (T2T (n := n) (by omega)).subtype := rfl
    rw [this, MonoidHom.range_comp, range_subtype]
  let SX : Sylow 2 (Y ⧸ CFSG.oddCore Y) := Qs.mapSurjective (QuotientGroup.mk'_surjective _)
  have hSX : (SX : Subgroup (Y ⧸ CFSG.oddCore Y)) = Q₁'.map κ ⊔ Q₂'.map κ := by
    rw [Sylow.coe_mapSurjective, hQsr, ← MonoidHom.range_comp, ← Subgroup.map_sup, hsup',
      ← MonoidHom.range_eq_map]
  obtain ⟨eQ1⟩ := nonempty_Q1_mulEquiv (n := n) (by omega)
  obtain ⟨eQ2⟩ := nonempty_Q2_mulEquiv (n := n) (by omega)
  let e₁ : Q₁'.map κ ≃* QuaternionGroup (2 ^ (n - 1)) :=
    ((Q₁'.equivMapOfInjective κ hκ).symm.trans
      (subgroupOfEquivOfLe (Q1_le_T2T (n := n) (by omega)))).trans eQ1
  let e₂ : Q₂'.map κ ≃* QuaternionGroup (2 ^ (n - 1)) :=
    ((Q₂'.equivMapOfInjective κ hκ).symm.trans
      (subgroupOfEquivOfLe (Q2_le_T2T (n := n) (by omega)))).trans eQ2
  obtain ⟨K, hKn, hzK, hK⟩ := exists_classical_component_of_quaternion_central_product
    (commutator_quotient_eq_top hYperf) (oddCore_quotient_oddCore_eq_bot Y) hzX hz2X hcommX
    hinfX SX hSX (k := n - 1) (by omega) e₁ e₂ hDD
  haveI := hKn
  have hzJ : z ∈ preimageOddCore Y K := mem_preimageOddCore (y := ιY z') hzK
  have hsub : CFSG.Open.IsSubnormal (preimageOddCore Y K) C :=
    CFSG.Open.IsSubnormal.step (preimageOddCore_le Y K) (preimageOddCore_subgroupOf_normal Y K)
      (CFSG.Open.IsSubnormal.step hYC (map_subtype_derivedSeries_subgroupOf_normal C m)
        (CFSG.Open.IsSubnormal.refl C))
  rcases hK with ⟨F, hF, hFin, hchar, ⟨eK⟩⟩ | ⟨hq, hc, ⟨eK⟩⟩
  · obtain ⟨hw, P, hP⟩ := witness_preimageOddCore_of_sl2 Y K hchar eK
    exact ⟨z, hz2, preimageOddCore Y K, hzJ, hsub, P, hP, hw⟩
  · obtain ⟨hw, P, hP⟩ := witness_preimageOddCore_of_a7 Y K hq hc eK
    exact ⟨z, hz2, preimageOddCore Y K, hzJ, hsub, P, hP, hw⟩

end CFSG.LocalAnalysis.Mason73
