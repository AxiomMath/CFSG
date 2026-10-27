module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneBar
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

namespace IsPComponentIn

variable {K L : Subgroup G}

theorem isPerfect (hp : p.Prime) (hLK : IsPComponentIn p L K) : Group.IsPerfect ↥L := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥(L.subgroupOf K) :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect p (L.subgroupOf K)
      hLK.2
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLK.1).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hLK.1).surjective

theorem isQuasisimple_quot (hp : p.Prime) (hLK : IsPComponentIn p L K) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pPrimeCore p ↥L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple
    p (L.subgroupOf K) hLK.2
  let e := Subgroup.subgroupOfEquivOfLe hLK.1
  have hmap := CFSG.pPrimeCore_map_iso p e
  exact CFSG.IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr (CFSG.pPrimeCore p ↥(L.subgroupOf K)) (CFSG.pPrimeCore p ↥L) e hmap).symm h

theorem closure_pElem_eq_top (hp : p.Prime) (hLK : IsPComponentIn p L K) :
    closure {y : ↥L | ∃ n : ℕ, orderOf y = p ^ n} = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  let S : Set ↥(L.subgroupOf K) := {x | ∃ n : ℕ, orderOf x = p ^ n}
  let T : Set ↥L := {y | ∃ n : ℕ, orderOf y = p ^ n}
  have htop : Subgroup.closure S = ⊤ := by
    have h := CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent
      p (L.subgroupOf K) hLK.2
    rwa [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure] at h
  let e := Subgroup.subgroupOfEquivOfLe hLK.1
  have hset : e.toMonoidHom '' S = T := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨n, hn⟩ := hx
      refine ⟨n, ?_⟩
      change orderOf (e x) = p ^ n
      rw [MulEquiv.orderOf_eq, hn]
    · rintro ⟨n, hn⟩
      refine ⟨e.symm y, ⟨n, ?_⟩, e.apply_symm_apply y⟩
      rw [MulEquiv.orderOf_eq, hn]
  have h' : Subgroup.map e.toMonoidHom (Subgroup.closure S) = ⊤ := by
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  rw [MonoidHom.map_closure, hset] at h'
  exact h'

end IsPComponentIn

theorem isSubnormal_kSub_of_not_le (hL : ¬ pLayerIn p H ≤ M) :
    ((kSub p M H).subgroupOf H).IsSubnormal := by
  classical
  unfold kSub
  rw [if_neg hL]
  let S : Set (Subgroup G) := {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M}
  let T : Set (Subgroup ↥H) := (fun K => K.subgroupOf H) '' S
  have hTsub : ∀ A ∈ T, A.IsSubnormal := by
    intro A hA
    obtain ⟨Y, hY, hYA⟩ := hA
    rw [← hYA]
    exact hY.1.2.choose_spec.2.1
  have hgen : (Subgroup.closure (⋃ A ∈ T, (A : Set ↥H))).IsSubnormal :=
    (CFSG.GroupTheory.subnormal_subgroups_generated_join T hTsub).1
  have hgen_eq : sSup T = Subgroup.closure (⋃ A ∈ T, (A : Set ↥H)) := by
    rw [sSup_eq_iSup']
    simpa using Subgroup.iSup_eq_closure (fun A : ↥T => (A : Subgroup ↥H))
  have hmap : (sSup T).map H.subtype = sSup S := by
    rw [sSup_eq_iSup', Subgroup.map_iSup, sSup_eq_iSup']
    refine le_antisymm ?_ ?_
    · refine iSup_le fun A => ?_
      obtain ⟨Y, hY, hYA⟩ := A.2
      rw [← hYA, Subgroup.map_subgroupOf_eq_of_le hY.1.1]
      exact le_iSup (fun Y : ↥S => (Y : Subgroup G)) ⟨Y, hY⟩
    · refine iSup_le fun Y => ?_
      have hYT : Y.1.subgroupOf H ∈ T := ⟨Y.1, Y.2, rfl⟩
      rw [← Subgroup.map_subgroupOf_eq_of_le Y.2.1.1]
      exact le_iSup (fun A : ↥T => (A : Subgroup ↥H).map H.subtype) ⟨Y.1.subgroupOf H, hYT⟩
  have hAle : sSup S ≤ H := sSup_le fun Y hY => hY.1.1
  have hA : ((sSup S).subgroupOf H).map H.subtype = sSup S :=
    Subgroup.map_subgroupOf_eq_of_le hAle
  have hEq : (sSup S).subgroupOf H = sSup T :=
    Subgroup.map_injective H.subtype_injective (hA.trans hmap.symm)
  rw [hEq, hgen_eq]
  exact hgen

theorem IsPComponentIn.isSubnormal_of_kSub {L : Subgroup G} (hL : ¬ pLayerIn p H ≤ M)
    (hLK : IsPComponentIn p L (kSub p M H)) : (L.subgroupOf H).IsSubnormal :=
  CFSG.Walter.isSubnormal_subgroupOf_trans hLK.1 hLK.2.choose_spec.2.1
    (isSubnormal_kSub_of_not_le hL)

private theorem relPPrimeCore_eq_map' (hp : p.Prime) (C : Subgroup G) :
    CFSG.Open.relPPrimeCore p C = (CFSG.pPrimeCore p ↥C).map C.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNC, hNn, hNc⟩ := hN
    have h1 : N.subgroupOf C ≤ CFSG.pPrimeCore p ↥C := by
      refine le_sSup ⟨hNn, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
      exact hNc
    calc N = (N.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hNC).symm
      _ ≤ _ := Subgroup.map_mono h1
  · refine le_sSup ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · show (Subgroup.comap C.subtype ((CFSG.pPrimeCore p ↥C).map C.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      exact CFSG.pPrimeCore_normal
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card

theorem isTwoPrimeComponentIn_of_le_center (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : ¬ pLayerIn p H ≤ M) {L : Subgroup G} (hLK : IsPComponentIn p L (kSub p M H))
    (hc : CFSG.pPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L) ≤ center (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsTwoPrimeComponentIn L H := by
  have hLH : L ≤ H := hLK.1.trans (kSub_le p M H)
  have hsn : (L.subgroupOf H).IsSubnormal := hLK.isSubnormal_of_kSub hL
  haveI : Group.IsPerfect ↥L := IsPComponentIn.isPerfect hp hLK
  refine ⟨hLH, hsn, ?_, ?_⟩
  · let P : Type := ↥L ⧸ CFSG.pCore 2 ↥L
    have hPperf : Group.IsPerfect P := inferInstance
    have hq : CFSG.IsQuasisimple (P ⧸ CFSG.pPrimeCore p P) := by
      obtain ⟨e⟩ := nonempty_quot_pPrimeCore_quot_mulEquiv (Y := ↥L) hp hp2
      exact CFSG.IsQuasisimple.of_mulEquiv e (IsPComponentIn.isQuasisimple_quot hp hLK)
    have hker : (QuotientGroup.mk' (CFSG.pPrimeCore p P)).ker ≤ center P := by
      rw [QuotientGroup.ker_mk']
      exact hc
    exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective hPperf (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) hker).mpr hq
  · let S : Set ↥L := {x : ↥L | Odd (orderOf x)}
    let N : Subgroup ↥L := Subgroup.closure S
    have hNnormal : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      refine Subgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_)
        (fun x _ ihx => ?_) hn
      · refine Subgroup.subset_closure ?_
        change Odd (orderOf (MulAut.conj g x))
        rw [MulEquiv.orderOf_eq]
        exact hx
      · simp
      · rw [← conj_mul]
        exact mul_mem ihx ihy
      · rw [← conj_inv]
        exact inv_mem ihx
    haveI : N.Normal := hNnormal
    have hP2 : IsPGroup 2 (↥L ⧸ N) := by
      rw [IsPGroup.iff_orderOf]
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
      obtain ⟨a, m, hm, horder⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
      have hz : y ^ 2 ^ a ∈ N := by
        apply Subgroup.subset_closure
        show Odd (orderOf (y ^ 2 ^ a))
        apply hm.of_dvd_nat
        rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, ← horder, pow_orderOf_eq_one]
      have hy2 : (QuotientGroup.mk' N y) ^ 2 ^ a = 1 := by
        rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hz
      have hdvd : orderOf (QuotientGroup.mk' N y) ∣ 2 ^ a :=
        orderOf_dvd_iff_pow_eq_one.mpr hy2
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨j, hj⟩
    have hsolv : Group.IsSolvable (↥L ⧸ N) := by
      haveI := hP2.isNilpotent
      infer_instance
    have hNtop : N = ⊤ := by
      have hsub : Subsingleton (↥L ⧸ N) := by
        by_contra h
        haveI : Nontrivial (↥L ⧸ N) := not_subsingleton_iff_nontrivial.mp h
        exact Group.IsPerfect.not_isSolvable (↥L ⧸ N) hsolv
      exact QuotientGroup.subsingleton_iff.mp hsub
    calc L = Subgroup.map L.subtype ⊤ :=
          (Subgroup.range_subtype L).symm.trans (MonoidHom.range_eq_map L.subtype)
      _ = Subgroup.map L.subtype N := by rw [hNtop]
      _ = Subgroup.map L.subtype (Subgroup.closure S) := rfl
      _ = Subgroup.closure (L.subtype '' S) := MonoidHom.map_closure L.subtype S
      _ = Subgroup.closure {x : G | x ∈ L ∧ Odd (orderOf x)} := by
            congr 1
            ext x
            constructor
            · rintro ⟨u, hu, rfl⟩
              refine ⟨u.2, ?_⟩
              change Odd (orderOf (u : G))
              rwa [Subgroup.orderOf_coe]
            · rintro ⟨hxL, hxodd⟩
              refine ⟨⟨x, hxL⟩, ?_, rfl⟩
              change Odd (orderOf (⟨x, hxL⟩ : ↥L))
              rwa [Subgroup.orderOf_mk]

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
