module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Quot
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Tools

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.ComponentClassification.CatalogueBPrimeJoin CFSG.GH74.GLS

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem mem_pPrimeCore_of_mem_center {t : X} {L : Subgroup X} (ht : orderOf t = 2)
    (hL : IsAhatIntr X t L) (htZ : t ∉ center X) {x : ↥L} (hx : (x : X) ∈ center X) :
    x ∈ pPrimeCore 2 ↥L := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLC, htL, -, n, -, hcov⟩ := hL
  have hQc : Nat.card (center (↥L ⧸ pPrimeCore 2 ↥L)) = 2 := hcov.2.1
  set tL : ↥L := ⟨t, htL⟩ with htLdef
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥L)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have htL2 : orderOf tL = 2 := by rw [htLdef, Subgroup.orderOf_mk]; exact ht
  have hxc : ((x : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hx (y : X)))
  have htc : ((tL : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    refine Subtype.ext ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLC y.2)
  have htne : ((tL : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) ≠ 1 := by
    intro h
    have hmem : tL ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff tL).1 h
    have := Subgroup.orderOf_dvd_natCard _ hmem
    rw [htL2] at this
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr this)
  by_cases hx1 : ((x : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) = 1
  · exact (QuotientGroup.eq_one_iff x).1 hx1
  exfalso
  have hxt : ((x : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) = ((tL : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center (↥L ⧸ pPrimeCore 2 ↥L))).1 hQc
    have h1 : (⟨_, hxc⟩ : center (↥L ⧸ pPrimeCore 2 ↥L)) = y :=
      hy _ (fun h => hx1 (congrArg Subtype.val h))
    have h2 : (⟨_, htc⟩ : center (↥L ⧸ pPrimeCore 2 ↥L)) = y :=
      hy _ (fun h => htne (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)
  have ho : tL⁻¹ * x ∈ pPrimeCore 2 ↥L := by
    rw [← QuotientGroup.eq]
    exact hxt.symm
  set o : ↥L := tL⁻¹ * x with hodef
  have hxo : x = tL * o := by rw [hodef]; group
  have hodd_o : Odd (orderOf o) := by
    have h1 : orderOf o ∣ Nat.card (pPrimeCore 2 ↥L) := Subgroup.orderOf_dvd_natCard _ ho
    exact Odd.of_dvd_nat hOodd h1
  have hcomm : Commute tL o := by
    have hxt' : Commute tL x := by
      refine Subtype.ext ?_
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hLC x.2)).symm
    rw [hodef]
    exact ((Commute.refl tL).inv_right).mul_right hxt'
  obtain ⟨m, hm⟩ := hodd_o
  have hom : o ^ orderOf o = 1 := pow_orderOf_eq_one o
  have htm : tL ^ orderOf o = tL := by
    rw [hm, pow_succ, pow_mul, show tL ^ 2 = 1 by rw [← htL2]; exact pow_orderOf_eq_one tL,
      one_pow, one_mul]
  have hxpow : x ^ orderOf o = tL := by
    rw [hxo, hcomm.mul_pow, htm, hom, mul_one]
  apply htZ
  have h1 : (x : X) ^ orderOf o ∈ center X := Subgroup.pow_mem _ hx _
  have h2 : (x : X) ^ orderOf o = t := by
    have := congrArg (fun z : ↥L => (z : X)) hxpow
    simpa using this
  rwa [h2] at h1


theorem not_two_dvd_card_ker_domRestrict_center {t : X} {L : Subgroup X} (ht : orderOf t = 2)
    (hL : IsAhatIntr X t L) (htZ : t ∉ center X) :
    ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (center X)).domRestrict L).ker := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥L)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hle : ((QuotientGroup.mk' (center X)).domRestrict L).ker ≤ pPrimeCore 2 ↥L := by
    intro x hx
    refine mem_pPrimeCore_of_mem_center ht hL htZ ?_
    have : QuotientGroup.mk' (center X) (x : X) = 1 := hx
    exact (QuotientGroup.eq_one_iff (x : X)).1 this
  have hdvd := Subgroup.card_dvd_of_le hle
  intro h2
  exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr (h2.trans hdvd))

theorem IsAhatIntr.map_center {t : X} {L : Subgroup X} (ht : orderOf t = 2)
    (hL : IsAhatIntr X t L) (htZ : t ∉ center X) :
    IsAhatIntr (X ⧸ center X) (QuotientGroup.mk t) (L.map (QuotientGroup.mk' (center X))) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : X →* X ⧸ center X := QuotientGroup.mk' (center X) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker := not_two_dvd_card_ker_domRestrict_center ht hL htZ
  have hq : IsTwoGenQuasi ↥L := isTwoGenQuasi_of_isAhatIntr hL
  obtain ⟨hLC, htL, hpc, n, hn, hcov⟩ := hL
  set D : Subgroup X := centralizer ({t} : Set X) with hD
  set C : Subgroup (X ⧸ center X) := centralizer ({QuotientGroup.mk t} : Set (X ⧸ center X))
    with hCdef
  have hπt : π t = QuotientGroup.mk t := rfl
  have hDC : D.map π ≤ C := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp hd
    rw [← hπt, ← map_mul, ← map_mul, this]
  have hLD : L ≤ D := hLC
  have hLC' : L.map π ≤ C := (Subgroup.map_mono hLD).trans hDC
  have hDn : ((D.map π).subgroupOf C).Normal := by
    refine ⟨fun d hd g => ?_⟩
    have hd' : (d : X ⧸ center X) ∈ D.map π := hd
    obtain ⟨δ, hδ, hδd⟩ := hd'
    obtain ⟨x, hx⟩ := hπs (g : X ⧸ center X)
    have hgC : (g : X ⧸ center X) ∈ C := g.2
    have hxt : ⁅x, t⁆ ∈ center X := by
      have h1 : π ⁅x, t⁆ = 1 := by
        rw [map_commutatorElement, hx, hπt, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hgC)
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hconj := conj_mem_centralizer_of_central_comm hxt hδ
    show ((g : X ⧸ center X) * (d : X ⧸ center X) * (g : X ⧸ center X)⁻¹) ∈ D.map π
    rw [← hx, ← hδd, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hconj, rfl⟩
  obtain ⟨e, -⟩ := exists_restrict_core_quotient_equiv (p := 2) π L hker
  have hgen : primeResidual 2 ↥(L.map π) = ⊤ := by
    rw [← primeResidual_map_surjective 2 (π.subgroupMap L) (π.subgroupMap_surjective L), hq.1]
    exact Subgroup.map_top_of_surjective _ (π.subgroupMap_surjective L)
  have hTGQ : IsTwoGenQuasi ↥(L.map π) := ⟨hgen, LocalCores.isQuasisimple_of_mulEquiv e hq.2⟩
  have hsubD : (L.subgroupOf D).IsSubnormal := (isPComponent_two_iff.1 hpc).1
  have hA : ((L.map π).subgroupOf (D.map π)).IsSubnormal := by
    have := Subgroup.IsSubnormal.map (π.subgroupMap_surjective D) hsubD
    rwa [ComponentClassification.GSThmB.OddQuot.map_subgroupOf_subgroupMap π hLD] at this
  have hsub : ((L.map π).subgroupOf C).IsSubnormal :=
    isSubnormal_subgroupOf_of_normal_overgroup (Subgroup.map_mono hLD) hDC hA hDn
  have hpc' : IsPComponent 2 ((L.map π).subgroupOf C) :=
    isPComponent_two_iff.2 ⟨hsub, (isTwoGenQuasi_subgroupOf_iff hLC').2 hTGQ⟩
  exact ⟨hLC', Subgroup.mem_map_of_mem π htL, hpc', n, hn,
    GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr e hcov⟩

end CFSG.OddStandard.Solomon75
