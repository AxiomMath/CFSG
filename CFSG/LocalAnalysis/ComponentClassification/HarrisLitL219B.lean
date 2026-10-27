module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219A

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace L219

section General

variable {Y : Type*} [Group Y] [Finite Y]

theorem le_normalizer_of_odd_of_normal {K N : Subgroup Y} (hK : TwoComponents.IsTwoComponent K)
    (hN : N.Normal) (hNo : Odd (Nat.card ↥N)) : N ≤ normalizer (K : Set Y) := by
  rcases TwoComponentSubnormal.contains_or_normalizes_core K N hK
    (Components.chain_of_mathlib_subnormal hN.isSubnormal) with h | h
  · exact absurd h (not_le_of_odd_of_twoComponent hK hNo)
  · exact h.1

omit [Finite Y] in
theorem card_subgroupOf_dvd (A B : Subgroup Y) : Nat.card ↥(A.subgroupOf B) ∣ Nat.card ↥A := by
  have h := Subgroup.card_dvd_of_le (show (A.subgroupOf B).map B.subtype ≤ A from by
    rw [subgroupOf_map_subtype]; exact inf_le_left)
  rwa [Subgroup.card_map_of_injective B.subtype_injective] at h

omit [Finite Y] in
theorem map_subtype_subgroupOf (A : Subgroup Y) (X : Subgroup ↥A) :
    (X.map A.subtype).subgroupOf A = X :=
  comap_map_eq_self_of_injective A.subtype_injective X

end General

variable {G : Type} [Group G] [Finite G] {z : G}

theorem diag_setup (hz : orderOf z = 2) {L : Subgroup G} (hL : TwoComponents.IsTwoComponent L)
    (hLz : L.map (MulAut.conj z).toMonoidHom ≠ L) :
    IsComponent (L.map (barMk G)) ∧
      (L.map (MulAut.conj z).toMonoidHom).map (barMk G) =
        conjSub (barMk G z)⁻¹ (L.map (barMk G)) ∧
      conjSub (barMk G z)⁻¹ (L.map (barMk G)) ≠ L.map (barMk G) := by
  have hinv : (barMk G z)⁻¹ = barMk G z := inv_eq_self_of_orderOf_eq_two (orderOf_barMk hz)
  have hmap : (L.map (MulAut.conj z).toMonoidHom).map (barMk G) =
      conjSub (barMk G z)⁻¹ (L.map (barMk G)) := by
    rw [hinv, map_barMk_map_conj]
  refine ⟨isComponent_map_barMk hL, hmap, fun h => hLz ?_⟩
  exact OddKernelTwoComponents.lift_unique (barMk G) barMk_surjective odd_card_ker_barMk _ _
    (twoComponent_map_conj hL z) hL (hmap.trans h)

theorem isComponent_diag {X : Type} [Group X] [Finite X] {t : X} (ht : orderOf t = 2)
    {A : Subgroup X} (hA : IsComponent A) (hAt : conjSub t⁻¹ A ≠ A) :
    IsComponent (((swapDiag (commutator_conjSub_eq_bot hA hAt)).range).subgroupOf
      (centralizer ({t} : Set X))) := by
  set hAB := commutator_conjSub_eq_bot hA hAt
  obtain ⟨-, hΔC, -, -, -, hΔq, -, -, hder, -, -, -⟩ :=
    swapped_quasisimple_fixed_central_product ht (assembly_isQuasisimple_of_isComponent hA) hAB
  have hΔCt : (swapDiag hAB).range ≤ centralizer ({t} : Set X) := hΔC.trans inf_le_right
  have hΔn : ((swapDiag hAB).range.subgroupOf
      ((A ⊔ conjSub t⁻¹ A) ⊓ centralizer ({t} : Set X))).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hΔC, ← hder]
    exact le_normalizer_commutator _ _
  have hMsub : (A ⊔ conjSub t⁻¹ A).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_sup hA.2 (isComponent_conjSub hA t⁻¹).2
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hΔCt).symm
    ((AssemblyBPredicates.isQuasisimple_iff_native _).mp hΔq), ?_⟩
  refine CFSG.GroupTheory.isSubnormal_subgroupOf_trans hΔC inf_le_right hΔn.isSubnormal ?_
  rw [inf_subgroupOf_right]
  exact hMsub.subgroupOf

theorem part_b1 (hz : orderOf z = 2) {L : Subgroup G} (hL : TwoComponents.IsTwoComponent L)
    (hLz : L.map (MulAut.conj z).toMonoidHom ≠ L) :
    IsTwoComponentIn (centralizerResidual (L ⊔ L.map (MulAut.conj z).toMonoidHom) z)
        (centralizer {z}) ∧
      ∃ hAB : ⁅L.map (barMk G), conjSub (barMk G z)⁻¹ (L.map (barMk G))⁆ = ⊥,
        (centralizerResidual (L ⊔ L.map (MulAut.conj z).toMonoidHom) z).map (barMk G) =
          (swapDiag hAB).range := by
  obtain ⟨hLb, hLzb, hne⟩ := diag_setup hz hL hLz
  have ht2 : orderOf (barMk G z) = 2 := orderOf_barMk hz
  have hcomp := isComponent_diag ht2 hLb hne
  set hAB := commutator_conjSub_eq_bot hLb hne
  obtain ⟨-, hΔC, -, -, -, -, -, -, hder, -, -, -⟩ :=
    swapped_quasisimple_fixed_central_product ht2 (assembly_isQuasisimple_of_isComponent hLb) hAB
  set H := centralizer ({z} : Set G) with hH
  set Ct := centralizer ({barMk G z} : Set (barQ G)) with hCt
  set Lz := L.map (MulAut.conj z).toMonoidHom with hLzdef
  set M := L ⊔ Lz with hMdef
  set R := centralizerResidual M z with hRdef
  set Δ := (swapDiag hAB).range with hΔdef
  have hΔCt : Δ ≤ Ct := hΔC.trans inf_le_right
  have hMmap : M.map (barMk G) = L.map (barMk G) ⊔ conjSub (barMk G z)⁻¹ (L.map (barMk G)) := by
    rw [hMdef, Subgroup.map_sup, hLzb]
  have hΔ2 : TwoComponents.IsTwoComponent (Δ.subgroupOf Ct) := by
    refine (CatalogueBAlternating.pComponent_two_iff _).mp
      (isPComponent_of_isComponent_of_not_le 2 hcomp ?_)
    exact not_le_of_isComponent_of_isSolvable hcomp
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_pPrimeCore _))
  obtain ⟨R', hR', hR'map⟩ := OddKernelTwoComponents.exists_lift (barMkCentralizer hz)
    (barMkCentralizer_surjective hz) (odd_card_ker_barMkCentralizer hz) _ hΔ2
  set R'' := R'.map H.subtype with hR''def
  have hR''H : R'' ≤ H := map_subtype_le _
  have hR''2 : IsTwoComponentIn R'' H :=
    isTwoComponentIn_iff_twoComponents.mpr
      ⟨hR''H, by rw [hR''def, map_subtype_subgroupOf]; exact hR'⟩
  have hR''map : R''.map (barMk G) = Δ := by
    have hcomp' : (barMk G).comp H.subtype = Ct.subtype.comp (barMkCentralizer hz) := by
      ext c
      exact (barMkCentralizer_apply hz c).symm
    rw [hR''def, Subgroup.map_map, hcomp', ← Subgroup.map_map, hR'map,
      map_subgroupOf_eq_of_le hΔCt]
  have hR''perf : Group.IsPerfect ↥R'' := hR''2.2.2.1
  have hOM : pPrimeCore 2 G ≤ normalizer (M : Set G) :=
    le_normalizer_sup (pPrimeCore_le_normalizer hL)
      (pPrimeCore_le_normalizer (twoComponent_map_conj hL z))
  have hR''M : R'' ≤ M := le_of_map_barMk_le hR''perf hOM (by
    rw [hR''map, hMmap]
    exact hΔC.trans inf_le_left)
  have hR''R : R'' ≤ R := le_perfectResidual_map (le_inf hR''M hR''H) hR''perf
  have hRC : R ≤ M ⊓ H := centralizerResidual_le
  have hRH : R ≤ H := hRC.trans inf_le_right
  have hRperf : Group.IsPerfect ↥R := isPerfect_perfectResidual_map (M ⊓ H)
  have hRmap : R.map (barMk G) ≤ Δ := by
    have hHmap : H.map (barMk G) = Ct := map_centralizer_barMk hz
    have h1 : R.map (barMk G) ≤
        (L.map (barMk G) ⊔ conjSub (barMk G z)⁻¹ (L.map (barMk G))) ⊓ Ct := by
      refine le_inf ?_ ?_
      · rw [← hMmap]
        exact map_mono (hRC.trans inf_le_left)
      · rw [← hHmap]
        exact map_mono hRH
    have h2 : ⁅R.map (barMk G), R.map (barMk G)⁆ = R.map (barMk G) := by
      rw [← map_commutator, (Subgroup.isPerfect_iff).mp hRperf]
    rw [← h2, ← hder]
    exact commutator_mono h1 h1
  set N := (pPrimeCore 2 G).subgroupOf H with hNdef
  have hNodd : Odd (Nat.card ↥N) :=
    (odd_card_pPrimeCore G).of_dvd_nat (card_subgroupOf_dvd _ _)
  have hNn : N.Normal := (pPrimeCore_normal (p := 2) (G := G)).subgroupOf H
  have hPperf : Group.IsPerfect ↥(R.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRH).symm.toMonoidHom) (MulEquiv.surjective _)
  have hRle : R.subgroupOf H ≤ R' := by
    refine le_of_le_sup_of_odd hPperf hNodd (le_normalizer_of_odd_of_normal hR' hNn hNodd) ?_
    intro p hp
    rw [mem_subgroupOf] at hp
    obtain ⟨r, hr, hrp⟩ : barMk G (p : G) ∈ R''.map (barMk G) := by
      rw [hR''map]
      exact hRmap ⟨p, hp, rfl⟩
    obtain ⟨r', hr', hr'r⟩ := hr
    have hr'r' : (r' : G) = r := hr'r
    have hk : r'⁻¹ * p ∈ N := by
      rw [hNdef, mem_subgroupOf, ← ker_barMk, MonoidHom.mem_ker, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv, hr'r', hrp, inv_mul_cancel]
    have : p = r' * (r'⁻¹ * p) := by group
    rw [this]
    exact mul_mem (mem_sup_left hr') (mem_sup_right hk)
  have hRR'' : R ≤ R'' := by
    have := map_mono (f := H.subtype) hRle
    rwa [map_subgroupOf_eq_of_le hRH] at this
  have hReq : R = R'' := le_antisymm hRR'' hR''R
  refine ⟨?_, hAB, ?_⟩
  · rw [hReq]
    exact hR''2
  · rw [hReq, hR''map]

end L219

end CFSG.ComponentClassification.HarrisLit
