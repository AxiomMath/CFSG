module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219B
import CFSG.GroupTheory.PCore.PrimeSetCore

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace L219

variable {G : Type} [Group G] [Finite G] {z : G}

theorem part_b2 (hz : orderOf z = 2) {L : Subgroup G} (hL : TwoComponents.IsTwoComponent L)
    (hLz : L.map (MulAut.conj z).toMonoidHom ≠ L) :
    (pPrimeCore 2 ↥((L ⊔ L.map (MulAut.conj z).toMonoidHom) ⊓ centralizer {z})).map
        ((L ⊔ L.map (MulAut.conj z).toMonoidHom) ⊓ centralizer {z}).subtype =
      pPrimeCore 2 G ⊓ ((L ⊔ L.map (MulAut.conj z).toMonoidHom) ⊓ centralizer {z}) := by
  obtain ⟨-, hAB, -⟩ := part_b1 hz hL hLz
  obtain ⟨hLb, hLzb, hne⟩ := diag_setup hz hL hLz
  have ht2 : orderOf (barMk G z) = 2 := orderOf_barMk hz
  have hcomp := isComponent_diag ht2 hLb hne
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hMZ, -⟩ :=
    diagonal_component_centralizer_index_two hLb hne ht2
  obtain ⟨-, hΔC, -, -, -, -, -, -, -, -, -, -⟩ :=
    swapped_quasisimple_fixed_central_product ht2 (assembly_isQuasisimple_of_isComponent hLb) hAB
  set H := centralizer ({z} : Set G) with hH
  set Ct := centralizer ({barMk G z} : Set (barQ G)) with hCt
  set Lz := L.map (MulAut.conj z).toMonoidHom with hLzdef
  set M := L ⊔ Lz with hMdef
  set C := M ⊓ H with hCdef
  set Q := (pPrimeCore 2 ↥C).map C.subtype with hQdef
  set Mb := L.map (barMk G) ⊔ conjSub (barMk G z)⁻¹ (L.map (barMk G)) with hMbdef
  set Δ := (swapDiag hAB).range with hΔdef
  have hΔCt : Δ ≤ Ct := hΔC.trans inf_le_right
  have hQC : Q ≤ C := map_subtype_le _
  have hQodd : Odd (Nat.card ↥Q) := by
    rw [hQdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact odd_card_pPrimeCore _
  refine le_antisymm (le_inf ?_ hQC) ?_
  ·
    have hMsub : M.IsSubnormal := CFSG.GroupTheory.isSubnormal_sup
      ((isTwoComponent_iff_twoComponents L).mpr hL).1
      ((isTwoComponent_iff_twoComponents Lz).mpr (twoComponent_map_conj hL z)).1
    have hCH : (C.subgroupOf H).IsSubnormal := by
      rw [hCdef, inf_subgroupOf_right]
      exact hMsub.subgroupOf
    have hQn : (Q.subgroupOf C).Normal := by
      rw [hQdef, map_subtype_subgroupOf]
      exact pPrimeCore_normal
    have hQH : (Q.subgroupOf H).IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_subgroupOf_trans hQC inf_le_right hQn.isSubnormal hCH
    set U := (Q.subgroupOf H).map (barMkCentralizer hz) with hUdef
    have hUsub : U.IsSubnormal := hQH.map (barMkCentralizer_surjective hz)
    have hUodd : Odd (Nat.card ↥U) :=
      (hQodd.of_dvd_nat (card_subgroupOf_dvd _ _)).of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hcomm : ⁅Δ.subgroupOf Ct, U⁆ = ⊥ := by
      rcases CFSG.LocalCores.component_subnormal_subgroup hcomp hUsub with h | h
      · exact absurd h (not_le_of_isComponent_of_isSolvable hcomp
          (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hUodd))
      · exact h
    have hZC : Q.map (barMk G) ≤ centralizer (Δ : Set (barQ G)) := by
      rintro _ ⟨q, hq, rfl⟩
      rw [mem_centralizer_iff]
      intro δ hδ
      have hqH : q ∈ H := (hQC hq).2
      have hu : barMkCentralizer hz ⟨q, hqH⟩ ∈ U := ⟨⟨q, hqH⟩, hq, rfl⟩
      have hd : (⟨δ, hΔCt hδ⟩ : ↥Ct) ∈ Δ.subgroupOf Ct := hδ
      have h1 := Subgroup.commutator_mem_commutator hd hu
      rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, barMkCentralizer_apply] at h2
      exact h2
    have hZM : Q.map (barMk G) ≤ Mb := by
      rw [hMbdef, ← hLzb, ← Subgroup.map_sup]
      exact map_mono (hQC.trans inf_le_left)
    have hZZ : Q.map (barMk G) ≤ (center ↥Mb).map Mb.subtype := (le_inf hZM hZC).trans hMZ.le
    have hZn : ((Q.map (barMk G)).subgroupOf Mb).Normal := by
      refine normal_of_le_center ?_
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hZZ hx
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    have hMbsub : Mb.IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_sup hLb.2 (isComponent_conjSub hLb _).2
    have hZsub : (Q.map (barMk G)).IsSubnormal :=
      Subgroup.IsSubnormal.trans hZM hZn.isSubnormal hMbsub
    have hZodd : Odd (Nat.card ↥(Q.map (barMk G))) := hQodd.of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hZO := Walter.map_pPrimeCore_le_of_isSubnormal hZsub
    rw [pPrimeCore_quotient_eq_bot Nat.prime_two] at hZO
    have htop : (⊤ : Subgroup ↥(Q.map (barMk G))) ≤ pPrimeCore 2 ↥(Q.map (barMk G)) :=
      le_sSup ⟨normal_top, by rw [Subgroup.card_top]; exact Nat.coprime_two_left.mpr hZodd⟩
    have hZbot : Q.map (barMk G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact hZO ⟨⟨x, hx⟩, htop (mem_top _), rfl⟩
    rw [Subgroup.map_eq_bot_iff, ker_barMk] at hZbot
    exact hZbot
  ·
    rintro x ⟨hxO, hxC⟩
    refine ⟨⟨x, hxC⟩, ?_, rfl⟩
    have hle : (pPrimeCore 2 G).subgroupOf C ≤ pPrimeCore 2 ↥C :=
      le_sSup ⟨(pPrimeCore_normal (p := 2) (G := G)).subgroupOf C,
        Nat.Coprime.coprime_dvd_right (card_subgroupOf_dvd _ _) pPrimeCore_coprime_card⟩
    exact hle hxO

theorem part_b3 (hz : orderOf z = 2) {L : Subgroup G} (hL : TwoComponents.IsTwoComponent L)
    (hLz : L.map (MulAut.conj z).toMonoidHom ≠ L) :
    ∃ φ : ↥L ⧸ pPrimeCore 2 ↥L →*
        ↥(centralizerResidual (L ⊔ L.map (MulAut.conj z).toMonoidHom) z) ⧸
          pPrimeCore 2 ↥(centralizerResidual (L ⊔ L.map (MulAut.conj z).toMonoidHom) z),
      Function.Surjective φ := by
  obtain ⟨-, hAB, hRmap⟩ := part_b1 hz hL hLz
  set R := centralizerResidual (L ⊔ L.map (MulAut.conj z).toMonoidHom) z with hRdef
  set ρ := (barMk G).subgroupMap R with hρ
  have hρs : Function.Surjective ρ := (barMk G).subgroupMap_surjective R
  have hkerO : ρ.ker.map R.subtype ≤ pPrimeCore 2 G := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← ker_barMk, MonoidHom.mem_ker]
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hr)
  have hker : ρ.ker ≤ pPrimeCore 2 ↥R := by
    refine le_sSup ⟨ρ.normal_ker, ?_⟩
    have h := Subgroup.card_dvd_of_le hkerO
    rw [Subgroup.card_map_of_injective R.subtype_injective] at h
    exact Nat.Coprime.coprime_dvd_right h pPrimeCore_coprime_card
  let q : ↥R ⧸ ρ.ker →* ↥R ⧸ pPrimeCore 2 ↥R := QuotientGroup.map _ _ (MonoidHom.id _) hker
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk r, rfl⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective ρ hρs
  let Φ : ↥L →* ↥R ⧸ pPrimeCore 2 ↥R :=
    q.comp (e.symm.toMonoidHom.comp ((MulEquiv.subgroupCongr hRmap.symm).toMonoidHom.comp
      ((swapDiag hAB).rangeRestrict.comp ((barMk G).subgroupMap L))))
  have hΦ : Function.Surjective Φ :=
    hq.comp (e.symm.surjective.comp ((MulEquiv.subgroupCongr hRmap.symm).surjective.comp
      ((swapDiag hAB).rangeRestrict_surjective.comp ((barMk G).subgroupMap_surjective L))))
  have hOL : pPrimeCore 2 ↥L ≤ Φ.ker := by
    have hn : ((pPrimeCore 2 ↥L).map Φ).Normal :=
      (pPrimeCore_normal (p := 2) (G := ↥L)).map Φ hΦ
    have hle : (pPrimeCore 2 ↥L).map Φ ≤ pPrimeCore 2 (↥R ⧸ pPrimeCore 2 ↥R) :=
      le_sSup ⟨hn, Nat.coprime_two_left.mpr (odd_card_map_pPrimeCore Φ)⟩
    rwa [pPrimeCore_quotient_eq_bot Nat.prime_two, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
  refine ⟨QuotientGroup.lift (pPrimeCore 2 ↥L) Φ hOL, ?_⟩
  intro y
  obtain ⟨l, rfl⟩ := hΦ y
  exact ⟨QuotientGroup.mk l, rfl⟩

end L219

end CFSG.ComponentClassification.HarrisLit
