module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieSub
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KHupGeFive
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526H
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem isPComponent_subgroupOf_of_isC2 {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {L Y : Subgroup X} (hL : IsC2 L) (hLY : L ≤ Y) (hpL : p ∣ Nat.card L) :
    CFSG.IsPComponent p (L.subgroupOf Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set φ := isPComponent_of_isLThree_barHom L
  have hφ : Function.Surjective φ := isPComponent_of_isLThree_aux1 L
  have hker2 : IsPGroup 2 φ.ker := isPComponent_of_isLThree_aux3 L
  have hkerp : ¬ p ∣ Nat.card φ.ker := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker2
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hQ : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.2.2.2.2
  have hpQ : p ∣ Nat.card ↥(barO2 L) := by
    have hcard : Nat.card φ.ker * Nat.card ↥(barO2 L) = Nat.card ↥L := by
      rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hφ,
        Subgroup.card_top]
    rw [← hcard] at hpL
    exact ((Nat.Prime.dvd_mul hp).1 hpL).resolve_left hkerp
  set N := CFSG.pPrimeCore p ↥(barO2 L)
  have hNtop : N ≠ ⊤ := by
    intro h
    have hc : Nat.Coprime p (Nat.card N) := CFSG.pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hc
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hc hpQ
  have hNc : N ≤ Subgroup.center ↥(barO2 L) := Quasisimple.normal_le_center_of_ne_top hQ N hNtop
  have hQ' : CFSG.Open.IsQuasisimple (↥(barO2 L) ⧸ N) := Quasisimple.central_quotient hQ N hNc
  have hres : primeResidual p ↥L = ⊤ := by
    have hresQ' : primeResidual p (↥(barO2 L) ⧸ N) = ⊤ :=
      primeResidual_eq_top_of_corefree_quasisimple p
        (CatalogueBAlternating.quasisimple_iff_native.2 hQ')
        (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p)
    haveI : Group.IsPerfect ↥(barO2 L) := ⟨hQ.1⟩
    have hresQ : primeResidual p ↥(barO2 L) = ⊤ :=
      primeResidual_eq_top_of_central_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hNc) hresQ'
    have hsup : primeResidual p ↥L ⊔ φ.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, primeResidual_map_surjective p φ hφ, hresQ,
        Subgroup.comap_top]
    haveI : (primeResidual p ↥L).Characteristic := primeResidual_characteristic p ↥L
    have hodd : ∀ x : ↥L, ¬ 2 ∣ orderOf x → x ∈ primeResidual p ↥L :=
      CFSG.QuasithinUnique.Vol2Native.L239.Lie.mem_of_odd_orderOf_of_isSubnormal hker2
        (Subgroup.Normal.isSubnormal inferInstance) hsup
    rw [eq_top_iff]
    intro y _
    have hy : (y : X) ∈ oddHull L := by
      rw [hL.2.1]
      exact y.2
    have hle : oddHull L ≤ (primeResidual p ↥L).map L.subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨hxL, hxodd⟩
      refine ⟨⟨x, hxL⟩, hodd _ ?_, rfl⟩
      rw [Subgroup.orderOf_mk]
      exact hxodd.not_two_dvd_nat
    obtain ⟨j, hj, hjy⟩ := hle hy
    have hjy' : j = y := Subtype.ext hjy
    exact hjy' ▸ hj
  have hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pPrimeCore p ↥L) := by
    have hcore : N.comap φ = CFSG.pPrimeCore p ↥L :=
      (CFSG.prime_complement_kernel_core_preimage φ hφ hkerp).1
    let θ : ↥L →* ↥(barO2 L) ⧸ N := (QuotientGroup.mk' N).comp φ
    have hθ : Function.Surjective θ := (QuotientGroup.mk'_surjective N).comp hφ
    have hθker : θ.ker = CFSG.pPrimeCore p ↥L := by
      rw [← hcore]
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      exact QuotientGroup.eq_one_iff (φ x)
    exact CFSG.IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hθker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθ))
      (CatalogueBAlternating.quasisimple_iff_native.2 hQ')
  have hsub : L.IsSubnormal := hL.1.mathlib Subgroup.IsSubnormal.top
  exact (pComponent_subgroupOf_iff p L Y hLY).2 ⟨hsub.subgroupOf, hres, hqs⟩

theorem exists_pComponent_cMHat_of_not_normal {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {L L₁ : Subgroup X} (hL : IsC2 L) (hn : ¬ L.Normal)
    (hL₁ : IsC2 L₁) (hpL₁ : p ∣ Nat.card L₁) (hrk : CFSG.Open.pRank p L₁ ≤ 1)
    (h3 : 1 ≤ CFSG.Open.pRank 3 L₁) :
    ∃ I : Subgroup X, I ≤ cMHat L ∧ CFSG.IsPComponent p (I.subgroupOf (cMHat L)) ∧
      CFSG.Open.pRank p I = 1 ∧ 1 ≤ CFSG.Open.pRank 3 I := by
  have key : ∀ I : Subgroup X, IsC2 I → I ≠ L → p ∣ Nat.card I → CFSG.Open.pRank p I ≤ 1 →
      1 ≤ CFSG.Open.pRank 3 I →
      ∃ I : Subgroup X, I ≤ cMHat L ∧ CFSG.IsPComponent p (I.subgroupOf (cMHat L)) ∧
        CFSG.Open.pRank p I = 1 ∧ 1 ≤ CFSG.Open.pRank 3 I := by
    intro I hI hne hpI hrkI h3I
    have hle : I ≤ cMHat L :=
      Subgroup.map_le_iff_le_comap.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (isC2_commute_of_ne hI hL hne))
    exact ⟨I, hle, isPComponent_subgroupOf_of_isC2 hp hp2 hI hle hpI,
      le_antisymm hrkI (one_le_pRank_of_dvd I hp hpI), h3I⟩
  by_cases hne : L₁ = L
  · subst hne
    obtain ⟨g, hg⟩ : ∃ g : X, L₁.map (MulAut.conj g).toMonoidHom ≠ L₁ := by
      by_contra hall
      push Not at hall
      refine hn ⟨fun n hn' g => ?_⟩
      rw [← hall g]
      exact ⟨n, hn', rfl⟩
    have hcard : Nat.card (L₁.map (MulAut.conj g).toMonoidHom) = Nat.card L₁ :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    refine key _ (liftOf_conj_aux4 hL g) hg (by rw [hcard]; exact hpL₁) ?_ ?_
    · rw [exists_yComponent_dvd_aux_pRank_map_conj hp.one_lt]
      exact hrk
    · rw [exists_yComponent_dvd_aux_pRank_map_conj (by norm_num)]
      exact h3
  · exact key L₁ hL₁ hne hpL₁ hrk h3

theorem row1520One_of_not_normal {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (hLifts : RowLifts G M T T₁ T₂) (h19 : Row1519 G M T T₁ T₂) {p : ℕ} (hp : p ∈ sigmaM G M)
    {L : Subgroup ↥M} (hL : IsC2 L) (hn : ¬ L.Normal) :
    ∃ I : Subgroup ↥M, I ≤ cMHat L ∧ CFSG.IsPComponent p (I.subgroupOf (cMHat L)) ∧
      CFSG.Open.pRank p I = 1 ∧ 1 ≤ CFSG.Open.pRank 3 I := by
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  obtain ⟨Ls₁, hLs₁, hdvd⟩ :=
    exists_yComponent_dvd_ctx_gen kWiel_holds (kHupAt_odd hpp hp2) ctx hp
  obtain ⟨L₁, hL₁⟩ := hLifts Ls₁ hLs₁
  exact exists_pComponent_cMHat_of_not_normal hpp hp2 hL hn hL₁.1 (dvd_card_of_liftOf hL₁ hdvd)
    (h19 p hp Ls₁ L₁ hLs₁ hL₁) (one_le_pRank_three_of_lift ctx.gnThree hLs₁ hL₁)

end CFSG.LocalAnalysis.RankThreeUC.S15
