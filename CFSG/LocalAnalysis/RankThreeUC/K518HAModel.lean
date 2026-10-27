module

public import CFSG.LocalAnalysis.RankThreeUC.K518HACaseB
public import CFSG.LocalAnalysis.RankThreeUC.K518HACaseA

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open scoped Pointwise
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar CFSG.AGLEmbeddingD2.Tits.GN516
  CFSG.AGLEmbeddingD2.Tits.GN516.Nodes
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def HasRkModel (Y : Type) [Group Y] : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) (π : K →* Y) (M : ℕ),
    BorelQuotient D n H π M ∧ (∀ i, RkKind ↥(rankOne D.rootGroup i)) ∧
      (∀ i, π.ker ⊓ rankOne D.rootGroup i = ⊥) ∧ (∀ i, M ∣ Nat.card ↥(rankOne D.rootGroup i)) ∧
      ∀ i j, i ≠ j → Subgroup.center ↥(rankOne D.rootGroup i) = ⊥ ∨
        Subgroup.center ↥(rankOne D.rootGroup j) = ⊥

section Numerics

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

private theorem dvd_M_of_normalizer (h : BorelQuotient D n H π M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {l : Y} (hl : l ∈ Subgroup.normalizer (((posUnipotent D).map π : Subgroup Y) : Set Y))
    (hl1 : l ≠ 1) (hlp : ∃ k : ℕ, orderOf l = p ^ k) : p ∣ M := by
  rw [h.normalizer_map_posUnipotent] at hl
  obtain ⟨k, hk⟩ := hlp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hl1 (orderOf_eq_one_iff.1 (by simpa using hk))
  have h1 : p ∣ orderOf l := hk ▸ dvd_pow_self p hk0
  have h2 : orderOf l ∣ Nat.card ((borel D H).map π) :=
    Subgroup.orderOf_dvd_natCard ((borel D H).map π) hl
  exact dvd_of_dvd_card_map_borel h.ct h.extras h.pGroup π (fun t ht => h.pow_eq_one_of_mem_iSup ht)
    hp hp2 (h1.trans h2)

end Numerics

theorem critModel {Y : Type} [Group Y] [Finite Y] (hY : HasRkModel Y) (hZ : Subgroup.center Y = ⊥)
    (h1 : K518RkSL2) (h2 : K518RkSU3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (T : Sylow 2 Y)
    {P : Subgroup Y} (hP : IsMinOverBorel (⊤ : Subgroup Y) (T : Subgroup Y) P) {l : Y}
    (hl : l ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hl1 : l ≠ 1)
    (hlp : ∃ k : ℕ, orderOf l = p ^ k) (c : MulAut Y) (hc : ∃ k : ℕ, orderOf c = p ^ k)
    (hcT : (T : Subgroup Y).map c.toMonoidHom = T)
    (hcInn : c ∉ (pElementSubgroup 2 P).map (MulAut.conj : Y →* MulAut Y)) :
    2 ≤ CFSG.Open.pRank p
      ((pElementSubgroup 2 P).map (MulAut.conj : Y →* MulAut Y) ⊔ Subgroup.zpowers c) := by
  classical
  obtain ⟨K, _, _, D, n, H, π, M, hπ, hkind, hker, hMdvd, hcent⟩ := hY
  obtain ⟨π', hπ'surj, hkerπ', hTπ'⟩ := hπ.exists_conj_eq T
  have hπ' : BorelQuotient D n H π' M :=
    { ct := hπ.ct, extras := hπ.extras, pGroup := hπ.pGroup, surj := hπ'surj, odd := hπ.odd,
      torus_pow := hπ.torus_pow, ker_central := fun z hz => hπ.ker_central z (hkerπ' ▸ hz)
      ker_pow := fun z hz => hπ.ker_pow z (hkerπ' ▸ hz) }
  have hker' : ∀ i, π'.ker ⊓ rankOne D.rootGroup i = ⊥ := fun i => by
    rw [hkerπ']
    exact hker i
  rw [hTπ'] at hP hl hcT
  obtain ⟨i, hi⟩ := exists_eq_map_parJ hπ' hP
  have hPe : pElementSubgroup 2 P = (unipJ D {i}).map π' := by
    rw [hi]
    exact pElement_map_parJ hπ' {i}
  rw [hPe] at hcInn ⊢
  have hpM : p ∣ M := dvd_M_of_normalizer hπ' hp hp2 hl hl1 hlp
  have hpL : ∀ j, p ∣ Nat.card ↥(rankOne D.rootGroup j) := fun j => hpM.trans (hMdvd j)
  by_cases hmove : nodePerm hπ' c hcT i = i
  · have hcR : ((unipJ D {i}).map π').map c.toMonoidHom = (unipJ D {i}).map π' := by
      rw [map_unipJ_nodePerm hπ' c hcT, Set.image_singleton, hmove]
    exact caseA hπ' hZ i (hkind i) (hker' i) h1 h2 hp hp2 (hpL i) c hc hcR hcInn
  · exact caseB hπ' hZ hker' hp hp2 hpL hcent c hc hcT i hmove

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
