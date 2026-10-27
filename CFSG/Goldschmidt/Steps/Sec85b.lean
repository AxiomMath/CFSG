module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem componentLayerOf_le_centralizer (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a) :
    componentLayerOf H ≤ Subgroup.centralizer (A : Set G) := by
  have hAH : A ≤ H := hset.le.trans (le_of_mem_benderM hset h4 ha hH)
  obtain ⟨hQ, -⟩ := eq_oddCoreOf_sup hset h4 ha ha1 hH
  have hEQ := componentLayerOf_centralizes_solvable_of_le_normalizer H _
    (normalClosureIn_le_self H A) (isSolvable_of_eq_oddCoreOf_sup hset.elem.1 hQ)
    ((componentLayerOf_isNormalIn H).1.trans (le_normalizer_normalClosureIn H A))
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hEQ).trans
    (Subgroup.centralizer_le (le_normalClosureIn hAH))

theorem isCyclic_qCoreOf_centralizer (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a b : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1) {H : Subgroup G}
    (hHa : H = Subgroup.centralizer ({a} : Set G))
    (hcyc : ∀ q : ℕ, q.Prime → q ≠ 2 → IsCyclic (qCoreOf H q)) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) : IsCyclic (qCoreOf (Subgroup.centralizer ({b} : Set G)) q) := by
  obtain ⟨n, -, hn⟩ := exists_conj_eq hset h4 ha hb ha1 hb1
  have hHbH : Subgroup.centralizer ({b} : Set G) = H.map (MulAut.conj n).toMonoidHom := by
    rw [← hn, ← Walter.map_conj_centralizer_singleton, ← hHa]
  have := hcyc q hq hq2
  have h1 : qCoreOf (H.map (MulAut.conj n).toMonoidHom) q =
      (qCoreOf H q).map (MulAut.conj n).toMonoidHom := qCoreOf_conjugateSubgroup H n q
  rw [hHbH, h1]
  exact isCyclic_map_conj n

theorem componentLayerOf_eq_bot (h81 : S_G81) (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a)
    (hcyc : ∀ q : ℕ, q.Prime → q ≠ 2 → IsCyclic (qCoreOf H q)) : componentLayerOf H = ⊥ := by
  have hsimple := hset.isSimpleGroup
  have hHa := (h81 G S A hset h4 a ha ha1 H hH).1
  have hCH : Subgroup.centralizer (A : Set G) ≤ H :=
    hHa ▸ Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)
  have hEA := componentLayerOf_le_centralizer hset h4 ha ha1 hH
  have hNE : ∀ b ∈ A, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.normalizer (componentLayerOf H : Set G) := by
    intro b hb hb1
    set Hb := Subgroup.centralizer ({b} : Set G) with hHbdef
    have hHb := centralizer_mem_benderM hset h4 ha ha1 hb hb1 hH hHa
    set X := oddCoreOf Hb with hX
    have hXodd := odd_card_oddCoreOf Hb
    have hXsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hXodd
    have hXn : IsNormalIn X Hb := ⟨oddCoreOf_le Hb, fun h hh y hy =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreOf Hb hh) y).mp hy⟩
    have hEX : componentLayerOf H ≤ Subgroup.centralizer (X : Set G) := by
      refine sSup_le fun L hL => ?_
      have hLHb : L ≤ Hb := ((le_sSup hL).trans hEA).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
      have hLL := G73.commutator_self_of_isComponentOf hL
      have hLq : ∀ q : ℕ, q.Prime → q ≠ 2 →
          L ≤ Subgroup.centralizer (qCoreOf Hb q : Set G) := fun q hq hq2 => by
        have := isCyclic_qCoreOf_centralizer hset h4 ha ha1 hb hb1 hHa hcyc hq hq2
        exact hLL.symm.le.trans (commutator_le_centralizer_of_isCyclic
          (hLHb.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in Hb q))))
      have hLF : L ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf X : Set G) := by
        rw [Subgroup.le_centralizer_iff, (show CFSG.fittingSubgroupOf X = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf X)]
        refine iSup_le fun q => ?_
        have hq := Nat.prime_of_mem_primeFactors q.1.2
        have hq2 : q.1.1 ≠ 2 := fun h => by
          have hdvd := Nat.dvd_of_mem_primeFactors q.1.2
          rw [h] at hdvd
          exact hXodd.not_two_dvd_nat hdvd
        exact (qCoreOf_le_qCoreOf_of_isNormalIn X Hb q.1.1 hXn).trans
          (Subgroup.le_centralizer_iff.mp (hLq _ hq hq2))
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (commutator_eq_bot_of_le_centralizer_fitting hXsolv
          (hLHb.trans (le_normalizer_oddCoreOf Hb)) hLL hLF)
    refine (eq_oddCoreOf_sup hset h4 hb hb1 hHb).2.le.trans (sup_le ?_ ?_)
    · exact (Subgroup.le_centralizer_iff.mp hEX).trans (Subgroup.centralizer_le_normalizer _)
    · exact hCH.trans (le_normalizer_of_isNormalIn (componentLayerOf_isNormalIn H))
  have htop : Subgroup.normalizer (componentLayerOf H : Set G) = ⊤ := by
    by_contra hne
    exact false_of_centralizer_le hset hne hNE
  have : (componentLayerOf H).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (componentLayerOf H) with h | h
  · exact h
  · exact absurd (top_le_iff.mp (h ▸ (componentLayerOf_isNormalIn H).1))
      (Walter.ne_top_of_mem_benderM hH)

end CFSG.Goldschmidt.Sec8
