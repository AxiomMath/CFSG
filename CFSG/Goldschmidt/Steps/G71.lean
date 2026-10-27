module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Walter.Bender1970.S5.Tools
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.GorensteinWalter CFSG.Walter

namespace G71

variable {G : Type} [Group G]

theorem isNormalIn_map_subtype (X : Subgroup G) (N : Subgroup X) [hN : N.Normal] :
    IsNormalIn (N.map X.subtype) X := by
  refine ⟨Subgroup.map_subtype_le N, fun h hh k hk => ?_⟩
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hk
  exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hN.conj_mem n hn ⟨h, hh⟩, rfl⟩

theorem normalClosureIn_isNormalIn (H A : Subgroup G) : IsNormalIn (normalClosureIn H A) H :=
  isNormalIn_map_subtype H _

theorem normalClosureIn_mono {X Y : Subgroup G} (A : Subgroup G) (hXY : X ≤ Y) :
    normalClosureIn X A ≤ normalClosureIn Y A := by
  have hN := normalClosureIn_isNormalIn Y A
  have : ((normalClosureIn Y A).comap X.subtype).Normal :=
    ⟨fun n hn x => hN.2 x (hXY x.2) n hn⟩
  rw [normalClosureIn, Subgroup.map_le_iff_le_comap]
  refine Subgroup.normalClosure_le_normal fun x hx => ?_
  exact ⟨⟨x, hXY x.2⟩, Subgroup.subset_normalClosure
    (show (⟨x, hXY x.2⟩ : Y) ∈ A.subgroupOf Y from hx), rfl⟩

theorem derivedSeries_add_eq {X : Type*} [Group X] {n : ℕ}
    (hn : derivedSeries X (n + 1) = derivedSeries X n) (k : ℕ) :
    derivedSeries X (n + k) = derivedSeries X n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← add_assoc, derivedSeries_succ, ih, ← derivedSeries_succ, hn]

theorem map_derivedSeries_le_of_le {K L : Subgroup G} (hKL : K ≤ L) (m : ℕ) :
    (derivedSeries K m).map K.subtype ≤ (derivedSeries L m).map L.subtype := by
  have h : K.subtype = L.subtype.comp (Subgroup.inclusion hKL) := rfl
  rw [h, ← Subgroup.map_map]
  exact Subgroup.map_mono (map_derivedSeries_le_derivedSeries _ m)

variable [Finite G]

theorem inf_centralizer_le_fittingSubgroupOf (K : Subgroup G) :
    K ⊓ Subgroup.centralizer (K : Set G) ≤ CFSG.fittingSubgroupOf K := by
  refine le_fittingSubgroupOf_of_isNormalIn_nilpotent inf_le_left ⟨inf_le_left, ?_⟩ ?_
  · intro k hk z hz
    have hzk : k * z = z * k := (Subgroup.mem_centralizer_iff.mp hz.2) k hk
    have : k * z * k⁻¹ = z := by rw [hzk, mul_inv_cancel_right]
    rw [this]
    exact hz
  · have : IsMulCommutative (K ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :=
      ⟨⟨fun x y => Subtype.ext ((Subgroup.mem_centralizer_iff.mp y.2.2) x x.2.1)⟩⟩
    exact CommGroup.isNilpotent

theorem componentLayerOf_le_sup_centralizer {K H : Subgroup G} (hKH : IsNormalIn K H) :
    componentLayerOf H ≤ componentLayerOf K ⊔ Subgroup.centralizer (K : Set G) := by
  refine sSup_le fun L hL => ?_
  rcases fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf hKH.1
      (isSubnormal_subgroupOf_of_isNormalIn hKH) hL with h | h
  · exact (le_componentLayerOf_of_isComponentOf (isComponentOf_of_le hL h hKH.1)).trans
      le_sup_left
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans le_sup_right

theorem le_componentLayerOf_of_isNormalIn {K H D : Subgroup G} [Group.IsPerfect D]
    (hKH : IsNormalIn K H) (hDK : D ≤ K) (hDF : D ≤ generalizedFittingSubgroupOf H) :
    D ≤ componentLayerOf K := by
  have hDE : D ≤ componentLayerOf H := le_componentLayerOf_of_le_generalizedFittingSubgroupOf hDF
  have hEK : componentLayerOf K ≤ K := (componentLayerOf_isNormalIn K).1
  refine le_componentLayerOf_of_le_generalizedFittingSubgroupOf fun d hd => ?_
  obtain ⟨f, hf, e, he, rfl⟩ := mem_sup_decompose_of_centralizes
    (componentLayerOf_le_sup_centralizer hKH (hDE hd)) (Subgroup.centralizer_le hEK)
  have heK : e ∈ K := by
    have : e = f⁻¹ * (f * e) := by group
    rw [this]
    exact K.mul_mem (K.inv_mem (hEK hf)) (hDK hd)
  exact (generalizedFittingSubgroupOf K).mul_mem (Subgroup.mem_sup_right hf)
    (Subgroup.mem_sup_left (inf_centralizer_le_fittingSubgroupOf K ⟨heK, he⟩))

theorem le_centralizer_oddCoreOf_fittingSubgroupOf {K H D : Subgroup G} (hKH : IsNormalIn K H)
    (hD : ∀ q : ℕ, q.Prime → q ≠ 2 → D ≤ Subgroup.centralizer (qCoreOf H q : Set G)) :
    D ≤ Subgroup.centralizer
      (CFSG.Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf K) : Set G) := by
  set F := CFSG.fittingSubgroupOf K with hFdef
  set Y := CFSG.Goldschmidt.oddCoreOf F with hYdef
  have hYF : IsNormalIn Y F := isNormalIn_map_subtype F (goldschmidtOddCore F)
  have hFK : IsNormalIn F K := fittingSubgroupOf_isNormalIn K
  have hYodd : Odd (Nat.card Y) := by
    rw [hYdef, CFSG.Goldschmidt.oddCoreOf, Subgroup.card_map_of_injective F.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card F
  have hYnil : Group.IsNilpotent Y :=
    isNilpotent_of_le (CFSG.fittingSubgroupOf_isNilpotent K) hYF.1
  have hYY : Y ≤ CFSG.fittingSubgroupOf Y :=
    le_fittingSubgroupOf_of_isNormalIn_nilpotent le_rfl
      ⟨le_rfl, fun h hh k hk => Y.mul_mem (Y.mul_mem hh hk) (Y.inv_mem hh)⟩ hYnil
  rw [Subgroup.le_centralizer_iff]
  refine hYY.trans ?_
  rw [(show CFSG.fittingSubgroupOf Y = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf Y)]
  refine iSup_le fun q => ?_
  have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  have hq2 : q.1.1 ≠ 2 := by
    intro h2
    have hdvd : q.1.1 ∣ Nat.card Y := Nat.dvd_of_mem_primeFactors q.1.2
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hYodd) (even_iff_two_dvd.mpr hdvd)
  refine (qCoreOf_le_qCoreOf_of_isNormalIn Y F _ hYF).trans
    ((qCoreOf_le_qCoreOf_of_isNormalIn F K _ hFK).trans
      ((qCoreOf_le_qCoreOf_of_isNormalIn K H _ hKH).trans ?_))
  rw [← Subgroup.le_centralizer_iff]
  exact hD _ hq hq2

end G71

open G71 in
theorem G71_of (h312 : S_G312) (h64 : S_G64) (h31 : S_G31) : S_G71 := by
  intro G _ _ S A hGS h8 a haA ha1 H hH
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hGS.elem.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
  have hAH : A ≤ H := hAC.trans (centralizer_le_of_mem_benderM hH)
  obtain ⟨g, hle, hS⟩ := hGS.sstar H (isCoatom_of_mem_benderM hH).1
  rw [inf_of_le_left hAH] at hle
  have hAg : A = conjSub g A := Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  rw [← hAg, inf_of_le_left hAH] at hS
  have hrk : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (qCoreOf H p) ≤ 2 :=
    (h64 G S A hGS a haA ha1 H hH).2.resolve_right (by omega)
  set K := normalClosureIn H A with hKdef
  have hKH : IsNormalIn K H := normalClosureIn_isNormalIn H A
  obtain ⟨n, hn⟩ := exists_derivedSeries_succ_eq K
  refine ⟨n, ?_⟩
  set D := (derivedSeries K n).map K.subtype with hDdef
  have : Group.IsPerfect (derivedSeries K n) :=
    Subgroup.isPerfect_iff.mpr (by rw [← derivedSeries_succ, hn])
  have : Group.IsPerfect D := Group.IsPerfect.map _
  have hDK : D ≤ K := Subgroup.map_subtype_le _
  have hDp : ∀ p : ℕ, p.Prime → p ≠ 2 → D ≤ Subgroup.centralizer (qCoreOf H p : Set G) := by
    intro p hp hp2
    obtain ⟨m, hm⟩ := (h312 G H A hS p hp hp2 (hrk p hp hp2)).1
    calc D = (derivedSeries K (n + m)).map K.subtype := by rw [derivedSeries_add_eq hn]
      _ ≤ (derivedSeries (K ⊔ CFSG.Goldschmidt.oddCoreOf H : Subgroup G) (n + m)).map
          (K ⊔ CFSG.Goldschmidt.oddCoreOf H).subtype := map_derivedSeries_le_of_le le_sup_left _
      _ ≤ (derivedSeries (K ⊔ CFSG.Goldschmidt.oddCoreOf H : Subgroup G) m).map
          (K ⊔ CFSG.Goldschmidt.oddCoreOf H).subtype :=
        Subgroup.map_mono (derivedSeries_antitone _ (Nat.le_add_left m n))
      _ ≤ Subgroup.centralizer (qCoreOf H p : Set G) := hm
  have hDF : D ≤ generalizedFittingSubgroupOf H := fun x hx =>
    (h31 G H A hS).2 ⟨hDK hx, le_centralizer_oddCoreOf_fittingSubgroupOf hKH hDp hx⟩
  exact le_componentLayerOf_of_isNormalIn hKH hDK hDF

end CFSG.Goldschmidt
