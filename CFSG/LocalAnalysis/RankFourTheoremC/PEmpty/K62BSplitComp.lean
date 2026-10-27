module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitBasic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitLocal
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit

open CFSG CFSG.LocalCores CFSG.Open Subgroup

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x : Y}

theorem isSylowOf_inf_subnormal {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) {H : Subgroup X}
    (hH : H.IsSubnormal) : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ H) H := by
  induction hH with
  | top => simpa using hP
  | step H K hHK _ hN ih =>
    have h1 := ih.inf_of_le_normalizer hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN)
    rwa [inf_assoc, inf_eq_right.mpr hHK] at h1

theorem simple_of_centre {K : Type*} [Group K] (hq : CFSG.IsQuasisimple K) (hZ : center K = ⊥) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨-, hs, a, b, hab⟩ := hq
  let e : K ⧸ center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun h' => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h']

theorem sylow_comp (h : SplitCfg p P x) (C : ComponentIndex Y) :
    CFSG.ABGLocalTools.IsSylowOf p (P ⊓ C.1) C.1 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact isSylowOf_inf_subnormal h.sylow C.2.2

theorem simple_comp (h : SplitCfg p P x) (C : ComponentIndex Y) :
    IsSimpleGroup C.1 ∧ ∃ a b : C.1, a * b ≠ b * a :=
  simple_of_centre C.2.1 (h.centre C)

theorem catalog_comp (h : SplitCfg p P x) (C : ComponentIndex Y) : IsCatalogGroup C.1 :=
  h.catalog.simple_subgroup C.1 (simple_comp h C).1 (simple_comp h C).2

theorem exists_sylow_comp (h : SplitCfg p P x) (C : ComponentIndex Y) :
    ∃ T : Sylow p C.1, (T : Subgroup C.1) = (P ⊓ C.1).subgroupOf C.1 ∧ IsCyclic T := by
  obtain ⟨T, hT⟩ := (sylow_comp h C).exists_sylow_eq_subgroupOf
  refine ⟨T, hT, ?_⟩
  have h1 : IsCyclic ↥((P ⊓ C.1).subgroupOf C.1) :=
    (MulEquiv.isCyclic (subgroupOfEquivOfLe (inf_le_right : P ⊓ C.1 ≤ C.1))).mpr (h.cyclic C)
  rw [← hT] at h1
  exact h1

theorem dvd_inf_comp (h : SplitCfg p P x) (C : ComponentIndex Y) : p ∣ Nat.card ↥(P ⊓ C.1) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  rw [(sylow_comp h C).card_eq]
  have h1 : 1 ≤ (Nat.card C.1).factorization p := by
    have hn : Nat.card C.1 ≠ 0 := Nat.card_pos.ne'
    exact (Nat.Prime.dvd_iff_one_le_factorization h.prime hn).mp (h.dvd C)
  exact dvd_pow_self p (by omega)

theorem card_le_comp (h : SplitCfg p P x) (C : ComponentIndex Y) {F : Subgroup Y} (hFC : F ≤ C.1)
    (hF : IsElemAbelian p F) : Nat.card F ≤ p := by
  obtain ⟨T, -, hT⟩ := exists_sylow_comp h C
  have h1 := card_le_of_le_sylow_cyclic h.prime T hT (F := F.subgroupOf C.1)
    (hF.subgroupOf C.1)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hFC).toEquiv] at h1

theorem pRank_comp_le_one (h : SplitCfg p P x) (C : ComponentIndex Y) :
    CFSG.Open.pRank p (⊤ : Subgroup C.1) ≤ 1 := by
  obtain ⟨T, -, hT⟩ := exists_sylow_comp h C
  exact pRank_le_one_of_cyclic_sylow h.prime T hT

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit
