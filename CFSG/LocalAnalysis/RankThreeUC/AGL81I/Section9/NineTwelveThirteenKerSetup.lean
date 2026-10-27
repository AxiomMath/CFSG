module

import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.SevenHull
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveFrattini
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveThreeGroupSub
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineElevenGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem mem_kerIn_iff_forall_conj {M K : Subgroup G} {x : G} :
    x ∈ kerIn M K ↔ x ∈ K ∧ ∀ k ∈ K, k * x * k⁻¹ ∈ M := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun k hk => ?_⟩
    have h1 := Subgroup.normalCore_le _ ((Subgroup.normalCore_normal _).conj_mem y hy ⟨k, hk⟩)
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h1)).1
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    intro b
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
      ⟨h b b.2, K.mul_mem (K.mul_mem b.2 hx) (K.inv_mem b.2)⟩)

theorem inf_le_kerIn_of_normal {M H K X : Subgroup G} (hKH : K ≤ H) (hXH : X ≤ H)
    (hX : (X.subgroupOf H).Normal) (hXM : X ≤ M) : K ⊓ X ≤ kerIn M K := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  rw [mem_kerIn_iff_forall_conj]
  rw [Subgroup.normal_subgroupOf_iff hXH] at hX
  exact ⟨hx.1, fun k hk => hXM (hX x k hx.2 (hKH hk))⟩

namespace NineSettingGen

variable [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem mem_centralizer_of_sevenElem (h : NineSettingGen G M p Q H E k) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R (relPPrimeCore p H)) {y : G}
    (hyN : y ∈ normalizer (R : Set G)) (hy : ∃ n : ℕ, y ^ 7 ^ n = 1) :
    y ∈ centralizer (R : Set G) := by
  by_contra hyC
  have hrk : CFSG.Open.pRank 3 R ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hR.le).trans
      (h.pRank_relPPrimeCore_le_three Nat.prime_three (by norm_num))
  rcases omegaOnePSub_of_pElement hR.isPGroup hrk (by norm_num : Nat.Prime 7) (by norm_num)
    (by norm_num) hyN hy hyC with ⟨h7, -⟩ | ⟨h7, -⟩ <;> norm_num at h7

theorem oPPrimeHull_seven_kSub_le (h : NineSettingGen G M p Q H E k) (hL : pLayerIn p H ≤ M)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf 3 R (relPPrimeCore p H)) :
    oPPrimeHull 7 (kSub p M H) ≤
      (kSub p M H ⊓ centralizer (R : Set G)) ⊔ (kSub p M H ⊓ relPPrimeCore p H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJK : oPPrimeHull 7 (kSub p M H) ≤ kSub p M H :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hgen : oPPrimeHull 7 (kSub p M H) ≤
      closure {x : G | x ∈ oPPrimeHull 7 (kSub p M H) ∧ ∃ n : ℕ, x ^ 7 ^ n = 1} := by
    refine (Subgroup.closure_le _).mpr fun x hx =>
      Subgroup.subset_closure ⟨Subgroup.subset_closure hx, ?_⟩
    obtain ⟨-, n, hn⟩ := hx
    exact ⟨n, by rw [← hn]; exact pow_orderOf_eq_one x⟩
  have h1 := le_inf_centralizer_sup_inf (p := 7) (q := 3) (H := H)
    (K := oPPrimeHull 7 (kSub p M H)) (N := relPPrimeCore p H) (R := R) (by norm_num)
    (hJK.trans (kSub_le p M H))
    (oPPrimeHull_subgroupOf_normal 7 (kSub_le p M H) (kSub_normal_of_le hL))
    (sSup_le fun _ hN => hN.1)
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      h.prime H) hR hgen
    (fun y _ hyN hy => h.mem_centralizer_of_sevenElem hR hyN hy)
  exact h1.trans (sup_le_sup (inf_le_inf_right _ hJK) (inf_le_inf_right _ hJK))

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
