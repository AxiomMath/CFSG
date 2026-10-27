module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBSetting

import CFSG.Quasithin.Background.E1Amb
import CFSG.GroupTheory.PowMemSupOfPGroup
import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup

variable {Ω : Type} [Group Ω] [Finite Ω] {G : Subgroup Ω}

private theorem twoResidual_subgroupOf_bres {X N : Subgroup Ω} (hXN : X ≤ N) :
    (twoResidual X).subgroupOf N = twoResidual (X.subgroupOf N) := by
  have h1 : (twoResidual X).subgroupOf N =
      (twoResidual (⊤ : Subgroup X)).map (Subgroup.inclusion hXN) := by
    ext n
    rw [E1.twoResidual_eq_map_top X]
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyn⟩
      exact ⟨y, hy, Subtype.ext hyn⟩
    · rintro ⟨y, hy, hyn⟩
      exact ⟨y, hy, congrArg Subtype.val hyn⟩
  have h2 : (twoResidual (⊤ : Subgroup X)).map (Subgroup.inclusion hXN) =
      twoResidual (X.subgroupOf N) := by
    rw [E1.map_twoResidual, Subgroup.map_top, Subgroup.inclusion_range]
  rw [h1, h2]

omit [Finite Ω] in
private theorem autOn_eq_sup_bres {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) :
    autOn H W = autOn L W ⊔ autOn S W := by
  set C := G ⊓ Subgroup.centralizer (gomiV G : Set Ω) with hC
  have hLSH : L ⊔ S ≤ H := by rw [hset.eq_sup]; exact le_sup_left
  have hCH : C ≤ H := by rw [hset.eq_sup]; exact le_sup_right
  have hLSN : L ⊔ S ≤ Subgroup.normalizer (W : Set Ω) :=
    hLSH.trans hset.le_normalizer_W
  have hCN : C ≤ Subgroup.normalizer (W : Set Ω) := hCH.trans hset.le_normalizer_W
  have hLN : L ≤ Subgroup.normalizer (W : Set Ω) := le_sup_left.trans hLSN
  have hSN : S ≤ Subgroup.normalizer (W : Set Ω) := le_sup_right.trans hLSN
  have hCC : C ≤ Subgroup.centralizer (W : Set Ω) :=
    inf_le_right.trans (Subgroup.centralizer_le hset.le_gomiV)
  have h1 : autOn H W = autOn (L ⊔ S) W ⊔ autOn C W := by
    rw [hset.eq_sup, AutOn.autOn_sup_eq hLSN hCN]
  have h2 : autOn (L ⊔ S) W = autOn L W ⊔ autOn S W :=
    AutOn.autOn_sup_eq hLN hSN
  rw [h1, h2, AutOn.autOn_eq_bot_of_le_centralizer hCC, sup_bot_eq]

omit [Finite Ω] in
private theorem le_autOn_left_bres {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) (hS : IsSylowTwoOf S G)
    {M : Subgroup (MulAut ↥W)} (hMY : M ≤ autOn H W) (hMres : twoResidual M = M) :
    M ≤ autOn L W := by
  have hY : autOn H W = autOn L W ⊔ autOn S W := autOn_eq_sup_bres hset
  have hSH : S ≤ H := by rw [hset.eq_sup]; exact le_sup_right.trans le_sup_left
  have hSL : S ≤ Subgroup.normalizer (L : Set Ω) := hSH.trans hset.le_normalizer
  have hS2 : IsPGroup 2 (autOn S W) := AutOn.isPGroup_autOn hS.2.1
  have hSLnorm : autOn S W ≤
      Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) :=
    AutOn.autOn_le_normalizer_autOn hSL
  have hYnorm : autOn H W ≤ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) := by
    rw [hY]
    exact sup_le Subgroup.le_normalizer hSLnorm
  have hMnorm : M ≤ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) :=
    hMY.trans hYnorm
  have hNnorm : M ≤ Subgroup.normalizer
      (((M ⊓ autOn L W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W))) :=
    (le_inf Subgroup.le_normalizer hMnorm).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hle : twoResidual M ≤ M ⊓ autOn L W := by
    refine twoResidual_le_of_isTwoQuotient inf_le_left hNnorm ?_
    intro x hx
    have hxY : x ∈ autOn L W ⊔ autOn S W := by rw [← hY]; exact hMY hx
    obtain ⟨k, hk⟩ := exists_pow_prime_pow_mem_of_mem_sup hS2 hSLnorm hxY
    exact ⟨k, Subgroup.mem_inf.mpr ⟨M.pow_mem hx (2 ^ k), hk⟩⟩
  rw [hMres] at hle
  exact hle.trans inf_le_right

private noncomputable def preimage_bres (L W : Subgroup Ω)
    (M : Subgroup (MulAut ↥W)) : Subgroup Ω :=
  L ⊓ (M.comap (conjAct W)).map (Subgroup.normalizer (W : Set Ω)).subtype

omit [Finite Ω] in
private theorem mem_preimage_bres {L W : Subgroup Ω} {M : Subgroup (MulAut ↥W)}
    {x : Ω} (hxN : x ∈ Subgroup.normalizer (W : Set Ω)) :
    x ∈ preimage_bres L W M ↔ x ∈ L ∧ conjAct W ⟨x, hxN⟩ ∈ M := by
  rw [preimage_bres, Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hxL, ⟨n, hn, hnx⟩⟩
    have hxn : n = ⟨x, hxN⟩ := Subtype.ext hnx
    exact ⟨hxL, hxn ▸ hn⟩
  · rintro ⟨hxL, hxM⟩
    exact ⟨hxL, ⟨⟨x, hxN⟩, hxM, rfl⟩⟩

omit [Finite Ω] in
private theorem subgroupOf_preimage_bres {L W : Subgroup Ω} {M : Subgroup (MulAut ↥W)}
    (hLN : L ≤ Subgroup.normalizer (W : Set Ω)) :
    (preimage_bres L W M).subgroupOf L =
      (M.subgroupOf (autOn L W)).comap (CFSG.CGT.PushingUpLit.BHS6.actOnRange W L hLN) := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_preimage_bres (x := (x : Ω)) (hLN x.2),
    Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  simp only [x.2, true_and]
  change (conjAct W ⟨(x : Ω), hLN x.2⟩ ∈ M) ↔
    (((CFSG.CGT.PushingUpLit.BHS6.actOnRange W L hLN) x : ↥(autOn L W)) : MulAut ↥W) ∈ M
  rfl

omit [Finite Ω] in
private theorem subgroupOf_preimage_isSubnormal_bres {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) {M : Subgroup (MulAut ↥W)}
    (hMsub : (M.subgroupOf (autOn H W)).IsSubnormal) :
    ((preimage_bres L W M).subgroupOf L).IsSubnormal := by
  have hLH : L ≤ H := by rw [hset.eq_sup]; exact le_sup_left.trans le_sup_left
  have hLN : L ≤ Subgroup.normalizer (W : Set Ω) := hLH.trans hset.le_normalizer_W
  have hAutLH : autOn L W ≤ autOn H W := AutOn.autOn_mono hLH
  have hMsubL : (M.subgroupOf (autOn L W)).IsSubnormal :=
    isSubnormal_subgroupOf_of_le hAutLH hMsub
  rw [subgroupOf_preimage_bres hLN]
  exact Subgroup.IsSubnormal.comap (CFSG.CGT.PushingUpLit.BHS6.actOnRange W L hLN) hMsubL

omit [Finite Ω] in
private theorem autOn_preimage_bres {L W : Subgroup Ω} {M : Subgroup (MulAut ↥W)}
    (hML : M ≤ autOn L W) :
    autOn (preimage_bres L W M) W = M := by
  ext φ
  rw [AutOn.mem_autOn_iff]
  constructor
  · rintro ⟨n, hnK, hφ⟩
    obtain ⟨-, hM⟩ := (mem_preimage_bres (x := (n : Ω)) n.2).mp hnK
    rwa [hφ] at hM
  · intro hφ
    obtain ⟨n, hnL, hφn⟩ := AutOn.mem_autOn_iff.mp (hML hφ)
    exact ⟨n, (mem_preimage_bres (x := (n : Ω)) n.2).mpr ⟨hnL, hφn ▸ hφ⟩, hφn⟩

private theorem autOn_twoResidual_preimage_bres {L W : Subgroup Ω}
    {M : Subgroup (MulAut ↥W)} (hLN : L ≤ Subgroup.normalizer (W : Set Ω))
    (hML : M ≤ autOn L W) (hMres : twoResidual M = M) :
    autOn (twoResidual (preimage_bres L W M)) W = M := by
  have hKN : preimage_bres L W M ≤ Subgroup.normalizer (W : Set Ω) :=
    inf_le_left.trans hLN
  calc
    autOn (twoResidual (preimage_bres L W M)) W =
        ((twoResidual (preimage_bres L W M)).subgroupOf
          (Subgroup.normalizer (W : Set Ω))).map (conjAct W) := rfl
    _ = (twoResidual ((preimage_bres L W M).subgroupOf
          (Subgroup.normalizer (W : Set Ω)))).map (conjAct W) := by
          rw [twoResidual_subgroupOf_bres hKN]
    _ = twoResidual (((preimage_bres L W M).subgroupOf
          (Subgroup.normalizer (W : Set Ω))).map (conjAct W)) := by
          rw [E1.map_twoResidual]
    _ = twoResidual (autOn (preimage_bres L W M) W) := rfl
    _ = twoResidual M := by rw [autOn_preimage_bres hML]
    _ = M := hMres

theorem IsGomi410bSetting.exists_autOn_eq {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) (hS : IsSylowTwoOf S G) {M : Subgroup (MulAut ↥W)}
    (hMY : M ≤ autOn H W) (hMsub : (M.subgroupOf (autOn H W)).IsSubnormal)
    (hMres : twoResidual M = M) :
    ∃ B : Subgroup Ω, B ≤ L ∧ (B.subgroupOf G).IsSubnormal ∧ twoResidual B = B ∧
      autOn B W = M := by
  set K := preimage_bres L W M with hK
  have hLH : L ≤ H := by rw [hset.eq_sup]; exact le_sup_left.trans le_sup_left
  have hLN : L ≤ Subgroup.normalizer (W : Set Ω) := hLH.trans hset.le_normalizer_W
  have hML : M ≤ autOn L W := le_autOn_left_bres hset hS hMY hMres
  have hKsubL : (K.subgroupOf L).IsSubnormal :=
    subgroupOf_preimage_isSubnormal_bres hset hMsub
  have hKsubG : (K.subgroupOf G).IsSubnormal :=
    isSubnormal_subgroupOf_trans inf_le_left hset.le hKsubL hset.subnormal
  have hBK : twoResidual K ≤ K := twoResidual_le K
  have hBnorm : ((twoResidual K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr (le_normalizer_twoResidual K)
  have hBsubG : ((twoResidual K).subgroupOf G).IsSubnormal :=
    isSubnormal_subgroupOf_trans hBK (inf_le_left.trans hset.le) hBnorm.isSubnormal hKsubG
  refine ⟨twoResidual K, hBK.trans inf_le_left, hBsubG, twoResidual_twoResidual K, ?_⟩
  exact autOn_twoResidual_preimage_bres hLN hML hMres

end CFSG.GroupTheory
