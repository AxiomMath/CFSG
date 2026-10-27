module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinNorm
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Assembly

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Claim

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G} {Ki KP R2 : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_centralizer_of {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, BenderBranch.conjugate_centralizer,
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hg]

theorem Ident2519.R_le_normalizer_R2 (hid : Ident2519 N t i Ki KP R2) :
    Rgrp2519 N i ≤ Subgroup.normalizer (R2 : Set G) := by
  have hn : (R2.subgroupOf (Rgrp2519 N i)).Normal := Subgroup.normal_of_index_eq_two hid.R2_index
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hid.R2_le).mp hn

theorem Ident2519.hyp_of_mem_R2 (hid : Ident2519 N t i Ki KP R2) {r : G} (hr : r ∈ R2) (hr1 : r ≠ 1)
    (hr2 : r ^ 2 = 1) : Hyp2519 N r :=
  ⟨(hid.R2_le hr).2, hr1, hr2, hid.R2_not_comp r hr hr1 hr2⟩

theorem Ident2519.claim (hid : Ident2519 N t i Ki KP R2) (h : Lv2518 N t zK) (hi : Hyp2519 N i)
    (hbig : 4 < Nat.card (Rgrp2519 N i))
    (M1 : ∀ j : G, Hyp2519 N j → Nat.card (Rgrp2519 N j) ≤ Nat.card (Rgrp2519 N i))
    (M2 : ∀ j : G, Hyp2519 N j → Nat.card (Rgrp2519 N j) = Nat.card (Rgrp2519 N i) →
      Nat.card ↥(N.S ⊓ Subgroup.centralizer ({j} : Set G)) ≤
        Nat.card ↥(N.S ⊓ Subgroup.centralizer ({i} : Set G))) :
    ∀ n ∈ N.S, n ∈ Subgroup.normalizer (N.K : Set G) → n * i = i * n := by
  intro n hnS hnK
  by_contra hn
  have hS2 : IsPGroup 2 N.S := N.tuple.sylow.isPGroup
  have hCiK : ∀ c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G),
      c ∈ Subgroup.normalizer (N.K : Set G) := fun c hc =>
    hid.mem_normalizer_K_of_commute h hi hc.1 (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
  have hRn := hid.R_le_normalizer_R2
  by_cases hA : N.S ⊓ Subgroup.centralizer (N.K : Set G) ≤ N.S ⊓ Subgroup.centralizer ({i} : Set G)
  ·
    have hRCs : Rgrp2519 N i = N.S ⊓ Subgroup.centralizer (N.K : Set G) := inf_eq_right.mpr hA
    have hCiNK : N.S ⊓ Subgroup.centralizer ({i} : Set G) <
        N.S ⊓ Subgroup.normalizer (N.K : Set G) := by
      refine lt_of_le_of_ne (fun c hc => ⟨hc.1, hCiK c hc⟩) fun e => ?_
      have hmem : n ∈ N.S ⊓ Subgroup.normalizer (N.K : Set G) := ⟨hnS, hnK⟩
      rw [← e] at hmem
      exact hn (Subgroup.mem_centralizer_singleton_iff.mp hmem.2)
    have hNK2 : IsPGroup 2 ↥(N.S ⊓ Subgroup.normalizer (N.K : Set G)) := hS2.to_le inf_le_left
    obtain ⟨s, hsNK, hsCi, hs2⟩ := exists_mem_normalizer_not_mem_sq_mem hNK2 hCiNK
    have hsS : s ∈ N.S := hsNK.1.1
    have hsK : s ∈ Subgroup.normalizer (N.K : Set G) := hsNK.1.2
    have hsRn : s ∈ Subgroup.normalizer (Rgrp2519 N i : Set G) := by
      rw [hRCs]
      exact mem_normalizer_inf' (Subgroup.le_normalizer hsS) (mem_normalizer_centralizer_of hsK)
    have hWS : N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊔ Subgroup.zpowers s ≤ N.S :=
      sup_le inf_le_left ((Subgroup.zpowers_le).mpr hsS)
    have hW : IsPGroup 2 ↥(N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊔ Subgroup.zpowers s) :=
      hS2.to_le hWS
    rcases exists_central_involution_or_card_le_four hW hid.R2_le inf_le_left hid.R2_index
        (fun c hc => hid.R2_norm hA hCiK M2 ⟨n, ⟨hnS, hnK⟩, hn⟩ c hc (hCiK c hc)) hsNK.2 hsRn hs2 with hle | ⟨r, hr, hr1, hr2, hc⟩
    · omega
    · have hHr := hid.hyp_of_mem_R2 hr hr1 hr2
      have hWr : N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊔ Subgroup.zpowers s ≤
          N.S ⊓ Subgroup.centralizer ({r} : Set G) :=
        fun w hw => ⟨hWS hw, Subgroup.mem_centralizer_singleton_iff.mpr (hc w hw)⟩
      have hCsr : N.S ⊓ Subgroup.centralizer (N.K : Set G) ≤
          N.S ⊓ Subgroup.centralizer ({r} : Set G) :=
        fun w hw => hWr (Subgroup.mem_sup_left (hA hw))
      have hRr : Rgrp2519 N r = N.S ⊓ Subgroup.centralizer (N.K : Set G) :=
        inf_eq_right.mpr hCsr
      have hcard : Nat.card (Rgrp2519 N r) = Nat.card (Rgrp2519 N i) := by rw [hRr, hRCs]
      have h2 := M2 r hHr hcard
      have hlt : N.S ⊓ Subgroup.centralizer ({i} : Set G) <
          N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊔ Subgroup.zpowers s := by
        refine lt_of_le_of_ne le_sup_left fun e => hsCi ?_
        rw [e]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
      have h3 := Subgroup.card_lt_of_lt hlt
      have h4 := Subgroup.card_le_of_le hWr
      omega
  ·
    have hRlt : Rgrp2519 N i < N.S ⊓ Subgroup.centralizer (N.K : Set G) :=
      lt_of_le_of_ne inf_le_right fun e => hA (e.symm.le.trans inf_le_left)
    have hCs2 : IsPGroup 2 ↥(N.S ⊓ Subgroup.centralizer (N.K : Set G)) := hS2.to_le inf_le_left
    obtain ⟨s, hs, hsR, hs2⟩ := exists_mem_normalizer_not_mem_sq_mem hCs2 hRlt
    have hsS : s ∈ N.S := hs.1.1
    have hsCs : s ∈ N.S ⊓ Subgroup.centralizer (N.K : Set G) := hs.1
    have hWS : Rgrp2519 N i ⊔ Subgroup.zpowers s ≤ N.S :=
      sup_le (Rgrp2519_le_S N i) ((Subgroup.zpowers_le).mpr hsS)
    have hW : IsPGroup 2 ↥(Rgrp2519 N i ⊔ Subgroup.zpowers s) := hS2.to_le hWS
    rcases exists_central_involution_or_card_le_four hW hid.R2_le le_rfl hid.R2_index hRn hs.2
        hs.2 hs2 with hle | ⟨r, hr, hr1, hr2, hc⟩
    · omega
    · have hHr := hid.hyp_of_mem_R2 hr hr1 hr2
      have hWr : Rgrp2519 N i ⊔ Subgroup.zpowers s ≤ Rgrp2519 N r := fun w hw =>
        ⟨⟨hWS hw, Subgroup.mem_centralizer_singleton_iff.mpr (hc w hw)⟩,
          sup_le inf_le_right ((Subgroup.zpowers_le).mpr hsCs) hw⟩
      have hlt : Rgrp2519 N i < Rgrp2519 N i ⊔ Subgroup.zpowers s := by
        refine lt_of_le_of_ne le_sup_left fun e => hsR ?_
        rw [e]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
      have h3 := Subgroup.card_lt_of_lt hlt
      have h4 := Subgroup.card_le_of_le hWr
      have h5 := M1 r hHr
      omega

end Claim

end CFSG.QuasithinUnique
