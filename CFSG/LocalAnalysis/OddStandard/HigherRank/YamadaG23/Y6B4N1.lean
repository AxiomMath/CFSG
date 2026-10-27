module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31SylConj
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma card_jSub_of_le_S {s : Setting3 G L} (hS : HRSetting G L)
    (hZ : Odd (Nat.card ↥(center ↥L))) {X : Subgroup G} (hX : X ≤ s.fr.S) :
    Nat.card ↥(jSub L X) = Nat.card ↥X := by
  have hinj : Function.Injective (jOn L (s3_S_le_N s)) := s3_jOn_S_injective s hS hZ
  have hmap : jSub L X = (X.subgroupOf s.fr.S).map (jOn L (s3_S_le_N s)) := by
    ext α
    rw [mem_jSub L, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hxX, hxα⟩
      exact ⟨⟨x, hX hxX⟩, by rwa [Subgroup.mem_subgroupOf],
        actsAs_unique L (jOn_actsAs L (s3_S_le_N s) ⟨x, hX hxX⟩) hxα⟩
    · rintro ⟨t, ht, htα⟩
      rw [Subgroup.mem_subgroupOf] at ht
      exact ⟨t, ht, htα ▸ jOn_actsAs L (s3_S_le_N s) t⟩
  rw [hmap, Subgroup.card_map_of_injective hinj,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv]

private lemma card_ker_jOn_comp_le_two {s : Setting3 G L} {e : Setting3.Ext s}
    (hH : F33Hyp s e) {U : Subgroup G} (hUH : U ≤ s.H) :
    Nat.card ↥((jOn L (s3_H_le_N s hH.hS)).comp (Subgroup.inclusion hUH)).ker ≤ 2 := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hH.hS
  let j := jOn L (s3_H_le_N s hH.hS)
  let φ : ↥U →* MulAut (L ⧸ center L) := j.comp (Subgroup.inclusion hUH)
  show Nat.card ↥φ.ker ≤ 2
  have hker_le : ∀ x : φ.ker, ((x : ↥U) : G) ∈ zpowers s.t := by
    intro x
    have hx : j (Subgroup.inclusion hUH (x : ↥U)) = 1 := x.2
    have hxmem : Subgroup.inclusion hUH (x : ↥U) ∈ j.ker := MonoidHom.mem_ker.mpr hx
    rw [ker_jOn L (s3_H_le_N s hH.hS)] at hxmem
    have hxcen : ((x : ↥U) : G) ∈ centralizer (L : Set G) := by
      simpa using Subgroup.mem_subgroupOf.mp hxmem
    have hxcent : ((x : ↥U) : G) ∈ centIn s.H L :=
      Subgroup.mem_inf.mpr ⟨hUH (x : ↥U).2, hxcen⟩
    rwa [f3_centIn_H_L hH] at hxcent
  let ψ : φ.ker → ↥(zpowers s.t) := fun x => ⟨((x : ↥U) : G), hker_le x⟩
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : (ψ x).val = (ψ y).val := Subtype.ext_iff.mp hxy
    have h2 : ((x : ↥U) : G) = ((y : ↥U) : G) := h1
    exact Subtype.ext (Subtype.ext h2)
  calc Nat.card ↥φ.ker ≤ Nat.card ↥(zpowers s.t) :=
        Nat.card_le_card_of_injective ψ hψinj
    _ = orderOf s.t := Nat.card_zpowers s.t
    _ = 2 := s.t_order

theorem y6b_card_abelian_H_le {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    (hRT : s.R ≠ s.T) {U : Subgroup G} (hUH : U ≤ s.H) (hU : IsPGroup 2 ↥U)
    (hUc : IsMulCommutative ↥U) : Nat.card ↥U ≤ 32 := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hH.hS
  haveI : IsMulCommutative ↥U := hUc
  let φ : ↥U →* MulAut (L ⧸ center L) :=
    (jOn L (s3_H_le_N s hH.hS)).comp (Subgroup.inclusion hUH)
  haveI hφcomm : IsMulCommutative φ.range := inferInstance
  have hφp : IsPGroup 2 φ.range := by
    have htop : IsPGroup 2 (⊤ : Subgroup ↥U) := hU.of_equiv Subgroup.topEquiv.symm
    have h := htop.map φ
    rwa [MonoidHom.range_eq_map]
  have hSylow : IsSylowIn 2 ⊤ (jSub L s.T) := s3_jSub_T_isSylow s hH.hS hH.hOut hRT
  have hSσ : jSub L s.T = s.fr'.Sσ := s3_jSub_T s hH.hS hH.hOut hRT
  obtain ⟨γ, -, hγ⟩ := exists_conj_le_isSylowIn hSylow hφp le_top
  have hγSσ : conjSub γ φ.range ≤ s.fr'.Sσ := hγ.trans (le_of_eq hSσ)
  have hconjcomm : IsMulCommutative ↥(conjSub γ φ.range) := by
    rw [conjSub]
    infer_instance
  have hconj16 : Nat.card ↥(conjSub γ φ.range) ≤ 16 :=
    s.facts.2.2.2.2.1.2.2.2.2.1 (conjSub γ φ.range) hγSσ hconjcomm
  have hconjcard : Nat.card ↥(conjSub γ φ.range) = Nat.card ↥φ.range := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj γ).injective]
  have hrange16 : Nat.card ↥φ.range ≤ 16 := by
    rw [← hconjcard]
    exact hconj16
  have hker : Nat.card ↥φ.ker ≤ 2 := card_ker_jOn_comp_le_two hH hUH
  calc Nat.card ↥U = Nat.card φ.ker * Nat.card φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ 2 * 16 := Nat.mul_le_mul hker hrange16
    _ = 32 := by norm_num

theorem y6b_card_cent_g_le (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T)
    {U : Subgroup G} (hUH : U ≤ c.s.H) (hUg : U ≤ centralizer ({c.g} : Set G))
    (hU : IsPGroup 2 ↥U) : Nat.card ↥U ≤ 32 := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hH.hS
  let σ : MulAut (L ⧸ center L) := c.s.fr'.σ
  let I : Subgroup (MulAut (L ⧸ center L)) := innerAut (L ⧸ center L)
  let φ : ↥U →* MulAut (L ⧸ center L) :=
    (jOn L (s3_H_le_N c.s hH.hS)).comp (Subgroup.inclusion hUH)
  have hgH : c.g ∈ c.s.H := c.s.sylow_T.1 (c.g_spec hRT).1
  have hjg : jOn L (s3_H_le_N c.s hH.hS) ⟨c.g, hgH⟩ = σ :=
    actsAs_unique L (jOn_actsAs L (s3_H_le_N c.s hH.hS) ⟨c.g, hgH⟩) (c.g_spec hRT).2.2.1
  have hφp : IsPGroup 2 φ.range := by
    have htop : IsPGroup 2 (⊤ : Subgroup ↥U) := hU.of_equiv Subgroup.topEquiv.symm
    have h := htop.map φ
    rwa [MonoidHom.range_eq_map]
  have hrange_le_cen : φ.range ≤ Subgroup.centralizer ({σ} : Set (MulAut (L ⧸ center L))) := by
    rintro α ⟨u, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    rw [Set.mem_singleton_iff] at hβ
    subst hβ
    have hcomm : σ * φ u = φ u * σ := by
      have hu : c.g * (u : G) = (u : G) * c.g :=
        Subgroup.mem_centralizer_iff.mp (hUg u.2) c.g (Set.mem_singleton c.g)
      have hmem : (⟨c.g, hgH⟩ : ↥c.s.H) * ⟨(u : G), hUH u.2⟩ =
          ⟨(u : G), hUH u.2⟩ * ⟨c.g, hgH⟩ := by
        apply Subtype.ext
        exact hu
      have h := congrArg (jOn L (s3_H_le_N c.s hH.hS)) hmem
      simp only [map_mul] at h
      rw [hjg] at h
      exact h
    exact hcomm
  let Q : Subgroup (MulAut (L ⧸ center L)) := φ.range ⊓ I
  have hQp : IsPGroup 2 Q := hφp.to_le inf_le_left
  have hQ_le : Q ≤ centEl I σ := by
    intro α hα
    rw [Subgroup.mem_inf] at hα
    exact Subgroup.mem_inf.mpr ⟨hα.2, hrange_le_cen hα.1⟩
  have hF'sylow : IsSylowIn 2 (centEl I σ) c.s.fr'.F := c.s.facts.2.2.2.2.2.2.1.2
  obtain ⟨γ, -, hγ⟩ := exists_conj_le_isSylowIn hF'sylow hQp hQ_le
  have hF'card : Nat.card ↥c.s.fr'.F = 8 := by
    rw [← s3_jSub_F hH.hS hH.hZ c.s,
      card_jSub_of_le_S hH.hS hH.hZ ((s3_F_le_A c.s).trans (s3_A_le_S c.s)),
      (s3_isE3_F hH.hS hH.hZ hH.hOut c.s).2]
    norm_num
  have hQ8 : Nat.card ↥Q ≤ 8 := by
    have hconjcard : Nat.card ↥(conjSub γ Q) = Nat.card ↥Q := by
      rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj γ).injective]
    rw [← hconjcard]
    calc Nat.card ↥(conjSub γ Q) ≤ Nat.card ↥c.s.fr'.F := Subgroup.card_le_of_le hγ
      _ = 8 := hF'card
  have hInormal : I.Normal := by
    constructor
    rintro _ ⟨g, rfl⟩ β
    exact ⟨β g, by ext x; simp [MulAut.conj_apply]⟩
  haveI := hInormal
  have hQrel : Q.relIndex φ.range ≤ 2 := by
    have hdvd : I.relIndex φ.range ∣ 2 := by
      rw [← hH.hOut]
      exact Subgroup.relIndex_dvd_index_of_normal (H := I) (K := φ.range)
    calc Q.relIndex φ.range = I.relIndex φ.range :=
          Subgroup.inf_relIndex_left (H := φ.range) (K := I)
      _ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hcard_range : Nat.card ↥φ.range = Q.relIndex φ.range * Nat.card ↥Q := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := φ.range)
    rw [inf_eq_left.mpr (show Q ≤ φ.range from inf_le_left)] at h
    exact h.symm
  have hrange16 : Nat.card ↥φ.range ≤ 16 := by
    rw [hcard_range]
    calc Q.relIndex φ.range * Nat.card ↥Q ≤ 2 * 8 := Nat.mul_le_mul hQrel hQ8
      _ = 16 := by norm_num
  have hker : Nat.card ↥φ.ker ≤ 2 := card_ker_jOn_comp_le_two hH hUH
  calc Nat.card ↥U = Nat.card φ.ker * Nat.card φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ 2 * 16 := Nat.mul_le_mul hker hrange16
    _ = 32 := by norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
