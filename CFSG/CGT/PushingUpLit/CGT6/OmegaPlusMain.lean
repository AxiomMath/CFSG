module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusStar
public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusSetup
public import CFSG.CGT.PushingUpLit.CGT6.EmbLayer

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.ComponentClassification CFSG.RankThree.PartOne CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {V : Type} [CommGroup V] {G Y D B : Subgroup (MulAut V)} {n : ℕ}

theorem PlusSide.dg (hP : PlusSide G Y D B n) : D ≤ G := hP.dy.trans hP.yg

theorem PlusSide.bg (hP : PlusSide G Y D B n) : B ≤ G := hP.by_.trans hP.yg

theorem PlusSide.center_subgroupOf (hP : PlusSide G Y D B n) :
    Subgroup.center ↥(B.subgroupOf G) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz1 : (z : ↥G).1 = 1 := by
    refine hP.eq_one_of_central (Subgroup.mem_subgroupOf.mp z.2) fun b hb => ?_
    have h := Subgroup.mem_center_iff.mp hz ⟨⟨b, hP.bg hb⟩, Subgroup.mem_subgroupOf.mpr hb⟩
    exact (congrArg (fun w : ↥(B.subgroupOf G) => (w : ↥G).1) h).symm
  exact Subtype.ext (Subtype.ext hz1)

theorem PlusSide.inf_centralizer_subgroupOf (hP : PlusSide G Y D B n) :
    B.subgroupOf G ⊓ Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxB, hxC⟩
  rw [Subgroup.mem_bot]
  have hx1 : (x : MulAut V) = 1 := by
    refine hP.eq_one_of_central (Subgroup.mem_subgroupOf.mp hxB) fun b hb => ?_
    have h := Subgroup.mem_centralizer_iff.mp hxC ⟨b, hP.bg hb⟩
      (Subgroup.mem_subgroupOf.mpr (hP.by_ hb))
    exact (congrArg Subtype.val h).symm
  exact Subtype.ext hx1

theorem PlusSide.cent_comm (hP : PlusSide G Y D B n)
    {c : ↥G} (hc : c ∈ Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G))
    {d : ↥G} (hd : d ∈ D.subgroupOf G) : c * d = d * c :=
  (Subgroup.mem_centralizer_iff.mp hc d (Subgroup.mem_subgroupOf.mpr
    (hP.dy (Subgroup.mem_subgroupOf.mp hd)))).symm

theorem PlusSide.comm_subgroupOf (hP : PlusSide G Y D B n) {d b : ↥G} (hd : d ∈ D.subgroupOf G)
    (hb : b ∈ B.subgroupOf G) : d * b = b * d :=
  Subtype.ext (hP.comm d.1 (Subgroup.mem_subgroupOf.mp hd) b.1 (Subgroup.mem_subgroupOf.mp hb))

theorem PlusSide.centralizer_subgroupOf (hP : PlusSide G Y D B n) :
    Subgroup.centralizer ((D.subgroupOf G : Subgroup ↥G) : Set ↥G) =
      B.subgroupOf G ⊔ Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G) := by
  apply le_antisymm
  · intro x hx
    have hxG := x.2
    have hxD : (x : MulAut V) ∈ G ⊓ Subgroup.centralizer (D : Set (MulAut V)) := by
      refine ⟨hxG, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      have h := Subgroup.mem_centralizer_iff.mp hx ⟨d, hP.dg hd⟩ (Subgroup.mem_subgroupOf.mpr hd)
      exact congrArg Subtype.val h
    obtain ⟨β, hβB, c, hcC, hxe⟩ := hP.cdec _ hxD
    have hβ' : (⟨β, hP.bg hβB⟩ : ↥G) ∈ B.subgroupOf G := Subgroup.mem_subgroupOf.mpr hβB
    have hc' : (⟨c, hcC.1⟩ : ↥G) ∈
        Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := Subgroup.mem_centralizer_iff.mp hcC.2 y.1 (Subgroup.mem_subgroupOf.mp hy)
      exact Subtype.ext h
    have hxe' : x = ⟨β, hP.bg hβB⟩ * ⟨c, hcC.1⟩ := Subtype.ext hxe
    rw [hxe']
    exact Subgroup.mul_mem_sup hβ' hc'
  · refine sup_le (fun b hb => ?_) (fun c hc => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact hP.comm_subgroupOf hd hb
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (hP.cent_comm hc hd).symm

theorem two_le_pRank_of_center_eq_bot {Γ : Type} [Group Γ] [Finite Γ] {A : Subgroup Γ}
    (hA : Nine7.QS A) (hZ : Subgroup.center ↥A = ⊥) : 2 ≤ Open.pRank 2 A := by
  refine Nine7.two_le_pRank_of_no_central_involution hA fun u hu hu2 hc => ?_
  have hmem : (⟨u, hu⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc g g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  have : u = 1 := congrArg Subtype.val hmem
  rw [this, orderOf_one] at hu2
  omega

theorem isSylowOf_of_maximal {Γ : Type*} [Group Γ] [Finite Γ] {C T : Subgroup Γ} (hT : T ≤ C)
    (hT2 : IsPGroup 2 T) (hTmax : ∀ T' : Subgroup Γ, T ≤ T' → T' ≤ C → IsPGroup 2 T' → T' = T) :
    ABGLocalTools.IsSylowOf 2 T C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2' : IsPGroup 2 (T.subgroupOf C) := hT2.comap_subtype
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hT2'
  have hSS : ABGLocalTools.IsSylowOf 2 ((S : Subgroup C).map C.subtype) C := ⟨S, rfl⟩
  have hTS : T ≤ (S : Subgroup C).map C.subtype := fun x hx => ⟨⟨x, hT hx⟩, hS hx, rfl⟩
  have heq := hTmax _ hTS (Subgroup.map_subtype_le _) hSS.isPGroup
  rw [← heq]
  exact hSS

variable [Finite V]

theorem sylow_subgroupOf {T : Subgroup (MulAut V)} (hYG : Y ≤ G) (hTG : T ≤ G)
    (hT2 : IsPGroup 2 ↥T) (hTY : T ≤ Subgroup.centralizer (Y : Set (MulAut V)))
    (hmax : ∀ T' : Subgroup (MulAut V), T ≤ T' →
      T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) → IsPGroup 2 ↥T' → T' = T) :
    ABGLocalTools.IsSylowOf 2 (T.subgroupOf G)
      (Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G)) := by
  refine isSylowOf_of_maximal ?_ hT2.comap_subtype ?_
  · intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hTY ht) y.1 (Subgroup.mem_subgroupOf.mp hy))
  · intro T' hTT' hT'c hT'2
    have hmap : T'.map G.subtype = T := by
      apply hmax (T'.map G.subtype)
      · intro x hx
        exact ⟨⟨x, hTG hx⟩, hTT' (show (⟨x, hTG hx⟩ : ↥G) ∈ T.subgroupOf G from hx), rfl⟩
      · rintro _ ⟨t, ht, rfl⟩
        refine ⟨t.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
        have := Subgroup.mem_centralizer_iff.mp (hT'c ht) ⟨y, hYG hy⟩
          (show (⟨y, hYG hy⟩ : ↥G) ∈ Y.subgroupOf G from hy)
        exact congrArg Subtype.val this
      · exact hT'2.map _
    calc T' = (T'.map G.subtype).comap G.subtype :=
          (Subgroup.comap_map_eq_self_of_injective G.subtype_injective T').symm
      _ = T.subgroupOf G := by rw [hmap]; rfl

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.ComponentClassification CFSG.RankThree.PartOne CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
open CFSG.ComponentClassification.AschbacherKnownGroup (AschbacherKnownGroupFacts)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_plusSide (hV : ∀ v : V, v ^ 2 = 1) (h5 : GSThmB.AschbacherTheorem5Input)
    (hK : AschbacherKnownGroupFacts) (hS : SchreierFor Assembly.InCatalog)
    (hT4 : AS76b.Asc75Theorem4) {G T Y D B : Subgroup (MulAut V)} {n : ℕ}
    (cfg : Emb4Cfg G T Y) (hP : PlusSide G Y D B n) (hP' : PlusSide G Y B D n) : False := by
  have hYG : Y ≤ G := hP.yg
  have hKP : Assembly.KProper Assembly.InCatalog ↥G := kProper_of_isKGroup' cfg.kgroup
  have hSch : LBalance.SchreierSections ↥G := schreierSections_of_isKGroup hS cfg.kgroup
  have hStarD : Nine7.Star (D.subgroupOf G) := star_subgroupOf hP.dg (star_D hV hSch cfg hP)
  have hStarB : Nine7.Star (B.subgroupOf G) := star_subgroupOf hP'.dg (star_D hV hSch cfg hP')
  have hDZ := hP'.center_subgroupOf
  have hBZ := hP.center_subgroupOf
  have hTY := cfg.adm.le_centralizer
  have hT1 : T.subgroupOf G ≠ ⊥ := by
    intro hbot
    apply cfg.adm.hT1
    have := Subgroup.map_subgroupOf_eq_of_le cfg.adm.hTG
    rw [hbot, Subgroup.map_bot] at this
    exact this.symm
  have hTC : T.subgroupOf G ≤ Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hTY (Subgroup.mem_subgroupOf.mp ht)) y.1
      (Subgroup.mem_subgroupOf.mp hy))
  have hTsyl := sylow_subgroupOf hYG cfg.adm.hTG cfg.adm.hT2 hTY cfg.sylow
  obtain ⟨hDsub, hBsub⟩ := plus_factors_subnormal h5 hK hS hKP hT4
    (D := D.subgroupOf G) (B := B.subgroupOf G)
    (C := Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G))
    (T := T.subgroupOf G) hP.qs hP'.qs (two_le_pRank_of_center_eq_bot hP.qs hDZ)
    (two_le_pRank_of_center_eq_bot hP'.qs hBZ) hDZ hBZ
    (fun d hd b hb => hP.comm_subgroupOf hd hb) (fun c hc d hd => hP.cent_comm hc hd)
    (fun c hc b hb => hP'.cent_comm hc hb) hP.centralizer_subgroupOf hP'.centralizer_subgroupOf
    hP.inf_centralizer_subgroupOf hP'.inf_centralizer_subgroupOf hTC hT1 hTsyl hStarD hStarB
  have hYsub : (Y.subgroupOf G).IsSubnormal := by
    have : Y.subgroupOf G = D.subgroupOf G ⊔ B.subgroupOf G := by
      rw [← Subgroup.subgroupOf_sup hP.dg hP.bg, hP.sup]
    rw [this]
    exact CFSG.GroupTheory.isSubnormal_sup hDsub hBsub
  exact cfg.nolift ⟨Y, lift4_self hYG hYsub cfg.adm.hcls⟩

theorem end4OmegaPlus_of_inputs (h5 : GSThmB.AschbacherTheorem5Input)
    (hK : AschbacherKnownGroupFacts) (hS : SchreierFor Assembly.InCatalog)
    (hT4 : AS76b.Asc75Theorem4) : End4OmegaPlus := by
  intro V _ _ hV G T Y cfg ⟨n, hn, hΩ⟩
  obtain ⟨D, B, hP, hP'⟩ := exists_plusSide hV hn (fun y hy => (cfg.adm.hYC hy).1) hΩ
  exact false_of_plusSide hV h5 hK hS hT4 cfg hP hP'

end CFSG.CGT.PushingUpLit.CGT6
