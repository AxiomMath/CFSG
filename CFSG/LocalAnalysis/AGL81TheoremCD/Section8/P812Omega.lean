module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Two
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneFourCover
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110b
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.GroupTheory.PRankQuotientLift
import CFSG.GH74.Generic.BProg.BpGeneral
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.GroupTheory.PowMemSupOfPGroup
import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofSubn
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open scoped commutatorElement Pointwise

private theorem isPGroup_quotient_sup_centralizer
    {X : Type} [Group X] [Finite X] {L S : Subgroup X}
    [(Subgroup.centralizer (L : Set X)).Normal]
    (hSp : IsPGroup 3 S) :
    IsPGroup 3 (↥(S ⊔ Subgroup.centralizer (L : Set X)) ⧸
      (Subgroup.centralizer (L : Set X)).subgroupOf
        (S ⊔ Subgroup.centralizer (L : Set X))) := by
  classical
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  let T : Subgroup X := S ⊔ C
  let K : Subgroup ↥T := C.subgroupOf T
  let Y : Type := ↥T ⧸ K
  have hTgen : S.subgroupOf T ⊔ C.subgroupOf T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (show S ≤ T from le_sup_left) (show C ≤ T from le_sup_right),
      show S ⊔ C = T from rfl, Subgroup.subgroupOf_self]
  have hSmap : (S.subgroupOf T).map (QuotientGroup.mk' K) = ⊤ := by
    have htop : (S.subgroupOf T ⊔ C.subgroupOf T).map (QuotientGroup.mk' K) = ⊤ := by
      rw [hTgen, Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K)
    rwa [Subgroup.map_sup, show C.subgroupOf T = K from rfl, QuotientGroup.map_mk'_self,
      sup_bot_eq] at htop
  let fS : S →* Y := (QuotientGroup.mk' K).comp (Subgroup.inclusion (show S ≤ T from le_sup_left))
  have hfSrange : fS.range = (S.subgroupOf T).map (QuotientGroup.mk' K) := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨s.1, Subgroup.mem_sup_left s.2⟩,
        Subgroup.mem_subgroupOf.mpr s.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t.1, Subgroup.mem_subgroupOf.mp ht⟩, rfl⟩
  have hfS : Function.Surjective fS := by
    rw [← MonoidHom.range_eq_top, hfSrange, hSmap]
  exact IsPGroup.of_surjective hSp fS hfS

private theorem isPGroup_quotient_inf_sup_centralizer
    {X : Type} [Group X] [Finite X] {L S : Subgroup X}
    [(Subgroup.centralizer (L : Set X)).Normal]
    (hSp : IsPGroup 3 S) :
    IsPGroup 3 (↥((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
        (L ⊔ Subgroup.centralizer (L : Set X))) ⧸
      (Subgroup.centralizer (L : Set X)).subgroupOf
        ((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
          (L ⊔ Subgroup.centralizer (L : Set X)))) := by
  classical
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  let T : Subgroup X := S ⊔ C
  let K : Subgroup ↥T := C.subgroupOf T
  let Y : Type := ↥T ⧸ K
  let A : Subgroup X := T ⊓ (L ⊔ C)
  have hYp : IsPGroup 3 Y :=
    isPGroup_quotient_sup_centralizer (X := X) (L := L) (S := S) hSp
  let η : A →* Y :=
    (QuotientGroup.mk' K).comp (Subgroup.inclusion (show A ≤ T from inf_le_left))
  have hηker : η.ker = C.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff
          (Subgroup.inclusion (show A ≤ T from inf_le_left) x)).mp hx)
    · intro hx
      change QuotientGroup.mk' K (Subgroup.inclusion (show A ≤ T from inf_le_left) x) = 1
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)
  let ηbar : (A ⧸ C.subgroupOf A) →* Y :=
    QuotientGroup.lift (C.subgroupOf A) η (by rw [hηker])
  have hηbar_inj : Function.Injective ηbar := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf A) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf A) y
    change QuotientGroup.mk a = QuotientGroup.mk b
    rw [QuotientGroup.eq]
    have hxy' : η a = η b := by
      simpa [ηbar, QuotientGroup.lift_mk'] using hxy
    have h1 : η (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hxy', inv_mul_cancel]
    have h2 : a⁻¹ * b ∈ η.ker := MonoidHom.mem_ker.mpr h1
    rwa [hηker] at h2
  exact IsPGroup.of_injective hYp ηbar hηbar_inj

private theorem pRank_quotient_centralizer_le_one
    {X : Type} [Group X] [Finite X] {L : Subgroup X}
    [(Subgroup.centralizer (L : Set X)).Normal]
    (hLrank : CFSG.Open.pRank 3 L = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸
      (Subgroup.centralizer (L : Set X)).subgroupOf L)) ≤ 1 := by
  by_contra h
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸
      (Subgroup.centralizer (L : Set X)).subgroupOf L)) := by omega
  have h2L := CFSG.GroupTheory.two_le_pRank_of_quotient
    ((Subgroup.centralizer (L : Set X)).subgroupOf L)
    Nat.prime_three (by norm_num) h2
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L] at h2L
  omega

private theorem pRank_top_quotient_inf_sup_centralizer_le
    {X : Type} [Group X] [Finite X] {L S : Subgroup X}
    [(Subgroup.centralizer (L : Set X)).Normal]
    (hLrank : CFSG.Open.pRank 3 L = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
        (L ⊔ Subgroup.centralizer (L : Set X))) ⧸
      (Subgroup.centralizer (L : Set X)).subgroupOf
        ((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
          (L ⊔ Subgroup.centralizer (L : Set X))))) ≤ 1 := by
  classical
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  let T : Subgroup X := S ⊔ C
  let A : Subgroup X := T ⊓ (L ⊔ C)
  have hLCrank : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ C.subgroupOf L)) ≤ 1 :=
    pRank_quotient_centralizer_le_one hLrank
  have eLC : (L ⧸ C.subgroupOf L) ≃* (↥(L ⊔ C) ⧸ C.subgroupOf (L ⊔ C)) :=
    QuotientGroup.quotientInfEquivProdNormalQuotient L C
  let θ : A →* (L ⧸ C.subgroupOf L) :=
    eLC.symm.toMonoidHom.comp ((QuotientGroup.mk' (C.subgroupOf (L ⊔ C))).comp
      (Subgroup.inclusion (show A ≤ L ⊔ C from inf_le_right)))
  have hθker : θ.ker = C.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : QuotientGroup.mk' (C.subgroupOf (L ⊔ C))
          (Subgroup.inclusion (show A ≤ L ⊔ C from inf_le_right) x) = 1 := by
        exact eLC.symm.injective (by simpa [θ] using hx)
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff
          (Subgroup.inclusion (show A ≤ L ⊔ C from inf_le_right) x)).mp hx')
    · intro hx
      change eLC.symm (QuotientGroup.mk' (C.subgroupOf (L ⊔ C))
        (Subgroup.inclusion (show A ≤ L ⊔ C from inf_le_right) x)) = 1
      rw [show QuotientGroup.mk' (C.subgroupOf (L ⊔ C))
          (Subgroup.inclusion (show A ≤ L ⊔ C from inf_le_right) x) = 1 from
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx), map_one]
  let θbar : (A ⧸ C.subgroupOf A) →* (L ⧸ C.subgroupOf L) :=
    QuotientGroup.lift (C.subgroupOf A) θ (by rw [hθker])
  have hθbar_inj : Function.Injective θbar := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf A) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf A) y
    change QuotientGroup.mk a = QuotientGroup.mk b
    rw [QuotientGroup.eq]
    have hxy' : θ a = θ b := by
      simpa [θbar, QuotientGroup.lift_mk'] using hxy
    have h1 : θ (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hxy', inv_mul_cancel]
    have h2 : a⁻¹ * b ∈ θ.ker := MonoidHom.mem_ker.mpr h1
    rwa [hθker] at h2
  exact (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) θbar
    hθbar_inj).trans hLCrank

private theorem isCyclic_quotient_inf_sup_centralizer
    {X : Type} [Group X] [Finite X] {L S : Subgroup X}
    [(Subgroup.centralizer (L : Set X)).Normal]
    (hACp : IsPGroup 3 (↥((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
        (L ⊔ Subgroup.centralizer (L : Set X))) ⧸
      (Subgroup.centralizer (L : Set X)).subgroupOf
        ((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
          (L ⊔ Subgroup.centralizer (L : Set X)))))
    (hLrank : CFSG.Open.pRank 3 L = 1) :
    IsCyclic (↥((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
        (L ⊔ Subgroup.centralizer (L : Set X))) ⧸
      (Subgroup.centralizer (L : Set X)).subgroupOf
        ((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
          (L ⊔ Subgroup.centralizer (L : Set X)))) := by
  classical
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  let T : Subgroup X := S ⊔ C
  let A : Subgroup X := T ⊓ (L ⊔ C)
  have hACrank_open : CFSG.Open.pRank 3 (⊤ : Subgroup (A ⧸ C.subgroupOf A)) ≤ 1 :=
    pRank_top_quotient_inf_sup_centralizer_le (X := X) (L := L) (S := S) hLrank
  have hACrank : CFSG.pRank 3 (A ⧸ C.subgroupOf A) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hACrank_open
  exact CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
    Nat.prime_three (by norm_num) hACp hACrank

private theorem isCyclic_map_subgroupOf_quotient
    {X : Type} [Group X] [Finite X] {L S : Subgroup X}
    [(Subgroup.centralizer (L : Set X)).Normal]
    (hACcyc : IsCyclic (↥((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
        (L ⊔ Subgroup.centralizer (L : Set X))) ⧸
      (Subgroup.centralizer (L : Set X)).subgroupOf
        ((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
          (L ⊔ Subgroup.centralizer (L : Set X))))) :
    IsCyclic ↥(((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
        (L ⊔ Subgroup.centralizer (L : Set X))).subgroupOf
          (S ⊔ Subgroup.centralizer (L : Set X)) |>.map
      (QuotientGroup.mk' ((Subgroup.centralizer (L : Set X)).subgroupOf
        (S ⊔ Subgroup.centralizer (L : Set X))))) := by
  classical
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  let T : Subgroup X := S ⊔ C
  let K : Subgroup ↥T := C.subgroupOf T
  let Y : Type := ↥T ⧸ K
  let A : Subgroup X := T ⊓ (L ⊔ C)
  let NY : Subgroup Y := (A.subgroupOf T).map (QuotientGroup.mk' K)
  let η : A →* Y :=
    (QuotientGroup.mk' K).comp (Subgroup.inclusion (show A ≤ T from inf_le_left))
  have hηker : η.ker = C.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff
          (Subgroup.inclusion (show A ≤ T from inf_le_left) x)).mp hx)
    · intro hx
      change QuotientGroup.mk' K (Subgroup.inclusion (show A ≤ T from inf_le_left) x) = 1
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)
  have hηrange : η.range = NY := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩,
        Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t.1, Subgroup.mem_subgroupOf.mp ht⟩, rfl⟩
  let ηbar : (A ⧸ C.subgroupOf A) →* Y :=
    QuotientGroup.lift (C.subgroupOf A) η (by rw [hηker])
  haveI : IsCyclic (A ⧸ C.subgroupOf A) := hACcyc
  let ηNY : (A ⧸ C.subgroupOf A) →* NY :=
    ηbar.codRestrict NY (by
      intro q
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf A) q
      erw [QuotientGroup.lift_mk']
      rw [← hηrange]
      exact MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  have hηNY : Function.Surjective ηNY := by
    intro n
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (by rw [hηrange]; exact n.2)
    refine ⟨QuotientGroup.mk' (C.subgroupOf A) a, ?_⟩
    apply Subtype.ext
    simpa [ηNY, ηbar] using ha
  exact isCyclic_of_surjective ηNY hηNY

private theorem isCyclic_quotient_inf_sup_centralizer_of_generator
    {X : Type} [Group X] [Finite X] {L W S : Subgroup X}
    [(Subgroup.centralizer (L : Set X)).Normal]
    [(L ⊔ Subgroup.centralizer (L : Set X)).Normal]
    (hLn : L.Normal) (hCW : Subgroup.centralizer (L : Set X) ≤ W)
    (hS : S ≤ L ⊔ W)
    (hgen : ∃ g ∈ W, ∀ w ∈ W, ∃ n : ℕ,
      w * (g ^ n)⁻¹ ∈ Subgroup.centralizer (L : Set X)) :
    IsCyclic (↥(S ⊔ Subgroup.centralizer (L : Set X)) ⧸
      ((S ⊔ Subgroup.centralizer (L : Set X)) ⊓
        (L ⊔ Subgroup.centralizer (L : Set X))).subgroupOf
          (S ⊔ Subgroup.centralizer (L : Set X))) := by
  classical
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  let T : Subgroup X := S ⊔ C
  let A : Subgroup X := T ⊓ (L ⊔ C)
  let πLC : X →* X ⧸ (L ⊔ C) := QuotientGroup.mk' (L ⊔ C)
  let φ : ↥T →* X ⧸ (L ⊔ C) := πLC.comp T.subtype
  have hφker : φ.ker = A.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro ht
      exact ⟨t.2, (QuotientGroup.eq_one_iff _).mp ht⟩
    · intro ht
      exact (QuotientGroup.eq_one_iff _).mpr ht.2
  have hT_le : T ≤ L ⊔ W := sup_le hS (hCW.trans le_sup_right)
  have hWmap_cyc : IsCyclic ↥(W.map πLC) := by
    obtain ⟨g, hgW, hgenw⟩ := hgen
    have hle : W.map πLC ≤ Subgroup.zpowers (πLC g) := by
      rintro - ⟨w, hw, rfl⟩
      obtain ⟨n, hn⟩ := hgenw w hw
      have hπ : πLC w = (πLC g) ^ n := by
        have h1 : πLC (w * (g ^ n)⁻¹) = 1 := by
          apply (QuotientGroup.eq_one_iff _).mpr
          exact Subgroup.mem_sup_right hn
        rw [map_mul, map_inv, map_pow] at h1
        exact mul_inv_eq_one.mp h1
      rw [hπ]
      exact Subgroup.npow_mem_zpowers _ _
    exact Subgroup.isCyclic_of_le hle
  have hφrange_cyc : IsCyclic ↥φ.range := by
    have hle : φ.range ≤ W.map πLC := by
      rintro - ⟨t, rfl⟩
      have ht : (t : X) ∈ L ⊔ W := hT_le t.2
      obtain ⟨l, hl, w, hw, hlw⟩ := Subgroup.mem_sup_of_normal_left.mp ht
      have hφt : φ t = πLC w := by
        change πLC (t : X) = πLC w
        rw [show (t : X) = l * w from hlw.symm, map_mul]
        have hl1 : πLC l = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left hl)
        rw [hl1, one_mul]
      exact Subgroup.mem_map.mpr ⟨w, hw, hφt.symm⟩
    haveI : IsCyclic ↥(W.map πLC) := hWmap_cyc
    exact Subgroup.isCyclic_of_le hle
  let e : (↥T ⧸ A.subgroupOf T) ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

private theorem isMetacyclic_quotient_centralizer
    {X : Type} [Group X] [Finite X] {L W S : Subgroup X}
    (hLn : L.Normal)
    (hCW : Subgroup.centralizer (L : Set X) ≤ W)
    (hS : S ≤ L ⊔ W)
    (hSp : IsPGroup 3 S)
    (hgen : ∃ g ∈ W, ∀ w ∈ W, ∃ n : ℕ,
      w * (g ^ n)⁻¹ ∈ Subgroup.centralizer (L : Set X))
    (hLrank : CFSG.Open.pRank 3 L = 1) :
    CFSG.IsMetacyclic (↥(S ⊔ Subgroup.centralizer (L : Set X)) ⧸
      (Subgroup.centralizer (L : Set X)).subgroupOf
        (S ⊔ Subgroup.centralizer (L : Set X))) := by
  classical
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  let T : Subgroup X := S ⊔ C
  let K : Subgroup ↥T := C.subgroupOf T
  let Y : Type := ↥T ⧸ K
  let A : Subgroup X := T ⊓ (L ⊔ C)
  let NY : Subgroup Y := (A.subgroupOf T).map (QuotientGroup.mk' K)
  haveI hCn : C.Normal := Subgroup.normal_centralizer
  haveI hLCn : (L ⊔ C).Normal := Subgroup.sup_normal L C
  have hAdef : A.subgroupOf T = (L ⊔ C).subgroupOf T := by
    ext x
    simp only [A, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hAn : (A.subgroupOf T).Normal := by
    rw [hAdef]
    exact hLCn.subgroupOf T
  have hNYn : NY.Normal :=
    Subgroup.Normal.map hAn (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  have hYp : IsPGroup 3 Y :=
    isPGroup_quotient_sup_centralizer (X := X) (L := L) (S := S) hSp
  have hACp : IsPGroup 3 (A ⧸ C.subgroupOf A) :=
    isPGroup_quotient_inf_sup_centralizer (X := X) (L := L) (S := S) hSp
  have hACcyc : IsCyclic (A ⧸ C.subgroupOf A) :=
    isCyclic_quotient_inf_sup_centralizer (X := X) (L := L) (S := S) hACp hLrank
  have hNYcyc : IsCyclic ↥NY :=
    isCyclic_map_subgroupOf_quotient (X := X) (L := L) (S := S) hACcyc
  have hTAcyc : IsCyclic (↥T ⧸ A.subgroupOf T) :=
    isCyclic_quotient_inf_sup_centralizer_of_generator (X := X) (L := L) (W := W) (S := S)
      hLn hCW hS hgen
  have hCA : K ≤ A.subgroupOf T := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ⟨x.2, Subgroup.mem_sup_right (show (x : X) ∈ C from Subgroup.mem_subgroupOf.mp hx)⟩
  have hQNcyc : IsCyclic (Y ⧸ NY) := by
    let e : (Y ⧸ NY) ≃* (↥T ⧸ A.subgroupOf T) :=
      QuotientGroup.quotientQuotientEquivQuotient K (A.subgroupOf T) hCA
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact ⟨NY, hNYn, hNYcyc, hQNcyc⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8



namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open scoped commutatorElement Pointwise

theorem image_isComponent_pRank
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {L Q : Subgroup X} (hL : CFSG.IsPComponent p L) (hLn : L.Normal)
    [Q.Normal] (hQ : Q = (CFSG.pPrimeCore p ↥L).map L.subtype)
    (hQ3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥L)) :
    (L.map (QuotientGroup.mk' Q)).Normal ∧
      CFSG.IsComponent (L.map (QuotientGroup.mk' Q)) ∧
      CFSG.Open.pRank 3 (L.map (QuotientGroup.mk' Q)) = CFSG.Open.pRank 3 L := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hQsub : Q.subgroupOf L = CFSG.pPrimeCore p ↥L := by
    rw [hQ]
    change Subgroup.comap L.subtype (Subgroup.map L.subtype (CFSG.pPrimeCore p ↥L)) =
      CFSG.pPrimeCore p ↥L
    rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  let Lq : Subgroup (X ⧸ Q) := L.map (QuotientGroup.mk' Q)
  have hLqn : Lq.Normal :=
    Subgroup.Normal.map hLn (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  have hLqq : CFSG.IsQuasisimple Lq := by
    have hquo :=
      CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple
        p L hL
    have e : (↥L ⧸ CFSG.pPrimeCore p ↥L) ≃* Lq :=
      (QuotientGroup.quotientMulEquivOfEq hQsub.symm).trans
        (CFSG.quotientSubgroupRangeEquiv L Q)
    exact hquo.of_mulEquiv e.symm
  have hLqc : CFSG.IsComponent Lq := ⟨hLqq, hLqn.isSubnormal⟩
  have hQ3' : ¬ 3 ∣ Nat.card (Q.subgroupOf L) := by
    rwa [hQsub]
  have hLqrank : CFSG.Open.pRank 3 Lq = CFSG.Open.pRank 3 L := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have e : (↥L ⧸ Q.subgroupOf L) ≃* Lq := CFSG.quotientSubgroupRangeEquiv L Q
    have htop : CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ Q.subgroupOf L)) =
        CFSG.Open.pRank 3 L := by
      rw [CFSG.SectionRank.pRank_quotient_eq (Q.subgroupOf L) hQ3',
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    calc CFSG.Open.pRank 3 Lq
        = CFSG.Open.pRank 3 (⊤ : Subgroup Lq) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup Lq
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ Q.subgroupOf L)) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).symm
      _ = CFSG.Open.pRank 3 L := htop
  exact ⟨hLqn, hLqc, hLqrank⟩

theorem mem_sup_centralizerSection_of_mem_map_sup_centralizer
    {X : Type} [Group X] [Finite X] {p : ℕ}
    {L Q : Subgroup X} (hLn : L.Normal) [Q.Normal]
    (hQ : Q = (CFSG.pPrimeCore p ↥L).map L.subtype)
    {x : X}
    (hx : QuotientGroup.mk' Q x ∈ L.map (QuotientGroup.mk' Q) ⊔
      Subgroup.centralizer (L.map (QuotientGroup.mk' Q) : Set (X ⧸ Q))) :
    x ∈ L ⊔ CFSG.GH74.GLS.centralizerSection L Q := by
  classical
  let Lbar : Subgroup (X ⧸ Q) := L.map (QuotientGroup.mk' Q)
  have hLbar_n : Lbar.Normal :=
    Subgroup.Normal.map hLn (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  haveI : Lbar.Normal := hLbar_n
  have hQleL : Q ≤ L := by
    rw [hQ]
    exact Subgroup.map_subtype_le _
  obtain ⟨lbar, hlbar, cbar, hcbar, hxeq⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hlbar
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective Q cbar
  have hxeq' : QuotientGroup.mk' Q x = QuotientGroup.mk' Q (l * c) := by
    rw [← hxeq, map_mul]
  let q : X := x * (l * c)⁻¹
  have hqQ : q ∈ Q := by
    apply (QuotientGroup.eq_one_iff q).mp
    dsimp [q]
    change QuotientGroup.mk' Q x *
      (QuotientGroup.mk' Q l * QuotientGroup.mk' Q c)⁻¹ = 1
    rw [← map_mul, hxeq', mul_inv_cancel]
  have hqL : q ∈ L := hQleL hqQ
  let l' : X := q * l
  have hl' : l' ∈ L := L.mul_mem hqL hl
  have hxdecomp : x = l' * c := by
    dsimp only [l', q]
    group
  have hcNL : c ∈ Subgroup.normalizer (L : Set X) :=
    Subgroup.le_normalizer_of_normal (H := L) (Subgroup.mem_top c)
  have hcNQ : c ∈ Subgroup.normalizer (Q : Set X) :=
    Subgroup.le_normalizer_of_normal (H := Q) (Subgroup.mem_top c)
  have hcComm : ∀ k ∈ L, ⁅k, c⁆ ∈ Q := by
    intro k hk
    have hkbar : QuotientGroup.mk' Q k ∈ Lbar := Subgroup.mem_map_of_mem _ hk
    have hcomm : QuotientGroup.mk' Q k * QuotientGroup.mk' Q c =
        QuotientGroup.mk' Q c * QuotientGroup.mk' Q k :=
      Subgroup.mem_centralizer_iff.mp hcbar _ hkbar
    have h1 : QuotientGroup.mk' Q (⁅k, c⁆) = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcC : c ∈ CFSG.GH74.GLS.centralizerSection L Q :=
    ⟨hcNL, hcNQ, hcComm⟩
  rw [hxdecomp]
  exact (L ⊔ CFSG.GH74.GLS.centralizerSection L Q).mul_mem
    (Subgroup.mem_sup_left hl') (Subgroup.mem_sup_right hcC)

private theorem commute_quotient_centralizer
    {X : Type} [Group X] [Finite X] {L S : Subgroup X}
    [(Subgroup.centralizer (L : Set X)).Normal]
    (hLn : L.Normal) (hLrank : CFSG.Open.pRank 3 L = 1)
    (hSp : IsPGroup 3 S)
    {W : Subgroup X} (hCW : Subgroup.centralizer (L : Set X) ≤ W)
    (hSW : S ≤ L ⊔ W)
    (hgen : ∃ g ∈ W, ∀ w ∈ W, ∃ n : ℕ,
      w * (g ^ n)⁻¹ ∈ Subgroup.centralizer (L : Set X))
    {u v : X} (hu : u ∈ S) (hv : v ∈ S) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) :
    QuotientGroup.mk' (Subgroup.centralizer (L : Set X)) u *
        QuotientGroup.mk' (Subgroup.centralizer (L : Set X)) v =
      QuotientGroup.mk' (Subgroup.centralizer (L : Set X)) v *
        QuotientGroup.mk' (Subgroup.centralizer (L : Set X)) u := by
  classical
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  let T : Subgroup X := S ⊔ C
  let Y : Type := ↥T ⧸ C.subgroupOf T
  have hmeta : CFSG.IsMetacyclic Y :=
    isMetacyclic_quotient_centralizer hLn hCW hSW hSp hgen hLrank
  haveI : C.Normal := Subgroup.normal_centralizer
  have hYp : IsPGroup 3 Y := CFSG.GroupTheory.isPGroup_quotient_sup_left hSp
  let uY : Y := QuotientGroup.mk' (C.subgroupOf T) ⟨u, Subgroup.mem_sup_left hu⟩
  let vY : Y := QuotientGroup.mk' (C.subgroupOf T) ⟨v, Subgroup.mem_sup_left hv⟩
  have huY3 : uY ^ 3 = 1 := by
    change (QuotientGroup.mk' (C.subgroupOf T) _) ^ 3 = 1
    rw [← map_pow]
    have h3 : (⟨u, Subgroup.mem_sup_left hu⟩ : ↥T) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hu3
    rw [h3, map_one]
  have hvY3 : vY ^ 3 = 1 := by
    change (QuotientGroup.mk' (C.subgroupOf T) _) ^ 3 = 1
    rw [← map_pow]
    have h3 : (⟨v, Subgroup.mem_sup_left hv⟩ : ↥T) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hv3
    rw [h3, map_one]
  have hcommY : uY * vY = vY * uY :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110b.comm_of_isMetacyclic
      (p := 3) (by norm_num) hYp hmeta huY3 hvY3
  have huYeq : (CFSG.quotientSubgroupRangeEquiv T C) uY = QuotientGroup.mk' C u := by
    dsimp [uY]
    exact CFSG.quotientSubgroupRangeEquiv_apply_mk T C ⟨u, _⟩
  have hvYeq : (CFSG.quotientSubgroupRangeEquiv T C) vY = QuotientGroup.mk' C v := by
    dsimp [vY]
    exact CFSG.quotientSubgroupRangeEquiv_apply_mk T C ⟨v, _⟩
  have hcomm : QuotientGroup.mk' C u * QuotientGroup.mk' C v =
      QuotientGroup.mk' C v * QuotientGroup.mk' C u := by
    have h := congrArg (fun z => (((CFSG.quotientSubgroupRangeEquiv T C) z :
      ↥(T.map (QuotientGroup.mk' C))) : X ⧸ C)) hcommY
    simpa only [map_mul, Subgroup.coe_mul, huYeq, hvYeq] using h
  exact hcomm

private theorem commutator_zpowers_le_pPrimeCore_of_commute_quotient
    {X : Type} [Group X] [Finite X] {p : ℕ} {L Q : Subgroup X} (hLn : L.Normal)
    [Q.Normal]
    [(Subgroup.centralizer
      ((L.map (QuotientGroup.mk' Q)) : Set (X ⧸ Q))).Normal]
    (hQ : Q = (CFSG.pPrimeCore p ↥L).map L.subtype)
    {u v : X}
    (hcomm : QuotientGroup.mk' (Subgroup.centralizer
          ((L.map (QuotientGroup.mk' Q)) : Set (X ⧸ Q))) (QuotientGroup.mk' Q u) *
        QuotientGroup.mk' (Subgroup.centralizer
          ((L.map (QuotientGroup.mk' Q)) : Set (X ⧸ Q))) (QuotientGroup.mk' Q v) =
      QuotientGroup.mk' (Subgroup.centralizer
          ((L.map (QuotientGroup.mk' Q)) : Set (X ⧸ Q))) (QuotientGroup.mk' Q v) *
        QuotientGroup.mk' (Subgroup.centralizer
          ((L.map (QuotientGroup.mk' Q)) : Set (X ⧸ Q))) (QuotientGroup.mk' Q u)) :
    ⁅Subgroup.zpowers (u * v * u⁻¹ * v⁻¹), L⁆ ≤
      (CFSG.pPrimeCore p ↥L).map L.subtype := by
  classical
  let Xq : Type := X ⧸ Q
  let Lq : Subgroup Xq := L.map (QuotientGroup.mk' Q)
  let Cq : Subgroup Xq := Subgroup.centralizer (Lq : Set Xq)
  let uq : Xq := QuotientGroup.mk' Q u
  let vq : Xq := QuotientGroup.mk' Q v
  let c : X := u * v * u⁻¹ * v⁻¹
  have hcq : ⁅uq, vq⁆ = QuotientGroup.mk' Q c := by
    change ⁅QuotientGroup.mk' Q u, QuotientGroup.mk' Q v⁆ = QuotientGroup.mk' Q c
    rw [← map_commutatorElement]
    simp [c, commutatorElement_def]
  have hcC : QuotientGroup.mk' Q c ∈ Cq := by
    apply (QuotientGroup.eq_one_iff _).mp
    have h1 : QuotientGroup.mk' Cq (⁅uq, vq⁆) = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    rwa [hcq] at h1
  have hc_cent : c ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L := by
    rw [CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup]
    refine ⟨Subgroup.le_normalizer_of_normal (H := L) (Subgroup.mem_top c), ?_⟩
    intro l hl
    have hlq : QuotientGroup.mk' Q l ∈ Lq := Subgroup.mem_map_of_mem _ hl
    have hcomml : QuotientGroup.mk' Q l * QuotientGroup.mk' Q c =
        QuotientGroup.mk' Q c * QuotientGroup.mk' Q l :=
      Subgroup.mem_centralizer_iff.mp hcC _ hlq
    have h1 : QuotientGroup.mk' Q (⁅l, c⁆) = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomml
    change ⁅l, c⁆ ∈ (CFSG.pPrimeCore p ↥L).map L.subtype
    rw [← hQ]
    exact (QuotientGroup.eq_one_iff (⁅l, c⁆)).mp h1
  rw [Subgroup.commutator_le]
  intro z hz l hl
  have hzcent : z ∈ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L :=
    (Subgroup.zpowers_le.mpr hc_cent) hz
  have h := (CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup.mp hzcent).2 l hl
  change ⁅l, z⁆ ∈ (CFSG.pPrimeCore p ↥L).map L.subtype at h
  change ⁅z, l⁆ ∈ (CFSG.pPrimeCore p ↥L).map L.subtype
  simpa only [commutatorElement_inv] using Subgroup.inv_mem _ h

private theorem commutator_mem_of_isPComponent
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hK : CFSG.Open.IsKGroup X)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections X)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    {L : Subgroup X} (hL : CFSG.IsPComponent p L) (hLn : L.Normal)
    (hLrank : CFSG.Open.pRank 3 L = 1)
    {S : Subgroup X} (hS3 : IsPGroup 3 S)
    {u v : X} (hu : u ∈ S) (hv : v ∈ S) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) :
    ⁅Subgroup.zpowers (u * v * u⁻¹ * v⁻¹), L⁆ ≤
      (CFSG.pPrimeCore p ↥L).map L.subtype := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let Q : Subgroup X := (CFSG.pPrimeCore p ↥L).map L.subtype
  have hQn : Q.Normal := by
    change (Subgroup.map L.subtype (CFSG.pPrimeCore p ↥L)).Normal
    exact ConjAct.normal_of_characteristic_of_normal
  haveI : Q.Normal := hQn
  let Xq : Type := X ⧸ Q
  let Lq : Subgroup Xq := L.map (QuotientGroup.mk' Q)
  have hQ3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥L) :=
    not_three_dvd_card_pPrimeCore_of_isPComponent hp hSch hL hLrank
  have hLqdata := image_isComponent_pRank hp hL hLn (Q := Q) rfl hQ3
  have hLqn : Lq.Normal := hLqdata.1
  have hLqc : CFSG.IsComponent Lq := hLqdata.2.1
  have hLqrank : CFSG.Open.pRank 3 Lq = 1 := hLqdata.2.2.trans hLrank
  let SX : Subgroup Xq := S.map (QuotientGroup.mk' Q)
  have hSX3 : IsPGroup 3 SX := hS3.map _
  obtain ⟨W, hCW, hSXle, g, hgW, hgenw⟩ :=
    h714 Xq (hK.quotient Q) 3 Nat.prime_three (by norm_num) Lq hLqc hLqn hLqrank SX hSX3
  haveI : (Subgroup.centralizer (Lq : Set Xq)).Normal := Subgroup.normal_centralizer
  have huq3 : (QuotientGroup.mk' Q u) ^ 3 = 1 := by
    rw [← map_pow, hu3, map_one]
  have hvq3 : (QuotientGroup.mk' Q v) ^ 3 = 1 := by
    rw [← map_pow, hv3, map_one]
  have hcommX : QuotientGroup.mk' (Subgroup.centralizer (Lq : Set Xq))
        (QuotientGroup.mk' Q u) * QuotientGroup.mk' (Subgroup.centralizer (Lq : Set Xq))
        (QuotientGroup.mk' Q v) =
      QuotientGroup.mk' (Subgroup.centralizer (Lq : Set Xq))
        (QuotientGroup.mk' Q v) * QuotientGroup.mk' (Subgroup.centralizer (Lq : Set Xq))
        (QuotientGroup.mk' Q u) :=
    commute_quotient_centralizer (X := Xq) (L := Lq) (S := SX)
      hLqn hLqrank hSX3 hCW hSXle ⟨g, hgW, hgenw⟩
      (Subgroup.mem_map_of_mem _ hu) (Subgroup.mem_map_of_mem _ hv) huq3 hvq3
  exact commutator_zpowers_le_pPrimeCore_of_commute_quotient
    (X := X) (p := p) (L := L) (Q := Q) hLn rfl hcommX

private theorem map_commutator_zpowers_core_of_subgroup
    {G : Type} [Group G] [Finite G] {p : ℕ} {X L : Subgroup G} (hLX : L ≤ X)
    {u v : G} (hu : u ∈ X) (hv : v ∈ X)
    (h : ⁅Subgroup.zpowers ((⟨u, hu⟩ : X) * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹),
        L.subgroupOf X⁆ ≤
      (CFSG.pPrimeCore p ↥(L.subgroupOf X)).map (L.subgroupOf X).subtype) :
    ⁅Subgroup.zpowers (u * v * u⁻¹ * v⁻¹), L⁆ ≤
      (CFSG.pPrimeCore p ↥L).map L.subtype := by
  have hmap := Subgroup.map_mono (f := X.subtype) h
  have hLHS : (⁅Subgroup.zpowers ((⟨u, hu⟩ : X) * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹),
      L.subgroupOf X⁆).map X.subtype =
      ⁅Subgroup.zpowers (u * v * u⁻¹ * v⁻¹), L⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le hLX]
    rfl
  have hRHS : ((CFSG.pPrimeCore p ↥(L.subgroupOf X)).map (L.subgroupOf X).subtype).map
      X.subtype = (CFSG.pPrimeCore p ↥L).map L.subtype := by
    simpa only [CFSG.GH74.GLS.pPrimeCoreOf] using
      (CFSG.GH74.Generic.BProg.map_pPrimeCoreOf_subgroupOf p hLX)
  rw [hLHS, hRHS] at hmap
  exact hmap

namespace P812Hyp

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

theorem commutator_mem₁ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    {S : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    {u v : G} (hu : u ∈ S) (hv : v ∈ S) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) :
    ⁅Subgroup.zpowers (u * v * u⁻¹ * v⁻¹), L₁⁆ ≤
      (CFSG.pPrimeCore p ↥L₁).map L₁.subtype := by
  have huM : (⟨u, hSM hu⟩ : ↥M) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hu3
  have hvM : (⟨v, hSM hv⟩ : ↥M) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hv3
  have hcore := commutator_mem_of_isPComponent h.prime hK hSch h714 h.comp₁ h.normal₁
    h.pRank_three_subgroupOf₁ (S := S.subgroupOf M) hS3.comap_subtype
    (u := ⟨u, hSM hu⟩) (v := ⟨v, hSM hv⟩) (Subgroup.mem_subgroupOf.mpr hu)
    (Subgroup.mem_subgroupOf.mpr hv) huM hvM
  exact map_commutator_zpowers_core_of_subgroup h.le₁ (hSM hu) (hSM hv) hcore

theorem commutator_mem₂ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    {S : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    {u v : G} (hu : u ∈ S) (hv : v ∈ S) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) :
    ⁅Subgroup.zpowers (u * v * u⁻¹ * v⁻¹), L₂⁆ ≤
      (CFSG.pPrimeCore p ↥L₂).map L₂.subtype := by
  haveI : Fact (Nat.Prime p) := ⟨h.prime⟩
  let X : Subgroup G := S ⊔ L₂
  have hSX : S ≤ X := le_sup_left
  have hL₂X : L₂ ≤ X := le_sup_right
  have hXM : X ≤ M := sup_le hSM h.le₂
  have hS_norm : S ≤ Subgroup.normalizer (L₂ : Set G) := by
    intro s hs
    apply h.mem_normalizer_two_of_odd hSch (hSM hs)
    obtain ⟨k, hk⟩ := hS3.exists_orderOf_eq_pow (⟨s, hs⟩ : S)
    rw [show orderOf s = 3 ^ k from (Subgroup.orderOf_coe (⟨s, hs⟩ : S)).trans hk]
    exact Odd.pow (n := k) (by norm_num : Odd (3 : ℕ))
  have hXN : X ≤ Subgroup.normalizer (L₂ : Set G) :=
    sup_le hS_norm (Subgroup.le_normalizer)
  have hLn : (L₂.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL₂X).mpr hXN
  have hL : CFSG.IsPComponent p (L₂.subgroupOf X) :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
      (L := L₂) (C := X) (A := M) hL₂X hXM h.comp₂
  have hLrank : CFSG.Open.pRank 3 (L₂.subgroupOf X) = 1 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three L₂ X
      hL₂X).trans h.rank_three₂
  have hSchX : CFSG.ComponentClassification.LBalance.SchreierSections ↥X :=
    hSch.of_injective (Subgroup.inclusion hXM) (Subgroup.inclusion_injective hXM)
  have hKX : CFSG.Open.IsKGroup ↥X := hK.of_le hXM
  have huX : (⟨u, hSX hu⟩ : ↥X) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hu3
  have hvX : (⟨v, hSX hv⟩ : ↥X) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hv3
  have hcore := commutator_mem_of_isPComponent h.prime hKX hSchX h714 hL hLn hLrank
    (S := S.subgroupOf X) hS3.comap_subtype
    (u := ⟨u, hSX hu⟩) (v := ⟨v, hSX hv⟩) (Subgroup.mem_subgroupOf.mpr hu)
    (Subgroup.mem_subgroupOf.mpr hv) huX hvX
  exact map_commutator_zpowers_core_of_subgroup hL₂X (hSX hu) (hSX hv) hcore

theorem commute_of_pow_three_eq_one (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    {S : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    {u v : G} (hu : u ∈ S) (hv : v ∈ S) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) :
    u * v = v * u := by
  let c : G := u * v * u⁻¹ * v⁻¹
  have hcS : c ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem hu hv) (S.inv_mem hu)) (S.inv_mem hv)
  have h1 := commutator_mem₁ h hSch hK h714 hSM hS3 hu hv hu3 hv3
  have h2 := commutator_mem₂ h hSch hK h714 hSM hS3 hu hv hu3 hv3
  have hc : c = 1 := hC c hcS h1 h2
  exact commutatorElement_eq_one_iff_mul_comm.mp hc

private def quotientSubgroupOfSupMap {G : Type} [Group G] {K C T : Subgroup G}
    [(C.subgroupOf T).Normal] (hT : K ⊔ C = T) :
    ↥T →* ↥(K.subgroupOf T ⊔ C.subgroupOf T) ⧸
      (C.subgroupOf T).subgroupOf (K.subgroupOf T ⊔ C.subgroupOf T) := by
  have hWtop : K.subgroupOf T ⊔ C.subgroupOf T = ⊤ := by
    have hsup := Subgroup.subgroupOf_sup (show K ≤ T by rw [← hT]; exact le_sup_left)
      (show C ≤ T by rw [← hT]; exact le_sup_right)
    rw [hT, Subgroup.subgroupOf_self] at hsup
    exact hsup.symm
  exact (QuotientGroup.mk' ((C.subgroupOf T).subgroupOf (K.subgroupOf T ⊔ C.subgroupOf T))).comp
    ((Subgroup.inclusion hWtop.ge).comp (Subgroup.topEquiv (G := ↥T)).symm.toMonoidHom)

private theorem ker_quotientSubgroupOfSupMap
    {G : Type} [Group G] {K C T : Subgroup G} [(C.subgroupOf T).Normal]
    (hT : K ⊔ C = T) :
    ∀ t : ↥T, quotientSubgroupOfSupMap hT t = 1 ↔ (t : G) ∈ C := by
  have hWtop : K.subgroupOf T ⊔ C.subgroupOf T = ⊤ := by
    have hsup := Subgroup.subgroupOf_sup (show K ≤ T by rw [← hT]; exact le_sup_left)
      (show C ≤ T by rw [← hT]; exact le_sup_right)
    rw [hT, Subgroup.subgroupOf_self] at hsup
    exact hsup.symm
  intro t
  change QuotientGroup.mk' ((C.subgroupOf T).subgroupOf (K.subgroupOf T ⊔ C.subgroupOf T))
    (((Subgroup.inclusion hWtop.ge).comp
      (Subgroup.topEquiv (G := ↥T)).symm.toMonoidHom) t) = 1 ↔ _
  constructor
  · intro ht
    have hmem : (Subgroup.inclusion hWtop.ge
        ((Subgroup.topEquiv (G := ↥T)).symm t)) ∈
        (C.subgroupOf T).subgroupOf (K.subgroupOf T ⊔ C.subgroupOf T) :=
      (QuotientGroup.eq_one_iff _).mp ht
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hmem)
  · intro ht
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ht))

private theorem pRank_quotient_subgroupOf_sup_le_one
    {G : Type} [Group G] [Finite G] {K C T : Subgroup G} [(C.subgroupOf T).Normal]
    (hKT : K ≤ T) (hCT : C ≤ T) (hT : K ⊔ C = T)
    (hKrank : CFSG.Open.pRank 3 K = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥(K.subgroupOf T ⊔ C.subgroupOf T) ⧸
      (C.subgroupOf T).subgroupOf (K.subgroupOf T ⊔ C.subgroupOf T))) ≤ 1 := by
  let H : Subgroup ↥T := K.subgroupOf T
  let N : Subgroup ↥T := C.subgroupOf T
  let W : Subgroup ↥T := H ⊔ N
  have hWtop : W = ⊤ := by
    have hsup := Subgroup.subgroupOf_sup hKT hCT
    rw [hT, Subgroup.subgroupOf_self] at hsup
    exact hsup.symm
  let Y : Type := ↥W ⧸ N.subgroupOf W
  have hYrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1 := by
    let e : (H ⧸ N.subgroupOf H) ≃* Y :=
      QuotientGroup.quotientInfEquivProdNormalQuotient H N
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (H ⧸ N.subgroupOf H)) ≤ 1 := by
      by_contra hlt
      have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (H ⧸ N.subgroupOf H)) := by omega
      have h2H := CFSG.GroupTheory.two_le_pRank_of_quotient (N.subgroupOf H)
        Nat.prime_three (by norm_num) h2
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H] at h2H
      have hHL : CFSG.Open.pRank 3 H = CFSG.Open.pRank 3 K :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf 3 Nat.prime_three K T hKT
      have h2L : 2 ≤ CFSG.Open.pRank 3 K := hHL ▸ h2H
      rw [hKrank] at h2L
      omega
    calc CFSG.Open.pRank 3 (⊤ : Subgroup Y)
        = CFSG.Open.pRank 3 (⊤ : Subgroup (H ⧸ N.subgroupOf H)) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).symm
      _ ≤ 1 := h1
  exact hYrank

private theorem isCyclic_map_inf_subgroupOf_of_pRank_top_le_one
    {G Y : Type} [Group G] [Group Y] [Finite G] [Finite Y] {S T : Subgroup G} (φ : ↥T →* Y)
    (hS3 : IsPGroup 3 S)
    (hYrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) :
    IsCyclic ↥(((S ⊓ T).subgroupOf T).map φ) := by
  classical
  let R : Subgroup G := S ⊓ T
  have hR3 : IsPGroup 3 R := hS3.to_le inf_le_left
  let RY : Subgroup Y := (R.subgroupOf T).map φ
  have hRYp : IsPGroup 3 ↥RY := (hR3.comap_subtype).map φ
  have hRYrank : CFSG.pRank 3 ↥RY ≤ 1 := by
    have hRYopen : CFSG.Open.pRank 3 RY ≤ 1 :=
      (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) (le_top : RY ≤ ⊤)).trans hYrank
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup RY]
    exact hRYopen
  exact CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
    Nat.prime_three (by norm_num) hRYp hRYrank

private theorem orderOf_map_eq_three_of_mem_inf_eq_bot
    {G Y : Type} [Group G] [Group Y] {T A C : Subgroup G} {φ : ↥T →* Y}
    (hAT : A ≤ T) (hAC : A ⊓ C = ⊥)
    (hφker : ∀ t : ↥T, φ t = 1 ↔ (t : G) ∈ C)
    {a : G} (haA : a ∈ A) (haord : orderOf a = 3) :
    orderOf (φ ⟨a, hAT haA⟩) = 3 := by
  have haT : a ∈ T := hAT haA
  have haY3 : (φ ⟨a, haT⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨a, haT⟩ : ↥T) ^ 3 = 1 := by
      apply Subtype.ext
      simpa [haord] using pow_orderOf_eq_one a
    rw [h3, map_one]
  have haY1 : φ ⟨a, haT⟩ ≠ 1 := by
    intro h1
    have hamem : a ∈ C := (hφker ⟨a, haT⟩).mp h1
    have hmem : a ∈ A ⊓ C := Subgroup.mem_inf.mpr ⟨haA, hamem⟩
    rw [hAC] at hmem
    have ha1 : a = 1 := Subgroup.mem_bot.mp hmem
    rw [ha1, orderOf_one] at haord
    omega
  exact orderOf_eq_prime haY3 haY1

private theorem map_subtype_pow_eq_one
    {G Y : Type} [Group G] [Group Y] {T : Subgroup G} {φ : ↥T →* Y}
    {x : G} (hxT : x ∈ T) {n : ℕ} (hx : x ^ n = 1) :
    (φ ⟨x, hxT⟩) ^ n = 1 := by
  rw [← map_pow]
  have h : (⟨x, hxT⟩ : ↥T) ^ n = 1 := Subtype.ext hx
  rw [h, map_one]

private theorem mem_map_inf_subgroupOf
    {G Y : Type} [Group G] [Group Y] {S T : Subgroup G} {φ : ↥T →* Y} {x : G}
    (hxS : x ∈ S) (hxT : x ∈ T) :
    φ ⟨x, hxT⟩ ∈ ((S ⊓ T).subgroupOf T).map φ :=
  Subgroup.mem_map.mpr ⟨⟨x, hxT⟩, Subgroup.mem_subgroupOf.mpr ⟨hxS, hxT⟩, rfl⟩

private theorem zpowers_le_of_isCyclic
    {Y : Type} [Group Y] [Finite Y] {RY : Subgroup Y} [IsCyclic ↥RY] {x a : Y}
    (hxRY : x ∈ RY) (haRY : a ∈ RY) (haord : orderOf a = 3) (hx3 : x ^ 3 = 1) :
    Subgroup.zpowers x ≤ Subgroup.zpowers a := by
  have hxRY' : Subgroup.zpowers x ≤ RY := Subgroup.zpowers_le.mpr hxRY
  have haRY' : Subgroup.zpowers a ≤ RY := Subgroup.zpowers_le.mpr haRY
  have hle' : (Subgroup.zpowers x).subgroupOf RY ≤
      (Subgroup.zpowers a).subgroupOf RY := by
    rw [IsCyclic.subgroup_le_iff_card_dvd]
    have hxcard : Nat.card ↥((Subgroup.zpowers x).subgroupOf RY) ∣ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxRY').toEquiv, Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hx3
    have hacard : Nat.card ↥((Subgroup.zpowers a).subgroupOf RY) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe haRY').toEquiv, Nat.card_zpowers,
        haord]
    rw [hacard]
    exact hxcard
  intro y hy
  have hyR : y ∈ RY := hxRY' hy
  let yR : ↥RY := ⟨y, hyR⟩
  have hy' : yR ∈ (Subgroup.zpowers x).subgroupOf RY := Subgroup.mem_subgroupOf.mpr hy
  exact Subgroup.mem_subgroupOf.mp (hle' hy')

private theorem exists_mem_of_isCyclic_image
    {G Y : Type} [Group G] [Group Y] [Finite G] [Finite Y]
    {T A C S : Subgroup G} {φ : ↥T →* Y} {x : G}
    (hAT : A ≤ T) (hAS : A ≤ S) (hA3 : Nat.card A = 3)
    (hAC : A ⊓ C = ⊥)
    (hφker : ∀ t : ↥T, φ t = 1 ↔ (t : G) ∈ C)
    (hRYcyc : IsCyclic ↥(((S ⊓ T).subgroupOf T).map φ))
    (hxS : x ∈ S) (hxT : x ∈ T) (hx3 : x ^ 3 = 1) :
    ∃ a ∈ A, x * a⁻¹ ∈ C := by
  classical
  obtain ⟨aA, haAord⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 3 (by rw [hA3])
  let a : G := (aA : G)
  have haA : a ∈ A := aA.2
  have haord : orderOf a = 3 := (Subgroup.orderOf_coe aA).trans haAord
  let aY : Y := φ ⟨a, hAT haA⟩
  let xY : Y := φ ⟨x, hxT⟩
  have haYord : orderOf aY = 3 :=
    orderOf_map_eq_three_of_mem_inf_eq_bot hAT hAC hφker haA haord
  have hxY3 : xY ^ 3 = 1 := map_subtype_pow_eq_one hxT hx3
  have hxRY : xY ∈ ((S ⊓ T).subgroupOf T).map φ := mem_map_inf_subgroupOf hxS hxT
  have haRY : aY ∈ ((S ⊓ T).subgroupOf T).map φ :=
    mem_map_inf_subgroupOf (hAS haA) (hAT haA)
  have hle : Subgroup.zpowers xY ≤ Subgroup.zpowers aY :=
    zpowers_le_of_isCyclic hxRY haRY haYord hxY3
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers xY))
  let b : G := a ^ n
  have hbA : b ∈ A := Subgroup.zpow_mem A haA n
  have hbY : φ ⟨b, hAT hbA⟩ = xY := by
    change φ ⟨b, _⟩ = φ ⟨x, hxT⟩
    have hbT : (⟨b, hAT hbA⟩ : ↥T) = (⟨a, hAT haA⟩ : ↥T) ^ n := by
      apply Subtype.ext
      rfl
    rw [hbT, map_zpow]
    exact hn
  have hker : x * b⁻¹ ∈ C := by
    have hxbT : x * b⁻¹ ∈ T :=
      T.mul_mem hxT (T.inv_mem (hAT hbA))
    have h1 : φ ⟨x * b⁻¹, hxbT⟩ = 1 := by
      rw [show (⟨x * b⁻¹, hxbT⟩ : ↥T) =
        ⟨x, hxT⟩ * (⟨b, hAT hbA⟩ : ↥T)⁻¹ from Subtype.ext rfl]
      rw [map_mul, map_inv, hbY]
      exact mul_inv_cancel xY
    exact (hφker _).mp h1
  exact ⟨b, hbA, hker⟩

private theorem mem_center_mk_pPrimeCore_of_mem_centralizerSection
    {G : Type} [Group G] {p : ℕ} {K : Subgroup G} {a : G} (haK : a ∈ K)
    (haC : a ∈ CFSG.GH74.GLS.centralizerSection K
      ((CFSG.pPrimeCore p ↥K).map K.subtype)) :
    QuotientGroup.mk' (CFSG.pPrimeCore p ↥K) (⟨a, haK⟩ : ↥K) ∈
      Subgroup.center (↥K ⧸ CFSG.pPrimeCore p ↥K) := by
  let P : Subgroup ↥K := CFSG.pPrimeCore p ↥K
  let Q : Subgroup G := (CFSG.pPrimeCore p ↥K).map K.subtype
  have haC' := haC
  change a ∈ Subgroup.normalizer (K : Set G) ∧ a ∈ Subgroup.normalizer (Q : Set G) ∧
    ∀ y ∈ K, ⁅y, a⁆ ∈ Q at haC'
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective P y
  have hcommQ : ⁅(y' : G), a⁆ ∈ Q := haC'.2.2 (y' : G) y'.2
  obtain ⟨p, hpP, hpval⟩ := Subgroup.mem_map.mp hcommQ
  have hmemL : ⁅(y' : G), a⁆ ∈ K :=
    Subgroup.commutator_le_self K (Subgroup.commutator_mem_commutator y'.2 haK)
  let cL : ↥K := ⟨⁅(y' : G), a⁆, hmemL⟩
  have hcLp : cL = p := Subtype.ext hpval.symm
  have hcommP : ⁅y', (⟨a, haK⟩ : ↥K)⁆ ∈ P := by
    have hEq : ⁅y', (⟨a, haK⟩ : ↥K)⁆ = cL := by
      apply Subtype.ext
      rfl
    rw [hEq, hcLp]
    exact hpP
  have hcommQ' : QuotientGroup.mk' P ⁅y', (⟨a, haK⟩ : ↥K)⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hcommP
  rw [map_commutatorElement] at hcommQ'
  exact commutatorElement_eq_one_iff_mul_comm.mp hcommQ'

private theorem false_of_mem_centralizerSection_of_orderOf_eq_three
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {M K : Subgroup G}
    (hLK : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPComponentIn p K M)
    (hK3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hKrank : CFSG.Open.pRank 3 K = 1)
    {a : G} (haK : a ∈ K) (haord : orderOf a = 3)
    (haC : a ∈ CFSG.GH74.GLS.centralizerSection K
      ((CFSG.pPrimeCore p ↥K).map K.subtype)) : False := by
  let P : Subgroup ↥K := CFSG.pPrimeCore p ↥K
  let Q : Subgroup G := (CFSG.pPrimeCore p ↥K).map K.subtype
  have haP : (⟨a, haK⟩ : ↥K) ∉ P := by
    intro hP
    have haQ : a ∈ Q := Subgroup.mem_map.mpr ⟨⟨a, haK⟩, hP, rfl⟩
    have hdvd : orderOf a ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q haQ
    have hcard : Nat.card Q = Nat.card P :=
      Subgroup.card_map_of_injective K.subtype_injective
    rw [hcard, haord] at hdvd
    exact hK3 hdvd
  have hcenter : QuotientGroup.mk' P (⟨a, haK⟩ : ↥K) ∈
      Subgroup.center (↥K ⧸ P) :=
    mem_center_mk_pPrimeCore_of_mem_centralizerSection haK haC
  have ha3 : a ^ 3 = 1 := by
    rw [← haord]
    exact pow_orderOf_eq_one a
  have habar3 : (QuotientGroup.mk' P (⟨a, haK⟩ : ↥K)) ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (by
      rw [show ((⟨a, haK⟩ : ↥K) ^ 3) = 1 from Subtype.ext ha3]
      exact P.one_mem)
  have habar1 : QuotientGroup.mk' P (⟨a, haK⟩ : ↥K) ≠ 1 := by
    intro h1
    exact haP ((QuotientGroup.eq_one_iff _).mp h1)
  have habarord : orderOf (QuotientGroup.mk' P (⟨a, haK⟩ : ↥K)) = 3 :=
    orderOf_eq_prime habar3 habar1
  have h3center : 3 ∣ Nat.card (Subgroup.center (↥K ⧸ P)) := by
    have hcard : Nat.card (Subgroup.zpowers
        (QuotientGroup.mk' P (⟨a, haK⟩ : ↥K))) = 3 := by
      rw [Nat.card_zpowers, habarord]
    rw [← hcard]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hcenter)
  have hcenterrank : CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ P)) = 1 := by
    rw [CFSG.SectionRank.pRank_quotient_eq P hK3,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
    exact hKrank
  have hquo : CFSG.IsQuasisimple (↥K ⧸ P) :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPComponentIn.isQuasisimple_quot hp hLK
  haveI : Group.IsPerfect (↥K ⧸ P) := hquo.1
  exact (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.not_dvd_card_center_of_pRank_eq_one
    (X := ↥K ⧸ P) (q := 3) (by norm_num) hcenterrank) h3center

private theorem pPrimeCore_inf_centralizerSection_eq_bot
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {M K : Subgroup G}
    (hLK : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPComponentIn p K M)
    (hK3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hKrank : CFSG.Open.pRank 3 K = 1)
    {A : Subgroup G} (hA : A ≤ K) (hA3 : Nat.card A = 3) :
    A ⊓ CFSG.GH74.GLS.centralizerSection K
      ((CFSG.pPrimeCore p ↥K).map K.subtype) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  by_contra ha1
  have ha3 : a ^ 3 = 1 := by
    have hdvd : orderOf a ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard A ha.1
      rwa [hA3] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · rw [← h3]; exact pow_orderOf_eq_one a
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  exact false_of_mem_centralizerSection_of_orderOf_eq_three hp hLK hK3 hKrank
    (hA ha.1) haord ha.2

private theorem mem_centralizerSection_of_normal (hp : p.Prime)
    {K : Subgroup G}
    (hLK : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPComponentIn p K M)
    (hK3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hKrank : CFSG.Open.pRank 3 K = 1)
    {S A : Subgroup G} (hS3 : IsPGroup 3 S)
    (hA : A ≤ K) (hAS : A ≤ S) (hA3 : Nat.card A = 3)
    {x : G} (hxS : x ∈ S) (hx3 : x ^ 3 = 1)
    (hxL : x ∈ K ⊔ CFSG.GH74.GLS.centralizerSection K
      ((CFSG.pPrimeCore p ↥K).map K.subtype)) :
    ∃ a ∈ A, x * a⁻¹ ∈ CFSG.GH74.GLS.centralizerSection K
      ((CFSG.pPrimeCore p ↥K).map K.subtype) := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup G := (CFSG.pPrimeCore p ↥K).map K.subtype
  let C : Subgroup G := CFSG.GH74.GLS.centralizerSection K Q
  let T : Subgroup G := K ⊔ C
  have hQnK : ∀ l ∈ K, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q := by
    intro l hl q hq
    obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
    refine Subgroup.mem_map.mpr ⟨⟨l, hl⟩ * q' * ⟨l, hl⟩⁻¹, ?_, rfl⟩
    exact (CFSG.pPrimeCore_normal (p := p) (G := ↥K)).conj_mem q' hq' ⟨l, hl⟩
  have hKNQ : K ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact hQnK
  have hKNC : K ≤ Subgroup.normalizer (C : Set G) :=
    CFSG.RankThree.PartTwo.Sec15.Proof155w2.le_normalizer_centralizerSection
      (Subgroup.le_normalizer) hKNQ
  have hCT : C ≤ T := le_sup_right
  have hTNC : T ≤ Subgroup.normalizer (C : Set G) :=
    sup_le hKNC (Subgroup.le_normalizer)
  have hKnorm : (C.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCT).mpr hTNC
  let H : Subgroup ↥T := K.subgroupOf T
  let N : Subgroup ↥T := C.subgroupOf T
  let W : Subgroup ↥T := H ⊔ N
  have hWtop : W = ⊤ := by
    have hsup := Subgroup.subgroupOf_sup (show K ≤ T from le_sup_left)
      (show C ≤ T from le_sup_right)
    rw [show K ⊔ C = T from rfl, Subgroup.subgroupOf_self] at hsup
    exact hsup.symm
  let Y : Type := ↥W ⧸ N.subgroupOf W
  have hYrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1 :=
    pRank_quotient_subgroupOf_sup_le_one (C := C) (T := T)
      (show K ≤ T from le_sup_left) (show C ≤ T from le_sup_right) rfl hKrank
  let φ : ↥T →* Y := quotientSubgroupOfSupMap (K := K) (C := C) (T := T) rfl
  have hφker : ∀ t : ↥T, φ t = 1 ↔ (t : G) ∈ C :=
    ker_quotientSubgroupOfSupMap (K := K) (C := C) (T := T) rfl
  have hRYcyc : IsCyclic ↥(((S ⊓ T).subgroupOf T).map φ) :=
    isCyclic_map_inf_subgroupOf_of_pRank_top_le_one φ hS3 hYrank
  have hAC : A ⊓ C = ⊥ :=
    pPrimeCore_inf_centralizerSection_eq_bot hp hLK hK3 hKrank hA hA3
  exact exists_mem_of_isCyclic_image (T := T) (A := A) (C := C) (S := S) (φ := φ) (x := x)
    (by intro a ha; exact Subgroup.mem_sup_left (hA ha)) hAS hA3 hAC hφker hRYcyc hxS hxL hx3

theorem mem_centralizerSection_of_mem_sup₁ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    {S A₁ : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3) {x : G}
    (hxS : x ∈ S) (hx3 : x ^ 3 = 1)
    (hxL : x ∈ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype)) :
    ∃ a ∈ A₁, x * a⁻¹ ∈ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) :=
  mem_centralizerSection_of_normal h.prime ⟨h.le₁, h.comp₁⟩
    (h.not_three_dvd_card_pPrimeCore₁ hSch) h.rank_three₁ hS3 hA₁ hA₁S hA₁3 hxS hx3 hxL

theorem mem_centralizerSection_of_mem_sup₂ (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    {S A₂ : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3) {x : G}
    (hxS : x ∈ S) (hx3 : x ^ 3 = 1)
    (hxL : x ∈ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)) :
    ∃ a ∈ A₂, x * a⁻¹ ∈ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) :=
  mem_centralizerSection_of_normal h.prime ⟨h.le₂, h.comp₂⟩
    (h.not_three_dvd_card_pPrimeCore₂ hSch) h.rank_three₂ hS3 hA₂ hA₂S hA₂3 hxS hx3 hxL

end P812Hyp
end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
