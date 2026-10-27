module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEBar
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Type
import CFSG.Walter.AStar.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellShort
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepA

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

private theorem pCoreOf_inf_eq_pCoreOf_eh21 {G B : Subgroup Ω} (hBG : B ≤ G)
    (hsub : (B.subgroupOf G).IsSubnormal) : pCoreOf 2 G ⊓ B = pCoreOf 2 B := by
  refine le_antisymm ?_ ?_
  · have hnorm : B ≤ Subgroup.normalizer ((pCoreOf 2 G ⊓ B : Subgroup Ω) : Set Ω) := by
      rw [Subgroup.le_normalizer_iff]
      intro b hb x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp
          (hBG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G) hb) x).mp hx.1,
        B.mul_mem (B.mul_mem hb hx.2) (B.inv_mem hb)⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G).to_le inf_le_left)
  · exact le_inf (CFSG.QuasithinUnique.Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hBG hsub)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 B)

private theorem subgroupOf_centralizer_eq_pCore_eh21 {G B : Subgroup Ω} (hBG : B ≤ G)
    (hsub : (B.subgroupOf G).IsSubnormal)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    (Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf B = CFSG.pCore 2 ↥B := by
  apply Subgroup.map_injective B.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype]
  show Subgroup.centralizer (gomiV G : Set Ω) ⊓ B = pCoreOf 2 B
  have hCB : Subgroup.centralizer (gomiV G : Set Ω) ⊓ B = pCoreOf 2 G ⊓ B := by
    rw [← hCQ]
    rw [show (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊓ B =
        (G ⊓ B) ⊓ Subgroup.centralizer (gomiV G : Set Ω) by ac_rfl,
      inf_eq_right.mpr hBG, inf_comm]
  rw [hCB, pCoreOf_inf_eq_pCoreOf_eh21 hBG hsub]

omit [Finite Ω] in
private theorem exists_pow_mem_centralizer_of_mem_gomiBarPre_eh21
    (P : Subgroup ↥(autOn G (gomiV G))) (hP2 : IsPGroup 2 P) {x : Ω}
    (hx : x ∈ gomiBarPre G P) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (gomiV G : Set Ω) := by
  have hxG : x ∈ G := gomiBarPre_le G P hx
  have hxP : gomiBar G ⟨x, hxG⟩ ∈ P := by
    rw [gomiBarPre, Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Subgroup.mem_comap] at hy
    have : (⟨x, hxG⟩ : ↥G) = y := Subtype.ext hyx.symm
    rw [this]
    exact hy
  obtain ⟨k, hk⟩ := hP2 ⟨gomiBar G ⟨x, hxG⟩, hxP⟩
  refine ⟨k, ?_⟩
  have hk' : (gomiBar G ⟨x, hxG⟩ : ↥(autOn G (gomiV G))) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hker : (⟨x, hxG⟩ : ↥G) ^ 2 ^ k ∈ (gomiBar G).ker := by
    rw [MonoidHom.mem_ker, map_pow, hk']
  rw [gomiBar_ker G, Subgroup.mem_subgroupOf] at hker
  simpa using hker

omit [Finite Ω] in
private theorem le_normalizer_gomiBarPre_eh21
    (P : Subgroup ↥(autOn G (gomiV G))) (hP : P.Normal) :
    G ≤ Subgroup.normalizer (gomiBarPre G P : Set Ω) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := gomiBarPre_map_conj G P ⟨g, hg⟩
  have hconj : P.map (MulAut.conj (gomiBar G ⟨g, hg⟩)).toMonoidHom = P :=
    Subgroup.Normal.map_conj_eq (H := P) (g := gomiBar G ⟨g, hg⟩)
  rw [hconj] at h1
  exact h1.symm

private theorem commute_conj_gomiBarOf_eh21 {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hQbar : CFSG.IsQuasisimple ↥(gomiBarOf G B)) :
    ∀ g : ↥(autOn G (gomiV G)),
      (gomiBarOf G B).map (MulAut.conj g).toMonoidHom ≠ gomiBarOf G B →
      ⁅gomiBarOf G B, (gomiBarOf G B).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hcomp : CFSG.IsComponent (gomiBarOf G B) :=
    ⟨hQbar, by rw [gomiBarOf_eq_map hB.le]; exact hB.subnormal.map (gomiBar_surjective G)⟩
  intro g hg
  have hcompg : CFSG.IsComponent ((gomiBarOf G B).map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hcomp
  rcases CFSG.LocalCores.distinct_components_commute hcomp hcompg with h | h
  · exact absurd h.symm hg
  · exact h

private theorem isPGroup_quotient_normalClosure_eh21 {B : Subgroup Ω}
    (hB : IsGomiTwoComponent G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S) :
    IsPGroup 2 (↥(autOn G (gomiV G)) ⧸
      Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G)))) := by
  obtain ⟨S, hS⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf G
  have hNcG : conjClosure B G ≤ G := le_sup_left.trans (le_of_eq (hGB S hS).symm)
  have hSG : S ≤ G := hS.1
  have hsup : (conjClosure B G).subgroupOf G ⊔ S.subgroupOf G = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNcG hSG, ← hGB S hS, Subgroup.subgroupOf_self]
  have htop : gomiBarOf G (conjClosure B G) ⊔ gomiBarOf G S = ⊤ := by
    have h := congrArg (Subgroup.map (gomiBar G)) hsup
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective (gomiBar G) (gomiBar_surjective G),
      ← gomiBarOf_eq_map hNcG, ← gomiBarOf_eq_map hSG] at h
    exact h
  let Nbar : Subgroup ↥(autOn G (gomiV G)) :=
    Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G)))
  have hsupBar : (⊤ : Subgroup ↥(autOn G (gomiV G))) = Nbar ⊔ gomiBarOf G S := by
    rw [← htop, gomiBarOf_conjClosure hB.le]
  have hNbot : Nbar.map (QuotientGroup.mk' Nbar) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact (QuotientGroup.ker_mk' Nbar).ge
  have hmap : (gomiBarOf G S).map (QuotientGroup.mk' Nbar) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' Nbar)) hsupBar
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective Nbar), hNbot, bot_sup_eq] at h
    exact h.symm
  have hSbar : IsPGroup 2 (gomiBarOf G S) := by
    rw [gomiBarOf_eq_map hSG]
    exact IsPGroup.map ((hS.2.1).of_equiv (Subgroup.subgroupOfEquivOfLe hSG).symm)
      (gomiBar G)
  have hq := IsPGroup.map hSbar (QuotientGroup.mk' Nbar)
  rw [hmap] at hq
  exact hq.of_equiv Subgroup.topEquiv

theorem nonempty_mulEquiv_gomiBarOf {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    Nonempty ((↥B ⧸ CFSG.pCore 2 ↥B) ≃* ↥(gomiBarOf G B)) := by
  obtain ⟨-, ψ, hψsurj, hψker⟩ :=
    gomi_moduleSetting (H := B) (U := gomiV G) (gomiV_moduleSetting G).1
      (hB.le.trans (gomiV_moduleSetting G).2)
  have hker : ψ.ker = CFSG.pCore 2 ↥B := by
    rw [hψker]
    exact subgroupOf_centralizer_eq_pCore_eh21 hB.le hB.subnormal hCQ
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (φ := ψ) hψsurj).trans
      (Subgroup.subgroupOfEquivOfLe (CFSG.Quasithin.AutOn.autOn_mono hB.le)).symm)⟩

theorem even_card_gomiBarOf {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hBt : IsGomi410Type G B)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    Even (Nat.card ↥(gomiBarOf G B)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_gomiBarOf hB hCQ
  rw [(Nat.card_congr e.toEquiv).symm]
  have hQ := IsGomi410Type.isQuasisimple hB hBt
  have hsimple : IsSimpleGroup ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸
      Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B)) := hQ.2.1
  refine even_iff_two_dvd.mpr ((even_iff_two_dvd.mp ?_).trans
    (Subgroup.card_quotient_dvd_card (Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B))))
  exact CFSG.Walter.even_card_of_isSimpleGroup hQ.2.2

omit [Finite Ω] in
theorem isSubnormal_gomiBarOf {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) :
    (gomiBarOf G B).IsSubnormal := by
  rw [gomiBarOf_eq_map hB.le]
  exact hB.subnormal.map (gomiBar_surjective G)

theorem gomiHyp21_gomiBarOf {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    GomiHyp21 (gomiBarOf G B) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_gomiBarOf hB hCQ
  have hQbar : CFSG.IsQuasisimple ↥(gomiBarOf G B) :=
    (IsGomi410Type.isQuasisimple hB hBt).of_mulEquiv e.symm
  exact ⟨⟨commute_conj_gomiBarOf_eh21 hB hQbar,
    isPGroup_quotient_normalClosure_eh21 hB hGB⟩, hQbar⟩

theorem Gomi410Cex.eq_bot_of_normal_autOn (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    (P : Subgroup ↥(autOn G (gomiV G))) (hP : P.Normal) (h2 : IsPGroup 2 P) : P = ⊥ := by
  have hNG : gomiBarPre G P ≤ G := gomiBarPre_le G P
  have hCN : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ gomiBarPre G P := by
    intro x hx
    obtain ⟨hxG, hxC⟩ := hx
    rw [gomiBarPre, Subgroup.mem_map]
    refine ⟨⟨x, hxG⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hker : (⟨x, hxG⟩ : ↥G) ∈ (gomiBar G).ker := by
      rw [gomiBar_ker G, Subgroup.mem_subgroupOf]
      exact hxC
    rw [MonoidHom.mem_ker] at hker
    rw [hker]
    exact P.one_mem
  have hNnorm : G ≤ Subgroup.normalizer (gomiBarPre G P : Set Ω) :=
    le_normalizer_gomiBarPre_eh21 P hP
  have h2' : ∀ x ∈ gomiBarPre G P,
      ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (gomiV G : Set Ω) :=
    fun x hx => exists_pow_mem_centralizer_of_mem_gomiBarPre_eh21 P h2 hx
  have hNC := h.le_centralizer_of_normal hfZ hchar hmono hCN hNG hNnorm h2'
  have hbot : gomiBarOf G (gomiBarPre G P) = ⊥ := by
    show (autOn (gomiBarPre G P) (gomiV G)).subgroupOf (autOn G (gomiV G)) = ⊥
    rw [CFSG.Quasithin.AutOn.autOn_eq_bot_of_le_centralizer hNC]
    simp
  calc P = gomiBarOf G (gomiBarPre G P) := (gomiBarOf_gomiBarPre G P).symm
    _ = ⊥ := hbot

end CFSG.GroupTheory

end
