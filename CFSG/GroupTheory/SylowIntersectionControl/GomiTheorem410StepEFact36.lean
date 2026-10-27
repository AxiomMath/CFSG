module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEOffender
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepESylow
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.GroupTheory.SylowIntersectionControl.Regular
import CFSG.Quasithin.Background.AutOnFixV
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne
open scoped IsMulCommutative Pointwise

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

private theorem normalClosure_le_normalizer_ef36 {H : Type*} [Group H] {L : Subgroup H}
    (hcomm : ∀ g : H, L.map (MulAut.conj g).toMonoidHom ≠ L →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    Subgroup.normalClosure (L : Set H) ≤ Subgroup.normalizer (L : Set H) := by
  rw [Subgroup.normalClosure]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rw [Group.mem_conjugatesOfSet_iff] at hx
  obtain ⟨a, ha, hconj⟩ := hx
  rw [isConj_iff] at hconj
  obtain ⟨c, rfl⟩ := hconj
  have hle : L.map (MulAut.conj c).toMonoidHom ≤ Subgroup.normalizer (L : Set H) := by
    by_cases hc : L.map (MulAut.conj c).toMonoidHom = L
    · rw [hc]; exact Subgroup.le_normalizer
    · have h : ⁅L.map (MulAut.conj c).toMonoidHom, L⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hcomm c hc
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
        (Subgroup.centralizer_le_normalizer (L : Set H))
  exact hle (Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom ha)

private theorem normalClosure_le_comap_fixingSubgroup_ef36
    {H M W : Type*} [Group H] [Group M] [MulAction M W]
    (φ : H →* M) (T : Set W) {L S : Subgroup H}
    (hNL : Subgroup.normalClosure (L : Set H) ≤ Subgroup.normalizer (L : Set H))
    (htop : (⊤ : Subgroup H) = Subgroup.normalClosure (L : Set H) ⊔ S)
    (hL : L ≤ (fixingSubgroup M T).comap φ) (hS : S ≤ (fixingSubgroup M T).comap φ) :
    Subgroup.normalClosure (L : Set H) ≤ (fixingSubgroup M T).comap φ := by
  rw [Subgroup.normalClosure]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rw [Group.mem_conjugatesOfSet_iff] at hx
  obtain ⟨a, ha, hconj⟩ := hx
  rw [isConj_iff] at hconj
  obtain ⟨c, rfl⟩ := hconj
  have hc : c ∈ S ⊔ Subgroup.normalClosure (L : Set H) := by
    rw [sup_comm, ← htop]; trivial
  have hc' : c ∈ ((S : Set H) * (Subgroup.normalClosure (L : Set H) : Set H)) := by
    rw [← Subgroup.mul_normal S (Subgroup.normalClosure (L : Set H))]
    exact hc
  obtain ⟨s, hs, n, hn, hsn⟩ := Set.mem_mul.mp hc'
  rw [← hsn]
  have hnL : MulAut.conj n a ∈ L := by
    have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNL hn)
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom ha
  change φ (s * n * a * (s * n)⁻¹) ∈ fixingSubgroup M T
  have heq : φ ((s * n) * a * (s * n)⁻¹) = φ s * φ (MulAut.conj n a) * (φ s)⁻¹ := by
    rw [MulAut.conj_apply]
    simp only [map_mul, map_inv]
    group
  rw [heq]
  exact (fixingSubgroup M T).mul_mem ((fixingSubgroup M T).mul_mem (hS hs) (hL hnL))
    ((fixingSubgroup M T).inv_mem (hS hs))

private lemma subgroupOf_map_subtype_eq_ef36 {M : Type*} [Group M] {Y : Subgroup M}
    {K : Subgroup ↥Y} : (K.map Y.subtype).subgroupOf Y = K := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Y.subtype_injective hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [Finite Ω] in
private theorem top_eq_normalClosure_gomiBarOf_sup_ef36 {B T : Subgroup Ω}
    {S : Subgroup (MulAut ↥(gomiV G))} (hBG : B ≤ G)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hT : IsSylowTwoOf T G) (hTS : autOn T (gomiV G) = S) :
    (⊤ : Subgroup ↥(autOn G (gomiV G))) =
      Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) ⊔
        S.subgroupOf (autOn G (gomiV G)) := by
  have hNcG : conjClosure B G ≤ G := le_sup_left.trans (le_of_eq (hGB T hT).symm)
  have hsup : (conjClosure B G).subgroupOf G ⊔ T.subgroupOf G = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNcG hT.1, ← hGB T hT, Subgroup.subgroupOf_self]
  have h := congrArg (Subgroup.map (gomiBar G)) hsup
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective (gomiBar G) (gomiBar_surjective G),
    ← gomiBarOf_eq_map hNcG, ← gomiBarOf_eq_map hT.1] at h
  have hST : gomiBarOf G T = S.subgroupOf (autOn G (gomiV G)) := by
    show (autOn T (gomiV G)).subgroupOf (autOn G (gomiV G)) =
      S.subgroupOf (autOn G (gomiV G))
    rw [hTS]
  rw [gomiBarOf_conjClosure hBG, hST] at h
  exact h.symm

private theorem normalClosure_map_subtype_le_fixingSubgroup_ef36 {B : Subgroup Ω}
    (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {S : Subgroup (MulAut ↥(gomiV G))} {T : Subgroup Ω}
    (hT : IsSylowTwoOf T G) (hTS : autOn T (gomiV G) = S)
    (hfix : fixV S ≤ fixV (autOn B (gomiV G))) :
    (Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G)))).map
        (autOn G (gomiV G)).subtype ≤
      fixingSubgroup (MulAut ↥(gomiV G)) (fixV S : Set ↥(gomiV G)) := by
  have hNL : Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) ≤
      Subgroup.normalizer ((gomiBarOf G B : Subgroup ↥(autOn G (gomiV G))) :
        Set ↥(autOn G (gomiV G))) :=
    normalClosure_le_normalizer_ef36 (gomiHyp21_gomiBarOf hB hBt hGB hCQ).commute
  have htopY := top_eq_normalClosure_gomiBarOf_sup_ef36 hB.le hGB hT hTS
  have hL_le : gomiBarOf G B ≤
      (fixingSubgroup (MulAut ↥(gomiV G)) (fixV S : Set ↥(gomiV G))).comap
        (autOn G (gomiV G)).subtype := by
    intro x hx
    rw [Subgroup.mem_comap, mem_fixingSubgroup_iff]
    intro v hv
    simpa using (hfix hv) (x : MulAut ↥(gomiV G)) hx
  have hS_le : S.subgroupOf (autOn G (gomiV G)) ≤
      (fixingSubgroup (MulAut ↥(gomiV G)) (fixV S : Set ↥(gomiV G))).comap
        (autOn G (gomiV G)).subtype := by
    intro x hx
    rw [Subgroup.mem_comap, mem_fixingSubgroup_iff]
    intro v hv
    simpa using hv (x : MulAut ↥(gomiV G)) hx
  exact Subgroup.map_le_iff_le_comap.mpr
    (normalClosure_le_comap_fixingSubgroup_ef36 (autOn G (gomiV G)).subtype
      (fixV S : Set ↥(gomiV G)) hNL htopY hL_le hS_le)

private theorem fixV_le_fixV_autOn_of_le_fixV_gomiBarOf_ef36 {B : Subgroup Ω}
    (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {S : Subgroup (MulAut ↥(gomiV G))} {T : Subgroup Ω}
    (hT : IsSylowTwoOf T G) (hTS : autOn T (gomiV G) = S)
    (hS : IsSylowIn 2 S (autOn G (gomiV G)))
    (hfix : fixV S ≤ fixV (autOn B (gomiV G))) :
    fixV S ≤ fixV (autOn G (gomiV G)) := by
  have hNbar_map_le :=
    normalClosure_map_subtype_le_fixingSubgroup_ef36 hB hBt hGB hCQ hT hTS hfix
  have hS_le_F : S ≤ fixingSubgroup (MulAut ↥(gomiV G)) (fixV S : Set ↥(gomiV G)) := by
    intro x hx
    rw [mem_fixingSubgroup_iff]
    intro v hv
    simpa using hv x hx
  have htopY := top_eq_normalClosure_gomiBarOf_sup_ef36 hB.le hGB hT hTS
  have hY_eq : autOn G (gomiV G) =
      (Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G)))).map
        (autOn G (gomiV G)).subtype ⊔ S := by
    calc autOn G (gomiV G) = (⊤ : Subgroup ↥(autOn G (gomiV G))).map
          (autOn G (gomiV G)).subtype := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = (Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) ⊔
            S.subgroupOf (autOn G (gomiV G))).map (autOn G (gomiV G)).subtype := by rw [htopY]
      _ = (Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G)))).map
            (autOn G (gomiV G)).subtype ⊔
          (S.subgroupOf (autOn G (gomiV G))).map (autOn G (gomiV G)).subtype := by
          rw [Subgroup.map_sup]
      _ = _ := by rw [Subgroup.map_subgroupOf_eq_of_le hS.le]
  have hY_le_F : autOn G (gomiV G) ≤
      fixingSubgroup (MulAut ↥(gomiV G)) (fixV S : Set ↥(gomiV G)) := by
    rw [hY_eq]
    exact sup_le hNbar_map_le hS_le_F
  intro v hv
  rw [mem_fixV] at hv ⊢
  intro x hx
  have hmem := (mem_fixingSubgroup_iff (MulAut ↥(gomiV G))).mp (hY_le_F hx)
  simpa using hmem v hv

theorem Gomi410Cex.not_fixV_le_fixV_autOn (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {S : Subgroup (MulAut ↥(gomiV G))} (hS : IsSylowIn 2 S (autOn G (gomiV G))) :
    ¬ fixV S ≤ fixV (autOn B (gomiV G)) := by
  intro hfix
  obtain ⟨T, hT, hTS⟩ := exists_isSylowTwoOf_autOn_eq hS
  have hYfix := fixV_le_fixV_autOn_of_le_fixV_gomiBarOf_ef36 hB hBt hGB hCQ hT hTS hS hfix
  have hKV : omegaOneCenterOf T ≤ gomiV G :=
    omegaOneCenterOf_le_gomiV_of_pCoreOf_le hchar hT.1
      (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hKfix : ∀ x (hx : x ∈ omegaOneCenterOf T),
      (⟨x, hKV hx⟩ : ↥(gomiV G)) ∈ fixV S := by
    intro x hx
    rw [← hTS]
    exact (AutOn.mem_fixV_autOn_iff (hT.1.trans (gomiV_moduleSetting G).2)
      ⟨x, hKV hx⟩).mpr (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf T hx).2
  have hKleCG : omegaOneCenterOf T ≤ Subgroup.centralizer (G : Set Ω) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hv : (⟨x, hKV hx⟩ : ↥(gomiV G)) ∈ fixV (autOn G (gomiV G)) := hYfix (hKfix x hx)
    rw [mem_fixV] at hv
    have hgN : g ∈ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2 hg
    have h := hv (conjAct (gomiV G) ⟨g, hgN⟩) (AutOn.conjAct_mem_autOn_of_mem hgN hg)
    have h2 := congrArg Subtype.val h
    rw [AutOn.coe_conjAct_apply] at h2
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [h2]
  have hGleN : G ≤ Subgroup.normalizer (omegaOneCenterOf T : Set Ω) :=
    (Subgroup.le_centralizer_iff.mp hKleCG).trans (Subgroup.centralizer_le_normalizer _)
  exact h.singular (PSubgroupSelection.isRegular_of_le_normalizer
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp hT) (hfZ T hT.2.1) hGleN)

theorem Gomi410Cex.exists_not_isGomiParabolicSwap (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    (h36 : GomiFact36)
    (h45 : ∀ S : Subgroup Ω, IsSylowTwoOf S G → ∃ X : Subgroup Ω, IsGomiSingularSubgroup G S X)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    (hchev : IsGomiChevTwo (↥B ⧸ CFSG.pCore 2 ↥B))
    (hL : IsGomiL3 (↥(gomiBarOf G B) ⧸ Subgroup.center ↥(gomiBarOf G B)) ∨
      IsGomiSp4 (↥(gomiBarOf G B) ⧸ Subgroup.center ↥(gomiBarOf G B))) :
    ∃ S : Sylow 2 ↥(autOn G (gomiV G)),
      ¬ IsGomiParabolicSwap (S : Subgroup ↥(autOn G (gomiV G))) (gomiBarOf G B) := by
  let Y : Subgroup (MulAut ↥(gomiV G)) := autOn G (gomiV G)
  obtain ⟨S₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥Y))
  let S : Subgroup (MulAut ↥(gomiV G)) := (S₀ : Subgroup ↥Y).map Y.subtype
  have hLle : autOn B (gomiV G) ≤ Y := AutOn.autOn_mono hB.le
  have hS : IsSylowIn 2 S Y := by
    refine ⟨Subgroup.map_subtype_le _, S₀.isPGroup'.map Y.subtype, ?_⟩
    have hsub : S.subgroupOf Y = (S₀ : Subgroup ↥Y) := subgroupOf_map_subtype_eq_ef36
    show ¬ 2 ∣ (S.subgroupOf Y).index
    rw [hsub]
    exact Sylow.not_dvd_index S₀
  obtain ⟨e⟩ := nonempty_mulEquiv_gomiBarOf hB hCQ
  have eY : ↥(gomiBarOf G B) ≃* ↥(autOn B (gomiV G)) :=
    Subgroup.subgroupOfEquivOfLe hLle
  have hchevL : IsGomiChevTwo ↥(autOn B (gomiV G)) :=
    IsGomiChevTwo.of_mulEquiv eY (IsGomiChevTwo.of_mulEquiv e hchev)
  have hL' : IsGomiL3 (↥(autOn B (gomiV G)) ⧸ Subgroup.center ↥(autOn B (gomiV G))) ∨
      IsGomiSp4 (↥(autOn B (gomiV G)) ⧸ Subgroup.center ↥(autOn B (gomiV G))) := by
    have e2 := QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) eY
      (Subgroup.map_center_eq eY)
    rcases hL with h | h
    · exact Or.inl (h.of_mulEquiv e2)
    · exact Or.inr (h.of_mulEquiv e2)
  have hcomp : CFSG.IsComponent ((autOn B (gomiV G)).subgroupOf Y) :=
    ⟨(gomiHyp21_gomiBarOf hB hBt hGB hCQ).quasisimple, isSubnormal_gomiBarOf hB⟩
  have hnotswap : ¬ IsGomiParabolicSwap S (autOn B (gomiV G)) :=
    h36 ↥(gomiV G) (fun w => Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)) Y S
      (autOn B (gomiV G)) hS hLle hcomp
      (commutator_autOn_sSup_pstarSet_ne_bot h hfZ hchar hmono h45 hB hBt hGB hCQ hS)
      (not_fixV_le_fixV_autOn h hfZ hchar hB hBt hGB hCQ hS) hchevL hL'
  refine ⟨S₀, ?_⟩
  intro hswap
  apply hnotswap
  have h := hswap.map_subtype
  have hmapL : (gomiBarOf G B).map Y.subtype = autOn B (gomiV G) := by
    show ((autOn B (gomiV G)).subgroupOf Y).map Y.subtype = autOn B (gomiV G)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLle]
  rwa [hmapL] at h

end CFSG.GroupTheory
