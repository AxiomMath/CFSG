module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526B1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526B
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open scoped commutatorElement

section Row26X2

variable {X : Type} [Group X] [Finite X]

theorem pElement_cMLStar_le_centralizer {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls)
    (hN : IsNatSum L ⁅L, gnV T⁆) :
    pElementSubgroup 7 (cMLStar T Ls) ≤
      Subgroup.centralizer ((⁅L, gnV T⁆ : Subgroup X) : Set X) := by
  haveI : (gnV T).Normal := Subgroup.normalClosure_normal
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hxc, k, hk⟩
  have hx' : toStar T x ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := hxc
  have hxL : L.map (MulAut.conj x).toMonoidHom = L :=
    liftOf_conj hX hLs hL x ((Subgroup.centralizer_le_normalizer (Ls : Set (X ⧸ gnC T))) hx')
  have hxU := mem_normalizer_commutator (V := gnV T) hxL
  have hU : (⁅L, gnV T⁆ : Subgroup X) ≤ gnV T := by
    rw [Subgroup.commutator_comm]; exact commutator_gnV_le T L
  have key := sevenElement_centralizes_of_isNatSum_of_comm
    (le_normalizer_commutator_s15 (Ls := Ls)) hN
    (comm_of_le_gnV hX hU) hxU (commute_action_of_mem_cMLStar hL.2 hx' hU) ⟨k, hk⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro u hu
  have := key u hu
  calc u * x = (x * u * x⁻¹) * x := by rw [this]
    _ = x * u := by group

end Row26X2

section Row26Three

variable {G : Type} [Group G] [Finite G]

theorem row1526_centralizer_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (hK55 : K55)
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls) :
    ∀ u ∈ (⁅L, gnV (T.subgroupOf M)⁆ : Subgroup ↥M).map M.subtype, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ M ∧
        7 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ({u} : Set G)) := by
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  have hN := isNatSum_of_K55 hK55 ctx.gn hLs.1 (ctx.shape Ls hLs).1 (h25.2 Ls L hLs hL) hL
  have hP := pElement_cMLStar_le_centralizer ctx.gn hLs.1 hL hN
  have h2 : 1 < CFSG.Open.pRank 7 (cMBar L) := (h20 7 h7 Ls L hLs hL).2.1
  have hR := two_le_pRank_pElement_cMLStar ctx.gn hL (by norm_num) (by norm_num) h2
  obtain ⟨P, -, hw⟩ := ctx.witness 7 h7
  set U : Subgroup ↥M := ⁅L, gnV (T.subgroupOf M)⁆ with hU
  have hUV : U ≤ gnV (T.subgroupOf M) := by
    rw [hU, Subgroup.commutator_comm]; exact commutator_gnV_le _ L
  have hVea := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV
    (T.subgroupOf M) ctx.gn
  set R : Subgroup ↥M := pElementSubgroup 7 (cMLStar (T.subgroupOf M) Ls) with hRdef
  intro u hu hu1
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
  have hsq : (u' : G) * (u' : G) = 1 := by
    have := hVea.2 u' (hUV hu')
    have h2' : u' * u' = 1 := by simpa [pow_two] using this
    simpa using congrArg Subtype.val h2'
  have hRc : R.map M.subtype ≤ Subgroup.centralizer ({(u' : G)} : Set G) := by
    rintro r ⟨r', hr', rfl⟩
    have := (Subgroup.mem_centralizer_iff.1 (hP hr')) u' hu'
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact congrArg Subtype.val this
  have hcent := centralizer_le_of_two_le_pRank_gen (M := M) hw hu1 hsq
    (Subgroup.map_subtype_le R) hRc (by rw [pRank_map_subtype]; exact hR)
  refine ⟨hcent, ?_⟩
  have hRle : R.map M.subtype ≤ M ⊓ Subgroup.centralizer ({(u' : G)} : Set G) :=
    le_inf (Subgroup.map_subtype_le R) hRc
  have h7R : 7 ∣ Nat.card ↥(R.map M.subtype) := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨E, hER, -, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 7)
      (H := R.map M.subtype) (k := 1) (by rw [pRank_map_subtype]; omega)
    rw [← Nat.pow_one 7]
    exact hEc ▸ (Subgroup.card_dvd_of_le hER)
  exact h7R.trans (Subgroup.card_dvd_of_le hRle)

theorem row1526_three_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (hK55 : K55)
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls) :
    CFSG.CGT.Timmesfeld75.IsTI ((⁅L, gnV (T.subgroupOf M)⁆ : Subgroup ↥M).map M.subtype) := by
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  have hN := isNatSum_of_K55 hK55 ctx.gn hLs.1 (ctx.shape Ls hLs).1 (h25.2 Ls L hLs hL) hL
  have hstrong := ctx.strong 7 h7
  set U : Subgroup ↥M := ⁅L, gnV (T.subgroupOf M)⁆ with hU
  refine isTI_of_centralizer_le (Subgroup.map_subtype_le U) ?_
    (row1526_centralizer_gen hK55 ctx h20 h25 hLs hL) hstrong
  intro m hm
  have h := isNatSum_tiM ctx.gn hLs.1 hL hN (⟨m, hm⟩ : ↥M)
  have e : (conjSub (⟨m, hm⟩ : ↥M) U).map M.subtype =
      (U.map M.subtype).map (MulAut.conj m).toMonoidHom := map_subtype_conjSub U ⟨m, hm⟩
  rcases h with h | h
  · left
    rw [← e]
    exact congrArg (Subgroup.map M.subtype) h
  · right
    have h' := congrArg (Subgroup.map M.subtype) h
    rw [Subgroup.map_inf _ _ _ M.subtype_injective, Subgroup.map_bot] at h'
    rw [← e]
    exact h'

end Row26Three

end CFSG.LocalAnalysis.RankThreeUC.S15
