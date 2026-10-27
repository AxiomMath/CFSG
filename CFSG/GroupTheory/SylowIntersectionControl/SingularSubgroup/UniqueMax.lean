module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Components
import CFSG.GroupTheory.SylowIntersectionControl.Regular
import CFSG.GroupTheory.UniqueMaxOverSylow
import CFSG.GroupTheory.UniqueMaxOverProduct

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ABGLocalTools
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

omit [Finite Ω] in
private theorem actionOn_range_g45h (G : Subgroup Ω) :
    (A4.actionOn (gomiV G) G (gomiV_moduleSetting G).2).range =
      autOn G (gomiV G) := by
  change ((conjAct (gomiV G)).comp (Subgroup.inclusion (gomiV_moduleSetting G).2)).range =
    autOn G (gomiV G)
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

omit [Finite Ω] in
private theorem actionOn_map_subgroupOf_g45h {G S : Subgroup Ω} (hSG : S ≤ G) :
    (S.subgroupOf G).map
        (A4.actionOn (gomiV G) G (gomiV_moduleSetting G).2) =
      autOn S (gomiV G) := by
  have key : ∀ {H : Subgroup Ω} (hH : H ≤ Subgroup.normalizer (gomiV G : Set Ω)) (x : ↥H),
      A4.actionOn (gomiV G) H hH x =
        conjAct (gomiV G) ⟨x.1, hH x.2⟩ := by
    intro H hH x
    ext v
    rw [A4.actionOn_apply_coe, AutOn.coe_conjAct_apply]
  ext a
  rw [AutOn.mem_autOn_iff_exists]
  constructor
  · rintro ⟨s, hs, hsa⟩
    refine ⟨s.1, (gomiV_moduleSetting G).2 s.2, Subgroup.mem_subgroupOf.mp hs, ?_⟩
    rw [← hsa, key]
  · rintro ⟨x, hx, hxS, rfl⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hSG hxS⟩, Subgroup.mem_subgroupOf.mpr hxS, ?_⟩
    rw [key]

omit [Finite Ω] in
private theorem actionOn_ker_g45h (G : Subgroup Ω) :
    (A4.actionOn (gomiV G) G (gomiV_moduleSetting G).2).ker.map G.subtype =
      G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
  have hker : (A4.actionOn (gomiV G) G (gomiV_moduleSetting G).2).ker =
      (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf G := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      A4.actionOn_eq_one_iff]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  rw [hker, Subgroup.map_subgroupOf_eq_of_le inf_le_left]

private theorem isSylowTwoOf_inf_stepE (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) :
    IsSylowTwoOf (autOn S (gomiV G) ⊓ Lb) Lb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y := autOn G (gomiV G)
  let Sb := autOn S (gomiV G)
  let N : Subgroup (MulAut ↥(gomiV G)) := ⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom
  have hSylow : IsSylowOf 2 Sb Y := isSylowOf_iff.mpr (isSylowIn_autOn h)
  have hNY : N ≤ Y := by
    refine iSup_le fun y => iSup_le fun hy => ?_
    rintro x ⟨l, hl, rfl⟩
    exact Y.mul_mem (Y.mul_mem hy (hL.le hl)) (Y.inv_mem hy)
  have hYN : Y ≤ Subgroup.normalizer (N : Set _) := le_normalizer_iSup_map_conj Y Lb
  have hNL : N ≤ Subgroup.normalizer (Lb : Set _) := iSup_map_conj_le_normalizer hL.commute
  have hLbN : Lb ≤ N := by
    refine le_iSup₂_of_le (1 : MulAut ↥(gomiV G)) Y.one_mem ?_
    have hmap : Lb.map (MulAut.conj (1 : MulAut ↥(gomiV G))).toMonoidHom = Lb := by
      rw [show MulAut.conj (1 : MulAut ↥(gomiV G)) = 1 from map_one _]
      exact Subgroup.map_id Lb
    exact le_of_eq hmap.symm
  have h1 : IsSylowOf 2 (Sb ⊓ N) N := hSylow.inf_of_le_normalizer hNY hYN
  have h2 : IsSylowOf 2 ((Sb ⊓ N) ⊓ Lb) Lb := h1.inf_of_le_normalizer hLbN hNL
  rw [inf_assoc, inf_eq_right.mpr hLbN] at h2
  exact isSylowOf_iff.mp h2

private theorem exists_isUniqueMaxOver_autOn_stepE (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb) :
    ∃ M : Subgroup (MulAut ↥(gomiV G)),
      IsUniqueMaxOver (autOn G (gomiV G)) (autOn S (gomiV G)) M := by
  have hT : IsSylowTwoOf (autOn S (gomiV G) ⊓ Lb) Lb := isSylowTwoOf_inf_stepE h hL
  have hSG : autOn S (gomiV G) ≤ autOn G (gomiV G) := (isSylowIn_autOn h).le
  have hcomm : ∀ g ∈ autOn G (gomiV G), Lb.map (MulAut.conj g).toMonoidHom ≠ Lb →
      ⁅Lb, Lb.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
    intro g hg hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    exact fun b hb => (hL.commute g hg hne a ha b hb).symm
  rcases hg with hSL | hAlt
  · obtain ⟨m, hm, hSL, -⟩ := hSL
    obtain ⟨K, hKfield, hKfin, hcard, ⟨eSL⟩⟩ := hSL
    let : Field K := hKfield
    have : Finite K := hKfin
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := m) (by
      rw [← Nat.card_eq_fintype_card]
      exact hcard)
    let e : ↥Lb ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      eSL.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
    refine exists_isUniqueMaxOver_of_commute_conj hL.le hSG hcomm hL.sup_eq
      (isUniqueMaxOver_inf_normalizer_of_mulEquiv_sl2 e hT) ?_
    intro K' hTK hKL hLK
    exact eq_of_le_normalizer_of_mulEquiv_sl2 e hT hTK hKL hLK
  · obtain ⟨m, hm, ⟨e⟩, -⟩ := hAlt
    obtain ⟨B, hB⟩ := exists_isUniqueMaxOver_of_mulEquiv_alt hm e hT
    refine exists_isUniqueMaxOver_of_commute_conj hL.le hSG hcomm hL.sup_eq hB ?_
    intro K' hTK hKL hLK
    exact eq_of_le_normalizer_of_mulEquiv_alt hm e hT hTK hKL hLK

theorem exists_isUniqueMaxOver (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb) :
    ∃ M : Subgroup Ω, IsUniqueMaxOver G S M := by
  obtain ⟨Mbar, hMbar⟩ := exists_isUniqueMaxOver_autOn_stepE h hL hg
  set φ : ↥G →* MulAut ↥(gomiV G) :=
    A4.actionOn (gomiV G) G (gomiV_moduleSetting G).2 with hφ
  have hker : ∀ H : Subgroup Ω, IsMaxSubgroupIn G H → S ≤ H → φ.ker.map G.subtype ≤ H := by
    intro H hHmax hSH
    rw [hφ, actionOn_ker_g45h]
    exact centralizer_le_of_isMaxSubgroupIn h hHmax hSH
  have hMbar' : IsUniqueMaxOver φ.range ((S.subgroupOf G).map φ) Mbar := by
    rw [hφ, actionOn_range_g45h, actionOn_map_subgroupOf_g45h h.isSylowTwoOf.1]
    exact hMbar
  exact ⟨_, isUniqueMaxOver_comap_of_ker_le h.isSylowTwoOf.1 φ hker hMbar'⟩

private theorem le_of_mem_sylowMembers_stepH (h : GomiThm45Counterexample c G S)
    {M Y : Subgroup Ω} (hM : IsUniqueMaxOver G S M)
    (hY : Y ∈ sylowMembers 2 (c.selection.family G) S) : Y ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, huniq⟩ := isUniqueMaxOver_iff.mp hM
  obtain ⟨hYfam, hYsyl⟩ := hY
  obtain ⟨P, hP, F, hF, hYeq⟩ := hYfam
  subst hYeq
  have hPX : P ≤ G ⊓ Subgroup.normalizer (F : Set Ω) :=
    le_inf hP.le (Subgroup.le_normalizer.trans (c.selection.normalizer_le P hP.isPGroup F hF))
  have hPXsyl : IsSylowOf 2 P (G ⊓ Subgroup.normalizer (F : Set Ω)) :=
    hP.of_le hPX inf_le_left
  have hSG : IsSylowOf 2 S G := isSylowOf_iff.mpr h.isSylowTwoOf
  have hcard : Nat.card (S ⊓ (G ⊓ Subgroup.normalizer (F : Set Ω)) : Subgroup Ω) =
      Nat.card S :=
    (hYsyl.card_eq.trans hPXsyl.card_eq.symm).trans (hP.card_eq.trans hSG.card_eq.symm)
  have hSX : S ≤ G ⊓ Subgroup.normalizer (F : Set Ω) := by
    have hEq : S ⊓ (G ⊓ Subgroup.normalizer (F : Set Ω)) = S :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcard.symm)
    exact hEq.symm.le.trans inf_le_right
  have hXlt : G ⊓ Subgroup.normalizer (F : Set Ω) < G := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hXG
    exact h.not_isRegular (c.selection.isRegular_of_mem_family ⟨P, hP, F, hF, hXG.symm⟩)
  obtain ⟨N, hNmax, hXN⟩ := exists_isMaxSubgroupIn hXlt
  exact hXN.trans (le_of_eq (huniq N hNmax (hSX.trans hXN)))

theorem iSup_sylowMembers_ne (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb) :
    (⨆ X ∈ sylowMembers 2 (c.selection.family G) S, X) ≠ G := by
  obtain ⟨M, hM⟩ := exists_isUniqueMaxOver h hL hg
  have hMlt : M < G := (isUniqueMaxOver_iff.mp hM).1.1
  have hle : (⨆ X ∈ sylowMembers 2 (c.selection.family G) S, X) ≤ M :=
    iSup_le fun X => iSup_le fun hX => le_of_mem_sylowMembers_stepH h hM hX
  intro hEq
  exact (ne_of_lt hMlt) (le_antisymm hMlt.le (hEq ▸ hle))

end CFSG.GroupTheory.GomiThm45Counterexample
