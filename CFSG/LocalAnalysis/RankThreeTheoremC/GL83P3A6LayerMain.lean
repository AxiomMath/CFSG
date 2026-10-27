module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Final
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3ZJAny
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerBarData
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerSolv
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerSimple
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerZJ
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.ABGLocalTools GL83P3A6Aux GL83P3A6Img GL83P3A6Layer CFSG.AGLEmbedding

theorem a6VICase2Layer_of_kfacts (h1435 : KFact1435) (hZJ : KFactZJFactorizationAny)
    {G : Type} [Group G] [Finite G] (hS : Setting G) (_hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) : A6VICase2Layer G := by
  intro p hp P M hM _hfail _hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Qt _ ψ hψ hker hQ h34
    hnwc hC1 _U _hU Y hY2 hYM _hUY hYO _hYN hbig
  subst hp3
  have hJ : IsA6Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Qt, inferInstance, ψ, hψ, hker, hQ⟩
  obtain ⟨e₂, e₃, t, ρ, s, hpd⟩ := exists_pointData hS hU0 hp hM hgen hJ h34 hnwc
  haveI hN : ((GLBPrimeCore 3 M).subgroupOf M).Normal := glbPrimeCore_normal 3 M
  have hsolv := hpd.isPSolvable_centralizer_bar hS hU0 hp hM hgen hJ
  have hd := hpd.xdata hJC hC1 hsolv
  have hf := hd.frame
  obtain ⟨L, hLn, hLs, hLnab, hLc, hQL, -⟩ := hd.exists_simple
  have hMtop : M ≠ ⊤ := fun h => hgen.2.1.2.2.2.2 (h ▸ le_top)
  have hchev := chev_or_alt hZJ hS hM.1.1 hMtop hY2 hYM hYO hbig hpd.Q_le_M hpd.tri.Q_el
    hpd.tri.Q_card hLn hLs hLnab hLc hd.core (by rw [hpd.img_Qf]; exact hQL)
  obtain ⟨S, hS'⟩ := hpd.sylow_bar
  obtain ⟨φ⟩ := hpd.wreath
  set π := QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) with hπ
  have hPinj : Function.Injective (π.comp ((P : Subgroup G).subgroupOf M).subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgO : ((g : M) : G) ∈ GLBPrimeCore 3 M := by
      have := hg
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf] at this
      exact this
    have hgP : ((g : M) : G) ∈ (P : Subgroup G) := mem_subgroupOf.mp g.2
    have : ((g : M) : G) ∈ (P : Subgroup G) ⊓ GLBPrimeCore 3 M := mem_inf.mpr ⟨hgP, hgO⟩
    rw [hpd.P_inf_O, mem_bot] at this
    exact Subtype.ext (Subtype.ext this)
  have hrange : (π.comp ((P : Subgroup G).subgroupOf M).subtype).range =
      img M (GLBPrimeCore 3 M) (P : Subgroup G) := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  have hwreath : Nonempty (↥(S : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) ≃*
      (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) :=
    ⟨(MulEquiv.subgroupCongr (hS'.trans hrange.symm)).trans
      ((MonoidHom.ofInjective hPinj).symm.trans
        ((Subgroup.subgroupOfEquivOfLe hpd.P_le).trans φ))⟩
  have hJP : thompsonSubgroup (S : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) =
      Qf (π ⟨x, hpd.x_memM⟩) (π ⟨e₂, hpd.e₂_memM⟩) (π ⟨e₃, hpd.e₃_memM⟩) := by
    obtain ⟨φS⟩ := hwreath
    exact hf.thompsonSubgroup_eq φS (hS' ▸ hd.Q_le)
  have hxJ : π ⟨x, hpd.x_memM⟩ ∈
      thompsonSubgroup (S : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) := by
    rw [hJP]; exact hf.x_mem
  have hlines3 : conjLinesIn (thompsonSubgroup (S : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)))
      (π ⟨x, hpd.x_memM⟩) = 3 := by
    rw [hJP]
    exact hf.conjLinesIn_eq_three hpd.lines_bar
  have hd1 : ∀ D : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M),
      D ≤ thompsonSubgroup (S : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) →
      (∀ g ∈ normalizer (thompsonSubgroup (S : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) :
          Set (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)), ∀ d ∈ D, g * d * g⁻¹ ∈ D) →
      D = ⊥ ∨ D = thompsonSubgroup (S : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) := by
    rw [hJP]
    intro D hDle hinv
    exact hf.eq_bot_or_eq_of_invariant hDle (hinv _ hf.t_mem_normalizer)
      (hinv _ hf.ρ_mem_normalizer)
  have hd2 : ∀ S₂ : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M),
      IsSylowOf 2 S₂ (normalizer (thompsonSubgroup
        (S : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) :
          Set (M ⧸ (GLBPrimeCore 3 M).subgroupOf M))) →
      ∃ a ∈ S₂, ∃ b ∈ S₂, a * b * a⁻¹ * b⁻¹ ∉ centralizer (thompsonSubgroup
        (S : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) :
          Set (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) := by
    rw [hJP]
    exact fun S₂ hS₂ => hf.exists_sylow_comm S₂ hS₂
  obtain ⟨-, hiso, h108⟩ := h1435 _ L S (π ⟨x, hpd.x_memM⟩) hLn hLs hLnab hLc hchev hwreath hxJ
    hf.x_ne hlines3 hd1 hd2 hsolv
  refine ⟨hpd.x_memM, hN, L, hLn, hiso, hLc, ?_, h108⟩
  rw [hpd.img_Q_eq]
  exact hQL

theorem gl83P3A6_holds_of_kfacts (h1435 : KFact1435) (hZJ : KFactZJFactorizationAny)
    (h2811 : KFact2811) (hLe8 : KFactPSp43ElemLe8) (h2sub : KFactPSp43TwoSubgroups)
    (hKA : KFactA6TwoNormalized) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
      GL83GenericPrimeThreeA6Lemma43VI G :=
  fun _ _ _ hS hD1 hU0 => gl83P3A6_holds_of_layer h2811 hLe8 h2sub hKA _ hS hD1 hU0
    (a6VICase2Layer_of_kfacts h1435 hZJ hS hD1 hU0)

end CFSG.LocalAnalysis.RankThreeTheoremC
