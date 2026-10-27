module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79c
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {E N W : Subgroup G}

theorem y7c_gl3_fix_sylow (hE : IsGL3Ext E N) (hW : E ≤ normalizer (W : Set G))
    (hN : N ≤ centralizer (W : Set G)) (hWe : IsElemAbelian 2 W) (hcard : Nat.card W = 8)
    (hfix : centIn W E = ⊥) {D : Subgroup G} (hND : N ≤ D) (hDE : D ≤ E)
    (hD : Nat.card D = 8 * Nat.card N) : Nat.card ↥(centIn W D) ≤ 2 := by
  classical
  obtain ⟨_, hsec⟩ := hE
  obtain ⟨hNn, he⟩ := hsec
  haveI := hNn
  obtain ⟨e⟩ := he
  haveI : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  let Q : Type := ↥E ⧸ N.subgroupOf E
  let π : ↥E →* Q := QuotientGroup.mk' (N.subgroupOf E)
  haveI : IsSimpleGroup Q := e.isSimpleGroup
  let ρ : ↥E →* MulAut ↥W := W.normalizerMonoidHom.comp (Subgroup.inclusion hW)
  have hρ_apply : ∀ y : ↥E, ρ y = W.normalizerMonoidHom (Subgroup.inclusion hW y) :=
    fun _ => rfl
  have hker : N.subgroupOf E ≤ ρ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker, hρ_apply]
    have hnN : ((n : ↥E) : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have hmem : Subgroup.inclusion hW n ∈ W.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      simpa [Subgroup.coe_inclusion] using hN hnN
    exact MonoidHom.mem_ker.mp hmem
  let ρ' : Q →* MulAut ↥W := QuotientGroup.lift (N.subgroupOf E) ρ hker
  have hρker : ρ.ker = N.subgroupOf E := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ'.ker with hbot | htop
    · apply le_antisymm _ hker
      intro x hx
      have hxπ : π x ∈ ρ'.ker := by
        rw [MonoidHom.mem_ker]
        exact hx
      rw [hbot] at hxπ
      have hx1 : π x = 1 := Subgroup.mem_bot.mp hxπ
      have hxker : x ∈ π.ker := MonoidHom.mem_ker.mpr hx1
      rwa [QuotientGroup.ker_mk' (N.subgroupOf E)] at hxker
    · exfalso
      have hρ1 : ρ = 1 := by
        apply MonoidHom.ext
        intro x
        have hx : π x ∈ ρ'.ker := by rw [htop]; exact Subgroup.mem_top _
        rw [MonoidHom.mem_ker] at hx
        exact hx
      have hWle : W ≤ centIn W E := by
        intro w hw
        refine ⟨hw, ?_⟩
        change w ∈ centralizer (E : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have h1 : ρ ⟨g, hg⟩ = 1 := by rw [hρ1, MonoidHom.one_apply]
        have hconj : (((ρ ⟨g, hg⟩) ⟨w, hw⟩ : ↥W) : G) = g * w * g⁻¹ := by
          simpa [ρ, MonoidHom.comp_apply, Subgroup.coe_inclusion] using
            Subgroup.normalizerMonoidHom_apply_apply_coe W
              (Subgroup.inclusion hW ⟨g, hg⟩) ⟨w, hw⟩
        have hfixw : g * w * g⁻¹ = w := by
          have h := congrArg (fun f : MulAut ↥W => (((f ⟨w, hw⟩ : ↥W)) : G)) h1
          rw [hconj] at h
          simpa using h
        calc g * w = (g * w * g⁻¹) * g := by group
          _ = w * g := by rw [hfixw]
      have hWbot : W = ⊥ := le_bot_iff.mp (hWle.trans (le_of_eq hfix))
      have hcard1 : Nat.card W = 1 := by rw [hWbot]; simp
      omega
  let ρD : ↥D →* MulAut ↥W := ρ.comp (Subgroup.inclusion hDE)
  let Dh : Subgroup (MulAut ↥W) := ρD.range
  have hkerD : ρD.ker = N.subgroupOf D := by
    change (ρ.comp (Subgroup.inclusion hDE)).ker = N.subgroupOf D
    rw [← MonoidHom.comap_ker ρ (Subgroup.inclusion hDE), hρker,
      Subgroup.comap_inclusion_subgroupOf]
  have hcardDh : Nat.card Dh = 8 := by
    have hc := Subgroup.card_ker_mul_card_range ρD
    rw [hkerD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND).toEquiv, hD] at hc
    have hNpos : 0 < Nat.card N := by
      haveI : Nonempty ↥N := ⟨1, N.one_mem⟩
      exact Nat.card_pos
    rw [mul_comm 8 (Nat.card N)] at hc
    exact Nat.mul_left_cancel hNpos hc
  have hF : IsE 3 ↥W := y7c_isE_of_isElemAbelian hWe (n := 3) (by rw [hcard]; norm_num)
  have hmain : Nat.card {w : ↥W // ∀ φ ∈ Dh, φ w = w} ≤ 2 :=
    y7c_mulAut_fix_le_two hF Dh hcardDh
  have hle : Nat.card ↥(centIn W D) ≤ Nat.card {w : ↥W // ∀ φ ∈ Dh, φ w = w} := by
    let f : ↥(centIn W D) → {w : ↥W // ∀ φ ∈ Dh, φ w = w} := fun w =>
      ⟨⟨w.1, (inf_le_left : centIn W D ≤ W) w.2⟩, fun φ hφ => by
        have hwW : w.1 ∈ W := (inf_le_left : centIn W D ≤ W) w.2
        rw [MonoidHom.mem_range] at hφ
        obtain ⟨d, hd⟩ := hφ
        rw [← hd]
        apply Subtype.ext
        have hwD : w.1 ∈ centralizer (D : Set G) := (inf_le_right : centIn W D ≤ _) w.2
        have hcomm : (d : G) * w.1 = w.1 * (d : G) :=
          Subgroup.mem_centralizer_iff.mp hwD (d : G) d.2
        have hconj : (((ρD d) ⟨w.1, hwW⟩ : ↥W) : G) = (d : G) * w.1 * (d : G)⁻¹ := by
          simpa [ρD, ρ, MonoidHom.comp_apply, Subgroup.coe_inclusion] using
            Subgroup.normalizerMonoidHom_apply_apply_coe W
              (Subgroup.inclusion hW (Subgroup.inclusion hDE d)) ⟨w.1, hwW⟩
        rw [hconj]
        change (d : G) * w.1 * (d : G)⁻¹ = w.1
        rw [hcomm]
        group⟩
    refine Nat.card_le_card_of_injective f ?_
    intro a b hab
    exact Subtype.ext (by
      simpa [f] using congrArg (fun x : {w : ↥W // ∀ φ ∈ Dh, φ w = w} => (x.1.1 : G)) hab)
  exact hle.trans hmain

end CFSG.OddStandard.HigherRank.YamadaG23
