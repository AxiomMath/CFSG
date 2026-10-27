module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab5
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.HSubT
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU

private theorem u4Split_of_mulEquiv {s y : M5} {τ : M5 ≃* M5} {Kb : Subgroup M5}
    (hτ : τ s = y) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hKbC : Kb ≤ Subgroup.centralizer ({y} : Set M5))
    (hsup : Subgroup.centralizer ({y} : Set M5) = Kb ⊔ Subgroup.zpowers y)
    (hdisj : Kb ⊓ Subgroup.zpowers y = ⊥)
    (hcent : Subgroup.center ↥Kb = ⊥) (hcard : Nat.card ↥Kb = 25920) :
    ∃ K₀ : Subgroup M5, U4Split s K₀ := by
  let K₀ : Subgroup M5 := Kb.map (τ.symm : M5 →* M5)
  have hsymm : τ.symm y = s := by
    rw [← hτ]
    simp
  have hs3 : s ^ 3 = 1 := by
    have h : τ.symm (y ^ 3) = 1 := by rw [hy3, map_one]
    simpa [hsymm] using h
  have hCmap : (Subgroup.centralizer ({y} : Set M5)).map (τ.symm : M5 →* M5) =
      Subgroup.centralizer ({s} : Set M5) := by
    have h := map_centralizer_singleton (e := τ.symm) (s := y)
    simpa [hsymm] using h
  have hsup' : Subgroup.centralizer ({s} : Set M5) = K₀ ⊔ Subgroup.zpowers s := by
    have h := congrArg (fun H : Subgroup M5 => H.map (τ.symm : M5 →* M5)) hsup
    simpa [K₀, hCmap, Subgroup.map_sup, MonoidHom.map_zpowers, hsymm] using h
  have hK0C : K₀ ≤ Subgroup.centralizer ({s} : Set M5) := by
    rw [← hCmap]
    exact Subgroup.map_mono hKbC
  have hcomm : ∀ a ∈ K₀, ∀ b ∈ Subgroup.zpowers s, a * b = b * a := by
    intro a ha b hb
    have has : Commute a s := Subgroup.mem_centralizer_singleton_iff.mp (hK0C ha)
    rcases mem_zpowers_cases hs3 hb with hb1 | hb2 | hb3
    · rw [hb1, mul_one, one_mul]
    · rw [hb2]
      exact has.eq
    · rw [hb3]
      exact (has.pow_right 2).eq
  have hdecomp : ∀ g ∈ Subgroup.centralizer ({s} : Set M5),
      ∃ n : ℕ, ∃ k ∈ K₀, g = s ^ n * k := by
    intro g hg
    have hg' : g ∈ K₀ ⊔ Subgroup.zpowers s := by
      rw [← hsup']
      exact hg
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hg'
    rcases mem_zpowers_cases hs3 hb with hb1 | hb2 | hb3
    · refine ⟨0, a, ha, ?_⟩
      calc g = a * b := hab.symm
        _ = a * 1 := by rw [hb1]
        _ = a := mul_one a
        _ = s ^ 0 * a := by simp
    · refine ⟨1, a, ha, ?_⟩
      calc g = a * b := hab.symm
        _ = b * a := hcomm a ha b hb
        _ = s * a := by rw [hb2]
        _ = s ^ 1 * a := by simp
    · refine ⟨2, a, ha, ?_⟩
      calc g = a * b := hab.symm
        _ = b * a := hcomm a ha b hb
        _ = s ^ 2 * a := by rw [hb3]
  have hsK0 : s ∉ K₀ := by
    intro hsK
    obtain ⟨a, ha, hza⟩ := Subgroup.mem_map.mp hsK
    have hza' : a = τ s := by
      simpa using congrArg τ hza
    have hyK : y ∈ Kb := by
      rw [← hτ, ← hza']
      exact ha
    have hybot : y ∈ (⊥ : Subgroup M5) := by
      rw [← hdisj]
      exact Subgroup.mem_inf.mpr ⟨hyK, Subgroup.mem_zpowers y⟩
    exact hy1 (Subgroup.mem_bot.mp hybot)
  have hcentK0 : Subgroup.center ↥K₀ = ⊥ := by
    let e : ↥Kb ≃* ↥K₀ := Kb.equivMapOfInjective (τ.symm : M5 →* M5) τ.symm.injective
    rw [← Subgroup.map_center_eq e, hcent, Subgroup.map_bot]
  have hcardK0 : Nat.card ↥K₀ = 25920 := by
    let e : ↥Kb ≃* ↥K₀ := Kb.equivMapOfInjective (τ.symm : M5 →* M5) τ.symm.injective
    rw [← Nat.card_congr e.toEquiv]
    exact hcard
  refine ⟨K₀, ?_⟩
  unfold U4Split
  exact ⟨hK0C, hdecomp, hsK0, hcentK0, hcardK0⟩

theorem centSplitOn_M5 : CentSplitOn M5 := by
  intro s hs
  have hs3 : s ^ 3 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one s
  rcases normal_form s hs3 with h1 | ⟨τ, hτ⟩ | ⟨τ, d, hd, hcnt⟩
  · exfalso
    rw [h1, orderOf_one] at hs
    omega
  · right
    obtain ⟨Kb, hKbC, hsup, hdisj, hsimp, hnc, -, hcat⟩ := m5_u4_layer
    have hcent : Subgroup.center ↥Kb = ⊥ := center_eq_bot_of_simple_not_comm Kb hnc
    have hcard : Nat.card ↥Kb = 25920 := card_of_catalogIs_u4two hcat
    rcases hτ with hτ | hτ
    · exact u4Split_of_mulEquiv hτ yM5_pow_three yM5_ne_one hKbC hsup hdisj hcent hcard
    · have hy3 : (yM5⁻¹) ^ 3 = 1 := by rw [inv_pow, yM5_pow_three, inv_one]
      have hy1 : yM5⁻¹ ≠ 1 := by simpa using yM5_ne_one
      have hKbC' : Kb ≤ Subgroup.centralizer ({yM5⁻¹} : Set M5) := by
        rwa [centralizer_inv_singleton]
      have hsup' : Subgroup.centralizer ({yM5⁻¹} : Set M5) =
          Kb ⊔ Subgroup.zpowers yM5⁻¹ := by
        rw [centralizer_inv_singleton, hsup, Subgroup.zpowers_inv]
      have hdisj' : Kb ⊓ Subgroup.zpowers yM5⁻¹ = ⊥ := by
        rw [Subgroup.zpowers_inv]
        exact hdisj
      exact u4Split_of_mulEquiv hτ hy3 hy1 hKbC' hsup' hdisj' hcent hcard
  · left
    intro K hK hKperf h5
    have hCsolv : Group.IsSolvable ↥(Subgroup.centralizer ({τ s} : Set M5)) :=
      centralizer_diag_solvable (τ s) d hd hcnt
    have hKmaple : K.map (τ : M5 →* M5) ≤ Subgroup.centralizer ({τ s} : Set M5) := by
      have h := Subgroup.map_mono (f := (τ : M5 →* M5)) hK
      rwa [map_centralizer_singleton (e := τ)] at h
    have hKmapSolv : Group.IsSolvable ↥(K.map (τ : M5 →* M5)) := by
      haveI := hCsolv
      exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hKmaple) (Subgroup.inclusion_injective hKmaple)
    have hKsolv : Group.IsSolvable ↥K := by
      let e : ↥K ≃* ↥(K.map (τ : M5 →* M5)) :=
        K.equivMapOfInjective (τ : M5 →* M5) τ.injective
      haveI := hKmapSolv
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have hKbot : K = ⊥ := by
      by_contra hne
      haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
      haveI : Group.IsPerfect ↥K := hKperf
      haveI := hKsolv
      exact (Group.IsPerfect.not_isSolvable ↥K) hKsolv
    rw [hKbot, Subgroup.card_bot] at h5
    exact absurd h5 (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
