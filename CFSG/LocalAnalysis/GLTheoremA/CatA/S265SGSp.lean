module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGResCls
import CFSG.HardMathSupport.Foote.E27.Q2Sp
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGEnd
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmPConj
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGSpBlock
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGSpModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGSpTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer b3Lie_center_eq_bot)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (perfectInLayer_conj_sp)
open CFSG.HardMathSupport.Foote.E27.Q2 (statedProjSpEquiv statedSp_eq)

private theorem false_of_spModel_two {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hcat : catalogIs (PSimple 3 K) (tyF 3))
    {ℓ : ℕ} (hℓ : ℓ = 3 ∨ ℓ = 4) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (Φ : PSimple 3 S ≃* StatedProj (StatedSp ℓ F)) {d : Ω} (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) (hdN : d ∈ Subgroup.normalizer (S : Set Ω))
    {r : StatedProj (StatedSp ℓ F)}
    (hr : MulAut.conj r = MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩)) (hr3 : r ^ 3 = 1)
    (hr1 : r ≠ 1) : False := by
  let Θ := (statedProjSpEquiv ℓ hF).trans
    (MulEquiv.subgroupCongr (statedSp_eq ℓ (ZMod 2)).symm)
  have hr' : MulAut.conj (Θ r) = MulAut.congr (Φ.trans Θ) (chevAut 3 S ⟨d, hdN⟩) := by
    refine MulEquiv.ext fun y => ?_
    have hy : r * Θ.symm y * r⁻¹ = Φ (chevAut 3 S ⟨d, hdN⟩ (Φ.symm (Θ.symm y))) :=
      congrArg (fun α : MulAut _ => α (Θ.symm y)) hr
    change Θ r * y * (Θ r)⁻¹ = Θ (Φ (chevAut 3 S ⟨d, hdN⟩ (Φ.symm (Θ.symm y))))
    rw [← hy, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨J, hJ, hJc⟩ := SG.exists_component_tyF_conj h hcat (Φ.trans Θ) hdD hdx hdN hr'
  exact SG.false_of_comp_sp_two hℓ (by rw [← map_pow, hr3, map_one]) (Θ.map_ne_one_iff.2 hr1)
    hJ hJc

private theorem false_of_spModel_four_le {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hcat : catalogIs (PSimple 3 K) (tyF 3))
    (hB : Nat.card B = 3 ^ 4) {ℓ n : ℕ} (hℓ : 3 ≤ ℓ) (hn : 2 ≤ n) {F : Type} [Field F]
    [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ n)
    [IsSimpleGroup (StatedProj (StatedSp ℓ F))]
    (hnc : ∃ a b : StatedProj (StatedSp ℓ F), a * b ≠ b * a)
    (Φ : PSimple 3 S ≃* StatedProj (StatedSp ℓ F))
    (hΦ : ∀ (b : Ω) (hbN : b ∈ Subgroup.normalizer (S : Set Ω)), b ∈ B →
      ∃ g : StatedSp ℓ F, MulAut.congr Φ (chevAut 3 S ⟨b, hbN⟩) =
        MulAut.conj (SymplecticFlag.proj ℓ F g))
    {d : Ω} (hdD : d ∈ D) (hdx : d ∉ Subgroup.zpowers x)
    (hdN : d ∈ Subgroup.normalizer (S : Set Ω)) {g : StatedSp ℓ F}
    (hg : MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩) = MulAut.conj (SymplecticFlag.proj ℓ F g)) :
    False := by
  haveI : NeZero ℓ := ⟨by omega⟩
  have hP := UnitaryHigher.proj_bijective_of_charTwo (r := ℓ) (K := F)
  set ρ : StatedSp ℓ F →* MulAut (StatedProj (StatedSp ℓ F)) :=
    MulAut.conj.comp (SymplecticFlag.proj ℓ F)
  have hρi : Function.Injective ρ :=
    (S172A.conj_injective_of_center_eq_bot (b3Lie_center_eq_bot hnc)).comp hP.1
  obtain ⟨hel, hcard⟩ := SG.card_map_chevAut h hB
  set X := ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)).map
    (MulAut.congr Φ).toMonoidHom with hX
  have hXc : Nat.card X = 3 ^ 3 := by
    rw [hX, Subgroup.card_map_of_injective (MulAut.congr Φ).injective, hcard]
  have hXr : X ≤ ρ.range := by
    rintro _ ⟨_, ⟨⟨b, hbN⟩, hb, rfl⟩, rfl⟩
    obtain ⟨g', hg'⟩ := hΦ b hbN hb
    exact ⟨g', hg'.symm⟩
  have hEe : IsElemAbelian 3 (X.comap ρ) := (hel.map (MulAut.congr Φ).toMonoidHom).comap hρi
  have hEc : Nat.card (X.comap ρ) = 3 ^ 3 := by
    rw [← Subgroup.card_map_of_injective hρi, Subgroup.map_comap_eq_self hXr, hXc]
  have hgE : g ∈ X.comap ρ := by
    show MulAut.conj (SymplecticFlag.proj ℓ F g) ∈ X
    rw [← hg]
    exact ⟨_, ⟨⟨d, hdN⟩, h.cfg.std.1 hdD, rfl⟩, rfl⟩
  have := hEe.1
  obtain ⟨ψ, χ, hψ, hχg, hχc⟩ := SG.exists_sl2_commute_sp hℓ (X.comap ρ)
    (fun a ha b hb => setLike_mul_comm ha hb) hEe.2 ⟨g, hgE⟩
  let f := (SymplecticFlag.proj ℓ F).comp ψ
  have hfi : Function.Injective f := hP.1.comp hψ
  let eA := MonoidHom.ofInjective hfi
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI := CFSG.RankThree.PartOne.SEITZ6.isSimpleGroup_SL2 h4
  haveI : IsSimpleGroup f.range := eA.symm.isSimpleGroup
  have hAnc : ∃ a b : f.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := CFSG.RankThree.PartOne.CTP.exists_noncomm_sl2 F
    exact ⟨eA a, eA b, fun h' => hab (eA.injective (by rw [map_mul, map_mul, h']))⟩
  have hA3 : 3 ∣ Nat.card f.range := by
    rw [← Nat.card_congr eA.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hF, ← pow_mul,
      mul_comm n 2, pow_mul]
    exact Dvd.dvd.mul_left (by simpa using Nat.sub_one_dvd_pow_sub_one 4 n) _
  have hfix : ∀ e ∈ χ.ker, f.range ≤ fixSubgroup (ρ e) := by
    rintro e he _ ⟨t, rfl⟩
    show SymplecticFlag.proj ℓ F e * SymplecticFlag.proj ℓ F (ψ t) *
      (SymplecticFlag.proj ℓ F e)⁻¹ = SymplecticFlag.proj ℓ F (ψ t)
    rw [← map_mul, ← map_inv, ← map_mul, ← (hχc e he t).eq, mul_inv_cancel_right]
  have hAd : f.range ≤ fixSubgroup (MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩)) := by
    rw [hg]
    exact hfix ⟨g, hgE⟩ hχg
  have hYX : χ.ker.map (ρ.comp (X.comap ρ).subtype) ≤ X := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hYi : Function.Injective (ρ.comp (X.comap ρ).subtype) :=
    hρi.comp (X.comap ρ).subtype_injective
  have hidx := Subgroup.relIndex_mul_card (χ.ker.map (ρ.comp (X.comap ρ).subtype)) X
  rw [inf_of_le_left hYX, Subgroup.card_map_of_injective hYi, hXc] at hidx
  have hkr := Subgroup.card_ker_mul_card_range χ
  rw [hEc] at hkr
  have hrg : Nat.card χ.range ≤ 3 := (Subgroup.card_le_card_group χ.range).trans_eq
    (by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod])
  have hk : 0 < Nat.card χ.ker := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hkr
    norm_num at hkr
  have hY := Nat.eq_of_mul_eq_mul_right hk (hidx.trans (hkr.symm.trans (mul_comm _ _)))
  have hY3 : (χ.ker.map (ρ.comp (X.comap ρ).subtype)).relIndex X ≤ 3 := by omega
  have hpl : PerfectInLayer (MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩)) := by
    rw [hg]
    exact perfectInLayer_conj_sp Nat.prime_two (by omega) hF (by omega) Nat.prime_three
      (by norm_num) (by norm_num) g (hEe.2 g hgE)
  refine SG.false_of_simple_fix_congr h hcat hB Φ hdD hdx hdN hpl hAnc hA3 hAd hY3 ?_
  rintro _ ⟨e, he, rfl⟩
  exact hfix e he

theorem qsF3ResSp_holds : QSF3ResSp := by
  intro Ω _ _ S B T x D K lab h hcat hB hlab hlab2 h3 hc
  have hℓ := SG.resSp_rank h3 hc
  obtain ⟨F, _, _, _, hF, _, hnc, Φ, hΦ⟩ := SG.spModel_of_innLabel h hlab hc.1
  obtain ⟨d, hdD, hdx⟩ := SG.exists_mem_D_not_zpowers h
  have hdB : d ∈ B := h.cfg.std.1 hdD
  have hdN : d ∈ Subgroup.normalizer (S : Set Ω) :=
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top d
  obtain ⟨g, hg⟩ := hΦ d hdN hdB
  rcases Nat.lt_or_ge lab.n 2 with hn | hn
  · have hF2 : Nat.card F = 2 := by
      rw [hF, show lab.n = 1 by have := hlab2.1; omega, pow_one]
    refine false_of_spModel_two h hcat hℓ hF2 Φ hdD hdx hdN hg.symm ?_ fun h1 => ?_
    · apply S172A.conj_injective_of_center_eq_bot (b3Lie_center_eq_bot hnc)
      rw [map_pow, ← hg, ← map_pow, (SG.card_map_chevAut h hB).1.2 _ ⟨⟨d, hdN⟩, hdB, rfl⟩,
        map_one, map_one]
    · refine hdx ((SG.chevAut_eq_one_iff_mem_zpowers h hdB hdN).1
        ((MulAut.congr Φ).injective ?_))
      rw [hg, h1, map_one, map_one]
  · exact false_of_spModel_four_le h hcat hB (by rcases hℓ with h' | h' <;> omega) hn hF hnc Φ
      hΦ hdD hdx hdN hg

end CFSG.LocalAnalysis.GLTheoremA.S265

end
