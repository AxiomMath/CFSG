module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGRes
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGU6b
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (fixSubgroup_congr)

private theorem nontrivial_of_tyF {X : Type} [Group X] (h : catalogIs X (tyF 3)) :
    Nontrivial X := by
  obtain ⟨m, hm, h⟩ := SGU6.card_mul_three_of_tyF h
  refine (subsingleton_or_nontrivial X).resolve_left fun _ => ?_
  have h2 : 2 ∣ Nat.card X * 3 := by
    rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;>
      exact (dvd_pow (dvd_pow_self 2 (by omega)) three_ne_zero).mul_right _
  rw [Nat.card_of_subsingleton (1 : X)] at h2
  norm_num at h2

private theorem layer_congr_chevAut {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hcat : catalogIs (PSimple 3 K) (tyF 3))
    {R : Type} [Group R] (Φ : PSimple 3 S ≃* R) {d : Ω} (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) (hdN : d ∈ Subgroup.normalizer (S : Set Ω)) :
    IsComponentOf (GLALayer (fixSubgroup (MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩))))
        (fixSubgroup (MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩))) ∧
      catalogIs (↥(GLALayer (fixSubgroup (MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩)))) ⧸
        Subgroup.center ↥(GLALayer (fixSubgroup (MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩)))))
        (tyF 3) := by
  have hc := h.cfg
  obtain ⟨-, -, -, -, -, hKc, -⟩ := hc.std
  have hKS : K ≤ S := hKc.1.trans inf_le_left
  set g : ↥K →* R := (Φ : PSimple 3 S →* R).comp ((chevQuotHom 3 S).comp (Subgroup.inclusion hKS))
    with hg
  have hJ : ((K.subgroupOf S).map (chevQuotHom 3 S)).map (Φ : PSimple 3 S →* R) = g.range := by
    rw [hg, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [fixSubgroup_congr, Y10F.glaLayer_map (ι := (Φ : PSimple 3 S →* R)) Φ.injective,
    SG.glaLayer_fixSubgroup_chevAut h hdD hdx hdN]
  refine ⟨CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map Φ
    (SG.isComponentOf_fixSubgroup_chevAut h hdD hdx hdN).2, ?_⟩
  rw [hJ]
  have hker : g.rangeRestrict.ker ≤ Subgroup.center ↥K := fun k hk => by
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hk
    have hk' : Subgroup.inclusion hKS k ∈ Subgroup.center ↥S := by
      rw [← S171.ker_chevQuotHom_eq_center' hc.prime hc.comp hc.quasi, MonoidHom.mem_ker]
      exact Φ.map_eq_one_iff.1 hk
    refine Subgroup.mem_center_iff.2 fun k' => Subtype.ext ?_
    exact congrArg (fun s : ↥S => (s : Ω))
      (Subgroup.mem_center_iff.1 hk' (Subgroup.inclusion hKS k'))
  haveI : Group.IsPerfect ↥K := ⟨hKc.2.2.1⟩
  haveI := nontrivial_of_tyF hcat
  obtain ⟨eK⟩ := SF.nonempty_centerQuot_equiv_pSimple (p := 3) hKc.2.2
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  exact ⟨i, hi, ⟨(CFSG.ComponentClassification.PerfectCentralQuotient.equivalence
    g.rangeRestrict g.rangeRestrict_surjective hker).symm.trans (eK.trans f)⟩⟩

theorem SG.qsF3ResU6_holds : QSF3ResU6 := by
  intro Ω _ _ S B T x D K lab h hcat _ hlab _ _ ⟨ht, hr, hpq⟩
  have hc := h.cfg
  obtain ⟨d, hdD, hdx⟩ := SG.exists_mem_D_not_zpowers h
  obtain ⟨hDB, -⟩ := hc.std
  have hdN : d ∈ Subgroup.normalizer (S : Set Ω) :=
    (Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top d
  have hraw := SG.exists_rawDatum_chevAut h hlab
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .twA := ht
  obtain rfl : rank = 5 := hr
  obtain ⟨F, _, _, hF, -, -, Φ, hΦ⟩ := hraw
  obtain ⟨hL, hty⟩ := layer_congr_chevAut h hcat Φ hdD hdx hdN
  refine SGU6.false_of_layer_tyF hF hpq (hΦ d hdN (hDB hdD)) (fun h1 => hdx ?_) ?_ hL hty
  · exact (SG.chevAut_eq_one_iff_mem_zpowers h (hDB hdD) hdN).1
      ((map_eq_one_iff _ (MulAut.congr Φ).injective).1 h1)
  · rw [← map_pow, chevAut_pow_eq_one 3 S hdN (hc.elem.2 d (hDB hdD)), map_one]

end CFSG.LocalAnalysis.GLTheoremA.S265

end
