module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFour
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalAutCent
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalModel
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly
import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.KlingenSpFour Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (projUnipotent exists_sylow_projUnipotent)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAssembly (classical_model_outer_solvable)

theorem spFour_catalog_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsSpFourIndex p d) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group ∧
      (∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) ∧
      Group.IsSolvable (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hS := statedClassicalModel_of_spFourIndex d hd (MulEquiv.refl _)
  obtain ⟨hfin, -, hsimple⟩ := CFSG.LieType.Simplicity.fam_classical_converse _ ⟨_, _, _, _, hS⟩
  refine ⟨hsimple, ?_, classical_model_outer_solvable hS⟩
  obtain ⟨ψ⟩ := nonempty_mulEquiv_psp4 hp2 hS
  refine exists_mul_ne_of_sq_dvd_card hp ?_ Nat.card_pos.ne'
  rw [Nat.card_congr ψ.toEquiv]
  exact (pow_dvd_pow p (by norm_num : 2 ≤ 4)).trans
    (card_projUnipotent_zmod p ▸ card_subgroup_dvd_card _)

theorem threeFourTwoSpFour_inf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsSpFourIndex p d) {Y : Type} [Group Y] [Finite Y]
    {K Y₀ E : Subgroup Y} (R : Sylow p Y) (hK : K.Normal)
    (hKX : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hcore : (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
      else GLBCore p 1 E) ≤ Y₀)
    (hKY₀ : ¬ K ≤ Y₀) :
    ∃ N : Subgroup Y, N ≤ K ⊓ Y₀ ∧ IsPGroup p N ∧ K ⊓ Y₀ ≤ normalizer (N : Set Y) ∧
      centralizer (N : Set Y) ⊓ (K ⊓ Y₀) ≤ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨eK⟩ := hKX
  obtain ⟨ψ⟩ := nonempty_mulEquiv_psp4 hp2 (statedClassicalModel_of_spFourIndex d hd eK)
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨S, hS⟩ := exists_sylow_projUnipotent (K := ZMod p) p (r := 2) (by norm_num)
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow ψ S.isPGroup' S.not_dvd_index T
  set ι : PSp4 p →* Y := K.subtype.comp Φ.toMonoidHom with hιdef
  have hι : Function.Injective ι := K.subtype_injective.comp Φ.injective
  have hrange : ι.range = K := by
    rw [hιdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Φ.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hTι : (projUnipotent 2 (ZMod p)).map ι = (R : Subgroup Y) ⊓ K := by
    rw [← hT, hΦ, ← hS, hιdef, ← map_map]
  have hdata := (siegelRadicalData_psp4 p hp2).map ι hι
  rw [hrange, hTι] at hdata
  set U : Subgroup Y := (xS p).U.map ι with hU
  have hUR : U ≤ R := hdata.U_le.trans inf_le_left
  have hU3 : 3 ≤ CFSG.Open.pRank p U :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hdata.elem hdata.card_U
  have hNY₀ : normalizer (U : Set Y) ≤ Y₀ :=
    normalizer_le_of_three_le_pRank_of_le hp R hcore hUR hU3
  have heq : K ⊓ Y₀ = normalizer (U : Set Y) ⊓ K := by
    rcases hdata.coatom (K ⊓ Y₀)
      (fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, hNY₀ (mem_inf.mp hx).1⟩) inf_le_left with
      h | h
    · exact h
    · exact absurd (fun x hx => (mem_inf.mp (h.ge hx)).2) hKY₀
  have hUK : U ≤ K := hdata.U_le.trans inf_le_right
  have hZ : center (PSp4 p) = ⊥ := by
    obtain ⟨hs, ⟨a, b, hab⟩, -⟩ := spFour_catalog_facts hp hp2 hd
    have e := ψ.symm.trans eK
    haveI : IsSimpleGroup (PSp4 p) := (MulEquiv.isSimpleGroup_congr e).2 hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (PSp4 p)) with h | h
    · exact h
    · refine absurd ?_ hab
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact mem_center_iff.mp (h ▸ mem_top (e.symm b)) (e.symm a)
  refine ⟨U, ?_, IsPGroup.of_card hdata.card_U, ?_, ?_⟩
  · rw [heq]
    exact le_inf le_normalizer hUK
  · rw [heq]
    exact inf_le_left
  ·
    intro y hy
    obtain ⟨hyC, hyK⟩ := mem_inf.mp hy
    obtain ⟨x, rfl⟩ : y ∈ ι.range := hrange ▸ (mem_inf.mp hyK).1
    have hcomm : ∀ u ∈ (xS p).U, MulAut.conj x u = u := fun u hu => by
      rw [MulAut.conj_apply]
      apply hι
      have h := mem_centralizer_iff.mp hyC (ι u) (mem_map_of_mem ι hu)
      rw [map_mul, map_mul, map_inv, ← h, mul_inv_cancel_right]
    obtain ⟨k, hk, hxk⟩ := autCent_xS p hp2 (MulAut.conj x) hcomm
    have hc : k⁻¹ * x ∈ center (PSp4 p) := mem_center_iff.mpr fun g => by
      have h1 := DFunLike.congr_fun hxk g
      simp only [MulAut.conj_apply] at h1
      calc g * (k⁻¹ * x) = k⁻¹ * (k * g * k⁻¹) * x := by group
        _ = k⁻¹ * (x * g * x⁻¹) * x := by rw [h1]
        _ = k⁻¹ * x * g := by group
    rw [hZ, mem_bot, inv_mul_eq_one] at hc
    rw [← hc]
    exact mem_map_of_mem ι hk

theorem threeFourTwoNoneAt_of_isSpFourIndex {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsSpFourIndex p d) :
    ThreeFourTwoNoneAt p (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨hX, hnab, hout⟩ := spFour_catalog_facts hp hp2 hd
  refine threeFourTwoNoneAt_of_inf hX hnab hout ?_
  intro Y _ _ K Y₀ E R _ _ hK hKX _ _ _ _ _ _ hcore _ hKY₀
  exact Or.inr (threeFourTwoSpFour_inf hp hp2 hd R hK hKX hcore hKY₀)

theorem threeFourTwoSpFour_holds : ThreeFourTwoSpFour :=
  ⟨fun _ hp hp2 q _ hqp hq1 hd =>
      threeFourTwoNoneAt_of_isSpFourIndex hp hp2 ⟨q, .inl ⟨hqp, hq1, hd⟩⟩,
    fun q _ hq2 hq1 hd => threeFourTwoNoneAt_of_isSpFourIndex Nat.prime_three (by norm_num)
      ⟨q, .inr ⟨rfl, hq2, hq1, hd⟩⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
