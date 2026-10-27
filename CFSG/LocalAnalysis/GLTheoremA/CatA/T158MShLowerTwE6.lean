module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailRankTE6
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank
open CFSG.RankThree.CentralCover

theorem lowerTwE6_holds :
    LowerTwE6 := by
  intro G _ _ L hq hcat
  classical
  haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  obtain ⟨q, rfl, hq2, hq3⟩ := hP
  set dd : TauCeti.ValidLieTypeIndex := ⟨.twistedE6 q, hv⟩ with hdd
  haveI := finite_fixedField dd
  haveI : Fintype dd.fixedField := Fintype.ofFinite _
  have hchar : dd.characteristic = q.p := TauCeti.LieTypeIndex.characteristic_twistedE6 q
  have h3 : q.p ^ q.exponent % 3 = 2 := by
    rw [TauCeti.PrimePower.card_def] at hq3
    omega
  have hLD : LiftDatum (TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) 3 :=
    twistedE6_liftDatum_even' q hv (by rw [ringChar_fixedField_eq, hchar]; exact hq2) h3
  obtain ⟨h, w, U, hcomm, hord, hinv, hfix, hU1, hU2, hN⟩ := hLD
  have hne1 : h 0 ≠ 1 := fun h1 => by
    have := hord 0
    rw [h1, orderOf_one] at this
    omega
  have hOne : GLAPPrimeCore 3 ↥L ≠ ⊤ := by
    intro htop
    have hall : ∀ x : PSimple 3 L, x = 1 := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 L)) x
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) y
      have hz : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) z = 1 :=
        (QuotientGroup.eq_one_iff z).2 (htop ▸ Subgroup.mem_top z)
      rw [hz, map_one]
    exact hne1 ((map_eq_one_iff e.symm e.symm.injective).1 (hall (e.symm (h 0))))
  have hOZ : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hOne
  let eZ : (↥L ⧸ Subgroup.center ↥L) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩ :=
    (S172A.pSimpleEquivCenterQuot 3 hOZ).trans e
  let φ : ↥L →* TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩ :=
    eZ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hφ : Function.Surjective φ := eZ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφker : φ.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥L)) x = 1 := by
        apply eZ.injective
        rw [map_one]
        exact hx
      exact (QuotientGroup.eq_one_iff _).1 h1
    · intro hx
      change eZ ((QuotientGroup.mk' (Subgroup.center ↥L)) x) = 1
      rw [show (QuotientGroup.mk' (Subgroup.center ↥L)) x = 1 from
        (QuotientGroup.eq_one_iff _).2 hx, map_one]
  obtain ⟨F, hF, hFcard, hFker, hFmap⟩ :=
    exists_elemAbelian_of_inversions hφ (by rw [hφker]) h w hcomm hord hinv hfix
  have hDU : Subgroup.closure (Set.range h) ≤
      Subgroup.normalizer ((U : Subgroup (TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩)) :
        Set (TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩)) :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hN i)
  obtain ⟨R, hR1, hR2, hFR⟩ := exists_two_subgroup_normalized_of_cover hφ (by rw [hφker]) hU1 hU2
    (S := F) (fun x hx u hu =>
      (Subgroup.mem_normalizer_iff.mp (hDU (hFmap ⟨x, hx, rfl⟩)) u).mp hu)
  refine ⟨F.map L.subtype, R.map L.subtype, Subgroup.map_subtype_le F, Subgroup.map_subtype_le R,
    hF.map L.subtype, hR2.map L.subtype, ?_, ?_, ?_⟩
  · intro h0
    exact hR1 ((Subgroup.map_eq_bot_iff_of_injective R L.subtype_injective).mp h0)
  · exact (Subgroup.map_mono hFR).trans (Subgroup.le_normalizer_map L.subtype)
  · have hbot : F.map L.subtype ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨⟨f, hf, rfl⟩, hc⟩
      have hfc : f ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hc l l.2
      have hmem : f ∈ F ⊓ φ.ker := ⟨hf, hφker ▸ hfc⟩
      rw [hFker] at hmem
      rw [Subgroup.mem_bot.mp hmem]
      rfl
    rw [hbot, Subgroup.card_bot, mul_one, Subgroup.card_map_of_injective L.subtype_injective, hFcard]

end CFSG.LocalAnalysis.GLTheoremA.T158

end
