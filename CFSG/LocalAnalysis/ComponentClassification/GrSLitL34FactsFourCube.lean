module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFourCubeLift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFourCubeTargets
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFourCubeNormal

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

open CFSG Subgroup

theorem card_GL32 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem factorization_two_eq {k m : ℕ} (hm : Odd m) : (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.2 hm)
      (even_iff_two_dvd.2 h2)), add_zero]

theorem exists_sylow_of_equiv {Γ G P : Type*} [Group Γ] [Group G] [Group P] [Finite P]
    (e : G ≃* P) (S : Sylow 2 P) (f : Γ ≃* ↥(S : Subgroup P)) :
    ∃ R : Sylow 2 G, Nonempty (Γ ≃* ↥(R : Subgroup G)) := by
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  have eK : ↥(S : Subgroup P) ≃* ↥((S : Subgroup P).map e.symm.toMonoidHom) :=
    (S : Subgroup P).equivMapOfInjective _ e.symm.injective
  have hc : Nat.card ↥((S : Subgroup P).map e.symm.toMonoidHom) =
      2 ^ (Nat.card G).factorization 2 := by
    rw [← Nat.card_congr eK.toEquiv, S.card_eq_multiplicity, Nat.card_congr e.toEquiv]
  exact ⟨Sylow.ofCard _ hc,
    ⟨f.trans (eK.trans (MulEquiv.subgroupCongr (Sylow.coe_ofCard _ hc).symm))⟩⟩

theorem exists_sylow_hs :
    ∃ R : Sylow 2 Blueprint.NativeSporadic.HS,
      Nonempty (Gam 0 ≃* ↥(R : Subgroup Blueprint.NativeSporadic.HS)) := by
  obtain ⟨hfin, hcard⟩ := card_gam_le (d := 0) (Or.inl rfl)
  have hinj : Function.Injective hsGam := by
    have hb := (MonoidHom.rangeRestrict_surjective hsGam).bijective_of_nat_card_le
      (by rw [card_range_hsGam]; exact hcard)
    intro g g' h
    exact hb.1 (Subtype.ext h)
  have eH : hsGam.range ≃* hsGam.range.subgroupOf CFSG.RankThree.Native.hs100P :=
    (Subgroup.subgroupOfEquivOfLe range_hsGam_le).symm
  have hS : Nat.card (hsGam.range.subgroupOf CFSG.RankThree.Native.hs100P) =
      2 ^ (Nat.card CFSG.RankThree.Native.hs100P).factorization 2 := by
    rw [← Nat.card_congr eH.toEquiv, card_range_hsGam, CFSG.RankThree.Native.card_hs100P,
      show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num,
      factorization_two_eq (k := 9) (m := 86625) ⟨43312, rfl⟩]
    norm_num
  exact exists_sylow_of_equiv CFSG.RankThree.Native.hs100Equiv (Sylow.ofCard _ hS)
    ((MonoidHom.ofInjective hinj).trans
      (eH.trans (MulEquiv.subgroupCongr (Sylow.coe_ofCard _ hS).symm)))

theorem exists_sylow_on :
    ∃ R : Sylow 2 Blueprint.NativeSporadic.ON,
      Nonempty (Gam d1 ≃* ↥(R : Subgroup Blueprint.NativeSporadic.ON)) := by
  obtain ⟨hfin, hcard⟩ := card_gam_le (d := d1) (Or.inr rfl)
  have hinj : Function.Injective onGam := by
    have hb := (MonoidHom.rangeRestrict_surjective onGam).bijective_of_nat_card_le
      (by rw [card_range_onGam]; exact hcard)
    intro g g' h
    exact hb.1 (Subtype.ext h)
  have heq : onGam.range = CFSG.ONSchreier.rhoT.range := by
    rw [CFSG.ONSchreier.rhoT_range]
    refine Subgroup.eq_of_le_of_card_ge range_onGam_le ?_
    rw [← CFSG.ONSchreier.rhoT_range, CFSG.ONSchreier.card_rhoT_range, card_range_onGam]
  have e3 : CFSG.ONSchreier.rhoT.range ≃* CFSG.ONSchreier.onT :=
    (MonoidHom.ofInjective CFSG.ONSchreier.rhoT_injective).symm
  have e4 : CFSG.ONSchreier.onT ≃* ↥(CFSG.ONSchreier.onTSylow : Subgroup CFSG.ONSchreier.Pv) :=
    (Subgroup.subgroupOfEquivOfLe CFSG.ONSchreier.onT_le).symm.trans
      (MulEquiv.subgroupCongr CFSG.ONSchreier.onTSylow_coe.symm)
  exact exists_sylow_of_equiv CFSG.ONSchreier.onEquivPv CFSG.ONSchreier.onTSylow
    ((MonoidHom.ofInjective hinj).trans ((MulEquiv.subgroupCongr heq).trans (e3.trans e4)))

theorem fourCubeSylow :
    FourCubeSylowFact := by
  intro L _ _ T hι hC hφ Q
  obtain ⟨ι⟩ := hι
  obtain ⟨φ, hφs, hφk⟩ := hφ
  have : T.Normal := hφk ▸ φ.normal_ker
  obtain ⟨ι', x, y, hx, hy⟩ := exists_std_lifts ι hC hφs hφk
  have hT0 : ∀ g, mat ι' g = 1 → g ∈ T := fun g hg => mem_of_mat_eq_one ι' hC hg
  obtain ⟨a, b, ha, hb, ha2, hb2, d, hd01, hd⟩ := exists_std_pair ι' hT0 hx hy
  obtain ⟨hfin, hcard⟩ := card_gam_le hd01
  have hinj := gamHom_injective ι' ha hb ha2 hb2 hd hfin hcard
  have hR : Nat.card (gamHom ι' ha hb ha2 hb2 hd).range = 512 :=
    le_antisymm (by rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]; exact hcard)
      (card_range_ge ι' ha hb ha2 hb2 hd)
  have hL : Nat.card L = 2 ^ 9 * 21 := by
    rw [T.card_eq_card_quotient_mul_card_subgroup, card_T ι', ← hφk,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv, card_GL32]
    norm_num
  let P : Sylow 2 L := Sylow.ofCard (gamHom ι' ha hb ha2 hb2 hd).range (by
    rw [hR, hL, factorization_two_eq (k := 9) (m := 21) ⟨10, rfl⟩]
    norm_num)
  have eQ : ↥(Q : Subgroup L) ≃* ↥(P : Subgroup L) := Q.equiv P
  have eP : ↥(P : Subgroup L) ≃* Gam d := (MonoidHom.ofInjective hinj).symm
  rcases hd01 with rfl | rfl
  · obtain ⟨R, ⟨eR⟩⟩ := exists_sylow_hs
    exact Or.inl ⟨R, ⟨eQ.trans (eP.trans eR)⟩⟩
  · obtain ⟨R, ⟨eR⟩⟩ := exists_sylow_on
    exact Or.inr ⟨R, ⟨eQ.trans (eP.trans eR)⟩⟩

end CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

namespace CFSG.ComponentClassification.GrSLit

theorem fourCubeSylowFact :
    FourCubeSylowFact :=
  L34Facts.FourCube.fourCubeSylow

end CFSG.ComponentClassification.GrSLit
