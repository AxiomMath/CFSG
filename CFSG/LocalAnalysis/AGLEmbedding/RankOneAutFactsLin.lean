module

public import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutFactsCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreLin
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThreeFamilies

public section

namespace CFSG.AGLEmbedding.RankOneAut

open CFSG.Open CFSG.PSL2Table CFSG.GH74.GLS.IVK CFSG.AGLEmbedding.KFactProofs.RankOneCore
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Model

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem unipotent_eq_sl2RootX : unipotent F = sl2RootX (mk : SL(2, F) →* PSL(2, F)) := by
  ext x
  rw [mem_unipotent_iff_exists, mem_sl2RootX]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

omit [Finite F] in
theorem mk_eq_one_scalar (g : SL(2, F)) (hg : (mk : SL(2, F) →* PSL(2, F)) g = 1) :
    ∃ l : Fˣ, l ^ 2 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) F) = (l : F) • 1 := by
  have hc : g ∈ Subgroup.center SL(2, F) := (QuotientGroup.eq_one_iff g).1 hg
  rcases (mem_center_SL_iff g).1 hc with rfl | rfl
  · exact ⟨1, one_pow 2, by simp⟩
  · exact ⟨-1, by simp, by simp⟩

omit [Finite F] in
theorem weyl_mul_sl2Upper (c : F) : weyl * sl2Upper F c = sl2Lower F (-c) * weyl := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_weyl]
  show !![0, -1; 1, 0] * !![1, c; 0, 1] = !![1, 0; -c, 1] * !![(0 : F), -1; 1, 0]
  simp

omit [Finite F] in
theorem map_conj_weyl_unipotent :
    (unipotent F).map (MulAut.conj (mk (weyl : SL(2, F)))).toMonoidHom =
      sl2RootY (mk : SL(2, F) →* PSL(2, F)) := by
  rw [unipotent_eq_sl2RootX]
  ext x
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨-c, ?_⟩
    change mk (sl2Lower F (-c)) = mk weyl * mk (sl2Upper F c) * (mk weyl)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, weyl_mul_sl2Upper, mul_inv_cancel_right]
  · rintro ⟨c, rfl⟩
    refine ⟨mk (sl2Upper F (-c)), ⟨-c, rfl⟩, ?_⟩
    change mk weyl * mk (sl2Upper F (-c)) * (mk weyl)⁻¹ = mk (sl2Lower F c)
    rw [← map_inv, ← map_mul, ← map_mul, weyl_mul_sl2Upper, neg_neg, mul_inv_cancel_right]

omit [Finite F] in
theorem sl2RootY_ne_unipotent (h2 : (2 : F) ≠ 0) :
    sl2RootY (mk : SL(2, F) →* PSL(2, F)) ≠ unipotent F := by
  intro h
  have hy : mk (sl2Lower F 1) ∈ unipotent F := h ▸ ⟨1, rfl⟩
  obtain ⟨t, ht⟩ := (mem_unipotent_iff_exists _).1 hy
  rcases (mk_eq_mk_iff _ _).1 ht with h1 | h1
  · have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 0) h1
    simp [sl2Lower, unip] at this
  · have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h1
    simp only [neg_apply_SL] at this
    simp [sl2Lower, unip] at this
    exact h2 (by linear_combination this)

theorem borelMetabelianAt_psl2 {p n : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ n)
    (h2 : (2 : F) ≠ 0) : BorelMetabelianAt PSL(2, F) (unipotent F) := by
  have := Fintype.ofFinite F
  have hinj : Function.Injective (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)) :=
    mulAutConj_injective_of_center_eq_bot (CFSG.GorensteinWalter.psl2_center_eq_bot F)
  obtain ⟨Q, hQ⟩ := L2Borel.exists_sylow_unipotent (F := F) hF
  have hTI : KSylowTI p PSL(2, F) := kSylowTI_of_rankOneCoreData fun U =>
    RankOneCoreData.of_equiv_sylow (MulEquiv.refl _) U Q (hQ ▸ rankOneCoreData_psl2 h2)
  have hcard : Nat.card (Sylow p PSL(2, F)) = Nat.card (Q : Subgroup PSL(2, F)) + 1 := by
    obtain ⟨h1, h3⟩ := KFactProofs.OneLieSylow.card_psl2_unipotent h2
    rw [Sylow.card_eq_index_normalizer Q]
    change (Subgroup.normalizer ((Q : Subgroup PSL(2, F)) : Set PSL(2, F))).index = _
    rw [hQ, h3, h1]
  let QY : Sylow p PSL(2, F) := mk (weyl : SL(2, F)) • Q
  have hQY : (QY : Subgroup PSL(2, F)) = sl2RootY (mk : SL(2, F) →* PSL(2, F)) := by
    rw [← map_conj_weyl_unipotent, ← hQ, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hQYQ : QY ≠ Q := fun h => sl2RootY_ne_unipotent h2 (by rw [← hQY, ← hQ, h])
  have hA := exceptional_central_SL2_pair_stabilizer (mk : SL(2, F) →* PSL(2, F))
    mk_surjective mk_eq_one_scalar
  rw [← unipotent_eq_sl2RootX] at hA
  refine borelMetabelianAt_of_pairAut hinj hA fun α hα => ?_
  obtain ⟨W, hW⟩ : ∃ W : Sylow p PSL(2, F),
      (W : Subgroup PSL(2, F)) = (sl2RootY mk).map α.toMonoidHom :=
    ⟨QY.mapSurjective (f := α.toMonoidHom)
      (by rw [MulEquiv.coe_toMonoidHom]; exact α.surjective),
      by rw [Sylow.coe_mapSurjective, hQY]⟩
  have hWQ : W ≠ Q := by
    intro h
    apply sl2RootY_ne_unipotent h2
    have h1 : (sl2RootY mk).map α.toMonoidHom = (unipotent F).map α.toMonoidHom := by
      rw [← hW, h, hQ, hα]
    exact (Subgroup.map_injective α.injective) h1
  obtain ⟨u, hu, huW⟩ := exists_map_conj_eq_of_ti hTI Q QY W hQYQ hWQ hcard
  rw [hQ] at hu
  refine ⟨u, hu, ?_⟩
  rw [hQY, hW] at huW
  have h1 : ((MulAut.conj u)⁻¹ * α).toMonoidHom =
      ((MulAut.conj u)⁻¹).toMonoidHom.comp α.toMonoidHom := rfl
  rw [h1, ← Subgroup.map_map, ← huW, Subgroup.map_map]
  have h3 : ((MulAut.conj u)⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    simp
  rw [h3, Subgroup.map_id]

end Model

theorem rankOneLieAutFacts_linTwo {K : Type} [Group K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 1 ≤ n) (h3 : 3 < p ^ n) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsLinTwoIndex p n d) (h : Nonempty (K ≃* CatGroup d)) : RankOneLieAutFacts p K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  obtain ⟨e₀⟩ := h
  let e : K ≃* PSL2GF p n := e₀.trans eP
  have hF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : GaloisField p n) = 0 := by simpa using h0
    have := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).1 h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  refine ⟨?_, kSylowTI_of_rankOneCoreData (rankOneCoreData_linTwo hp2 hn hd ⟨e₀⟩), ?_⟩
  · have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p n)) :=
      ⟨p, n, hp, hp.odd_of_ne_two hp2, hn, hF⟩
    exact kOutRankLeOne_of_outPChain hp
      (CFSG.RankThree.PartOne.OutStructure.OutPNice.of_mulEquiv e
        (CFSG.LocalAnalysis.RankThreeTheoremC.outPNice_PSL2_field_of_ne_two hp hp2
          (GaloisField p n) hF hodd (hF ▸ h3))).toChain
  · intro U
    obtain ⟨Q, hQ⟩ := L2Borel.exists_sylow_unipotent (F := GaloisField p n) hF
    obtain ⟨e', he'⟩ := KFactProofs.SmallGamma.exists_equiv_map_eq e U Q
    exact BorelMetabelianAt.of_equiv e' (he'.trans hQ) (borelMetabelianAt_psl2 hF h2)

end CFSG.AGLEmbedding.RankOneAut
