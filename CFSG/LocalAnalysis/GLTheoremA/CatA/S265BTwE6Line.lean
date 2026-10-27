module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HTE6Model
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterIn
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompModel
import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.TE6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Seitz
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterInAux
  (mem_inn_sup_diag_of_pow_three)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs
  (glaPComponent_eq_comap_of_langSetup)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs (ratQuasiEq_holds)
open CFSG.LocalAnalysis.GLTheoremA.CatB.I2610
  (exists_twistedE6RootGroup_of_catalogIs_isTE6two)

private theorem nonempty_centerQuot_equiv_pSimple {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L) [Nontrivial (PSimple 3 L)] :
    Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* PSimple 3 L) := by
  have : Nontrivial (PQuot 3 L) := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PSimple 3 L)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  refine psimple_equiv_of_central_surj hq (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))
    (QuotientGroup.mk'_surjective _) ?_
  rw [QuotientGroup.ker_mk']
  refine le_center_of_normal_of_isQuasisimple hq inferInstance fun htop => ?_
  obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 L)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (QuotientGroup.eq.2 (by rw [htop]; exact Subgroup.mem_top _))


theorem exists_twE6LineModel_of_glaPComponent_of_equiv {P : Type} [Group P] [Finite P]
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2)
    (e : P ≃* twistedE6RootGroup K σ) {β : MulAut P} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    {J : Subgroup P} (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    ∃ (h : twistedE6InndiagGL K σ) (_ : h ^ 3 = 1) (_ : h ≠ 1) (D : TwE6LineLang K σ 2 h)
      (i : KernelComponent (rootCharHom D.a)),
      MulAut.congr e β = twistedE6InndiagConj K σ h ∧
      CFSG.IsQuasisimple (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ∧
      J.map e.toMonoidHom = (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i).comap D.ι ∧
      IsComponentOf (J.map e.toMonoidHom)
        (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) ∧
      Nonempty (PSimple 3 J ≃*
        (↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom))) := by
  have hβ'3 : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hβ'1 : MulAut.congr e β ≠ 1 := fun h1 =>
    hβ1 ((MulAut.congr e).injective (h1.trans (map_one (MulAut.congr e)).symm))
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  have hmem := mem_inn_sup_diag_of_pow_three hK σ hσ hβ'3
  rw [← range_twistedE6InndiagConj] at hmem
  obtain ⟨h, hh⟩ := hmem
  have hinj := twistedE6InndiagConj_injective Nat.prime_two le_rfl hK2 σ hσ2
  have hh3 : h ^ 3 = 1 := hinj (by rw [map_pow, hh, hβ'3, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ'1 (by rw [← hh, h', map_one])
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; decide
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ 2 hK3 hσ (by rw [hK]; norm_num) le_rfl h hh1 hh3
  have hJe : GLAPComponent 3 (fixSubgroup (MulAut.congr e β)) (J.map e.toMonoidHom) := by
    rw [CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr]
    refine glaPComponent_map Nat.prime_three e.toMonoidHom ?_ hJ
    rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).2 e.injective, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hJh := hJe
  rw [← hh] at hJh
  have hq2 : D.S.D.q = 2 := D.hSq.trans D.hqe.symm
  obtain ⟨i, hqi, -, hJi⟩ := glaPComponent_eq_comap_of_langSetup D.S Nat.prime_three D.ι D.hinj
    D.hrange _ D.hconj D.hT D.hap D.h1 D.hTame
    (ratQuasiEq_holds _ _ D.S D.a hq2 D.hT D.hap D.h1) hJh
  have hcomp : IsComponentOf (J.map e.toMonoidHom)
      (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) := by
    rw [hJi]
    exact D.isComponentOf_comap i hqi
  obtain ⟨e1⟩ := nonempty_pSimple_equiv_map Nat.prime_three e.toMonoidHom hJ hJe
  have := (chev_pSimple_simple_nonabelian Nat.prime_three hJe).1
  obtain ⟨e2⟩ := nonempty_centerQuot_equiv_pSimple hcomp.2.2
  exact ⟨h, hh3, hh1, D, i, hh.symm, hqi, hJi, hcomp, ⟨e1.trans e2.symm⟩⟩

theorem exists_twE6LineModel_of_glaPComponent {P : Type} [Group P] [Finite P]
    (hP : catalogIs P S9.isTE6two) {β : MulAut P} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    {J : Subgroup P} (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K) (_ : Nat.card K = 4)
      (_ : ∀ c, σ c = c ^ 2) (e : P ≃* twistedE6RootGroup K σ) (h : twistedE6InndiagGL K σ)
      (_ : h ^ 3 = 1) (_ : h ≠ 1) (D : TwE6LineLang K σ 2 h)
      (i : KernelComponent (rootCharHom D.a)),
      MulAut.congr e β = twistedE6InndiagConj K σ h ∧
      CFSG.IsQuasisimple (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ∧
      J.map e.toMonoidHom = (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i).comap D.ι ∧
      IsComponentOf (J.map e.toMonoidHom)
        (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) ∧
      Nonempty (PSimple 3 J ≃*
        (↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom))) := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_twistedE6RootGroup_of_catalogIs_isTE6two hP
  obtain ⟨h, hh3, hh1, D, i, hres⟩ :=
    exists_twE6LineModel_of_glaPComponent_of_equiv hK hσ e hβ3 hβ1 hJ
  exact ⟨K, inferInstance, inferInstance, σ, hK, hσ, e, h, hh3, hh1, D, i, hres⟩

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
