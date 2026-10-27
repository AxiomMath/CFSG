module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB71Step1
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPMatch
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped MatrixGroups

namespace Eight2

variable {X : Type} [Group X] [Finite X]

theorem false_of_sl2_conj (hS : SchreierFor Blueprint.Catalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ w : X, orderOf w = 2 ∧ oddCore (centralizer ({w} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a z b δ g : X} {J : Subgroup X} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))))
    (hCJ : centralizer ({a} : Set X) ≤ normalizer (J : Set X)) (hzJ : z ∈ J) (hzz : z * z = 1)
    (haJ : a ∉ J) (hga : g⁻¹ * a * g = δ) (hgz : g⁻¹ * z * g = b) {N : Subgroup X}
    (hNX : N ≤ centralizer ({b} : Set X) ⊓ centralizer ({δ} : Set X))
    (hN : IsPComponent 2 (N.subgroupOf (centralizer ({b} : Set X) ⊓ centralizer ({δ} : Set X))))
    (hδN : δ ∈ N) {p' n : ℕ} (hp' : Fact p'.Prime) (hp'2 : p' ≠ 2) (hn : 0 < n)
    (eN : ↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : X ≃* X := MulAut.conj g with hφ
  have hφa : φ δ = a := by
    rw [hφ, MulAut.conj_apply, ← hga]
    group
  have hφb : φ b = z := by
    rw [hφ, MulAut.conj_apply, ← hgz]
    group
  have hCmap : (centralizer ({b} : Set X) ⊓ centralizer ({δ} : Set X)).map φ.toMonoidHom =
      centralizer ({a} : Set X) ⊓ centralizer ({z} : Set X) := by
    rw [Subgroup.map_inf _ _ _ φ.injective, CatFactsSp4.map_centralizer_singleton,
      CatFactsSp4.map_centralizer_singleton, hφa, hφb, inf_comm]
  have hN'pc : IsPComponent 2 ((N.map φ.toMonoidHom).subgroupOf (centralizer ({a} : Set X) ⊓
      centralizer ({z} : Set X))) := by
    have h1 := CatFactsSp4.isPComponent_map_subgroupOf 2 φ hNX hN
    rwa [hCmap] at h1
  have hN'X : N.map φ.toMonoidHom ≤ centralizer ({a} : Set X) ⊓ centralizer ({z} : Set X) := by
    rw [← hCmap]
    exact map_mono hNX
  have haN' : a ∈ N.map φ.toMonoidHom := by
    rw [← hφa]
    exact mem_map_of_mem _ hδN
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact absurd ha (by norm_num)
  have hCa : centralizer ({a} : Set X) ≠ ⊤ := by
    intro htop
    apply ha1
    have hcen : a ∈ center X := by
      rw [mem_center_iff]
      intro w
      exact mem_centralizer_singleton_iff.mp (htop ▸ mem_top w)
    have hbot : center X = ⊥ := by
      rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨u, v, huv⟩ := hnonab
        exact huv ((mem_center_iff.mp (h1 ▸ mem_top v : v ∈ center X)) u)
    rw [hbot] at hcen
    exact mem_bot.mp hcen
  have hsch : LBalance.SchreierSections ↥(centralizer ({a} : Set X)) :=
    schreierSections_of_isKGroupCat hS (isKGroupCat_of_ne_top' hK hCa)
  have hzC : z ∈ centralizer ({a} : Set X) := hJa hzJ
  have hN'L : N.map φ.toMonoidHom ≤ layerIn (centralizer ({a} : Set X)) := by
    have h1 := lBalancePLayer_inf_centralizer_le_of_sections (p := 2) hsch hzC
      ⟨1, by rw [pow_one, pow_two]; exact hzz⟩
    rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
    refine le_trans ?_ h1
    have h2 : (N.map φ.toMonoidHom).subgroupOf (centralizer ({a} : Set X) ⊓
        centralizer ({z} : Set X)) ≤
        pLayer ↥(centralizer ({a} : Set X) ⊓ centralizer ({z} : Set X)) 2 :=
      le_sSup hN'pc
    have h3 := map_mono
      (f := (centralizer ({a} : Set X) ⊓ centralizer ({z} : Set X)).subtype) h2
    rwa [map_subgroupOf_eq_of_le hN'X] at h3
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  obtain ⟨M, hMC, hMpc, -, haM, ⟨eM⟩⟩ := Seven.exists_isPComponent_of_isPComponent_inf hJa hJ
    hCJ hzJ hzz hN'X hN'pc hN'L haN' hJa haa haJ
  let e₀ : ↥(N.map φ.toMonoidHom) ≃* ↥N :=
    (N.equivMapOfInjective φ.toMonoidHom φ.injective).symm
  let e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, GaloisField p' n) :=
    eM.symm.trans ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₀).trans eN)
  have hchar : ringChar (GaloisField p' n) ≠ 2 := by
    rw [ringChar.eq (GaloisField p' n) p']
    exact hp'2
  have hrank : CFSG.pRank 2 M ≤ 1 := by
    have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 M) := fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
    rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd,
      UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two e]
    exact TBLit.pRank_two_SL2_le_one hchar
  exact intrinsic_rank_one_exclusion hCI hUc hnonab hunb hU ha hMC hMpc haM hrank
    (.inl ⟨p', n, hp', hp'2, hn,
      ⟨(QuotientGroup.quotientMulEquivOfEq (TBLit.classicalInvolutionOddCore_eq M)).trans e⟩⟩)

end Eight2

end CFSG.ComponentClassification.GSThmB
