module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRDisp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPRows
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQ

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem subfieldGrp_map {R S : Type} [Group R] [Group S] (φ : R ≃* S) {f : MulAut R} {g : MulAut S}
    (h : ∀ x, φ (f x) = g (φ x)) {D : Subgroup R} (hD : SubfieldGrp f D) :
    SubfieldGrp g (D.map φ.toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := hD
  have hT : FP.fixSub g = (FP.fixSub f).map φ.toMonoidHom := by
    ext y
    constructor
    · intro hy
      refine ⟨φ.symm y, FP.mem_fixSub.2 (φ.injective ?_), by simp⟩
      rw [h, MulEquiv.apply_symm_apply]
      exact FP.mem_fixSub.1 hy
    · rintro ⟨x, hx, rfl⟩
      refine FP.mem_fixSub.2 ?_
      show g (φ x) = φ x
      rw [← h, FP.mem_fixSub.1 hx]
  rw [SubfieldGrp, hT]
  refine ⟨Subgroup.map_mono h1, ?_, ?_⟩
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono h2
  · rw [Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
    exact h3

noncomputable def equivMapEquiv {R S : Type} [Group R] [Group S] (φ : R ≃* S) (D : Subgroup R) :
    ↥D ≃* ↥(D.map φ.toMonoidHom) :=
  D.equivMapOfInjective φ.toMonoidHom φ.injective

section Lift


variable {G : Type} [Group G] [Finite G]

theorem fieldOn_subfield {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {g : G}
    (hF : FieldOn p g L) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) ∧
      MarkedModel lab (PSimple p L) ∧ p ∣ lab.n ∧
      ∃ D : Subgroup (PSimple p L), SubfieldGrp (indAut p L g hF.1) D ∧
        (CFSG.Assembly.LargeEvenRawDatum ⟨lab.tag, lab.rank, lab.n / p⟩
            (fun R' _ _ _ => Nonempty (↥D ≃* R')) ∨ SubfieldExc p lab D) := by
  have h := canon_marking_and_labelAll_simple' (P' := fun lab R _ I F =>
      ¬ (lab.tag = .triD4 ∧ p = 3) → SubfieldBody p lab R I F)
    (fun lab hlab => by
      by_cases h3 : lab.tag = .triD4 ∧ p = 3
      · exact (canonRawInnAny hp.ne_one hlab).mono fun R _ I F _ hs hna h => absurd h3 h
      · exact (canonSubfield hp hp2 hlab h3).mono fun R _ I F h' hs hna _ => h' hs hna) hF.2
  obtain ⟨lab, hlab, R, _, I, F, θ, hs, hna, ⟨hP, hSub⟩, hM⟩ :=
    Canonical.largeEvenMarking_exists_markedModel h
  obtain ⟨hne, f, hf, u, hu, hord, he⟩ := fieldOn_data hF.1 θ hP
  have h3 : ¬ (lab.tag = .triD4 ∧ p = 3) := by
    rintro ⟨h, h'⟩
    rcases hne with h0 | h0
    · exact h0 h
    · exact h0 h'
  obtain ⟨hpn, D, hD, hdat⟩ := hSub h3 f hf hord
  have hDu : SubfieldGrp (u * f * u⁻¹) (D.map (u : R ≃* R).toMonoidHom) :=
    subfieldGrp_map (u : R ≃* R) (fun x => by simp) hD
  have hDS : SubfieldGrp (indAut p L g hF.1)
      ((D.map (u : R ≃* R).toMonoidHom).map θ.symm.toMonoidHom) := by
    refine subfieldGrp_map θ.symm (f := u * f * u⁻¹) (fun x => ?_) hDu
    rw [← he]
    simp [MulAut.congr_apply]
  have eD : ↥((D.map (u : R ≃* R).toMonoidHom).map θ.symm.toMonoidHom) ≃* ↥D :=
    (equivMapEquiv θ.symm _).symm.trans (equivMapEquiv (u : R ≃* R) D).symm
  refine ⟨lab, hlab, h3, MarkedModel.of_mulEquiv θ.symm hM, hpn, _, hDS, ?_⟩
  rcases hdat with hdat | hexc
  · exact Or.inl (Canonical.largeEvenRawDatum_mono (fun R' _ I' F' ⟨e⟩ => ⟨eD.trans e⟩) hdat)
  · refine Or.inr ?_
    rcases hexc with ⟨h1, h2, h4⟩ | h5
    · exact Or.inl ⟨h1, h2, Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom)
        eD.injective⟩
    · exact Or.inr h5

theorem centralizer_lift {p : ℕ} (hp : p.Prime) {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hbp : b ^ p = 1) :
    ((L ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) =
      FP.fixSub (HardMathSupport.Solomon.LocalBalance.barAut p L ⟨b⁻¹, Subgroup.inv_mem _ hb⟩) := by
  have hb' : b⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hb
  have hap : IsPGroup p (Subgroup.zpowers b⁻¹) :=
    isPGroup_zpowers_of_pow_eq_one (by rw [inv_pow, hbp, inv_one])
  have h := map_fixSubgroup_pQuotHom hp hb' hap
  rw [fixSubgroup_normalizerMonoidHom hb'] at h
  have e : Subgroup.centralizer ({b⁻¹} : Set G) = Subgroup.centralizer ({b} : Set G) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff (a := x) (b := b)
  rw [e] at h
  exact h

theorem fieldOn_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hbp : b ^ p = 1) :
    SubfieldGrp (indAut p L b hb)
      (((L ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf L).map (chevQuotHom p L)) := by
  have hY := centralizer_lift hp hb hbp
  have hZo : Odd (Nat.card (Subgroup.center (PQuot p L))) := odd_card_center_pQuot hp hp2 L
  have hmk : ∀ x : PQuot p L, indAut p L b hb (QuotientGroup.mk x) =
      QuotientGroup.mk (HardMathSupport.Solomon.LocalBalance.barAut p L
        ⟨b⁻¹, Subgroup.inv_mem _ hb⟩ x) := fun x =>
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk _ _
  obtain ⟨h1, h2, h3⟩ := subfield_core (Subgroup.center (PQuot p L)) le_rfl hZo
    (HardMathSupport.Solomon.LocalBalance.barAut p L ⟨b⁻¹, Subgroup.inv_mem _ hb⟩)
    (indAut p L b hb) hmk
  have hmap : ((L ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf L).map (chevQuotHom p L) =
      (FP.fixSub (HardMathSupport.Solomon.LocalBalance.barAut p L
        ⟨b⁻¹, Subgroup.inv_mem _ hb⟩)).map (QuotientGroup.mk' (Subgroup.center (PQuot p L))) := by
    rw [← hY, Subgroup.map_map]
    rfl
  rw [hmap]
  exact ⟨h1, h2, h3⟩

end Lift

end FR

end CFSG.LocalAnalysis.GLTheoremA
