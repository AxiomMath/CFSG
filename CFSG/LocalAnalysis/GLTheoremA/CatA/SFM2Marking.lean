module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM2Delta
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPFieldN
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.Adapters.LieModelSimple
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.StandardType CFSG.StandardType.ChevTwo CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
open CFSG.Yardstones.Md0ec50421ce4

theorem marking_b2der_n_one {X : Type} [Group X] (hX : commutator X = ⊤)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) :
    CFSG.Assembly.LargeEvenMarkingLegacy X fun lab _ _ _ _ _ => lab.n = 1 := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := e.isSimpleGroup
  have hK : Nat.card (ZMod 2) = 2 := by simp
  obtain ⟨e₆⟩ := nonempty_b2der_equiv_alternatingGroup hK
  have hnab := exists_mul_ne_mul_centerQuot_of_perfect hX inferInstance
  let θ := e.trans e₆.symm
  refine ⟨hX, ⟨.B2der, 0, 1⟩, ⟨le_rfl, rfl, rfl⟩, ZMod 2, inferInstance, inferInstance, hK, ?_⟩
  exact ⟨θ.symm.isSimpleGroup, nonabelian_of_mulEquiv θ hnab, θ, rfl⟩

theorem marking_g2der_n_one {X : Type} [Group X]
    (hX : commutator X = ⊤)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 3 1) :
    CFSG.Assembly.LargeEvenMarkingLegacy X fun lab _ _ _ _ _ => lab.n = 1 := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h
  have hK : Nat.card (ZMod 2) = 2 := by simp
  have hC : StatedClassicalModel ↥⁅adjointGroup .G2 (ZMod 2), adjointGroup .G2 (ZMod 2)⁆ .PSU 3 3 1 :=
    (CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds (ZMod 2)
      hK).statedClassicalModel (by simp [classicalTags])
  obtain ⟨φ⟩ := CFSG.ClassicalInvolution.Upgrade.statedClassicalModel_unique (by norm_num) h hC
  have hnab := exists_mul_ne_mul_centerQuot_of_perfect hX inferInstance
  have : IsSimpleGroup ↥⁅adjointGroup .G2 (ZMod 2), adjointGroup .G2 (ZMod 2)⁆ :=
    φ.symm.isSimpleGroup
  have hZ := center_eq_bot_of_isSimpleGroup_of_nonabelian (nonabelian_of_mulEquiv φ hnab)
  let ψ : CFSG.Blueprint.DerivedCentralQuotient (adjointGroup .G2 (ZMod 2)) ≃*
      ↥⁅adjointGroup .G2 (ZMod 2), adjointGroup .G2 (ZMod 2)⁆ :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨e₁⟩ := centerQuot_commutator_chevGroup_equiv (ZMod 2) .G2
  let θ := (φ.trans ψ.symm).trans e₁.symm
  refine ⟨hX, ⟨.G2der, 0, 1⟩, ⟨le_rfl, rfl, rfl⟩, ZMod 2, inferInstance, inferInstance, hK, ?_⟩
  exact ⟨θ.symm.isSimpleGroup, nonabelian_of_mulEquiv θ hnab, θ, rfl⟩

theorem canon_n_one_of_b2der {p : ℕ} {H : Type} [Group H] (δ : MulAut H)
    (hX : commutator (ppQuot p H) = ⊤)
    (e : ppQuot p H ⧸ Subgroup.center (ppQuot p H) ≃* alternatingGroup (Fin 6)) :
    CFSG.Assembly.LargeEvenMarking (PQuot p (deltaL δ)) fun lab _ _ _ _ _ => lab.n = 1 := by
  have h := CFSG.Assembly.largeEvenMarkingLegacy_to_canonical_carrier
    (P := fun lab _ _ θ => lab.n = 1) (marking_b2der_n_one hX e)
  exact canonMarking_congr (deltaQuotIso p δ) (P' := fun lab _ _ _ _ _ => lab.n = 1)
    (by intro lab R _ I F θ h'; exact h') h

theorem canon_n_one_of_g2der {p : ℕ} {H : Type} [Group H]
    (δ : MulAut H) (hX : commutator (ppQuot p H) = ⊤)
    (h : StatedClassicalModel (ppQuot p H ⧸ Subgroup.center (ppQuot p H)) .PSU 3 3 1) :
    CFSG.Assembly.LargeEvenMarking (PQuot p (deltaL δ)) fun lab _ _ _ _ _ => lab.n = 1 := by
  have h' := CFSG.Assembly.largeEvenMarkingLegacy_to_canonical_carrier
    (P := fun lab _ _ θ => lab.n = 1) (marking_g2der_n_one hX h)
  exact canonMarking_congr (deltaQuotIso p δ) (P' := fun lab _ _ _ _ _ => lab.n = 1)
    (by intro lab R _ I F θ h''; exact h'') h'

theorem not_fieldOn_of_marking_n_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {g : G} (hF : S10.FieldOn p g L)
    (hM : CFSG.Assembly.LargeEvenMarking (PQuot p L) fun lab _ _ _ _ _ => lab.n = 1) : False := by
  obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, hn1, hpn⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists
      (CFSG.LocalAnalysis.GLTheoremA.FP.fieldNAt_marking hp hp2 hF hM)
  rw [hn1] at hpn
  exact hp.one_lt.ne' (Nat.dvd_one.1 hpn)

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
