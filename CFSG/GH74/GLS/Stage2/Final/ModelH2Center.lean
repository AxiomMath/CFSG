module

public import CFSG.GH74.GLS.Stage2.Final.ModelFam
public import CFSG.GH74.GLS.Stage2.Final.ModelOdd

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem negOne_central_H2 (g : GL (Fin 2) F) : g * (-1 : GL (Fin 2) F) = (-1) * g := by
  simp

theorem center_H2_eq [Finite F] {M : ModelData F} (hG : GoodModel M) :
    (Subgroup.center ↥M.H2).map M.H2.subtype = Subgroup.zpowers (-1 : GL (Fin 2) F) := by
  obtain ⟨a, b, hab, hH⟩ := hG.quat
  ext g
  constructor
  · rintro ⟨⟨g, hg⟩, hc, rfl⟩
    have hcomm : ∀ c, g * rhoQ hab c = rhoQ hab c * g := fun c => by
      have := Subgroup.mem_center_iff.1 hc ⟨rhoQ hab c, hH c⟩
      exact (congrArg Subtype.val this).symm
    obtain ⟨l, rfl⟩ := rhoQ_irr hab hG.two_ne_zero g hcomm
    have hdet : (sc2 l : GL (Fin 2) F) ∈ M.H2 := hg
    have h1 := ((M.mem_H2 _).1 hdet).2
    rw [det_sc2] at h1
    have hll : l * l = 1 := Units.ext (by simpa [sq] using h1)
    rcases units_sq_eq_one hll with rfl | rfl
    · exact ⟨0, by simp [sc2_one]⟩
    · refine ⟨1, ?_⟩
      show (-1 : GL (Fin 2) F) ^ (1 : ℤ) = sc2 (-1)
      rw [zpow_one]
      exact (CFSG.GH74.L5U5.scalar_neg_one_eq (F := F) 2).symm
  · rintro hg
    obtain ⟨n, rfl⟩ := hg
    refine ⟨⟨(-1 : GL (Fin 2) F) ^ n, M.H2.zpow_mem M.neg_one_mem_H2 n⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro h
    apply Subtype.ext
    show (h : GL (Fin 2) F) * (-1) ^ n = (-1) ^ n * h
    have : ((-1 : GL (Fin 2) F) ^ n) ∈ Subgroup.center (GL (Fin 2) F) :=
      (Subgroup.center (GL (Fin 2) F)).zpow_mem (by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨-1, by rw [CFSG.GH74.L5U5.scalar_neg_one_eq]⟩) n
    exact Subgroup.mem_center_iff.1 this h

theorem hasSL2Model_H2_lin (F : Type) [Field F] [Finite F] :
    CFSG.GH74.GLS.HasSL2Model ↥(ModelData.lin F).H2 (fun r => r = Nat.card F) :=
  ⟨F, inferInstance, inferInstance, rfl, ⟨MulEquiv.refl _⟩⟩

theorem hasSL2Model_H2_sp (F : Type) [Field F] [Finite F] :
    CFSG.GH74.GLS.HasSL2Model ↥(ModelData.sp F).H2 (fun r => r = Nat.card F) :=
  ⟨F, inferInstance, inferInstance, rfl,
    ⟨(ModelSp.sp_sl2_equiv_H2 F).symm.trans (specialLinearGroupEquivStatedSL 2 F)⟩⟩

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg in
theorem hasSL2Model_H2_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) :
    CFSG.GH74.GLS.HasSL2Model ↥(ModelData.uni hF).H2 (fun r => r = p ^ f) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 2
  have e : Nonempty (SL(2, fixedSubfield F p f) ≃* StatedSU 2 (p ^ f) F) :=
    ⟨((hypEquiv hζ0 hζ).trans (conjEquiv P hP)).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hF 2))⟩
  obtain ⟨e⟩ := e
  refine ⟨↥(fixedSubfield F p f), inferInstance, inferInstance, card_fixedSubfield hF, ⟨?_⟩⟩
  exact e.symm.trans (specialLinearGroupEquivStatedSL 2 _)

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
