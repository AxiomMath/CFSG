module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusLinearTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial

theorem census_linear_reduce
    (d : TauCeti.ValidLieTypeIndex) {n : ℕ} {q : TauCeti.PrimePower}
    (hd : d.1 = TauCeti.LieTypeIndex.A n q) (hchar : d.1.characteristic = 2) :
    ∀ η : MulAut (TauCeti.CFSGIndex.lie d).Group,
      η ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (TauCeti.CFSGIndex.lie d).Group →
      η ^ 3 = 1 → η ≠ 1 → ∀ r : ℕ, Odd r →
      ∀ J₁ J₂ J₃ : Subgroup (TauCeti.CFSGIndex.lie d).Group,
        CFSG.Open.IsComponentOf J₁ (fixSubgroup η) →
        CFSG.Open.IsComponentOf J₂ (fixSubgroup η) →
        CFSG.Open.IsComponentOf J₃ (fixSubgroup η) →
        J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ →
        catalogIs (↥J₁ ⧸ Subgroup.center ↥J₁) (S10.isL2n r) →
        catalogIs (↥J₂ ⧸ Subgroup.center ↥J₂) (S10.isL2n r) →
        catalogIs (↥J₃ ⧸ Subgroup.center ↥J₃) (S10.isL2n r) →
      ∃ (k : Type) (_ : Field k) (_ : Fintype k)
        (e : (TauCeti.CFSGIndex.lie d).Group ≃* LinearFlag.projectiveSL (n + 1) k)
        (A : GL (Fin (n + 1)) k) (c : kˣ)
        (K₁ K₂ K₃ : Subgroup (LinearFlag.projectiveSL (n + 1) k)),
        Nat.card k = q.card ∧
        CharP k 2 ∧
        A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c ∧
        CFSG.Open.IsComponentOf K₁ (fixSubgroup (LinearFlag.conjAut (n + 1) k A)) ∧
        CFSG.Open.IsComponentOf K₂ (fixSubgroup (LinearFlag.conjAut (n + 1) k A)) ∧
        CFSG.Open.IsComponentOf K₃ (fixSubgroup (LinearFlag.conjAut (n + 1) k A)) ∧
        K₁ ≠ K₂ ∧ K₁ ≠ K₃ ∧ K₂ ≠ K₃ ∧
        catalogIs (↥K₁ ⧸ Subgroup.center ↥K₁) (S10.isL2n r) ∧
        catalogIs (↥K₂ ⧸ Subgroup.center ↥K₂) (S10.isL2n r) ∧
        catalogIs (↥K₃ ⧸ Subgroup.center ↥K₃) (S10.isL2n r) := by
  obtain ⟨d₁, hv⟩ := d
  have hd₁ : d₁ = TauCeti.LieTypeIndex.A n q := hd
  subst hd₁
  have hn1 : 1 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  have hn2 : 2 ≤ n + 1 := Nat.succ_le_succ hn1
  have hpq : q.p = 2 := by simpa using hchar
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let k := GaloisField q.p q.exponent
  have hcardk : Nat.card k = q.card := by
    dsimp only [k]
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne']
    exact (TauCeti.PrimePower.card_def q).symm
  have hchark : CharP k 2 := by
    dsimp only [k]
    exact CharP.congr q.p hpq
  have eModel : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hv⟩).Group ≃*
      LinearFlag.projectiveSL (n + 1) k :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) k)
  intro η hη hη3 hηne r hr J₁ J₂ J₃ hJ₁ hJ₂ hJ₃ h12 h13 h23 hL1 hL2 hL3
  let η' : MulAut (LinearFlag.projectiveSL (n + 1) k) := eModel.symm.trans (η.trans eModel)
  have hη'mem : η' ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      (LinearFlag.projectiveSL (n + 1) k) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr eModel).2 hη
  have hη'3 : η' ^ 3 = 1 := by
    have h := map_pow (MulAut.congr eModel) η 3
    rw [hη3, map_one] at h
    exact h.symm
  have hη'ne : η' ≠ 1 := by
    intro h
    refine hηne ((MulAut.congr eModel).injective ?_)
    rw [show MulAut.congr eModel η = 1 from h, map_one]
  obtain ⟨A, hAeq⟩ := LinearFlag.mem_linearAutGroup_iff.1
    (CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_projectiveSL_le_linearAutGroup
      (m := n + 1) hn2 hη'mem)
  have hconj3 : LinearFlag.conjAut (n + 1) k (A ^ 3) = 1 := by
    rw [map_pow, hAeq, hη'3]
  obtain ⟨c, hc⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_eq_scalar_of_conjAut_eq_one
      (n := n + 1) hn2 hconj3
  have hfix := map_fixSubgroup eModel η
  let K₁ : Subgroup (LinearFlag.projectiveSL (n + 1) k) := J₁.map eModel.toMonoidHom
  let K₂ : Subgroup (LinearFlag.projectiveSL (n + 1) k) := J₂.map eModel.toMonoidHom
  let K₃ : Subgroup (LinearFlag.projectiveSL (n + 1) k) := J₃.map eModel.toMonoidHom
  have hK₁ : CFSG.Open.IsComponentOf K₁
      (fixSubgroup (LinearFlag.conjAut (n + 1) k A)) := by
    have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map eModel hJ₁
    rw [hAeq]
    exact hfix ▸ h
  have hK₂ : CFSG.Open.IsComponentOf K₂
      (fixSubgroup (LinearFlag.conjAut (n + 1) k A)) := by
    have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map eModel hJ₂
    rw [hAeq]
    exact hfix ▸ h
  have hK₃ : CFSG.Open.IsComponentOf K₃
      (fixSubgroup (LinearFlag.conjAut (n + 1) k A)) := by
    have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map eModel hJ₃
    rw [hAeq]
    exact hfix ▸ h
  have hK12 : K₁ ≠ K₂ := by
    intro h
    exact h12 (Subgroup.map_injective (f := eModel.toMonoidHom) eModel.injective h)
  have hK13 : K₁ ≠ K₃ := by
    intro h
    exact h13 (Subgroup.map_injective (f := eModel.toMonoidHom) eModel.injective h)
  have hK23 : K₂ ≠ K₃ := by
    intro h
    exact h23 (Subgroup.map_injective (f := eModel.toMonoidHom) eModel.injective h)
  have hcat : ∀ J : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hv⟩).Group,
      catalogIs (↥J ⧸ Subgroup.center ↥J) (S10.isL2n r) →
      catalogIs (↥(J.map eModel.toMonoidHom) ⧸
        Subgroup.center ↥(J.map eModel.toMonoidHom)) (S10.isL2n r) := by
    intro J hJ
    have eJ : ↥J ≃* ↥(J.map eModel.toMonoidHom) :=
      J.equivMapOfInjective eModel.toMonoidHom eModel.injective
    have eZ : (↥J ⧸ Subgroup.center ↥J) ≃*
        (↥(J.map eModel.toMonoidHom) ⧸
          Subgroup.center ↥(J.map eModel.toMonoidHom)) :=
      QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
    exact (catalogIs_congr eZ).1 hJ
  refine ⟨k, inferInstance, Fintype.ofFinite k, eModel, A, c, K₁, K₂, K₃,
    hcardk, hchark, hc, hK₁, hK₂, hK₃, hK12, hK13, hK23, ?_, ?_, ?_⟩
  · exact hcat J₁ hL1
  · exact hcat J₂ hL2
  · exact hcat J₃ hL3

end CFSG.LocalAnalysis.GLTheoremA.T1428
