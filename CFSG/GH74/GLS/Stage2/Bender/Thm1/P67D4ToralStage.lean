module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutG2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem d4Out_of_toral (hA2 : D4OuterThreeA2Toral) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hh : (h : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hφ : φ = MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ ∨
      φ⁻¹ = MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ) (hφ3 : φ ^ 3 = 1) :
    D4Out φ := by
  classical
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 : (MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rcases hφ with h1 | h1
    · rw [← h1]
      exact hφ3
    · rw [← h1, inv_pow, hφ3, inv_one]
  have hN := normSeq_eq_one_of_pow_eq_one hZ (d4_fieldActor_pow_three K hK σ hσ) hψ3
  obtain ⟨y, s, hs, hs3, hconj, d, hd, hd3, hsd⟩ := d4_toral_conj hp hp2 hf K hK σ hσ h hh hN
  have hD : D4Out (MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ) := by
    by_cases hd1 : d = 1
    · have hs1 : s = 1 := by
        apply Subtype.ext
        have h1 : (![1, 1, 1, 1] : Fin TwistTag.D4.tag.rank → Kˣ) =
            (1 : Fin TwistTag.D4.tag.rank → Kˣ) := funext fun i => by fin_cases i <;> rfl
        rw [hsd, hd1, h1, rootDiagUnit_one]
        rfl
      rw [hs1, map_one, one_mul] at hconj
      exact (d4OuterThreeG2_thm p f hp hp2 hp3 hf K hK σ hσ).of_conj_eq _ hconj
    · exact (hA2 p f hp hp2 hp3 hf hq K hK σ hσ d hd hd3 hd1 s hsd).of_conj_eq _ hconj
  rcases hφ with h1 | h1
  · rw [h1]
    exact hD
  · have h2 := hD.inv
    rw [← h1, inv_inv] at h2
    exact h2

end CFSG.GH74.GLS.Stage2.Bender.Thm1
