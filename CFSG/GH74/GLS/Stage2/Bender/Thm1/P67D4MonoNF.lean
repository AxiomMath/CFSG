module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MonoIdx
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OddIdx
public import CFSG.GH74.GLS.Stage2.OddAut.LangR

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut

theorem d4MonoNF :
    ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 1 →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
      ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1 →
        ∃ y n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
          MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
            (MulAut.conj y)⁻¹ = MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ := by
  intro p f hp hp2 _ hf hq K _ _ hK σ hσ g hg
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have hα3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
    have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
    rw [hσ3, map_one] at h
    exact h.symm
  have hα : ∀ y, fieldActor (t := TwistTag.D4) σ σ
      (fieldActor (t := TwistTag.D4) σ σ (fieldActor (t := TwistTag.D4) σ σ y)) = y := fun y => by
    have := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) => φ y) hα3
    simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at this
    exact this
  have hg' : g * fieldActor (t := TwistTag.D4) σ σ g *
      fieldActor (t := TwistTag.D4) σ σ (fieldActor (t := TwistTag.D4) σ σ g) = 1 := by
    have : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = g * fieldActor σ σ g *
        fieldActor σ σ (fieldActor σ σ g) := by
      simp only [normSeq, pow_two, MulAut.mul_apply, MulAut.one_apply, pow_zero, pow_one,
        one_mul]
    rw [← this]
    exact hg
  obtain ⟨y, n, hn, h⟩ := exists_conj_mem_of_index_not_dvd (fieldActor (t := TwistTag.D4) σ σ) hα
    ((graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (d4_monomial_stable K σ) (d4_monomial_index_not_dvd hp hp2 hf K hK σ hσ hq) g hg'
  exact ⟨y, n, Subgroup.mem_subgroupOf.1 hn, h⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
