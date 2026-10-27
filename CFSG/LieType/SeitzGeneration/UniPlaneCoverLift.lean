module

public import CFSG.LieType.SeitzGeneration.QuasiHigh
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311c

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
open CFSG.LieType.Seitz
open CFSG.LieType.SeitzGeneration.QuasiHigh

@[expose] def coverImage {K C : Type*} [Group K] [Group C]
    (e : K ⧸ Subgroup.center K ≃* C) (E : Subgroup (MulAut K)) : Subgroup (MulAut C) :=
  E.map ((MulAut.congr e).toMonoidHom.comp (quotientCenterAut' K))

theorem isElemAbelian_coverImage {K C : Type*} [Group K] [Group C]
    (e : K ⧸ Subgroup.center K ≃* C) {p : ℕ} {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) : IsElemAbelian p (coverImage e E) :=
  CFSG.SectionRank.isElemAbelian_map hE _

theorem card_coverImage {K C : Type*} [Group K] [Group C] (hperf : commutator K = ⊤)
    (e : K ⧸ Subgroup.center K ≃* C) (E : Subgroup (MulAut K)) :
    Nat.card (coverImage e E) = Nat.card E := by
  rw [coverImage]
  exact Subgroup.card_map_of_injective
    ((MulAut.congr e).injective.comp (quotientCenterAut'_injective hperf))

theorem coverImage_le_range_conj {K C : Type*} [Group K] [Group C]
    (e : K ⧸ Subgroup.center K ≃* C) {E : Subgroup (MulAut K)}
    (hin : E ≤ (MulAut.conj : K →* MulAut K).range) :
    coverImage e E ≤ (MulAut.conj : C →* MulAut C).range := by
  intro x hx
  rw [coverImage] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  rw [← CFSG.LieType.SeitzGeneration.map_range_conj_congr e]
  refine Subgroup.mem_map_of_mem _ ?_
  exact QuasiHigh.map_quotientCenterAut'_le_range_conj hin (Subgroup.mem_map_of_mem _ hy)

theorem seitzHyperGamma_eq_top_of_uniPlaneGen {K C : Type*} [Group K] [Group C] [Finite K]
    (hperf : commutator K = ⊤) (e : K ⧸ Subgroup.center K ≃* C) {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hrp : r ≠ p) {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2)
    (h : CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.UniPlaneGen r (coverImage e E)) :
    CFSG.LieType.Seitz.seitzHyperGamma p E = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  refine QuasiHigh.seitzHyperGamma_eq_top_of_quot hperf
    (CFSG.Open.IsElemAbelian.isPGroup hE) ?_
  have hG : Subgroup.closure {c : C | ∃ φ ∈ coverImage e E, φ ≠ 1 ∧ φ c = c ∧
      ∃ n : ℕ, c ^ (r ^ n) = 1} = ⊤ := by
    simpa [CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.UniPlaneGen,
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.uniPlaneClosure] using h
  have htop : (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤
      Subgroup.closure (e.symm.toMonoidHom ''
        {c : C | ∃ φ ∈ coverImage e E, φ ≠ 1 ∧ φ c = c ∧ ∃ n : ℕ, c ^ (r ^ n) = 1}) := by
    rw [← MonoidHom.map_closure (f := e.symm.toMonoidHom), hG,
      Subgroup.map_top_of_surjective _ e.symm.surjective]
  refine htop.trans (Subgroup.closure_mono ?_)
  rintro s ⟨c, hc, rfl⟩
  obtain ⟨φ, hφ, hφ1, hφc, n, hn⟩ := hc
  unfold coverImage at hφ
  obtain ⟨f, hfE, rfl⟩ := Subgroup.mem_map.1 hφ
  simp only [MonoidHom.comp_apply] at hφ1 hφc
  have hf1 : f ≠ 1 := by
    rintro rfl
    exact hφ1 (by rw [map_one, map_one])
  have hfix : quotientCenterAut' K f (e.symm c) = e.symm c := by
    have h1 : e (quotientCenterAut' K f (e.symm c)) = c := by
      simpa [MulAut.congr_apply] using hφc
    exact e.injective (by simpa using h1)
  have hpow : (e.symm c) ^ (r ^ n) = 1 := by
    simpa using congrArg e.symm hn
  refine ⟨Or.inr ⟨r ^ n, ?_, hpow⟩, Subgroup.zpowers f, Subgroup.zpowers_le.2 hfE,
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.relIndex_zpowers hp hE hcard hfE hf1,
    ?_⟩
  · intro hd
    exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow hd)).symm
  · intro g hg
    have hmap : Subgroup.map (quotientCenterAut' K) (Subgroup.zpowers f) =
        Subgroup.zpowers (quotientCenterAut' K f) := MonoidHom.map_zpowers _ _
    have hg' : quotientCenterAut' K g ∈ Subgroup.zpowers (quotientCenterAut' K f) := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hg
    have hfixall : quotientCenterAut' K g (e.symm c) = e.symm c :=
      (mem_fixedPoints.1
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.mem_fixedPoints_zpowers hfix))
        (quotientCenterAut' K g) hg'
    simpa [QuasiHigh.quotAut_eq_quotientCenterAut'] using hfixall

end CFSG.LieType.SeitzGeneration
