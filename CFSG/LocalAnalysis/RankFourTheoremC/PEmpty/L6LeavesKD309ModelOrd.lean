module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBGen

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB Matrix Subgroup

variable {p : ℕ} {K : Type} [Field K] {P' : Type} [Group P'] (M : MatModel p K P')

@[expose] def scalarsIn : Subgroup Kˣ :=
  M.𝔾.comap (GeneralLinearGroup.scalar (Fin p) : Kˣ →* GL (Fin p) K)

theorem c_scalar {z : Kˣ} (hz : GeneralLinearGroup.scalar (Fin p) z ∈ M.𝔾) :
    M.c ⟨GeneralLinearGroup.scalar (Fin p) z, hz⟩ = 1 := by
  refine MulEquiv.ext fun y => ?_
  rw [MulAut.one_apply]
  obtain ⟨A, rfl⟩ := M.ι_surj y
  rw [M.c_ι]
  have h : (GeneralLinearGroup.scalar (Fin p) z : GL (Fin p) K) * A *
      (GeneralLinearGroup.scalar (Fin p) z)⁻¹ = (A : GL (Fin p) K) := by
    have := (scalar_comm z (A : GL (Fin p) K))
    calc (GeneralLinearGroup.scalar (Fin p) z : GL (Fin p) K) * A *
          (GeneralLinearGroup.scalar (Fin p) z)⁻¹
        = (A : GL (Fin p) K) * GeneralLinearGroup.scalar (Fin p) z *
            (GeneralLinearGroup.scalar (Fin p) z)⁻¹ := by rw [this]
      _ = A := by group
  have h2 : (⟨(GeneralLinearGroup.scalar (Fin p) z : GL (Fin p) K) * A *
      (GeneralLinearGroup.scalar (Fin p) z)⁻¹, M.norm_mem _ hz A A.2⟩ : ↥M.H) = A :=
    Subtype.ext h
  have h3 : M.ι ⟨(GeneralLinearGroup.scalar (Fin p) z : GL (Fin p) K) * A *
      (GeneralLinearGroup.scalar (Fin p) z)⁻¹, M.norm_mem _ hz A A.2⟩ = M.ι A :=
    congrArg M.ι h2
  exact h3

theorem card_ker_c (hp : p ≠ 0) : Nat.card M.c.ker = Nat.card (scalarsIn M) := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun z : scalarsIn M => (⟨⟨GeneralLinearGroup.scalar (Fin p) (z : Kˣ), z.2⟩,
      c_scalar M z.2⟩ : M.c.ker)) ⟨?_, ?_⟩)
  · intro a b hab
    have h1 : GeneralLinearGroup.scalar (Fin p) (a : Kˣ) =
        GeneralLinearGroup.scalar (Fin p) (b : Kˣ) :=
      congrArg (fun g : M.c.ker => ((g : ↥M.𝔾) : GL (Fin p) K)) hab
    have h2 : (a : Kˣ) * (b : Kˣ)⁻¹ = 1 := by
      refine scalar_eq_one hp ?_
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  · rintro ⟨g, hg⟩
    obtain ⟨z, hz⟩ := M.c_eq_one g hg
    refine ⟨⟨z, ?_⟩, ?_⟩
    · show GeneralLinearGroup.scalar (Fin p) z ∈ M.𝔾
      rw [← hz]
      exact g.2
    · refine Subtype.ext (Subtype.ext ?_)
      exact hz.symm


section Orders

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal] [Group.IsPerfect ↥L]
  {eP : (↥L ⧸ center ↥L) ≃* P'} [Finite K]

theorem factorization_card_eq (hp : p.Prime) (hAut : AutHyps (thetaP L eP) M) :
    (Nat.card Y).factorization p + (Nat.card M.c.ker).factorization p =
      (Nat.card (centralizer (L : Set Y))).factorization p +
        (Nat.card M.𝔾).factorization p := by
  set θ := thetaP L eP with hθ
  have hker : θ.ker = centralizer (L : Set Y) := by
    ext y
    rw [MonoidHom.mem_ker, hθ, thetaP_eq_one_iff]
  have h1 := Subgroup.card_ker_mul_card_range θ
  have h2 := Subgroup.relIndex_mul_card M.c.range θ.range
  rw [inf_eq_left.mpr hAut.D_le] at h2
  have h3 : ¬ p ∣ M.c.range.relIndex θ.range := by
    have := hAut.D_idx
    rwa [Subgroup.index_comap] at this
  have h4 := Subgroup.card_ker_mul_card_range M.c
  haveI : Finite θ.range := Finite.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  haveI : Finite (GL (Fin p) K) := inferInstance
  haveI : Finite M.𝔾 := inferInstance
  haveI : Finite M.c.range := Finite.of_surjective M.c.rangeRestrict M.c.rangeRestrict_surjective
  have hY0 : Nat.card θ.ker ≠ 0 := Nat.card_pos.ne'
  have hR0 : Nat.card θ.range ≠ 0 := Nat.card_pos.ne'
  have hI0 : M.c.range.relIndex θ.range ≠ 0 := left_ne_zero_of_mul (h2 ▸ hR0)
  have hD0 : Nat.card M.c.range ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card M.c.ker ≠ 0 := Nat.card_pos.ne'
  have hZ : (M.c.range.relIndex θ.range).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd h3
  have e1 : (Nat.card Y).factorization p =
      (Nat.card θ.ker).factorization p + (Nat.card θ.range).factorization p := by
    rw [← h1, Nat.factorization_mul hY0 hR0]
    rfl
  have e2 : (Nat.card θ.range).factorization p = (Nat.card M.c.range).factorization p := by
    rw [← h2, Nat.factorization_mul hI0 hD0]
    simp [hZ]
  have e3 : (Nat.card M.𝔾).factorization p =
      (Nat.card M.c.ker).factorization p + (Nat.card M.c.range).factorization p := by
    rw [← h4, Nat.factorization_mul hK0 hD0]
    rfl
  rw [hker] at e1
  omega

theorem card_sylow_eq (hp : p.Prime) (hAut : AutHyps (thetaP L eP) M)
    (hCp : IsPGroup p (centralizer (L : Set Y))) (S : Sylow p Y) {a : ℕ}
    (hGL : (Nat.card M.𝔾).factorization p = p * a + 1)
    (hker : (Nat.card M.c.ker).factorization p = a) :
    Nat.card (S : Subgroup Y) = Nat.card (centralizer (L : Set Y)) * p ^ ((p - 1) * a + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := factorization_card_eq M hp hAut (L := L) (eP := eP)
  obtain ⟨k, hk⟩ := hCp.exists_card_eq
  have hk' : (Nat.card (centralizer (L : Set Y))).factorization p = k := by
    rw [hk, Nat.Prime.factorization_pow hp]
    simp
  rw [hk', hGL, hker] at h
  rw [Sylow.card_eq_multiplicity, hk]
  rw [← pow_add]
  congr 1
  have hp1 : 1 ≤ p := hp.one_lt.le
  have : (p - 1) * a + a = p * a := by
    zify [hp1]
    ring
  omega

end Orders

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M
