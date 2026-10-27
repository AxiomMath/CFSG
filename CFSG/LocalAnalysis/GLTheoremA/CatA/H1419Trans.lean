module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419Facts
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.K1419 (PQ)

variable {Q : Type} [Group Q] [Finite Q]

theorem map_glaPPrimeCore_eq (β : MulAut Q) :
    (GLAPPrimeCore 3 Q).map β.toMonoidHom = GLAPPrimeCore 3 Q := by
  have hp : Nat.Prime 3 := Nat.prime_three
  apply le_antisymm (map_glaPPrimeCore_le_of_surjective hp β.toMonoidHom β.surjective)
  intro x hx
  have h1 : (GLAPPrimeCore 3 Q).map β.symm.toMonoidHom ≤ GLAPPrimeCore 3 Q :=
    map_glaPPrimeCore_le_of_surjective hp β.symm.toMonoidHom β.symm.surjective
  have hy : β.symm x ∈ GLAPPrimeCore 3 Q := h1 (Subgroup.mem_map_of_mem _ hx)
  exact ⟨β.symm x, hy, by simp⟩

noncomputable def betaBar (β : MulAut Q) : MulAut (Q ⧸ GLAPPrimeCore 3 Q) :=
  QuotientGroup.congr (GLAPPrimeCore 3 Q) (GLAPPrimeCore 3 Q) β (map_glaPPrimeCore_eq β)

theorem betaBar_mk (β : MulAut Q) (x : Q) :
    betaBar β (QuotientGroup.mk x) = QuotientGroup.mk (β x) :=
  QuotientGroup.congr_mk _ _ _ _ _

theorem betaBar_pow_apply (β : MulAut Q) (n : ℕ) (x : Q) :
    (betaBar β ^ n) (QuotientGroup.mk x) = QuotientGroup.mk ((β ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, betaBar_mk, pow_succ', MulAut.mul_apply]

theorem betaBar_pow_three (β : MulAut Q) (hβ : β ^ 3 = 1) : betaBar β ^ 3 = 1 := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [betaBar_pow_apply, hβ]
  simp

theorem map_fixSubgroup_eq (β : MulAut Q) (hβ : β ^ 3 = 1) :
    (fixSubgroup β).map (QuotientGroup.mk' (GLAPPrimeCore 3 Q)) = fixSubgroup (betaBar β) := by
  classical
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 Q)) := CFSG.pPrimeCore_coprime_card
  have hndvd : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 Q) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  have hβ3 : ∀ x : Q, β (β (β x)) = x := by
    intro x
    have h := DFunLike.congr_fun hβ x
    simpa [pow_succ, MulAut.mul_apply] using h
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : β k = k := mem_fixSubgroup.1 (SetLike.mem_coe.1 hk)
    rw [mem_fixSubgroup, QuotientGroup.mk'_apply, betaBar_mk, hk']
  · intro hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    rw [mem_fixSubgroup, betaBar_mk] at hy
    have hu : k⁻¹ * β k ∈ GLAPPrimeCore 3 Q := QuotientGroup.eq.1 hy.symm
    let σ : GLAPPrimeCore 3 Q → GLAPPrimeCore 3 Q := fun o =>
      ⟨k⁻¹ * β k * β o, (GLAPPrimeCore 3 Q).mul_mem hu (by
        have h1 : β (o : Q) ∈ (GLAPPrimeCore 3 Q).map β.toMonoidHom := Subgroup.mem_map_of_mem _ o.2
        rw [map_glaPPrimeCore_eq] at h1
        exact h1)⟩
    have hrel : ∀ o : GLAPPrimeCore 3 Q, β (k * o) = k * (σ o : Q) := by
      intro o
      simp only [σ, map_mul]
      group
    have hσ3 : ∀ o : GLAPPrimeCore 3 Q, σ (σ (σ o)) = o := by
      intro o
      apply Subtype.ext
      apply mul_left_cancel (a := k)
      rw [← hrel, ← hrel, ← hrel, hβ3]
    let τ : Equiv.Perm (GLAPPrimeCore 3 Q) :=
      { toFun := σ
        invFun := fun o => σ (σ o)
        left_inv := fun o => hσ3 o
        right_inv := fun o => hσ3 o }
    have hτ : τ ^ 3 ^ 1 = 1 := by
      ext o
      simp only [pow_one, Equiv.Perm.coe_pow, Function.iterate_succ, Function.iterate_zero,
        Function.comp_apply, id_eq, Equiv.Perm.one_apply]
      exact congrArg Subtype.val (hσ3 o)
    haveI : Fintype (GLAPPrimeCore 3 Q) := Fintype.ofFinite _
    have hndvd' : ¬ 3 ∣ Fintype.card (GLAPPrimeCore 3 Q) := by
      rwa [Nat.card_eq_fintype_card] at hndvd
    obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hndvd' hτ
    refine ⟨k * (a : Q), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_fixSubgroup, hrel a]
      have : σ a = a := ha
      rw [this]
    · rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq.2 (by simpa using a.2)).symm

noncomputable def centerBar {K : Type} [Group K] (σ : MulAut K) : MulAut (K ⧸ Subgroup.center K) :=
  QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) σ (Subgroup.map_center_eq σ)

theorem centerBar_mk {K : Type} [Group K] (σ : MulAut K) (x : K) :
    centerBar σ (QuotientGroup.mk x) = QuotientGroup.mk (σ x) :=
  QuotientGroup.congr_mk _ _ _ _ _

theorem centerBar_pow_apply {K : Type} [Group K] (σ : MulAut K) (n : ℕ) (x : K) :
    (centerBar σ ^ n) (QuotientGroup.mk x) = QuotientGroup.mk ((σ ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, centerBar_mk, pow_succ', MulAut.mul_apply]

theorem centerBar_pow_three {K : Type} [Group K] (σ : MulAut K) (hσ : σ ^ 3 = 1) :
    centerBar σ ^ 3 = 1 := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [centerBar_pow_apply, hσ]
  simp

theorem transfer_pSimple {J : Subgroup Q} (β : MulAut Q) (hβ : β ^ 3 = 1)
    (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    ∃ (β' : MulAut (PQ Q ⧸ Subgroup.center (PQ Q))) (J' : Subgroup (PQ Q ⧸ Subgroup.center (PQ Q))),
      β' ^ 3 = 1 ∧ GLAPComponent 3 (fixSubgroup β') J' ∧ Nonempty (PSimple 3 J ≃* PSimple 3 J') := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 Q)) := CFSG.pPrimeCore_coprime_card
  have hker : Nat.Coprime 3
      (Nat.card ↥(fixSubgroup β ⊓ (QuotientGroup.mk' (GLAPPrimeCore 3 Q) : Q →* PQ Q).ker)) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hcop
  have hJ1 := glaPComponent_map hp (QuotientGroup.mk' (GLAPPrimeCore 3 Q) : Q →* PQ Q) hker hJ
  rw [map_fixSubgroup_eq β hβ] at hJ1
  have hker2 : (QuotientGroup.mk' (Subgroup.center (PQ Q)) : PQ Q →* PQ Q ⧸ Subgroup.center (PQ Q)).ker
      ≤ Subgroup.center (PQ Q) := (QuotientGroup.ker_mk' _).le
  have hαβ : ∀ y : PQ Q, (QuotientGroup.mk' (Subgroup.center (PQ Q)) : PQ Q →* PQ Q ⧸ Subgroup.center (PQ Q))
      (betaBar β y) = centerBar (betaBar β) ((QuotientGroup.mk' (Subgroup.center (PQ Q)) : PQ Q →* PQ Q ⧸
        Subgroup.center (PQ Q)) y) := fun y => rfl
  have hJ2 := glaPComponent_map_fixSubgroup (QuotientGroup.mk' (Subgroup.center (PQ Q)) : PQ Q →* PQ Q ⧸
    Subgroup.center (PQ Q)) hker2 (betaBar β) (centerBar (betaBar β)) hαβ
    (QuotientGroup.mk'_surjective _) hp hJ1
  have hJπ : GLAPComponent 3 (fixSubgroup (centerBar (betaBar β)))
      (J.map ((QuotientGroup.mk' (Subgroup.center (PQ Q)) : PQ Q →* PQ Q ⧸ Subgroup.center (PQ Q)).comp
        (QuotientGroup.mk' (GLAPPrimeCore 3 Q) : Q →* PQ Q))) := by
    rw [← Subgroup.map_map]
    exact hJ2
  exact ⟨centerBar (betaBar β), _, centerBar_pow_three _ (betaBar_pow_three β hβ), hJπ,
    nonempty_pSimple_equiv_map hp _ hJ hJπ⟩

end CFSG.LocalAnalysis.GLTheoremA.H1419
