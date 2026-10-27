module

public import CFSG.HardMathSupport.Foote.Coordinator.CoverThree.Defs
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.LieType.SeitzGeneration.OutdiagScope
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThree

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts CFSG.Open

theorem conj_injective_of_center_eq_bot {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : g ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun φ : MulAut M => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  rw [hZ] at hg'
  exact hg'

theorem card_le_nine_of_conj {M : Type*} [Group M] [Finite M] (hZ : Subgroup.center M = ⊥)
    (N : Subgroup (MulAut M)) (hN : ∀ g : M, (MulAut.conj g : MulAut M) ∈ N)
    (hb : ∀ B ≤ N, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x ^ 3 = 1) → Nat.card B ≤ 9)
    {A : Subgroup M} (hA : IsElemAbelian 3 A) : Nat.card A ≤ 9 := by
  have hinj : Function.Injective (MulAut.conj : M →* MulAut M) :=
    conj_injective_of_center_eq_bot hZ
  set B : Subgroup (MulAut M) := A.map (MulAut.conj : M →* MulAut M) with hB
  have hBN : B ≤ N := by
    rintro _ ⟨g, -, rfl⟩
    exact hN g
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb'⟩)
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]
  have hle := hb B hBN hBab hB3
  rwa [hB, Subgroup.card_map_of_injective hinj] at hle

theorem card_le_nine_projectiveSL {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {G : Type} [Group G] (ψ : G ≃* projectiveSL 3 K) {A : Subgroup G} (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 9 := by
  have := Finite.of_equiv _ ψ.symm.toEquiv
  have hA' : IsElemAbelian 3 (A.map ψ.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hA _
  have := card_le_nine_of_conj (M := projectiveSL 3 K)
    (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num))
    (linearAutGroup 3 K) (fun g => CFSG.LieType.SeitzGeneration.conj_mem_linearAutGroup g)
    (fun B hB hab h3' =>
      CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof.card_le_nine_of_le_linearAutGroup h3 B hB hab h3')
    hA'
  rwa [Subgroup.card_map_of_injective ψ.injective] at this

theorem card_le_nine_unitaryPSU {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) (h3 : 3 ∣ Nat.card K - 1) {G : Type} [Group G]
    (ψ : G ≃* unitaryPSU h 3) {A : Subgroup G} (hA : IsElemAbelian 3 A) : Nat.card A ≤ 9 := by
  have := h.finite
  have := Finite.of_equiv _ ψ.symm.toEquiv
  have hA' : IsElemAbelian 3 (A.map ψ.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hA _
  have := card_le_nine_of_conj (M := unitaryPSU h 3) (center_unitaryPSU_three_eq_bot h hq)
    (psuConj h).range
    (fun g => CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.mem_psuConj_range_of_isInnerAut ⟨g, rfl⟩)
    (fun B hB hab h3' =>
      CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.card_le_nine_of_le_psuConj_range h3 B hB hab h3')
    hA'
  rwa [Subgroup.card_map_of_injective ψ.injective] at this

open CFSG.HardMathSupport.Foote.Coordinator in
theorem coverThree_rank_le_two (d : TauCeti.ValidLieTypeIndex) (hd : CoverThreeIndex d)
    (hchar : 3 ≠ d.1.characteristic) :
    ∀ A : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian 3 A → Nat.card A ≤ 9 := by
  obtain ⟨d, hv⟩ := d
  rcases hd with ⟨q, rfl, h3⟩ | ⟨q, rfl, h3⟩
  · intro A hA
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    let e : CFSG.LieType.SeitzGeneration.Cat ⟨.A 2 q, hv⟩ ≃*
        projectiveSL 3 (GaloisField q.p q.exponent) :=
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _)
    have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
    exact card_le_nine_projectiveSL (by rw [hcardF]; exact h3) e hA
  · intro A hA
    obtain ⟨⟨hℓ, hf, -, hne⟩, F, _, _, hFc, ⟨e⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
        (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩))
    have hU : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hf, by rw [hFc, ← pow_mul, mul_comm]⟩
    have hq2 : 2 < q.p ^ q.exponent := by
      have h1 : 2 ≤ q.p ^ q.exponent :=
        (hℓ.two_le).trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.1 q.exponent_pos) _)
      refine lt_of_le_of_ne h1 fun h2 => hne ?_
      rw [← h2]
    have hp3 : q.p ≠ 3 := fun h => hchar (by simpa using h.symm)
    have h3Q : ¬ 3 ∣ q.p ^ q.exponent := fun hd =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
        (Nat.prime_three.dvd_of_dvd_pow hd)).symm
    have hK3 : 3 ∣ Nat.card F - 1 := by
      rw [hFc]
      have h1 : (q.p ^ q.exponent) % 3 = 1 ∨ (q.p ^ q.exponent) % 3 = 2 := by omega
      have h2 : ((q.p ^ q.exponent) ^ 2) % 3 = 1 := by
        rw [pow_two, Nat.mul_mod]
        rcases h1 with h1 | h1 <;> rw [h1]
      omega
    exact card_le_nine_unitaryPSU hU hq2 hK3 (e.trans (unitaryPSUEquiv hU (by norm_num)).symm) hA

end CFSG.HardMathSupport.Malle.Coordinator.CoverThree
