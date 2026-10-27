module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympFieldExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrderSix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnipotentThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

private theorem exists_statedClassicalModel_psp {S : Type} [Group S]
    (idx : TauCeti.ValidLieTypeIndex)
    (hsp : (∃ r q, idx.1 = .B r q ∧ (q.p = 2 ∨ r = 2)) ∨ ∃ r q, idx.1 = .C r q)
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    ∃ r f : ℕ, StatedClassicalModel S .PSp r (lieIndexChar idx.1) f := by
  obtain ⟨d, hv⟩ := idx
  rcases hsp with ⟨r, q, hd, hq⟩ | ⟨r, q, hd⟩
  · dsimp only at hd
    subst hd
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact ⟨2, q.exponent, CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e⟩
    · have hq2 : q.p = 2 := hq.resolve_right (by omega)
      exact ⟨r, q.exponent,
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 hr3 e⟩
  · dsimp only at hd
    subst hd
    exact ⟨r, q.exponent, CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e⟩

private theorem ringChar_eq_of_card {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ ^ f) : ringChar K = ℓ := by
  haveI := Fintype.ofFinite K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  exact ringChar.eq K ℓ

private theorem congr_conj_apply {S G : Type} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem congr_self_eq {P : Type} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

theorem lieCompCase_symplectic
    (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3)
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (idx : TauCeti.ValidLieTypeIndex)
    (hsp : (∃ r q, idx.1 = .B r q ∧ (q.p = 2 ∨ r = 2)) ∨ ∃ r q, idx.1 = .C r q)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) (β : MulAut S) (hβ : β ^ 3 = 1) :
    LieCompExport (lieIndexChar idx.1) β ∨ NoThreeComponents β := by
  haveI := hs
  by_cases hβ1 : β = 1
  · subst hβ1
    exact Or.inl (lieCompExport_one hna idx he (isEmpty_mulEquiv_alternating_six hb _ he))
  obtain ⟨e⟩ := he
  obtain ⟨r, f, ⟨hℓ, hf, hr, hne⟩, K, _, _, hK, ⟨e'⟩⟩ :=
    exists_statedClassicalModel_psp idx hsp e
  have hne' : ¬(r = 2 ∧ lieIndexChar idx.1 ^ f = 2) := fun h => hne (Prod.ext h.1 h.2)
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) hℓ hf hr hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (orderOf (MulAut.congr e' β)) :=
    (Nat.prime_three.odd_of_ne_two (by norm_num)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : MulAut.congr e' β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : MulAut.congr e' β ∈ spLinearAutGroup r K
  ·
    have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      Nat.prime_three (by norm_num) hD hβ'
    have hβs : β = MulAut.conj (e'.symm t) := by
      apply (MulAut.congr e').injective
      rw [← ht, congr_conj_apply, MulEquiv.apply_symm_apply]
    have hs3 : (e'.symm t) ^ 3 = 1 := by
      have hc : (e'.symm t) ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut S => φ g)
          (show MulAut.conj ((e'.symm t) ^ 3) = 1 by rw [map_pow, ← hβs]; exact hβ)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * (e'.symm t) ^ 3
            = (e'.symm t) ^ 3 * g * ((e'.symm t) ^ 3)⁻¹ * (e'.symm t) ^ 3 := by rw [h1]
          _ = (e'.symm t) ^ 3 * g := by group
      rw [b3Lie_center_eq_bot hna, Subgroup.mem_bot] at hc
      exact hc
    by_cases hℓ3 : lieIndexChar idx.1 = 3
    ·
      right
      have hS : IsChevOfChar 3 S :=
        ⟨idx, YS08.isChevIndexOfChar_of_lieIndexChar_eq hℓ3, ⟨e⟩⟩
      have hs1 : e'.symm t ≠ 1 := by
        intro h1
        apply hβ1
        rw [hβs, h1, map_one]
      rw [hβs]
      exact noThreeComponents_of_conj hQ hs hna hS hs1 hs3
    · left
      have ht3 : t ^ 3 = 1 := by
        have := congrArg e' hs3
        rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
      obtain ⟨x, hx, hx3⟩ := LieSemisimple.exists_proj_eq_pow_eq_one_sp (by omega)
        Nat.prime_three (by norm_num) ht3
      have h1 := lieCompExport_conj_sp slFactorFacts_holds slAltSixFacts_holds
        suFactorFacts_holds suAltSixFacts_holds spFactorFacts_holds spAltSixFacts_holds
        spFourTwoFacts_holds hℓ hf hK hr hne' hℓ3 x hx3
      rw [hx, ht] at h1
      exact LieCompExport.of_congr e' h1
  ·
    left
    have hne1 : MulAut.congr e' β ≠ 1 := fun h1 => hD (h1 ▸ one_mem _)
    have hord : orderOf (MulAut.congr e' β) = 3 := orderOf_eq_prime hβ' hne1
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent 3 Nat.prime_three _ hE hD hord
    have h1 := lieCompExport_fieldAut_sp spFactorFacts_holds spAltSixFacts_holds
      spFourTwoFacts_holds hr σ hσ
    rw [ringChar_eq_of_card hℓ hK] at h1
    refine LieCompExport.of_congr e' ?_
    refine LieCompExport.of_congr (h⁻¹ : MulAut _) ?_
    rw [congr_self_eq, hβeq]
    have : h⁻¹ * (h * SymplecticHigher.fieldAut r K σ * h⁻¹) * h⁻¹⁻¹ =
        SymplecticHigher.fieldAut r K σ := by group
    rw [this]
    exact h1

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
