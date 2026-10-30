module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearUnitaryComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympFieldComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

private theorem congr_conj_apply {S G : Type} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem congr_self_eq {P : Type} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

private theorem pow_eq_one_of_conj_pow {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {p : ℕ} {a : S} (h : MulAut.conj a ^ p = 1) : a ^ p = 1 := by
  have hc : a ^ p ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut S => φ g)
      (show MulAut.conj (a ^ p) = 1 by rw [map_pow]; exact h)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * a ^ p = a ^ p * g * (a ^ p)⁻¹ * a ^ p := by rw [h1]
      _ = a ^ p * g := by group
  rw [b3Lie_center_eq_bot hna, Subgroup.mem_bot] at hc
  exact hc

section Symplectic

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

private theorem lieCompsCase_symplectic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (idx : TauCeti.ValidLieTypeIndex)
    (hsp : (∃ r q, idx.1 = .B r q ∧ (q.p = 2 ∨ r = 2)) ∨ ∃ r q, idx.1 = .C r q)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) (β : MulAut S) (hβ : β ^ p = 1)
    (hout : lieIndexChar idx.1 ≠ p ∨ ∀ a : S, MulAut.conj a ≠ β) :
    LieCompsExport (lieIndexChar idx.1) β := by
  haveI := hs
  obtain ⟨e⟩ := he
  obtain ⟨r, f, ⟨hℓ, hf, hr, hne⟩, K, _, _, hK, ⟨e'⟩⟩ :=
    exists_statedClassicalModel_psp idx hsp e
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) hℓ hf hr hK
  have hodd : Odd (orderOf (MulAut.congr e' β)) :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : MulAut.congr e' β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : MulAut.congr e' β ∈ spLinearAutGroup r K
  ·
    have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      hp hp2 hD hβ'
    have hβs : β = MulAut.conj (e'.symm t) := by
      apply (MulAut.congr e').injective
      rw [← ht, congr_conj_apply, MulEquiv.apply_symm_apply]
    by_cases hℓp : lieIndexChar idx.1 = p
    ·
      exact absurd hβs.symm ((hout.resolve_left fun h => h hℓp) (e'.symm t))
    · have hs3 : (e'.symm t) ^ p = 1 :=
        pow_eq_one_of_conj_pow hna (by rw [← hβs]; exact hβ)
      have ht3 : t ^ p = 1 := by
        have := congrArg e' hs3
        rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
      obtain ⟨x, hx, hxp⟩ := LieSemisimple.exists_proj_eq_pow_eq_one_sp (by omega) hp hp2 ht3
      have h1 := lieCompsExport_conj_sp slFactorFacts_holds suFactorFacts_holds
        spFactorFacts_holds spFourTwoFacts_holds hp hp2 hℓ hf hK (by omega) (Ne.symm hℓp) x hxp
      rw [hx, ht] at h1
      exact LieCompsExport.of_congr e' h1
  ·
    have hne1 : MulAut.congr e' β ≠ 1 := fun h1 => hD (h1 ▸ one_mem _)
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' hne1
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent p hp _ hE hD hord
    have h1 := lieCompsExport_fieldAut_sp spFactorFacts_holds spFourTwoFacts_holds hp hp2 hr σ hσ
    rw [ringChar_eq_of_card hℓ hK] at h1
    refine LieCompsExport.of_congr e' ?_
    refine LieCompsExport.of_congr (h⁻¹ : MulAut _) ?_
    rw [congr_self_eq, hβeq]
    have : h⁻¹ * (h * SymplecticHigher.fieldAut r K σ * h⁻¹) * h⁻¹⁻¹ =
        SymplecticHigher.fieldAut r K σ := by group
    rw [this]
    exact h1

end Symplectic

section Orthogonal

open CFSG.Assembly.LowTwoRank

private theorem exists_statedClassicalModel_orth {S : Type} [Group S]
    (idx : TauCeti.ValidLieTypeIndex)
    (hor : (∃ r q, idx.1 = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r) ∨ (∃ r q, idx.1 = .D r q) ∨
      ∃ r q, idx.1 = .twistedD r q)
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t n (lieIndexChar idx.1) f := by
  obtain ⟨d, hv⟩ := idx
  rcases hor with ⟨r, q, hd, hq2, hr3⟩ | ⟨r, q, hd⟩ | ⟨r, q, hd⟩
  · dsimp only at hd
    subst hd
    exact ⟨.POmegaOdd, r, q.exponent, Or.inl rfl,
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hq2 hr3 e⟩
  · dsimp only at hd
    subst hd
    exact ⟨.POmegaPlus, r, q.exponent, Or.inr (Or.inl rfl),
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e⟩
  · dsimp only at hd
    subst hd
    exact ⟨.POmegaMinus, r, q.exponent, Or.inr (Or.inr rfl),
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e⟩

private theorem lieCompsCase_orthogonal {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (idx : TauCeti.ValidLieTypeIndex)
    (hor : (∃ r q, idx.1 = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r) ∨ (∃ r q, idx.1 = .D r q) ∨
      ∃ r q, idx.1 = .twistedD r q)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) (β : MulAut S) (hβ : β ^ p = 1)
    (hout : lieIndexChar idx.1 ≠ p ∨ ∀ a : S, MulAut.conj a ≠ β) :
    LieCompsExport (lieIndexChar idx.1) β := by
  haveI := hs
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e⟩ := he
  obtain ⟨t, n, f, ht, hG⟩ := exists_statedClassicalModel_orth idx hor e
  by_cases hin : ∃ a : S, MulAut.conj a = β
  ·
    obtain ⟨a, rfl⟩ := hin
    have hℓp : lieIndexChar idx.1 ≠ p := hout.resolve_right fun h => h a rfl
    exact lieCompsExport_conj_omega slFactorFacts_holds suFactorFacts_holds omegaFactorFacts_holds
      hp hp2 ht hG (Ne.symm hℓp) a (pow_eq_one_of_conj_pow hna hβ)
  ·
    have hout' : ∀ a : S, MulAut.conj a ≠ β := fun a h => hin ⟨a, h⟩
    exact lieCompsExport_omega_outer omegaFactorFacts_holds hp hp2 ht hG (fun _ _ => by omega) β hβ
      hout'

end Orthogonal

theorem lieCompsOn_symplecticOrthogonal {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    LieCompsOn p .symplecticOrthogonal := by
  intro S _ _ hs hna idx hF he β hβ _ hout
  obtain ⟨d, hv⟩ := idx
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | B r q =>
    by_cases hsp : q.p = 2 ∨ r = 2
    · exact lieCompsCase_symplectic hp (by omega) hs hna ⟨_, hv⟩ (Or.inl ⟨r, q, rfl, hsp⟩) he β hβ
        hout
    · push Not at hsp
      exact lieCompsCase_orthogonal hp hp5 hs hna ⟨_, hv⟩
        (Or.inl ⟨r, q, rfl, hsp.1, by simp only at hr; omega⟩) he β hβ hout
  | C r q =>
    exact lieCompsCase_symplectic hp (by omega) hs hna ⟨_, hv⟩ (Or.inr ⟨r, q, rfl⟩) he β hβ hout
  | D r q =>
    exact lieCompsCase_orthogonal hp hp5 hs hna ⟨_, hv⟩ (Or.inr (Or.inl ⟨r, q, rfl⟩)) he β hβ hout
  | twistedD r q =>
    exact lieCompsCase_orthogonal hp hp5 hs hna ⟨_, hv⟩ (Or.inr (Or.inr ⟨r, q, rfl⟩)) he β hβ hout
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
