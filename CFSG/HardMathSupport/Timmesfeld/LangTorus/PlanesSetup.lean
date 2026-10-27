module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
public import CFSG.LieType.SeitzGeneration.ExcTorusTors

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false

@[expose] noncomputable def LangDescent.descentEquiv {τ : Tag} {L : Type} [Field L]
    {D : LangDatum τ L} {p : ℕ} {C : Type} [Group C] {ι : C →* ModGL τ L}
    (h : LangDescent D p ι) (hι : Function.Injective ι) : C ≃* D.Γ :=
  (MonoidHom.ofInjective hι).trans
    ((Subgroup.equivMapOfInjective ι.range (MulAut.conj D.g0⁻¹).toMonoidHom
      (MulAut.conj D.g0⁻¹).injective).trans (MulEquiv.subgroupCongr h.Γ_eq.symm))

theorem exists_langSetup_of_descent_nosylow {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (hF : FrobeniusOnRoots) (D : LangDatum τ L) {p : ℕ} (hp : p.Prime) (hq : 5 ≤ p ∨ 4 ≤ D.q)
    (hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0) (hpq : ¬ p ∣ D.q)
    {C : Type} [Group C] (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hd : LangDescent D p ι) :
    ∃ S : LangSetup τ L p, S.D = D ∧ Nonempty (C ≃* S.Γ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hfm := hd.finite_model
  obtain ⟨ρ, hρ⟩ := hF τ L D
  have hcomm := D.isMulCommutative_torus
  have hcomm' : IsMulCommutative ↥(D.torus ⊓ D.Γ) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (by
      have := hcomm
      exact setLike_mul_comm a.2.1 b.2.1)
  let E : Subgroup (ModGL τ L) := torsionSubgroup (D.torus ⊓ D.Γ) hcomm' p
  exact ⟨⟨D, ρ, hρ, E, hp, hq, hqpow, hpq, hfm, fun x hx => hx.1, fun x hx => hx.2,
    fun x hx hxp => ⟨hx, hxp⟩⟩, rfl, ⟨hd.descentEquiv hι⟩⟩

section Untw

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [IsAlgClosed L] [Algebra K L]
  [IsAlgClosure K L]

theorem exists_langSetup_untw_of_datum (hF : FrobeniusOnRoots) (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (hperf : Group.IsPerfect ↥(adjointGroup τ K))
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K) (w : WeylGroup τ) {g0 : ModGL τ L}
    (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) L w) :
    ∃ S : LangSetup τ L p, S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 ∧
      LangDescent S.D p ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype) := by
  classical
  have hperf' : commutator ↥(adjointGroup τ K) = ⊤ := hperf.commutator_eq_top
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  set D : LangDatum τ L := LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 with hDdef
  have hD : D.Φ = Units.map (entrywiseHom Fr) := rfl
  set ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype with hιdef
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hd := langDescent_untw (K := K) (L := L) d hτ hFr D hD hp hp3 hperf'
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 :=
    ⟨by rw [show D.q = Fintype.card K from Nat.card_eq_fintype_card]
        exact FiniteField.isPrimePow_card K, hK0⟩
  obtain ⟨S, hSD, -⟩ := exists_langSetup_of_descent_nosylow hF D hp
    (Or.inl (five_le_of_three_lt hp hp3)) hqpow hpq ι hι hd
  exact ⟨S, hSD, hSD ▸ hd⟩

end Untw

end CFSG.HardMathSupport.Timmesfeld.LangTorus
