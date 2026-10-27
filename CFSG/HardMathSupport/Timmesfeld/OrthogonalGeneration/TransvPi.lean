module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvKd
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component
public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {X : Type*} [Group X] {K : Subgroup X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

@[expose] noncomputable def liftSubEquiv (e : ↥K ≃* ↥(elementaryGroup Q))
    {J : Subgroup (V ≃ₗ[ZMod 2] V)} (hJ : J ≤ elementaryGroup Q) : ↥(liftSub e J) ≃* ↥J :=
  MulEquiv.ofBijective
    (((embK e).comp (Subgroup.inclusion (liftSub_le e J))).codRestrict J fun k =>
      (mem_liftSub.mp k.2).2)
    ⟨fun a b h => by
      have h1 := congrArg Subtype.val h
      have h2 := embK_injective e h1
      exact Subtype.ext (congrArg (fun y : ↥K => (y : X)) h2),
     fun z => by
      obtain ⟨k, hk1, hk2⟩ := exists_mem_liftSub e hJ z.2
      exact ⟨⟨k, hk1⟩, Subtype.ext hk2⟩⟩

theorem glaPPrimeCore_eq_bot_of_simple {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hdvd : p ∣ Nat.card G) : GLAPPrimeCore p G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p G) with h | h
  · exact h
  · exfalso
    have hc := GL83.PiGen.coprime_card_glaPPrimeCore hp G
    rw [h, Subgroup.card_top] at hc
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hc hdvd

theorem center_eq_bot_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (hnc : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have : a ∈ Subgroup.center G := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem isPiGroup_of_simple_data {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnc : ∃ a b : G, a * b ≠ b * a) (hdvd : p ∣ Nat.card G)
    (hΩ : ∃ (n' : ℕ) (ε' : Bool), 1 ≤ n' ∧ IsOmegaTwo ε' (n' + 1) G ∧
      HasFixedPointFreeOrder ε' n' p) : LocalAnalysis.GLTheoremB.IsPiGroup p G := by
  have hcen : Subgroup.center G = ⊥ := center_eq_bot_of_simple_nonabelian hnc
  refine ⟨GL83.PiGen.isQuasisimple_of_simple_nonabelian hnc,
    glaPPrimeCore_eq_bot_of_simple hp hdvd, Or.inr (Or.inl ?_)⟩
  obtain ⟨n', ε', h1, h2, h3⟩ := hΩ
  refine ⟨n', ε', h1, ?_, h3⟩
  let φ : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  cases ε'
  · obtain ⟨ψ⟩ := h2
    exact ⟨φ.trans ψ⟩
  · obtain ⟨ψ⟩ := h2
    exact ⟨φ.trans ψ⟩

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
