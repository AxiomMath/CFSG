module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharDetCover

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section

theorem outTowerAt_adjointE {τ : Tag} {F : Type} [Field F] [Finite F]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ} [Fact p.Prime]
    (hdet : τ.cartan.det.natAbs ≤ p) : OutTowerAt (adjointGroup τ F) p := by
  obtain ⟨Φ, -, -, hkerΦ⟩ := exists_outer_hom_E (K := F) hτ
  have hpos : 0 < τ.cartan.det.natAbs := by
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6]; decide
    · rw [det_cartan_E7]; decide
    · rw [det_cartan_E8]; decide
  have hcardker : Nat.card Φ.ker ≤ p := (Nat.le_of_dvd hpos hkerΦ).trans hdet
  obtain ⟨ℓ, f, hℓ, hf, hF⟩ : ∃ ℓ f : ℕ, ℓ.Prime ∧ 1 ≤ f ∧ Nat.card F = ℓ ^ f := by
    have : Fintype F := Fintype.ofFinite F
    have := Fact.mk (CharP.char_is_prime F (ringChar F))
    obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
    exact ⟨ringChar F, n, hp, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hcyc : IsCyclic (F ≃+* F) := CFSG.RankThree.PartOne.CTP.isCyclic_ringEquiv_of_card hℓ hf hF
  have hcomm : ∀ x y : RingAut F × Multiplicative (ZMod (exactE τ)), x * y = y * x := by
    intro x y
    refine Prod.ext ?_ (mul_comm _ _)
    exact (IsCyclic.commGroup (α := F ≃+* F)).mul_comm x.1 y.1
  set π := Φ.comp (QuotientGroup.mk' (inner (adjointGroup τ F))) with hπ
  set D := π.ker with hD
  have hab : ∀ γ α : MulAut (adjointGroup τ F), (∃ k : ℕ, α ^ (p ^ k) = 1) →
      γ * α * γ⁻¹ * α⁻¹ ∈ D := by
    intro γ α _
    rw [hD, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm (π γ) (π α)]
    group
  refine outTowerAt_of_card_le D hab ?_
  set I := inner (adjointGroup τ F) with hI
  let ψ : D →* Outer (adjointGroup τ F) := (QuotientGroup.mk' I).comp D.subtype
  have hker : ψ.ker = I.subgroupOf D := by
    ext x
    simp [ψ, hI, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : ψ.range = Φ.ker := by
    ext y
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective I y
    constructor
    · rintro ⟨x, hx⟩
      have h2 : π (x : MulAut (adjointGroup τ F)) = 1 := x.2
      have h3 : QuotientGroup.mk' I (x : MulAut (adjointGroup τ F)) = QuotientGroup.mk' I α := hx
      rw [MonoidHom.mem_ker, ← h3]
      simpa [hπ] using h2
    · intro hy
      refine ⟨⟨α, ?_⟩, rfl⟩
      rw [hD, MonoidHom.mem_ker]
      simpa [hπ] using hy
  have h1 : Nat.card (D ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  rw [hker, hrange] at h1
  change Nat.card (D ⧸ I.subgroupOf D) ≤ p
  omega

end

section

theorem exists_mulEquiv_adjoint {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty (ValidLieTypeIndex.Group ⟨c q, hv⟩ ≃* adjointGroup τ F) := by
  have hF := CFSG.TauCetiBridge.card_fieldOf q Nat.one_pos
  rw [pow_one] at hF
  obtain ⟨φ⟩ := hB q hv (CFSG.TauCetiBridge.fieldOf q 1) hF
  exact ⟨CFSG.TauCetiBridge.fieldOf q 1, inferInstance, inferInstance,
    ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)⟩⟩

theorem outTowerAt_E6 {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid) {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) : OutTowerAt (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group p := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_mulEquiv_adjoint
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e6 q hv
  refine OutTowerAt.of_mulEquiv e (outTowerAt_adjointE (Or.inl rfl) ?_)
  rw [det_cartan_E6]; exact hp

theorem outTowerAt_E7 {q : PrimePower} (hv : (LieTypeIndex.E7 q).Valid) {p : ℕ} [Fact p.Prime] :
    OutTowerAt (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group p := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_mulEquiv_adjoint
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e7 q hv
  refine OutTowerAt.of_mulEquiv e (outTowerAt_adjointE (Or.inr (Or.inl rfl)) ?_)
  rw [det_cartan_E7]; exact (Fact.out : p.Prime).two_le

theorem p1OffCharAlmostSimpleNonNormalAt_E6 {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.E6 q, hv⟩ :=
  p1OffCharAlmostSimpleNonNormalAt_of_towerOrCover fun p _ hp2 _ _ =>
    Or.inl (outTowerAt_E6 hv (by
      have := (Fact.out : p.Prime).two_le
      omega))

theorem p1OffCharAlmostSimpleNonNormalAt_E7 {q : PrimePower} (hv : (LieTypeIndex.E7 q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.E7 q, hv⟩ :=
  p1OffCharAlmostSimpleNonNormalAt_of_towerOrCover fun _ _ _ _ _ => Or.inl (outTowerAt_E7 hv)

end

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
