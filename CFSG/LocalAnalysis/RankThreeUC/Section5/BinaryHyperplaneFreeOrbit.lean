module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinarySubgroup
public import CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeB
public import CFSG.LinearAlgebra.CoprimeActions.BinaryInvariantHyperplanes

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryHyperplaneFreeOrbit

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem free_at (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (K : BinaryRepresentations.hyperplanes 2 (X hc)) (b : B)
    (hnorm : conjOnP P hc.faithfulBinaryIrreducibleAction.normal b.val ∈ Subgroup.normalizer (K.val : Set (MulAut ↥P))) :
    b = 1 := by
  by_contra hb
  obtain ⟨hcard, hprime, hodd, -⟩ := PrimeB.prime_order hc hr
  haveI : Fact (Nat.card B).Prime := ⟨hprime⟩
  have htop : Subgroup.zpowers b = ⊤ := by
    have hd : orderOf b ∣ Nat.card B := orderOf_dvd_natCard b
    have hne : orderOf b ≠ 1 := fun h => hb (orderOf_eq_one_iff.mp h)
    have := (hprime.eq_one_or_self_of_dvd _ hd).resolve_left hne
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, this]
  have hcen := CentralBinarySubgroup.central_binary hc hodd
  refine CFSG.LinearAlgebra.CoprimeActions.BinaryInvariantHyperplanes.not_normalized
    (X hc) (Bstar P B) K.val hcen.2.2.1 hcen.2.2.2.2.2.1 hcen.2.2.2.2.2.2 K.2.1 K.2.2 ?_
  rintro _ ⟨⟨g, hgN⟩, hgB, rfl⟩
  have hgB' : g ∈ B := hgB
  have hmem : (⟨g, hgB'⟩ : B) ∈ Subgroup.zpowers b := by rw [htop]; trivial
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hg : g = (b : G) ^ n := by
    have := congrArg Subtype.val hn
    simpa using this.symm
  have : Subgroup.normalizerMonoidHom P ⟨g, hgN⟩ = (conjOnP P hc.faithfulBinaryIrreducibleAction.normal b.val) ^ n := by
    rw [← map_zpow]
    show conjOnP P hc.faithfulBinaryIrreducibleAction.normal g = _
    rw [hg]
  rw [this]
  exact zpow_mem hnorm n

theorem conj_injective (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (K : BinaryRepresentations.hyperplanes 2 (X hc)) (b₁ b₂ : B)
    (h : K.val.map (MulAut.conj (conjOnP P hc.faithfulBinaryIrreducibleAction.normal b₁.val)).toMonoidHom =
      K.val.map (MulAut.conj (conjOnP P hc.faithfulBinaryIrreducibleAction.normal b₂.val)).toMonoidHom) :
    b₁ = b₂ := by
  set f := conjOnP P hc.faithfulBinaryIrreducibleAction.normal
  have : b₁⁻¹ * b₂ = 1 := by
    refine free_at hc hr K _ ?_
    show f ((b₁⁻¹ * b₂ : B) : G) ∈ _
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    have key : ∀ (φ ψ : MulAut ↥P), K.val.map (MulAut.conj φ).toMonoidHom =
        K.val.map (MulAut.conj ψ).toMonoidHom → ∀ y, y ∈ K.val → φ⁻¹ * ψ * y * (φ⁻¹ * ψ)⁻¹ ∈ K.val := by
      intro φ ψ hφψ y hy
      have h1 : ψ * y * ψ⁻¹ ∈ K.val.map (MulAut.conj ψ).toMonoidHom :=
        ⟨y, hy, by simp [MulAut.conj_apply]⟩
      rw [← hφψ] at h1
      obtain ⟨z, hz, hzz⟩ := h1
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hzz
      have : φ⁻¹ * ψ * y * (φ⁻¹ * ψ)⁻¹ = z := by
        have : z = φ⁻¹ * (ψ * y * ψ⁻¹) * φ := by rw [← hzz]; group
        rw [this]; group
      rw [this]; exact hz
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key _ _ h y, fun hy => ?_⟩
    have := key _ _ h.symm _ hy
    simpa [mul_assoc] using this
  exact inv_mul_eq_one.mp this |>.symm ▸ rfl

end CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryHyperplaneFreeOrbit
