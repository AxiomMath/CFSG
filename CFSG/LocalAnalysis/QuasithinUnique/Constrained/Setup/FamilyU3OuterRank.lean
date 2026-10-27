module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3VGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyWeights

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

section OuterRank

variable {p : ℕ} [Fact p.Prime] {K F : Type} [Field K] [Field F] [Fintype F] [DecidableEq F]
  [CharP F p] {h : UnitaryFieldData p 1 K} {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
  (D : CoverDataU h L)

theorem CoverDataU.outer_rank [Finite W] [Fact (∀ w : W, w * w = 1)] (ι : F →+* K)
    (hFcard : Fintype.card F = p) (hp5 : 5 ≤ p) (hι : ∀ x, h.bar (ι x) = ι x)
    (hfix : ∀ m : K, h.bar m = m → ∃ x : F, ι x = m)
    (hFK : ∀ k : F, ∃ n : ℕ, (n : F) = k) (hperf : Group.IsPerfect ↥(SUI h)) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) (A : UI h)
    (hAs : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hAA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = 1)
    (hβ : D.beta hb = primeFormConjHom h _ A * primeFormFieldHom h
      (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin 3) K)) (barEquiv h)) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin b))) := by
  classical
  obtain ⟨v, hv0, hvadd, hvinv, hvfaith⟩ :=
    exists_unitary_inverted_vgroup h ι hFcard hp5 hι hfix A hAs hAA
  have hrel : ∀ x : ↥(SUI h), b * ((D.φ x : ↥L) : MulAut W) * b⁻¹ =
      ((D.φ (tauU h A (barEquiv h) x) : ↥L) : MulAut W) :=
    D.conj_eq hperf hb (tauU h A (barEquiv h)) (fun x => by rw [hβ]; exact conjField_mk h A _ x)
  have hvneg : ∀ a, v (-a) = (v a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_right
    rw [← hvadd, add_neg_cancel, hv0]
  let ρ' : F × F → (Additive W ≃ₗ[ZMod 2] Additive W) := fun a =>
    binaryLin ((D.φ (v a) : ↥L) : MulAut W)
  have hV : IsVAct ρ' := ⟨by simp [ρ', hv0], fun x y => by simp [ρ', hvadd]⟩
  have hodd : Odd (Fintype.card F) := by
    rw [hFcard]
    exact (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hfaith : ∀ x, ρ' x = 1 → x = 0 := by
    intro x hx
    have h1 : ((D.φ (v x) : ↥L) : MulAut W) = 1 :=
      binaryLin_injective (by rw [map_one]; exact hx)
    have h2' : D.φ (v x) = 1 := Subtype.ext h1
    obtain ⟨r, hr⟩ := D.ker_scalar _ (MonoidHom.mem_ker.2 h2')
    exact hvfaith x r hr
  have hs : binaryLin b * binaryLin b = 1 := by rw [← map_mul, hb2, map_one]
  have hsρ : ∀ a, binaryLin b * ρ' a * binaryLin b = ρ' (-a) := by
    intro a
    have h1 : b * ((D.φ (v a) : ↥L) : MulAut W) * b = ((D.φ (v (-a)) : ↥L) : MulAut W) := by
      have := hrel (v a)
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
      rw [hvinv, hbinv] at this
      rw [this, hvneg, map_inv, Subgroup.coe_inv]
    show binaryLin b * binaryLin ((D.φ (v a) : ↥L) : MulAut W) * binaryLin b =
      binaryLin ((D.φ (v (-a)) : ↥L) : MulAut W)
    rw [← map_mul, ← map_mul, h1]
  obtain ⟨o, o', hne, ho, ho'⟩ := exists_two_lines hV hodd hfaith
  have hdet : det2 (lineRep o) (lineRep o') ≠ 0 := det2_lineRep hne
  have hdet' : det2 (lineRep o') (lineRep o) ≠ 0 := det2_lineRep hne.symm
  have hne' : lineRep o ≠ lineRep o' := fun h => hdet (by rw [h]; simp [det2]; ring)
  have := card_le_finrank_range_sub1 hV hodd hFK hs hsρ {lineRep o, lineRep o'}
    (by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact lineRep_ne_zero _
      · rw [Finset.mem_singleton.1 hu]; exact lineRep_ne_zero _)
    (by
      intro u hu w hw huw
      rcases Finset.mem_insert.1 hu with rfl | hu <;>
        rcases Finset.mem_insert.1 hw with rfl | hw
      · exact absurd rfl huw
      · rw [Finset.mem_singleton.1 hw]; exact hdet
      · rw [Finset.mem_singleton.1 hu]
        exact hdet'
      · rw [Finset.mem_singleton.1 hu, Finset.mem_singleton.1 hw] at huw
        exact absurd rfl huw)
    (by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact ho
      · rw [Finset.mem_singleton.1 hu]; exact ho')
  rwa [Finset.card_pair hne'] at this

end OuterRank

end CFSG.QuasithinUnique.Setup.Family
