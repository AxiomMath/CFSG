module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FOMat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FURed
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFullCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog

namespace OmegaTwo

theorem conj_injective_of_simple {P : Type*} [Group P] [IsSimpleGroup P]
    (hnab : ∃ x y : P, x * y ≠ y * x) : Function.Injective (MulAut.conj : P →* MulAut P) := by
  have hZ : center P = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center P) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      apply hxy
      have hx : x ∈ center P := by rw [h]; exact mem_top x
      exact ((mem_center_iff.mp hx) y).symm
  rw [injective_iff_map_eq_one]
  intro y hy
  have hyZ : y ∈ center P := mem_center_iff.mpr fun z => by
    have h1 := congrArg (fun φ : MulAut P => φ z) hy
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc z * y = y * z * y⁻¹ * y := by rw [h1]
      _ = y * z := by group
  rw [hZ, mem_bot] at hyZ
  exact hyZ

theorem pPrimeCore_fixed_eq_bot_of_full {P : Type} [Group P] [Finite P]
    (hcj : Function.Injective (MulAut.conj : P →* MulAut P)) (β : MulAut P)
    (h0 : CFSG.oddCore ↥((⊤ : Subgroup (MulAut P)) ⊓ centralizer {β}) = ⊥) :
    pPrimeCore 2 ↥(fixedPoints β) = ⊥ := by
  have : Finite (MulAut P) := Finite.of_injective (fun e : MulAut P => (e : P → P))
    fun _ _ h => MulEquiv.ext (congrFun h)
  rw [PSUTwo.oddCore_eq_pPrimeCore_two] at h0
  have hM := PSUTwo.pPrimeCore_eq_bot_of_normal h0
    ((inner P).subgroupOf (⊤ ⊓ centralizer {β}))
  have hle : inner P ⊓ centralizer {β} ≤ ⊤ ⊓ centralizer {β} := inf_le_inf_right _ le_top
  have heq : (inner P ⊓ centralizer {β}).subgroupOf (⊤ ⊓ centralizer {β}) =
      (inner P).subgroupOf (⊤ ⊓ centralizer {β}) := by
    ext x
    simp only [mem_subgroupOf, mem_inf]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (mem_inf.mp x.2).2⟩⟩
  let e : ↥(fixedPoints β) ≃* ↥((inner P).subgroupOf (⊤ ⊓ centralizer {β})) :=
    (CatLeafProof.fixedInnerEquiv hcj β).trans ((Subgroup.subgroupOfEquivOfLe hle).symm.trans
      (MulEquiv.subgroupCongr heq))
  have hmap := pPrimeCore_map_iso 2 e
  rw [hM] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

theorem not_isPGroup_fixed_of {K : Type} [Field K] {f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    [Finite (matrixProjectiveDerived Q)]
    (hcj : Function.Injective (MulAut.conj : matrixProjectiveDerived Q →*
      MulAut (matrixProjectiveDerived Q)))
    (hfull : OmegaRadical.FullInvolutionOddCore Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ δ, δ⁻¹ * α * δ ∈ matrixProjectiveImage Q)
    (β : MulAut (matrixProjectiveDerived Q)) (hβ : orderOf β = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints β) ⧸ pPrimeCore 2 ↥(fixedPoints β)) := by
  intro hP
  have hO := pPrimeCore_fixed_eq_bot_of_full hcj β (hfull ⊤ le_top β (mem_top β) hβ)
  have hββ : β * β = 1 := by
    have h := pow_orderOf_eq_one β
    rw [hβ, pow_two] at h
    exact h
  obtain ⟨δ, hδ⟩ := hconj β hββ
  have hγ : orderOf (δ⁻¹ * β * δ) = 2 := by
    rw [show δ⁻¹ * β * δ = MulAut.conj δ⁻¹ β by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, hβ]
  obtain ⟨y, hy, hy1, hy3⟩ := exists_fixed_order_three hf hK hn hQ hT hE hcj hδ hγ
  refine PSUTwo.false_of_fixed hO hP (y := δ y) ?_ ?_ (by decide : Odd 3) ?_
  · have h1 : (δ⁻¹ * β * δ) y = y := hy
    rw [MulAut.mul_apply, MulAut.mul_apply] at h1
    calc β (δ y) = δ (δ⁻¹ (β (δ y))) := by rw [MulAut.apply_inv_self]
      _ = δ y := by rw [h1]
  · intro h1
    apply hy1
    rw [← map_one δ] at h1
    exact δ.injective h1
  · rw [← map_pow, hy3, map_one]

end OmegaTwo

theorem twoNilpFor_pOmegaPlus : POmegaPlusRow := by
  intro Y _ _ hY hs hnab a ha hP
  exfalso
  obtain ⟨n, f, hm⟩ := hY
  have hm' := hm
  obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  let ψ := coordinatePlusWitnessEquiv K e
  have : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv _ ψ.toEquiv
  have : IsSimpleGroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    MulEquiv.isSimpleGroup ψ.symm
  have hnab' : ∃ x y : matrixProjectiveDerived (coordinateQuadPlus n K), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨ψ x, ψ y, fun h => hxy (ψ.injective (by rw [map_mul, map_mul, h]))⟩
  have hcj := OmegaTwo.conj_injective_of_simple hnab'
  have hfull := even_orthogonal_all_involution_full_centralizer_odd_core Y .POmegaPlus
    (Or.inl rfl) n f hm' K hK e
  have hconj := ((even_orthogonal_involutions_conjugate_into_semilinear_image Y .POmegaPlus
    (Or.inl rfl) n f hm').1 K hK e).1
  exact OmegaTwo.not_isPGroup_fixed_of hf hK hn hQ hT hE hcj hfull hconj (MulAut.congr ψ a)
    ((orderOf_congr ψ a).trans ha) (isPGroup_fixedPoints_congr ψ a hP)

theorem twoNilpFor_pOmegaMinus : POmegaMinusRow := by
  intro Y _ _ hY hs hnab a ha hP
  exfalso
  obtain ⟨n, f, hm⟩ := hY
  have hm' := hm
  obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hm
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  have hE := commutator_coordinateQuadMinus n K b c hn hirr
  let ψ := coordinateMinusWitnessEquiv K hn1 b c e
  have : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    Finite.of_equiv _ ψ.toEquiv
  have : IsSimpleGroup (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    MulEquiv.isSimpleGroup ψ.symm
  have hnab' : ∃ x y : matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c),
      x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨ψ x, ψ y, fun h => hxy (ψ.injective (by rw [map_mul, map_mul, h]))⟩
  have hcj := OmegaTwo.conj_injective_of_simple hnab'
  have hfull := even_orthogonal_all_involution_full_centralizer_odd_core Y .POmegaMinus
    (Or.inr rfl) n f hm' hn1 K hK b c hirr e
  have hconj := (even_orthogonal_involutions_conjugate_into_semilinear_image Y .POmegaMinus
    (Or.inr rfl) n f hm').1 hn1 K hK b c hirr e
  exact OmegaTwo.not_isPGroup_fixed_of hf hK hn hQ hT hE hcj hfull hconj (MulAut.congr ψ a)
    ((orderOf_congr ψ a).trans ha) (isPGroup_fixedPoints_congr ψ a hP)

end CFSG.ComponentClassification.HarrisLit.L33.C2
