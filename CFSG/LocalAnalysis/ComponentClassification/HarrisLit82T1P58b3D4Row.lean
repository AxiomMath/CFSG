module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3D4Aut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3D4Four
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LConfig

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open scoped MatrixGroups

namespace P58b3D4

variable {K : Type} [Field K] [Finite K]

theorem false_of_typeD_three_four {X : Type} [Group X] [Finite X] (hO : pPrimeCore 2 X = ⊥)
    (hK3 : Nat.card K = 3) {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R) (hker : OKer (oQ R))
    (θ : X ⧸ center X ≃* StatedProj (matrixDerived (oQ R))) {c t : X}
    (hcZ : c ∈ center X) (hc2 : orderOf c = 2) (ht2 : orderOf t = 2) (htZ : t ∉ center X)
    {Q₁ : Subgroup X} (hQ₁ : IsSolvableTwoComponentIn Q₁ (centralizer {t})) (hcQ₁ : c ∈ Q₁) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set π₀ : X →* StatedProj (matrixDerived (oQ R)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (center X)) with hπ₀
  have hπ₀s : Function.Surjective π₀ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπ₀k : π₀.ker = center X := by
    ext y
    rw [MonoidHom.mem_ker, hπ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have hxx : π₀ t * π₀ t = 1 := by rw [← map_mul, htt, map_one]
  have hx1 : π₀ t ≠ 1 := fun h => htZ (hπ₀k ▸ MonoidHom.mem_ker.mpr h)
  obtain ⟨T, hT, hxT, hT2 | hT2⟩ := P51e.Orth.exists_lift_sq h2 (by omega) hR hxx
  ·
    obtain ⟨w, hw, J, hJ, θ', hker', hJne, hJc, hNF, hθ'T, -⟩ :=
      P58b3L.exists_sign_frame_plus hK hR hker hT hT2 (by rw [← hxT]; exact hx1)
    set π : X →* StatedProj (matrixDerived (oQ (diagGL hw))) := θ'.toMonoidHom.comp π₀ with hπ
    have hπs : Function.Surjective π := θ'.surjective.comp hπ₀s
    have hπk : π.ker = center X := by
      ext y
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hπ₀k]
    have hπt : π t = projH _ ⟨signGL K J, hJ⟩ := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hxT, hθ'T]
    obtain ⟨hR₁x, hR₁s, hR₁solv, hR₁odd, ⟨r, hr, hr3, hr1⟩, hnc⟩ :=
      P58b3L.facts_map_solvable_two hO π hπs hπk hcZ hc2 hQ₁ hcQ₁
    rw [hπt] at hR₁x hR₁s
    have hJev := P58b.OLie.even_card_of_signGL_mem hK hJ
    have hsum : J.card + Jᶜ.card = 2 * 4 := by
      rw [Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_univ J
      rw [Fintype.card_fin] at this
      omega
    have hJcev : Even Jᶜ.card := by
      obtain ⟨a, ha⟩ := hJev
      exact ⟨4 - a, by omega⟩
    obtain ⟨I, hI, h3I, hqI, hIcev⟩ : ∃ I : Finset (Fin (2 * 4)), (I = J ∨ I = Jᶜ) ∧
        3 ≤ I.card ∧ IsQuasisimple (blockP K hw I) ∧ Even Iᶜ.card := by
      by_cases h5 : 5 ≤ J.card
      · exact ⟨J, Or.inl rfl, by omega, P58b3.isQuasisimple_blockP_of_five_le hw hK h5 hJc,
          hJcev⟩
      by_cases h5' : 5 ≤ Jᶜ.card
      · exact ⟨Jᶜ, Or.inr rfl, by omega, P58b3.isQuasisimple_blockP_of_five_le hw hK h5'
          (by rwa [compl_compl]), by rw [compl_compl]; exact hJev⟩
      have hJ4 : J.card = 4 := by
        obtain ⟨a, ha⟩ := hJev
        obtain ⟨b, hb⟩ := hJcev
        omega
      have hJc4 : Jᶜ.card = 4 := by omega
      by_cases hqJ : IsQuasisimple (blockP K hw J)
      · exact ⟨J, Or.inl rfl, by omega, hqJ, hJcev⟩
      by_cases hqJc : IsQuasisimple (blockP K hw Jᶜ)
      · exact ⟨Jᶜ, Or.inr rfl, by omega, hqJc, by rw [compl_compl]; exact hJev⟩
      exact (false_of_sign_four_plus hw hK3 hJ hJ4 hJc4 hqJ hqJc hR₁x hR₁s hR₁odd hr hr3 hr1
        hnc).elim
    exact P58b3L.false_of_sign_of_quasisimple hw hK3 hker' hJ hJne hJc hNF hI h3I hqI hIcev hR₁x
      hR₁s hR₁solv hR₁odd hr hr3 hr1 hnc
  ·
    obtain ⟨R₁, A, θ₂, hR₁m, hAm, hθ₂T⟩ := P58b3L.exists_pc_model hK hR hT hT2
    set π : X →* StatedProj (matrixDerived (oQ R₁)) := θ₂.toMonoidHom.comp π₀ with hπ
    have hπs : Function.Surjective π := θ₂.surjective.comp hπ₀s
    have hπk : π.ker = center X := by
      ext y
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hπ₀k]
    have hπt : π t = projH _ A := by
      rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hxT, hθ₂T]
    obtain ⟨hR₁x, hR₁s, hR₁solv, -, ⟨r, hr, hr3, hr1⟩, -⟩ :=
      P58b3L.facts_map_solvable_two hO π hπs hπk hcZ hc2 hQ₁ hcQ₁
    rw [hπt] at hR₁x hR₁s
    exact hr1 (P58b3L.eq_one_of_odd_of_pc hK3 (by norm_num) hR₁m hAm hR₁x hR₁s hR₁solv hr
      (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hr3)))

end P58b3D4


open P58b3L in
theorem harris82Lemma58bThreeRowAt_POmegaPlus_four :
    P58b3.Harris82Lemma58bThreeRowAt .POmegaPlus 4 1 := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ L₂ K hL₁ _ hz₁L _ _ hKc hO₁ _ hN hz₂K hz₂Z hm
  exfalso
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, hO, hmX, -⟩ := P58b3.setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  have hc2 := P58b.orderOf_mk_eq_two (K := ↥K) (z := ⟨z₁, hz₁K⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz₁)
  have ht2 := P58b.orderOf_mk_eq_two (K := ↥K) (z := ⟨z₂, hz₂K⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz₂)
  have hcZ := mk_mem_center hKc.1 hz₁K
  have hcQ₁ : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ∈
      ((L₁ ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
    ⟨⟨z₁, hz₁K⟩, mem_subgroupOf.mpr ⟨hz₁L, hz₁K⟩, rfl⟩
  have hc1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have ha := P58b3D4.oddAutInnerFix_of_POmegaPlus_four hX hmX hcZ hc1
  have hQ₁ := P58b3.lemma57_fourGroup_map_of_fix hz₂ hL₁ hKc.1 hO₁ hN hz₂K hz₁K ha
  rcases hmX with ⟨-, hcm⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hcm' := hcm
  obtain ⟨-, K₀, _, _, hK₀c, ⟨e⟩⟩ := hcm'
  have hK3 : Nat.card K₀ = 3 := by rw [hK₀c, pow_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : CharP K₀ 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K₀ ≠ 2 := by rw [ringChar.eq K₀ 3]; norm_num
  have h2 : (2 : K₀) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus 4 K₀)
    (regular_coordinateQuadPlus 4 K₀ (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * 4)) K₀) : Matrix _ _ K₀) *ᵥ v) =
      ((1 : K₀ˣ) : K₀) * coordinateQuadPlus 4 K₀ v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker : OKer (oQ R) := OKer.transport 1 1 hS₁ (oKer_coordinatePlus hcm K₀ hK₀c e)
  exact P58b3D4.false_of_typeD_three_four hO hK3 hR hker
    ((coordinatePlusWitnessEquiv K₀ e).trans (oTransport 1 1 hS₁)) hcZ hc2 ht2 hz₂Z hQ₁ hcQ₁

end CFSG.ComponentClassification.HarrisLit.T1
