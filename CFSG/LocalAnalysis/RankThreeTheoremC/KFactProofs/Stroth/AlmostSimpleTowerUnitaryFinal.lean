module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerUnitaryBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section Numerics

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem dvd_card_gramSU_one (hU : UnitaryFieldData ℓ f K) {e p : ℕ} (he : 2 ≤ e)
    (hpe : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ e - (-1) ^ e ∨
      (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ (e * (e - 1) / 2)) :
    p ∣ Nat.card (gramSU hU (1 : Matrix (Fin e) (Fin e) K)) := by
  have hfin := hU.finite
  have hsymm : (gramForm hU (1 : Matrix (Fin e) (Fin e) K)).IsSymm :=
    gramForm_isSymm hU (by simp [Matrix.map_one])
  have hsep : (gramForm hU (1 : Matrix (Fin e) (Fin e) K)).SeparatingLeft :=
    gramForm_separatingLeft hU (by simp)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order hU hsymm hsep
    (Module.finrank_fin_fun K) (by omega)).2.1
  rw [card_gramSU]
  refine Int.natCast_dvd_natCast.1 ?_
  rw [hSU]
  rcases hpe with h | h
  · exact (h.trans (Finset.dvd_prod_of_mem (fun i => (((ℓ ^ f : ℕ) : ℤ) ^ i - (-1) ^ i))
      (Finset.mem_Icc.2 ⟨he, le_rfl⟩))).mul_left _
  · exact h.mul_right _

end Numerics

theorem conj_injective_of_centralizer_eq_bot {X : Type*} [Group X] {L : Subgroup X} [L.Normal]
    (hC : Subgroup.centralizer (L : Set X) = ⊥) {P : Type*} [Group P] (e : ↥L ≃* P) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  intro a b hab
  obtain ⟨c, hcdef⟩ : ∃ c : P, c = b⁻¹ * a := ⟨_, rfl⟩
  have hc : ∀ z : P, c * z = z * c := by
    intro z
    have h1 := congrArg (fun φ : MulAut P => φ z) hab
    simp only [MulAut.conj_apply] at h1
    rw [hcdef]
    calc b⁻¹ * a * z = b⁻¹ * (a * z * a⁻¹) * a := by group
      _ = b⁻¹ * (b * z * b⁻¹) * a := by rw [h1]
      _ = z * (b⁻¹ * a) := by group
  have hl : ((e.symm c : ↥L) : X) ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h2 := hc (e ⟨g, hg⟩)
    have h3 : e.symm c * ⟨g, hg⟩ = ⟨g, hg⟩ * e.symm c := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h2
    exact (congrArg Subtype.val h3).symm
  rw [hC, Subgroup.mem_bot] at hl
  have h4 : e.symm c = 1 := Subtype.ext hl
  have h5 : c = 1 := e.symm.injective (by rw [h4, map_one])
  rw [hcdef] at h5
  exact (inv_mul_eq_one.1 h5).symm

theorem unitaryOuterResidual_holds : UnitaryOuterResidual := by
  intro p hp hp2 X _ _ L _ hC hE m q hv hm ⟨e⟩ hφ hq1 x hx
  haveI : Fact p.Prime := ⟨hp⟩
  have hN3 : 3 ≤ m + 1 := by omega
  have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv (MulEquiv.refl _)
  have hqne : ¬ (m + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h => hmodel.1.2.2.2 (by rw [h.1, h.2])
  obtain ⟨K, _, hU, ⟨e₀⟩, ⟨eP⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.exists_primeFormP_mulEquiv_of_statedModel
      hmodel
  haveI : Finite K := hU.finite
  have hC1 : IsPrimeFormGram (1 : GL (Fin (m + 1)) K) := isPrimeFormGram_one'
  set Cmat : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    ((1 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) with hCmat
  let eL : ↥L ≃* primeFormP hU Cmat := e.trans eP
  haveI : Finite (primeFormP hU Cmat) := Finite.of_equiv _ eL.toEquiv
  have hq1' : ¬ p ∣ q.p ^ q.exponent + 1 := by
    rwa [TauCeti.PrimePower.card_def] at hq1
  have hker : (primeFormFieldFactor hU hC1 hN3 hqne).ker = primeFormD hU Cmat :=
    ker_primeFormFieldFactor hU hC1 hN3 hqne
  haveI hDn : (primeFormD hU Cmat).Normal := by
    rw [← hker]
    infer_instance
  have hΘfld : ∀ σ : K ≃+* K,
      primeFormFieldFactor hU hC1 hN3 hqne (primeFormFieldHom hU hC1 σ) = σ := fun σ => by
    have := primeFormFieldFactor_apply hU hC1 hN3 hqne 1 σ
    rwa [map_one, one_mul] at this
  have hIDle : inner (primeFormP hU Cmat) ≤ primeFormD hU Cmat := fun α hα => by
    obtain ⟨s, rfl⟩ := (mem_inner_primeFormP hU Cmat α).1 hα
    exact ⟨_, rfl⟩
  haveI : (inner (primeFormP hU Cmat)).Normal := inner_normal _
  have hDI : ∀ w ∈ primeFormD hU Cmat, (∃ k : ℕ, w ^ (p ^ k) = 1) →
      w ∈ inner (primeFormP hU Cmat) := by
    rintro w hw ⟨k, hk⟩
    refine mem_of_pPow_eq_one_of_not_dvd_relIndex hp hIDle ?_ hw hk
    intro hd
    have hc := card_primeFormD_quotient_dvd hU (1 : GL (Fin (m + 1)) K)
    have hrel : (inner (primeFormP hU Cmat)).relIndex (primeFormD hU Cmat) =
        Nat.card (primeFormD hU Cmat ⧸
          (inner (primeFormP hU Cmat)).subgroupOf (primeFormD hU Cmat)) := by
      rw [Subgroup.relIndex, Subgroup.index]
    rw [hrel] at hd
    exact hq1' (hd.trans hc)
  have hfld : ∀ σ : K ≃+* K, primeFormFieldHom hU hC1 σ ∈ primeFormD hU Cmat → σ = 1 :=
    fun σ h => by
      rw [← hker, MonoidHom.mem_ker, hΘfld] at h
      exact h
  have hdec : ∀ z : MulAut (primeFormP hU Cmat), (∃ k : ℕ, z ^ (p ^ k) = 1) →
      ∃ c ∈ primeFormD hU Cmat, ∃ σ : K ≃+* K, z = c * primeFormFieldHom hU hC1 σ := by
    intro z _
    refine ⟨z * (primeFormFieldHom hU hC1 (primeFormFieldFactor hU hC1 hN3 hqne z))⁻¹, ?_,
      primeFormFieldFactor hU hC1 hN3 hqne z, by group⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hΘfld, mul_inv_cancel]
  have hconj : Function.Injective (MulAut.conj : primeFormP hU Cmat →* MulAut (primeFormP hU Cmat)) :=
    conj_injective_of_centralizer_eq_bot hC eL
  have hex : ∃ e' : ℕ, 2 ≤ e' ∧ 2 * e' ≤ m + 1 ∧
      p ∣ Nat.card (gramSU hU (1 : Matrix (Fin e') (Fin e') K)) := by
    have hd0 : 0 < Nat.gcd (m + 1) (q.card + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hd : 2 * p ≤ Nat.gcd (m + 1) (q.card + 1) := by
      by_contra h
      exact not_dvd_totient_of_lt hp hp2 hd0 (by omega) hφ
    have hn2 : 2 * p ≤ m + 1 := hd.trans (Nat.gcd_le_left _ (by omega))
    have h3 := hp.two_le
    by_cases hpc : p = q.p
    · refine ⟨2, le_rfl, by omega, dvd_card_gramSU_one hU le_rfl (Or.inr ?_)⟩
      have : (p : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) := by
        rw [hpc]
        exact_mod_cast dvd_pow_self q.p q.exponent_pos.ne'
      simpa using this
    · refine ⟨p - 1, by omega, by omega, dvd_card_gramSU_one hU (by omega) (Or.inl ?_)⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hz : ((q.p ^ q.exponent : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd'
        exact hpc ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow hd'))
      have h2 : ((q.p ^ q.exponent : ℕ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hz
      push_cast at h2 ⊢
      rw [(hp.even_sub_one hp2).neg_one_pow, h2, sub_self]
  obtain ⟨e', he2, hn', hdvd'⟩ := hex
  have hTwo : ∀ τ : K ≃+* K, orderOf τ = p → ∃ x₁ x₂ : primeFormP hU Cmat, Commute x₁ x₂ ∧
      x₁ ^ p = 1 ∧ x₂ ^ p = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      primeFormFieldHom hU hC1 τ x₁ = x₁ ∧ primeFormFieldHom hU hC1 τ x₂ = x₂ := fun τ hτ =>
    exists_two_indep_fixed_unitary hU hp hq1' hdvd' hn' (by omega) τ (hτ ▸ pow_orderOf_eq_one τ)
  let ψ : X →* MulAut (primeFormP hU Cmat) := (MulAut.congr eL).toMonoidHom.comp MulAut.conjNormal
  have hψ : Function.Injective ψ := by
    have h1 : Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) :=
      CFSG.LieType.SeitzGeneration.conjNormal_injective hC
    exact (MulAut.congr eL).injective.comp h1
  have hL : ∀ y : primeFormP hU Cmat, ∃ l ∈ L, ψ l = MulAut.conj y := by
    intro y
    refine ⟨((eL.symm y : ↥L) : X), (eL.symm y).2, ?_⟩
    ext z
    simp [ψ, MulAut.conjNormal_val, MulAut.congr_apply, MulAut.conj_apply]
  have hrk : CFSG.LieType.SeitzGeneration.RankLE2 p X := hE
  have hin := pElements_inner_of_two_indep (primeFormFieldHom hU hC1) (primeFormD hU Cmat) hp
    hIDle hDI hfld hdec hconj hTwo hrk ψ hψ L hL hx
  obtain ⟨y, hy⟩ := hin
  obtain ⟨l, hlL, hl⟩ := hL y
  have : l = x := hψ (by rw [hl, hy])
  exact this ▸ hlL

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
