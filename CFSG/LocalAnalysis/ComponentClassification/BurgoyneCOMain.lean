module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOB3
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOReduce
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOForm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open scoped MatrixGroups commutatorElement

@[expose] def NoProperPair (G : Type) [Group G] (R₁ R₂ : Subgroup G) : Prop :=
  ¬ ∃ t : G, orderOf t = 2 ∧ ∃ Y : Subgroup G, Y ≠ ⊥ ∧ Y ≤ oddCentralizerCore t ∧
    ActsProperly t Y R₁ ((pPrimeCore 2 R₁).map R₁.subtype) ∧
    ActsProperly t Y R₂ ((pPrimeCore 2 R₂).map R₂.subtype)

section Proper

variable {G : Type*} [Group G]

theorem exists_noncomm_of_actsProperly {t : G} {E A B : Subgroup G} (h : ActsProperly t E A B) :
    ∃ e ∈ E, ∃ a ∈ A, a * e ≠ e * a := by
  obtain ⟨-, -, e, he, a, ha, hne⟩ := h
  refine ⟨e, he, a, ha, fun hc => hne ?_⟩
  rw [commutatorElement_def, hc, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem B

theorem mem_normalizer_of_actsProperly {t : G} {E A B : Subgroup G} (h : ActsProperly t E A B)
    {e : G} (he : e ∈ E) : e ∈ normalizer (A : Set G) :=
  (h.1 (subset_closure (Set.mem_insert_of_mem t he))).1

end Proper

theorem odd_orderOf_of_mem_oddCentralizerCore {X : Type} [Group X] [Finite X] {t y : X}
    (hy : y ∈ oddCentralizerCore t) : Odd (orderOf y) := by
  obtain ⟨c, hc, rfl⟩ := hy
  have h1 := orderOf_dvd_natCard (⟨c, hc⟩ : pPrimeCore 2 (centralizer ({t} : Set X)))
  rw [Subgroup.orderOf_mk] at h1
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  exact Odd.of_dvd_nat odd_card_pPrimeCore h1

theorem congr_conj {T T' : Type*} [Group T] [Group T'] (Θ : T ≃* T') (y : T) :
    MulAut.congr Θ (MulAut.conj y) = MulAut.conj (Θ y) := by
  ext z
  simp [MulAut.congr_apply]

theorem mul_conj_mul_inv {T : Type*} [Group T] (α : MulAut T) (b : T) :
    α * MulAut.conj b * α⁻¹ = MulAut.conj (α b) := by
  ext z
  simp

section Model

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem orth_odd_propC (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hKc : Nat.card K = ℓ ^ e) (hd : 7 ≤ d) (hodd : Odd d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R)) (hsurj : OSurj (oQ R))
    {X : Type} [Group X] [Finite X] (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (hout : Group.IsSolvable (OuterAutomorphisms.Outer (GeneralizedFitting.subgroup X)))
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {r : X} {R₁ R₂ : Subgroup X} {p n : ℕ} [Fact p.Prime] (hC : PropCData r R₁ R₂ p n) :
    d = 7 ∧ Nat.card K = p ^ n ∧ NoProperPair X R₁ R₂ := by
  obtain ⟨x, R₁', R₂', hC', hrx, hR₁', hR₂'⟩ := exists_propCData_of_socle hsimple hnab hout θ
    hC.orderOf_eq hC.le₁ hC.comp₁ hC.le₂ hC.comp₂ hC.p_ne_two hC.n_pos hC.iso₁ hC.iso₂ hC.mem
  obtain ⟨hd7, hcard, w, hw, S, hS, J, I, hJ, hxJ, hI, hI4, hR₂I, hR₁I⟩ :=
    orth_propC_odd hK hd hodd hR hC'
  refine ⟨hd7, hcard, ?_⟩
  rintro ⟨t, ht, Y, -, hYO, hp₁, hp₂⟩
  obtain ⟨e₁, he₁, a₁, ha₁, hne₁⟩ := exists_noncomm_of_actsProperly hp₁
  obtain ⟨e₂, he₂, a₂, ha₂, hne₂⟩ := exists_noncomm_of_actsProperly hp₂
  have hGF2 : (2 : GaloisField p n) ≠ 0 := two_ne_zero_galoisField hC.p_ne_two
  obtain ⟨f₂⟩ := hC.iso₂
  have hYr : ∀ {y : X}, y ∈ Y → y * r = r * y := by
    intro y hy
    have := conj_eq_of_mem_normalizer hGF2 f₂ hC.le₂ hC.mem hC.orderOf_eq
      (mem_normalizer_of_actsProperly hp₂ hy)
    calc y * r = y * r * y⁻¹ * y := by group
      _ = r * y := by rw [this]
  have hcore : oddCentralizerCore t ≠ ⊥ := by
    intro hbot
    have h1 := hYO he₁
    rw [hbot, mem_bot] at h1
    exact hne₁ (by rw [h1, mul_one, one_mul])
  obtain ⟨g, hg⟩ := hsurj (socleAction θ t)
  have hshape : OddShape θ t := by
    by_cases hσ : g.val.right = 1
    · rcases inner_odd_shape hK hd hodd hR hker hsimple hnab θ (hsurj.surjX θ t) ht hσ hg with
        h | h
      · exact absurd h hcore
      · exact h
    · exact absurd (field_oddCentralizerCore_eq_bot hK (by omega) hℓ he hKc hR hker hsimple hnab
        θ (hsurj.surjX θ t) ht hσ hg) hcore
  set θ' := θ.trans (oTransport S 1 hS) with hθ'
  obtain ⟨U, hU, hUx⟩ := hshape.transport S 1 hS
  obtain ⟨B₁, hB₁, hB₁x, hB₁U⟩ := hUx e₁ (hYO he₁)
  obtain ⟨B₂, hB₂, hB₂x, hB₂U⟩ := hUx e₂ (hYO he₂)
  have hψ' := socleAction_injective hsimple hnab θ'
  have hψr : socleAction θ' r = oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) := by
    rw [hθ', socleAction_trans, hrx, congr_conj, hxJ, sgnPair, oκ_linPair_eq_conj _ hJ]
    rfl
  have hcomm : ∀ {y : X} {B : GL (Fin d) K} (hB : B ∈ matrixIsometries (oQ (diagGL hw))),
      y ∈ Y → socleAction θ' y = oκ _ (linPair B hB) →
      oκ _ (linPair B hB) * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
        oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * oκ _ (linPair B hB) := by
    intro y B hB hy hyB
    rw [← hyB, ← hψr, ← map_mul, ← map_mul, hYr hy]
  have hm := odd_orderOf_of_mem_oddCentralizerCore (hYO he₁)
  have hm1 : oκ _ (linPair B₁ hB₁) ^ orderOf e₁ = 1 := by
    rw [← hB₁x, ← map_pow, pow_orderOf_eq_one, map_one]
  have hmove : ∀ {y a : X} {Ri : Subgroup X} {Ri' : Subgroup (StatedProj (matrixDerived (oQ R)))}
      {B : GL (Fin d) K} (hB : B ∈ matrixIsometries (oQ (diagGL hw)))
      {T : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))},
      Ri.map (socleAction θ) = Ri'.map MulAut.conj →
      Ri'.map (oTransport S 1 hS).toMonoidHom ≤ T → a ∈ Ri → a * y ≠ y * a →
      socleAction θ' y = oκ _ (linPair B hB) → ∃ b ∈ T, oκ _ (linPair B hB) b ≠ b := by
    intro y a Ri Ri' B hB T hmap hT ha hay hyB
    have hmem : socleAction θ a ∈ Ri'.map MulAut.conj := by
      rw [← hmap]
      exact ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hbe⟩ := hmem
    refine ⟨oTransport S 1 hS b, hT ⟨b, hb, rfl⟩, fun hfix => hay (hψ' ?_)⟩
    have hψa : socleAction θ' a = MulAut.conj (oTransport S 1 hS b) := by
      rw [hθ', socleAction_trans, ← hbe, congr_conj]
    have h3 : oκ _ (linPair B hB) * MulAut.conj (oTransport S 1 hS b) *
        (oκ _ (linPair B hB))⁻¹ = MulAut.conj (oTransport S 1 hS b) := by
      rw [mul_conj_mul_inv, hfix]
    rw [map_mul, map_mul, hψa, hyB]
    calc MulAut.conj (oTransport S 1 hS b) * oκ _ (linPair B hB) =
        (oκ _ (linPair B hB) * MulAut.conj (oTransport S 1 hS b) * (oκ _ (linPair B hB))⁻¹) *
          oκ _ (linPair B hB) := by rw [h3]
      _ = oκ _ (linPair B hB) * MulAut.conj (oTransport S 1 hS b) := by group
  have hIc : 2 ≤ Iᶜ.card := by
    have := card_compl_add I
    omega
  exact b3_false hw hK (hker.transport S 1 hS) (by omega) hI hIc hU hB₁ hB₂ hB₁U hB₂U
    (hcomm hB₁ he₁ hB₁x) (hcomm hB₂ he₂ hB₂x) hm hm1 (hmove hB₁ hR₁' hR₁I ha₁ hne₁ hB₁x)
    (hmove hB₂ hR₂' hR₂I ha₂ hne₂ hB₂x)

end Model

section Tags

variable {X : Type} [Group X] [Finite X]

theorem burgoynePropC_POmegaOdd (hX : IsM4 X) {m p' f' : ℕ} (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaOdd m p' f') {r : X}
    {R₁ R₂ : Subgroup X} {p n : ℕ} [Fact p.Prime] (hC : PropCData r R₁ R₂ p n) :
    LieModel (GeneralizedFitting.subgroup X) .POmegaOdd 3 p n ∧ NoProperPair X R₁ R₂ := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  have hL' := hL
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, hm, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p'.Prime := ⟨hp⟩
    have : CharP K p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p']; exact hp2'
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hker₀ := oKer_coordinateOdd hmod K hKc e
    have hsurj₀ := oSurj_coordinateOdd hmod K hKc e
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd m K)
      (regular_coordinateQuadOdd m K h2 hm).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * m + 1)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadOdd m K v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hout := (CatalogueBOrthogonalPointSchreier.orthogonal_geometry_classical_model_Schreier
      .POmegaOdd (Or.inl rfl) hmod).2.2
    obtain ⟨hd7, hcard, hno⟩ := orth_odd_propC hK hp hf hKc (by omega) ⟨m, rfl⟩ hR
      (hker₀.transport 1 1 hS₁) (hsurj₀.transport 1 1 hS₁) hsimple hnab hout
      ((coordinateOddWitnessEquiv K e).trans (oTransport 1 1 hS₁)) hC
    refine ⟨?_, hno⟩
    have hm3 : m = 3 := by omega
    obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hp (Fact.out : p.Prime) (by omega) hC.n_pos.ne'
      (hKc.symm.trans hcard)
    subst hm3
    exact hL'
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

theorem burgoynePropC_POmegaPlus (hX : IsM4 X) {m p' f' : ℕ} (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaPlus m p' f') {r : X}
    {R₁ R₂ : Subgroup X} {p n : ℕ} [Fact p.Prime] (hC : PropCData r R₁ R₂ p n) : False := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, hm⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p'.Prime := ⟨hp⟩
    have : CharP K p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p']; exact hp2'
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus m K)
      (regular_coordinateQuadPlus m K (by omega)).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * m)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadPlus m K v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hout := (CatalogueBOrthogonalPointSchreier.orthogonal_geometry_classical_model_Schreier
      .POmegaPlus (Or.inr (Or.inl rfl)) hmod).2.2
    obtain ⟨x, R₁', R₂', hC', -⟩ := exists_propCData_of_socle hsimple hnab hout
      ((coordinatePlusWitnessEquiv K e).trans (oTransport 1 1 hS₁)) hC.orderOf_eq hC.le₁
      hC.comp₁ hC.le₂ hC.comp₂ hC.p_ne_two hC.n_pos hC.iso₁ hC.iso₂ hC.mem
    exact orth_propC_even hK hp hKc hm hR hC'
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

theorem burgoynePropC_POmegaMinus (hX : IsM4 X) {m p' f' : ℕ} (hp2' : p' ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaMinus m p' f') {r : X}
    {R₁ R₂ : Subgroup X} {p n : ℕ} [Fact p.Prime] (hC : PropCData r R₁ R₂ p n) : False := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, hm⟩, K, _, _, hKc, b, c, hirr, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p'.Prime := ⟨hp⟩
    have : CharP K p' := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p']; exact hp2'
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hm1 : 1 ≤ m := by omega
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus m K hm1 b c)
      (regular_coordinateQuadMinus m K b c hm hirr).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * m)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadMinus m K hm1 b c v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hout := (CatalogueBOrthogonalPointSchreier.orthogonal_geometry_classical_model_Schreier
      .POmegaMinus (Or.inr (Or.inr rfl)) hmod).2.2
    obtain ⟨x, R₁', R₂', hC', -⟩ := exists_propCData_of_socle hsimple hnab hout
      ((coordinateMinusWitnessEquiv K hm1 b c e).trans (oTransport 1 1 hS₁)) hC.orderOf_eq hC.le₁
      hC.comp₁ hC.le₂ hC.comp₂ hC.p_ne_two hC.n_pos hC.iso₁ hC.iso₂ hC.mem
    exact orth_propC_even hK hp hKc hm hR hC'
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end Tags

end CFSG.ComponentClassification.Burgoyne.C
