module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6CartanRankFour
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318LocalU
public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Local
  CFSG.HardMathSupport.Dickson.I271
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Gen2318LocalExcAux

theorem hsec_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : ∀ (E : Type) [Group E] [Finite E] (p : E →* G), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : G →* E, ∀ g, p (s g) = g) :
    ∀ (E : Type) [Group E] [Finite E] (p : E →* G'), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : G' →* E, ∀ g, p (s g) = g := by
  intro E _ _ p hp hk
  let p' : E →* G := e.symm.toMonoidHom.comp p
  have hp' : Function.Surjective p' := e.symm.surjective.comp hp
  have hk' : p'.ker ≤ Subgroup.center E := by
    intro x hx
    apply hk
    rw [MonoidHom.mem_ker] at hx ⊢
    exact e.symm.injective (hx.trans (map_one e.symm).symm)
  obtain ⟨s, hs⟩ := h E p' hp' hk'
  refine ⟨s.comp e.symm.toMonoidHom, fun g => ?_⟩
  have := hs (e.symm g)
  exact e.symm.injective this

theorem lift_witness {K G : Type} [Group K] [Finite K] [Group G] [Finite G]
    (hsec : ∀ (E : Type) [Group E] [Finite E] (p : E →* G), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : G →* E, ∀ g, p (s g) = g)
    (ρ : K →* G) (hρ : Function.Surjective ρ) (hρk : ρ.ker = Subgroup.center K)
    {k : ℕ} {E₀ P₀ : Subgroup G} (hE : IsElemAbelian 3 E₀) (hEc : Nat.card E₀ = 3 ^ k)
    (hP0 : P₀ ≠ ⊥) (hP2 : IsPGroup 2 ↥P₀) (hEN : E₀ ≤ Subgroup.normalizer (P₀ : Set G)) :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
      k ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧ E ≤ Subgroup.normalizer (P : Set K) := by
  obtain ⟨σ, hσ⟩ := Gen2318LocalAux.exists_lift_gen hsec ρ hρ hρk.le (MonoidHom.id G)
  have hσ' : ∀ g, ρ (σ g) = g := hσ
  have hinj : Function.Injective σ := fun a b h => by
    have := congrArg ρ h
    rwa [hσ', hσ'] at this
  have hE' : IsElemAbelian 3 (E₀.map σ) := CartanConjAux.isElemAbelian_map σ hE
  have hcard : Nat.card (E₀.map σ) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hEc
  refine ⟨E₀.map σ, P₀.map σ, hE', ?_, le_of_eq (i271_pRank_eq Nat.prime_three hE' hcard).symm,
    fun h => hP0 ((Subgroup.map_eq_bot_iff_of_injective P₀ hinj).1 h), hP2.map σ,
    (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map σ)⟩
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxZ⟩
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hxE
  have h1 : ρ (σ y) = 1 := by
    rw [← hρk] at hxZ
    exact MonoidHom.mem_ker.1 hxZ
  rw [hσ'] at h1
  rw [h1, map_one]
  exact Subgroup.one_mem _

theorem exists_rho {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeEven τ c) {q : TauCeti.PrimePower}
    (hv : (c q).Valid) (hq : q.p = 2) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = TauCeti.PrimePower.card q) (hZ : Subgroup.center ↥(adjointGroup τ F) = ⊥)
    {K : Type} [Group K]
    (e : K ⧸ Subgroup.center K ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    ∃ ρ : K →* ↥(adjointGroup τ F), Function.Surjective ρ ∧ ρ.ker = Subgroup.center K := by
  obtain ⟨ψ0⟩ := hB q hv hq F hF
  let ψ := e.trans ψ0.symm
  let eZ : AdjointQuotient τ F ≃* ↥(adjointGroup τ F) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let ρ : K →* ↥(adjointGroup τ F) :=
    eZ.toMonoidHom.comp (ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
  refine ⟨ρ, eZ.surjective.comp (ψ.surjective.comp (QuotientGroup.mk'_surjective _)), ?_⟩
  ext x
  rw [MonoidHom.mem_ker]
  change eZ (ψ (QuotientGroup.mk x)) = 1 ↔ x ∈ Subgroup.center K
  rw [map_eq_one_iff eZ eZ.injective, map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff]

theorem residual_of_data {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeEven τ c)
    (hZ : ∀ (F : Type) [Field F] [Finite F], Subgroup.center ↥(adjointGroup τ F) = ⊥)
    (hFin : ∀ (F : Type) [Field F] [Finite F], Finite ↥(adjointGroup τ F))
    (hsec : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], (Nat.card F = 2 ∨ Nat.card F = 8) →
      ∀ (E : Type) [Group E] [Finite E] (p : E →* ↥(adjointGroup τ F)), Function.Surjective p →
        p.ker ≤ Subgroup.center E → ∃ s : ↥(adjointGroup τ F) →* E, ∀ g, p (s g) = g)
    {k : ℕ} (hW : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      ∃ E U : Subgroup ↥(adjointGroup τ F), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k ∧ U ≠ ⊥ ∧
        IsPGroup 2 ↥U ∧ E ≤ Subgroup.normalizer (U : Set ↥(adjointGroup τ F)))
    {K : Type} [Group K] [Finite K] {q : TauCeti.PrimePower} (hv : (c q).Valid) (hq1 : q.p = 2)
    (hq : q.exponent = 1 ∨ q.exponent = 3)
    (e : K ⧸ Subgroup.center K ≃* TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
      k ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧ E ≤ Subgroup.normalizer (P : Set K) := by
  have hFc : Nat.card (GaloisField 2 q.exponent) = TauCeti.PrimePower.card q := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card 2 q.exponent q.exponent_pos.ne', hq1]
  haveI : Finite ↥(adjointGroup τ (GaloisField 2 q.exponent)) := hFin _
  obtain ⟨ρ, hρ, hρk⟩ := exists_rho hB hv hq1 hFc (hZ _) e
  have hF8 : Nat.card (GaloisField 2 q.exponent) = 2 ∨ Nat.card (GaloisField 2 q.exponent) = 8 := by
    rw [GaloisField.card 2 q.exponent q.exponent_pos.ne']
    rcases hq with h | h <;> rw [h] <;> norm_num
  obtain ⟨E₀, U, hE, hEc, hU0, hU2, hEN⟩ := hW (GaloisField 2 q.exponent)
  exact lift_witness (hsec _ hF8) ρ hρ hρk hE hEc hU0 hU2 hEN

section Fin


theorem finite_adjointGroup {τ : Tag} {F : Type} [Field F] [Finite F] :
    Finite ↥(adjointGroup τ F) := by
  have : Finite (Module.End F (RootModule τ F)) := Module.finite_of_finite F
  infer_instance

end Fin

section E8

set_option linter.unusedSectionVars false

open CFSG.LieType.Steinberg.CentralExt


@[expose] def e8D6Roots : Fin 6 → Fin 8 → ℤ :=
  ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 1, 2, 2, 2, 1, 0]]

@[expose] def e8Nodes : Finset (Fin 8) := {1, 2, 3, 4, 5, 6, 7}

theorem e8D6Roots_check : E6CartanRankFourAux.StronglyOrthogonalCheck Tag.E8 e8D6Roots := by
  unfold E6CartanRankFourAux.StronglyOrthogonalCheck
  decide +kernel

theorem e8D6Roots_supp : ∀ i j, j ∉ e8Nodes → e8D6Roots i j = 0 := by
  decide +kernel

theorem e8Nodes_not_mem : (0 : Fin 8) ∉ e8Nodes := by
  decide +kernel

theorem e8_beta_pos : 0 < (Pi.single (0 : Fin 8) 1 : Fin 8 → ℤ) 0 := by
  simp

theorem e8_beta_isRoot : IsRoot Tag.E8 (Pi.single (0 : Fin 8) 1 : Fin 8 → ℤ) :=
  isRoot_single Tag.E8 (0 : Fin 8)

theorem e8_cartan {F : Type} [Field F] [Finite F] [CharP F 2] :
    ∃ E U : Subgroup ↥(adjointGroup Tag.E8 F), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 ∧ U ≠ ⊥ ∧
      IsPGroup 2 ↥U ∧ E ≤ Subgroup.normalizer (U : Set ↥(adjointGroup Tag.E8 F)) :=
  E6CartanRankFourAux.exists_cartan_generic (K := F) (Or.inr (Or.inr (Or.inr rfl))) e8D6Roots
    e8D6Roots_check e8D6Roots_supp (β := (Pi.single (0 : Fin 8) 1 : Fin 8 → ℤ)) e8_beta_isRoot
    (j₀ := (0 : Fin 8)) e8Nodes_not_mem e8_beta_pos

theorem e8_hsec {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ∨ Nat.card F = 8) :
    ∀ (E : Type) [Group E] [Finite E] (p : E →* ↥(adjointGroup Tag.E8 F)), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : ↥(adjointGroup Tag.E8 F) →* E, ∀ g, p (s g) = g := by
  intro E _ _ p hp hk
  rcases hF with h | h
  · exact FieldTwo.e8_two_exists_section h E p hp hk
  · exact AdjointClosed.e8_exists_section_of_central (by rw [h]; norm_num) hp hk

end E8

section E7

set_option linter.unusedSectionVars false

open CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule


@[expose] def e7D6Roots : Fin 6 → Fin 7 → ℤ :=
  ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0],
    ![0, 1, 1, 2, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 2, 2, 2, 1]]

@[expose] def e7Nodes : Finset (Fin 7) := {1, 2, 3, 4, 5, 6}

theorem e7D6Roots_check : E6CartanRankFourAux.StronglyOrthogonalCheck Tag.E7 e7D6Roots := by
  unfold E6CartanRankFourAux.StronglyOrthogonalCheck
  decide +kernel

theorem e7D6Roots_supp : ∀ i j, j ∉ e7Nodes → e7D6Roots i j = 0 := by
  decide +kernel

theorem e7Nodes_not_mem : (0 : Fin 7) ∉ e7Nodes := by
  decide +kernel

theorem e7_beta_pos : 0 < (Pi.single (0 : Fin 7) 1 : Fin 7 → ℤ) 0 := by
  simp

theorem e7_beta_isRoot : IsRoot Tag.E7 (Pi.single (0 : Fin 7) 1 : Fin 7 → ℤ) :=
  isRoot_single Tag.E7 (0 : Fin 7)

theorem e7_cartan {F : Type} [Field F] [Finite F] [CharP F 2] :
    ∃ E U : Subgroup ↥(adjointGroup Tag.E7 F), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 ∧ U ≠ ⊥ ∧
      IsPGroup 2 ↥U ∧ E ≤ Subgroup.normalizer (U : Set ↥(adjointGroup Tag.E7 F)) :=
  E6CartanRankFourAux.exists_cartan_generic (K := F) (Or.inr (Or.inr (Or.inl rfl))) e7D6Roots
    e7D6Roots_check e7D6Roots_supp (β := (Pi.single (0 : Fin 7) 1 : Fin 7 → ℤ)) e7_beta_isRoot
    (j₀ := (0 : Fin 7)) e7Nodes_not_mem e7_beta_pos

theorem e7_hsec {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ∨ Nat.card F = 8) :
    ∀ (E : Type) [Group E] [Finite E] (p : E →* ↥(adjointGroup Tag.E7 F)), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : ↥(adjointGroup Tag.E7 F) →* E, ∀ g, p (s g) = g := by
  have hZ : Subgroup.center ↥(e7Data_valid.minGroup F) = ⊥ := by
    have h1 := (MinusculeClosed.card_center_e7 F).1
    have h2 : Nat.gcd 2 (Nat.card F - 1) = 1 := by
      rcases hF with h | h <;> rw [h] <;> norm_num
    rw [h2] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hinj : Function.Injective (e7Isogeny F) := by
    rw [← MonoidHom.ker_eq_bot_iff, FieldFour.e7Isogeny_ker_eq_center, hZ]
  refine Gen2318LocalExcAux.hsec_of_mulEquiv
    (MulEquiv.ofBijective (e7Isogeny F) ⟨hinj, e7Isogeny_surjective F⟩) ?_
  intro E _ _ p hp hk
  rcases hF with h | h
  · exact FieldTwo.e7_two_exists_section h E p hp hk
  · exact MinusculeClosed.e7_exists_section_of_central (by rw [h]; norm_num) hp hk

end E7

section E6

set_option linter.unusedSectionVars false

open CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule


theorem e6_cartan {F : Type} [Field F] [Finite F] [CharP F 2] :
    ∃ E U : Subgroup ↥(adjointGroup Tag.E6 F), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ U ≠ ⊥ ∧
      IsPGroup 2 ↥U ∧ E ≤ Subgroup.normalizer (U : Set ↥(adjointGroup Tag.E6 F)) :=
  E6CartanRankFourAux.exists_cartan_generic (K := F) (Or.inr (Or.inl rfl))
    E6CartanRankFourAux.e6D4Roots E6CartanRankFourAux.e6D4Roots_check
    E6CartanRankFourAux.e6D4Roots_supp
    (β := (Pi.single (0 : Fin 6) 1 : Fin 6 → ℤ)) E6CartanRankFourAux.e6_beta_isRoot
    (j₀ := (0 : Fin 6)) E6CartanRankFourAux.e6D4Nodes_not_mem E6CartanRankFourAux.e6_beta_pos

theorem e6_hsec {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ∨ Nat.card F = 8) :
    ∀ (E : Type) [Group E] [Finite E] (p : E →* ↥(adjointGroup Tag.E6 F)), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : ↥(adjointGroup Tag.E6 F) →* E, ∀ g, p (s g) = g := by
  have hZ : Subgroup.center ↥(e6Data_valid.minGroup F) = ⊥ := by
    have h1 := (MinusculeClosed.card_center_e6 F).1
    have h2 : Nat.gcd 3 (Nat.card F - 1) = 1 := by
      rcases hF with h | h <;> rw [h] <;> norm_num
    rw [h2] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hinj : Function.Injective (e6Isogeny F) := by
    rw [← MonoidHom.ker_eq_bot_iff, FieldFour.e6Isogeny_ker_eq_center, hZ]
  refine Gen2318LocalExcAux.hsec_of_mulEquiv
    (MulEquiv.ofBijective (e6Isogeny F) ⟨hinj, e6Isogeny_surjective F⟩) ?_
  intro E _ _ p hp hk
  rcases hF with h | h
  · exact FieldTwo.e6_two_exists_section h E p hp hk
  · exact MinusculeClosed.e6_exists_section_of_central (by rw [h]; norm_num) hp hk

end E6

end Gen2318LocalExcAux

section Main

set_option linter.unusedSectionVars false


theorem gen2318Residual_E8odd :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
      Gen2318Index d.1 → (∃ q, d.1 = TauCeti.LieTypeIndex.E8 q ∧ (IsTwoPow q 1 ∨ IsTwoPow q 3)) →
        Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
            rho2318 d.1 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧
            E ≤ Subgroup.normalizer (P : Set K) := by
  intro K _ _ _hq d _hd hE hiso
  obtain ⟨q, hdq, hqq⟩ := hE
  obtain ⟨idx, hv⟩ := d
  obtain ⟨e⟩ := hiso
  have hdq' : idx = TauCeti.LieTypeIndex.E8 q := hdq
  subst hdq'
  have hq1 : q.p = 2 := by rcases hqq with h | h <;> exact h.1
  have hq : q.exponent = 1 ∨ q.exponent = 3 := by
    rcases hqq with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  obtain ⟨E, P, h1, h2, h3, h4, h5, h6⟩ :=
    Gen2318LocalExcAux.residual_of_data (τ := Tag.E8) (c := TauCeti.LieTypeIndex.E8)
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 (fun F _ _ => center_adjointGroup_eq_bot)
      (fun F _ _ => Gen2318LocalExcAux.finite_adjointGroup)
      (fun F _ _ _ hF => Gen2318LocalExcAux.e8_hsec hF) (k := 6)
      (fun F _ _ _ => Gen2318LocalExcAux.e8_cartan) hv hq1 hq e
  have hrk : rho2318 (⟨TauCeti.LieTypeIndex.E8 q, hv⟩ : TauCeti.ValidLieTypeIndex).1 = 6 := rfl
  exact ⟨E, P, h1, h2, hrk.le.trans h3, h4, h5, h6⟩

end Main

section MainE7

set_option linter.unusedSectionVars false


theorem gen2318Residual_E7odd :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
      Gen2318Index d.1 → (∃ q, d.1 = TauCeti.LieTypeIndex.E7 q ∧ (IsTwoPow q 1 ∨ IsTwoPow q 3)) →
        Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
            rho2318 d.1 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧
            E ≤ Subgroup.normalizer (P : Set K) := by
  intro K _ _ _hq d _hd hE hiso
  obtain ⟨q, hdq, hqq⟩ := hE
  obtain ⟨idx, hv⟩ := d
  obtain ⟨e⟩ := hiso
  have hdq' : idx = TauCeti.LieTypeIndex.E7 q := hdq
  subst hdq'
  have hq1 : q.p = 2 := by rcases hqq with h | h <;> exact h.1
  have hq : q.exponent = 1 ∨ q.exponent = 3 := by
    rcases hqq with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  obtain ⟨E, P, h1, h2, h3, h4, h5, h6⟩ :=
    Gen2318LocalExcAux.residual_of_data (τ := Tag.E7) (c := TauCeti.LieTypeIndex.E7)
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 (fun F _ _ => center_adjointGroup_eq_bot)
      (fun F _ _ => Gen2318LocalExcAux.finite_adjointGroup)
      (fun F _ _ _ hF => Gen2318LocalExcAux.e7_hsec hF) (k := 6)
      (fun F _ _ _ => Gen2318LocalExcAux.e7_cartan) hv hq1 hq e
  have hrk : rho2318 (⟨TauCeti.LieTypeIndex.E7 q, hv⟩ : TauCeti.ValidLieTypeIndex).1 = 6 := rfl
  exact ⟨E, P, h1, h2, hrk.le.trans h3, h4, h5, h6⟩

end MainE7

section MainE6

set_option linter.unusedSectionVars false


theorem gen2318Residual_E6odd :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
      Gen2318Index d.1 → (∃ q, d.1 = TauCeti.LieTypeIndex.E6 q ∧ (IsTwoPow q 1 ∨ IsTwoPow q 3)) →
        Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
            rho2318 d.1 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧
            E ≤ Subgroup.normalizer (P : Set K) := by
  intro K _ _ _hq d _hd hE hiso
  obtain ⟨q, hdq, hqq⟩ := hE
  obtain ⟨idx, hv⟩ := d
  obtain ⟨e⟩ := hiso
  have hdq' : idx = TauCeti.LieTypeIndex.E6 q := hdq
  subst hdq'
  have hq1 : q.p = 2 := by rcases hqq with h | h <;> exact h.1
  have hq : q.exponent = 1 ∨ q.exponent = 3 := by
    rcases hqq with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  obtain ⟨E, P, h1, h2, h3, h4, h5, h6⟩ :=
    Gen2318LocalExcAux.residual_of_data (τ := Tag.E6) (c := TauCeti.LieTypeIndex.E6)
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 (fun F _ _ => center_adjointGroup_eq_bot)
      (fun F _ _ => Gen2318LocalExcAux.finite_adjointGroup)
      (fun F _ _ _ hF => Gen2318LocalExcAux.e6_hsec hF) (k := 4)
      (fun F _ _ _ => Gen2318LocalExcAux.e6_cartan) hv hq1 hq e
  have hrk : rho2318 (⟨TauCeti.LieTypeIndex.E6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1 = 4 := by
    have h2 : ¬ (q.p = 2 ∧ q.exponent = 2) := by
      rintro ⟨-, h⟩
      rcases hq with h' | h' <;> omega
    simp [rho2318, h2]
  exact ⟨E, P, h1, h2, hrk.le.trans h3, h4, h5, h6⟩

end MainE6

section Assembly

set_option linter.unusedSectionVars false


theorem gen2318ResidualRest_holds : Gen2318ResidualRest := by
  intro K _ _ hq d hd hopen hnE6 hnU hiso
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | E6 q =>
    have hq' : IsTwoPow q 1 ∨ IsTwoPow q 3 := by
      rcases hd with h | h | h
      · exact Or.inl h
      · exact absurd ⟨q, rfl, h⟩ hnE6
      · exact Or.inr h
    exact gen2318Residual_E6odd K hq ⟨TauCeti.LieTypeIndex.E6 q, hv⟩ hd ⟨q, rfl, hq'⟩ hiso
  | E7 q => exact gen2318Residual_E7odd K hq ⟨TauCeti.LieTypeIndex.E7 q, hv⟩ hd ⟨q, rfl, hd⟩ hiso
  | E8 q =>
    have hq' : IsTwoPow q 1 ∨ IsTwoPow q 3 := by
      rcases hd with h | h | h
      · exact Or.inl h
      · exact absurd h hopen
      · exact Or.inr h
    exact gen2318Residual_E8odd K hq ⟨TauCeti.LieTypeIndex.E8 q, hv⟩ hd ⟨q, rfl, hq'⟩ hiso
  | twistedA r q => exact absurd ⟨r, q, rfl⟩ hnU
  | A r q => exact hopen.elim
  | B r q => exact hopen.elim
  | C r q => exact hopen.elim
  | D r q => exact hopen.elim
  | twistedD r q => exact hopen.elim
  | F4 q => exact hopen.elim
  | G2 q => exact hopen.elim
  | twistedE6 q => exact hopen.elim
  | trialityD4 q => exact hopen.elim
  | suzuki m => exact hopen.elim
  | reeG2 m => exact hopen.elim
  | reeF4 m => exact hopen.elim
  | tits => exact hopen.elim

end Assembly

section TwoLocal

set_option linter.unusedSectionVars false


theorem gen2318TwoLocal_holds : Gen2318TwoLocal :=
  Gen2318Local.gen2318TwoLocal_of_residual
    (gen2318Residual_of_noE64 (gen2318ResidualNoE64_of_rest gen2318ResidualRest_holds))

end TwoLocal

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
