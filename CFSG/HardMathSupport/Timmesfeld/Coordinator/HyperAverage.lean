module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open Module TensorProduct CFSG.RankThree.Classical

section Kernels

variable {Γ : Type*} [Group Γ] {p : ℕ}

theorem card_eq_prime_mul_natCard_charKer [Finite Γ] (hp : p.Prime)
    {χ : Additive Γ →+ ZMod p} (hχ : χ ≠ 0) : Nat.card Γ = p * Nat.card (charKer χ) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (Additive Γ) := Finite.of_equiv Γ Additive.ofMul
  have hrange : Nat.card χ.range = p := by
    have hdvd : Nat.card χ.range ∣ p :=
      (AddSubgroup.card_addSubgroup_dvd_card _).trans (Nat.card_zmod p).dvd
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exfalso
      apply hχ
      have hbot : χ.range = ⊥ := AddSubgroup.eq_bot_of_card_eq _ h
      ext x
      have : χ x ∈ χ.range := ⟨x, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at this
      exact this
    · exact h
  have hiso := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange χ).toEquiv
  have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup χ.ker
  rw [hiso, hrange, Nat.card_congr Additive.toMul] at hmul
  rw [hmul]
  rfl

theorem eq_charKer_of_le [Finite Γ] (hp : p.Prime) {χ : Additive Γ →+ ZMod p} (hχ : χ ≠ 0)
    {F : Subgroup Γ} (hF : Nat.card Γ = p * Nat.card F) (hle : F ≤ charKer χ) :
    F = charKer χ := by
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  have h := card_eq_prime_mul_natCard_charKer hp hχ
  rw [hF] at h
  exact (Nat.eq_of_mul_eq_mul_left hp.pos h).symm

end Kernels

section Identity

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable {Γ : Type*} [CommGroup Γ] [Fintype Γ] {p : ℕ}

abbrev Hyper (p : ℕ) (Γ : Type*) [Group Γ] : Type _ :=
  {F : Subgroup Γ // Nat.card Γ = p * Nat.card F}

theorem natCast_card_subgroup_ne_zero {L : Type*} [Field L] (hp : p.Prime)
    (hexp : ∀ g : Γ, g ^ p = 1) (hpL : (p : L) ≠ 0) (D : Subgroup Γ) [Fintype D] :
    (Fintype.card D : L) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hG : IsPGroup p Γ := fun g => ⟨1, by rw [pow_one]; exact hexp g⟩
  obtain ⟨j, hj⟩ := (hG.to_subgroup D).exists_card_eq
  rw [← Nat.card_eq_fintype_card, hj, Nat.cast_pow]
  exact pow_ne_zero j hpL

open _root_.Classical in
theorem sum_avgOp_hyper_apply_of_mem_charSpace (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1)
    {L : Type} [Field L] [Algebra K L] (hpL : (p : L) ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (ρ : Γ →* Module.End K V) {χ : Additive Γ →+ ZMod p} {v : L ⊗[K] V}
    (hv : v ∈ charSpace (bcRepOf L ρ) ζ χ) :
    (∑ F : Hyper p Γ, avgOp (bcRepOf L ρ) F.1) v =
      v + ((Fintype.card (Hyper p Γ) : L) - 1) • avgOp (bcRepOf L ρ) ⊤ v := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hD : ∀ D : Subgroup Γ, (Fintype.card D : L) ≠ 0 := fun D =>
    natCast_card_subgroup_ne_zero hp hexp hpL D
  rw [LinearMap.sum_apply, avgOp_apply_of_mem_charSpace hζ ⊤ (hD ⊤) hv]
  simp_rw [fun F : Hyper p Γ => avgOp_apply_of_mem_charSpace hζ F.1 (hD F.1) hv]
  by_cases hχ : χ = 0
  · subst hχ
    have hle : ∀ D : Subgroup Γ, D ≤ charKer (0 : Additive Γ →+ ZMod p) := fun D x _ =>
      AddMonoidHom.zero_apply _
    simp only [hle, ite_true, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul L]
    module
  · have htop : ¬ (⊤ : Subgroup Γ) ≤ charKer χ := fun h => hχ (top_le_charKer_iff.mp h)
    rw [ite_eq_right_iff.mpr (fun h => absurd h htop), smul_zero, add_zero]
    have hker : Nat.card Γ = p * Nat.card (charKer χ) := card_eq_prime_mul_natCard_charKer hp hχ
    rw [Finset.sum_eq_single (⟨charKer χ, hker⟩ : Hyper p Γ)]
    · simp only [le_refl, ↓reduceIte]
    · intro F _ hF
      have hle : ¬ F.1 ≤ charKer χ := fun hle => hF (Subtype.ext (eq_charKer_of_le hp hχ F.2 hle))
      simp only [hle, ↓reduceIte]
    · intro h
      exact absurd (Finset.mem_univ _) h

open _root_.Classical in
theorem sum_avgOp_hyper (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1) (hpK : (p : K) ≠ 0)
    (ρ : Γ →* Module.End K V) :
    ∑ F : Hyper p Γ, avgOp ρ F.1 = 1 + ((Fintype.card (Hyper p Γ) : K) - 1) • avgOp ρ ⊤ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpL : (p : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K))]
    exact (map_ne_zero _).mpr hpK
  have : NeZero (p : K) := ⟨hpK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  have : Finite (Additive Γ →+ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
  have : Fintype (Additive Γ →+ ZMod p) := Fintype.ofFinite _
  have hΓL : (Fintype.card Γ : AlgebraicClosure K) ≠ 0 := by
    have h := natCast_card_subgroup_ne_zero hp hexp hpL (⊤ : Subgroup Γ)
    rwa [← Nat.card_eq_fintype_card, Subgroup.card_top, Nat.card_eq_fintype_card] at h
  apply eq_of_baseChange_eq (AlgebraicClosure K)
  have hl : (∑ F : Hyper p Γ, avgOp ρ F.1).baseChange (AlgebraicClosure K) =
      ∑ F : Hyper p Γ, avgOp (bcRepOf (AlgebraicClosure K) ρ) F.1 := by
    have h := map_sum (LinearMap.baseChangeHom K (AlgebraicClosure K) V V)
      (fun F : Hyper p Γ => avgOp ρ F.1) Finset.univ
    exact h.trans (Finset.sum_congr rfl fun F _ => avgOp_baseChange (AlgebraicClosure K) F.1)
  have hr : (1 + ((Fintype.card (Hyper p Γ) : K) - 1) • avgOp ρ ⊤).baseChange
      (AlgebraicClosure K) = 1 + ((Fintype.card (Hyper p Γ) : AlgebraicClosure K) - 1) •
        avgOp (bcRepOf (AlgebraicClosure K) ρ) ⊤ := by
    rw [LinearMap.baseChange_add, LinearMap.baseChange_smul, avgOp_baseChange,
      ← algebraMap_smul (AlgebraicClosure K), map_sub, map_natCast, map_one]
    congr 1
    exact LinearMap.baseChange_id
  rw [hl, hr]
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ ⨆ χ : Additive Γ →+ ZMod p, charSpace (bcRepOf (AlgebraicClosure K) ρ) ζ χ := by
    rw [iSup_charSpace_eq_top hp hζ hexp hΓL]
    trivial
  refine Submodule.iSup_induction _ (motive := fun v =>
    (∑ F : Hyper p Γ, avgOp (bcRepOf (AlgebraicClosure K) ρ) F.1) v =
      (1 + ((Fintype.card (Hyper p Γ) : AlgebraicClosure K) - 1) •
        avgOp (bcRepOf (AlgebraicClosure K) ρ) ⊤) v) hv ?_ ?_ ?_
  · intro χ w hw
    rw [sum_avgOp_hyper_apply_of_mem_charSpace hp hexp hpL hζ ρ hw]
    rfl
  · simp
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

open _root_.Classical in
theorem eq_sum_avgOp_hyper_apply (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1) (hpK : (p : K) ≠ 0)
    (ρ : Γ →* Module.End K V) (v : V) :
    v = ∑ F : Hyper p Γ, avgOp ρ F.1 v -
      ((Fintype.card (Hyper p Γ) : K) - 1) • avgOp ρ ⊤ v := by
  have h := LinearMap.congr_fun (sum_avgOp_hyper hp hexp hpK ρ) v
  rw [LinearMap.sum_apply] at h
  rw [h, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, add_sub_cancel_right]

end Identity

end CFSG.HardMathSupport.Timmesfeld.Coordinator
