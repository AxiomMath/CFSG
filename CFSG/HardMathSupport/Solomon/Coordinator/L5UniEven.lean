module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5UniFix
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Torus

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LocalTwo.Torus
  CFSG.HardMathSupport.Solomon.Proving CFSG.HardMathSupport.Timmesfeld.CrossChar Subgroup

section Heis

variable {p : ℕ} {S : Type*} [Group S] {K : Type*} [Field K] {M : Type*} [Group M]

theorem exists_heis_of_model (hp : p.Prime)
    (ι : M →* GL (Fin p) K) (hι : Function.Injective ι) (ρ : M →* MulAut S)
    (hker : ∀ g : M, ρ g = 1 → ∃ c : Kˣ, ι g = GeneralLinearGroup.scalar (Fin p) c)
    (hplane : ∀ A B : M, A * B = B * A → ρ A ^ p = 1 → ρ B ^ p = 1 → ρ A ≠ 1 →
      ρ B ∉ zpowers (ρ A) → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
        closure {ρ A, ρ B} ≤ normalizer (H : Set (MulAut S)) →
          localDeltaIn p H (closure {ρ A, ρ B}) = ⊥)
    (houter : ∀ D : Subgroup (MulAut S), IsElemAbelian p D → ¬ D ≤ ρ.range →
      ∀ H : Subgroup (MulAut S), innerAut S ≤ H → localDeltaIn p H D = ⊥)
    {D : Subgroup (MulAut S)} (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2)
    {H : Subgroup (MulAut S)} (hH : innerAut S ≤ H) (hDH : D ≤ normalizer (H : Set (MulAut S)))
    (hΔ : localDeltaIn p H D ≠ ⊥) :
    ∃ (A B : M) (ω : Kˣ), ρ A ∈ D ∧ ρ B ∈ D ∧ ρ A ^ p = 1 ∧ ρ B ^ p = 1 ∧ ω ≠ 1 ∧
      ι A * ι B * (ι A)⁻¹ * (ι B)⁻¹ = GeneralLinearGroup.scalar (Fin p) ω := by
  classical
  have hDr : D ≤ ρ.range := by
    by_contra h
    exact hΔ (houter D hD h H hH)
  obtain ⟨x, hx, y, hy, hx1, hyx, hgen⟩ := exists_gen_pair hp hD hcard
  obtain ⟨A0, rfl⟩ := MonoidHom.mem_range.1 (hDr hx)
  obtain ⟨B0, rfl⟩ := MonoidHom.mem_range.1 (hDr hy)
  have hxy : ρ A0 * ρ B0 = ρ B0 * ρ A0 :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  obtain ⟨z, hz⟩ := hker (A0 * B0 * A0⁻¹ * B0⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy]; group)
  simp only [map_mul, map_inv] at hz
  refine ⟨A0, B0, z, hx, hy, hD.2 _ hx, hD.2 _ hy, fun hz1 => hΔ ?_, hz⟩
  have hAB : A0 * B0 = B0 * A0 := by
    apply hι
    rw [hz1, map_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hz
    rw [map_mul, map_mul]
    exact hz
  rw [← hgen]
  exact hplane A0 B0 hAB (hD.2 _ hx) (hD.2 _ hy) hx1 hyx H hH (hgen ▸ hDH)

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem exists_heis_primeFormP (h5 : 5 ∣ ℓ ^ f + 1)
    {D : Subgroup (MulAut (primeFormP h (idGram K 5)))} (hD : IsElemAbelian 5 D)
    (hcard : Nat.card D = 5 ^ 2) {H : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hH : innerAut (primeFormP h (idGram K 5)) ≤ H)
    (hDH : D ≤ normalizer (H : Set (MulAut (primeFormP h (idGram K 5)))))
    (hΔ : localDeltaIn 5 H D ≠ ⊥) :
    ∃ (A B : primeFormUnitary h (idGram K 5)) (ω : Kˣ),
      primeFormConjHom h (idGram K 5) A ∈ D ∧ primeFormConjHom h (idGram K 5) B ∈ D ∧
      primeFormConjHom h (idGram K 5) A ^ 5 = 1 ∧ primeFormConjHom h (idGram K 5) B ^ 5 = 1 ∧
      ω ≠ 1 ∧ (A : GL (Fin 5) K) * B * (A : GL (Fin 5) K)⁻¹ * (B : GL (Fin 5) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 5) ω := by
  have := h.finite
  have hp : Nat.Prime 5 := Nat.prime_five
  have hn : 3 ≤ 5 := by norm_num
  have hne : ¬(5 = 3 ∧ ℓ ^ f = 2) := by omega
  have hq3 := three_lt_of_dvd_add_one h hp (by norm_num) hne h5
  exact exists_heis_of_model hp (primeFormUnitary h (idGram K 5)).subtype
    (Subgroup.subtype_injective _) (primeFormConjHom h (idGram K 5))
    (fun g hg => by
      obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne g).1 hg
      exact ⟨c, hc⟩)
    (fun A B hAB hAp hBp hA1 hBA H hH _ =>
      localDeltaIn_eq_bot_of_unitary_plane hn hne hq3 hp (by norm_num) h5 hAB hAp hBp hA1 hBA hH)
    (fun D hD hDl H hH => localDeltaIn_eq_bot_of_not_le_primeFormD h hn hne hp (by norm_num) h5
      (by omega) hD hDl hH)
    hD hcard hH hDH hΔ

end Heis

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
variable {Lb : Type*} [Group Lb] [Finite Lb] {Γ : Lb →* primeFormP h (idGram K 5)}

theorem hasTorus_three_primeFormP_five (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb)))
    (h5 : 5 ∣ ℓ ^ f + 1) : HasTorus 5 3 Lb 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := h.finite
  obtain ⟨ζ, hζ, hζb⟩ := exists_primitiveRoot_five_norm h h5
  have hd : ∀ k : Fin 3, (0 : Fin 5) ≠ ![1, 2, 3] k := by decide
  obtain ⟨D, hcard, -, -⟩ := exists_torusData_star hζ (gramSU h (idGram K 5)).subtype
    (Subgroup.subtype_injective _) (uniProj h 5) (uniProj_ker_scalar h) 0 4 ![1, 2, 3]
    (by decide) hd (by decide) (by decide)
    (fun k => mem_range_gramSU h (tvec_mem_unitary h hζb _ _) (det_starX ζ hd k))
    (fun k => mem_range_gramSU h (sgnSwap_mem_unitary h _ _) (det_starSw hd k))
  exact hasTorus_of_torusData Nat.prime_five hΓ hker hodd D hcard

theorem hasTorus_three_primeFormP_five_fix (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb)))
    (h5 : 5 ∣ ℓ ^ f + 1) {β : MulAut Lb} {b : MulAut (primeFormP h (idGram K 5))}
    (hβ : ∀ x, Γ (β x) = b (Γ x)) (hbD : b ∉ primeFormD h (idGram K 5)) (hb5 : b ^ 5 = 1) :
    HasTorus 5 3 Lb β := by
  obtain ⟨M, σ, ζ, hM, hζ, hζb, hζσ, -⟩ := exists_descent_primeFormP_five h h5 hbD hb5
  obtain ⟨D, hcard, -, -⟩ := exists_fixTorus_primeFormP_five h hΓ hker hodd hβ hM hζ hζb hζσ
  exact hasTorus_of_fixData Nat.prime_five hker hodd β D hcard

end CFSG.HardMathSupport.Solomon.Coordinator
