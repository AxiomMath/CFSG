module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4ThreeD4
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Model
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Gen

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance.Q27
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Signs

variable {K : Type} [Field K]

@[expose] def toralSignsTD4 (K : Type) [Field K] : Set (Fin d4.rank → Kˣ) :=
  {aLongTD4 K, aShortTD4 K, aLongTD4 K * aShortTD4 K}

theorem rootChar_mul_td4 (a b : Fin d4.rank → Kˣ) (γ : Fin d4.rank → ℤ) :
    rootChar (a * b) γ = rootChar a γ * rootChar b γ := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_one_tuple (γ : Fin d4.rank → ℤ) : rootChar (1 : Fin d4.rank → Kˣ) γ = 1 := by
  simp [rootChar]

theorem rootChar_eq_one_or_neg_one {a : Fin d4.rank → Kˣ} (ha : a * a = 1)
    (γ : Fin d4.rank → ℤ) : rootChar a γ = 1 ∨ rootChar a γ = -1 := by
  have h : rootChar a γ ^ 2 = 1 := by
    rw [sq, ← rootChar_mul_td4, ha, rootChar_one_tuple]
  exact unit_eq_one_or_neg_one_of_sq_eq_one h

theorem rootChar_rho_of_invariant {a : Fin d4.rank → Kˣ} (ha : ∀ i, a (rhoPerm i) = a i)
    (γ : Fin d4.rank → ℤ) : rootChar a (rho γ) = rootChar a γ := by
  calc rootChar a (rho γ) = ∏ i, a i ^ γ (rhoPerm.symm i) := rfl
    _ = ∏ j, a (rhoPerm j) ^ γ (rhoPerm.symm (rhoPerm j)) :=
      (Equiv.prod_comp rhoPerm (fun i => a i ^ γ (rhoPerm.symm i))).symm
    _ = ∏ j, a j ^ γ j := by simp [ha]

theorem aLongTD4_invariant : ∀ i, aLongTD4 K (rhoPerm i) = aLongTD4 K i := by
  intro i
  change Fin 4 at i
  fin_cases i <;> rfl

theorem aShortTD4_invariant : ∀ i, aShortTD4 K (rhoPerm i) = aShortTD4 K i := by
  intro i
  change Fin 4 at i
  fin_cases i <;> rfl

theorem toralSignsTD4_invariant {a : Fin d4.rank → Kˣ} (ha : a ∈ toralSignsTD4 K) :
    ∀ i, a (rhoPerm i) = a i := by
  rcases ha with rfl | rfl | rfl
  · exact aLongTD4_invariant
  · exact aShortTD4_invariant
  · intro i
    rw [Pi.mul_apply, Pi.mul_apply, aLongTD4_invariant, aShortTD4_invariant]

theorem exists_sign_kernel (γ : Fin d4.rank → ℤ) :
    ∃ a ∈ toralSignsTD4 K, rootChar a γ = 1 := by
  rcases rootChar_eq_one_or_neg_one (aLongTD4_mul_self (K := K)) γ with h1 | h1
  · exact ⟨aLongTD4 K, Or.inl rfl, h1⟩
  · rcases rootChar_eq_one_or_neg_one (aShortTD4_mul_self (K := K)) γ with h2 | h2
    · exact ⟨aShortTD4 K, Or.inr (Or.inl rfl), h2⟩
    · refine ⟨aLongTD4 K * aShortTD4 K, Or.inr (Or.inr rfl), ?_⟩
      rw [rootChar_mul_td4, h1, h2]
      simp

theorem toralSignsTD4_cover {a b c : Fin d4.rank → Kˣ} (ha : a ∈ toralSignsTD4 K)
    (hb : b ∈ toralSignsTD4 K) (hc : c ∈ toralSignsTD4 K) (hab : a ≠ b) :
    c = a ∨ c = b ∨ c = a * b := by
  have hx : aLongTD4 K * aLongTD4 K = 1 := aLongTD4_mul_self
  have hy : aShortTD4 K * aShortTD4 K = 1 := aShortTD4_mul_self
  have h1 : aLongTD4 K * (aLongTD4 K * aShortTD4 K) = aShortTD4 K := by
    rw [← mul_assoc, hx, one_mul]
  have h2 : aShortTD4 K * (aLongTD4 K * aShortTD4 K) = aLongTD4 K := by
    rw [mul_comm (aLongTD4 K), ← mul_assoc, hy, one_mul]
  have h3 : aLongTD4 K * aShortTD4 K = aShortTD4 K * aLongTD4 K := mul_comm _ _
  have h4 : aLongTD4 K * aShortTD4 K * aLongTD4 K = aShortTD4 K := by
    rw [h3, mul_assoc, hx, mul_one]
  have h5 : aLongTD4 K * aShortTD4 K * aShortTD4 K = aLongTD4 K := by
    rw [mul_assoc, hy, mul_one]
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | exact Or.inr (Or.inr h3)
    | exact Or.inr (Or.inr h3.symm)
    | exact Or.inr (Or.inr (by rw [h1]))
    | exact Or.inr (Or.inr (by rw [h2]))
    | exact Or.inr (Or.inr (by rw [h3, h1]))
    | exact Or.inr (Or.inr (by rw [h4]))
    | exact Or.inr (Or.inr (by rw [h5]))

end Signs

section Centralize

variable {K : Type} [Field K]

theorem td4Orb_subset_rootCharKernel {a : Fin d4.rank → Kˣ} (ha : ∀ i, a (rhoPerm i) = a i)
    {α₀ : Fin d4.rank → ℤ} (hα₀ : IsRoot d4 α₀) (h1 : rootChar a α₀ = 1) :
    td4Orb α₀ ⊆ rootCharKernel a := by
  intro δ hδ
  refine ⟨isRoot_of_mem_td4Orb hα₀ hδ, ?_⟩
  simp only [td4Orb, Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
  rcases hδ with rfl | rfl | rfl
  · exact h1
  · rw [rootChar_rho_of_invariant ha, h1]
  · rw [rootChar_rho_of_invariant ha, rootChar_rho_of_invariant ha, h1]

theorem exists_sign_centralizes (σ : K →+* K) {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) :
    ∃ a ∈ toralSignsTD4 K, ∀ x ∈ twistedRootGroup σ β,
      twistedIncl σ x ∈ Subgroup.centralizer ({rootDiagUnit d4 a} : Set (ModGL d4 K)) := by
  obtain ⟨α₀, hα₀, rfl⟩ := exists_proj_eq hβ
  obtain ⟨a, ha, h1⟩ := exists_sign_kernel (K := K) α₀
  refine ⟨a, ha, fun x hx => ?_⟩
  have hmem : twistedIncl σ x ∈ (twistedRootGroup σ (proj α₀)).map (twistedIncl σ) :=
    Subgroup.mem_map_of_mem _ hx
  rw [map_twistedRootGroup σ hβ, map_twistedRootSubgroupD4_eq σ hα₀] at hmem
  exact rootSpan_le_centralizer a
    (td4Orb_subset_rootCharKernel (toralSignsTD4_invariant ha) hα₀ h1) hmem.1

end Centralize

section Generate

variable {K : Type} [Field K] {σ : K →+* K}

theorem mem_centralizer_of_twistedIncl {τ x : twistedGroup σ}
    (h : twistedIncl σ x ∈ Subgroup.centralizer ({twistedIncl σ τ} : Set (ModGL d4 K))) :
    x ∈ Subgroup.centralizer ({τ} : Set (twistedGroup σ)) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  exact twistedIncl_injective σ (by rw [map_mul, map_mul]; exact h)

theorem centralizer_sup_sup_eq_top_td4 {τL τS : twistedGroup σ}
    (hL : twistedIncl σ τL = rootDiagUnit d4 (aLongTD4 K))
    (hS : twistedIncl σ τS = rootDiagUnit d4 (aShortTD4 K)) :
    Subgroup.centralizer ({τL} : Set (twistedGroup σ)) ⊔
      Subgroup.centralizer ({τS} : Set (twistedGroup σ)) ⊔
        Subgroup.centralizer ({τL * τS} : Set (twistedGroup σ)) = ⊤ := by
  rw [eq_top_iff, ← iSup_twistedDatum_rootGroup σ]
  refine iSup₂_le fun β hβ => ?_
  rw [twistedDatum_roots] at hβ
  show twistedRootGroup σ β ≤ _
  obtain ⟨a, ha, hx⟩ := exists_sign_centralizes σ (K := K) hβ
  intro x hxβ
  have hxa := hx x hxβ
  rcases ha with rfl | rfl | rfl
  · rw [← hL] at hxa
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_centralizer_of_twistedIncl hxa))
  · rw [← hS] at hxa
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_centralizer_of_twistedIncl hxa))
  · have : rootDiagUnit d4 (aLongTD4 K * aShortTD4 K) = twistedIncl σ (τL * τS) := by
      rw [map_mul, hL, hS, rootDiagUnit_mul]
    rw [this] at hxa
    exact Subgroup.mem_sup_right (mem_centralizer_of_twistedIncl hxa)

end Generate

section Toral

variable {K : Type} [Field K]

theorem sup_sup_centralizer_conj_eq_top_iff {G : Type*} [Group G] (g u v : G) :
    Subgroup.centralizer ({g * u * g⁻¹} : Set G) ⊔ Subgroup.centralizer ({g * v * g⁻¹} : Set G) ⊔
        Subgroup.centralizer ({g * u * g⁻¹ * (g * v * g⁻¹)} : Set G) = ⊤ ↔
      Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({v} : Set G) ⊔
        Subgroup.centralizer ({u * v} : Set G) = ⊤ := by
  have e : g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
  rw [e, ← conjSub_centralizer_singleton_g2d4, ← conjSub_centralizer_singleton_g2d4,
    ← conjSub_centralizer_singleton_g2d4, ← Subgroup.map_sup, ← Subgroup.map_sup]
  constructor
  · intro h
    exact Subgroup.map_injective (MulAut.conj g).injective
      (h.trans (Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective).symm)
  · intro h
    rw [h]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

@[expose] def TD4ToralPair (σ : K →+* K) (u v : twistedGroup σ) : Prop :=
  ∃ (g : twistedGroup σ) (a b : Fin d4.rank → Kˣ), a ∈ toralSignsTD4 K ∧ b ∈ toralSignsTD4 K ∧
    a ≠ b ∧ twistedIncl σ (g * u * g⁻¹) = rootDiagUnit d4 a ∧
      twistedIncl σ (g * v * g⁻¹) = rootDiagUnit d4 b

theorem centralizer_sup_sup_eq_top_of_toralPair_td4 {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c) {u v : twistedGroup σ} (h : TD4ToralPair σ u v) :
    Subgroup.centralizer ({u} : Set (twistedGroup σ)) ⊔
      Subgroup.centralizer ({v} : Set (twistedGroup σ)) ⊔
        Subgroup.centralizer ({u * v} : Set (twistedGroup σ)) = ⊤ := by
  obtain ⟨g, a, b, ha, hb, hab, hu, hv⟩ := h
  rw [← sup_sup_centralizer_conj_eq_top_iff g u v]
  obtain ⟨τL, -, hL⟩ := exists_involution_long σ
  obtain ⟨τS, -, hS⟩ := exists_involution_short hσ
  have key := centralizer_sup_sup_eq_top_td4 hL hS
  set u' : twistedGroup σ := g * u * g⁻¹ with hu'
  set v' : twistedGroup σ := g * v * g⁻¹ with hv'
  have hcov : ∀ c ∈ toralSignsTD4 K, ∀ x : twistedGroup σ,
      twistedIncl σ x = rootDiagUnit d4 c → x = u' ∨ x = v' ∨ x = u' * v' := by
    intro c hc x hx
    rcases toralSignsTD4_cover ha hb hc hab with rfl | rfl | rfl
    · exact Or.inl (twistedIncl_injective σ (hx.trans hu.symm))
    · exact Or.inr (Or.inl (twistedIncl_injective σ (hx.trans hv.symm)))
    · exact Or.inr (Or.inr (twistedIncl_injective σ (by
        rw [map_mul, hu, hv, ← rootDiagUnit_mul]; exact hx)))
  have hle : ∀ x : twistedGroup σ, (x = u' ∨ x = v' ∨ x = u' * v') →
      Subgroup.centralizer ({x} : Set (twistedGroup σ)) ≤
        Subgroup.centralizer ({u'} : Set (twistedGroup σ)) ⊔
          Subgroup.centralizer ({v'} : Set (twistedGroup σ)) ⊔
            Subgroup.centralizer ({u' * v'} : Set (twistedGroup σ)) := by
    rintro x (rfl | rfl | rfl)
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  rw [eq_top_iff, ← key]
  refine sup_le (sup_le (hle _ (hcov _ (Or.inl rfl) _ hL)) (hle _ (hcov _ (Or.inr (Or.inl rfl)) _
    hS))) (hle _ (hcov _ (Or.inr (Or.inr rfl)) _ ?_))
  rw [map_mul, hL, hS, rootDiagUnit_mul]

end Toral

section Model

variable {p : ℕ} [Fact p.Prime]

theorem iterateFrobenius_cube_td4 {e : ℕ} (he : 1 ≤ e) (c : GaloisField p (3 * e)) :
    iterateFrobenius (GaloisField p (3 * e)) p e
      (iterateFrobenius (GaloisField p (3 * e)) p e
        (iterateFrobenius (GaloisField p (3 * e)) p e c)) = c := by
  have hK3 : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hfin : Finite (GaloisField p (3 * e)) := Nat.finite_of_card_ne_zero (by
    rw [hK3]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  exact sigma_three_of_card hK3 (fun c => iterateFrobenius_def p e c) c

@[expose] def TD4NonToralGenerate (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .trialityD4 0 p e → p ≠ 2 →
    ∀ u v : (modelUniv .trialityD4 0 p e Fact.out).K, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 →
      u ≠ v → u * v = v * u →
        ¬ TD4ToralPair (iterateFrobenius (GaloisField p (3 * e)) p e) u v →
          Subgroup.centralizer ({u} : Set (modelUniv .trialityD4 0 p e Fact.out).K) ⊔
            Subgroup.centralizer ({v} : Set (modelUniv .trialityD4 0 p e Fact.out).K) ⊔
              Subgroup.centralizer ({u * v} : Set (modelUniv .trialityD4 0 p e Fact.out).K) = ⊤

theorem involutionCentralizersGenerate_td4_of_nonToral (hNT : TD4NonToralGenerate p)
    (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    InvolutionCentralizersGenerate (modelUniv .trialityD4 0 p e Fact.out).K := by
  intro u₁ u₂ h₁ h₂ h₁1 h₂1 hne hcomm
  by_cases hT : TD4ToralPair (iterateFrobenius (GaloisField p (3 * e)) p e) u₁ u₂
  · exact centralizer_sup_sup_eq_top_of_toralPair_td4
      (fun c => iterateFrobenius_cube_td4 hadm.2.1 c) hT
  · exact hNT e hadm hp2 u₁ u₂ h₁ h₂ h₁1 h₂1 hne hcomm hT

theorem d4ThreeCentralizerFacts_of_nonToral [Fact (Nat.Prime 3)] (hNT : TD4NonToralGenerate 3)
    (hB : TD4ThreeOddCore) : D4ThreeCentralizerFacts := by
  intro n p e hp hadm he3
  have hn : n = 0 := hadm.2.2
  subst hn
  have hp3 : p = 3 := by
    have he : e ≠ 0 := by
      have := hadm.2.1
      omega
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (he3 ▸ dvd_pow_self p he)
  subst hp3
  exact ⟨hB 0 3 e hp hadm he3,
    involutionCentralizersGenerate_td4_of_nonToral hNT (by norm_num) hadm⟩

end Model

end CFSG.ClassicalInvolution.G2D4Models
