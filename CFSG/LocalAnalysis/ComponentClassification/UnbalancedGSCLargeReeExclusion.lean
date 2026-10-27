module

public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSuzukiExclusion

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

namespace LargeReeExclusion

open ReeTag

section

variable {K : Type} [Field K]

theorem largeReeX_two_three_commute (h2 : (2 : K) = 0) (c d : K) :
    largeReeX K 2 c * largeReeX K 3 d = largeReeX K 3 d * largeReeX K 2 c :=
  ((large_Ree_B2_characteristic_two_commutators K h2).2.1 2 3 (by decide)
    (by decide) _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)).eq

theorem largeReeX_two_three_injective (h2 : (2 : K) = 0) {c d c' d' : K}
    (h : largeReeX K 2 c * largeReeX K 3 d = largeReeX K 2 c' * largeReeX K 3 d') :
    c = c' ∧ d = d' := by
  have hP : ∀ x y : K, largeReeP K 0 0 x y = largeReeX K 2 x * largeReeX K 3 y := by
    intro x y
    simp [largeReeP, largeReeX_zero]
  have hinj := (large_Ree_B2_characteristic_two_commutators K h2).2.2.2.injOn
  have := @hinj ![0, 0, c, d] (Set.mem_univ _) ![0, 0, c', d'] (Set.mem_univ _) (by
    simp only [Matrix.cons_val]
    simpa [hP] using h)
  exact ⟨congrFun this 2, congrFun this 3⟩

end

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime]

omit [Finite K] in
theorem two_eq_zero_F4 : (2 : K) = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  exact_mod_cast CharP.cast_eq_zero K 2

theorem zElt_mem (a : ℕ) (σ ρ : K ≃+* K) (hρσ : σ.trans ρ = RingEquiv.refl K)
    (h3 : ∀ c : K, F4.finiteReeAut K a ⟨largeReeX K 2 c, pinnedX_mem_adjointGroup _ c⟩ =
      ⟨largeReeX K 3 (σ c), pinnedX_mem_adjointGroup _ _⟩)
    (h4 : ∀ c : K, F4.finiteReeAut K a ⟨largeReeX K 3 c, pinnedX_mem_adjointGroup _ c⟩ =
      ⟨largeReeX K 2 (ρ c), pinnedX_mem_adjointGroup _ _⟩) (c : K) :
    largeReeX K 2 c * largeReeX K 3 (σ c) ∈ F4.reeGamma K a := by
  refine mem_reeGamma.2
    ⟨mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _), ?_⟩
  have hsplit : (⟨largeReeX K 2 c * largeReeX K 3 (σ c), mul_mem (pinnedX_mem_adjointGroup _ _)
      (pinnedX_mem_adjointGroup _ _)⟩ : adjointGroup F4.tag K) =
      ⟨largeReeX K 2 c, pinnedX_mem_adjointGroup _ c⟩ *
        ⟨largeReeX K 3 (σ c), pinnedX_mem_adjointGroup _ _⟩ := rfl
  rw [hsplit, map_mul, h3, h4]
  have hρ : ρ (σ c) = c := by
    have := congrArg (fun φ : K ≃+* K => φ c) hρσ
    simpa using this
  apply Subtype.ext
  change largeReeX K 3 (σ c) * largeReeX K 2 (ρ (σ c)) = largeReeX K 2 c * largeReeX K 3 (σ c)
  rw [hρ, largeReeX_two_three_commute two_eq_zero_F4]

end LargeReeExclusion

open LargeReeExclusion ReeTag

theorem dihedral_sylow_large_ree_model_exclusion {T : Type} [Group T] {p f : ℕ}
    (hT : ReeTitsModel T .twistedF4 p f) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  rintro ⟨eP⟩
  obtain ⟨hfin, -, -, hp, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ := large_Ree_model_Schreier T p f hT
  subst hp
  obtain ⟨-, a, hfa, hmodel⟩ := hT
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hK
  obtain ⟨ρ, σ, -, -, -, hρσ, -, -, -, hR, -⟩ := large_Ree_root_parameter_involution a K hK'
  have h2 : (2 : K) = 0 := two_eq_zero_F4
  let z : Multiplicative K →* F4.reeGamma K a :=
    { toFun := fun c => ⟨largeReeX K 2 (Multiplicative.toAdd c) *
          largeReeX K 3 (σ (Multiplicative.toAdd c)),
        zElt_mem a σ ρ hρσ (fun c => (hR c).2.2.1) (fun c => (hR c).2.2.2) _⟩
      map_one' := by
        apply Subtype.ext
        change largeReeX K 2 0 * largeReeX K 3 (σ 0) = 1
        rw [map_zero, largeReeX_zero, largeReeX_zero, one_mul]
      map_mul' := fun c d => by
        apply Subtype.ext
        change largeReeX K 2 (Multiplicative.toAdd c + Multiplicative.toAdd d) *
            largeReeX K 3 (σ (Multiplicative.toAdd c + Multiplicative.toAdd d)) =
          largeReeX K 2 (Multiplicative.toAdd c) * largeReeX K 3 (σ (Multiplicative.toAdd c)) *
            (largeReeX K 2 (Multiplicative.toAdd d) * largeReeX K 3 (σ (Multiplicative.toAdd d)))
        generalize Multiplicative.toAdd c = x
        generalize Multiplicative.toAdd d = y
        rw [map_add, largeReeX_add, largeReeX_add]
        simp only [mul_assoc]
        rw [← mul_assoc (largeReeX K 2 y), largeReeX_two_three_commute h2, mul_assoc] }
  have hz : Function.Injective z := by
    intro c d h
    have h' := congrArg (fun g : F4.reeGamma K a => (g : ModGL F4.tag K)) h
    exact Multiplicative.toAdd.injective (largeReeX_two_three_injective h2 h').1
  have : Finite T := hfin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := SuzukiExclusion.isElementaryAbelian_top_multiplicative h2
  let φ : Multiplicative K →* T := E.symm.toMonoidHom.comp z
  have hφ : Function.Injective φ := E.symm.injective.comp hz
  have hEl := CFSG.IsElementaryAbelian.map (A := (⊤ : Subgroup (Multiplicative K))) (p := 2) φ
  have hcard : Nat.card ((⊤ : Subgroup (Multiplicative K)).map φ) = 2 ^ f := by
    rw [Subgroup.card_map_of_injective hφ, Subgroup.card_top]
    exact hK
  have hle := RankOneCenter.le_pRank_of_subgroup hEl hcard
  have hrank :=
    (SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, ⟨eP⟩⟩).1
  omega

end CFSG.ComponentClassification.UnbalancedGS
