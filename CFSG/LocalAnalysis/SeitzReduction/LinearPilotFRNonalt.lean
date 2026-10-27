module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltFour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotMainInputs
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltMixed
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltSelf

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore)

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem innerNonaltFieldRigid_of_six_le {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 6 ≤ n) : InnerNonaltFieldRigid K (by omega : 3 ≤ n) := by
  intro hev k P hP
  obtain ⟨m, hm⟩ := hev
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => hP (P.elt_eq_one_of_eq_zero h)
  have hc := P.card_free
  have h2k : 2 * k ≤ n := by
    have := Fintype.card_le_of_injective P.supp P.supp_injective
    simpa [two_mul] using this
  rcases (by omega : 2 ≤ P.free.card ∨ P.free.card = 0) with hJ | hJ
  · exact fieldRigidIn_inner_nonalt_of_two_le_free hK hq _ (r := m - 1) (by omega) (by omega) P hP
      hJ
  · exact fieldRigidIn_inner_nonalt_of_free_eq_empty hK hq _ (r := m - 1) (by omega) (by omega) P
      (Finset.card_eq_zero.1 hJ)

theorem innerGraphFieldRigid_of_even_of_six_le {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 6 ≤ n)
    (hev : Even n) : InnerGraphFieldRigid K (by omega : 3 ≤ n) := by
  rcases Nat.lt_or_ge (Nat.card K) 4 with h | hq
  · have h2 : Nat.card K = 2 := by
      have h1 := Finite.one_lt_card (α := K)
      rcases f with _ | _ | f
      · rw [hK, pow_zero] at h1
        omega
      · rw [hK, pow_one]
      · rw [hK, pow_succ, pow_succ] at h
        have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega
    exact innerGraphFieldRigid_of_card_eq_two h2 _
  · obtain ⟨m, hm⟩ := hev
    exact innerGraphFieldRigid_of_nonalt_even hK hq (by omega)
      (innerNonaltFieldRigid_of_six_le hK hq hn) fun _ =>
        fieldRigidIn_graph_nonalt_self_of_even hK hq _ (r := m - 1) (by omega) (by omega)

theorem innerGraphFieldRigid_of_five_le {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) :
    InnerGraphFieldRigid K (by omega : 3 ≤ n) := by
  rcases Nat.even_or_odd n with hev | hodd
  · exact innerGraphFieldRigid_of_even_of_six_le hK (by obtain ⟨m, hm⟩ := hev; omega) hev
  · exact innerGraphFieldRigid_of_odd hK (by omega) hodd

theorem linearFRInput_holds : LinearFRInput := by
  intro n hn h5 K _ _ f hK _
  exact innerGraphFieldRigid_of_five_le hK h5

section Four

open Nonalt

theorem fieldRigidIn_inner_nonalt_four_of_free_eq_empty {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {k : ℕ} (P : InvPlacement 4 k) (hJ : P.free = ∅) :
    FieldRigidIn (by norm_num : 3 ≤ 4)
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL 4 K))))
      (perfectCore (autFixSubgroup (dualAut 4 K))) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hcard := P.card_free
  rw [hJ, Finset.card_empty] at hcard
  have h2k : 2 * k ≤ 4 := by
    have := Fintype.card_le_of_injective P.supp P.supp_injective
    simpa [two_mul] using this
  obtain rfl : k = 2 := by omega
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  set Λ := perfectCore (centralizer ({P.elt K} : Set (projectiveSL 4 K))) with hΛ
  obtain ⟨hQp, hQΛ, hΛN, hmax, hΛeq, hMN, hdisj⟩ := P.coreRadicalP_spec hq (by norm_num) hJ
  obtain ⟨hQp', hQΘ, hΘN, hmax', hΘeq, hLN, hdisj'⟩ :=
    coreRadical_spec (K := K) hK hq (n := 4) (r := 1) rfl le_rfl 0
  have hβ₁Λ : Λ.map β₁.toMonoidHom = Λ := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective β₁.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact hβX x hx
  have heq : coreRadical K (0 : Fin 4) = ((P.coreRadicalP K).map φ₁).comap φ₂ :=
    le_antisymm (le_comap_map_of_forall hφ₁ hX hmax hQp' hQΘ hΘN)
      (hmax' _ (isPGroup_comap_map hφ₂ hQp) (comap_map_le hφ₂ hX hQΛ)
        (le_normalizer_comap_map hX hΛN))
  have hQ : (coreRadical K (0 : Fin 4)).map φ₂ = (P.coreRadicalP K).map φ₁ := by
    have h := map_comap_map_eq hX hQΛ
    rw [← heq] at h
    exact h
  have hβ₁Q := P.map_coreRadicalP_eq_of_map_eq hq (by norm_num) hJ β₁ hβ₁Λ
  obtain ⟨βbar₁, βbar₂, ψ, hc₁, hc₂, hint⟩ := exists_intertwined_complements hφ₁ hφ₂ hΛeq hΘeq
    hMN hLN hdisj hdisj' hX hQ h₁ h₂ hβ₁Λ hβ₁Q
  set e₂ := LinearCover.projectiveSLTwoEquivSL K with he₂
  set F : MulAut (projectiveSL 2 K) →* (K ≃+* K) :=
    (sl2FieldPart K).comp (MulAut.congr e₂).toMonoidHom with hFdef
  have hF : ∀ A : GL (Fin 2) K, F (conjAut 2 K A) = 1 := fun A => by
    change sl2FieldPart K (MulAut.congr e₂ (descendAut 2 K
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K A))) = 1
    rw [he₂, congr_projectiveSLTwoEquivSL_descendAut, sl2FieldPart_slConjugation]
  have hFσ : ∀ σ : K ≃+* K, F (fieldAut 2 K σ) = σ := fun σ => by
    change sl2FieldPart K (MulAut.congr e₂ (descendAut 2 K
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 2) K σ))) = σ
    rw [he₂, congr_projectiveSLTwoEquivSL_descendAut, sl2FieldPart_slFieldAut]
  have hFδ : F (dualAut 2 K) = 1 := by
    change sl2FieldPart K (MulAut.congr e₂ (descendAut 2 K
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 2 K))) = 1
    rw [he₂, congr_projectiveSLTwoEquivSL_descendAut, sl2FieldPart_slGraphAut]
  set κ := (P.leviOnePEquivPSL K hJ).symm with hκ
  have hF₁ := P.projFieldPart_congr_eq_linearFieldPart_of_free_eq_empty hq (by norm_num) le_rfl hJ
    F hF hFσ hFδ β₁ hβ₁Λ βbar₁ hc₁ κ
  have hF₁' : sl2FieldPart K (MulAut.congr (κ.trans e₂) βbar₁) =
      linearFieldPart K (by norm_num) β₁ := by
    rw [← hF₁]
    rfl
  have hF₂ := sl2FieldPart_congr_kappa hK hq β₂ βbar₂ hc₂
  have hT := mulAutHom_congr_eq_of_intertwine (sl2FieldPart K) (sl2FieldPart_mul_comm K)
    (κ.trans e₂) (kappa K) ψ βbar₁ βbar₂ hint
  rw [← hF₁', ← hF₂, hT]

theorem innerNonaltFieldRigid_four {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) :
    InnerNonaltFieldRigid K (by norm_num : 3 ≤ 4) := by
  intro _ k P hP
  have hc := P.card_free
  have h2k : 2 * k ≤ 4 := by
    have := Fintype.card_le_of_injective P.supp P.supp_injective
    simpa [two_mul] using this
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => hP (P.elt_eq_one_of_eq_zero h)
  rcases (by omega : 2 ≤ P.free.card ∨ P.free.card = 0) with hJ | hJ
  · exact fieldRigidIn_inner_nonalt_of_two_le_free hK hq _ (r := 1) rfl le_rfl P hP hJ
  · exact fieldRigidIn_inner_nonalt_four_of_free_eq_empty hK hq P (Finset.card_eq_zero.1 hJ)

theorem innerGraphFieldRigid_four {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    InnerGraphFieldRigid K (by norm_num : 3 ≤ 4) := by
  rcases Nat.lt_or_ge (Nat.card K) 4 with h | hq
  · have h2 : Nat.card K = 2 := by
      have h1 := Finite.one_lt_card (α := K)
      rcases f with _ | _ | f
      · rw [hK, pow_zero] at h1
        omega
      · rw [hK, pow_one]
      · rw [hK, pow_succ, pow_succ] at h
        have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega
    exact innerGraphFieldRigid_of_card_eq_two h2 _
  · exact innerGraphFieldRigid_of_nonalt_even hK hq le_rfl (innerNonaltFieldRigid_four hK hq)
      fun _ => fieldRigidIn_graph_nonalt_self_of_even hK hq _ (r := 1) rfl le_rfl

end Four

end CFSG.SeitzReduction.LinearPilot
