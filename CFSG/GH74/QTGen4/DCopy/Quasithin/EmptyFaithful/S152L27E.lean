module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S152FinRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem normal_threePrime_le_M152_F4 {T Mc M : Subgroup G} (hs : Setting152 T Mc M)
    (h15208 : StageLemma15208_F4) {W : Subgroup G} (hWMc : W ≤ Mc)
    (hWn : Mc ≤ Subgroup.normalizer (W : Set G)) (hW3 : ¬ 3 ∣ Nat.card W) : W ≤ M := by
  by_contra hWM
  obtain ⟨S, rfl⟩ := hs.qtfe.exists_sylow
  have hTMc : (S : Subgroup G) ≤ Mc := hs.qtfe.t_le_mc
  have hTW : ∀ t ∈ (S : Subgroup G), ∀ w ∈ W, t * w * t⁻¹ ∈ W := fun t ht w hw =>
    (Subgroup.mem_normalizer_iff.mp (hWn (hTMc ht)) w).mp hw
  let 𝒦 : Set (Subgroup G) :=
    {K | K ≤ W ∧ (∀ t ∈ (S : Subgroup G), ∀ k ∈ K, t * k * t⁻¹ ∈ K) ∧ ¬ K ⊔ (S : Subgroup G) ≤ M}
  have hne : 𝒦.Nonempty := ⟨W, le_rfl, hTW, fun h => hWM (le_sup_left.trans h)⟩
  obtain ⟨K₀, ⟨hK₀W, hK₀T, hK₀M⟩, hmin⟩ :=
    Set.Finite.exists_minimalFor (fun K : Subgroup G => K) 𝒦 (Set.toFinite _) hne
  have hTnorm : (S : Subgroup G) ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hK₀T t ht x, fun hx => ?_⟩
    have := hK₀T t⁻¹ ((S : Subgroup G).inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hprod : ((K₀ ⊔ (S : Subgroup G) : Subgroup G) : Set G) = (K₀ : Set G) * ((S : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K₀ _ hTnorm
  set J : Subgroup G := K₀ ⊔ (S : Subgroup G) with hJ
  have hmulJ : ∀ y ∈ J, ∃ k ∈ K₀, ∃ t ∈ (S : Subgroup G), k * t = y := fun y hy => by
    have : y ∈ (J : Set G) := hy
    rw [hprod] at this
    exact Set.mem_mul.mp this
  have hTJ : (S : Subgroup G) ≤ J := le_sup_right
  have hJMc : J ≤ Mc := sup_le (hK₀W.trans hWMc) hTMc
  have hMcH : InH (S : Subgroup G) Mc := inH_of_inM hs.qtfe.inM_mc
  have hJH : InH (S : Subgroup G) J := inH_of_le S hTJ hJMc hMcH
  have hJstar : IsHStar (S : Subgroup G) M J := by
    refine ⟨hJH, hK₀M, fun Y hY hYJ hYM => ?_⟩
    have hTY : (S : Subgroup G) ≤ Y := hY.1
    have hYle : Y ≤ (Y ⊓ K₀) ⊔ (S : Subgroup G) := by
      intro y hy
      obtain ⟨k, hk, t, ht, rfl⟩ := hmulJ y (hYJ hy)
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨?_, hk⟩) (Subgroup.mem_sup_right ht)
      have := Y.mul_mem hy (Y.inv_mem (hTY ht))
      simpa using this
    have hK₁ : Y ⊓ K₀ ∈ 𝒦 := by
      refine ⟨inf_le_right.trans hK₀W, fun t ht k hk => ⟨?_, hK₀T t ht k hk.2⟩, ?_⟩
      · exact Y.mul_mem (Y.mul_mem (hTY ht) hk.1) (Y.inv_mem (hTY ht))
      · intro h
        exact hYM (hYle.trans h)
    have hle := hmin hK₁ (inf_le_right : Y ⊓ K₀ ≤ K₀)
    exact le_antisymm hYJ (sup_le (hle.trans inf_le_left) hTY)

  obtain ⟨e⟩ := h15208 G (S : Subgroup G) Mc M hs J hJstar
  have h72 : Nat.card (OTwoQuot J) = 72 := by
    rw [Nat.card_congr e.toEquiv]
    exact S152Fin.card_Wr
  have h3J : 3 ∣ Nat.card J := by
    have hd : Nat.card (OTwoQuot J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
    rw [h72] at hd
    exact (by norm_num : 3 ∣ 72).trans hd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 3 h3J
  have hy3 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  obtain ⟨k, hk, t, ht, hkt⟩ := hmulJ (y : G) y.2

  have hyG3 : (y : G) ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one _
  have ht3 : t ^ 3 ∈ K₀ := by
    have hk1 : t * k * t⁻¹ ∈ K₀ := hK₀T t ht k hk
    have hk2 : t * (t * k * t⁻¹) * t⁻¹ ∈ K₀ := hK₀T t ht _ hk1
    have e3 : t ^ 3 = (k * (t * k * t⁻¹) * (t * (t * k * t⁻¹) * t⁻¹))⁻¹ := by
      have h1 : (k * t) ^ 3 = 1 := by rw [hkt]; exact hyG3
      have e0 : (k * t) ^ 3 = (k * (t * k * t⁻¹) * (t * (t * k * t⁻¹) * t⁻¹)) * t ^ 3 := by
        simp only [pow_three]; group
      rw [e0] at h1
      exact eq_inv_of_mul_eq_one_right h1
    rw [e3]
    exact K₀.inv_mem (K₀.mul_mem (K₀.mul_mem hk hk1) hk2)
  have htK : t ∈ K₀ := by
    obtain ⟨a, ha⟩ := (S.isPGroup') ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by
      have := congrArg (fun z : (S : Subgroup G) => (z : G)) ha
      simpa using this
    have hcop : Nat.Coprime 3 (orderOf t) := by
      have h2 : Nat.Coprime (2 ^ a) 3 := Nat.Coprime.pow_left a (by norm_num)
      exact (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hta) h2).symm
    exact (Subgroup.zpowers_le.mpr ht3) (A4.mem_zpowers_pow_of_coprime hcop)
  have hyK : (y : G) ∈ K₀ := by
    rw [← hkt]; exact K₀.mul_mem hk htK
  have hdvd := Subgroup.orderOf_dvd_natCard W (hK₀W hyK)
  rw [hy3] at hdvd
  exact hW3 hdvd

end CFSG.Quasithin
