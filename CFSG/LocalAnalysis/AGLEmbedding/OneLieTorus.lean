module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieBender

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers

section Torus

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y}

omit [Finite Y] in
theorem mul_mul_commutator_eq {K : Subgroup Y} {t c a : Y}
    (hc : c ∈ Subgroup.centralizer (K : Set Y)) (ha : a ∈ K) :
    t * c * a * (t * c)⁻¹ * a⁻¹ = t * (a * t⁻¹ * a⁻¹) := by
  have hca : c * a = a * c := (Subgroup.mem_centralizer_iff.mp hc a ha).symm
  calc t * c * a * (t * c)⁻¹ * a⁻¹ = t * (c * a) * c⁻¹ * t⁻¹ * a⁻¹ := by group
    _ = t * (a * c) * c⁻¹ * t⁻¹ * a⁻¹ := by rw [hca]
    _ = t * (a * t⁻¹ * a⁻¹) := by group

theorem le_of_inf_centralizer_eq_bot (hp : p.Prime) {K : Subgroup Y} [K.Normal]
    (_hZ : Subgroup.center K = ⊥)
    (T₁ : Sylow p K) (hT₁ : (T₁ : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K)
    (hF : OneLieFacts p K T₁) {W : Subgroup Y} (hW : IsPGroup p W)
    (hWle : W ≤ ((Rb : Subgroup Y) ⊓ K) ⊔ ((Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y)))
    (hWn : K ⊓ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y) ≤
      Subgroup.normalizer (W : Set Y))
    (hWC : W ⊓ Subgroup.centralizer (K : Set Y) = ⊥) : W ≤ (Rb : Subgroup Y) ⊓ K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₀, hT₀N, hT₀p, hT₀C⟩ := hF.torus
  have hAKN : T₀.map K.subtype ≤
      K ⊓ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← hT₁]
    exact coe_mem_normalizer_map (hT₀N ha)
  have hAW : T₀.map K.subtype ≤ Subgroup.normalizer (W : Set Y) := hAKN.trans hWn
  have hdec : ∀ w ∈ W, ∃ t ∈ (Rb : Subgroup Y) ⊓ K, ∃ c ∈ Subgroup.centralizer (K : Set Y),
      t * c = w := by
    intro w hw
    have hw' : w ∈ ((((Rb : Subgroup Y) ⊓ K) ⊔ Subgroup.centralizer (K : Set Y) : Subgroup Y) :
        Set Y) := (hWle.trans (sup_le_sup_left inf_le_right _)) hw
    rw [Subgroup.mul_normal] at hw'
    obtain ⟨t, ht, c, hc, htc⟩ := hw'
    exact ⟨t, ht, c, hc, htc⟩
  have hcomm : ⁅W, T₀.map K.subtype⁆ ≤ (Rb : Subgroup Y) ⊓ K := by
    rw [Subgroup.commutator_le]
    intro w hw a ha
    obtain ⟨t, ht, c, hc, rfl⟩ := hdec w hw
    rw [commutatorElement_def, mul_mul_commutator_eq hc (hAKN ha).1]
    exact Subgroup.mul_mem _ ht
      ((Subgroup.mem_normalizer_iff.mp (hAKN ha).2 t⁻¹).mp (Subgroup.inv_mem _ ht))
  have hfix : W ⊓ Subgroup.centralizer ((T₀.map K.subtype : Subgroup Y) : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hw, hwA⟩
    obtain ⟨t, ht, c, hc, rfl⟩ := hdec w hw
    have htA : t ∈ Subgroup.centralizer ((T₀.map K.subtype : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 : a * (t * c) = t * c * a := Subgroup.mem_centralizer_iff.mp hwA a ha
      have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc a (hAKN ha).1
      have h2 : a * t * c = t * a * c := by
        calc a * t * c = a * (t * c) := by group
          _ = t * c * a := h1
          _ = t * (c * a) := by group
          _ = t * (a * c) := by rw [← hca]
          _ = t * a * c := by group
      exact mul_right_cancel h2
    have ht1 : t = 1 := by
      rw [← hT₁] at ht
      obtain ⟨t₁, ht₁, rfl⟩ := ht
      have hmem : t₁ ∈ (T₁ : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) :=
        ⟨ht₁, Subgroup.mem_centralizer_iff.mpr fun s hs =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp htA _ ⟨s, hs, rfl⟩)⟩
      rw [hT₀C, Subgroup.mem_bot] at hmem
      rw [hmem]
      rfl
    subst ht1
    rw [one_mul] at hw ⊢
    have hcW : c ∈ W ⊓ Subgroup.centralizer (K : Set Y) := ⟨hw, hc⟩
    rwa [hWC] at hcW
  have hcop : Nat.Coprime (Nat.card (T₀.map K.subtype)) (Nat.card W) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW
    rw [hk, Subgroup.card_map_of_injective K.subtype_injective]
    exact Nat.Coprime.pow_right k hT₀p.symm
  have hsolv : Group.IsSolvable W := by
    have := hW.isNilpotent
    infer_instance
  have hle := le_commutator_sup_inf_centralizer_of_coprime hAW hcop hsolv
  rw [hfix, sup_bot_eq] at hle
  exact hle.trans hcomm

end Torus

section Reduced

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.centralizer_le_of_inf_ne_bot (h : ReducedNongeneration p Y Rb Y₀)
    {K : Subgroup Y} [K.Normal] (hK : IsComponentOf K ⊤) (hZ : Subgroup.center K = ⊥)
    (hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y))
    (hz : ∃ z ∈ (Rb : Subgroup Y), z ∉ K ∧ orderOf z = p ∧
      z ∈ Subgroup.centralizer (K : Set Y))
    {W : Subgroup Y} (hWp : IsPGroup p W)
    (hCW : Subgroup.centralizer (K : Set Y) ≤ Subgroup.normalizer (W : Set Y))
    (hWC : W ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥)
    (hcent : Subgroup.centralizer (W : Set Y) ≤
      ((Rb : Subgroup Y) ⊓ K) ⊔ Subgroup.centralizer (K : Set Y)) :
    Subgroup.centralizer (W : Set Y) ≤ Rb := by
  intro y hy
  have hmem : y ∈ ((((Rb : Subgroup Y) ⊓ K) ⊔ Subgroup.centralizer (K : Set Y) : Subgroup Y) :
      Set Y) := hcent hy
  rw [Subgroup.mul_normal] at hmem
  obtain ⟨t, ht, c, hc, rfl⟩ := hmem
  have hCC : Subgroup.centralizer (K : Set Y) ≤
      Subgroup.normalizer ((W ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y) : Set Y) :=
    (le_inf hCW (Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hc' : c ∈ Subgroup.centralizer (K : Set Y) ⊓
      Subgroup.centralizer ((W ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y) : Set Y) := by
    refine ⟨hc, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hyw : w * (t * c) = t * c * w := Subgroup.mem_centralizer_iff.mp hy w hw.1
    have htw : t * w = w * t := Subgroup.mem_centralizer_iff.mp hw.2 t ht.2
    calc w * c = t⁻¹ * (t * w * c) := by group
      _ = t⁻¹ * (w * (t * c)) := by rw [htw]; group
      _ = t⁻¹ * (t * c * w) := by rw [hyw]
      _ = c * w := by group
  have hcR := h.inf_centralizer_le_of_rankOne hK hZ hnc hz inf_le_right hWC
    (hWp.to_le inf_le_left) hCC hc'
  exact (Rb : Subgroup Y).mul_mem ht.1 hcR

end Reduced

end CFSG.AGLEmbedding
