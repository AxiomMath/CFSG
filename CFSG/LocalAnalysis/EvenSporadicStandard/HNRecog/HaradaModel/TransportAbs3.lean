module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.TransportCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.EvenSporadicStandard.HNRecog.TwoHSData

variable {H K : Type} [Group H] [Group K]

private theorem isConj_map_iff (e : H ≃* K) {x y : H} : IsConj (e x) (e y) ↔ IsConj x y :=
  ⟨isConj_of_map_mulEquiv e, isConj_map_mulEquiv e⟩

theorem tTH_map (e : H ≃* K) (a z z₁ y : H) : tTH (e a) (e z) (e z₁) (e y) ↔ tTH a z z₁ y := by
  unfold tTH
  constructor
  · rintro (h | h | h)
    · exact Or.inl ((isConj_map_iff e).mp h)
    · exact Or.inr (Or.inl ((isConj_map_iff e).mp (by simpa only [← map_mul] using h)))
    · exact Or.inr (Or.inr ((isConj_map_iff e).mp h))
  · rintro (h | h | h)
    · exact Or.inl ((isConj_map_iff e).mpr h)
    · exact Or.inr (Or.inl (by simpa only [map_mul] using (isConj_map_iff e).mpr h))
    · exact Or.inr (Or.inr ((isConj_map_iff e).mpr h))

private theorem map_invol_set (e : H ≃* K) (a z z₁ x : H) :
    e '' {y : H | y ∈ centralizer ({x} : Set H) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ tTH a z z₁ y} =
      {y : K | y ∈ centralizer ({e x} : Set K) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
        tTH (e a) (e z) (e z₁) y} := by
  ext y'
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyc, hy2, hy1, hyt⟩ := hy
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
      rw [← map_mul, ← map_mul, hyc]
    · rw [← map_pow, hy2, map_one]
    · intro h
      apply hy1
      have h' : e y = e 1 := by rw [h, map_one]
      exact e.injective h'
    · exact (tTH_map e a z z₁ y).mpr hyt
  · intro hy'
    obtain ⟨hyc, hy2, hy1, hyt⟩ := hy'
    refine ⟨e.symm y', ⟨?_, ?_, ?_, ?_⟩, by simp⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hyc
    · apply e.injective
      rw [map_pow, e.apply_symm_apply, hy2, map_one]
    · intro h
      apply hy1
      have h' : e (e.symm y') = e 1 := by rw [h, map_one]
      simpa using h'
    · exact (tTH_map e a z z₁ (e.symm y')).mp (by simpa using hyt)

theorem map_WsubH (e : H ≃* K) (a z z₁ x : H) :
    (WsubH a z z₁ x).map e.toMonoidHom = WsubH (e a) (e z) (e z₁) (e x) := by
  unfold WsubH
  rw [MonoidHom.map_closure]
  change closure (e '' {y : H | y ∈ centralizer ({x} : Set H) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
    tTH a z z₁ y}) = closure {y : K | y ∈ centralizer ({e x} : Set K) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
      tTH (e a) (e z) (e z₁) y}
  rw [map_invol_set e a z z₁ x]

theorem three_conj_map (e : H ≃* K)
    (h : ∀ x y : H, orderOf x = 3 → orderOf y = 3 → IsConj x y) :
    ∀ x y : K, orderOf x = 3 → orderOf y = 3 → IsConj x y := by
  intro x y hx hy
  have hx' : orderOf (e.symm x) = 3 := by rw [orderOf_symm, hx]
  have hy' : orderOf (e.symm y) = 3 := by rw [orderOf_symm, hy]
  simpa using isConj_map_mulEquiv e (h (e.symm x) (e.symm y) hx' hy')

theorem card_C3_map (e : H ≃* K)
    (h : ∀ x : H, orderOf x = 3 → Nat.card (centralizer ({x} : Set H)) = 1440) :
    ∀ x : K, orderOf x = 3 → Nat.card (centralizer ({x} : Set K)) = 1440 := by
  intro x hx
  have hx' : orderOf (e.symm x) = 3 := by rw [orderOf_symm, hx]
  have hmap : centralizer ({x} : Set K) =
      (centralizer ({e.symm x} : Set H)).map e.toMonoidHom := by
    rw [map_centralizer_singleton, e.apply_symm_apply]
  rw [hmap, card_map_mulEquiv, h (e.symm x) hx']

theorem odd_normal_map (e : H ≃* K)
    (h : ∀ x : H, orderOf x = 3 → ∀ N : Subgroup H, N ≤ centralizer ({x} : Set H) →
      (∀ c ∈ centralizer ({x} : Set H), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card N) →
        N ≤ zpowers x) :
    ∀ x : K, orderOf x = 3 → ∀ N : Subgroup K, N ≤ centralizer ({x} : Set K) →
      (∀ c ∈ centralizer ({x} : Set K), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card N) →
        N ≤ zpowers x := by
  intro x hx N hN hNnorm hNodd
  have hx' : orderOf (e.symm x) = 3 := by rw [orderOf_symm, hx]
  let N0 : Subgroup H := N.comap e.toMonoidHom
  have hN0le : N0 ≤ centralizer ({e.symm x} : Set H) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    have hc := hN hn
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hc
  have hN0norm : ∀ c ∈ centralizer ({e.symm x} : Set H), ∀ n ∈ N0,
      c * n * c⁻¹ ∈ N0 := by
    intro c hc n hn
    show e (c * n * c⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    apply hNnorm (e c) _ (e n) hn
    rw [← e.apply_symm_apply x, ← map_centralizer_singleton e (e.symm x)]
    exact Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
  have hN0card : Nat.card N0 = Nat.card N := by
    have hN0eq : N0 = N.map e.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm' e N
    rw [hN0eq, card_map_mulEquiv]
  have hN0odd : Odd (Nat.card N0) := by rw [hN0card]; exact hNodd
  have hle := h (e.symm x) hx' N0 hN0le hN0norm hN0odd
  intro n hn
  have hn0 : e.symm n ∈ N0 := by
    show e (e.symm n) ∈ N
    rwa [e.apply_symm_apply]
  have hz : e.symm n ∈ zpowers (e.symm x) := hle hn0
  have hmem : e (e.symm n) ∈ (zpowers (e.symm x)).map e.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨e.symm n, hz, rfl⟩
  rw [MonoidHom.map_zpowers] at hmem
  simpa using hmem

theorem card_tT_map (e : H ≃* K) (a z z₁ : H)
    (h : ∀ x : H, orderOf x = 3 →
      Set.ncard {y : H | y ∈ centralizer ({x} : Set H) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ tTH a z z₁ y} = 46) :
    ∀ x : K, orderOf x = 3 →
      Set.ncard {y : K | y ∈ centralizer ({x} : Set K) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
        tTH (e a) (e z) (e z₁) y} = 46 := by
  intro x hx
  have hx' : orderOf (e.symm x) = 3 := by rw [orderOf_symm, hx]
  have himg : {y : K | y ∈ centralizer ({x} : Set K) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
        tTH (e a) (e z) (e z₁) y} =
      e '' {y : H | y ∈ centralizer ({e.symm x} : Set H) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
        tTH a z z₁ y} := by
    rw [map_invol_set e a z z₁ (e.symm x), e.apply_symm_apply]
  rw [himg, Set.ncard_image_of_injective _ e.injective, h (e.symm x) hx']

theorem perfect60_map (e : H ≃* K)
    (h : ∀ x : H, orderOf x = 3 → ∃ M : Subgroup H, M ≤ centralizer ({x} : Set H) ∧ ⁅M, M⁆ = M ∧
      Nat.card M = 60 ∧ M ⊓ zpowers x = ⊥) :
    ∀ x : K, orderOf x = 3 → ∃ M : Subgroup K, M ≤ centralizer ({x} : Set K) ∧ ⁅M, M⁆ = M ∧
      Nat.card M = 60 ∧ M ⊓ zpowers x = ⊥ := by
  intro x hx
  have hx' : orderOf (e.symm x) = 3 := by rw [orderOf_symm, hx]
  obtain ⟨M, hMle, hMcomm, hMcard, hMinf⟩ := h (e.symm x) hx'
  refine ⟨M.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [← e.apply_symm_apply x, ← map_centralizer_singleton e (e.symm x)]
    exact Subgroup.map_mono hMle
  · rw [← Subgroup.map_commutator, hMcomm]
  · rw [card_map_mulEquiv, hMcard]
  · rw [show zpowers x = (zpowers (e.symm x)).map e.toMonoidHom by
        rw [MonoidHom.map_zpowers]; simp,
      ← Subgroup.map_inf M (zpowers (e.symm x)) e.toMonoidHom e.injective, hMinf,
      Subgroup.map_bot]

theorem W_comm_map (e : H ≃* K) (a z z₁ : H)
    (h : ∀ x : H, orderOf x = 3 → ∃ s : H, s ∈ centralizer ({x} : Set H) ∧ s ^ 2 = 1 ∧ s ≠ 1 ∧
      tTH a z z₁ s ∧ s ∈ ⁅WsubH a z z₁ x, WsubH a z z₁ x⁆) :
    ∀ x : K, orderOf x = 3 → ∃ s : K, s ∈ centralizer ({x} : Set K) ∧ s ^ 2 = 1 ∧ s ≠ 1 ∧
      tTH (e a) (e z) (e z₁) s ∧
        s ∈ ⁅WsubH (e a) (e z) (e z₁) x, WsubH (e a) (e z) (e z₁) x⁆ := by
  intro x hx
  have hx' : orderOf (e.symm x) = 3 := by rw [orderOf_symm, hx]
  obtain ⟨s, hsc, hs2, hs1, hst, hsW⟩ := h (e.symm x) hx'
  refine ⟨e s, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← e.apply_symm_apply x, ← map_centralizer_singleton e (e.symm x)]
    exact Subgroup.mem_map.mpr ⟨s, hsc, rfl⟩
  · rw [← map_pow, hs2, map_one]
  · intro h
    apply hs1
    have h' : e s = e 1 := by rw [h, map_one]
    exact e.injective h'
  · exact (tTH_map e a z z₁ s).mpr hst
  · rw [← e.apply_symm_apply x, ← map_WsubH e a z z₁ (e.symm x),
      ← Subgroup.map_commutator]
    exact Subgroup.mem_map.mpr ⟨s, hsW, rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
