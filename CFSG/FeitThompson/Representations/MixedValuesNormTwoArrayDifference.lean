module

public import CFSG.FeitThompson.Representations.TIRectangleCoefficientExchange
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.LowNormAnchoredRectangleColumnProjection
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

namespace CyclicTINormTwoDifference

open Finset

theorem card_support_le_sum_sq {ι : Type*} [Fintype ι] (n : ι → ℤ) :
    (#{z : ι | n z ≠ 0} : ℤ) ≤ ∑ z, n z ^ 2 := by
  classical
  calc (#{z : ι | n z ≠ 0} : ℤ) = ∑ _z ∈ {z : ι | n z ≠ 0}, (1 : ℤ) := by simp
    _ ≤ ∑ z ∈ {z : ι | n z ≠ 0}, n z ^ 2 :=
        Finset.sum_le_sum fun z hz =>
          AnchoredLowNormRectangle.one_le_sq_of_ne_zero (by simpa using hz)
    _ ≤ ∑ z, n z ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

private theorem eq_zero_of_sum_sq_le_two_aux {a : I × J → ℤ} {p q : I × J} (hpq : p ≠ q)
    (hsum : ∑ z : I × J,
      (a z + ((if z = p then 1 else 0) - (if z = q then 1 else 0))) ^ 2 ≤ 2)
    (hexch : ∀ i k : I, ∀ j l : J, a (i, j) + a (k, l) = a (i, l) + a (k, j))
    (hI : 3 ≤ Fintype.card I) (hJ : 5 ≤ Fintype.card J) : a = 0 := by
  classical
  set d : I × J → ℤ := fun z => (if z = p then 1 else 0) - (if z = q then 1 else 0) with hd
  set T := ({z : I × J | a z ≠ 0} : Finset (I × J)) with hT
  have hmemT : ∀ z : I × J, z ∈ T ↔ a z ≠ 0 := by intro z; simp [hT]
  have hTcard : #T ≤ 4 := by
    have hsub : T ⊆ ({z : I × J | a z + d z ≠ 0} : Finset (I × J)) ∪ {p, q} := by
      intro z hz
      have hz' := (hmemT z).1 hz
      by_cases hzn : a z + d z = 0
      · refine Finset.mem_union_right _ ?_
        by_cases hzp : z = p
        · simp [hzp]
        · by_cases hzq : z = q
          · simp [hzq]
          · simp only [hd, hzp, hzq, if_false, sub_zero, add_zero] at hzn
            exact absurd hzn hz'
      · exact Finset.mem_union_left _ (by simpa using hzn)
    have h2 : (#({z : I × J | a z + d z ≠ 0} : Finset (I × J)) : ℤ) ≤ 2 :=
      le_trans (card_support_le_sum_sq _) hsum
    have h2' : #({z : I × J | a z + d z ≠ 0} : Finset (I × J)) ≤ 2 := by omega
    calc #T ≤ #(({z : I × J | a z + d z ≠ 0} : Finset (I × J)) ∪ {p, q}) :=
          Finset.card_le_card hsub
      _ ≤ #({z : I × J | a z + d z ≠ 0} : Finset (I × J)) + #({p, q} : Finset (I × J)) :=
          Finset.card_union_le _ _
      _ ≤ 2 + 2 := by gcongr; exact le_of_eq (Finset.card_pair hpq)
      _ = 4 := rfl
  have hrows : ∀ (i₁ i₂ : I) (j : J), a (i₁, j) = a (i₂, j) := by
    intro i₁ i₂ j₁
    by_contra hne
    have hall : ∀ j, a (i₁, j) ≠ a (i₂, j) := by
      intro j hj
      have := hexch i₁ i₂ j j₁
      omega
    have hmaps : ∀ j : J, (if a (i₁, j) ≠ 0 then (i₁, j) else (i₂, j)) ∈ T := by
      intro j
      by_cases h : a (i₁, j) ≠ 0
      · simpa [h] using (hmemT (i₁, j)).2 h
      · have : a (i₂, j) ≠ 0 := by
          simp only [ne_eq, not_not] at h
          intro h2
          exact hall j (by rw [h, h2])
        simpa [h] using (hmemT (i₂, j)).2 this
    have hinj : Set.InjOn (fun j : J => if a (i₁, j) ≠ 0 then (i₁, j) else (i₂, j))
        (Finset.univ : Finset J) := by
      intro x _ y _ hxy
      by_cases hx : a (i₁, x) ≠ 0 <;> by_cases hy : a (i₁, y) ≠ 0 <;>
        simp only [hx, hy, if_false, ne_eq] at hxy <;>
        exact (Prod.mk.injEq _ _ _ _ ▸ hxy).2
    have := Finset.card_le_card_of_injOn _ (fun j _ => hmaps j) hinj
    rw [Finset.card_univ] at this
    omega
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  set b : J → ℤ := fun j => a (i₀, j) with hb
  have hab : ∀ z : I × J, a z = b z.2 := fun z => hrows z.1 i₀ z.2
  have hsumsq : ∑ z : I × J, a z ^ 2 = (Fintype.card I : ℤ) * ∑ j : J, b j ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [hab]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcross : ∑ z : I × J, a z * d z = b p.2 - b q.2 := by
    simp only [hd, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ p a, Finset.sum_ite_eq' Finset.univ q a,
      if_pos (Finset.mem_univ p), if_pos (Finset.mem_univ q), hab p, hab q]
  have hdsq : ∑ z : I × J, d z ^ 2 = 2 := by
    have hterm : ∀ z : I × J, d z ^ 2 = (if z = p then 1 else 0) + (if z = q then 1 else 0) := by
      intro z
      by_cases hzp : z = p
      · have hzq : z ≠ q := by rw [hzp]; exact hpq
        simp [hd, if_pos hzp, if_neg hzq]
      · by_cases hzq : z = q
        · simp [hd, if_neg hzp, if_pos hzq]
        · simp [hd, if_neg hzp, if_neg hzq]
    rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_add_distrib]
    simp
  have hexpand : ∑ z : I × J, (a z + d z) ^ 2
      = (Fintype.card I : ℤ) * (∑ j : J, b j ^ 2) + 2 * (b p.2 - b q.2) + 2 := by
    have hterm : ∀ z : I × J, (a z + d z) ^ 2 = a z ^ 2 + 2 * (a z * d z) + d z ^ 2 :=
      fun z => by ring
    rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsumsq, hcross, hdsq]
  rw [hexpand] at hsum
  set S := ∑ j : J, b j ^ 2 with hS
  have hcardI : (3 : ℤ) ≤ (Fintype.card I : ℤ) := by exact_mod_cast hI
  have hzero : ∀ j, b j = 0 := by
    by_contra hcon
    obtain ⟨j₁, hj₁⟩ := not_forall.1 hcon
    have hS1 : 1 ≤ S := by
      calc (1 : ℤ) ≤ b j₁ ^ 2 := AnchoredLowNormRectangle.one_le_sq_of_ne_zero hj₁
        _ ≤ S := Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ j₁)
    have h3S : 3 * S ≤ (Fintype.card I : ℤ) * S := by nlinarith
    by_cases hcol : p.2 = q.2
    · rw [hcol] at hsum
      simp only [sub_self, mul_zero, add_zero] at hsum
      linarith
    · have hpair : b p.2 ^ 2 + b q.2 ^ 2 ≤ S := by
        have h3 := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ ({p.2, q.2} : Finset J)) fun x _ _ => sq_nonneg (b x)
        rwa [Finset.sum_pair hcol] at h3
      set u := b p.2 with hu
      set v := b q.2 with hv
      have hkey : 3 * u ^ 2 + 2 * u + (3 * v ^ 2 - 2 * v) ≤ 0 := by nlinarith
      have hu0 : u = 0 := by
        by_contra h
        have h1 : 1 ≤ 3 * u ^ 2 + 2 * u := by
          rcases lt_or_gt_of_ne h with h' | h'
          · have : u ≤ -1 := by omega
            nlinarith
          · nlinarith
        have h2 : 0 ≤ 3 * v ^ 2 - 2 * v := by
          rcases lt_trichotomy v 0 with h'' | h'' | h''
          · nlinarith
          · simp [h'']
          · have : 1 ≤ v := by omega
            nlinarith
        linarith
      have hv0 : v = 0 := by
        by_contra h
        have h1 : 1 ≤ 3 * v ^ 2 - 2 * v := by
          rcases lt_or_gt_of_ne h with h' | h'
          · have : v ≤ -1 := by omega
            nlinarith
          · have : 1 ≤ v := by omega
            nlinarith
        have h2 : 0 ≤ 3 * u ^ 2 + 2 * u := by
          rcases lt_trichotomy u 0 with h'' | h'' | h''
          · have : u ≤ -1 := by omega
            nlinarith
          · simp [h'']
          · nlinarith
        linarith
      rw [hu0, hv0] at hsum
      simp only [sub_zero, mul_zero, add_zero] at hsum
      linarith
  funext z
  rw [hab z, hzero z.2]
  rfl

theorem eq_zero_of_sum_sq_le_two {a : I × J → ℤ} {p q : I × J} (hpq : p ≠ q)
    (hsum : ∑ z : I × J,
      (a z + ((if z = p then 1 else 0) - (if z = q then 1 else 0))) ^ 2 ≤ 2)
    (hexch : ∀ i k : I, ∀ j l : J, a (i, j) + a (k, l) = a (i, l) + a (k, j))
    (hI : 3 ≤ Fintype.card I) (hJ : 3 ≤ Fintype.card J)
    (h5 : 5 ≤ Fintype.card I ∨ 5 ≤ Fintype.card J) : a = 0 := by
  classical
  rcases h5 with h5 | h5
  ·
    have hsumeq : ∑ z : J × I, ((fun w : J × I => a w.swap) z
        + ((if z = p.swap then (1 : ℤ) else 0) - (if z = q.swap then 1 else 0))) ^ 2
        = ∑ z : I × J, (a z + ((if z = p then (1 : ℤ) else 0)
          - (if z = q then 1 else 0))) ^ 2 := by
      refine Fintype.sum_equiv (Equiv.prodComm J I) _ _ fun z => ?_
      have h1 : (if z = p.swap then (1 : ℤ) else 0) = if z.swap = p then 1 else 0 :=
        if_congr ⟨fun h => by rw [h, Prod.swap_swap], fun h => by rw [← h, Prod.swap_swap]⟩ rfl rfl
      have h2 : (if z = q.swap then (1 : ℤ) else 0) = if z.swap = q then 1 else 0 :=
        if_congr ⟨fun h => by rw [h, Prod.swap_swap], fun h => by rw [← h, Prod.swap_swap]⟩ rfl rfl
      simp only [Equiv.prodComm_apply, h1, h2]
      rfl
    have hsum' : ∑ z : J × I, ((fun w : J × I => a w.swap) z
        + ((if z = p.swap then (1 : ℤ) else 0) - (if z = q.swap then 1 else 0))) ^ 2 ≤ 2 :=
      hsumeq ▸ hsum
    have hexch' : ∀ i k : J, ∀ j l : I, (fun w : J × I => a w.swap) (i, j)
        + (fun w : J × I => a w.swap) (k, l) = (fun w : J × I => a w.swap) (i, l)
          + (fun w : J × I => a w.swap) (k, j) := by
      intro i k j l
      simp only [Prod.swap_prod_mk]
      linarith [hexch j l i k]
    have hres := eq_zero_of_sum_sq_le_two_aux (Prod.swap_injective.ne hpq) hsum' hexch' hJ h5
    funext z
    simpa using congrFun hres z.swap
  · exact eq_zero_of_sum_sq_le_two_aux hpq hsum hexch hI h5

end CyclicTINormTwoDifference

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype ↥W]
  {σ : classFun ↥W →ₗ[ℂ] classFun G}

namespace IsCyclicTIPair

theorem prodCharEta_apply_of_mem_cyclicTIDiff (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) {v : G}
    (hv : v ∈ cyclicTIDiff W W1 W2) :
    hW.prodCharEta σ i j v =
      hW.prodChar (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) ⟨v, cyclicTIDiff_subset hv⟩ := by
  rw [prodCharEta_eq_coe_apply,
    hσ.apply_eq_of_mem_cyclicTIDiff' hW (hW.basisProdIrr (i, j)) hv, coe_basisProdIrr_apply]

open scoped Classical in
theorem cfInner_prodCharEta_pair (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (z z' : Irr ↥W1 × Irr ↥W2) :
    cfInner (hW.prodCharEta σ z.1 z.2) (hW.prodCharEta σ z'.1 z'.2) =
      if z = z' then 1 else 0 := by
  rw [hW.cfInner_prodCharEta hσ]
  exact if_congr Prod.ext_iff.symm rfl rfl

theorem cfInner_prodCharEta_exchange' (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {f : G → ℂ} (hf : f ∈ classFun G)
    (hf0 : ∀ x ∈ cyclicTIDiff W W1 W2, f x = 0) (i k : Irr ↥W1) (j l : Irr ↥W2) :
    cfInner f (hW.prodCharEta σ i j) + cfInner f (hW.prodCharEta σ k l) =
      cfInner f (hW.prodCharEta σ i l) + cfInner f (hW.prodCharEta σ k j) := by
  have h := fun (i' : Irr ↥W1) (j' : Irr ↥W2) =>
    hW.cfInner_prodCharEta_exchange hσ hf hf0 i' j'
  linear_combination h i j + h k l - h i l - h k j

omit [Fintype G] [Fintype ↥W] in
theorem card_Irr_ge (hW : IsCyclicTIPair W W1 W2) :
    3 ≤ Nat.card (Irr ↥W1) ∧ 3 ≤ Nat.card (Irr ↥W2) ∧
      (5 ≤ Nat.card (Irr ↥W1) ∨ 5 ≤ Nat.card (Irr ↥W2)) := by
  rw [hW.card_Irr_left, hW.card_Irr_right]
  obtain ⟨d1, hd1⟩ := hW.odd_natCard_left
  obtain ⟨d2, hd2⟩ := hW.odd_natCard_right
  have h3 := hW.three_le_natCard_left
  have h4 := hW.three_le_natCard_right
  have h5 := hW.natCard_ne
  omega

theorem eq_signed_sub_prodCharEta (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {i k : Irr ↥W1} {j l : Irr ↥W2}
    (hne : (i, j) ≠ (k, l)) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (hnorm : cfInner f f = 2)
    (hV : ∀ v : ↥W, (v : G) ∈ cyclicTIDiff W W1 W2 →
      f (v : G) = ε * (hW.prodChar (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) v
        - hW.prodChar (k : ↥W1 → ℂ) (l : ↥W2 → ℂ) v)) :
    f = ε • (hW.prodCharEta σ i j - hW.prodCharEta σ k l) := by
  classical
  have hfin1 : Finite ↥W1 := hW.finite_left
  have hfin2 : Finite ↥W2 := hW.finite_right
  have hFI : Fintype (Irr ↥W1) := Fintype.ofFinite _
  have hFJ : Fintype (Irr ↥W2) := Fintype.ofFinite _
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεc : conj ε = ε := by rcases hε with rfl | rfl <;> simp
  set η : Irr ↥W1 × Irr ↥W2 → G → ℂ := fun z => hW.prodCharEta σ z.1 z.2 with hηdef
  set p : Irr ↥W1 × Irr ↥W2 := (i, j) with hp
  set q : Irr ↥W1 × Irr ↥W2 := (k, l) with hq
  set ρ : G → ℂ := η p - η q with hρ
  set F : G → ℂ := ε • f with hFdef
  have hηortho : ∀ z z', cfInner (η z) (η z') = if z = z' then 1 else 0 :=
    fun z z' => hW.cfInner_prodCharEta_pair hσ z z'
  have hηmem : ∀ z, η z ∈ Submodule.span ℤ (Irr G) := fun z =>
    virtualChars_le_span_Irr (hW.prodCharEta_mem_virtualChars hσ z.1 z.2)
  have hFmem : F ∈ Submodule.span ℤ (Irr G) := by
    rcases hε with rfl | rfl
    · simpa [hFdef] using hf
    · simpa [hFdef] using Submodule.neg_mem _ hf
  have hFnorm : cfInner F F = 2 := by
    rw [hFdef, cfInner_smul_left, cfInner_smul_right, hεc, hnorm]
    linear_combination 2 * hε2
  have hρmem : ρ ∈ Submodule.span ℤ (Irr G) := sub_mem (hηmem p) (hηmem q)
  set Φ : G → ℂ := F - ρ with hΦdef
  have hΦmem : Φ ∈ Submodule.span ℤ (Irr G) := sub_mem hFmem hρmem
  have hΦcf : Φ ∈ classFun G := mem_classFun_of_mem_span_Irr hΦmem
  have hΦ0 : ∀ x ∈ cyclicTIDiff W W1 W2, Φ x = 0 := by
    intro x hx
    have h1 : η p x = hW.prodChar (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) ⟨x, cyclicTIDiff_subset hx⟩ :=
      hW.prodCharEta_apply_of_mem_cyclicTIDiff hσ i j hx
    have h2 : η q x = hW.prodChar (k : ↥W1 → ℂ) (l : ↥W2 → ℂ) ⟨x, cyclicTIDiff_subset hx⟩ :=
      hW.prodCharEta_apply_of_mem_cyclicTIDiff hσ k l hx
    have hfx := hV ⟨x, cyclicTIDiff_subset hx⟩ hx
    simp only [hΦdef, hFdef, hρ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2, hfx]
    linear_combination (hW.prodChar (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) ⟨x, cyclicTIDiff_subset hx⟩
      - hW.prodChar (k : ↥W1 → ℂ) (l : ↥W2 → ℂ) ⟨x, cyclicTIDiff_subset hx⟩) * hε2
  choose a ha using fun z => exists_int_cfInner_of_mem_span_Irr hΦmem (hηmem z)
  have hρη : ∀ z, cfInner ρ (η z)
      = ((if z = p then (1 : ℤ) else 0) - (if z = q then 1 else 0) : ℤ) := by
    intro z
    rw [hρ, cfInner_sub_left, hηortho, hηortho]
    push_cast
    rw [if_congr eq_comm rfl rfl, if_congr (eq_comm (a := q) (b := z)) rfl rfl]
  set m : Irr ↥W1 × Irr ↥W2 → ℤ := fun z =>
    a z + ((if z = p then 1 else 0) - (if z = q then 1 else 0)) with hm
  have hFΦρ : F = Φ + ρ := by rw [hΦdef]; ring
  have hFη : ∀ z, cfInner F (η z) = (m z : ℂ) := by
    intro z
    rw [hFΦρ, cfInner_add_left, ha z, hρη z, hm]
    push_cast
    ring
  have hbessel : ∑ z, ‖cfInner F (η z)‖ ^ 2 ≤ (cfInner F F).re :=
    sum_norm_sq_cfInner_le_re_of_cfInner_eq_ite hηortho F
  rw [hFnorm] at hbessel
  have hsumsq : ∑ z, m z ^ 2 ≤ 2 := by
    have h1 : ∀ z, ‖cfInner F (η z)‖ ^ 2 = ((m z : ℝ)) ^ 2 := by
      intro z
      rw [hFη z, Complex.norm_intCast, sq_abs]
    rw [Finset.sum_congr rfl fun z _ => h1 z] at hbessel
    have h2 : ((∑ z, m z ^ 2 : ℤ) : ℝ) ≤ ((2 : ℤ) : ℝ) := by
      push_cast
      simpa using hbessel
    exact_mod_cast h2
  have hexch : ∀ i' k' : Irr ↥W1, ∀ j' l' : Irr ↥W2,
      a (i', j') + a (k', l') = a (i', l') + a (k', j') := by
    intro i' k' j' l'
    have h := hW.cfInner_prodCharEta_exchange' hσ hΦcf hΦ0 i' k' j' l'
    rw [show hW.prodCharEta σ i' j' = η (i', j') from rfl,
      show hW.prodCharEta σ k' l' = η (k', l') from rfl,
      show hW.prodCharEta σ i' l' = η (i', l') from rfl,
      show hW.prodCharEta σ k' j' = η (k', j') from rfl,
      ha, ha, ha, ha] at h
    exact_mod_cast h
  obtain ⟨hc1, hc2, hc5⟩ := hW.card_Irr_ge
  simp only [Nat.card_eq_fintype_card] at hc1 hc2 hc5
  have hpq : p ≠ q := hne
  have ha0 : a = 0 := CyclicTINormTwoDifference.eq_zero_of_sum_sq_le_two
    (a := a) (p := p) (q := q) hpq hsumsq hexch hc1 hc2 hc5
  have hΦρ : cfInner Φ ρ = 0 := by
    rw [hρ, cfInner_sub_right, ha p, ha q, ha0]
    simp
  have hFρ : cfInner F ρ = 2 := by
    rw [hρ, cfInner_sub_right, hFη p, hFη q]
    simp only [hm, ha0, Pi.zero_apply, zero_add, if_neg hpq, if_neg (Ne.symm hpq)]
    push_cast
    ring
  have h1 : cfInner F Φ = 0 := by rw [hΦdef, cfInner_sub_right, hFnorm, hFρ, sub_self]
  have h2 : cfInner Φ F = 0 := by rw [← conj_cfInner, h1, map_zero]
  have hΦΦ : cfInner Φ Φ = 0 := by
    nth_rewrite 2 [hΦdef]
    rw [cfInner_sub_right, h2, hΦρ, sub_self]
  have hΦeq : Φ = 0 := cfInner_self_eq_zero.1 hΦΦ
  have hsub0 : F - ρ = 0 := by rw [← hΦdef]; exact hΦeq
  have hFeq : F = ρ := sub_eq_zero.1 hsub0
  change f = ε • ρ
  funext x
  have hx : ε * f x = ρ x := congrFun hFeq x
  change f x = ε * ρ x
  linear_combination ε * hx - f x * hε2

end IsCyclicTIPair

end CFSG.FeitThompson

end
