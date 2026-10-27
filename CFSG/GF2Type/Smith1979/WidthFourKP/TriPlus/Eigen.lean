module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Basic
public import CFSG.GroupTheory.CommuteOfSqEqOne
public import CFSG.GroupTheory.DiagonalTwentySeven

public section

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup

variable {X : Type*} [Group X]

theorem pow_neg_val {M : Type*} [Group M] {x : M} (hx : x ^ 3 = 1) (a : ZMod 3) :
    x ^ (-a).val = (x ^ a.val)⁻¹ := by
  have h := CFSG.GroupTheory.DiagonalTwentySeven.pow_add_zmod3 x hx a (-a)
  have h0 : a + -a = 0 := add_neg_cancel a
  rw [h0, ZMod.val_zero, pow_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

@[expose] def signAt (i : Fin 3) : Fin 3 → ZMod 3 :=
  fun j => if j = i then -1 else 1

theorem signAt_mul_eq_negAt (i : Fin 3) (c : Fin 3 → ZMod 3) :
    signAt i * c = negAt i c := by
  funext j
  by_cases h : j = i
  · rw [h]
    simp only [signAt, Pi.mul_apply, if_pos rfl, negAt, Function.update_self]
    exact neg_one_mul (c i)
  · simp [signAt, negAt, h]

namespace EigenHyp

theorem exists_eigenBasis {Y L : Subgroup X} [Finite X] (h : EigenHyp Y L) :
    ∃ (σ : Multiplicative (Fin 3 → ZMod 3) →* X) (l : Fin 3 → X),
      EigenBasis Y L σ l := by
  classical
  have hLY : L ≤ Subgroup.normalizer (Y : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    exact h.conj
  have hLc : ∀ s ∈ L, ∀ s' ∈ L, s * s' = s' * s := by
    intro s hs t ht
    exact CFSG.commute_of_sq_eq_one (by simpa [pow_two] using h.sq s hs)
      (by simpa [pow_two] using h.sq t ht)
      (by simpa [pow_two] using h.sq (s * t) (L.mul_mem hs ht))
  have hfaith : ∀ s ∈ L, (∀ y ∈ Y, s * y = y * s) → s = 1 := h.centL
  obtain ⟨-, hcube, e, l, he, F, hl, hdiag, hoff, hF, hsingle, hgen⟩ :=
    CFSG.GroupTheory.DiagonalTwentySeven.exists_diagonal_mulEquiv h.card_Y hLY hLc h.sq
      h.card_L hfaith
  have hcube_e : ∀ i, e i ^ 3 = 1 := fun i => hcube (e i) (he i)
  let σ : Multiplicative (Fin 3 → ZMod 3) →* X := Y.subtype.comp F.toMonoidHom
  refine ⟨σ, l, ?_⟩
  refine ⟨?_, ?_, hl, ?_, ?_⟩
  · intro a b hab
    apply F.injective
    exact Subtype.ext (by simpa [σ] using hab)
  · ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact (F a).2
    · intro hy
      refine ⟨F.symm ⟨y, hy⟩, ?_⟩
      simp [σ]
  · intro i c
    have hσ : ∀ c : Fin 3 → ZMod 3,
        σ (Multiplicative.ofAdd c) = CFSG.GroupTheory.DiagonalTwentySeven.eprod e c := by
      intro c
      simp [σ, hF c]
    rw [hσ c, hσ (negAt i c)]
    have hconj_e : ∀ j, l i * e j * (l i)⁻¹ = if j = i then (e j)⁻¹ else e j := by
      intro j
      by_cases hji : j = i
      · rw [if_pos hji]
        simpa [hji] using hdiag i
      · rw [if_neg hji]
        exact hoff i j (Ne.symm hji)
    have hfac : ∀ j, l i * e j ^ (c j).val * (l i)⁻¹ =
        (if j = i then (e j)⁻¹ else e j) ^ (c j).val := by
      intro j
      rw [← conj_pow, hconj_e j]
    have hdistrib : l i * (e 0 ^ (c 0).val * e 1 ^ (c 1).val * e 2 ^ (c 2).val) *
        (l i)⁻¹ =
        (l i * e 0 ^ (c 0).val * (l i)⁻¹) *
          (l i * e 1 ^ (c 1).val * (l i)⁻¹) *
            (l i * e 2 ^ (c 2).val * (l i)⁻¹) := by group
    unfold CFSG.GroupTheory.DiagonalTwentySeven.eprod
    rw [hdistrib, hfac 0, hfac 1, hfac 2]
    fin_cases i
    · simp [negAt, Function.update, inv_pow]
      exact (pow_neg_val (hx := hcube_e 0) (c 0)).symm
    · simp [negAt, Function.update, inv_pow]
      exact (pow_neg_val (hx := hcube_e 1) (c 1)).symm
    · simp [negAt, Function.update, inv_pow]
      exact (pow_neg_val (hx := hcube_e 2) (c 2)).symm
  · intro s hs
    obtain ⟨c, hc⟩ := hgen s hs
    let K := Subgroup.closure (Set.range l)
    have h0 : l 0 ∈ K :=
      Subgroup.subset_closure (show l 0 ∈ Set.range l from ⟨0, rfl⟩)
    have h1 : l 1 ∈ K :=
      Subgroup.subset_closure (show l 1 ∈ Set.range l from ⟨1, rfl⟩)
    have h2 : l 2 ∈ K :=
      Subgroup.subset_closure (show l 2 ∈ Set.range l from ⟨2, rfl⟩)
    rw [hc]
    exact K.mul_mem (K.mul_mem (K.pow_mem h0 _) (K.pow_mem h1 _)) (K.pow_mem h2 _)

end EigenHyp

theorem signAt_sign (i j : Fin 3) : signAt i j = 1 ∨ signAt i j = -1 := by
  by_cases h : j = i <;> simp [signAt, h]

theorem signAt_mul_self (i : Fin 3) : signAt i * signAt i = 1 := by
  revert i
  decide +kernel


theorem single_eq_nsmul_single (i : Fin 3) (a : ZMod 3) :
    (Pi.single i a : Fin 3 → ZMod 3) =
      a.val • (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) := by
  funext j
  by_cases h : j = i
  · subst h
    simp only [Pi.single_eq_same, Pi.smul_apply]
    rw [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val a).symm
  · simp [Pi.single_eq_of_ne h]

namespace EigenBasis

variable {Y L : Subgroup X}
  {σ : Multiplicative (Fin 3 → ZMod 3) →* X} {l : Fin 3 → X}

theorem mem_iff (E : EigenBasis Y L σ l) {y : X} :
    y ∈ Y ↔ ∃ c : Fin 3 → ZMod 3, σ (Multiplicative.ofAdd c) = y := by
  rw [← E.range_eq]
  exact MonoidHom.mem_range

theorem comm (E : EigenBasis Y L σ l) {y y' : X} (hy : y ∈ Y) (hy' : y' ∈ Y) :
    y * y' = y' * y := by
  obtain ⟨c, rfl⟩ := E.mem_iff.mp hy
  obtain ⟨d, rfl⟩ := E.mem_iff.mp hy'
  calc σ (Multiplicative.ofAdd c) * σ (Multiplicative.ofAdd d)
      = σ (Multiplicative.ofAdd c * Multiplicative.ofAdd d) := (map_mul σ _ _).symm
    _ = σ (Multiplicative.ofAdd (c + d)) := by rw [ofAdd_add]
    _ = σ (Multiplicative.ofAdd (d + c)) := by rw [add_comm]
    _ = σ (Multiplicative.ofAdd d * Multiplicative.ofAdd c) := by rw [ofAdd_add]
    _ = σ (Multiplicative.ofAdd d) * σ (Multiplicative.ofAdd c) := map_mul σ _ _

theorem eb_mem (E : EigenBasis Y L σ l) (i : Fin 3) : eb σ i ∈ Y :=
  E.mem_iff.mpr ⟨Pi.single i 1, rfl⟩

theorem orderOf_eb (E : EigenBasis Y L σ l) (i : Fin 3) : orderOf (eb σ i) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hzero : (3 : ℕ) • (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3) 3]
    have h3z : ((3 : ℕ) : ZMod 3) = 0 := ZMod.natCast_self 3
    rw [h3z, zero_smul]
  refine orderOf_eq_prime ?_ ?_
  · calc eb σ i ^ 3 = σ (Multiplicative.ofAdd (Pi.single i 1)) ^ 3 := rfl
      _ = σ ((Multiplicative.ofAdd (Pi.single i 1)) ^ 3) := (map_pow σ _ 3).symm
      _ = σ (Multiplicative.ofAdd (3 • Pi.single i 1)) := by rw [ofAdd_nsmul]
      _ = σ (Multiplicative.ofAdd (0 : Fin 3 → ZMod 3)) := by rw [hzero]
      _ = 1 := by simp
  · intro h
    have h1 : Multiplicative.ofAdd (Pi.single i 1) = 1 := E.inj (by simpa [eb] using h)
    have h2 : (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) = 0 := by
      simpa using congrArg Multiplicative.toAdd h1
    simpa using congrFun h2 i

theorem mem_zpowers_eb_iff (E : EigenBasis Y L σ l) (i : Fin 3)
    (c : Fin 3 → ZMod 3) :
    σ (Multiplicative.ofAdd c) ∈ zpowers (eb σ i) ↔ ∀ j, j ≠ i → c j = 0 := by
  constructor
  · intro hmem j hj
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hfix : l j * eb σ i * (l j)⁻¹ = eb σ i := by
      have h := E.act j (Pi.single i 1)
      have hupd : negAt j (Pi.single i 1) = Pi.single i 1 := by
        funext k
        by_cases hk : k = j
        · subst hk
          simp [negAt, Pi.single_eq_of_ne hj]
        · simp [negAt, hk]
      rwa [hupd] at h
    have hcomm : Commute (l j) (eb σ i) := by
      refine (commute_iff_eq (l j) (eb σ i)).mpr ?_
      have h := congrArg (fun z => z * l j) hfix
      simpa [mul_assoc] using h
    have hcommz : Commute (l j) (eb σ i ^ n) := hcomm.zpow_right n
    have hfixσ : l j * σ (Multiplicative.ofAdd c) * (l j)⁻¹ =
        σ (Multiplicative.ofAdd c) := by
      calc l j * σ (Multiplicative.ofAdd c) * (l j)⁻¹
          = l j * eb σ i ^ n * (l j)⁻¹ := by rw [← hn]
        _ = (eb σ i ^ n * l j) * (l j)⁻¹ := by rw [hcommz.eq]
        _ = eb σ i ^ n := by simp
        _ = σ (Multiplicative.ofAdd c) := hn
    have hact := E.act j c
    rw [hfixσ] at hact
    have hc : c = negAt j c := Multiplicative.ofAdd.injective (E.inj hact)
    have hcj : c j = -c j := by
      have h := congrFun hc j
      rw [negAt, Function.update_self] at h
      exact h
    have h2 : (2 : ZMod 3) * c j = 0 := by
      have hsum : c j + c j = 0 := add_eq_zero_iff_eq_neg.mpr hcj
      simpa [two_mul] using hsum
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  · intro hzero
    have hc_single : c = (Pi.single i (c i) : Fin 3 → ZMod 3) := by
      funext j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hzero j hji, Pi.single_eq_of_ne hji]
    have hc : c = (c i).val • (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) :=
      hc_single.trans (single_eq_nsmul_single i (c i))
    have hpow : σ (Multiplicative.ofAdd c) = eb σ i ^ (c i).val := by
      calc σ (Multiplicative.ofAdd c)
          = σ (Multiplicative.ofAdd ((c i).val • Pi.single i 1)) := by
              conv_lhs => rw [hc]
        _ = σ ((Multiplicative.ofAdd (Pi.single i 1)) ^ (c i).val) := by rw [ofAdd_nsmul]
        _ = (σ (Multiplicative.ofAdd (Pi.single i 1))) ^ (c i).val := map_pow σ _ _
        _ = eb σ i ^ (c i).val := rfl
    have hz : eb σ i ^ ((c i).val : ℤ) = σ (Multiplicative.ofAdd c) := by
      rw [zpow_natCast, hpow]
    exact hz ▸ Subgroup.zpow_mem_zpowers (eb σ i) ((c i).val : ℤ)

theorem conj_eq_inv_iff (E : EigenBasis Y L σ l) (i : Fin 3) (c : Fin 3 → ZMod 3) :
    l i * σ (Multiplicative.ofAdd c) * (l i)⁻¹ = (σ (Multiplicative.ofAdd c))⁻¹ ↔
      ∀ j, j ≠ i → c j = 0 := by
  constructor
  · intro h j hj
    have hneg : negAt i c = -c := by
      apply Multiplicative.ofAdd.injective
      apply E.inj
      calc σ (Multiplicative.ofAdd (negAt i c))
          = l i * σ (Multiplicative.ofAdd c) * (l i)⁻¹ := (E.act i c).symm
        _ = (σ (Multiplicative.ofAdd c))⁻¹ := h
        _ = σ (Multiplicative.ofAdd (-c)) := by
              rw [ofAdd_neg]
              exact (map_inv σ (Multiplicative.ofAdd c)).symm
    have hcj : c j = -c j := by
      have := congrFun hneg j
      simpa [negAt, Function.update, hj] using this
    have h2 : (2 : ZMod 3) * c j = 0 := by
      have hsum : c j + c j = 0 := add_eq_zero_iff_eq_neg.mpr hcj
      simpa [two_mul] using hsum
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  · intro hzero
    have hneg : negAt i c = -c := by
      funext j
      by_cases hji : j = i
      · subst hji
        rw [negAt, Function.update_self, Pi.neg_apply]
        rfl
      · simp [negAt, hji, hzero j hji]
        exact neg_zero.symm
    calc l i * σ (Multiplicative.ofAdd c) * (l i)⁻¹
        = σ (Multiplicative.ofAdd (negAt i c)) := E.act i c
      _ = σ (Multiplicative.ofAdd (-c)) := by rw [hneg]
      _ = (σ (Multiplicative.ofAdd c))⁻¹ := by
            rw [ofAdd_neg]
            exact map_inv σ (Multiplicative.ofAdd c)

theorem diag (E : EigenBasis Y L σ l) {x : X} (hx : x ∈ L) :
    ∃ s : Fin 3 → ZMod 3, (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ c : Fin 3 → ZMod 3,
        x * σ (Multiplicative.ofAdd c) * x⁻¹ = σ (Multiplicative.ofAdd (s * c)) := by
  let P : X → Prop := fun y =>
    ∃ s : Fin 3 → ZMod 3, (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ c : Fin 3 → ZMod 3,
        y * σ (Multiplicative.ofAdd c) * y⁻¹ = σ (Multiplicative.ofAdd (s * c))
  have hxcl : x ∈ Subgroup.closure (Set.range l) := E.gen hx
  refine Subgroup.closure_induction (p := fun y _ => P y) ?_ ?_ ?_ ?_ hxcl
  · intro y hy
    obtain ⟨i, rfl⟩ := hy
    exact ⟨signAt i, signAt_sign i, by
      intro c
      rw [E.act i c, signAt_mul_eq_negAt]⟩
  · exact ⟨1, by intro i; left; rfl, by intro c; simp⟩
  · intro a b _ha _hb ha hb
    obtain ⟨sa, hsa, hact⟩ := ha
    obtain ⟨sb, hsb, hbact⟩ := hb
    refine ⟨sa * sb, ?_, ?_⟩
    · intro i
      rcases hsa i with h | h <;> rcases hsb i with k | k <;> simp [h, k] <;> decide
    · intro c
      calc a * b * σ (Multiplicative.ofAdd c) * (a * b)⁻¹
          = a * (b * σ (Multiplicative.ofAdd c) * b⁻¹) * a⁻¹ := by group
        _ = a * σ (Multiplicative.ofAdd (sb * c)) * a⁻¹ := by rw [hbact c]
        _ = σ (Multiplicative.ofAdd (sa * (sb * c))) := hact (sb * c)
        _ = σ (Multiplicative.ofAdd ((sa * sb) * c)) := by rw [mul_assoc]
  · intro a _ha ha
    obtain ⟨sa, hsa, hact⟩ := ha
    refine ⟨sa, hsa, ?_⟩
    intro c
    have hss : sa * sa = 1 := by
      funext i
      rcases hsa i with h | h
      · simp [h]
      · simp [h]
        decide
    have h' : a * σ (Multiplicative.ofAdd (sa * c)) * a⁻¹ = σ (Multiplicative.ofAdd c) := by
      have := hact (sa * c)
      rwa [show sa * (sa * c) = c by rw [← mul_assoc, hss, one_mul]] at this
    simp only [inv_inv]
    calc a⁻¹ * σ (Multiplicative.ofAdd c) * a
        = a⁻¹ * (a * σ (Multiplicative.ofAdd (sa * c)) * a⁻¹) * a := by rw [h']
      _ = σ (Multiplicative.ofAdd (sa * c)) := by group

theorem exists_mem_of_signs (E : EigenBasis Y L σ l) (s : Fin 3 → ZMod 3)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    ∃ x ∈ L, ∀ c : Fin 3 → ZMod 3,
      x * σ (Multiplicative.ofAdd c) * x⁻¹ = σ (Multiplicative.ofAdd (s * c)) := by
  classical
  let e : Fin 3 → ℕ := fun i => if s i = 1 then 0 else 1
  have he : ∀ i, e i = 0 ∨ e i = 1 := by
    intro i
    by_cases h : s i = 1 <;> simp [e, h]
  have hsingle : ∀ (i : Fin 3) (n : ℕ), n = 0 ∨ n = 1 → ∀ c : Fin 3 → ZMod 3,
      l i ^ n * σ (Multiplicative.ofAdd c) * (l i ^ n)⁻¹ =
        σ (Multiplicative.ofAdd (signAt i ^ n * c)) := by
    intro i n hn c
    rcases hn with rfl | rfl
    · simp
    · simpa [pow_one, signAt_mul_eq_negAt] using E.act i c
  let x : X := l 0 ^ e 0 * l 1 ^ e 1 * l 2 ^ e 2
  have hxL : x ∈ L := by
    simp only [x]
    exact L.mul_mem (L.mul_mem (L.pow_mem (E.l_mem 0) _) (L.pow_mem (E.l_mem 1) _))
      (L.pow_mem (E.l_mem 2) _)
  refine ⟨x, hxL, ?_⟩
  intro c
  have hsign_coord : ∀ i : Fin 3,
      signAt i ^ e i = (if s i = 1 then (1 : Fin 3 → ZMod 3) else signAt i) := by
    intro i
    by_cases h : s i = 1
    · simp [e, h]
    · simp [e, h]
  have hsign : signAt 0 ^ e 0 * (signAt 1 ^ e 1 * (signAt 2 ^ e 2 * c)) = s * c := by
    have hne : (-1 : ZMod 3) ≠ 1 := by decide
    rw [hsign_coord 0, hsign_coord 1, hsign_coord 2]
    funext j
    fin_cases j <;>
      (rcases hs 0 with h0 | h0 <;> rcases hs 1 with h1 | h1 <;>
        rcases hs 2 with h2 | h2 <;> simp [signAt, h0, h1, h2, hne])
  calc x * σ (Multiplicative.ofAdd c) * x⁻¹
      = l 0 ^ e 0 * (l 1 ^ e 1 * (l 2 ^ e 2 * σ (Multiplicative.ofAdd c) *
          (l 2 ^ e 2)⁻¹) * (l 1 ^ e 1)⁻¹) * (l 0 ^ e 0)⁻¹ := by
        simp only [x]
        group
    _ = l 0 ^ e 0 * (l 1 ^ e 1 * σ (Multiplicative.ofAdd (signAt 2 ^ e 2 * c)) *
          (l 1 ^ e 1)⁻¹) * (l 0 ^ e 0)⁻¹ := by rw [hsingle 2 (e 2) (he 2) c]
    _ = l 0 ^ e 0 * σ (Multiplicative.ofAdd (signAt 1 ^ e 1 * (signAt 2 ^ e 2 * c))) *
          (l 0 ^ e 0)⁻¹ := by rw [hsingle 1 (e 1) (he 1)]
    _ = σ (Multiplicative.ofAdd (signAt 0 ^ e 0 *
          (signAt 1 ^ e 1 * (signAt 2 ^ e 2 * c)))) := by
          rw [hsingle 0 (e 0) (he 0)]
    _ = σ (Multiplicative.ofAdd (s * c)) := by rw [hsign]

theorem apply_eq_eprod (E : EigenBasis Y L σ l) (c : Fin 3 → ZMod 3) :
    σ (Multiplicative.ofAdd c) =
      CFSG.GroupTheory.DiagonalTwentySeven.eprod (eb σ) c := by
  classical
  have h0 : (Pi.single 0 (c 0) : Fin 3 → ZMod 3) =
      (c 0).val • (Pi.single 0 (1 : ZMod 3) : Fin 3 → ZMod 3) :=
    single_eq_nsmul_single 0 (c 0)
  have h1 : (Pi.single 1 (c 1) : Fin 3 → ZMod 3) =
      (c 1).val • (Pi.single 1 (1 : ZMod 3) : Fin 3 → ZMod 3) :=
    single_eq_nsmul_single 1 (c 1)
  have h2 : (Pi.single 2 (c 2) : Fin 3 → ZMod 3) =
      (c 2).val • (Pi.single 2 (1 : ZMod 3) : Fin 3 → ZMod 3) :=
    single_eq_nsmul_single 2 (c 2)
  have hprod : Multiplicative.ofAdd c =
      Multiplicative.ofAdd ((c 0).val • (Pi.single 0 (1 : ZMod 3) : Fin 3 → ZMod 3)) *
        Multiplicative.ofAdd ((c 1).val • (Pi.single 1 (1 : ZMod 3) : Fin 3 → ZMod 3)) *
          Multiplicative.ofAdd ((c 2).val • (Pi.single 2 (1 : ZMod 3) : Fin 3 → ZMod 3)) := by
    calc Multiplicative.ofAdd c
        = Multiplicative.ofAdd (∑ i : Fin 3, (Pi.single i (c i) : Fin 3 → ZMod 3)) := by
            rw [Finset.univ_sum_single]
      _ = ∏ i : Fin 3,
            Multiplicative.ofAdd (Pi.single i (c i) : Fin 3 → ZMod 3) := by
            rw [ofAdd_sum]
      _ = _ := by
            rw [Fin.prod_univ_three, h0, h1, h2]
  calc σ (Multiplicative.ofAdd c)
      = σ (Multiplicative.ofAdd ((c 0).val • (Pi.single 0 (1 : ZMod 3) : Fin 3 → ZMod 3)) *
          Multiplicative.ofAdd ((c 1).val • (Pi.single 1 (1 : ZMod 3) : Fin 3 → ZMod 3)) *
            Multiplicative.ofAdd ((c 2).val • (Pi.single 2 (1 : ZMod 3) : Fin 3 → ZMod 3))) := by
          conv_lhs => rw [hprod]
    _ = (σ (Multiplicative.ofAdd ((c 0).val •
            (Pi.single 0 (1 : ZMod 3) : Fin 3 → ZMod 3))) *
          σ (Multiplicative.ofAdd ((c 1).val •
            (Pi.single 1 (1 : ZMod 3) : Fin 3 → ZMod 3)))) *
        σ (Multiplicative.ofAdd ((c 2).val •
          (Pi.single 2 (1 : ZMod 3) : Fin 3 → ZMod 3))) := by
          rw [map_mul, map_mul]
    _ = ((eb σ 0) ^ (c 0).val * (eb σ 1) ^ (c 1).val) * (eb σ 2) ^ (c 2).val := by
          rw [ofAdd_nsmul, ofAdd_nsmul, ofAdd_nsmul, map_pow, map_pow, map_pow]
          simp [eb]
    _ = CFSG.GroupTheory.DiagonalTwentySeven.eprod (eb σ) c := by
          simp [CFSG.GroupTheory.DiagonalTwentySeven.eprod, eb]

end EigenBasis


theorem mem_left_of_mem_sup {Y L : Subgroup X}
    (hLY : ∀ x ∈ L, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y)
    (hLsq : ∀ x ∈ L, x * x = 1)
    (hYL : ∀ x ∈ Y, x ∈ L → x = 1) {x : X} (hx : x ∈ Y ⊔ L)
    {n : ℕ} (hn : x ^ (3 ^ n) = 1) : x ∈ Y := by
  classical
  have hLN : L ≤ Subgroup.normalizer (Y : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    exact hLY
  have hx' : x ∈ ((Y ⊔ L : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y L hLN] at hx'
  rw [Set.mem_mul] at hx'
  obtain ⟨y, hy, l, hl, hyl⟩ := hx'
  rw [← hyl] at hn ⊢
  have hpow : ∀ m : ℕ, ∃ y' ∈ Y, (y * l) ^ m = y' * l ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, Y.one_mem, by simp⟩
    | succ m ih =>
        obtain ⟨y', hy', h⟩ := ih
        refine ⟨y' * (l ^ m * y * (l ^ m)⁻¹),
          Y.mul_mem hy' (hLY (l ^ m) (L.pow_mem hl m) y hy), ?_⟩
        calc (y * l) ^ (m + 1) = (y * l) ^ m * (y * l) := pow_succ _ _
          _ = (y' * l ^ m) * (y * l) := by rw [h]
          _ = (y' * (l ^ m * y * (l ^ m)⁻¹)) * (l ^ m * l) := by group
          _ = (y' * (l ^ m * y * (l ^ m)⁻¹)) * l ^ (m + 1) := by rw [pow_succ]
  obtain ⟨y', hy', hpy⟩ := hpow (3 ^ n)
  have hl3 : l ^ 3 = l := by
    calc l ^ 3 = l ^ 2 * l := by rw [pow_succ]
      _ = (l * l) * l := by rw [pow_two]
      _ = 1 * l := by rw [hLsq l hl]
      _ = l := one_mul l
  have hlpow : ∀ m : ℕ, l ^ (3 ^ m) = l := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, pow_mul, ih, hl3]
  have h1 : y' * l = 1 := by
    rw [hn, hlpow n] at hpy
    exact hpy.symm
  have hlY : l ∈ Y := by
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Y.inv_mem hy'
  have hl1 : l = 1 := hYL l hlY hl
  simpa [hl1] using hy

end CFSG.GF2Type.Smith1979.TriPlus

end
