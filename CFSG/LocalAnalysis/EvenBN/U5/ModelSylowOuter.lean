module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowA2

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section Outer

theorem ncard_bar_eq_le (h : UnitaryFieldData 2 f K) {a d : K} (ha : a ≠ 0) :
    {t : K | a * h.bar t = d * t}.ncard ≤ 2 ^ f := by
  have := h.finite
  by_cases hex : ∃ t₀ : K, t₀ ≠ 0 ∧ a * h.bar t₀ = d * t₀
  · obtain ⟨t₀, ht₀, he₀⟩ := hex
    have hb0 : h.bar t₀ ≠ 0 := by simpa using ht₀
    have hsub : {t : K | a * h.bar t = d * t} ⊆ (· * t₀) '' {t : K | h.bar t = t} := by
      intro t ht
      have ht : a * h.bar t = d * t := ht
      refine ⟨t / t₀, ?_, div_mul_cancel₀ t ht₀⟩
      change h.bar (t / t₀) = t / t₀
      rw [map_div₀, div_eq_div_iff hb0 ht₀]
      apply mul_left_cancel₀ ha
      linear_combination t₀ * ht - t * he₀
    calc _ ≤ ((· * t₀) '' {t : K | h.bar t = t}).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 2 ^ f := U4.ncard_fixed_mul h ht₀
  · push Not at hex
    have hsub : {t : K | a * h.bar t = d * t} ⊆ {0} := fun t ht => by
      by_contra h0
      exact hex t h0 ht
    calc _ ≤ ({0} : Set K).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 1 := Set.ncard_singleton 0
      _ ≤ 2 ^ f := Nat.one_le_two_pow

theorem inv_mul_e₁e₂_e₂z {x y : hypSU h 2 1} (hx : x ∈ hypUnitriangular h 2 1)
    (hy : y ∈ hypUnitriangular h 2 1) :
    mat (x⁻¹ * y) ιe₁ ιe₂ = mat x ιe₁ ιe₂ + mat y ιe₁ ιe₂ ∧
      mat (x⁻¹ * y) ιe₂ ιz = mat x ιe₂ ιz + mat y ιe₂ ιz := by
  rw [mul_e₁e₂ (inv_mem hx) hy, mul_e₂z (inv_mem hx) hy, mat_inv_apply, mat_inv_apply]
  simp only [hypPartner_inl, hypPartner_inr_inl]
  obtain ⟨r1, r2, -⟩ := U_rel hx
  rw [r1, r2, h.bar_bar, h.bar_bar]
  exact ⟨rfl, rfl⟩

theorem outer_entries {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K} (hA : IsPara A)
    {u v : hypSU h 2 1} (hu : u ∈ hypUnitriangular h 2 1) (hv : v ∈ Vsub h)
    (hrel : A * (mat u).map h.bar = mat (v * u) * A) :
    A ιe₂ ιe₁ * h.bar (mat u ιe₁ ιe₂) = 0 ∧
      A ιe₁ ιe₁ * h.bar (mat u ιe₁ ιe₂) = mat u ιe₁ ιe₂ * A ιe₂ ιe₂ ∧
      A ιe₂ ιe₁ * h.bar (mat u ιe₁ ιz) + A ιe₂ ιe₂ * h.bar (mat u ιe₂ ιz) =
        mat u ιe₂ ιz * A ιz ιz := by
  have hvU : v ∈ hypUnitriangular h 2 1 := Ssub_le_Usub (Vsub_le_Ssub hv)
  have hvu := mul_mem hvU hu
  obtain ⟨-, v1, -, -, -, v5, -⟩ := mem_Vsub'.1 hv
  have w1 : mat (v * u) ιe₁ ιe₂ = mat u ιe₁ ιe₂ := by rw [mul_e₁e₂ hvU hu, v1, zero_add]
  have w3 : mat (v * u) ιe₂ ιz = mat u ιe₂ ιz := by rw [mul_e₂z hvU hu, v5, zero_add]
  obtain ⟨⟨-, u22, u33, -, -⟩, ⟨-, -, -, -, u32, u52, u42, u53, u43, -⟩⟩ := U_entries hu
  obtain ⟨⟨w11, w22, -, -, -⟩, ⟨w21, -, -, -, -, -, -, -, -, -⟩⟩ := U_entries hvu
  have hA1 := hA.1
  have hA2 := hA.2.1
  have hA3 := hA.2.2
  have e1 := congrFun (congrFun hrel ιe₂) ιe₂
  have e2 := congrFun (congrFun hrel ιe₁) ιe₂
  have e3 := congrFun (congrFun hrel ιe₂) ιz
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.map_apply] at e1 e2 e3
  simp only [u22, u33, u32, u52, u42, u53, u43, w11, w22, w21, w1, w3, map_zero, map_one, hA1,
    hA2, hA3, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e1
  · linear_combination e2
  · linear_combination e3

theorem card_le_of_elemAbMod_Vsub_of_outer {E : Subgroup (hypSU h 2 1)}
    (hEU : E ≤ hypUnitriangular h 2 1) (hE : ElemAbMod (Vsub h) E)
    {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K} (hA : IsPara A)
    (hdet : A ιe₁ ιe₁ * A ιe₂ ιe₂ - A ιe₁ ιe₂ * A ιe₂ ιe₁ ≠ 0)
    (hact : ∀ u ∈ E, ∃ v ∈ Vsub h, A * (mat u).map h.bar = mat (v * u) * A) :
    Nat.card E ≤ (2 ^ f) ^ 7 := by
  have := h.charP
  have := h.finite
  have := finite_hypSU (hK := h)
  have key : ∀ u ∈ E, A ιe₂ ιe₁ * h.bar (mat u ιe₁ ιe₂) = 0 ∧
      A ιe₁ ιe₁ * h.bar (mat u ιe₁ ιe₂) = mat u ιe₁ ιe₂ * A ιe₂ ιe₂ ∧
      A ιe₂ ιe₁ * h.bar (mat u ιe₁ ιz) + A ιe₂ ιe₂ * h.bar (mat u ιe₂ ιz) =
        mat u ιe₂ ιz * A ιz ιz := fun u hu => by
    obtain ⟨v, hv, hrel⟩ := hact u hu
    exact outer_entries hA (hEU hu) hv hrel
  have hB₁ : ∀ w ∈ hypUnitriangular h 2 1, mat w ιe₁ ιe₂ = 0 → mat w ιe₂ ιz = 0 →
      w ∈ patSub h sB₁ isPattern_sB₁ := fun w hw h1 h2 => by
    obtain ⟨r1, r2, -⟩ := U_rel hw
    exact mem_patSub_sB₁.2 ⟨hw, h1, by rw [r1, h1, map_zero], h2, by rw [r2, h2, map_zero]⟩
  have hV : ∀ w ∈ hypUnitriangular h 2 1, mat w ιe₁ ιe₂ = 0 → mat w ιe₁ ιz = 0 →
      mat w ιe₂ ιz = 0 → w ∈ Vsub h := fun w hw h1 h2 h3 => by
    obtain ⟨r1, r2, r3, -⟩ := U_rel hw
    exact mem_Vsub'.2 ⟨hw, h1, by rw [r1, h1, map_zero], h2, by rw [r3, h1, h2, map_zero,
      zero_mul, add_zero], h3, by rw [r2, h3, map_zero]⟩
  have hcardB₁ : ∀ H : Subgroup (hypSU h 2 1),
      Nat.card (H ⊓ patSub h sB₁ isPattern_sB₁ : Subgroup _) ≤ (2 ^ f) ^ 6 := fun H =>
    (card_le_of_le inf_le_right).trans card_patSub_sB₁.le
  have hcardV : ∀ H : Subgroup (hypSU h 2 1), Nat.card (H ⊓ Vsub h : Subgroup _) ≤ (2 ^ f) ^ 4 :=
    fun H => (card_le_of_le inf_le_right).trans card_Vsub.le
  have hq : 0 < 2 ^ f := by positivity
  rcases le_Ssub_or_le_sB₂_of_elemAbMod hEU hE with hS | hB
  ·
    have hα : ∀ u ∈ E, mat u ιe₁ ιe₂ = 0 := fun u hu => (mem_Ssub'.1 (hS hu)).2.1
    by_cases hc : A ιe₂ ιe₁ = 0
    · have hd : A ιe₂ ιe₂ ≠ 0 := fun hd => hdet (by rw [hc, hd]; ring)
      have h1 := U4.card_le_card_inf_mul_ncard (H := E) (N := patSub h sB₁ isPattern_sB₁)
        (fun x => mat x ιe₂ ιz) (T := {t : K | A ιe₂ ιe₂ * h.bar t = A ιz ιz * t})
        (Set.toFinite _) (fun x hx => by
          have := (key x hx).2.2
          rw [hc, zero_mul, zero_add, mul_comm (mat x ιe₂ ιz)] at this
          exact this)
        (fun x hx y hy e => by
          have hxy := mul_mem (inv_mem hx) hy
          obtain ⟨a1, a2⟩ := inv_mul_e₁e₂_e₂z (hEU hx) (hEU hy)
          refine hB₁ _ (hEU hxy) (hα _ hxy) ?_
          change mat x ιe₂ ιz = mat y ιe₂ ιz at e
          rw [a2, e, CharTwo.add_self_eq_zero])
      calc Nat.card E ≤ (2 ^ f) ^ 6 * 2 ^ f :=
            h1.trans (Nat.mul_le_mul (hcardB₁ E) (ncard_bar_eq_le h hd))
        _ = (2 ^ f) ^ 7 := by ring
    · have h1 := U4.card_le_card_inf_mul_ncard (H := E) (N := Vsub h)
        (fun x => mat x ιe₂ ιz) (T := Set.univ) (Set.toFinite _) (fun _ _ => Set.mem_univ _)
        (fun x hx y hy e => by
          have hxy := mul_mem (inv_mem hx) hy
          obtain ⟨a1, a2⟩ := inv_mul_e₁e₂_e₂z (hEU hx) (hEU hy)
          change mat x ιe₂ ιz = mat y ιe₂ ιz at e
          have hγ : mat (x⁻¹ * y) ιe₂ ιz = 0 := by rw [a2, e, CharTwo.add_self_eq_zero]
          have hβ := (key _ hxy).2.2
          rw [hγ, map_zero, mul_zero, add_zero, zero_mul] at hβ
          have hβ' : mat (x⁻¹ * y) ιe₁ ιz = 0 := by
            simpa using (mul_eq_zero.1 hβ).resolve_left hc
          exact hV _ (hEU hxy) (hα _ hxy) hβ' hγ)
      rw [Set.ncard_univ, h.card_eq_sq] at h1
      calc Nat.card E ≤ (2 ^ f) ^ 4 * (2 ^ f) ^ 2 := h1.trans (Nat.mul_le_mul_right _ (hcardV E))
        _ ≤ (2 ^ f) ^ 7 := by
          rw [← pow_add]
          exact Nat.pow_le_pow_right hq (by norm_num)
  ·
    have hγ : ∀ u ∈ E, mat u ιe₂ ιz = 0 := fun u hu => (mem_patSub_sB₂.1 (hB hu)).2.1
    by_cases hc : A ιe₂ ιe₁ = 0
    · have ha : A ιe₁ ιe₁ ≠ 0 := fun ha => hdet (by rw [hc, ha]; ring)
      have h1 := U4.card_le_card_inf_mul_ncard (H := E) (N := patSub h sB₁ isPattern_sB₁)
        (fun x => mat x ιe₁ ιe₂) (T := {t : K | A ιe₁ ιe₁ * h.bar t = A ιe₂ ιe₂ * t})
        (Set.toFinite _) (fun x hx => by
          have := (key x hx).2.1
          rw [mul_comm (mat x ιe₁ ιe₂)] at this
          exact this)
        (fun x hx y hy e => by
          have hxy := mul_mem (inv_mem hx) hy
          obtain ⟨a1, a2⟩ := inv_mul_e₁e₂_e₂z (hEU hx) (hEU hy)
          refine hB₁ _ (hEU hxy) ?_ (hγ _ hxy)
          change mat x ιe₁ ιe₂ = mat y ιe₁ ιe₂ at e
          rw [a1, e, CharTwo.add_self_eq_zero])
      calc Nat.card E ≤ (2 ^ f) ^ 6 * 2 ^ f :=
            h1.trans (Nat.mul_le_mul (hcardB₁ E) (ncard_bar_eq_le h ha))
        _ = (2 ^ f) ^ 7 := by ring
    · have hEV : E ≤ Vsub h := fun u hu => by
        obtain ⟨k1, -, k3⟩ := key u hu
        rw [hγ u hu, map_zero, mul_zero, add_zero, zero_mul] at k3
        have hα : mat u ιe₁ ιe₂ = 0 := by simpa using (mul_eq_zero.1 k1).resolve_left hc
        have hβ : mat u ιe₁ ιz = 0 := by simpa using (mul_eq_zero.1 k3).resolve_left hc
        exact hV u (hEU hu) hα hβ (hγ u hu)
      calc Nat.card E ≤ Nat.card (Vsub h) := card_le_of_le hEV
        _ = (2 ^ f) ^ 4 := card_Vsub
        _ ≤ (2 ^ f) ^ 7 := Nat.pow_le_pow_right hq (by norm_num)

theorem act_pow (x : Gam h) (g : hypSU h 2 1) (n : ℕ) : act h x (g ^ n) = act h x g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, act_one]
  | succ n ih => rw [pow_succ, pow_succ, act_mul, ih]

theorem eq_of_innM_eq_of_two (hZ : center (hypPSU h 2 1) = ⊥) {g g' : hypSU h 2 1}
    (he : innM h g = innM h g') {k : ℕ} (hg : g ^ 2 ^ k = 1) (hg' : g' ^ 2 ^ k = 1) :
    g = g' := by
  have h1 : innM h (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have hz := (innM_eq_one_iff hZ).1 h1
  set z := g⁻¹ * g' with hzdef
  have hg'z : g' = g * z := by rw [hzdef]; group
  have hzk : z ^ 2 ^ k = 1 := by
    have hcomm : Commute g z := scalar_central hz g
    have := hcomm.mul_pow (2 ^ k)
    rw [← hg'z, hg', hg, one_mul] at this
    exact this.symm
  obtain ⟨c, -, hc5, hc⟩ := hz
  have hck : c ^ 2 ^ k = 1 := by
    have e1 : ((z ^ 2 ^ k : hypSU h 2 1) : GL (HypIndex 2 1) K) = 1 := by rw [hzk]; rfl
    rw [Subgroup.coe_pow, hc, ← map_pow] at e1
    have e2 := congrArg (fun B : GL (HypIndex 2 1) K =>
      (B : Matrix (HypIndex 2 1) (HypIndex 2 1) K) ιe₁ ιe₁) e1
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at e2
    exact Units.ext (by simpa using e2)
  have hc1 : c = 1 := by
    have hcop : Nat.Coprime 5 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h5 : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one hc5
    have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd h5 h2))
  have hz1 : z = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hc, hc1, map_one]
    rfl
  rw [hg'z, hz1, mul_one]

theorem act_eq_mul_of_commutator_mem (hZ : center (hypPSU h 2 1) = ⊥)
    {N : Subgroup (hypSU h 2 1)} (hN : N ≤ hypUnitriangular h 2 1) {x : Gam h}
    {u : hypSU h 2 1} (hu : u ∈ hypUnitriangular h 2 1)
    (hc : ⁅Phi h x, innM h u⁆ ∈ N.map (innM h)) : ∃ v ∈ N, act h x u = v * u := by
  obtain ⟨v, hv, hve⟩ := hc
  refine ⟨v, hv, ?_⟩
  have h1 : innM h (act h x u) = innM h (v * u) := by
    rw [map_mul, hve, commutatorElement_def, ← Phi_mul_innM_mul_inv]
    group
  have hU := CFSG.RankThree.CentralLiftU.isPGroup_hypUnitriangular (h := h) (r := 2)
    (ε := 1) (by norm_num)
  obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
  obtain ⟨l, hl⟩ := hU ⟨v * u, mul_mem (hN hv) hu⟩
  have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hl' : (v * u) ^ 2 ^ l = 1 := by simpa using congrArg Subtype.val hl
  refine eq_of_innM_eq_of_two hZ h1 (k := k + l) ?_ ?_
  · rw [← act_pow, pow_add, pow_mul, hk', one_pow, act_one]
  · rw [pow_add, mul_comm, pow_mul, hl', one_pow]

theorem act_eq_mul_of_commutator_mem_Vh (hZ : center (hypPSU h 2 1) = ⊥) {x : Gam h}
    {u : hypSU h 2 1} (hu : u ∈ hypUnitriangular h 2 1) (hc : ⁅Phi h x, innM h u⁆ ∈ Vh h) :
    ∃ v ∈ Vsub h, act h x u = v * u :=
  act_eq_mul_of_commutator_mem hZ (Vsub_le_Ssub.trans Ssub_le_Usub) hu hc

theorem right_eq_of_sq_mem_Pi {ρ : MulAut (hypPSU h 2 1)} (hρ : ρ * ρ ∈ Pi h) {x : Gam h}
    (hx : Phi h x = ρ) : x.1.right = 1 ∨ ∀ c, x.1.right c = h.bar c := by
  have h1 : Phi h (x * x) = ρ * ρ := by rw [map_mul, hx]
  have h2 := (mem_Dlin_iff h1).1 (Pi_le_Dlin hρ)
  rw [Subgroup.coe_mul, SemidirectProduct.mul_right] at h2
  rcases UnitaryHigher.ringEquiv_eq_refl_or_bar h h2 with e | e
  · exact Or.inl e
  · exact Or.inr e

theorem Vh_le_Pi : Vh h ≤ Pi h := Vh_le_Sh.trans (Sh_le_Uh.trans Uh_le_Pi)

theorem right_eq_bar_of_sq_mem_Vh {ρ : MulAut (hypPSU h 2 1)} (hρ : ρ * ρ ∈ Vh h)
    (hρP : ρ ∉ Pi h) {x : Gam h} (hx : Phi h x = ρ) : ∀ c, x.1.right c = h.bar c := by
  refine (right_eq_of_sq_mem_Pi (Vh_le_Pi hρ) hx).resolve_left fun e => hρP ?_
  refine Dlin_two_mem_Pi ((mem_Dlin_iff hx).2 e) (k := 2) ?_
  have e4 : ρ ^ 2 ^ 2 = (ρ * ρ) * (ρ * ρ) := by norm_num [pow_succ, mul_assoc]
  rw [e4, Vh_sq hρ]

theorem card_le_two_mul_inf_Pi_of_sq {X : Subgroup (MulAut (hypPSU h 2 1))}
    (hsq : ∀ ρ ∈ X, ρ * ρ ∈ Vh h) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ Pi h : Subgroup _) := by
  classical
  have := finite_mulAut_hyp h
  by_cases hall : ∀ ρ ∈ X, ρ ∈ Pi h
  · calc Nat.card X ≤ Nat.card (X ⊓ Pi h : Subgroup _) :=
          Nat.card_le_card_of_injective (fun ρ => ⟨ρ, ρ.2, hall ρ ρ.2⟩)
            (fun a b e => Subtype.ext (by simpa using congrArg Subtype.val e))
      _ ≤ 2 * Nat.card (X ⊓ Pi h : Subgroup _) := Nat.le_mul_of_pos_left _ (by norm_num)
  push Not at hall
  obtain ⟨ρ₀, hρ₀, hρ₀P⟩ := hall
  obtain ⟨x₀, hx₀⟩ := Phi_surjective h ρ₀
  have hmem : ∀ ρ ∈ X, ρ ∉ Pi h → ρ₀ * ρ ∈ Pi h := by
    intro ρ hρ hρP
    obtain ⟨x, hx⟩ := Phi_surjective h ρ
    have hlift : Phi h (x₀ * x) = ρ₀ * ρ := by rw [map_mul, hx₀, hx]
    have hr : (x₀ * x).1.right = 1 := by
      rw [Subgroup.coe_mul, SemidirectProduct.mul_right]
      ext c
      change x₀.1.right (x.1.right c) = c
      rw [right_eq_bar_of_sq_mem_Vh (hsq ρ hρ) hρP hx c,
        right_eq_bar_of_sq_mem_Vh (hsq ρ₀ hρ₀) hρ₀P hx₀ (h.bar c), h.bar_bar]
    refine Dlin_two_mem_Pi ((mem_Dlin_iff hlift).2 hr) (k := 2) ?_
    have e4 : (ρ₀ * ρ) ^ 2 ^ 2 = ((ρ₀ * ρ) * (ρ₀ * ρ)) * ((ρ₀ * ρ) * (ρ₀ * ρ)) := by
      norm_num [pow_succ, mul_assoc]
    rw [e4, Vh_sq (hsq _ (X.mul_mem hρ₀ hρ))]
  let φ : X → (X ⊓ Pi h : Subgroup _) × Bool := fun ρ =>
    if hP : (ρ : MulAut (hypPSU h 2 1)) ∈ Pi h then (⟨ρ, ρ.2, hP⟩, false)
    else (⟨ρ₀ * ρ, X.mul_mem hρ₀ ρ.2, hmem ρ ρ.2 hP⟩, true)
  have hinj : Function.Injective φ := by
    intro a b hab
    by_cases ha : (a : MulAut (hypPSU h 2 1)) ∈ Pi h <;>
      by_cases hb : (b : MulAut (hypPSU h 2 1)) ∈ Pi h <;>
      simp only [φ, ha, hb, dite_true, dite_false] at hab
    · exact Subtype.ext (congrArg (fun p => (p.1 : MulAut (hypPSU h 2 1))) hab)
    · exact absurd (congrArg Prod.snd hab) (by simp)
    · exact absurd (congrArg Prod.snd hab) (by simp)
    · exact Subtype.ext (mul_left_cancel (congrArg (fun p => (p.1 : MulAut (hypPSU h 2 1))) hab))
  calc Nat.card X ≤ Nat.card ((X ⊓ Pi h : Subgroup _) × Bool) :=
        Nat.card_le_card_of_injective φ hinj
    _ = 2 * Nat.card (X ⊓ Pi h : Subgroup _) := by rw [Nat.card_prod]; simp [mul_comm]

theorem elemAbMod_Vh_T (hZ : center (hypPSU h 2 1) = ⊥) (hf : 2 ≤ f)
    {T : Subgroup (MulAut (hypPSU h 2 1))} (hTU : T ⊓ Pi h = Uh h)
    {X : Subgroup (MulAut (hypPSU h 2 1))} (hXT : X ≤ T) (hX : ElemAbMod (Vh h) X) :
    Nat.card X ≤ (2 ^ f) ^ 8 ∧
      ((2 ^ f) ^ 8 ≤ Nat.card X → X = Sh h ∨ X = (Vsub h ⊔ A₂sub h).map (innM h)) := by
  classical
  have := finite_mulAut_hyp h
  set X' : Subgroup (hypSU h 2 1) := X.comap (innM h) ⊓ hypUnitriangular h 2 1 with hX'
  have hX'U : X' ≤ hypUnitriangular h 2 1 := inf_le_right
  have hmap : X'.map (innM h) = X ⊓ Pi h := by
    apply le_antisymm
    · rintro _ ⟨u, ⟨hu, huU⟩, rfl⟩
      exact ⟨hu, Uh_le_Pi ⟨u, huU, rfl⟩⟩
    · intro ρ hρ
      have hρU : ρ ∈ Uh h := by rw [← hTU]; exact ⟨hXT hρ.1, hρ.2⟩
      obtain ⟨u, huU, rfl⟩ := hρU
      exact ⟨u, ⟨hρ.1, huU⟩, rfl⟩
  have hcard' : Nat.card X' = Nat.card (X ⊓ Pi h : Subgroup _) := by
    rw [← hmap, card_map_innM hZ hX'U]
  have hVin : ∀ g ∈ hypUnitriangular h 2 1, innM h g ∈ Vh h → g ∈ Vsub h := by
    rintro g hg ⟨v, hv, hve⟩
    rw [← innM_injOn hZ (Ssub_le_Usub (Vsub_le_Ssub hv)) hg hve]
    exact hv
  have hX'E : ElemAbMod (Vsub h) X' := by
    refine ⟨fun u hu => hVin _ (mul_mem (hX'U hu) (hX'U hu)) ?_, fun u hu w hw => ?_⟩
    · rw [map_mul]
      exact hX.1 _ hu.1
    · refine hVin _ ?_ ?_
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (hX'U hu) (hX'U hw)) (inv_mem (hX'U hu)))
          (inv_mem (hX'U hw))
      · rw [map_commutatorElement]
        exact hX.2 _ hu.1 _ hw.1
  by_cases hall : ∀ ρ ∈ X, ρ ∈ Pi h
  · have hXP : X ⊓ Pi h = X := inf_eq_left.2 hall
    have hc := card_le_of_elemAbMod_Vsub hX'U hX'E
    rw [hcard', hXP] at hc
    refine ⟨hc.1, fun hge => ?_⟩
    have hmap' : X'.map (innM h) = X := by rw [hmap, hXP]
    rcases hc.2 hge with e | e
    · left
      rw [← hmap', e]
      rfl
    · right
      rw [← hmap', e]
  push Not at hall
  obtain ⟨ρ₀, hρ₀, hρ₀P⟩ := hall
  obtain ⟨x₀, hx₀⟩ := Phi_surjective h ρ₀
  have hbar := right_eq_bar_of_sq_mem_Vh (hX.1 ρ₀ hρ₀) hρ₀P hx₀
  have hρN : Phi h x₀ ∈ normalizer (Vh h : Set (MulAut (hypPSU h 2 1))) := by
    rw [hx₀]
    exact mem_normalizer_Vh hZ hTU (hXT hρ₀)
  have hP := isParaW_of_act_mem fun v hv => act_mem_Vsub hZ hρN hv
  have hdet := det_blkEE_ne_zero hP
  rw [Matrix.det_fin_two] at hdet
  have hact : ∀ u ∈ X', ∃ v ∈ Vsub h, lmat x₀ * (mat u).map h.bar = mat (v * u) * lmat x₀ := by
    intro u hu
    obtain ⟨v, hv, hvu⟩ := act_eq_mul_of_commutator_mem_Vh hZ (hX'U hu)
      (by rw [hx₀]; exact hX.2 _ hρ₀ _ hu.1)
    refine ⟨v, hv, ?_⟩
    rw [← hvu, ← lmat_mul_map]
    congr 1
    ext i j
    simp [hbar]
  have h7 := card_le_of_elemAbMod_Vsub_of_outer hX'U hX'E (isPara_of_paraW hP) hdet hact
  have hq : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have hlt : 2 * (2 ^ f) ^ 7 < (2 ^ f) ^ 8 := by
    have e : (2 ^ f) ^ 8 = 2 ^ f * (2 ^ f) ^ 7 := by ring
    have hpos : 0 < (2 ^ f) ^ 7 := by positivity
    rw [e]
    nlinarith
  have hX8 : Nat.card X < (2 ^ f) ^ 8 := by
    calc Nat.card X ≤ 2 * Nat.card (X ⊓ Pi h : Subgroup _) := card_le_two_mul_inf_Pi_of_sq hX.1
      _ = 2 * Nat.card X' := by rw [hcard']
      _ ≤ 2 * (2 ^ f) ^ 7 := Nat.mul_le_mul_left _ h7
      _ < _ := hlt
  exact ⟨hX8.le, fun hge => absurd hge (not_le.2 hX8)⟩

theorem right_pow (x : Gam h) (n : ℕ) : (x ^ n).1.right = x.1.right ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, Subgroup.coe_mul, SemidirectProduct.mul_right, ih]

theorem conj_mem_Zh (hZ : center (hypPSU h 2 1) = ⊥) {T : Subgroup (MulAut (hypPSU h 2 1))}
    (hTU : T ⊓ Pi h = Uh h) {ρ : MulAut (hypPSU h 2 1)} (hρT : ρ ∈ T) {z : hypSU h 2 1}
    (hz : z ∈ ZPsub h) : ρ * innM h z * ρ⁻¹ ∈ (ZPsub h).map (innM h) := by
  have hUh : ∀ σ ∈ T, ∀ u ∈ hypUnitriangular h 2 1, ∃ u' ∈ hypUnitriangular h 2 1,
      σ * innM h u * σ⁻¹ = innM h u' := by
    intro σ hσ u hu
    have hmem : σ * innM h u * σ⁻¹ ∈ T ⊓ Pi h := by
      have huT : innM h u ∈ T ⊓ Pi h := by rw [hTU]; exact ⟨u, hu, rfl⟩
      exact ⟨T.mul_mem (T.mul_mem hσ huT.1) (T.inv_mem hσ),
        (inferInstance : (Pi h).Normal).conj_mem _ huT.2 σ⟩
    rw [hTU] at hmem
    obtain ⟨u', hu', e⟩ := hmem
    exact ⟨u', hu', e.symm⟩
  have hzU := ZPsub_le_U hz
  obtain ⟨w, hwU, hw⟩ := hUh ρ hρT z hzU
  rw [hw]
  refine ⟨w, ?_, rfl⟩
  rw [← centerIn_U]
  refine ⟨hwU, mem_centralizer_iff.2 fun u hu => ?_⟩
  obtain ⟨u'', hu''U, hu''⟩ := hUh ρ⁻¹ (T.inv_mem hρT) u hu
  rw [inv_inv] at hu''
  have hzc : z * u'' = u'' * z := by
    rw [← centerIn_U] at hz
    exact (mem_centralizer_iff.1 hz.2 u'' hu''U).symm
  refine innM_injOn hZ (mul_mem hu hwU) (mul_mem hwU hu) ?_
  have hu' : innM h u = ρ * innM h u'' * ρ⁻¹ := by
    rw [← hu'']
    group
  rw [map_mul, map_mul, ← hw, hu']
  calc ρ * innM h u'' * ρ⁻¹ * (ρ * innM h z * ρ⁻¹) = ρ * innM h (u'' * z) * ρ⁻¹ := by
        rw [map_mul]; group
    _ = ρ * innM h (z * u'') * ρ⁻¹ := by rw [hzc]
    _ = ρ * innM h z * ρ⁻¹ * (ρ * innM h u'' * ρ⁻¹) := by rw [map_mul]; group

theorem commutator_pow_mem_Zh (hZ : center (hypPSU h 2 1) = ⊥)
    {T : Subgroup (MulAut (hypPSU h 2 1))} (hTU : T ⊓ Pi h = Uh h)
    {ρ : MulAut (hypPSU h 2 1)} (hρT : ρ ∈ T) {ξ : MulAut (hypPSU h 2 1)}
    (hξ : ⁅ρ, ξ⁆ ∈ (ZPsub h).map (innM h)) (n : ℕ) :
    ⁅ρ ^ n, ξ⁆ ∈ (ZPsub h).map (innM h) := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp [commutatorElement_def]⟩
  | succ n ih =>
    have e : ⁅ρ ^ (n + 1), ξ⁆ = (ρ * ⁅ρ ^ n, ξ⁆ * ρ⁻¹) * ⁅ρ, ξ⁆ := by
      simp only [commutatorElement_def, pow_succ']
      group
    rw [e]
    obtain ⟨z, hz, hze⟩ := ih
    rw [← hze]
    exact mul_mem (conj_mem_Zh hZ hTU hρT hz) hξ

theorem exists_lift_pow_bar {T : Subgroup (MulAut (hypPSU h 2 1))} (hT2 : IsPGroup 2 T)
    {ρ : MulAut (hypPSU h 2 1)} (hρT : ρ ∈ T) (hρP : ρ ∉ Pi h) :
    ∃ n : ℕ, ∃ x : Gam h, Phi h x = ρ ^ n ∧ ∀ c, x.1.right c = h.bar c := by
  classical
  obtain ⟨j, hj⟩ := hT2 ⟨ρ, hρT⟩
  have hj' : ρ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  obtain ⟨x, hx⟩ := Phi_surjective h ρ
  have hex : ∃ i, x.1.right ^ 2 ^ i = 1 := ⟨j, by
    rw [← right_pow]
    exact (Phi_eq_one_iff.1 (by rw [map_pow, hx, hj'])).1⟩
  have hσ1 : x.1.right ^ 2 ^ 0 ≠ 1 := by
    rw [pow_zero, pow_one]
    exact fun e => hρP (Dlin_two_mem_Pi ((mem_Dlin_iff hx).2 e) hj')
  have hspec := Nat.find_spec hex
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun e => hσ1 (by rw [← e]; exact hspec)
  rw [hi] at hspec
  have hτ : x.1.right ^ 2 ^ i ≠ 1 := Nat.find_min hex (by omega)
  have hττ : x.1.right ^ 2 ^ i * x.1.right ^ 2 ^ i = 1 := by
    rw [← pow_add, ← hspec]
    ring_nf
  have hτbar := (UnitaryHigher.ringEquiv_eq_refl_or_bar h hττ).resolve_left hτ
  exact ⟨2 ^ i, x ^ 2 ^ i, by rw [map_pow, hx], fun c => by rw [right_pow, hτbar c]⟩

theorem outer_entries_A₂ {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K} (hA : IsPara A)
    (hA21 : A ιe₂ ιe₁ = 0) {a z : hypSU h 2 1} (ha : a ∈ A₂sub h) (hz : z ∈ ZPsub h)
    (hrel : A * (mat a).map h.bar = mat (z * a) * A) :
    A ιe₁ ιe₁ * h.bar (mat a ιe₁ ιe₂) = mat a ιe₁ ιe₂ * A ιe₂ ιe₂ ∧
      (mat a ιe₁ ιe₂ = 0 → A ιe₁ ιe₁ * h.bar (mat a ιe₁ ιz) = mat a ιe₁ ιz * A ιz ιz) ∧
      (mat a ιe₁ ιe₂ = 0 → mat a ιe₁ ιz = 0 →
        A ιe₂ ιe₂ * h.bar (mat a ιe₂ ιf₁) = mat a ιe₂ ιf₁ * A ιf₁ ιf₁) := by
  have haU := A₂sub_le_U ha
  have hza := mul_mem (ZPsub_le_U hz) haU
  obtain ⟨hzE, -⟩ := mul_ZPsub_entries hz haU
  obtain ⟨-, a1, -, a3⟩ := mem_A₂sub.1 ha
  obtain ⟨c1, c2, -⟩ := A₂_rel ha
  obtain ⟨⟨-, u22, u33, u44, -⟩, ⟨-, -, -, -, u32, u52, u42, u53, u43, -⟩⟩ := U_entries haU
  obtain ⟨⟨w11, w22, -, -, -⟩, ⟨w21, -, -, -, -, -, -, -, -, -⟩⟩ := U_entries hza
  have w12 : mat (z * a) ιe₁ ιe₂ = mat a ιe₁ ιe₂ := hzE _ _ (by decide) (by decide)
  have w13 : mat (z * a) ιe₁ ιz = mat a ιe₁ ιz := hzE _ _ (by decide) (by decide)
  have w23 : mat (z * a) ιe₂ ιz = mat a ιe₂ ιz := hzE _ _ (by decide) (by decide)
  have w24 : mat (z * a) ιe₂ ιf₁ = mat a ιe₂ ιf₁ := hzE _ _ (by decide) (by decide)
  have w25 : mat (z * a) ιe₂ ιf₂ = mat a ιe₂ ιf₂ := hzE _ _ (by decide) (by decide)
  have hA1 := hA.1
  have hA2 := hA.2.1
  have hA3 := hA.2.2
  have e1 := congrFun (congrFun hrel ιe₁) ιe₂
  have e2 := congrFun (congrFun hrel ιe₁) ιz
  have e3 := congrFun (congrFun hrel ιe₂) ιf₁
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.map_apply] at e1 e2 e3
  simp only [u22, u33, u44, u32, u52, u42, u53, u43, w11, w22,
    w21, w12, w13, w23, w24, w25, a1, a3, hA21, map_zero, map_one, hA1, hA2, hA3, mul_zero,
    zero_mul, mul_one, one_mul, add_zero, zero_add] at e1 e2 e3
  refine ⟨?_, fun h1 => ?_, fun h1 h2 => ?_⟩
  · linear_combination e1
  · rw [h1, zero_mul, add_zero] at e2
    linear_combination e2
  · rw [c1, c2, h1, h2, map_zero, map_zero] at e3
    linear_combination e3

theorem lmat_e₂e₁_eq_zero (hZ : center (hypPSU h 2 1) = ⊥) {T : Subgroup (MulAut (hypPSU h 2 1))}
    (hTU : T ⊓ Pi h = Uh h) {x : Gam h} (hxT : Phi h x ∈ T) : lmat x ιe₂ ιe₁ = 0 := by
  have hz₁ : z₁SU h ∈ ZPsub h := z₁SU_mem_ZPsub
  obtain ⟨z', hz', hze⟩ := conj_mem_Zh hZ hTU hxT hz₁
  rw [Phi_mul_innM_mul_inv] at hze
  have hsq : act h x (z₁SU h) * act h x (z₁SU h) = 1 := by
    rw [← act_mul, Vsub_sq (ZPsub_le_Vsub hz₁), act_one]
  have e := eq_of_innM_eq_of_sq hZ hze (Vsub_sq (ZPsub_le_Vsub hz')) hsq
  have hrel := lmat_mul_map x (z₁SU h)
  rw [← e] at hrel
  have e1 := congrFun (congrFun hrel ιe₂) ιf₁
  obtain ⟨hzU, -, k2, -, k4, -, -, -, k8, -⟩ := mem_ZPsub.1 hz₁
  obtain ⟨hz'U, -, -, -, -, l5, -, -, l8, l9⟩ := mem_ZPsub.1 hz'
  obtain ⟨⟨-, -, -, u44, -⟩, ⟨-, -, -, -, -, -, -, -, -, -⟩⟩ := U_entries hzU
  obtain ⟨⟨-, v22, -, -, -⟩, ⟨v21, -, -, -, -, -, -, -, -, -⟩⟩ := U_entries hz'U
  have k0 := mat_z₁SU_e₁f₁ (h := h)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.map_apply] at e1
  simp only [k0, k2, k4, k8, u44, v22, v21, l5, l8, l9, map_zero, map_one, mul_zero,
    zero_mul, mul_one, one_mul, add_zero, zero_add] at e1
  linear_combination e1

theorem card_le_of_outer_A₂sub {Y : Subgroup (hypSU h 2 1)} (hYA : Y ≤ A₂sub h)
    {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K} (hA : IsPara A) (hA21 : A ιe₂ ιe₁ = 0)
    (hdet : A ιe₁ ιe₁ * A ιe₂ ιe₂ - A ιe₁ ιe₂ * A ιe₂ ιe₁ ≠ 0)
    (hact : ∀ a ∈ Y, ∃ z ∈ ZPsub h, A * (mat a).map h.bar = mat (z * a) * A) :
    Nat.card Y ≤ (2 ^ f) ^ 4 := by
  have := h.charP
  have := h.finite
  have := finite_hypSU (hK := h)
  rw [hA21, mul_zero, sub_zero] at hdet
  have ha₁ : A ιe₁ ιe₁ ≠ 0 := left_ne_zero_of_mul hdet
  have ha₂ : A ιe₂ ιe₂ ≠ 0 := right_ne_zero_of_mul hdet
  have key : ∀ a ∈ Y, A ιe₁ ιe₁ * h.bar (mat a ιe₁ ιe₂) = mat a ιe₁ ιe₂ * A ιe₂ ιe₂ ∧
      (mat a ιe₁ ιe₂ = 0 → A ιe₁ ιe₁ * h.bar (mat a ιe₁ ιz) = mat a ιe₁ ιz * A ιz ιz) ∧
      (mat a ιe₁ ιe₂ = 0 → mat a ιe₁ ιz = 0 →
        A ιe₂ ιe₂ * h.bar (mat a ιe₂ ιf₁) = mat a ιe₂ ιf₁ * A ιf₁ ιf₁) := fun a ha => by
    obtain ⟨z, hz, hrel⟩ := hact a ha
    exact outer_entries_A₂ hA hA21 (hYA ha) hz hrel
  have h1 := U4.card_le_card_inf_mul_ncard (H := Y) (N := A₂sub h ⊓ Ssub h)
    (fun x => mat x ιe₁ ιe₂) (T := {t : K | A ιe₁ ιe₁ * h.bar t = A ιe₂ ιe₂ * t})
    (Set.toFinite _) (fun x hx => by
      change _ = _
      rw [(key x hx).1, mul_comm])
    (fun x hx y hy e => by
      have hxy := mul_mem (inv_mem (hYA hx)) (hYA hy)
      refine ⟨hxy, (mem_Ssub'.2 ⟨A₂sub_le_U hxy, ?_, ?_⟩)⟩
      · change mat x ιe₁ ιe₂ = mat y ιe₁ ιe₂ at e
        rw [(A₂_inv_mul (hYA hx) (hYA hy)).1, e, CharTwo.add_self_eq_zero]
      · rw [(A₂_rel hxy).1, (A₂_inv_mul (hYA hx) (hYA hy)).1]
        change mat x ιe₁ ιe₂ = mat y ιe₁ ιe₂ at e
        rw [e, CharTwo.add_self_eq_zero, map_zero])
  set Y₁ := Y ⊓ (A₂sub h ⊓ Ssub h) with hY₁
  have hY₁Y : ∀ x ∈ Y₁, x ∈ Y := fun x hx => (mem_inf.1 hx).1
  have hY₁A : ∀ x ∈ Y₁, x ∈ A₂sub h := fun x hx => (mem_inf.1 (mem_inf.1 hx).2).1
  have hα : ∀ x ∈ Y₁, mat x ιe₁ ιe₂ = 0 := fun x hx =>
    (mem_Ssub'.1 (mem_inf.1 (mem_inf.1 hx).2).2).2.1
  have h2 := U4.card_le_card_inf_mul_ncard (H := Y₁) (N := Z₂Psub h)
    (fun x => mat x ιe₁ ιz) (T := {t : K | A ιe₁ ιe₁ * h.bar t = A ιz ιz * t})
    (Set.toFinite _) (fun x hx => by
      change _ = _
      rw [(key x (hY₁Y x hx)).2.1 (hα x hx), mul_comm])
    (fun x hx y hy e => by
      have hxy := mul_mem (inv_mem (hY₁A x hx)) (hY₁A y hy)
      obtain ⟨n1, n2, -⟩ := A₂_inv_mul (hY₁A x hx) (hY₁A y hy)
      change mat x ιe₁ ιz = mat y ιe₁ ιz at e
      exact mem_Z₂Psub_of_A₂ hxy (by rw [n1, hα x hx, hα y hy, add_zero])
        (by rw [n2, e, CharTwo.add_self_eq_zero]))
  set Y₂ := Y₁ ⊓ Z₂Psub h with hY₂
  have hY₂Y₁ : ∀ x ∈ Y₂, x ∈ Y₁ := fun x hx => (mem_inf.1 hx).1
  have hβ : ∀ x ∈ Y₂, mat x ιe₁ ιz = 0 := fun x hx =>
    (mem_Z₂Psub.1 (mem_inf.1 hx).2).2.2.2.1
  have h3 := U4.card_le_card_inf_mul_ncard (H := Y₂) (N := ZPsub h)
    (fun x => mat x ιe₂ ιf₁) (T := {t : K | A ιe₂ ιe₂ * h.bar t = A ιf₁ ιf₁ * t})
    (Set.toFinite _) (fun x hx => by
      change _ = _
      rw [(key x (hY₁Y x (hY₂Y₁ x hx))).2.2 (hα x (hY₂Y₁ x hx)) (hβ x hx), mul_comm])
    (fun x hx y hy e => by
      have hxA := hY₁A x (hY₂Y₁ x hx)
      have hyA := hY₁A y (hY₂Y₁ y hy)
      obtain ⟨n1, n2, n3⟩ := A₂_inv_mul hxA hyA
      change mat x ιe₂ ιf₁ = mat y ιe₂ ιf₁ at e
      have hc : mat x ιe₁ ιf₂ = mat y ιe₁ ιf₂ := by
        have ex := (A₂_rel hxA).2.2
        have ey := (A₂_rel hyA).2.2
        rw [ex, ey] at e
        exact h.bar.injective e
      exact mem_ZPsub_of_A₂ (mul_mem (inv_mem hxA) hyA)
        (by rw [n1, hα x (hY₂Y₁ x hx), hα y (hY₂Y₁ y hy), add_zero])
        (by rw [n2, hβ x hx, hβ y hy, add_zero])
        (by rw [n3, hc, CharTwo.add_self_eq_zero]))
  have h4 : Nat.card (Y₂ ⊓ ZPsub h : Subgroup _) ≤ 2 ^ f :=
    (card_le_of_le inf_le_right).trans card_ZPsub.le
  have b1 := ncard_bar_eq_le h (d := A ιe₂ ιe₂) ha₁
  have b2 := ncard_bar_eq_le h (d := A ιz ιz) ha₁
  have b3 := ncard_bar_eq_le h (d := A ιf₁ ιf₁) ha₂
  calc Nat.card Y ≤ Nat.card Y₁ * 2 ^ f := h1.trans (Nat.mul_le_mul_left _ b1)
    _ ≤ Nat.card Y₂ * 2 ^ f * 2 ^ f :=
        Nat.mul_le_mul_right _ (h2.trans (Nat.mul_le_mul_left _ b2))
    _ ≤ 2 ^ f * 2 ^ f * 2 ^ f * 2 ^ f := by
        refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
        exact h3.trans (Nat.mul_le_mul h4 b3)
    _ = (2 ^ f) ^ 4 := by ring

theorem card_Vh_inf_centralizer_le_of_outer (hZ : center (hypPSU h 2 1) = ⊥)
    {T : Subgroup (MulAut (hypPSU h 2 1))} (hT2 : IsPGroup 2 T) (hTU : T ⊓ Pi h = Uh h)
    {ρ : MulAut (hypPSU h 2 1)} (hρT : ρ ∈ T) (hρP : ρ ∉ Pi h) :
    Nat.card (Vh h ⊓ centralizer {ρ} : Subgroup _) ≤ (2 ^ f) ^ 3 := by
  obtain ⟨n, x, hx, hbar⟩ := exists_lift_pow_bar hT2 hρT hρP
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  refine card_le_of_outer hZ hx (mem_normalizer_Vh hZ hTU (pow_mem hρT _)) (fun e => hc ?_)
    (fun c hc => by rw [hbar c, hc]) inf_le_left fun w hw => ?_
  · rw [← hbar c, e]
    rfl
  have hcw : Commute ρ w := mem_centralizer_iff.1 hw.2 ρ rfl
  exact (hcw.pow_left n).eq

theorem card_le_of_outer_Ah (hZ : center (hypPSU h 2 1) = ⊥)
    {T : Subgroup (MulAut (hypPSU h 2 1))} (hT2 : IsPGroup 2 T) (hTU : T ⊓ Pi h = Uh h)
    {ρ : MulAut (hypPSU h 2 1)} (hρT : ρ ∈ T) (hρP : ρ ∉ Pi h)
    {X : Subgroup (MulAut (hypPSU h 2 1))} (hXA : X ≤ (A₂sub h).map (innM h))
    (hX : ∀ ξ ∈ X, ⁅ρ, ξ⁆ ∈ (ZPsub h).map (innM h)) : Nat.card X ≤ (2 ^ f) ^ 4 := by
  obtain ⟨n, x, hx, hbar⟩ := exists_lift_pow_bar hT2 hρT hρP
  have hxT : Phi h x ∈ T := by rw [hx]; exact pow_mem hρT n
  have hρN := mem_normalizer_Vh hZ hTU hxT
  have hP := isParaW_of_act_mem fun v hv => act_mem_Vsub hZ hρN hv
  have hdet := det_blkEE_ne_zero hP
  rw [Matrix.det_fin_two] at hdet
  set X' : Subgroup (hypSU h 2 1) := X.comap (innM h) ⊓ A₂sub h with hX'
  have hX'A : X' ≤ A₂sub h := inf_le_right
  have hmap : X'.map (innM h) = X := by
    apply le_antisymm
    · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
      exact ha
    · intro ξ hξ
      obtain ⟨a, ha, rfl⟩ := hXA hξ
      exact ⟨a, ⟨hξ, ha⟩, rfl⟩
  rw [← hmap, card_map_innM hZ (hX'A.trans A₂sub_le_U)]
  refine card_le_of_outer_A₂sub hX'A (isPara_of_paraW hP) (lmat_e₂e₁_eq_zero hZ hTU hxT) hdet
    fun a ha => ?_
  have hc := commutator_pow_mem_Zh hZ hTU hρT (hX _ ha.1) n
  rw [← hx] at hc
  obtain ⟨z, hz, hza⟩ := act_eq_mul_of_commutator_mem hZ ZPsub_le_U (A₂sub_le_U ha.2) hc
  refine ⟨z, hz, ?_⟩
  rw [← hza, ← lmat_mul_map]
  congr 1
  ext i j
  simp [hbar]

end Outer

end CFSG.LocalAnalysis.EvenBN.U5
