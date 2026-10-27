module

public import CFSG.GH74.GLS.Stage4.Q9.CharGlue
public import CFSG.GH74.GLS.Stage4.Q9.FrobCount
public import CFSG.GH74.GLS.Stage4.Q9.Numerics
public import CFSG.GH74.GLS.Stage4.Q9.SylowEnd

public section

open scoped BigOperators Classical

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup CFSG

theorem congr_mod256 (F : ℕ) (h : 256 ∣ F * 42661 + 1) : F % 256 = 211 := by omega

theorem congr_mod81 (F : ℕ) (h : 81 ∣ F * 6560 + 1) : F % 81 = 1 := by omega

theorem congr_mod25 (F : ℕ) (h : 25 ∣ F * 288 + 1) : F % 25 = 23 := by omega

theorem congr_crt (F : ℕ) (h2 : 256 ∣ F * 42661 + 1) (h3 : 81 ∣ F * 6560 + 1)
    (h5 : 25 ∣ F * 288 + 1) : F % 518400 = 45523 := by
  have e2 := congr_mod256 F h2
  have e3 := congr_mod81 F h3
  have e5 := congr_mod25 F h5
  have a1 : F ≡ 45523 [MOD 256] := by unfold Nat.ModEq; rw [e2]
  have a2 : F ≡ 45523 [MOD 81] := by unfold Nat.ModEq; rw [e3]
  have a3 : F ≡ 45523 [MOD 25] := by unfold Nat.ModEq; rw [e5]
  have b1 := (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 256 81)).1 ⟨a1, a2⟩
  have b2 :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime (256 * 81) 25)).1 ⟨b1, a3⟩
  unfold Nat.ModEq at b2
  have : 256 * 81 * 25 = 518400 := by norm_num
  rw [this] at b2
  rw [b2]

theorem abs_le_509 (a : ℤ) (h : 1 + (a + 1) ^ 2 + a ^ 2 ≤ 518400) : |a| ≤ 509 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (a + 1), sq_nonneg a]

theorem coprime_thirty {F G' : ℕ} (hG : G' = 518400 * F) (hG0 : G' ≠ 0)
    (hG2 : G'.factorization 2 = 8) (hG3 : G'.factorization 3 = 4) (hG5 : G'.factorization 5 = 2) :
    Nat.Coprime F 30 := by
  have key : ∀ p k : ℕ, p.Prime → p ^ k ∣ 518400 → G'.factorization p = k → ¬ p ∣ F := by
    intro p k hp hdvd hfac hpF
    have h1 : p ^ (k + 1) ∣ G' := by
      rw [hG, pow_succ]
      exact Nat.mul_dvd_mul hdvd hpF
    have h2 := (hp.pow_dvd_iff_le_factorization hG0).1 h1
    omega
  have h2 : Nat.Coprime F 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (key 2 8 Nat.prime_two (by norm_num) hG2)).symm
  have h3 : Nat.Coprime F 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (key 3 4 Nat.prime_three (by norm_num) hG3)).symm
  have h5 : Nat.Coprime F 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2
      (key 5 2 Nat.prime_five (by norm_num) hG5)).symm
  have : (30 : ℕ) = 2 * 3 * 5 := by norm_num
  rw [this]
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right h2 h3) h5

theorem card_centralizer_eq_of_isConj' {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set G)) = Nat.card (centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  subst hc
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨c * x * c⁻¹, ?_⟩
      invFun := fun y => ⟨c⁻¹ * y * c, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun y => ?_ }
  · have hx := x.2
    rw [mem_centralizer_iff] at hx ⊢
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    have := hx a rfl
    calc c * a * c⁻¹ * (c * (x : G) * c⁻¹) = c * (a * x) * c⁻¹ := by group
      _ = c * (x * a) * c⁻¹ := by rw [this]
      _ = c * x * c⁻¹ * (c * a * c⁻¹) := by group
  · have hy := y.2
    rw [mem_centralizer_iff] at hy ⊢
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    have := hy (c * a * c⁻¹) rfl
    calc a * (c⁻¹ * (y : G) * c) = c⁻¹ * (c * a * c⁻¹ * y) * c := by group
      _ = c⁻¹ * (y * (c * a * c⁻¹)) * c := by rw [this]
      _ = c⁻¹ * y * c * a := by group
  · apply Subtype.ext; show c⁻¹ * (c * (x : G) * c⁻¹) * c = x; group
  · apply Subtype.ext; show c * (c⁻¹ * (y : G) * c) * c⁻¹ = y; group

theorem fac518400_2 : (518400 : ℕ).factorization 2 = 8 := by
  have : (518400 : ℕ) = 2 ^ 8 * (3 ^ 4 * 5 ^ 2) := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow,
    Nat.prime_two.factorization, Nat.prime_three.factorization, Nat.prime_five.factorization]
  simp

theorem fac518400_3 : (518400 : ℕ).factorization 3 = 4 := by
  have : (518400 : ℕ) = 2 ^ 8 * (3 ^ 4 * 5 ^ 2) := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow,
    Nat.prime_two.factorization, Nat.prime_three.factorization, Nat.prime_five.factorization]
  simp

theorem orderOf_conj_eq' {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g
    (show SemiconjBy g x (g * x * g⁻¹) by simp [SemiconjBy, mul_assoc])).symm

@[expose] def ThetaData (G : Type) [Group G] (z : G) (K₁ K₂ : Subgroup G)
    [Fintype ↥(centralizer ({z} : Set G))] : Prop :=
  ∃ θ : ↥(centralizer ({z} : Set G)) → ℂ, θ ∈ BlocksVChar ↥(centralizer ({z} : Set G)) ∧
    (∀ c : ↥(centralizer ({z} : Set G)), (c : G) ∉ Sset z K₁ K₂ → θ c = 0) ∧
    BlocksInnerProduct θ θ = 3 ∧ BlocksInnerProduct θ 1 = 1 ∧ θ 1 = 0 ∧
    (∀ h : ↥(centralizer ({z} : Set G)), (h : G) = z → θ h = 0) ∧
    ∑ x ∈ (Finset.univ.filter fun x : ↥(centralizer ({z} : Set G)) => orderOf x = 2 ∧ (x : G) ≠ z),
      ∑ y ∈ (Finset.univ.filter fun y : ↥(centralizer ({z} : Set G)) =>
        orderOf y = 2 ∧ (y : G) ≠ z), θ (x * y) = 43571520

theorem q9_false_of_facts {G : Type} [Group G] [Finite G] {z : G} (K₁ K₂ : Subgroup G)
    (hz : orderOf z = 2) (hone : ∀ u : G, orderOf u = 2 → IsConj z u)
    (hK₁ : K₁ ≤ centralizer ({z} : Set G)) (hK₂ : K₂ ≤ centralizer ({z} : Set G))
    (hn₁ : ∀ c ∈ centralizer ({z} : Set G), ∀ k ∈ K₁, c * k * c⁻¹ ∈ K₁)
    (hn₂ : ∀ c ∈ centralizer ({z} : Set G), ∀ k ∈ K₂, c * k * c⁻¹ ∈ K₂)
    (hK3 : ∀ y : G, y ∈ centralizer ({z} : Set G) → orderOf y = 3 →
      centralizer ({y} : Set G) ≤ centralizer ({z} : Set G) ∧
        ∀ e : G, orderOf e = 2 → e ∈ centralizer ({y} : Set G) → e = z)
    (hK5 : ∀ x : G, (x ∈ K₁ ∨ x ∈ K₂) → orderOf x = 5 →
      centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) ∧
        ∀ e : G, e ∈ centralizer ({x} : Set G) → orderOf e = 2 →
          (∀ c ∈ centralizer ({x} : Set G), e * c = c * e) → e = z)
    (hC : Nat.card (centralizer ({z} : Set G)) = 518400)
    (hcard2 : (Nat.card G).factorization 2 = (Nat.card (centralizer ({z} : Set G))).factorization 2)
    (hcard3 : (Nat.card G).factorization 3 = (Nat.card (centralizer ({z} : Set G))).factorization 3)
    (hG5 : (Nat.card G).factorization 5 = 2)
    (h5conj : ∀ g : G, orderOf g = 5 → ∃ h : G, h * g * h⁻¹ ∈ K₁ ∨ h * g * h⁻¹ ∈ K₂)
    (hexp : ∀ g : G, (∃ k : ℕ, orderOf g = 5 ^ k) → orderOf g = 1 ∨ orderOf g = 5)
    (h7 : 7 ∣ Nat.card G)
    (hθ : @ThetaData G _ z K₁ K₂ (Fintype.ofFinite _))
    (hN2 : Nat.card (pSet 2 z K₁ K₂) = 42661) (hN3 : Nat.card (pSet 3 z K₁ K₂) = 6560)
    (hN5 : Nat.card (pSet 5 z K₁ K₂) = 288) : False := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hG2 : (Nat.card G).factorization 2 = 8 := by rw [hcard2, hC, fac518400_2]
  have hG3 : (Nat.card G).factorization 3 = 4 := by rw [hcard3, hC, fac518400_3]
  obtain ⟨hTI, hinv, hS2, hSC⟩ := ti_of_key hz K₁ K₂ hK₁ hK₂ hn₁ hn₂ hK3 hK5
  have hzS : z ∈ Sset z K₁ K₂ := Or.inl (Or.inl ⟨mem_centralizer_singleton_iff.mpr rfl,
    Subgroup.mem_zpowers z⟩)
  obtain ⟨θ, hθv, hθS, hθθ, hθ1, hθone, hθz, hκ⟩ := hθ
  obtain ⟨x, a, hx1, hax, hbound, hF⟩ :=
    @q9_glue G _ _ (centralizer ({z} : Set G)) (Fintype.ofFinite _) (Sset z K₁ K₂) hTI z hz hzS rfl
      hone hinv hS2 θ hθv hθS hθθ hθ1 hθone hθz 43571520 hκ
  set F : ℕ := Nat.card G / Nat.card (centralizer ({z} : Set G)) with hFdef
  have hidx : (centralizer ({z} : Set G)).index = F := by
    rw [hFdef, ← (centralizer ({z} : Set G)).card_mul_index,
      Nat.mul_div_cancel_left _ Nat.card_pos]
  have hGF : Nat.card G = 518400 * F := by
    have := (centralizer ({z} : Set G)).card_mul_index
    rw [hC, hidx] at this
    exact this.symm
  have hFz : (F : ℤ) * ((x : ℤ) - a) ^ 2 = 43571520 * (x : ℤ) * ((x : ℤ) + 1) := by
    have : ((F : ℕ) : ℂ) * ((x : ℂ) - a) ^ 2 = 43571520 * x * (x + 1) := hF
    exact_mod_cast this
  have ha509 : |a| ≤ 509 := by
    refine abs_le_509 a ?_
    have := hbound
    rw [hC] at this
    exact_mod_cast this
  have hne2 : (pSet 2 z K₁ K₂).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hN2
    simp at hN2
  have hne3 : (pSet 3 z K₁ K₂).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hN3
    simp at hN3
  have hne5 : (pSet 5 z K₁ K₂).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hN5
    simp at hN5
  have f2 := frobenius_two hz hone K₁ K₂ hTI hne2
  have f3 := frobenius_three hcard3 K₁ K₂ hTI hne3
  have f5 := frobenius_five K₁ K₂ h5conj hexp hTI hne5
  rw [hG2, hidx, hN2] at f2
  rw [hG3, hidx, hN3] at f3
  rw [hG5, hidx, hN5] at f5
  have hmod : F % 518400 = 45523 :=
    congr_crt F (by simpa using f2) (by simpa using f3) (by simpa using f5)
  have hcop : Nat.Coprime F 30 :=
    coprime_thirty hGF Nat.card_pos.ne' hG2 hG3 hG5
  have h7F : 7 ∣ F := by
    rw [hGF] at h7
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h7)
  have hFeq := numerics_F_eq F x a hx1 hax ha509 hFz hcop hmod h7F
  have hcard : Nat.card G = 518400 * (7 * 1039 * 5851) := by rw [hGF, hFeq]
  refine sylow1039_false G hcard ?_
  intro y hy
  have h1039 : ¬ 1039 ∣ (518400 : ℕ) := by norm_num
  have hdvdC : ∀ w : G, centralizer ({w} : Set G) ≤ centralizer ({z} : Set G) →
      ¬ 1039 ∣ Nat.card (centralizer ({w} : Set G)) := by
    intro w hw hd
    exact h1039 (hC ▸ hd.trans (Subgroup.card_dvd_of_le hw))
  rcases hy with h2 | h3 | h5
  · rw [← card_centralizer_eq_of_isConj' (a := z) (b := y) (hone y h2), hC]
    exact h1039
  · have hy1 : y ≠ 1 := by
      rintro rfl
      simp at h3
    obtain ⟨a', ha'⟩ := cover_three hcard3 K₁ K₂ y hy1 ⟨1, by rw [h3]; simp⟩
    have hmem := ha'.1
    have hord' : orderOf (a' * y * a'⁻¹) = 3 := by rw [orderOf_conj_eq', h3]
    have hC' := hSC _ hmem
    rw [card_centralizer_eq_of_isConj' (a := y) (b := a' * y * a'⁻¹) (isConj_iff.mpr ⟨a', rfl⟩)]
    exact hdvdC _ (hK3 _ hC' hord').1
  · obtain ⟨h', hh'⟩ := h5conj y h5
    have hord' : orderOf (h' * y * h'⁻¹) = 5 := by rw [orderOf_conj_eq', h5]
    rw [card_centralizer_eq_of_isConj' (a := y) (b := h' * y * h'⁻¹) (isConj_iff.mpr ⟨h', rfl⟩)]
    exact hdvdC _ (hK5 _ hh' hord').1

end CFSG.GH74.GLS.Stage4.Q9
