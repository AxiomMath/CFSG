module

public import CFSG.ClassicalGroups.SpecialLinear.NaturalNotDual
public import CFSG.ClassicalGroups.SpecialLinear.Transitive

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open CFSG.Open CFSG.Open.StatedAPI Matrix

private theorem natDual_eq_bot_or_top {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (S : AddSubgroup (Fin n → K))
    (hS : ∀ g ∈ StatedSL n K, ∀ v ∈ S, (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases h : ∃ v ∈ S, v ≠ 0
  · right
    obtain ⟨v, hv, hv0⟩ := h
    rw [AddSubgroup.eq_top_iff']
    intro y
    by_cases hy : y = 0
    · rw [hy]
      exact S.zero_mem
    · obtain ⟨A, hA, hAv⟩ := exists_statedSL_mulVec_eq hn hv0 hy
      rw [← hAv]
      exact hS A hA v hv
  · left
    rw [AddSubgroup.eq_bot_iff_forall]
    intro v hv
    by_contra hv0
    exact h ⟨v, hv, hv0⟩

private theorem natDual_exists_inv_transpose {K : Type} [Field K] {n : ℕ} {h : GL (Fin n) K}
    (hh : h ∈ StatedSL n K) :
    ∃ k ∈ StatedSL n K,
      ((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = (h : Matrix (Fin n) (Fin n) K) := by
  have hMN : (h : Matrix (Fin n) (Fin n) K) *
      ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.mul_inv h
  have hNM : ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (h : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.inv_mul h
  have hdet : ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
    det_of_mem_statedSL (inv_mem hh)
  obtain ⟨k, hk1, hk2⟩ : ∃ k : GL (Fin n) K,
      (k : Matrix (Fin n) (Fin n) K) = ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ ∧
        ((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (h : Matrix (Fin n) (Fin n) K)ᵀ :=
    ⟨Units.mk (((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ
      ((h : Matrix (Fin n) (Fin n) K))ᵀ
      (by rw [← Matrix.transpose_mul, hMN, Matrix.transpose_one])
      (by rw [← Matrix.transpose_mul, hNM, Matrix.transpose_one]), rfl, rfl⟩
  refine ⟨k, mem_statedSL_of_det ?_, ?_⟩
  · rw [hk1, Matrix.det_transpose]
    exact hdet
  · rw [hk2, Matrix.transpose_transpose]

theorem natDual_invariant_addSubgroup {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n)
    (W : AddSubgroup ((Fin n → K) × (Fin n → K)))
    (hW : ∀ g ∈ StatedSL n K, ∀ p ∈ W,
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ p.1,
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ p.2) ∈ W) :
    W = ⊥ ∨ W = (⊤ : AddSubgroup (Fin n → K)).prod ⊥ ∨
      W = (⊥ : AddSubgroup (Fin n → K)).prod ⊤ ∨ W = ⊤ := by
  obtain ⟨W₁, hW₁⟩ : ∃ S : AddSubgroup (Fin n → K),
      ∀ x, x ∈ S ↔ ((x, 0) : (Fin n → K) × (Fin n → K)) ∈ W :=
    ⟨W.comap (AddMonoidHom.inl (Fin n → K) (Fin n → K)), fun _ => Iff.rfl⟩
  obtain ⟨W₂, hW₂⟩ : ∃ S : AddSubgroup (Fin n → K),
      ∀ y, y ∈ S ↔ ((0, y) : (Fin n → K) × (Fin n → K)) ∈ W :=
    ⟨W.comap (AddMonoidHom.inr (Fin n → K) (Fin n → K)), fun _ => Iff.rfl⟩
  obtain ⟨P₁, hP₁⟩ : ∃ S : AddSubgroup (Fin n → K),
      ∀ x, x ∈ S ↔ ∃ y, ((x, y) : (Fin n → K) × (Fin n → K)) ∈ W := by
    refine ⟨W.map (AddMonoidHom.fst (Fin n → K) (Fin n → K)), fun x => ?_⟩
    constructor
    · intro hx
      obtain ⟨p, hp, hpx⟩ := AddSubgroup.mem_map.mp hx
      refine ⟨p.2, ?_⟩
      have hpe : ((x, p.2) : (Fin n → K) × (Fin n → K)) = p := Prod.ext hpx.symm rfl
      rw [hpe]
      exact hp
    · rintro ⟨y, hy⟩
      exact AddSubgroup.mem_map.mpr ⟨(x, y), hy, rfl⟩
  have hS₁ : ∀ g ∈ StatedSL n K, ∀ v ∈ W₁, (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W₁ := by
    intro g hg v hv
    rw [hW₁] at hv ⊢
    have h : ((g : Matrix (Fin n) (Fin n) K) *ᵥ v,
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ (0 : Fin n → K)) ∈ W :=
      hW g hg (v, 0) hv
    rw [Matrix.mulVec_zero] at h
    exact h
  have hS₂ : ∀ g ∈ StatedSL n K, ∀ v ∈ W₂, (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W₂ := by
    intro g hg v hv
    rw [hW₂] at hv ⊢
    obtain ⟨k, hk, hkg⟩ := natDual_exists_inv_transpose hg
    have h : ((k : Matrix (Fin n) (Fin n) K) *ᵥ (0 : Fin n → K),
        ((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ v) ∈ W :=
      hW k hk (0, v) hv
    rw [Matrix.mulVec_zero, hkg] at h
    exact h
  have hSP₁ : ∀ g ∈ StatedSL n K, ∀ v ∈ P₁, (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ P₁ := by
    intro g hg v hv
    obtain ⟨y, hy⟩ := (hP₁ v).mp hv
    rw [hP₁]
    exact ⟨_, hW g hg (v, y) hy⟩
  have hi₁ := natDual_eq_bot_or_top (by omega : 2 ≤ n) W₁ hS₁
  have hi₂ := natDual_eq_bot_or_top (by omega : 2 ≤ n) W₂ hS₂
  have hiP := natDual_eq_bot_or_top (by omega : 2 ≤ n) P₁ hSP₁
  rcases hi₁ with h1 | h1 <;> rcases hi₂ with h2 | h2
  ·
    rcases hiP with hP | hP
    · left
      rw [AddSubgroup.eq_bot_iff_forall]
      rintro ⟨x, y⟩ hxy
      have hx : x ∈ P₁ := (hP₁ x).mpr ⟨y, hxy⟩
      rw [hP, AddSubgroup.mem_bot] at hx
      subst hx
      have hy : y ∈ W₂ := (hW₂ y).mpr hxy
      rw [h2, AddSubgroup.mem_bot] at hy
      subst hy
      rfl
    ·
      exfalso
      have hex : ∀ x : Fin n → K, ∃ y : Fin n → K,
          ((x, y) : (Fin n → K) × (Fin n → K)) ∈ W := by
        intro x
        exact (hP₁ x).mp (by rw [hP]; exact AddSubgroup.mem_top x)
      choose f hf using hex
      have huniq : ∀ x y : Fin n → K, ((x, y) : (Fin n → K) × (Fin n → K)) ∈ W → y = f x := by
        intro x y hxy
        have h0 : ((0 : Fin n → K), y - f x) ∈ W := by
          have := AddSubgroup.sub_mem W hxy (hf x)
          simpa using this
        have h0' : y - f x ∈ W₂ := (hW₂ _).mpr h0
        rw [h2, AddSubgroup.mem_bot] at h0'
        exact sub_eq_zero.mp h0'
      have hadd : ∀ x x' : Fin n → K, f (x + x') = f x + f x' := by
        intro x x'
        symm
        apply huniq
        have := AddSubgroup.add_mem W (hf x) (hf x')
        simpa using this
      let F : (Fin n → K) →+ (Fin n → K) := AddMonoidHom.mk' f hadd
      have hinj : Function.Injective F := by
        refine (injective_iff_map_eq_zero F).mpr ?_
        intro a ha
        have ha' : f a = 0 := ha
        have h0 : ((a, (0 : Fin n → K)) : (Fin n → K) × (Fin n → K)) ∈ W := by
          have := hf a
          rwa [ha'] at this
        have ha0 : a ∈ W₁ := (hW₁ a).mpr h0
        rw [h1, AddSubgroup.mem_bot] at ha0
        exact ha0
      have hequiv : ∀ g ∈ StatedSL n K, ∀ x : Fin n → K,
          F ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) =
            ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ F x := by
        intro g hg x
        have h : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ f x =
            f ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) :=
          huniq _ _ (hW g hg (x, f x) (hf x))
        exact h.symm
      exact not_exists_natural_dual_hom_statedSL hn ⟨F, hinj, hequiv⟩
  ·
    right
    right
    left
    ext ⟨x, y⟩
    rw [AddSubgroup.mem_prod]
    simp only [AddSubgroup.mem_bot, AddSubgroup.mem_top, and_true]
    constructor
    · intro hxy
      have hy0 : ((0 : Fin n → K), y) ∈ W :=
        (hW₂ y).mp (by rw [h2]; exact AddSubgroup.mem_top y)
      have hx0 : (x, (0 : Fin n → K)) ∈ W := by
        have := AddSubgroup.sub_mem W hxy hy0
        simpa using this
      have hx : x ∈ W₁ := (hW₁ x).mpr hx0
      rw [h1, AddSubgroup.mem_bot] at hx
      exact hx
    · intro hx
      subst hx
      exact (hW₂ y).mp (by rw [h2]; exact AddSubgroup.mem_top y)
  ·
    right
    left
    ext ⟨x, y⟩
    rw [AddSubgroup.mem_prod]
    simp only [AddSubgroup.mem_bot, AddSubgroup.mem_top, true_and]
    constructor
    · intro hxy
      have hx0 : (x, (0 : Fin n → K)) ∈ W :=
        (hW₁ x).mp (by rw [h1]; exact AddSubgroup.mem_top x)
      have hy0 : ((0 : Fin n → K), y) ∈ W := by
        have := AddSubgroup.sub_mem W hxy hx0
        simpa using this
      have hy : y ∈ W₂ := (hW₂ y).mpr hy0
      rw [h2, AddSubgroup.mem_bot] at hy
      exact hy
    · intro hy
      subst hy
      exact (hW₁ x).mp (by rw [h1]; exact AddSubgroup.mem_top x)
  ·
    right
    right
    right
    rw [AddSubgroup.eq_top_iff']
    rintro ⟨x, y⟩
    have hx0 : (x, (0 : Fin n → K)) ∈ W :=
      (hW₁ x).mp (by rw [h1]; exact AddSubgroup.mem_top x)
    have hy0 : ((0 : Fin n → K), y) ∈ W :=
      (hW₂ y).mp (by rw [h2]; exact AddSubgroup.mem_top y)
    have := AddSubgroup.add_mem W hx0 hy0
    simpa using this

theorem det_eq_one_of_pow_two_pow_eq_one {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (g : GL (Fin n) K) {k : ℕ} (hg : g ^ (2 ^ k) = 1) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hd : (g : Matrix (Fin n) (Fin n) K).det ^ (2 ^ k) = 1 := by
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hg, Units.val_one, Matrix.det_one]
  have hne : (g : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hq : (g : Matrix (Fin n) (Fin n) K).det ^ (Fintype.card K - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ hne
  have hmod : Fintype.card K % 2 = 0 :=
    FiniteField.even_card_iff_char_two.mp (ringChar.eq K 2)
  have hpos : 0 < Fintype.card K := Fintype.card_pos
  have hodd : ¬ 2 ∣ (Fintype.card K - 1) := by omega
  have hcop : Nat.Coprime (2 ^ k) (Fintype.card K - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h1 : (g : Matrix (Fin n) (Fin n) K).det ^ Nat.gcd (2 ^ k) (Fintype.card K - 1) = 1 :=
    pow_gcd_eq_one.mpr ⟨hd, hq⟩
  have hgcd : Nat.gcd (2 ^ k) (Fintype.card K - 1) = 1 := hcop
  rw [hgcd, pow_one] at h1
  exact h1

end CFSG.ClassicalGroups.SpecialLinear

end
