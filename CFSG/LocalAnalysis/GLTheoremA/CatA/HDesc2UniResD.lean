module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResC
public import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
open CFSG.RankThree.PartOne.CTP
open Matrix

section Indep

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem diagonal_apply_pow_three_eq_one {n : ℕ} {X : GL (Fin n) K} {d : Fin n → K}
    (hX3 : X ^ 3 = 1) (hd : (X : Matrix (Fin n) (Fin n) K) = diagonal d) (t : Fin n) :
    d t ^ 3 = 1 := by
  have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) t t) hX3
  simp only [Units.val_pow_eq_pow_val, hd, diagonal_pow, diagonal_apply_eq, Units.val_one,
    one_apply_eq] at h2
  exact h2

theorem conjHom_eq_one_or_mem_zpowers_of_eq_off {n : ℕ}
    {X₁ X₂ : primeFormUnitary h (idGram K n)} {d₁ d₂ : Fin n → K}
    (hX₁ : ((X₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal d₁)
    (hX₂ : ((X₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal d₂)
    (hd₁ : ∀ t, d₁ t ^ 3 = 1) (hd₂ : ∀ t, d₂ t ^ 3 = 1) {j l : Fin n}
    (hoff : ∀ x, x ≠ l → d₁ x = d₁ j ∧ d₂ x = d₂ j) :
    primeFormConjHom h (idGram K n) X₁ = 1 ∨
      primeFormConjHom h (idGram K n) X₂ ∈
        Subgroup.zpowers (primeFormConjHom h (idGram K n) X₁) := by
  by_cases hal : d₁ l = d₁ j
  · left
    have hc : ∀ x, d₁ x = d₁ j := fun x => by
      by_cases hx : x = l
      · rw [hx, hal]
      · exact (hoff x hx).1
    have hj0 : d₁ j ≠ 0 := fun h0 => by
      have := hd₁ j
      rw [h0] at this
      norm_num at this
    apply primeFormConjHom_eq_one_of_coe_eq_scalar (c := Units.mk0 (d₁ j) hj0)
    apply Units.ext
    rw [hX₁, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
    congr 1
    funext x
    exact hc x
  · right
    obtain ⟨m, s, hs0, hb⟩ := exists_pow_of_eq_off hoff hal hd₁ hd₂
    have hX₂' : (X₂ : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs0) * (X₁ : GL (Fin n) K) ^ m := by
      apply Units.ext
      rw [hX₂, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, hX₁,
        diagonal_pow, Units.val_mk0, Matrix.scalar_apply, diagonal_mul_diagonal]
      congr 1
      funext x
      rw [hb x]
      rfl
    have hS : ((X₂ * (X₁ ^ m)⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs0) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hX₂', mul_inv_cancel_right]
    have hSc := primeFormConjHom_eq_one_of_coe_eq_scalar hS
    have e : X₂ = (X₂ * (X₁ ^ m)⁻¹) * X₁ ^ m := by group
    rw [e, map_mul, hSc, one_mul, map_pow]
    exact Subgroup.npow_mem_zpowers _ m

end Indep

theorem map_map_conj_eq_of_map_eq {G : Type*} [Group G] {T : Subgroup G} (g c : MulAut G)
    (hc : T.map c.toMonoidHom = T) :
    (T.map g.toMonoidHom).map (g * c * g⁻¹).toMonoidHom = T.map g.toMonoidHom := by
  rw [Subgroup.map_map]
  have e : (g * c * g⁻¹).toMonoidHom.comp g.toMonoidHom = g.toMonoidHom.comp c.toMonoidHom := by
    ext x
    show (g * c * g⁻¹) (g x) = g (c x)
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
  rw [e, ← Subgroup.map_map, hc]

private theorem injective_vec_four {i j k l : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) (hkl : k ≠ l) : Function.Injective ![i, j, k, l] := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

section AssemblyFour

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem exists_weight_split_four {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K)
    {T : Subgroup (primeFormP h (idGram K 4))} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    {X₁ X₂ : primeFormUnitary h (idGram K 4)} {d₁ d₂ : Fin 4 → K}
    (hX₁ : ((X₁ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal d₁)
    (hX₂ : ((X₂ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal d₂)
    (hd₁ : ∀ t, d₁ t ^ 3 = 1) (hd₂ : ∀ t, d₂ t ^ 3 = 1)
    (hN₁ : T.map (primeFormConjHom h (idGram K 4) X₁).toMonoidHom = T)
    (hN₂ : T.map (primeFormConjHom h (idGram K 4) X₂).toMonoidHom = T)
    (h₁ : primeFormConjHom h (idGram K 4) X₁ ≠ 1)
    (h₂ : primeFormConjHom h (idGram K 4) X₂ ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K 4) X₁)) :
    ∃ i j k l : Fin 4, Function.Injective ![i, j, k, l] ∧ d₁ i = d₁ j ∧ d₂ i = d₂ j ∧
      (d₁ k ≠ d₁ i ∨ d₂ k ≠ d₂ i) ∧ (d₁ l ≠ d₁ i ∨ d₂ l ≠ d₂ i) := by
  classical
  obtain ⟨i, j, hij, h₁ij, h₂ij⟩ :=
    exists_eq_weight_of_primeFormP_four h hT2 hT hX₁ hX₂ hd₁ hd₂ hN₁ hN₂
  have hindep : ∀ {n' : Fin 4}, ¬ ∀ x, x ≠ n' → d₁ x = d₁ i ∧ d₂ x = d₂ i := fun hoff =>
    (conjHom_eq_one_or_mem_zpowers_of_eq_off hX₁ hX₂ hd₁ hd₂ hoff).elim h₁ h₂
  obtain ⟨k, l, hkl, hs⟩ := Finset.card_eq_two.1 (show (({i, j} : Finset (Fin 4))ᶜ).card = 2 by
    rw [Finset.card_compl, Finset.card_pair hij, Fintype.card_fin])
  have hmem : ∀ x : Fin 4, x = i ∨ x = j ∨ x = k ∨ x = l := by
    intro x
    by_cases hx : x ∈ ({i, j} : Finset (Fin 4))
    · rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
    · have hx' : x ∈ ({i, j} : Finset (Fin 4))ᶜ := Finset.mem_compl.2 hx
      rw [hs, Finset.mem_insert, Finset.mem_singleton] at hx'
      exact Or.inr (Or.inr hx')
  have hk : k ∈ ({i, j} : Finset (Fin 4))ᶜ := by
    rw [hs]
    exact Finset.mem_insert_self k {l}
  have hl : l ∈ ({i, j} : Finset (Fin 4))ᶜ := by
    rw [hs]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self l)
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hk hl
  obtain ⟨hki, hkj⟩ := hk
  obtain ⟨hli, hlj⟩ := hl
  refine ⟨i, j, k, l, injective_vec_four hij hki hkj hli hlj hkl, h₁ij, h₂ij, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    apply hindep (n' := l)
    intro x hx
    rcases hmem x with hx' | hx' | hx' | hx'
    · rw [hx']
      exact ⟨rfl, rfl⟩
    · rw [hx']
      exact ⟨h₁ij.symm, h₂ij.symm⟩
    · rw [hx']
      exact hc
    · exact absurd hx' hx
  · by_contra hc
    push Not at hc
    apply hindep (n' := k)
    intro x hx
    rcases hmem x with hx' | hx' | hx' | hx'
    · rw [hx']
      exact ⟨rfl, rfl⟩
    · rw [hx']
      exact ⟨h₁ij.symm, h₂ij.symm⟩
    · exact absurd hx' hx
    · rw [hx']
      exact hc

theorem glaPLayer_ne_bot_of_eigenbasis_four {f : ℕ} (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (h3 : 3 ∣ 2 ^ f + 1) {A B : primeFormUnitary h (idGram K 4)} {b : Fin 4 → Fin 4 → K}
    (hb : IsOrthonormalFamily h b) {μ ν : Fin 4 → K}
    (hμ : ∀ t, ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ b t = μ t • b t)
    (hν : ∀ t, ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ b t = ν t • b t)
    {i j k l : Fin 4} (hπ : Function.Injective ![i, j, k, l]) (hμij : μ i = μ j)
    (hνij : ν i = ν j) (hk : μ k ≠ μ i ∨ ν k ≠ ν i) (hl : μ l ≠ μ i ∨ ν l ≠ ν i) :
    GLAPLayer 3 (fixSubgroup (primeFormConjHom h (idGram K 4) A) ⊓
      fixSubgroup (primeFormConjHom h (idGram K 4) B)) ≠ ⊥ := by
  obtain ⟨R, hRU, hRA, hRB⟩ := exists_unitary_conj_eq_diagonal_pair h
    (isOrthonormalFamily_comp hb hπ) (μ := μ ∘ ![i, j, k, l]) (ν := ν ∘ ![i, j, k, l])
    (fun t => hμ (![i, j, k, l] t)) (fun t => hν (![i, j, k, l] t))
  obtain ⟨R', hR'⟩ : ∃ R' : primeFormUnitary h (idGram K 4), (R' : GL (Fin 4) K) = R :=
    ⟨⟨R, hRU⟩, rfl⟩
  have hY₁ : (((R' * A * R'⁻¹ : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = diagonal (μ ∘ ![i, j, k, l]) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hR']
    exact hRA
  have hY₂ : (((R' * B * R'⁻¹ : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = diagonal (ν ∘ ![i, j, k, l]) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hR']
    exact hRB
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd (F := K) Nat.prime_three
    (three_dvd_card_sub_one h h3)
  have hω3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hω : ζ ^ 2 + ζ + 1 = 0 := by
    have e1 : (ζ - 1) * (ζ ^ 2 + ζ + 1) = ζ ^ 3 - 1 := by ring
    rw [hω3, sub_self] at e1
    exact (mul_eq_zero.1 e1).resolve_left (sub_ne_zero.2 (hζ.ne_one (by norm_num)))
  have h2f : 2 ^ f % 3 = 2 := by omega
  have hωb : h.bar ζ = ζ ^ 2 := by
    rw [UnitaryFieldData.bar_apply, pow_eq_pow_mod _ hω3, h2f]
  have e0 : ∀ e : Fin 4 → K, (e ∘ ![i, j, k, l]) 0 = e i := fun _ => rfl
  have e1 : ∀ e : Fin 4 → K, (e ∘ ![i, j, k, l]) 1 = e j := fun _ => rfl
  have e2 : ∀ e : Fin 4 → K, (e ∘ ![i, j, k, l]) 2 = e k := fun _ => rfl
  have e3 : ∀ e : Fin 4 → K, (e ∘ ![i, j, k, l]) 3 = e l := fun _ => rfl
  have hcore := glaPLayer_ne_bot_of_unitary_diagonal_four h hf hω hωb hY₁ hY₂
    (by rw [e0, e1]; exact hμij) (by rw [e0, e1]; exact hνij)
    (by rw [e0, e2, e0, e2]; exact hk) (by rw [e0, e3, e0, e3]; exact hl)
  simp only [map_mul, map_inv] at hcore
  exact HDescLinRes.glaPLayer_ne_bot_of_conj Nat.prime_three _ _ _ hcore

theorem glaPLayer_ne_bot_of_commuting_four {f : ℕ} (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (h3 : 3 ∣ 2 ^ f + 1) {T : Subgroup (primeFormP h (idGram K 4))} (hT2 : IsPGroup 2 T)
    (hT : T ≠ ⊥) {A B : primeFormUnitary h (idGram K 4)} (hAB : A * B = B * A)
    (hA3 : A ^ 3 = 1) (hB3 : B ^ 3 = 1)
    (hNA : T.map (primeFormConjHom h (idGram K 4) A).toMonoidHom = T)
    (hNB : T.map (primeFormConjHom h (idGram K 4) B).toMonoidHom = T)
    (hA1 : primeFormConjHom h (idGram K 4) A ≠ 1)
    (hBA : primeFormConjHom h (idGram K 4) B ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K 4) A)) :
    GLAPLayer 3 (fixSubgroup (primeFormConjHom h (idGram K 4) A) ⊓
      fixSubgroup (primeFormConjHom h (idGram K 4) B)) ≠ ⊥ := by
  obtain ⟨bs, μ, ν, hbo, hAe, hBe⟩ :=
    exists_orthonormal_eigenbasis_pair (h := h) Nat.prime_three h3 hAB hA3 hB3
  have hμ : ∀ t, ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ bs t = μ t • bs t :=
    fun t => hAe t
  have hν : ∀ t, ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ bs t = ν t • bs t :=
    fun t => hBe t
  obtain ⟨R, hRU, hRA, hRB⟩ := exists_unitary_conj_eq_diagonal_pair h hbo hμ hν
  obtain ⟨R', hR'⟩ : ∃ R' : primeFormUnitary h (idGram K 4), (R' : GL (Fin 4) K) = R :=
    ⟨⟨R, hRU⟩, rfl⟩
  have hX₁ : (((R' * A * R'⁻¹ : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = diagonal μ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hR']
    exact hRA
  have hX₂ : (((R' * B * R'⁻¹ : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = diagonal ν := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hR']
    exact hRB
  obtain ⟨g, hg⟩ : ∃ g : MulAut (primeFormP h (idGram K 4)),
      g = primeFormConjHom h (idGram K 4) R' := ⟨_, rfl⟩
  have hc : ∀ X, primeFormConjHom h (idGram K 4) (R' * X * R'⁻¹) =
      g * primeFormConjHom h (idGram K 4) X * g⁻¹ := fun X => by
    rw [hg, map_mul, map_mul, map_inv]
  have hd : ∀ {X : primeFormUnitary h (idGram K 4)} {d : Fin 4 → K}, X ^ 3 = 1 →
      (((R' * X * R'⁻¹ : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = diagonal d → ∀ t, d t ^ 3 = 1 := fun hX3 hX =>
    diagonal_apply_pow_three_eq_one
      (by rw [← Subgroup.coe_pow, conj_pow, hX3, mul_one, mul_inv_cancel, Subgroup.coe_one]) hX
  have hN : ∀ {X : primeFormUnitary h (idGram K 4)},
      T.map (primeFormConjHom h (idGram K 4) X).toMonoidHom = T →
      (T.map g.toMonoidHom).map (primeFormConjHom h (idGram K 4) (R' * X * R'⁻¹)).toMonoidHom =
        T.map g.toMonoidHom := fun hX => by
    rw [hc]
    exact map_map_conj_eq_of_map_eq g _ hX
  have hT' : T.map g.toMonoidHom ≠ ⊥ := fun hbot =>
    hT ((Subgroup.map_eq_bot_iff_of_injective T (g.injective :
      Function.Injective g.toMonoidHom)).1 hbot)
  have h₁ : primeFormConjHom h (idGram K 4) (R' * A * R'⁻¹) ≠ 1 := by
    rw [hc]
    intro h1
    apply hA1
    calc primeFormConjHom h (idGram K 4) A =
          g⁻¹ * (g * primeFormConjHom h (idGram K 4) A * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have h₂ : primeFormConjHom h (idGram K 4) (R' * B * R'⁻¹) ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K 4) (R' * A * R'⁻¹)) := by
    rw [hc, hc]
    intro hm
    apply hBA
    obtain ⟨m, hm'⟩ := Subgroup.mem_zpowers_iff.1 hm
    rw [conj_zpow] at hm'
    exact Subgroup.mem_zpowers_iff.2 ⟨m, mul_left_cancel (mul_right_cancel hm')⟩
  obtain ⟨i, j, k, l, hπ, hμij, hνij, hk, hl⟩ := exists_weight_split_four h (hT2.map _) hT'
    hX₁ hX₂ (hd hA3 hX₁) (hd hB3 hX₂) (hN hNA) (hN hNB) h₁ h₂
  exact glaPLayer_ne_bot_of_eigenbasis_four h hf h3 hbo hμ hν hπ hμij hνij hk hl

theorem goodSubThree_primeFormP_four {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2)
    (hf : Odd f) (hf1 : f ≠ 1) : HDescLinRes.GoodSubThree (primeFormP h (idGram K 4)) := by
  classical
  subst hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro A hA hA27 T hT2 hT hAT
  have hne : ¬ (4 = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have h3 : 3 ∣ 2 ^ f + 1 := by
    have := CFSG.two_pow_mod_three_of_odd hf
    omega
  have hf2 : 2 ≤ f := by
    obtain ⟨m, hm⟩ := hf
    omega
  have hAf := card_le_three_mul_card_inf_primeFormD_of_le h (by norm_num) hne (B := A)
    (fun b hb => hA.2 b hb)
  have hE : IsElemAbelian 3 (A ⊓ primeFormD h (idGram K 4) :
      Subgroup (MulAut (primeFormP h (idGram K 4)))) := isElemAbelian_mono hA inf_le_left
  have h9 : 3 ^ 2 ≤ Nat.card (A ⊓ primeFormD h (idGram K 4) :
      Subgroup (MulAut (primeFormP h (idGram K 4)))) := by
    have h27 : (27 : ℕ) ≤ Nat.card A := hA27
    have : 9 ≤ Nat.card (A ⊓ primeFormD h (idGram K 4) :
        Subgroup (MulAut (primeFormP h (idGram K 4)))) := by omega
    exact this
  obtain ⟨D, hDE, hD9⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_sub_card_pow Nat.prime_three hE h9
  have hD : IsElemAbelian 3 D := isElemAbelian_mono hE hDE
  have hD9' : Nat.card D = 9 := hD9
  have hD1 : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hD9'
    norm_num at hD9'
  obtain ⟨⟨a, haD⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD1
  have ha1' : a ≠ 1 := fun h0 => ha1 (Subtype.ext h0)
  obtain ⟨b, hbD, hba⟩ : ∃ b ∈ D, b ∉ Subgroup.zpowers a := by
    by_contra hc
    push Not at hc
    have hle := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers a from hc)
    rw [Nat.card_zpowers, hD9'] at hle
    have := orderOf_le_of_pow_eq_one (by norm_num) (hD.2 a haD)
    omega
  have hab : a * b = b * a := congrArg Subtype.val (hD.1.is_comm.comm ⟨a, haD⟩ ⟨b, hbD⟩)
  have haA : a ∈ A := (Subgroup.mem_inf.1 (hDE haD)).1
  have hbA : b ∈ A := (Subgroup.mem_inf.1 (hDE hbD)).1
  have ha3 : a ^ 3 = 1 := hD.2 a haD
  have hb3 : b ^ 3 = 1 := hD.2 b hbD
  have hcl := HDescLinRes.closure_eq_of_card_nine_not_mem hD9' hbD haD hb3 hba
    (Subgroup.mem_zpowers a) ha1'
  refine ⟨Subgroup.closure {b, a}, hcl.le.trans (hDE.trans inf_le_left), by rw [hcl, hD9], ?_⟩
  apply HDescLinRes.isGood_closure_pair
  rw [inf_comm]
  obtain ⟨A₀, α, hαn, hA3, rfl⟩ :=
    exists_pow_scalar_of_mem_primeFormD (by norm_num) (Subgroup.mem_inf.1 (hDE haD)).2 ha3
  obtain ⟨B₀, β, hβn, hB3, rfl⟩ :=
    exists_pow_scalar_of_mem_primeFormD (by norm_num) (Subgroup.mem_inf.1 (hDE hbD)).2 hb3
  obtain ⟨μ, hμn, hμ⟩ := exists_cube_root_four h hαn hA3
  obtain ⟨ν, hνn, hν⟩ := exists_cube_root_four h hβn hB3
  have hμ'n : h.norm ((μ⁻¹ : Kˣ) : K) = 1 := by
    simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hμn
  have hν'n : h.norm ((ν⁻¹ : Kˣ) : K) = 1 := by
    simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hνn
  obtain ⟨A', hA'⟩ : ∃ A' : primeFormUnitary h (idGram K 4), A' = scalarU h 4 μ⁻¹ hμ'n * A₀ :=
    ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : primeFormUnitary h (idGram K 4), B' = scalarU h 4 ν⁻¹ hν'n * B₀ :=
    ⟨_, rfl⟩
  have hA'c : primeFormConjHom h (idGram K 4) A' = primeFormConjHom h (idGram K 4) A₀ := by
    rw [hA', map_mul, conjHom_scalarU (by norm_num) hne, one_mul]
  have hB'c : primeFormConjHom h (idGram K 4) B' = primeFormConjHom h (idGram K 4) B₀ := by
    rw [hB', map_mul, conjHom_scalarU (by norm_num) hne, one_mul]
  have hA'3 : A' ^ 3 = 1 := by
    rw [hA']
    exact rescale_pow_eq_one (by norm_num) hne hμ'n (by rw [hμ]; exact hA3)
  have hB'3 : B' ^ 3 = 1 := by
    rw [hB']
    exact rescale_pow_eq_one (by norm_num) hne hν'n (by rw [hν]; exact hB3)
  rw [← hA'c, ← hB'c] at hab hba ⊢
  rw [← hA'c] at ha1' haA
  rw [← hB'c] at hbA
  exact glaPLayer_ne_bot_of_commuting_four h hf2 h3 hT2 hT
    (mul_comm_of_primeFormConjHom_comm_four h hab) hA'3 hB'3 (hAT _ haA) (hAT _ hbA) ha1' hba

end AssemblyFour

theorem goodSubAt_twistedA_three (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (h8 : q.card = 8) :
    HDesc.GoodSubAt 3 ⟨.twistedA 3 q, hv⟩ 2 := by
  intro _ _ A hA hcard T hT2 hT hAT
  obtain ⟨r, q', K, _, hU, -, hdA, -, ⟨eP⟩⟩ :=
    KD264Lie.exists_primeFormP_mulEquiv_of_isUnitaryIdx (d := ⟨.twistedA 3 q, hv⟩) trivial
  injection hdA with hr hqq
  subst hr hqq
  haveI := hU.charP
  haveI := hU.finite
  have hq8 : q.p ^ q.exponent = 2 ^ 3 := by
    rw [← TauCeti.PrimePower.card_def, h8]
    norm_num
  have hp2 : q.p = 2 := by
    have hdvd : q.p ∣ 2 ^ 3 := hq8 ▸ dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)
  have he3 : q.exponent = 3 := by
    rw [hp2] at hq8
    exact Nat.pow_right_injective (le_refl 2) hq8
  haveI : CharP K 2 := CharP.congr q.p hp2
  have hodd : Odd q.exponent := by
    rw [he3]
    decide
  have hf1 : q.exponent ≠ 1 := by omega
  exact HDescLinRes.GoodSubThree.of_mulEquiv eP (goodSubThree_primeFormP_four hU hp2 hodd hf1) A
    hA hcard T hT2 hT hAT

end CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

end
