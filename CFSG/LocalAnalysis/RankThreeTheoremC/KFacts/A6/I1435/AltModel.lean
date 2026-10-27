module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Wreath
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSimple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

open Subgroup Equiv

abbrev Ω3 : Type := M3 × M3

@[expose] def toPermW : W3 →* Perm Ω3 := RegularWreathProduct.toPerm M3 M3 M3

theorem toPermW_injective : Function.Injective toPermW :=
  RegularWreathProduct.toPermInj M3 M3 M3

@[expose] def baseHom : (M3 → M3) →* W3 where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by ext <;> simp

theorem baseHom_injective : Function.Injective baseHom := fun f g h =>
  congrArg RegularWreathProduct.left h

theorem toPermW_baseHom_apply (f : M3 → M3) (p : Ω3) :
    toPermW (baseHom f) p = (f p.2 * p.1, p.2) := by
  simp [toPermW, baseHom, RegularWreathProduct.toPerm]

theorem m3_cube : ∀ m : M3, m ^ 3 = 1 := by decide

theorem fun_cube (g : M3 → M3) : g ^ 3 = 1 := funext fun q => m3_cube (g q)

theorem zpow_trichotomy (g : M3 → M3) (k : ℤ) : g ^ k = 1 ∨ g ^ k = g ∨ g ^ k = g⁻¹ := by
  rw [zpow_eq_zpow_emod' k (fun_cube g)]
  have h2 : g ^ (2 : ℤ) = g⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = (3 : ℕ) by norm_num, zpow_natCast,
      fun_cube]
  have hk : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
  rcases hk with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero g)
  · exact Or.inr (Or.inl (zpow_one g))
  · exact Or.inr (Or.inr h2)

@[expose] def q1 : M3 := Multiplicative.ofAdd 1

@[expose] def q2 : M3 := Multiplicative.ofAdd 2

@[expose] def cact : Fin 6 → (M3 → M3) → (M3 → M3) :=
  ![fun f => f, fun f x => f (q1⁻¹ * x), fun f x => f ((q1 * q1)⁻¹ * x),
    fun f q => if q = q2 then f q else (f q)⁻¹, fun f q => if q = q1 then f q else (f q)⁻¹,
    fun f q => if q = 1 then f q else (f q)⁻¹]

@[expose] def cperm : Fin 6 → Perm Ω3 :=
  ![1, toPermW (RegularWreathProduct.inl q1), toPermW (RegularWreathProduct.inl (q1 * q1)),
    swap (q1, 1) (q2, 1) * swap (q1, q1) (q2, q1),
    swap (q1, 1) (q2, 1) * swap (q1, q2) (q2, q2),
    swap (q1, q1) (q2, q1) * swap (q1, q2) (q2, q2)]

theorem cperm_conj : ∀ c : Fin 6, ∀ f : M3 → M3,
    cperm c * toPermW (baseHom f) * (cperm c)⁻¹ = toPermW (baseHom (cact c f)) := by
  decide +kernel

theorem sign_toPermW (w : W3) : Perm.sign (toPermW w) = 1 := by
  have h81 : w ^ 81 = 1 := by
    have := pow_card_eq_one' (G := W3) (x := w)
    rwa [card_W3] at this
  have hs : Perm.sign (toPermW w) ^ 81 = 1 := by
    rw [← map_pow, ← map_pow, h81, map_one, map_one]
  rcases Int.units_eq_one_or (Perm.sign (toPermW w)) with h | h
  · exact h
  · rw [h] at hs
    exact absurd hs (by decide)

theorem sign_cperm (c : Fin 6) : Perm.sign (cperm c) = 1 := by
  have hsw : ∀ a b c d : Ω3, a ≠ b → c ≠ d → Perm.sign (swap a b * swap c d) = 1 := by
    intro a b c d hab hcd
    rw [map_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    decide
  fin_cases c
  · exact map_one _
  · exact sign_toPermW _
  · exact sign_toPermW _
  · exact hsw _ _ _ _ (by decide) (by decide)
  · exact hsw _ _ _ _ (by decide) (by decide)
  · exact hsw _ _ _ _ (by decide) (by decide)

@[expose] def lineD (g h : M3 → M3) : Prop := h ≠ g ∧ h ≠ g⁻¹ ∧ h ≠ 1

instance (g h : M3 → M3) : Decidable (lineD g h) := inferInstanceAs (Decidable (_ ∧ _))

@[expose] def pick (f : M3 → M3) : Fin 4 → Fin 6 :=
  if f 1 ≠ 1 ∧ f q1 ≠ 1 ∧ f q2 ≠ 1 then ![0, 3, 4, 5]
  else if f 1 = 1 then ![0, 1, 2, 3] else ![0, 1, 2, 5]

theorem alt_check : ∀ f : M3 → M3, f ≠ 1 →
    (∃ q₀, f q₀ ≠ 1 ∧ ∀ q, q ≠ q₀ → f q = 1) ∨
      ∀ i j : Fin 4, i ≠ j → lineD (cact (pick f i) f) (cact (pick f j) f) := by
  decide +kernel

abbrev offBlock (q₀ : M3) : Type := {p : Ω3 // p.2 ≠ q₀}

theorem card_offBlock : ∀ q₀ : M3, Fintype.card (offBlock q₀) = 6 := by decide

theorem commute_ofSubtype {f : M3 → M3} {q₀ : M3} (hf : ∀ q, q ≠ q₀ → f q = 1)
    (σ : Perm (offBlock q₀)) :
    Perm.ofSubtype σ * toPermW (baseHom f) = toPermW (baseHom f) * Perm.ofSubtype σ := by
  have hd : Perm.Disjoint (Perm.ofSubtype σ) (toPermW (baseHom f)) := by
    intro p
    by_cases hp : p.2 ≠ q₀
    · right
      rw [toPermW_baseHom_apply, hf _ hp, one_mul]
    · left
      exact Perm.ofSubtype_apply_of_not_mem σ hp
  exact hd.commute.eq

theorem not_isPSolvable_altSix (q₀ : M3) :
    ¬ CFSG.HallHigman.IsPSolvable 3 (alternatingGroup (offBlock q₀)) := by
  have h6 : Nat.card (offBlock q₀) = 6 := by rw [Nat.card_eq_fintype_card, card_offBlock]
  have : Nontrivial (offBlock q₀) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, card_offBlock]
    norm_num
  have hS : IsSimpleGroup (alternatingGroup (offBlock q₀)) :=
    alternatingGroup.isSimpleGroup (by rw [h6]; norm_num)
  have hcard : Nat.card (alternatingGroup (offBlock q₀)) = 360 := by
    rw [nat_card_alternatingGroup, h6]
    decide
  have hnc : ¬ IsMulCommutative (alternatingGroup (offBlock q₀)) := by
    intro hc
    letI : CommGroup (alternatingGroup (offBlock q₀)) :=
      { (inferInstance : Group (alternatingGroup (offBlock q₀))) with
        mul_comm := fun a b => hc.is_comm.comm a b }
    have := hS.prime_card
    rw [hcard] at this
    exact absurd this (by norm_num)
  exact CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.not_isPSolvable_three_of_simple hS hnc
    (by rw [hcard]; norm_num)

section Embed

variable (n : ℕ) (hn : 9 ≤ n)

@[expose] noncomputable def embΩ : Ω3 ↪ Fin n :=
  (Fintype.equivFin Ω3).toEmbedding.trans (Fin.castLEEmb (by
    have : Fintype.card Ω3 = 9 := by decide
    omega))

@[expose] noncomputable def iotaΩ : Perm Ω3 →* Perm (Fin n) :=
  Perm.viaEmbeddingHom (embΩ n hn)

theorem iotaΩ_injective : Function.Injective (iotaΩ n hn) :=
  Perm.viaEmbeddingHom_injective _

theorem sign_iotaΩ (σ : Perm Ω3) : Perm.sign (iotaΩ n hn σ) = Perm.sign σ := by
  classical
  rw [iotaΩ, Perm.viaEmbeddingHom_apply, Perm.viaEmbedding]
  convert Perm.sign_extendDomain σ (Equiv.ofInjective _ (embΩ n hn).injective)

@[expose] noncomputable def altOf (σ : Perm Ω3) (hσ : Perm.sign σ = 1) : alternatingGroup (Fin n) :=
  ⟨iotaΩ n hn σ, by rw [Perm.mem_alternatingGroup, sign_iotaΩ, hσ]⟩

@[expose] noncomputable def phiAlt : W3 →* alternatingGroup (Fin n) :=
  ((iotaΩ n hn).comp toPermW).codRestrict _ fun w => by
    rw [Perm.mem_alternatingGroup, MonoidHom.comp_apply, sign_iotaΩ, sign_toPermW]

theorem phiAlt_injective : Function.Injective (phiAlt n hn) := by
  intro a b h
  apply toPermW_injective
  apply iotaΩ_injective n hn
  exact congrArg Subtype.val h

@[expose] noncomputable def betaAlt : (M3 → M3) →* alternatingGroup (Fin n) :=
  (phiAlt n hn).comp baseHom

theorem betaAlt_injective : Function.Injective (betaAlt n hn) :=
  (phiAlt_injective n hn).comp baseHom_injective

theorem coe_betaAlt (f : M3 → M3) :
    ((betaAlt n hn f : alternatingGroup (Fin n)) : Perm (Fin n)) =
      iotaΩ n hn (toPermW (baseHom f)) := rfl

theorem eq_of_zpowers_betaAlt {g h : M3 → M3}
    (hgh : zpowers (betaAlt n hn g) = zpowers (betaAlt n hn h)) : h = g ∨ h = g⁻¹ ∨ h = 1 := by
  have hm : betaAlt n hn h ∈ zpowers (betaAlt n hn g) := by
    rw [hgh]
    exact mem_zpowers _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm
  rw [← map_zpow] at hk
  have hk' := betaAlt_injective n hn hk
  rw [← hk']
  rcases zpow_trichotomy g k with h1 | h1 | h1
  · exact Or.inr (Or.inr h1)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)

end Embed

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
