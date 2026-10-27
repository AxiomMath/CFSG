module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxA

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Idx

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer

@[expose] def FixCatS (Y J : Type) [Group Y] [Group J] : Prop :=
  ∀ α τ : MulAut Y, α * α = 1 → α ≠ 1 → τ * α = α * τ → (∃ k : ℕ, τ ^ 2 ^ k = 1) →
    ∀ X : Subgroup Y, ⁅X, X⁆ = X → (∃ f : ↥X →* J, Function.Surjective f) →
      (∀ x ∈ X, α x = x) → (∀ x ∈ X, τ x = x) → τ = 1 ∨ τ = α

theorem card_eq_mul_ker {G G' : Type*} [Group G] [Group G'] [Finite G] {φ : G →* G'}
    (hφ : Function.Surjective φ) : Nat.card G = Nat.card G' * Nat.card φ.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]

theorem fixCatS_of_cover {Y J : Type} [Group Y] [Group J] [Finite Y]
    (hY : Group.IsPerfect Y) (hJ : center J = ⊥)
    (hcat : FixCat (Y ⧸ center Y) (Nat.card J)) : FixCatS Y J := by
  intro α τ hα2 hα1 hτα hτ2 X hXp hXf hXα hXτ
  have hinj := GH74.KGroups.inducedHom_injective hY
  set ι := GH74.KGroups.inducedHom (K := Y) with hι
  set π := QuotientGroup.mk' (center Y) with hπ
  set X' := X.map π with hX'
  obtain ⟨f, hf⟩ := hXf
  set φ : ↥X →* ↥X' := π.subgroupMap X with hφ
  have hφs : Function.Surjective φ := π.subgroupMap_surjective X
  have hker : φ.ker ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxZ : (x : Y) ∈ center Y := by
      have h1 : π (x : Y) = 1 := congrArg Subtype.val hx
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hfc : f x ∈ center J := by
      rw [mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := hf w
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((mem_center_iff.mp hxZ) w')
    rw [hJ] at hfc
    exact mem_bot.mp hfc
  have hdvd : Nat.card J ∣ Nat.card X' := by
    have e1 := card_eq_mul_ker hφs
    have e2 := card_eq_mul_ker hf
    have h3 : Nat.card φ.ker ∣ Nat.card f.ker := card_dvd_of_le hker
    obtain ⟨m, hm⟩ := h3
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    refine ⟨m, ?_⟩
    have : Nat.card X' * Nat.card φ.ker = Nat.card J * m * Nat.card φ.ker := by
      rw [← e1, e2, hm]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hX'p : ⁅X', X'⁆ = X' := by rw [hX', ← map_commutator, hXp]
  have hfix : ∀ β : MulAut Y, (∀ x ∈ X, β x = x) → ∀ x ∈ X', ι β x = x := by
    rintro β hβ _ ⟨x, hx, rfl⟩
    rw [hι, hπ, QuotientGroup.mk'_apply, GH74.KGroups.inducedHom_mk, hβ x hx]
  have h := hcat (ι α) (ι τ) (by rw [← map_mul, hα2, map_one])
    (fun h1 => hα1 (hinj (by rw [h1, map_one])))
    (by rw [← map_mul, ← map_mul, hτα])
    (by obtain ⟨k, hk⟩ := hτ2; exact ⟨k, by rw [← map_pow, hk, map_one]⟩)
    X' hX'p hdvd (hfix α hXα) (hfix τ hXτ)
  rcases h with h | h
  · exact Or.inl (hinj (by rw [h, map_one]))
  · exact Or.inr (hinj h)

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem exists_fixed_surj (hKa : conjugate h.K h.a = h.K) {t : H} (ht : t ∈ h.T) :
    ∃ X : Subgroup (OddBar h.K), ⁅X, X⁆ = X ∧
      (∃ f : ↥X →* OddBar h.J, Function.Surjective f) ∧
      (∀ x ∈ X, actW h hKa ⟨h.a, h.a_mem_normalizer⟩ x = x) ∧
      (∀ x ∈ X, actW h hKa ⟨t, mem_W_of_mem_T h ht⟩ x = x) := by
  set Y := GSLit.fixedLayer h.J (E h t) with hYdef
  have hYK : Y ≤ h.K := (fixedLayer_E_le h ht).trans (fixedLayer_le_K h hKa)
  obtain ⟨e⟩ := nonempty_equiv_E h ht
  obtain ⟨X, hXp, -, hXa, hXt⟩ := exists_fixed h hKa ht
  refine ⟨imK h Y, imK_commutator_eq h hYK (fixedLayer_commutator_eq _ _), ?_,
    fun x hx => actW_apply_of_mem_imK h hKa (fun y hy => ?_) hx,
    fun x hx => actW_apply_of_mem_imK h hKa (fun y hy => ?_) hx⟩
  · set g := (QuotientGroup.quotientKerEquivRange (toK h hYK)).symm.toMonoidHom.comp
      (MulEquiv.subgroupCongr (range_toK h hYK)).symm.toMonoidHom with hg
    refine ⟨e.toMonoidHom.comp ((QuotientGroup.map _ _ (MonoidHom.id _)
      (ker_toK_le h hYK)).comp g), ?_⟩
    intro w
    obtain ⟨w', rfl⟩ := e.surjective w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w'
    refine ⟨(MulEquiv.subgroupCongr (range_toK h hYK))
      (QuotientGroup.quotientKerEquivRange (toK h hYK) (QuotientGroup.mk y)), ?_⟩
    simp only [hg, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  · have hyJ : y ∈ h.J := (mem_inf.mp ((GSLit.fixedLayer_le_inf h.J _) hy)).1
    exact (mem_centralizer_singleton_iff.mp (h.J_le hyJ)).symm
  · have hyC := (mem_inf.mp ((GSLit.fixedLayer_le_inf h.J _) hy)).2
    exact mem_centralizer_iff.mp hyC t (mem_sup_left (mem_zpowers t))

theorem T_le_of_fixCatS (hKa : conjugate h.K h.a = h.K)
    (hcat : FixCatS (OddBar h.K) (OddBar h.J)) : h.T ≤ zpowers h.a ⊔ h.B := by
  intro t ht
  obtain ⟨k, hk⟩ := h.orderOf_eq_two_pow_of_mem_S (mem_S_of_mem_T h ht)
  have ht2 : t ^ 2 ^ k = 1 := by rw [← hk, pow_orderOf_eq_one]
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  set α := actW h hKa ⟨h.a, h.a_mem_normalizer⟩ with hα
  set τ := actW h hKa ⟨t, mem_W_of_mem_T h ht⟩ with hτ
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul]
    have : (⟨h.a, h.a_mem_normalizer⟩ * ⟨h.a, h.a_mem_normalizer⟩ : h.W) = 1 := Subtype.ext ha2
    rw [this, map_one]
  have hα1 : α ≠ 1 := oddBarConj_a_ne_one h hKa
  have hτα : τ * α = α * τ := by
    rw [hτ, hα, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.comm_a (mem_S_of_mem_T h ht))
  have hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1 := by
    refine ⟨k, ?_⟩
    rw [hτ, ← map_pow]
    have : (⟨t, mem_W_of_mem_T h ht⟩ : h.W) ^ 2 ^ k = 1 := Subtype.ext ht2
    rw [this, map_one]
  obtain ⟨X, hXp, hXf, hXa, hXt⟩ := exists_fixed_surj h hKa ht
  exact mem_of_actW h hKa ht (hcat α τ hα2 hα1 hτα hτ2 X hXp hXf hXa hXt)

end Idx

end CFSG.ComponentClassification.CatFactsL4U4
