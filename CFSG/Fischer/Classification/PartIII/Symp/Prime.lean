module

public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Fischer.Classification.Basic.Local
public import CFSG.Permutation.BurnsideSchur.PrimeDegree
public import CFSG.Permutation.BurnsideSchur.RegularCyclic

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.BurnsideSchur MulAction
open scoped commutatorElement

namespace LocalSymp

@[expose] def translations (p : ℕ) : Subgroup (Equiv.Perm (ZMod p)) where
  carrier := {τ | ∃ c, ∀ x, τ x = x + c}
  mul_mem' := by
    rintro σ τ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨b + a, fun x => by rw [Equiv.Perm.mul_apply, hb, ha, add_assoc]⟩
  one_mem' := ⟨0, fun x => by rw [Equiv.Perm.one_apply, add_zero]⟩
  inv_mem' := by
    rintro τ ⟨c, hc⟩
    exact ⟨-c, fun x => by rw [Equiv.Perm.inv_eq_iff_eq, hc, neg_add_cancel_right]⟩

theorem translations_comm {p : ℕ} {σ τ : Equiv.Perm (ZMod p)} (hσ : σ ∈ translations p)
    (hτ : τ ∈ translations p) : σ * τ = τ * σ := by
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨b, hb⟩ := hτ
  ext x
  simp only [Equiv.Perm.mul_apply, ha, hb]
  ring

theorem commutatorElement_mem_translations {p : ℕ} {σ τ : Equiv.Perm (ZMod p)}
    (hσ : ∃ a ≠ 0, ∃ b, ∀ x, σ x = a * x + b) (hτ : ∃ a ≠ 0, ∃ b, ∀ x, τ x = a * x + b) :
    ⁅σ, τ⁆ ∈ translations p := by
  obtain ⟨a, -, b, hab⟩ := hσ
  obtain ⟨a', -, b', hab'⟩ := hτ
  have key : ∀ x, (σ * τ) x = (τ * σ) x + (a * b' + b - a' * b - b') := by
    intro x
    simp only [Equiv.Perm.mul_apply, hab, hab']
    ring
  refine ⟨a * b' + b - a' * b - b', fun y => ?_⟩
  rw [commutatorElement_def, show σ * τ * σ⁻¹ * τ⁻¹ = σ * τ * (τ * σ)⁻¹ by group,
    Equiv.Perm.mul_apply, key, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

end LocalSymp

open LocalSymp

variable {G : Type} [Group G] {D : Set G}

theorem Pair.not_prime_ncard (hH : Hyp G D) (hna : NonabelianCommutator G) :
    ¬ D.ncard.Prime := by
  intro hp
  obtain ⟨hP, hZ, hS⟩ := hH
  classical
  have := Pair.finite hP
  have := Fintype.ofFinite D
  have hcardD : Nat.card D = D.ncard := Nat.card_coe_set_eq D
  set ρ := Pair.conjPerm hP
  have hρ := Pair.conjPerm_injective hP hZ
  set R := ρ.range
  have := Fintype.ofFinite R
  have hact : ∀ (g : G) (x : D), (((⟨ρ g, g, rfl⟩ : R) • x : D) : G) = g * x * g⁻¹ :=
    fun g x => rfl
  have htrans : IsPretransitive R D := ⟨fun x y => by
    obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP x.2 y.2)
    exact ⟨⟨ρ g, g, rfl⟩, Subtype.ext (by rw [hact, hg])⟩⟩
  have hnot2 : ¬ IsMultiplyPretransitive R D 2 := by
    intro h2
    obtain ⟨d, hd⟩ := Pair.nonempty hP
    obtain ⟨f, hf⟩ := Pair.localClass_nonempty hP hS hna hd
    obtain ⟨c, hc, hcd⟩ : ∃ c ∈ D, c * d ≠ d * c := by
      by_contra! h
      have hdZ : d ∈ Subgroup.center G := (Pair.mem_center_iff hP).2 h
      rw [hZ, Subgroup.mem_bot] at hdZ
      exact Pair.ne_one hP hd hdZ
    have h2t : ∀ {a b c d : D}, a ≠ b → c ≠ d → ∃ g : R, g • a = c ∧ g • b = d :=
      is_two_pretransitive_iff.1 h2
    obtain ⟨⟨_, g, rfl⟩, h1, h2'⟩ := h2t
      (show (⟨d, hd⟩ : D) ≠ ⟨f, hf.1⟩ from fun h => hf.2.1 (congrArg Subtype.val h).symm)
      (show (⟨d, hd⟩ : D) ≠ ⟨c, hc⟩ from
        fun h => hcd (by rw [show d = c from congrArg Subtype.val h]))
    have e1 : g * d * g⁻¹ = d := by rw [← hact g ⟨d, hd⟩, h1]
    have e2 : g * f * g⁻¹ = c := by rw [← hact g ⟨f, hf.1⟩, h2']
    apply hcd
    rw [← e2, ← e1, conj_commute_iff]
    exact hf.2.2
  obtain ⟨d₀, hd₀⟩ := Pair.nonempty hP
  have hdvd : D.ncard ∣ Fintype.card R := by
    have h := MulAction.index_stabilizer R (⟨d₀, hd₀⟩ : D)
    rw [MulAction.orbit_eq_univ, Set.ncard_univ, hcardD] at h
    rw [← h, ← Nat.card_eq_fintype_card]
    exact Subgroup.index_dvd_card _
  have := Fact.mk hp
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card D.ncard hdvd
  have hσ' : orderOf (σ : Equiv.Perm D) = Fintype.card D := by
    rw [Subgroup.orderOf_coe, hσ, ← hcardD, Nat.card_eq_fintype_card]
  have hcyc := Equiv.Perm.isCycle_of_prime_order''
    (by rwa [← Nat.card_eq_fintype_card, hcardD]) hσ'
  have hsupp : ∀ x, (σ : Equiv.Perm D) x ≠ x := by
    intro x
    have h := hcyc.orderOf
    rw [hσ'] at h
    rw [← Equiv.Perm.mem_support, Finset.eq_univ_of_card _ h.symm]
    exact Finset.mem_univ x
  set K := Subgroup.zpowers (σ : Equiv.Perm D)
  have hKR : K ≤ R := Subgroup.zpowers_le.2 σ.2
  have : IsPretransitive K D := ⟨fun x y => by
    obtain ⟨i, hi⟩ := hcyc.exists_zpow_eq (hsupp x) (hsupp y)
    exact ⟨⟨_, i, rfl⟩, hi⟩⟩
  have hK : ∀ x : D, stabilizer K x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    rintro ⟨k, hk⟩ hkx
    rw [Subgroup.mem_bot]
    obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers).2 hk
    exact Subtype.ext ((hcyc.pow_eq_one_iff' (hsupp x)).2 hkx)
  have : Nonempty D := ⟨⟨d₀, hd₀⟩⟩
  obtain ⟨e, he⟩ := exists_equiv_zmod_image_eq K hK
  set G' := R.map e.permCongrHom.toMonoidHom
  have hG' : ∀ c, Equiv.addRight c ∈ G' := by
    intro c
    have : Equiv.addRight c ∈ e.permCongr '' (K : Set (Equiv.Perm D)) := by
      rw [he]
      exact ⟨c, fun x => rfl⟩
    obtain ⟨k, hk, hke⟩ := this
    exact ⟨k, hKR hk, hke⟩
  have h2' : ¬ IsMultiplyPretransitive G' (ZMod (Nat.card D)) 2 := by
    rwa [isMultiplyPretransitive_map_permCongrHom_iff]
  have : Fact (Nat.card D).Prime := ⟨by rwa [hcardD]⟩
  have haff : ∀ g : G, ∃ a ≠ 0, ∃ b, ∀ x, (e.permCongrHom.toMonoidHom.comp ρ g) x = a * x + b :=
    fun g => exists_affine_of_not_isMultiplyPretransitive hG' h2' ⟨ρ g, ⟨g, rfl⟩, rfl⟩
  set ψ : G →* Equiv.Perm (ZMod (Nat.card D)) := e.permCongrHom.toMonoidHom.comp ρ
  have hψ : Function.Injective ψ := e.permCongrHom.injective.comp hρ
  have hcomm : commutator G ≤ (translations (Nat.card D)).comap ψ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact commutatorElement_mem_translations (haff g) (haff h)
  obtain ⟨a, b, hab⟩ := hna
  apply hab
  apply Subtype.ext
  apply hψ
  simp only [Subgroup.coe_mul, map_mul]
  exact translations_comm (hcomm a.2) (hcomm b.2)

end CFSG.Fischer.Classification
