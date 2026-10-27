module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Loc
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Abs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.Kc3J
  CFSG.QuasithinUnique.Unc25G2 CFSG.QuasithinUnique.Unc25G2.M2x

@[expose] def LocClass (K : Type) [Group K] : Prop :=
  ∀ E : Subgroup K, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
    Nat.card E = 16 → ∃ (E₀ : Subgroup K) (g : K), LocHypA E₀ ∧
      E = E₀.map (MulAut.conj g).toMonoidHom

section Local

variable {K : Type} [Group K] [Finite K]

theorem kc3LocalData_of_locClass (h : LocClass K) : Kc3LocalData K := by
  intro E β hact
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (comm_of_beta β ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    have h1 : β (⟨x, hx⟩ * ⟨x, hx⟩) = β 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      exact Kc3L3.add_self_evenWeight _
    have h2 := β.injective h1
    exact congrArg Subtype.val h2
  have hcard : Nat.card E = 16 := by
    rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd]
    exact CFSG.QuasithinUnique.AppC.card_evenWeight
  obtain ⟨E₀, g, hA, rfl⟩ := h E hcomm hsq hcard
  exact localAt_of_hypA β hact (hA.map (MulAut.conj g))

end Local

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem LocClass.of_equiv (e : X ≃* Y) (h : LocClass Y) : LocClass X := by
  intro E hcomm hsq hcard
  have hE'comm : ∀ x ∈ E.map e.toMonoidHom, ∀ y ∈ E.map e.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show e x * e y = e y * e x
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hE'sq : ∀ x ∈ E.map e.toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show e x * e x = 1
    rw [← map_mul, hsq x hx, map_one]
  have hE'card : Nat.card (E.map e.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hcard
  obtain ⟨E₀, g, hA, hEE⟩ := h _ hE'comm hE'sq hE'card
  refine ⟨E₀.map e.symm.toMonoidHom, e.symm g, hA.map e.symm, ?_⟩
  have h1 : E = (E.map e.toMonoidHom).map e.symm.toMonoidHom := by
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
      ext x; simp
    rw [this, Subgroup.map_id]
  rw [h1, hEE, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

end Transport

section Two

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem isPGroup_of_elemAb {E : Subgroup K} (hE : ElemAb E) : IsPGroup 2 E := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  simpa [pow_two] using hE.2 x x.2

theorem exists_conj_le {P F : Subgroup K} (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index)
    (hF : IsPGroup 2 F) : ∃ g : K, F.map (MulAut.conj g).toMonoidHom ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hFQ⟩ := hF.exists_le_sylow
  obtain ⟨c, hc⟩ := exists_conj_map_eq Q.isPGroup' Q.not_dvd_index hP hPi
  exact ⟨c, hc ▸ Subgroup.map_mono hFQ⟩

theorem classify_of_twoE (htwo : TwoE K) {E₁ E₂ : Subgroup K} (h1 : ElemAb E₁)
    (c1 : Nat.card E₁ = 16) (h2 : ElemAb E₂) (c2 : Nat.card E₂ = 16)
    (hne : Nat.card (Subgroup.normalizer (E₁ : Set K)) ≠
      Nat.card (Subgroup.normalizer (E₂ : Set K))) :
    ∀ E : Subgroup K, ElemAb E → Nat.card E = 16 →
      (∃ g : K, E = E₁.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g : K, E = E₂.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨P, hP, hPi, hat⟩ := htwo
  obtain ⟨Ea, Eb, ga, gb, hEaP, hEbP, hab, hEa, hEb, hca, hcb, hcl, -, -, -, -⟩ := hat
  obtain ⟨g₁, hg₁⟩ := exists_conj_le hP hPi (isPGroup_of_elemAb h1)
  obtain ⟨g₂, hg₂⟩ := exists_conj_le hP hPi (isPGroup_of_elemAb h2)
  have hF₁ := hcl _ hg₁ (h1.map (MulAut.conj g₁))
    ((Subgroup.card_map_of_injective (MulAut.conj g₁).injective).trans c1)
  have hF₂ := hcl _ hg₂ (h2.map (MulAut.conj g₂))
    ((Subgroup.card_map_of_injective (MulAut.conj g₂).injective).trans c2)
  have hdist : E₁.map (MulAut.conj g₁).toMonoidHom ≠ E₂.map (MulAut.conj g₂).toMonoidHom := by
    intro h
    apply hne
    rw [← card_normalizer_map (MulAut.conj g₁) E₁, ← card_normalizer_map (MulAut.conj g₂) E₂, h]
  intro E hE hc
  obtain ⟨g, hg⟩ := exists_conj_le hP hPi (isPGroup_of_elemAb hE)
  have hFE := hcl _ hg (hE.map (MulAut.conj g))
    ((Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hc)
  have key : E.map (MulAut.conj g).toMonoidHom = E₁.map (MulAut.conj g₁).toMonoidHom ∨
      E.map (MulAut.conj g).toMonoidHom = E₂.map (MulAut.conj g₂).toMonoidHom := by
    rcases hF₁ with h₁ | h₁ <;> rcases hF₂ with h₂ | h₂ <;> rcases hFE with h | h <;>
      first
        | exact absurd (h₁.trans h₂.symm) hdist
        | exact Or.inl (h.trans h₁.symm)
        | exact Or.inr (h.trans h₂.symm)
  have hback : ∀ (F : Subgroup K) (g₀ : K), E.map (MulAut.conj g).toMonoidHom =
      F.map (MulAut.conj g₀).toMonoidHom →
        E = F.map (MulAut.conj (g⁻¹ * g₀)).toMonoidHom := by
    intro F g₀ h
    have h1 : E = (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id K := by
        ext x; simp [MulAut.conj_apply, mul_assoc]
      rw [this, Subgroup.map_id]
    rw [h1, h, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rcases key with h | h
  · left
    exact ⟨g⁻¹ * g₁, hback E₁ g₁ h⟩
  · right
    exact ⟨g⁻¹ * g₂, hback E₂ g₂ h⟩

theorem locClass_of_twoE (htwo : TwoE K) {E₁ E₂ : Subgroup K} (h1 : ElemAb E₁)
    (c1 : Nat.card E₁ = 16) (h2 : ElemAb E₂) (c2 : Nat.card E₂ = 16)
    (hne : Nat.card (Subgroup.normalizer (E₁ : Set K)) ≠
      Nat.card (Subgroup.normalizer (E₂ : Set K)))
    (hA₁ : LocHypA E₁) (hA₂ : LocHypA E₂) : LocClass K := by
  intro E hcomm hsq hcard
  rcases classify_of_twoE htwo h1 c1 h2 c2 hne E ⟨hcomm, hsq⟩ hcard with ⟨g, h⟩ | ⟨g, h⟩
  · exact ⟨E₁, g, hA₁, h⟩
  · exact ⟨E₂, g, hA₂, h⟩

end Two

end CFSG.QuasithinUnique.A5
