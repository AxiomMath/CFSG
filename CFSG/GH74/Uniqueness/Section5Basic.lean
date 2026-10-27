module

public import CFSG.GH74.Uniqueness.Prop36

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section OmegaFix

variable {X : Type*} [Group X] {Z : Set X} {M : Subgroup X}

@[expose] def omegaFix (M : Subgroup X) (Y : Set X) : Set (Subgroup X) :=
  {β | β ∈ omega M ∧ ∀ g ∈ Y, conjugate β g = β}

theorem mem_omegaFix {Y : Set X} {β : Subgroup X} :
    β ∈ omegaFix M Y ↔ β ∈ omega M ∧ ∀ g ∈ Y, conjugate β g = β := Iff.rfl

theorem omegaFix_subset_omega (Y : Set X) : omegaFix M Y ⊆ omega M := fun _ h => h.1

theorem omegaFix_anti {Y Y' : Set X} (h : Y ⊆ Y') : omegaFix M Y' ⊆ omegaFix M Y :=
  fun _ hβ => ⟨hβ.1, fun g hg => hβ.2 g (h hg)⟩

theorem IsProductDisconnected.mem_omegaFix_iff (h : IsProductDisconnected Z M) {P : Subgroup X}
    {β : Subgroup X} : β ∈ omegaFix M (P : Set X) ↔ β ∈ omega M ∧ P ≤ β := by
  constructor
  · rintro ⟨hβ, hfix⟩
    exact ⟨hβ, fun g hg => (h.conjugate_eq_iff_mem hβ).mp (hfix g hg)⟩
  · rintro ⟨hβ, hle⟩
    exact ⟨hβ, fun g hg => (h.conjugate_eq_iff_mem hβ).mpr (hle hg)⟩

theorem IsProductDisconnected.self_mem_omegaFix_iff (h : IsProductDisconnected Z M)
    {P : Subgroup X} : M ∈ omegaFix M (P : Set X) ↔ P ≤ M := by
  rw [h.mem_omegaFix_iff]
  exact ⟨fun h => h.2, fun h => ⟨self_mem_omega M, h⟩⟩

theorem omegaFix_conjugate (P : Subgroup X) (g : X) :
    omegaFix M ((conjugate P g : Subgroup X) : Set X) =
      (fun β => conjugate β g) '' omegaFix M (P : Set X) := by
  ext β'
  constructor
  · rintro ⟨hβ', hfix⟩
    have hβ : conjugate β' g⁻¹ ∈ omega M := conjugate_mem_omega hβ' g⁻¹
    refine ⟨conjugate β' g⁻¹, ⟨hβ, fun p hp => ?_⟩, ?_⟩
    · have hx : g⁻¹ * p * g ∈ conjugate P g := by
        rw [mem_conjugate_iff]
        have e : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
        rw [e]
        exact hp
      have h1 := hfix _ hx
      rw [conjugate_conjugate]
      have e : g⁻¹ * p = (g⁻¹ * p * g) * g⁻¹ := by group
      rw [e, ← conjugate_conjugate, h1]
    · show conjugate (conjugate β' g⁻¹) g = β'
      rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]
  · rintro ⟨β, ⟨hβ, hfix⟩, rfl⟩
    refine ⟨conjugate_mem_omega hβ g, fun x hx => ?_⟩
    have hx' : g * x * g⁻¹ ∈ P := mem_conjugate_iff.mp hx
    show conjugate (conjugate β g) x = conjugate β g
    rw [conjugate_conjugate]
    have e : g * x = (g * x * g⁻¹) * g := by group
    rw [e, ← conjugate_conjugate, hfix _ hx']

theorem conjugate_mul_mul (A : Subgroup X) (a b c : X) :
    conjugate A (a * b * c) = conjugate (conjugate (conjugate A a) b) c := by
  rw [conjugate_conjugate, conjugate_conjugate, mul_assoc]

theorem conjugate_injective (g : X) : Function.Injective (fun A : Subgroup X => conjugate A g) := by
  intro A B hAB
  have := congrArg (fun C : Subgroup X => conjugate C g⁻¹) hAB
  simpa [conjugate_conjugate, conjugate_one] using this

theorem ncard_omegaFix_conjugate (P : Subgroup X) (g : X) :
    (omegaFix M ((conjugate P g : Subgroup X) : Set X)).ncard =
      (omegaFix M (P : Set X)).ncard := by
  rw [omegaFix_conjugate]
  exact Set.ncard_image_of_injective _ (conjugate_injective g)

theorem conjugate_mem_omegaFix_of_mem_normalizer {P : Subgroup X} {n : X}
    (hn : n ∈ normalizer (P : Set X)) {β : Subgroup X} (hβ : β ∈ omegaFix M (P : Set X)) :
    conjugate β n ∈ omegaFix M (P : Set X) := by
  have h1 : conjugate P n = P := conjugate_eq_iff_mem_normalizer.mpr hn
  have h2 : omegaFix M ((conjugate P n : Subgroup X) : Set X) =
      (fun β => conjugate β n) '' omegaFix M (P : Set X) := omegaFix_conjugate P n
  rw [h1] at h2
  rw [h2]
  exact ⟨β, hβ, rfl⟩

theorem conjugate_mem_omegaFix_conjugate_iff (P : Subgroup X) (g : X) (β : Subgroup X) :
    conjugate β g ∈ omegaFix M ((conjugate P g : Subgroup X) : Set X) ↔
      β ∈ omegaFix M (P : Set X) := by
  rw [omegaFix_conjugate]
  exact ⟨fun ⟨β', hβ', hβ'g⟩ => by rwa [← conjugate_injective g hβ'g], fun h => ⟨β, h, rfl⟩⟩

end OmegaFix

section Action

variable {X : Type*} [Group X] {M : Subgroup X}

instance omegaMulAction (M : Subgroup X) : MulAction X (omega M) where
  smul g β := ⟨conjugate (β : Subgroup X) g⁻¹, conjugate_mem_omega β.2 g⁻¹⟩
  one_smul β := Subtype.ext (by
    show conjugate (β : Subgroup X) (1 : X)⁻¹ = β
    rw [inv_one, conjugate_one])
  mul_smul g h β := Subtype.ext (by
    show conjugate (β : Subgroup X) (g * h)⁻¹ = conjugate (conjugate (β : Subgroup X) h⁻¹) g⁻¹
    rw [conjugate_conjugate, mul_inv_rev])

theorem omegaMulAction_smul_coe (g : X) (β : omega M) :
    ((g • β : omega M) : Subgroup X) = conjugate (β : Subgroup X) g⁻¹ := rfl

theorem mem_fixedPoints_omegaMulAction_iff (P : Subgroup X) (β : omega M) :
    β ∈ MulAction.fixedPoints P (omega M) ↔ (β : Subgroup X) ∈ omegaFix M (P : Set X) := by
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    refine ⟨β.2, fun g hg => ?_⟩
    have := congrArg (fun γ : omega M => (γ : Subgroup X)) (h ⟨g⁻¹, P.inv_mem hg⟩)
    simpa [omegaMulAction_smul_coe] using this
  · rintro ⟨-, hfix⟩ g
    apply Subtype.ext
    have h1 : ((g • β : omega M) : Subgroup X) = conjugate (β : Subgroup X) (g : X)⁻¹ := rfl
    rw [h1]
    exact hfix _ (P.inv_mem g.2)

theorem ncard_omegaFix_eq_card_fixedPoints (P : Subgroup X) :
    (omegaFix M (P : Set X)).ncard = Nat.card ↥(MulAction.fixedPoints P (omega M)) := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun β => ⟨⟨β.1, β.2.1⟩, (mem_fixedPoints_omegaMulAction_iff P ⟨β.1, β.2.1⟩).mpr β.2⟩
      invFun := fun β => ⟨β.1.1, (mem_fixedPoints_omegaMulAction_iff P β.1).mp β.2⟩
      left_inv := fun β => rfl
      right_inv := fun β => rfl }

theorem ncard_omega_modEq_ncard_omegaFix [Finite X] {p : ℕ} (hp : p.Prime) {P : Subgroup X}
    (hP : IsPGroup p P) :
    (omega M).ncard ≡ (omegaFix M (P : Set X)).ncard [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (omega M) := Set.toFinite _
  rw [ncard_omegaFix_eq_card_fixedPoints, ← Nat.card_coe_set_eq]
  exact hP.card_modEq_card_fixedPoints (omega M)

end Action


section DoublyTransitive

variable {X : Type*} [Group X] {Z : Set X} {M : Subgroup X}

@[expose] def DoublyTransitive (M : Subgroup X) : Prop :=
  ∀ β₁ ∈ omega M, ∀ γ₁ ∈ omega M, β₁ ≠ γ₁ → ∀ β₂ ∈ omega M, ∀ γ₂ ∈ omega M, β₂ ≠ γ₂ →
    ∃ g : X, conjugate β₁ g = β₂ ∧ conjugate γ₁ g = γ₂

theorem exists_conjugate_eq_base {β : Subgroup X} (hβ : β ∈ omega M) :
    ∃ g : X, conjugate β g = M := by
  obtain ⟨k, rfl⟩ := hβ
  exact ⟨k⁻¹, by rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]⟩

theorem IsProductDisconnected.exists_mem_conjugate_of_doublyTransitive
    (h : IsProductDisconnected Z M) (hD : DoublyTransitive M) {β γ : Subgroup X}
    (hβ : β ∈ omega M) (hγ : γ ∈ omega M) (hβM : β ≠ M) (hγM : γ ≠ M) :
    ∃ m ∈ M, conjugate β m = γ := by
  obtain ⟨g, hg1, hg2⟩ := hD M (self_mem_omega M) β hβ hβM.symm M (self_mem_omega M) γ hγ hγM.symm
  refine ⟨g, ?_, hg2⟩
  rw [← h.normalizer_eq_self]
  exact conjugate_eq_iff_mem_normalizer.mp hg1

theorem IsProductDisconnected.doublyTransitive_of_baseTransitive (h : IsProductDisconnected Z M)
    (hT : ∀ β ∈ omega M, β ≠ M → ∀ γ ∈ omega M, γ ≠ M → ∃ m ∈ M, conjugate β m = γ) :
    DoublyTransitive M := by
  intro β₁ hβ₁ γ₁ hγ₁ h₁ β₂ hβ₂ γ₂ hγ₂ h₂
  obtain ⟨g₁, hg₁⟩ := exists_conjugate_eq_base hβ₁
  obtain ⟨g₂, hg₂⟩ := exists_conjugate_eq_base hβ₂
  have hγ₁' : conjugate γ₁ g₁ ∈ omega M := conjugate_mem_omega hγ₁ g₁
  have hγ₂' : conjugate γ₂ g₂ ∈ omega M := conjugate_mem_omega hγ₂ g₂
  have hne₁ : conjugate γ₁ g₁ ≠ M := by
    intro heq
    apply h₁
    apply conjugate_injective g₁
    simp only
    rw [hg₁, heq]
  have hne₂ : conjugate γ₂ g₂ ≠ M := by
    intro heq
    apply h₂
    apply conjugate_injective g₂
    simp only
    rw [hg₂, heq]
  obtain ⟨m, hmM, hm⟩ := hT _ hγ₁' hne₁ _ hγ₂' hne₂
  refine ⟨g₁ * m * g₂⁻¹, ?_, ?_⟩
  · have hm1 : conjugate M m = M := conjugate_eq_iff_mem_normalizer.mpr (by
      rw [h.normalizer_eq_self]; exact hmM)
    have e : conjugate β₁ (g₁ * m * g₂⁻¹) =
        conjugate (conjugate (conjugate β₁ g₁) m) g₂⁻¹ := by
      rw [conjugate_conjugate, conjugate_conjugate, mul_assoc]
    rw [e, hg₁, hm1, ← hg₂, conjugate_conjugate, mul_inv_cancel, conjugate_one]
  · have e : conjugate γ₁ (g₁ * m * g₂⁻¹) =
        conjugate (conjugate (conjugate γ₁ g₁) m) g₂⁻¹ := by
      rw [conjugate_conjugate, conjugate_conjugate, mul_assoc]
    rw [e, hm, conjugate_conjugate, mul_inv_cancel, conjugate_one]

end DoublyTransitive

section Witt

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem exists_mul_mem_normalizer_of_isSylowOf {p : ℕ} (hp : p.Prime) {R S₀ : Subgroup X}
    (hR : ABGLocalTools.IsSylowOf p R S₀) {g : X} (hRg : R ≤ conjugate S₀ g) :
    ∃ e ∈ S₀, e * g ∈ normalizer (R : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hR'le : conjugate R g⁻¹ ≤ S₀ := by
    intro x hx
    have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ R := mem_conjugate_iff.mp hx
    have h2 := mem_conjugate_iff.mp (hRg h1)
    have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
    rwa [e] at h2
  have hR' : ABGLocalTools.IsSylowOf p (conjugate R g⁻¹) S₀ := by
    refine ABGLocalTools.isSylowOf_of_card hR'le ?_
    have hcard : Nat.card ↥(conjugate R g⁻¹) = Nat.card R :=
      Subgroup.card_map_of_injective (MulAut.conj (g⁻¹)⁻¹).injective
    rw [hcard]
    exact hR.card_eq
  obtain ⟨w, hw, hwR⟩ := exists_conj_of_isSylowOf hR' hR
  rw [conjugate_conjugate] at hwR
  have hn : g⁻¹ * w ∈ normalizer (R : Set X) := conjugate_eq_iff_mem_normalizer.mp hwR
  refine ⟨w⁻¹, S₀.inv_mem hw, ?_⟩
  have := (normalizer (R : Set X)).inv_mem hn
  simpa [mul_inv_rev] using this

theorem IsProductDisconnected.isSylowOf_of_omegaFix_pair (h : IsProductDisconnected Z M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {G R β γ : Subgroup X} (hβγ : β ≠ γ)
    (hR : ABGLocalTools.IsSylowOf p R (G ⊓ β ⊓ γ)) (hΩ : omegaFix M (R : Set X) = {β, γ}) :
    ABGLocalTools.IsSylowOf p R G := by
  have : Fact p.Prime := ⟨hp⟩
  have hβΩ : β ∈ omegaFix M (R : Set X) := by rw [hΩ]; exact Or.inl rfl
  have hγΩ : γ ∈ omegaFix M (R : Set X) := by rw [hΩ]; exact Or.inr rfl
  have hRG : R ≤ G := hR.le.trans (inf_le_left.trans inf_le_left)
  set A : Subgroup X := G ⊓ normalizer (R : Set X) with hA
  have hRA : R ≤ A := le_inf hRG Subgroup.le_normalizer
  have hRβ : R ≤ β := (h.mem_omegaFix_iff.mp hβΩ).2
  have hAβ : A ⊓ β ≤ G ⊓ β ⊓ γ := by
    intro n hn
    obtain ⟨hnA, hnβ⟩ := Subgroup.mem_inf.mp hn
    obtain ⟨hnG, hnN⟩ := Subgroup.mem_inf.mp hnA
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hnG, hnβ⟩, ?_⟩
    have hγn := conjugate_mem_omegaFix_of_mem_normalizer hnN hγΩ
    rw [hΩ] at hγn
    rcases hγn with hγn | hγn
    · exfalso
      have hβn : conjugate β n = β := (h.conjugate_eq_iff_mem hβΩ.1).mpr hnβ
      exact hβγ (conjugate_injective n (hβn.trans hγn.symm))
    · exact (h.conjugate_eq_iff_mem hγΩ.1).mp hγn
  have hRAβ : R ≤ A ⊓ β := le_inf hRA hRβ
  have hRsyl : ABGLocalTools.IsSylowOf p R (A ⊓ β) := hR.of_le hRAβ hAβ
  have hidx : (A ⊓ β).relIndex A ≤ 2 := by
    let β₀ : omega M := ⟨β, hβΩ.1⟩
    let γ₀ : omega M := ⟨γ, hγΩ.1⟩
    have hstab : MulAction.stabilizer A β₀ = (A ⊓ β).subgroupOf A := by
      ext n
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have h1 : (n • β₀ : omega M) = β₀ ↔ conjugate β (n : X)⁻¹ = β := by
        constructor
        · intro hh
          exact congrArg (fun x : omega M => (x : Subgroup X)) hh
        · intro hh
          exact Subtype.ext hh
      rw [h1, h.conjugate_eq_iff_mem hβΩ.1]
      constructor
      · intro hn
        exact ⟨n.2, by simpa using β.inv_mem hn⟩
      · intro hn
        simpa using β.inv_mem (Subgroup.mem_inf.mp hn).2
    have horb : MulAction.orbit A β₀ ⊆ {β₀, γ₀} := by
      rintro _ ⟨n, rfl⟩
      have hn : (n : X)⁻¹ ∈ normalizer (R : Set X) :=
        (normalizer (R : Set X)).inv_mem (Subgroup.mem_inf.mp n.2).2
      have := conjugate_mem_omegaFix_of_mem_normalizer hn hβΩ
      rw [hΩ] at this
      rcases this with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    have hne : β₀ ≠ γ₀ := fun hh => hβγ (congrArg (fun x : omega M => (x : Subgroup X)) hh)
    have := MulAction.index_stabilizer A β₀
    rw [hstab] at this
    have h2 : (Subgroup.subgroupOf (A ⊓ β) A).index ≤ 2 := by
      rw [this]
      calc (MulAction.orbit A β₀).ncard ≤ ({β₀, γ₀} : Set (omega M)).ncard :=
            Set.ncard_le_ncard horb (Set.toFinite _)
        _ = 2 := Set.ncard_pair hne
    exact h2
  have hRA' : ABGLocalTools.IsSylowOf p R A := by
    rw [ABGLocalTools.isSylowOf_iff] at hRsyl ⊢
    obtain ⟨-, hRp, hndvd⟩ := hRsyl
    refine ⟨hRA, hRp, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex R (A ⊓ β) A hRAβ inf_le_left]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · exact hndvd h1
    · have hne0 : (A ⊓ β).relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) h1
      have h3 : p ≥ 3 := by
        have := hp.two_le
        omega
      omega
  obtain ⟨Q, hQ⟩ := (hR.isPGroup.comap_subtype (K := G)).exists_le_sylow
  set R' : Subgroup X := (Q : Subgroup G).map G.subtype with hR'
  have hR'syl : ABGLocalTools.IsSylowOf p R' G := ⟨Q, rfl⟩
  have hRR' : R ≤ R' := by
    intro x hx
    exact ⟨⟨x, hRG hx⟩, hQ (show (⟨x, hRG hx⟩ : G) ∈ R.subgroupOf G from hx), rfl⟩
  by_cases hEq : R = R'
  · rw [hEq]
    exact hR'syl
  · exfalso
    have hlt : R < R' := lt_of_le_of_ne hRR' hEq
    obtain ⟨R₁, hR₁p, hRR₁, hR₁R', hR₁N⟩ :=
      CFSG.BenderSuzuki.exists_larger_normalizer_pSubgroup hp hR'syl.isPGroup hlt
    have hR₁A : R₁ ≤ A := le_inf (hR₁R'.trans hR'syl.le) hR₁N
    have := hRA'.eq_of_le hRR₁.le hR₁A hR₁p
    exact absurd this (ne_of_gt hRR₁)


theorem IsProductDisconnected.isSylowOf_omegaFix_pair' (h : IsProductDisconnected Z M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {R β γ : Subgroup X} (hβγ : β ≠ γ)
    (hR : ABGLocalTools.IsSylowOf p R (β ⊓ γ)) (hΩ : omegaFix M (R : Set X) = {β, γ}) :
    ABGLocalTools.IsSylowOf p R ⊤ :=
  h.isSylowOf_of_omegaFix_pair hp hp2 hβγ (by simpa using hR) hΩ

theorem IsProductDisconnected.doublyTransitive_of_sylow (h : IsProductDisconnected Z M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hcrit : ∀ β ∈ omega M, ∀ γ ∈ omega M, β ≠ γ → ∀ P : Subgroup X,
      ABGLocalTools.IsSylowOf p P (β ⊓ γ) → omegaFix M (P : Set X) = {β, γ}) :
    DoublyTransitive M := by
  have : Fact p.Prime := ⟨hp⟩
  refine h.doublyTransitive_of_baseTransitive ?_
  intro β hβ hβM γ hγ hγM
  obtain ⟨P, hP⟩ := ABGLocalTools.exists_isSylowOf p (M ⊓ β)
  obtain ⟨Q, hQ⟩ := ABGLocalTools.exists_isSylowOf p (M ⊓ γ)
  have hPΩ := hcrit M (self_mem_omega M) β hβ hβM.symm P hP
  have hQΩ := hcrit M (self_mem_omega M) γ hγ hγM.symm Q hQ
  have hPtop : ABGLocalTools.IsSylowOf p P ⊤ :=
    h.isSylowOf_omegaFix_pair' hp hp2 hβM.symm (by simpa using hP) hPΩ
  have hQtop : ABGLocalTools.IsSylowOf p Q ⊤ :=
    h.isSylowOf_omegaFix_pair' hp hp2 hγM.symm (by simpa using hQ) hQΩ
  have hPM : P ≤ M := hP.le.trans inf_le_left
  have hQM : Q ≤ M := hQ.le.trans inf_le_left
  have hPM' : ABGLocalTools.IsSylowOf p P M := hPtop.of_le hPM le_top
  have hQM' : ABGLocalTools.IsSylowOf p Q M := hQtop.of_le hQM le_top
  obtain ⟨w, hw, hwPQ⟩ := exists_conj_of_isSylowOf hPM' hQM'
  refine ⟨w, hw, ?_⟩
  have h1 : omegaFix M (Q : Set X) = (fun β => conjugate β w) '' omegaFix M (P : Set X) := by
    rw [← hwPQ]
    exact omegaFix_conjugate P w
  rw [hPΩ, hQΩ] at h1
  have hβw : conjugate β w ∈ ({M, γ} : Set (Subgroup X)) := by
    rw [h1]
    exact ⟨β, Or.inr rfl, rfl⟩
  rcases hβw with hβw | hβw
  · exfalso
    have hMw : conjugate M w = M := conjugate_eq_iff_mem_normalizer.mpr (by
      rw [h.normalizer_eq_self]; exact hw)
    exact hβM (conjugate_injective w (hβw.trans hMw.symm))
  · exact hβw

end Witt

section Counting

variable {X : Type*} [Group X] {Z : Set X} {M : Subgroup X}

@[expose] noncomputable def zCosetNum (Z : Set X) (P : Subgroup X) (u : X) : ℕ :=
  Nat.card {y : X // y ∈ Z ∧ y * u⁻¹ ∈ P}

@[expose] noncomputable def zNumShare (Z : Set X) (M : Subgroup X) (p : ℕ) : ℕ :=
  p ^ (zNum Z M).factorization p

theorem zCosetNum_mono [Finite X] {P Q : Subgroup X} (hPQ : P ≤ Q) (u : X) :
    zCosetNum Z P u ≤ zCosetNum Z Q u := by
  let f : {y : X // y ∈ Z ∧ y * u⁻¹ ∈ P} → {y : X // y ∈ Z ∧ y * u⁻¹ ∈ Q} :=
    fun y => ⟨y, y.2.1, hPQ y.2.2⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (by
    have := congrArg (fun q : {y : X // y ∈ Z ∧ y * u⁻¹ ∈ Q} => (q : X)) hab
    exact this)
  exact Nat.card_le_card_of_injective f hf

theorem zCosetNum_conjugate (hZ : IsInvariantInvolutionSet Z) (P : Subgroup X) (u g : X) :
    zCosetNum Z (conjugate P g) (g⁻¹ * u * g) = zCosetNum Z P u := by
  have hZc : ∀ y ∈ Z, g * y * g⁻¹ ∈ Z := fun y hy => by
    have := hZ.2 y hy g⁻¹
    rwa [inv_inv] at this
  unfold zCosetNum
  refine Nat.card_congr
    { toFun := fun y => ⟨g * (y : X) * g⁻¹, hZc _ y.2.1, by
        have h1 : (y : X) * (g⁻¹ * u * g)⁻¹ ∈ conjugate P g := y.2.2
        have h2 := mem_conjugate_iff.mp h1
        have e : g * ((y : X) * (g⁻¹ * u * g)⁻¹) * g⁻¹ = g * (y : X) * g⁻¹ * u⁻¹ := by group
        rwa [e] at h2⟩
      invFun := fun w => ⟨g⁻¹ * (w : X) * g, hZ.2 _ w.2.1 g, by
        refine mem_conjugate_iff.mpr ?_
        have e : g * (g⁻¹ * (w : X) * g * (g⁻¹ * u * g)⁻¹) * g⁻¹ = (w : X) * u⁻¹ := by group
        rw [e]
        exact w.2.2⟩
      left_inv := fun y => Subtype.ext (by simp only [mul_assoc]; group)
      right_inv := fun w => Subtype.ext (by simp only [mul_assoc]; group) }

theorem zCosetNum_eq_card_invertedSet (hZ : IsInvariantInvolutionSet Z) {P : Subgroup X} {u : X}
    (hu : u ∈ Z) (hP : Odd (Nat.card P)) (huP : u ∈ normalizer (P : Set X)) :
    zCosetNum Z P u = Nat.card (CFSG.OddInversion.invertedSet P u) :=
  card_zCoset_eq_card_invertedSet hZ hu hP huP

end Counting

end CFSG.GH74.Uniqueness
