module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.LieType.BorelTits

theorem eq_of_inf_normalizer_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {W Q : Subgroup G} (hQ : IsPGroup p Q) (hWQ : W ≤ Q)
    (hN : Q ⊓ Subgroup.normalizer (W : Set G) ≤ W) : W = Q := by
  by_contra hne
  have hnf : W.subgroupOf Q ≠ ⊤ := fun h => hne (le_antisymm hWQ (Subgroup.subgroupOf_eq_top.mp h))
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : W.subgroupOf Q < Subgroup.normalizer ((W.subgroupOf Q : Subgroup Q) : Set Q) :=
    Group.normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.mpr hnf)
  obtain ⟨x, hxN, hxW⟩ := SetLike.exists_of_lt hlt
  apply hxW
  rw [Subgroup.mem_subgroupOf]
  refine hN ⟨x.2, ?_⟩
  have hx : x ∈ (Subgroup.normalizer (W : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hWQ]
    exact hxN
  exact hx

theorem exists_stable_overgroup {X : Type*} [Group X] [Finite X] (hX : Holds X 2) (φ : MulAut X)
    {A V : Subgroup X} (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hVφ : V.map φ.toMonoidHom = V)
    (hAV : A ≤ Subgroup.normalizer (V : Set X)) :
    ∃ (P : Subgroup X) (S : Sylow 2 X), P ≠ ⊤ ∧
      Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P ∧ A ≤ P ∧ P.map φ.toMonoidHom = P := by
  classical
  haveI : Finite (Subgroup X) := Finite.of_injective _ SetLike.coe_injective
  set 𝒲 : Set (Subgroup X) := {W | IsPGroup 2 W ∧ W.map φ.toMonoidHom = W ∧
    A ≤ Subgroup.normalizer (W : Set X)} with h𝒲
  have hV𝒲 : V ∈ 𝒲 := ⟨hV2, hVφ, hAV⟩
  obtain ⟨W, ⟨hW2, hWφ, hAW⟩, hWmax⟩ :=
    Set.exists_max_image 𝒲 (fun W : Subgroup X => Nat.card W) (Set.toFinite _) ⟨V, hV𝒲⟩
  have hWne : W ≠ ⊥ := by
    intro hbot
    have h := hWmax V hV𝒲
    rw [hbot, Subgroup.card_bot] at h
    exact hV (Subgroup.eq_bot_of_card_le V h)
  have hNφ : (Subgroup.normalizer (W : Set X)).map φ.toMonoidHom =
      Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.map_equiv_normalizer_eq W φ, hWφ]
  have hRW : pCoreOf 2 (Subgroup.normalizer (W : Set X)) = W := by
    have hWR : W ≤ pCoreOf 2 (Subgroup.normalizer (W : Set X)) := le_pCoreOf_normalizer 2 W hW2
    have hR𝒲 : pCoreOf 2 (Subgroup.normalizer (W : Set X)) ∈ 𝒲 := by
      refine ⟨pCoreOf_isPGroup 2 _, ?_, hAW.trans (le_normalizer_pCoreOf 2 _)⟩
      rw [← pCoreOf_map_mulEquiv, hNφ]
    exact (Subgroup.eq_of_le_of_card_ge hWR (hWmax _ hR𝒲)).symm
  obtain ⟨S, P, hPtop, hNP, -, hWP, hSP⟩ := hX W hWne hW2
  have hQ2 : IsPGroup 2 (pCoreOf 2 P) := pCoreOf_isPGroup 2 P
  have hQN : pCoreOf 2 P ⊓ Subgroup.normalizer (W : Set X) ≤ W := by
    refine (le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hQ2.to_le inf_le_left)).trans hRW.le
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P (hNP hn)) z
    have h2 := Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer (H := Subgroup.normalizer (W : Set X)) hn) z
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩
  have hWQ : W = pCoreOf 2 P := eq_of_inf_normalizer_le hQ2 hWP hQN
  have hPN : P ≤ Subgroup.normalizer (W : Set X) := by
    rw [hWQ]
    exact le_normalizer_pCoreOf 2 P
  have hNeq : Subgroup.normalizer (W : Set X) = P := le_antisymm hNP hPN
  refine ⟨P, S, hPtop, hSP, hNeq ▸ hAW, ?_⟩
  rw [← hNeq]
  exact hNφ

theorem exists_twisted_fixed_coset {G : Type*} [Group G] [Finite G] {P₁ P₂ A : Subgroup G}
    (h12 : P₁ ≤ P₂) (φ : G →* G) (hφ3 : ∀ x, φ (φ (φ x)) = x) (hφ1 : ∀ x ∈ P₁, φ x ∈ P₁)
    (hφ2 : ∀ x ∈ P₂, φ x ∈ P₂) {y : G} (hy : y ∈ P₂) (hyy : y * φ y * φ (φ y) = 1)
    (hA : IsPGroup 3 A) (hA2 : A ≤ P₂) (hAy : ∀ a ∈ A, y * φ a * y⁻¹ = a)
    (hidx : ¬ 3 ∣ (P₁.subgroupOf P₂).index) :
    ∃ x ∈ P₂, x⁻¹ * y * φ x ∈ P₁ ∧ ∀ a ∈ A, x⁻¹ * a * x ∈ P₁ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L : Subgroup P₂ := P₁.subgroupOf P₂ with hL
  let f : P₂ → P₂ := fun x => ⟨y * φ x, mul_mem hy (hφ2 x x.2)⟩
  have hf : ∀ a b : P₂, a⁻¹ * b ∈ L → (f a)⁻¹ * f b ∈ L := by
    intro a b hab
    rw [hL, Subgroup.mem_subgroupOf] at hab ⊢
    have h : ((f a)⁻¹ * f b : P₂) = φ ((a⁻¹ * b : P₂) : G) := by
      simp only [f, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, mul_inv_rev]
      group
    rw [h]
    exact hφ1 _ hab
  let τ : P₂ ⧸ L → P₂ ⧸ L := Quotient.map' f fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hf a b hab
  have hτ : ∀ x : P₂, τ (x : P₂ ⧸ L) = ((f x : P₂) : P₂ ⧸ L) := fun _ => rfl
  set A₂ : Subgroup P₂ := A.subgroupOf P₂ with hA₂
  have hA₂p : IsPGroup 3 A₂ := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hA2).symm
  set F₁ : Set (P₂ ⧸ L) := MulAction.fixedPoints A₂ (P₂ ⧸ L) with hF₁
  have hcomm : ∀ (a : A₂) (ω : P₂ ⧸ L), a • τ ω = τ (a • ω) := by
    intro a ω
    induction ω using QuotientGroup.induction_on with
    | H x =>
      rw [Subgroup.smul_def, Subgroup.smul_def, hτ, MulAction.Quotient.smul_mk,
        MulAction.Quotient.smul_mk, hτ]
      congr 1
      apply Subtype.ext
      have ha : ((a : P₂) : G) ∈ A := a.2
      simp only [f, smul_eq_mul, Subgroup.coe_mul, map_mul]
      rw [← mul_assoc, ← mul_assoc]
      congr 1
      have h := hAy _ ha
      calc ((a : P₂) : G) * y = (y * φ ((a : P₂) : G) * y⁻¹) * y := by rw [h]
        _ = y * φ ((a : P₂) : G) := by group
  have hτF : ∀ ω ∈ F₁, τ ω ∈ F₁ := by
    intro ω hω a
    rw [hcomm, hω a]
  have hτ3 : ∀ ω : P₂ ⧸ L, τ (τ (τ ω)) = ω := by
    intro ω
    induction ω using QuotientGroup.induction_on with
    | H x =>
      rw [hτ, hτ, hτ]
      congr 1
      apply Subtype.ext
      simp only [f, map_mul, hφ3]
      calc y * (φ y * (φ (φ y) * (x : G))) = (y * φ y * φ (φ y)) * x := by group
        _ = x := by rw [hyy, one_mul]
  haveI : Fintype (P₂ ⧸ L) := Fintype.ofFinite _
  haveI : Fintype F₁ := Fintype.ofFinite _
  let T : Function.End F₁ := fun ω => ⟨τ ω, hτF ω ω.2⟩
  have hT : T ^ 3 ^ 1 = 1 := by
    funext ω
    apply Subtype.ext
    exact hτ3 ω
  have h1 : Nat.card (P₂ ⧸ L) ≡ Nat.card F₁ [MOD 3] := hA₂p.card_modEq_card_fixedPoints _
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := T) hT
  rw [← Nat.card_eq_fintype_card] at h2
  obtain ⟨ω, hωT⟩ : (Function.fixedPoints T).Nonempty := by
    rw [← Set.nonempty_coe_sort, ← not_isEmpty_iff]
    intro hempty
    rw [Fintype.card_eq_zero] at h2
    apply hidx
    have h3 : Nat.card (P₂ ⧸ L) ≡ 0 [MOD 3] := h1.trans h2
    exact Nat.dvd_of_mod_eq_zero h3
  obtain ⟨ω, hωF⟩ := ω
  have hτω : τ ω = ω := congrArg Subtype.val hωT
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ω
  refine ⟨x, x.2, ?_, fun a ha => ?_⟩
  · rw [hτ, QuotientGroup.eq] at hτω
    have h := inv_mem hτω
    rw [hL, Subgroup.mem_subgroupOf] at h
    simpa [f, mul_assoc] using h
  · have h := hωF ⟨⟨a, hA2 ha⟩, by rw [hA₂, Subgroup.mem_subgroupOf]; exact ha⟩
    rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, QuotientGroup.eq] at h
    have h' := inv_mem h
    rw [hL, Subgroup.mem_subgroupOf] at h'
    simpa [mul_assoc] using h'

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
