module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalStandardInvolution
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalSmallStandardSource
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.ComponentClassification.SymmetricLocal

open Equiv Subgroup CFSG.Assembly.LowTwoRank

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem isComponentOf_map_of_injective (f : A →* B) (hf : Function.Injective f)
    {K H : Subgroup A} (hK : CFSG.Assembly.IsComponentOf K H) :
    CFSG.Assembly.IsComponentOf (K.map f) (H.map f) := by
  obtain ⟨hKH, hs, hq⟩ := hK
  refine ⟨Subgroup.map_mono hKH, ?_, ?_⟩
  · exact (AssemblyBPredicates.isSubnormal_iff_open _ _).2
      (Components.chain_map f ((AssemblyBPredicates.isSubnormal_iff_open K H).1 hs))
  · rw [AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
    exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr (K.equivMapOfInjective f hf)).1 hq

theorem map_centralizer_singleton_of_injective (f : A →* B) (hf : Function.Injective f) (a : A) :
    (centralizer ({a} : Set A)).map f = f.range ⊓ centralizer ({f a} : Set B) := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hc]
  · rintro ⟨⟨c, rfl⟩, h⟩
    refine ⟨c, mem_centralizer_singleton_iff.mpr (hf ?_), rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_singleton_iff.mp h

theorem map_centralizer_of_injective (f : A →* B) (hf : Function.Injective f) (L : Subgroup A) :
    (centralizer (L : Set A)).map f = f.range ⊓ centralizer ((L.map f : Subgroup B) : Set B) := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc l hl]
  · rintro ⟨⟨c, rfl⟩, h⟩
    refine ⟨c, mem_centralizer_iff.mpr fun l hl => hf ?_, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp h (f l) ⟨l, hl, rfl⟩

end Transport

theorem socle_selector_permutation_data {A : Type*} [Group A] [Finite A] {W : Subgroup A}
    [W.Normal] (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2)
    {L : Subgroup A} (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) (φ : W ≃* alternatingGroup (Fin n)) :
    ∃ β : A →* Perm (Fin n), Function.Injective β ∧ (∀ w : W, β w = φ w) ∧
      alternatingGroup (Fin n) ≤ β.range ∧ IsSimpleGroup L ∧
      L.map β = (alternatingGroup {x // β a x = x}).map Perm.ofSubtype ∧
      Xor (β.range = ⊤ ∧ Nat.card {x // β a x ≠ x} = 2 ∧
          ∃ u v : Fin n, u ≠ v ∧ (∀ x, β a x ≠ x ↔ x = u ∨ x = v) ∧ β a = swap u v)
        (β.range = alternatingGroup (Fin n) ∧ Nat.card {x // β a x ≠ x} = 4 ∧
          ∃ u v w z : Fin n, u ≠ v ∧ u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ w ≠ z ∧
            (∀ x, β a x ≠ x ↔ x = u ∨ x = v ∨ x = w ∨ x = z) ∧ β a = swap u v * swap w z) ∧
      centralizer (L : Set A) =
        (β.range ⊓ (Perm.ofSubtype : Perm {x // β a x ≠ x} →* Perm (Fin n)).range).comap β ∧
      5 ≤ Nat.card {x // β a x = x} ∧
      Nat.card {x // β a x = x} + Nat.card {x // β a x ≠ x} = n ∧
      Nonempty (L ⧸ center L ≃* alternatingGroup {x // β a x = x}) := by
  have hκinj : Function.Injective
      (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) := by
    rw [injective_iff_map_eq_one]
    intro τ hτ
    refine LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
      (by rw [Fintype.card_fin]; omega) fun g hg => ?_
    have h := congrArg (fun χ : MulAut (alternatingGroup (Fin n)) =>
      ((χ ⟨g, hg⟩ : alternatingGroup (Fin n)) : Perm (Fin n))) hτ
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc τ * g = τ * g * τ⁻¹ * τ := by group
      _ = g * τ := by rw [h]
  set κ : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      ⟨hκinj, CatalogueSchreierAlternating.conjugation_surjective hn⟩ with hκ
  set α : A →* MulAut (alternatingGroup (Fin n)) :=
    (MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal with hα
  set β : A →* Perm (Fin n) := κ.symm.toMonoidHom.comp α with hβdef
  have hκβ : ∀ g, κ (β g) = α g := fun g => κ.apply_symm_apply (α g)
  have hαapply : ∀ (g : A) (y : alternatingGroup (Fin n)),
      α g y = φ (MulAut.conjNormal g (φ.symm y)) := fun _ _ => rfl
  have hκapply : ∀ (τ : Perm (Fin n)) (y : alternatingGroup (Fin n)),
      ((κ τ y : alternatingGroup (Fin n)) : Perm (Fin n)) = τ * y * τ⁻¹ := fun _ _ => rfl
  have hβW : ∀ w : W, β w = φ w := by
    intro w
    have h : α w = κ (φ w) := by
      ext y
      rw [hαapply, hκapply]
      have hconj : MulAut.conjNormal (w : A) (φ.symm y) = w * φ.symm y * w⁻¹ :=
        Subtype.ext rfl
      rw [hconj, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
    rw [← hκβ] at h
    exact κ.injective h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hα1 : α g = 1 := by rw [← hκβ, hg, map_one]
    have hgW : g ∈ centralizer (W : Set A) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun χ : MulAut (alternatingGroup (Fin n)) => χ (φ ⟨x, hx⟩)) hα1
      simp only [MulAut.one_apply] at h
      rw [hαapply, MulEquiv.symm_apply_apply] at h
      have h3 : g * x * g⁻¹ = x := by
        simpa only [MulAut.conjNormal_apply] using congrArg Subtype.val (φ.injective h)
      calc x * g = g * x * g⁻¹ * g := by rw [h3]
        _ = g * x := by group
    rw [hCW] at hgW
    exact hgW
  have hAltT : alternatingGroup (Fin n) ≤ β.range := by
    intro y hy
    refine ⟨(φ.symm ⟨y, hy⟩ : A), ?_⟩
    rw [hβW, MulEquiv.apply_symm_apply]
  have hσT : β a ∈ β.range := ⟨a, rfl⟩
  have hσ : orderOf (β a) = 2 := by rw [orderOf_injective β hinj a]; exact ha
  have hL' : CFSG.Assembly.IsComponentOf (L.map β)
      (β.range ⊓ centralizer ({β a} : Set (Perm (Fin n)))) := by
    rw [← map_centralizer_singleton_of_injective β hinj a]
    exact isComponentOf_map_of_injective β hinj hL
  have hCL := map_centralizer_of_injective β hinj L
  obtain ⟨-, heven, hodd, -, -⟩ := hstd
  have heven' : Even (Nat.card ↥(β.range ⊓
      centralizer ((L.map β : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))))) := by
    rw [← hCL, Subgroup.card_map_of_injective hinj]
    exact heven
  have hnorm : ∀ g ∈ β.range, ∀ z ∈ β.range ⊓
      centralizer ((L.map β : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))), orderOf z = 2 →
      g * z = z * g → ∀ c ∈ β.range ⊓
        centralizer ((L.map β : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))),
        g * c * g⁻¹ ∈ β.range ⊓
          centralizer ((L.map β : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
    rw [← hCL]
    rintro _ ⟨g, rfl⟩ _ ⟨z, hz, rfl⟩ hz2 hgz _ ⟨c, hc, rfl⟩
    have hz2' : orderOf z = 2 := by rwa [orderOf_injective β hinj z] at hz2
    have hgz' : g * z = z * g := hinj (by rw [map_mul, map_mul]; exact hgz)
    have hgN : g ∈ normalizer (centralizer (L : Set A) : Set A) := by
      by_contra hgN
      have hodd' := hodd g hgN
      have hzmem : z ∈ centralizer (L : Set A) ⊓
          (centralizer (L : Set A)).map (MulAut.conj g).toMonoidHom := by
        refine ⟨hz, z, hz, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hgz', mul_inv_cancel_right]
      have hdvd := Subgroup.orderOf_dvd_natCard _ hzmem
      rw [hz2'] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr hdvd)
    refine ⟨g * c * g⁻¹, (mem_normalizer_iff.mp hgN c).mp hc, ?_⟩
    rw [map_mul, map_mul, map_inv]
  obtain ⟨hF5, hLalt, hCeq, hxor, -, -⟩ :=
    natural_permutation_standard_core hAltT hσT hσ hL' heven' hnorm
  let eL : L ≃* alternatingGroup {x // β a x = x} :=
    (L.equivMapOfInjective β hinj).trans ((MulEquiv.subgroupCongr hLalt).trans
      ((alternatingGroup _).equivMapOfInjective _ Perm.ofSubtype_injective).symm)
  have : IsSimpleGroup (alternatingGroup {x // β a x = x}) := alternatingGroup.isSimpleGroup hF5
  have hLsimple : IsSimpleGroup L := eL.isSimpleGroup
  have hcentL : centralizer (L : Set A) = (β.range ⊓
      (Perm.ofSubtype : Perm {x // β a x ≠ x} →* Perm (Fin n)).range).comap β := by
    rw [← hCeq, ← hCL, Subgroup.comap_map_eq_self_of_injective hinj]
  have hsum : Nat.card {x // β a x = x} + Nat.card {x // β a x ≠ x} = n := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Fintype.card_subtype]
    simp only [ne_eq]
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hcenter : center L = ⊥ := by
    have h := Subgroup.map_center_eq eL
    rw [alternatingGroup.center_eq_bot (by omega)] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ eL.injective).mp h
  exact ⟨β, hinj, hβW, hAltT, hLsimple, hLalt, hxor, hcentL, hF5, hsum,
    ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans eL)⟩⟩

theorem socle_selector_support_card {n : ℕ} (hn : 2 ≤ n) {T : Subgroup (Perm (Fin n))}
    {σ : Perm (Fin n)} {P Q : Prop}
    (hxor : Xor (T = ⊤ ∧ Nat.card {x // σ x ≠ x} = 2 ∧ P)
      (T = alternatingGroup (Fin n) ∧ Nat.card {x // σ x ≠ x} = 4 ∧ Q)) :
    (T = ⊤ ∨ T = alternatingGroup (Fin n)) ∧ (T = ⊤ → Nat.card {x // σ x ≠ x} = 2) ∧
      (T = alternatingGroup (Fin n) → Nat.card {x // σ x ≠ x} = 4) := by
  have hAne : alternatingGroup (Fin n) ≠ ⊤ :=
    alternatingGroup_ne_top (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) (by simp)
  rcases xor_def.mp hxor with ⟨hP, -⟩ | ⟨hQ, -⟩
  · exact ⟨Or.inl hP.1, fun _ => hP.2.1, fun hT => absurd (hT.symm.trans hP.1) hAne⟩
  · exact ⟨Or.inr hQ.1, fun hT => absurd (hQ.1.symm.trans hT) hAne, fun _ => hQ.2.1⟩

theorem classicalModel_psl_two_three_two_of_alternating_six {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 6)) : Assembly.ComponentType.ClassicalModel X .PSL 2 3 2 := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨ψ⟩ :=
    LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      (GaloisField 3 2) hcard
  refine ⟨⟨by norm_num, by norm_num, le_rfl, by norm_num⟩, ⟨?_⟩⟩
  exact e.trans (ψ.symm.trans
    ((projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 3 2)).trans
      (ClassicalModelStatedBridge.pslModelEquiv 2 3 2).symm))

theorem faithful_alternating_socle_small_standard_source_selector {A : Type} [Group A] [Finite A]
    {W : Subgroup A} [W.Normal] (_hWsimple : IsSimpleGroup W)
    (_hWnonab : ∃ x y : W, x * y ≠ y * x) (hCW : centralizer (W : Set A) = ⊥) {a : A}
    (ha : orderOf a = 2) {L : Subgroup A} (_hLW : L ≤ W)
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hsource : (∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧
        Assembly.ComponentType.ClassicalModel (L ⧸ center L) .PSL 2 p f) ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      Assembly.ComponentType.ClassicalModel (L ⧸ center L) .PSL 3 2 2)
    {n : ℕ} (hn : 5 ≤ n) (φ : W ≃* alternatingGroup (Fin n)) :
    ((n = 6 ∧ Assembly.ComponentType.ClassicalModel W .PSL 2 3 2) ∨ (7 ≤ n ∧ n ≤ 11)) ∧
    (n ≠ 6 → ∃ β : A →* Perm (Fin n), Function.Injective β ∧ (∀ w : W, β w = φ w) ∧
      alternatingGroup (Fin n) ≤ β.range ∧ IsSimpleGroup L ∧
      L.map β = (alternatingGroup {x // β a x = x}).map Perm.ofSubtype ∧
      Xor (β.range = ⊤ ∧ Nat.card {x // β a x ≠ x} = 2 ∧
          ∃ u v : Fin n, u ≠ v ∧ (∀ x, β a x ≠ x ↔ x = u ∨ x = v) ∧ β a = swap u v)
        (β.range = alternatingGroup (Fin n) ∧ Nat.card {x // β a x ≠ x} = 4 ∧
          ∃ u v w z : Fin n, u ≠ v ∧ u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ w ≠ z ∧
            (∀ x, β a x ≠ x ↔ x = u ∨ x = v ∨ x = w ∨ x = z) ∧ β a = swap u v * swap w z) ∧
      centralizer (L : Set A) =
        (β.range ⊓ (Perm.ofSubtype : Perm {x // β a x ≠ x} →* Perm (Fin n)).range).comap β ∧
      (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 →
        Assembly.ComponentType.ClassicalModel (L ⧸ center L) .PSL 2 p f →
        (Nat.card {x // β a x = x} = 5 ∧ p = 5 ∧ f = 1 ∧ (β.range = ⊤ → n = 7) ∧
            (β.range = alternatingGroup (Fin n) → n = 9)) ∨
          (Nat.card {x // β a x = x} = 6 ∧ p = 3 ∧ f = 2 ∧ (β.range = ⊤ → n = 8) ∧
            (β.range = alternatingGroup (Fin n) → n = 10))) ∧
      (Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
        Nat.card {x // β a x = x} = 7 ∧ (β.range = ⊤ → n = 9) ∧
          (β.range = alternatingGroup (Fin n) → n = 11)) ∧
      ¬ Assembly.ComponentType.ClassicalModel (L ⧸ center L) .PSL 3 2 2) := by
  by_cases h6 : n = 6
  · subst h6
    exact ⟨Or.inl ⟨rfl, classicalModel_psl_two_three_two_of_alternating_six φ⟩,
      fun h => absurd rfl h⟩
  obtain ⟨β, hinj, hβW, hAltT, hLsimple, hLalt, hxor, hcentL, hF5, hsum, ⟨eQ⟩⟩ :=
    socle_selector_permutation_data hCW ha hL hstd (by omega) φ
  obtain ⟨hTcases, hΔsym, hΔalt⟩ := socle_selector_support_card (by omega) hxor
  obtain ⟨h1, h2, h3⟩ := small_standard_source_alternating_degree_and_parameters
    (Ω := {x // β a x = x}) (by rw [← Nat.card_eq_fintype_card]; exact hF5) ⟨eQ⟩
  simp only [← Nat.card_eq_fintype_card] at h1 h2
  have hpsl : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 →
      Assembly.ComponentType.ClassicalModel (L ⧸ center L) .PSL 2 p f →
      (Nat.card {x // β a x = x} = 5 ∧ p = 5 ∧ f = 1 ∧ (β.range = ⊤ → n = 7) ∧
          (β.range = alternatingGroup (Fin n) → n = 9)) ∨
        (Nat.card {x // β a x = x} = 6 ∧ p = 3 ∧ f = 2 ∧ (β.range = ⊤ → n = 8) ∧
          (β.range = alternatingGroup (Fin n) → n = 10)) := by
    intro p f _ hp2 hmodel
    rcases h1 p f hp2 hmodel with ⟨hF, hp, hf⟩ | ⟨hF, hp, hf⟩
    · exact Or.inl ⟨hF, hp, hf, fun hT => by have := hΔsym hT; omega,
        fun hT => by have := hΔalt hT; omega⟩
    · exact Or.inr ⟨hF, hp, hf, fun hT => by have := hΔsym hT; omega,
        fun hT => by have := hΔalt hT; omega⟩
  have halt7 : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
      Nat.card {x // β a x = x} = 7 ∧ (β.range = ⊤ → n = 9) ∧
        (β.range = alternatingGroup (Fin n) → n = 11) := by
    intro h7
    have hF := h2 h7
    exact ⟨hF, fun hT => by have := hΔsym hT; omega, fun hT => by have := hΔalt hT; omega⟩
  refine ⟨Or.inr ?_, fun _ => ⟨β, hinj, hβW, hAltT, hLsimple, hLalt, hxor, hcentL, hpsl, halt7,
    h3⟩⟩
  rcases hsource with ⟨p, f, _, hp2, hmodel⟩ | h7 | h322
  · rcases hpsl p f hp2 hmodel with ⟨-, -, -, hs, ha'⟩ | ⟨-, -, -, hs, ha'⟩ <;>
      rcases hTcases with hT | hT
    · have := hs hT; omega
    · have := ha' hT; omega
    · have := hs hT; omega
    · have := ha' hT; omega
  · obtain ⟨-, hs, ha'⟩ := halt7 h7
    rcases hTcases with hT | hT
    · have := hs hT; omega
    · have := ha' hT; omega
  · exact absurd h322 h3

theorem faithful_alternating_socle_small_standard_source_selector_of_psl_two_or_alt_seven
    {A : Type} [Group A] [Finite A]
    {W : Subgroup A} [W.Normal] (_hWsimple : IsSimpleGroup W)
    (_hWnonab : ∃ x y : W, x * y ≠ y * x) (hCW : centralizer (W : Set A) = ⊥) {a : A}
    (ha : orderOf a = 2) {L : Subgroup A} (_hLW : L ≤ W)
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hsource : (∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧
        Assembly.ComponentType.ClassicalModel (L ⧸ center L) .PSL 2 p f) ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)))
    {n : ℕ} (hn : 5 ≤ n) (φ : W ≃* alternatingGroup (Fin n)) :
    ((n = 6 ∧ Assembly.ComponentType.ClassicalModel W .PSL 2 3 2) ∨ (7 ≤ n ∧ n ≤ 11)) ∧
    (n ≠ 6 → ∃ β : A →* Perm (Fin n), Function.Injective β ∧ (∀ w : W, β w = φ w) ∧
      alternatingGroup (Fin n) ≤ β.range ∧ IsSimpleGroup L ∧
      L.map β = (alternatingGroup {x // β a x = x}).map Perm.ofSubtype ∧
      Xor (β.range = ⊤ ∧ Nat.card {x // β a x ≠ x} = 2 ∧
          ∃ u v : Fin n, u ≠ v ∧ (∀ x, β a x ≠ x ↔ x = u ∨ x = v) ∧ β a = swap u v)
        (β.range = alternatingGroup (Fin n) ∧ Nat.card {x // β a x ≠ x} = 4 ∧
          ∃ u v w z : Fin n, u ≠ v ∧ u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ w ≠ z ∧
            (∀ x, β a x ≠ x ↔ x = u ∨ x = v ∨ x = w ∨ x = z) ∧ β a = swap u v * swap w z) ∧
      centralizer (L : Set A) =
        (β.range ⊓ (Perm.ofSubtype : Perm {x // β a x ≠ x} →* Perm (Fin n)).range).comap β ∧
      (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 →
        Assembly.ComponentType.ClassicalModel (L ⧸ center L) .PSL 2 p f →
        (Nat.card {x // β a x = x} = 5 ∧ p = 5 ∧ f = 1 ∧ (β.range = ⊤ → n = 7) ∧
            (β.range = alternatingGroup (Fin n) → n = 9)) ∨
          (Nat.card {x // β a x = x} = 6 ∧ p = 3 ∧ f = 2 ∧ (β.range = ⊤ → n = 8) ∧
            (β.range = alternatingGroup (Fin n) → n = 10))) ∧
      (Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
        Nat.card {x // β a x = x} = 7 ∧ (β.range = ⊤ → n = 9) ∧
          (β.range = alternatingGroup (Fin n) → n = 11))) := by
  by_cases h6 : n = 6
  · subst h6
    exact ⟨Or.inl ⟨rfl, classicalModel_psl_two_three_two_of_alternating_six φ⟩,
      fun h => absurd rfl h⟩
  obtain ⟨β, hinj, hβW, hAltT, hLsimple, hLalt, hxor, hcentL, hF5, hsum, ⟨eQ⟩⟩ :=
    socle_selector_permutation_data hCW ha hL hstd (by omega) φ
  obtain ⟨hTcases, hΔsym, hΔalt⟩ := socle_selector_support_card (by omega) hxor
  obtain ⟨h1, h2⟩ := alternating_psl_two_parameters_and_degree_seven
    (Ω := {x // β a x = x}) (by rw [← Nat.card_eq_fintype_card]; exact hF5) ⟨eQ⟩
  simp only [← Nat.card_eq_fintype_card] at h1 h2
  have hpsl : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 →
      Assembly.ComponentType.ClassicalModel (L ⧸ center L) .PSL 2 p f →
      (Nat.card {x // β a x = x} = 5 ∧ p = 5 ∧ f = 1 ∧ (β.range = ⊤ → n = 7) ∧
          (β.range = alternatingGroup (Fin n) → n = 9)) ∨
        (Nat.card {x // β a x = x} = 6 ∧ p = 3 ∧ f = 2 ∧ (β.range = ⊤ → n = 8) ∧
          (β.range = alternatingGroup (Fin n) → n = 10)) := by
    intro p f _ hp2 hmodel
    rcases h1 p f hp2 hmodel with ⟨hF, hp, hf⟩ | ⟨hF, hp, hf⟩
    · exact Or.inl ⟨hF, hp, hf, fun hT => by have := hΔsym hT; omega,
        fun hT => by have := hΔalt hT; omega⟩
    · exact Or.inr ⟨hF, hp, hf, fun hT => by have := hΔsym hT; omega,
        fun hT => by have := hΔalt hT; omega⟩
  have halt7 : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
      Nat.card {x // β a x = x} = 7 ∧ (β.range = ⊤ → n = 9) ∧
        (β.range = alternatingGroup (Fin n) → n = 11) := by
    intro h7
    have hF := h2 h7
    exact ⟨hF, fun hT => by have := hΔsym hT; omega, fun hT => by have := hΔalt hT; omega⟩
  refine ⟨Or.inr ?_, fun _ => ⟨β, hinj, hβW, hAltT, hLsimple, hLalt, hxor, hcentL, hpsl,
    halt7⟩⟩
  rcases hsource with ⟨p, f, _, hp2, hmodel⟩ | h7
  · rcases hpsl p f hp2 hmodel with ⟨-, -, -, hs, ha'⟩ | ⟨-, -, -, hs, ha'⟩ <;>
      rcases hTcases with hT | hT
    · have := hs hT; omega
    · have := ha' hT; omega
    · have := hs hT; omega
    · have := ha' hT; omega
  · obtain ⟨-, hs, ha'⟩ := halt7 h7
    rcases hTcases with hT | hT
    · have := hs hT; omega
    · have := ha' hT; omega

theorem faithful_alternating_socle_small_standard_source_selector_stated {A : Type} [Group A]
    [Finite A]
    {W : Subgroup A} [W.Normal] (_hWsimple : IsSimpleGroup W)
    (_hWnonab : ∃ x y : W, x * y ≠ y * x) (hCW : centralizer (W : Set A) = ⊥) {a : A}
    (ha : orderOf a = 2) {L : Subgroup A} (_hLW : L ≤ W)
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hsource : (∃ p f : ℕ, p ≠ 2 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f) ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    {n : ℕ} (hn : 5 ≤ n) (φ : W ≃* alternatingGroup (Fin n)) :
    ((n = 6 ∧ StatedClassicalModel W .PSL 2 3 2) ∨ (7 ≤ n ∧ n ≤ 11)) ∧
    (n ≠ 6 → ∃ β : A →* Perm (Fin n), Function.Injective β ∧ (∀ w : W, β w = φ w) ∧
      alternatingGroup (Fin n) ≤ β.range ∧ IsSimpleGroup L ∧
      L.map β = (alternatingGroup {x // β a x = x}).map Perm.ofSubtype ∧
      Xor (β.range = ⊤ ∧ Nat.card {x // β a x ≠ x} = 2 ∧
          ∃ u v : Fin n, u ≠ v ∧ (∀ x, β a x ≠ x ↔ x = u ∨ x = v) ∧ β a = swap u v)
        (β.range = alternatingGroup (Fin n) ∧ Nat.card {x // β a x ≠ x} = 4 ∧
          ∃ u v w z : Fin n, u ≠ v ∧ u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ w ≠ z ∧
            (∀ x, β a x ≠ x ↔ x = u ∨ x = v ∨ x = w ∨ x = z) ∧ β a = swap u v * swap w z) ∧
      centralizer (L : Set A) =
        (β.range ⊓ (Perm.ofSubtype : Perm {x // β a x ≠ x} →* Perm (Fin n)).range).comap β ∧
      (∀ p f : ℕ, p ≠ 2 → StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
        (Nat.card {x // β a x = x} = 5 ∧ p = 5 ∧ f = 1 ∧ (β.range = ⊤ → n = 7) ∧
            (β.range = alternatingGroup (Fin n) → n = 9)) ∨
          (Nat.card {x // β a x = x} = 6 ∧ p = 3 ∧ f = 2 ∧ (β.range = ⊤ → n = 8) ∧
            (β.range = alternatingGroup (Fin n) → n = 10))) ∧
      (Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
        Nat.card {x // β a x = x} = 7 ∧ (β.range = ⊤ → n = 9) ∧
          (β.range = alternatingGroup (Fin n) → n = 11)) ∧
      ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) := by
  by_cases h6 : n = 6
  · subst h6
    exact ⟨Or.inl ⟨rfl, ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 2 3 2
      (classicalModel_psl_two_three_two_of_alternating_six φ)⟩, fun h => absurd rfl h⟩
  obtain ⟨β, hinj, hβW, hAltT, hLsimple, hLalt, hxor, hcentL, hF5, hsum, ⟨eQ⟩⟩ :=
    socle_selector_permutation_data hCW ha hL hstd (by omega) φ
  obtain ⟨hTcases, hΔsym, hΔalt⟩ := socle_selector_support_card (by omega) hxor
  obtain ⟨h1, h2, h3⟩ := small_standard_source_alternating_degree_and_parameters_stated
    (Ω := {x // β a x = x}) (by rw [← Nat.card_eq_fintype_card]; exact hF5) ⟨eQ⟩
  simp only [← Nat.card_eq_fintype_card] at h1 h2
  have hpsl : ∀ p f : ℕ, p ≠ 2 → StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
      (Nat.card {x // β a x = x} = 5 ∧ p = 5 ∧ f = 1 ∧ (β.range = ⊤ → n = 7) ∧
          (β.range = alternatingGroup (Fin n) → n = 9)) ∨
        (Nat.card {x // β a x = x} = 6 ∧ p = 3 ∧ f = 2 ∧ (β.range = ⊤ → n = 8) ∧
          (β.range = alternatingGroup (Fin n) → n = 10)) := by
    intro p f hp2 hmodel
    rcases h1 p f hp2 hmodel with ⟨hF, hp, hf⟩ | ⟨hF, hp, hf⟩
    · exact Or.inl ⟨hF, hp, hf, fun hT => by have := hΔsym hT; omega,
        fun hT => by have := hΔalt hT; omega⟩
    · exact Or.inr ⟨hF, hp, hf, fun hT => by have := hΔsym hT; omega,
        fun hT => by have := hΔalt hT; omega⟩
  have halt7 : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
      Nat.card {x // β a x = x} = 7 ∧ (β.range = ⊤ → n = 9) ∧
        (β.range = alternatingGroup (Fin n) → n = 11) := by
    intro h7
    have hF := h2 h7
    exact ⟨hF, fun hT => by have := hΔsym hT; omega, fun hT => by have := hΔalt hT; omega⟩
  refine ⟨Or.inr ?_, fun _ => ⟨β, hinj, hβW, hAltT, hLsimple, hLalt, hxor, hcentL, hpsl, halt7,
    h3⟩⟩
  rcases hsource with ⟨p, f, hp2, hmodel⟩ | h7 | h322
  · rcases hpsl p f hp2 hmodel with ⟨-, -, -, hs, ha'⟩ | ⟨-, -, -, hs, ha'⟩ <;>
      rcases hTcases with hT | hT
    · have := hs hT; omega
    · have := ha' hT; omega
    · have := hs hT; omega
    · have := ha' hT; omega
  · obtain ⟨-, hs, ha'⟩ := halt7 h7
    rcases hTcases with hT | hT
    · have := hs hT; omega
    · have := ha' hT; omega
  · exact absurd h322 h3

theorem faithful_alternating_socle_small_standard_source_selector_of_psl_two_or_alt_seven_stated
    {A : Type} [Group A] [Finite A]
    {W : Subgroup A} [W.Normal] (_hWsimple : IsSimpleGroup W)
    (_hWnonab : ∃ x y : W, x * y ≠ y * x) (hCW : centralizer (W : Set A) = ⊥) {a : A}
    (ha : orderOf a = 2) {L : Subgroup A} (_hLW : L ≤ W)
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hsource : (∃ p f : ℕ, p ≠ 2 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f) ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)))
    {n : ℕ} (hn : 5 ≤ n) (φ : W ≃* alternatingGroup (Fin n)) :
    ((n = 6 ∧ StatedClassicalModel W .PSL 2 3 2) ∨ (7 ≤ n ∧ n ≤ 11)) ∧
    (n ≠ 6 → ∃ β : A →* Perm (Fin n), Function.Injective β ∧ (∀ w : W, β w = φ w) ∧
      alternatingGroup (Fin n) ≤ β.range ∧ IsSimpleGroup L ∧
      L.map β = (alternatingGroup {x // β a x = x}).map Perm.ofSubtype ∧
      Xor (β.range = ⊤ ∧ Nat.card {x // β a x ≠ x} = 2 ∧
          ∃ u v : Fin n, u ≠ v ∧ (∀ x, β a x ≠ x ↔ x = u ∨ x = v) ∧ β a = swap u v)
        (β.range = alternatingGroup (Fin n) ∧ Nat.card {x // β a x ≠ x} = 4 ∧
          ∃ u v w z : Fin n, u ≠ v ∧ u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ w ≠ z ∧
            (∀ x, β a x ≠ x ↔ x = u ∨ x = v ∨ x = w ∨ x = z) ∧ β a = swap u v * swap w z) ∧
      centralizer (L : Set A) =
        (β.range ⊓ (Perm.ofSubtype : Perm {x // β a x ≠ x} →* Perm (Fin n)).range).comap β ∧
      (∀ p f : ℕ, p ≠ 2 → StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
        (Nat.card {x // β a x = x} = 5 ∧ p = 5 ∧ f = 1 ∧ (β.range = ⊤ → n = 7) ∧
            (β.range = alternatingGroup (Fin n) → n = 9)) ∨
          (Nat.card {x // β a x = x} = 6 ∧ p = 3 ∧ f = 2 ∧ (β.range = ⊤ → n = 8) ∧
            (β.range = alternatingGroup (Fin n) → n = 10))) ∧
      (Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
        Nat.card {x // β a x = x} = 7 ∧ (β.range = ⊤ → n = 9) ∧
          (β.range = alternatingGroup (Fin n) → n = 11))) := by
  by_cases h6 : n = 6
  · subst h6
    exact ⟨Or.inl ⟨rfl, ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 2 3 2
      (classicalModel_psl_two_three_two_of_alternating_six φ)⟩, fun h => absurd rfl h⟩
  obtain ⟨β, hinj, hβW, hAltT, hLsimple, hLalt, hxor, hcentL, hF5, hsum, ⟨eQ⟩⟩ :=
    socle_selector_permutation_data hCW ha hL hstd (by omega) φ
  obtain ⟨hTcases, hΔsym, hΔalt⟩ := socle_selector_support_card (by omega) hxor
  obtain ⟨h1, h2⟩ := alternating_psl_two_parameters_and_degree_seven_stated
    (Ω := {x // β a x = x}) (by rw [← Nat.card_eq_fintype_card]; exact hF5) ⟨eQ⟩
  simp only [← Nat.card_eq_fintype_card] at h1 h2
  have hpsl : ∀ p f : ℕ, p ≠ 2 → StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
      (Nat.card {x // β a x = x} = 5 ∧ p = 5 ∧ f = 1 ∧ (β.range = ⊤ → n = 7) ∧
          (β.range = alternatingGroup (Fin n) → n = 9)) ∨
        (Nat.card {x // β a x = x} = 6 ∧ p = 3 ∧ f = 2 ∧ (β.range = ⊤ → n = 8) ∧
          (β.range = alternatingGroup (Fin n) → n = 10)) := by
    intro p f hp2 hmodel
    rcases h1 p f hp2 hmodel with ⟨hF, hp, hf⟩ | ⟨hF, hp, hf⟩
    · exact Or.inl ⟨hF, hp, hf, fun hT => by have := hΔsym hT; omega,
        fun hT => by have := hΔalt hT; omega⟩
    · exact Or.inr ⟨hF, hp, hf, fun hT => by have := hΔsym hT; omega,
        fun hT => by have := hΔalt hT; omega⟩
  have halt7 : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
      Nat.card {x // β a x = x} = 7 ∧ (β.range = ⊤ → n = 9) ∧
        (β.range = alternatingGroup (Fin n) → n = 11) := by
    intro h7
    have hF := h2 h7
    exact ⟨hF, fun hT => by have := hΔsym hT; omega, fun hT => by have := hΔalt hT; omega⟩
  refine ⟨Or.inr ?_, fun _ => ⟨β, hinj, hβW, hAltT, hLsimple, hLalt, hxor, hcentL, hpsl,
    halt7⟩⟩
  rcases hsource with ⟨p, f, hp2, hmodel⟩ | h7
  · rcases hpsl p f hp2 hmodel with ⟨-, -, -, hs, ha'⟩ | ⟨-, -, -, hs, ha'⟩ <;>
      rcases hTcases with hT | hT
    · have := hs hT; omega
    · have := ha' hT; omega
    · have := hs hT; omega
    · have := ha' hT; omega
  · obtain ⟨-, hs, ha'⟩ := halt7 h7
    rcases hTcases with hT | hT
    · have := hs hT; omega
    · have := ha' hT; omega

end CFSG.ComponentClassification.SymmetricLocal
