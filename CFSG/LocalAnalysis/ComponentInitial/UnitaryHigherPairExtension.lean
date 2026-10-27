module

public import CFSG.ClassicalGroups.UnitaryFlag.WittBasis

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem prependPair (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) {a b : V} (haa : B a a = 0) (hbb : B b b = 0)
    (hab : B a b = 1) {U : Submodule K V} (haU : ∀ x ∈ U, B a x = 0)
    (hbU : ∀ x ∈ U, B b x = 0) {r ε : ℕ} (hn : Module.finrank K V = 2 * (r + 1) + ε)
    (w' : Module.Basis (HypIndex r ε) K U) (hw' : ∀ x y, B (w' x) (w' y) = hypGram r ε K x y) :
    ∃ w : Module.Basis (HypIndex (r + 1) ε) K V,
      (∀ x y, B (w x) (w y) = hypGram (r + 1) ε K x y) ∧ w (.inl 0) = a ∧
      w (.inr (.inr 0)) = b ∧ (∀ j, w (.inl j.succ) = w' (.inl j)) ∧
      ∀ j, w (.inr (.inr j.succ)) = w' (.inr (.inr j)) := by
  have hba : B b a = 1 := by rw [← hB.eq a b, hab, map_one]
  have haU' : ∀ x : U, B a x = 0 := fun x => haU x x.2
  have hbU' : ∀ x : U, B b x = 0 := fun x => hbU x x.2
  have hUa : ∀ x : U, B x a = 0 := fun x => by rw [← hB.eq a x, haU', map_zero]
  have hUb : ∀ x : U, B x b = 0 := fun x => by rw [← hB.eq b x, hbU', map_zero]
  let v : HypIndex (r + 1) ε → V
    | .inl i => Fin.cases a (fun j => (w' (.inl j) : V)) i
    | .inr (.inl l) => (w' (.inr (.inl l)) : V)
    | .inr (.inr i) => Fin.cases b (fun j => (w' (.inr (.inr j)) : V)) i
  have hv : ∀ x y, B (v x) (v y) = hypGram (r + 1) ε K x y := by
    intro x y
    rcases x with i | l | i <;> rcases y with j | m | j <;>
      [cases i using Fin.cases <;> cases j using Fin.cases;
       cases i using Fin.cases;
       cases i using Fin.cases <;> cases j using Fin.cases;
       cases j using Fin.cases;
       skip;
       cases j using Fin.cases;
       cases i using Fin.cases <;> cases j using Fin.cases;
       cases i using Fin.cases;
       cases i using Fin.cases <;> cases j using Fin.cases] <;>
      simp [v, haa, hbb, hab, hba, haU', hbU', hUa, hUb, hw', Fin.succ_ne_zero,
        (Fin.succ_ne_zero _).symm]
  refine ⟨basisOfHypGram v hv hn, fun x y => by rw [coe_basisOfHypGram, hv], ?_, ?_,
    fun j => ?_, fun j => ?_⟩ <;> rw [coe_basisOfHypGram] <;> rfl

theorem hermitian_isotropic_pair_extension (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) {a₁ a₂ : V}
    (hli : LinearIndependent K ![a₁, a₂]) (h11 : B a₁ a₁ = 0) (h12 : B a₁ a₂ = 0)
    (h21 : B a₂ a₁ = 0) (h22 : B a₂ a₂ = 0) :
    ∃ b₁ b₂ : V, B a₁ b₁ = 1 ∧ B a₁ b₂ = 0 ∧ B a₂ b₁ = 0 ∧ B a₂ b₂ = 1 ∧ B b₁ b₁ = 0 ∧
      B b₁ b₂ = 0 ∧ B b₂ b₁ = 0 ∧ B b₂ b₂ = 0 ∧
      Module.finrank K (Submodule.span K {a₁, a₂, b₁, b₂}) = 4 ∧
      (B.domRestrict₁₂ (Submodule.span K {a₁, a₂, b₁, b₂})
        (Submodule.span K {a₁, a₂, b₁, b₂})).SeparatingLeft ∧
      IsCompl (Submodule.span K {a₁, a₂, b₁, b₂})
        ((Submodule.span K {a₁, a₂, b₁, b₂}).orthogonalBilin B) ∧
      (B.domRestrict₁₂ ((Submodule.span K {a₁, a₂, b₁, b₂}).orthogonalBilin B)
        ((Submodule.span K {a₁, a₂, b₁, b₂}).orthogonalBilin B)).SeparatingLeft ∧
      ∃ (r ε : ℕ) (_ : ε ≤ 1) (_ : Module.finrank K V = 2 * (r + 2) + ε)
        (w : Module.Basis (HypIndex (r + 2) ε) K V),
        (∀ x y, B (w x) (w y) = hypGram (r + 2) ε K x y) ∧ w (.inl 0) = a₁ ∧
        w (.inl 1) = a₂ ∧ w (.inr (.inr 0)) = b₁ ∧ w (.inr (.inr 1)) = b₂ := by
  classical
  rw [LinearIndependent.pair_iff] at hli
  have ha₁ : a₁ ≠ 0 := fun h0 => by
    have := hli 1 0 (by rw [h0]; simp)
    exact one_ne_zero this.1
  obtain ⟨⟨b, hab, hbb⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha₁ h11
  obtain ⟨-, -, -, hUsep, -⟩ := hsplit b hab hbb
  have hba : B b a₁ = 1 := by rw [← hB.eq a₁ b, hab, map_one]
  set U := (Submodule.span K {a₁, b}).orthogonalBilin B with hU
  set c := B b a₂ with hc
  have huU : a₂ - c • a₁ ∈ U := by
    rw [hU, Submodule.mem_orthogonalBilin]
    intro z hz
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
    simp [h11, h12, hba, ← hc]
  have hu0 : (⟨a₂ - c • a₁, huU⟩ : U) ≠ 0 := fun h0 => by
    have h0' : a₂ - c • a₁ = 0 := congrArg Subtype.val h0
    have := hli (-c) 1 (by rw [← h0']; module)
    exact one_ne_zero this.2
  have huu : B (a₂ - c • a₁) (a₂ - c • a₁) = 0 := by
    simp [h11, h12, h21, h22]
  obtain ⟨⟨b₂', hub₂, hb₂b₂⟩, -⟩ := hermitian_hyperbolic_splitting h (hB.domRestrict U) hUsep
    hu0 huu
  set b₂ : V := (b₂' : V) with hb₂def
  have hub₂' : B (a₂ - c • a₁) b₂ = 1 := hub₂
  have hb₂b₂' : B b₂ b₂ = 0 := hb₂b₂
  have ha₁b₂ : B a₁ b₂ = 0 :=
    (Submodule.mem_orthogonalBilin.mp b₂'.2) a₁ (Submodule.subset_span (by simp))
  have hbb₂ : B b b₂ = 0 :=
    (Submodule.mem_orthogonalBilin.mp b₂'.2) b (Submodule.subset_span (by simp))
  have hb₂a₁ : B b₂ a₁ = 0 := by rw [← hB.eq a₁ b₂, ha₁b₂, map_zero]
  have hb₂b : B b₂ b = 0 := by rw [← hB.eq b b₂, hbb₂, map_zero]
  have ha₂b₂ : B a₂ b₂ = 1 := by
    have : B a₂ b₂ = B (a₂ - c • a₁) b₂ + h.bar c * B a₁ b₂ := by
      simp [map_sub, map_smulₛₗ]
    rw [this, hub₂', ha₁b₂, mul_zero, add_zero]
  have ha₂b : B a₂ b = h.bar c := by rw [← hB.eq b a₂, ← hc]
  set b₁ : V := b - h.bar c • b₂ with hb₁def
  have ha₁b₁ : B a₁ b₁ = 1 := by simp [hb₁def, hab, ha₁b₂]
  have ha₂b₁ : B a₂ b₁ = 0 := by simp [hb₁def, ha₂b, ha₂b₂]
  have hb₁b₁ : B b₁ b₁ = 0 := by simp [hb₁def, hbb, hbb₂, hb₂b, hb₂b₂']
  have hb₁b₂ : B b₁ b₂ = 0 := by simp [hb₁def, hbb₂, hb₂b₂']
  have hb₂b₁ : B b₂ b₁ = 0 := by rw [← hB.eq b₁ b₂, hb₁b₂, map_zero]
  obtain ⟨⟨-, -⟩, hsplit₁⟩ := hermitian_hyperbolic_splitting h hB hBl ha₁ h11
  obtain ⟨hH₁, -, -, hU₁sep, hU₁dim⟩ := hsplit₁ b₁ ha₁b₁ hb₁b₁
  set U₁ := (Submodule.span K {a₁, b₁}).orthogonalBilin B with hU₁
  have hmemU₁ : ∀ x, B a₁ x = 0 → B b₁ x = 0 → x ∈ U₁ := fun x hx1 hx2 => by
    rw [hU₁, Submodule.mem_orthogonalBilin]
    intro z hz
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
    simp [hx1, hx2]
  have hb₁a₂ : B b₁ a₂ = 0 := by rw [← hB.eq a₂ b₁, ha₂b₁, map_zero]
  have ha₂U₁ := hmemU₁ a₂ h12 hb₁a₂
  have hb₂U₁ := hmemU₁ b₂ ha₁b₂ hb₁b₂
  have ha₂0 : (⟨a₂, ha₂U₁⟩ : U₁) ≠ 0 := fun h0 => by
    have h0' : a₂ = 0 := congrArg Subtype.val h0
    have := hli 0 1 (by rw [h0']; simp)
    exact one_ne_zero this.2
  obtain ⟨-, hsplitU₁⟩ := hermitian_hyperbolic_splitting h (hB.domRestrict U₁) hU₁sep ha₂0 h22
  obtain ⟨hH₂, -⟩ := hsplitU₁ ⟨b₂, hb₂U₁⟩ ha₂b₂ hb₂b₂'
  have h2U₁ : 2 ≤ Module.finrank K U₁ := hH₂ ▸ Submodule.finrank_le _
  have h2V : 2 ≤ Module.finrank K V := hH₁ ▸ Submodule.finrank_le _
  obtain ⟨r, ε, hε1, hdimU₁⟩ : ∃ r ε, ε ≤ 1 ∧ Module.finrank K U₁ = 2 * (r + 1) + ε :=
    ⟨Module.finrank K U₁ / 2 - 1, Module.finrank K U₁ % 2, by omega, by omega⟩
  obtain ⟨w', hw', hw'a, hw'b⟩ := exists_hypBasis_of_pair h (hB.domRestrict U₁) hU₁sep hdimU₁
    (Nat.succ_pos r) (a := ⟨a₂, ha₂U₁⟩) (b := ⟨b₂, hb₂U₁⟩) h22 hb₂b₂' ha₂b₂
  have hw'' : ∀ x y, B (w' x) (w' y) = hypGram (r + 1) ε K x y := fun x y => by
    rw [← hw' x y, LinearMap.domRestrict₁₂_apply]
  have hdimV : Module.finrank K V = 2 * (r + 1 + 1) + ε := by omega
  have ha₁U₁ : ∀ x ∈ U₁, B a₁ x = 0 := fun x hx =>
    (Submodule.mem_orthogonalBilin.mp hx) a₁ (Submodule.subset_span (by simp))
  have hb₁U₁ : ∀ x ∈ U₁, B b₁ x = 0 := fun x hx =>
    (Submodule.mem_orthogonalBilin.mp hx) b₁ (Submodule.subset_span (by simp))
  obtain ⟨w, hw, hwa, hwb, hwa', hwb'⟩ :=
    prependPair h hB h11 hb₁b₁ ha₁b₁ ha₁U₁ hb₁U₁ hdimV w' hw''
  have hwa₂ : w (.inl 1) = a₂ := by
    rw [← Fin.succ_zero_eq_one, hwa' 0]
    exact congrArg Subtype.val hw'a
  have hwb₂ : w (.inr (.inr 1)) = b₂ := by
    rw [← Fin.succ_zero_eq_one, hwb' 0]
    exact congrArg Subtype.val hw'b
  set H := Submodule.span K {a₁, a₂, b₁, b₂} with hH
  have hgen : ∀ x : HypIndex (r + 1 + 1) ε, x ≠ .inl 0 → x ≠ .inl 1 → x ≠ .inr (.inr 0) →
      x ≠ .inr (.inr 1) → B a₁ (w x) = 0 ∧ B a₂ (w x) = 0 ∧ B b₁ (w x) = 0 ∧
        B b₂ (w x) = 0 := by
    intro x h1 h2 h3 h4
    rw [← hwa, ← hwa₂, ← hwb, ← hwb₂, hw, hw, hw, hw]
    simp only [hypGram_apply, hypPartner_inl, hypPartner_inr_inr, h1, h2, h3, h4, ↓reduceIte,
      and_self]
  have horth : ∀ x : HypIndex (r + 1 + 1) ε, x ≠ .inl 0 → x ≠ .inl 1 →
      x ≠ .inr (.inr 0) → x ≠ .inr (.inr 1) → w x ∈ H.orthogonalBilin B := by
    intro x h1 h2 h3 h4
    obtain ⟨g1, g2, g3, g4⟩ := hgen x h1 h2 h3 h4
    rw [Submodule.mem_orthogonalBilin]
    intro z hz
    have hle : H ≤ LinearMap.ker (B.flip (w x)) := by
      rw [hH, Submodule.span_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> simpa
    exact hle hz
  have hmemH : ∀ x : HypIndex (r + 1 + 1) ε, x = .inl 0 ∨ x = .inl 1 ∨ x = .inr (.inr 0) ∨
      x = .inr (.inr 1) → w x ∈ H := by
    rintro x (rfl | rfl | rfl | rfl)
    · rw [hwa]; exact Submodule.subset_span (by simp)
    · rw [hwa₂]; exact Submodule.subset_span (by simp)
    · rw [hwb]; exact Submodule.subset_span (by simp)
    · rw [hwb₂]; exact Submodule.subset_span (by simp)
  have htop : H ⊔ H.orthogonalBilin B = ⊤ := by
    rw [eq_top_iff, ← w.span_eq, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    by_cases hx : x = .inl 0 ∨ x = .inl 1 ∨ x = .inr (.inr 0) ∨ x = .inr (.inr 1)
    · exact Submodule.mem_sup_left (hmemH x hx)
    · push Not at hx
      exact Submodule.mem_sup_right (horth x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2)
  have hsep : ∀ v : V, (∀ z ∈ H, B v z = 0) → (∀ z ∈ H.orthogonalBilin B, B v z = 0) →
      v = 0 := fun v hv1 hv2 => by
    refine hBl v fun z => ?_
    have hz : z ∈ H ⊔ H.orthogonalBilin B := by rw [htop]; trivial
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add, hv1 z₁ hz₁, hv2 z₂ hz₂, add_zero]
  have hHH : ∀ v ∈ H, ∀ z ∈ H.orthogonalBilin B, B v z = 0 := fun v hv z hz =>
    (Submodule.mem_orthogonalBilin.mp hz) v hv
  have hHH' : ∀ v ∈ H.orthogonalBilin B, ∀ z ∈ H, B v z = 0 := fun v hv z hz => by
    rw [← hB.eq z v, (Submodule.mem_orthogonalBilin.mp hv) z hz, map_zero]
  have hdisj : H ⊓ H.orthogonalBilin B = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    exact (Submodule.mem_bot K).mpr (hsep v (fun z hz => hHH' v hv2 z hz)
      (fun z hz => hHH v hv1 z hz))
  have hfin : Module.finrank K H = 4 := by
    let ι : Fin 4 → HypIndex (r + 1 + 1) ε := ![.inl 0, .inl 1, .inr (.inr 0), .inr (.inr 1)]
    have hι : Function.Injective ι := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [ι] at hij ⊢
    have hli4 := w.linearIndependent.comp ι hι
    have hrange : Set.range (⇑w ∘ ι) = {a₁, a₂, b₁, b₂} := by
      rw [Set.range_comp]
      ext v
      simp only [Set.mem_image, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        fin_cases i <;> simp [ι, hwa, hwa₂, hwb, hwb₂]
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨_, ⟨0, rfl⟩, hwa⟩
        · exact ⟨_, ⟨1, rfl⟩, hwa₂⟩
        · exact ⟨_, ⟨2, rfl⟩, hwb⟩
        · exact ⟨_, ⟨3, rfl⟩, hwb₂⟩
    rw [hH, ← hrange, finrank_span_eq_card hli4, Fintype.card_fin]
  refine ⟨b₁, b₂, ha₁b₁, ha₁b₂, ha₂b₁, ha₂b₂, hb₁b₁, hb₁b₂, hb₂b₁, hb₂b₂', hfin, ?_, ?_, ?_,
    r, ε, hε1, by omega, w, hw, hwa, hwa₂, hwb, hwb₂⟩
  · intro v hv
    refine Subtype.ext (hsep v (fun z hz => hv ⟨z, hz⟩) fun z hz => hHH v v.2 z hz)
  · exact ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr htop⟩
  · intro v hv
    refine Subtype.ext (hsep v (fun z hz => hHH' v v.2 z hz) fun z hz => hv ⟨z, hz⟩)

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
