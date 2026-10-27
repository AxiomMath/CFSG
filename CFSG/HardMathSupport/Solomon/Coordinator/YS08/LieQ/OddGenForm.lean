module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGen
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddForm
public import CFSG.LieType.BorelTits.OrthogonalSingular

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut

section OneStep

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def oneStep (W : Submodule F V) : ℕ → Submodule F V := fun k => if k = 0 then ⊥ else W

theorem oneStep_zero (W : Submodule F V) : oneStep W 0 = ⊥ := by simp [oneStep]

theorem oneStep_succ (W : Submodule F V) (k : ℕ) : oneStep W (k + 1) = W := by simp [oneStep]

theorem oneStep_mono (W : Submodule F V) : Monotone (oneStep W) := by
  intro i j hij
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [oneStep_zero]; exact bot_le
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [oneStep_succ, oneStep_succ]

variable {H : Type} [Group H]

@[expose] def subspStab (ρ : H →* Module.End F V) (W : Submodule F V) : Subgroup H :=
  flagStab ρ (oneStep W)

theorem mem_subspStab {ρ : H →* Module.End F V} {W : Submodule F V} {h : H} :
    h ∈ subspStab ρ W ↔ ∀ v ∈ W, ρ h v ∈ W ∧ ρ h⁻¹ v ∈ W := by
  unfold subspStab
  rw [mem_flagStab]
  constructor
  · intro hh v hv
    simpa only [oneStep_succ] using hh 1 v (by simpa only [oneStep_succ] using hv)
  · intro hh k v hv
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [oneStep_zero, Submodule.mem_bot] at hv
      rw [hv, map_zero, map_zero, oneStep_zero]
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [oneStep_succ] at hv ⊢
      exact hh v hv

@[expose] noncomputable def formUrad (Φ : ReflForm F V) (ρ : H →* Module.End F V)
    (W : Submodule F V) : Subgroup H :=
  flagKernel ρ (isoCompletion Φ (oneStep W) 1)

variable (Φ : ReflForm F V) (ρ : H →* Module.End F V)

theorem subspStab_le_normalizer_formUrad (hiso : IsIsometric Φ ρ) (W : Submodule F V) :
    subspStab ρ W ≤ Subgroup.normalizer (formUrad Φ ρ W : Set H) := by
  refine le_trans ?_ (flagStab_le_normalizer_flagKernel ρ (isoCompletion Φ (oneStep W) 1))
  refine le_flagStab_isoCompletion ρ hiso 1 ?_
  intro h hh k v hv
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [oneStep_zero, Submodule.mem_bot] at hv
    rw [hv, map_zero, oneStep_zero]
    exact Submodule.zero_mem _
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [oneStep_succ] at hv ⊢
    exact (mem_subspStab.1 hh v hv).1

theorem formUrad_isPGroup {q : ℕ} [Fact q.Prime] [CharP F q] (hρ : Function.Injective ρ)
    (W : Submodule F V) : IsPGroup q (formUrad Φ ρ W) :=
  isPGroup_flagKernel ρ q hρ (isoCompletion_zero (oneStep_zero W) 1)
    (isoCompletion_top (oneStep_zero W) 1)

theorem eichler_mem_formUrad [Finite F] [Finite V] {W : Submodule F V} (hW : Φ.IsTotallyIsotropic W)
    {x y : V} (hx : x ∈ W) (hy : y ∈ Φ.perp W) {c ε : F} {g : H}
    (hg : ∀ v, ρ g v = v + Φ.β x v • (y + c • x) + (ε * Φ.β y v) • x) :
    g ∈ formUrad Φ ρ W := by
  refine mem_flagKernel_isoCompletion ρ (oneStep_mono W) (fun k => ?_) (Nat.lt_succ_self 0)
    (x := x) (y := y) (a := y + c • x) (by rw [oneStep_succ]; exact hx)
    (by rw [oneStep_succ]; exact hy) (by
      rw [oneStep_succ]
      exact add_mem hy (Submodule.smul_mem _ _ (hW hx))) ε hg
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [oneStep_zero]; exact bot_le
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [oneStep_succ]; exact hW

theorem mem_subspStab_of_forward [Finite V] {ρ : H →* Module.End F V} {W : Submodule F V} {h : H}
    (hfw : ∀ v ∈ W, ρ h v ∈ W) : h ∈ subspStab ρ W := by
  rw [mem_subspStab]
  intro v hv
  refine ⟨hfw v hv, ?_⟩
  have h2 : ∀ w : V, ρ h⁻¹ (ρ h w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinj : Function.Injective (fun w : W => (⟨ρ h w, hfw w w.2⟩ : W)) := by
    intro a b hab
    have : ρ h a = ρ h b := congrArg Subtype.val hab
    exact Subtype.ext (by rw [← h2 a, ← h2 b, this])
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨v, hv⟩
  have : ρ h w = v := congrArg Subtype.val hw
  rw [← this, h2]
  exact w.2

theorem exists_perp_not_perp (Φ : ReflForm F V) {x₁ x₂ : V} (hx₁ : x₁ ≠ 0)
    (hx₂ : x₂ ∉ Submodule.span F {x₁}) : ∃ y : V, Φ.β x₂ y = 0 ∧ Φ.β x₁ y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hx₂0 : x₂ ≠ 0 := fun h => hx₂ (h ▸ Submodule.zero_mem _)
  obtain ⟨v₂, hv₂⟩ : ∃ v, Φ.β x₂ v ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hx₂0 (Φ.nondeg x₂ h')
  set v₀ : V := (Φ.β x₂ v₂)⁻¹ • v₂ with hv₀
  have hv₀1 : Φ.β x₂ v₀ = 1 := by rw [hv₀, Φ.smul_right, inv_mul_cancel₀ hv₂]
  set c : F := Φ.β x₁ v₀ with hc
  have key : ∀ y, Φ.β x₁ y = c * Φ.β x₂ y := by
    intro y
    have h1 : Φ.β x₂ (y - Φ.β x₂ y • v₀) = 0 := by
      rw [Φ.β_sub_right, Φ.smul_right, hv₀1, mul_one, sub_self]
    have h2 := hcon _ h1
    rw [Φ.β_sub_right, Φ.smul_right] at h2
    rw [hc]
    linear_combination h2
  have hx₁eq : x₁ = (Φ.σ.symm c) • x₂ := by
    have : ∀ y, Φ.β (x₁ - (Φ.σ.symm c) • x₂) y = 0 := by
      intro y
      rw [Φ.β_sub_left, Φ.smul_left, RingEquiv.apply_symm_apply, key y, sub_self]
    exact sub_eq_zero.mp (Φ.nondeg _ this)
  have hc0 : Φ.σ.symm c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hx₁eq
    exact hx₁ hx₁eq
  apply hx₂
  have : x₂ = (Φ.σ.symm c)⁻¹ • x₁ := by
    rw [hx₁eq, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end OneStep

section Coatom

variable {G : Type} [Group G] [Finite G]

theorem isCoatom_of_overgroups {P₀ B : Subgroup G} (hBP : B ≤ P₀) (hP₀ : P₀ ≠ ⊤)
    (h : ∀ M : Subgroup G, IsCoatom M → B ≤ M → P₀ ≤ M → M = P₀) : IsCoatom P₀ := by
  obtain ⟨M, hM, hPM⟩ := (eq_top_or_exists_le_coatom P₀).resolve_left hP₀
  have := h M hM (hBP.trans hPM) hPM
  rw [this] at hM
  exact hM

theorem eq_of_le_of_index_eq {P₀ M : Subgroup G} (hle : P₀ ≤ M) (hidx : M.index = P₀.index) :
    P₀ = M := by
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := P₀.index_mul_card
  have h2 := M.index_mul_card
  rw [hidx] at h2
  have hpos : 0 < P₀.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have : Nat.card P₀ = Nat.card M := Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  exact this.ge

theorem index_le_of_le {P₀ M : Subgroup G} (hle : P₀ ≤ M) : M.index ≤ P₀.index :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le hle)

end Coatom

section Scalars

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem exists_smul_of_mem_scalars {H : Subgroup (GL ι F)} {g : H}
    (hg : g ∈ (StatedScalars ι F).subgroupOf H) : ∃ c : F, ∀ v, natRep H g v = c • v := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  refine ⟨(c : F), fun v => ?_⟩
  rw [natRep_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext x
  simp [Matrix.mulVec_diagonal]

end Scalars

section Generic

variable {F : Type} [Field F] [Finite F] {q : ℕ} [Fact q.Prime] [CharP F q]
  {V : Type} [AddCommGroup V] [Module F V] [Finite V] {H : Type} [Group H] [Finite H]

theorem exists_moving_elem (Φ : ReflForm F V) (ρ : H →* Module.End F V)
    (Z : Subgroup H) (hZsc : ∀ z ∈ Z, ∃ c : F, ∀ v, ρ z v = c • v)
    (ε : F) (hε : ε ≠ 0) (Sing : V → Prop) (hE : EA1ε Φ Sing ρ ε)
    {x₁ x₂ : V} (hx₁0 : x₁ ≠ 0) (hx₂ : Sing x₂) (h21 : Φ.β x₂ x₁ = 0)
    (hind : x₂ ∉ Submodule.span F {x₁}) :
    ∃ g' : H, (∀ W : Submodule F V, Φ.IsTotallyIsotropic W → x₂ ∈ W → g' ∈ subspStab ρ W) ∧
      ∀ s ∈ subspStab ρ (Submodule.span F {x₁}), ∀ z ∈ Z, g' ≠ s * z := by
  obtain ⟨y', hy'2, hy'1⟩ := exists_perp_not_perp Φ hx₁0 hind
  obtain ⟨c', g', hg'⟩ := hE x₂ y' hx₂ hy'2
  refine ⟨g', fun W hW hx₂W => ?_, ?_⟩
  · have hfw : ∀ v ∈ W, ρ g' v ∈ W := by
      intro v hv
      have hβ : Φ.β x₂ v = 0 := hW hv x₂ hx₂W
      rw [hg' v, hβ, zero_smul, add_zero]
      exact add_mem hv (Submodule.smul_mem _ _ hx₂W)
    exact mem_subspStab_of_forward hfw
  · intro s hs z hz hgsz
    obtain ⟨cz, hcz⟩ := hZsc z hz
    have hx₁W : x₁ ∈ Submodule.span F {x₁} := Submodule.mem_span_singleton_self x₁
    have h1 : ρ g' x₁ = cz • ρ s x₁ := by
      rw [hgsz, map_mul, Module.End.mul_apply, hcz, map_smul]
    have h2 : ρ g' x₁ = x₁ + (ε * Φ.β y' x₁) • x₂ := by
      rw [hg' x₁, h21, zero_smul, add_zero]
    have h3 : ρ s x₁ ∈ Submodule.span F {x₁} := (mem_subspStab.1 hs x₁ hx₁W).1
    have h4 : ρ g' x₁ ∈ Submodule.span F {x₁} := by
      rw [h1]
      exact Submodule.smul_mem _ _ h3
    rw [h2] at h4
    have hβ0 : Φ.β y' x₁ ≠ 0 := fun h0 => hy'1 (Φ.refl _ _ h0)
    have h5 : (ε * Φ.β y' x₁) • x₂ ∈ Submodule.span F {x₁} := by
      have := Submodule.sub_mem _ h4 hx₁W
      simpa using this
    apply hind
    have h6 := Submodule.smul_mem (Submodule.span F {x₁}) (ε * Φ.β y' x₁)⁻¹ h5
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hε hβ0), one_smul] at h6

theorem map_subspStab_ne_top (Φ : ReflForm F V) (ρ : H →* Module.End F V)
    (Z : Subgroup H) [Z.Normal] (hZsc : ∀ z ∈ Z, ∃ c : F, ∀ v, ρ z v = c • v)
    (ε : F) (hε : ε ≠ 0) (Sing : V → Prop) (hE : EA1ε Φ Sing ρ ε)
    {x₁ x₂ : V} (hx₁0 : x₁ ≠ 0) (hx₂ : Sing x₂) (h21 : Φ.β x₂ x₁ = 0)
    (hind : x₂ ∉ Submodule.span F {x₁}) :
    (subspStab ρ (Submodule.span F {x₁})).map (QuotientGroup.mk' Z) ≠ ⊤ := by
  intro htop
  obtain ⟨g', -, hg's⟩ := exists_moving_elem Φ ρ Z hZsc ε hε Sing hE hx₁0 hx₂ h21 hind
  have hmem : QuotientGroup.mk' Z g' ∈ (subspStab ρ (Submodule.span F {x₁})).map
      (QuotientGroup.mk' Z) := htop ▸ Subgroup.mem_top _
  obtain ⟨s, hs, hsg⟩ := hmem
  exact hg's s hs _ (QuotientGroup.eq.1 hsg) (by group)

theorem twoParabolics_of_form (Φ : ReflForm F V) (ρ : H →* Module.End F V)
    (hρ : Function.Injective ρ) (hiso : IsIsometric Φ ρ)
    (Z : Subgroup H) [Z.Normal] (hZsc : ∀ z ∈ Z, ∃ c : F, ∀ v, ρ z v = c • v)
    (ε : F) (hε : ε ≠ 0) (Sing : V → Prop) (hE : EA1ε Φ Sing ρ ε)
    {x₁ x₂ : V} (hx₁0 : x₁ ≠ 0) (hx₁ : Sing x₁) (hx₂ : Sing x₂)
    (h11 : Φ.β x₁ x₁ = 0) (h22 : Φ.β x₂ x₂ = 0) (h12 : Φ.β x₁ x₂ = 0)
    (hind : x₂ ∉ Submodule.span F {x₁})
    (U : Sylow q (H ⧸ Z)) {P₁ : Subgroup (H ⧸ Z)} (hc₁ : IsCoatom P₁)
    (hP₁ : P₁ ≤ (subspStab ρ (Submodule.span F {x₁})).map (QuotientGroup.mk' Z))
    (hU₁ : (U : Subgroup (H ⧸ Z)) ≤ P₁)
    (hU₂ : (U : Subgroup (H ⧸ Z)) ≤
      (subspStab ρ (Submodule.span F {x₁} ⊔ Submodule.span F {x₂})).map (QuotientGroup.mk' Z)) :
    TwoParabolics q (H ⧸ Z) := by
  classical
  have h21 : Φ.β x₂ x₁ = 0 := Φ.refl _ _ h12
  set W₁ : Submodule F V := Submodule.span F {x₁} with hW₁
  set W₂ : Submodule F V := Submodule.span F {x₁} ⊔ Submodule.span F {x₂} with hW₂
  have hx₁W₁ : x₁ ∈ W₁ := Submodule.mem_span_singleton_self x₁
  have hW₁iso : Φ.IsTotallyIsotropic W₁ :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (Φ.mem_perp_span_singleton.mpr h11)
  have hx₂perp₁ : x₂ ∈ Φ.perp W₁ := Φ.mem_perp_span_singleton.mpr h12
  have hW₂iso : Φ.IsTotallyIsotropic W₂ := hW₁iso.sup_span hx₂perp₁ h22
  have hx₁W₂ : x₁ ∈ W₂ := Submodule.mem_sup_left hx₁W₁
  have hx₂W₂ : x₂ ∈ W₂ := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x₂)
  obtain ⟨v₂, hv₂⟩ : ∃ v, Φ.β x₁ v ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hx₁0 (Φ.nondeg x₁ h')
  set v₀ : V := (Φ.β x₁ v₂)⁻¹ • v₂ with hv₀def
  have hv₀ : Φ.β x₁ v₀ = 1 := by rw [hv₀def, Φ.smul_right, inv_mul_cancel₀ hv₂]
  obtain ⟨c, g₀, hg₀⟩ := hE x₁ x₂ hx₁ h12
  have hg₀₁ : g₀ ∈ formUrad Φ ρ W₁ := eichler_mem_formUrad Φ ρ hW₁iso hx₁W₁ hx₂perp₁ hg₀
  have hg₀₂ : g₀ ∈ formUrad Φ ρ W₂ := eichler_mem_formUrad Φ ρ hW₂iso hx₁W₂ (hW₂iso hx₂W₂) hg₀
  have hnonsc : ¬ ∃ lam : F, ∀ v, ρ g₀ v = lam • v := by
    rintro ⟨lam, hlam⟩
    have h1 := hg₀ v₀
    rw [hlam v₀, hv₀, one_smul] at h1
    have h2 := congrArg (Φ.β x₁) h1
    simp only [Φ.smul_right, Φ.add_right, hv₀, h11, h12, mul_zero, add_zero, mul_one] at h2
    have hlam1 : lam = 1 := by linear_combination h2
    rw [hlam1, one_smul] at h1
    have h3 : x₂ + (c + ε * Φ.β x₂ v₀) • x₁ = 0 := by
      have h4 : v₀ + (x₂ + (c + ε * Φ.β x₂ v₀) • x₁) = v₀ + 0 := by
        rw [add_zero]
        rw [add_smul]
        calc v₀ + (x₂ + (c • x₁ + (ε * Φ.β x₂ v₀) • x₁)) = v₀ + (x₂ + c • x₁) + (ε * Φ.β x₂ v₀) • x₁ := by
              abel
          _ = v₀ := h1.symm
      exact add_left_cancel h4
    apply hind
    have : x₂ = -((c + ε * Φ.β x₂ v₀) • x₁) := eq_neg_of_add_eq_zero_left h3
    rw [this]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hx₁W₁)
  have hQne : ∀ W : Submodule F V, g₀ ∈ formUrad Φ ρ W →
      (formUrad Φ ρ W).map (QuotientGroup.mk' Z) ≠ ⊥ := by
    intro W hW hbot
    have h1 := (Subgroup.eq_bot_iff_forall _).1 hbot _ ⟨g₀, hW, rfl⟩
    have h2 : g₀ ∈ Z := (QuotientGroup.eq_one_iff g₀).1 h1
    exact hnonsc (hZsc g₀ h2)
  have hne : ¬ (subspStab ρ W₂).map (QuotientGroup.mk' Z) ≤ P₁ := by
    intro hle
    obtain ⟨g', hg'W, hg's⟩ := exists_moving_elem Φ ρ Z hZsc ε hε Sing hE hx₁0 hx₂ h21 hind
    have hg'W₂ : g' ∈ subspStab ρ W₂ := hg'W W₂ hW₂iso hx₂W₂
    obtain ⟨s, hs, hsg⟩ := hP₁ (hle ⟨g', hg'W₂, rfl⟩)
    exact hg's s hs _ (QuotientGroup.eq.1 hsg) (by group)
  refine ⟨U, P₁, (subspStab ρ W₂).map (QuotientGroup.mk' Z),
    (formUrad Φ ρ W₁).map (QuotientGroup.mk' Z), (formUrad Φ ρ W₂).map (QuotientGroup.mk' Z), hc₁,
    hne, hU₁, hU₂, hQne W₁ hg₀₁, (formUrad_isPGroup Φ ρ hρ W₁).map _,
    hP₁.trans ((Subgroup.map_mono (subspStab_le_normalizer_formUrad Φ ρ hiso W₁)).trans
      (Subgroup.le_normalizer_map _)), hQne W₂ hg₀₂, (formUrad_isPGroup Φ ρ hρ W₂).map _,
    (Subgroup.map_mono (subspStab_le_normalizer_formUrad Φ ρ hiso W₂)).trans
      (Subgroup.le_normalizer_map _)⟩

end Generic

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
