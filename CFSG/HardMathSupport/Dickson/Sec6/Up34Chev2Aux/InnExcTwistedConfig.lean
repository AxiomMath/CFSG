module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedBad
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryBasic
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.LargeExtraspecial.AS35WSp4Gen
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLang

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley CFSG.RankThree.Classical CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.ClassicalInvolution.ModelFacts.Levi

namespace Up34Chev2

section SL2Basic

variable {K : Type} [Field K] [CharP K 2]

theorem sl2_eq_one_of_forall_comm {A : SL2 K} (hA : ∀ B : SL2 K, A * B = B * A) : A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1
    (Subgroup.mem_center_iff.2 fun B => (hA B).symm)
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have : (r - 1) ^ 2 = 0 := by linear_combination hr - r * h2 + h2
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linear_combination this
  subst hr1
  exact Subtype.ext (by rw [← hrA]; simp)

end SL2Basic

section Centerless

theorem centerless_range {G H : Type*} [Group G] [Group H] (ψ : G →* H)
    (hψ : Function.Injective ψ) (hG : ∀ a : G, (∀ b, a * b = b * a) → a = 1) :
    ∀ a ∈ ψ.range, (∀ b ∈ ψ.range, a * b = b * a) → a = 1 := by
  rintro _ ⟨x, rfl⟩ h
  have : x = 1 := hG x fun b => hψ (by rw [map_mul, map_mul]; exact h _ ⟨b, rfl⟩)
  rw [this, map_one]

theorem card_range_of_injective {G H : Type*} [Group G] [Group H] (ψ : G →* H)
    (hψ : Function.Injective ψ) : Nat.card ψ.range = Nat.card G :=
  (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm

end Centerless

section Homs

variable {τ : Tag} {L : Type} [Field L]

theorem sl2_map_map {R S T : Type} [Field R] [Field S] [Field T] (f : R →+* S) (g : S →+* T)
    (A : SL2 R) :
    Matrix.SpecialLinearGroup.map g (Matrix.SpecialLinearGroup.map f A) =
      Matrix.SpecialLinearGroup.map (g.comp f) A := by
  apply Subtype.ext
  ext i j
  simp

theorem sl2_map_injective {R S : Type} [Field R] [Field S] (f : R →+* S) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have := congrArg (fun M : SL2 S => (M : Matrix (Fin 2) (Fin 2) S) i j) h
  simpa using f.injective this

@[expose] noncomputable def slHom (β : Fin τ.rank → ℤ) (φ : L →+* L) (K : Subfield L) :
    SL2 K →* ModGL τ L :=
  (rootSL2 τ L β).comp (Matrix.SpecialLinearGroup.map (φ.comp K.subtype))

theorem slHom_apply (β : Fin τ.rank → ℤ) (φ : L →+* L) (K : Subfield L) (A : SL2 K) :
    slHom β φ K A = rootSL2 τ L β (Matrix.SpecialLinearGroup.map (φ.comp K.subtype) A) := rfl

theorem slHom_injective (β : Fin τ.rank → ℤ) (φ : L →+* L) (K : Subfield L) :
    Function.Injective (slHom (τ := τ) β φ K) :=
  (rootSL2_injective_of_field (τ := τ) (K := L) β).comp (sl2_map_injective _)

theorem F_slHom {F₁ : ModGL τ L →* ModGL τ L} {β β' : Fin τ.rank → ℤ} (Fr : L →+* L)
    (hF : ∀ B : SL2 L, F₁ (rootSL2 τ L β B) =
      rootSL2 τ L β' (Matrix.SpecialLinearGroup.map Fr B))
    (φ : L →+* L) (K : Subfield L) (A : SL2 K) :
    F₁ (slHom β φ K A) = slHom β' (Fr.comp φ) K A := by
  rw [slHom_apply, hF, slHom_apply, sl2_map_map, RingHom.comp_assoc]

@[expose] def mulHom {G H : Type*} [Group G] [Group H] (f g : G →* H)
    (h : ∀ x y, Commute (f x) (g y)) : G →* H :=
  (MonoidHom.noncommCoprod f g h).comp (MonoidHom.prod (MonoidHom.id G) (MonoidHom.id G))

theorem mulHom_apply {G H : Type*} [Group G] [Group H] (f g : G →* H)
    (h : ∀ x y, Commute (f x) (g y)) (x : G) : mulHom f g h x = f x * g x := rfl

end Homs

section Frob

variable {L : Type} [Field L] [CharP L 2]

theorem frob_fixed_one {f : ℕ} {c : L} (hc : c ∈ frobeniusFixedField L 2 f) :
    iterateFrobenius L 2 f c = c := by
  rw [iterateFrobenius_def]
  exact mem_frobeniusFixedField.1 hc

theorem frob_fixed_two {f : ℕ} {c : L} (hc : c ∈ frobeniusFixedField L 2 (2 * f)) :
    iterateFrobenius L 2 f (iterateFrobenius L 2 f c) = c := by
  rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add]
  have := mem_frobeniusFixedField.1 hc
  rwa [show 2 * f = f + f by ring] at this

theorem frob_fixed_three {f : ℕ} {c : L} (hc : c ∈ frobeniusFixedField L 2 (3 * f)) :
    iterateFrobenius L 2 f (iterateFrobenius L 2 f (iterateFrobenius L 2 f c)) = c := by
  rw [iterateFrobenius_def, iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_mul,
    ← pow_add, ← pow_add]
  have := mem_frobeniusFixedField.1 hc
  rwa [show 3 * f = f + (f + f) by ring] at this

theorem frob_comp_subtype_one (f : ℕ) :
    (iterateFrobenius L 2 f).comp (frobeniusFixedField L 2 f).subtype =
      (frobeniusFixedField L 2 f).subtype := by
  ext c
  exact frob_fixed_one c.2

theorem frob_comp_subtype_two (f : ℕ) :
    (iterateFrobenius L 2 f).comp ((iterateFrobenius L 2 f).comp
      (frobeniusFixedField L 2 (2 * f)).subtype) = (frobeniusFixedField L 2 (2 * f)).subtype := by
  ext c
  exact frob_fixed_two c.2

theorem frob_comp_subtype_three (f : ℕ) :
    (iterateFrobenius L 2 f).comp ((iterateFrobenius L 2 f).comp ((iterateFrobenius L 2 f).comp
      (frobeniusFixedField L 2 (3 * f)).subtype)) = (frobeniusFixedField L 2 (3 * f)).subtype := by
  ext c
  exact frob_fixed_three c.2

instance charP_frobeniusFixedField (n : ℕ) : CharP (frobeniusFixedField L 2 n) 2 :=
  RingHom.charP (frobeniusFixedField L 2 n).subtype Subtype.val_injective 2

end Frob

section Config

variable {τ : Tag}

structure D4Cfg (τ : Tag) (βa βb βk βc : Fin τ.rank → ℤ) : Prop where
  ra : IsRoot τ βa
  rb : IsRoot τ βb
  rk : IsRoot τ βk
  rc : IsRoot τ βc
  ab : iform βa βb = 0
  ak : iform βa βk = 0
  bk : iform βb βk = 0
  ca : iform βc βa = -1
  cb : iform βc βb = -1
  ck : iform βc βk = -1

@[expose] noncomputable def wD4 (βa βb βk βc : Fin τ.rank → ℤ) : WeylGroup τ :=
  rootReflection βc * rootReflection βa * rootReflection βb * rootReflection βk

theorem reflect_apply (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) : rootReflection β • v = v - iform β v • β := by
  rw [rootReflection_smul hβ]
  have h2 := corootPair_mul hβ v
  rw [CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hβ] at h2
  have : corootPair β v = iform β v := by linarith
  rw [this]

theorem wD4_smul (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {βa βb βk βc : Fin τ.rank → ℤ}
    (cfg : D4Cfg τ βa βb βk βc) :
    wD4 βa βb βk βc • βc = βa + βb + βk + (2 : ℤ) • βc := by
  have e1 : rootReflection βk • βc = βc + βk := by
    rw [reflect_apply hτ cfg.rk, iform_comm βk βc, cfg.ck]
    simp
  have e2 : rootReflection βb • (βc + βk) = βc + βk + βb := by
    rw [reflect_apply hτ cfg.rb, iform_add_right, iform_comm βb βc, cfg.cb, cfg.bk]
    simp
  have e3 : rootReflection βa • (βc + βk + βb) = βc + βk + βb + βa := by
    rw [reflect_apply hτ cfg.ra, iform_add_right, iform_add_right, iform_comm βa βc, cfg.ca,
      cfg.ak, cfg.ab]
    simp
  have e4 : rootReflection βc • (βc + βk + βb + βa) = βa + βb + βk + (2 : ℤ) • βc := by
    rw [reflect_apply hτ cfg.rc, iform_add_right, iform_add_right, iform_add_right,
      CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ cfg.rc, cfg.ck, cfg.cb, cfg.ca]
    have h : (2 + -1 + -1 + -1 : ℤ) = -1 := by norm_num
    rw [h, neg_smul, one_smul, sub_neg_eq_add, two_smul]
    abel
  unfold wD4
  simp only [mul_smul]
  rw [e1, e2, e3, e4]

theorem commute_rootSL2_of_iform_zero {L : Type} [Field L]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (h0 : iform α β = 0) (A B : SL2 L) :
    Commute (rootSL2 τ L α A) (rootSL2 τ L β B) := by
  have h4 : ∀ x : Fin τ.rank → ℤ, IsRoot τ x → iform x x = 2 := fun x hx =>
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hx
  have hp : ¬ IsRoot τ (α + β) := fun hr => by
    have := h4 _ hr
    rw [iform_add_left, iform_add_right, iform_add_right, h4 _ hα, h4 _ hβ, h0, iform_comm,
      h0] at this
    omega
  have hm : ¬ IsRoot τ (α - β) := fun hr => by
    have := h4 _ hr
    rw [iform_sub_left, iform_sub_right, iform_sub_right, h4 _ hα, h4 _ hβ, h0, iform_comm,
      h0] at this
    omega
  exact rootSL2_commute_of_orth hα hβ h0 hp hm A B

section Weyl

variable {L : Type} [Field L] {βa βb βk βc : Fin τ.rank → ℤ}

@[expose] noncomputable def nD4 (L : Type) [Field L] (βa βb βk βc : Fin τ.rank → ℤ) :
    ModGL τ L :=
  rootSL2 τ L βc WSL * rootSL2 τ L βa WSL * rootSL2 τ L βb WSL * rootSL2 τ L βk WSL

@[expose] noncomputable def cfgGroup (τ : Tag) (L : Type) [Field L]
    (βa βb βk βc : Fin τ.rank → ℤ) : Subgroup (ModGL τ L) :=
  (rootSL2 τ L βa).range ⊔ (rootSL2 τ L βb).range ⊔ (rootSL2 τ L βk).range ⊔
    (rootSL2 τ L βc).range

theorem rootSL2_mem_cfgGroup_a (A : SL2 L) : rootSL2 τ L βa A ∈ cfgGroup τ L βa βb βk βc :=
  (le_sup_left.trans (le_sup_left.trans le_sup_left) : (rootSL2 τ L βa).range ≤ _) ⟨A, rfl⟩

theorem rootSL2_mem_cfgGroup_b (A : SL2 L) : rootSL2 τ L βb A ∈ cfgGroup τ L βa βb βk βc :=
  (le_sup_right.trans (le_sup_left.trans le_sup_left) : (rootSL2 τ L βb).range ≤ _) ⟨A, rfl⟩

theorem rootSL2_mem_cfgGroup_k (A : SL2 L) : rootSL2 τ L βk A ∈ cfgGroup τ L βa βb βk βc :=
  (le_sup_right.trans le_sup_left : (rootSL2 τ L βk).range ≤ _) ⟨A, rfl⟩

theorem rootSL2_mem_cfgGroup_c (A : SL2 L) : rootSL2 τ L βc A ∈ cfgGroup τ L βa βb βk βc :=
  (le_sup_right : (rootSL2 τ L βc).range ≤ _) ⟨A, rfl⟩

theorem nD4_mem_monomialSubgroup (cfg : D4Cfg τ βa βb βk βc) :
    nD4 L βa βb βk βc ∈ monomialSubgroup τ L :=
  mul_mem (mul_mem (mul_mem (rootSL2_WSL_mem_monomialSubgroup cfg.rc)
    (rootSL2_WSL_mem_monomialSubgroup cfg.ra)) (rootSL2_WSL_mem_monomialSubgroup cfg.rb))
    (rootSL2_WSL_mem_monomialSubgroup cfg.rk)

theorem nD4_mapsRootLines (cfg : D4Cfg τ βa βb βk βc) :
    MapsRootLines (nD4 L βa βb βk βc) (wD4 βa βb βk βc) :=
  (((mapsRootLines_rootSL2_WSL cfg.rc).mul (mapsRootLines_rootSL2_WSL cfg.ra)).mul
    (mapsRootLines_rootSL2_WSL cfg.rb)).mul (mapsRootLines_rootSL2_WSL cfg.rk)

end Weyl

section Theta

variable {L : Type} [Field L] [CharP L 2] {βa βb βk βc : Fin τ.rank → ℤ}

theorem slHom_frob_one (β : Fin τ.rank → ℤ) (f : ℕ) (A : SL2 (frobeniusFixedField L 2 f)) :
    slHom β (iterateFrobenius L 2 f) (frobeniusFixedField L 2 f) A =
      slHom β (RingHom.id L) (frobeniusFixedField L 2 f) A := by
  rw [slHom_apply, slHom_apply, frob_comp_subtype_one, RingHom.id_comp]

theorem card_sl2_frobFixed [IsAlgClosed L] {m : ℕ} (hm : 0 < m) :
    Nat.card (SL2 (frobeniusFixedField L 2 m)) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  have hc : Nat.card (frobeniusFixedField L 2 m) = 2 ^ m := card_frobeniusFixedField hm
  haveI : Finite (frobeniusFixedField L 2 m) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  rw [CFSG.LargeExtraspecial.AS35W.card_SL2, hc]

theorem iform_theta_zero (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (cfg : D4Cfg τ βa βb βk βc) {x : Fin τ.rank → ℤ}
    (hx : x = βa ∨ x = βb ∨ x = βk) : iform (wD4 βa βb βk βc • βc) x = 0 := by
  rw [wD4_smul hτ cfg]
  have h2 : ∀ y, IsRoot τ y → iform y y = 2 := fun y hy =>
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hy
  rcases hx with rfl | rfl | rfl
  · rw [iform_add_left, iform_add_left, iform_add_left, iform_smul_left, h2 _ cfg.ra,
      iform_comm βb x, cfg.ab, iform_comm βk x, cfg.ak, cfg.ca]
    norm_num
  · rw [iform_add_left, iform_add_left, iform_add_left, iform_smul_left, h2 _ cfg.rb,
      cfg.ab, iform_comm βk x, cfg.bk, cfg.cb]
    norm_num
  · rw [iform_add_left, iform_add_left, iform_add_left, iform_smul_left, h2 _ cfg.rk,
      cfg.ak, cfg.bk, cfg.ck]
    norm_num

theorem exists_theta_factor [IsAlgClosed L] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f) (cfg : D4Cfg τ βa βb βk βc) (F₁ : ModGL τ L →* ModGL τ L)
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFn : F₁ (nD4 L βa βb βk βc) = nD4 L βa βb βk βc) (C : Subgroup (ModGL τ L))
    (hnC : nD4 L βa βb βk βc ∈ C)
    (hXC : (slHom βc (RingHom.id L) (frobeniusFixedField L 2 f)).range ≤ C) :
    ∃ X : Subgroup (ModGL τ L),
      (∀ g ∈ X, F₁ g = g) ∧ (∀ g ∈ X, g ∈ C) ∧
      (∀ a ∈ X, (∀ b ∈ X, a * b = b * a) → a = 1) ∧
      Nat.card X = 2 ^ f * ((2 ^ f) ^ 2 - 1) ∧
      (∀ g ∈ X, ∀ B : SL2 L, g * rootSL2 τ L βa B = rootSL2 τ L βa B * g) ∧
      (∀ g ∈ X, ∀ B : SL2 L, g * rootSL2 τ L βb B = rootSL2 τ L βb B * g) ∧
      (∀ g ∈ X, ∀ B : SL2 L, g * rootSL2 τ L βk B = rootSL2 τ L βk B * g) := by
  classical
  set nW := nD4 L βa βb βk βc with hnW
  have hn : nW ∈ monomialSubgroup τ L := nD4_mem_monomialSubgroup cfg
  have hw : MapsRootLines nW (wD4 βa βb βk βc) := nD4_mapsRootLines cfg
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq hn hw cfg.rc
    (rfl : wD4 βa βb βk βc • βc = wD4 βa βb βk βc • βc)
  have hθ : IsRoot τ (wD4 βa βb βk βc • βc) := IsRoot.smul cfg.rc _
  set K₁ := frobeniusFixedField L 2 f with hK₁
  let Xc : Subgroup (ModGL τ L) := (slHom βc (RingHom.id L) K₁).range
  have hXc : ∀ g ∈ Xc, ∃ A : SL2 K₁, slHom βc (RingHom.id L) K₁ A = g := fun g hg => hg
  have hinj : Function.Injective (slHom (τ := τ) βc (RingHom.id L) K₁) := slHom_injective _ _ _
  have hconj : ∀ g ∈ Xc.map (MulAut.conj nW).toMonoidHom, ∃ A : SL2 K₁,
      g = nW * slHom βc (RingHom.id L) K₁ A * nW⁻¹ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨A, rfl⟩ := hXc x hx
    exact ⟨A, rfl⟩
  refine ⟨Xc.map (MulAut.conj nW).toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨A, rfl⟩ := hconj g hg
    rw [map_mul, map_mul, map_inv, hFn, F_slHom _ hFc, RingHom.comp_id, slHom_frob_one]
  · intro g hg
    obtain ⟨A, rfl⟩ := hconj g hg
    exact mul_mem (mul_mem hnC (hXC ⟨A, rfl⟩)) (inv_mem hnC)
  · exact centerless_map_conj nW (centerless_range _ hinj fun A hA => sl2_eq_one_of_forall_comm hA)
  · rw [Subgroup.card_map_of_injective (MulAut.conj nW).injective, card_range_of_injective _ hinj,
      card_sl2_frobFixed (by omega)]
  · intro g hg B
    obtain ⟨A, rfl⟩ := hconj g hg
    have h1 := hs (Matrix.SpecialLinearGroup.map ((RingHom.id L).comp K₁.subtype) A)
    have h2 : nW * slHom βc (RingHom.id L) K₁ A * nW⁻¹ =
        rootSL2 τ L (wD4 βa βb βk βc • βc)
          (conjSL (diagUnitOne s) (Matrix.SpecialLinearGroup.map ((RingHom.id L).comp K₁.subtype) A)) :=
      h1
    rw [h2]
    exact (commute_rootSL2_of_iform_zero hτ hθ cfg.ra (iform_theta_zero hτ cfg (Or.inl rfl))
      _ B).eq
  · intro g hg B
    obtain ⟨A, rfl⟩ := hconj g hg
    have h1 := hs (Matrix.SpecialLinearGroup.map ((RingHom.id L).comp K₁.subtype) A)
    have h2 : nW * slHom βc (RingHom.id L) K₁ A * nW⁻¹ =
        rootSL2 τ L (wD4 βa βb βk βc • βc)
          (conjSL (diagUnitOne s) (Matrix.SpecialLinearGroup.map ((RingHom.id L).comp K₁.subtype) A)) :=
      h1
    rw [h2]
    exact (commute_rootSL2_of_iform_zero hτ hθ cfg.rb (iform_theta_zero hτ cfg (Or.inr (Or.inl rfl)))
      _ B).eq
  · intro g hg B
    obtain ⟨A, rfl⟩ := hconj g hg
    have h1 := hs (Matrix.SpecialLinearGroup.map ((RingHom.id L).comp K₁.subtype) A)
    have h2 : nW * slHom βc (RingHom.id L) K₁ A * nW⁻¹ =
        rootSL2 τ L (wD4 βa βb βk βc • βc)
          (conjSL (diagUnitOne s) (Matrix.SpecialLinearGroup.map ((RingHom.id L).comp K₁.subtype) A)) :=
      h1
    rw [h2]
    exact (commute_rootSL2_of_iform_zero hτ hθ cfg.rk (iform_theta_zero hτ cfg (Or.inr (Or.inr rfl)))
      _ B).eq

end Theta

section Arith

theorem not_dvd_swap {f : ℕ} (hf : 1 ≤ f) :
    ¬ ((2 ^ f) ^ 2 * (((2 ^ f) ^ 2) ^ 2 - 1) * ((2 ^ f) * ((2 ^ f) ^ 2 - 1)) *
      ((2 ^ f) * ((2 ^ f) ^ 2 - 1)) ∣ 20160) := by
  intro h
  rcases Nat.lt_or_ge f 2 with h1 | h1
  · obtain rfl : f = 1 := by omega
    revert h
    decide
  · have hQ : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h1
    generalize 2 ^ f = Q at hQ h
    have hle := Nat.le_of_dvd (by norm_num) h
    have ha : 4080 ≤ Q ^ 2 * ((Q ^ 2) ^ 2 - 1) := by
      have h16 : 16 ≤ Q ^ 2 := by nlinarith
      have h255 : 255 ≤ (Q ^ 2) ^ 2 - 1 := by
        have : 256 ≤ (Q ^ 2) ^ 2 := by nlinarith
        omega
      calc 4080 = 16 * 255 := by norm_num
        _ ≤ Q ^ 2 * ((Q ^ 2) ^ 2 - 1) := Nat.mul_le_mul h16 h255
    have hb : 60 ≤ Q * (Q ^ 2 - 1) := by
      have h15 : 15 ≤ Q ^ 2 - 1 := by
        have : 16 ≤ Q ^ 2 := by nlinarith
        omega
      calc 60 = 4 * 15 := by norm_num
        _ ≤ Q * (Q ^ 2 - 1) := Nat.mul_le_mul hQ h15
    have := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hb
    omega

theorem not_dvd_cycle {f : ℕ} (hf : 1 ≤ f) :
    ¬ ((2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1) * ((2 ^ f) * ((2 ^ f) ^ 2 - 1)) ∣ 20160) := by
  intro h
  rcases Nat.lt_or_ge f 2 with h1 | h1
  · obtain rfl : f = 1 := by omega
    revert h
    decide
  · have hQ : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h1
    generalize 2 ^ f = Q at hQ h
    have hle := Nat.le_of_dvd (by norm_num) h
    have ha : 64 * 4095 ≤ Q ^ 3 * ((Q ^ 3) ^ 2 - 1) := by
      have h64 : 64 ≤ Q ^ 3 := by
        calc 64 = 4 ^ 3 := by norm_num
          _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
      have h4095 : 4095 ≤ (Q ^ 3) ^ 2 - 1 := by
        have : 4096 ≤ (Q ^ 3) ^ 2 := by
          calc 4096 = 64 ^ 2 := by norm_num
            _ ≤ (Q ^ 3) ^ 2 := Nat.pow_le_pow_left h64 2
        omega
      exact Nat.mul_le_mul h64 h4095
    have hb : 60 ≤ Q * (Q ^ 2 - 1) := by
      have h15 : 15 ≤ Q ^ 2 - 1 := by
        have : 16 ≤ Q ^ 2 := by nlinarith
        omega
      calc 60 = 4 * 15 := by norm_num
        _ ≤ Q * (Q ^ 2 - 1) := Nat.mul_le_mul hQ h15
    have := Nat.mul_le_mul ha hb
    omega

end Arith

section Pair

variable {L : Type} [Field L] [CharP L 2]

@[expose] noncomputable def fixSub (F₁ : ModGL τ L →* ModGL τ L) : Subgroup (ModGL τ L) :=
  F₁.eqLocus (MonoidHom.id _)

theorem mem_fixSub {F₁ : ModGL τ L →* ModGL τ L} {g : ModGL τ L} : g ∈ fixSub F₁ ↔ F₁ g = g :=
  Iff.rfl

theorem sl2_map_WSL (φ : L →+* L) :
    Matrix.SpecialLinearGroup.map φ (WSL : SL2 L) = WSL := by
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [WSL]

theorem sl2_map_uSL (φ : L →+* L) (c : L) :
    Matrix.SpecialLinearGroup.map φ (CFSG.LieType.Chevalley.uSL c : SL2 L) =
      CFSG.LieType.Chevalley.uSL (φ c) := by
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [CFSG.LieType.Chevalley.uSL]

theorem sl2_map_vSL (φ : L →+* L) (c : L) :
    Matrix.SpecialLinearGroup.map φ (CFSG.LieType.Chevalley.vSL c : SL2 L) =
      CFSG.LieType.Chevalley.vSL (φ c) := by
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [CFSG.LieType.Chevalley.vSL]

theorem slHom_commute_gen (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (h0 : iform α β = 0) (φ ψ : L →+* L)
    (K K' : Subfield L) (A : SL2 K) (B : SL2 K') :
    Commute (slHom α φ K A) (slHom β ψ K' B) :=
  commute_rootSL2_of_iform_zero hτ hα hβ h0 _ _

theorem pair_injective (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (h0 : iform α β = 0) (φ ψ : L →+* L) (K : Subfield L) :
    Function.Injective (mulHom (slHom (τ := τ) α φ K) (slHom β ψ K)
      (fun A B => slHom_commute_gen hτ hα hβ h0 φ ψ K K A B)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [mulHom_apply] at hA
  have h1 : slHom (τ := τ) α φ K A = (slHom β ψ K A)⁻¹ := eq_inv_of_mul_eq_one_left hA
  have hcen : ∀ C : SL2 L, C * Matrix.SpecialLinearGroup.map (φ.comp K.subtype) A =
      Matrix.SpecialLinearGroup.map (φ.comp K.subtype) A * C := by
    intro C
    apply rootSL2_injective_of_field (τ := τ) (K := L) α
    rw [map_mul, map_mul]
    have h2 : rootSL2 τ L α (Matrix.SpecialLinearGroup.map (φ.comp K.subtype) A) =
        (slHom β ψ K A)⁻¹ := h1
    rw [h2]
    exact ((commute_rootSL2_of_iform_zero hτ hα hβ h0 C
      (Matrix.SpecialLinearGroup.map (ψ.comp K.subtype) A)).inv_right).eq
  have h3 := sl2_eq_one_of_forall_comm (fun B => (hcen B).symm)
  exact sl2_map_injective (φ.comp K.subtype) (by rw [h3, map_one])

theorem nD4_fixed_swap (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc) {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A)) :
    F₁ (nD4 L βa βb βk βc) = nD4 L βa βb βk βc := by
  unfold nD4
  rw [map_mul, map_mul, map_mul, hFc, hFa, hFb, hFk, sl2_map_WSL]
  have hc : rootSL2 τ L βb WSL * rootSL2 τ L βa WSL = rootSL2 τ L βa WSL * rootSL2 τ L βb WSL :=
    (commute_rootSL2_of_iform_zero hτ cfg.rb cfg.ra (by rw [iform_comm]; exact cfg.ab) _ _).eq
  congr 1
  rw [mul_assoc, hc, ← mul_assoc]

theorem mulHom_injective_right {β : Fin τ.rank → ℤ} (φ : L →+* L) (K : Subfield L)
    (f : SL2 K →* ModGL τ L) (h : ∀ A B, Commute (f A) (slHom (τ := τ) β φ K B))
    (hall : ∀ (A : SL2 K) (C : SL2 L), Commute (f A) (rootSL2 τ L β C)) :
    Function.Injective (mulHom f (slHom β φ K) h) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [mulHom_apply] at hA
  have h1 : slHom (τ := τ) β φ K A = (f A)⁻¹ := eq_inv_of_mul_eq_one_right hA
  have hcen : ∀ C : SL2 L, C * Matrix.SpecialLinearGroup.map (φ.comp K.subtype) A =
      Matrix.SpecialLinearGroup.map (φ.comp K.subtype) A * C := by
    intro C
    apply rootSL2_injective_of_field (τ := τ) (K := L) β
    rw [map_mul, map_mul]
    have h2 : rootSL2 τ L β (Matrix.SpecialLinearGroup.map (φ.comp K.subtype) A) = (f A)⁻¹ := h1
    rw [h2]
    exact ((hall A C).symm.inv_right).eq
  have h3 := sl2_eq_one_of_forall_comm (fun B => (hcen B).symm)
  exact sl2_map_injective (φ.comp K.subtype) (by rw [h3, map_one])

theorem nD4_fixed_cycle (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc) {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A)) :
    F₁ (nD4 L βa βb βk βc) = nD4 L βa βb βk βc := by
  unfold nD4
  rw [map_mul, map_mul, map_mul, hFc, hFa, hFb, hFk, sl2_map_WSL]
  have hba : rootSL2 τ L βb WSL * rootSL2 τ L βa WSL = rootSL2 τ L βa WSL * rootSL2 τ L βb WSL :=
    (commute_rootSL2_of_iform_zero hτ cfg.rb cfg.ra (by rw [iform_comm]; exact cfg.ab) _ _).eq
  have hka : rootSL2 τ L βk WSL * rootSL2 τ L βa WSL = rootSL2 τ L βa WSL * rootSL2 τ L βk WSL :=
    (commute_rootSL2_of_iform_zero hτ cfg.rk cfg.ra (by rw [iform_comm]; exact cfg.ak) _ _).eq
  calc rootSL2 τ L βc WSL * rootSL2 τ L βb WSL * rootSL2 τ L βk WSL * rootSL2 τ L βa WSL
      = rootSL2 τ L βc WSL * (rootSL2 τ L βb WSL * (rootSL2 τ L βk WSL * rootSL2 τ L βa WSL)) := by
        simp only [mul_assoc]
    _ = rootSL2 τ L βc WSL * (rootSL2 τ L βb WSL * (rootSL2 τ L βa WSL * rootSL2 τ L βk WSL)) := by
        rw [hka]
    _ = rootSL2 τ L βc WSL * ((rootSL2 τ L βb WSL * rootSL2 τ L βa WSL) * rootSL2 τ L βk WSL) := by
        simp only [mul_assoc]
    _ = rootSL2 τ L βc WSL * ((rootSL2 τ L βa WSL * rootSL2 τ L βb WSL) * rootSL2 τ L βk WSL) := by
        rw [hba]
    _ = rootSL2 τ L βc WSL * rootSL2 τ L βa WSL * rootSL2 τ L βb WSL * rootSL2 τ L βk WSL := by
        simp only [mul_assoc]

theorem sl2_map_WSL' {R S : Type} [Field R] [Field S] (f : R →+* S) :
    Matrix.SpecialLinearGroup.map f (WSL : SL2 R) = WSL := by
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [WSL]

@[expose] noncomputable def psiAB (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (h0 : iform α β = 0)
    (f m : ℕ) : SL2 (frobeniusFixedField L 2 m) →* ModGL τ L :=
  mulHom (slHom α (RingHom.id L) (frobeniusFixedField L 2 m))
    (slHom β (iterateFrobenius L 2 f) (frobeniusFixedField L 2 m))
    (fun A B => slHom_commute_gen hτ hα hβ h0 _ _ _ _ A B)

theorem psiAB_apply (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (h0 : iform α β = 0) (f m : ℕ)
    (A : SL2 (frobeniusFixedField L 2 m)) :
    psiAB hτ hα hβ h0 f m A = slHom α (RingHom.id L) (frobeniusFixedField L 2 m) A *
      slHom β (iterateFrobenius L 2 f) (frobeniusFixedField L 2 m) A := rfl

theorem psiAB_injective (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (h0 : iform α β = 0) (f m : ℕ) :
    Function.Injective (psiAB (L := L) hτ hα hβ h0 f m) :=
  pair_injective hτ hα hβ h0 _ _ _

theorem psiAB_commute_k (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc) (f m : ℕ) (φ : L →+* L)
    (A B : SL2 (frobeniusFixedField L 2 m)) :
    Commute (psiAB hτ cfg.ra cfg.rb cfg.ab f m A)
      (slHom βk φ (frobeniusFixedField L 2 m) B) := by
  rw [psiAB_apply]
  exact Commute.mul_left (slHom_commute_gen hτ cfg.ra cfg.rk cfg.ak _ _ _ _ A B)
    (slHom_commute_gen hτ cfg.rb cfg.rk cfg.bk _ _ _ _ A B)

@[expose] noncomputable def psiABK (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc) (f m : ℕ) :
    SL2 (frobeniusFixedField L 2 m) →* ModGL τ L :=
  mulHom (psiAB hτ cfg.ra cfg.rb cfg.ab f m)
    (slHom βk ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
      (frobeniusFixedField L 2 m)) (fun A B => psiAB_commute_k hτ cfg f m _ A B)

theorem psiABK_apply (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc) (f m : ℕ)
    (A : SL2 (frobeniusFixedField L 2 m)) :
    psiABK hτ cfg f m A = slHom βa (RingHom.id L) (frobeniusFixedField L 2 m) A *
      slHom βb (iterateFrobenius L 2 f) (frobeniusFixedField L 2 m) A *
      slHom βk ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
        (frobeniusFixedField L 2 m) A := rfl

theorem psiABK_injective (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc) (f m : ℕ) :
    Function.Injective (psiABK (L := L) hτ cfg f m) := by
  refine mulHom_injective_right _ _ (psiAB hτ cfg.ra cfg.rb cfg.ab f m) _ fun A C => ?_
  rw [psiAB_apply]
  exact Commute.mul_left (commute_rootSL2_of_iform_zero hτ cfg.ra cfg.rk cfg.ak _ C)
    (commute_rootSL2_of_iform_zero hτ cfg.rb cfg.rk cfg.bk _ C)

theorem nD4_eq_swap (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc) (f : ℕ) :
    nD4 L βa βb βk βc =
      slHom βc (RingHom.id L) (frobeniusFixedField L 2 f) WSL *
        psiAB hτ cfg.ra cfg.rb cfg.ab f (2 * f) WSL *
        slHom βk (RingHom.id L) (frobeniusFixedField L 2 f) WSL := by
  simp only [psiAB_apply, slHom_apply, sl2_map_WSL']
  unfold nD4
  simp only [mul_assoc]

theorem nD4_eq_cycle (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc) (f : ℕ) :
    nD4 L βa βb βk βc =
      slHom βc (RingHom.id L) (frobeniusFixedField L 2 f) WSL *
        psiABK hτ cfg f (3 * f) WSL := by
  simp only [psiABK_apply, slHom_apply, sl2_map_WSL']
  unfold nD4
  simp only [mul_assoc]

theorem bad3_swap_in [IsAlgClosed L] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc)
    {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (C : Subgroup (ModGL τ L))
    (hCab : (psiAB hτ cfg.ra cfg.rb cfg.ab f (2 * f)).range ≤ C)
    (hCk : (slHom βk (RingHom.id L) (frobeniusFixedField L 2 f)).range ≤ C)
    (hCc : (slHom βc (RingHom.id L) (frobeniusFixedField L 2 f)).range ≤ C) :
    Bad3 (C ⊓ fixSub F₁) := by
  classical
  have hFn := nD4_fixed_swap hτ cfg hFa hFb hFk hFc
  have hnC : nD4 L βa βb βk βc ∈ C := by
    rw [nD4_eq_swap hτ cfg f]
    exact mul_mem (mul_mem (hCc ⟨WSL, rfl⟩) (hCab ⟨WSL, rfl⟩)) (hCk ⟨WSL, rfl⟩)
  obtain ⟨Z, hZfix, hZC, hZc, hZcard, hZa, hZb, hZk⟩ :=
    exists_theta_factor hτ hf cfg F₁ hFc hFn C hnC hCc
  have h22 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [mul_comm, pow_mul]
  have hΨab_apply := psiAB_apply (L := L) hτ cfg.ra cfg.rb cfg.ab f (2 * f)
  have hΨab_inj := psiAB_injective (L := L) hτ cfg.ra cfg.rb cfg.ab f (2 * f)
  have hΨab_fix : ∀ A, F₁ (psiAB hτ cfg.ra cfg.rb cfg.ab f (2 * f) A) =
      psiAB hτ cfg.ra cfg.rb cfg.ab f (2 * f) A := by
    intro A
    rw [hΨab_apply, map_mul, F_slHom _ hFa, F_slHom _ hFb, RingHom.comp_id]
    have : slHom βa ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
        (frobeniusFixedField L 2 (2 * f)) A =
        slHom βa (RingHom.id L) (frobeniusFixedField L 2 (2 * f)) A := by
      rw [slHom_apply, slHom_apply, RingHom.comp_assoc, frob_comp_subtype_two, RingHom.id_comp]
    rw [this]
    exact (slHom_commute_gen hτ cfg.ra cfg.rb cfg.ab _ _ _ _ A A).eq.symm
  let Ψk : SL2 (frobeniusFixedField L 2 f) →* ModGL τ L :=
    slHom βk (RingHom.id L) (frobeniusFixedField L 2 f)
  have hΨk_inj : Function.Injective Ψk := slHom_injective _ _ _
  have hΨk_fix : ∀ A, F₁ (Ψk A) = Ψk A := by
    intro A
    change F₁ (slHom βk (RingHom.id L) (frobeniusFixedField L 2 f) A) =
      slHom βk (RingHom.id L) (frobeniusFixedField L 2 f) A
    rw [F_slHom _ hFk, RingHom.comp_id, slHom_frob_one]
  refine ⟨(psiAB hτ cfg.ra cfg.rb cfg.ab f (2 * f)).range, Ψk.range, Z, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hCab ⟨A, rfl⟩, mem_fixSub.2 (hΨab_fix A)⟩
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hCk ⟨A, rfl⟩, mem_fixSub.2 (hΨk_fix A)⟩
  · intro g hg
    exact Subgroup.mem_inf.2 ⟨hZC g hg, mem_fixSub.2 (hZfix g hg)⟩
  · rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    rw [hΨab_apply]
    exact (Commute.mul_left (slHom_commute_gen hτ cfg.ra cfg.rk cfg.ak _ _ _ _ A B)
      (slHom_commute_gen hτ cfg.rb cfg.rk cfg.bk _ _ _ _ A B)).eq
  · rintro _ ⟨A, rfl⟩ g hg
    rw [hΨab_apply]
    exact (Commute.mul_left (show Commute _ g from (hZa g hg _).symm)
      (show Commute _ g from (hZb g hg _).symm)).eq
  · rintro _ ⟨A, rfl⟩ g hg
    exact (show Commute _ g from (hZk g hg _).symm).eq
  · exact centerless_range _ hΨab_inj fun A hA => sl2_eq_one_of_forall_comm hA
  · exact centerless_range _ hΨk_inj fun A hA => sl2_eq_one_of_forall_comm hA
  · exact hZc
  · rw [card_range_of_injective _ hΨab_inj, card_range_of_injective _ hΨk_inj, hZcard,
      card_sl2_frobFixed (by omega : 0 < 2 * f), card_sl2_frobFixed (by omega : 0 < f), h22]
    exact not_dvd_swap hf

theorem bad3_swap [IsAlgClosed L] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc)
    {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A)) :
    Bad3 (cfgGroup τ L βa βb βk βc ⊓ fixSub F₁) :=
  bad3_swap_in hτ hf cfg hFa hFb hFk hFc _
    (by
      rintro _ ⟨A, rfl⟩
      rw [psiAB_apply]
      exact mul_mem (rootSL2_mem_cfgGroup_a _) (rootSL2_mem_cfgGroup_b _))
    (by
      rintro _ ⟨A, rfl⟩
      exact rootSL2_mem_cfgGroup_k _)
    (by
      rintro _ ⟨A, rfl⟩
      exact rootSL2_mem_cfgGroup_c _)

theorem bad3_cycle_in [IsAlgClosed L] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc)
    {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (C : Subgroup (ModGL τ L))
    (hCabk : (psiABK hτ cfg f (3 * f)).range ≤ C)
    (hCc : (slHom βc (RingHom.id L) (frobeniusFixedField L 2 f)).range ≤ C) :
    Bad3 (C ⊓ fixSub F₁) := by
  classical
  have hFn := nD4_fixed_cycle hτ cfg hFa hFb hFk hFc
  have hnC : nD4 L βa βb βk βc ∈ C := by
    rw [nD4_eq_cycle hτ cfg f]
    exact mul_mem (hCc ⟨WSL, rfl⟩) (hCabk ⟨WSL, rfl⟩)
  obtain ⟨Z, hZfix, hZC, hZc, hZcard, hZa, hZb, hZk⟩ :=
    exists_theta_factor hτ hf cfg F₁ hFc hFn C hnC hCc
  have h33 : 2 ^ (3 * f) = (2 ^ f) ^ 3 := by rw [mul_comm, pow_mul]
  have hΨ₃_apply := psiABK_apply (L := L) hτ cfg f (3 * f)
  have hΨ₃_inj := psiABK_injective (L := L) hτ cfg f (3 * f)
  have hΨ₃_fix : ∀ A, F₁ (psiABK hτ cfg f (3 * f) A) = psiABK hτ cfg f (3 * f) A := by
    intro A
    rw [hΨ₃_apply, map_mul, map_mul, F_slHom _ hFa, F_slHom _ hFb, F_slHom _ hFk,
      RingHom.comp_id]
    have h3 : slHom βa ((iterateFrobenius L 2 f).comp ((iterateFrobenius L 2 f).comp
        (iterateFrobenius L 2 f))) (frobeniusFixedField L 2 (3 * f)) A =
        slHom βa (RingHom.id L) (frobeniusFixedField L 2 (3 * f)) A := by
      rw [slHom_apply, slHom_apply]
      simp only [RingHom.comp_assoc]
      rw [frob_comp_subtype_three, RingHom.id_comp]
    rw [h3]
    have hba := (slHom_commute_gen hτ cfg.rb cfg.ra (by rw [iform_comm]; exact cfg.ab)
      (iterateFrobenius L 2 f) (RingHom.id L) (frobeniusFixedField L 2 (3 * f))
      (frobeniusFixedField L 2 (3 * f)) A A).eq
    have hka := (slHom_commute_gen hτ cfg.rk cfg.ra (by rw [iform_comm]; exact cfg.ak)
      ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f)) (RingHom.id L)
      (frobeniusFixedField L 2 (3 * f)) (frobeniusFixedField L 2 (3 * f)) A A).eq
    calc slHom βb (iterateFrobenius L 2 f) (frobeniusFixedField L 2 (3 * f)) A *
          slHom βk ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
            (frobeniusFixedField L 2 (3 * f)) A *
          slHom βa (RingHom.id L) (frobeniusFixedField L 2 (3 * f)) A
        = slHom βb (iterateFrobenius L 2 f) (frobeniusFixedField L 2 (3 * f)) A *
          (slHom βk ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
            (frobeniusFixedField L 2 (3 * f)) A *
          slHom βa (RingHom.id L) (frobeniusFixedField L 2 (3 * f)) A) := by
          simp only [mul_assoc]
      _ = slHom βb (iterateFrobenius L 2 f) (frobeniusFixedField L 2 (3 * f)) A *
          (slHom βa (RingHom.id L) (frobeniusFixedField L 2 (3 * f)) A *
          slHom βk ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
            (frobeniusFixedField L 2 (3 * f)) A) := by rw [hka]
      _ = slHom βa (RingHom.id L) (frobeniusFixedField L 2 (3 * f)) A *
          slHom βb (iterateFrobenius L 2 f) (frobeniusFixedField L 2 (3 * f)) A *
          slHom βk ((iterateFrobenius L 2 f).comp (iterateFrobenius L 2 f))
            (frobeniusFixedField L 2 (3 * f)) A := by
          rw [← mul_assoc, hba, mul_assoc]
  refine ⟨(psiABK hτ cfg f (3 * f)).range, Z, ⊥, ?_, ?_, bot_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hCabk ⟨A, rfl⟩, mem_fixSub.2 (hΨ₃_fix A)⟩
  · intro g hg
    exact Subgroup.mem_inf.2 ⟨hZC g hg, mem_fixSub.2 (hZfix g hg)⟩
  · rintro _ ⟨A, rfl⟩ g hg
    rw [hΨ₃_apply]
    exact (Commute.mul_left (Commute.mul_left (show Commute _ g from (hZa g hg _).symm)
      (show Commute _ g from (hZb g hg _).symm)) (show Commute _ g from (hZk g hg _).symm)).eq
  · rintro a _ b hb
    rw [Subgroup.mem_bot.1 hb, mul_one, one_mul]
  · rintro a _ b hb
    rw [Subgroup.mem_bot.1 hb, mul_one, one_mul]
  · exact centerless_range _ hΨ₃_inj fun A hA => sl2_eq_one_of_forall_comm hA
  · exact hZc
  · intro a ha _
    exact Subgroup.mem_bot.1 ha
  · rw [card_range_of_injective _ hΨ₃_inj, hZcard, Subgroup.card_bot,
      card_sl2_frobFixed (by omega : 0 < 3 * f), h33, mul_one]
    exact not_dvd_cycle hf

theorem bad3_cycle [IsAlgClosed L] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) {βa βb βk βc : Fin τ.rank → ℤ} (cfg : D4Cfg τ βa βb βk βc)
    {F₁ : ModGL τ L →* ModGL τ L}
    (hFa : ∀ A : SL2 L, F₁ (rootSL2 τ L βa A) =
      rootSL2 τ L βb (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFb : ∀ A : SL2 L, F₁ (rootSL2 τ L βb A) =
      rootSL2 τ L βk (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFk : ∀ A : SL2 L, F₁ (rootSL2 τ L βk A) =
      rootSL2 τ L βa (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A))
    (hFc : ∀ A : SL2 L, F₁ (rootSL2 τ L βc A) =
      rootSL2 τ L βc (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f) A)) :
    Bad3 (cfgGroup τ L βa βb βk βc ⊓ fixSub F₁) :=
  bad3_cycle_in hτ hf cfg hFa hFb hFk hFc _
    (by
      rintro _ ⟨A, rfl⟩
      rw [psiABK_apply]
      exact mul_mem (mul_mem (rootSL2_mem_cfgGroup_a _) (rootSL2_mem_cfgGroup_b _))
        (rootSL2_mem_cfgGroup_k _))
    (by
      rintro _ ⟨A, rfl⟩
      exact rootSL2_mem_cfgGroup_c _)

end Pair

end Config

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
