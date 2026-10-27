module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271Defs202
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsNineOddInner
public import CFSG.GH74.GLS.IVK.L2.Hilbert90

public noncomputable section

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.HardMathSupport.Solomon.Coordinator

namespace CFSG.HardMathSupport.Solomon.Coordinator.L2Plane

variable {F : Type} [Field F] [Finite F]

@[expose] def cSL (y : PGammaL2 F) : Subgroup (PSL2 F) :=
  MonoidHom.eqLocus (semilinearAction F y).toMonoidHom (MonoidHom.id _)

theorem mem_cSL {y : PGammaL2 F} {x : PSL2 F} : x ∈ cSL y ↔ semilinearAction F y x = x := Iff.rfl

theorem mem_fixSub_zpowers_iff {S : Type} [Group S] (e : S ≃* PSL2 F) (a : MulAut S) (s : S) :
    s ∈ fixSubAut (Subgroup.zpowers a) ↔ e s ∈ cSL (autEquiv e a) := by
  rw [mem_cSL, semilinearAction_autEquiv_apply, e.injective.eq_iff]
  unfold fixSubAut
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h
    exact h a (Subgroup.mem_zpowers a)
  · intro h c hc
    have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (MulAut S) s :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h)
    exact MulAction.mem_stabilizer_iff.1 (hle hc)

theorem cSL_conj (c y : PGammaL2 F) :
    cSL (c * y * c⁻¹) = (cSL y).map (semilinearAction F c).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_cSL, mem_cSL]
  simp only [map_mul, map_inv, MulAut.mul_apply]
  have h1 : ((semilinearAction F c)⁻¹ : MulAut (PSL2 F)) x = (semilinearAction F c).symm x := rfl
  rw [h1]
  constructor
  · intro h
    have := congrArg (semilinearAction F c).symm h
    simpa using this
  · intro h
    rw [h]
    simp

open CFSG.Open

structure PlaneCase (F : Type) [Field F] [Finite F] : Prop where
  bound : ∀ σ : F ≃+* F, orderOf σ = 3 → ∀ A₀ : Subgroup (PGL2 F), IsElemAbelian 3 A₀ →
    (∀ g ∈ A₀, pgl2FieldAut F σ g = g) → Nat.card A₀ ≤ 3
  gen : ∀ σ : F ≃+* F, orderOf σ = 3 → ∀ g : PGL2 F, g ≠ 1 → g ^ 3 = 1 →
    pgl2FieldAut F σ g = g →
      cSL (SemidirectProduct.inr σ : PGammaL2 F) ⊔ cSL (SemidirectProduct.inl g : PGammaL2 F) = ⊤

theorem exists_outer (A : Subgroup (PGammaL2 F)) (hA : IsElemAbelian 3 A)
    (hnin : ¬ A ≤ pGammaL2PSLRange F) : ∃ y ∈ A, y ^ 3 = 1 ∧ y.right ≠ 1 := by
  rw [SetLike.not_le_iff_exists] at hnin
  obtain ⟨y, hyA, hy⟩ := hnin
  refine ⟨y, hyA, hA.2 y hyA, ?_⟩
  intro hr
  apply hy
  have hy' : y = SemidirectProduct.inl y.left := SemidirectProduct.ext rfl hr
  have h3 : y.left ^ 3 = 1 := by
    have := hA.2 y hyA
    rw [hy', ← map_pow] at this
    exact SemidirectProduct.inl_injective (by simpa using this)
  have hodd : Odd (orderOf y.left) := by
    have hd : orderOf y.left ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h <;> rw [h] <;> decide
  obtain ⟨z, hz⟩ := mem_psl2Range_of_odd _ hodd
  rw [hy']
  refine ⟨z, ?_⟩
  rw [MonoidHom.comp_apply, hz]

theorem card_eq_card_ker_mul_card_range' {P Q : Type*} [Group P] [Group Q] (f : P →* Q) :
    Nat.card P = Nat.card f.ker * Nat.card f.range := by
  rw [mul_comm, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker

theorem card_le_three_of_cube_ringAut (H : Subgroup (F ≃+* F)) (hH : ∀ σ ∈ H, σ ^ 3 = 1) :
    Nat.card H ≤ 3 := by
  classical
  have := isCyclic_ringAut F
  have : Fintype (F ≃+* F) := Fintype.ofFinite _
  have h := IsCyclic.card_pow_eq_one_le (α := F ≃+* F) (n := 3) (by norm_num)
  calc Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
    _ = (Finset.univ.filter fun σ : F ≃+* F => σ ∈ H).card := by
        rw [← Fintype.card_subtype]
    _ ≤ (Finset.univ.filter fun σ : F ≃+* F => σ ^ 3 = 1).card := by
        apply Finset.card_le_card
        intro σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hH σ
    _ ≤ 3 := h

theorem plane_core (h : PlaneCase F) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    {A : Subgroup (PGammaL2 F)} (hA : IsElemAbelian 3 A)
    (hσA : (SemidirectProduct.inr σ : PGammaL2 F) ∈ A) :
    Nat.card A ≤ 9 ∧ (Nat.card A = 9 → ∃ y₁ ∈ A, ∃ y₂ ∈ A, y₁ ≠ 1 ∧ y₂ ≠ 1 ∧
      y₂ ∉ Subgroup.zpowers y₁ ∧ cSL y₁ ⊔ cSL y₂ = ⊤) := by
  classical
  let π : PGammaL2 F →* (F ≃+* F) := SemidirectProduct.rightHom
  let f : A →* (F ≃+* F) := π.comp A.subtype
  have hcard := card_eq_card_ker_mul_card_range' f
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ
    omega
  have hrange3 : Nat.card f.range = 3 := by
    apply le_antisymm
    · refine card_le_three_of_cube_ringAut f.range ?_
      rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : (a : PGammaL2 F) ^ 3 = 1 := hA.2 a a.2
      have h3 : a ^ 3 = 1 := Subtype.ext this
      rw [h3, map_one]
    · have hmem : σ ∈ f.range := ⟨⟨SemidirectProduct.inr σ, hσA⟩, by simp [f, π]⟩
      have hle : Subgroup.zpowers σ ≤ f.range := (Subgroup.zpowers_le).2 hmem
      have := Subgroup.card_le_of_le hle
      rwa [Nat.card_zpowers, hσ] at this
  let A₀ : Subgroup (PGL2 F) := A.comap SemidirectProduct.inl
  have hker : Nat.card f.ker = Nat.card A₀ := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun g : A₀ => (⟨⟨SemidirectProduct.inl g.1, g.2⟩, ?_⟩ : f.ker)) ⟨?_, ?_⟩)
    · simp [f, π]
    · intro g g' hgg
      have := congrArg (fun z : f.ker => ((z : A) : PGammaL2 F)) hgg
      exact Subtype.ext (SemidirectProduct.inl_injective this)
    · rintro ⟨⟨a, haA⟩, ha⟩
      have hr : a.right = 1 := by simpa [f, π, MonoidHom.mem_ker] using ha
      have hy' : a = SemidirectProduct.inl a.left := SemidirectProduct.ext rfl hr
      refine ⟨⟨a.left, by rw [Subgroup.mem_comap, ← hy']; exact haA⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hy'.symm
  have hA₀ : IsElemAbelian 3 A₀ := by
    refine ⟨⟨⟨fun g g' => ?_⟩⟩, fun g hg => ?_⟩
    · have := hA.1.is_comm.comm ⟨SemidirectProduct.inl g.1, g.2⟩ ⟨SemidirectProduct.inl g'.1, g'.2⟩
      have h2 := congrArg Subtype.val this
      exact Subtype.ext (SemidirectProduct.inl_injective (by simpa using h2))
    · have := hA.2 (SemidirectProduct.inl g) hg
      rw [← map_pow] at this
      exact SemidirectProduct.inl_injective (by simpa using this)
  have hfix : ∀ g ∈ A₀, pgl2FieldAut F σ g = g := by
    intro g hg
    have := hA.1.is_comm.comm ⟨SemidirectProduct.inl g, hg⟩ ⟨SemidirectProduct.inr σ, hσA⟩
    have h2 := congrArg (fun z : A => ((z : PGammaL2 F)).left) this
    simpa using h2.symm
  have hb := h.bound σ hσ A₀ hA₀ hfix
  refine ⟨by rw [hcard, hrange3, hker]; omega, fun h9 => ?_⟩
  have h30 : Nat.card A₀ = 3 := by rw [hcard, hrange3, hker] at h9; omega
  obtain ⟨g, hgA, hg1⟩ : ∃ g ∈ A₀, g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card A₀ = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩, ⟨1⟩⟩
    omega
  have hg3 : g ^ 3 = 1 := hA₀.2 g hgA
  have hfixg := hfix g hgA
  refine ⟨SemidirectProduct.inr σ, hσA, SemidirectProduct.inl g, hgA, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact hσ1 (SemidirectProduct.inr_injective (by simpa using h1))
  · intro h1
    exact hg1 (SemidirectProduct.inl_injective (by simpa using h1))
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hk' : (SemidirectProduct.inr (σ ^ k) : PGammaL2 F) = SemidirectProduct.inl g := by
      rw [map_zpow]; exact hk
    have this : (1 : PGL2 F) = g := congrArg SemidirectProduct.left hk'
    exact hg1 this.symm
  · exact h.gen σ hσ g hg1 hg3 hfixg

theorem plane_pgammaL2 (h : PlaneCase F) {A : Subgroup (PGammaL2 F)} (hA : IsElemAbelian 3 A)
    (hnin : ¬ A ≤ pGammaL2PSLRange F) :
    Nat.card A ≤ 9 ∧ (Nat.card A = 9 → ∃ y₁ ∈ A, ∃ y₂ ∈ A, y₁ ≠ 1 ∧ y₂ ≠ 1 ∧
      y₂ ∉ Subgroup.zpowers y₁ ∧ cSL y₁ ⊔ cSL y₂ = ⊤) := by
  obtain ⟨y, hyA, hy3, hyr⟩ := exists_outer A hA hnin
  have hσ3 : y.right ^ 3 = 1 := by
    have h1 := map_pow (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) y 3
    rw [hy3, map_one] at h1
    exact h1.symm
  have hσ : orderOf y.right = 3 := orderOf_eq_prime hσ3 hyr
  obtain ⟨C, hC⟩ := CFSG.GH74.GLS.IVK.H90.pgammaL2_conj_inr_of_pow_eq_one y (by rw [hσ]; exact hy3)
  set c : PGammaL2 F := SemidirectProduct.inl C with hc
  let κ : PGammaL2 F ≃* PGammaL2 F := MulAut.conj c⁻¹
  have hκ : ∀ z, κ z = c⁻¹ * z * c := fun z => by simp [κ, MulAut.conj_apply]
  have hκs : ∀ z, κ.symm z = c * z * c⁻¹ := fun z => by
    apply κ.injective
    rw [MulEquiv.apply_symm_apply, hκ]
    group
  let A' : Subgroup (PGammaL2 F) := A.map κ.toMonoidHom
  have hA' : IsElemAbelian 3 A' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      have h2 : a' * b' = b' * a' := by
        have := hA.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
        exact congrArg Subtype.val this
      apply Subtype.ext
      show (a : PGammaL2 F) * b = b * a
      rw [← ha, ← hb]
      show κ a' * κ b' = κ b' * κ a'
      rw [← map_mul, ← map_mul, h2]
    · rintro _ ⟨a', ha', rfl⟩
      rw [← map_pow]
      show κ (a' ^ 3) = 1
      rw [hA.2 a' ha', map_one]
  have hσA' : (SemidirectProduct.inr y.right : PGammaL2 F) ∈ A' := by
    refine ⟨y, hyA, ?_⟩
    show κ y = _
    rw [hκ, ← hC]
  obtain ⟨hc9, hgen⟩ := plane_core h hσ hA' hσA'
  have hcard : Nat.card A' = Nat.card A :=
    Nat.card_congr (A.equivMapOfInjective κ.toMonoidHom κ.injective).toEquiv.symm
  refine ⟨hcard ▸ hc9, fun h9 => ?_⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, h1, h2, h3, h4⟩ := hgen (hcard ▸ h9)
  have hmem : ∀ z ∈ A', κ.symm z ∈ A := fun z hz => by
    have := (Subgroup.mem_map_equiv (f := κ) (K := A) (x := z)).1 hz
    exact this
  refine ⟨κ.symm y₁, hmem _ hy₁, κ.symm y₂, hmem _ hy₂, ?_, ?_, ?_, ?_⟩
  · intro h; exact h1 (by simpa using h)
  · intro h; exact h2 (by simpa using h)
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    apply h3
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have := congrArg κ hk
    rw [← map_zpow] at this
    simpa using this
  · rw [hκs, hκs, cSL_conj, cSL_conj, ← Subgroup.map_sup, h4]
    exact (Subgroup.map_top_of_surjective _ (semilinearAction F c).surjective)

theorem center_specialLinearGroup_two_eq_bot {K : Type} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hrA⟩ := hA
  rw [Subgroup.mem_bot]
  have h2 : r ^ 2 = 1 := by simpa using hr
  have h1 : r = 1 := by
    have h3 : (r + 1) ^ 2 = 0 := by
      have h22 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination h2 + (r + 1) * h22
    have := pow_eq_zero_iff (two_ne_zero) |>.1 h3
    calc r = (r + 1) - 1 := by ring
      _ = 0 - 1 := by rw [this]
      _ = 1 := by
        have : (2 : K) = 0 := CharP.cast_eq_zero K 2
        linear_combination (-1 : K) * this
  subst h1
  apply Subtype.ext
  rw [← hrA]
  simp

noncomputable def slEquivPsl2 (K : Type) [Field K] [CharP K 2] :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* PSL2 K :=
  (QuotientGroup.quotientBot (G := Matrix.SpecialLinearGroup (Fin 2) K)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_specialLinearGroup_two_eq_bot (K := K)).symm)

theorem l2FieldPlane_of_case
    (hcase : ∀ (F : Type) [Field F] [Finite F],
      (Nat.card F = 27 ∨ ∃ n : ℕ, n % 2 = 1 ∧ 3 < n ∧ Nat.card F = 2 ^ n) → PlaneCase F) :
    L2FieldPlane := by
  intro S _ _ hS A hA hnin
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      (Nat.card F = 27 ∨ ∃ n : ℕ, n % 2 = 1 ∧ 3 < n ∧ Nat.card F = 2 ^ n) ∧
        Nonempty (S ≃* PSL2 F) := by
    rcases hS with h27 | ⟨hOdd, hn8⟩
    · obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h27
      exact ⟨F, hF, hfin, Or.inl hcard,
        ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩
    · obtain ⟨K, hK, hfin, n, hn, hn1, hcard, ⟨e⟩⟩ := hOdd
      have hn3 : n ≠ 3 := fun h3 =>
        hn8 ⟨K, hK, hfin, by rw [hcard, h3]; norm_num, ⟨e⟩⟩
      have : Fintype K := Fintype.ofFinite K
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
      exact ⟨K, hK, hfin, Or.inr ⟨n, hn, by omega, hcard⟩,
        ⟨e.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm.trans (slEquivPsl2 K))⟩⟩
  have hc := hcase F hF
  let φ : MulAut S ≃* PGammaL2 F := autEquiv e
  have hA' : IsElemAbelian 3 (A.map φ.toMonoidHom) := CFSG.SectionRank.isElemAbelian_map hA _
  have hnin' : ¬ A.map φ.toMonoidHom ≤ pGammaL2PSLRange F := by
    intro hle
    apply hnin
    intro a ha
    have h1 : φ a ∈ pGammaL2PSLRange F := hle ⟨a, ha, rfl⟩
    rw [← map_autEquiv_innAut e] at h1
    have h2 : (autEquiv e).symm (autEquiv e a) ∈ MulAut.conj.range := Subgroup.mem_map_equiv.1 h1
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2
  obtain ⟨hcard9, hgen⟩ := plane_pgammaL2 hc hA' hnin'
  have hcardA : Nat.card (A.map φ.toMonoidHom) = Nat.card A :=
    Nat.card_congr (A.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv.symm
  refine ⟨hcardA ▸ hcard9, fun h9 => ?_⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, h1, h2, h3, h4⟩ := hgen (hcardA ▸ h9)
  have hmem : ∀ z ∈ A.map φ.toMonoidHom, φ.symm z ∈ A := fun z hz => Subgroup.mem_map_equiv.1 hz
  refine ⟨φ.symm y₁, hmem _ hy₁, φ.symm y₂, hmem _ hy₂, ?_, ?_, ?_, ?_⟩
  · intro h; exact h1 (by simpa using h)
  · intro h; exact h2 (by simpa using h)
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    apply h3
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have := congrArg φ hk
    rw [← map_zpow] at this
    simpa using this
  · have key : ∀ y : PGammaL2 F,
        fixSubAut (Subgroup.zpowers (φ.symm y)) = (cSL y).map e.symm.toMonoidHom := by
      intro y
      ext s
      rw [mem_fixSub_zpowers_iff e, Subgroup.mem_map_equiv]
      simp [φ]
    rw [key, key, ← Subgroup.map_sup, h4]
    exact Subgroup.map_top_of_surjective _ e.symm.surjective


end CFSG.HardMathSupport.Solomon.Coordinator.L2Plane
