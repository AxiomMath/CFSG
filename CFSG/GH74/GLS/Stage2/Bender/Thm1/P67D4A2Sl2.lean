module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Core
public import CFSG.GH74.GLS.Stage4.HexModelD4
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Elementary

variable {K : Type} [Field K]

theorem a2sl_map_upper (k : Subfield K) (c : k) :
    Matrix.SpecialLinearGroup.map k.subtype (sl2Upper c) = sl2Upper (c : K) :=
  Subtype.ext (by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [coe_sl2Upper])

theorem a2sl_map_lower (k : Subfield K) (c : k) :
    Matrix.SpecialLinearGroup.map k.subtype (sl2Lower c) = sl2Lower (c : K) :=
  Subtype.ext (by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [coe_sl2Lower])

theorem a2sl_char_outer (d : Kˣ) {s : ℤ} {a : Fin d4.rank} (ha : a ≠ nd 2) :
    a2Char d (s • Pi.single a 1) = 1 := by
  have h0 : (s • Pi.single a 1 : Fin d4.rank → ℤ) (nd 2) = 0 := by
    simp [Ne.symm ha]
  simp [a2Char, h0]

def a2slFix (σ : K ≃+* K) (d : Kˣ) : Subgroup (ModGL TwistTag.D4.tag K) where
  carrier := {g | a2Conj σ d g = g}
  one_mem' := a2Conj_one σ d
  mul_mem' {g g'} hg hg' := by
    change a2Conj σ d g = g at hg
    change a2Conj σ d g' = g' at hg'
    change a2Conj σ d (g * g') = g * g'
    rw [a2Conj_mul, hg, hg']
  inv_mem' {g} hg := by
    change a2Conj σ d g = g at hg
    change a2Conj σ d g⁻¹ = g⁻¹
    rw [a2Conj_inv, hg]

theorem a2sl_mem_fix {σ : K ≃+* K} {d : Kˣ} {g : ModGL TwistTag.D4.tag K} :
    g ∈ a2slFix σ d ↔ a2Conj σ d g = g := Iff.rfl

theorem A2Core.a2sl_sigma_three [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ} (h : A2Core σ d q)
    (c : K) :
    σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
  sigma_three_of_card h.card h.frob c

theorem a2sl_sigma_three [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ} (h : A2Std σ d q) (c : K) :
    σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
  A2Core.a2sl_sigma_three h.toCore c

end Elementary

section Root

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2sl_xOuter_fixed (h : A2Core σ d q) {s : ℤ} (hs : s = 1 ∨ s = -1) {c : K}
    (hc : σ c = c) :
    a2Conj σ d ((xOuter s c c c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ((xOuter s c c c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  have key : ∀ a : Fin d4.rank, a ≠ nd 2 →
      a2Conj σ d ((xPar (rootOperatorFamily d4) (s • Pi.single a 1) c : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) =
      ((xPar (rootOperatorFamily d4) (s • Pi.single a 1) c : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) := fun a ha => by
    rw [a2Conj_xPar h (isRoot_smul_single hs a), a2sl_char_outer d ha, one_mul, hc]
  simp only [xOuter, Subgroup.coe_mul, a2Conj_mul]
  rw [key (nd 0) (by decide), key (nd 1) (by decide), key (nd 3) (by decide)]

end Root

section Short

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2sl_upper_fixed (h : A2Core σ d q) {c : K} (hc : σ c = c) :
    a2Conj σ d (((slShort σ.toRingHom (a2sl_sigma_three h) (sl2Upper c) :
      twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      (((slShort σ.toRingHom (a2sl_sigma_three h) (sl2Upper c) :
        twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  have hc' : σ.toRingHom c = c := hc
  rw [slShort_upper]
  simp only [hc']
  exact a2sl_xOuter_fixed h (Or.inl rfl) hc

theorem a2sl_upper_fixed (h : A2Std σ d q) {c : K} (hc : σ c = c) :
    a2Conj σ d (((slShort σ.toRingHom (a2sl_sigma_three h) (sl2Upper c) :
      twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      (((slShort σ.toRingHom (a2sl_sigma_three h) (sl2Upper c) :
        twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) :=
  A2Core.a2sl_upper_fixed h.toCore hc

theorem A2Core.a2sl_lower_fixed (h : A2Core σ d q) {c : K} (hc : σ c = c) :
    a2Conj σ d (((slShort σ.toRingHom (a2sl_sigma_three h) (sl2Lower c) :
      twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      (((slShort σ.toRingHom (a2sl_sigma_three h) (sl2Lower c) :
        twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  have hc' : σ.toRingHom c = c := hc
  rw [slShort_lower]
  simp only [hc']
  exact a2sl_xOuter_fixed h (Or.inr rfl) hc

theorem a2sl_lower_fixed (h : A2Std σ d q) {c : K} (hc : σ c = c) :
    a2Conj σ d (((slShort σ.toRingHom (a2sl_sigma_three h) (sl2Lower c) :
      twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      (((slShort σ.toRingHom (a2sl_sigma_three h) (sl2Lower c) :
        twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) :=
  A2Core.a2sl_lower_fixed h.toCore hc

theorem A2Core.a2_not_solvable (h : A2Core σ d q) :
    ∃ S : Subgroup (twistedGroup σ.toRingHom), ¬ Group.IsSolvable S ∧
      ∀ x ∈ S, a2Conj σ d (((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) =
        (((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  have hσ := a2sl_sigma_three h
  let k : Subfield K := fixedField σ.toRingHom
  let φ : Matrix.SpecialLinearGroup (Fin 2) k →* twistedGroup σ.toRingHom :=
    (slShort σ.toRingHom hσ).comp (Matrix.SpecialLinearGroup.map k.subtype)
  let ι : twistedGroup σ.toRingHom →* ModGL TwistTag.D4.tag K :=
    (adjointGroup d4 K).subtype.comp (twistedGroup σ.toRingHom).subtype
  have hu : ∀ c : k, ι (φ (sl2Upper c)) ∈ a2slFix σ d := fun c => by
    have e : φ (sl2Upper c) = slShort σ.toRingHom hσ (sl2Upper (c : K)) := by
      simp only [φ, MonoidHom.comp_apply, a2sl_map_upper]
    rw [e]
    exact a2sl_upper_fixed h c.2
  have hl : ∀ c : k, ι (φ (sl2Lower c)) ∈ a2slFix σ d := fun c => by
    have e : φ (sl2Lower c) = slShort σ.toRingHom hσ (sl2Lower (c : K)) := by
      simp only [φ, MonoidHom.comp_apply, a2sl_map_lower]
    rw [e]
    exact a2sl_lower_fixed h c.2
  have hT : ∀ y : Matrix.SpecialLinearGroup (Fin 2) k, ι (φ y) ∈ a2slFix σ d := by
    intro y
    obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod y
    simp only [map_mul]
    exact mul_mem (mul_mem (mul_mem (hl e) (hu a)) (hl b)) (hu c)
  refine ⟨φ.range, ?_, ?_⟩
  · have hcard : Nat.card k = q :=
      CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom h.two_le h.card h.frob
    have h4 : 4 ≤ Nat.card k := by
      have := h.two_le
      have := h.mod3
      omega
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect
        (CFSG.LinearGroups.exists_finset_card_eq_four h4)
    have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have : Nontrivial φ.range := by
      have hne : φ (sl2Upper (1 : k)) ≠ 1 := by
        have e : φ (sl2Upper (1 : k)) = slShort σ.toRingHom hσ (sl2Upper (1 : K)) := by
          simp only [φ, MonoidHom.comp_apply, a2sl_map_upper]
          rfl
        rw [e, ← map_one (slShort σ.toRingHom hσ)]
        intro h1
        have h2 := slShort_injective hσ h1
        have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
          (M : Matrix (Fin 2) (Fin 2) K) 0 1) h2
        simp [coe_sl2Upper] at h3
      exact ⟨⟨⟨φ (sl2Upper (1 : k)), _, rfl⟩, 1, fun h1 => hne (congrArg Subtype.val h1)⟩⟩
    exact Group.IsPerfect.not_isSolvable φ.range
  · rintro x ⟨y, rfl⟩
    exact hT y

end Short

end CFSG.GH74.GLS.Stage2.Bender.Thm1
