module

public import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

section Abstract

variable {K : Type} [Field K]

theorem l3_exists_psl2_section [CharP K 2] {D Q : Type} [Group D] [Group Q] [IsSimpleGroup Q]
    (hab : ∃ a b : Q, a * b ≠ b * a) (f : D →* Q) (hf : Function.Surjective f)
    (ψ : D →* GL (Fin 2) K) (hψ : ∀ x : D, ψ x = 1 → x ^ 2 = 1) :
    ∃ (Hb : Subgroup (PSL2MatrixGroup K)) (ρ : Hb →* Q), Function.Surjective ρ := by
  let δ : D →* Kˣ := Matrix.GeneralLinearGroup.det.comp ψ
  let D₁ : Subgroup D := δ.ker
  have hD₁n : D₁.Normal := δ.normal_ker
  have hcomm : ∀ x y : D, ⁅x, y⁆ ∈ D₁ := fun x y => by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have hfD₁ : D₁.map f = ⊤ := by
    rcases (hD₁n.map f hf).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab'⟩ := hab
      obtain ⟨x, rfl⟩ := hf a
      obtain ⟨y, rfl⟩ := hf b
      apply hab'
      have h1 : f ⁅x, y⁆ ∈ D₁.map f := ⟨_, hcomm x y, rfl⟩
      rw [h, Subgroup.mem_bot, map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    · exact h
  let f₁ : D₁ →* Q := f.comp D₁.subtype
  have hf₁ : Function.Surjective f₁ := fun q => by
    have : q ∈ D₁.map f := by rw [hfD₁]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hdetD₁ : ∀ x : D₁,
      ((ψ (x : D) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := fun x => by
    have h := x.2
    rw [MonoidHom.mem_ker] at h
    have := congrArg (fun u : Kˣ => (u : K)) h
    simpa [δ, Matrix.GeneralLinearGroup.val_det_apply] using this
  let φ₀ : D₁ →* Matrix.SpecialLinearGroup (Fin 2) K :=
    { toFun := fun x => ⟨(ψ (x : D) : GL (Fin 2) K), hdetD₁ x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp
        rfl }
  let φ : D₁ →* PSL2MatrixGroup K :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).comp φ₀
  have hker_sq : ∀ x : D₁, φ x = 1 → (x : D) ^ 2 = 1 := fun x hx => by
    have h1 : φ₀ x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
      (QuotientGroup.eq_one_iff _).1 hx
    rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.mem_bot] at h1
    apply hψ
    apply Units.ext
    exact congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K)) h1
  have hker : φ.ker ≤ f₁.ker := by
    rcases (φ.normal_ker.map f₁ hf₁).eq_bot_or_eq_top with h | h
    · intro x hx
      have : f₁ x ∈ (φ.ker).map f₁ := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have hsq : ∀ q : Q, q * q = 1 := fun q => by
        have : q ∈ (φ.ker).map f₁ := by rw [h]; trivial
        obtain ⟨x, hx, rfl⟩ := this
        rw [← map_mul]
        have h2 : x * x = 1 := Subtype.ext (by simpa [sq] using hker_sq x hx)
        rw [h2, map_one]
      obtain ⟨a, b, hab'⟩ := hab
      apply hab'
      have ha := inv_eq_of_mul_eq_one_right (hsq a)
      have hb := inv_eq_of_mul_eq_one_right (hsq b)
      have hab2 := inv_eq_of_mul_eq_one_right (hsq (a * b))
      rw [mul_inv_rev, ha, hb] at hab2
      exact hab2.symm
  have hφs : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  refine ⟨φ.range, φ.rangeRestrict.liftOfSurjective hφs
    ⟨f₁, (MonoidHom.ker_rangeRestrict φ).le.trans hker⟩, fun q => ?_⟩
  obtain ⟨x, hx⟩ := hf₁ q
  exact ⟨φ.rangeRestrict x, by
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    exact hx⟩

end Abstract

theorem l3_card_of_quotient_psl2_even {m : ℕ} (hm : m ≠ 0) {S : Type} [Group S]
    [IsSimpleGroup S] (hab : ∃ a b : S, a * b ≠ b * a)
    (σ : PSL2MatrixGroup (GaloisField 2 m) →* S) (hσ : Function.Surjective σ) :
    ∃ m' : ℕ, 2 ≤ m' ∧ Nat.card S = 2 ^ m' * (4 ^ m' - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm
  by_cases h1 : m = 1
  · exfalso
    subst h1
    apply not_isSolvable_of_simple_nonabelian hab
    have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 2 ^ 1 * 3 ^ 1 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard]
      norm_num
    have hsl := isSolvable_of_card_two_three hc
    have hpsl : Group.IsSolvable (PSL2MatrixGroup (GaloisField 2 1)) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1))))
    exact Group.isSolvable_of_surjective hσ
  · refine ⟨m, by omega, ?_⟩
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsimple : IsSimpleGroup (PSL2MatrixGroup (GaloisField 2 m)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hcard]; exact h4)
    have hinj := injective_of_surjective_simple σ hσ
    rw [← Nat.card_congr (Equiv.ofBijective σ ⟨hinj, hσ⟩),
      Nat.card_congr (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 m)).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard, ← pow_mul, mul_comm m 2,
      pow_mul]
    norm_num

section Dickson


theorem l3_card_simple_section_psl2_even {F : Type} [Field F] [Finite F] {f : ℕ} (hf : f ≠ 0)
    (hF : Nat.card F = 2 ^ f) (Hb : Subgroup (PSL2MatrixGroup F)) {S : Type} [Group S]
    [IsSimpleGroup S] (hab : ∃ a b : S, a * b ≠ b * a) (ρ : ↥Hb →* S)
    (hρ : Function.Surjective ρ) :
    Nat.card S = 60 ∨ ∃ m : ℕ, 2 ≤ m ∧ Nat.card S = 2 ^ m * (4 ^ m - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ∀ {m : ℕ}, m ∣ f → m ≠ 0 := fun {m} hm h0 => hf (by
    rw [h0] at hm
    exact zero_dvd_iff.1 hm)
  rcases psl2_subgroup_dichotomy hF Hb with hsolv | hA5 | ⟨m, hm, hPSL⟩ | ⟨m, hm, hPGL⟩
  · exact absurd (Group.isSolvable_of_surjective hρ) (not_isSolvable_of_simple_nonabelian hab)
  · left
    obtain ⟨e⟩ := hA5
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hs : Function.Surjective (ρ.comp e.symm.toMonoidHom) := hρ.comp e.symm.surjective
    have hinj := injective_of_surjective_simple (ρ.comp e.symm.toMonoidHom) hs
    rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hs⟩), Nat.card_eq_fintype_card,
      card_alternatingGroup, Fintype.card_fin]
    decide
  · right
    obtain ⟨e⟩ := hPSL
    exact l3_card_of_quotient_psl2_even (hne hm) hab (ρ.comp e.symm.toMonoidHom)
      (hρ.comp e.symm.surjective)
  · right
    obtain ⟨e⟩ := hPGL
    have hm0 : m ≠ 0 := hne (Dvd.dvd.trans (dvd_mul_left m 2) hm)
    let σ : PSL2MatrixGroup (GaloisField 2 m) →* S :=
      (ρ.comp e.symm.toMonoidHom).comp
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField 2 m))
    have hσ : Function.Surjective σ :=
      (hρ.comp e.symm.surjective).comp
        (CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.toPGL_surjective (GaloisField 2 m))
    exact l3_card_of_quotient_psl2_even hm0 hab σ hσ

end Dickson

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
