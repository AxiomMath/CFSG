module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Coeffs

variable {L : Type} [Field L]

theorem splitLine_commute_coeffs {A : Type*} [Ring A] [Algebra L A] {g a b : A} {t₁ t₂ : L}
    (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (h₁₂ : t₁ ≠ t₂)
    (hc₁ : g * (1 + t₁ • a + t₁ ^ 2 • b) = (1 + t₁ • a + t₁ ^ 2 • b) * g)
    (hc₂ : g * (1 + t₂ • a + t₂ ^ 2 • b) = (1 + t₂ • a + t₂ ^ 2 • b) * g) :
    g * a = a * g ∧ g * b = b * g := by
  have key : ∀ t : L, g * (1 + t • a + t ^ 2 • b) - (1 + t • a + t ^ 2 • b) * g =
      t • (g * a - a * g) + t ^ 2 • (g * b - b * g) := by
    intro t
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
    abel
  have e₁ : t₁ • (g * a - a * g) + t₁ ^ 2 • (g * b - b * g) = 0 := by
    rw [← key, sub_eq_zero.2 hc₁]
  have e₂ : t₂ • (g * a - a * g) + t₂ ^ 2 • (g * b - b * g) = 0 := by
    rw [← key, sub_eq_zero.2 hc₂]
  have e₃ : (t₁ * t₂ * (t₁ - t₂)) • (g * b - b * g) = 0 := by
    have h : t₂ • (t₁ • (g * a - a * g) + t₁ ^ 2 • (g * b - b * g)) -
        t₁ • (t₂ • (g * a - a * g) + t₂ ^ 2 • (g * b - b * g)) =
          (t₁ * t₂ * (t₁ - t₂)) • (g * b - b * g) := by
      module
    rw [← h, e₁, e₂]
    simp only [smul_zero, sub_zero]
  have hb : g * b - b * g = 0 :=
    (smul_eq_zero.1 e₃).resolve_left (mul_ne_zero (mul_ne_zero h₁ h₂) (sub_ne_zero.2 h₁₂))
  rw [hb, smul_zero, add_zero] at e₁
  have ha : g * a - a * g = 0 := (smul_eq_zero.1 e₁).resolve_left h₁
  exact ⟨sub_eq_zero.1 ha, sub_eq_zero.1 hb⟩

end Coeffs

section Fix

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem langDatum_step_injective (D : LangDatum τ L) : Function.Injective D.step := by
  obtain ⟨Fr, -, P, -, hΦ⟩ := D.steinberg
  intro x y hxy
  have h1 : (MulAut.conj D.n) (D.Φ x) = (MulAut.conj D.n) (D.Φ y) := hxy
  have h2 := (MulAut.conj D.n).injective h1
  rw [hΦ, hΦ] at h2
  have h3 : Units.map (entrywiseHom Fr) x = Units.map (entrywiseHom Fr) y := by
    have := congrArg (fun g => P⁻¹ * g * P) h2
    simpa [mul_assoc] using this
  exact Units.map_injective (f := entrywiseHom Fr) (entrywise_injective Fr) h3


theorem splitLine_step_injective : Function.Injective S.D.step :=
  langDatum_step_injective S.D

theorem splitLine_spec {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = S.D.q) {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ i j, i ≠ j → S.ρ (σ i j) = σ (π i) (π j)) :
    (∃ H : SL(3, L), ∀ X : SL(3, L), S.D.step (ρ X) = ρ X ↔
      ∃ Y : SL(3, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) ∧
    ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) ≤ S.Γ ∧
    ⁅ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _), ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _)⁆ =
      ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
  obtain ⟨ℓ, f, hℓ, -, hf, hq⟩ := exists_char_pow S
  obtain ⟨Fr, hFr, -⟩ := S.D.steinberg
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => by rw [hFr, hq]
  have hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L, S.D.step (pinnedX τ L (σ i j) c) =
      pinnedX τ L (σ (π i) (π j)) ((b : L) * Fr c) := by
    intro i j hij
    obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S (h.isRoot i j hij)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hμ c, hπ i j hij, Units.val_mk0, hFr]
  obtain ⟨hH, -, hqs, -⟩ := h.fix_split hinj hℓ hf (k := k) (hk.trans hq) le_rfl Fr hFr'
    S.D.step (splitLine_step_injective S) π hΨ
  have hperf : ⁅ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _),
      ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _)⁆ =
        ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) :=
    Subgroup.isPerfect_iff.mp hqs.1
  refine ⟨hH, ?_, hperf⟩
  have hM : ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) ≤ S.D.model :=
    inf_le_inf_right _ h.range_le_adjointGroup
  rw [← hperf]
  exact Subgroup.commutator_mono hM hM

theorem splitLine_map_injective {k : Type} [Field k] [Algebra k L] :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 3) (algebraMap k L)) := by
  intro A B hAB
  ext i j
  have h := congrArg (fun M : SL(3, L) => (M : Matrix (Fin 3) (Fin 3) L) i j) hAB
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at h
  exact (algebraMap k L).injective h

theorem splitLine_dvd_card_SL {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hpq : p ∣ Nat.card k ^ 2 + Nat.card k + 1) : p ∣ Nat.card (SL(3, k)) := by
  classical
  let _ := Fintype.ofFinite k
  have hq1 : 1 ≤ Nat.card k := Nat.card_pos
  have hGL : Nat.card (GL (Fin 3) k) =
      (Nat.card k ^ 3 - 1) * (Nat.card k ^ 3 - Nat.card k) *
        (Nat.card k ^ 3 - Nat.card k ^ 2) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_three, ← Nat.card_eq_fintype_card]
    simp
  have hcube : Nat.card k ^ 3 - 1 = (Nat.card k - 1) * (Nat.card k ^ 2 + Nat.card k + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card k = m + 1 := ⟨Nat.card k - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hdvd : p ∣ Nat.card (SL(3, k)) * Nat.card kˣ := by
    rw [Matrix.card_SL_mul_card_units, hGL, hcube]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left hpq _) _) _
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact h
  · exfalso
    rw [Nat.card_units] at h
    have h3 : p ∣ Nat.card k ^ 2 + Nat.card k + 1 - (Nat.card k - 1) * (Nat.card k + 2) :=
      Nat.dvd_sub hpq (Dvd.dvd.mul_right h _)
    have he : Nat.card k ^ 2 + Nat.card k + 1 - (Nat.card k - 1) * (Nat.card k + 2) = 3 := by
      obtain ⟨m, hm⟩ : ∃ m, Nat.card k = m + 1 := ⟨Nat.card k - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rw [he] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)

theorem splitLine_exists_orderOf {k : Type} [Field k] [Finite k] [Algebra k L]
    {ρ : SL(3, L) →* ModGL τ L} (hinj : Function.Injective ρ) {H : SL(3, L)}
    (hH : ∀ X : SL(3, L), S.D.step (ρ X) = ρ X ↔
      ∃ Y : SL(3, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹)
    (hp3 : p ≠ 3) (hpq : p ∣ Nat.card k ^ 2 + Nat.card k + 1) :
    ∃ x ∈ ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _), orderOf x = p := by
  classical
  have : Fact p.Prime := ⟨S.hp⟩
  let φ : SL(3, k) →* ModGL τ L :=
    ρ.comp ((MulAut.conj H).toMonoidHom.comp (Matrix.SpecialLinearGroup.map (algebraMap k L)))
  have hφinj : Function.Injective φ :=
    hinj.comp ((MulAut.conj H).injective.comp (splitLine_map_injective (L := L)))
  obtain ⟨Y₀, hY₀⟩ := exists_prime_orderOf_dvd_card' p (splitLine_dvd_card_SL S.hp hp3 hpq)
  refine ⟨φ Y₀, ⟨⟨_, rfl⟩, (hH _).2 ⟨Y₀, rfl⟩⟩, ?_⟩
  rw [orderOf_injective φ hφinj Y₀, hY₀]

theorem splitLine_map_transvection {k : Type} [Field k] [Algebra k L] {i j : Fin 3}
    (hij : i ≠ j) (t : k) :
    Matrix.SpecialLinearGroup.map (algebraMap k L) (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij (algebraMap k L t) := by
  ext a b
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    CFSG.LinearGroups.coe_transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem splitLine_commute_range (hτ : τ ≠ .G2) {k : Type} [Field k] [Algebra k L]
    {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (h : IsSLFrame ρ σ)
    {H : SL(3, L)} (hk3 : ∃ t : k, t ≠ 0 ∧ t ≠ 1) {g : ModGL τ L}
    (hg : ∀ Y : SL(3, k),
      Commute g (ρ (H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹))) :
    ∀ x ∈ ρ.range, Commute g x := by
  classical
  obtain ⟨t₀, ht₀, ht₁⟩ := hk3
  have htr : ∀ (i j : Fin 3) (hij : i ≠ j) (c : L),
      Commute g (ρ (H * Matrix.SpecialLinearGroup.transvection hij c * H⁻¹)) := by
    intro i j hij c
    obtain ⟨ε, hε⟩ := h.transv i j hij
    obtain ⟨a, b, -, -, hab⟩ :=
      conj_map_pinnedX_expand hτ (RingHom.id L) (ρ H) ε.ne_zero (σ i j)
    have hval : ∀ c : L, ((ρ (H * Matrix.SpecialLinearGroup.transvection hij c * H⁻¹) :
        ModGL τ L) : Module.End L (RootModule τ L)) = 1 + c • a + c ^ 2 • b := by
      intro c
      have e1 : ρ (H * Matrix.SpecialLinearGroup.transvection hij c * H⁻¹) =
          Units.map (entrywiseHom (RingHom.id L))
            (ρ H * pinnedX τ L (σ i j) ((ε : L) * c) * (ρ H)⁻¹) := by
        rw [map_mul, map_mul, map_inv, hε c]
        exact (Units.ext (entrywise_id _)).symm
      rw [e1, hab c]
      rfl
    have hk : ∀ t : k, (g : Module.End L (RootModule τ L)) *
        (1 + (algebraMap k L t) • a + (algebraMap k L t) ^ 2 • b) =
          (1 + (algebraMap k L t) • a + (algebraMap k L t) ^ 2 • b) * g := by
      intro t
      have h1 := (hg (Matrix.SpecialLinearGroup.transvection hij t)).eq
      rw [splitLine_map_transvection] at h1
      have h2 := congrArg (fun m : ModGL τ L => (m : Module.End L (RootModule τ L))) h1
      simp only [Units.val_mul] at h2
      rwa [hval] at h2
    have hne1 : algebraMap k L 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
    have hne2 : algebraMap k L t₀ ≠ 0 := fun h0 => ht₀ ((map_eq_zero _).1 h0)
    have hne12 : algebraMap k L 1 ≠ algebraMap k L t₀ :=
      fun h0 => ht₁ ((algebraMap k L).injective h0).symm
    obtain ⟨ha, hb⟩ := splitLine_commute_coeffs hne1 hne2 hne12 (hk 1) (hk t₀)
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [hval c]
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, ha, hb]
  have hall : ∀ X : SL(3, L), Commute g (ρ (H * X * H⁻¹)) := by
    intro X
    have hX : X ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 L) := by
      rw [CFSG.LinearGroups.special_linear_elementary_generation]
      exact Subgroup.mem_top X
    induction hX using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, j, hij, c, rfl⟩ := hx
      exact htr i j hij c
    | one => simp
    | mul x y _ _ hx hy =>
      have e : H * (x * y) * H⁻¹ = (H * x * H⁻¹) * (H * y * H⁻¹) := by group
      rw [e, map_mul]
      exact hx.mul_right hy
    | inv x _ hx =>
      have e : H * x⁻¹ * H⁻¹ = (H * x * H⁻¹)⁻¹ := by group
      rw [e, map_inv]
      exact hx.inv_right
  rintro _ ⟨X, rfl⟩
  have e : X = H * (H⁻¹ * X * H) * H⁻¹ := by group
  rw [e]
  exact hall _

end Fix

end CFSG.HardMathSupport.Timmesfeld.CrossChar
