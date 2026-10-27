module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

private theorem le_of_pow_dvd_prod_GL {q : ℕ} (hq : q.Prime) {m j : ℕ}
    (h : q ^ j ∣ ∏ i : Fin m, (q ^ m - q ^ (i : ℕ))) : j ≤ m * (m - 1) / 2 := by
  have hfac : ∏ i : Fin m, (q ^ m - q ^ (i : ℕ)) =
      q ^ (m * (m - 1) / 2) * ∏ i : Fin m, (q ^ (m - (i : ℕ)) - 1) := by
    have h1 : ∀ i : Fin m, q ^ m - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (m - (i : ℕ)) - 1) := by
      intro i
      have hi : (i : ℕ) + (m - (i : ℕ)) = m := by omega
      rw [Nat.mul_sub_one, ← pow_add, hi]
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) m,
      Finset.sum_range_id]
  have hcop : Nat.Coprime (q ^ j) (∏ i : Fin m, (q ^ (m - (i : ℕ)) - 1)) := by
    refine Nat.Coprime.prod_right fun i _ => Nat.Coprime.pow_left j ?_
    have hs : 1 ≤ m - (i : ℕ) := by have := i.2; omega
    have h1 : Nat.Coprime (q ^ (m - (i : ℕ))) (q ^ (m - (i : ℕ)) - 1) :=
      (Nat.coprime_self_sub_right (Nat.one_le_pow _ _ hq.pos)).2 (Nat.coprime_one_right _)
    exact Nat.Coprime.coprime_dvd_left (dvd_pow_self q (by omega)) h1
  rw [hfac] at h
  exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).1 (hcop.dvd_of_dvd_mul_right h)

private theorem card_linearEquiv_eq {q : ℕ} [Fact q.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod q) V] [Module.Finite (ZMod q) V] {m : ℕ}
    (hfr : Module.finrank (ZMod q) V = m) :
    Nat.card (V ≃ₗ[ZMod q] V) = ∏ i : Fin m, (q ^ m - q ^ (i : ℕ)) := by
  let b : Module.Basis (Fin m) (ZMod q) V := Module.finBasisOfFinrankEq (ZMod q) V hfr
  calc Nat.card (V ≃ₗ[ZMod q] V)
      = Nat.card (LinearMap.GeneralLinearGroup (ZMod q) V) :=
        (Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod q) V).toEquiv).symm
    _ = Nat.card (GL (Fin m) (ZMod q)) :=
        (Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv).symm
    _ = _ := by rw [Matrix.card_GL_field, ZMod.card]

theorem card_le_of_isPGroup_mulAut {A : Type*} [CommGroup A] [Finite A] {q : ℕ} (hq : q.Prime)
    (hexp : ∀ a : A, a ^ q = 1) {m : ℕ} (hcard : Nat.card A = q ^ m)
    (P : Subgroup (MulAut A)) (hP : IsPGroup q P) : Nat.card P ≤ q ^ (m * (m - 1) / 2) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  letI : Module (ZMod q) (Additive A) :=
    AddCommGroup.zmodModule (n := q) fun x => by
      change Additive.ofMul (Additive.toMul x ^ q) = 0
      rw [hexp]; rfl
  haveI : Fintype (Additive A) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod q) (Additive A) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod q) (Additive A) = m := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod q) (V := Additive A)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h1
    have h2 : Nat.card (Additive A) = Nat.card A := rfl
    rw [h2, hcard] at h1
    exact (Nat.pow_right_injective hq.two_le h1).symm
  let eLin : (Additive A ≃+ Additive A) ≃ (Additive A ≃ₗ[ZMod q] Additive A) :=
    { toFun := fun e => e.toLinearEquiv fun c x => ZMod.map_smul e c x
      invFun := fun f => f.toAddEquiv
      left_inv := fun e => by ext x; rfl
      right_inv := fun f => by ext x; rfl }
  have hGL : Nat.card (MulAut A) = ∏ i : Fin m, (q ^ m - q ^ (i : ℕ)) := by
    calc Nat.card (MulAut A)
        = Nat.card (Additive A ≃+ Additive A) := Nat.card_congr MulEquiv.toAdditive
      _ = Nat.card (Additive A ≃ₗ[ZMod q] Additive A) := Nat.card_congr eLin
      _ = _ := by exact card_linearEquiv_eq (q := q) (V := Additive A) hfr
  haveI : Finite (MulAut A) :=
    Finite.of_injective (fun e : MulAut A => (e : A → A)) fun e₁ e₂ h =>
      MulEquiv.ext (congrFun h)
  obtain ⟨j, hj⟩ := hP.exists_card_eq
  have hdvd : q ^ j ∣ ∏ i : Fin m, (q ^ m - q ^ (i : ℕ)) := by
    rw [← hj, ← hGL]; exact Subgroup.card_subgroup_dvd_card P
  rw [hj]
  exact Nat.pow_le_pow_right hq.pos (le_of_pow_dvd_prod_GL hq hdvd)

theorem exists_index_le_of_elemAb {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    (T A B : Subgroup X) (hT : IsPGroup q T) (hBA : B ≤ A)
    (hBn : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B)
    (hTA : ∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hTB : ∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ ∈ B)
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) (hpow : ∀ a ∈ A, a ^ q ∈ B)
    (k : ℕ) (hcard : Nat.card A ≤ q ^ k * Nat.card B) :
    ∃ C : Subgroup X, C ≤ T ∧ (∀ c ∈ C, ∀ a ∈ A, a⁻¹ * (c * a * c⁻¹) ∈ B) ∧
      Nat.card T ≤ q ^ (k * (k - 1) / 2) * Nat.card C := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set N : Subgroup A := B.subgroupOf A with hN
  haveI hNn : N.Normal :=
    ⟨fun n hn g => by
      rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hBn g g.2 n hn⟩
  letI : CommGroup (A ⧸ N) :=
    { (inferInstance : Group (A ⧸ N)) with
      mul_comm := fun x y => by
        induction x using QuotientGroup.induction_on with | H a => ?_
        induction y using QuotientGroup.induction_on with | H a' => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN,
          Subgroup.mem_subgroupOf]
        have h := hcomm _ (A.inv_mem a'.2) _ (A.inv_mem a.2)
        have e : (((a * a')⁻¹ * (a' * a) : A) : X) =
            (a' : X)⁻¹ * (a : X)⁻¹ * ((a' : X)⁻¹)⁻¹ * ((a : X)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]; group
        rw [e]
        exact h }
  have hexpQ : ∀ x : A ⧸ N, x ^ q = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with | H a => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    simpa using hpow a a.2
  let conjA : T → A →* A := fun t =>
    { toFun := fun a => ⟨t * a * t⁻¹, hTA t t.2 a a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a a' => by ext; simp [mul_assoc] }
  have hconjN : ∀ t : T, N ≤ N.comap (conjA t) := by
    intro t n hn
    rw [Subgroup.mem_comap, hN, Subgroup.mem_subgroupOf]
    rw [hN, Subgroup.mem_subgroupOf] at hn
    exact hTB t t.2 n hn
  let actQ : T → (A ⧸ N) →* (A ⧸ N) := fun t => QuotientGroup.map N N (conjA t) (hconjN t)
  have hactQ : ∀ (t : T) (a : A), actQ t (a : A ⧸ N) = ((conjA t a : A) : A ⧸ N) := fun _ _ => rfl
  have hact_mul : ∀ s t : T, actQ (s * t) = (actQ s).comp (actQ t) := by
    intro s t
    ext a
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hactQ]
    congr 1
    ext
    simp [conjA, mul_assoc]
  have hact_one : actQ 1 = MonoidHom.id _ := by
    ext a
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hactQ, MonoidHom.id_apply]
    congr 1
    ext
    simp [conjA]
  let φ : T →* MulAut (A ⧸ N) :=
    { toFun := fun t => MonoidHom.toMulEquiv (actQ t) (actQ t⁻¹)
          (by rw [← hact_mul, inv_mul_cancel, hact_one])
          (by rw [← hact_mul, mul_inv_cancel, hact_one])
      map_one' := by
        ext x
        show actQ 1 x = x
        rw [hact_one, MonoidHom.id_apply]
      map_mul' := fun s t => by
        ext x
        show actQ (s * t) x = actQ s (actQ t x)
        rw [hact_mul, MonoidHom.comp_apply] }
  have hφ : ∀ (t : T) (x : A ⧸ N), φ t x = actQ t x := fun _ _ => rfl
  refine ⟨φ.ker.map T.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩ a ha
    have ht' : φ t = 1 := ht
    have h1 : actQ t ((⟨a, ha⟩ : A) : A ⧸ N) = ((⟨a, ha⟩ : A) : A ⧸ N) := by
      rw [← hφ, ht']; rfl
    rw [hactQ, QuotientGroup.eq, hN, Subgroup.mem_subgroupOf] at h1
    have h2 := B.inv_mem h1
    have e : (((conjA t ⟨a, ha⟩)⁻¹ * ⟨a, ha⟩ : A) : X)⁻¹ = a⁻¹ * (t * a * t⁻¹) := by
      simp [conjA, mul_assoc]
    rw [e] at h2
    simpa using h2
  ·
    have hQp : IsPGroup q (A ⧸ N) := fun x => ⟨1, by rw [pow_one]; exact hexpQ x⟩
    obtain ⟨m, hm⟩ := hQp.exists_card_eq
    have hAB : Nat.card A = Nat.card (A ⧸ N) * Nat.card B := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
      congr 1
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
    have hBpos : 0 < Nat.card B := Nat.card_pos
    have hmk : m ≤ k := by
      rw [hAB, hm] at hcard
      exact (Nat.pow_le_pow_iff_right hq.one_lt).1 (Nat.le_of_mul_le_mul_right hcard hBpos)
    have hrange : Nat.card φ.range ≤ q ^ (k * (k - 1) / 2) := by
      have h1 := card_le_of_isPGroup_mulAut hq hexpQ hm φ.range
        (hT.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
      refine h1.trans (Nat.pow_le_pow_right hq.pos ?_)
      exact Nat.div_le_div_right (Nat.mul_le_mul hmk (Nat.sub_le_sub_right hmk 1))
    have hT1 : Nat.card T = Nat.card φ.range * Nat.card φ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    have hC : Nat.card (φ.ker.map T.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective T.subtype_injective
    rw [hC, hT1]
    exact Nat.mul_le_mul_right _ hrange

end CFSG.LocalAnalysis.GLTheoremA.H248L227
