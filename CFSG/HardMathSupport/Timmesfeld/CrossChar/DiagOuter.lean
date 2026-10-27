module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagField
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms (higher_linear_prime_semilinear_field_descent')
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)

section Subfield

variable {n : ℕ} {F : Type} [Field F]

theorem conj_mem_range_linearSubfieldInclusion (σ : F ≃+* F) {x t : projectiveSL n F}
    (hx : fieldAut n F σ x = x)
    (ht : t ∈ (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range) :
    x * t * x⁻¹ ∈ (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range := by
  have hk : ∀ c, c ∈ semilinearFixedSubfield σ ↔ σ c = c := fun c => RingHom.mem_eqLocusField
  obtain ⟨g, rfl⟩ := proj_surjective n F x
  obtain ⟨s, hs, rfl⟩ := mem_range_linearSubfieldInclusion.1 ht
  rw [fieldAut_proj, proj_eq_proj_iff] at hx
  set z := (SpecialLinearGroup.map σ.toRingHom g)⁻¹ * g with hz
  have hzc := Subgroup.mem_center_iff.1 (scalars_le_center n F hx)
  have hg : SpecialLinearGroup.map σ.toRingHom g = g * z⁻¹ := by
    rw [hz, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have hs' : SpecialLinearGroup.map σ.toRingHom s = s := by
    ext i j
    simpa [SpecialLinearGroup.map_apply_coe] using (hk _).1 (hs i j)
  have key : SpecialLinearGroup.map σ.toRingHom (g * s * g⁻¹) = g * s * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg, hs']
    have hzs : z⁻¹ * s * z = s := by rw [mul_assoc, hzc s, inv_mul_cancel_left]
    calc g * z⁻¹ * s * (g * z⁻¹)⁻¹ = g * (z⁻¹ * s * z) * g⁻¹ := by group
      _ = g * s * g⁻¹ := by rw [hzs]
  refine mem_range_linearSubfieldInclusion.2 ⟨g * s * g⁻¹, fun i j => (hk _).2 ?_, ?_⟩
  · have := congrArg (fun m : SpecialLinearGroup (Fin n) F => (m : Matrix (Fin n) (Fin n) F) i j)
      key
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
    exact this
  · rw [map_mul, map_mul, map_inv]

theorem isQuasisimple_range_linearSubfieldInclusion (hn : 3 ≤ n) (k : Subfield F) :
    CFSG.IsQuasisimple (linearSubfieldInclusion n k).range := by
  obtain ⟨hs, hna⟩ := simple_nonabelian_range_linearSubfieldInclusion hn k
  have hab : ∃ a b : (linearSubfieldInclusion n k).range, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hna h
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hab).1

theorem exists_orderOf_projectiveSL_eq {E : Type*} [Field E] {p : ℕ} (hp : p.Prime)
    (hn : 3 ≤ n) {ζ : E} (hζ : IsPrimitiveRoot ζ p) : ∃ y : projectiveSL n E, orderOf y = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  let v : Fin n → E := fun i => if i = ⟨0, by omega⟩ then ζ else
    if i = ⟨1, by omega⟩ then ζ⁻¹ else 1
  have hdet : (Matrix.diagonal v).det = 1 := by
    rw [Matrix.det_diagonal]
    rw [Finset.prod_eq_mul (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ hne]
    · simp [v, hζ0]
    · intro c _ hc
      simp [v, hc.1, hc.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  let s : SpecialLinearGroup (Fin n) E := ⟨Matrix.diagonal v, hdet⟩
  have hsp : s ^ p = 1 := by
    apply Subtype.ext
    change (Matrix.diagonal v) ^ p = 1
    rw [Matrix.diagonal_pow]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.one_apply_eq]
      by_cases h0 : i = ⟨0, by omega⟩
      · simp [v, h0, hζ.pow_eq_one]
      · by_cases h1 : i = ⟨1, by omega⟩
        · simp [v, h1, hne.symm, inv_pow, hζ.pow_eq_one]
        · simp [v, h0, h1]
    · simp [hij]
  refine ⟨proj n E s, orderOf_eq_prime (by rw [← map_pow, hsp, map_one]) fun h1 => ?_⟩
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h1)
  have e0 := congrFun (congrFun hc ⟨0, by omega⟩) ⟨0, by omega⟩
  have e2 := congrFun (congrFun hc ⟨2, by omega⟩) ⟨2, by omega⟩
  have h20 : (⟨2, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp
  have h21 : (⟨2, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  simp only [s, v, Matrix.diagonal_apply_eq, scalar_apply, ite_true, h20, h21, ite_false] at e0 e2
  exact hζ.ne_one hp.one_lt (e0.trans e2.symm)

theorem dvd_card_projectiveSL_of_dvd_card_sub_one {E : Type*} [Field E] [Finite E] {p : ℕ}
    (hp : p.Prime) (hn : 3 ≤ n) (h : p ∣ Nat.card E - 1) : p ∣ Nat.card (projectiveSL n E) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Eˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζ : IsPrimitiveRoot (x : E) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (hx ▸ IsPrimitiveRoot.orderOf x)
  obtain ⟨y, hy⟩ := exists_orderOf_projectiveSL_eq hp hn hζ
  rw [← hy]
  exact orderOf_dvd_natCard y

theorem dvd_sub_one_of_dvd_pow_self_sub_one {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q)
    (h : p ∣ q ^ p - 1) : p ∣ q - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, ZMod.pow_card] at h
  rwa [Nat.cast_sub hq]

end Subfield

section Outer

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem localDeltaIn_eq_bot_of_conj_fieldAut (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    {σ : F ≃+* F} (hσ : orderOf σ = p) (hpk : p ∣ Nat.card (semilinearFixedSubfield σ) - 1)
    {H D : Subgroup (MulAut (projectiveSL n F))} (hH : innerAut (projectiveSL n F) ≤ H)
    {x : MulAut (projectiveSL n F)} (hx : x ∈ D) (h : MulAut (projectiveSL n F))
    (hxh : x = h * fieldAut n F σ * h⁻¹) : localDeltaIn p H D = ⊥ := by
  set k := semilinearFixedSubfield σ with hkdef
  have hk : ∀ c, c ∈ k ↔ σ c = c := fun c => RingHom.mem_eqLocusField
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F) hn
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h1 : fieldAut n F σ = 1 := by
      calc fieldAut n F σ = h⁻¹ * (h * fieldAut n F σ * h⁻¹) * h := by group
        _ = 1 := by rw [← hxh, mul_one, inv_mul_cancel]
    have h2 : σ = 1 := fieldAut_injective hn (by rw [h1, map_one])
    rw [h2, orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  refine localDeltaIn_eq_bot_of_conj_normal_quasisimple_fixSub hp hinj hH hx hx1 h
    (fieldAut n F σ) hxh (linearSubfieldInclusion n k).range ?_ ?_
    (isQuasisimple_range_linearSubfieldInclusion hn k) ?_ ?_
  · rintro _ ⟨y, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).1 hc) y
  · intro a ha t ht
    exact conj_mem_range_linearSubfieldInclusion σ ha ht
  · rw [← Nat.card_congr (MonoidHom.ofInjective (linearSubfieldInclusion_injective
      (by omega) k)).toEquiv]
    exact dvd_card_projectiveSL_of_dvd_card_sub_one hp hn hpk
  · intro g hg hfix
    have hmem : g ∈ fixingSubgroup (MulAut (projectiveSL n F))
        ((linearSubfieldInclusion n k).range : Set (projectiveSL n F)) :=
      (mem_fixingSubgroup_iff _).2 fun y hy => hfix y hy
    rw [fixingSubgroup_range_linearSubfieldInclusion hk hn] at hmem
    have hdvd : orderOf g ∣ p := by
      rw [← hσ, ← orderOf_fieldAut hn σ]
      exact orderOf_dvd_of_mem_zpowers hmem
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hg.symm hdvd)

theorem localDeltaIn_eq_bot_of_mem_semilinear_not_linear (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F - 1) {H D : Subgroup (MulAut (projectiveSL n F))}
    (hH : innerAut (projectiveSL n F) ≤ H) {x : MulAut (projectiveSL n F)} (hx : x ∈ D)
    (hxE : x ∈ semilinearAutGroup n F) (hxD : x ∉ linearAutGroup n F) (hxp : x ^ p = 1) :
    localDeltaIn p H D = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card F (ringChar F)
  have hx1 : x ≠ 1 := fun h => hxD (h ▸ (linearAutGroup n F).one_mem)
  have hFc : Nat.card F = ringChar F ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hpf, σ, hσ, ⟨h, -, hxh⟩, hk⟩ := higher_linear_prime_semilinear_field_descent' hℓ
    f.pos hn hFc hp x hxE hxD (orderOf_eq_prime hxp hx1)
  refine localDeltaIn_eq_bot_of_conj_fieldAut hn hp hσ ?_ hH hx h hxh
  rw [hk]
  refine dvd_sub_one_of_dvd_pow_self_sub_one hp (Nat.one_le_pow _ _ hℓ.pos) ?_
  rw [← pow_mul, Nat.div_mul_cancel hpf, ← hFc]
  exact hpF

theorem localDeltaIn_eq_bot_of_not_le_linearAutGroup (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) {D : Subgroup (MulAut (projectiveSL n F))}
    (hD : IsElemAbelian p D) (hDl : ¬ D ≤ linearAutGroup n F)
    {H : Subgroup (MulAut (projectiveSL n F))} (hH : innerAut (projectiveSL n F) ≤ H) :
    localDeltaIn p H D = ⊥ := by
  obtain ⟨x, hx, hxl⟩ := IsConcreteLE.not_le_iff_exists.1 hDl
  have hxp := hD.2 x hx
  have hxE : x ∈ semilinearAutGroup n F := by
    refine mem_semilinearAutGroup_of_odd hn ?_
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hxp) with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  exact localDeltaIn_eq_bot_of_mem_semilinear_not_linear hn hp hpF hH hx hxE hxl hxp

theorem isLocallyBalancedAbs_projectiveSL_of_linear (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    (hlin : ∀ D : Subgroup (MulAut (projectiveSL n F)), IsElemAbelian p D → Nat.card D = p ^ 3 →
      D ≤ linearAutGroup n F → ∀ H : Subgroup (MulAut (projectiveSL n F)),
        innerAut (projectiveSL n F) ≤ H → D ≤ Subgroup.normalizer (H : Set _) →
          localDeltaIn p H D = ⊥) :
    IsLocallyBalancedAbs p 3 (projectiveSL n F) := by
  intro D hD hcard H hH hDH
  by_cases hDl : D ≤ linearAutGroup n F
  · exact hlin D hD hcard hDl H hH hDH
  · exact localDeltaIn_eq_bot_of_not_le_linearAutGroup hn hp hp2 hpF hD hDl hH

end Outer

end CFSG.HardMathSupport.Timmesfeld.CrossChar
