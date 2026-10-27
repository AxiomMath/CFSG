module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Choice
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Weights

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap

section Fixed

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {V : Type*} [AddCommGroup V] [Module K V]
  (ρ : Representation K A V)

@[expose] def stabSubgroup (v : V) : Subgroup A where
  carrier := {g | ρ g v = v}
  mul_mem' := fun {g g'} hg hg' => by
    have hg1 : ρ g v = v := hg
    have hg2 : ρ g' v = v := hg'
    show ρ (g * g') v = v
    rw [map_mul, Module.End.mul_apply, hg2, hg1]
  one_mem' := by
    show ρ 1 v = v
    rw [map_one]
    rfl
  inv_mem' := fun {g} hg => by
    have hg1 : ρ g v = v := hg
    show ρ g⁻¹ v = v
    calc ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := by rw [hg1]
      _ = v := Representation.inv_self_apply ρ g v

theorem mem_wtFixedSpace_zpowers_iff {a : A} {v : V} :
    v ∈ Wt.fixedSpace ρ (Subgroup.zpowers a) ↔ ρ a v = v := by
  rw [Wt.mem_fixedSpace]
  constructor
  · intro h
    exact h a (Subgroup.mem_zpowers a)
  · intro h u hu
    exact (Subgroup.zpowers_le.mpr (show a ∈ stabSubgroup ρ v from h)) hu

theorem mem_wtFixedSpace_sup_iff {a b : A} {v : V} :
    v ∈ Wt.fixedSpace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ↔ ρ a v = v ∧ ρ b v = v := by
  rw [Wt.mem_fixedSpace]
  constructor
  · intro h
    exact ⟨h a (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)),
      h b (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))⟩
  · rintro ⟨ha, hb⟩ u hu
    exact (sup_le (Subgroup.zpowers_le.mpr (show a ∈ stabSubgroup ρ v from ha))
      (Subgroup.zpowers_le.mpr (show b ∈ stabSubgroup ρ v from hb))) hu

end Fixed

section Conf

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}

theorem conf_of_wt {A : Type} [CommGroup A] (hQ : (polarBilin Q).Nondegenerate)
    (hpK : (p : K) ≠ 0) (f : A →* ↥(orthDerived Q)) (hf : Function.Injective f)
    (hfp : ∀ a, f a ^ p = 1) (ρ : Representation K A V)
    (hρ : ∀ a v, ρ a v = ((f a : ↥(orthDerived Q)) : V ≃ₗ[K] V) v) {dW : ℕ}
    (hV : finrank K V = dW + 2) {yy zz : A} (h1 : yy ≠ 1) (h2 : zz ∉ Subgroup.zpowers yy)
    (h3 : finrank K (Wt.fixedSpace ρ (Subgroup.zpowers yy)) = dW)
    (h4 : finrank K (Wt.fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz)) + 2 = dW)
    (h5 : ∀ a : A, (∀ v ∈ Wt.fixedSpace ρ (Subgroup.zpowers yy), ρ a v = v) →
      a ∈ Subgroup.zpowers yy)
    (h6 : ∀ v : V, ρ zz (ρ yy v - v) = ρ yy v - v)
    (h7 : finrank K (Wt.fixedSpace ρ ⊤) <
      finrank K (Wt.fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz))) :
    f yy ≠ 1 ∧ f zz ∉ Subgroup.zpowers (f yy) ∧
      finrank K (othersSpace (f yy : V ≃ₗ[K] V).toLinearMap (X - 1)) = 2 ∧
      finrank K (fixedSpace (f yy : V ≃ₗ[K] V)) = dW ∧
      finrank K (fixedSpace ((f yy : V ≃ₗ[K] V) * (f zz : V ≃ₗ[K] V))) + 2 = dW ∧
      (∀ a ∈ f.range, (∀ v ∈ fixedSpace (f yy : V ≃ₗ[K] V), (a : V ≃ₗ[K] V) v = v) →
        a ∈ Subgroup.zpowers (f yy)) ∧
      (∀ v, (f zz : V ≃ₗ[K] V) ((f yy : V ≃ₗ[K] V) v - v) = (f yy : V ≃ₗ[K] V) v - v) ∧
      ∃ t ∈ f.range, ∃ u ∈ fixedSpace ((f yy : V ≃ₗ[K] V) * (f zz : V ≃ₗ[K] V)),
        (t : V ≃ₗ[K] V) u ≠ u := by
  set x : V ≃ₗ[K] V := (f yy : V ≃ₗ[K] V) with hx
  set y : V ≃ₗ[K] V := (f zz : V ≃ₗ[K] V) with hy
  have hoi : ∀ a : A, OddOrderIsometry Q p (f a : V ≃ₗ[K] V) := fun a =>
    { mem := orthDerived_le_orthogonalGroup' Q (f a).2
      pow_eq_one := congrArg Subtype.val (hfp a)
      cast_ne_zero := hpK
      regular := fun v hv => eq_zero_of_polar_eq_zero hQ hv }
  have hxo := hoi yy
  have hyo := hoi zz
  have hxy : x * y = y * x := by
    rw [hx, hy, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm]
  have hyR : ∀ v, y (x v - v) = x v - v := fun v => by
    have := h6 v
    rwa [hρ, hρ] at this
  have hfix1 : fixedSpace x = Wt.fixedSpace ρ (Subgroup.zpowers yy) := by
    ext v
    rw [mem_fixedSpace, mem_wtFixedSpace_zpowers_iff, hρ]
  have hfix2 : fixedSpace (x * y) =
      Wt.fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz) := by
    ext v
    rw [mem_wtFixedSpace_sup_iff, hρ, hρ]
    constructor
    · intro hv
      have hxv : x v = v := mem_fixedSpace.mp (fixedSpace_mul_le hxo hyo hxy hyR hv)
      refine ⟨hxv, ?_⟩
      have h := mem_fixedSpace.mp hv
      rw [hxy, LinearEquiv.mul_apply, hxv] at h
      exact h
    · rintro ⟨hxv, hyv⟩
      rw [mem_fixedSpace, LinearEquiv.mul_apply, hyv, hxv]
  refine ⟨fun h => h1 (hf (by rw [h, map_one])), ?_, ?_, ?_, ?_, ?_, hyR, ?_⟩
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact h2 (Subgroup.mem_zpowers_iff.mpr ⟨k, hf (by rw [map_zpow, hk])⟩)
  · have hc : finrank K (fixedSpace x) + finrank K (othersSpace x.toLinearMap (X - 1)) =
        finrank K V := Submodule.finrank_add_eq_of_isCompl hxo.fixed_others.1
    have h3' : finrank K (fixedSpace x) = dW := by rw [hfix1, h3]
    omega
  · rw [hfix1, h3]
  · rw [hfix2, h4]
  · rintro _ ⟨b, rfl⟩ hb
    have hb' := h5 b fun v hv => by
      rw [hρ]
      exact hb v (hfix1 ▸ hv)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk]⟩
  · have hnle : ¬ Wt.fixedSpace ρ (Subgroup.zpowers yy ⊔ Subgroup.zpowers zz) ≤
        Wt.fixedSpace ρ ⊤ := fun h => absurd (Submodule.finrank_mono h) (not_le.mpr h7)
    obtain ⟨u, hu, hu'⟩ := SetLike.not_le_iff_exists.mp hnle
    rw [Wt.mem_fixedSpace] at hu'
    push Not at hu'
    obtain ⟨a, -, ha⟩ := hu'
    refine ⟨f a, ⟨a, rfl⟩, u, hfix2 ▸ hu, ?_⟩
    rwa [hρ] at ha

end Conf

section Lift

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}

theorem h81Choice_of_lift [Finite (ProjOrthDerived Q)] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hK : ringChar K ≠ 2)
    (hK3 : Nat.card K ≠ 3) (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    {P : Subgroup (ProjOrthDerived Q)} (hP : IsElemAbelian p P)
    (hconf : ∀ Pt : Subgroup ↥(orthDerived Q), IsElemAbelian p Pt →
      Nat.card Pt = Nat.card P → ∃ yy ∈ Pt, ∃ zz ∈ Pt, yy ≠ 1 ∧ zz ∉ Subgroup.zpowers yy ∧
        finrank K (othersSpace (yy : V ≃ₗ[K] V).toLinearMap (X - 1)) = 2 ∧
        5 ≤ finrank K (fixedSpace (yy : V ≃ₗ[K] V)) ∧
        (finrank K (fixedSpace ((yy : V ≃ₗ[K] V) * (zz : V ≃ₗ[K] V))) = 3 ∨
          finrank K (fixedSpace ((yy : V ≃ₗ[K] V) * (zz : V ≃ₗ[K] V))) = 4) ∧
        (∀ a ∈ Pt, (∀ v ∈ fixedSpace (yy : V ≃ₗ[K] V), (a : V ≃ₗ[K] V) v = v) →
          a ∈ Subgroup.zpowers yy) ∧
        (∀ v, (zz : V ≃ₗ[K] V) ((yy : V ≃ₗ[K] V) v - v) = (yy : V ≃ₗ[K] V) v - v) ∧
        ∃ t ∈ Pt, ∃ u ∈ fixedSpace ((yy : V ≃ₗ[K] V) * (zz : V ≃ₗ[K] V)), (t : V ≃ₗ[K] V) u ≠ u)
    {JType : Subgroup (ProjOrthDerived Q) → Prop}
    (hType : ∀ yy : ↥(orthDerived Q), OddOrderIsometry Q p (yy : V ≃ₗ[K] V) →
      finrank K (othersSpace (yy : V ≃ₗ[K] V).toLinearMap (X - 1)) = 2 →
      5 ≤ finrank K (fixedSpace (yy : V ≃ₗ[K] V)) →
      p ∣ Nat.card ↥(fixedComponentImage Q (yy : V ≃ₗ[K] V)) →
      JType (fixedComponentImage Q (yy : V ≃ₗ[K] V)))
    (hAut : ∀ yy : ↥(orthDerived Q), OddOrderIsometry Q p (yy : V ≃ₗ[K] V) →
      finrank K (othersSpace (yy : V ≃ₗ[K] V).toLinearMap (X - 1)) = 2 →
      5 ≤ finrank K (fixedSpace (yy : V ≃ₗ[K] V)) →
      ∀ α : MulAut (ProjOrthDerived Q), α ^ p = 1 →
        (∀ j ∈ fixedComponentImage Q (yy : V ≃ₗ[K] V), α j = j) →
          ∃ k : ℤ, α = MulAut.conj (projT Q yy ^ k)) :
    H81Choice p P JType := by
  obtain ⟨Pt, hPt, hmap, hinj⟩ := exists_lift hQ hT hp hp2 hP
  have hcard : Nat.card Pt = Nat.card P := by
    rw [← hmap]
    refine (Nat.card_congr (Equiv.ofBijective (fun a : ↥Pt => (⟨projT Q a, a, a.2, rfl⟩ :
      ↥(Pt.map (projT Q)))) ⟨fun a b h => Subtype.ext (hinj a a.2 b b.2
        (congrArg Subtype.val h)), ?_⟩))
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨yy, hyy, zz, hzz, hyy1, hzy, hR, hW, hWz, hker, hzR, hmove⟩ := hconf Pt hPt hcard
  have hy := oddOrderIsometry_of_mem hQ hpK hPt hyy
  have h := h81Choice_of_config hQ hT hK hK3 hp hp2 hpK hPt hinj hyy hzz hyy1 hzy hR hW hWz
    hker hzR hmove (hType yy hy hR hW) (hAut yy hy hR hW)
  rwa [hmap] at h

end Lift

section Facts

theorem map_map_symm_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (P : Subgroup A) :
    (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
  ext x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem ne_char_of_dvd_sq_sub_one {p : ℕ} {Q : TauCeti.PrimePower} (h : p ∣ Q.card ^ 2 - 1) :
    p ≠ Q.p := by
  intro hpq
  have h1 : Q.p ∣ Q.card ^ 2 := by
    rw [TauCeti.PrimePower.card_def, ← pow_mul]
    exact dvd_pow_self _ (by have := Q.exponent_pos; omega)
  have h4 : 1 ≤ Q.card ^ 2 := Nat.one_le_pow _ _ (by
    rw [TauCeti.PrimePower.card_def]; exact pow_pos Q.prime_p.pos _)
  have h5 : Q.p ∣ Q.card ^ 2 - 1 + 1 := by rw [Nat.sub_add_cancel h4]; exact h1
  have h6 : Q.p ∣ 1 := (Nat.dvd_add_right (hpq ▸ h)).mp h5
  exact Q.prime_p.one_lt.ne' (Nat.dvd_one.mp h6)

theorem field_facts {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : TauCeti.PrimePower} (hQ2 : Q.p ≠ 2) (hFcard : Nat.card F = Q.p ^ Q.exponent)
    (hdiv : p ∣ Q.card ^ 2 - 1) :
    ringChar F ≠ 2 ∧ Nat.card F ≠ 3 ∧ (p : F) ≠ 0 ∧ Nat.card F = Q.card := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hFQ : Nat.card F = Q.card := by rw [hFcard, TauCeti.PrimePower.card_def]
  have hchar : ringChar F = Q.p := by
    have := Fintype.ofFinite F
    haveI := charP_of_card_eq_prime_pow (R := F) (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
    exact ringChar.eq F Q.p
  refine ⟨by rw [hchar]; exact hQ2, by rw [hFQ]; exact card_ne_three_of_dvd_sq_sub_one hp hp2 hdiv,
    fun h => ?_, hFQ⟩
  have h1 := ringChar.dvd h
  rw [hchar] at h1
  exact ne_char_of_dvd_sq_sub_one hdiv ((Nat.prime_dvd_prime_iff_eq Q.prime_p hp).mp h1).symm

end Facts

end CFSG.LocalAnalysis.GLTheoremA.H81Orth
