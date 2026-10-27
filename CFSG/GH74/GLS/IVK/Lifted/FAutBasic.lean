module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Transport
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage1.Thm3.Sec5 (fixedSubgroup_congr hasSolvableTwoComponentSL23_congr)

section FixedCondSec

@[expose] def FixedCond (Q : Type) [Group Q] (φ : MulAut Q) : Prop :=
  (∃ L : Subgroup ↥(fixedSubgroup Q φ), IsPComponent 2 L) ∨
    HasSolvableTwoComponentSL23 ↥(fixedSubgroup Q φ)

theorem fixedCond_of_equiv {Q : Type} [Group Q] (φ : MulAut Q) {Y : Type} [Group Y]
    (e : ↥(fixedSubgroup Q φ) ≃* Y)
    (h : (∃ L : Subgroup Y, IsPComponent 2 L) ∨ HasSolvableTwoComponentSL23 Y) : FixedCond Q φ := by
  rcases h with ⟨L, hL⟩ | hS
  · exact Or.inl ⟨L.map e.symm.toMonoidHom,
      CFSG.LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e.symm hL⟩
  · exact Or.inr (hasSolvableTwoComponentSL23_congr e.symm hS)

theorem not_fixedCond_of_comm {Q : Type} [Group Q] (φ : MulAut Q)
    (hcomm : ∀ a ∈ fixedSubgroup Q φ, ∀ b ∈ fixedSubgroup Q φ, a * b = b * a) :
    ¬ FixedCond Q φ := by
  have hXc : ∀ a b : ↥(fixedSubgroup Q φ), a * b = b * a := fun a b =>
    Subtype.ext (hcomm a.1 a.2 b.1 b.2)
  have hXOc : ∀ a b : ↥(fixedSubgroup Q φ) ⧸ pPrimeCore 2 ↥(fixedSubgroup Q φ), a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hXc]
  rintro (⟨L, hL⟩ | hfix)
  · obtain ⟨Kc, ⟨hqs, -⟩, hsub, hmap, hmin⟩ := hL
    obtain ⟨-, -, a, b, hab⟩ := hqs
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have : x * y = y * x := Subtype.ext (hXOc x.1 y.1)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  · obtain ⟨W, -, F, hF, hFin, hcard, ⟨iso⟩⟩ := hfix
    have hnc : ∃ a b : ↥(StatedSL 2 F), a * b ≠ b * a := by
      let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
      let u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
      let v : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
      refine ⟨e u, e v, fun h => ?_⟩
      have h1 : u * v = v * u := e.injective (by simpa using h)
      have h2 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
        ((x : Matrix (Fin 2) (Fin 2) F) 0 0)) h1
      simp only [Matrix.SpecialLinearGroup.coe_mul] at h2
      simp [u, v, Matrix.mul_apply, Fin.sum_univ_two] at h2
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have h1 : iso.symm a * iso.symm b = iso.symm b * iso.symm a :=
      Subtype.ext (hXOc (iso.symm a).1 (iso.symm b).1)
    have h2 := congrArg iso h1
    simpa using h2

theorem not_isFAutomorphism_of_comm {Q : Type} [Group Q] (φ : MulAut Q)
    (hcomm : ∀ a ∈ fixedSubgroup Q φ, ∀ b ∈ fixedSubgroup Q φ, a * b = b * a) :
    ¬ IsFAutomorphism Q φ := fun h => not_fixedCond_of_comm φ hcomm h.2.2.2.2

theorem exists_pow_two_orderOf {Q : Type} [Group Q] {φ : MulAut Q} (h : φ * φ = 1) :
    ∃ k : ℕ, orderOf φ = 2 ^ k := by
  have h2 : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf φ ∣ 2 ^ 1 by simpa using h2)
  exact ⟨k, hk⟩

theorem isFAutomorphism_of_fixedCond {Q : Type} [Group Q] {φ : MulAut Q} (hq : IsQuasisimple Q)
    (hk : IsKGroupNative Q) (hr : pRank 2 Q = 1) (h : φ * φ = 1) (hf : FixedCond Q φ) :
    IsFAutomorphism Q φ := ⟨hq, hk, hr, exists_pow_two_orderOf h, hf⟩

theorem fixedCond_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') {φ : MulAut Q}
    (h : FixedCond Q φ) : FixedCond Q' (MulAut.congr e φ) := by
  have hF := fixedSubgroup_congr e φ
  let eF : ↥(fixedSubgroup Q φ) ≃* ↥(fixedSubgroup Q' (MulAut.congr e φ)) :=
    (MulEquiv.subgroupMap e _).trans (MulEquiv.subgroupCongr hF.symm)
  rcases h with ⟨L, hL⟩ | hS
  · exact Or.inl ⟨L.map eF.toMonoidHom,
      CFSG.LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 eF hL⟩
  · exact Or.inr (hasSolvableTwoComponentSL23_congr eF hS)

theorem fixedCond_of_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') {φ : MulAut Q}
    (h : FixedCond Q' (MulAut.congr e φ)) : FixedCond Q φ := by
  have := fixedCond_congr e.symm h
  have e1 : MulAut.congr e.symm (MulAut.congr e φ) = φ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [e1] at this

end FixedCondSec

end CFSG.GH74.GLS.IVK.Lifted
