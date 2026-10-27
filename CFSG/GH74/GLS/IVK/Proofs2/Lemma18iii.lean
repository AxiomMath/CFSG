module

public import CFSG.GH74.GLS.IVK.Proofs2.Stmt18iii
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma18iiiS
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma18iiiM
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma18iiiD
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma18iiiU

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma18iii

open Subgroup Matrix CFSG CFSG.PSL2Table CFSG.GH74.GLS.IVK CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

theorem core
    {F : Type} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (hq : Nat.card F = p ^ n) (hn : 0 < n) (h4 : 4 < Nat.card F)
    (y : PSL(2, F)) (hy1 : y ≠ 1) (hyodd : Odd (orderOf y)) :
    ∃ g : PSL(2, F), ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), ringChar F₀ = p ∧
      Nat.card F₀ ≤ Nat.card F ∧
      Nonempty (↥(Subgroup.closure ({y, g * y * g⁻¹} : Set (PSL(2, F)))) ≃* L2 F₀) := by
  obtain ⟨Y, rfl⟩ := mk_surjective y
  by_cases hsq : (Y : Matrix (Fin 2) (Fin 2) F).trace ^ 2 = 4
  ·
    have h2 : ((Y : Matrix (Fin 2) (Fin 2) F).trace - 2) * ((Y : Matrix (Fin 2) (Fin 2) F).trace + 2)
        = 0 := by linear_combination hsq
    obtain ⟨Y₁, hY₁, htr⟩ : ∃ Y₁ : SL(2, F), mk Y₁ = mk Y ∧
        (Y₁ : Matrix (Fin 2) (Fin 2) F).trace = 2 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact ⟨Y, rfl, by linear_combination h⟩
      · refine ⟨-Y, mk_neg Y, ?_⟩
        rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg]
        linear_combination -h
    have hY₁1 : Y₁ ≠ 1 := by
      rintro rfl
      apply hy1
      rw [← hY₁, map_one]
    obtain ⟨g, ⟨e⟩⟩ := unipotent_closure_pair hp2 Y₁ hY₁1 htr
    rw [hY₁] at e
    refine ⟨g, ZMod p, inferInstance, inferInstance, ZMod.ringChar_zmod_n p, ?_, ⟨?_⟩⟩
    · rw [Nat.card_zmod, hq]
      exact Nat.le_self_pow hn.ne' p
    · exact e.trans (L2.equivPSL (ZMod p)).symm
  ·
    have h2 : (2 : F) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff F p] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h')
    have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    have hFodd : Odd (Nat.card F) := by rw [hq]; exact hpodd.pow
    have hY1 : Y ≠ 1 := by
      intro h
      apply hsq
      rw [h]
      simp
      norm_num
    have hY2 : Y ≠ -1 := by
      intro h
      apply hsq
      rw [h]
      simp
      norm_num
    set t : F := (Y : Matrix (Fin 2) (Fin 2) F).trace with ht
    obtain ⟨s, hs⟩ := exists_goodS (F := F) (p := p) hFodd h4 t hsq
    obtain ⟨g₁, htrace, hdet⟩ := exists_conj_traces Y hsq s
    set B : SL(2, F) := g₁ * Y * g₁⁻¹ with hB
    obtain ⟨hD0, hD4, hrel⟩ := hs
    have hD0' : ((Y : Matrix (Fin 2) (Fin 2) F) * B - B * Y).det ≠ 0 := by
      rw [hdet]; exact hD0
    have hD4' : ((Y : Matrix (Fin 2) (Fin 2) F) * B - B * Y).det ≠ 4 := by
      rw [hdet]; exact hD4
    have hmkB : mk B = mk g₁ * mk Y * (mk g₁)⁻¹ := by
      rw [hB, map_mul, map_mul, map_inv]
    have hconj : orderOf (mk g₁ * mk Y * (mk g₁)⁻¹) = orderOf (mk Y) := by
      have := orderOf_injective (MulAut.conj (mk g₁)).toMonoidHom (MulAut.conj (mk g₁)).injective
        (mk Y)
      simpa [MulAut.conj_apply] using this
    have hBo : Odd (orderOf (mk B)) := by rw [hmkB, hconj]; exact hyodd
    have hsq1 : mk Y ^ 2 ≠ 1 := by
      intro h
      have hd : orderOf (mk Y) ∣ 2 := orderOf_dvd_of_pow_eq_one h
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
      · exact hy1 (orderOf_eq_one_iff.1 h1)
      · rw [h1] at hyodd
        exact absurd hyodd (by decide)
    have hxmem : ∀ z : PSL(2, F), z ∈ ({mk Y, mk B} : Set (PSL(2, F))) →
        z ∈ Subgroup.closure ({mk Y, mk B} : Set (PSL(2, F))) := fun z hz =>
      Subgroup.subset_closure hz
    have hx : ∃ x ∈ Subgroup.closure ({mk Y, mk B} : Set (PSL(2, F))),
        x ≠ 1 ∧ x ^ 2 ≠ 1 ∧ x ^ 3 ≠ 1 ∧ (p ≠ 5 → x ^ 5 ≠ 1) := by
      by_cases hrelt : t ^ 2 = 1 ∨ t ^ 4 - 3 * t ^ 2 + 1 = 0
      · obtain ⟨hτ2, hτ3, hτ5⟩ := hrel hrelt
        rw [← htrace] at hτ2 hτ3 hτ5
        obtain ⟨h1, h2', h3, h5⟩ := mk_mul_orders (p := p) h2 hD0' hτ2 hτ3 hτ5
        refine ⟨mk (Y * B), ?_, h1, h2', h3, h5⟩
        rw [map_mul]
        exact Subgroup.mul_mem _ (hxmem (mk Y) (by simp)) (hxmem (mk B) (by simp))
      · push Not at hrelt
        refine ⟨mk Y, hxmem (mk Y) (by simp), hy1, hsq1, ?_, fun _ => ?_⟩
        · exact mk_cube_ne_one hY1 hY2 (sub_ne_zero.2 hrelt.1)
        · exact mk_pow5_ne_one hY1 hY2 hrelt.2
    obtain ⟨m, hmf, ⟨e⟩⟩ := closure_pair_iso (p := p) (f := n) hq hp2 Y B hyodd hBo hD0' hD4' hx
    rw [hmkB] at e
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hmf
      omega
    refine ⟨mk g₁, GaloisField p m, inferInstance, inferInstance, ringChar.eq (GaloisField p m) p, ?_,
      ⟨e.trans (L2.equivPSL (GaloisField p m)).symm⟩⟩
    rw [GaloisField.card p m hm0, hq]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (Nat.le_of_dvd hn hmf)

end Lemma18iii

open scoped MatrixGroups
open CFSG.PSL2Table CFSG.GH74.GLS.IVK Lemma18iii

open Lemma18iii in
theorem ivk_1_8_iii : IVK_1_8_iii := by
  intro F _ _ hF K _ _ e y hy1 hyodd
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := isOddPrimePower_of_L2Field hF
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hcharF : CharP F p :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hq)
  have hringF : ringChar F = p := ringChar.eq F p
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  have h4 : 4 < Nat.card F := by
    obtain ⟨k, hk⟩ := hF.1
    have := hF.2
    omega
  let φ : K ≃* PSL(2, F) := toPSL e
  have hφy1 : φ y ≠ 1 := by
    intro h
    exact hy1 (φ.injective (by rw [h, map_one]))
  have hφyodd : Odd (orderOf (φ y)) := by
    rw [MulEquiv.orderOf_eq]; exact hyodd
  obtain ⟨g', F₀, hF₀, hfin₀, hch, hle, ⟨e₀⟩⟩ := core hp2 hq hn h4 (φ y) hφy1 hφyodd
  refine ⟨φ.symm g', F₀, hF₀, hfin₀, by rw [hch, hringF], hle, ?_⟩
  set S : Set K := {y, φ.symm g' * y * (φ.symm g')⁻¹} with hS
  have himg : φ '' S = {φ y, g' * φ y * g'⁻¹} := by
    rw [hS, Set.image_pair]
    simp
  have hmap : (Subgroup.closure S).map φ.toMonoidHom = Subgroup.closure {φ y, g' * φ y * g'⁻¹} := by
    rw [MonoidHom.map_closure]
    change Subgroup.closure (φ '' S) = _
    rw [himg]
  exact ⟨(Subgroup.equivMapOfInjective (Subgroup.closure S) φ.toMonoidHom φ.injective).trans
    ((MulEquiv.subgroupCongr hmap).trans e₀)⟩

theorem ivk_1_8 : IVK_1_8 := ivk_1_8_of_iii ivk_1_8_iii

end CFSG.GH74.GLS.IVK.Proofs2
