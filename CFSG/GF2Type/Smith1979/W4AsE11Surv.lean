module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module CFSG.Open

section Plus

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem add_self_eq_zero_of_zmod_two (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem orthogonal_eq_of_totallySingular {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {W : Submodule (ZMod 2) V} (hW : ∀ v ∈ W, Q v = 0)
    (hdim : 2 * finrank (ZMod 2) W = finrank (ZMod 2) V) :
    LinearMap.BilinForm.orthogonal Q.polarBilin W = W := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    show QuadraticMap.polarBilin Q w u = 0
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      hW _ (W.add_mem hw hu), hW _ hw, hW _ hu]
    rfl
  · rw [LinearMap.BilinForm.finrank_orthogonal hQ]
    omega

theorem card_singular_eq_136 {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate)
    (h8 : finrank (ZMod 2) V = 8) {W : Submodule (ZMod 2) V} (hW4 : finrank (ZMod 2) W = 4)
    (hW : ∀ v ∈ W, Q v = 0) : Nat.card {v : V // Q v = 0} = 136 := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  letI : Fintype V := Fintype.ofFinite V
  have hperp := orthogonal_eq_of_totallySingular hQ hW (by omega)
  have hz1 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hz2 : ∀ a : ZMod 2, a ≠ 0 → a + 1 = 0 := by decide
  have hex : ∀ x : V, x ∉ W → ∃ c ∈ W, QuadraticMap.polar Q c x ≠ 0 := by
    intro x hx
    by_contra hcon
    push Not at hcon
    apply hx
    rw [← hperp, LinearMap.BilinForm.mem_orthogonal_iff]
    intro c hc
    show QuadraticMap.polarBilin Q c x = 0
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hcon c hc
  have hconst : ∀ c ∈ W, ∀ x y : V, x - y ∈ W →
      QuadraticMap.polar Q c x = QuadraticMap.polar Q c y := by
    intro c hc x y hxy
    have h0 : QuadraticMap.polar Q c (x - y) = 0 := by
      rw [QuadraticMap.polar, hW _ (W.add_mem hc hxy), hW _ hc, hW _ hxy]; rfl
    rw [QuadraticMap.polar_sub_right] at h0
    exact sub_eq_zero.mp h0
  let g : V ⧸ W → V := fun q =>
    if h : ∃ c ∈ W, QuadraticMap.polar Q c (Quotient.out q) ≠ 0 then h.choose else 0
  have hgW : ∀ q, g q ∈ W := by
    intro q
    simp only [g]
    split_ifs with h
    · exact h.choose_spec.1
    · exact W.zero_mem
  have hgB : ∀ x : V, x ∉ W → QuadraticMap.polar Q (g (W.mkQ x)) x = 1 := by
    intro x hx
    have hout : Quotient.out (W.mkQ x) - x ∈ W := by
      rw [← Submodule.Quotient.eq]
      exact Quotient.out_eq _
    have hxo : Quotient.out (W.mkQ x) ∉ W := fun h => hx (by
      have := W.sub_mem h hout
      rwa [sub_sub_cancel] at this)
    have h := hex _ hxo
    simp only [g, dif_pos h]
    rw [← hconst _ h.choose_spec.1 _ _ hout]
    exact hz1 _ h.choose_spec.2
  let σ : V → V := fun x => x + g (W.mkQ x)
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    have : W.mkQ (x + g (W.mkQ x)) = W.mkQ x := by
      rw [map_add, Submodule.mkQ_apply W (g _), (Submodule.Quotient.mk_eq_zero W).mpr (hgW _),
        add_zero]
    simp only [σ, this, add_assoc, add_self_eq_zero_of_zmod_two, add_zero]
  have hσW : ∀ x, x ∉ W → σ x ∉ W := by
    intro x hx h
    have := W.sub_mem h (hgW (W.mkQ x))
    simp only [σ, add_sub_cancel_right] at this
    exact hx this
  have hσQ : ∀ x, x ∉ W → Q (σ x) = Q x + 1 := by
    intro x hx
    have h := QuadraticMap.polar_comm Q x (g (W.mkQ x))
    rw [hgB x hx, QuadraticMap.polar] at h
    rw [hW _ (hgW _)] at h
    simp only [σ]
    linear_combination h
  set A := (Finset.univ : Finset V).filter (· ∉ W)
  have hA0 : (A.filter (fun x => Q x = 0)).card = (A.filter (fun x => Q x ≠ 0)).card := by
    refine Finset.card_bij' (fun x _ => σ x) (fun x _ => σ x) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨hσW x hx.1, ?_⟩
      rw [hσQ x hx.1, hx.2]
      decide
    · intro x hx
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨hσW x hx.1, ?_⟩
      rw [hσQ x hx.1]
      exact hz2 _ hx.2
    · intro x _; exact hσσ x
    · intro x _; exact hσσ x
  have hcardV : Fintype.card V = 256 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), h8, ZMod.card]
    norm_num
  have hcardW : ((Finset.univ : Finset V).filter (· ∈ W)).card = 16 := by
    have : ((Finset.univ : Finset V).filter (· ∈ W)).card = Nat.card W := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [this, Module.natCard_eq_pow_finrank (K := ZMod 2), hW4, Nat.card_zmod]
    norm_num
  have hA : A.card = 240 := by
    have := (Finset.univ : Finset V).card_filter_add_card_filter_not (fun x => x ∈ W)
    rw [Finset.card_univ, hcardV, hcardW] at this
    simp only [A]
    omega
  have hsplit := A.card_filter_add_card_filter_not (fun x => Q x = 0)
  rw [hA] at hsplit
  have h120 : (A.filter (fun x => Q x = 0)).card = 120 := by
    have : (A.filter (fun x => ¬ Q x = 0)).card = (A.filter (fun x => Q x ≠ 0)).card := rfl
    omega
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hS := ((Finset.univ : Finset V).filter (fun v => Q v = 0)).card_filter_add_card_filter_not
    (fun x => x ∈ W)
  rw [Finset.filter_filter, Finset.filter_filter] at hS
  have e1 : (Finset.univ : Finset V).filter (fun v => Q v = 0 ∧ v ∈ W) =
      (Finset.univ : Finset V).filter (· ∈ W) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hW v h, h⟩⟩
  have e2 : (Finset.univ : Finset V).filter (fun v => Q v = 0 ∧ v ∉ W) =
      A.filter (fun x => Q x = 0) := by
    ext v
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [e1, e2, hcardW, h120] at hS
  omega

end Plus

section L28

open Polynomial
open scoped MatrixGroups

theorem irreducible_cyclotomic_nine_zmod_two : Irreducible (cyclotomic 9 (ZMod 2)) := by
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (by decide) dvd_rfl ?_
  rw [natDegree_cyclotomic, show Nat.totient 9 = 6 by decide, eq_comm,
    orderOf_eq_iff (by decide)]
  refine ⟨Units.ext (by simp; decide), fun m hm hm0 => ?_⟩
  rw [ne_eq, Units.ext_iff]
  interval_cases m <;> simp <;> decide

theorem pow_three_eq_one_of_pow_nine_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V ≤ 5) {f : Module.End (ZMod 2) V}
    (hf : f ^ 9 = 1) : f ^ 3 = 1 := by
  set μ := minpoly (ZMod 2) f
  have h9 : cyclotomic 9 (ZMod 2) * (X ^ 3 - 1) = X ^ 9 - 1 :=
    cyclotomic_prime_pow_mul_X_pow_sub_one (ZMod 2) 3 1
  have hμ9 : μ ∣ cyclotomic 9 (ZMod 2) * (X ^ 3 - 1) := by
    rw [h9]
    exact minpoly.dvd _ _ (by simp [hf])
  have hμ0 : μ ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral f)
  have hμdeg : μ.natDegree ≤ 5 :=
    (natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f) (LinearMap.charpoly_monic f).ne_zero
      |>.trans_eq (LinearMap.charpoly_natDegree f)).trans hV
  have hcop : IsCoprime (cyclotomic 9 (ZMod 2)) μ := by
    refine (irreducible_cyclotomic_nine_zmod_two.coprime_iff_not_dvd).mpr fun h => ?_
    have := natDegree_le_of_dvd h hμ0
    rw [natDegree_cyclotomic, show Nat.totient 9 = 6 by decide] at this
    omega
  obtain ⟨c, hc⟩ := hcop.symm.dvd_of_dvd_mul_left hμ9
  have := congrArg (aeval f) hc
  simp [μ] at this
  exact sub_eq_zero.mp this

theorem exists_pow_three_eq_add_one : ∃ α : GaloisField 2 3, α ^ 3 = α + 1 := by
  have hcard : Nat.card (GaloisField 2 3)ˣ = 7 := by
    rw [Nat.card_units, GaloisField.card 2 3 (by decide)]; rfl
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 (by rw [hcard])
  have two : (2 : GaloisField 2 3) = 0 := CharTwo.two_eq_zero
  have h7 : (g : GaloisField 2 3) ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  have h1 : (g : GaloisField 2 3) - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, ← Units.val_one, Units.val_inj]
    rintro rfl
    simp at hg
  set α := (g : GaloisField 2 3)
  have hprod : (α ^ 3 + α + 1) * (α ^ 3 + α ^ 2 + 1) = 0 := by
    have h : (α - 1) * ((α ^ 3 + α + 1) * (α ^ 3 + α ^ 2 + 1)) = 0 := by
      linear_combination h7 + (α ^ 4 - α ^ 3) * two
    exact (mul_eq_zero.mp h).resolve_left h1
  rcases mul_eq_zero.mp hprod with h | h
  · exact ⟨α, by linear_combination h - (α + 1) * two⟩
  · exact ⟨α ^ 3, by linear_combination α ^ 2 * h7 - h + α ^ 2 * two⟩

theorem exists_orderOf_eq_nine_sl2 : ∃ A : SL(2, GaloisField 2 3), orderOf A = 9 := by
  obtain ⟨α, hα⟩ := exists_pow_three_eq_add_one
  have two : (2 : GaloisField 2 3) = 0 := CharTwo.two_eq_zero
  have hA3 : (!![0, 1; 1, α] : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) ^ 3 =
      !![α, α ^ 2 + 1; α ^ 2 + 1, α + 1] := by
    rw [pow_three]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp; ring
    · simp; ring
    · simp; linear_combination hα + α * two
  have hB3 : (!![α, α ^ 2 + 1; α ^ 2 + 1, α + 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) ^ 3 =
      1 := by
    rw [pow_three, Matrix.one_fin_two]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
      linear_combination (10 + α + 3 * α ^ 2) * hα + (5 + 7 * α + 3 * α ^ 2) * two
    · simp
      linear_combination (4 + 7 * α + α ^ 3) * hα + (3 + 7 * α + 7 * α ^ 2) * two
    · simp
      linear_combination (4 + 7 * α + α ^ 3) * hα + (3 + 7 * α + 7 * α ^ 2) * two
    · simp
      linear_combination (10 + 2 * α + 3 * α ^ 2) * hα + (6 + 9 * α + 6 * α ^ 2) * two
  let A : SL(2, GaloisField 2 3) := ⟨!![0, 1; 1, α], by simp [Matrix.det_fin_two_of,
    CharTwo.neg_eq]⟩
  have hA3' : ((A ^ 3 : SL(2, GaloisField 2 3)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) =
      !![α, α ^ 2 + 1; α ^ 2 + 1, α + 1] := by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact hA3
  refine ⟨A, orderOf_eq_prime_pow (p := 3) (n := 1) ?_ ?_⟩
  · intro h
    rw [pow_one] at h
    have h01 : (!![α, α ^ 2 + 1; α ^ 2 + 1, α + 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 3))
        0 1 = (1 : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) 0 1 := by
      rw [← hA3', h]
      rfl
    simp at h01
    have h1 : (α + 1) ^ 2 = 0 := by linear_combination h01 + α * two
    have h1' : α + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h1
    have h0 : α = 0 := pow_eq_zero_iff (by decide : 3 ≠ 0) |>.mp (hα.trans h1')
    simp [h0] at h1'
  · apply Subtype.ext
    rw [show 3 ^ (1 + 1) = 3 * 3 from rfl, pow_mul, Matrix.SpecialLinearGroup.coe_pow, hA3', hB3]
    rfl

end L28

end CFSG.GF2Type.Smith1979.W4As
