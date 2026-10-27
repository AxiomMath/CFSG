module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44SevenFixed
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Matrix

variable {K : Type*} [Field K]

theorem eq_one_of_commute_of_pow_seven (hK : Nat.card K = 4) {g u : Matrix (Fin 4) (Fin 4) K}
    (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1) (hu : u * u = 1) (hgu : g * u = u * g) : u = 1 := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hK]; norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) hKcard
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  set W : Submodule K (Fin 4 → K) := LinearMap.ker (Matrix.mulVecLin g - 1) with hWdef
  set U : Submodule K (Fin 4 → K) := LinearMap.ker (Matrix.mulVecLin (u - 1)) with hUdef
  have hsubg : ∀ v : Fin 4 → K, (Matrix.mulVecLin g - 1) v = g *ᵥ v - v := by
    intro v
    rw [LinearMap.sub_apply, Matrix.mulVecLin_apply, Module.End.one_apply]
  have hsubu : ∀ v : Fin 4 → K, (u - 1) *ᵥ v = u *ᵥ v - v := by
    intro v
    have := sub_smul u (1 : Matrix (Fin 4) (Fin 4) K) v
    simpa [Matrix.smul_eq_mulVec, Matrix.one_mulVec] using this
  have mem_W : ∀ v : Fin 4 → K, v ∈ W ↔ g *ᵥ v = v := by
    intro v
    simp only [hWdef, LinearMap.mem_ker, hsubg v, sub_eq_zero]
  have mem_U : ∀ v : Fin 4 → K, v ∈ U ↔ u *ᵥ v = v := by
    intro v
    simp only [hUdef, LinearMap.mem_ker, Matrix.mulVecLin_apply, hsubu v, sub_eq_zero]
  have hWcard : Nat.card W = 4 := by
    have e : W ≃ {v : Fin 4 → K // g *ᵥ v = v} :=
      Equiv.subtypeEquivRight (fun v => mem_W v)
    rw [Nat.card_congr e, card_fixedVec_eq_four_of_pow_seven (K := K) hK hg7 hg1]
  have hWfin : Module.finrank K W = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := W)
    rw [hWcard, hK] at h
    have h' : (4 : ℕ) ^ (1 : ℕ) = 4 ^ Module.finrank K W := by
      rw [pow_one]; exact h
    exact (Nat.pow_right_injective (show 2 ≤ (4 : ℕ) by norm_num) h').symm
  have hWne : W ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank K W = 0 := (Submodule.finrank_eq_zero).mpr hbot
    omega
  obtain ⟨w0, hw0mem, hw0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  let w0' : W := ⟨w0, hw0mem⟩
  have hw0'ne : w0' ≠ 0 := by
    intro h
    have h' : (w0' : Fin 4 → K) = 0 := congrArg Subtype.val h
    dsimp only [w0'] at h'
    exact hw0ne h'
  have hsmul : ∀ y : W, ∃ c : K, c • w0' = y :=
    exists_smul_eq_of_finrank_eq_one hWfin hw0'ne
  have huW : u *ᵥ (w0' : Fin 4 → K) ∈ W := by
    rw [mem_W]
    calc g *ᵥ (u *ᵥ (w0' : Fin 4 → K))
        = (g * u) *ᵥ (w0' : Fin 4 → K) :=
          Matrix.mulVec_mulVec (w0' : Fin 4 → K) g u
      _ = (u * g) *ᵥ (w0' : Fin 4 → K) := by rw [hgu]
      _ = u *ᵥ (g *ᵥ (w0' : Fin 4 → K)) :=
          (Matrix.mulVec_mulVec (w0' : Fin 4 → K) u g).symm
      _ = u *ᵥ (w0' : Fin 4 → K) := by rw [(mem_W (w0' : Fin 4 → K)).mp hw0mem]
  obtain ⟨c, hc⟩ := hsmul ⟨u *ᵥ (w0' : Fin 4 → K), huW⟩
  have hc' : c • (w0' : Fin 4 → K) = u *ᵥ (w0' : Fin 4 → K) := by
    simpa using congrArg Subtype.val hc
  have h1 : u *ᵥ (u *ᵥ (w0' : Fin 4 → K)) = (w0' : Fin 4 → K) := by
    rw [Matrix.mulVec_mulVec (w0' : Fin 4 → K) u u, hu, Matrix.one_mulVec]
  have h2 : u *ᵥ (u *ᵥ (w0' : Fin 4 → K)) = (c * c) • (w0' : Fin 4 → K) := by
    rw [← hc', Matrix.mulVec_smul, ← hc', smul_smul]
  have hcc_smul : (c * c) • (w0' : Fin 4 → K) = (w0' : Fin 4 → K) := h2.symm.trans h1
  have hcc1 : c * c - 1 = 0 := by
    have hz : (c * c - 1) • (w0' : Fin 4 → K) = 0 := by
      rw [sub_smul, one_smul, hcc_smul, sub_self]
    have hw0i : ∃ i : Fin 4, (w0' : Fin 4 → K) i ≠ 0 := by
      by_contra h
      push Not at h
      exact hw0'ne (Subtype.ext (funext h))
    obtain ⟨i, hi⟩ := hw0i
    have hzi : (c * c - 1) * ((w0' : Fin 4 → K) i) = 0 := by
      have := congrFun hz i
      simpa using this
    rcases mul_eq_zero.mp hzi with h | h
    · exact h
    · exact absurd h hi
  have hcc : c * c = 1 := sub_eq_zero.mp hcc1
  have hc_one : c = 1 := by
    have hsq : (c - 1) * (c - 1) = 0 := by
      calc (c - 1) * (c - 1) = c * c - 2 * c + 1 := by ring
        _ = 0 := by rw [hcc, hchar, zero_mul, sub_zero, one_add_one_eq_two, hchar]
    rcases mul_eq_zero.mp hsq with h | h
    · exact sub_eq_zero.mp h
    · exact sub_eq_zero.mp h
  have hu_w0 : u *ᵥ (w0' : Fin 4 → K) = (w0' : Fin 4 → K) := by
    rw [← hc', hc_one, one_smul]
  have hWU : W ≤ U := by
    intro v hv
    rw [mem_U]
    obtain ⟨d, hd⟩ := hsmul ⟨v, hv⟩
    have hd' : d • (w0' : Fin 4 → K) = v := by simpa using congrArg Subtype.val hd
    rw [← hd', Matrix.mulVec_smul, hu_w0]
  have hNN : (Matrix.mulVecLin (u - 1)) * (Matrix.mulVecLin (u - 1)) = 0 := by
    have h2m : (2 : Matrix (Fin 4) (Fin 4) K) = 0 := by
      rw [← Matrix.diagonal_ofNat (n := Fin 4) (α := K) 2, Matrix.diagonal_eq_zero]
      funext i
      exact hchar
    have huu : u + u = 0 := by rw [← two_mul, h2m, zero_mul]
    have h11 : (1 : Matrix (Fin 4) (Fin 4) K) + 1 = 0 := by
      rw [one_add_one_eq_two, h2m]
    have hsq : (u - 1) * (u - 1) = 0 := by
      have hexp : (u - 1) * (u - 1) = u * u - (u + u) + 1 := by noncomm_ring
      rw [hexp, hu, huu, sub_zero, h11]
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hsq, Matrix.mulVecLin_zero]
  have hrange_le : LinearMap.range (Matrix.mulVecLin (u - 1)) ≤
      LinearMap.ker (Matrix.mulVecLin (u - 1)) := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    show (Matrix.mulVecLin (u - 1)) ((Matrix.mulVecLin (u - 1)) x) = 0
    rw [← Module.End.mul_apply, hNN, LinearMap.zero_apply]
  have hb : 2 ≤ Module.finrank K U := by
    rw [hUdef]
    have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (u - 1))
    have hfin : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
    have hmono : Module.finrank K (LinearMap.range (Matrix.mulVecLin (u - 1))) ≤
        Module.finrank K (LinearMap.ker (Matrix.mulVecLin (u - 1))) :=
      Submodule.finrank_mono hrange_le
    omega
  let f : U → U := fun x => ⟨g *ᵥ (x : Fin 4 → K), by
    rw [mem_U]
    calc u *ᵥ (g *ᵥ (x : Fin 4 → K))
        = (u * g) *ᵥ (x : Fin 4 → K) :=
          Matrix.mulVec_mulVec (x : Fin 4 → K) u g
      _ = (g * u) *ᵥ (x : Fin 4 → K) := by rw [← hgu]
      _ = g *ᵥ (u *ᵥ (x : Fin 4 → K)) :=
          (Matrix.mulVec_mulVec (x : Fin 4 → K) g u).symm
      _ = g *ᵥ (x : Fin 4 → K) := by rw [(mem_U (x : Fin 4 → K)).mp x.2]⟩
  have hiter : ∀ n : ℕ, ∀ x : U,
      (((f^[n]) x : U) : Fin 4 → K) = g ^ n *ᵥ (x : Fin 4 → K) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply']
        show g *ᵥ (((f^[n]) x : U) : Fin 4 → K) = g ^ (n + 1) *ᵥ (x : Fin 4 → K)
        rw [ih x, Matrix.mulVec_mulVec (x : Fin 4 → K) g (g ^ n), ← pow_succ']
  have hf : f^[7] = id := by
    funext x
    apply Subtype.ext
    rw [hiter 7 x, hg7]
    simp
  have hmod := card_modEq_card_fixed_of_iterate_seven f hf
  have hfix : Nat.card {a : U // f a = a} = 4 := by
    have he : Nat.card {a : U // f a = a} = Nat.card W := by
      apply Nat.card_congr
      exact
        { toFun := fun a => ⟨(a.1 : Fin 4 → K), (mem_W (a.1 : Fin 4 → K)).mpr (by
              have h := congrArg Subtype.val a.2
              simpa [f] using h)⟩
          invFun := fun w => ⟨⟨(w : Fin 4 → K), hWU w.2⟩, by
              apply Subtype.ext
              simpa [f] using (mem_W (w : Fin 4 → K)).mp w.2⟩
          left_inv := fun a => Subtype.ext (Subtype.ext rfl)
          right_inv := fun w => Subtype.ext rfl }
    rw [he, hWcard]
  rw [hfix] at hmod
  have hcardU : Nat.card U = 4 ^ Module.finrank K U := by
    haveI : Fintype U := Fintype.ofFinite U
    have h1 : Nat.card U = Fintype.card U := Nat.card_eq_fintype_card
    have h2 : Fintype.card U = Fintype.card K ^ Module.finrank K U :=
      Module.card_eq_pow_finrank
    have h3 : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
    rw [h1, h2, h3]
  have hmod' : 4 ^ Module.finrank K U ≡ 4 [MOD 7] := by
    rw [← hcardU]; exact hmod
  have hle : Module.finrank K U ≤ 4 := by
    have h := Submodule.finrank_le U
    rwa [Module.finrank_fin_fun K] at h
  have hk : Module.finrank K U = 4 := by
    have hcases : Module.finrank K U = 2 ∨ Module.finrank K U = 3 ∨
        Module.finrank K U = 4 := by omega
    rcases hcases with h2 | h3 | h4
    · exfalso; rw [h2] at hmod'; exact absurd hmod' (by decide)
    · exfalso; rw [h3] at hmod'; exact absurd hmod' (by decide)
    · exact h4
  have hUtop : U = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hk, Module.finrank_fin_fun K]
  have hN0 : Matrix.mulVecLin (u - 1) = 0 := by
    rw [← LinearMap.ker_eq_top, ← hUdef]
    exact hUtop
  have hu1 : u - 1 = 0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply', hN0, Matrix.mulVecLin_zero]
  exact sub_eq_zero.mp hu1

end CFSG.OddStandard.AltStdSec.SwapPartner
