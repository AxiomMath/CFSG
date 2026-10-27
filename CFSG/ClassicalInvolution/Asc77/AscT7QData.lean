module

import CFSG.ClassicalInvolution.Asc77.AscT7QDataEng
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Act
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Frat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace T7Q

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


open T7F2 T7G2 T7DR

section Basic

variable (h : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')

include h

theorem z_eq_pow {a b : G} {n : ℕ} (c : QuatCoord R a b n) : z = a ^ (2 ^ n) := by
  exact CFSG.ClassicalInvolution.Asc77.T7QEng.z_eq_pow_gen h.hzR c

end Basic

section Part

variable (h : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h11 : C25_11 p f) (h16 : C25_16 p f)
  (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R'))

include h h11 h16 h4

private theorem frame_of : CFSG.ClassicalInvolution.Asc77.T7QEng.Frame S R R' z t' := by
  have hF : ∀ y ∈ Nsub S R, ¬ IsFAut R' y := fun y hy =>
    h16 G Ω K K' W S R R' z t u₁ u₂ h.hyp y (mem_Nsub.mp hy).1
  have hN2 : IsPGroup 2 ↥(Nsub S R) := S.isPGroup'.to_le (show Nsub S R ≤ _ from inf_le_left)
  exact
    { hzR := h.hzR
      hqR := h.hqR
      hcomm := h.hcomm
      hRS := h.hRS
      ht'S := h.ht'S
      ht'2 := h.ht'2
      ht'R := h.ht'R
      ht'R' := h.ht'R'
      ht'inv := h.ht'inv
      conj_R'_of_mem_N := fun {n} hn => h.conj_R'_of_mem_N hn
      C'_le_N := h.C'_le_N
      N_conj := fun {n} hn => h.N_conj hn
      S_cover := fun {s} hs => h.S_cover hs
      conj_mem_RR := fun {x} hx {ρ} hρ => conj_mem_RR h hx hρ
      inf_R_R'_eq := inf_R_R'_eq h
      eq_one_or_z_of_mem_zpowers := fun {w} hw => eq_one_or_z_of_mem_zpowers h hw
      struct := struct h h11 h16 h4
      exists_comm_not_mem := fun {m} hm hmn => exists_comm_not_mem h.hqR' h.hzR' h.R'_le_N hN2 (fun y hy => h.conj_R'_of_mem_N hy) hF hm hmn
      squaresSub_conj_mem := fun {g} hg {x} hx => squaresSub_conj_mem hg hx }


theorem exists_comm_not_mem_R {s : G} (hsN : s ∈ Nsub S R) (hsn : s ∉ R ⊔ R') :
    ∃ r ∈ R, ⁅s, r⁆ ∉ squaresSub R := by
  exact CFSG.ClassicalInvolution.Asc77.T7QEng.exists_comm_not_mem_R_gen (frame_of h h11 h16 h4)
    hsN hsn

theorem exists_coord_s {s : G} (hsN : s ∈ Nsub S R) (hsn : s ∉ R ⊔ R') :
    ∃ (a b : G) (n : ℕ) (i m : ℤ), QuatCoord R a b n ∧ Odd i ∧ Odd m ∧
      s * a * s⁻¹ = a ^ i ∧ s * b * s⁻¹ = b * a ^ m := by
  exact CFSG.ClassicalInvolution.Asc77.T7QEng.exists_coord_s_gen (frame_of h h11 h16 h4) hsN hsn

theorem sq_form {s : G} (hsN : s ∈ Nsub S R) (hst' : s * t' = t' * s)
    {a b : G} {n : ℕ} (c : QuatCoord R a b n) {i m : ℤ} (hi : Odd i) (hm : Odd m)
    (hsa : s * a * s⁻¹ = a ^ i) (hsb : s * b * s⁻¹ = b * a ^ m) :
    ∃ k δ : ℤ, s * s = a ^ k * (t' * a * t'⁻¹) ^ k * a ^ ((2 ^ n : ℤ) * δ) := by
  exact CFSG.ClassicalInvolution.Asc77.T7QEng.sq_form_gen (frame_of h h11 h16 h4) hsN hst' c hi hm
    hsa hsb

theorem closure_eq_S {s : G} (hsN : s ∈ Nsub S R) (hsn : s ∉ R ⊔ R') {a b : G} {n : ℕ}
    (c : QuatCoord R a b n) :
    Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G) := by
  exact CFSG.ClassicalInvolution.Asc77.T7QEng.closure_eq_S_gen (frame_of h h11 h16 h4) hsN hsn c

end Part

end T7Q

end CFSG.ClassicalInvolution.Asc77
