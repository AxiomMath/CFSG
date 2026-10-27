module

public import CFSG.ClassicalInvolution.Q3.Q3T7F25M4
import CFSG.ClassicalInvolution.Asc77.AscT7QDataEng
public import CFSG.ClassicalInvolution.Asc77.AscT7QShape

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.T7F25

section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7G2
open T7F2 T7DR
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]

variable {R N : Subgroup G} {a b : G} {n : ℕ}

theorem squaresSub_le_zpowers_sq (c : QuatCoord R a b n) :
    squaresSub R ≤ Subgroup.zpowers (a ^ 2) := by
  rw [squaresSub, Subgroup.closure_le]
  rintro x ⟨r, hr, rfl⟩
  rcases c.cover r hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨i, ?_⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    push_cast
    ring
  · have h := c.sq_mul i
    rw [h]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := c.hn; omega⟩
    have e : a ^ (2 ^ (n' + 1)) = (a ^ 2) ^ (2 ^ n') := by rw [← pow_mul, pow_succ']
    rw [e]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem zpow_odd_not_mem_zpowers_sq (c : QuatCoord R a b n) {j : ℤ} (hj : Odd j) :
    a ^ j ∉ Subgroup.zpowers (a ^ 2) := by
  rintro ⟨k, hk⟩
  simp only at hk
  have h1 : a ^ (2 * k) = a ^ j := by
    rw [← hk, zpow_mul]
    norm_cast
  rw [c.zpow_eq_iff] at h1
  have h2 : (2 : ℤ) ∣ 2 * k - j := by
    refine dvd_trans ?_ h1
    exact dvd_pow_self 2 (by omega)
  have h3 : (2 : ℤ) ∣ j := by
    have h4 : (2 : ℤ) ∣ 2 * k := dvd_mul_right 2 k
    have := dvd_sub h4 h2
    simpa using this
  exact (Int.not_even_iff_odd.mpr hj) (even_iff_two_dvd.mpr h3)

theorem exists_comm_not_mem {z : G}
    (hR : IsQuatSub R) (hz : IsUniqueInvolution R z)
    (hRN : R ≤ N) (hN2 : IsPGroup 2 N) (hNR : ∀ y ∈ N, conjSub y R = R)
    (hF : ∀ y ∈ N, ¬ IsFAut R y) {m : G} (hm : m ∈ N)
    (hmn : m ∉ R ⊔ (N ⊓ Subgroup.centralizer (R : Set G))) :
    ∃ r ∈ R, ⁅m, r⁆ ∉ squaresSub R := by
  obtain ⟨a, b, n, c, hinv⟩ := exists_coord hR hz hN2 hNR
  have s : Out.Setting R N a b n := ⟨c, hRN, hNR, hinv⟩
  have hH := Out.Hsub_le_sup s hF hN2
  obtain ⟨i, j, hi, hia, hjb⟩ := s.coord_of_mem hm
  have hjodd : Odd j := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    exact hmn (hH ((Out.mem_Hsub s).mpr ⟨hm, j, hev, hjb⟩))
  refine ⟨b, c.hb, fun hmem => ?_⟩
  have hcomm : ⁅m, b⁆ = a ^ (-j) := by
    rw [commutatorElement_def, hjb]
    calc b * a ^ j * b⁻¹ = a ^ (-j) := c.conj_zpow j
      _ = a ^ (-j) := rfl
  rw [hcomm] at hmem
  exact zpow_odd_not_mem_zpowers_sq c (j := -j) (by simpa using hjodd.neg)
    (squaresSub_le_zpowers_sq c hmem)

theorem squaresSub_conj_mem {R R' : Subgroup G} {g : G} (hg : ∀ r ∈ R, g * r * g⁻¹ ∈ R') {x : G}
    (hx : x ∈ squaresSub R) : g * x * g⁻¹ ∈ squaresSub R' := by
  have hle : squaresSub R ≤ (squaresSub R').comap (MulAut.conj g).toMonoidHom := by
    rw [squaresSub, Subgroup.closure_le]
    rintro y ⟨r, hr, rfl⟩
    show g * (r * r) * g⁻¹ ∈ squaresSub R'
    have e : g * (r * r) * g⁻¹ = (g * r * g⁻¹) * (g * r * g⁻¹) := by group
    rw [e]
    exact square_mem_squaresSub (hg r hr)
  exact hle hx

theorem not_isFAut_of_card_eight {R : Subgroup G} (hR2 : IsPGroup 2 R) (h8 : Nat.card ↥R = 8)
    (a : G) : ¬ IsFAut R a := by
  rintro ⟨-, -, Q, R₁, -, hQ, hR₁, hcard⟩
  have hR₁eq : R₁ = R := (hR₁.2.2 R le_rfl hR2 hR₁.1).symm
  have h8Q := hQ.eight_le
  rw [hR₁eq, h8] at hcard
  omega

theorem commutator_mem_squaresSub {R : Subgroup G} {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    ⁅x, y⁆ ∈ squaresSub R := by
  have e : ⁅x, y⁆ = (x * x) * ((x⁻¹ * y) * (x⁻¹ * y)) * (y⁻¹ * y⁻¹)⁻¹⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (square_mem_squaresSub hx)
    (square_mem_squaresSub (R.mul_mem (R.inv_mem hx) hy))) ?_
  rw [inv_inv]
  exact square_mem_squaresSub (R.inv_mem hy)

end T7G2
end Asc77
end

section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
namespace T7Q
open CFSG.ClassicalInvolution.Asc77.T7Q
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
open CFSG.ClassicalInvolution.Asc77.T7F2 CFSG.ClassicalInvolution.Asc77.T7G2
    CFSG.ClassicalInvolution.Asc77.T7DR
section Basic
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
theorem z_eq_pow {a b : G} {n : ℕ} (c : QuatCoord R a b n) : z = a ^ (2 ^ n) := by
  exact CFSG.ClassicalInvolution.Asc77.T7QEng.z_eq_pow_gen h.hzR c
end Basic
section Part
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t') (h11 : (S : Subgroup G)
    ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z) (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a)
  (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R'))
include h h11 h16 h4

private theorem frame_of : CFSG.ClassicalInvolution.Asc77.T7QEng.Frame S R R' z t' := by
  have hF : ∀ y ∈ Nsub S R, ¬ IsFAut R' y := fun y hy =>
    h16 y (mem_Nsub.mp hy).1
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
      conj_mem_RR := fun {x} hx {ρ} hρ => T7G2.conj_mem_RR h hx hρ
      inf_R_R'_eq := T7G2.inf_R_R'_eq h
      eq_one_or_z_of_mem_zpowers := fun {w} hw => T7G2.eq_one_or_z_of_mem_zpowers h hw
      struct := T7G2.struct h h11 h16 h4
      exists_comm_not_mem := fun {m} hm hmn => T7G2.exists_comm_not_mem h.hqR' h.hzR' h.R'_le_N hN2 (fun y hy => h.conj_R'_of_mem_N hy) hF hm hmn
      squaresSub_conj_mem := fun {g} hg {x} hx => T7G2.squaresSub_conj_mem hg hx }


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
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7Q
open CFSG.ClassicalInvolution.Asc77.T7Q
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ : G}
open CFSG.ClassicalInvolution.Asc77.T7F2 CFSG.ClassicalInvolution.Asc77.T7G2

theorem twoSubgroupsFourGenerated_of_index_four (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z) (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a)
    (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')) : TwoSubgroupsFourGenerated G := by
  obtain ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, hnf⟩ := T7G2.exists_swap_nonfused hyp
  have hT : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t' := ⟨hyp, ht'S, ht'2, ht'R⟩
  obtain ⟨s, hsN, hsn, hst'⟩ := T7G2.exists_s hT h11 h16 h4 hg hnf
  obtain ⟨a, b, n, i, m, c, hi, hm, hsa, hsb⟩ := exists_coord_s hT h11 h16 h4 hsN hsn
  obtain ⟨k, δ, hs2⟩ := sq_form hT h11 h16 h4 hsN hst' c hi hm hsa hsb
  have hS := closure_eq_S hT h11 h16 h4 hsN hsn c
  have hza := z_eq_pow hT c
  have ha'R' : t' * a * t'⁻¹ ∈ R' := by
    have := conj_mem_conjSub (n := t') c.ha
    rwa [ht'R] at this
  have hb'R' : t' * b * t'⁻¹ ∈ R' := by
    have := conj_mem_conjSub (n := t') c.hb
    rwa [ht'R] at this
  have htz : t' * a ^ (2 ^ n) * t'⁻¹ = a ^ (2 ^ n) := by
    rw [← hza]
    calc t' * z * t'⁻¹ = z * t' * t'⁻¹ := by rw [hyp.hzS t' ht'S]
      _ = z := by group
  apply T7DR.twoSubgroupsFourGenerated_of_sylow S
  intro H hH
  exact genLE_four_of_shape_sub hS c.hbab c.hbb c.pow_card ht'2 htz rfl rfl
    (hT.hcomm a c.ha _ ha'R') (hT.hcomm a c.ha _ hb'R') (hT.hcomm b c.hb _ ha'R')
    (hT.hcomm b c.hb _ hb'R') hi hm hsa hsb hst' hs2 hH
end T7Q
end Asc77
end
end CFSG.ClassicalInvolution.T7F25
