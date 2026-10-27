module

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Co1Rank
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open scoped Matrix

private noncomputable def elt (i : Fin 6) (p : ZMod 3 × ZMod 3) :
    ↥(ElemThree.E.subgroupOf GA) :=
  ⟨⟨ElemThree.a 0 ^ p.1.val * ElemThree.a i ^ p.2.val, H1017.H1016M3.Co1Sylow.E_le_GA
      (mul_mem (pow_mem (a_mem_E 0) _) (pow_mem (a_mem_E i) _))⟩,
    Subgroup.mem_subgroupOf.2 (mul_mem (pow_mem (a_mem_E 0) _) (pow_mem (a_mem_E i) _))⟩

private theorem mulVec_eq_of_inv_mul_mem {K : Subgroup ↥GA} {x y : ↥GA} (hxy : x⁻¹ * y ∈ K)
    {v : Fin 24 → ZMod 2}
    (hv : ∀ g ∈ K, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) :
    ((y : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v =
      ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v := by
  have h := hv _ hxy
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at h
  conv_rhs => rw [← h]
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]


private theorem a_pow_mulVec_plane (i : Fin 6) {j : Fin 12} {w : Fin 24 → ZMod 2}
    (hw : w ∈ plane j) (n : ℕ) :
    ((ElemThree.a i ^ n : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w =
      (zM ^ ((ElemThree.γ j i).val * n)) *ᵥ w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec, ih,
      a_mulVec_plane i (zM_pow_mulVec_mem_plane hw _), Matrix.mulVec_mulVec, ← pow_add,
      mul_add_one, add_comm]

private theorem elt_mulVec (i : Fin 6) (p : ZMod 3 × ZMod 3) {j : Fin 12}
    {w : Fin 24 → ZMod 2} (hw : w ∈ plane j) :
    ((((elt i p : ↥(ElemThree.E.subgroupOf GA)) : ↥GA) : GL24) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w =
      (zM ^ (p.1.val + (ElemThree.γ j i).val * p.2.val)) *ᵥ w := by
  change ((ElemThree.a 0 ^ p.1.val * ElemThree.a i ^ p.2.val : GL24) :
    Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w = _
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, a_pow_mulVec_plane i hw,
    a_pow_mulVec_plane 0 (zM_pow_mulVec_mem_plane hw _), γ_zero,
    show (1 : ZMod 3).val = 1 from rfl, one_mul, Matrix.mulVec_mulVec, ← pow_add]

private theorem cast_eq_of_zM_pow {w : Fin 24 → ZMod 2} (hw : w ≠ 0) {m n : ℕ}
    (h : (zM ^ m) *ᵥ w = (zM ^ n) *ᵥ w) : (m : ZMod 3) = n := by
  have h3 : (zM ^ (2 * n + m)) *ᵥ w = w := by
    rw [pow_add, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec, ← pow_add,
      show 2 * n + n = 3 * n by ring, pow_mul, zM_cube, one_pow, Matrix.one_mulVec]
  have := zM_pow_mulVec_eq_self hw h3
  exact (ZMod.natCast_eq_natCast_iff' m n 3).2 (by omega)

private theorem mulVec_eq_of_sum {x : GL24} (hx : x ∈ ElemThree.E)
    {u : Fin 12 → Fin 24 → ZMod 2} (hu : ∀ k, u k ∈ plane k)
    (h : (x : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ ∑ k, u k = ∑ k, u k) (k : Fin 12) :
    (x : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ u k = u k := by
  rw [Matrix.mulVec_sum] at h
  exact plane_decomp_unique (fun k => E_mulVec_mem_plane hx (hu k)) hu h k

private theorem not_fix_two_planes {K : Subgroup ↥GA} (hKE : K ≤ ElemThree.E.subgroupOf GA)
    (hKc : Nat.card K * 3 = 3 ^ 6) {j k : Fin 12} (hjk : j ≠ k) {w u : Fin 24 → ZMod 2}
    (hw : w ∈ plane j) (hu : u ∈ plane k) (hw0 : w ≠ 0) (hu0 : u ≠ 0)
    (hwK : ∀ x ∈ K, ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w = w)
    (huK : ∀ x ∈ K, ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ u = u) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (γ_injective.ne hjk)
  have hq : Nat.card (↥(ElemThree.E.subgroupOf GA) ⧸ K.subgroupOf (ElemThree.E.subgroupOf GA)) =
      3 := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf (ElemThree.E.subgroupOf GA))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv,
      H1017.H1016M3.Co1Sylow.card_EG, Subgroup.index_eq_card] at h1
    have hpos : 0 < Nat.card K := Nat.pos_of_ne_zero fun h0 => by
      rw [h0] at hKc
      norm_num at hKc
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hKc.symm)
  haveI : Finite (↥(ElemThree.E.subgroupOf GA) ⧸ K.subgroupOf (ElemThree.E.subgroupOf GA)) :=
    Nat.finite_of_card_ne_zero (by rw [hq]; norm_num)
  have hninj : ¬ Function.Injective fun p : ZMod 3 × ZMod 3 => (QuotientGroup.mk (elt i p) :
      ↥(ElemThree.E.subgroupOf GA) ⧸ K.subgroupOf (ElemThree.E.subgroupOf GA)) := fun hinj => by
    have h := Nat.card_le_card_of_injective _ hinj
    rw [hq, Nat.card_prod, Nat.card_zmod] at h
    norm_num at h
  obtain ⟨p, p', hpp, hne⟩ := Function.not_injective_iff.mp hninj
  have hy : ((elt i p : ↥GA))⁻¹ * (elt i p' : ↥GA) ∈ K := by
    have h := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hpp)
    rwa [Subgroup.coe_mul, Subgroup.coe_inv] at h
  have key : ∀ {l : Fin 12} {v : Fin 24 → ZMod 2}, v ∈ plane l → v ≠ 0 →
      (∀ x ∈ K, ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) →
      p'.1 + ElemThree.γ l i * p'.2 = p.1 + ElemThree.γ l i * p.2 := by
    intro l v hv hv0 hvK
    have h := mulVec_eq_of_inv_mul_mem hy hvK
    rw [elt_mulVec i p' hv, elt_mulVec i p hv] at h
    have h' := cast_eq_of_zM_pow hv0 h
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val] at h'
    exact h'
  have hj' := key hw hw0 hwK
  have hk' := key hu hu0 huK
  have h2 : (ElemThree.γ j i - ElemThree.γ k i) * (p'.2 - p.2) = 0 := by
    linear_combination hj' - hk'
  rcases mul_eq_zero.mp h2 with h | h
  · exact hi (sub_eq_zero.mp h)
  · have ht : p'.2 = p.2 := sub_eq_zero.mp h
    rw [ht] at hj'
    exact hne (Prod.ext (add_right_cancel hj').symm ht.symm)

private theorem exists_plane_of_fixed {K : Subgroup ↥GA} (hKE : K ≤ ElemThree.E.subgroupOf GA)
    (hKc : Nat.card K * 3 = 3 ^ 6) : ∃ j, ∀ v : Fin 24 → ZMod 2,
      (∀ x ∈ K, ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) → v ∈ plane j := by
  have hcomp : ∀ u : Fin 12 → Fin 24 → ZMod 2, (∀ l, u l ∈ plane l) →
      (∀ x ∈ K, ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ ∑ l, u l = ∑ l, u l) →
      ∀ l, ∀ x ∈ K, ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ u l = u l :=
    fun u hu hv l x hx => mulVec_eq_of_sum (Subgroup.mem_subgroupOf.1 (hKE hx)) hu (hv x hx) l
  by_cases h : ∃ j, ∃ w ∈ plane j, w ≠ 0 ∧
      ∀ x ∈ K, ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w = w
  · obtain ⟨j, w, hw, hw0, hwK⟩ := h
    refine ⟨j, fun v hv => ?_⟩
    obtain ⟨u, hu, rfl⟩ := exists_plane_decomp v
    rw [Finset.sum_eq_single j]
    · exact hu j
    · intro l _ hl
      by_contra h0
      exact not_fix_two_planes hKE hKc hl (hu l) hw h0 hw0 (hcomp u hu hv l) hwK
    · exact fun hj => absurd (Finset.mem_univ j) hj
  · refine ⟨0, fun v hv => ?_⟩
    obtain ⟨u, hu, rfl⟩ := exists_plane_decomp v
    have h0 : ∀ l, u l = 0 := fun l => by
      by_contra h0
      exact h ⟨l, u l, hu l, h0, hcomp u hu hv l⟩
    rw [Finset.sum_eq_zero fun l _ => h0 l]
    exact Submodule.zero_mem _

theorem card_fixed_le_of_hyperplane_three_six {F H : Subgroup ↥CFSG.Sporadic.Co1Schreier.GA}
    (hF : IsElemAbelian 3 F) (hFc : Nat.card F = 3 ^ 6) (hHF : H ≤ F)
    (hHc : Nat.card H * 3 = Nat.card F) :
    Nat.card {v : Fin 24 → ZMod 2 // ∀ j ∈ H,
      ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} ≤ 2 ^ 2 := by
  haveI : Finite ↥GA := Co1T.finite_GA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : Nat.card Co1T.Qg = 3 ^ (Nat.card ↥GA).factorization 3 := by
    rw [Co1T.card_Qg, ← Subgroup.card_top (G := ↥GA), Co1T.factorization_card_GA]
  obtain ⟨g, hg⟩ :=
    CFSG.LieType.BorelTits.exists_conj_mem_sylow (Sylow.ofCard Co1T.Qg hQ) hF.isPGroup
  have hcard : ∀ K : Subgroup ↥GA, Nat.card (K.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card K :=
    fun K => Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hFQ : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ Co1T.Qg := by
    rintro _ ⟨r, hr, rfl⟩
    have h := hg r hr
    rw [Sylow.coe_ofCard] at h
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hEq : F.map (MulAut.conj g⁻¹).toMonoidHom = ElemThree.E.subgroupOf GA :=
    (H1017.H1016M3.Co1Sylow.card_le_or_eq_of_le_Qg hFQ (hF.map _)).resolve_left (by
      rw [hcard, hFc]
      norm_num)
  obtain ⟨j, hj⟩ := exists_plane_of_fixed ((Subgroup.map_mono hHF).trans hEq.le)
    (by rw [hcard, hHc, hFc])
  have hfix : ∀ v : Fin 24 → ZMod 2,
      (∀ y ∈ H, ((y : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) →
      (((g⁻¹ : ↥GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ plane j := by
    refine fun v hv => hj _ ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Matrix.mulVec_mulVec,
      ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_right, Subgroup.coe_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, hv y hy]
  have hinj : Function.Injective fun v : {v : Fin 24 → ZMod 2 // ∀ y ∈ H,
      ((y : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} =>
      (⟨_, hfix v.1 v.2⟩ : plane j) := by
    intro v w h
    have h' := congrArg (fun x : plane j =>
      (((g : ↥GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ (x : Fin 24 → ZMod 2)) h
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] at h'
    exact Subtype.ext h'
  calc _ ≤ Nat.card (plane j) := Nat.card_le_card_of_injective _ hinj
    _ = 2 ^ 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_plane]

end CFSG.LocalAnalysis.GLTheoremA.H301B
