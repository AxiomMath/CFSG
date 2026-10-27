module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PieceAction
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Projection

variable [CharP K 2]

theorem two_eq_zero_end : (2 : Module.End K V) = 0 := by
  have h : (2 : K) = 0 := CharTwo.two_eq_zero
  have := map_ofNat (algebraMap K (Module.End K V)) 2
  rw [← this, h, map_zero]

theorem sq_add_add_one_eq (g : Module.End K V) :
    g ^ 2 + g + 1 = (g - 1) ^ 2 + (g - 1) + 1 := by
  have h2 := two_eq_zero_end (K := K) (V := V)
  have : g ^ 2 + g + 1 = (g - 1) ^ 2 + (g - 1) + 1 + 2 * g := by noncomm_ring
  rw [this, h2]
  simp

omit [CharP K 2] in
theorem sub_one_proj {g : Module.End K V} (hg : g ^ 3 = 1) (v : V) :
    (g - 1) (g (g v) + g v + v) = 0 := by
  have h : (g - 1) * (g ^ 2 + g + 1) = 0 := by
    have : (g - 1) * (g ^ 2 + g + 1) = g ^ 3 - 1 := by noncomm_ring
    rw [this, hg, sub_self]
  have := congrArg (fun f : Module.End K V => f v) h
  simpa [pow_two, Module.End.mul_apply] using this

theorem proj_sub_self (g : Module.End K V) (v : V) :
    (g (g v) + g v + v) - v = (g - 1) ((g - 1) v) + (g - 1) v := by
  have h := sq_add_add_one_eq (K := K) g
  have := congrArg (fun f : Module.End K V => f v) h
  simp only [LinearMap.add_apply, pow_two, Module.End.mul_apply, Module.End.one_apply] at this
  rw [this]
  abel

end Projection

section Piece

variable [CharP K 2] [FiniteDimensional K V]

theorem finrank_ker_quotAct_sub_one_add {g : Module.End K V} (hg : g ^ 3 = 1)
    {F F' : Submodule K V} (hFF' : F ≤ F') (hF : ∀ v ∈ F, g v ∈ F) (hF' : ∀ v ∈ F', g v ∈ F') :
    finrank K (LinearMap.ker (quotAct g hF hF' - 1)) + finrank K ↥(F ⊓ LinearMap.ker (g - 1)) =
      finrank K ↥(F' ⊓ LinearMap.ker (g - 1)) := by
  set A := LinearMap.ker (g - 1) with hA
  let Φ : ↥(F' ⊓ A) →ₗ[K] PieceQ F F' :=
    (Submodule.mkQ (F.comap F'.subtype)).comp
      (LinearMap.codRestrict F' (F' ⊓ A).subtype (fun v => v.2.1))
  have hΦ : ∀ v : ↥(F' ⊓ A), Φ v = Submodule.Quotient.mk ⟨(v : V), v.2.1⟩ := fun v => rfl
  have hrange : LinearMap.range Φ = LinearMap.ker (quotAct g hF hF' - 1) := by
    ext q
    constructor
    · rintro ⟨v, rfl⟩
      rw [hΦ, LinearMap.mem_ker, LinearMap.sub_apply, quotAct_mk, Module.End.one_apply,
        ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
      have hv : (g - 1) (v : V) = 0 := v.2.2
      simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_sub]
      have : g (v : V) - (v : V) = 0 := by simpa using hv
      rw [this]
      exact F.zero_mem
    · intro hq
      induction q using Submodule.Quotient.induction_on with
      | H u =>
        rw [LinearMap.mem_ker, LinearMap.sub_apply, quotAct_mk, Module.End.one_apply,
          ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero] at hq
        simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_sub] at hq
        have hu1 : (g - 1) (u : V) ∈ F := by simpa using hq
        have hu2 : (g - 1) ((g - 1) (u : V)) ∈ F := by
          simpa using (show g ((g - 1) (u : V)) - (g - 1) (u : V) ∈ F from
            F.sub_mem (hF _ hu1) hu1)
        have hgu : g (u : V) ∈ F' := hF' _ u.2
        have hggu : g (g (u : V)) ∈ F' := hF' _ hgu
        have hw : g (g (u : V)) + g (u : V) + (u : V) ∈ F' ⊓ A :=
          ⟨F'.add_mem (F'.add_mem hggu hgu) u.2, sub_one_proj hg _⟩
        refine ⟨⟨_, hw⟩, ?_⟩
        rw [hΦ, Submodule.Quotient.eq]
        simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_sub]
        rw [proj_sub_self]
        exact F.add_mem hu2 hu1
  have hker : (LinearMap.ker Φ).map (F' ⊓ A).subtype = F ⊓ A := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hΦ, Submodule.Quotient.mk_eq_zero] at hw
      exact ⟨hw, w.2.2⟩
    · rintro ⟨hvF, hvA⟩
      refine ⟨⟨v, hFF' hvF, hvA⟩, ?_, rfl⟩
      rw [hΦ, Submodule.Quotient.mk_eq_zero]
      exact hvF
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  have h2 : finrank K ↥(LinearMap.ker Φ) = finrank K ↥(F ⊓ A) := by
    rw [← hker]
    exact (Submodule.finrank_map_subtype_eq _ _).symm
  rw [hrange] at h1
  omega

omit [CharP K 2] in
theorem finrank_pieceQ_add {F F' : Submodule K V} (hFF' : F ≤ F') :
    finrank K (PieceQ F F') + finrank K F = finrank K F' := by
  have h1 : finrank K (PieceQ F F') + finrank K (F.comap F'.subtype) = finrank K F' :=
    Submodule.finrank_quotient_add_finrank (F.comap F'.subtype)
  have h2 : finrank K (F.comap F'.subtype) = finrank K F :=
    (Submodule.comapSubtypeEquivOfLe hFF').finrank_eq
  omega

omit [CharP K 2] in
open scoped Classical in
theorem finrank_ker_quotAct_sub_one_of_scalar {g : Module.End K V} {F F' : Submodule K V}
    (hFF' : F ≤ F') (hF : ∀ v ∈ F, g v ∈ F) (hF' : ∀ v ∈ F', g v ∈ F') (c : K)
    (hc : ∀ v ∈ F', g v - c • v ∈ F) :
    finrank K (LinearMap.ker (quotAct g hF hF' - 1)) =
      if c = 1 then finrank K F' - finrank K F else 0 := by
  have hact : ∀ q : PieceQ F F', (quotAct g hF hF' - 1) q = (c - 1) • q := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H u =>
      rw [LinearMap.sub_apply, quotAct_mk, Module.End.one_apply, sub_smul, one_smul,
        ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.eq]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_sub,
        SetLike.val_smul]
      convert hc (u : V) u.2 using 1
      abel
  by_cases h : c = 1
  · simp only [h, ite_true]
    have : LinearMap.ker (quotAct g hF hF' - 1) = ⊤ := by
      rw [eq_top_iff]
      intro q _
      rw [LinearMap.mem_ker, hact, h, sub_self, zero_smul]
    rw [this, finrank_top]
    have := finrank_pieceQ_add hFF'
    omega
  · simp only [h, ite_false]
    have : LinearMap.ker (quotAct g hF hF' - 1) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro q hq
      rw [hact] at hq
      exact (smul_eq_zero.1 hq).resolve_left (sub_ne_zero.2 h)
    rw [this, finrank_bot]

end Piece

section Filtration

variable [CharP K 2] [FiniteDimensional K V]

omit [CharP K 2] [FiniteDimensional K V] in
theorem mem_stabPair_of_pow_three {x : LinearMap.GeneralLinearGroup K V} (hx : x ^ 3 = 1)
    {F F' : Submodule K V} (hF : ∀ v ∈ F, (x : Module.End K V) v ∈ F)
    (hF' : ∀ v ∈ F', (x : Module.End K V) v ∈ F') : x ∈ stabPair F F' := by
  have hinv : x⁻¹ = x ^ 2 := by
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← pow_succ' x 2]
    exact hx
  have key : ∀ G : Submodule K V, (∀ v ∈ G, (x : Module.End K V) v ∈ G) →
      ∀ v ∈ G, ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ G := by
    intro G hG v hv
    rw [hinv, pow_two, Units.val_mul, Module.End.mul_apply]
    exact hG _ (hG _ hv)
  exact ⟨hF, hF', key F hF, key F' hF'⟩

variable {N : ℕ}

theorem finrank_ker_eq_sum_pieces (x : LinearMap.GeneralLinearGroup K V) (hx : x ^ 3 = 1)
    (F : ℕ → Submodule K V) (hF0 : F 0 = ⊥) (hFmono : Monotone F) (hFN : F N = ⊤)
    (hstab : ∀ i, x ∈ stabPair (F i) (F (i + 1))) :
    finrank K (LinearMap.ker ((x : Module.End K V) - 1)) =
      ∑ i ∈ Finset.range N,
        finrank K (LinearMap.ker (quotEnd (F i) (F (i + 1)) ⟨x, hstab i⟩ - 1)) := by
  have hx' : (x : Module.End K V) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx]; rfl
  let a : ℕ → ℕ := fun i => finrank K ↥(F i ⊓ LinearMap.ker ((x : Module.End K V) - 1))
  have hmono : Monotone a := fun i j hij =>
    Submodule.finrank_mono (inf_le_inf_right _ (hFmono hij))
  have hterm : ∀ i, finrank K (LinearMap.ker (quotEnd (F i) (F (i + 1)) ⟨x, hstab i⟩ - 1)) =
      a (i + 1) - a i := by
    intro i
    have := finrank_ker_quotAct_sub_one_add (g := (x : Module.End K V)) hx'
      (hFmono (Nat.le_add_right i 1)) (hstab i).1 (hstab i).2.1
    show finrank K (LinearMap.ker (quotAct (x : Module.End K V) (hstab i).1 (hstab i).2.1 - 1))
      = _
    exact Nat.eq_sub_of_add_eq this
  simp only [hterm]
  rw [Finset.sum_range_tsub hmono N]
  show _ = finrank K ↥(F N ⊓ LinearMap.ker ((x : Module.End K V) - 1)) -
    finrank K ↥(F 0 ⊓ LinearMap.ker ((x : Module.End K V) - 1))
  rw [hFN, hF0, top_inf_eq, bot_inf_eq, finrank_bot, Nat.sub_zero]

theorem finrank_ker_eq_sum_pieces' (x : LinearMap.GeneralLinearGroup K V) (hx : x ^ 3 = 1)
    (F : ℕ → Submodule K V) (hF0 : F 0 = ⊥) (hFmono : Monotone F) (hFN : F N = ⊤)
    (hstab : ∀ i, ∀ v ∈ F i, (x : Module.End K V) v ∈ F i) :
    finrank K (LinearMap.ker ((x : Module.End K V) - 1)) =
      ∑ i ∈ Finset.range N,
        finrank K (LinearMap.ker (quotEnd (F i) (F (i + 1))
          ⟨x, mem_stabPair_of_pow_three hx (hstab i) (hstab (i + 1))⟩ - 1)) :=
  finrank_ker_eq_sum_pieces x hx F hF0 hFmono hFN
    fun i => mem_stabPair_of_pow_three hx (hstab i) (hstab (i + 1))

theorem finrank_le_finrank_ker_add_of_trivial_pieces (x : LinearMap.GeneralLinearGroup K V)
    (hx : x ^ 3 = 1) (F : ℕ → Submodule K V) (hF0 : F 0 = ⊥) (hFmono : Monotone F)
    (hFN : F N = ⊤) (hstab : ∀ i, ∀ v ∈ F i, (x : Module.End K V) v ∈ F i) (S : Finset ℕ)
    (htriv : ∀ i, i ∉ S → ∀ v ∈ F (i + 1), ((x : Module.End K V) - 1) v ∈ F i) :
    finrank K V ≤ finrank K (LinearMap.ker ((x : Module.End K V) - 1)) +
      ∑ i ∈ S, (finrank K (F (i + 1)) - finrank K (F i)) := by
  have hf : Monotone fun i => finrank K (F i) := fun i j hij =>
    Submodule.finrank_mono (hFmono hij)
  rw [finrank_ker_eq_sum_pieces' x hx F hF0 hFmono hFN hstab]
  have htel : ∑ i ∈ Finset.range N, (finrank K (F (i + 1)) - finrank K (F i)) = finrank K V := by
    have h : ∑ i ∈ Finset.range N, (finrank K (F (i + 1)) - finrank K (F i)) =
        finrank K (F N) - finrank K (F 0) := Finset.sum_range_tsub hf N
    rw [hFN, hF0, finrank_top, finrank_bot, Nat.sub_zero] at h
    exact h
  rw [← htel]
  have hle : ∀ i ∈ Finset.range N, finrank K (F (i + 1)) - finrank K (F i) ≤
      finrank K (LinearMap.ker (quotEnd (F i) (F (i + 1))
        ⟨x, mem_stabPair_of_pow_three hx (hstab i) (hstab (i + 1))⟩ - 1)) +
        (if i ∈ S then finrank K (F (i + 1)) - finrank K (F i) else 0) := by
    intro i _
    split_ifs with hi
    · omega
    · have h := finrank_ker_quotAct_sub_one_of_scalar (g := (x : Module.End K V))
        (hFmono (Nat.le_add_right i 1)) (hstab i) (hstab (i + 1)) 1
        (fun v hv => by simpa using htriv i hi v hv)
      simp only [ite_true] at h
      have hq : finrank K (LinearMap.ker (quotEnd (F i) (F (i + 1))
          ⟨x, mem_stabPair_of_pow_three hx (hstab i) (hstab (i + 1))⟩ - 1)) =
          finrank K (F (i + 1)) - finrank K (F i) := h
      omega
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
  refine add_le_add le_rfl ?_
  exact Finset.sum_le_sum_of_subset Finset.inter_subset_right

end Filtration

end CFSG.HardMathSupport.Curtis.UnitaryLevi
