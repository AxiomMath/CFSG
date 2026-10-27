module

public import CFSG.LargeExtraspecial.S12InspFamDefs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2

namespace S12InspJ2

@[expose] def LRep (l : List ℕ) (g : Equiv.Perm (Fin 315)) : Prop :=
  l.length = 315 ∧ ∀ x : Fin 315, l.getD x 0 = g x

@[expose] def compL (t u : List ℕ) : List ℕ := u.map fun j => t.getD j 0

theorem LRep.comp {t u : List ℕ} {g h : Equiv.Perm (Fin 315)} (ht : LRep t g) (hu : LRep u h) :
    LRep (compL t u) (g * h) := by
  refine ⟨by rw [compL, List.length_map, hu.1], fun x => ?_⟩
  have hx : (x : ℕ) < u.length := by rw [hu.1]; exact x.2
  rw [compL, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hx), List.getElem_map,
    ← List.getD_eq_getElem _ 0 hx, hu.2 x, ht.2 (h x)]
  rfl

theorem LRep.one : LRep (List.range 315) 1 :=
  ⟨List.length_range, fun x => by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact x.2), List.getElem_range]
    rfl⟩

theorem LRep.unique {l : List ℕ} {g h : Equiv.Perm (Fin 315)} (hg : LRep l g) (hh : LRep l h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg.2 x).symm.trans (hh.2 x))

theorem LRep.eq_of_rep {l l' : List ℕ} {g : Equiv.Perm (Fin 315)} (hl : LRep l g)
    (hl' : LRep l' g) : l = l' := by
  refine List.ext_getElem (hl.1.trans hl'.1.symm) fun i h1 h2 => ?_
  have hi : i < 315 := hl.1 ▸ h1
  rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2]
  exact (hl.2 ⟨i, hi⟩).trans (hl'.2 ⟨i, hi⟩).symm

theorem LRep.of_rep {t : Array ℕ} {g : Equiv.Perm (Fin 315)} (ht : Rep 315 t g)
    (hs : t.size = 315) : LRep t.toList g := by
  refine ⟨by rw [Array.length_toList, hs], fun x => ?_⟩
  have hx : (x : ℕ) < t.size := by rw [hs]; exact x.2
  rw [← ht x, List.getD_eq_getElem _ _ (by rw [Array.length_toList]; exact hx),
    Array.getElem_toList, getElem!_pos t (x : ℕ) hx]

theorem orderOf_eq_five_of_lRep {l : List ℕ} {x : Equiv.Perm (Fin 315)} (hl : LRep l x)
    (h5 : compL l (compL l (compL l (compL l l))) = List.range 315)
    (h1 : l ≠ List.range 315) : orderOf x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ fun hx => h1 (hl.eq_of_rep (hx ▸ LRep.one))
  have hp := hl.comp (hl.comp (hl.comp (hl.comp hl)))
  rw [h5] at hp
  rw [show x ^ 5 = x * (x * (x * (x * x))) by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
  exact (LRep.unique hp LRep.one)

theorem strong_mem_P {j : ℕ} (hj : j < 7) :
    perm autStrong[j]! ∈ P := by
  have h := CFSG.Certificates.RawSchreierDatum.strong_get_mem_originalSubgroup autChain
    autChain_valid ⟨j, hj⟩
  have h2 : autChain.strong.get ⟨j, hj⟩ = permOfArr 315 autStrong[j]! :=
    CFSG.Certificates.RawSchreierDatum.ofArrays_strong_get _
  rw [autChain_originalSubgroup, h2] at h
  exact h

theorem inv_eq_of_lRep {l : List ℕ} {s : Equiv.Perm (Fin 315)} (hl : LRep l s)
    (h2 : compL l l = List.range 315) : s⁻¹ = s := by
  have hp := hl.comp hl
  rw [h2] at hp
  exact inv_eq_of_mul_eq_one_right (LRep.unique hp LRep.one)

theorem orderOf_witness_a :
    orderOf (permA * (perm autStrong[2]! * permA * (perm autStrong[2]!)⁻¹)) = 5 := by
  have hA := LRep.of_rep rep_permA (by decide +kernel)
  have hS := LRep.of_rep (rep_strong (j := 2) (by norm_num)) (by decide +kernel)
  rw [inv_eq_of_lRep hS (by decide +kernel), mul_assoc (perm autStrong[2]!)]
  exact orderOf_eq_five_of_lRep (hA.comp (hS.comp (hA.comp hS))) (by decide +kernel)
    (by decide +kernel)

theorem orderOf_witness_twoA :
    orderOf (permTwoA * (perm autStrong[3]! * permTwoA * (perm autStrong[3]!)⁻¹)) = 5 := by
  have hT := LRep.of_rep rep_permTwoA (by decide +kernel)
  have hS := LRep.of_rep (rep_strong (j := 3) (by norm_num)) (by decide +kernel)
  rw [inv_eq_of_lRep hS (by decide +kernel), mul_assoc (perm autStrong[3]!)]
  exact orderOf_eq_five_of_lRep (hT.comp (hS.comp (hT.comp hS))) (by decide +kernel)
    (by decide +kernel)

theorem exists_conj_orderOf_five {t : Equiv.Perm (Fin 315)}
    (htP : t ∈ P) (ht : orderOf t = 2) :
    ∃ w ∈ P, orderOf (t * (w * t * w⁻¹)) = 5 := by
  obtain ⟨r, hr, c, hc, rfl⟩ := inner_classes.1 t htP ht
  obtain ⟨w, hw, h5⟩ : ∃ w ∈ P, orderOf (r * (w * r * w⁻¹)) = 5 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, strong_mem_P (by norm_num), orderOf_witness_a⟩
    · exact ⟨_, strong_mem_P (by norm_num), orderOf_witness_twoA⟩
  refine ⟨c * w * c⁻¹, P.mul_mem (P.mul_mem hc hw) (P.inv_mem hc), ?_⟩
  have e : c * r * c⁻¹ * (c * w * c⁻¹ * (c * r * c⁻¹) * (c * w * c⁻¹)⁻¹) =
      MulAut.conj c (r * (w * r * w⁻¹)) := by
    rw [MulAut.conj_apply]
    group
  rw [e, MulEquiv.orderOf_eq]
  exact h5

end S12InspJ2

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_isSporadic_J2
    {g : G} {t : S.O} (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (h : NativeSporadic.IsSporadic (S.Xbar12 g) .J2) : False := by
  obtain ⟨e⟩ := h
  have e' : S.Xbar12 g ≃* NativeSporadic.J2 := e
  set ψ : S.Xbar12 g ≃* P := e'.trans nativeEquivP with hψ
  obtain ⟨-, ⟨d₀, hd₀, hcls⟩, hinv, hord, -⟩ := isTransClass34_Ebar12 ht htA hS
  have hd2 : orderOf ((ψ d₀ : P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact (hinv d₀ hd₀).2) (hinv d₀ hd₀).1
  obtain ⟨w, hw, h5⟩ := S12InspJ2.exists_conj_orderOf_five (ψ d₀).2 hd2
  set k : S.Xbar12 g := ψ.symm ⟨w, hw⟩ with hk
  have hmem : k * d₀ * k⁻¹ ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) :=
    (hcls _).mpr (isConj_iff.mpr ⟨k, rfl⟩)
  have h4 := hord d₀ hd₀ _ hmem
  have h5' : orderOf (d₀ * (k * d₀ * k⁻¹)) = 5 := by
    rw [← MulEquiv.orderOf_eq ψ, ← Subgroup.orderOf_coe]
    simpa [hk] using h5
  omega

end Setting

theorem inspJ2 : InspJ2 := by
  intro G _ _ _ S g t _ _ _ ht htA hS _ h
  exact (Setting.false_of_isSporadic_J2 ht htA hS h).elim

end CFSG.LargeExtraspecial
