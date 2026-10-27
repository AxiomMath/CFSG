module

public import CFSG.FeitThompson.Representations.CentralPrimeOrientedProjection
import CFSG.FeitThompson.Representations.JoinedLayersStrictBoundRemainingChars
import CFSG.FeitThompson.Representations.CentralPrimeCoherentCentralLinearSupport
public import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CentralPrimeInduction

open Subgroup
open NormalLinearInduced (indFamLinear)

variable {G : Type*} [Group G] {p a : ℕ} {L P E Z : Subgroup G}

noncomputable def centralDetectFam (L P Z : Subgroup G) [Fintype ↥L] : Set (↥L → ℂ) :=
  indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))

theorem centralDetectFam_eq_indFamDetect (L P Z : Subgroup G) [Fintype ↥L] :
    centralDetectFam L P Z
      = indFamDetect (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) := (rfl)

theorem centralDetectFam_eq_indFam (L P Z : Subgroup G) [Fintype ↥L] :
    centralDetectFam L P Z
      = indFam (P.subgroupOf L) (irrDetect ℂ ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) :=
  indFamDetect_eq_indFam _ _

theorem mem_centralDetectFam [Fintype ↥L] {f : ↥L → ℂ} :
    f ∈ centralDetectFam L P Z ↔ ∃ θ ∈ irrDetect ℂ ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)),
      indClassFun (P.subgroupOf L) θ = f := mem_indFamDetect _

theorem centralDetectFam_subset_centralFam [Fintype ↥L] :
    centralDetectFam L P Z ⊆ centralFam L P := by
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := mem_centralDetectFam.1 hf
  refine mem_centralFam.2 ⟨θ, mem_nonprincipalIrr.2 ⟨?_, ne_one_of_mem_irrDetect hθ⟩, rfl⟩
  rw [Irr_eq_irrChar]
  exact (mem_irrDetect.1 hθ).1

theorem star_mem_centralDetectFam [Fintype ↥L] {f : ↥L → ℂ}
    (hf : f ∈ centralDetectFam L P Z) : star f ∈ centralDetectFam L P Z := by
  have : Finite ↥(P.subgroupOf L) := Subtype.finite
  rw [centralDetectFam_eq_indFam] at hf ⊢
  exact DisjointCoherentFamilies.star_mem_indFam _ (fun _ hθ => conj_mem_irrDetect hθ) hf

theorem centralFam_subset_indFam_Irr [Fintype ↥L] :
    centralFam L P ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)) := by
  rw [centralFam_eq_indFam]
  exact indFam_mono _ nonprincipalIrr_subset_Irr

theorem centralDetectFam_union_indFamLinear_subset_indFam_Irr [Fintype ↥L] :
    centralDetectFam L P Z ∪ indFamLinear (P.subgroupOf L)
      ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)) :=
  Set.union_subset (centralDetectFam_subset_centralFam.trans centralFam_subset_indFam_Irr)
    (NormalLinearInduced.indFamLinear_subset_indFam_Irr _)

theorem centralDetectFam_union_indFamLinear_subset_centralFam [Fintype ↥L] :
    centralDetectFam L P Z ∪ indFamLinear (P.subgroupOf L) ⊆ centralFam L P :=
  Set.union_subset centralDetectFam_subset_centralFam indFamLinear_subset_centralFam

theorem exists_pos_apply_one_of_mem_centralDetectFam [Fintype ↥L] {f : ↥L → ℂ}
    (hf : f ∈ centralDetectFam L P Z) :
    ∃ n : ℕ, 0 < n ∧ f 1 = ((P.subgroupOf L).index : ℂ) * n := by
  refine exists_pos_apply_one_eq_index_mul ?_
  rw [← centralFam_eq_indFam]
  exact centralDetectFam_subset_centralFam hf

namespace IsCentralPrimeInduction

variable (h : IsCentralPrimeInduction p a L P E Z)

include h

theorem apply_one_of_mem_indFamLinear [Fintype ↥L] {f : ↥L → ℂ}
    (hf : f ∈ indFamLinear (P.subgroupOf L)) : f 1 = ((P.subgroupOf L).index : ℂ) :=
  NormalLinearInduced.apply_one_of_mem_indFamLinear _ hf

theorem inter_centralDetectFam_indFamLinear_eq_empty [Fintype ↥L] :
    centralDetectFam L P Z ∩ indFamLinear (P.subgroupOf L) = ∅ := by
  have := h.normal_subgroupOf
  have := h.normal_Z_subgroupOf
  rw [centralDetectFam_eq_indFamDetect]
  refine inter_indFamDetect_indFamLinear_eq_empty
    (fun x hx => mem_subgroupOf.2 (h.Z_le_P (mem_subgroupOf.1 hx))) ?_
  rw [commutator_subgroupOf_eq h.P_le]
  exact Subgroup.subgroupOf_mono L h.Z_le_commutator

theorem isCoherent_indFamLinear [Fintype G] [Fintype ↥L] [(P.subgroupOf L).Normal] :
    IsCoherent (indFamLinear (P.subgroupOf L))
      (tiIndCharSpanZeroHom h.isTI
        (NormalLinearInduced.indFamLinear_subset_indFam_Irr (P.subgroupOf L))
        h.indFamLinear_subset_Irr) :=
  isCoherent_tiIndCharSpanZeroHom h.isTI (NormalLinearInduced.finite_indFamLinear _) _ _
    (fun _ hf => h.apply_one_of_mem_indFamLinear hf)

end IsCentralPrimeInduction

theorem centralDetectFam_nonempty [Fintype ↥L] [Finite G]
    (h : IsCentralPrimeInduction p a L P E Z) : (centralDetectFam L P Z).Nonempty := by
  classical
  have : Fintype ↥(P.subgroupOf L) := Fintype.ofFinite _
  have hPn := h.normal_subgroupOf
  have hZlPl : Z.subgroupOf L ≤ P.subgroupOf L := Subgroup.subgroupOf_mono L h.Z_le_P
  have hZc := IsCentralPrimeInduction.Z_subgroupOf_P_le_center h
  have hp : Fact p.Prime := ⟨h.prime⟩
  have hcard : Nat.card ↥((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZlPl).toEquiv]
    exact IsCentralPrimeInduction.natCard_Z_subgroupOf h
  have hfin : Finite ↥((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) := Subtype.finite
  have hcyc := isCyclic_of_prime_card (α := ↥((Z.subgroupOf L).subgroupOf (P.subgroupOf L))) hcard
  have hnt : Nontrivial ↥((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hcard]; exact h.prime.one_lt
  have hsolv : Group.IsSolvable ↥((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) :=
    isSolvable_of_isMulCommutative
  obtain ⟨lam, hlamIrr, hlam1, hlamne⟩ :=
    exists_mem_Irr_apply_one_eq_one_and_ne_one ↥((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
  set I := centralIrrFinset ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) lam with hI
  have hidx : ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)).index = Z.relIndex P := by
    rw [show ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)).index
        = (Z.subgroupOf L).relIndex (P.subgroupOf L) from rfl,
      Subgroup.relIndex_subgroupOf h.P_le]
  have hsq : ∑ θ ∈ I, θ 1 ^ 2 = ((Z.relIndex P : ℕ) : ℂ) := by
    rw [hI, sum_sq_apply_one_centralIrrFinset hZc hlamIrr hlam1, hidx]
  have hrne : ((Z.relIndex P : ℕ) : ℂ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 ?_
    have : Finite (↥(P.subgroupOf L) ⧸ (Z.subgroupOf L).subgroupOf (P.subgroupOf L)) :=
      Quotient.finite _
    rw [show Z.relIndex P = ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)).index from hidx.symm]
    exact Subgroup.index_ne_zero_of_finite
  have hIne : I.Nonempty := by
    rcases Finset.eq_empty_or_nonempty I with hce | hce
    · rw [hce, Finset.sum_empty] at hsq
      exact absurd hsq.symm hrne
    · exact hce
  obtain ⟨θ, hθ⟩ := hIne
  have hθIrr : θ ∈ Irr ↥(P.subgroupOf L) := (mem_centralIrrFinset.1 hθ).1
  refine ⟨indClassFun (P.subgroupOf L) θ, mem_centralDetectFam.2 ⟨θ, ?_, rfl⟩⟩
  refine mem_irrDetect.2 ⟨by rw [← Irr_eq_irrChar]; exact hθIrr, ?_⟩
  have heq := (centralLinearChar_eq_iff_mem_centralIrrFinset hZc hθIrr).2 hθ
  rw [← centralLinearChar_ne_one_iff hθIrr hZc, heq]
  exact hlamne

theorem exists_centralIrrFinset_of_mem_centralDetectFam [Fintype ↥L] [Finite G]
    (h : IsCentralPrimeInduction p a L P E Z) {χ : ↥L → ℂ}
    (hχ : χ ∈ centralDetectFam L P Z) :
    ∃ (I : Finset (↥(P.subgroupOf L) → ℂ)) (θ₀ : ↥(P.subgroupOf L) → ℂ)
      (d : (↥(P.subgroupOf L) → ℂ) → ℤ) (lam : ↥(Z.subgroupOf L) → ℂ),
      θ₀ ∈ I ∧ indClassFun (P.subgroupOf L) θ₀ = χ ∧
      (∀ θ ∈ I, indClassFun (P.subgroupOf L) θ ∈ centralDetectFam L P Z) ∧
      (∀ θ ∈ I, 1 ≤ d θ) ∧ (∀ θ ∈ I, θ 1 = ((d θ : ℤ) : ℂ)) ∧
      lam ∈ Irr ↥(Z.subgroupOf L) ∧ lam ≠ 1 ∧
      ∑ θ ∈ I, ((d θ : ℤ) : ℂ) • indClassFun (P.subgroupOf L) θ
        = indClassFun (Z.subgroupOf L) lam ∧
      ∑ θ ∈ I, d θ ^ 2 = (Z.relIndex P : ℤ) := by
  classical
  have : Fintype ↥(P.subgroupOf L) := Fintype.ofFinite _
  have hPn := h.normal_subgroupOf
  have hZlPl : Z.subgroupOf L ≤ P.subgroupOf L := Subgroup.subgroupOf_mono L h.Z_le_P
  have hZc := IsCentralPrimeInduction.Z_subgroupOf_P_le_center h
  obtain ⟨θ₀, hθ₀, hθ₀χ⟩ := mem_centralDetectFam.1 hχ
  have hθ₀Irr : θ₀ ∈ Irr ↥(P.subgroupOf L) := by
    rw [Irr_eq_irrChar]; exact (mem_irrDetect.1 hθ₀).1
  set lam := centralLinearChar hθ₀Irr hZc with hlamdef
  have hlamIrr : ⇑lam ∈ Irr ↥((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) :=
    centralLinearChar_mem_Irr hθ₀Irr hZc
  have hlamne : ⇑lam ≠ 1 := (centralLinearChar_ne_one_iff hθ₀Irr hZc).2 (mem_irrDetect.1 hθ₀).2
  set I := centralIrrFinset ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ⇑lam with hI
  have hθ₀mem : θ₀ ∈ I := (centralLinearChar_eq_iff_mem_centralIrrFinset hZc hθ₀Irr).1 rfl
  have hIdet : ∀ θ ∈ I, θ ∈ irrDetect ℂ ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) := by
    intro θ hθ
    have hθIrr : θ ∈ Irr ↥(P.subgroupOf L) := (mem_centralIrrFinset.1 hθ).1
    refine mem_irrDetect.2 ⟨by rw [← Irr_eq_irrChar]; exact hθIrr, ?_⟩
    have heq := (centralLinearChar_eq_iff_mem_centralIrrFinset hZc hθIrr).2 hθ
    rw [← centralLinearChar_ne_one_iff hθIrr hZc, heq]
    exact hlamne
  set eqv := Subgroup.subgroupOfEquivOfLe hZlPl with heqvdef
  set lam' : ↥(Z.subgroupOf L) → ℂ := ⇑lam ∘ eqv.symm with hlam'
  have hlam'Irr : lam' ∈ Irr ↥(Z.subgroupOf L) :=
    FrobeniusInduction.mem_Irr_comp_mulEquiv hlamIrr eqv.symm
  have hcomp : lam' ∘ eqv = ⇑lam := by funext z; simp [hlam']
  have hlam'ne : lam' ≠ 1 := by
    intro hcc
    refine hlamne ?_
    rw [← hcomp, hcc]
    funext z; simp
  choose! n hnpos hn using fun θ (hθ : θ ∈ I) =>
    NormalInducedFamily.exists_apply_one_eq_of_mem_Irr ((mem_centralIrrFinset.1 hθ).1)
  have hidx : ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)).index = Z.relIndex P := by
    rw [show ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)).index
        = (Z.subgroupOf L).relIndex (P.subgroupOf L) from rfl,
      Subgroup.relIndex_subgroupOf h.P_le]
  have hsq : ∑ θ ∈ I, θ 1 ^ 2 = ((Z.relIndex P : ℕ) : ℂ) := by
    rw [hI, sum_sq_apply_one_centralIrrFinset hZc hlamIrr (map_one lam), hidx]
  have htrans := AbelianInertiaBlock.indClassFun_indClassFun (P.subgroupOf L) hZlPl lam'
  rw [hcomp, indClassFun_eq_sum_centralIrrFinset hZc hlamIrr,
    AbelianInertiaBlock.indClassFun_sum] at htrans
  rw [Finset.sum_congr rfl fun θ (_ : θ ∈ I) => indClassFun_smul (P.subgroupOf L) (θ 1) θ]
    at htrans
  refine ⟨I, θ₀, fun θ => (n θ : ℤ), lam', hθ₀mem, hθ₀χ,
    fun θ hθ => mem_centralDetectFam.2 ⟨θ, hIdet θ hθ, rfl⟩, fun θ hθ => ?_, fun θ hθ => ?_,
    hlam'Irr, hlam'ne, ?_, ?_⟩
  · have h0 := hnpos θ hθ
    beta_reduce
    omega
  · beta_reduce
    rw [hn θ hθ]; push_cast; ring
  · beta_reduce
    rw [← htrans]
    exact Finset.sum_congr rfl fun θ hθ => by rw [hn θ hθ]; push_cast; ring_nf
  · have h2 : ((∑ θ ∈ I, (n θ : ℤ) ^ 2 : ℤ) : ℂ) = ((Z.relIndex P : ℕ) : ℂ) := by
      rw [← hsq]
      push_cast
      exact Finset.sum_congr rfl fun θ hθ => by rw [hn θ hθ]
    beta_reduce
    exact_mod_cast h2

theorem exists_isCoherent_centralDetectFam_union_indFamLinear [Fintype G] [Fintype ↥L]
    (h : IsCentralPrimeInduction p a L P E Z) {S : Finset (↥L → ℂ)}
    (hS : (S : Set (↥L → ℂ)) = centralFam L P) {R : (↥L → ℂ) → Finset (G → ℂ)}
    (hc : IsSubcoherent S (indClassFun L) R)
    (τ : charSpanZero (centralDetectFam L P Z ∪ indFamLinear (P.subgroupOf L)) →+ virtualChars G)
    (hτ : ∀ f : charSpanZero (centralDetectFam L P Z ∪ indFamLinear (P.subgroupOf L)),
      ((τ f : virtualChars G) : G → ℂ) = indClassFun L (f : ↥L → ℂ)) :
    IsCoherent (centralDetectFam L P Z ∪ indFamLinear (P.subgroupOf L)) τ := by
  classical
  have hPn := h.normal_subgroupOf
  have hZn := IsCentralPrimeInduction.normal_Z_subgroupOf h
  set X := centralDetectFam L P Z with hX
  set Y := indFamLinear (P.subgroupOf L) with hY
  set e := (P.subgroupOf L).index with he
  have hXS : X ⊆ (S : Set (↥L → ℂ)) := by rw [hS]; exact centralDetectFam_subset_centralFam
  have hYS : Y ⊆ (S : Set (↥L → ℂ)) := by rw [hS]; exact indFamLinear_subset_centralFam
  have hXfin : X.Finite := Set.Finite.subset S.finite_toSet hXS
  have hYfin : Y.Finite := NormalLinearInduced.finite_indFamLinear _
  have hXY : Disjoint X Y := Set.disjoint_iff_inter_eq_empty.2
    (IsCentralPrimeInduction.inter_centralDetectFam_indFamLinear_eq_empty h)
  have hXstar : ∀ ψ ∈ X, star ψ ∈ X := fun ψ hψ => star_mem_centralDetectFam hψ
  have hYstar : ∀ ψ ∈ Y, star ψ ∈ Y := fun ψ hψ =>
    IsCentralPrimeInduction.star_mem_indFamLinear hψ
  have hYIrr : Y ⊆ Irr ↥L := IsCentralPrimeInduction.indFamLinear_subset_Irr h
  have hYind := NormalLinearInduced.indFamLinear_subset_indFam_Irr (P.subgroupOf L)
  have hYdeg : ∀ ψ ∈ Y, ψ 1 = ((e : ℕ) : ℂ) := fun ψ hψ =>
    IsCentralPrimeInduction.apply_one_of_mem_indFamLinear h hψ
  obtain ⟨η, hη⟩ := IsCentralPrimeInduction.indFamLinear_nonempty h
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 (IsCentralPrimeInduction.isCoherent_indFamLinear h)
  obtain ⟨μ, hμinner, hμ0, -, -, hor⟩ := CentralPrimeInduction.exists_oriented_projection h ν
    hν.inner_eq (fun f => by rw [hν.eq_on_zero f, coe_tiIndCharSpanZeroHom]) hη
  set τY := tiIndCharSpanZeroHom h.isTI hYind hYIrr with hτYdef
  have hμcoh : IsCoherentWith Y τY μ :=
    ⟨hμinner, fun f => Subtype.ext (by rw [coe_tiIndCharSpanZeroHom]; exact hμ0 f)⟩
  have hτY : ∀ f : charSpanZero Y, ((τY f : virtualChars G) : G → ℂ)
      = indClassFun L (f : ↥L → ℂ) := fun f => coe_tiIndCharSpanZeroHom _ _ _ f
  set hvη := (μ ⟨η, Submodule.subset_span hη⟩ : G → ℂ) with hhvη
  have hvηeq : coherentVal μ ⟨η, hη⟩ = hvη := coherentVal_apply μ ⟨η, hη⟩
  have hηη : cfInner η η = 1 := cfInner_self_of_mem_Irr (hYIrr hη)
  have hvv : cfInner hvη hvη = 1 := by rw [hhvη, hμinner]; exact hηη
  have hene : ((e : ℕ) : ℂ) ≠ 0 := by
    rw [← hYdeg η hη]; exact apply_one_ne_zero_of_mem_Irr (hYIrr hη)
  have hdegX : ∀ χ ∈ X, ∃ m : ℤ, 1 ≤ m ∧ χ 1 = (m : ℂ) * ((e : ℕ) : ℂ) := by
    intro χ hχ
    obtain ⟨m, hm, hme⟩ := exists_pos_apply_one_of_mem_centralDetectFam hχ
    exact ⟨(m : ℤ), by omega, by rw [hme, he]; push_cast; ring⟩
  choose! b hbpos hbdeg using hdegX
  have hVex : ∀ χ ∈ X, ∃ Vχ ∈ Submodule.span ℤ (Irr G),
      indClassFun L (χ - (b χ : ℂ) • η) = Vχ - (b χ : ℂ) • hvη ∧ cfInner Vχ hvη = 0 := by
    intro χ hχ
    obtain ⟨I, θ₀, d, lam, hθ₀I, hθ₀χ, hIX, hdpos, hddeg, hlam, hlam1, hwsum, hrsum⟩ :=
      exists_centralIrrFinset_of_mem_centralDetectFam h hχ
    obtain ⟨-, -, hγorth⟩ := hor lam hlam hlam1
    set ξ : ↥I → ↥L → ℂ := fun i => indClassFun (P.subgroupOf L) (i : ↥(P.subgroupOf L) → ℂ)
      with hξdef
    set cc : ↥I → ℤ := fun i => d (i : ↥(P.subgroupOf L) → ℂ) with hccdef
    have hξX : ∀ i, ξ i ∈ X := fun i => hIX _ i.2
    have hccpos : ∀ i, 1 ≤ cc i := fun i => hdpos _ i.2
    have hξdeg : ∀ i, ξ i 1 = (cc i : ℂ) * ((e : ℕ) : ℂ) := fun i => by
      simp only [hξdef, hccdef]
      rw [he, indClassFun_apply_one, hddeg _ i.2]; ring
    have hξθ₀ : ξ ⟨θ₀, hθ₀I⟩ = χ := hθ₀χ
    have hsum : ∑ i, (cc i : ℂ) • ξ i = indClassFun (Z.subgroupOf L) lam := by
      rw [← hwsum]
      exact Finset.sum_coe_sort I fun θ => ((d θ : ℤ) : ℂ) • indClassFun (P.subgroupOf L) θ
    have hrs : ∑ i, cc i ^ 2 = (Z.relIndex P : ℤ) := by
      rw [← hrsum]
      exact Finset.sum_coe_sort I fun θ => d θ ^ 2
    have hweq : cfInner (indClassFun L ((∑ i, (cc i : ℂ) • ξ i)
        - (((Z.relIndex P : ℤ) : ℂ)) • η)) hvη = -(((Z.relIndex P : ℤ) : ℂ)) := by
      have h0 := isOrthogonal_iff.1 (hγorth η hη)
      rw [hvηeq, cfInner_add_left, cfInner_smul_left, hvv] at h0
      rw [hsum, show (((Z.relIndex P : ℤ) : ℂ)) = ((Z.relIndex P : ℕ) : ℂ) from by push_cast; ring,
        ← gammaChar_def]
      linear_combination h0
    have hbi : b χ = cc ⟨θ₀, hθ₀I⟩ := by
      have h1 : ((b χ : ℂ)) * ((e : ℕ) : ℂ) = ((cc ⟨θ₀, hθ₀I⟩ : ℂ)) * ((e : ℕ) : ℂ) := by
        rw [← hbdeg χ hχ, ← hξdeg ⟨θ₀, hθ₀I⟩, hξθ₀]
      exact_mod_cast mul_right_cancel₀ hene h1
    have hsat := WeightedPivotJoining.cfInner_tau_sub_smul_pivot hc hXfin hYfin hXS hYS hXY
      hXstar hYstar hYIrr hμcoh hτY hη hYdeg hξX hξdeg hccpos rfl hrs.symm hweq ⟨θ₀, hθ₀I⟩
    rw [hξθ₀] at hsat
    rw [hbi]
    exact hsat
  obtain ⟨χ₀, hχ₀⟩ := centralDetectFam_nonempty h
  exact WeightedPivotJoining.isCoherent_union_of_exists_bridge hc hXfin hYfin hXS hYS hXY
    hχ₀ ⟨η, hη⟩ hXstar hYstar hYIrr hμcoh hτY hη hYdeg hbdeg hVex hτ

end CentralPrimeInduction

end CFSG.FeitThompson
