module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.Assembly.OddCoreSpan
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification

section OddCore

variable {G : Type*} [Group G]

@[expose] def oddCoreIn (X : Subgroup G) : Subgroup G :=
  (componentClassificationOddCore X).map X.subtype

theorem involutionOddCore_eq_oddCoreIn (a : G) :
    CFSG.Assembly.Dichotomy.involutionOddCore a = oddCoreIn (Subgroup.centralizer {a}) :=
  rfl

theorem oddCoreIn_le (X : Subgroup G) : oddCoreIn X ≤ X :=
  Subgroup.map_subtype_le _

theorem odd_card_oddCoreIn [Finite G] (X : Subgroup G) : Odd (Nat.card (oddCoreIn X)) := by
  rw [oddCoreIn, Subgroup.card_map_of_injective X.subtype_injective]
  exact OddCore.odd_card X

theorem conj_mem_oddCoreIn {X : Subgroup G} {x : G} (hx : x ∈ X) {y : G}
    (hy : y ∈ oddCoreIn X) : x * y * x⁻¹ ∈ oddCoreIn X := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹,
    (componentClassificationOddCore_normal X).conj_mem y' hy' ⟨x, hx⟩, rfl⟩

theorem normalizer_oddCoreIn (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oddCoreIn X : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_oddCoreIn hx hy, fun hy => ?_⟩
  have := conj_mem_oddCoreIn (inv_mem hx) hy
  simpa [mul_assoc] using this

theorem isSubnormal_oddCoreIn (X : Subgroup G) : IsSubnormal (oddCoreIn X) X := by
  refine isSubnormal_of_normal_subgroupOf (oddCoreIn_le X) ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreIn_le X)]
  exact normalizer_oddCoreIn X

theorem le_oddCoreIn_of_normalizes [Finite G] {X S : Subgroup G} (hSX : S ≤ X)
    (hnorm : X ≤ Subgroup.normalizer (S : Set G)) (hodd : Odd (Nat.card S)) :
    S ≤ oddCoreIn X := by
  have hN : (S.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSX).mpr hnorm
  have hcard : Odd (Nat.card (S.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv]
    exact hodd
  have h1 := Subgroup.map_mono (f := X.subtype) (OddCore.maximal X (S.subgroupOf X) hN hcard)
  rwa [Subgroup.map_subgroupOf_eq_of_le hSX] at h1

theorem le_oddCoreIn_of_isSubnormal [Finite G] {X S : Subgroup G} (hS : IsSubnormal S X)
    (hodd : Odd (Nat.card S)) : S ≤ oddCoreIn X := by
  intro s hs
  have hSO : (⟨s, hs⟩ : S) ∈ componentClassificationOddCore S :=
    OddCore.maximal S ⊤ inferInstance (by simpa using hodd) (Subgroup.mem_top _)
  obtain ⟨hX, hXO⟩ := (OddCore.subnormal_mem_iff hS s hs).mp hSO
  exact ⟨⟨s, hX⟩, hXO, rfl⟩

theorem oddCoreIn_le_of_isSubnormal [Finite G] {N P : Subgroup G} (h : IsSubnormal N P) :
    oddCoreIn N ≤ oddCoreIn P :=
  le_oddCoreIn_of_isSubnormal (isSubnormal_trans (isSubnormal_oddCoreIn N) h)
    (odd_card_oddCoreIn N)

end OddCore

section NormalClosure

variable {G : Type*} [Group G]

@[expose] def normalClosureIn (H L : Subgroup G) : Subgroup G :=
  ⨆ h ∈ H, L.map (MulAut.conj h).toMonoidHom

theorem map_map_conj (L : Subgroup G) (a b : G) :
    (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  show b * (a * x * a⁻¹) * b⁻¹ = b * a * x * (b * a)⁻¹
  group

theorem le_normalClosureIn (H L : Subgroup G) : L ≤ normalClosureIn H L := by
  intro x hx
  refine Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem (one_mem H) ⟨x, hx, ?_⟩)
  simp

theorem normalClosureIn_le {H L M : Subgroup G}
    (h : ∀ g ∈ H, L.map (MulAut.conj g).toMonoidHom ≤ M) : normalClosureIn H L ≤ M :=
  iSup₂_le h

theorem conj_mem_normalClosureIn {H L : Subgroup G} {h x : G} (hh : h ∈ H)
    (hx : x ∈ normalClosureIn H L) : h * x * h⁻¹ ∈ normalClosureIn H L := by
  have key : (normalClosureIn H L).map (MulAut.conj h).toMonoidHom ≤ normalClosureIn H L := by
    unfold normalClosureIn
    rw [Subgroup.map_iSup]
    refine iSup_le fun h' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hh' => ?_
    rw [map_map_conj]
    exact le_iSup₂_of_le (h * h') (mul_mem hh hh') le_rfl
  exact key ⟨x, hx, rfl⟩

theorem normalClosureIn_le_of_le {H L : Subgroup G} (hLH : L ≤ H) : normalClosureIn H L ≤ H := by
  refine normalClosureIn_le fun g hg => ?_
  rintro _ ⟨x, hx, rfl⟩
  exact H.mul_mem (H.mul_mem hg (hLH hx)) (H.inv_mem hg)

theorem normal_subgroupOf_normalClosureIn {H L : Subgroup G} (hLH : L ≤ H) :
    ((normalClosureIn H L).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (normalClosureIn_le_of_le hLH)]
  intro x k hx hk
  exact conj_mem_normalClosureIn hk hx

theorem isSubnormal_normalClosureIn {H L : Subgroup G} (hLH : L ≤ H) :
    IsSubnormal (normalClosureIn H L) H :=
  isSubnormal_of_normal_subgroupOf (normalClosureIn_le_of_le hLH)
    (normal_subgroupOf_normalClosureIn hLH)

end NormalClosure

section Perfect

theorem eq_top_of_perfect_of_odd_index {X : Type*} [Group X] [Finite X] (hX : commutator X = ⊤)
    (M : Subgroup X) [M.Normal] (hM : Odd M.index) : M = ⊤ := by
  have hodd : Odd (Nat.card (X ⧸ M)) := by rwa [← Subgroup.index_eq_card]
  have hsolv : Group.IsSolvable (X ⧸ M) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsPerfect X := ⟨hX⟩
  have : Group.IsPerfect (X ⧸ M) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
  by_contra hne
  have : Nontrivial (X ⧸ M) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    exact hne (QuotientGroup.subsingleton_iff.mp hs)
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (X ⧸ M)
  rw [Group.IsPerfect.commutator_eq_top] at hlt
  exact lt_irrefl _ hlt

theorem twoResidual_eq_top_of_perfect {X : Type*} [Group X] [Finite X] (hX : commutator X = ⊤) :
    TwoResidual.subgroup X = ⊤ := by
  have : (TwoResidual.subgroup X).Characteristic := TwoResidual.characteristic X
  exact eq_top_of_perfect_of_odd_index hX _ (TwoResidual.odd_index X)

variable {G : Type*} [Group G] [Finite G]

theorem eq_bot_of_perfect_of_odd {L : Subgroup G} (hL : commutator L = ⊤)
    (hodd : Odd (Nat.card L)) : L = ⊥ := by
  have h := eq_top_of_perfect_of_odd_index hL (⊥ : Subgroup L) (by rwa [Subgroup.index_bot])
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : L) ∈ (⊥ : Subgroup L) := by
    rw [h]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hx')

theorem le_of_perfect_of_forall_isPGroup_le {L C : Subgroup G} (hL : commutator L = ⊤)
    (h : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P → P ≤ C) : L ≤ C := by
  have hres := twoResidual_eq_top_of_perfect hL
  have hle : TwoResidual.subgroup L ≤ C.subgroupOf L := by
    refine sSup_le fun P hP => ?_
    have h2 := h (P.map L.subtype) (Subgroup.map_subtype_le P) (hP.map L.subtype)
    intro x hx
    exact h2 ⟨x, hx, rfl⟩
  rw [hres] at hle
  intro x hx
  exact hle (Subgroup.mem_top (⟨x, hx⟩ : L))

end Perfect

section Quasisimple

variable {J : Type*} [Group J] [Finite J]

theorem oddCore_le_center_of_isQuasisimple (hJ : CFSG.Open.IsQuasisimple J) :
    componentClassificationOddCore J ≤ Subgroup.center J := by
  have : Group.IsPerfect J := ⟨hJ.1⟩
  have : Nontrivial J := Quasisimple.nontrivial hJ
  rcases Quasisimple.normal_le_center_or_eq_top hJ (componentClassificationOddCore J) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card J) := by
      have := OddCore.odd_card J
      rwa [h, Subgroup.card_top] at this
    have hsolv : Group.IsSolvable J := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial J
    rw [Group.IsPerfect.commutator_eq_top] at hlt
    exact lt_irrefl _ hlt

end Quasisimple

section Coprime

variable {G : Type*} [Group G] [Finite G]

theorem commutator_commutator_eq_of_isPGroup {P V : Subgroup G} (hP : IsPGroup 2 P)
    (hV : Odd (Nat.card V)) (hnorm : P ≤ Subgroup.normalizer (V : Set G)) :
    ⁅⁅V, P⁆, P⁆ = ⁅V, P⁆ :=
  CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2 Nat.prime_two P V hP
    (fun h => (Nat.not_even_iff_odd.mpr hV) (even_iff_two_dvd.mpr h)) hnorm

end Coprime

end CFSG.ClassicalInvolution.Balance
