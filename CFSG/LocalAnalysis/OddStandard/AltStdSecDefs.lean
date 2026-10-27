module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalLocal
public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

structure ExactShape {X : Type} [Group X] (t : X) (A : Subgroup X) (m : ℕ) : Prop where
  order : orderOf t = 2
  iso : Nonempty (A ≃* alternatingGroup (Fin m))
  le_cent : A ≤ centralizer ({t} : Set X)
  cent_le_norm : centralizer ({t} : Set X) ≤ normalizer (A : Set X)
  cent_cent : centralizer (A : Set X) ⊓ centralizer ({t} : Set X) = zpowers t

theorem exactShape_of_setting {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}
    {Q : Subgroup G} {z : G} (h : AltStdBal.Setting G L n) (d : AltStdBal.Cyc L Q z)
    (hQ2 : Nat.card Q = 2) : ExactShape z L n := by
  refine ⟨d.order, h.iso, AltStdBal.le_centralizer_single h d,
    AltStdBal.centralizer_le_normalizer h d, ?_⟩
  rw [AltStdBal.cent_inf_eq h d]
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le.2 d.mem
  · rw [hQ2, Nat.card_zpowers, d.order]

theorem cyc_of_exactShape {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}
    (h : ExactShape t A m) : AltStdBal.Cyc A (zpowers t) t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set X) with hK
  have htK : t ∈ K := by
    rw [hK, mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.1 (h.le_cent ha)
  let t' : K := ⟨t, htK⟩
  have ht'2 : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact h.order
  have hzp : IsPGroup 2 (zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'2, pow_one])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hPeq : (P : Subgroup K) = zpowers t' := by
    by_contra hne
    have hnil : Group.IsNilpotent (P : Subgroup K) := P.isPGroup'.isNilpotent
    have hlt : (zpowers t').subgroupOf (P : Subgroup K) < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hne ?_
      refine le_antisymm ?_ hP
      intro s hs
      have : (⟨s, hs⟩ : (P : Subgroup K)) ∈ (zpowers t').subgroupOf (P : Subgroup K) := by
        rw [htop]; trivial
      exact this
    have hgrow := Group.normalizerCondition_of_isNilpotent (G := (P : Subgroup K))
      ((zpowers t').subgroupOf (P : Subgroup K)) hlt
    obtain ⟨⟨y, hyP⟩, hyN, hyH⟩ := IsConcreteLE.exists_of_lt hgrow
    apply hyH
    have hyt : y * t' * y⁻¹ ∈ zpowers t' :=
      (mem_normalizer_iff.1 hyN ⟨t', hP (mem_zpowers t')⟩).1 (mem_zpowers t')
    have hord : orderOf (y * t' * y⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact ht'2
    have hyt2 : y * t' * y⁻¹ = t' :=
      CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.eq_of_orderOf_eq_two_of_isCyclic
        (inferInstance : IsCyclic (zpowers t')) hyt (mem_zpowers t') hord ht'2
    have hcomm : y * t' = t' * y := by
      have := congrArg (· * y) hyt2
      simpa [mul_assoc] using this
    have hyC : (y : X) ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hcomm
    have hyz : (y : X) ∈ zpowers t := by
      rw [← h.cent_cent]
      exact ⟨y.2, hyC⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hyz
    refine mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
    simpa using hk
  have hsub : (zpowers t).subgroupOf K = zpowers t' := by
    ext x
    simp only [mem_subgroupOf, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine ⟨zpowers_le.2 htK, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.order, pow_one]),
    ?_, inferInstance, h.order, mem_zpowers t⟩
  show ¬ 2 ∣ ((zpowers t).subgroupOf K).index
  rw [hsub, ← hPeq]
  exact P.not_dvd_index

abbrev Sec (X : Type) [Group X] (R : Subgroup X) : Type :=
  ↥(centralizer (R : Set X)) ⧸ CFSG.oddCore ↥(centralizer (R : Set X))

@[expose] def oddCoreOf {X : Type} [Group X] (H : Subgroup X) : Subgroup X :=
  (CFSG.oddCore ↥H).map H.subtype

@[expose] def AlmostSimple (X : Type) [Group X] : Prop :=
  ∃ F : Subgroup X, F = CFSG.generalizedFitting X ∧ IsSimpleGroup F ∧ ∃ a b : F, a * b ≠ b * a

section Stage1

variable {G : Type} [Group G]

@[expose] def FusionAll (L : Subgroup G) (z : G) : Prop :=
  ∀ y ∈ L, orderOf y = 2 → ∃ g : G, g * z * g⁻¹ = z * y

structure WreathPair (L : Subgroup G) (z : G) (n : ℕ) (H : Subgroup G) : Prop where
  iso : Nonempty (H ≃* alternatingGroup (Fin n))
  comm : ∀ a ∈ H, ∀ b ∈ H.map (MulAut.conj z).toMonoidHom, a * b = b * a
  diag : (L : Set G) = {g | ∃ a ∈ H, g = a * (z * a * z⁻¹)}

end Stage1

end CFSG.OddStandard.AltStdSec
