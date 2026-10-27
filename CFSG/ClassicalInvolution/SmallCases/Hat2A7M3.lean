module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Hat2A7M
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7ER
open CFSG.ClassicalInvolution.Asc77.T7ER
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem ne_of_hyp25 (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) : R ≠ R' :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7ER.ne_of_hyp25 hyp.toF

end T7ER

@[expose] def C25_17_norm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥((S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) ≤ 2 * Nat.card ↥(R ⊔ R')

theorem c25_17_idx_of_norm (h : C25_17_norm) : C25_17_idx := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  exact CFSG.ClassicalInvolution.T7F25.Asc77.c25_17_idx_of_norm_at hyp.toF
    (h G Ω K K' W S R R' z t u₁ u₂ hyp)
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7F2
open CFSG.ClassicalInvolution.Asc77.T7F2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ t' : G}
structure Hyp25T (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ t' : G) : Prop where
  hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂
  ht'S : t' ∈ (S : Subgroup G)
  ht'2 : t' * t' = 1
  ht'R : conjSub t' R = R'

theorem _root_.CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2.Hyp25T.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ t' : G}
    (h : CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t') :
    CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t' :=
  { h with hyp := h.hyp.toF }
namespace Hyp25T
open CFSG.ClassicalInvolution.Asc77.T7F2.Hyp25T
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
theorem hs : Hyp23Setting Ω K K' z := h.hyp.std.setting
theorem hΩ : HypOmegaMod Ω := h.hs.stand.hyp
theorem hK : K ∈ Ω := h.hs.stand.mem
theorem hK' : K' ∈ Ω := h.hs.hK'.1
theorem hz : IsUniqueInvolution K z := h.hs.hz
theorem hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet h.hz h.hs.hK'
theorem hRsyl : IsSylow2In R K :=
  T7C.isSylow2In_of_mem_RSet_of_le h.hΩ h.hK h.hyp.hR.1 h.hyp.hR.2.1
theorem hR'syl : IsSylow2In R' K' :=
  T7C.isSylow2In_of_mem_RSet_of_le h.hΩ h.hK' h.hyp.hR'.1 h.hyp.hR'.2.1
theorem hRS : R ≤ (S : Subgroup G) := h.hyp.hR.2.2
theorem hR'S : R' ≤ (S : Subgroup G) := h.hyp.hR'.2.2
theorem hcomm : Commutes R R' :=
  h.hΩ.commutes_of_twin_of_isPGroup h.hK h.hK' h.hs.hne.symm h.hz h.hz' h.hRsyl.1 h.hR'syl.1
    (S.isPGroup'.to_le (sup_le h.hRS h.hR'S))
theorem hne : R ≠ R' := T7ER.ne_of_hyp25 h.hyp
theorem hqR : IsQuatSub R := h.hΩ.isQuatSub_of_mem_RSet h.hyp.hR.1
theorem hqR' : IsQuatSub R' := h.hΩ.isQuatSub_of_mem_RSet h.hyp.hR'.1
theorem hzR' : IsUniqueInvolution R' z :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T.hzR' h.toF
theorem perm_R {s : G} (hs : s ∈ (S : Subgroup G)) : conjSub s R = R ∨ conjSub s R = R' :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T.perm_R h.toF hs
theorem ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right h.ht'2
theorem mem_N_of_conj_R' {n : G} (hnS : n ∈ (S : Subgroup G)) (hn : conjSub n R' = R') :
    n ∈ Nsub S R :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T.mem_N_of_conj_R' h.toF hnS hn
@[expose] def Psub (S : Sylow 2 G) (R : Subgroup G) : Subgroup G := R ⊔ Csub S R
end Hyp25T
end T7F2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7F2
open CFSG.ClassicalInvolution.Asc77.T7F2
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
namespace Hyp25T
open CFSG.ClassicalInvolution.Asc77.T7F2.Hyp25T
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
theorem inf_R_R' : Nat.card ↥(R ⊓ R') = 2 :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T.inf_R_R' h.toF
variable (h11 : Asc77.C25_11)
include h11
end Hyp25T
end T7F2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7F2
open CFSG.ClassicalInvolution.Asc77.T7F2
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
namespace Hyp25T
open CFSG.ClassicalInvolution.Asc77.T7F2.Hyp25T
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
theorem conj_twin {x : G} (hx : x⁻¹ * z * x = z) {J : Subgroup G} (hJ : J = K ∨ J = K') :
    conjSub x⁻¹ J = K ∨ conjSub x⁻¹ J = K' :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T.conj_twin h.toF hx hJ
theorem bdata (h11 : C25_11) (h16 : C25_16)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) {a : G} (haC : a ∈ Csub S R)
    (haR' : a ∉ R') :
    BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T.bdata h.toF
    (h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp) (h16 G Ω K K' W S R R' z t u₁ u₂ h.hyp) hlt haC haR'
theorem exists_a (h11 : C25_11) (h16 : C25_16)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) :
    ∃ a ∈ Csub S R, a ∉ R' ∧ a * a ≠ 1 :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T.exists_a h.toF
    (h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp) (h16 G Ω K K' W S R R' z t u₁ u₂ h.hyp) hlt
end Hyp25T
end T7F2
end Asc77
end
end CFSG.ClassicalInvolution.Hat2A7M
