module

public import CFSG.LargeExtraspecial.AS35DSixThreeC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Asc77 CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G]

namespace SixThreeCtx

variable {S : Setting G} (c : SixThreeCtx S)

theorem card_QG_eq_four_mul (hS : IsSThreeAt S.z c.N) :
    Nat.card S.QG = 2 ^ 2 * Nat.card ↥(S.QG ⊓ centralizer ({c.t} : Set G)) := by
  obtain ⟨hcard, -, -, -⟩ := hS
  have htΩ : c.t ∈ S.zConj c.N := c.t_mem_zConj
  have hzΩ : S.z ∈ S.zConj c.N := self_mem_conjIn _ _
  have htz := c.t_ne_z
  have hnle := c.not_le_centralizer_t
  have hcqt := c.cqt_le
  generalize c.t = t at htΩ htz hnle hcqt
  obtain ⟨p, hpP, hpt⟩ : ∃ p ∈ c.P, p * t * p⁻¹ ≠ t := by
    by_contra! h
    refine hnle fun q hq => mem_centralizer_singleton_iff.mpr ?_
    calc q * t = q * t * q⁻¹ * q := by group
      _ = t * q := by rw [h q hq]
  have hqz : ∀ q ∈ S.QG, q⁻¹ * S.z * q = S.z := fun q hq => by
    rw [mul_assoc, ← S.z_comm_QG hq]
    group
  set O := {x | ∃ q ∈ c.P, q * t * q⁻¹ = x} with hO
  have hOsub : O ⊆ S.zConj c.N \ {S.z} := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨conj_mem_conjIn_of_mem (c.hPN hq) htΩ, fun h' => htz ?_⟩
    have h'' : q * t * q⁻¹ = S.z := h'
    calc t = q⁻¹ * (q * t * q⁻¹) * q := by group
      _ = S.z := by rw [h'', hqz q (mem_inf.mp hq).1]
  have hOsup : ({t, p * t * p⁻¹} : Set G) ⊆ O := by
    rintro x (rfl | rfl)
    · exact ⟨1, one_mem _, by group⟩
    · exact ⟨p, hpP, rfl⟩
  have hΩz : (S.zConj c.N \ {S.z}).ncard = 2 := by
    rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr hzΩ), hcard, Set.ncard_singleton]
  have hOcard : O.ncard = 2 := le_antisymm
    (hΩz ▸ Set.ncard_le_ncard hOsub (Set.toFinite _))
    ((Set.ncard_pair (Ne.symm hpt)) ▸ Set.ncard_le_ncard hOsup (Set.toFinite _))
  have hQP : Nat.card S.QG = 2 * Nat.card c.P := by
    have h1 := card_eq_relIndex_mul S.QG (S.QG ⊓ centralizer ({c.u} : Set G))
    rw [S.relIndex_centralizer_eq_two c.huQ c.hu1 c.huz, ← inf_assoc, inf_idem] at h1
    exact h1
  have hPt : Nat.card c.P = 2 * Nat.card ↥(S.QG ⊓ centralizer ({t} : Set G)) := by
    have h1 := card_eq_relIndex_mul c.P (centralizer ({t} : Set G))
    rw [relIndex_centralizer_eq_ncard, ← hO, hOcard] at h1
    have heq : c.P ⊓ centralizer ({t} : Set G) = S.QG ⊓ centralizer ({t} : Set G) := by
      refine le_antisymm (inf_le_inf_right _ inf_le_left) fun x hx => ?_
      exact mem_inf.mpr ⟨hcqt hx, (mem_inf.mp hx).2⟩
    rw [heq] at h1
    exact h1
  rw [hQP, hPt]
  ring

omit [Finite G] in
theorem t_mem_M_of_sThree (hS : IsSThreeAt S.z c.N) : c.t ∈ S.M :=
  S.mem_M_iff.mpr (hS.2.1 c.t c.t_mem_zConj S.z (self_mem_conjIn _ _))

theorem sThree_typeA (hS : IsSThreeAt S.z c.N) :
    finrank (ZMod 2) (commSpace (S.rhoL (c.t_mem_M_of_sThree hS))) = 2 ∧
      (∀ v ∈ commSpace (S.rhoL (c.t_mem_M_of_sThree hS)), S.q v = 0) ∧
      S.QG ⊓ centralizer ({c.t} : Set G) =
        S.clPre (fixSpace (S.rhoL (c.t_mem_M_of_sThree hS))) ∧
      S.QG ⊓ centralizer ({c.t} : Set G) ⊓
          centralizer ((S.QG ⊓ centralizer ({c.t} : Set G) : Subgroup G) : Set G) =
        S.clPre (commSpace (S.rhoL (c.t_mem_M_of_sThree hS))) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set htM := c.t_mem_M_of_sThree hS
  have hk := c.card_QG_eq_four_mul hS
  have hpos : 0 < Nat.card ↥(S.QG ⊓ centralizer ({c.t} : Set G)) := Nat.card_pos
  rcases S.fourFive htM c.t_mul_self c.t_not_mem_QG with ⟨hA', hk', -⟩ | ⟨-, hk', hΩ', -⟩ |
    ⟨hA', hk', -, -⟩
  · have hm := Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hpos (hk'.symm.trans hk))
    exact ⟨hm, hA'.2.2.2.2, S.cqx_eq_clPre_fixSpace htM hk' c.t_mul_self,
      S.center_cqx_eq_clPre_commSpace htM hk' c.t_mul_self⟩
  · exfalso
    have hm := Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hpos (hk'.symm.trans hk))
    have hcen : ∀ y ∈ S.QG ⊓ centralizer ({c.t} : Set G), c.u * y = y * c.u := fun y hy =>
      (mem_centralizer_singleton_iff.mp (mem_inf.mp (c.cqt_le hy)).2).symm
    have hsub : ({1, S.z, c.u, c.u * S.z} : Set G) ⊆
        {y | y ∈ S.QG ⊓ centralizer ({c.t} : Set G) ⊓
          centralizer ((S.QG ⊓ centralizer ({c.t} : Set G) : Subgroup G) : Set G) ∧
          y * y = 1} := by
      have hu : c.u ∈ S.QG ⊓ centralizer ({c.t} : Set G) ⊓
          centralizer ((S.QG ⊓ centralizer ({c.t} : Set G) : Subgroup G) : Set G) :=
        mem_inf.mpr ⟨mem_inf.mpr ⟨c.huQ, mem_centralizer_singleton_iff.mpr c.commute_u_t⟩,
          mem_centralizer_iff.mpr fun y hy => (hcen y hy).symm⟩
      have hz : S.z ∈ S.QG ⊓ centralizer ({c.t} : Set G) ⊓
          centralizer ((S.QG ⊓ centralizer ({c.t} : Set G) : Subgroup G) : Set G) :=
        mem_inf.mpr ⟨S.z_mem_cqx htM, mem_centralizer_iff.mpr fun y hy =>
          S.z_comm_QG (mem_inf.mp hy).1⟩
      rintro x (rfl | rfl | rfl | rfl)
      · exact ⟨one_mem _, mul_one 1⟩
      · exact ⟨hz, S.z_mul_z⟩
      · exact ⟨hu, c.huu⟩
      · refine ⟨mul_mem hu hz, ?_⟩
        rw [show c.u * S.z * (c.u * S.z) = (c.u * c.u) * (S.z * S.z) by
          rw [mul_assoc, ← mul_assoc S.z c.u S.z, ← S.z_comm_QG c.huQ]; group,
          c.huu, S.z_mul_z, mul_one]
    have h4 : ({1, S.z, c.u, c.u * S.z} : Set G).ncard = 4 := by
      have huz1 : c.u * S.z ≠ 1 := fun h => c.huz (eq_inv_of_mul_eq_one_left h ▸ S.z_inv)
      have huzz : c.u * S.z ≠ S.z := fun h => c.hu1 (mul_eq_right.mp h)
      have huzu : c.u * S.z ≠ c.u := fun h => S.z_ne_one (mul_eq_left.mp h)
      rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨Ne.symm S.z_ne_one, Ne.symm c.hu1, Ne.symm huz1⟩),
        Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨Ne.symm c.huz, Ne.symm huzz⟩),
        Set.ncard_pair (Ne.symm huzu)]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h4, hΩ', show finrank (ZMod 2) (commSpace (S.rhoL htM)) = 1 by omega] at this
    omega
  · exfalso
    have hm := Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hpos (hk'.symm.trans hk))
    have hev := even_finrank_commSpace_of_forall_eq_zero S.q_nondegenerate (S.rhoL_mem htM)
      (S.rhoL_mul_self htM c.t_mul_self) hA'.2.2.2.2
    rw [show finrank (ZMod 2) (commSpace (S.rhoL htM)) = 1 by omega] at hev
    exact absurd hev (by decide)

omit [Finite G] in
theorem inf_Qa_le_center : S.QG ⊓ S.Qa c.g ≤ S.QG ⊓ centralizer ({c.t} : Set G) ⊓
    centralizer ((S.QG ⊓ centralizer ({c.t} : Set G) : Subgroup G) : Set G) := by
  intro w hw
  obtain ⟨hwQ, hwQa⟩ := mem_inf.mp hw
  set T := S.conjBy c.g with hT
  have hwt : w ∈ centralizer ({c.t} : Set G) := T.QG_le_M hwQa
  refine mem_inf.mpr ⟨mem_inf.mpr ⟨hwQ, hwt⟩, mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨hyQ, hyt⟩ := mem_inf.mp hy
  have hyT : y ∈ T.M := hyt
  have h1 : y * w * y⁻¹ * w⁻¹ ∈ S.Qa c.g := mul_mem (T.conj_mem_QG hyT hwQa) (inv_mem hwQa)
  rcases S.commutator_eq_one_or_z hyQ hwQ with h | h
  · calc y * w = y * w * y⁻¹ * w⁻¹ * (w * y) := by group
      _ = w * y := by rw [h, one_mul]
  · exact absurd (h ▸ h1) (S.z_not_mem_Qa c.hW c.t_ne_z)

omit [Finite G] in
theorem exists_swap (hS : IsSThreeAt S.z c.N) :
    ∃ h ∈ c.N, h * S.z * h⁻¹ = c.t ∧ h * c.t * h⁻¹ = S.z := by
  classical
  obtain ⟨-, -, -, hsurj⟩ := hS
  have htΩ : c.t ∈ S.zConj c.N := c.t_mem_zConj
  have hzΩ : S.z ∈ S.zConj c.N := self_mem_conjIn _ _
  obtain ⟨h, hh⟩ := hsurj (Equiv.swap ⟨S.z, hzΩ⟩ ⟨c.t, htΩ⟩)
  refine ⟨h, h.2, ?_, ?_⟩
  · have := congrArg (fun σ : Equiv.Perm (S.zConj c.N) => ((σ ⟨S.z, hzΩ⟩ : S.zConj c.N) : G))
      hh
    simp only [Equiv.swap_apply_left] at this
    exact this
  · have := congrArg (fun σ : Equiv.Perm (S.zConj c.N) => ((σ ⟨c.t, htΩ⟩ : S.zConj c.N) : G))
      hh
    simp only [Equiv.swap_apply_right] at this
    exact this

end SixThreeCtx

end Setting

end CFSG.LargeExtraspecial
