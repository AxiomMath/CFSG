module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Diag.Delta
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.PerfectCover
public import CFSG.GroupTheory.ConjugatePairSubnormality

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {T W W' M K : Subgroup H} {s : H}

@[expose] def diagX (h : DiagData T W W' M K s) : Subgroup H :=
  (ccLift (diagΔ h) K).map (diagA M W').subtype

omit [Finite H] in
theorem DiagData.K_perfect (h : DiagData T W W' M K s) : ⁅K, K⁆ = K :=
  Subgroup.isPerfect_iff.1 h.isComp_K.isQuasisimple.1

theorem DiagData.diagX_le_A (h : DiagData T W W' M K s) : diagX h ≤ diagA M W' :=
  Subgroup.map_subtype_le _

theorem DiagData.diagX_le_conjClosure (h : DiagData T W W' M K s) :
    diagX h ≤ conjClosure M W' :=
  h.diagX_le_A.trans inf_le_left

theorem DiagData.perfect_diagX (h : DiagData T W W' M K s) : ⁅diagX h, diagX h⁆ = diagX h := by
  unfold diagX
  rw [← Subgroup.map_commutator, commutator_ccLift_eq h.ker_le_center h.K_perfect h.K_le_range]

theorem DiagData.mem_K_of_mem_X (h : DiagData T W W' M K s) {x : H} (hx : x ∈ diagX h) :
    x * (s * x * s⁻¹) ∈ K := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ccLift_le_comap (diagΔ h) K hy

theorem DiagData.exists_mem_X (h : DiagData T W W' M K s) {k : H} (hk : k ∈ K) :
    ∃ x ∈ diagX h, x * (s * x * s⁻¹) = k := by
  have : k ∈ (ccLift (diagΔ h) K).map (diagΔ h) := by
    rw [map_ccLift (diagΔ h) h.K_perfect h.K_le_range]
    exact hk
  obtain ⟨y, hy, hyk⟩ := this
  exact ⟨y, ⟨y, hy, rfl⟩, hyk⟩

@[expose] def diagψ (h : DiagData T W W' M K s) : ↥(diagX h) →* ↥K :=
  MonoidHom.codRestrict ((diagΔ h).comp (Subgroup.inclusion h.diagX_le_A)) K
    (fun x => h.mem_K_of_mem_X x.2)

theorem DiagData.diagψ_surjective (h : DiagData T W W' M K s) :
    Function.Surjective (diagψ h) := by
  rintro ⟨k, hk⟩
  obtain ⟨x, hx, hxk⟩ := h.exists_mem_X hk
  exact ⟨⟨x, hx⟩, Subtype.ext hxk⟩

theorem DiagData.ker_diagψ_le_center (h : DiagData T W W' M K s) :
    (diagψ h).ker ≤ center ↥(diagX h) := by
  intro x hx
  have h1 : Subgroup.inclusion h.diagX_le_A x ∈ (diagΔ h).ker := by
    rw [MonoidHom.mem_ker]
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact this
  have h2 := h.ker_le_center h1
  rw [Subgroup.mem_center_iff] at h2 ⊢
  intro y
  have := h2 (Subgroup.inclusion h.diagX_le_A y)
  exact Subtype.ext (by simpa using congrArg Subtype.val this)

theorem DiagData.isPerfect_diagX (h : DiagData T W W' M K s) : Group.IsPerfect ↥(diagX h) :=
  Subgroup.isPerfect_iff.2 h.perfect_diagX

theorem DiagData.quasisimple_diagX (h : DiagData T W W' M K s) : CFSG.IsQuasisimple ↥(diagX h) :=
  isQuasisimple_of_perfect_cover h.isPerfect_diagX h.isComp_K.isQuasisimple (diagψ h)
    h.diagψ_surjective h.ker_diagψ_le_center

theorem DiagData.cqEquiv_diagX (h : DiagData T W W' M K s) :
    Nonempty ((↥(diagX h) ⧸ center ↥(diagX h)) ≃* (↥K ⧸ center ↥K)) := by
  have := h.isPerfect_diagX
  exact cqEquiv_of_cover (diagψ h) h.diagψ_surjective h.ker_diagψ_le_center

theorem DiagData.diagX_ne (h : DiagData T W W' M K s) :
    (diagX h).map (MulAut.conj s).toMonoidHom ≠ diagX h := by
  intro heq
  refine not_forall_commute_of_isQuasisimple h.quasisimple_diagX fun a ha b hb => ?_
  have hbP₂ : b ∈ diagP₂ M W' s := by
    rw [← heq] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    exact ⟨c, (h.diagX_le_A hc).1, rfl⟩
  exact h.commute a (h.diagX_le_A ha).1 b hbP₂

theorem DiagData.K_le_sup_X (h : DiagData T W W' M K s) :
    K ≤ diagX h ⊔ (diagX h).map (MulAut.conj s).toMonoidHom := by
  intro k hk
  obtain ⟨x, hx, rfl⟩ := h.exists_mem_X hk
  exact Subgroup.mul_mem_sup hx ⟨x, hx, by simp [MulAut.conj_apply]⟩

omit [Finite H] in
theorem DiagData.diagA_le_centralizer (h : DiagData T W W' M K s) :
    diagA M W' ≤ centralizer ((W' ⊔ T : Subgroup H) : Set H) := fun _ hx =>
  mem_centralizer_sup.2 ⟨hx.2, h.P₁_le_centralizer hx.1⟩

theorem DiagData.subnormal_diagX (h : DiagData T W W' M K s) :
    ((diagX h).subgroupOf (centralizer ((W' ⊔ T : Subgroup H) : Set H))).IsSubnormal := by
  set Y' : Subgroup H := centralizer ((W' ⊔ T : Subgroup H) : Set H) with hY'
  set I : Subgroup H := (diagΔ h).range with hI
  have hIC : I ≤ centralizer ((W ⊔ T : Subgroup H) : Set H) := by
    rintro _ ⟨a, rfl⟩
    exact h.diagΔ_mem a
  have hKsub : (K.subgroupOf I).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hIC h.isComp_K.2.2
  have hB : (K.comap (diagΔ h)).IsSubnormal := by
    have := hKsub.comap (diagΔ h).rangeRestrict
    exact this
  have hXsub : (ccLift (diagΔ h) K).IsSubnormal :=
    Subgroup.IsSubnormal.trans (ccLift_le_comap (diagΔ h) K)
      (normal_commutator_subgroupOf (K.comap (diagΔ h))).isSubnormal hB
  have hXA : (diagX h).subgroupOf (diagA M W') = ccLift (diagΔ h) K :=
    Subgroup.comap_map_eq_self_of_injective (diagA M W').subtype_injective _
  have hP₁Y : (conjClosure M W').subgroupOf Y' |>.IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le
      (Subgroup.centralizer_le (by exact_mod_cast (le_sup_right : T ≤ W' ⊔ T)))
      h.subnormal_P₁
  have hAeq : (diagA M W').subgroupOf Y' = (conjClosure M W').subgroupOf Y' := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · exact fun hx => hx.1
    · exact fun hx => ⟨hx, (mem_centralizer_sup.1 x.2).1⟩
  have hAY : ((diagA M W').subgroupOf Y').IsSubnormal := by
    rw [hAeq]
    exact hP₁Y
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans h.diagX_le_A h.diagA_le_centralizer
    (by rw [hXA]; exact hXsub) hAY

theorem DiagData.isComp_diagX (h : DiagData T W W' M K s) :
    IsCompIn (diagX h) (centralizer ((W' ⊔ T : Subgroup H) : Set H)) :=
  isCompIn_of_subnormal (h.diagX_le_A.trans h.diagA_le_centralizer) h.quasisimple_diagX
    h.subnormal_diagX

end CFSG.EvenSporadicStandard.Induction.Junction
