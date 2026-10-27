module

public import CFSG.LocalAnalysis.EvenBN.GMS.LocalFusion
public import CFSG.LocalAnalysis.EvenBN.GMS.FittingTrivial
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian
public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.Goldschmidt.Steps.Red2Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup CFSG.Open CFSG.ComponentClassification

namespace LocalSetting

variable {H : Type} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}

section Cores

variable (h : LocalSetting A t U V D n)
include h

theorem goldschmidtOddCore_eq_bot (N : Subgroup H) [N.Normal] : goldschmidtOddCore N = ⊥ := by
  have h1 := OddCore.normal_intersection H N
  have h2 : componentClassificationOddCore H = ⊥ := h.oddCore_eq_bot
  rw [h2, inf_bot_eq] at h1
  exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp h1

theorem fittingSubgroup_eq_bot_of_normal (N : Subgroup H) [N.Normal] :
    CFSG.fittingSubgroup N = ⊥ := by
  have h1 := CFSG.LocalCores.fitting_normal_intersection N
  rw [h.fittingSubgroup_eq_bot, inf_bot_eq] at h1
  exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp h1

theorem pCore_eq_bot_of_normal (N : Subgroup H) [N.Normal] : CFSG.pCore 2 N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_bot_iff.mp ((CFSG.pCore_le_fitting N 2).trans (h.fittingSubgroup_eq_bot_of_normal N).le)

end Cores

section Goldschmidt


theorem goldschmidt_normalClosure (h : LocalSetting A t U V D n) (S : Sylow 2 H)
    (hVS : V ≤ S)
    (hclosed : ∀ v ∈ V, ∀ g : H, g⁻¹ * v * g ∈ (S : Subgroup H) → g⁻¹ * v * g ∈ V) :
    sSup {K : Subgroup H | IsComponentOf K ⊤ ∧ K ≤ normalClosure (V : Set H)} =
        normalClosure (V : Set H) ∧
      (∀ x ∈ (S : Subgroup H), x ∈ normalClosure (V : Set H) → x * x = 1 → x ∈ V) ∧
      ∀ K : Subgroup H, IsComponentOf K ⊤ → K ≤ normalClosure (V : Set H) →
        goldschmidtSimpleType (K ⧸ center K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup H := normalClosure (V : Set H) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hVab : IsMulCommutative V := isMulCommutative_iff.mpr fun a b =>
    Subtype.ext (h.V_comm a a.2 b b.2)
  obtain ⟨ha, hb, hc⟩ :=
    CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian H S V hVS hVab hclosed
  have hO : goldschmidtOddCore M = ⊥ := h.goldschmidtOddCore_eq_bot M
  let e : (M ⧸ goldschmidtOddCore M) ≃* M :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have he : ∀ m : M, e (QuotientGroup.mk' (goldschmidtOddCore M) m) = m := fun m => rfl
  have hP : CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) = ⊥ := by
    have h1 := CFSG.pCore_map_iso (p := 2) e
    rw [h.pCore_eq_bot_of_normal M] at h1
    exact (map_eq_bot_iff_of_injective _ e.injective).mp h1
  rw [hP, bot_sup_eq] at ha
  rw [hP, bot_sup_eq, ha, inf_top_eq] at hb
  have hlayer : Layer.subgroup M = ⊤ := by
    rw [← Layer.equiv_invariant e]
    change (goldschmidtLayer (M ⧸ goldschmidtOddCore M)).map e.toMonoidHom = ⊤
    rw [ha]
    exact map_top_of_surjective _ e.surjective
  have hsub : IsSubnormal M ⊤ :=
    Components.chain_of_mathlib_subnormal hMn.isSubnormal
  refine ⟨le_antisymm (sSup_le fun K hK => hK.2) ?_, ?_, ?_⟩
  ·
    intro x hx
    have hxL : (⟨x, hx⟩ : M) ∈ Layer.subgroup M := by rw [hlayer]; exact mem_top _
    have hmap : (Layer.subgroup M).map M.subtype ≤
        sSup {K : Subgroup H | IsComponentOf K ⊤ ∧ K ≤ M} := by
      refine map_le_iff_le_comap.mpr (sSup_le fun K' hK' => map_le_iff_le_comap.mp ?_)
      exact le_sSup ⟨LocalComponents.of_subnormal_subgroup M hsub K' hK', map_subtype_le K'⟩
    exact hmap (mem_map_of_mem M.subtype hxL)
  ·
    intro x hxS hxM hx2
    set xm : M := ⟨x, hxM⟩
    have hy2 : (QuotientGroup.mk' (goldschmidtOddCore M) xm) ^ 2 = 1 := by
      have : xm ^ 2 = 1 := Subtype.ext (by simpa [sq] using hx2)
      rw [← map_pow, this, map_one]
    have hyc : QuotientGroup.mk' (goldschmidtOddCore M) xm ∈ closure {s | s ∈
        ((S : Subgroup H).subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) ∧
          s ^ 2 = 1} :=
      subset_closure ⟨mem_map_of_mem _ (mem_subgroupOf.mpr hxS), hy2⟩
    rw [← hb] at hyc
    obtain ⟨v, hv, hve⟩ := mem_map.mp hyc
    have hvx : v = xm := by
      have h1 := congrArg e hve
      rwa [he, he] at h1
    have : (v : H) ∈ V := mem_subgroupOf.mp hv
    rwa [hvx] at this
  ·
    intro K hK hKM
    have hK' : IsComponentOf (K.subgroupOf M) ⊤ := LocalComponents.of_overgroup hK hKM
    have hK'' : IsComponentOf ((K.subgroupOf M).map e.symm.toMonoidHom) ⊤ :=
      (LocalComponents.equiv_iff e.symm _).mpr hK'
    have hT := hc _ hK''
    let φ : ((K.subgroupOf M).map e.symm.toMonoidHom) ≃* K :=
      ((K.subgroupOf M).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans
        (subgroupOfEquivOfLe hKM)
    let ψ : (((K.subgroupOf M).map e.symm.toMonoidHom) ⧸
        center ((K.subgroupOf M).map e.symm.toMonoidHom)) ≃* (K ⧸ center K) :=
      QuotientGroup.congr _ _ φ (map_center_eq φ)
    exact CFSG.Goldschmidt.Red2.goldschmidtSimpleType_of_mulEquiv ψ.symm hT

end Goldschmidt

end LocalSetting

end CFSG.LocalAnalysis.EvenBN.GMS
