module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Stab
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210NoSplitA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X] {A : Subgroup X} {w : X}
  {ψ : ↥(normalizer (A : Set X)) →* A5WrTwo}

theorem L210_card_le_eight (h : Abs210 A w ψ) {D : Subgroup X} (hD : D ≤ normalizer (A : Set X))
    (hDe : IsElemAbelian 2 D) (hDA : D ⊓ A = ⊥) : Nat.card D ≤ 8 := by
  by_contra hle
  push Not at hle
  obtain ⟨C, hCK, hCψ⟩ := L210_exists_base_complement h.toL28Hyp hD hDe hDA hle
  let N : Subgroup X := normalizer (A : Set X)
  let wN : N := ⟨w, Subgroup.le_normalizer h.w_mem⟩
  let S : Subgroup A5WrTwo :=
    Subgroup.map ψ (Subgroup.centralizer ({(⟨w, Subgroup.le_normalizer h.w_mem⟩ : N)} : Set N))
  let Cw : Subgroup N := C ⊓ Subgroup.centralizer ({wN} : Set N)
  have hstab : Nonempty (↥S ≃* Equiv.Perm (Fin 5)) := h.stab
  have f : ↥(S ⊓ commutator A5WrTwo) ≃* alternatingGroup (Fin 5) :=
    (L28_nonempty_equiv_inf_base hstab.some).some
  have hCwψ : Cw.map ψ = S ⊓ commutator A5WrTwo := by
    ext y
    constructor
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨c, hc, rfl⟩
      exact ⟨Subgroup.mem_map.mpr ⟨c, hc.2, rfl⟩,
        hCψ ▸ Subgroup.mem_map.mpr ⟨c, hc.1, rfl⟩⟩
    · rintro ⟨hyS, hyB⟩
      rcases Subgroup.mem_map.mp hyS with ⟨x, hx, rfl⟩
      rw [← hCψ] at hyB
      rcases Subgroup.mem_map.mp hyB with ⟨c, hcC, hψc⟩
      refine Subgroup.mem_map.mpr ⟨c, ⟨hcC, ?_⟩, hψc⟩
      let a : N := x * c⁻¹
      have haψ : ψ a = 1 := by
        change ψ (x * c⁻¹) = 1
        rw [map_mul, map_inv, hψc, mul_inv_cancel]
      have haA : a ∈ A.subgroupOf N := by
        rw [← h.ker]
        exact MonoidHom.mem_ker.mpr haψ
      have haX : (a : X) ∈ A := Subgroup.mem_subgroupOf.mp haA
      have ha_cent : a ∈ Subgroup.centralizer ({wN} : Set N) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        have hc := (h.elemAb.1).is_comm.comm (⟨(a : X), haX⟩ : ↥A)
          (⟨w, h.w_mem⟩ : ↥A)
        simpa [wN, Subgroup.coe_mul] using congrArg (fun z : ↥A => (z : X)) hc
      have hc_eq : c = a⁻¹ * x := by
        change c = (x * c⁻¹)⁻¹ * x
        rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      rw [hc_eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha_cent) hx
  have hker_le : (ψ.comp Cw.subtype).ker ≤ ⊥ := by
    intro x hx
    rw [Subgroup.mem_bot]
    have hxψ : ψ (x : N) = 1 := by
      have := MonoidHom.mem_ker.mp hx
      simpa [MonoidHom.comp_apply] using this
    have hxint : (x : N) ∈ C ⊓ ψ.ker := ⟨x.2.1, MonoidHom.mem_ker.mpr hxψ⟩
    rw [hCK] at hxint
    exact Subtype.ext (Subgroup.mem_bot.mp hxint)
  have hinj : Function.Injective (ψ.comp Cw.subtype) :=
    (MonoidHom.ker_eq_bot_iff (ψ.comp Cw.subtype)).mp (le_bot_iff.mp hker_le)
  have hrange : (ψ.comp Cw.subtype).range = Cw.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hCw_alt : Nonempty (↥Cw ≃* alternatingGroup (Fin 5)) :=
    ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans
      ((MulEquiv.subgroupCongr hCwψ).trans f)⟩
  let D' : Subgroup X := Cw.map N.subtype
  have hD'le : D' ≤ normalizer (A : Set X) := by
    intro d hd
    rcases Subgroup.mem_map.mp hd with ⟨x, -, rfl⟩
    exact x.2
  have hD'comm : ∀ d ∈ D', d * w = w * d := by
    intro d hd
    rcases Subgroup.mem_map.mp hd with ⟨x, hx, rfl⟩
    have hxcomm : x * wN = wN * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    simpa [wN, Subgroup.coe_mul] using congrArg (fun z : N => (z : X)) hxcomm
  have hD'equiv : Nonempty (↥D' ≃* alternatingGroup (Fin 5)) :=
    ⟨((Subgroup.equivMapOfInjective Cw N.subtype Subtype.val_injective).symm).trans
      hCw_alt.some⟩
  exact (h.noA5 D' hD'le hD'comm).elim hD'equiv.some

end CFSG.EvenSporadicStandard.HNRecog.Harada
