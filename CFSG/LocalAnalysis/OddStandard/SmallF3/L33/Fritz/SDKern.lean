module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDDict

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCtx

open Subgroup Equiv CFSG.ComponentClassification.HSFLit
open CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (ctx : SDCtx X t L)

include ctx

theorem eq_one_or_eq_t_of_centralizer {g : X} (hg : g ∈ centralizer ({t} : Set X))
    (hgL : g ∈ centralizer (L : Set X)) : g = 1 ∨ g = t := by
  have hgT : g ∈ ctx.A.T :=
    SDSylowT.ker_le_sylowIn ctx.isPGroup_ker ctx.A.config.le_normalizer ctx.A.syl ⟨hg, hgL⟩
  have hgK : g ∈ coreActionKernel L := by
    refine ⟨ctx.A.config.le_normalizer hg, fun j hj => ?_⟩
    have hcomm : j * g = g * j := mem_centralizer_iff.mp hgL j hj
    have h1 : j⁻¹ * g⁻¹ * j * g = 1 := by
      calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * (j * g)) := by group
        _ = j⁻¹ * (g⁻¹ * (g * j)) := by rw [hcomm]
        _ = 1 := by group
    rw [h1]
    exact one_mem _
  have hgK' : g ∈ ctx.A.K := ⟨hgT, hgK⟩
  have hdvd : orderOf g ∣ Nat.card ctx.A.K := Subgroup.orderOf_dvd_natCard ctx.A.K hgK'
  rw [ctx.C.card_K] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact Or.inl (orderOf_eq_one_iff.mp h)
  · refine Or.inr (ctx.A.eq_t_of_mem_K hgK' ?_ ?_)
    · rw [← h]; exact pow_orderOf_eq_one g
    · intro h1
      rw [h1, orderOf_one] at h
      exact absurd h (by norm_num)

theorem actX_eq_one_iff {g : X} (hg : g ∈ centralizer ({t} : Set X)) :
    ctx.actX g = 1 ↔ g = 1 ∨ g = t := by
  constructor
  · intro h
    refine eq_one_or_eq_t_of_centralizer ctx hg ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : l = g * l * g⁻¹ := by
      have h2 := ctx.actX_apply hg ⟨l, hl⟩
      rw [h, MulAut.one_apply] at h2
      exact h2
    conv_lhs => rw [h1]
    group
  · rintro (hg1 | hgt)
    · rw [hg1]; exact ctx.actX_one
    · rw [hgt]
      have ht : t ∈ centralizer ({t} : Set X) := by
        rw [mem_centralizer_singleton_iff]
      refine MulEquiv.ext fun l => Subtype.ext ?_
      rw [ctx.actX_apply ht l, MulAut.one_apply]
      have hcomm : (l : X) * t = t * l :=
        mem_centralizer_singleton_iff.mp (ctx.L_le_centralizer l.2)
      calc t * (l : X) * t⁻¹ = ((l : X) * t) * t⁻¹ := by rw [← hcomm]
        _ = (l : X) := by group

theorem exists_actX_eq (φ : MulAut ↥L) : ∃ g ∈ centralizer ({t} : Set X), ctx.actX g = φ := by
  have hIR : (MulAut.conj : ↥L →* MulAut ↥L).range ≤ ctx.act.range :=
    SDAct.inn_le_range_actC ctx.A.config.le_normalizer ctx.L_le_centralizer
  have hkC : ctx.C.k ∈ centralizer ({t} : Set X) := ctx.A.T_le_centralizer ctx.C.k_mem
  have hkR : ctx.M.F.k ∈ ctx.act.range := by
    refine ⟨⟨ctx.C.k, hkC⟩, ?_⟩
    rw [← ctx.actX_of_mem hkC]
    exact actX_k ctx
  have hkI : ctx.M.F.k ∉ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rintro ⟨a, ha⟩
    apply ctx.M.F.k_outer
    refine ⟨a, fun u => ?_⟩
    have h1 : (MulAut.conj a) u = ctx.M.F.k u := congrArg (fun e : MulAut ↥L => e u) ha
    rw [MulAut.conj_apply] at h1
    exact h1.symm
  have hidx_dvd : ctx.act.range.index ∣ (MulAut.conj : ↥L →* MulAut ↥L).range.index :=
    Subgroup.index_dvd_of_le hIR
  rw [ctx.M.index_inner] at hidx_dvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx_dvd with h | h
  · have htop : ctx.act.range = ⊤ := Subgroup.index_eq_one.mp h
    have hmem : φ ∈ ctx.act.range := by rw [htop]; exact Subgroup.mem_top φ
    obtain ⟨g, hg⟩ := hmem
    exact ⟨g.1, g.2, by rw [ctx.actX_of_mem g.2]; exact hg⟩
  · exfalso
    have hrel : ((MulAut.conj : ↥L →* MulAut ↥L).range).relIndex ctx.act.range = 1 := by
      have hh := Subgroup.relIndex_mul_index hIR
      rw [h, ctx.M.index_inner] at hh
      omega
    have hRI : ctx.act.range ≤ (MulAut.conj : ↥L →* MulAut ↥L).range :=
      Subgroup.relIndex_eq_one.mp hrel
    have hEq : ctx.act.range = (MulAut.conj : ↥L →* MulAut ↥L).range := le_antisymm hRI hIR
    rw [hEq] at hkR
    exact hkI hkR

end CFSG.OddStandard.SmallF3.L33.KD.SDCtx
