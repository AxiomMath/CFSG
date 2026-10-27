module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Outside

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem aor_oddInner_of_conj_range {L : Subgroup G}
    (h : ∀ (α : MulAut ↥L) (k : ℕ), Odd k → α ^ k ∈ (MulAut.conj : ↥L →* MulAut ↥L).range →
      α ∈ (MulAut.conj : ↥L →* MulAut ↥L).range) : Asc82OddInner L := by
  unfold Asc82OddInner
  intro y hyN hyodd
  let n : normalizer (L : Set G) := ⟨y, hyN⟩
  let α : MulAut ↥L := L.normalizerMonoidHom n
  have hαk : α ^ orderOf y = 1 := by
    have hn : n ^ orderOf y = 1 := by
      simpa [n] using pow_orderOf_eq_one n
    simp only [α]
    rw [← map_pow, hn, map_one]
  have hmem : α ∈ (MulAut.conj : ↥L →* MulAut ↥L).range :=
    h α (orderOf y) hyodd (by rw [hαk]; exact Subgroup.one_mem _)
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hmem
  have hrel : ∀ x : ↥L, (l : G) * (x : G) * (l : G)⁻¹ = y * (x : G) * y⁻¹ := by
    intro x
    have hx := congrArg (fun f : MulAut ↥L => ((f x : ↥L) : G)) hl
    simpa [α, n, MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] using hx
  let c : G := (l : G)⁻¹ * y
  have hc : c ∈ centralizer (L : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hxL => ?_
    have hxrel := hrel ⟨x, hxL⟩
    have h2 := congrArg (fun z : G => (l : G)⁻¹ * z * y) hxrel
    have e1 : (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * y = x * (l : G)⁻¹ * y := by
      group
    have e2 : (l : G)⁻¹ * (y * x * y⁻¹) * y = (l : G)⁻¹ * y * x := by
      group
    rw [e1, e2] at h2
    show x * c = c * x
    simpa only [c, mul_assoc] using h2
  have hlc : (l : G) * c ∈ L ⊔ centralizer (L : Set G) := Subgroup.mul_mem_sup l.2 hc
  have hyl : (l : G) * c = y := by simp only [c]; group
  rwa [hyl] at hlc

end CFSG.OddStandard.SmallF3.Omega
