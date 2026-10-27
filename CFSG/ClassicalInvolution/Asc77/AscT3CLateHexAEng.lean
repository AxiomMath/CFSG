module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfgEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20F.late_isSylow2In_S (d : Std20F K K' J S R R' W V z t) :
    IsSylow2In (S : Subgroup G) (Subgroup.centralizer ({z} : Set G)) :=
  ⟨d.hSz, S.isPGroup', fun _ _ hT2 hle => S.is_maximal' hT2 hle⟩

theorem Std20F.late_nbr (d : Std20F K K' J S R R' W V z t) :
    ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, L ∈ twinSet (CoreAssembly.conjClass K) K := by
  rintro L ⟨hL, -, R₁, hR₁, hR₁L, hR₁N⟩
  have hR₁z : R₁ ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := d.viol.hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hR₁N hx))
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [h]
  have hR₁2 : IsPGroup 2 R₁ := Sec7.isPGroup_of_mem_RSet hR₁
  obtain ⟨V₂, hV₂, hR₁V₂⟩ := IsSylow2In.exists_ge hR₁2 hR₁z
  obtain ⟨x, hx, hxS⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In d.late_isSylow2In_S hV₂
  have hle : conjSub x⁻¹ R₁ ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := x⁻¹) (hxS ▸ hR₁V₂ : R₁ ≤ conjSub x (S : Subgroup G))
    rwa [conjSub_inv_conjSub] at this
  have hmem : conjSub x⁻¹ R₁ ∈ RSet (CoreAssembly.conjClass K) :=
    RSet.conj d.hyp.conjInvariant hR₁ x⁻¹
  have hx8 : 4 ≤ Nat.card ↥R₁ := by
    have := Sec6Gen.eight_le_of_mem_RSet d.late_hΩ hR₁
    omega
  have hxz : x ∈ Subgroup.centralizer ({z} : Set G) := hx
  rw [d.twins]
  rcases d.hRG _ hmem hle with h | h
  · have hR₁eq : R₁ = conjSub x R := by rw [← h, conjSub_conjSub_inv]
    have hle2 : R₁ ≤ conjSub x K := hR₁eq ▸ conjSub_mono d.hR.1
    have hLK := Sec6Gen.eq_of_le_of_le d.late_hΩ hL
      (d.hyp.conjInvariant x K d.late_mem_K) hR₁2 hx8 hR₁L hle2
    rw [hLK]
    rcases d.late_conj_K hxz with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · have hR₁eq : R₁ = conjSub x R' := by rw [← h, conjSub_conjSub_inv]
    have hle2 : R₁ ≤ conjSub x K' := hR₁eq ▸ conjSub_mono d.hR'.1
    have hLK := Sec6Gen.eq_of_le_of_le d.late_hΩ hL
      (d.hyp.conjInvariant x K' d.late_mem_K') hR₁2 hx8 hR₁L hle2
    rw [hLK]
    rcases d.late_conj_K' hxz with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
