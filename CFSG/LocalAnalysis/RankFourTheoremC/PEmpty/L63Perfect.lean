module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fusion

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem sylow_le_commutator (hS : Situation G p P M) : (P : Subgroup G) ≤ ⁅M, M⁆ := by
  haveI : Fact p.Prime := ⟨hS.prime⟩
  haveI := hS.simple
  have hperf : commutator G = ⊤ := by
    rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with
      h | h
    · obtain ⟨a, b, hab⟩ := hS.nonab
      exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
    · exact h
  have hfoc := Subgroup.commutator_inf_eq_focalSubgroup P
  rw [hperf, top_inf_eq] at hfoc
  rw [hfoc, Subgroup.focalSubgroup_def, Subgroup.closure_le]
  rintro _ ⟨hgP, x, hxP, u, rfl⟩
  have hux : u * x * u⁻¹ ∈ (P : Subgroup G) := by
    have h := (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hxP) hgP
    rw [commutatorElement_def] at h
    simpa [mul_assoc] using (P : Subgroup G).inv_mem h
  have hmap : (zpowers x).map (MulAut.conj u⁻¹⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    simpa [MulAut.conj_apply] using hux
  obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le hS (zpowers_le.mpr hxP) hmap
  have hcx : c⁻¹ * x * c = u * x * u⁻¹ := by
    simpa using hc x (mem_zpowers x)
  have heq : ⁅x, u⁆ = ⁅x, c⁻¹⁆ := by
    rw [commutatorElement_def, commutatorElement_def, inv_inv]
    calc x * u * x⁻¹ * u⁻¹ = x * (u * x * u⁻¹)⁻¹ := by group
      _ = x * (c⁻¹ * x * c)⁻¹ := by rw [hcx]
      _ = x * c⁻¹ * x⁻¹ * c := by group
  rw [heq]
  exact commutator_mem_commutator (hS.sylow_le hxP) (M.inv_mem hcM)

theorem eq_top_of_isPGroup_quotient (hS : Situation G p P M) (N : Subgroup M) [N.Normal]
    (hN : IsPGroup p (M ⧸ N)) : N = ⊤ := by
  haveI : Fact p.Prime := ⟨hS.prime⟩
  by_contra hNtop
  have hidx : 1 < N.index := by
    have h0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : N.index ≠ 1 := fun h => hNtop (Subgroup.index_eq_one.mp h)
    omega
  haveI hnt : Nontrivial (M ⧸ N) := Finite.one_lt_card_iff_nontrivial.mp hidx
  set π := QuotientGroup.mk' N with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  set P' : Sylow p M := P.subtype hS.sylow_le with hP'
  have himg : (P' : Subgroup M).map π = ⊤ := by
    have h := (Sylow.mapSurjective hπ P').3 (hN.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hPcomm : (P' : Subgroup M) ≤ _root_.commutator M := by
    have h1 : (_root_.commutator M).map M.subtype = ⁅M, M⁆ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    intro y hy
    have hyP : (y : G) ∈ (P : Subgroup G) := hy
    have := sylow_le_commutator hS hyP
    rw [← h1] at this
    obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp this
    exact (Subtype.ext hyy) ▸ hy'
  have hperfQ : _root_.commutator (M ⧸ N) = ⊤ := by
    have h2 : (_root_.commutator M).map π = _root_.commutator (M ⧸ N) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr hπ]
    rw [← h2, eq_top_iff, ← himg]
    exact Subgroup.map_mono hPcomm
  haveI : Group.IsPerfect (M ⧸ N) := Group.isPerfect_def.mpr hperfQ
  exact Group.IsPerfect.not_isNilpotent (M ⧸ N) hN.isNilpotent

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
