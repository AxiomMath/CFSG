module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.Sporadic.Schreier.LyOuter

public section

namespace CFSG.ClassicalInvolution

namespace LyProof

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier
open CFSG.Sporadic.Schreier (centralizerIn)

abbrev GrpEquiv (F F' : Type*) [Group F] [Group F'] : Type _ := F ≃* F'


noncomputable abbrev zJ : J := lyz

noncomputable abbrev KJ : Subgroup J := lyC

noncomputable abbrev SJ : Subgroup J := (lySylow : Subgroup J)

theorem z_facts : zJ * zJ = 1 ∧ zJ ≠ 1 :=
  ⟨lyz_mul_self, fun h => by
    have := orderOf_lyz
    rw [show lyz = 1 from h, orderOf_one] at this
    exact absurd this (by norm_num)⟩

theorem K_facts :
    Subgroup.centralizer ({zJ} : Set J) = KJ ∧ CFSG.Open.IsQuasisimple KJ ∧
      Nat.card (Subgroup.center KJ) = 2 ∧ Nat.card KJ = 39916800 := by
  obtain ⟨-, -, -, -, -, -, -, hcard, -⟩ := centralizer_double_cover
  exact ⟨lyC_eq_centralizer.symm,
    ⟨(Group.isPerfect_def (G := lyC)).1 isQuasisimple_lyC.1, isQuasisimple_lyC.2.1⟩,
    card_center_lyC, hcard⟩

theorem S_facts :
    Nat.card SJ = 256 ∧ ∀ s ∈ SJ, s * s = 1 → s ≠ 1 → ∃ C : J, s = C * zJ * C⁻¹ := by
  refine ⟨card_lyS, fun s _ hss hs1 => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ :=
    involution_centralizer_fusion_generator.2 s (orderOf_eq_prime (by rw [pow_two]; exact hss) hs1)
  exact ⟨c, hc.symm⟩

theorem S_sylow : IsPGroup 2 SJ ∧ ¬ 2 ∣ (SJ.subgroupOf ⊤).index := by
  refine ⟨(lySylow : Sylow 2 J).isPGroup', ?_⟩
  have e : (SJ.subgroupOf ⊤).index = SJ.index := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  have hm := SJ.card_mul_index
  rw [S_facts.1, card_J] at hm
  rw [e]
  omega

theorem exists_noncentral_involution : ∃ u ∈ KJ, u * u = 1 ∧ u ≠ 1 ∧ u ≠ zJ := by
  have hea := eaSub_ea e16a_mem
  have hcard : Nat.card (lyE1 : Subgroup lyS) = 16 := eaSub_card e16a_mem
  obtain ⟨u, hu, hu'⟩ : ∃ u ∈ (lyE1 : Set lyS), u ∉ ({1, zS} : Set lyS) := by
    by_contra hc
    push Not at hc
    have h1 : Nat.card (lyE1 : Subgroup lyS) ≤ ({1, zS} : Set lyS).ncard := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hc (Set.toFinite _)
    have h2 : ({1, zS} : Set lyS).ncard ≤ 2 := by
      have := Set.ncard_insert_le (1 : lyS) {zS}
      rw [Set.ncard_singleton] at this
      exact this
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu'
  refine ⟨u, lyS_le_lyC u.2, ?_, fun h => hu'.1 (Subtype.ext h), fun h => hu'.2 (Subtype.ext h)⟩
  have h2' : u * u = 1 := ea_sq hea hu
  rw [← Subgroup.coe_mul, h2', Subgroup.coe_one]

theorem noNonsolvableClassical_J : NoNonsolvableClassical J := by
  obtain ⟨hCK, hq, hcen, hcard⟩ := K_facts
  obtain ⟨hSp, hidx⟩ := S_sylow
  obtain ⟨-, hcover⟩ := S_facts
  have htop : NoNonsolvableClassical (⊤ : Subgroup J) := by
    refine noNonsolvableClassical_of_single_class_quasisimple (⊤ : Subgroup J) SJ KJ hSp hidx
      (Subgroup.mem_top zJ) ?_ ?_ hq hcen (Or.inr hcard)
    · intro s hs hord
      have hss : s * s = 1 := by
        have := pow_orderOf_eq_one s
        rwa [hord, pow_two] at this
      have hs1 : s ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hord
        exact absurd hord (by norm_num)
      obtain ⟨C, hC⟩ := hcover s hs hss hs1
      exact ⟨C, Subgroup.mem_top C, hC⟩
    · rw [centralizerIn, top_inf_eq]
      exact hCK
  have e : GrpEquiv J (⊤ : Subgroup J) := (Subgroup.topEquiv (G := J)).symm
  exact NoNonsolvableClassical.of_mulEquiv e htop

theorem noNonsolvableClassical_Ly_centralizer :
    NoNonsolvableClassical CFSG.Blueprint.NativeSporadic.Ly := by
  have e : GrpEquiv CFSG.Blueprint.NativeSporadic.Ly J := lyEquivJ
  exact NoNonsolvableClassical.of_mulEquiv e noNonsolvableClassical_J

end LyProof

end CFSG.ClassicalInvolution
