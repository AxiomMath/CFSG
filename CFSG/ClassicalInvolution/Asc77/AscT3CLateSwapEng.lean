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

theorem Std20F.late_exists_swap (d : Std20F K K' J S R R' W V z t) :
    ∃ u ∈ (S : Subgroup G), conjSub u K = K' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg, hgK⟩ := d.swap
  have hS1 : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) ⊓
      Subgroup.centralizer ({z} : Set G) := fun u hu => by
    have h1 : u ∈ Subgroup.normalizer (K : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq]
      rcases d.late_conj_K (d.hSz hu) with h | h
      · exact h
      · exact absurd h (hcon u hu)
    exact ⟨h1, d.hSz hu⟩
  have hN₁C : Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.centralizer ({z} : Set G) := inf_le_right
  have hrel : (Subgroup.normalizer (K : Set G) ⊓
      Subgroup.centralizer ({z} : Set G)).relIndex (Subgroup.centralizer ({z} : Set G)) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨g, hg, fun b hb => ?_⟩
    have hbK' : conjSub b K' = K ∨ conjSub b K' = K' := d.late_conj_K' hb
    have hbK : conjSub b K = K ∨ conjSub b K = K' := d.late_conj_K hb
    have hbgK : conjSub (b * g) K = conjSub b K' := by rw [conjSub_mul, hgK]
    rcases hbK with h | h
    · have h' : conjSub b K' = K' := (d.late_conj_iff hb).mp h
      have h1 : b ∈ Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
        ⟨mem_normalizer_iff_conjSub_eq.mpr h, hb⟩
      have h2 : b * g ∉ Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer ({z} : Set G) := by
        intro hbg
        have := mem_normalizer_iff_conjSub_eq.mp hbg.1
        rw [hbgK, h'] at this
        exact d.ne this
      exact Or.inr ⟨h1, h2⟩
    · have h' : conjSub b K' = K := by
        rcases hbK' with h'' | h''
        · exact h''
        · exact absurd (conjSub_injective b (h.trans h''.symm)) d.ne.symm
      have h1 : b * g ∈ Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer ({z} : Set G) :=
        ⟨mem_normalizer_iff_conjSub_eq.mpr (hbgK.trans h'), Subgroup.mul_mem _ hb hg⟩
      have h2 : b ∉ Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({z} : Set G) := by
        intro hbN
        have := mem_normalizer_iff_conjSub_eq.mp hbN.1
        rw [h] at this
        exact d.ne this
      exact Or.inl ⟨h1, h2⟩
  have hidx := Subgroup.relIndex_mul_index hN₁C
  rw [hrel] at hidx
  have hdvd := Subgroup.index_dvd_of_le hS1
  have h2 : 2 ∣ (Subgroup.normalizer (K : Set G) ⊓
      Subgroup.centralizer ({z} : Set G)).index := ⟨_, hidx.symm⟩
  exact Sylow.not_dvd_index S (h2.trans hdvd)

theorem Std20F.late_swap_data (d : Std20F K K' J S R R' W V z t) {u : G}
    (hu : u ∈ (S : Subgroup G)) (huK : conjSub u K = K') :
    conjSub u K' = K ∧ conjSub u R = R' ∧ conjSub u W = W ∧ conjSub u (S : Subgroup G) = S := by
  have huz : u ∈ Subgroup.centralizer ({z} : Set G) := d.hSz hu
  have hK' : conjSub u K' = K := by
    rcases d.late_conj_K' huz with h | h
    · exact h
    · exact absurd (conjSub_injective u (huK.trans h.symm)) d.ne.symm
  have huS : conjSub u (S : Subgroup G) = S := conjSub_eq_self_of_mem hu
  refine ⟨hK', ?_, mem_normalizer_iff_conjSub_eq.mp (d.hWN hu), huS⟩
  rw [d.late_R_eq, d.late_R'_eq, late_conjSub_infE, huK, huS]

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
