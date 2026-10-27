module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Tags
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Embed
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Prime
public import Certificates.Certificate442261
public import Certificates.Certificate442262
public import Certificates.Certificate442263
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Ind

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

private theorem gh23Sub_singleton {ρ : Equiv.Perm (Fin 8)} {c : ℕ} (hc : gh23Code ρ = c) :
    gh23Sub [c] = Subgroup.zpowers ρ := by
  unfold gh23Sub
  rw [Subgroup.zpowers_eq_closure]
  congr 1
  ext σ
  simp only [Set.mem_setOf_eq, List.mem_singleton, Set.mem_singleton_iff]
  constructor
  · intro h
    exact gh23_code_injective (h.trans hc.symm)
  · intro h
    rw [h]
    exact hc

private theorem member_zero : (⟨[16419025], .solv [[]]⟩ : MemberData) ∈ members :=
  List.mem_cons_self

private theorem member_one : (⟨[14899409], .solv [[]]⟩ : MemberData) ∈ members :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem gh23_alt8Rooted_of_checks
    (h1 : ∀ m ∈ members, ∀ σ ∈ alternatingGroup (Fin 8), ∃ m' ∈ members,
      gh23Sub m.gens ⊔ Subgroup.zpowers σ = gh23Sub m'.gens)
    (h2 : ∀ m ∈ members, (m.tag matches .solv _ | .two _) = true → GH23Spec (gh23Sub m.gens))
    (h3 : ∀ m ∈ members, (m.tag matches .solv _ | .two _) = false → GH23Spec (gh23Sub m.gens)) :
    Alt8Rooted := by
  intro H hHA hroot hns hno
  have hjoin := h1
  have hspec : ∀ m ∈ members, GH23Spec (gh23Sub m.gens) := by
    intro m hm
    cases hb : (m.tag matches .solv _ | .two _)
    · exact h3 m hm hb
    · exact h2 m hm hb
  let 𝓜 : Set (Subgroup (Equiv.Perm (Fin 8))) := {K | ∃ m ∈ members, K = gh23Sub m.gens}
  have hclosed : ∀ K ∈ 𝓜, ∀ σ ∈ alternatingGroup (Fin 8), K ⊔ Subgroup.zpowers σ ∈ 𝓜 := by
    rintro K ⟨m, hm, rfl⟩ σ hσ
    obtain ⟨m', hm', he⟩ := hjoin m hm σ hσ
    exact ⟨m', hm', he⟩
  have hmem : H ∈ 𝓜 := by
    rcases hroot with h5 | h7
    · have hK0 : gh23Sub [16419025] ∈ 𝓜 := ⟨_, member_zero, rfl⟩
      rw [gh23Sub_singleton gh23_code_g5] at hK0
      refine gh23_mem_of_join_closed 𝓜 (alternatingGroup (Fin 8)) hclosed hHA hK0 ?_
      exact (Subgroup.zpowers_le).mpr h5
    · have hK0 : gh23Sub [14899409] ∈ 𝓜 := ⟨_, member_one, rfl⟩
      rw [gh23Sub_singleton gh23_code_g7] at hK0
      refine gh23_mem_of_join_closed 𝓜 (alternatingGroup (Fin 8)) hclosed hHA hK0 ?_
      exact (Subgroup.zpowers_le).mpr h7
  obtain ⟨m, hm, rfl⟩ := hmem
  rcases hspec m hm with hsol | hnn | hconcl
  · exact absurd hsol hns
  · exact absurd hno hnn
  · exact hconcl

theorem ghii23List_of_checks
    (h1 : ∀ m ∈ members, ∀ σ ∈ alternatingGroup (Fin 8), ∃ m' ∈ members,
      gh23Sub m.gens ⊔ Subgroup.zpowers σ = gh23Sub m'.gens)
    (h2 : ∀ m ∈ members, (m.tag matches .solv _ | .two _) = true → GH23Spec (gh23Sub m.gens))
    (h3 : ∀ m ∈ members, (m.tag matches .solv _ | .two _) = false → GH23Spec (gh23Sub m.gens)) :
    GHII23List :=
  ghii23List_of_alt8 (alt8Classification_of_rooted (gh23_alt8Rooted_of_checks h1 h2 h3))

theorem ghii23List_holds :
    GHII23List :=
  ghii23List_of_checks Certificates.certificate442261 Certificates.certificate442262
    Certificates.certificate442263

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
