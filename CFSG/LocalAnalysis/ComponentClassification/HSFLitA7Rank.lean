module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAction
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGen

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem exists_finset_closure_eq_of_le_P0 {Q : Subgroup (Perm (Fin 7))} (hQ : Q ≤ P0) :
    ∃ s : Finset (Perm (Fin 7)), s.card ≤ 3 ∧ closure (s : Set (Perm (Fin 7))) = Q := by
  classical
  have hdvd : Nat.card Q ∣ 16 := card_P0 ▸ Subgroup.card_dvd_of_le hQ
  by_cases h16 : Nat.card Q = 16
  · have hQP : Q = P0 := Subgroup.eq_of_le_of_card_ge hQ (by rw [card_P0, h16])
    refine ⟨{a0, b0, c0}, Finset.card_le_three, le_antisymm ?_ ?_⟩
    · rw [closure_le, hQP]
      intro g hg
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact a0_mem_P0
      · exact b0_mem_P0
      · exact c0_mem_P0
    · rw [hQP]
      simpa using P0_le_closure
  · have hle : Nat.card Q ≤ 2 ^ 3 := by
      have hmem : Nat.card Q ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    exact exists_finset_closure_eq_of_card_le Q hle

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

theorem Config.exists_finset_closure_eq_of_le_sylowIn (h : Config t L)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))
    (T : Sylow 2 ↥(centralizer ({t} : Set X))) {U : Subgroup X} (hU : U ≤ Config.sylowIn T) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = U := by
  classical
  obtain ⟨ψ, hker, -, hP0, -⟩ := h.exists_good_action e T
  have hTN : Config.sylowIn T ≤ normalizer (L : Set X) :=
    (Config.sylowIn_le T).trans h.le_normalizer
  have hUN : U ≤ normalizer (L : Set X) := hU.trans hTN
  have hQ : (U.subgroupOf (normalizer (L : Set X))).map ψ ≤ P0 := by
    rintro _ ⟨g, hg, rfl⟩
    exact hP0 g (hU hg)
  obtain ⟨s, hs, hsU⟩ := exists_finset_closure_eq_of_le_P0 hQ
  have hKN : (Config.sylowIn T ⊓ coreActionKernel L : Subgroup X) ≤ normalizer (L : Set X) :=
    inf_le_left.trans hTN
  have : IsCyclic ((Config.sylowIn T ⊓ coreActionKernel L : Subgroup X).subgroupOf
      (normalizer (L : Set X))) :=
    (subgroupOfEquivOfLe hKN).isCyclic.mpr (h.isCyclic_inf_kernel T)
  have hle : (U.subgroupOf (normalizer (L : Set X)) ⊓ ψ.ker) ≤
      (Config.sylowIn T ⊓ coreActionKernel L : Subgroup X).subgroupOf
        (normalizer (L : Set X)) := by
    intro g hg
    exact ⟨hU (mem_inf.mp hg).1, (hker g).mp (mem_inf.mp hg).2⟩
  have : IsCyclic (U.subgroupOf (normalizer (L : Set X)) ⊓ ψ.ker : Subgroup _) :=
    Subgroup.isCyclic_of_le hle
  obtain ⟨r, hr, hrU⟩ := exists_finset_closure_eq_of_isCyclic
    (U.subgroupOf (normalizer (L : Set X)) ⊓ ψ.ker)
  obtain ⟨u, hu, huU⟩ := exists_finset_closure_eq_of_map ψ _ hs hsU hr hrU
  refine ⟨u.image (normalizer (L : Set X)).subtype, Finset.card_image_le.trans hu, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, huU, subgroupOf_map_subtype,
    inf_of_le_left hUN]

theorem Config.gen4_of_coe_sylow_eq (h : Config t L)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))
    (T : Sylow 2 ↥(centralizer ({t} : Set X))) (S : Sylow 2 X)
    (hS : (S : Subgroup X) = Config.sylowIn T) (P : Subgroup X) (hP : IsPGroup 2 P) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P :=
  exists_finset_closure_eq_of_sylow S
    (fun _ hU => h.exists_finset_closure_eq_of_le_sylowIn e T (hS ▸ hU)) P hP

end CFSG.ComponentClassification.HSFLit
