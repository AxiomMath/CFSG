module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinL2p
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6Out

public section

namespace CFSG.QuasithinUnique.Out21

open CFSG.Open CFSG.Quasithin

section A6

variable {G : Type} [Group G] [Finite G] {K H S : Subgroup G}

omit [Finite G] in
theorem card_autOn_H_a6
    (hM : Nonempty (↥(autOn H K) ≃* ↥A6Models.m10) ∨ Nonempty (↥(autOn H K) ≃* ↥A6Models.pgl29)) :
    Nat.card ↥(autOn H K) = 720 := by
  rcases hM with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · rw [Nat.card_congr φ.toEquiv]
    exact A6.card_m10
  · rw [Nat.card_congr φ.toEquiv]
    exact A6.card_pgl29

theorem card_autOn_S_a6 (h : OutSetting K H S)
    (hM : Nonempty (↥(autOn H K) ≃* ↥A6Models.m10) ∨ Nonempty (↥(autOn H K) ≃* ↥A6Models.pgl29)) :
    Nat.card ↥(autOn S K) = 16 := by
  rw [(isSylowTwoOf_autOn h).card_eq]
  exact twoPart_eq_pow (k := 4) (b := 45) (by norm_num) (by norm_num [card_autOn_H_a6 hM])

theorem card_inf_a6 (h : OutSetting K H S) (e6 : ↥K ≃* alternatingGroup (Fin 6)) :
    Nat.card ↥(S ⊓ K) = 8 := by
  rw [(isSylowTwoOf_inf h).card_eq]
  exact twoPart_eq_pow (k := 3) (b := 45) (by norm_num) (by norm_num [card_K_of_a6 e6])

theorem hasDS_a6 (h : OutSetting K H S)
    (hM : Nonempty (↥(autOn H K) ≃* ↥A6Models.m10) ∨ Nonempty (↥(autOn H K) ≃* ↥A6Models.pgl29)) :
    ∃ R : Subgroup ↥(autOn S K), DS.DSData R := by
  have hle : autOn S K ≤ autOn H K := (isSylowTwoOf_autOn h).le
  have hP : IsSylowTwoOf ((autOn S K).subgroupOf (autOn H K)) (⊤ : Subgroup ↥(autOn H K)) :=
    (Unc25Small.isSylowTwoOf_subgroupOf_top_iff hle).mp (isSylowTwoOf_autOn h)
  have hDS : ∃ R : Subgroup ↥((autOn S K).subgroupOf (autOn H K)), DS.DSData R := by
    rcases hM with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · have : Finite ↥(autOn H K) := Finite.of_equiv _ φ.symm.toEquiv
      exact A6.hasDS_of_sylow_m10 φ hP
    · have : Finite ↥(autOn H K) := Finite.of_equiv _ φ.symm.toEquiv
      exact A6.hasDS_of_sylow_pgl29 φ hP
  exact hasDS_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hDS

end A6

end CFSG.QuasithinUnique.Out21

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Out21

theorem outShape : OutShape := by
  intro G _ _ K H S h
  have key : Nat.card ↥(autOn S K) ≤ 2 * Nat.card ↥(S ⊓ K) ∧
      ∃ R : Subgroup ↥(autOn S K), DS.DSData R := by
    rcases h.fam with hX | ⟨⟨e6⟩, hM⟩
    · obtain ⟨F, _, _, p, _, hp7, hF, hmod, ⟨e⟩⟩ := model_of_isL2pType hX
      exact ⟨card_autOn_le_of_equiv h hp7 hF e, hasDS_of_equiv h hp7 hF hmod e⟩
    · refine ⟨?_, hasDS_a6 h hM⟩
      have h1 := card_autOn_S_a6 h hM
      have h2 := card_inf_a6 h e6
      omega
  exact ⟨card_S_le h key.1, key.2⟩

theorem outOneClass : OutOneClass := by
  intro G _ _ K H S h i j hi hj hi2 hj2 hi1 hj1
  rcases h.fam with hX | ⟨⟨e6⟩, -⟩
  · exact oneClass_of_l2p hX hi hj hi2 hj2 hi1 hj1
  · obtain ⟨k, hk⟩ := A6.a6_involutions_conj e6 ⟨i, hi⟩ ⟨j, hj⟩
      (Subtype.ext (by simpa using hi2)) (Subtype.ext (by simpa using hj2))
      (fun h => hi1 (congrArg Subtype.val h)) (fun h => hj1 (congrArg Subtype.val h))
    exact ⟨k, k.2, by simpa using congrArg Subtype.val hk⟩

theorem outOuter : OutOuter := by
  intro G _ _ K H S h u hu hu2 hout
  rcases h.fam with hX | ⟨⟨e6⟩, hM⟩
  · obtain ⟨F, _, _, p, _, hp7, hF, -, ⟨e⟩⟩ := model_of_isL2pType hX
    exact outer_of_l2p h hp7 hF e hu hu2 hout
  · have hm10 : ¬ Nonempty (↥(autOn H K) ≃* ↥A6Models.m10) := fun ⟨φ⟩ =>
      false_of_outer_m10 h e6 φ hu hu2 hout
    refine ⟨hm10, ?_⟩
    rcases hM with hM | ⟨⟨φ⟩⟩
    · exact absurd hM hm10
    · exact oddCoreIn_ne_bot_of_oddNormalFix h hu
        (oddNormalFix_of_outer_pgl29 h e6 φ hu hu2 hout)

end CFSG.QuasithinUnique
