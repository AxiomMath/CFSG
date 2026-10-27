module

public import CFSG.Sporadic.Schreier.Co3Sp6
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public meta import CFSG.Sporadic.Schreier.Co3Sp6
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs
public import Certificates.Certificate3088
public import Certificates.Certificate2152
public import Certificates.Certificate2161

public section

namespace CFSG.EvenSmallLie.Sp6

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3
open CFSG.ComponentClassification.M12Cover
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
  (nonempty_mulEquiv_statedSp_of_lieModel)

theorem sp6InvReps_eq : sp6InvReps = [sp6Rep1, sp6Rep2, sp6Rep3, sp6Rep4] := rfl

theorem sp6_chain_check :
    sp6Q.check = true ∧ sp6Q.orderCertificate = 1451520 ∧
      siftA 36 (rawLevels 36 co3Sp36Arrs co3Sp36BaseArr) co3Sp36BaseArr 0
        (Array.ofFn fun i => (sp6A i : ℕ)) = true ∧
      siftA 36 (rawLevels 36 co3Sp36Arrs co3Sp36BaseArr) co3Sp36BaseArr 0
        (Array.ofFn fun i => (sp6B i : ℕ)) = true :=
  Certificates.certificate3088.1

theorem sp6_cover_check :
    repsOK 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹)))
      (cosetOrderTables sp6Q 1 2) (sp6InvReps.map toTable) 4000 = true ∧
    repSizes 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹)))
      (sp6InvReps.map toTable) 4000 = [63, 315, 945, 3780] ∧
    (sp6InvReps.map toTable).all (ordTest 36 2) = true :=
  Certificates.certificate3088.2.1

theorem sp6_cent_check₁ :
    centCheck sp6CentQ1 23040 sp6CentGens1 sp6FourReps1 sp6Rep1 = true :=
  Certificates.certificate3088.2.2.1

theorem sp6_cent_check₂ :
    centCheck sp6CentQ2 4608 sp6CentGens2 sp6FourReps2 sp6Rep2 = true :=
  Certificates.certificate3088.2.2.2.1

theorem sp6_cent_check₃ :
    centCheck sp6CentQ3 1536 sp6CentGens3 sp6FourReps3 sp6Rep3 = true :=
  Certificates.certificate3088.2.2.2.2.1

theorem sp6_cent_check₄ :
    centCheck sp6CentQ4 384 sp6CentGens4 sp6FourReps4 sp6Rep4 = true :=
  Certificates.certificate3088.2.2.2.2.2

theorem sp6Q_valid : ValidSchreier sp6Q := sp6_chain_check.1

theorem sp6Gens_mem : ∀ g ∈ sp6Gens, g ∈ sp6Q.originalSubgroup := fun g hg => by
  rw [sp6Q, certificate_originalSubgroup]
  exact Subgroup.subset_closure hg

theorem card_sp6Q : Nat.card sp6Q.originalSubgroup = 1451520 := by
  rw [← sp6Q.orderCertificate_eq_card sp6Q_valid, sp6_chain_check.2.1]

theorem mem_co3X36_of_siftA
    {g : Equiv.Perm (Fin 36)}
    (h : siftA 36 (rawLevels 36 co3Sp36Arrs co3Sp36BaseArr) co3Sp36BaseArr 0
      (Array.ofFn fun i => (g i : ℕ)) = true) : g ∈ co3X36 :=
  (siftA_iff_mem_originalSubgroup co3Sp36Arrays (by norm_num) co3Sp36_check.1
    (fun x => CFSG.Monster.B.Co2.getElem!_ofFn_nat _ x.2)).1 h

theorem sp6Q_originalSubgroup :
    sp6Q.originalSubgroup = co3X36 := by
  have hle : sp6Q.originalSubgroup ≤ co3X36 := by
    rw [sp6Q, certificate_originalSubgroup, Subgroup.closure_le]
    intro g hg
    rcases List.mem_pair.1 hg with rfl | rfl
    · exact mem_co3X36_of_siftA sp6_chain_check.2.2.1
    · exact mem_co3X36_of_siftA sp6_chain_check.2.2.2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_co3X36, card_sp6Q])

theorem sp6InvReps_mem : ∀ r ∈ sp6InvReps, r ∈ sp6Q.originalSubgroup
    ∧ orderOf r = 2 := by
  have hn : (36 : ℕ) < 2 ^ 32 := by norm_num
  intro r hr
  refine ⟨?_, (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
    (List.all_eq_true.1 sp6_cover_check.2.2 _ (List.mem_map_of_mem hr))⟩
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
  exact evalCodes_mem _ sp6Gens_mem w

theorem sp6_involution_cover :
    (∀ u ∈ sp6Q.originalSubgroup, orderOf u = 2 →
      ∃ r ∈ sp6InvReps, ∃ c ∈ sp6Q.originalSubgroup, u = c * r * c⁻¹) ∧
    ∀ r ∈ sp6InvReps, (conjClosure 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹)))
      (toTable r) 4000).1.size ≤ (conjClass sp6Q.originalSubgroup r).ncard := by
  have hn : (36 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hcov, hsz⟩ := exists_conj_of_repsOK hn sp6Q sp6Q_valid (listTables_spec hn sp6Gens_mem)
    1 (fun h hh => by rwa [inv_one, one_mul, mul_one]) (by norm_num) sp6InvReps
    (fun r hr => by rw [inv_one, one_mul]; exact sp6InvReps_mem r hr) 4000
    sp6_cover_check.1
  exact ⟨fun u hu ho => hcov u (by rwa [inv_one, one_mul]) ho, hsz⟩

theorem sp6_closure_sizes :
    (conjClosure 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹))) (toTable sp6Rep1)
      4000).1.size = 63 ∧
    (conjClosure 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹))) (toTable sp6Rep2)
      4000).1.size = 315 ∧
    (conjClosure 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹))) (toTable sp6Rep3)
      4000).1.size = 945 ∧
    (conjClosure 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹))) (toTable sp6Rep4)
      4000).1.size = 3780 := by
  have h := sp6_cover_check.2.1
  rw [sp6InvReps_eq] at h
  simpa only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] using h

theorem centralizerIn_eq_of_centCheck {r : Equiv.Perm (Fin 36)}
    {cl c : ℕ}
    (hcl : cl ≤ (conjClass sp6Q.originalSubgroup r).ncard) (hc : c * cl = 1451520)
    {gs reps : List (Equiv.Perm (Fin 36))} (hgs : ∀ g ∈ gs, g ∈ sp6Q.originalSubgroup)
    {Q : RawSchreierDatum 36} (hQ : Q.originalSubgroup = Subgroup.closure {g | g ∈ gs})
    (hreps : ∀ x ∈ reps, ∃ w, x = evalCodes gs w) (h : centCheck Q c gs reps r = true) :
    centralizerIn sp6Q.originalSubgroup r = Q.originalSubgroup ∧
      Nat.card Q.originalSubgroup = c ∧ FourClassesLarge Q.originalSubgroup := by
  have hn : (36 : ℕ) < 2 ^ 32 := by norm_num
  simp only [centCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hQv, hQc⟩, hcomm⟩, hok⟩, hsz⟩, h4⟩ := h
  have hcard : Nat.card Q.originalSubgroup = c := by rw [← Q.orderCertificate_eq_card hQv, hQc]
  have hgs' : ∀ g ∈ gs, g ∈ Q.originalSubgroup := fun g hg => by
    rw [hQ]
    exact Subgroup.subset_closure hg
  refine ⟨centralizerIn_eq_of_le _ r (by rw [hQ]; exact closure_le_centralizerIn hn hgs hcomm) hcl
    (by rw [hcard, card_sp6Q, ← hc, mul_comm]), hcard,
    fourClassesLarge_of_repsOK hn Q hQv gs hgs' reps (fun x hx => ⟨?_, ?_⟩) 4000 hok
      fun x hx => ?_⟩
  · obtain ⟨w, rfl⟩ := hreps x hx
    exact evalCodes_mem _ hgs' w
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 h4 _ (List.mem_map_of_mem hx))
  · exact of_decide_eq_true (List.all_eq_true.1 hsz _
      (List.mem_map_of_mem (List.mem_map_of_mem hx)))

theorem evalCodes_map_mem {ws : List (List ℤ)} :
    ∀ g ∈ ws.map (evalCodes sp6Gens), g ∈ sp6Q.originalSubgroup := fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalCodes_mem _ sp6Gens_mem w

theorem exists_word_of_mem_map {gs : List (Equiv.Perm (Fin 36))} {ws : List (List ℤ)} :
    ∀ x ∈ ws.map (evalCodes gs), ∃ w, x = evalCodes gs w := fun x hx => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact ⟨w, rfl⟩

theorem sp6_cent_spec₁ : centralizerIn sp6Q.originalSubgroup sp6Rep1
    = sp6CentQ1.originalSubgroup ∧
    Nat.card sp6CentQ1.originalSubgroup = 23040 ∧ FourClassesLarge sp6CentQ1.originalSubgroup :=
  centralizerIn_eq_of_centCheck
    (sp6_closure_sizes.1 ▸ sp6_involution_cover.2 _ (by rw [sp6InvReps_eq]; simp))
    (by norm_num) (gs := sp6CentGens1) evalCodes_map_mem
    (by rw [sp6CentQ1, certificate_originalSubgroup]) exists_word_of_mem_map sp6_cent_check₁

theorem sp6_cent_spec₂ : centralizerIn sp6Q.originalSubgroup sp6Rep2
    = sp6CentQ2.originalSubgroup ∧
    Nat.card sp6CentQ2.originalSubgroup = 4608 ∧ FourClassesLarge sp6CentQ2.originalSubgroup :=
  centralizerIn_eq_of_centCheck
    (sp6_closure_sizes.2.1 ▸ sp6_involution_cover.2 _ (by rw [sp6InvReps_eq]; simp))
    (by norm_num) (gs := sp6CentGens2) evalCodes_map_mem
    (by rw [sp6CentQ2, certificate_originalSubgroup]) exists_word_of_mem_map sp6_cent_check₂

theorem sp6_cent_spec₃ : centralizerIn sp6Q.originalSubgroup sp6Rep3
    = sp6CentQ3.originalSubgroup ∧
    Nat.card sp6CentQ3.originalSubgroup = 1536 ∧ FourClassesLarge sp6CentQ3.originalSubgroup :=
  centralizerIn_eq_of_centCheck
    (sp6_closure_sizes.2.2.1 ▸ sp6_involution_cover.2 _ (by rw [sp6InvReps_eq]; simp))
    (by norm_num) (gs := sp6CentGens3) evalCodes_map_mem
    (by rw [sp6CentQ3, certificate_originalSubgroup]) exists_word_of_mem_map sp6_cent_check₃

theorem sp6_cent_spec₄ : centralizerIn sp6Q.originalSubgroup sp6Rep4
    = sp6CentQ4.originalSubgroup ∧
    Nat.card sp6CentQ4.originalSubgroup = 384 ∧ FourClassesLarge sp6CentQ4.originalSubgroup :=
  centralizerIn_eq_of_centCheck
    (sp6_closure_sizes.2.2.2 ▸ sp6_involution_cover.2 _ (by rw [sp6InvReps_eq]; simp))
    (by norm_num) (gs := sp6CentGens4) evalCodes_map_mem
    (by rw [sp6CentQ4, certificate_originalSubgroup]) exists_word_of_mem_map sp6_cent_check₄

theorem co3X36_involution_centralizers :
    (∀ v ∈ co3X36, orderOf v = 2 →
      ∃ r ∈ [sp6Rep1, sp6Rep2, sp6Rep3, sp6Rep4], ∃ c ∈ co3X36, v = c * r * c⁻¹) ∧
    Nat.card (centralizerIn co3X36 sp6Rep1) = 23040 ∧
    Nat.card (centralizerIn co3X36 sp6Rep2) = 4608 ∧
    Nat.card (centralizerIn co3X36 sp6Rep3) = 1536 ∧
    Nat.card (centralizerIn co3X36 sp6Rep4) = 384 ∧
    ∀ v ∈ co3X36, orderOf v = 2 → FourClassesLarge (centralizerIn co3X36 v) := by
  rw [← sp6Q_originalSubgroup, ← sp6InvReps_eq]
  refine ⟨sp6_involution_cover.1, by rw [sp6_cent_spec₁.1, sp6_cent_spec₁.2.1],
    by rw [sp6_cent_spec₂.1, sp6_cent_spec₂.2.1], by rw [sp6_cent_spec₃.1, sp6_cent_spec₃.2.1],
    by rw [sp6_cent_spec₄.1, sp6_cent_spec₄.2.1], fun v hv h2 => ?_⟩
  obtain ⟨r, hr, c, hc, rfl⟩ := sp6_involution_cover.1 v hv h2
  refine FourClassesLarge.of_mulEquiv (centralizerInConjEquiv _ hc r).symm ?_
  rw [sp6InvReps_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [sp6_cent_spec₁.1]
    exact sp6_cent_spec₁.2.2
  · rw [sp6_cent_spec₂.1]
    exact sp6_cent_spec₂.2.2
  · rw [sp6_cent_spec₃.1]
    exact sp6_cent_spec₃.2.2
  · rw [sp6_cent_spec₄.1]
    exact sp6_cent_spec₄.2.2

theorem nonempty_mulEquiv_co3X36
    {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y .PSp 3 2 1) : Nonempty (Y ≃* co3X36) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSp_of_lieModel hY
  exact ⟨e.trans co3Sp6Equiv⟩

theorem sp62_fourClassesLarge
    {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y .PSp 3 2 1)
    (v : Y) (hv : orderOf v = 2) : FourClassesLarge (Subgroup.centralizer ({v} : Set Y)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hY
  refine FourClassesLarge.of_mulEquiv (centralizerEquiv e v) ?_
  refine FourClassesLarge.of_mulEquiv (centralizerSubgroupEquiv _ (e v)) ?_
  exact co3X36_involution_centralizers.2.2.2.2.2 _ (e v).2
    (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hv])

theorem sp62_J_condition
    {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y .PSp 3 2 1)
    (v : Y) (hv : orderOf v = 2) : NoNormalFour (Subgroup.centralizer ({v} : Set Y)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hY
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  exact (sp62_fourClassesLarge hY v hv).noNormalFour

end CFSG.EvenSmallLie.Sp6
