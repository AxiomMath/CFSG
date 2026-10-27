module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem sign_eq_one_of_odd_orderOf {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : Odd (orderOf σ)) :
    Equiv.Perm.sign σ = 1 := by
  have h1 : (Equiv.Perm.sign σ) ^ orderOf σ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, Odd.neg_one_pow h] at h1
    exact absurd h1 (by decide)

theorem exists_derived_of_statedSp {C : Type} [Group C] {m : ℕ} (hm : 2 ≤ m)
    (e : C ≃* ↥(StatedSp m (ZMod 2))) :
    Lemma137b.GoodDer C ∧ 3 ∣ Nat.card ↥(commutator C) ∧
      ∀ c : C, Odd (orderOf c) → c ∈ commutator C := by
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · obtain rfl : m = 2 := by omega
    obtain ⟨f⟩ := OmegaFacts.nonempty_statedSp_two_mulEquiv_perm_six
    let g : C ≃* Equiv.Perm (Fin 6) := e.trans f
    have h5 : 5 ≤ Nat.card (Fin 6) := by simp
    have hmap : (commutator C).map g.toMonoidHom = alternatingGroup (Fin 6) := by
      unfold commutator
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ g.surjective]
      have := alternatingGroup.commutator_perm_eq h5
      rwa [commutator_def] at this
    refine ⟨Lemma137b.GoodDer.of_mulEquiv g.symm (Lemma137b.goodDer_perm (by norm_num)), ?_, ?_⟩
    · have hc : Nat.card ↥(commutator C) = Nat.card ↥(alternatingGroup (Fin 6)) :=
        Nat.card_congr ((Subgroup.equivMapOfInjective _ g.toMonoidHom g.injective).trans
          (MulEquiv.subgroupCongr hmap)).toEquiv
      have h2 := CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin 6
        (by norm_num)
      have h720 : Nat.factorial 6 = 720 := by decide
      omega
    · intro c hc
      have hsign : Equiv.Perm.sign (g c) = 1 :=
        sign_eq_one_of_odd_orderOf (by rwa [MulEquiv.orderOf_eq])
      have : g c ∈ (commutator C).map g.toMonoidHom := by
        rw [hmap]
        exact Equiv.Perm.mem_alternatingGroup.2 hsign
      have h' := Subgroup.mem_map_equiv.1 this
      rwa [MulEquiv.symm_apply_apply] at h'
  · haveI : IsSimpleGroup ↥(StatedSp m (ZMod 2)) := OmegaFacts.isSimpleGroup_statedSp_zmod_two h3
    haveI : IsSimpleGroup C := e.isSimpleGroup
    have h4 : 4 ∣ Nat.card C := by
      rw [Nat.card_congr e.toEquiv, OmegaFacts.card_statedSp_zmod_two]
      refine Dvd.dvd.mul_right ?_ _
      exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 (by nlinarith)
    have hnp : ¬ (Nat.card C).Prime := fun hprime =>
      absurd ((Nat.dvd_prime hprime).1 h4) (by
        rintro (h | h)
        · omega
        · rw [← h] at hprime
          exact absurd hprime (by norm_num))
    have hZ : Subgroup.center C = ⊥ := CatalogInputs.center_eq_bot_of_simple_not_prime hnp
    have htop : commutator C = ⊤ := OmegaFacts.commutator_eq_top_of_simple_of_center_bot hZ
    refine ⟨Lemma137b.goodDer_of_simple (Lemma137b.not_comm_of_simple_center_bot hZ), ?_,
      fun c _ => htop ▸ Subgroup.mem_top c⟩
    rw [htop, Subgroup.card_top, Nat.card_congr e.toEquiv, OmegaFacts.card_statedSp_zmod_two]
    refine Dvd.dvd.mul_left ?_ _
    have h1 : (2 ^ (2 * 1) - 1 : ℕ) ∣ ∏ j ∈ Finset.Icc 1 m, (2 ^ (2 * j) - 1) :=
      Finset.dvd_prod_of_mem (fun j => 2 ^ (2 * j) - 1) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
    simpa using h1

theorem exists_Y {X : Type} [Group X] (C : Subgroup X) {m : ℕ} (hm : 2 ≤ m)
    (e : ↥C ≃* ↥(StatedSp m (ZMod 2))) {z : X} (hz : z ∈ C) (hodd : Odd (orderOf z)) :
    ∃ Y : Subgroup X, Y ≤ C ∧ z ∈ Y ∧ IsSimpleGroup ↥Y ∧ (∃ x y : ↥Y, x * y ≠ y * x) ∧
      3 ∣ Nat.card ↥Y := by
  obtain ⟨hgd, h3, hodd'⟩ := exists_derived_of_statedSp hm e
  let e1 : ↥(commutator ↥C) ≃* ↥((commutator ↥C).map C.subtype) :=
    Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective
  refine ⟨(commutator ↥C).map C.subtype, Subgroup.map_subtype_le _,
    ⟨⟨z, hz⟩, hodd' ⟨z, hz⟩ (by rwa [Subgroup.orderOf_mk]), rfl⟩, ?_, ?_, ?_⟩
  · haveI := hgd.simple
    exact e1.symm.isSimpleGroup
  · by_contra hcon
    push Not at hcon
    apply hgd.nonab
    exact ⟨⟨fun x y => e1.injective (by rw [map_mul, map_mul]; exact hcon _ _)⟩⟩
  · rw [← Nat.card_congr e1.toEquiv]
    exact h3

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv
