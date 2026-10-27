module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympCover
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding CFSG.Open Subgroup

theorem exists_mulEquiv_statedSp_of_lie_index (hZ : OddCenterRest) {Y : Type} [Group Y]
    [Finite Y] {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤)
    (hodd : Odd (Nat.card (center ↥L))) (d : TauCeti.LieTypeIndex) (hv : d.Valid)
    (hd : IdxB d) (e : ↥L ⧸ center ↥L ≃* (TauCeti.CFSGIndex.lie ⟨d, hv⟩).Group) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 2 ≤ r ∧
      (∀ (r₀ : ℕ) (q : TauCeti.PrimePower), d = .B r₀ q → Nat.card K = q.card) ∧
      Nonempty (↥L ≃* CFSG.Open.StatedSp r K) := by
  cases d
  case B r q =>
    have hq2 : q.p = 2 := hd
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hr : 2 ≤ r := hrange.1
    have hmodel : CFSG.Open.StatedClassicalModel (↥L ⧸ center ↥L) .PSp r 2 q.exponent := by
      by_cases h2 : r = 2
      · subst h2
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rwa [hq2] at hm
      · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2
          (by omega) e
        rwa [hq2] at hm
    obtain ⟨⟨-, hf, -⟩, K, hKf, hKfin, hK, ⟨e'⟩⟩ := hmodel
    have hCh : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hf hK
    refine ⟨r, K, hKf, hKfin, hCh, hr, ?_, ?_⟩
    · rintro r₀ q' h
      cases h
      rw [hK, TauCeti.PrimePower.card_def, hq2]
    ·
      have hZ1 : Nat.card (center ↥L) = 1 := by
        rcases hZ Y L hL hodd (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩) with h1 | ⟨-, ⟨e6⟩⟩
        · exact h1
        · exfalso
          have h360 : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSp r K)) = 360 := by
            rw [← Nat.card_congr e'.toEquiv, Nat.card_congr e6.toEquiv, nat_card_alternatingGroup]
            simp [Nat.factorial]
          rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hK] at h360
          have hdvd : 2 ^ 4 ∣ 360 := by
            rw [← h360]
            refine Dvd.dvd.mul_right ?_ _
            rw [← pow_mul]
            exact Nat.pow_dvd_pow 2 (by nlinarith)
          norm_num at hdvd
      have hbot : center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
      exact ⟨((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
        hbot.symm)).trans e').trans (LeviBlock.spFlagProjEquiv r K)⟩
  all_goals exact hd.elim

theorem exists_mulEquiv_statedSp_of_idxBTwo (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤) (hodd : Odd (Nat.card (center ↥L)))
    (h : IsLieOf IdxBTwo (↥L ⧸ center ↥L)) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 2 ≤ r ∧ Nat.card K = 2 ∧
      Nonempty (↥L ≃* CFSG.Open.StatedSp r K) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  have hdB : IdxB d := by
    cases d with
    | B r q =>
      have hq2 : q.card = 2 := hd
      have hc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
      have hdvd : q.p ∣ 2 := by
        have h' : q.p ∣ q.p ^ q.exponent :=
          dvd_pow_self q.p (TauCeti.PrimePower.exponent_pos q).ne'
        rwa [← hc, hq2] at h'
      exact ((Nat.Prime.dvd_iff_eq Nat.prime_two q.prime_p.ne_one).mp hdvd).symm
    | _ => exact hd.elim
  obtain ⟨r, K, hKf, hKfin, hCh, hr, hcard, ⟨e'⟩⟩ :=
    exists_mulEquiv_statedSp_of_lie_index hZ hL hodd d hv hdB e
  have hK : Nat.card K = 2 := by
    cases d with
    | B r₀ q => exact (hcard r₀ q rfl).trans hd
    | _ => exact hd.elim
  exact ⟨r, K, hKf, hKfin, hCh, hr, hK, ⟨e'⟩⟩

theorem exists_mulEquiv_statedSp_of_idxBBig (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤) (hodd : Odd (Nat.card (center ↥L)))
    (h : IsLieOf IdxBBig (↥L ⧸ center ↥L)) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 2 ≤ r ∧ 4 ≤ Nat.card K ∧
      Nonempty (↥L ≃* CFSG.Open.StatedSp r K) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  have hdB : IdxB d := by
    cases d with
    | B r q => exact hd.1
    | _ => exact hd.elim
  obtain ⟨r, K, hKf, hKfin, hCh, hr, hcard, ⟨e'⟩⟩ :=
    exists_mulEquiv_statedSp_of_lie_index hZ hL hodd d hv hdB e
  have hK4 : 4 ≤ Nat.card K := by
    cases d with
    | B r₀ q =>
      have hcard' : Nat.card K = q.card := hcard r₀ q rfl
      have hc : q.card = 2 ^ q.exponent := by
        rw [TauCeti.PrimePower.card_def, hd.1]
      have he1 : q.exponent ≠ 1 := by
        intro h1
        exact hd.2 (by rw [hc, h1, pow_one])
      have he2 : 2 ≤ q.exponent := by
        have := (TauCeti.PrimePower.exponent_pos q).ne'
        omega
      rw [hcard', hc]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) he2
    | _ => exact hd.elim
  exact ⟨r, K, hKf, hKfin, hCh, hr, hK4, ⟨e'⟩⟩

@[expose] noncomputable def spFlagLeviTopBlocks {r : ℕ} {K : Type} [Field K] {I : Set ℕ}
    (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) : Fin (r + 1) → Subgroup (StatedSp r K) := by
  classical
  exact fun j =>
    if (j : ℕ) = 0 then (LeviBlock.spFlagResEmb (r := r) (K := K) t).range
    else if hj : (j : ℕ) ∈ I then
      (LeviBlock.spFlagCutEmb (LeviBlock.spFlagPrev I j) j (hI j hj)).range
    else ⊥

theorem spFlagLeviTopBlocks_zero {r : ℕ} {K : Type} [Field K] {I : Set ℕ}
    (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)} (hj0 : (j : ℕ) = 0) :
    spFlagLeviTopBlocks (K := K) hI t j = (LeviBlock.spFlagResEmb (r := r) (K := K) t).range := by
  simp [spFlagLeviTopBlocks, hj0]

theorem spFlagLeviTopBlocks_mem {r : ℕ} {K : Type} [Field K] {I : Set ℕ}
    (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)} (hj0 : (j : ℕ) ≠ 0)
    (hj : (j : ℕ) ∈ I) :
    spFlagLeviTopBlocks (K := K) hI t j =
      (LeviBlock.spFlagCutEmb (LeviBlock.spFlagPrev I j) j (hI j hj)).range := by
  simp [spFlagLeviTopBlocks, hj0, hj]

theorem spFlagLeviTopBlocks_not_mem {r : ℕ} {K : Type} [Field K] {I : Set ℕ}
    (hI : ∀ i ∈ I, i ≤ r) (t : ℕ) {j : Fin (r + 1)} (hj0 : (j : ℕ) ≠ 0)
    (hj : (j : ℕ) ∉ I) : spFlagLeviTopBlocks (K := K) hI t j = ⊥ := by
  simp [spFlagLeviTopBlocks, hj0, hj]

theorem hasLeviCensus_idxBBig (hZ : OddCenterRest) {X : Type} [Group X] [Finite X]
    {L J : Subgroup X} (hCP : CompParab L J) (h : IsLieOf IdxBBig (↥L ⧸ center ↥L)) :
    HasLeviCensus ↥J IsWBlock := by
  obtain ⟨r, K, hKf, hKfin, hCh, hr, hK4, ⟨φ⟩⟩ :=
    exists_mulEquiv_statedSp_of_idxBBig hZ hCP.comp hCP.odd h
  obtain ⟨ρ, I, t, hI, htI, hmax, hcomap⟩ := LeviBlock.exists_flagStabilizer_of_compParab hCP φ
  have hI' : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
  have hI1 : ∀ i ∈ I, 1 ≤ i := fun i hi => (hI i hi).1
  classical
  have hcomm_top : commutator (StatedSp (r - t) K) = ⊤ := by
    rcases Nat.eq_zero_or_pos (r - t) with hm | hm
    · haveI : Subsingleton (StatedSp (r - t) K) := by rw [hm]; infer_instance
      refine eq_top_iff.mpr ?_
      intro x _
      rw [Subsingleton.elim x 1]
      exact one_mem _
    · exact (LeviBlock.spFlag_isQuasisimple_Sp (K := K) hm (Or.inl hK4)).1
  have hcenter_bot : Subgroup.center (StatedSp (r - t) K) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  let β : ↥((J.subgroupOf L).comap ρ.toMonoidHom) →* (Fin (r + 1) → StatedSp r K) :=
    (LeviBlock.spFlagLeviHom hI' htI).comp (MulEquiv.subgroupCongr hcomap).toMonoidHom
  have hrange : β.range = (LeviBlock.spFlagLeviHom hI' htI).range := by
    dsimp only [β]
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (MulEquiv.subgroupCongr hcomap).surjective, Subgroup.map_top]
  have hβ : IsPGroup 2 β.ker := by
    have hker_eq : β.ker = Subgroup.comap (MulEquiv.subgroupCongr hcomap).toMonoidHom
        (LeviBlock.spFlagLeviHom hI' htI).ker := rfl
    rw [hker_eq]
    exact IsPGroup.comap_of_injective (p := 2)
      (LeviBlock.isPGroup_ker_spFlagLeviHom hI' htI hI1)
      (MulEquiv.subgroupCongr hcomap).toMonoidHom (MulEquiv.injective _)
  have hle : Subgroup.pi Set.univ (LeviBlock.spFlagLeviBlock hI' t) ≤ β.range := by
    rw [hrange]
    exact LeviBlock.pi_le_range_spFlagLeviHom hI' htI hmax
  have hn : β.range ≤ normalizer
      (Subgroup.pi Set.univ (LeviBlock.spFlagLeviBlock (K := K) hI' t) :
        Set (Fin (r + 1) → StatedSp r K)) := by
    refine le_normalizer_of_commutator_le hle ?_
    rw [hrange]
    exact LeviBlock.commutator_range_spFlagLeviHom_le hI' htI
  have hpiT : β.range ≤ Subgroup.pi Set.univ (spFlagLeviTopBlocks hI' t) := by
    intro x hx
    rw [Subgroup.mem_pi]
    intro j _
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
    have happ : β y =
        (LeviBlock.spFlagLeviHom hI' htI) ((MulEquiv.subgroupCongr hcomap) y) := rfl
    rw [happ, LeviBlock.spFlagLeviHom, MonoidHom.pi_apply]
    by_cases hj0 : (j : ℕ) = 0
    · rw [spFlagLeviTopBlocks_zero hI' t hj0, LeviBlock.spFlagLeviCoord_of_eq_zero hI' htI hj0,
        MonoidHom.comp_apply]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    · by_cases hj : (j : ℕ) ∈ I
      · rw [spFlagLeviTopBlocks_mem hI' t hj0 hj, LeviBlock.spFlagLeviCoord_of_mem hI' htI hj0 hj,
          MonoidHom.comp_apply]
        exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      · rw [spFlagLeviTopBlocks_not_mem hI' t hj0 hj,
          LeviBlock.spFlagLeviCoord_of_not_mem hI' htI hj0 hj]
        exact one_mem _
  have hodd : ¬ 2 ∣
      (Subgroup.pi Set.univ (LeviBlock.spFlagLeviBlock hI' t)).relIndex β.range := by
    refine not_two_dvd_relIndex_pi (T := spFlagLeviTopBlocks hI' t) ?_ hle hpiT ?_
    · intro j
      by_cases hj0 : (j : ℕ) = 0
      · rw [LeviBlock.spFlagLeviBlock_of_eq_zero hI' hj0, spFlagLeviTopBlocks_zero hI' t hj0]
        exact Subgroup.map_le_range _ _
      · by_cases hj : (j : ℕ) ∈ I
        · rw [LeviBlock.spFlagLeviBlock_of_mem hI' hj0 hj, spFlagLeviTopBlocks_mem hI' t hj0 hj,
            MonoidHom.range_comp]
          exact Subgroup.map_le_range _ _
        · rw [LeviBlock.spFlagLeviBlock_of_not_mem hI' hj0 hj,
            spFlagLeviTopBlocks_not_mem hI' t hj0 hj]
    · intro j
      by_cases hj0 : (j : ℕ) = 0
      · rw [LeviBlock.spFlagLeviBlock_of_eq_zero hI' hj0, spFlagLeviTopBlocks_zero hI' t hj0]
        have hEq : (commutator (StatedSp (r - t) K)).map
            (LeviBlock.spFlagResEmb (r := r) (K := K) t) =
            (LeviBlock.spFlagResEmb (r := r) (K := K) t).range := by
          rw [hcomm_top, Subgroup.map_top]
        rw [hEq, Subgroup.relIndex_self]
        norm_num
      · by_cases hj : (j : ℕ) ∈ I
        · rw [LeviBlock.spFlagLeviBlock_of_mem hI' hj0 hj, spFlagLeviTopBlocks_mem hI' t hj0 hj,
            MonoidHom.range_comp,
            ← Subgroup.map_top (LeviBlock.spFlagCutEmb (LeviBlock.spFlagPrev I j) j (hI' j hj)),
            Subgroup.relIndex_map_map_of_injective _ _
              (LeviBlock.spFlagCutEmb_injective _ _ _),
            Subgroup.relIndex_top_right]
          exact not_two_dvd_index_range_toGL _
        · rw [LeviBlock.spFlagLeviBlock_of_not_mem hI' hj0 hj,
            spFlagLeviTopBlocks_not_mem hI' t hj0 hj, Subgroup.relIndex_self]
          norm_num
  have hS : ∀ j, LeviBlock.spFlagLeviBlock (K := K) hI' t j = ⊥ ∨
      IsWBlock ↥(LeviBlock.spFlagLeviBlock (K := K) hI' t j) := by
    intro j
    by_cases hj0 : (j : ℕ) = 0
    · have h0 : LeviBlock.spFlagLeviBlock hI' t j =
          (commutator (StatedSp (r - t) K)).map
            (LeviBlock.spFlagResEmb (r := r) (K := K) t) :=
        LeviBlock.spFlagLeviBlock_of_eq_zero hI' hj0
      rcases Nat.eq_zero_or_pos (r - t) with hm | hm
      · left
        rw [h0]
        refine Subgroup.eq_bot_of_card_eq _ ?_
        have hcomm : commutator (StatedSp (r - t) K) = ⊥ := by
          rw [hm]
          refine le_bot_iff.mp ?_
          intro x _
          exact Subgroup.mem_bot.mpr (Subsingleton.elim x 1)
        rw [Nat.card_congr (MulEquiv.subgroupCongr h0).symm.toEquiv,
          Nat.card_congr (LeviBlock.spFlagLeviBlockZeroEquiv (K := K) hI' t hj0).toEquiv,
          hcomm, Subgroup.card_bot]
      · right
        rw [h0]
        have hW : IsWBlock (StatedSp (r - t) K) := by
          refine Or.inl ⟨LeviBlock.spFlag_isQuasisimple_Sp hm (Or.inl hK4), ?_⟩
          rw [hcenter_bot, Subgroup.card_bot]
          exact ⟨0, rfl⟩
        have eW : StatedSp (r - t) K ≃*
            ↥((commutator (StatedSp (r - t) K)).map
              (LeviBlock.spFlagResEmb (r := r) (K := K) t)) :=
          ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hcomm_top).symm).trans
            ((LeviBlock.spFlagLeviBlockZeroEquiv (K := K) hI' t hj0).symm.trans
              (MulEquiv.subgroupCongr h0)))
        exact IsWBlock.of_mulEquiv eW hW
    · by_cases hj : (j : ℕ) ∈ I
      · rw [LeviBlock.spFlagLeviBlock_of_mem hI' hj0 hj]
        rcases range_toGL_cases (K := K) (m := (j : ℕ) - LeviBlock.spFlagPrev I j) with
          hbot | ⟨hK2, -, -⟩ | ⟨hq, hoddZ⟩
        · left
          rw [MonoidHom.range_comp, hbot, Subgroup.map_bot]
        · exact absurd hK4 (by omega)
        · right
          rw [MonoidHom.range_comp]
          exact IsWBlock.of_mulEquiv
            (Subgroup.equivMapOfInjective _ _ (LeviBlock.spFlagCutEmb_injective _ _ _))
            (Or.inl ⟨hq, hoddZ⟩)
      · rw [LeviBlock.spFlagLeviBlock_of_not_mem hI' hj0 hj]
        exact Or.inl rfl
  exact hasLeviCensus_of_mulEquiv hCP.parab.1 ρ (G := fun _ => StatedSp r K)
    (S := LeviBlock.spFlagLeviBlock hI' t) (β := β) hβ hle hn hodd hS

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
