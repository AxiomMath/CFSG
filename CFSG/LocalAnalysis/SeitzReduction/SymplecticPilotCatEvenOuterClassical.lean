module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatEvenOuter
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2EvenOuterOmega

public noncomputable section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.SeitzReduction.RankOne (SpFixedRankOrNoPComponent)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)

theorem two_pow_eight_dvd_card_of_lieModel_PSp {D : Type} [Group D] {m f : ℕ}
    (h : LieModel D .PSp m 2 f) : 2 ^ 8 ∣ Nat.card D := by
  obtain ⟨hf, hm, h22⟩ := admissible_of_lieModel_PSp h
  rw [card_of_lieModel_PSp_two_pow h]
  refine (Nat.pow_dvd_pow 2 ?_).trans (ordBC_two_pow_bounds hf).1
  rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
  · have hf2 : 2 ≤ f := by
      by_contra h1
      obtain rfl : f = 1 := by omega
      exact h22 rfl
    omega
  · have h9 : 9 ≤ m * m := Nat.mul_le_mul hm3 hm3
    have hle : m * m ≤ f * (m * m) := Nat.le_mul_of_pos_left _ hf
    omega

theorem isPComponent_of_isComponent_lieModel_PSp_two {X : Type} [Group X] [Finite X]
    {D : Subgroup X} (hD : IsComponent D) {m f : ℕ} (hDm : LieModel D .PSp m 2 f) :
    IsPComponent 2 D := by
  refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hD fun hle => ?_
  have h2 : 2 ∣ Nat.card (pPrimeCore 2 X) :=
    ((dvd_pow_self 2 (by norm_num : (8 : ℕ) ≠ 0)).trans
      (two_pow_eight_dvd_card_of_lieModel_PSp hDm)).trans (Subgroup.card_dvd_of_le hle)
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)

theorem false_of_lieModel_ne_PSp {m : ℕ} (hdet : Sp2mEvenTypeDetClassical m) {D : Type}
    [Group D] {f : ℕ} (hDm : LieModel D .PSp m 2 f) {t : StatedLieTag} {n e : ℕ}
    (ht : t ∈ classicalTags ∨ t = .twistedB2) (htp : t ≠ .PSp)
    (hadm : StatedLieAdmissible t n 2 e) (hm : LieModel D t n 2 e) : False :=
  htp (hdet D f t n e ht hDm hadm hm).1

theorem sp2m_of_isComponent_statedSp {m : ℕ} (hdet : Sp2mEvenTypeDetClassical m) {X : Type}
    [Group X] [Finite X] {k : Type} [Field k] [Finite k] {g r : ℕ} (hk : Nat.card k = 2 ^ g)
    (hr : 1 ≤ r) (Φ : X ≃* StatedSp r k) {D : Subgroup X} (hD : IsComponent D) {f : ℕ}
    (hDm : LieModel D .PSp m 2 f) : r = m ∧ g = f ∧ LieModel X .PSp m 2 f := by
  have hg : 1 ≤ g := by
    by_contra h0
    have hk1 : Nat.card k = 1 := by rw [hk, show g = 0 by omega, pow_zero]
    exact absurd hk1 (ne_of_gt Finite.one_lt_card)
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hk
  have hcardX : Nat.card X = Nat.card k ^ (r ^ 2) *
      ∏ j ∈ Finset.Icc 1 r, (Nat.card k ^ (2 * j) - 1) := by
    rw [Nat.card_congr Φ.toEquiv]
    exact LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp r
  have h28 : 2 ^ 8 ∣ Nat.card X :=
    (two_pow_eight_dvd_card_of_lieModel_PSp hDm).trans (Subgroup.card_subgroup_dvd_card D)
  have hsmall : ¬ (g = 1 ∧ r ≤ 2) := by
    rintro ⟨rfl, hr2⟩
    rw [hcardX, hk, pow_one] at h28
    rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
    · exact absurd h28 (by decide)
    · exact absurd h28 (by decide)
  obtain ⟨t, r', hr', hX, hadm, hm, ht⟩ : ∃ (t : StatedLieTag) (r' : ℕ), 1 ≤ r' ∧
      IsSimpleGroup X ∧ StatedLieAdmissible t r' 2 g ∧ LieModel X t r' 2 g ∧
        (t = .PSp → r' = r) := by
    rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
    · have hg2 : 2 ≤ g := by omega
      obtain ⟨e₂⟩ := RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := k)
      have h4 : 4 ≤ 2 ^ g :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hadm : StatedLieAdmissible .PSL 2 2 g := ⟨Nat.prime_two, hg, le_rfl,
        fun h => by rw [Prod.mk.injEq] at h; omega,
        fun h => by rw [Prod.mk.injEq] at h; omega⟩
      have hstated : StatedClassicalModel X .PSL 2 2 g :=
        ⟨hadm, k, inferInstance, inferInstance, hk,
          ⟨(Φ.trans (ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k).symm).trans
            e₂⟩⟩
      exact ⟨.PSL, 2, by norm_num, (LieType.Simplicity.fam_PSL_simplicity X 2 2 g hstated).2, hadm,
        Or.inl ⟨by decide, hstated⟩, fun h => absurd h (by decide)⟩
    · have hcond : (Infinite k ∨ 4 ≤ Nat.card k) ∨ (Nat.card k = 3 ∧ 2 ≤ r) ∨
          (Nat.card k = 2 ∧ 3 ≤ r) := by
        rcases (by omega : g = 1 ∨ 2 ≤ g) with rfl | hg2
        · exact Or.inr (Or.inr ⟨by rw [hk, pow_one], by omega⟩)
        · refine Or.inl (Or.inr ?_)
          rw [hk]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
      have hS := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r (by omega) hcond
      obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
        small_standard_source_even_simple_symplectic_parameters_stated (X := StatedSp r k) hk
          (by omega) ⟨MulEquiv.refl _⟩
      have hadm : StatedLieAdmissible .PSp r 2 g := ⟨Nat.prime_two, hg, hr2, fun h => by
        rw [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact hsmall ⟨Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm), le_rfl⟩⟩
      exact ⟨.PSp, r, by omega, (Φ.trans eProj.symm).isSimpleGroup, hadm,
        Or.inl ⟨by decide, hadm, k, inferInstance, inferInstance, hk, ⟨Φ.trans eProj.symm⟩⟩,
        fun _ => rfl⟩
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* X := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  obtain ⟨htt, hrm, hgf⟩ := hdet D f t r' g (F4Pilot.classicalOrSuzukiTag_of_admissible hadm hr')
    hDm hadm (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hm)
  have hrr := ht htt
  subst htt
  exact ⟨hrr ▸ hrm, hgf, LieType.CurtisTits.lieModel_of_mulEquiv eD hDm⟩

theorem sp2m_of_spFixedRankOrNoPComponent {m : ℕ} (hdet : Sp2mEvenTypeDetClassical m)
    {X : Type} [Group X] [Finite X] {g : ℕ} {R : ℕ → Prop} (h : SpFixedRankOrNoPComponent X g R)
    {D : Subgroup X} (hD : IsComponent D) {f : ℕ} (hDm : LieModel D .PSp m 2 f) :
    R m ∧ g = f ∧ LieModel X .PSp m 2 f := by
  rcases h with ⟨k, _, _, r, hk, hr, hR, ⟨Φ⟩⟩ | h
  · obtain ⟨rfl, rfl, hX⟩ := sp2m_of_isComponent_statedSp hdet hk hr Φ hD hDm
    exact ⟨hR, rfl, hX⟩
  · exact (h D (isPComponent_of_isComponent_lieModel_PSp_two hD hDm)).elim

theorem sp2mOvergroupType_two_iff {S : Type} [Group S] {f : ℕ} :
    Sp2mOvergroupType S 2 f ↔
      LieModel S .PSp 2 2 (2 * f) ∨ LieModel S .PSL 4 2 f ∨ LieModel S .PSU 4 2 f ∨
        LieModel S .PSL 5 2 f ∨ LieModel S .PSU 5 2 f := by
  have hO : ∀ {t : StatedLieTag}, (t = .POmegaPlus ∨ t = .POmegaMinus) →
      ¬ LieModel S t (2 + 1) 2 f := fun ht h => by
    have h4 : 4 ≤ 2 + 1 := by
      rcases ht with rfl | rfl <;> exact (F4Pilot.statedLieAdmissible_of_lieModel h).2.2
    omega
  constructor
  · rintro (h | h | h | h | h | h | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
    · exact (hO (.inl rfl) h).elim
    · exact (hO (.inr rfl) h).elim
  · rintro (h | h | h | h | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr (.inl h))))

section Symplectic

open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem psp_outer_fixed_sp2m {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSp n 2 e) (hm : LieModel J .PSp n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (e / 2) ∧ e = 2 * (e / 2) ∧
        Nonempty (fixedSubgroup α ≃* StatedSp n k)) ∨
      (IsSimpleGroup (fixedSubgroup α) ∧ StatedLieAdmissible .twistedB2 0 2 e ∧
        LieModel (fixedSubgroup α) .twistedB2 0 2 e) := by
  obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel hadm hm
  have hf : 1 ≤ e := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hnf : (n, 2 ^ e) ≠ (2, 2) := hadm.2.2.2
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  have : Finite J := Finite.of_equiv _ eJ.symm.toEquiv
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβ2 : MulAut.congr eJ α * MulAut.congr eJ α = 1 := by
    rw [← sq, ← hβ, pow_orderOf_eq_one]
  have hβo : MulAut.congr eJ α ∉ inner (StatedProj (StatedSp n K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  let Ψ := fixedSubgroupCongrEquiv eJ α
  have hE : MulAut.congr eJ α ∈ spSemilinearAutGroup n K →
      ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (e / 2) ∧ e = 2 * (e / 2) ∧
        Nonempty (fixedSubgroup α ≃* StatedSp n k) := by
    intro hmem
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut hmem
    have hσ : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hgσ
      exact hβo (hgσ ▸ spInner_mem_inner g)
    obtain ⟨k, _, _, hk, he2, ⟨Φ⟩⟩ := F4Pilot.psp_field_fixed hn hf hK hβ2 g σ hgσ hσ
    exact ⟨k, inferInstance, inferInstance, hk, he2, ⟨Ψ.trans Φ⟩⟩
  by_cases hn3 : 3 ≤ n
  · left
    apply hE
    rw [(SymplecticHigher.automorphism_generation (K := K) hn3).1]
    exact mem_top _
  · obtain rfl : n = 2 := by omega
    obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ := even_symplectic_two_exterior_square_automorphism hf hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, hodd⟩ := hall γ hγ
    rcases Nat.even_or_odd e with hfe | hfo
    · exact Or.inl (hE (heven hfe _ hβ))
    · obtain ⟨s, hs⟩ := hodd hfo _ hβ hβo
      obtain ⟨m, rfl⟩ := hfo
      have hm : 1 ≤ m := by
        by_contra h0
        obtain rfl : m = 0 := by omega
        exact hnf rfl
      rw [eq_exceptionalAut hγ] at hs
      obtain ⟨hS, hadmB, hLie⟩ := LinearPilot.psp_suzuki_fixed hm hK hβ2 s hs
      exact Or.inr ⟨Ψ.isSimpleGroup, hadmB, LieType.CurtisTits.lieModel_of_mulEquiv Ψ.symm hLie⟩

end Symplectic

section Families

variable {m : ℕ}

theorem catSp2mEvenOuterFamily_PSL (hdet : Sp2mEvenTypeDetClassical m) :
    CatSp2mEvenOuterFamily .PSL m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm
  have hP := isPComponent_of_isComponent_lieModel_PSp_two hD hDm
  rcases RankOne.psl_outer_fixed_rank hadm hmS σ hσ hout with h | h | h
  · obtain ⟨hadm', hm', -⟩ := h D hP
    exact (false_of_lieModel_ne_PSp hdet hDm (Or.inl (by decide)) (by decide) hadm' hm').elim
  · obtain ⟨hadm', hm'⟩ := h D hP
    exact (false_of_lieModel_ne_PSp hdet hDm (Or.inl (by decide)) (by decide) hadm' hm').elim
  · obtain ⟨⟨-, hn⟩, rfl, hfix⟩ := sp2m_of_spFixedRankOrNoPComponent hdet h hD hDm
    refine ⟨?_, hfix⟩
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl hmS)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hmS)))

theorem catSp2mEvenOuterFamily_PSU (hdet : Sp2mEvenTypeDetClassical m) :
    CatSp2mEvenOuterFamily .PSU m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm
  obtain ⟨hn, rfl, hfix⟩ := sp2m_of_spFixedRankOrNoPComponent hdet
    (RankOne.psu_outer_fixed_rank hadm hmS σ hσ hout) hD hDm
  refine ⟨?_, hfix⟩
  rcases hn with rfl | rfl
  · exact Or.inr (Or.inr (Or.inl hmS))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmS))))

theorem catSp2mEvenOuterFamily_PSp
    (hdet : Sp2mEvenTypeDetClassical m) : CatSp2mEvenOuterFamily .PSp m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm
  rcases psp_outer_fixed_sp2m hadm hmS σ hσ hout with
    ⟨k, _, _, hk, he, ⟨Φ⟩⟩ | ⟨hS, hadmB, hLie⟩
  · obtain ⟨rfl, hef, hfix⟩ :=
      sp2m_of_isComponent_statedSp hdet hk (by have := hadm.2.2.1; omega) Φ hD hDm
    refine ⟨Or.inl ?_, hfix⟩
    rw [hef] at he
    rw [← he]
    exact hmS
  · have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
    let eD : D ≃* fixedSubgroup σ := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
    exact (false_of_lieModel_ne_PSp hdet hDm (Or.inr rfl) (by decide) hadmB
      (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLie)).elim

theorem catSp2mEvenOuterFamily_POmega {τ : StatedLieTag}
    (hτ : τ = .POmegaPlus ∨ τ = .POmegaMinus) (hdet : Sp2mEvenTypeDetClassical m) :
    CatSp2mEvenOuterFamily τ m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout f D hD hDm
  have hn : 4 ≤ n := by rcases hτ with rfl | rfl <;> exact hadm.2.2
  rcases RankOne.omega_family_fixed_rank hτ hadm hmS σ hσ hout with h | h
  · obtain ⟨hr, rfl, hfix⟩ := sp2m_of_spFixedRankOrNoPComponent hdet h hD hDm
    obtain rfl : n = m + 1 := by omega
    refine ⟨?_, hfix⟩
    rcases hτ with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmS)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmS)))))
  · obtain ⟨t', n', f', ht', hadm', hm'⟩ :=
      h D (isPComponent_of_isComponent_lieModel_PSp_two hD hDm)
    exact (false_of_lieModel_ne_PSp hdet hDm (Or.inl (by rcases ht' with rfl | rfl <;> decide))
      (by rcases ht' with rfl | rfl <;> decide) hadm' hm').elim

theorem catSp2mEvenOuterFamily_classical (m : ℕ) :
    CatSp2mEvenOuterFamily .PSL m ∧ CatSp2mEvenOuterFamily .PSU m ∧
      CatSp2mEvenOuterFamily .PSp m ∧ CatSp2mEvenOuterFamily .POmegaPlus m ∧
        CatSp2mEvenOuterFamily .POmegaMinus m :=
  ⟨catSp2mEvenOuterFamily_PSL (sp2mEvenTypeDetClassical m),
    catSp2mEvenOuterFamily_PSU (sp2mEvenTypeDetClassical m),
    catSp2mEvenOuterFamily_PSp (sp2mEvenTypeDetClassical m),
    catSp2mEvenOuterFamily_POmega (Or.inl rfl) (sp2mEvenTypeDetClassical m),
    catSp2mEvenOuterFamily_POmega (Or.inr rfl) (sp2mEvenTypeDetClassical m)⟩

end Families

end CFSG.SeitzReduction.SymplecticPilot
