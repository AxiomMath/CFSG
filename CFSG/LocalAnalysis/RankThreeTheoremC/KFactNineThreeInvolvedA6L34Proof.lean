module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111SizeMax
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactL34SectionA6Proof
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34ModelS
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111E16
import CFSG.Adapters.LinearCatalogStated
public import CFSG.LocalAnalysis.StandardType.L34SylowOvergroupBase
import CFSG.LocalAnalysis.StandardType.L34SylowOvergroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactInvolved

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasiDihedralFusion Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.I1420

theorem dvd_orderA_one (q : ℕ) : q ∣ orderA 1 q := by
  unfold orderA
  have hI : Finset.Icc 2 (1 + 1) = {2} := by decide
  rw [hI, Finset.prod_singleton, show 1 * (1 + 1) / 2 = 1 by norm_num, pow_one]
  have hg : Nat.gcd (1 + 1) (q - 1) ∣ q ^ 2 - 1 := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp
    · have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        rcases q with _ | q
        · omega
        · simp [Nat.succ_sub_one, pow_two]; ring_nf; omega
      rw [this]
      exact dvd_mul_right _ _
  rw [Nat.mul_div_assoc _ hg]
  exact dvd_mul_right _ _

theorem pow_three_dvd_orderTwistedA_two (q : ℕ) (hq : ¬ 3 ∣ q + 1) :
    q ^ 3 ∣ orderTwistedA 2 q := by
  unfold orderTwistedA
  have hg : Nat.gcd (2 + 1) (q + 1) = 1 := by
    rw [show (2 + 1 : ℕ) = 3 by norm_num]
    exact Nat.coprime_iff_gcd_eq_one.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hq)
  rw [hg, Nat.div_one, show 2 * (2 + 1) / 2 = 3 by norm_num]
  exact dvd_mul_right _ _

theorem pow_three_dvd_orderRee (q : ℕ) : q ^ 3 ∣ orderRee q := by
  unfold orderRee
  exact (dvd_mul_right _ _).mul_right _

theorem not_27_dvd_20160 : ¬ 27 ∣ 20160 := by decide

theorem not_dvd_of_27_dvd {n : ℕ} (h : 27 ∣ n) : ¬ n ∣ 20160 := fun hn =>
  not_27_dvd_20160 (h.trans hn)

theorem card_m11 : Nat.card (TauCeti.CFSGIndex.sporadic .M11).Group = 7920 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M11.tauCeti_finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M11.le_card_native
  rw [Nat.card_congr e.toEquiv] at h2
  exact le_antisymm h1 h2

theorem card_m12 : Nat.card (TauCeti.CFSGIndex.sporadic .M12).Group = 95040 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M12.tauCeti_finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M12.le_card_native
  rw [Nat.card_congr e.toEquiv] at h2
  exact le_antisymm h1 h2

theorem card_j3 :
    Nat.card (TauCeti.CFSGIndex.sporadic .J3).Group = 50232960 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  rw [← Nat.card_congr b.toEquiv]
  exact CFSG.Sporadic.J3.card_J3

@[expose] def IsLTwoEight (K : Type) [Group K] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∧
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)


theorem card_eq {q : TauCeti.PrimePower} {p e : ℕ} (hp : q.p = p) (he : q.exponent = e) :
    q.card = p ^ e := by
  rw [TauCeti.PrimePower.card_def, hp, he]

theorem listThree_of_dvd (hb : LieOrderBridge)
    {K : Type} [Group K] [Finite K] (hK : NineThreeListGroup 3 K) (hd : Nat.card K ∣ 20160) :
    IsAltTwoP 3 K ∨ IsLinThreeFour K ∨ IsLTwoEight K := by
  rcases hK with ⟨i, hi, ⟨e⟩⟩ | ⟨d, hd', ⟨e⟩⟩
  · cases i with
    | cyclic p hp => exact hi.elim
    | alternating n hn =>
      rcases hi with ⟨-, rfl | rfl⟩ | ⟨h, -⟩
      · exact Or.inl ⟨e⟩
      · exfalso
        rw [Nat.card_congr e.toEquiv] at hd
        have h9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
          rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
          decide
        change Nat.card (alternatingGroup (Fin 9)) ∣ 20160 at hd
        rw [h9] at hd
        norm_num at hd
      · omega
    | sporadic s =>
      rcases hi with ⟨-, rfl | rfl | rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exfalso
        rw [Nat.card_congr e.toEquiv, card_m11] at hd
        norm_num at hd
      · exfalso
        rw [Nat.card_congr e.toEquiv, card_m12] at hd
        norm_num at hd
      · exfalso
        rw [Nat.card_congr e.toEquiv, card_j3] at hd
        norm_num at hd
      all_goals omega
    | lie d =>
      have hcard : Nat.card K = lieOrderFormula d.1 := hb d K ⟨e⟩
      rw [hcard] at hd
      obtain ⟨d, hv⟩ := d
      simp only at hd
      rcases hi with ⟨q, hq3, hq2, hdq⟩ | ⟨q, hq3, hdq⟩ | ⟨q, ⟨hq3, hq1, hdq⟩ | ⟨-, hq2, hq1, hdq⟩⟩ |
          ⟨q, hq3, hq1, hdq⟩ | ⟨-, m, hdq⟩ | ⟨-, hspec⟩ | ⟨h, -⟩
      ·
        exfalso
        simp only at hdq
        subst hdq
        have hnd := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hnd
        have hc := card_eq hq3 rfl
        have he3 : 3 ≤ q.exponent := by
          by_contra h
          have h2 : q.exponent = 2 := by omega
          rw [h2] at hc
          exact hnd (Or.inl ⟨rfl, Or.inr (Or.inr (by rw [hc]; norm_num))⟩)
        apply not_dvd_of_27_dvd _ hd
        change 27 ∣ orderA 1 q.card
        refine dvd_trans ?_ (dvd_orderA_one _)
        rw [hc]
        exact (Nat.pow_dvd_pow 3 he3)
      ·
        exfalso
        simp only at hdq
        subst hdq
        have hc := card_eq hq3 rfl
        have h3q : 3 ∣ q.card := by
          rw [hc]
          exact dvd_pow_self 3 q.exponent_pos.ne'
        apply not_dvd_of_27_dvd _ hd
        change 27 ∣ orderTwistedA 2 q.card
        refine dvd_trans ?_ (pow_three_dvd_orderTwistedA_two _ ?_)
        · exact pow_dvd_pow_of_dvd h3q 3
        · intro h
          have := (Nat.dvd_add_right h3q).mp h
          norm_num at this
      ·
        exfalso
        simp only at hdq
        subst hdq
        have hnd := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hnd
        exact hnd ⟨rfl, by rw [card_eq hq3 hq1]; norm_num⟩
      ·
        exfalso
        simp only at hdq
        subst hdq
        change orderTwistedA 3 q.card ∣ 20160 at hd
        rw [card_eq hq2 hq1] at hd
        revert hd
        decide
      ·
        exfalso
        simp only at hdq
        subst hdq
        change orderA 2 q.card ∣ 20160 at hd
        rw [card_eq hq3 hq1] at hd
        revert hd
        decide
      ·
        exfalso
        simp only at hdq
        subst hdq
        apply not_dvd_of_27_dvd _ hd
        change 27 ∣ orderRee (3 ^ (2 * m + 1))
        refine dvd_trans ?_ (pow_three_dvd_orderRee _)
        exact pow_dvd_pow_of_dvd (dvd_pow_self 3 (by omega)) 3
      · rcases hspec with ⟨q, hq2, hq3, hdq | hdq | hdq⟩ | ⟨q, hq2, hq3, hdq⟩ |
          ⟨q, hq2, hq1, hdq⟩ | hdq
        · exact Or.inr (Or.inr ⟨⟨_, hv⟩, ⟨q, hq2, hq3, hdq⟩, ⟨e⟩⟩)
        · exfalso
          simp only at hdq
          subst hdq
          change orderG2 q.card ∣ 20160 at hd
          rw [card_eq hq2 hq3] at hd
          revert hd
          decide
        · exfalso
          simp only at hdq
          subst hdq
          change orderBC 2 q.card ∣ 20160 at hd
          rw [card_eq hq2 hq3] at hd
          revert hd
          decide
        · exact Or.inr (Or.inl ⟨⟨_, hv⟩, ⟨q, hq2, hq3, hdq⟩, ⟨e⟩⟩)
        · exfalso
          simp only at hdq
          subst hdq
          change orderBC 3 q.card ∣ 20160 at hd
          rw [card_eq hq2 hq1] at hd
          revert hd
          decide
        · exfalso
          simp only at hdq
          subst hdq
          change orderTits ∣ 20160 at hd
          revert hd
          decide
      · omega
  · rcases hd' with ⟨-, q, hq2, hq3, hdq⟩ | ⟨h, -⟩
    · exfalso
      haveI : Finite (TauCeti.CFSGIndex.lie d).Group :=
        Finite.of_injective (fun x => e.symm (x, 1)) fun a b h => by
          have := congrArg Prod.fst (e.symm.injective h)
          simpa using this
      have h1 := hb d (TauCeti.CFSGIndex.lie d).Group ⟨MulEquiv.refl _⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, h1] at hd
      obtain ⟨d, hv⟩ := d
      simp only at hdq hd
      subst hdq
      change orderA 1 q.card * orderA 1 q.card ∣ 20160 at hd
      rw [card_eq hq2 hq3] at hd
      revert hd
      decide
    · omega

theorem not_isSolvable_of_simple_of_card_504 {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (h : Nat.card K = 504) : ¬ Group.IsSolvable K := by
  intro hsol
  rcases (commutator K).normal_of_characteristic.eq_bot_or_eq_top with hc | hc
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [h]; norm_num)
    have hcomm : ∀ a b : K, a * b = b * a := by
      intro a b
      have hab : a * b * a⁻¹ * b⁻¹ ∈ commutator K := by
        rw [commutator_def]
        have := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rwa [commutatorElement_def] at this
      rw [hc, Subgroup.mem_bot] at hab
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [hab, one_mul]
    have hn : (Subgroup.zpowers g).Normal := ⟨fun x hx k => by
      rw [show k * x * k⁻¹ = x by rw [hcomm k x]; group]; exact hx⟩
    rcases hn.eq_bot_or_eq_top with hb | ht
    · have : g = 1 := by
        rw [← Subgroup.mem_bot, ← hb]; exact Subgroup.mem_zpowers g
      rw [this, orderOf_one] at hg
      norm_num at hg
    · have := Nat.card_zpowers g
      rw [ht, Subgroup.card_top, h, hg] at this
      norm_num at this
  · haveI : Group.IsPerfect K := ⟨hc⟩
    haveI : Nontrivial K := IsSimpleGroup.toNontrivial
    exact Group.IsPerfect.not_isSolvable K hsol

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactInvolved

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasiDihedralFusion Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactInvolved CFSG.LocalAnalysis.RankThreeTheoremC.KFactL34Sec
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.I1420

theorem kFactNineThreeInvolvedA6L34_of (hb : LieOrderBridge) :
    KFactNineThreeInvolvedA6L34 := by
  intro A K _ _ _ hA hK hAK
  classical
  obtain ⟨U, φ, hφ⟩ := hAK
  haveI : Finite K := Finite.of_surjective φ hφ
  have hKU : Nat.card K ∣ Nat.card U := Subgroup.card_dvd_of_surjective hφ
  have hUA : Nat.card U ∣ Nat.card A := Subgroup.card_subgroup_dvd_card U
  have hcardS : Nat.card ↥CFSG.ComponentClassification.PSL3Four.S = 20160 := by
    rw [← CFSG.StandardType.L34Sylow.closureTabs_gensS]
    exact CFSG.StandardType.L34Sylow.overgroupFacts.card_S
  have hA20160 : Nat.card A ∣ 20160 := by
    rcases hA with hA6 | hL
    · obtain ⟨e⟩ := hA6
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (alternatingGroup (Fin 6)) ∣ 20160
      rw [card_alternatingGroup_six]
      norm_num
    · obtain ⟨e⟩ := KFactProofs.L34ModelS.nonempty_mulEquiv_S_of_isLinThreeFour hL
      rw [Nat.card_congr e.toEquiv, hcardS]
  rcases listThree_of_dvd hb hK ((hKU.trans hUA).trans hA20160) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    obtain ⟨⟨d, hv⟩, ⟨q, hq2, hq3, hdq⟩, ⟨eK⟩⟩ := h
    simp only at hdq
    subst hdq
    have hK504 : Nat.card K = 504 := by
      rw [hb ⟨_, hv⟩ K ⟨eK⟩]
      change orderA 1 q.card = 504
      rw [card_eq hq2 hq3]
      decide
    haveI : IsSimpleGroup K :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity K _ _ _
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv eK)).2
    have hKns := not_isSolvable_of_simple_of_card_504 hK504
    have h504U : 504 ∣ Nat.card U := hK504 ▸ hKU
    rcases hA with hA6 | hL
    ·
      obtain ⟨eA⟩ := hA6
      have h360 : Nat.card A = 360 := by
        rw [Nat.card_congr eA.toEquiv]
        exact card_alternatingGroup_six
      have := h504U.trans hUA
      rw [h360] at this
      norm_num at this
    · obtain ⟨e⟩ := KFactProofs.L34ModelS.nonempty_mulEquiv_S_of_isLinThreeFour hL
      haveI : IsSimpleGroup A := isSimpleGroup_of_isLinThreeFour' hL
      by_cases hU : U = ⊤
      · subst hU
        haveI : IsSimpleGroup ↥(⊤ : Subgroup A) := Subgroup.topEquiv.isSimpleGroup
        rcases (φ.normal_ker).eq_bot_or_eq_top with hk | hk
        · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hk
          have h1 : Nat.card K = Nat.card A := by
            rw [← Nat.card_congr (MulEquiv.ofBijective φ ⟨hinj, hφ⟩).toEquiv, Subgroup.card_top]
          rw [hK504, Nat.card_congr e.toEquiv, hcardS] at h1
          norm_num at h1
        · have hsub : Subsingleton K := by
            refine ⟨fun a b => ?_⟩
            obtain ⟨u, rfl⟩ := hφ a
            obtain ⟨v, rfl⟩ := hφ b
            have hu : u ∈ φ.ker := by rw [hk]; exact mem_top u
            have hv' : v ∈ φ.ker := by rw [hk]; exact mem_top v
            rw [MonoidHom.mem_ker.mp hu, MonoidHom.mem_ker.mp hv']
          have := Finite.card_le_one_iff_subsingleton.mpr hsub
          omega
      · set U' : Subgroup ↥CFSG.ComponentClassification.PSL3Four.S := U.map e.toMonoidHom
          with hU'
        have eU : ↥U ≃* ↥U' := U.equivMapOfInjective e.toMonoidHom e.injective
        have hU'ne : U' ≠ ⊤ := by
          intro h
          apply hU
          rw [eq_top_iff]
          intro x _
          have hx : e x ∈ U' := by rw [h]; exact mem_top _
          obtain ⟨y, hy, hyx⟩ := hx
          have : y = x := e.injective hyx
          rwa [← this]
        have hidx : ¬ 3 ∣ U'.index := by
          have h := Subgroup.card_mul_index U'
          rw [hcardS, ← Nat.card_congr eU.toEquiv] at h
          obtain ⟨c, hc⟩ := h504U
          intro h3
          obtain ⟨d, hd⟩ := h3
          rw [hc, hd] at h
          have h1512 : 1512 ∣ 20160 := ⟨c * d, by rw [← h]; ring⟩
          norm_num at h1512
        rcases solvable_or_aSix_of_not_dvd_index hU'ne hidx with hsol | ha6
        · have hUs : Group.IsSolvable ↥U :=
            solvable_of_solvable_injective (f := eU.toMonoidHom) eU.injective
          exact hKns (solvable_of_surjective hφ)
        · obtain ⟨a6⟩ := ha6
          have hU360 : Nat.card U = 360 := by
            rw [Nat.card_congr (eU.trans a6).toEquiv, card_alternatingGroup_six]
          rw [hU360] at h504U
          norm_num at h504U

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
