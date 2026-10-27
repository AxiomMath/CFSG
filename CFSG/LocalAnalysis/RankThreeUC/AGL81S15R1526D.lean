module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0a
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open scoped commutatorElement

section LiftFacts

variable {X : Type} [Group X] [Finite X]

theorem barO2_isLThree_of_lift_aux_center {S : Type} [Group S] (h : IsLThreeOfExp 1 S) :
    Subgroup.center S = ⊥ := by
  have hc := card_eq_of_isLThreeOfExp_one h
  have hs := isSimpleGroup_of_isLThreeOfExp_one h
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h0 | h1
  · exact h0
  · exfalso
    have hcomm : ∀ x y : S, x * y = y * x := fun x y =>
      Subgroup.mem_center_iff.mp (by rw [h1]; exact Subgroup.mem_top y) x
    let _ : CommGroup S := { ‹Group S› with mul_comm := hcomm }
    have hp := (CommGroup.is_simple_iff_prime_card (α := S)).1 hs
    rw [hc] at hp
    norm_num at hp

theorem barO2_isLThree_of_lift (hKSML3 : KSML3) {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls)
    (h3 : IsLThreeOfExp 1 ↥Ls) :
    IsLThreeOfExp 1 ↥(barO2 L) ∧ Nat.card (Subgroup.center ↥(barO2 L)) = 1 := by
  obtain ⟨f, hf, hker⟩ := barO2_centralExt hX hLs hL
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs hL
  have hZs := barO2_isLThree_of_lift_aux_center h3
  rcases h3 with ⟨-, d, q, hq, hd, ⟨e⟩⟩ | ⟨h2, -⟩
  · let eK : (↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) ≃* (TauCeti.CFSGIndex.lie d).Group :=
      (eQ.trans ((QuotientGroup.quotientMulEquivOfEq hZs).trans QuotientGroup.quotientBot)).trans e
    have hcard : Nat.card (Subgroup.center ↥(barO2 L)) = 1 :=
      (hKSML3 ↥(barO2 L) hL.1.component.2.2 d ⟨eK⟩ (centre_barO2_odd hL.1)).1
        (Or.inr ⟨q, hq, hd⟩)
    have hbot : Subgroup.center ↥(barO2 L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
    have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans hbot.le
    exact ⟨Or.inl ⟨rfl, d, q, hq, hd, ⟨(MulEquiv.ofBijective f ⟨hinj, hf⟩).trans e⟩⟩, hcard⟩
  · omega

theorem eq_one_of_mem_inf_of_pPow {L I : Subgroup X} (hL : IsC2 L)
    (hZ : Nat.card (Subgroup.center ↥(barO2 L)) = 1) (hI : I ≤ cMHat L) :
    ∀ x ∈ L ⊓ I, (∃ k : ℕ, orderOf x = 3 ^ k) → x = 1 := by
  have _ := hL
  rintro x ⟨hxL, hxI⟩ ⟨k, hk⟩
  have hc : ∀ b ∈ barO2 L, b * QuotientGroup.mk' (CFSG.pCore 2 X) x =
      QuotientGroup.mk' (CFSG.pCore 2 X) x * b := fun b hb =>
    Subgroup.mem_centralizer_iff.1 (hI hxI) b hb
  have hz : (⟨QuotientGroup.mk' (CFSG.pCore 2 X) x, x, hxL, rfl⟩ : ↥(barO2 L)) ∈
      Subgroup.center ↥(barO2 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  rw [Subgroup.eq_bot_of_card_eq _ hZ, Subgroup.mem_bot] at hz
  have hx2 : x ∈ CFSG.pCore 2 X :=
    (QuotientGroup.eq_one_iff x).1 (congrArg Subtype.val hz)
  obtain ⟨j, hj⟩ := pRank_barO2_eq_aux_powTwo hx2
  have hdvd : 3 ^ k ∣ 2 ^ j := hk ▸ orderOf_dvd_of_pow_eq_one hj
  have hcop : Nat.Coprime (3 ^ k) (2 ^ j) := Nat.Coprime.pow k j (by norm_num)
  have h1 : 3 ^ k = 1 := hcop.eq_one_of_dvd hdvd
  exact orderOf_eq_one_iff.1 (hk.trans h1)

end LiftFacts

section UOfProps

theorem uOf_props {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    {L : Subgroup X} (hL : L ∈ CY T T₁ T₂) :
    ⁅L, gnV T⁆ ≠ ⊥ ∧ ⁅L, gnV T⁆ ≤ T := by
  obtain ⟨Ls, hLs, hLift⟩ := hL
  refine ⟨fun hbot => ?_, ?_⟩
  · have hle : L ≤ gnC T := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    have hLsbot : Ls = ⊥ := by
      rw [← hLift.2, eq_bot_iff]
      rintro _ ⟨l, hl, rfl⟩
      exact (QuotientGroup.eq_one_iff l).2 (hle hl)
    have h1 : Subsingleton ↥Ls := by
      rw [hLsbot]
      infer_instance
    have h4 : Subsingleton (↥Ls ⧸ Subgroup.center ↥Ls) := ⟨fun a b => by
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      rw [Subsingleton.elim a' b']⟩
    have hs : IsSimpleGroup (↥Ls ⧸ Subgroup.center ↥Ls) := hLs.1.2.2.2
    obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  · haveI : (gnV T).Normal := Subgroup.normalClosure_normal
    exact (Subgroup.commutator_le_right L (gnV T)).trans
      ((gnV_le_pCore hX).trans (pCore_le_gnC_aux1 hX.sylow))

end UOfProps

section RankBound

variable {X : Type} [Group X] [Finite X]

theorem pRank_three_le_two_of_le_cMHat {L I : Subgroup X} (hL : IsC2 L)
    (h3 : IsLThreeOfExp 1 ↥(barO2 L)) (hZ : Nat.card (Subgroup.center ↥(barO2 L)) = 1)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) (hI : I ≤ cMHat L) :
    CFSG.Open.pRank 3 I ≤ 2 := by
  have hq : Nat.Prime 3 := Nat.prime_three
  have hq2 : (3 : ℕ) ≠ 2 := by norm_num
  have hc : ∀ a ∈ barO2 I, ∀ b ∈ barO2 L, a * b = b * a := by
    rintro _ ⟨i, hi, rfl⟩ b hb
    exact (Subgroup.mem_centralizer_iff.1 (hI hi) b hb).symm
  have key := pRank_add_le_pRank_sup_add_pRank_inf hc hq
  have hinf : barO2 I ⊓ barO2 L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.2⟩ : ↥(barO2 L)) ∈ Subgroup.center ↥(barO2 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc x hx.1 g g.2).symm
    rw [Subgroup.eq_bot_of_card_eq _ hZ, Subgroup.mem_bot] at hz
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)
  have hbot : CFSG.Open.pRank 3 (barO2 I ⊓ barO2 L) = 0 := by
    rw [hinf]
    exact pRank_eq_zero_of_not_dvd_s15 hq (by rw [Subgroup.card_bot]; norm_num)
  have hsup : CFSG.Open.pRank 3 (barO2 I ⊔ barO2 L) ≤ 3 := by
    have e : barO2 I ⊔ barO2 L = barO2 (I ⊔ L) := (Subgroup.map_sup _ _ _).symm
    rw [e, ← pRank_barO2_eq_aux_eq (I ⊔ L) hq hq2]
    exact (CFSG.SectionRank.pRank_mono hq.one_lt le_top).trans hX3
  have hL1 : CFSG.Open.pRank 3 (barO2 L) = 1 :=
    (pRank_barO2_eq hL hq hq2).symm.trans (pRank_eq_one_of_isLThree hL h3).1
  rw [← pRank_barO2_eq_aux_eq I hq hq2] at key
  omega

end RankBound

end CFSG.LocalAnalysis.RankThreeUC.S15
