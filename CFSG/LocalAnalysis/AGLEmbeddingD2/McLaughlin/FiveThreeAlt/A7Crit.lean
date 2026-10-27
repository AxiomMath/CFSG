module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.U33Crit
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Final
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Smith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridge
public import CFSG.HardMathSupport.Cooperstein.Proving.EvenWeightCard
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeAbstract
public import CFSG.Quasithin.EmptyFaithful.S153EB6D

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

theorem card_altHeart_seven : Nat.card (altHeart 7) = 2 ^ 6 := by
  have hbot : evenWeightOnes 7 = ⊥ := by
    rw [eq_bot_iff]
    rintro x hx
    rw [evenWeightOnes, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_zmultiples_iff] at hx
    obtain ⟨k, hk⟩ := hx
    have hsum := x.2
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply] at hsum
    rw [← hk] at hsum
    simp only [allOnes, Pi.smul_apply, zsmul_eq_mul, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have h7 : ((7 : ℕ) : ZMod 2) = 1 := rfl
    rw [h7, one_mul] at hsum
    rw [AddSubgroup.mem_bot]
    apply Subtype.ext
    rw [← hk]
    funext i
    simp [allOnes, zsmul_eq_mul, hsum]
  have hc1 : Nat.card ↥(evenWeightOnes 7) = 1 := by rw [hbot, AddSubgroup.card_bot]
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (evenWeightOnes 7)
  rw [hc1, mul_one, CFSG.HardMathSupport.Cooperstein.Proving.card_evenWeight 7 (by norm_num)] at h1
  exact h1.symm

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commV_eq_top_of_irr {G : Subgroup (MulAut V)} (hG1 : G ≠ ⊥)
    (hirr : ∀ J : Subgroup V, (∀ g ∈ G, ∀ v ∈ J, g v ∈ J) → J = ⊥ ∨ J = ⊤) : commV G = ⊤ := by
  rcases hirr (commV G) (fun g hg v hv => apply_mem_commV hg hv) with h | h
  · exfalso
    apply hG1
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun v => ?_
    have h1 : g v * v⁻¹ ∈ commV G := apply_mul_inv_mem_commV hg v
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  · exact h

theorem card_mul_card_fixV_le_of_qOf (hV : ∀ v : V, v ^ 2 = 1) {G B : Subgroup (MulAut V)}
    (hBG : B ≤ G) (hB1 : B ≠ ⊥) (hBe : IsElemAbelian2 B) (hBq : IsQuadratic B)
    (hq : qOf G = ((1 : ℚ) : WithTop ℚ)) : Nat.card B * Nat.card (fixV B) ≤ Nat.card V := by
  have hA2 : IsA2 G B := ⟨hBG, hB1, hBe⟩
  have h1 : (1 : ℚ) ≤ rAV B := by
    have hle : ((1 : ℚ) : WithTop ℚ) ≤ kq G 2 := le_of_eq hq.symm
    exact le_kq_iff.1 hle B hA2 ((isQuadratic_iff_commSeries_two B).1 hBq)
  have hbpos : 0 < rk ↥B := hA2.rk_pos
  unfold rAV at h1
  rw [le_div_iff₀ (by exact_mod_cast hbpos), one_mul] at h1
  have h2 : rk ↥B ≤ rkIdx (fixV B) := by exact_mod_cast h1
  have h3 := rk_add_rkIdx (fixV B)
  have hVp := isPGroup_two_of_sq_eq_one hV
  rw [card_eq_two_pow_of_isPGroup hBe.isPGroup,
    card_eq_two_pow_of_isPGroup (hVp.to_subgroup (fixV B)), ← pow_add,
    card_eq_two_pow_of_isPGroup hVp]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem alt7_secCrit :
    SecCrit (alternatingGroup (Fin 7)) (fun n => n = 2 ^ 4 ∨ n = 2 ^ 6) := by
  intro V _ _ hV G L B ⟨eL⟩ hLG hGN hBG hGeq hsq hB1 hBe hBq hirr hoff
  have hsimp7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hLs : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hcardL : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hL1 : L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardL
    omega
  have hG1 : G ≠ ⊥ := fun h => hL1 (eq_bot_iff.mpr (h ▸ hLG))
  have hnc : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup ↥L :=
      { (inferInstance : Group ↥L) with
        mul_comm := fun a b => Subtype.ext (hcon a a.2 b b.2) }
    have := IsSimpleGroup.prime_card (α := ↥L)
    rw [hcardL] at this
    exact absurd this (by norm_num)
  have hq : CFSG.Open.IsQuasisimple ↥L :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.isQuasisimple_of_alt (by norm_num) eL
  have hO2 : pCoreOf 2 G = ⊥ := S153EB6.pCoreOf_two_eq_bot_of_irr hV le_rfl hirr
  have hn : ∀ y ∈ G, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun y hy l hl =>
    (Subgroup.mem_normalizer_iff.mp (hGN hy) l).mp hl
  have hF : quasithinGenFitting G = L :=
    C124.quasithinGenFitting_eq_of_two_group_quot hLG hn (Or.inl hq)
      (fun y hy => ⟨1, by rw [pow_one]; exact hsq y hy⟩) hO2
  obtain ⟨A, hA⟩ := B6.exists_isFFStarOffender ⟨B, hBG, hB1, hBe, hoff⟩
  have hGF : GF2EightFive := EightFive.gf2EightFive_of_b42L42Core EightFive.b42L42Core_holds
  have hcommV : commV G = ⊤ := commV_eq_top_of_irr hG1 hirr
  have hfixL : fixV L = ⊥ := fixV_eq_bot_of_irr hGN hL1 hirr
  have hLirr : (∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤) ∧
      (Nat.card V = 2 ^ 4 ∨ Nat.card V = 2 ^ 6) := by
    rcases hGF V hV G L hF.symm 7 (Or.inl rfl) ⟨eL⟩ ⟨A, hA⟩ with hnat | ⟨-, -, hc16⟩
    · obtain ⟨α, hα, π, hπ, hker, heq⟩ := hnat
      have hπinj : Function.Injective π := by
        rw [← MonoidHom.ker_eq_bot_iff, hker, hfixL, inf_bot_eq, Subgroup.bot_subgroupOf]
      have hcardC : Nat.card ↥(commV G) = 2 ^ 6 := by
        rw [Nat.card_congr (Equiv.ofBijective π ⟨hπinj, hπ⟩), ← card_altHeart_seven]
        rfl
      refine ⟨fun J hJ => ?_, Or.inr ?_⟩
      ·
        let U : AddSubgroup (altHeart 7) :=
          { carrier := {a | ∃ u : ↥(commV G), (u : V) ∈ J ∧ Multiplicative.toAdd (π u) = a}
            add_mem' := by
              rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
              exact ⟨u * u', J.mul_mem hu hu', by rw [map_mul, toAdd_mul]⟩
            zero_mem' := ⟨1, J.one_mem, by rw [map_one, toAdd_one]⟩
            neg_mem' := by
              rintro _ ⟨u, hu, rfl⟩
              exact ⟨u⁻¹, J.inv_mem hu, by rw [map_inv, toAdd_inv]⟩ }
        have hU : ∀ σ ∈ alternatingGroup (Fin 7), ∀ x : evenWeight 7,
            (QuotientAddGroup.mk x : altHeart 7) ∈ U →
              (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart 7) ∈ U := by
          rintro σ hσ x ⟨u, hu, hux⟩
          obtain ⟨l, hl⟩ := hα ⟨σ, hσ⟩
          have hv : (l : MulAut V) (u : V) ∈ commV G := apply_mem_commV (hLG l.2) u.2
          refine ⟨⟨(l : MulAut V) (u : V), hv⟩, hJ _ l.2 _ hu, ?_⟩
          have h1 := heq l u ⟨(l : MulAut V) (u : V), hv⟩ rfl x hux
          rw [h1, hl]
        rcases altHeart_irreducible (by norm_num) U hU with hb | ht
        · left
          rw [eq_bot_iff]
          intro v hv
          have hvC : v ∈ commV G := by rw [hcommV]; exact Subgroup.mem_top v
          have h1 : Multiplicative.toAdd (π ⟨v, hvC⟩) ∈ U := ⟨⟨v, hvC⟩, hv, rfl⟩
          rw [hb, AddSubgroup.mem_bot] at h1
          have h2 : π ⟨v, hvC⟩ = 1 := h1
          have h3 : (⟨v, hvC⟩ : ↥(commV G)) = 1 := hπinj (h2.trans (map_one π).symm)
          rw [Subgroup.mem_bot]
          exact congrArg Subtype.val h3
        · right
          rw [eq_top_iff]
          intro v _
          have hvC : v ∈ commV G := by rw [hcommV]; exact Subgroup.mem_top v
          have h1 : Multiplicative.toAdd (π ⟨v, hvC⟩) ∈ U := by rw [ht]; exact AddSubgroup.mem_top _
          obtain ⟨u, hu, hux⟩ := h1
          have h2 : u = ⟨v, hvC⟩ := hπinj (Multiplicative.toAdd.injective hux)
          rw [h2] at hu
          exact hu
      · rw [← Subgroup.card_top (G := V), ← hcommV]
        exact hcardC
    · have hcardV : Nat.card V = 2 ^ 4 := by
        rw [← Subgroup.card_top (G := V), ← hcommV]
        exact hc16
      refine ⟨fun J hJ => ?_, Or.inl hcardV⟩
      refine eq_bot_or_eq_top_of_small hV hnc (fun J _ _ hJ2 hJc φ => ?_) J hJ
      rw [hcardV] at hJc
      have h1 := alt7_trivial_of_card_lt_two_pow_four J hJ2 hJc (φ.comp eL.symm.toMonoidHom)
      refine MonoidHom.ext fun l => ?_
      have h2 := congrArg (fun f : alternatingGroup (Fin 7) →* MulAut J => f (eL l)) h1
      simpa using h2
  obtain ⟨hLirr, hcardV⟩ := hLirr
  have hnt : Nontrivial V := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hxy (MulEquiv.ext fun v => Subsingleton.elim _ _)
  have hctx : CFSG.QuasithinUnique.Bridge.Alt57.Ctx G L 7 := ⟨Or.inr rfl, ⟨eL⟩, hF.symm, hsq⟩
  have hIrrSec : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤ := by
    refine ⟨bot_lt_top, fun J hJ _ _ => hLirr J fun l hl v hv => ?_⟩
    have h1 := hJ ⟨l, hl⟩ v hv
    have h2 : (⟨l, hl⟩ : ↥L) • v = l v := by simp [Subgroup.smul_def, MulAut.smul_def]
    rwa [h2] at h1
  have hq1 : qOf G = ((1 : ℚ) : WithTop ℚ) := by
    rcases EightFive.asB42Alt7_ctx hV hctx hIrrSec hA with h | h
    · exact h.2
    · exact h.2.2.2.2.1
  exact ⟨hLirr, card_mul_card_fixV_le_of_qOf hV hBG hB1 hBe hBq hq1, hcardV⟩

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
