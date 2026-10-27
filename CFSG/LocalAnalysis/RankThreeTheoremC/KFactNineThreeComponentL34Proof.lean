module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111E16
import CFSG.LieType.Catalog.Realization
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.Sporadic.Bridge.J3Surj
import CFSG.Sporadic.Bridge.M12
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.Sporadic.J3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.AGLEmbedding

namespace KFC34

theorem eq_of_isSimple {Y : Type*} [Group Y] {K L : Subgroup Y} (hK : IsSimpleGroup K)
    (hL : CFSG.Open.IsComponentOf L ⊤) (hLK : L ≤ K) : L = K := by
  obtain ⟨-, hsub, hqs⟩ := hL
  have h1 : CFSG.Open.IsSubnormal L K := by
    simpa [inf_eq_left.2 hLK] using hsub.inf_of_le (le_top : K ≤ ⊤)
  rcases h1.eq_bot_or_eq_of_isSimpleGroup hK with h | h
  · exfalso
    have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hqs.2.toNontrivial
    have hnt : Nontrivial ↥L := (QuotientGroup.mk_surjective (s := Subgroup.center ↥L)).nontrivial
    exact (L.nontrivial_iff_ne_bot.1 hnt) h
  · exact h

theorem not_isSLThreeFour_of_isSimple {X : Type} [Group X] (hs : IsSimpleGroup X)
    (h : IsSLThreeFour X) : False := by
  obtain ⟨hq, hc, -⟩ := h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hz | hz
  · rw [hz, Subgroup.card_bot] at hc
    omega
  · obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    refine hab ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hz]
    exact Subgroup.mem_top _

theorem card_alt (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem card_alt_eleven : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
  rw [card_alt 11 (by norm_num)]
  decide

theorem card_cases {Y : Type} [Group Y] {L : Subgroup Y}
    (h : IsLinThreeFour ↥L ∨ IsSLThreeFour ↥L ∨ Nonempty (↥L ≃* alternatingGroup (Fin 11))) :
    Nat.card ↥L = 20160 ∨ Nat.card ↥L = 60480 ∨ Nat.card ↥L = 19958400 := by
  rcases h with h | h | h
  · exact Or.inl (card_of_isLinThreeFour h)
  · refine Or.inr (Or.inl ?_)
    obtain ⟨-, hc, hl⟩ := h
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L), hc,
      card_of_isLinThreeFour hl]
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr ((Nat.card_congr f.toEquiv).trans card_alt_eleven))

theorem sporadic_orders :
    Nat.card TauCeti.SporadicName.M11.Group ≤ 7920 ∧
      Nat.card TauCeti.SporadicName.M12.Group = 95040 ∧
      Nat.card TauCeti.SporadicName.J3.Group = 50232960 := by
  refine ⟨CFSG.Sporadic.Bridge.M11.tauCeti_finite_card_le.2, ?_, ?_⟩
  · obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
    have h1 := CFSG.Sporadic.Bridge.M12.tauCeti_finite_card_le.2
    have h2 := CFSG.Sporadic.Bridge.M12.le_card_native
    have h3 := Nat.card_congr e.toEquiv
    omega
  · obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J3.card_J3

theorem false_of_sporadic {K : Type} [Group K] {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .J3)
    (h11 : Nat.card TauCeti.SporadicName.M11.Group ≤ 7920)
    (h12 : Nat.card TauCeti.SporadicName.M12.Group = 95040)
    (hJ3 : Nat.card TauCeti.SporadicName.J3.Group = 50232960)
    (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h35 : 35 ∣ Nat.card K) (hge : 20160 ≤ Nat.card K) : False := by
  have hcard := Nat.card_congr e.toEquiv
  rcases hs with rfl | rfl | rfl
  · have : Nat.card K ≤ 7920 := hcard ▸ h11
    omega
  · have : Nat.card K = 95040 := hcard.trans h12
    omega
  · have : Nat.card K = 50232960 := hcard.trans hJ3
    omega

theorem card_catGroup_A {d : TauCeti.ValidLieTypeIndex} {r : ℕ} {q : TauCeti.PrimePower}
    (h : d.1 = .A r q) : Nat.card (CatGroup d) = CFSG.Open.orderA r (q.p ^ q.exponent) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.A r q := h
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv
  haveI : Finite (GaloisField q.p q.exponent) := inferInstance
  change Nat.card (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A r q, hv⟩) = _
  rw [Nat.card_congr e.toEquiv,
    CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear_eq_orderA,
    GaloisField.card _ _ q.exponent_pos.ne']

theorem card_ne_alt_eleven {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsNineThreeLieIndex 3 d) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hG2 : ∀ {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}, q.p = 2 → d.1 = .G2 q →
      Nat.card (CatGroup d) = CFSG.Open.ordG2 (2 ^ q.exponent))
    (hRee : KFactReeOrder)
    (hTits : ∀ {d : TauCeti.ValidLieTypeIndex}, d.1 = .tits →
      Nat.card (CatGroup d) = 17971200) :
    Nat.card K ≠ 19958400 := by
  intro hN
  have hc : Nat.card (CatGroup d) = 19958400 := (Nat.card_congr e.toEquiv).symm.trans hN
  have h3 : ∀ k : ℕ, 3 ^ k ∣ 19958400 → k ≤ 4 := by
    intro k hk
    by_contra hlt
    have h5 : 3 ^ 5 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := h5.trans hk
    norm_num at this
  rcases hd with ⟨q, hqp, hqe, hdq⟩ | ⟨q, hqp, hdq⟩ | ⟨q, ⟨hqp, hqe, hdq⟩ | ⟨-, hqp, hqe, hdq⟩⟩ |
    ⟨q, hqp, hqe, hdq⟩ | ⟨-, m, hdq⟩ | ⟨-, ⟨q, hqp, hqe, hdq | hdq | hdq⟩ |
      ⟨q, hqp, hqe, hdq⟩ | ⟨q, hqp, hqe, hdq⟩ | hdq⟩ | ⟨h, -⟩
  ·
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := card_catGroup_linTwo (p := 3) (n := q.exponent) (by norm_num)
      q.exponent_pos.ne' (d := d) ⟨q, hdq, hqp, rfl⟩
    rw [hc] at h
    have hle := h3 _ (Dvd.intro _ h.symm)
    generalize q.exponent = k at hqe h hle
    interval_cases k <;> omega
  ·
    have h := card_catGroup_twistedA hdq
    have hdv := pow_dvd_card_catGroup_unitary (p := 3) (d := d) ⟨q, hqp, hdq⟩
    have hfe : d.1.fieldExponent = q.exponent := by rw [hdq]; simp
    rw [hfe, hc] at hdv
    have hle := h3 _ hdv
    have hq1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [hc, hqp, hq1] at h
    revert h
    decide
  ·
    rw [card_catGroup_B2 hdq, hqp, hqe] at hc
    revert hc
    decide
  ·
    rw [card_catGroup_twistedA hdq, hqp, hqe] at hc
    revert hc
    decide
  ·
    rw [card_catGroup_A hdq, hqp, hqe] at hc
    revert hc
    decide
  ·
    have h := hRee K d ⟨rfl, m, hdq⟩ ⟨e⟩
    have hfe : d.1.fieldExponent = 2 * m + 1 := by rw [hdq]; simp
    rw [hfe] at h
    have hdv : 3 ^ ((2 * m + 1) * 3) ∣ 19958400 := by
      rw [pow_mul, ← hN, h]
      exact (dvd_mul_right _ _).mul_right _
    have hle := h3 _ hdv
    have hm0 : m = 0 := by omega
    subst hm0
    rw [hN] at h
    revert h
    decide
  ·
    rw [card_catGroup_A hdq, hqp, hqe] at hc
    revert hc
    decide
  ·
    rw [hG2 hqp hdq, hqe] at hc
    revert hc
    decide
  ·
    rw [card_catGroup_B2 hdq, hqp, hqe] at hc
    revert hc
    decide
  ·
    rw [card_catGroup_A hdq, hqp, hqe] at hc
    revert hc
    decide
  ·
    rw [card_catGroup_B_even (by norm_num) hqp hdq, hqe] at hc
    revert hc
    decide
  ·
    have := hTits hdq
    omega
  · omega

theorem false_of_product {K G : Type} [Group K] [Group G] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsNineThreeProductIndex 3 d) (eG : G ≃* (TauCeti.CFSGIndex.lie d).Group)
    (e : K ≃* G × G) (h5 : 5 ∣ Nat.card K) : False := by
  have hcard : Nat.card G = 504 := by
    rcases hd with ⟨-, q, hqp, hqe, hdq⟩ | ⟨h, -⟩
    · rw [Nat.card_congr eG.toEquiv]
      change Nat.card (CatGroup d) = 504
      rw [card_catGroup_A hdq, hqp, hqe]
      decide
    · omega
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, hcard] at h5
  omega

end KFC34

theorem kFactNineThreeComponentL34_holds :
    KFactNineThreeComponentL34 := by
  intro Y _ _ K L hK hL hLK hcase
  obtain ⟨h11, h12, hJ3⟩ := KFC34.sporadic_orders
  have hL35 : 35 ∣ Nat.card L ∧ 20160 ≤ Nat.card L := by
    rcases KFC34.card_cases hcase with h | h | h <;> rw [h] <;> norm_num
  have hK35 : 35 ∣ Nat.card K ∧ 20160 ≤ Nat.card K := by
    have hd : Nat.card L ∣ Nat.card K := Subgroup.card_dvd_of_le hLK
    exact ⟨hL35.1.trans hd, hL35.2.trans (Nat.le_of_dvd Nat.card_pos hd)⟩
  have key : IsSimpleGroup ↥K → (Nonempty (↥K ≃* alternatingGroup (Fin 11)) → False) →
      IsLinThreeFour ↥K := by
    intro hs hno
    have hLK' : L = K := KFC34.eq_of_isSimple hs hL hLK
    subst hLK'
    rcases hcase with h | h | h
    · exact h
    · exact (KFC34.not_isSLThreeFour_of_isSimple hs h).elim
    · exact (hno h).elim
  rcases hK with ⟨i, hi, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · cases i with
    | cyclic p hp => exact hi.elim
    | alternating n hn =>
      have hn' : n = 6 ∨ n = 9 := by
        rcases hi with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · omega
      haveI hsA : IsSimpleGroup (TauCeti.CFSGIndex.alternating n hn).Group := by
        change IsSimpleGroup (alternatingGroup (Fin n))
        exact alternatingGroup.isSimpleGroup (by simp; omega)
      refine key e.isSimpleGroup ?_
      rintro ⟨f⟩
      have h1 : Nat.card ↥K = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
      have h2 : Nat.card ↥K = Nat.card (alternatingGroup (Fin 11)) := Nat.card_congr f.toEquiv
      rw [h1, KFC34.card_alt n (by omega), KFC34.card_alt_eleven] at h2
      rcases hn' with rfl | rfl <;> revert h2 <;> decide
    | lie d =>
      haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := by
        obtain ⟨t, n, r, f, -, hm, -, -, -⟩ :=
          CFSG.RankThree.PartOne.CTP.seitzBridge d.Group d.1 ⟨d.2, ⟨MulEquiv.refl _⟩⟩
        exact (CFSG.LieType.Catalog.lieModel_finite_simple d.Group t n r f hm).2.2
      refine key e.isSimpleGroup ?_
      rintro ⟨f⟩
      exact KFC34.card_ne_alt_eleven hi e card_catGroup_G2_even kFactReeOrder
        (fun hd => CFSG.AGLEmbedding.KFactProofs.SmallIdent.card_of_isTitsGroup
          ⟨_, hd, ⟨MulEquiv.refl _⟩⟩)
        ((Nat.card_congr f.toEquiv).trans KFC34.card_alt_eleven)
    | sporadic s =>
      exfalso
      have hs3 : s = .M11 ∨ s = .M12 ∨ s = .J3 := by
        rcases hi with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | omega
      exact KFC34.false_of_sporadic hs3 h11 h12 hJ3 e hK35.1 hK35.2
  · exact (KFC34.false_of_product hd (MulEquiv.refl _) e (dvd_trans (by norm_num) hK35.1)).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
