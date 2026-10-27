module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigSpB
public import CFSG.Assembly.Dichotomy

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {N K : Subgroup G}

theorem involutionGraph_preconnected_of_quot (hK : K ∈ kStarComponents N) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSQ : S ≤ coreActionKernel K)
    (hconn : (CFSG.Assembly.involutionGraph (coreQuot K)).Preconnected) :
    (CFSG.Assembly.involutionGraph ↥(K ⊓ centralizer (S : Set G))).Preconnected := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := K ⊓ centralizer (S : Set G) with hYdef
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  have hO : Odd (Nat.card (oddCoreIn K)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn K)
  have hsup : Y ⊔ oddCoreIn K = K := inf_centralizer_sup_oddCoreIn_eq hS2 hSQ
  have hinv : ∀ y : G, orderOf y = 2 → y⁻¹ = y := fun y hy =>
    inv_eq_of_mul_eq_one_right (by rw [← sq, ← hy, pow_orderOf_eq_one])
  have himg2 : ∀ t : {y : ↥Y // orderOf y = 2},
      orderOf (π ⟨(t.1 : G), t.1.2.1⟩) = 2 := fun t =>
    Sig.orderOf_mk_eq_two (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]; exact t.2)
  let ρ : {y : ↥Y // orderOf y = 2} → {x : coreQuot K // orderOf x = 2} := fun t =>
    ⟨π ⟨(t.1 : G), t.1.2.1⟩, himg2 t⟩
  have hlift : ∀ x : {x : coreQuot K // orderOf x = 2}, ∃ t, ρ t = x := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) x.1
    have hkY : (k : G) ∈ ((Y ⊔ oddCoreIn K : Subgroup G) : Set G) := by
      rw [hsup]
      exact k.2
    rw [coe_mul_of_left_le_normalizer_right _ _
      (inf_le_left.trans (le_normalizer_oddCoreIn K))] at hkY
    obtain ⟨c, hcY, o, hoO, hco⟩ := hkY
    have hcK : c ∈ K := hcY.1
    have hck : π ⟨c, hcK⟩ = x.1 := by
      rw [← hk]
      refine mk_eq_mk_iff.mpr ?_
      have e : c⁻¹ * (k : G) = o := by rw [← hco]; group
      rw [e]
      exact hoO
    have hx2 : x.1 ^ 2 = 1 := by
      have h := pow_orderOf_eq_one x.1
      rwa [x.2] at h
    have hc2 : c ^ 2 ∈ oddCoreIn K := by
      have h : π ⟨c ^ 2, pow_mem hcK 2⟩ = 1 := by
        have e : (⟨c ^ 2, pow_mem hcK 2⟩ : ↥K) = ⟨c, hcK⟩ ^ 2 := rfl
        rw [e, map_pow, hck, hx2]
      exact mk_eq_one_iff.mp h
    have hcO : c ∉ oddCoreIn K := fun h => by
      have h1 : π ⟨c, hcK⟩ = 1 := mk_eq_one_iff.mpr h
      rw [hck] at h1
      have h2 := x.2
      rw [h1, orderOf_one] at h2
      norm_num at h2
    set m := orderOf (c ^ 2) with hm
    have hmodd : Odd m := Odd.of_dvd_nat hO ((oddCoreIn K).orderOf_dvd_natCard hc2)
    have ht2 : orderOf (c ^ m) = 2 := orderOf_pow_orderOf_sq_eq_two hO hc2 hcO
    have htY : c ^ m ∈ Y := pow_mem hcY m
    refine ⟨⟨⟨c ^ m, htY⟩, by rw [Subgroup.orderOf_mk]; exact ht2⟩, Subtype.ext ?_⟩
    change π ⟨c ^ m, (pow_mem hcY m).1⟩ = x.1
    have e : (⟨c ^ m, (pow_mem hcY m).1⟩ : ↥K) = ⟨c, hcK⟩ ^ m := rfl
    obtain ⟨j, hj⟩ := hmodd
    rw [e, map_pow, hck, hj, pow_succ, pow_mul, hx2, one_pow, one_mul]
  have hadj : ∀ t₁ t₂ : {y : ↥Y // orderOf y = 2},
      (CFSG.Assembly.involutionGraph (coreQuot K)).Adj (ρ t₁) (ρ t₂) →
        (CFSG.Assembly.involutionGraph ↥Y).Reachable t₁ t₂ := by
    intro t₁ t₂ h
    rw [CFSG.Assembly.involutionGraph, SimpleGraph.fromRel_adj] at h
    obtain ⟨hne, hc⟩ := h
    set a : G := ((t₁.1 : ↥Y) : G) with ha
    set b : G := ((t₂.1 : ↥Y) : G) with hb
    have ha2 : orderOf a = 2 := by rw [ha, Subgroup.orderOf_coe]; exact t₁.2
    have hb2 : orderOf b = 2 := by rw [hb, Subgroup.orderOf_coe]; exact t₂.2
    have hcomm : π ⟨a, t₁.1.2.1⟩ * π ⟨b, t₂.1.2.1⟩ = π ⟨b, t₂.1.2.1⟩ * π ⟨a, t₁.1.2.1⟩ := by
      rcases hc with hc | hc
      · exact hc
      · exact hc.symm
    have hab2 : (a * b) ^ 2 ∈ oddCoreIn K := by
      have h := (mk_mul_comm_iff (⟨a, t₁.1.2.1⟩ : ↥K) ⟨b, t₂.1.2.1⟩).mp hcomm
      change a⁻¹ * b⁻¹ * a * b ∈ oddCoreIn K at h
      rw [hinv a ha2, hinv b hb2] at h
      rw [sq, ← mul_assoc]
      exact h
    have habO : a * b ∉ oddCoreIn K := fun h => hne (Subtype.ext (by
      have h1 : π (⟨a, t₁.1.2.1⟩ * ⟨b, t₂.1.2.1⟩) = 1 := mk_eq_one_iff.mpr h
      rw [map_mul] at h1
      have h2 : π ⟨b, t₂.1.2.1⟩ * π ⟨b, t₂.1.2.1⟩ = 1 := by
        have h3 := pow_orderOf_eq_one (π ⟨b, t₂.1.2.1⟩)
        rw [himg2 t₂, sq] at h3
        exact h3
      change π ⟨a, t₁.1.2.1⟩ = π ⟨b, t₂.1.2.1⟩
      calc π ⟨a, t₁.1.2.1⟩ = π ⟨a, t₁.1.2.1⟩ * (π ⟨b, t₂.1.2.1⟩ * π ⟨b, t₂.1.2.1⟩) := by
            rw [h2, mul_one]
        _ = π ⟨a, t₁.1.2.1⟩ * π ⟨b, t₂.1.2.1⟩ * π ⟨b, t₂.1.2.1⟩ := by rw [mul_assoc]
        _ = π ⟨b, t₂.1.2.1⟩ := by rw [h1, one_mul]))
    obtain ⟨w, hwz, hw2, hwa, hwb⟩ := exists_involution_commute_of_mul_sq_mem hO ha2 hb2 hab2 habO
    have hwY : w ∈ Y := (zpowers_le.mpr (mul_mem t₁.1.2 t₂.1.2)) hwz
    set w₀ : {y : ↥Y // orderOf y = 2} := ⟨⟨w, hwY⟩, by rw [Subgroup.orderOf_mk]; exact hw2⟩
    exact (reachable_of_commute (s := t₁) (t := w₀) (Subtype.ext hwa.symm)).trans
      (reachable_of_commute (s := w₀) (t := t₂) (Subtype.ext hwb))
  have hsame : ∀ t₁ t₂ : {y : ↥Y // orderOf y = 2}, ρ t₁ = ρ t₂ →
      (CFSG.Assembly.involutionGraph ↥Y).Reachable t₁ t₂ := by
    intro t₁ t₂ h
    have hrank : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (coreQuot K)) := by
      show 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (↥K ⧸ pPrimeCore 2 ↥K))
      rw [← SectionRank.pRank_eq_open_pRank_top, FooteLit.pRank_quotient_pPrimeCore,
        pRank_coe_eq]
      exact two_le_pRank_of_mem_solomonKStar hK.2
    obtain ⟨F, -, hF, hxF⟩ := exists_isKleinFour_mem hrank (mem_top _) (ρ t₁).2
    obtain ⟨x', hx'F, hx'z⟩ := exists_not_mem_zpowers_of_isKleinFour hF hxF
    have hx'1 : x' ≠ 1 := fun h => hx'z (h ▸ one_mem _)
    have hx'2 : orderOf x' = 2 := orderOf_eq_two_of_isKleinFour hF hx'F hx'1
    obtain ⟨t', ht'⟩ := hlift ⟨x', hx'2⟩
    have hA : ∀ t : {y : ↥Y // orderOf y = 2}, ρ t = ρ t₁ →
        (CFSG.Assembly.involutionGraph (coreQuot K)).Adj (ρ t) (ρ t') := by
      intro t ht
      rw [ht, ht', CFSG.Assembly.involutionGraph, SimpleGraph.fromRel_adj]
      refine ⟨fun h' => hx'z ?_, Or.inl (comm_of_isKleinFour hF _ hxF x' hx'F)⟩
      rw [show x' = (ρ t₁).1 from (congrArg Subtype.val h').symm]
      exact mem_zpowers _
    exact (hadj t₁ t' (hA t₁ rfl)).trans (hadj t₂ t' (hA t₂ h.symm)).symm
  have hwalk : ∀ (x y : {x : coreQuot K // orderOf x = 2})
      (p : (CFSG.Assembly.involutionGraph (coreQuot K)).Walk x y)
      (t₁ t₂ : {y : ↥Y // orderOf y = 2}), ρ t₁ = x → ρ t₂ = y →
        (CFSG.Assembly.involutionGraph ↥Y).Reachable t₁ t₂ := by
    intro x y p
    induction p with
    | nil =>
      intro t₁ t₂ h₁ h₂
      exact hsame t₁ t₂ (h₁.trans h₂.symm)
    | cons hxy p ih =>
      intro t₁ t₂ h₁ h₂
      obtain ⟨t', ht'⟩ := hlift _
      exact (hadj t₁ t' (by rw [h₁, ht']; exact hxy)).trans (ih t' t₂ ht' h₂)
  intro t₁ t₂
  obtain ⟨p⟩ := hconn (ρ t₁) (ρ t₂)
  exact hwalk _ _ p t₁ t₂ rfl rfl

@[expose] def Lemma39TwoDiscSEFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (K' ≤ normalizer (wGroup B V : Set G) →
        (∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
          E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)) ∧
      ((∃ M : Subgroup (coreQuot K'), Assembly.Dichotomy.dichotomyStronglyEmbedded M) →
        (∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
          ¬ (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected) →
        K' ≤ normalizer (wGroup B V : Set G))

@[expose] def Lemma39TwoDiscSEAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      (K' ≤ normalizer (wGroup B V : Set G) →
        (∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
          E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)) ∧
      ((∃ M : Subgroup (coreQuot K'), Assembly.Dichotomy.dichotomyStronglyEmbedded M) →
        (∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
          ¬ (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected) →
        K' ≤ normalizer (wGroup B V : Set G))

theorem even_card_coreQuot {K' V B : Subgroup G} (hP : SigPair N K K' V B) :
    Even (Nat.card (coreQuot K')) := by
  obtain ⟨-, -, -, hV, hVK', -⟩ := hP
  obtain ⟨v, hv, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  have hv2 := orderOf_eq_two_of_isKleinFour hV hv hv1
  have h := Sig.orderOf_mk_eq_two (K := K') (y := ⟨v, hVK' hv⟩)
    (by rw [Subgroup.orderOf_mk]; exact hv2)
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk' (pPrimeCore 2 ↥K') (⟨v, hVK' hv⟩ : ↥K'))
  rw [h] at hdvd
  exact even_iff_two_dvd.mpr hdvd

theorem not_forall_disc_of_preconnected {K' V B : Subgroup G} (hP : SigPair N K K' V B)
    (hc : (CFSG.Assembly.involutionGraph (coreQuot K')).Preconnected) :
    ¬ ∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
      ¬ (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected := by
  obtain ⟨hK, hK', hne, -, -, -, -, -, -, -, E, hE, hEB, hEK⟩ := hP
  exact fun h => h E hE hEB hEK (involutionGraph_preconnected_of_quot hK'
    (isPGroup_of_isKleinFour hE) (hEK.trans (le_coreActionKernel_of_ne hK' hK hne.symm)) hc)

theorem lemma39TwoDiscAt_of_SE {R : SigOrientation} (h : Lemma39TwoDiscSEAt R) :
    Lemma39TwoDiscAt R := by
  intro G _ _ hG N hN h2 K K' V B hP hR hW
  obtain ⟨h1, h2'⟩ := h G hG N hN h2 K K' V B hP hR hW
  refine ⟨h1, fun hdisc => ?_⟩
  by_cases hc : (CFSG.Assembly.involutionGraph (coreQuot K')).Preconnected
  · exact (not_forall_disc_of_preconnected hP hc hdisc).elim
  · exact h2' ((Assembly.Dichotomy.involutionGraph_disconnected_iff_stronglyEmbedded _
      (even_card_coreQuot hP)).mp hc) hdisc

end CFSG.ComponentClassification.Sol76.Sig
