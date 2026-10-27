module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28E
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28F
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28D
public import CFSG.GH74.Uniqueness.SU.SU1BgNormalEp2

public section

namespace CFSG.GH74.GLS.Th2.R714

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2

variable {G : Type} [Group G] [Finite G] {x t y : G} {T Q P : Subgroup G} {Good : G → Prop}

namespace Setup714

variable (S : Setup714 x t y T Q P Good)

include S in
theorem eight_le_card_Q : 8 ≤ Nat.card Q := by
  obtain ⟨a, b, haQ, hbQ, ha2, hb2, hab, ha1, hb1, hab', hya, hyb⟩ := S.Klein
  obtain ⟨hVcard, hVel⟩ := klein_facts ha2 hb2 hab ha1 hb1 hab'
  set V : Subgroup G := zpowers a ⊔ zpowers b with hV
  have hVQ : V ≤ Q := sup_le (zpowers_le.2 haQ) (zpowers_le.2 hbQ)
  have htV : t ∉ V := by
    intro h
    apply S.t_bad
    apply S.good_outer t S.tQ S.t2 S.t1 S.tx y S.yT S.yR S.y2
    rcases hVel t h with h1 | h1 | h1 | h1
    · exact absurd h1 S.t1
    · rw [h1]; exact hya
    · rw [h1]; exact hyb
    · rw [h1]
      calc y * (a * b) = (y * a) * b := by group
        _ = (a * y) * b := by rw [hya]
        _ = a * (y * b) := by group
        _ = a * (b * y) := by rw [hyb]
        _ = a * b * y := by group
  have hne : V ≠ Q := fun h => htV (h ▸ S.tQ)
  have hlt : Nat.card V < Nat.card Q := by
    by_contra hge
    push Not at hge
    exact hne (Subgroup.eq_of_le_of_card_ge hVQ hge)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hVQ
  rw [hVcard] at hm hlt
  have : 2 ≤ m := by
    by_contra h2
    push Not at h2
    interval_cases m <;> omega
  omega

include S in
theorem two_le_pRank_Q : 2 ≤ pRank 2 ↥Q := by
  obtain ⟨a, b, haQ, hbQ, ha2, hb2, hab, ha1, hb1, hab', hya, hyb⟩ := S.Klein
  obtain ⟨hVcard, hVel⟩ := klein_facts ha2 hb2 hab ha1 hb1 hab'
  have hel : ∀ {z : G}, orderOf z = 2 → CFSG.IsElementaryAbelian 2 ↥(zpowers z) := fun h =>
    Th2.isElementaryAbelian_zpowers_of_orderOf_two h
  have ha2' : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hb2' : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have hVel' : CFSG.IsElementaryAbelian 2 ↥(zpowers a ⊔ zpowers b) :=
    isElementaryAbelian_sup (hel ha2') (hel hb2') fun k hk l hl => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hk
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hl
      exact (Commute.zpow_zpow (show Commute a b from hab) m n).eq
  have hVQ : zpowers a ⊔ zpowers b ≤ Q := sup_le (zpowers_le.2 haQ) (zpowers_le.2 hbQ)
  have h4 : IsFourSub Q (zpowers a ⊔ zpowers b) := ⟨hVQ, hVel', hVcard⟩
  have := Th2.pRank_of_isFourSub h4
  have h5 := C3.Layer1.Back.pRank_mono' hVQ
  omega

include S in
theorem false_of_transfer (hIG : Stage1.Thm3.Sec5.IG_15_16_ext)
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) {Syl : Subgroup G}
    (hSyl : IsSylowOf 2 Syl ⊤) (hTSyl : T ≤ Syl) (hTx : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (fus : ∀ g : G, g⁻¹ * x * g ∈ Q → Good (g⁻¹ * x * g) → g⁻¹ * t * g ∈ T →
      g⁻¹ * t * g ∈ Q ∧ ¬ Good (g⁻¹ * t * g))
    (fusC : ∀ g : G, g * x = x * g → g⁻¹ * t * g ∈ T → g⁻¹ * t * g ∈ Q) : False := by
  classical
  have h8 := S.eight_le_card_Q
  have hQ2 : IsPGroup 2 ↥Q := S.T2.to_le S.QT
  let z : ↥Q := ⟨x, S.xQ⟩
  let t' : ↥Q := ⟨t, S.tQ⟩
  have hzc : ∀ g : ↥Q, g * z = z * g := fun g => Subtype.ext (S.xc g (S.QT g.2))
  have hz2 : z * z = 1 := Subtype.ext S.x2
  have hz1 : z ≠ 1 := fun h => S.x1 (congrArg Subtype.val h)
  have ht2' : t' * t' = 1 := Subtype.ext S.t2
  have ht1' : t' ≠ 1 := fun h => S.t1 (congrArg Subtype.val h)
  have htz : t' ≠ z := fun h => S.tx (congrArg Subtype.val h)
  obtain ⟨u, huQ, hu2, hu1, hux, huy, -, -, htu⟩ := S.exists_u
  have hnab : ¬ ∀ a b : ↥Q, a * b = b * a := fun h => htu (congrArg Subtype.val (h t' ⟨u, huQ⟩))
  obtain ⟨a, b, haQ, hbQ, ha2, hb2, hab, ha1, hb1, hab', hya, hyb⟩ := S.Klein
  obtain ⟨hVcard, hVel⟩ := klein_facts ha2 hb2 hab ha1 hb1 hab'
  have hVQ : zpowers a ⊔ zpowers b ≤ Q := sup_le (zpowers_le.2 haQ) (zpowers_le.2 hbQ)
  have hE2 : ∀ e ∈ (zpowers a ⊔ zpowers b).subgroupOf Q, e * e = 1 := by
    intro e he
    rw [Subgroup.mem_subgroupOf] at he
    apply Subtype.ext
    show (e : G) * (e : G) = 1
    rcases hVel _ he with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact ha2
    · rw [h]; exact hb2
    · rw [h]
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  have hE4 : Nat.card ↥((zpowers a ⊔ zpowers b).subgroupOf Q) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVQ).toEquiv, hVcard]
  by_cases hC : Nat.card ↥(centralizer ({t'} : Set ↥Q)) ≤ 4
  ·
    rcases R714Dsd.dsd_of_small_centralizer hQ2 z t' hzc hz2 hz1 ht2' ht1' htz hE2 hE4 h8 hnab hC with
      h8' | ⟨A, ρ, hAcyc, hρA, hρ4, hA8, hAcard, hinv, hout, hCl3⟩
    · exact S.case_c h8'
    · have hAQ : A.map Q.subtype ≤ Q := Subgroup.map_subtype_le A
      have hAcardG : Nat.card ↥(A.map Q.subtype) = Nat.card A :=
        Subgroup.card_map_of_injective Q.subtype_injective
      have hcycG : IsCyclic ↥(A.map Q.subtype) :=
        ((Subgroup.equivMapOfInjective A Q.subtype Q.subtype_injective).isCyclic).1 hAcyc
      have hD : DSDShape Q (A.map Q.subtype) (ρ : G) x :=
        { AQ := hAQ
          A2 := S.T2.to_le (hAQ.trans S.QT)
          cyc := hcycG
          ρA := Subgroup.mem_map_of_mem _ hρA
          ρ4 := by rw [Subgroup.orderOf_coe]; exact hρ4
          card := by rw [hAcardG]; exact hAcard
          A8 := by rw [hAcardG]; exact hA8
          inv := by
            intro s hs hsA
            have hsA' : (⟨s, hs⟩ : ↥Q) ∉ A := fun h => hsA ⟨_, h, rfl⟩
            have := hinv _ hsA'
            exact congrArg Subtype.val this
          out := by
            intro s hs hsA
            have hsA' : (⟨s, hs⟩ : ↥Q) ∉ A := fun h => hsA ⟨_, h, rfl⟩
            have h1 := hout _ hsA'
            have e : orderOf (⟨s, hs⟩ : ↥Q) = orderOf s := Subgroup.orderOf_mk s hs
            rw [e] at h1
            rw [hAcardG]
            exact h1
          xQ := S.xQ
          x2 := S.x2
          x1 := S.x1
          xc := fun q hq => S.xc q (S.QT hq) }
      have hCl3G : Cl3G Q x := by
        intro a' ha' b' hb' c' hc' ha2' hb2' hc2' ha1' hb1' hc1' hax hbx hcx
        have := hCl3 ⟨a', ha'⟩ ⟨b', hb'⟩ ⟨c', hc'⟩ (Subtype.ext ha2') (Subtype.ext hb2') (Subtype.ext hc2')
          (fun h => ha1' (congrArg Subtype.val h)) (fun h => hb1' (congrArg Subtype.val h))
          (fun h => hc1' (congrArg Subtype.val h)) (fun h => hax (congrArg Subtype.val h))
          (fun h => hbx (congrArg Subtype.val h)) (fun h => hcx (congrArg Subtype.val h))
        rcases this with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
        · exact Or.inl ⟨q, q.2, congrArg Subtype.val hq⟩
        · exact Or.inr (Or.inl ⟨q, q.2, congrArg Subtype.val hq⟩)
        · exact Or.inr (Or.inr ⟨q, q.2, congrArg Subtype.val hq⟩)
      exact S.case_f hD hIG hperf hSyl hTSyl hTx hCl3G fusC
  ·
    push Not at hC
    have hC8 : 8 ≤ Nat.card ↥(centralizer ({t'} : Set ↥Q)) := by
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (hQ2.to_subgroup (centralizer ({t'} : Set ↥Q)))
      rw [hj] at hC ⊢
      have : 3 ≤ j := by
        by_contra h3
        push Not at h3
        have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) this
    have hv : ∃ v ∈ Q, orderOf v = 4 ∧ v * t = t * v := by
      by_contra hno
      push Not at hno
      have hsq : ∀ g ∈ centralizer ({t'} : Set ↥Q), g * g = 1 := by
        intro g hg
        obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hQ2 g
        by_contra hne
        have hk2 : 2 ≤ k := by
          by_contra hlt
          push Not at hlt
          apply hne
          have hd : orderOf g ∣ 2 := by
            rw [hk]
            simpa using pow_dvd_pow 2 (show k ≤ 1 by omega)
          have h2 : g ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
          simpa [pow_two] using h2
        obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
        have hg4 : orderOf (g ^ (2 ^ i)) = 4 := by
          rw [orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk]
          rw [show 2 ^ (i + 2) = 4 * 2 ^ i by ring]
          exact Nat.mul_div_cancel _ (by positivity)
        have hgC : g ^ (2 ^ i) ∈ centralizer ({t'} : Set ↥Q) := Subgroup.pow_mem _ hg _
        refine hno ((g ^ (2 ^ i) : ↥Q) : G) (g ^ (2 ^ i)).2 ?_ ?_
        · rw [Subgroup.orderOf_coe]; exact hg4
        · exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hgC)
      set C' : Subgroup G := (centralizer ({t'} : Set ↥Q)).map Q.subtype with hC'
      have hC'Q : C' ≤ Q := Subgroup.map_subtype_le _
      have hC'card : Nat.card C' = Nat.card ↥(centralizer ({t'} : Set ↥Q)) :=
        Subgroup.card_map_of_injective Q.subtype_injective
      have hC's : ∀ e ∈ C', e * e = 1 := by
        rintro _ ⟨g, hg, rfl⟩
        exact congrArg Subtype.val (hsq g hg)
      have hC'c : ∀ e ∈ C', ∀ e' ∈ C', e * e' = e' * e := fun e he e' he' =>
        Stage1.Thm3.Sec6.B.comm_of_forall_sq hC's he he'
      have := S.Qrank C' hC'Q hC'c hC's
      omega
    have hNQ : (Q.subgroupOf T).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact S.Qn g g.2 n hn⟩
    have hrk : 2 ≤ pRank 2 ↥(Q.subgroupOf T) := by
      have := Th2.pRank_two_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe S.QT)
      rw [this]
      exact S.two_le_pRank_Q
    rcases CFSG.GH74.Uniqueness.SU.SU1.b_normal_Ep2 2 Nat.prime_two ↥T S.T2 (Q.subgroupOf T) hNQ hrk with
      ⟨E, hEn, hEQ, hEEA, hE4'⟩ | ⟨-, ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩⟩
    · obtain ⟨hEc, hEs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEEA
      refine S.case_e hIG hperf hSyl hTSyl hTx hv ⟨E.map T.subtype, ?_, ?_, ?_, ?_, ?_⟩ fus
      · rintro _ ⟨w, hw, rfl⟩
        exact Subgroup.mem_subgroupOf.1 (hEQ hw)
      · rw [Subgroup.card_map_of_injective T.subtype_injective, hE4']
        norm_num
      · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
        exact congrArg Subtype.val (hEc w hw w' hw')
      · rintro _ ⟨w, hw, rfl⟩
        exact congrArg Subtype.val (hEs w hw)
      · rintro s hs _ ⟨w, hw, rfl⟩
        exact ⟨⟨s, hs⟩ * w * ⟨s, hs⟩⁻¹, hEn.conj_mem w hw ⟨s, hs⟩, rfl⟩
    · exfalso
      have e' : ↥Q ≃* DihedralGroup (2 ^ m) := (Subgroup.subgroupOfEquivOfLe S.QT).symm.trans e
      have := R714Dsd.card_centralizer_le_four_of_model z t' hzc hz2 hz1 ht2' ht1' htz h8
        (Or.inl ⟨m, hm, ⟨e'⟩⟩)
      omega
    · exfalso
      have e' : ↥Q ≃* CFSG.Open.SemidihedralGroup n := (Subgroup.subgroupOfEquivOfLe S.QT).symm.trans e
      have := R714Dsd.card_centralizer_le_four_of_model z t' hzc hz2 hz1 ht2' ht1' htz h8
        (Or.inr ⟨n, hn, ⟨e'⟩⟩)
      omega

end Setup714

end CFSG.GH74.GLS.Th2.R714
