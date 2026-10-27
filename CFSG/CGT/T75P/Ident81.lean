module

public import CFSG.CGT.T75P.IdentGen
public import CFSG.CGT.T75P.Clos1
public import CFSG.CGT.T75P.NatTrans

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem Std81.not_isPGroup_H (s : Std81 T T₁) : ¬ IsPGroup 2 (hSub T (normIn T₁ T)) := by
  intro hp
  have hfin : Finite G := s.finite
  obtain ⟨hN, e, φ, hcompat⟩ := s.hnat
  have hq : Nat.card (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_SL_three_two
  have hdvd := Subgroup.card_quotient_dvd_card (T.subgroupOf (hSub T (normIn T₁ T)))
  rw [hq] at hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  rw [hk] at hdvd
  have h3 : 3 ∣ 2 ^ k := (show 3 ∣ 168 by norm_num).trans hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem Std81.hHgen (s : Std81 T T₁) :
    hSub T (normIn T₁ T) ≤ Subgroup.closure {x | x ∈ hSub T (normIn T₁ T) ∧ x * x = 1} := by
  refine le_trans (le_of_eq s.closure_normD.symm) (Subgroup.closure_mono ?_)
  intro x hx
  exact ⟨s.normD_le hx, mul_self_eq_one_of_mem_classD s.hc.hy.pair.wc.1 hx.1⟩

theorem Std81.hHC (s : Std81 T T₁) :
    hSub T (normIn T₁ T) ⊓ Subgroup.centralizer (T : Set G) = T := by
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  exact inf_centralizer_eq_of_natural hTH hHN s.hnat

theorem Std81.T_inf_pCore (s : Std81 T T₁) {Y : Subgroup G} (hUY : Uc T T₁ ≤ Y)
    (hcl : Subgroup.normalClosure ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊤) :
    T.subgroupOf Y ⊓ CFSG.pCore 2 ↥Y = ⊥ := by
  classical
  have hfin : Finite G := s.finite
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  have hHY : hSub T (normIn T₁ T) ≤ Y := hSub_le_Uc.trans hUY
  have htrans := natural_trans hHN s.hnat
  by_contra hne
  obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hqG : (q : G) ≠ 1 := fun h => hq1' (Subtype.ext h)
  have hTyO : T.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := by
    intro t ht
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    by_cases ht1 : t = 1
    · rw [ht1]
      exact Subgroup.one_mem _
    · obtain ⟨h, hh, hqh⟩ := htrans (q : G) (Subgroup.mem_subgroupOf.1 hq.1) hqG (t : G) htT
        (fun h => ht1 (Subtype.ext h))
      have hO := (CFSG.pCore_normal (p := 2) (G := ↥Y)).conj_mem q hq.2 ⟨h, hHY hh⟩
      have : (⟨h, hHY hh⟩ * q * ⟨h, hHY hh⟩⁻¹ : ↥Y) = t := Subtype.ext (by simpa using hqh)
      rwa [this] at hO
  have hOtop : CFSG.pCore 2 ↥Y = ⊤ := by
    rw [eq_top_iff, ← hcl]
    exact Subgroup.normalClosure_le_normal hTyO
  apply s.not_isPGroup_H
  intro h
  have hyO : (⟨(h : G), hHY h.2⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
    rw [hOtop]
    exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y) ⟨_, hyO⟩
  refine ⟨n, Subtype.ext ?_⟩
  have := congrArg (fun z : ↥(CFSG.pCore 2 ↥Y) => ((z : ↥Y) : G)) hn
  simpa using this

theorem ident81 (s : Std81 T T₁) (hInd : SimpleCaseUpTo (Nat.card G)) (h215 : Lemma215Stmt)
    (hL : ListWCIdentification) {Y : Subgroup G} (hUY : Uc T T₁ ≤ Y) (hY : Y ≠ ⊤)
    (hcl : Subgroup.normalClosure ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊤) :
    IsSimpleGroup (jQuot ↥Y) ∧ ListGroup (jQuot ↥Y) ∧
      StdPair (jQuot ↥Y) ((T.subgroupOf Y).map (jMap ↥Y)) ∧
      Nat.card ((T.subgroupOf Y).map (jMap ↥Y)) = 8 ∧ NonBender (jQuot ↥Y) := by
  have hfin : Finite G := s.finite
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  have hHY : hSub T (normIn T₁ T) ≤ Y := hSub_le_Uc.trans hUY
  have hlt : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ Nat.card Y :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card Y < Nat.card G := by
      have hidx := Subgroup.card_mul_index Y
      have : Y.index ≠ 1 := fun h => hY (Subgroup.index_eq_one.1 h)
      have hpos : 0 < Y.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hY0 : 0 < Nat.card Y := Nat.card_pos
      have h2' : 2 ≤ Y.index := by omega
      have h3 : Nat.card Y * 2 ≤ Nat.card G := by
        rw [← hidx]
        exact Nat.mul_le_mul_left _ h2'
      omega
    omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := ident_gen hInd h215 hL s.hc.hy.pair.wc hTH hHY hHN s.hHC
    s.hHgen s.not_isPGroup_H hcl (s.T_inf_pCore hUY hcl) (by rw [s.card_T]; norm_num) hlt
  exact ⟨h1, h2, h3, by rw [h4, s.card_T], h5⟩

theorem Std81.normalClosure_top_of_gen (s : Std81 T T₁) {Y : Subgroup G} (hUY : Uc T T₁ ≤ Y)
    (hgen : Y ≤ Subgroup.closure (classD T ∩ (Y : Set G))) :
    Subgroup.normalClosure ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊤ := by
  classical
  have hfin : Finite G := s.finite
  rw [eq_top_iff]
  intro y _
  have key : ∀ g ∈ Subgroup.closure (classD T ∩ (Y : Set G)),
      ∃ hg : g ∈ Y, (⟨g, hg⟩ : ↥Y) ∈
        Subgroup.normalClosure ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem d hd =>
      obtain ⟨y', hy', t, ht, ht1, rfl⟩ := classD_inter_le_deltaOf s.hc.hy.pair.wc
        (fun x hx => mem_deltaOf_Uc_of_mem_normD s hx) s.h66' T_le_Uc s.exists_ne_one hUY hd.1 hd.2
      refine ⟨Y.mul_mem (Y.mul_mem hy' (T_le_Uc.trans hUY ht)) (Y.inv_mem hy'), ?_⟩
      have htN : (⟨t, T_le_Uc.trans hUY ht⟩ : ↥Y) ∈
          Subgroup.normalClosure ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) :=
        Subgroup.le_normalClosure (Subgroup.mem_subgroupOf.2 ht)
      have hmem := Subgroup.normalClosure_normal.conj_mem _ htN ⟨y', hy'⟩
      have e : (⟨y' * t * y'⁻¹, Y.mul_mem (Y.mul_mem hy' (T_le_Uc.trans hUY ht)) (Y.inv_mem hy')⟩ :
          ↥Y) = ⟨y', hy'⟩ * ⟨t, T_le_Uc.trans hUY ht⟩ * ⟨y', hy'⟩⁻¹ := Subtype.ext rfl
      rw [e]
      exact hmem
    | one => exact ⟨Y.one_mem, Subgroup.one_mem _⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨hay, ha'⟩ := iha
      obtain ⟨hby, hb'⟩ := ihb
      exact ⟨Y.mul_mem hay hby, Subgroup.mul_mem _ ha' hb'⟩
    | inv a ha iha =>
      obtain ⟨hay, ha'⟩ := iha
      exact ⟨Y.inv_mem hay, Subgroup.inv_mem _ ha'⟩
  obtain ⟨hy, hyN⟩ := key (y : G) (hgen y.2)
  exact hyN

theorem ident81_cases (s : Std81 T T₁) (hInd : SimpleCaseUpTo (Nat.card G)) (h215 : Lemma215Stmt)
    (hL : ListWCIdentification) {Y : Subgroup G} (hUY : Uc T T₁ ≤ Y) (hY : Y ≠ ⊤)
    (hcl : Subgroup.normalClosure ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊤) :
    StatedClassicalModel (jQuot ↥Y) .PSL 4 2 1 ∨
      Nonempty (jQuot ↥Y ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (jQuot ↥Y ≃* alternatingGroup (Fin 9)) := by
  obtain ⟨-, -, hstd, hcard, hnb⟩ := ident81 s hInd h215 hL hUY hY hcl
  rcases hnb with ⟨mm, sf, hm3, hs1, hmod⟩ | ⟨k, hk6, hk9, hk⟩ | h22 | h23 | h24
  · left
    obtain ⟨hadm, K', hF, hFin, hK', ⟨e⟩⟩ := hmod
    have h8 := (hstd.of_psl hm3 K' hK' e).1
    rw [hcard] at h8
    have h3 : sf * (mm - 1) = 3 := by
      have : (2 : ℕ) ^ 3 = 2 ^ (sf * (mm - 1)) := by rw [← h8]; norm_num
      exact (Nat.pow_right_injective (le_refl 2) this).symm
    have hsf : sf = 1 := by
      have h2 : 2 ≤ mm - 1 := by omega
      have : sf * 2 ≤ sf * (mm - 1) := Nat.mul_le_mul_left _ h2
      omega
    have hmm : mm = 4 := by
      subst hsf
      omega
    subst hsf
    subst hmm
    exact ⟨hadm, K', hF, hFin, hK', ⟨e⟩⟩
  · right
    have h8 := hstd.card_alternating hk6 hk9 hk
    rw [hcard] at h8
    have hk8 : 8 ≤ k := by
      by_contra hlt
      have : k ≤ 7 := by omega
      simp only [this, ↓reduceIte] at h8
      omega
    have : k = 8 ∨ k = 9 := by omega
    rcases this with rfl | rfl
    · exact Or.inl hk
    · exact Or.inr hk
  · have := hstd.card_sporadic (Or.inl h22)
    omega
  · have := hstd.card_sporadic (Or.inr (Or.inl h23))
    omega
  · have := hstd.card_sporadic (Or.inr (Or.inr h24))
    omega

end CFSG.CGT.T75P
