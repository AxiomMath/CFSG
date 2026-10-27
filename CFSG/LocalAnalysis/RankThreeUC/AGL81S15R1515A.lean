module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

section RankCount

variable {X : Type} [Group X] [Finite X]

theorem pRank_add_le_pRank_sup_add_pRank_inf {Y : Type} [Group Y] [Finite Y] {A B : Subgroup Y}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {q : ℕ} (hq : q.Prime) :
    CFSG.Open.pRank q A + CFSG.Open.pRank q B ≤
      CFSG.Open.pRank q (A ⊔ B) + CFSG.Open.pRank q (A ⊓ B) := by
  have hq1 : 1 < q := hq.one_lt
  obtain ⟨E₁, hE₁A, hE₁, hc₁⟩ := CFSG.SectionRank.exists_pRank hq1 A
  obtain ⟨E₂, hE₂B, hE₂, hc₂⟩ := CFSG.SectionRank.exists_pRank hq1 B
  have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    hc x (hE₁A hx) y (hE₂B hy)
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂ hcomm
  have hmem : ∀ x ∈ E₁ ⊔ E₂, ∃ a ∈ E₁, ∃ b ∈ E₂, x = a * b := by
    intro x hx
    have hx' : x ∈ ((E₁ ⊔ E₂ : Subgroup Y) : Set Y) := hx
    rw [hset] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  have hsupEA : CFSG.Open.IsElemAbelian q (E₁ ⊔ E₂) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha, b, hb, hxe⟩ := hmem x x.2
      obtain ⟨a', ha', b', hb', hye⟩ := hmem y y.2
      apply Subtype.ext
      change (x : Y) * y = y * x
      have c1 : Commute a a' := pRank_add_le_pRank_sup_aux_comm hE₁ ha ha'
      have c2 : Commute a b' := hcomm a ha b' hb'
      have c3 : Commute b a' := (hcomm a' ha' b hb).symm
      have c4 : Commute b b' := pRank_add_le_pRank_sup_aux_comm hE₂ hb hb'
      have c : Commute (a * b) (a' * b') :=
        Commute.mul_left (Commute.mul_right c1 c2) (Commute.mul_right c3 c4)
      rw [hxe, hye]
      exact c
    · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
      have c : Commute a b := hcomm a ha b hb
      rw [c.mul_pow, hE₁.2 a ha, hE₂.2 b hb, one_mul]
  have hinfEA : CFSG.Open.IsElemAbelian q (E₁ ⊓ E₂) :=
    ⟨⟨⟨fun x y => Subtype.ext (pRank_add_le_pRank_sup_aux_comm hE₁ x.2.1 y.2.1)⟩⟩,
      fun x hx => hE₁.2 x hx.1⟩
  have hinfAB : E₁ ⊓ E₂ ≤ A ⊓ B := inf_le_inf hE₁A hE₂B
  have hdvd1 : Nat.card ↥(E₁ ⊓ E₂) ∣ q ^ CFSG.Open.pRank q A := by
    rw [← hc₁]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨t, -, htcard⟩ := (Nat.dvd_prime_pow hq).1 hdvd1
  have ht : t ≤ CFSG.Open.pRank q (A ⊓ B) := CFSG.SectionRank.le_pRank hq1 hinfAB hinfEA htcard
  have hprod : Nat.card ↥(E₁ ⊔ E₂) * q ^ t = q ^ (CFSG.Open.pRank q A + CFSG.Open.pRank q B) := by
    rw [← htcard, hcard, hc₁, hc₂, pow_add]
  obtain ⟨j, -, hjcard⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro _ hprod)
  rw [hjcard, ← pow_add] at hprod
  have hjt : j + t = CFSG.Open.pRank q A + CFSG.Open.pRank q B :=
    Nat.pow_right_injective hq.two_le hprod
  have hj : j ≤ CFSG.Open.pRank q (A ⊔ B) :=
    CFSG.SectionRank.le_pRank hq1 (sup_le_sup hE₁A hE₂B) hsupEA hjcard
  omega

theorem pRank_sum_le_pRank_sup (S : Finset (Subgroup X)) (hS : ∀ L ∈ S, IsC2 L) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {s : ℕ}
    (hs : ∀ L ∈ S, CFSG.Open.pRank q (KFactsPair.centerIn (barO2 L)) ≤ s) :
    ∑ L ∈ S, CFSG.Open.pRank q L ≤ CFSG.Open.pRank q (S.sup id) + (S.card - 1) * s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert L S' hLS ih =>
    have hL : IsC2 L := hS L (Finset.mem_insert_self _ _)
    have hS' : ∀ K ∈ S', IsC2 K := fun K hK => hS K (Finset.mem_insert_of_mem hK)
    have hs' : ∀ K ∈ S', CFSG.Open.pRank q (KFactsPair.centerIn (barO2 K)) ≤ s :=
      fun K hK => hs K (Finset.mem_insert_of_mem hK)
    have ih' := ih hS' hs'
    rw [Finset.sum_insert hLS, Finset.sup_insert, Finset.card_insert_of_notMem hLS]
    by_cases hemp : S' = ∅
    · subst hemp
      simp
    · have hcard : S'.card ≠ 0 := by simpa using hemp
      have hc : ∀ a ∈ barO2 L, ∀ b ∈ barO2 (S'.sup id), a * b = b * a := by
        intro a ha b hb
        have hBle : S'.sup id ≤ (Subgroup.centralizer ({a} : Set (X ⧸ CFSG.pCore 2 X))).comap
            (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
          refine Finset.sup_le (fun K hK => ?_)
          have hne : L ≠ K := fun h => hLS (h ▸ hK)
          have hcomm := isC2_commute_of_ne hL (hS' K hK) hne
          have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
          intro y hy
          have h2 := (Subgroup.mem_centralizer_iff.1 h1) (QuotientGroup.mk' _ y)
            (Subgroup.mem_map_of_mem _ hy)
          rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff.1 hh]
          exact h2.symm
        obtain ⟨y, hy, rfl⟩ := hb
        have := hBle hy
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
        exact this a rfl
      have hmain := pRank_add_le_pRank_sup_aux_commute hc hq (hs L (Finset.mem_insert_self _ _))
      have e1 : CFSG.Open.pRank q (barO2 L) = CFSG.Open.pRank q L :=
        (pRank_barO2_eq_aux_eq L hq hq2).symm
      have e2 : CFSG.Open.pRank q (barO2 (S'.sup id)) = CFSG.Open.pRank q (S'.sup id) :=
        (pRank_barO2_eq_aux_eq _ hq hq2).symm
      have e3 : CFSG.Open.pRank q (barO2 L ⊔ barO2 (S'.sup id)) =
          CFSG.Open.pRank q (L ⊔ S'.sup id) := by
        rw [← Subgroup.map_sup]
        exact (pRank_barO2_eq_aux_eq _ hq hq2).symm
      have hk : (S'.card - 1) * s + s = S'.card * s := by
        obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard
        rw [hn]
        simp [Nat.succ_mul]
      show CFSG.Open.pRank q L + ∑ K ∈ S', CFSG.Open.pRank q K ≤
        CFSG.Open.pRank q (L ⊔ S'.sup id) + (S'.card + 1 - 1) * s
      rw [Nat.add_sub_cancel]
      nlinarith [ih', hmain, e1, e2, e3, hk]

theorem isC2_le_normalClosure_conj {L L' : Subgroup X} (hL : IsC2 L) (hL' : IsC2 L')
    (h : L' ≤ Subgroup.normalClosure (L : Set X)) :
    ∃ x : X, L' = L.map (MulAut.conj x).toMonoidHom := by
  by_contra hcon
  push Not at hcon
  set N' : Subgroup X := (Subgroup.centralizer
    (barO2 L' : Set (X ⧸ CFSG.pCore 2 X))).comap (QuotientGroup.mk' (CFSG.pCore 2 X)) with hN'
  have hconj : ∀ x : X, L.map (MulAut.conj x).toMonoidHom ≤ N' := by
    intro x
    have hc := isC2_commute_of_ne hL' (liftOf_conj_aux4 hL x) (hcon x)
    have h1 : barO2 (L.map (MulAut.conj x).toMonoidHom) ≤
        Subgroup.centralizer (barO2 L' : Set (X ⧸ CFSG.pCore 2 X)) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hc
    intro y hy
    exact h1 (Subgroup.mem_map_of_mem _ hy)
  have hnc : Subgroup.normalClosure (L : Set X) ≤ N' := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro b hb
    obtain ⟨a, ha, hab⟩ := Group.mem_conjugatesOfSet_iff.1 hb
    obtain ⟨c, rfl⟩ := isConj_iff.1 hab
    exact hconj c ⟨a, ha, by simp [MulAut.conj_apply]⟩
  have hL'N : L' ≤ N' := h.trans hnc
  have h2 : barO2 L' ≤ Subgroup.centralizer (barO2 L' : Set (X ⧸ CFSG.pCore 2 X)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hL'N hy
  exact liftOf_unique_aux1 hL'.component (Subgroup.commutator_eq_bot_iff_le_centralizer.2 h2)

theorem barO2_map_conj (L : Subgroup X) (x : X) :
    barO2 (L.map (MulAut.conj x).toMonoidHom) =
      (barO2 L).map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 X) x)).toMonoidHom := by
  unfold barO2
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_centerIn_iff_s15 {Y : Type} [Group Y] (H : Subgroup Y) (y : Y) :
    y ∈ KFactsPair.centerIn H ↔ y ∈ H ∧ ∀ g ∈ H, g * y = y * g := by
  unfold KFactsPair.centerIn
  constructor
  · rintro ⟨⟨z, hz⟩, hzc, rfl⟩
    exact ⟨hz, fun g hg => by
      have := Subgroup.mem_center_iff.1 hzc ⟨g, hg⟩
      exact congrArg Subtype.val this⟩
  · rintro ⟨hy, hc⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    show (⟨y, hy⟩ : H) ∈ Subgroup.center ↥H
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)

theorem centerIn_eq_cfsg {Y : Type} [Group Y] (H : Subgroup Y) :
    KFactsPair.centerIn H = CFSG.centerIn H := by
  ext y
  rw [mem_centerIn_iff_s15]
  unfold CFSG.centerIn
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hy, hc⟩
    exact ⟨hy, fun g hg => hc g hg⟩
  · rintro ⟨hy, hc⟩
    exact ⟨hy, fun g hg => hc g hg⟩

theorem centerIn_map_conj {Y : Type} [Group Y] (H : Subgroup Y) (z : Y) :
    KFactsPair.centerIn (H.map (MulAut.conj z).toMonoidHom) =
      (KFactsPair.centerIn H).map (MulAut.conj z).toMonoidHom := by
  ext y
  rw [mem_centerIn_iff_s15, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hc⟩
    refine ⟨a, (mem_centerIn_iff_s15 H a).2 ⟨ha, fun g hg => ?_⟩, rfl⟩
    have h1 := hc ((MulAut.conj z).toMonoidHom g) ⟨g, hg, rfl⟩
    have h2 : (MulAut.conj z) (g * a) = (MulAut.conj z) (a * g) := by
      rw [map_mul, map_mul]
      exact h1
    exact (MulAut.conj z).injective h2
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨haH, hac⟩ := (mem_centerIn_iff_s15 H a).1 ha
    refine ⟨⟨a, haH, rfl⟩, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    show (MulAut.conj z) g * (MulAut.conj z) a = (MulAut.conj z) a * (MulAut.conj z) g
    rw [← map_mul, ← map_mul, hac g hg]

theorem pRank_normalClosure_ge {L : Subgroup X} (hL : IsC2 L) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {s : ℕ} (hs : CFSG.Open.pRank q (KFactsPair.centerIn (barO2 L)) ≤ s) :
    Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} *
        CFSG.Open.pRank q L ≤
      CFSG.Open.pRank q (Subgroup.normalClosure (L : Set X)) +
        (Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} - 1) * s := by
  classical
  set T : Set (Subgroup X) :=
    {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} with hT
  have hfin : T.Finite := Set.toFinite _
  set S : Finset (Subgroup X) := hfin.toFinset with hS
  have hmemS : ∀ K, K ∈ S ↔ K ∈ T := fun K => hfin.mem_toFinset
  have hCS : ∀ K ∈ S, IsC2 K := fun K hK => ((hmemS K).1 hK).1
  have hconj : ∀ K ∈ S, ∃ x : X, K = L.map (MulAut.conj x).toMonoidHom := fun K hK =>
    isC2_le_normalClosure_conj hL ((hmemS K).1 hK).1 ((hmemS K).1 hK).2
  have hrankK : ∀ K ∈ S, CFSG.Open.pRank q K = CFSG.Open.pRank q L := by
    intro K hK
    obtain ⟨x, rfl⟩ := hconj K hK
    exact exists_yComponent_dvd_aux_pRank_map_conj hq.one_lt L x
  have hsK : ∀ K ∈ S, CFSG.Open.pRank q (KFactsPair.centerIn (barO2 K)) ≤ s := by
    intro K hK
    obtain ⟨x, rfl⟩ := hconj K hK
    rw [barO2_map_conj, centerIn_map_conj, exists_yComponent_dvd_aux_pRank_map_conj hq.one_lt]
    exact hs
  have hmain := pRank_sum_le_pRank_sup S hCS hq hq2 hsK
  have hsup : S.sup id = Subgroup.normalClosure (L : Set X) := by
    apply le_antisymm
    · exact Finset.sup_le (fun K hK => ((hmemS K).1 hK).2)
    · rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro bb hbb
      obtain ⟨c, hc, hconj'⟩ := Group.mem_conjugatesOfSet_iff.1 hbb
      obtain ⟨d, rfl⟩ := isConj_iff.1 hconj'
      have hK : L.map (MulAut.conj d).toMonoidHom ∈ S := by
        rw [hmemS]
        refine ⟨liftOf_conj_aux4 hL d, ?_⟩
        rintro _ ⟨e, he, rfl⟩
        exact (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem e
          (Subgroup.le_normalClosure he) d
      have hbbmem : d * c * d⁻¹ ∈ L.map (MulAut.conj d).toMonoidHom :=
        ⟨c, hc, by simp [MulAut.conj_apply]⟩
      exact (Finset.le_sup (f := id) hK) hbbmem
  rw [Finset.sum_congr rfl hrankK, Finset.sum_const, smul_eq_mul, hsup] at hmain
  have hcard : S.card = T.ncard := (Set.ncard_eq_toFinset_card T hfin).symm
  rw [hcard] at hmain
  exact hmain

theorem two_le_ncard_of_ne_normalClosure {L : Subgroup X} (hL : IsC2 L)
    (h : L ≠ Subgroup.normalClosure (L : Set X)) :
    2 ≤ Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} := by
  have hex : ∃ x : X, L.map (MulAut.conj x).toMonoidHom ≠ L := by
    by_contra hcon
    push Not at hcon
    apply h
    haveI : L.Normal := ⟨fun n hn g => by
      have := hcon g
      rw [← this]
      exact ⟨n, hn, by simp [MulAut.conj_apply]⟩⟩
    exact (Subgroup.normalClosure_eq_self L).symm
  obtain ⟨x, hx⟩ := hex
  refine (Set.one_lt_ncard_iff (Set.toFinite _)).2 ⟨L, L.map (MulAut.conj x).toMonoidHom, ?_, ?_, hx.symm⟩
  · exact ⟨hL, Subgroup.le_normalClosure⟩
  · refine ⟨liftOf_conj_aux4 hL x, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem a
      (Subgroup.le_normalClosure ha) x

theorem eq_sup_of_ncard_two {L : Subgroup X} (hL : IsC2 L)
    (h : Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} = 2) :
    ∃ x : X, L.map (MulAut.conj x).toMonoidHom ≠ L ∧
      Subgroup.normalClosure (L : Set X) = L ⊔ L.map (MulAut.conj x).toMonoidHom := by
  set T : Set (Subgroup X) :=
    {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} with hT
  have hfin : T.Finite := Set.toFinite _
  have hLmem : L ∈ T := ⟨hL, Subgroup.le_normalClosure⟩
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff hfin).1 (by omega : 1 < T.ncard)
  obtain ⟨L', hL'T, hL'ne⟩ : ∃ L', L' ∈ T ∧ L' ≠ L := by
    by_cases hal : a = L
    · exact ⟨b, hb, fun hbl => hab (hal.trans hbl.symm)⟩
    · exact ⟨a, ha, hal⟩
  have hTeq : ({L, L'} : Set (Subgroup X)) = T := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
    · intro K hK
      rcases hK with rfl | rfl
      · exact hLmem
      · exact hL'T
    · rw [Set.ncard_pair hL'ne.symm]
      omega
  obtain ⟨hC', hle'⟩ := hL'T
  obtain ⟨x, rfl⟩ := isC2_le_normalClosure_conj hL hC' hle'
  refine ⟨x, hL'ne, le_antisymm ?_ (sup_le Subgroup.le_normalClosure hle')⟩
  rw [Subgroup.normalClosure, Subgroup.closure_le]
  intro bb hbb
  obtain ⟨c, hc, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hbb
  obtain ⟨d, rfl⟩ := isConj_iff.1 hconj
  have hmem : L.map (MulAut.conj d).toMonoidHom ∈ T := by
    refine ⟨liftOf_conj_aux4 hL d, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem e
      (Subgroup.le_normalClosure he) d
  rw [← hTeq] at hmem
  have hbbmem : d * c * d⁻¹ ∈ L.map (MulAut.conj d).toMonoidHom :=
    ⟨c, hc, by simp [MulAut.conj_apply]⟩
  rcases hmem with h1 | h1
  · rw [h1] at hbbmem
    exact (le_sup_left : L ≤ L ⊔ L.map (MulAut.conj x).toMonoidHom) hbbmem
  · rw [h1] at hbbmem
    exact (le_sup_right : L.map (MulAut.conj x).toMonoidHom ≤
      L ⊔ L.map (MulAut.conj x).toMonoidHom) hbbmem

theorem centerIn_eq_inf_of_dvd {Y : Type} [Group Y] [Finite Y] {A B : Subgroup Y}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {q : ℕ} (hq : q.Prime)
    (hA : Nat.card (KFactsPair.centerIn A) = q) (hB : Nat.card (KFactsPair.centerIn B) = q)
    (h : q ∣ Nat.card ↥(A ⊓ B)) : KFactsPair.centerIn A = A ⊓ B ∧ KFactsPair.centerIn B = A ⊓ B := by
  have hAle : A ⊓ B ≤ KFactsPair.centerIn A := by
    intro x hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    show (⟨x, hx.1⟩ : A) ∈ Subgroup.center ↥A
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2 x hx.2)
  have hBle : A ⊓ B ≤ KFactsPair.centerIn B := by
    intro x hx
    refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
    show (⟨x, hx.2⟩ : B) ∈ Subgroup.center ↥B
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc x hx.1 g g.2).symm
  have h1 : Nat.card ↥(A ⊓ B) ≤ q := hA ▸ Subgroup.card_le_of_le hAle
  have hpos : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  have h2 : Nat.card ↥(A ⊓ B) = q := le_antisymm h1 (Nat.le_of_dvd hpos h)
  exact ⟨(Subgroup.eq_of_le_of_card_ge hAle (by rw [h2, hA])).symm,
    (Subgroup.eq_of_le_of_card_ge hBle (by rw [h2, hB])).symm⟩

theorem pRank_le_one_of_card_eq {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y} {q : ℕ}
    (hq : q.Prime) (h : Nat.card A = q) : CFSG.Open.pRank q A ≤ 1 := by
  obtain ⟨E, hEA, -, hcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt A
  have h1 : Nat.card E ≤ Nat.card A := Subgroup.card_le_of_le hEA
  rw [hcard, h] at h1
  by_contra hgt
  have h2 : q ^ 2 ≤ q ^ CFSG.Open.pRank q A := Nat.pow_le_pow_right hq.pos (by omega)
  nlinarith [hq.two_le]

theorem pRank_eq_zero_of_not_dvd_s15 {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y} {q : ℕ}
    (hq : q.Prime) (h : ¬ q ∣ Nat.card A) : CFSG.Open.pRank q A = 0 := by
  have := (one_le_pRank_iff_dvd A hq).not.2 h
  omega

end RankCount

end CFSG.LocalAnalysis.RankThreeUC.S15
