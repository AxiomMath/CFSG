module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515F
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall

variable {X : Type} [Group X] [Finite X]

theorem commute_barO2_of_commute_star_aux_perfect {G : Type*} [Group G] {H : Subgroup G}
    (h : commutator ↥H = ⊤) : H ≤ ⁅H, H⁆ := by
  have h1 : ⁅H, H⁆ = H := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr h)
  exact h1.ge

theorem commute_barO2_of_commute_star_aux_conj {L : Subgroup X} (hL : IsC2 L) (x : X) :
    barO2 (L.map (MulAut.conj x).toMonoidHom) ≤
      ⁅barO2 (L.map (MulAut.conj x).toMonoidHom), barO2 (L.map (MulAut.conj x).toMonoidHom)⁆ :=
  commute_barO2_of_commute_star_aux_perfect (liftOf_conj_aux4 hL x).component.2.2.1

theorem commute_barO2_of_commute_star_aux_normalClosure {L : Subgroup X}
    {P : Subgroup (X ⧸ CFSG.pCore 2 X)}
    (h : ∀ x : X, barO2 (L.map (MulAut.conj x).toMonoidHom) ≤ P) :
    barO2 (Subgroup.normalClosure (L : Set X)) ≤ P := by
  unfold barO2
  rw [Subgroup.map_le_iff_le_comap, Subgroup.normalClosure, Subgroup.closure_le]
  intro b hb
  obtain ⟨a, ha, hab⟩ := Group.mem_conjugatesOfSet_iff.1 hb
  obtain ⟨c, rfl⟩ := isConj_iff.1 hab
  exact h c (Subgroup.mem_map_of_mem _ ⟨a, ha, by simp [MulAut.conj_apply]⟩)

theorem commute_barO2_of_commute_star_aux_le {L : Subgroup X} (x : X) :
    L.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalClosure (L : Set X) := by
  rintro _ ⟨e, he, rfl⟩
  exact (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem e
    (Subgroup.le_normalClosure he) x

theorem commute_barO2_of_commute_star_aux_centralizes_gen {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L)
    (N : Subgroup X) [N.Normal] (hNC : N ≤ gnC T) :
    barO2 (Subgroup.normalClosure (L : Set X)) ≤
      Subgroup.centralizer (barO2 N : Set (X ⧸ CFSG.pCore 2 X)) := by
  have hLne : Ls ≠ ⊥ := liftOf_unique_aux2 hl.comp.1
  refine commute_barO2_of_commute_star_aux_normalClosure (fun x => ?_)
  have hC' := liftOf_conj_aux4 hl.lift.1 x
  rcases isC2_barO2_le_or_commute hC' N with hle | hcomm
  · exfalso
    apply hLne
    have hL'C : L.map (MulAut.conj x).toMonoidHom ≤ gnC T := by
      intro y hy
      have hy' : QuotientGroup.mk' (CFSG.pCore 2 X) y ∈ barO2 N :=
        hle (Subgroup.mem_map_of_mem _ hy)
      obtain ⟨n, hn, hny⟩ := hy'
      have hq : n⁻¹ * y ∈ CFSG.pCore 2 X := QuotientGroup.eq.1 hny
      have hy2 : y = n * (n⁻¹ * y) := by group
      rw [hy2]
      exact (gnC T).mul_mem (hNC hn) (pCore_le_gnC hl.gn hq)
    have hLC : L ≤ gnC T := by
      intro l hl'
      have h1 : x * l * x⁻¹ ∈ gnC T := hL'C ⟨l, hl', rfl⟩
      have h2 := (gnC_normal T).conj_mem _ h1 x⁻¹
      simpa [mul_assoc] using h2
    rw [← hl.lift.2, eq_bot_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact (QuotientGroup.eq_one_iff a).2 (hLC ha)
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm

theorem commute_barO2_of_commute_star_aux_centralizes {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L)
    (N : Subgroup X) [N.Normal] (hNC : N ≤ gnC T) :
    barO2 (Subgroup.normalClosure (L : Set X)) ≤
      Subgroup.centralizer (barO2 N : Set (X ⧸ CFSG.pCore 2 X)) :=
  commute_barO2_of_commute_star_aux_centralizes_gen hl.toGen N hNC

theorem commute_barO2_of_commute_star_gen {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L) {A : Subgroup X}
    (h : ⁅gnImg T (Subgroup.normalClosure (L : Set X)), gnImg T A⁆ = ⊥) :
    ⁅barO2 (Subgroup.normalClosure (L : Set X)), barO2 A⁆ = ⊥ := by
  haveI hJn : (Subgroup.normalClosure (L : Set X)).Normal := Subgroup.normalClosure_normal
  set J : Subgroup X := Subgroup.normalClosure (L : Set X) with hJ
  haveI hNn : (J ⊓ gnC T).Normal := inferInstance
  have hJA : ⁅J, A⁆ ≤ J ⊓ gnC T := by
    refine le_inf (Subgroup.commutator_le_left J A) ?_
    have h2 : (⁅J, A⁆).map (toStar T) = ⊥ := by
      rw [Subgroup.map_commutator]
      exact h
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h2
  have hcomm_N : ⁅barO2 J, barO2 (J ⊓ gnC T)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (commute_barO2_of_commute_star_aux_centralizes_gen hl (J ⊓ gnC T) inf_le_right)
  have h1 : ⁅barO2 J, barO2 A⁆ ≤ barO2 (J ⊓ gnC T) := by
    unfold barO2
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hJA
  have h2 : ⁅⁅barO2 J, barO2 A⁆, barO2 J⁆ = ⊥ := by
    refine eq_bot_iff.2 ?_
    calc ⁅⁅barO2 J, barO2 A⁆, barO2 J⁆ ≤ ⁅barO2 (J ⊓ gnC T), barO2 J⁆ :=
          Subgroup.commutator_mono_left h1
      _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomm_N
  have h3 : ⁅⁅barO2 J, barO2 J⁆, barO2 A⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h2
      (by rw [Subgroup.commutator_comm (barO2 A) (barO2 J)]; exact h2)
  have hperf : barO2 J ≤ ⁅barO2 J, barO2 J⁆ := by
    refine commute_barO2_of_commute_star_aux_normalClosure (fun x => ?_)
    have hle : barO2 (L.map (MulAut.conj x).toMonoidHom) ≤ barO2 J :=
      Subgroup.map_mono (commute_barO2_of_commute_star_aux_le x)
    exact (commute_barO2_of_commute_star_aux_conj hl.lift.1 x).trans
      (Subgroup.commutator_mono hle hle)
  exact eq_bot_iff.2 (h3 ▸ Subgroup.commutator_mono_left hperf)

theorem commute_barO2_of_commute_star {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) {A : Subgroup X}
    (h : ⁅gnImg T (Subgroup.normalClosure (L : Set X)), gnImg T A⁆ = ⊥) :
    ⁅barO2 (Subgroup.normalClosure (L : Set X)), barO2 A⁆ = ⊥ :=
  commute_barO2_of_commute_star_gen hl.toGen h

theorem pRank_centre_barO2_normalClosure_le_one_aux_rank {Y : Type} [Group Y] [Finite Y]
    {H : Subgroup Y} {q : ℕ} (hq : q.Prime) (h : ¬ q ^ 2 ∣ Nat.card H) :
    CFSG.Open.pRank q H ≤ 1 := by
  by_contra hgt
  have h2 : 2 ≤ CFSG.Open.pRank q H := by omega
  obtain ⟨E, hEH, -, hcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt H
  apply h
  have h3 : q ^ 2 ∣ Nat.card E := by rw [hcard]; exact pow_dvd_pow q h2
  exact h3.trans (Subgroup.card_dvd_of_le hEH)

theorem pRank_centre_barO2_normalClosure_le_one_aux_card_gen (hT : LieOddRankTable)
    (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3)
    {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hl : LiftCtxGen X T T₁ T₂ Ls L) :
    Nat.card (Subgroup.center ↥(barO2 L)) ∣ 15 := by
  have h3 : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 3 := hl.rank_L
  have hdat := rankDatum1512_of_ctx hT hl.gn hl.good.shape hl.comp hl.lift h3
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hl.gn hl.comp.1 hl.lift
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hl.lift.1.component.2.2
  have hoddK : Odd (Nat.card (Subgroup.center ↥(barO2 L))) := centre_barO2_odd hl.lift.1
  rcases hdat with ⟨d, hrt, hin, ⟨e⟩, hr⟩ | ⟨n, hn, ⟨e⟩, hr⟩ | ⟨n, hn, ⟨e⟩, hr⟩ |
    ⟨⟨d, q, hq, hd, ⟨e⟩⟩, hr⟩ | ⟨⟨d, q, hq, hd, ⟨e⟩⟩, hr⟩
  · by_cases hA2 : ∃ Q : TauCeti.PrimePower, d.1 = .A 2 Q
    · obtain ⟨Q, hQ⟩ := hA2
      have hQp : Q.p = 2 := by
        have := hrt
        rw [hQ] at this
        exact this.1
      have hk := hKSML3 ↥(barO2 L) hK d ⟨eQ.trans e⟩ hoddK
      rcases Nat.even_or_odd Q.exponent with hev | hodd
      · exact (hk.2 ⟨Q, hQp, hev, hQ⟩).trans (by norm_num)
      · rw [hk.1 (Or.inl ⟨Q, hQp, hodd, hQ⟩)]
        exact one_dvd _
    · push Not at hA2
      by_cases hU4 : ∃ Q : TauCeti.PrimePower, d.1 = .twistedA 3 Q
      · obtain ⟨Q, hQ⟩ := hU4
        have hQp : Q.p = 2 := by
          have := hrt
          rw [hQ] at this
          exact this.1
        rw [hKSMU4 ↥(barO2 L) hK d ⟨Q, hQp, hQ⟩ ⟨eQ.trans e⟩ hoddK]
        exact one_dvd _
      · push Not at hU4
        have hk := hKSMOdd.1 ↥(barO2 L) hK d hin hA2 hU4 ⟨eQ.trans e⟩ hoddK
        by_cases hU5 : ∃ Q : TauCeti.PrimePower, d.1 = .twistedA 4 Q
        · exact (hk.1 hU5).trans (by norm_num)
        · push Not at hU5
          rw [hk.2 hU5]
          exact one_dvd _
  · rcases hn with rfl | rfl
    · exact ((hKSMAlt ↥(barO2 L) hK 6 ⟨eQ.trans e⟩ hoddK).1 (Or.inl rfl)).trans (by norm_num)
    · rw [(hKSMAlt ↥(barO2 L) hK 8 ⟨eQ.trans e⟩ hoddK).2 (by norm_num)]
      exact one_dvd _
  · obtain ⟨-, ⟨e'⟩⟩ := quotCenter_equiv_alt (n := n) (by rcases hn with rfl | rfl <;> norm_num) e
    rcases hn with rfl | rfl
    · exact ((hKSMAlt ↥(barO2 L) hK 7 ⟨eQ.trans e'⟩ hoddK).1 (Or.inr rfl)).trans (by norm_num)
    · rw [(hKSMAlt ↥(barO2 L) hK 10 ⟨eQ.trans e'⟩ hoddK).2 (by norm_num)]
      exact one_dvd _
  · rw [(hKSML3 ↥(barO2 L) hK d ⟨eQ.trans e⟩ hoddK).1 (Or.inr ⟨q, hq, hd⟩)]
    exact one_dvd _
  · rw [hKSMOdd.2 ↥(barO2 L) hK d ⟨q, hq, hd⟩ ⟨eQ.trans e⟩ hoddK]
    exact one_dvd _

theorem pRank_centre_barO2_normalClosure_le_one_aux_card (hT : LieOddRankTable) (hKSMAlt : KSMAlt)
    (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) :
    Nat.card (Subgroup.center ↥(barO2 L)) ∣ 15 :=
  pRank_centre_barO2_normalClosure_le_one_aux_card_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 hl.toGen

theorem pRank_centre_barO2_normalClosure_le_one_aux_prod {S : Type} [Group S] [Finite S]
    (h : IsCentralProdA6Z3 S) : Nat.card (Subgroup.center S) ∣ 3 := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hsup, hcomm, hi1, hi2⟩ := h
  have hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.1 (hcomm hx)) y hy).symm
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K₁ K₂ hc).2
  have hZ : Subgroup.center S ≤ K₁ ⊓ K₂ := by
    intro z hz
    have hzt : z ∈ ((K₁ ⊔ K₂ : Subgroup S) : Set S) := by
      rw [hsup]
      exact Subgroup.mem_top z
    rw [hset] at hzt
    obtain ⟨a, ha, b, hb, rfl⟩ := hzt
    have hzc := Subgroup.mem_center_iff.1 hz
    have ha1 : ∀ g ∈ K₁, g * a = a * g := by
      intro g hg
      have h1 := hzc g
      have h2 : g * b = b * g := hc g hg b hb
      have h3 : g * a * b = a * g * b := by
        calc g * a * b = g * (a * b) := by rw [mul_assoc]
          _ = a * b * g := h1
          _ = a * (b * g) := by rw [mul_assoc]
          _ = a * (g * b) := by rw [h2]
          _ = a * g * b := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hb1 : ∀ g ∈ K₂, g * b = b * g := by
      intro g hg
      have h1 := hzc g
      have h2 : a * g = g * a := hc a ha g hg
      have h3 : a * (g * b) = a * (b * g) := by
        calc a * (g * b) = a * g * b := by rw [mul_assoc]
          _ = g * a * b := by rw [h2]
          _ = g * (a * b) := by rw [mul_assoc]
          _ = a * b * g := h1
          _ = a * (b * g) := by rw [mul_assoc]
      exact mul_left_cancel h3
    have haZ : a ∈ K₁ ⊓ K₂ := by
      rw [hi1, ← centerIn_eq_cfsg]
      exact (mem_centerIn_iff_s15 K₁ a).2 ⟨ha, ha1⟩
    have hbZ : b ∈ K₁ ⊓ K₂ := by
      rw [hi2, ← centerIn_eq_cfsg]
      exact (mem_centerIn_iff_s15 K₂ b).2 ⟨hb, hb1⟩
    exact (K₁ ⊓ K₂).mul_mem haZ hbZ
  have hcard : Nat.card ↥(K₁ ⊓ K₂) = 3 := by
    rw [hi1, ← centerIn_eq_cfsg, card_centerIn_s15]
    exact hK₁.2.1
  exact hcard ▸ Subgroup.card_dvd_of_le hZ

theorem pRank_centre_barO2_normalClosure_le_one_aux_centre {G ι : Type*} [Group G] [Finite G]
    (f : ι → Subgroup G) (S : Finset ι)
    (hc : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, a * b = b * a)
    (hs : ∀ i ∈ S, ∀ z ∈ f i, (∀ g ∈ f i, g * z = z * g) → z = 1) :
    ∀ z ∈ S.sup f, (∀ g ∈ S.sup f, g * z = z * g) → z = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro z hz _
    simpa using hz
  | insert i S' hi ih =>
    intro z hz hzc
    rw [Finset.sup_insert] at hz hzc
    have hc' : ∀ j ∈ S', ∀ a ∈ f i, ∀ b ∈ f j, a * b = b * a := fun j hj =>
      hc i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))
    have hcomm : ∀ a ∈ f i, ∀ b ∈ S'.sup f, a * b = b * a := by
      intro a ha b hb
      have hle : S'.sup f ≤ Subgroup.centralizer ({a} : Set G) := by
        refine Finset.sup_le (fun j hj => ?_)
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hc' j hj a ha y hy
      have := hle hb
      rw [Subgroup.mem_centralizer_iff] at this
      exact this a rfl
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (f i) (S'.sup f) hcomm).2
    have hz' : z ∈ ((f i ⊔ S'.sup f : Subgroup G) : Set G) := hz
    rw [hset] at hz'
    obtain ⟨a, ha, s, hs', rfl⟩ := hz'
    have ha1 : a = 1 := by
      refine hs i (Finset.mem_insert_self _ _) a ha (fun g hg => ?_)
      have h1 := hzc g (Subgroup.mem_sup_left hg)
      have h2 : g * s = s * g := hcomm g hg s hs'
      have h3 : g * a * s = a * g * s := by
        calc g * a * s = g * (a * s) := by rw [mul_assoc]
          _ = a * s * g := h1
          _ = a * (s * g) := by rw [mul_assoc]
          _ = a * (g * s) := by rw [h2]
          _ = a * g * s := by rw [mul_assoc]
      exact mul_right_cancel h3
    subst ha1
    simp only [one_mul] at hzc ⊢
    have hs1 : s = 1 := by
      refine ih (fun i' hi' j hj hij => hc i' (Finset.mem_insert_of_mem hi') j
        (Finset.mem_insert_of_mem hj) hij) (fun i' hi' => hs i' (Finset.mem_insert_of_mem hi')) s hs'
        (fun g hg => hzc g (Subgroup.mem_sup_right hg))
    exact hs1

theorem pRank_centre_barO2_normalClosure_le_one_aux_threecase {L : Subgroup X} (hL : IsC2 L)
    (hZ : Subgroup.center ↥(barO2 L) = ⊥) :
    Subgroup.center ↥(barO2 (Subgroup.normalClosure (L : Set X))) = ⊥ := by
  classical
  set T : Set (Subgroup X) :=
    {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} with hT
  have hfin : T.Finite := Set.toFinite _
  set S : Finset (Subgroup X) := hfin.toFinset with hS
  have hmemS : ∀ K, K ∈ S ↔ K ∈ T := fun K => hfin.mem_toFinset
  have hsup : barO2 (Subgroup.normalClosure (L : Set X)) = S.sup (fun K => barO2 K) := by
    apply le_antisymm
    · refine commute_barO2_of_commute_star_aux_normalClosure (fun x => ?_)
      have hK : L.map (MulAut.conj x).toMonoidHom ∈ S := by
        rw [hmemS]
        exact ⟨liftOf_conj_aux4 hL x, commute_barO2_of_commute_star_aux_le x⟩
      exact Finset.le_sup (f := fun K => barO2 K) hK
    · refine Finset.sup_le (fun K hK => ?_)
      exact Subgroup.map_mono ((hmemS K).1 hK).2
  rw [eq_bot_iff]
  intro z hz
  have hz1 : (z : X ⧸ CFSG.pCore 2 X) = 1 := by
    refine pRank_centre_barO2_normalClosure_le_one_aux_centre (fun K => barO2 K) S ?_ ?_
      (z : X ⧸ CFSG.pCore 2 X) (hsup ▸ z.2) ?_
    · intro i hi j hj hij a ha b hb
      have hcomm := isC2_commute_of_ne ((hmemS i).1 hi).1 ((hmemS j).1 hj).1 hij
      have ha' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
      exact ((Subgroup.mem_centralizer_iff.1 ha') b hb).symm
    · intro i hi w hw hwc
      obtain ⟨x, rfl⟩ := isC2_le_normalClosure_conj hL ((hmemS i).1 hi).1 ((hmemS i).1 hi).2
      have hcen : KFactsPair.centerIn (barO2 (L.map (MulAut.conj x).toMonoidHom)) = ⊥ := by
        have h0 : KFactsPair.centerIn (barO2 L) = ⊥ := by
          unfold KFactsPair.centerIn
          rw [hZ, Subgroup.map_bot]
        rw [barO2_map_conj, centerIn_map_conj, h0, Subgroup.map_bot]
      have hw' := (mem_centerIn_iff_s15 _ w).2 ⟨hw, hwc⟩
      rw [hcen] at hw'
      exact Subgroup.mem_bot.1 hw'
    · intro g hg
      have hg' : g ∈ barO2 (Subgroup.normalClosure (L : Set X)) := hsup ▸ hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg'⟩)
  exact Subgroup.mem_bot.2 (Subtype.ext hz1)

theorem pRank_centre_barO2_normalClosure_le_one_gen (hT : LieOddRankTable) (hKSMAlt : KSMAlt)
    (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L)
    (h15 : Shape1515 L) :
    CFSG.Open.pRank 3 (Subgroup.center ↥(barO2 (Subgroup.normalClosure (L : Set X)))) ≤ 1 := by
  rcases h15 with hJ | hJ | ⟨hL3, -⟩
  · rw [← hJ]
    refine pRank_centre_barO2_normalClosure_le_one_aux_rank Nat.prime_three (fun h9 => ?_)
    have h15' := h9.trans (pRank_centre_barO2_normalClosure_le_one_aux_card_gen hT hKSMAlt hKSMOdd
      hKSMU4 hKSML3 hl)
    norm_num at h15'
  · refine pRank_centre_barO2_normalClosure_le_one_aux_rank Nat.prime_three (fun h9 => ?_)
    have h3' := h9.trans (pRank_centre_barO2_normalClosure_le_one_aux_prod hJ)
    norm_num at h3'
  · have hZ : Subgroup.center ↥(barO2 L) = ⊥ := by
      rcases hL3 with ⟨-, d, q, hq, hd, ⟨e⟩⟩ | ⟨h, -⟩
      · exact R1515F.center_eq_bot_of_equiv_derivedCentralQuotient
          hl.lift.1.component.2.2.1 e
      · omega
    rw [pRank_centre_barO2_normalClosure_le_one_aux_threecase hl.lift.1 hZ]
    exact pRank_centre_barO2_normalClosure_le_one_aux_rank Nat.prime_three
      (by rw [Subgroup.card_bot]; norm_num)

theorem pRank_centre_barO2_normalClosure_le_one (hT : LieOddRankTable) (hKSMAlt : KSMAlt)
    (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3) {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L)
    (h15 : Shape1515 L) :
    CFSG.Open.pRank 3 (Subgroup.center ↥(barO2 (Subgroup.normalClosure (L : Set X)))) ≤ 1 :=
  pRank_centre_barO2_normalClosure_le_one_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 hl.toGen h15

theorem xlevel_1521_S1_aux_inf {A J : Subgroup X} [J.Normal] (hA : IsElemAbelian 3 A)
    (h : A ⊓ J = ⊥) : barO2 A ⊓ barO2 J = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨a, haA, rfl⟩, ⟨j, hjJ, hja⟩⟩
  have hq : j⁻¹ * a ∈ CFSG.pCore 2 X := QuotientGroup.eq.1 hja
  obtain ⟨k, hk⟩ := pRank_barO2_eq_aux_powTwo hq
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hπ1 : (QuotientGroup.mk' J a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hπj : QuotientGroup.mk' J j = 1 := (QuotientGroup.eq_one_iff j).2 hjJ
  have hπq : QuotientGroup.mk' J a = QuotientGroup.mk' J (j⁻¹ * a) := by
    rw [map_mul, map_inv, hπj, inv_one, one_mul]
  have hπ2 : (QuotientGroup.mk' J a) ^ (2 ^ k) = 1 := by
    rw [hπq, ← map_pow, hk, map_one]
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hord : orderOf (QuotientGroup.mk' J a) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hπ1) (orderOf_dvd_of_pow_eq_one hπ2)
  have haJ : a ∈ J := (QuotientGroup.eq_one_iff a).1 (orderOf_eq_one_iff.1 hord)
  have ha1 : a ∈ A ⊓ J := ⟨haA, haJ⟩
  rw [h, Subgroup.mem_bot] at ha1
  rw [ha1, map_one]
  exact Subgroup.one_mem _

theorem xlevel_1521_S1_aux_rank_gen {T T₁ T₂ R A : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L) (hA : AConfig T R A)
    (hbot : A ⊓ Subgroup.normalClosure (L : Set X) = ⊥)
    (hbar : ⁅barO2 (Subgroup.normalClosure (L : Set X)), barO2 A⁆ = ⊥) :
    CFSG.Open.pRank 3 (Subgroup.normalClosure (L : Set X)) ≤ 1 := by
  haveI hJn : (Subgroup.normalClosure (L : Set X)).Normal := Subgroup.normalClosure_normal
  have hperm : ∀ a ∈ barO2 A, ∀ b ∈ barO2 (Subgroup.normalClosure (L : Set X)), a * b = b * a := by
    intro a ha b hb
    have hb' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbar hb
    exact (Subgroup.mem_centralizer_iff.1 hb') a ha
  have hcount := pRank_add_le_pRank_sup_add_pRank_inf hperm Nat.prime_three
  rw [xlevel_1521_S1_aux_inf hA.elemAbelian hbot] at hcount
  have h0 : CFSG.Open.pRank 3 (⊥ : Subgroup (X ⧸ CFSG.pCore 2 X)) = 0 :=
    pRank_eq_zero_of_not_dvd_s15 Nat.prime_three
      (by rw [Subgroup.card_bot]; exact Nat.prime_three.not_dvd_one)
  have h2A : 2 ≤ CFSG.Open.pRank 3 A :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hA.elemAbelian
      (by rw [hA.card_eq]; norm_num)
  have hAbar : 2 ≤ CFSG.Open.pRank 3 (barO2 A) := by
    rw [← pRank_barO2_eq_aux_eq A Nat.prime_three (by norm_num)]
    exact h2A
  have hsup3 : CFSG.Open.pRank 3 (barO2 A ⊔ barO2 (Subgroup.normalClosure (L : Set X))) ≤ 3 := by
    refine (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top).trans ?_
    have h1 := pRank_barO2_eq_aux_eq (⊤ : Subgroup X) Nat.prime_three (by norm_num)
    have htop : barO2 (⊤ : Subgroup X) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [htop] at h1
    rw [← h1]
    exact hl.rank_three
  have hJ1 : CFSG.Open.pRank 3 (barO2 (Subgroup.normalClosure (L : Set X))) ≤ 1 := by omega
  rw [pRank_barO2_eq_aux_eq _ Nat.prime_three (by norm_num)]
  exact hJ1

theorem xlevel_1521_S1_aux_rank {T T₁ T₂ R A : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) (hA : AConfig T R A)
    (hbot : A ⊓ Subgroup.normalClosure (L : Set X) = ⊥)
    (hbar : ⁅barO2 (Subgroup.normalClosure (L : Set X)), barO2 A⁆ = ⊥) :
    CFSG.Open.pRank 3 (Subgroup.normalClosure (L : Set X)) ≤ 1 :=
  xlevel_1521_S1_aux_rank_gen hl.toGen hA hbot hbar

theorem xlevel_1521_S1_aux_le_gen (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) {T T₁ T₂ R A : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L) (hA : AConfig T R A) (h15 : Shape1515 L)
    (hAJ : A ≤ Subgroup.normalClosure (L : Set X))
    (hbar : ⁅barO2 (Subgroup.normalClosure (L : Set X)), barO2 A⁆ = ⊥) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperm : ∀ a ∈ barO2 A, ∀ b ∈ barO2 (Subgroup.normalClosure (L : Set X)), a * b = b * a := by
    intro a ha b hb
    have hb' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbar hb
    exact (Subgroup.mem_centralizer_iff.1 hb') a ha
  have hAp : IsPGroup 3 A := IsPGroup.iff_card.2 ⟨2, by rw [hA.card_eq]; norm_num⟩
  have hbotA : A ⊓ CFSG.pCore 2 X = ⊥ :=
    CFSG.RankThree.PartTwo.Sec4.inf_eq_bot_of_isPGroup_of_not_dvd Nat.prime_three hAp
      (pRank_barO2_eq_aux_notDvdCard Nat.prime_three (by norm_num))
  let f : ↥A →* ↥(barO2 (Subgroup.normalClosure (L : Set X))) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 X)).comp A.subtype).codRestrict
      (barO2 (Subgroup.normalClosure (L : Set X))) (fun a => ⟨a, hAJ a.2, rfl⟩)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : (e : X) ∈ CFSG.pCore 2 X := by
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 X) (e : X) = 1 := congrArg Subtype.val he
      simpa [QuotientGroup.eq_one_iff] using h2
    have h2 : (e : X) ∈ A ⊓ CFSG.pCore 2 X := ⟨e.2, h1⟩
    rw [hbotA, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hrange : f.range ≤ Subgroup.center ↥(barO2 (Subgroup.normalClosure (L : Set X))) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hperm _ ⟨a, a.2, rfl⟩ g g.2).symm
  have hcomm : ∀ a b : ↥A, a * b = b * a := by
    haveI := hA.elemAbelian.1
    exact fun a b => mul_comm' a b
  have h2le : 2 ≤ CFSG.Open.pRank 3
      (Subgroup.center ↥(barO2 (Subgroup.normalClosure (L : Set X)))) :=
    CFSG.SectionRank.le_pRank_of_injective Nat.prime_three.one_lt hcomm
      (fun a => Subtype.ext (hA.elemAbelian.2 _ a.2)) (by rw [hA.card_eq]; norm_num) f hinj hrange
  have h1le := pRank_centre_barO2_normalClosure_le_one_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 hl h15
  omega

theorem xlevel_1521_S1_aux_le (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) {T T₁ T₂ R A : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) (hA : AConfig T R A) (h15 : Shape1515 L)
    (hAJ : A ≤ Subgroup.normalClosure (L : Set X))
    (hbar : ⁅barO2 (Subgroup.normalClosure (L : Set X)), barO2 A⁆ = ⊥) : False :=
  xlevel_1521_S1_aux_le_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 hl.toGen hA h15 hAJ hbar

theorem xlevel_1521_S1_gen (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) {T T₁ T₂ R A : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L) (hA : AConfig T R A) (h15 : Shape1515 L)
    (hcomm : ⁅gnImg T (Subgroup.normalClosure (L : Set X)), gnImg T A⁆ = ⊥) :
    L.Normal ∧ IsLThreeOdd ↥Ls := by
  haveI hJn : (Subgroup.normalClosure (L : Set X)).Normal := Subgroup.normalClosure_normal
  have hbar := commute_barO2_of_commute_star_gen hl hcomm
  have hbot : A ⊓ Subgroup.normalClosure (L : Set X) = ⊥ := by
    rcases hA.inf_eq_bot_or_le (K := Subgroup.normalClosure (L : Set X))
      Subgroup.le_normalizer_of_normal with hb | hle
    · exact hb
    · exact (xlevel_1521_S1_aux_le_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 hl hA h15 hle hbar).elim
  have hJ1 := xlevel_1521_S1_aux_rank_gen hl hA hbot hbar
  have hLJ : CFSG.Open.pRank 3 L ≤ 1 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt Subgroup.le_normalClosure).trans hJ1
  have hL1 : CFSG.Open.pRank 3 L = 1 :=
    le_antisymm hLJ (one_le_pRank_three_of_lift hl.good.three hl.comp hl.lift)
  have h3 : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 3 := hl.rank_L
  have hdat := rankDatum1512_of_ctx hT hl.gn hl.good.shape hl.comp hl.lift h3
  obtain ⟨hZ1, hshape⟩ := rankOneShape_of_datum hKSML3 hl.gn hl.comp.1 hl.lift hdat hL1
  have hs0 : CFSG.Open.pRank 3 (KFactsPair.centerIn (barO2 L)) = 0 :=
    pRank_eq_zero_of_not_dvd_s15 Nat.prime_three
      (by rw [card_centerIn_s15, hZ1]; exact Nat.prime_three.not_dvd_one)
  have hge := pRank_normalClosure_ge hl.lift.1 Nat.prime_three (by norm_num) hs0.le
  have hLeq : L = Subgroup.normalClosure (L : Set X) := by
    by_contra hne
    have h2 := two_le_ncard_of_ne_normalClosure hl.lift.1 hne
    rw [hL1] at hge
    simp only [mul_one, mul_zero, add_zero] at hge
    omega
  have hNormal : L.Normal := by
    have h := (Subgroup.normalClosure_normal (s := (L : Set X)))
    rw [← hLeq] at h
    exact h
  refine ⟨hNormal, ?_⟩
  obtain ⟨-, hdvd, -⟩ := centre_of_lift hl.gn hl.comp.1 hl.lift
  have hZLs : Subgroup.center ↥Ls = ⊥ :=
    Subgroup.card_eq_one.1 (Nat.dvd_one.1 (hZ1 ▸ hdvd))
  rcases hshape with ⟨m, d, Q, hodd, hm2, hQp, hQe, hd, ⟨e⟩, -⟩ | ⟨hL3, -⟩
  · exact ⟨m, hodd, Or.inr ⟨hm2, d, Q, hQp, hQe, hd, ⟨((QuotientGroup.quotientMulEquivOfEq hZLs).trans
      QuotientGroup.quotientBot).symm.trans e⟩⟩⟩
  · obtain ⟨f, hf, hker⟩ := barO2_centralExt hl.gn hl.comp.1 hl.lift
    have hZbot : Subgroup.center ↥(barO2 L) = ⊥ := Subgroup.card_eq_one.1 hZ1
    have hfinj : Function.Injective f :=
      (MonoidHom.ker_eq_bot_iff f).1 (le_bot_iff.1 (hker.trans hZbot.le))
    let eL : ↥(barO2 L) ≃* ↥Ls := MulEquiv.ofBijective f ⟨hfinj, hf⟩
    rcases hL3 with ⟨h1, d, q, hq, hd, ⟨e⟩⟩ | ⟨h, -⟩
    · exact ⟨1, odd_one, Or.inl ⟨h1, d, q, hq, hd, ⟨eL.symm.trans e⟩⟩⟩
    · omega

theorem xlevel_1521_S1 (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) {T T₁ T₂ R A : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) (hA : AConfig T R A) (h15 : Shape1515 L)
    (hcomm : ⁅gnImg T (Subgroup.normalClosure (L : Set X)), gnImg T A⁆ = ⊥) :
    L.Normal ∧ IsLThreeOdd ↥Ls :=
  xlevel_1521_S1_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 hl.toGen hA h15 hcomm

end CFSG.LocalAnalysis.RankThreeUC.S15
