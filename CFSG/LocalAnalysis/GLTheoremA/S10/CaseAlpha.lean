module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseU
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBetaK
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
public import CFSG.LocalAnalysis.GLTheoremA.PartI.BmaxCent
public import CFSG.LocalAnalysis.GLTheoremA.Prop51Core
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma105More

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure AlphaInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l105 : Lemma105Inputs G p
  i1428 : I1428At G
  i266 : I266At G
  i112 : I112NormAt G
  i1015two : I1015twoAt G
  i263 : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G
  i158 : I158AtK G
  out : OutCyclicAt G p
  iso : InnDiagIsoAt G p
  i148f : I148fiveAt G
  i112one : I112OneAt G
  multa : MultAlphaAt G
  i91u6 : I91U6At G
  fieldpow : FieldAutPowClosedAt
  l2cent : L2CentAt G
  i1015cover : I1015coverAt G
  i1015four62 : I1015fourU62At G
  u62t9 : U62Type9At G
  u33 : U33SolvCentAt G
  fu6exp : FieldU6ExpAt G
  g2c : G2CentrelessAt

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

abbrev Kf (p : ℕ) (K F : Subgroup G) : Subgroup G := closureIn K (GLAPLayer p (cs F))

structure AlphaCtx (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b a : G) :
    Prop where
  c105 : Concl105 G p B x L b
  mem : a ∈ Dgrp b x
  not_x : a ∉ Subgroup.zpowers x
  lt : ¬ (Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a) = Jpart p (Ipart p L b) a)
  c104 : Concl104 p B x L b a
  d5 : dLevel G p = 5
  caseA : CaseA p B x L b

structure AlphaBase (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b a : G) (E₀ F : Subgroup G) : Prop where
  E₀_B : E₀ ≤ B
  E₀_el : IsElemAbelian p E₀
  D_E₀ : Dgrp b x ≤ E₀
  E₀_layer : GLAPLayer p (L ⊓ cs E₀) ≠ ⊥
  E₀_max : ∀ E' : Subgroup G, E' ≤ B → IsElemAbelian p E' → Dgrp b x ≤ E' → GLAPLayer p (L ⊓ cs E') ≠ ⊥ →
    Nat.card E' ≤ Nat.card E₀
  E₀_card : p ^ 3 ≤ Nat.card E₀
  F_E₀ : F ≤ E₀
  F_innL : InnDiagOn p F L
  F_innJ : InnDiagOn p F (Jpart p (Ipart p L b) a)
  F_inf : F ⊓ Dgrp b x = ⊥
  F_sup : F ⊔ Dgrp b x = E₀

structure AlphaData (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b a : G) (E₀ F : Subgroup G) (y : G)
    (E K : Subgroup G) : Prop extends AlphaBase p B x L b a E₀ F where
  y_F : y ∈ F
  y_ne : y ≠ 1
  y_ess : (∃ z ∈ F, z ≠ 1 ∧ IsEssential p B z) → IsEssential p B y
  E_def : E = Dgrp b x ⊔ Subgroup.zpowers y
  E_card : Nat.card E = p ^ 3
  K_comp : GLAPComponent p (L ⊓ cs E) K
  K_G2 : p = 3 → ∀ n : ℕ, catalogIs (PSimple 3 (Ipart p L b)) (isG2n n) → catalogIs (PSimple 3 K) (isL2n n)
  K_U6 : p = 3 → ∀ m k : ℕ, 3 ≤ m → Odd m → catalogIs (PSimple 3 (Jpart p (Ipart p L b) a)) (isU6n m) →
    ¬ catalogIs (PSimple 3 K) (isL2n k)

structure AlphaKData (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b a : G) (y : G) (E K : Subgroup G) :
    Prop where
  y_B : y ∈ B
  y_ne : y ≠ 1
  y_inn : InnDiagOn p (Subgroup.zpowers y) (Jpart p (Ipart p L b) a)
  E_def : E = Dgrp b x ⊔ Subgroup.zpowers y
  E_B : E ≤ B
  K_comp : GLAPComponent p (L ⊓ cs E) K
  K_G2 : p = 3 → ∀ n : ℕ, catalogIs (PSimple 3 (Ipart p L b)) (isG2n n) → catalogIs (PSimple 3 K) (isL2n n)
  K_U6 : p = 3 → ∀ m k : ℕ, 3 ≤ m → Odd m → catalogIs (PSimple 3 (Jpart p (Ipart p L b) a)) (isU6n m) →
    ¬ catalogIs (PSimple 3 K) (isL2n k)

theorem AlphaData.toK {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G} {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) : AlphaKData p B x L b a y E K :=
  ⟨hd.E₀_B (hd.F_E₀ hd.y_F), hd.y_ne, innDiagOn_mono hd.F_innJ (Subgroup.zpowers_le.2 hd.y_F), hd.E_def, by
    rw [hd.E_def]
    exact sup_le (hd.D_E₀.trans hd.E₀_B) (Subgroup.zpowers_le.2 (hd.E₀_B (hd.F_E₀ hd.y_F))),
    hd.K_comp, hd.K_G2, hd.K_U6⟩

theorem alpha_E0 {B : Subgroup G} {x : G} {L : Subgroup G} {b : G} (hA : CaseA p B x L b) :
    ∃ E₀ : Subgroup G, E₀ ≤ B ∧ IsElemAbelian p E₀ ∧ Dgrp b x ≤ E₀ ∧ GLAPLayer p (L ⊓ cs E₀) ≠ ⊥ ∧
      (∀ E' : Subgroup G, E' ≤ B → IsElemAbelian p E' → Dgrp b x ≤ E' → GLAPLayer p (L ⊓ cs E') ≠ ⊥ →
        Nat.card E' ≤ Nat.card E₀) ∧ p ^ 3 ≤ Nat.card E₀ := by
  classical
  obtain ⟨E, hEB, hEel, hEcard, hDE, hEne⟩ := hA
  obtain ⟨E₀, ⟨hE₀B, hE₀el, hDE₀, hE₀ne⟩, hmax⟩ := Set.exists_max_image
    {E' : Subgroup G | E' ≤ B ∧ IsElemAbelian p E' ∧ Dgrp b x ≤ E' ∧ GLAPLayer p (L ⊓ cs E') ≠ ⊥}
    (fun E' => Nat.card E') (Set.toFinite _) ⟨E, hEB, hEel, hDE, hEne⟩
  refine ⟨E₀, hE₀B, hE₀el, hDE₀, hE₀ne, fun E' h1 h2 h3 h4 => hmax E' ⟨h1, h2, h3, h4⟩, ?_⟩
  have := hmax E ⟨hEB, hEel, hDE, hEne⟩
  simp only [hEcard] at this
  exact this

private theorem caseAlpha_card_eq_mul {p : ℕ} (hp : p.Prime) {E A : Subgroup G}
    (hel : IsElemAbelian p E) (hAE : A ≤ E) (hle : Nat.card E ≤ p * Nat.card A) (hne : A ≠ E) :
    Nat.card E = p * Nat.card A := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hel).exists_card_eq
  have hdvd : Nat.card A ∣ p ^ k := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le hAE
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hlt : Nat.card A < Nat.card E := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hAE) fun he => hne ?_
    exact Subgroup.eq_of_le_of_card_ge hAE (le_of_eq he.symm)
  have hjk : j < k := by
    rw [hj, hk] at hlt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
  apply le_antisymm hle
  calc p * Nat.card A = p ^ (j + 1) := by rw [hj, pow_succ']
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hjk
    _ = Nat.card E := hk.symm

private theorem caseAlpha_inf_eq_zpowers {p : ℕ} (hp : p.Prime) {E A D : Subgroup G} {a : G}
    (hel : IsElemAbelian p E) (hAE : A ≤ E) (hDE : D ≤ E) (hDc : Nat.card D = p ^ 2)
    (hEA : Nat.card E = p * Nat.card A) (hDA : ¬ D ≤ A) (haA : a ∈ A) (haD : a ∈ D) (ha1 : a ≠ 1) :
    A ⊓ D = Subgroup.zpowers a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hnorm : D ≤ Subgroup.normalizer (A : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh =>
      (isElemAbelian_commute hel (hDE hg) (hAE hh)).symm)
  have hsup : A ⊔ D = E := by
    obtain ⟨q, hq⟩ := Subgroup.card_dvd_of_le (le_sup_left : A ≤ A ⊔ D)
    have h1 : Nat.card (A ⊔ D : Subgroup G) ∣ Nat.card E :=
      Subgroup.card_dvd_of_le (sup_le hAE hDE)
    rw [hEA, hq, mul_comm p] at h1
    have hqd : q ∣ p := Nat.dvd_of_mul_dvd_mul_left hApos h1
    have hqp : q = p := by
      rcases (Nat.dvd_prime hp).1 hqd with h | h
      · exfalso
        apply hDA
        have hAeq : A = A ⊔ D :=
          Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hq, h, mul_one])
        rw [hAeq]
        exact le_sup_right
      · exact h
    apply Subgroup.eq_of_le_of_card_ge (sup_le hAE hDE)
    rw [hEA, hq, hqp]
    exact (mul_comm _ _).le
  have hinf : Nat.card (A ⊓ D : Subgroup G) = p := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hsup, hEA, hDc] at h1
    have h2 : (p * Nat.card A) * Nat.card (A ⊓ D : Subgroup G) = (p * Nat.card A) * p := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos hApos) h2
  have hle : Subgroup.zpowers a ≤ A ⊓ D :=
    le_inf (Subgroup.zpowers_le.2 haA) (Subgroup.zpowers_le.2 haD)
  have hord : orderOf a = p := orderOf_eq_prime (hel.2 a (hAE haA)) ha1
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hinf])).symm

theorem alpha_Dx (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) {E₀ : Subgroup G} (hE₀B : E₀ ≤ B) (hE₀el : IsElemAbelian p E₀)
    (hDE₀ : Dgrp b x ≤ E₀) :
    ∃ Dx : Subgroup G, Dx ≤ E₀ ∧ InnDiagOn p Dx L ∧ Nat.card E₀ = p * Nat.card Dx ∧
      Dx ⊓ Dgrp b x = Subgroup.zpowers x := by
  have hp : p.Prime := hc.ctx.prime
  have hS := sstar_triple h.star
  have hLc : GLAPComponent p (cx x) L := hS.2.2
  have hchev : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc h.star
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := sstar_norm h.star hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  obtain ⟨-, -, hDc⟩ := dgrp_facts hc h
  obtain ⟨A₀, hA₀E, hA₀inn, hcardA, hmem⟩ :=
    hin.out B x L E₀ hS
      (isKGroup_of_isKProper hc.ctx.kProper
        (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1))
      hchev (sstar_norm h.star) hE₀B
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hbN : NonInnDiag p b L := by
    have hpr : FieldOn p b L ∨ (p = 3 ∧ IsTD4 3 L ∧ NonInner 3 b L) := h.prop
    rcases hpr with hF | ⟨h3, hT, hNI⟩
    · exact hin.l105.l103.aut.field_nonInnDiag _ L b hLc hchev hF
    · subst h3
      exact hin.l105.l103.aut.td4_nonInnDiag _ L b hLc hT hNI
  have hbA : b ∉ A₀ := fun hb => hbN.2 (innDiagOn_mono hA₀inn (Subgroup.zpowers_le.2 hb))
  have hneq : A₀ ≠ E₀ := fun he => hbA (by rw [he]; exact hDE₀ hbD)
  have hEA : Nat.card E₀ = p * Nat.card A₀ :=
    caseAlpha_card_eq_mul hp hE₀el hA₀E hcardA hneq
  have hxinn : InnDiagOn p (Subgroup.zpowers x) L :=
    hin.l105.l103.aut.inner_innDiag (cx x) L x hLc hchev hxN
      (inducesInnerMod_of_centMod (centMod_zpowers_of_le hLc.1 (Subgroup.mem_zpowers x)))
  have hxA : x ∈ A₀ := hmem x (hDE₀ hxD) hxinn
  have hDA : ¬ Dgrp b x ≤ A₀ := fun hle => hbA (hle hbD)
  exact ⟨A₀, hA₀E, hA₀inn, hEA, caseAlpha_inf_eq_zpowers hp hE₀el hA₀E hDE₀ hDc hEA hDA hxA hxD hx1⟩

theorem alpha_Da (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G}
    (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ : Subgroup G} (hE₀B : E₀ ≤ B)
    (hE₀el : IsElemAbelian p E₀) (hDE₀ : Dgrp b x ≤ E₀) :
    ∃ Da : Subgroup G, Da ≤ E₀ ∧ InnDiagOn p Da (Jpart p (Ipart p L b) a) ∧
      Nat.card E₀ = p * Nat.card Da ∧ Da ⊓ Dgrp b x = Subgroup.zpowers a := by
  have hp : p.Prime := hc.ctx.prime
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have hcs := ac.c105.single a ha ha1
  have hJc : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a) := hcs.1
  have hChev : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a)) := ac.c104.1.2
  have hIST : IsSTriple p B a (Jpart p (Ipart p L b) a) := ac.c104.1.1
  have haB : a ∈ B := (ac.c105.essential a ha ha1).1
  have hBN : B ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    hcs.2 _ hJc ⟨MulEquiv.refl _⟩
  obtain ⟨-, -, hDc⟩ := dgrp_facts hc h
  obtain ⟨Da₀, hDaE, hDainn, hcardDa, hmem⟩ :=
    hin.out B a (Jpart p (Ipart p L b) a) E₀ hIST
      (isKGroup_of_isKProper hc.ctx.kProper
        (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha1))
      hChev hBN hE₀B
  obtain ⟨d, hdD, hdN⟩ : ∃ d ∈ Dgrp b x, NonInnDiag p d (Jpart p (Ipart p L b) a) := by
    rcases ac.c104.2 with ⟨d, hd, hF⟩ | ⟨h3, hT, ⟨d, hd, hNI⟩, -⟩
    · exact ⟨d, hd, hin.l105.l103.aut.field_nonInnDiag _ _ d hJc hChev hF⟩
    · subst h3
      exact ⟨d, hd, hin.l105.l103.aut.td4_nonInnDiag _ _ d hJc hT hNI⟩
  have hdA : d ∉ Da₀ := fun hd => hdN.2 (innDiagOn_mono hDainn (Subgroup.zpowers_le.2 hd))
  have hneq : Da₀ ≠ E₀ := fun he => hdA (by rw [he]; exact hDE₀ hdD)
  have hEA : Nat.card E₀ = p * Nat.card Da₀ :=
    caseAlpha_card_eq_mul hp hE₀el hDaE hcardDa hneq
  have haInn : InnDiagOn p (Subgroup.zpowers a) (Jpart p (Ipart p L b) a) :=
    hin.l105.l103.aut.inner_innDiag (cx a) _ a hJc hChev (hBN haB)
      (inducesInnerMod_of_centMod (centMod_zpowers_of_le (Jpart_le_cx h ha) (Subgroup.mem_zpowers a)))
  have haA : a ∈ Da₀ := hmem a (hDE₀ ha) haInn
  have hDA : ¬ Dgrp b x ≤ Da₀ := fun hle => hdA (hle hdD)
  exact ⟨Da₀, hDaE, hDainn, hEA, caseAlpha_inf_eq_zpowers hp hE₀el hDaE hDE₀ hDc hEA hDA haA ha ha1⟩

private theorem casealpha_zpowers_eq {p : ℕ} (hp : p.Prime) {g x : G} (hxo : orderOf x = p)
    (hgp : g ^ p = 1) (hg : g ∈ Subgroup.zpowers x) (hg1 : g ≠ 1) :
    Subgroup.zpowers g = Subgroup.zpowers x := by
  have hgo : orderOf g = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hgp) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hg)
  rw [Nat.card_zpowers, Nat.card_zpowers, hgo, hxo]

private theorem casealpha_zpowers_inf_eq_bot {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hel : IsElemAbelian p E) {x a : G} (hxE : x ∈ E) (haE : a ∈ E)
    (hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a) :
    Subgroup.zpowers x ⊓ Subgroup.zpowers a = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  rintro g ⟨h1, h2⟩
  rw [Subgroup.mem_bot]
  by_contra hg1
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hg1
    simpa using h1
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hg1
    simpa using h2
  have hgE : g ∈ E := Subgroup.zpowers_le.2 hxE h1
  have hgp : g ^ p = 1 := hel.2 g hgE
  have e1 : Subgroup.zpowers g = Subgroup.zpowers x :=
    casealpha_zpowers_eq hp (orderOf_eq_prime (hel.2 x hxE) hx1) hgp h1 hg1
  have e2 : Subgroup.zpowers g = Subgroup.zpowers a :=
    casealpha_zpowers_eq hp (orderOf_eq_prime (hel.2 a haE) ha1) hgp h2 hg1
  exact hxa (e1.symm.trans e2)

theorem hyperplanes_complement {p : ℕ} (hp : p.Prime) {E₀ Dx Da D : Subgroup G} {x a : G}
    (hel : IsElemAbelian p E₀) (hDx : Dx ≤ E₀) (hDa : Da ≤ E₀) (hD : D ≤ E₀) (hDcard : Nat.card D = p ^ 2)
    (hxc : Nat.card E₀ = p * Nat.card Dx) (hac : Nat.card E₀ = p * Nat.card Da)
    (hx : Dx ⊓ D = Subgroup.zpowers x) (ha : Da ⊓ D = Subgroup.zpowers a)
    (hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a) :
    Dx ⊓ Da ⊓ D = ⊥ ∧ Dx ⊓ Da ⊔ D = E₀ := by
  have hnorm : ∀ {A B : Subgroup G}, A ≤ E₀ → B ≤ E₀ → B ≤ Subgroup.normalizer (A : Set G) :=
    fun hA hB g hg => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2
      fun h hh => (isElemAbelian_commute hel (hB hg) (hA hh)).symm)
  have hxD : x ∈ D := by
    have h : x ∈ Dx ⊓ D := by rw [hx]; exact Subgroup.mem_zpowers x
    exact h.2
  have haD : a ∈ D := by
    have h : a ∈ Da ⊓ D := by rw [ha]; exact Subgroup.mem_zpowers a
    exact h.2
  have hI : Dx ⊓ Da ⊓ D = ⊥ := by
    rw [inf_inf_distrib_right, hx, ha]
    exact casealpha_zpowers_inf_eq_bot hp hel (hD hxD) (hD haD) hxa
  refine ⟨hI, ?_⟩
  have hIle : Dx ⊓ Da ≤ E₀ := inf_le_of_left_le hDx
  have hDxpos : 0 < Nat.card Dx := Nat.card_pos
  have hDa_eq : Nat.card Da = Nat.card Dx := by
    have h := hxc.symm.trans hac
    exact (Nat.eq_of_mul_eq_mul_left hp.pos h).symm
  have F1 : Nat.card (Dx ⊔ Da : Subgroup G) * Nat.card (Dx ⊓ Da : Subgroup G) = Nat.card Dx * Nat.card Da :=
    card_sup_mul_card_inf_of_le_normalizer (hnorm hDx hDa)
  have F2 : Nat.card (Dx ⊓ Da ⊔ D : Subgroup G) * Nat.card (Dx ⊓ Da ⊓ D : Subgroup G) = Nat.card (Dx ⊓ Da : Subgroup G) * Nat.card D :=
    card_sup_mul_card_inf_of_le_normalizer (hnorm hIle hD)
  rw [hI, Subgroup.card_bot, hDcard, mul_one] at F2
  have hM : Nat.card (Dx ⊔ Da : Subgroup G) ≤ p * Nat.card Dx :=
    hxc ▸ Subgroup.card_le_of_le (sup_le hDx hDa)
  have hS : Nat.card (Dx ⊓ Da ⊔ D : Subgroup G) ≤ p * Nat.card Dx :=
    hxc ▸ Subgroup.card_le_of_le (sup_le hIle hD)
  have hA : Nat.card Dx ≤ p * Nat.card (Dx ⊓ Da : Subgroup G) := by
    have h : Nat.card Dx * Nat.card Dx ≤ Nat.card Dx * (p * Nat.card (Dx ⊓ Da : Subgroup G)) := by
      calc Nat.card Dx * Nat.card Dx = Nat.card (Dx ⊔ Da : Subgroup G) * Nat.card (Dx ⊓ Da : Subgroup G) := by
            rw [F1, hDa_eq]
        _ ≤ (p * Nat.card Dx) * Nat.card (Dx ⊓ Da : Subgroup G) := Nat.mul_le_mul_right _ hM
        _ = Nat.card Dx * (p * Nat.card (Dx ⊓ Da : Subgroup G)) := by ring
    exact Nat.le_of_mul_le_mul_left h hDxpos
  have hB : p * Nat.card (Dx ⊓ Da : Subgroup G) ≤ Nat.card Dx := by
    have h : p * (p * Nat.card (Dx ⊓ Da : Subgroup G)) ≤ p * Nat.card Dx := by
      calc p * (p * Nat.card (Dx ⊓ Da : Subgroup G)) = Nat.card (Dx ⊓ Da : Subgroup G) * p ^ 2 := by ring
        _ = Nat.card (Dx ⊓ Da ⊔ D : Subgroup G) := F2.symm
        _ ≤ p * Nat.card Dx := hS
    exact Nat.le_of_mul_le_mul_left h hp.pos
  have hpI : p * Nat.card (Dx ⊓ Da : Subgroup G) = Nat.card Dx := le_antisymm hB hA
  refine Subgroup.eq_of_le_of_card_ge (sup_le hIle hD) ?_
  rw [hxc, ← hpI]
  have h2 : p * (p * Nat.card (Dx ⊓ Da : Subgroup G)) = Nat.card (Dx ⊓ Da ⊔ D : Subgroup G) := by
    calc p * (p * Nat.card (Dx ⊓ Da : Subgroup G)) = Nat.card (Dx ⊓ Da : Subgroup G) * p ^ 2 := by ring
      _ = Nat.card (Dx ⊓ Da ⊔ D : Subgroup G) := F2.symm
  exact le_of_eq h2

theorem alpha_F (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b a : G}
    (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ : Subgroup G} (hE₀B : E₀ ≤ B)
    (hE₀el : IsElemAbelian p E₀) (hDE₀ : Dgrp b x ≤ E₀) (hE₀l : GLAPLayer p (L ⊓ cs E₀) ≠ ⊥) :
    ∃ F : Subgroup G, F ≤ E₀ ∧ InnDiagOn p F L ∧ InnDiagOn p F (Jpart p (Ipart p L b) a) ∧
      F ⊓ Dgrp b x = ⊥ ∧ F ⊔ Dgrp b x = E₀ := by
  obtain ⟨Dx, hDxE, hDxL, hDxc, hDxD⟩ := alpha_Dx hc hin h hE₀B hE₀el hDE₀
  obtain ⟨Da, hDaE, hDaJ, hDac, hDaD⟩ := alpha_Da hc hin h ac hE₀B hE₀el hDE₀
  have hS := sstar_triple h.star
  obtain ⟨-, -, hDcard⟩ := card_Dgrp hS.1.1 hc.ctx.prime h.mem hS.2.1.1 hS.2.1.2.1 h.not_mem
  have hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a := fun he =>
    ac.not_x (he ▸ Subgroup.mem_zpowers a)
  obtain ⟨h1, h2⟩ := hyperplanes_complement hc.ctx.prime hE₀el hDxE hDaE hDE₀ hDcard hDxc hDac hDxD hDaD hxa
  exact ⟨Dx ⊓ Da, inf_le_left.trans hDxE, innDiagOn_mono hDxL inf_le_left,
    innDiagOn_mono hDaJ inf_le_right, h1, h2⟩

theorem alpha_base (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) :
    ∃ E₀ F : Subgroup G, AlphaBase p B x L b a E₀ F := by
  obtain ⟨E₀, hB, hel, hD, hl, hmax, hcard⟩ := alpha_E0 ac.caseA
  obtain ⟨F, hFE, hFL, hFJ, hF1, hF2⟩ := alpha_F hc hin h ac hB hel hD hl
  exact ⟨E₀, F, ⟨hB, hel, hD, hl, hmax, hcard, hFE, hFL, hFJ, hF1, hF2⟩⟩

private theorem casealpha_mem_centralizer_iff (T : Subgroup G) (g : G) :
    g ∈ Subgroup.centralizer (T : Set G) ↔ T ≤ cx g := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hg t ht
    exact Subgroup.mem_centralizer_singleton_iff.2 (hg t ht)
  · intro hT t ht
    exact Subgroup.mem_centralizer_singleton_iff.1 (hT ht)

private theorem alpha_conj_mem_cx {b e g : G} (he : e * b = b * e) (hg : g * b = b * g) :
    (e * g * e⁻¹) * b = b * (e * g * e⁻¹) := by
  have he' : e⁻¹ * b = b * e⁻¹ := by
    calc e⁻¹ * b = e⁻¹ * (b * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * b) * e⁻¹ := by rw [he]
      _ = b * e⁻¹ := by group
  calc e * g * e⁻¹ * b = e * g * (e⁻¹ * b) := by group
    _ = e * g * (b * e⁻¹) := by rw [he']
    _ = e * (g * b) * e⁻¹ := by group
    _ = e * (b * g) * e⁻¹ := by rw [hg]
    _ = (e * b) * g * e⁻¹ := by group
    _ = (b * e) * g * e⁻¹ := by rw [he]
    _ = b * (e * g * e⁻¹) := by group

private theorem alpha_normalizer_inf_cx {X : Subgroup G} {b e : G}
    (he : e ∈ Subgroup.normalizer (X : Set G)) (hcomm : e * b = b * e) :
    e ∈ Subgroup.normalizer ((X ⊓ cx b : Subgroup G) : Set G) := by
  have he' : e⁻¹ * b = b * e⁻¹ := by
    calc e⁻¹ * b = e⁻¹ * (b * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * b) * e⁻¹ := by rw [hcomm]
      _ = b * e⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hX : g ∈ X ↔ e * g * e⁻¹ ∈ X := Subgroup.mem_normalizer_iff.1 he g
  have hC : g ∈ cx b ↔ e * g * e⁻¹ ∈ cx b := by
    simp only [cx, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨alpha_conj_mem_cx hcomm, fun h => ?_⟩
    have := alpha_conj_mem_cx he' h
    rwa [show e⁻¹ * (e * g * e⁻¹) * e⁻¹⁻¹ = g by group] at this
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX, hC]

theorem alpha_E0_eq_IsE0 (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) :
    (∀ E' : Subgroup G, Dgrp b x ≤ E' → E' ≤ B →
      (GLAPLayer 3 (L ⊓ cs E') ≠ ⊥ ↔ GLAPLayer 3 (Ipart 3 L b ⊓ cs E') ≠ ⊥)) ∧
    ∀ E : Subgroup G, IsE0 B (Ipart 3 L b) E → Dgrp b x ≤ E ∧
      (∀ E' : Subgroup G, E' ≤ B → IsElemAbelian 3 E' → Dgrp b x ≤ E' → GLAPLayer 3 (L ⊓ cs E') ≠ ⊥ →
        Nat.card E' ≤ Nat.card E) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hLB : LBalanceAt G 3 := hin.l105.lbal
  have hBel : IsElemAbelian 3 B := B_el h
  obtain ⟨hDB, -, -⟩ := dgrp_facts hc h
  have hLc : GLAPComponent 3 (cx x) L := (sstar_triple h.star).2.2
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hbB : b ∈ B := h.mem
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hIL : Ipart 3 L b ≤ L := (layer_le 3 _).trans inf_le_left
  have hcs_le : ∀ E' : Subgroup G, Dgrp b x ≤ E' → cs E' ≤ cx b := fun E' hD =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 (hD hbD)))
  have hEx : ∀ E' : Subgroup G, E' ≤ B → E' ≤ cx x := fun E' hE' e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel (hE' he) hxB)
  have hEN : ∀ E' : Subgroup G, E' ≤ B → E' ≤ Subgroup.normalizer ((L ⊓ cx b : Subgroup G) : Set G) :=
    fun E' hE' e he => alpha_normalizer_inf_cx (sstar_norm h.star (hE' he))
      (isElemAbelian_commute hBel (hE' he) hbB)
  have hIsub : ∀ E' : Subgroup G, Dgrp b x ≤ E' → E' ≤ B →
      IsSubnormal (Ipart 3 L b ⊓ cs E') (L ⊓ cs E') := by
    intro E' hD hE'B
    refine IsSubnormal.step (inf_le_inf_right _ hIL) ?_ (IsSubnormal.refl _)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgX : (g : G) ∈ L ⊓ cx b := ⟨g.2.1, hcs_le E' hD g.2.2⟩
    have hgN : (g : G) ∈ Subgroup.normalizer (GLAPLayer 3 (L ⊓ cx b) : Set G) :=
      mem_normalizer_glaPLayer (Subgroup.le_normalizer hgX)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨(Subgroup.mem_normalizer_iff.1 hgN (n : G)).1 hn.1, ?_⟩
    exact (cs E').mul_mem ((cs E').mul_mem g.2.2 hn.2) ((cs E').inv_mem g.2.2)
  have hIsubL : ∀ E' : Subgroup G, Dgrp b x ≤ E' → E' ≤ B →
      GLAPLayer 3 (Ipart 3 L b ⊓ cs E') ≤ GLAPLayer 3 (L ⊓ cs E') := fun E' hD hE'B =>
    glaPLayer_le_of_isSubnormal hp (hIsub E' hD hE'B)
  have hLI : ∀ E' : Subgroup G, Dgrp b x ≤ E' → E' ≤ B →
      GLAPLayer 3 (L ⊓ cs E') ≤ GLAPLayer 3 (Ipart 3 L b ⊓ cs E') := by
    intro E' hD hE'B
    have hP : IsPGroup 3 E' := isPGroup_of_isElemAbelian (isElemAbelian_mono hBel hE'B)
    have hK : CFSG.Open.IsKGroup ↥((L ⊓ cx b) ⊔ E') := by
      refine isKGroup_of_isKProper hc.ctx.kProper (fun e => hCx (top_le_iff.1 ?_))
      rw [← e]
      exact sup_le ((inf_le_left.trans hLc.1)) (hEx E' hE'B)
    have hA : GLAPLayer 3 (L ⊓ cs E') ≤ Ipart 3 L b := by
      have e1 : (L ⊓ cx b) ⊓ cs E' = L ⊓ cs E' := by
        rw [inf_assoc, inf_eq_right.2 (hcs_le E' hD)]
      have := glaPLayer_inf_centralizer_le hp hLB hK hP (hEN E' hE'B)
      rwa [e1] at this
    unfold GLAPLayer
    refine sSup_le fun K hKc => le_sSup ?_
    have hKI : K ≤ Ipart 3 L b ⊓ cs E' :=
      le_inf ((le_sSup hKc : K ≤ GLAPLayer 3 (L ⊓ cs E')).trans hA) (hKc.1.trans inf_le_right)
    exact glaPComponent_of_le hp hKc hKI (inf_le_inf_right _ hIL)
  have hiff : ∀ E' : Subgroup G, Dgrp b x ≤ E' → E' ≤ B →
      (GLAPLayer 3 (L ⊓ cs E') ≠ ⊥ ↔ GLAPLayer 3 (Ipart 3 L b ⊓ cs E') ≠ ⊥) := fun E' hD hE'B =>
    ⟨fun hne hbot => hne (le_bot_iff.1 ((hLI E' hD hE'B).trans (le_of_eq hbot))),
      fun hne hbot => hne (le_bot_iff.1 ((hIsubL E' hD hE'B).trans (le_of_eq hbot)))⟩
  refine ⟨hiff, fun E hE => ?_⟩
  obtain ⟨hEB, hEne, hmax⟩ := hE
  have hI_cD : ∀ g ∈ Ipart 3 L b, Dgrp b x ≤ cx g := fun g hg =>
    (casealpha_mem_centralizer_iff _ g).1 (Ipart_le_cs h hg)
  have hEq : Ipart 3 L b ⊓ cs (E ⊔ Dgrp b x) = Ipart 3 L b ⊓ cs E := by
    refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))) ?_
    intro g hg
    obtain ⟨hgI, hgE⟩ := hg
    refine ⟨hgI, ?_⟩
    have hgE' : E ≤ cx g := (casealpha_mem_centralizer_iff E g).1 hgE
    exact (casealpha_mem_centralizer_iff _ g).2 (sup_le hgE' (hI_cD g hgI))
  have hne' : GLAPLayer 3 (Ipart 3 L b ⊓ cs (E ⊔ Dgrp b x)) ≠ ⊥ := by
    rw [hEq]
    exact hEne
  have hcard := hmax (E ⊔ Dgrp b x) (sup_le hEB hDB) hne'
  have heq : E = E ⊔ Dgrp b x := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  refine ⟨?_, fun E' hE'B _ hD hLne => hmax E' hE'B ((hiff E' hD hE'B).1 hLne)⟩
  rw [heq]
  exact le_sup_right

theorem alpha_split_F {p : ℕ} (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) {E₀ F : Subgroup G} (hE₀B : E₀ ≤ B) (hF1 : F ⊓ Dgrp b x = ⊥)
    (hF2 : F ⊔ Dgrp b x = E₀) {y₀ : G} (hy₀ : y₀ ∈ E₀) (hy₀D : y₀ ∉ Dgrp b x) :
    ∃ f ∈ F, f ≠ 1 ∧ ∃ d ∈ Dgrp b x, y₀ = f * d ∧ Ipart p L b ⊓ cx y₀ = Ipart p L b ⊓ cx f ∧
      Dgrp b x ⊔ Subgroup.zpowers f = Dgrp b x ⊔ Subgroup.zpowers y₀ := by
  have hBel : IsElemAbelian p B := B_el h
  obtain ⟨hDB, -, -⟩ := dgrp_facts hc h
  have hFB : F ≤ B := (le_sup_left : F ≤ F ⊔ Dgrp b x).trans (hF2 ▸ hE₀B)
  have hFN : F ≤ Subgroup.normalizer (Dgrp b x : Set G) := fun f hf =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
      isElemAbelian_commute hBel (hDB hd) (hFB hf))
  have hmem : y₀ ∈ (↑(F ⊔ Dgrp b x) : Set G) := by rw [hF2]; exact hy₀
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hFN] at hmem
  obtain ⟨f, hf, d, hd, hfd⟩ := Set.mem_mul.1 hmem
  have hf1 : f ≠ 1 := by
    intro h1
    apply hy₀D
    rw [← hfd, h1, one_mul]
    exact hd
  refine ⟨f, hf, hf1, d, hd, hfd.symm, ?_, ?_⟩
  · ext g
    simp only [Subgroup.mem_inf]
    have hgd : ∀ {g : G}, g ∈ Ipart p L b → g * d = d * g := fun hg =>
      Subgroup.mem_centralizer_singleton_iff.1 (Ipart_le_cx h hd hg)
    constructor
    · rintro ⟨hgI, hg⟩
      refine ⟨hgI, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 hg
      rw [← hfd] at h1
      have h2 : g * f * d = f * g * d := by
        calc g * f * d = g * (f * d) := by rw [mul_assoc]
          _ = f * d * g := h1
          _ = f * (d * g) := by rw [mul_assoc]
          _ = f * (g * d) := by rw [hgd hgI]
          _ = f * g * d := by rw [mul_assoc]
      exact mul_right_cancel h2
    · rintro ⟨hgI, hg⟩
      refine ⟨hgI, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 hg
      rw [← hfd]
      calc g * (f * d) = g * f * d := by rw [mul_assoc]
        _ = f * g * d := by rw [h1]
        _ = f * (g * d) := by rw [mul_assoc]
        _ = f * (d * g) := by rw [hgd hgI]
        _ = f * d * g := by rw [mul_assoc]
  · apply le_antisymm
    · refine sup_le le_sup_left (Subgroup.zpowers_le.2 ?_)
      have : f = y₀ * d⁻¹ := by rw [← hfd]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y₀))
        (Subgroup.mem_sup_left (Subgroup.inv_mem _ hd))
    · refine sup_le le_sup_left (Subgroup.zpowers_le.2 ?_)
      rw [← hfd]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers f)) (Subgroup.mem_sup_left hd)

private theorem alpha_card_le_center_pquot {I H : Subgroup G} (hHI : H ≤ I)
    (hcomm : ∀ h ∈ H, ∀ i ∈ I, h * i = i * h) (hH3 : ∀ h ∈ H, h ^ 3 = 1) :
    Nat.card H ≤ Nat.card (Subgroup.center (PQuot 3 I)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥I)) := CFSG.pPrimeCore_coprime_card
  have hn3 : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥I) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  set H' : Subgroup ↥I := H.subgroupOf I with hH'
  have hcardH : Nat.card H' = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHI).toEquiv
  have hcent : ∀ h : ↥I, h ∈ H' → (QuotientGroup.mk h : PQuot 3 I) ∈ Subgroup.center (PQuot 3 I) := by
    intro h hh
    have hhH : (h : G) ∈ H := hh
    rw [Subgroup.mem_center_iff]
    intro q
    refine QuotientGroup.induction_on q (fun g => ?_)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hcomm (h : G) hhH (g : G) g.2).symm
  have hinj : Function.Injective (fun h : H' => (⟨QuotientGroup.mk (h.1 : ↥I), hcent h.1 h.2⟩ :
      ↥(Subgroup.center (PQuot 3 I)))) := by
    intro h1 h2 he
    have hq : (QuotientGroup.mk (h1.1 : ↥I) : PQuot 3 I) = QuotientGroup.mk (h2.1 : ↥I) :=
      congrArg Subtype.val he
    have hmem : (h1.1 : ↥I)⁻¹ * h2.1 ∈ GLAPPrimeCore 3 ↥I := QuotientGroup.eq.1 hq
    have hmemH : (h1.1 : ↥I)⁻¹ * h2.1 ∈ H' := H'.mul_mem (H'.inv_mem h1.2) h2.2
    have hone : (h1.1 : ↥I)⁻¹ * h2.1 = 1 := by
      by_contra hne
      set z : ↥I := (h1.1 : ↥I)⁻¹ * h2.1 with hz
      have hzH : (z : G) ∈ H := hmemH
      have hz3 : z ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hH3 _ hzH)
      have hord : orderOf z = 3 := orderOf_eq_prime hz3 hne
      have hdvd : orderOf (⟨z, hmem⟩ : GLAPPrimeCore 3 ↥I) ∣ Nat.card (GLAPPrimeCore 3 ↥I) :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hord] at hdvd
      exact hn3 hdvd
    exact Subtype.ext (inv_mul_eq_one.1 hone)
  calc Nat.card H = Nat.card H' := hcardH.symm
    _ ≤ Nat.card (Subgroup.center (PQuot 3 I)) := Nat.card_le_card_of_injective _ hinj

theorem alpha_U62_rank (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hI : catalogIs (PSimple 3 (Ipart 3 L b)) (isU6n 1)) :
    3 ^ 5 ≤ Nat.card B := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  obtain ⟨E, T, hEI, hEel, hEcard, hTI, hT2, hTnot, hEN⟩ :=
    hin.i1015four62 _ _ (Icomp_of_cfg hc hin.l105 h).1 hI
  have hcomm : ∀ d ∈ Dgrp b x, ∀ i ∈ Ipart 3 L b, d * i = i * d := fun d hd i hi =>
    (Subgroup.mem_centralizer_iff.1 (Ipart_le_cs h hi)) d hd
  have hEcomm : ∀ e ∈ E, ∀ d ∈ Dgrp b x, e * d = d * e := fun e he d hd =>
    ((Subgroup.mem_centralizer_iff.1 (Ipart_le_cs h (hEI he))) d hd).symm
  have hEDel : IsElemAbelian 3 (E ⊔ Dgrp b x) := IsElemAbelian.sup_of_commute hEel hDel hEcomm
  have hTcent : ∀ d ∈ Dgrp b x, d ∈ Subgroup.normalizer (T : Set G) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun t ht =>
      ((Subgroup.mem_centralizer_iff.1 (Ipart_le_cs h (hTI ht))) d hd).symm)
  have hEDN : E ⊔ Dgrp b x ≤ Subgroup.normalizer (T : Set G) := sup_le hEN (fun d hd => hTcent d hd)
  have hT0 : T ≠ ⊥ := fun hT => hTnot (by rw [hT]; exact bot_le)
  have hrank := card_le_pow_glaTwoLocalRank hp hEDel hT0 hT2 hEDN
  have hBcard : Nat.card B = 3 ^ GLATwoLocalRank 3 G := (sstar_triple h.star).1.2.1
  have hDN : Dgrp b x ≤ Subgroup.normalizer (E : Set G) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun e he => hEcomm e he d hd)
  have hcardid := card_sup_mul_card_inf_of_le_normalizer hDN
  have hinter : Nat.card (E ⊓ Dgrp b x : Subgroup G) ≤
      Nat.card (Subgroup.center (PQuot 3 (Ipart 3 L b))) :=
    alpha_card_le_center_pquot (inf_le_left.trans hEI) (fun h' hh i hi => hcomm h' hh.2 i hi)
      (fun h' hh => hDel.2 h' hh.2)
  have hZpos : 0 < Nat.card (Subgroup.center (PQuot 3 (Ipart 3 L b))) := Nat.card_pos
  have hEc : Nat.card E = 3 ^ 3 * Nat.card (Subgroup.center (PQuot 3 (Ipart 3 L b))) := hEcard
  have hDc' : Nat.card (Dgrp b x) = 3 ^ 2 := hDc
  have key : 3 ^ 5 * Nat.card (Subgroup.center (PQuot 3 (Ipart 3 L b))) ≤
      Nat.card (E ⊔ Dgrp b x : Subgroup G) * Nat.card (Subgroup.center (PQuot 3 (Ipart 3 L b))) := by
    calc 3 ^ 5 * Nat.card (Subgroup.center (PQuot 3 (Ipart 3 L b)))
        = Nat.card (E ⊔ Dgrp b x : Subgroup G) * Nat.card (E ⊓ Dgrp b x : Subgroup G) := by
          rw [hcardid, hEc, hDc']
          ring
      _ ≤ Nat.card (E ⊔ Dgrp b x : Subgroup G) * Nat.card (Subgroup.center (PQuot 3 (Ipart 3 L b))) :=
          Nat.mul_le_mul_left _ hinter
  have h243 : 3 ^ 5 ≤ Nat.card (E ⊔ Dgrp b x : Subgroup G) := le_of_mul_le_mul_right key hZpos
  calc 3 ^ 5 ≤ Nat.card (E ⊔ Dgrp b x : Subgroup G) := h243
    _ ≤ 3 ^ GLATwoLocalRank 3 G := hrank
    _ = Nat.card B := hBcard.symm

private theorem alpha_le_normalizer_of_abelian {B A D : Subgroup G}
    (hcomm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u) (hA : A ≤ B) (hD : D ≤ B) :
    D ≤ Subgroup.normalizer (A : Set G) := fun d hd =>
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun a ha =>
    hcomm a (hA ha) d (hD hd))

private theorem alpha_exists_compl {B D : Subgroup G} {y : G} (hBel : IsElemAbelian 3 B) (hDB : D ≤ B)
    (hDc : Nat.card D = 3 ^ 2) (hyB : y ∈ B) (hyD : y ∉ D) :
    ∃ A : Subgroup G, A ≤ B ∧ y ∈ A ∧ A ⊓ D = ⊥ ∧ A ⊔ D = B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv => isElemAbelian_commute hBel hu hv
  have hy1 : y ≠ 1 := fun h1 => hyD (h1 ▸ Subgroup.one_mem D)
  have hy3 : y ^ 3 = 1 := hBel.2 y hyB
  have hFne : {A : Subgroup G | A ≤ B ∧ y ∈ A ∧ A ⊓ D = ⊥}.Nonempty := by
    refine ⟨Subgroup.zpowers y, Subgroup.zpowers_le.2 hyB, Subgroup.mem_zpowers y, ?_⟩
    rw [eq_bot_iff]
    rintro g ⟨hg1, hg2⟩
    rw [Subgroup.mem_bot]
    by_contra hg
    have hg3 : g ^ 3 = 1 := hBel.2 g (Subgroup.zpowers_le.2 hyB hg1)
    have e := casealpha_zpowers_eq Nat.prime_three (orderOf_eq_prime hy3 hy1) hg3 hg1 hg
    have hyz : y ∈ Subgroup.zpowers g := by rw [e]; exact Subgroup.mem_zpowers y
    exact hyD (Subgroup.zpowers_le.2 hg2 hyz)
  obtain ⟨A, hAF, hAmax⟩ := Set.exists_max_image {A : Subgroup G | A ≤ B ∧ y ∈ A ∧ A ⊓ D = ⊥}
    (fun A : Subgroup G => Nat.card A) (Set.toFinite _) hFne
  obtain ⟨hAB, hyA, hAD⟩ := hAF
  refine ⟨A, hAB, hyA, hAD, ?_⟩
  by_contra hne
  obtain ⟨c, hcB, hcn⟩ : ∃ c ∈ B, c ∉ A ⊔ D := by
    by_contra hall
    push_neg at hall
    exact hne (le_antisymm (sup_le hAB hDB) fun c hc => hall c hc)
  have hc3 : c ^ 3 = 1 := hBel.2 c hcB
  have hc1 : c ≠ 1 := fun h1 => hcn (h1 ▸ Subgroup.one_mem _)
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcA : A ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgA, hgc⟩
    rw [Subgroup.mem_bot]
    by_contra hg
    have e := casealpha_zpowers_eq Nat.prime_three hord (hBel.2 g (hAB hgA)) hgc hg
    have hcAz : c ∈ Subgroup.zpowers g := by rw [e]; exact Subgroup.mem_zpowers c
    exact hcn ((le_sup_left : A ≤ A ⊔ D) (Subgroup.zpowers_le.2 hgA hcAz))
  have hBN : B ≤ Subgroup.normalizer (A : Set G) := alpha_le_normalizer_of_abelian hcomm hAB (le_refl B)
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hA'B : A ⊔ Subgroup.zpowers c ≤ B := sup_le hAB (Subgroup.zpowers_le.2 hcB)
  have hyA' : y ∈ A ⊔ Subgroup.zpowers c := Subgroup.mem_sup_left hyA
  have hcard' : Nat.card (A ⊔ Subgroup.zpowers c : Subgroup G) = 3 * Nat.card A := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer (A := A) (B := Subgroup.zpowers c)
      ((Subgroup.zpowers_le.2 hcB).trans hBN)
    rw [hcA, Subgroup.card_bot, mul_one, Nat.card_zpowers, hord] at h1
    rw [h1, mul_comm]
  have hA'D : (A ⊔ Subgroup.zpowers c) ⊓ D = ⊥ := by
    have hJD : (A ⊔ Subgroup.zpowers c) ⊓ D ≤ D := inf_le_right
    have hcardJ : Nat.card ((A ⊔ Subgroup.zpowers c) ⊓ D : Subgroup G) ∣ 3 ^ 2 := by
      rw [← hDc]
      exact Subgroup.card_dvd_of_le hJD
    obtain ⟨i, hi, hJi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hcardJ
    have hid := card_sup_mul_card_inf_of_le_normalizer (A := A ⊔ Subgroup.zpowers c) (B := D)
      (alpha_le_normalizer_of_abelian hcomm hA'B hDB)
    have hAid := card_sup_mul_card_inf_of_le_normalizer (A := A) (B := D)
      (alpha_le_normalizer_of_abelian hcomm hAB hDB)
    rw [hAD, Subgroup.card_bot, mul_one, hDc] at hAid
    have hle : Nat.card (A ⊔ D : Subgroup G) ≤ Nat.card ((A ⊔ Subgroup.zpowers c) ⊔ D : Subgroup G) :=
      Subgroup.card_le_of_le (sup_le_sup_right le_sup_left D)
    rw [hDc, hcard'] at hid
    interval_cases i
    · rw [pow_zero] at hJi
      exact Subgroup.card_eq_one.1 hJi
    ·
      rw [hJi, pow_one] at hid
      norm_num at hid hAid
      have hsame : A ⊔ D = (A ⊔ Subgroup.zpowers c) ⊔ D :=
        Subgroup.eq_of_le_of_card_ge (sup_le_sup_right le_sup_left D) (by omega)
      have hcA'D : c ∈ (A ⊔ Subgroup.zpowers c) ⊔ D :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
      rw [← hsame] at hcA'D
      exact absurd hcA'D hcn
    ·
      have hJD' : (A ⊔ Subgroup.zpowers c) ⊓ D = D :=
        Subgroup.eq_of_le_of_card_ge hJD (le_of_eq (by rw [hJi, hDc]))
      have hDA' : D ≤ A ⊔ Subgroup.zpowers c := by
        rw [← hJD']
        exact inf_le_left
      have hsupA' : (A ⊔ Subgroup.zpowers c) ⊔ D = A ⊔ Subgroup.zpowers c := sup_eq_left.2 hDA'
      rw [hsupA', hcard'] at hle
      norm_num at hAid hle
      omega
  have hmax : Nat.card (A ⊔ Subgroup.zpowers c : Subgroup G) ≤ Nat.card A :=
    hAmax _ ⟨hA'B, hyA', hA'D⟩
  rw [hcard'] at hmax
  omega

private theorem alpha_not_L2_of_U45 (hd : CatDistinctAt) {S : Type} [Group S] [Finite S] (k : ℕ)
    (h : catalogIs S (fun i => S9.isU4two i ∨ S9.isU5two i)) : ¬ catalogIs S (isL2n k) :=
  fun h2 => hd.u45_l2 S k h h2

theorem alpha_U62_K_not_L2 (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b)
    (hT : ∃ T : Subgroup G, T ≤ Ipart 3 L b ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 (Ipart 3 L b))
    (hI : catalogIs (PSimple 3 (Ipart 3 L b)) (isU6n 1)) {y : G} (hyB : y ∈ B) (hyD : y ∉ Dgrp b x)
    {K : Subgroup G} (hK : GLAPComponent 3 (Ipart 3 L b ⊓ cx y) K) (k : ℕ) :
    ¬ catalogIs (PSimple 3 K) (isL2n k) := by
  obtain ⟨T, hTI, hT2, hBT, hTnot⟩ := hT
  have hB5 := alpha_U62_rank hc hin h hI
  have hBel := B_el h
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  obtain ⟨A, hAB, hyA, hAD, hAsup⟩ := alpha_exists_compl hBel hDB hDc hyB hyD
  have hcardid := card_sup_mul_card_inf_of_le_normalizer (A := A) (B := Dgrp b x)
    (alpha_le_normalizer_of_abelian (fun u hu v hv => isElemAbelian_commute hBel hu hv) hAB hDB)
  rw [hAD, Subgroup.card_bot, mul_one, hDc, hAsup] at hcardid
  have h27 : 3 ^ 3 ≤ Nat.card A := by
    norm_num at hB5 hcardid ⊢
    omega
  have hy1 : y ≠ 1 := fun h1 => hyD (h1 ▸ Subgroup.one_mem _)
  have hcomp : GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) := (Icomp_of_cfg hc hin.l105 h).1
  have hres := hin.u62t9 (L ⊓ cx b) (Ipart 3 L b) A T hcomp hI (isElemAbelian_mono hBel hAB) h27
    (hAB.trans h.inner_I.1)
    (fun a ha ha1 hcm => ha1 (by
      have haD : a ∈ A ⊓ Dgrp b x := ⟨ha, (h.cent_I a (hAB ha)).1 hcm⟩
      rw [hAD] at haD
      exact Subgroup.mem_bot.1 haD))
    (innDiagOn_mono h.inner_I hAB) hTI hT2 hTnot (hAB.trans hBT) y hyA hy1 K hK
  exact alpha_not_L2_of_U45 hin.l105.l103.dist k hres

theorem alpha_I_comp_CD (hc : S10Ctx G p) (hin : Lemma105Inputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) :
    GLAPComponent p (cs (Dgrp b x)) (Ipart p L b) := by
  have hp := hc.ctx.prime
  have hLcomp : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hchev : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc h.star
  have hbp : b ^ p = 1 := (B_el h).2 b h.mem
  have hIcomp : GLAPComponent p (L ⊓ cx b) (Ipart p L b) :=
    (hin.i91comp (cx x) L b hLcomp hchev hbp h.prop h.I_ne).1
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert _ _)
  have hEq : L ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) = L ⊓ cx b := by
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hgL, hgD⟩
      refine ⟨hgL, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hgD b hbD).symm
    · rintro ⟨hgL, hgb⟩
      refine ⟨hgL, ?_⟩
      have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hLcomp.1 hgL)
      have hle : Dgrp b x ≤ Subgroup.centralizer ({g} : Set G) := by
        refine Subgroup.closure_le _ |>.2 ?_
        intro k hk
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
        rcases hk with rfl | rfl
        · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hgb).symm
        · exact Subgroup.mem_centralizer_singleton_iff.2 hgx.symm
      exact Subgroup.mem_centralizer_iff.2 fun d hd =>
        Subgroup.mem_centralizer_singleton_iff.1 (hle hd)
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G))
      (Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G)) := by
    have hCD : Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) ≤ cx x :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxD)
    have := isSubnormal_inf hLcomp.2.1 (Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G))
    rwa [inf_eq_right.2 hCD] at this
  have hJ : GLAPComponent p (L ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G))
      (Ipart p L b) := by
    rw [hEq]
    exact hIcomp
  exact glaPComponent_of_isSubnormal' hp hsub hJ

private theorem y9xC_td4_u6 (hd : CatDistinctAt) {S : Type} [Group S] [Finite S] {m : ℕ} (hm : Odd m)
    (h1 : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) (h2 : catalogIs S (isU6n m)) : False :=
  hd.td4_u6 S m hm h1 h2

private theorem y9xC_U6_I (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) (ac : AlphaCtx G 3 B x L b a) {m : ℕ} (hm : Odd m)
    (hJU6 : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) (isU6n m)) :
    ∃ m' : ℕ, Odd m' ∧ 3 * m' = m ∧ catalogIs (PSimple 3 (Ipart 3 L b)) (isU6n m') := by
  classical
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  obtain ⟨-, hDel, -⟩ := dgrp_facts hc h
  have hcs := ac.c105.single a ha ha1
  have hJc : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a) := hcs.1
  have hJchev : IsChevSimple 2 (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) := ac.c104.1.2
  rcases ac.c104.2 with ⟨d, hdD, hdF⟩ | ⟨-, hT, -, -⟩
  · have hBN : B ≤ Subgroup.normalizer ((Jpart 3 (Ipart 3 L b) a : Subgroup G) : Set G) :=
      hcs.2 _ hJc ⟨MulEquiv.refl _⟩
    have haB : a ∈ B := (ac.c105.essential a ha ha1).1
    have haInn : InnDiagOn 3 (Subgroup.zpowers a) (Jpart 3 (Ipart 3 L b) a) :=
      hin.l105.l103.aut.inner_innDiag (cx a) _ a hJc hJchev (hBN haB)
        (inducesInnerMod_of_centMod (centMod_zpowers_of_le (Jpart_le_cx h ha) (Subgroup.mem_zpowers a)))
    have hdNI : NonInnDiag 3 d (Jpart 3 (Ipart 3 L b) a) :=
      hin.l105.l103.aut.field_nonInnDiag _ _ d hJc hJchev hdF
    have hda : d ∉ Subgroup.zpowers a := fun hm' =>
      hdNI.2 (innDiagOn_mono haInn (Subgroup.zpowers_le.2 hm'))
    have hI : GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ cx d) (Ipart 3 L b) :=
      I_comp_in_J hc hin.l105.l104 h ha ha1 hdD hda hJc
    have hd3 : d ^ 3 = 1 := hDel.2 d hdD
    obtain ⟨m', hm'⟩ := hin.fu6exp _ _ d m hJc hdF hJU6
    subst hm'
    have hodd' : Odd m' := (Nat.odd_mul.1 hm).2
    exact ⟨m', hodd', rfl, (hin.i91u6 (cx a) (Jpart 3 (Ipart 3 L b) a) d (Ipart 3 L b) m' hJc hd3 hdF hI hodd').1 hJU6⟩
  · exact (y9xC_td4_u6 hin.l105.l103.dist hm hT hJU6).elim

private theorem y9xC_card_sup {p : ℕ} (hp : p.Prime) {E₀ F D : Subgroup G} {y : G}
    (hel : IsElemAbelian p E₀) (hDE : D ≤ E₀) (hDc : Nat.card D = p ^ 2) (hFE : F ≤ E₀)
    (hF : F ⊓ D = ⊥) (hyF : y ∈ F) (hy1 : y ≠ 1) :
    Nat.card (D ⊔ Subgroup.zpowers y : Subgroup G) = p ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hyE : y ∈ E₀ := hFE hyF
  have hyN : y ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
      isElemAbelian_commute hel (hDE hd) hyE)
  have hzD : Subgroup.zpowers y ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgF : g ∈ F ⊓ D := ⟨Subgroup.zpowers_le.2 hyF hg.1, hg.2⟩
    rw [hF, Subgroup.mem_bot] at hgF
    exact Subgroup.mem_bot.2 hgF
  have h1 := card_sup_mul_card_inf_of_le_normalizer (A := D) (B := Subgroup.zpowers y)
    (Subgroup.zpowers_le.2 hyN)
  rw [inf_comm, hzD, Subgroup.card_bot, mul_one, hDc, Nat.card_zpowers,
    orderOf_eq_prime (hel.2 y hyE) hy1] at h1
  rw [h1]
  ring

private theorem y9xC_exists_comp {X : Subgroup G} {p : ℕ} (hne : GLAPLayer p X ≠ ⊥) :
    ∃ K : Subgroup G, GLAPComponent p X K := by
  by_contra hcon
  push_neg at hcon
  exact hne (le_bot_iff.1 (show GLAPLayer p X ≤ ⊥ from sSup_le fun K hK => absurd hK (hcon K)))

private theorem y9xC_conj_cs {E : Subgroup G} {t : G} (ht : ∀ e ∈ E, e * t = t * e) {k : G}
    (hk : k ∈ Subgroup.centralizer (E : Set G)) :
    t * k * t⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro e he
  have h1 : e * t = t * e := ht e he
  have h3 : t⁻¹ * e = e * t⁻¹ := by
    calc t⁻¹ * e = t⁻¹ * (e * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * e) * t⁻¹ := by rw [h1]
      _ = e * t⁻¹ := by group
  calc e * (t * k * t⁻¹) = (e * t) * k * t⁻¹ := by group
    _ = (t * e) * k * t⁻¹ := by rw [h1]
    _ = t * (e * k) * t⁻¹ := by group
    _ = t * (k * e) * t⁻¹ := by rw [hk e he]
    _ = t * k * (e * t⁻¹) := by group
    _ = t * k * (t⁻¹ * e) := by rw [h3]
    _ = t * k * t⁻¹ * e := by group

private theorem y9xC_normalizer_cs {E : Subgroup G} {g : G} (hg : ∀ e ∈ E, e * g = g * e) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
  have hg' : ∀ e ∈ E, e * g⁻¹ = g⁻¹ * e := by
    intro e he
    have h1 : e * g = g * e := hg e he
    calc e * g⁻¹ = g⁻¹ * (g * e) * g⁻¹ := by group
      _ = g⁻¹ * (e * g) * g⁻¹ := by rw [h1]
      _ = g⁻¹ * e := by group
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact y9xC_conj_cs hg hk
  · intro hk
    have := y9xC_conj_cs hg' hk
    simpa [mul_assoc] using this

private theorem y9x_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro k
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA k, hB k]

private theorem y9xC_layer_mono (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (h : Cfg p B x L b) {E₀ E : Subgroup G} (hE₀B : E₀ ≤ B)
    (hel₀ : IsElemAbelian p E₀) (hEE₀ : E ≤ E₀) :
    GLAPLayer p (L ⊓ cs E₀) ≤ GLAPLayer p (L ⊓ cs E) := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have hBel := B_el h
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hE₀x : E₀ ≤ cx x := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel (hE₀B he) hxB)
  have hsupX : (L ⊓ cs E) ⊔ E₀ ≤ cx x := sup_le (inf_le_left.trans hLc.1) hE₀x
  have hK : CFSG.Open.IsKGroup ↥((L ⊓ cs E) ⊔ E₀) :=
    isKGroup_of_isKProper hc.ctx.kProper (fun e => hCx (top_le_iff.1 (by rw [← e]; exact hsupX)))
  have hPX : E₀ ≤ Subgroup.normalizer ((L ⊓ cs E : Subgroup G) : Set G) := fun g hg =>
    y9x_normalizer_inf (sstar_norm h.star (hE₀B hg))
      (y9xC_normalizer_cs (E := E) (g := g) fun e he => isElemAbelian_commute hel₀ (hEE₀ he) hg)
  have hP : IsPGroup p E₀ := isPGroup_of_isElemAbelian hel₀
  have hbal := glaPLayer_inf_centralizer_le hp hin.l105.lbal hK hP hPX
  have hEq : (L ⊓ cs E) ⊓ cs E₀ = L ⊓ cs E₀ := by
    rw [inf_assoc]
    congr 1
    exact inf_eq_right.2 (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hEE₀))
  calc GLAPLayer p (L ⊓ cs E₀) = GLAPLayer p ((L ⊓ cs E) ⊓ cs E₀) := by rw [hEq]
    _ ≤ GLAPLayer p (L ⊓ cs E) := hbal

private theorem y9x_mem_centralizer_iff (T : Subgroup G) (g : G) :
    g ∈ Subgroup.centralizer (T : Set G) ↔ T ≤ cx g := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hg t ht
    exact Subgroup.mem_centralizer_singleton_iff.2 (hg t ht)
  · intro hT t ht
    exact Subgroup.mem_centralizer_singleton_iff.1 (hT ht)

private theorem y9x_cs_sup (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  ext g
  rw [Subgroup.mem_inf, y9x_mem_centralizer_iff, y9x_mem_centralizer_iff,
    y9x_mem_centralizer_iff]
  constructor
  · intro hg
    exact ⟨le_trans le_sup_left hg, le_trans le_sup_right hg⟩
  · rintro ⟨hA, hB⟩
    exact sup_le hA hB

private theorem y9x_cs_zpowers (y : G) :
    Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) = cx y := by
  ext g
  rw [y9x_mem_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

private theorem y9xC_generic (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a)
    (hG : ¬ (p = 3 ∧ ∃ n : ℕ, catalogIs (PSimple 3 (Ipart p L b)) (isG2n n)))
    (hU : ¬ (p = 3 ∧ ∃ n : ℕ, Odd n ∧ 1 < n ∧ catalogIs (PSimple 3 (Ipart p L b)) (isU6n n))) :
    ∃ (E₀ F : Subgroup G) (y : G) (E K : Subgroup G), AlphaData p B x L b a E₀ F y E K := by
  classical
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₀, F, hbase⟩ := alpha_base hc hin h ac
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  have hBel := B_el h
  have hFne : ∃ y ∈ F, y ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hF : F = ⊥ := eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (hcon g hg)
    have hE₀D : E₀ = Dgrp b x := by
      have := hbase.F_sup
      rw [hF, bot_sup_eq] at this
      exact this.symm
    have h1 := hbase.E₀_card
    rw [hE₀D, hDc] at h1
    exact absurd h1 (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  obtain ⟨y, hyF, hy1, hyess⟩ : ∃ y ∈ F, y ≠ 1 ∧
      ((∃ z ∈ F, z ≠ 1 ∧ IsEssential p B z) → IsEssential p B y) := by
    by_cases hex : ∃ z ∈ F, z ≠ 1 ∧ IsEssential p B z
    · obtain ⟨z, hz, hz1, hzE⟩ := hex
      exact ⟨z, hz, hz1, fun _ => hzE⟩
    · obtain ⟨y, hy, hy1⟩ := hFne
      exact ⟨y, hy, hy1, fun h' => absurd h' hex⟩
  have hyE0 : y ∈ E₀ := hbase.F_E₀ hyF
  have hyB : y ∈ B := hbase.E₀_B hyE0
  have hyD : y ∉ Dgrp b x := fun hyD => hy1 (by
    have hm : y ∈ F ⊓ Dgrp b x := ⟨hyF, hyD⟩
    rw [hbase.F_inf, Subgroup.mem_bot] at hm
    exact hm)
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G, E = Dgrp b x ⊔ Subgroup.zpowers y := ⟨_, rfl⟩
  have hEE₀ : E ≤ E₀ := by
    rw [hEdef]
    exact sup_le hbase.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hbase.E₀_el hEE₀
  have hEcard : Nat.card E = p ^ 3 := by
    rw [hEdef]
    exact y9xC_card_sup hp hbase.E₀_el hbase.D_E₀ hDc hbase.F_E₀ hbase.F_inf hyF hy1
  have hbE : b ∈ E := by
    rw [hEdef]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hyE : y ∈ E := by
    rw [hEdef]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := (hEE₀.trans hbase.E₀_B).trans (sstar_norm h.star)
  have hlay : GLAPLayer p (L ⊓ cs E) ≠ ⊥ := fun hbot =>
    hbase.E₀_layer (le_bot_iff.1 ((y9xC_layer_mono hc hin h hbase.E₀_B hbase.E₀_el hEE₀).trans (le_of_eq hbot)))
  obtain ⟨K, hK⟩ := y9xC_exists_comp hlay
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian (sstar_triple h.star).2.1.2.1
  have hLK : CFSG.Open.IsKGroup ↥L :=
    isKGroup_of_isKProper hc.ctx.kProper (fun e => hCx (top_le_iff.1 (by rw [← e]; exact (sstar_triple h.star).2.2.1)))
  have hKI : K ≤ Ipart p L b :=
    glaPComponent_le_glaPLayer_centralizer_singleton hp hin.l105.lbal hLK hEel hEN hbE hK
  have hKcy : K ≤ cx y :=
    (hK.1.trans inf_le_right).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hyE)))
  have hcsE : Subgroup.centralizer ((E : Subgroup G) : Set G) =
      Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) ⊓ cx y := by
    rw [hEdef, y9x_cs_sup, y9x_cs_zpowers y]
  have hsubI : Ipart p L b ⊓ cx y ≤ L ⊓ Subgroup.centralizer ((E : Subgroup G) : Set G) := by
    refine le_inf (inf_le_left.trans ((layer_le p _).trans inf_le_left)) ?_
    rw [hcsE]
    exact inf_le_inf_right _ (Ipart_le_cs h)
  have hKIy : GLAPComponent p (Ipart p L b ⊓ cx y) K :=
    glaPComponent_of_le hp hK (le_inf hKI hKcy) hsubI
  refine ⟨E₀, F, y, E, K, ⟨hbase, hyF, hy1, hyess, hEdef, hEcard, hK, ?_, ?_⟩⟩
  · intro hp3 n hn
    exact (hG ⟨hp3, n, hn⟩).elim
  · intro hp3 m k hm3 hodd hJU6 hKk
    subst hp3
    obtain ⟨m', hm'odd, -, hI⟩ := y9xC_U6_I hc hin h ac hodd hJU6
    have hm'1 : m' = 1 := by
      by_contra hne
      have hpos := hm'odd.pos
      exact hU ⟨rfl, m', hm'odd, by omega, hI⟩
    subst hm'1
    obtain ⟨T, hT1, hT2, hT3, hT4, -⟩ := ac.c105.T_exists
    exact alpha_U62_K_not_L2 hc hin h ⟨T, hT1, hT2, hT3, hT4⟩ hI hyB hyD hKIy k hKk

private theorem y9xC_g2_inj (hd : CatDistinctAt) {S : Type} [Group S] [Finite S] {n n' : ℕ}
    (h1 : catalogIs S (isG2n n)) (h2 : catalogIs S (isG2n n')) : n = n' :=
  hd.g2_inj S n n' h1 h2

private theorem y9xC_g2_u6 (hd : CatDistinctAt) {S : Type} [Group S] [Finite S] {n m : ℕ}
    (hnm : n = m ∨ Odd m) (h1 : catalogIs S (isG2n n)) (h2 : catalogIs S (isU6n m)) : False :=
  hd.g2_u6 S n m hnm h1 h2

private theorem y9xC_urn_l2 (hd : CatDistinctAt) {S : Type} [Group S] [Finite S] {n k : ℕ}
    (hodd : Odd n) (hn1 : 1 < n) (h1 : catalogIs S (isUrn n)) (h2 : catalogIs S (isL2n k)) : False :=
  hd.urn_l2 S n k hodd hn1 h1 h2

private theorem y9xC_route (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) (ac : AlphaCtx G 3 B x L b a) {n : ℕ}
    (hn : catalogIs (PSimple 3 (Ipart 3 L b)) (isG2n n) ∨
      (Odd n ∧ 1 < n ∧ catalogIs (PSimple 3 (Ipart 3 L b)) (isU6n n))) :
    ∃ (E₀ F : Subgroup G) (y : G) (E K : Subgroup G), AlphaData 3 B x L b a E₀ F y E K := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hdist := hin.l105.l103.dist
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  have hBel := B_el h
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hLc : GLAPComponent 3 (cx x) L := (sstar_triple h.star).2.2
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hcsD_ne : Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) ≠ ⊤ := fun e =>
    hCx (top_le_iff.1 (by rw [← e]; exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hxD))))
  have hcsD_K : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper hcsD_ne
  have hIcsD : GLAPComponent 3 (Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G)) (Ipart 3 L b) :=
    alpha_I_comp_CD hc hin.l105 h
  have hIcomp : GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) := (Icomp_of_cfg hc hin.l105 h).1
  have hbb : b ^ 3 = 1 := (hBel).2 b h.mem
  have hqs : CFSG.Open.IsQuasisimple ↥L := (hc.stage9.1 B x L h.star).1
  have hg2c : ∀ n', catalogIs (PSimple 3 (Ipart 3 L b)) (isG2n n') →
      GLAPPrimeCoreOf 3 (Ipart 3 L b) = ⊥ ∧ Subgroup.center (PQuot 3 (Ipart 3 L b)) = ⊥ := fun n' hn' =>
    hin.multa.g2 (cx x) L b n' hLc hqs hbb h.prop hIcomp hn'
  have hBcsD : B ≤ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hBel (hDB hd) hg
  have hrank : 3 ^ GLATwoLocalRank 3 ↥(Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G)) ≤ Nat.card B := by
    rw [(sstar_triple h.star).1.2.1]
    exact Nat.pow_le_pow_right hp.pos
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_twoLocalRank_le_of_injective hp
        (Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G)).subtype Subtype.val_injective)
  have hcentB : B ⊓ centModSubgroup 3 (Ipart 3 L b) = Dgrp b x := by
    ext c
    constructor
    · rintro ⟨hcB, hcM⟩
      exact (h.cent_I c hcB).1 (centMod_iff.2 hcM)
    · intro hcD
      exact ⟨hDB hcD, centMod_iff.1 ((h.cent_I c (hDB hcD)).2 hcD)⟩
  have hB4 : 3 ^ 4 ≤ Nat.card B := by
    rw [(sstar_triple h.star).1.2.1]
    exact Nat.pow_le_pow_right hp.pos hc.ctx.rank_ge
  have hcardB : 3 ^ 2 * Nat.card ↥(B ⊓ centModSubgroup 3 (Ipart 3 L b)) ≤ Nat.card B := by
    rw [hcentB, hDc]
    calc 3 ^ 2 * 3 ^ 2 = 3 ^ 4 := by norm_num
      _ ≤ Nat.card B := hB4
  have hT0 := ac.c105.T_exists
  obtain ⟨T₀, hT₀1, hT₀2, hT₀3, hT₀4, hT₀5, hT₀6⟩ := hT0
  have hT₀c : (⁅T₀, B⁆ : Subgroup G) ≠ ⊥ := by
    rw [Subgroup.commutator_comm, hT₀5]
    exact hT₀6
  have hEcond : ∀ E : Subgroup G, IsE0 B (Ipart 3 L b) E → ¬ ∀ g ∈ E, CentMod 3 (Ipart 3 L b) g := by
    intro E hE hall
    have hED : E ≤ Dgrp b x := fun g hg => (h.cent_I g (hE.1 hg)).1 (hall g hg)
    obtain ⟨EA, hEAB, hEAel, hEAcard, hEAD, hEAne⟩ := ac.caseA
    have hEAI := ((alpha_E0_eq_IsE0 hc hin h).1 EA hEAD hEAB).1 hEAne
    have hmaxEA := hE.2.2 EA hEAB hEAI
    have h9 : Nat.card E ≤ 3 ^ 2 := by rw [← hDc]; exact Subgroup.card_le_of_le hED
    have h27 : 3 ^ 3 ≤ Nat.card E := by rw [← hEAcard]; exact hmaxEA
    have hle : (3 : ℕ) ^ 3 ≤ 3 ^ 2 := h27.trans h9
    norm_num at hle
  have hn' := hn
  obtain ⟨E₁, y₁, J₁, hE₁, hy₁E, hy₁nc, hJ₁, hconc, hT₁⟩ :=
    hin.i266 (Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G)) (Ipart 3 L b) B n hcsD_K hIcsD hn
      (fun hG => (hg2c n hG).2) (fun hG => (hg2c n hG).1)
      (by
        intro hU6
        rcases hn with hG | ⟨hodd, hn1, hU⟩
        · exact (y9xC_g2_u6 hdist (Or.inl rfl) hG hU6).elim
        · exact hin.multa.u6core (cx x) L b n hLc hqs hbb (sstar_chev2 hc h.star) h.prop hIcomp hodd hn1 hU)
      (by
        intro hU6
        rcases hn with hG | ⟨hodd, hn1, hU⟩
        · exact (y9xC_g2_u6 hdist (Or.inl rfl) hG hU6).elim
        · exact hin.multa.u6 _ _ n hIcomp hodd hn1 hU)
      hBel h.inner_I.1 hBcsD hrank hcardB h.inner_I ⟨T₀, hT₀1, hT₀2, hT₀3, hT₀4, hT₀c⟩ hEcond
  obtain ⟨hE₁B, hE₁ne, hE₁max⟩ := hE₁
  have hE1 := (alpha_E0_eq_IsE0 hc hin h).2 E₁ ⟨hE₁B, hE₁ne, hE₁max⟩
  have hDE₁ : Dgrp b x ≤ E₁ := hE1.1
  have hE₁el : IsElemAbelian 3 E₁ := isElemAbelian_mono hBel hE₁B
  have hE₁l : GLAPLayer 3 (L ⊓ cs E₁) ≠ ⊥ :=
    ((alpha_E0_eq_IsE0 hc hin h).1 E₁ hDE₁ hE₁B).2 hE₁ne
  have hy₁D : y₁ ∉ Dgrp b x := fun hyD => hy₁nc ((h.cent_I y₁ (hE₁B hy₁E)).2 hyD)
  obtain ⟨EA, hEAB, hEAel, hEAcard, hEAD, hEAne⟩ := ac.caseA
  have hcardE₁ : 3 ^ 3 ≤ Nat.card E₁ := by
    rw [← hEAcard]
    exact hE1.2 EA hEAB hEAel hEAD hEAne
  obtain ⟨F, hFE, hFL, hFJ, hF1, hF2⟩ := alpha_F hc hin h ac hE₁B hE₁el hDE₁ hE₁l
  have hbase : AlphaBase 3 B x L b a E₁ F :=
    ⟨hE₁B, hE₁el, hDE₁, hE₁l, hE1.2, hcardE₁, hFE, hFL, hFJ, hF1, hF2⟩
  obtain ⟨f, hfF, hf1, d, hdD, hy₁fd, hIcf, hDf⟩ := alpha_split_F hc h hE₁B hF1 hF2 hy₁E hy₁D
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G, E = Dgrp b x ⊔ Subgroup.zpowers f := ⟨_, rfl⟩
  have hfE₁ : f ∈ E₁ := hFE hfF
  have hfB : f ∈ B := hE₁B hfE₁
  have hEcard : Nat.card E = 3 ^ 3 := by
    rw [hEdef]
    exact y9xC_card_sup hp hE₁el hDE₁ hDc hFE hF1 hfF hf1
  have hbE : b ∈ E := by rw [hEdef]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hcsE : Subgroup.centralizer ((E : Subgroup G) : Set G) =
      Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) ⊓ cx f := by
    rw [hEdef, y9x_cs_sup, y9x_cs_zpowers f]
  have hIE : Ipart 3 L b ⊓ Subgroup.centralizer ((E : Subgroup G) : Set G) = Ipart 3 L b ⊓ cx f := by
    rw [hcsE, ← inf_assoc, inf_eq_left.2 (Ipart_le_cs h)]
  have hJE : GLAPComponent 3 (Ipart 3 L b ⊓ Subgroup.centralizer ((E : Subgroup G) : Set G)) J₁ := by
    rw [hIE, ← hIcf]
    exact hJ₁
  have hsubIE : IsSubnormal (Ipart 3 L b ⊓ Subgroup.centralizer ((E : Subgroup G) : Set G))
      (L ⊓ Subgroup.centralizer ((E : Subgroup G) : Set G)) := by
    have h1 := isSubnormal_inf (Icomp_of_cfg hc hin.l105 h).1.2.1
      (Subgroup.centralizer ((E : Subgroup G) : Set G))
    have hcb : Subgroup.centralizer ((E : Subgroup G) : Set G) ≤ cx b :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hbE))
    rwa [inf_assoc, inf_eq_right.2 hcb] at h1
  have hK₁ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ((E : Subgroup G) : Set G)) J₁ :=
    glaPComponent_of_isSubnormal' hp hsubIE hJE
  obtain ⟨T₁, hT₁a, hT₁b, hT₁c, hT₁d, hT₁e⟩ := hT₁
  have hessf : IsEssential 3 B f := by
    have hTf : T₁ ≤ Subgroup.centralizer ({f} : Set G) := by
      have : T₁ ≤ Ipart 3 L b ⊓ cx f := by rw [← hIcf]; exact hT₁a
      exact this.trans inf_le_right
    exact ⟨hfB, hf1, T₁, hTf, hT₁b, hT₁c, hT₁d, fun _ => hT₁e⟩
  refine ⟨E₁, F, f, E, J₁, ⟨hbase, hfF, hf1, fun _ => hessf, hEdef, hEcard, hK₁, ?_, ?_⟩⟩
  ·
    intro _ n' hn'
    rcases hn with hG | ⟨hodd, hn1, hU⟩
    · have hnn := y9xC_g2_inj hdist hG hn'
      subst hnn
      exact (hconc.1 hG).2
    · exact (y9xC_g2_u6 hdist (Or.inr hodd) hn' hU).elim
  ·
    intro _ m k _ hodd hJU6 hKk
    rcases hn with hG | ⟨hodd', hn1, hU⟩
    · obtain ⟨m', hm'odd, -, hI'⟩ := y9xC_U6_I hc hin h ac hodd hJU6
      exact (y9xC_g2_u6 hdist (Or.inr hm'odd) hG hI').elim
    · exact y9xC_urn_l2 hdist hodd' hn1 (hconc.2 hU) hKk

theorem alpha_yEK (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) :
    ∃ (E₀ F : Subgroup G) (y : G) (E K : Subgroup G), AlphaData p B x L b a E₀ F y E K := by
  by_cases hG : p = 3 ∧ ∃ n : ℕ, catalogIs (PSimple 3 (Ipart p L b)) (isG2n n)
  · obtain ⟨rfl, n, hn⟩ := hG
    exact y9xC_route hc hin h ac (n := n) (Or.inl hn)
  by_cases hU : p = 3 ∧ ∃ n : ℕ, Odd n ∧ 1 < n ∧ catalogIs (PSimple 3 (Ipart p L b)) (isU6n n)
  · obtain ⟨rfl, n, hodd, hn1, hn⟩ := hU
    exact y9xC_route hc hin h ac (n := n) (Or.inr ⟨hodd, hn1, hn⟩)
  exact y9xC_generic hc hin h ac hG hU

private theorem casealpha_closureIn_le {I H Z : Subgroup G} (hI : I ≤ Z)
    (hH : H ≤ Subgroup.normalizer (Z : Set G)) : closureIn I H ≤ Z := by
  unfold closureIn
  refine iSup₂_le fun h hh => ?_
  rintro _ ⟨i, hi, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (hH hh) i).1 (hI hi)

private theorem casealpha_le_closureIn (I : Subgroup G) {H : Subgroup G} (h1 : (1 : G) ∈ H) :
    I ≤ closureIn I H := by
  intro i hi
  unfold closureIn
  exact (le_iSup₂ (f := fun g (_ : g ∈ H) => I.map (MulAut.conj g).toMonoidHom) (1 : G) h1)
    (Subgroup.mem_map.2 ⟨i, hi, by simp⟩)

private theorem casealpha_closureIn_mono {I H H' : Subgroup G} (h : H ≤ H') :
    closureIn I H ≤ closureIn I H' := by
  unfold closureIn
  exact iSup₂_le fun g hg => le_iSup₂_of_le g (h hg) le_rfl

private theorem casealpha_conj_closureIn_of_mem {I H : Subgroup G} {g : G} (hg : g ∈ H) :
    closureIn I H ≤ (closureIn I H).comap (MulAut.conj g).toMonoidHom := by
  unfold closureIn
  refine iSup₂_le fun h hh => Subgroup.map_le_iff_le_comap.2 fun i hi => ?_
  have e : (MulAut.conj g).toMonoidHom ((MulAut.conj h).toMonoidHom i) =
      (MulAut.conj (g * h)).toMonoidHom i := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.mem_comap, Subgroup.mem_comap, e]
  exact (le_iSup₂ (f := fun k (_ : k ∈ H) => I.map (MulAut.conj k).toMonoidHom) (g * h)
    (H.mul_mem hg hh)) (Subgroup.mem_map.2 ⟨i, hi, rfl⟩)

private theorem casealpha_le_normalizer_closureIn (I H : Subgroup G) :
    H ≤ Subgroup.normalizer ((closureIn I H : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact casealpha_conj_closureIn_of_mem hg hk
  · intro hk
    have := casealpha_conj_closureIn_of_mem (H.inv_mem hg) hk
    simpa [MulAut.conj_apply, mul_assoc] using this

private theorem casealpha_conj_closureIn {I H : Subgroup G} {g : G}
    (hI : ∀ i ∈ I, g * i * g⁻¹ ∈ I) (hH : ∀ h ∈ H, g * h * g⁻¹ ∈ H) :
    closureIn I H ≤ (closureIn I H).comap (MulAut.conj g).toMonoidHom := by
  unfold closureIn
  refine iSup₂_le fun h hh => Subgroup.map_le_iff_le_comap.2 fun i hi => ?_
  have e : (MulAut.conj g).toMonoidHom ((MulAut.conj h).toMonoidHom i) =
      (MulAut.conj (g * h * g⁻¹)).toMonoidHom ((MulAut.conj g).toMonoidHom i) := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.mem_comap, Subgroup.mem_comap, e]
  exact (le_iSup₂ (f := fun k (_ : k ∈ H) => I.map (MulAut.conj k).toMonoidHom) (g * h * g⁻¹)
    (hH h hh)) (Subgroup.mem_map.2 ⟨(MulAut.conj g).toMonoidHom i, hI i hi, rfl⟩)

private theorem casealpha_normalizer_closureIn {I H : Subgroup G} {g : G}
    (hI : g ∈ Subgroup.normalizer (I : Set G)) (hH : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((closureIn I H : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact casealpha_conj_closureIn (fun i hi => (Subgroup.mem_normalizer_iff.1 hI i).1 hi)
      (fun h hh => (Subgroup.mem_normalizer_iff.1 hH h).1 hh) hk
  · intro hk
    have hI' := Subgroup.inv_mem _ hI
    have hH' := Subgroup.inv_mem _ hH
    have := casealpha_conj_closureIn (g := g⁻¹)
      (fun i hi => (Subgroup.mem_normalizer_iff.1 hI' i).1 hi)
      (fun h hh => (Subgroup.mem_normalizer_iff.1 hH' h).1 hh) hk
    simpa [MulAut.conj_apply, mul_assoc] using this

private theorem casealpha_closureIn_eq_iSup (I H : Subgroup G) :
    closureIn I H = ⨆ g ∈ H, GLBConj g I := by
  apply le_antisymm
  · unfold closureIn
    refine iSup₂_le fun g hg => ?_
    refine le_iSup₂_of_le g⁻¹ (H.inv_mem hg) (le_of_eq ?_)
    simp [GLBConj]
  · refine iSup₂_le fun g hg => ?_
    refine le_iSup₂_of_le g⁻¹ (H.inv_mem hg) (le_of_eq ?_)
    simp [GLBConj]

private theorem casealpha_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro k
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA k, hB k]

private theorem casealpha_cs_sup (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  ext g
  rw [Subgroup.mem_inf, casealpha_mem_centralizer_iff, casealpha_mem_centralizer_iff,
    casealpha_mem_centralizer_iff]
  constructor
  · intro hg
    exact ⟨le_trans le_sup_left hg, le_trans le_sup_right hg⟩
  · rintro ⟨hA, hB⟩
    exact sup_le hA hB

private theorem casealpha_cs_zpowers (y : G) :
    Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) = cx y := by
  ext g
  rw [casealpha_mem_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

private theorem casealpha_dgrp_eq {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hDel : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) {a x : G} (ha : a ∈ D) (hx : x ∈ D) (ha1 : a ≠ 1) (hx1 : x ≠ 1)
    (hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a) :
    D = Subgroup.zpowers a ⊔ Subgroup.zpowers x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hza : Subgroup.zpowers a ≤ D := Subgroup.zpowers_le.2 ha
  have hzx : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.2 hx
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
    fun g hg => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh =>
      isElemAbelian_commute hDel (hza hh) (hzx hg))
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers x = ⊥ := by
    rw [inf_comm]
    exact casealpha_zpowers_inf_eq_bot hp hDel hx ha hxa
  have hcardS : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers x : Subgroup G) = p ^ 2 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime (hDel.2 a (hza (Subgroup.mem_zpowers a))) ha1,
      orderOf_eq_prime (hDel.2 x (hzx (Subgroup.mem_zpowers x))) hx1] at h1
    rw [h1, sq]
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hza hzx) (hDc.trans hcardS.symm).le).symm

private theorem casealpha_component_ne_bot {p : ℕ} {X L : Subgroup G} (h : GLAPComponent p X L) :
    L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

private theorem casealpha_cs_zpowers' (z : G) : cs (Subgroup.zpowers z) = cx z :=
  casealpha_cs_zpowers z

private theorem casealpha_layer_cz_le {p : ℕ} (hp : p.Prime) (hLB : LBalanceAt G p)
    {X : Subgroup G} (hXK : CFSG.Open.IsKGroup ↥X) {z : G} (hzX : z ∈ X)
    (hP : IsPGroup p (Subgroup.zpowers z)) :
    GLAPLayer p (X ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)) ≤ GLAPLayer p X := by
  refine glaPLayer_inf_centralizer_le hp hLB ?_ hP ((Subgroup.zpowers_le.2 hzX).trans Subgroup.le_normalizer)
  rw [sup_eq_left.2 (Subgroup.zpowers_le.2 hzX)]
  exact hXK

private theorem casealpha_cs_pair (a y : G) :
    Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) =
      cx a ⊓ cx y := by
  rw [casealpha_cs_sup (Subgroup.zpowers a) (Subgroup.zpowers y), casealpha_cs_zpowers a,
    casealpha_cs_zpowers y]

private theorem casealpha_layer_le (p : ℕ) (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ hK => hK.1



private theorem y9xD_center_eq_bot_of_mulEquiv {Q S : Type} [Group Q] [Group S] (e : Q ≃* S)
    (hS : Subgroup.center S = ⊥) : Subgroup.center Q = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h1 : e x ∈ Subgroup.center S := (MulEquivClass.apply_mem_center_iff e).2 hx
  rw [hS, Subgroup.mem_bot] at h1
  exact e.map_eq_one_iff.1 h1

private theorem y9xD_isG2Quot_cases {i : TauCeti.CFSGIndex} (h : isG2Quot i) :
    (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid),
        i = TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩) ∨
      (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid),
        q.card = 3 ∧ i = TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩) := by
  rcases i with ⟨r, hr⟩ | ⟨n, hn⟩ | ⟨d, hd⟩ | s
  · exact absurd h (by simp [isG2Quot, onLie])
  · exact absurd h (by simp [isG2Quot, onLie])
  · cases d with
    | G2 q => exact Or.inl ⟨q, hd, rfl⟩
    | twistedA r q =>
        by_cases hr2 : r = 2
        · subst hr2
          rcases h with h | h
          · exact absurd h (by simp [onLie])
          · exact Or.inr ⟨q, hd, h, rfl⟩
        · exact absurd h (by simp [isG2Quot, onLie, hr2])
    | _ => exact absurd h (by simp [isG2Quot, onLie])
  · exact absurd h (by simp [isG2Quot, onLie])

theorem y9xD_of_G2 (hd : CatDistinctAt)
    (hG2 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid),
      Subgroup.center (TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) = ⊥)
    {I : Subgroup G} (hG : IsG2Quot 3 I) (hch : IsChevSimple 2 (PSimple 3 I)) :
    Subgroup.center (PQuot 3 I) = ⊥ ∧
      ((∃ n : ℕ, 1 < n ∧ catalogIs (PSimple 3 I) (isG2n n)) ∨ catalogIs (PSimple 3 I) isU33) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hG
  rcases y9xD_isG2Quot_cases hi with ⟨q, hv, rfl⟩ | ⟨q, hv, hq3, rfl⟩
  ·
    have hz : Subgroup.center (PQuot 3 I) = ⊥ := y9xD_center_eq_bot_of_mulEquiv e (hG2 q hv)
    let eS : PSimple 3 I ≃* PQuot 3 I :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    refine ⟨hz, ?_⟩
    have hp2 : q.p = 2 := hd.g2_chev2 (PSimple 3 I) q hv ⟨eS.trans e⟩ hch
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hcard : q.card = 2 ^ q.exponent := by
      rw [TauCeti.PrimePower.card_def, hp2]
    have hn : 1 < q.exponent := by
      have he := q.exponent_pos
      by_contra hle
      have h1 : q.exponent = 1 := by omega
      rw [h1] at hcard
      omega
    exact Or.inl ⟨q.exponent, hn, TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩, ⟨hp2, rfl⟩, ⟨eS.trans e⟩⟩
  ·
    haveI hsimple : IsSimpleGroup (PQuot 3 I) :=
      isSimple_of_catalogIs_twistedA ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩, trivial, ⟨e⟩⟩
    have hz : Subgroup.center (PQuot 3 I) = ⊥ := hd.u33_center (PQuot 3 I) q hv hq3 ⟨e⟩
    let eS : PSimple 3 I ≃* PQuot 3 I :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    exact ⟨hz, Or.inr ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩, hq3, ⟨eS.trans e⟩⟩⟩

theorem alpha_g2quot_cases (hd : CatDistinctAt) (hg2 : G2CentrelessAt) {I : Subgroup G}
    (hG : IsG2Quot 3 I) (hch : IsChevSimple 2 (PSimple 3 I)) :
    Subgroup.center (PQuot 3 I) = ⊥ ∧
      ((∃ n : ℕ, 1 < n ∧ catalogIs (PSimple 3 I) (isG2n n)) ∨ catalogIs (PSimple 3 I) isU33) :=
  y9xD_of_G2 hd hg2 hG hch

theorem alpha_not_U33 (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) (ac : AlphaCtx G 3 B x L b a) :
    ¬ catalogIs (PSimple 3 (Ipart 3 L b)) isU33 := by
  intro hU
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEB, hEel, hEcard, hDE, hEne⟩ := ac.caseA
  obtain ⟨-, -, hDcard⟩ := dgrp_facts hc h
  have hlt : Dgrp b x < E := lt_of_le_of_ne hDE fun e => by
    have h1 := hDcard
    rw [e, hEcard] at h1
    norm_num at h1
  obtain ⟨y, hyE, hyD⟩ := SetLike.exists_of_lt hlt
  have hyB : y ∈ B := hEB hyE
  have hy1 : y ≠ 1 := fun e => hyD (e ▸ Subgroup.one_mem _)
  have hy3 : y ^ 3 = 1 := hEel.2 y hyE
  have hcsE : cs E ≤ cx y :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hyE))
  have hEcy : E ≤ cx y := isElemAbelian_le_centralizer hEel hyE
  have hne : GLAPLayer 3 (Ipart 3 L b ⊓ cs E) ≠ ⊥ :=
    ((alpha_E0_eq_IsE0 hc hin h).1 E hDE hEB).1 hEne
  have hIN : E ≤ Subgroup.normalizer ((Ipart 3 L b : Subgroup G) : Set G) := fun g hg =>
    h.inner_I.1 (hEB hg)
  have hXN : E ≤ Subgroup.normalizer (((Ipart 3 L b ⊓ cx y : Subgroup G)) : Set G) := fun g hg =>
    casealpha_normalizer_inf (hIN hg) (Subgroup.le_normalizer (hEcy hg))
  have hcytop : cx y ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hy1
  have hKG : CFSG.Open.IsKGroup ↥((Ipart 3 L b ⊓ cx y) ⊔ E) :=
    isKGroup_of_isKProper hc.ctx.kProper fun e =>
      hcytop (top_le_iff.1 (by rw [← e]; exact sup_le inf_le_right hEcy))
  have hbal := glaPLayer_inf_centralizer_le Nat.prime_three hin.l105.lbal hKG
    (isPGroup_of_isElemAbelian hEel) hXN
  have hinf : (Ipart 3 L b ⊓ cx y) ⊓ cs E = Ipart 3 L b ⊓ cs E := by
    rw [inf_assoc, inf_eq_right.2 hcsE]
  rw [hinf] at hbal
  have hIcomp : GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) := (Icomp_of_cfg hc hin.l105 h).1
  have hCent : ¬ CentMod 3 (Ipart 3 L b) y := fun hc' => hyD ((h.cent_I y hyB).1 hc')
  have hbot := hin.u33 _ (Ipart 3 L b) y hIcomp hU (h.inner_I.1 hyB) hy3 hCent
  exact hne (le_bot_iff.1 (hbot ▸ hbal))

theorem alpha_I_G2n (hc : S10Ctx G 3) (hin : AlphaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) (ac : AlphaCtx G 3 B x L b a) (hG : IsG2Quot 3 (Ipart 3 L b)) :
    ∃ n : ℕ, 1 < n ∧ catalogIs (PSimple 3 (Ipart 3 L b)) (isG2n n) ∧
      Subgroup.center (PQuot 3 (Ipart 3 L b)) = ⊥ := by
  obtain ⟨hz, hcases⟩ := alpha_g2quot_cases hin.l105.l103.dist hin.g2c hG (Icomp_of_cfg hc hin.l105 h).2
  rcases hcases with ⟨n, hn1, hn⟩ | hU
  · exact ⟨n, hn1, hn, hz⟩
  · exact absurd hU (alpha_not_U33 hc hin h ac)

private theorem y9x_layer_le (p : ℕ) (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ hK => hK.1

private theorem y9xA_layer_sn (p : ℕ) (X : Subgroup G) : IsSubnormal (GLAPLayer p X) X :=
  IsSubnormal.step (y9x_layer_le p X)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (y9x_layer_le p X)).2
      (fun _ hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)))
    (IsSubnormal.refl X)

private theorem y9x_closureIn_le {I H Z : Subgroup G} (hI : I ≤ Z)
    (hH : H ≤ Subgroup.normalizer (Z : Set G)) : closureIn I H ≤ Z := by
  unfold closureIn
  refine iSup₂_le fun h hh => ?_
  rintro _ ⟨i, hi, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 (hH hh) i).1 (hI hi)

private theorem y9x_cs_pair (a y : G) :
    Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) =
      cx a ⊓ cx y := by
  rw [y9x_cs_sup (Subgroup.zpowers a) (Subgroup.zpowers y), y9x_cs_zpowers a,
    y9x_cs_zpowers y]

private theorem y9x_le_closureIn (I : Subgroup G) {H : Subgroup G} (h1 : (1 : G) ∈ H) :
    I ≤ closureIn I H := by
  intro i hi
  unfold closureIn
  exact (le_iSup₂ (f := fun g (_ : g ∈ H) => I.map (MulAut.conj g).toMonoidHom) (1 : G) h1)
    (Subgroup.mem_map.2 ⟨i, hi, by simp⟩)

private theorem y9x_conj_closureIn_of_mem {I H : Subgroup G} {g : G} (hg : g ∈ H) :
    closureIn I H ≤ (closureIn I H).comap (MulAut.conj g).toMonoidHom := by
  unfold closureIn
  refine iSup₂_le fun h hh => Subgroup.map_le_iff_le_comap.2 fun i hi => ?_
  have e : (MulAut.conj g).toMonoidHom ((MulAut.conj h).toMonoidHom i) =
      (MulAut.conj (g * h)).toMonoidHom i := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.mem_comap, Subgroup.mem_comap, e]
  exact (le_iSup₂ (f := fun k (_ : k ∈ H) => I.map (MulAut.conj k).toMonoidHom) (g * h)
    (H.mul_mem hg hh)) (Subgroup.mem_map.2 ⟨i, hi, rfl⟩)

private theorem y9x_le_normalizer_closureIn (I H : Subgroup G) :
    H ≤ Subgroup.normalizer ((closureIn I H : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact y9x_conj_closureIn_of_mem hg hk
  · intro hk
    have := y9x_conj_closureIn_of_mem (H.inv_mem hg) hk
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem alpha_Kay_comps (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1) {y : G} {E K : Subgroup G}
    (hE : E = Dgrp b x ⊔ Subgroup.zpowers y) (hEB : E ≤ B) (hK : GLAPComponent p (L ⊓ cs E) K) :
    ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) M →
      GLAPComponent p (Jpart p (Ipart p L b) a ⊓ cx y) M := by
  intro M hM
  have hp : p.Prime := hc.ctx.prime
  have hDE : Dgrp b x ≤ E := by rw [hE]; exact le_sup_left
  have hyE : y ∈ E := by rw [hE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hbE : b ∈ E := hDE (Subgroup.subset_closure (by simp))
  have hxE : x ∈ E := hDE (Subgroup.subset_closure (by simp))
  have hEel : IsElemAbelian p E := isElemAbelian_mono (sstar_triple h.star).1.1 hEB
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEB.trans (sstar_norm h.star)
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hCa : cx a ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha1
  have hLK : CFSG.Open.IsKGroup ↥L :=
    isKGroup_of_isKProper hc.ctx.kProper (fun e => hCx (top_le_iff.1 (by rw [← e]; exact hLc.1)))
  have hcaK : CFSG.Open.IsKGroup ↥(cx a) := isKGroup_of_isKProper hc.ctx.kProper hCa
  have hcsE_le : ∀ z ∈ E, cs E ≤ cx z := fun z hz =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hz))
  have hKI : K ≤ Ipart p L b :=
    glaPComponent_le_glaPLayer_centralizer_singleton hp hin.l105.lbal hLK hEel hEN hbE hK
  have hKJ : K ≤ Jpart p (Ipart p L b) a :=
    hKI.trans (y9x_le_closureIn _ (Subgroup.one_mem _))
  have hKcs : K ≤ cs E := hK.1.trans inf_le_right
  have hKcy : K ≤ cx y := hKcs.trans (hcsE_le y hyE)
  have hJcx : Jpart p (Ipart p L b) a ≤ cx a := Jpart_le_cx h ha
  have hyca : y ∈ cx a := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE haE)
  have hcs_ay : cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) = cx a ⊓ cx y := y9x_cs_pair a y
  have hbal_ay : GLAPLayer p (cx a ⊓ cx y) ≤ GLAPLayer p (cx a) := by
    rw [← y9x_cs_zpowers y]
    refine glaPLayer_inf_centralizer_le hp hin.l105.lbal ?_
      (isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 hyE)))
      ((Subgroup.zpowers_le.2 hyca).trans Subgroup.le_normalizer)
    rw [sup_eq_left.2 (Subgroup.zpowers_le.2 hyca)]
    exact hcaK
  have hsnE : IsSubnormal (L ⊓ cs E) (cs E) := by
    have hsn := isSubnormal_inf hLc.2.1 (cs E)
    rwa [inf_eq_right.2 (hcsE_le x hxE)] at hsn
  have hK_cs : GLAPComponent p (cs E) K := glaPComponent_of_isSubnormal' hp hsnE hK
  have hK_layer : K ≤ GLAPLayer p (cs E) := by
    unfold GLAPLayer
    exact le_sSup (show K ∈ {L' : Subgroup G | GLAPComponent p (cs E) L'} from hK_cs)
  have hAYE : Subgroup.zpowers a ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 haE) (Subgroup.zpowers_le.2 hyE)
  have hsubE : cs E ≤ cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hAYE)
  have hEX : E ≤ cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) := fun e he => by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact isElemAbelian_commute hEel (hAYE hg) he
  have hsub_a : cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤ cx a := by
    rw [hcs_ay]; exact inf_le_left
  have hXtop : cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≠ ⊤ :=
    fun e => hCa (top_le_iff.1 (by rw [← e]; exact hsub_a))
  have hXK : CFSG.Open.IsKGroup ↥(cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
    isKGroup_of_isKProper hc.ctx.kProper hXtop
  have hE_layer : GLAPLayer p (cs E) ≤ GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := by
    have h1 := glaPLayer_inf_centralizer_le hp hin.l105.lbal
      (X := cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (P := E)
      (by rw [sup_eq_left.2 hEX]; exact hXK) (isPGroup_of_isElemAbelian hEel)
      (hEX.trans Subgroup.le_normalizer)
    rwa [inf_eq_right.2 hsubE] at h1
  have hKlay : K ≤ GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
    hK_layer.trans hE_layer
  have hLayS : GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) ≤
      Subgroup.normalizer ((Jpart p (Ipart p L b) a ⊓ cx y : Subgroup G) : Set G) := by
    intro g hg
    have hgs : g ∈ cx a ⊓ cx y := by
      have := y9x_layer_le p _ hg
      rw [hcs_ay] at this
      exact this
    have hgJ : g ∈ GLAPLayer p (cx a) := hbal_ay (by rw [hcs_ay] at hg; exact hg)
    exact y9x_normalizer_inf (y9x_le_normalizer_closureIn _ _ hgJ) (Subgroup.le_normalizer hgs.2)
  have hKay_S : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤ Jpart p (Ipart p L b) a ⊓ cx y :=
    y9x_closureIn_le (le_inf hKJ hKcy) hLayS
  have hKay_lay : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤
      GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
    y9x_closureIn_le hKlay (fun g hg => Subgroup.le_normalizer hg)
  have hKay_norm : GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) ≤
      Subgroup.normalizer ((Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) : Subgroup G) : Set G) :=
    y9x_le_normalizer_closureIn K _
  have hKay_sn_lay : IsSubnormal (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
      (GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y))) :=
    IsSubnormal.step hKay_lay
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKay_lay).2 hKay_norm)
      (IsSubnormal.refl _)
  have hKay_sn : IsSubnormal (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
      (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
    hKay_sn_lay.trans (y9xA_layer_sn p _)
  have hS_le : Jpart p (Ipart p L b) a ⊓ cx y ≤ cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) := by
    rw [hcs_ay]; exact inf_le_inf_right _ hJcx
  have hsn : IsSubnormal (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
      (Jpart p (Ipart p L b) a ⊓ cx y) := by
    have := hKay_sn.inf_of_le hS_le
    rwa [inf_eq_left.2 hKay_S] at this
  exact glaPComponent_of_isSubnormal' hp hsn hM

theorem alpha_Kxy_comps (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg p B x L b) {y : G} {E K : Subgroup G}
    (hE : E = Dgrp b x ⊔ Subgroup.zpowers y) (hEB : E ≤ B) (hK : GLAPComponent p (L ⊓ cs E) K) :
    ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) M →
      GLAPComponent p (L ⊓ cx y) M := by
  intro M hM
  have hp : p.Prime := hc.ctx.prime
  have hDE : Dgrp b x ≤ E := by rw [hE]; exact le_sup_left
  have hyE : y ∈ E := by rw [hE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hxE : x ∈ E := hDE (Subgroup.subset_closure (by simp))
  have hEel : IsElemAbelian p E := isElemAbelian_mono (sstar_triple h.star).1.1 hEB
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hLx : GLAPLayer p (cx x) = L := sstar_layer hc h.star
  have hcsE_le : ∀ z ∈ E, cs E ≤ cx z := fun z hz =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hz))
  have hKcs : K ≤ cs E := hK.1.trans inf_le_right
  have hKL : K ≤ L := hK.1.trans inf_le_left
  have hKcy : K ≤ cx y := hKcs.trans (hcsE_le y hyE)
  have hcs_xy : cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = cx x ⊓ cx y := y9x_cs_pair x y
  have hAYE : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 hxE) (Subgroup.zpowers_le.2 hyE)
  have hsubE : cs E ≤ cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hAYE)
  have hEX : E ≤ cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := fun e he => by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact isElemAbelian_commute hEel (hAYE hg) he
  have hsub_x : cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ cx x := by
    rw [hcs_xy]; exact inf_le_left
  have hXtop : cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≠ ⊤ :=
    fun e => hCx (top_le_iff.1 (by rw [← e]; exact hsub_x))
  have hXK : CFSG.Open.IsKGroup ↥(cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) :=
    isKGroup_of_isKProper hc.ctx.kProper hXtop
  have hsnE : IsSubnormal (L ⊓ cs E) (cs E) := by
    have hsn := isSubnormal_inf hLc.2.1 (cs E)
    rwa [inf_eq_right.2 (hcsE_le x hxE)] at hsn
  have hK_cs : GLAPComponent p (cs E) K := glaPComponent_of_isSubnormal' hp hsnE hK
  have hK_layer : K ≤ GLAPLayer p (cs E) := by
    unfold GLAPLayer
    exact le_sSup (show K ∈ {L' : Subgroup G | GLAPComponent p (cs E) L'} from hK_cs)
  have hE_layer : GLAPLayer p (cs E) ≤ GLAPLayer p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) := by
    have h1 := glaPLayer_inf_centralizer_le hp hin.l105.lbal
      (X := cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) (P := E)
      (by rw [sup_eq_left.2 hEX]; exact hXK) (isPGroup_of_isElemAbelian hEel)
      (hEX.trans Subgroup.le_normalizer)
    rwa [inf_eq_right.2 hsubE] at h1
  have hKlay : K ≤ GLAPLayer p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) :=
    hK_layer.trans hE_layer
  have hLayS : GLAPLayer p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ≤
      Subgroup.normalizer ((L ⊓ cx y : Subgroup G) : Set G) := by
    intro g hg
    have hgs : g ∈ cx x ⊓ cx y := by
      have := y9x_layer_le p _ hg
      rw [hcs_xy] at this
      exact this
    have hgL : g ∈ Subgroup.normalizer (GLAPLayer p (cx x) : Set G) :=
      mem_normalizer_glaPLayer (Subgroup.le_normalizer hgs.1)
    rw [hLx] at hgL
    exact y9x_normalizer_inf hgL (Subgroup.le_normalizer hgs.2)
  have hKxy_S : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ L ⊓ cx y :=
    y9x_closureIn_le (le_inf hKL hKcy) hLayS
  have hKxy_lay : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤
      GLAPLayer p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) :=
    y9x_closureIn_le hKlay (fun g hg => Subgroup.le_normalizer hg)
  have hKxy_norm : GLAPLayer p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ≤
      Subgroup.normalizer ((Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) : Subgroup G) : Set G) :=
    y9x_le_normalizer_closureIn K _
  have hKxy_sn_lay : IsSubnormal (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))
      (GLAPLayer p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y))) :=
    IsSubnormal.step hKxy_lay
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKxy_lay).2 hKxy_norm)
      (IsSubnormal.refl _)
  have hKxy_sn : IsSubnormal (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))
      (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) :=
    hKxy_sn_lay.trans (y9xA_layer_sn p _)
  have hS_le : L ⊓ cx y ≤ cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
    rw [hcs_xy]; exact inf_le_inf_right _ hLc.1
  have hsn : IsSubnormal (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) (L ⊓ cx y) := by
    have := hKxy_sn.inf_of_le hS_le
    rwa [inf_eq_left.2 hKxy_S] at this
  exact glaPComponent_of_isSubnormal' hp hsn hM

private theorem y9xB_isBmaxIn {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) {a : G} (ha : IsEssential p B a) : IsBmaxIn p (cx a) B := by
  have hBX : B ≤ cx a := le_centralizer_of_mem (B_el h) ha.1
  obtain ⟨hrk, -⟩ := glaIsBmax_subgroupOf_centralizer hp (sstar_triple h.star).1 ha
  obtain ⟨T, hTX, hT2, hBT, hTB, -⟩ := ha.2.2
  have hT1 : T ≠ ⊥ := fun h0 => hTB (by rw [h0]; exact Subgroup.commutator_bot_left B)
  refine ⟨hBX, B_el h, ?_, T, hTX, hT1, hT2, hBT⟩
  rw [hrk]
  exact (sstar_triple h.star).1.2.1

private theorem y9xB_normalizer_iSup (𝒞 : Set (Subgroup G)) {g : G}
    (hg1 : ∀ M ∈ 𝒞, GLBConj g⁻¹ M ∈ 𝒞) (hg2 : ∀ M ∈ 𝒞, GLBConj g M ∈ 𝒞) :
    g ∈ Subgroup.normalizer ((⨆ M ∈ 𝒞, M : Subgroup G) : Set G) := by
  have key : ∀ k : G, (∀ M ∈ 𝒞, GLBConj k⁻¹ M ∈ 𝒞) →
      ∀ w ∈ (⨆ M ∈ 𝒞, M : Subgroup G), k * w * k⁻¹ ∈ (⨆ M ∈ 𝒞, M : Subgroup G) := by
    intro k hk w hw
    have hle : (⨆ M ∈ 𝒞, M : Subgroup G) ≤
        (⨆ M ∈ 𝒞, M : Subgroup G).comap (MulAut.conj k).toMonoidHom := by
      refine iSup₂_le fun M hM => fun m hm => ?_
      rw [Subgroup.mem_comap]
      refine le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) (GLBConj k⁻¹ M) (hk M hM) ?_
      rw [mem_gLBConj]
      simpa [MulAut.conj_apply, mul_assoc] using hm
    exact hle hw
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact key g hg1 w hw
  · intro hw
    have hw' := key g⁻¹ (fun M hM => by simpa using hg2 M hM) _ hw
    have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
    rwa [e] at hw'

private theorem y9x_closureIn_eq_iSup (I H : Subgroup G) :
    closureIn I H = ⨆ g ∈ H, GLBConj g I := by
  apply le_antisymm
  · unfold closureIn
    refine iSup₂_le fun g hg => ?_
    refine le_iSup₂_of_le g⁻¹ (H.inv_mem hg) (le_of_eq ?_)
    simp [GLBConj]
  · refine iSup₂_le fun g hg => ?_
    refine le_iSup₂_of_le g⁻¹ (H.inv_mem hg) (le_of_eq ?_)
    simp [GLBConj]

private theorem y9x_zpowers_eq {p : ℕ} (hp : p.Prime) {g x : G} (hxo : orderOf x = p)
    (hgp : g ^ p = 1) (hg : g ∈ Subgroup.zpowers x) (hg1 : g ≠ 1) :
    Subgroup.zpowers g = Subgroup.zpowers x := by
  have hgo : orderOf g = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hgp) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1
    · exact h
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hg)
  rw [Nat.card_zpowers, Nat.card_zpowers, hgo, hxo]

private theorem y9x_zpowers_inf_eq_bot {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hel : IsElemAbelian p E) {x a : G} (hxE : x ∈ E) (haE : a ∈ E)
    (hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a) :
    Subgroup.zpowers x ⊓ Subgroup.zpowers a = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  rintro g ⟨h1, h2⟩
  rw [Subgroup.mem_bot]
  by_contra hg1
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hg1
    simpa using h1
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hg1
    simpa using h2
  have hgE : g ∈ E := Subgroup.zpowers_le.2 hxE h1
  have hgp : g ^ p = 1 := hel.2 g hgE
  have e1 : Subgroup.zpowers g = Subgroup.zpowers x :=
    y9x_zpowers_eq hp (orderOf_eq_prime (hel.2 x hxE) hx1) hgp h1 hg1
  have e2 : Subgroup.zpowers g = Subgroup.zpowers a :=
    y9x_zpowers_eq hp (orderOf_eq_prime (hel.2 a haE) ha1) hgp h2 hg1
  exact hxa (e1.symm.trans e2)

private theorem y9x_dgrp_eq {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hDel : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) {a x : G} (ha : a ∈ D) (hx : x ∈ D) (ha1 : a ≠ 1) (hx1 : x ≠ 1)
    (hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a) :
    D = Subgroup.zpowers a ⊔ Subgroup.zpowers x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hza : Subgroup.zpowers a ≤ D := Subgroup.zpowers_le.2 ha
  have hzx : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.2 hx
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
    fun g hg => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh =>
      isElemAbelian_commute hDel (hza hh) (hzx hg))
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers x = ⊥ := by
    rw [inf_comm]
    exact y9x_zpowers_inf_eq_bot hp hDel hx ha hxa
  have hcardS : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers x : Subgroup G) = p ^ 2 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime (hDel.2 a (hza (Subgroup.mem_zpowers a))) ha1,
      orderOf_eq_prime (hDel.2 x (hzx (Subgroup.mem_zpowers x))) hx1] at h1
    rw [h1, sq]
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hza hzx) (hDc.trans hcardS.symm).le).symm

theorem alpha_Kay_norm_gen (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {y : G}
    {E K : Subgroup G} (hk : AlphaKData p B x L b a y E K) :
    ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) M →
      x ∈ Subgroup.normalizer (M : Set G) := by
  classical
  intro M hM
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := B_el h
  have hBcomm : ∀ g ∈ B, ∀ g' ∈ B, g * g' = g' * g := fun g hg g' hg' =>
    isElemAbelian_commute hBel hg hg'
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  have hess : IsEssential p B a := ac.c104.1.1.2.1
  have hJc : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a) := ac.c104.1.1.2.2
  have hJch : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a)) := ac.c104.1.2
  have haB : a ∈ B := hess.1
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hb1 : b ≠ 1 := fun h1 => h.not_mem (h1 ▸ Subgroup.one_mem _)
  have hxb : Subgroup.zpowers x ≠ Subgroup.zpowers b := fun he =>
    h.not_mem (he ▸ Subgroup.mem_zpowers b)
  have hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a := fun he =>
    ac.not_x (he ▸ Subgroup.mem_zpowers a)
  have hx_pow : x ^ p = 1 := hDel.2 x hxD
  have ha_pow : a ^ p = 1 := hDel.2 a ha
  have hxo : orderOf x = p := orderOf_eq_prime hx_pow hx1
  have hxna : x ∉ Subgroup.zpowers a := fun hxa' =>
    hxa (y9x_zpowers_eq hp (orderOf_eq_prime ha_pow ha1) hx_pow hxa' hx1)
  have hDeqb : Dgrp b x = Subgroup.zpowers b ⊔ Subgroup.zpowers x :=
    y9x_dgrp_eq hp hDel hDc hbD hxD hb1 hx1 hxb
  have hDeq : Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x :=
    y9x_dgrp_eq hp hDel hDc ha hxD ha1 hx1 hxa
  have hCa : cx a ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha1
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hcaK : CFSG.Open.IsKGroup ↥(cx a) := isKGroup_of_isKProper hc.ctx.kProper hCa
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hLK : CFSG.Open.IsKGroup ↥L := isKGroup_of_isKProper hc.ctx.kProper
    (fun e => hCx (top_le_iff.1 (by rw [← e]; exact hLc.1)))
  have hcm_a : CentMod p (Jpart p (Ipart p L b) a) a :=
    centMod_of_mem_centralizer ((y9x_mem_centralizer_iff _ a).2 hJc.1)
  have hDE : Dgrp b x ≤ E := by rw [hk.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hk.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hxE : x ∈ E := hDE hxD
  have hbE : b ∈ E := hDE hbD
  have hEB : E ≤ B := hk.E_B
  have hyB : y ∈ B := hk.y_B
  have hEel : IsElemAbelian p E := isElemAbelian_mono hBel hEB
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEB.trans (sstar_norm h.star)
  have hEF : E = (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers x := by
    rw [hk.E_def, hDeq, sup_right_comm]
  have hEb : E = (Subgroup.zpowers b ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers y := by
    rw [hk.E_def, hDeqb]
  have hFE : Subgroup.zpowers a ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 haE) (Subgroup.zpowers_le.2 hyE)
  have hFB : Subgroup.zpowers a ⊔ Subgroup.zpowers y ≤ B :=
    sup_le (Subgroup.zpowers_le.2 haB) (Subgroup.zpowers_le.2 hyB)
  have hxF : x ∈ Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun g hg => hBcomm g (hFB hg) x hxB
  have hcsF_a : Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G)
      ≤ cx a := by
    rw [← y9x_cs_zpowers a]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left)
  have hXtop : Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) ≠ ⊤ :=
    fun e => hCa (top_le_iff.1 (by rw [← e]; exact hcsF_a))
  have hXK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper hXtop
  have hxel : IsElemAbelian p (Subgroup.zpowers x) := isElemAbelian_mono hEel (Subgroup.zpowers_le.2 hxE)
  have hcsE_le : Subgroup.centralizer ((E : Subgroup G) : Set G) ≤ cx x :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hxE))
  have hK_csE : GLAPComponent p (Subgroup.centralizer ((E : Subgroup G) : Set G)) K := by
    refine glaPComponent_of_isSubnormal' hp ?_ hk.K_comp
    have hsn := isSubnormal_inf hLc.2.1 (Subgroup.centralizer ((E : Subgroup G) : Set G))
    rwa [inf_eq_right.2 hcsE_le] at hsn
  have hcsE : Subgroup.centralizer ((E : Subgroup G) : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [hEF, y9x_cs_sup]
  have hK_cs : GLAPComponent p (Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) :
      Set G) ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) K := by
    rw [← hcsE]
    exact hK_csE
  obtain ⟨𝒞, hC1, hC2, hC3, hC4⟩ :=
    hin.l105.l103.lemma102.i183 G _ hXK p hp (Subgroup.zpowers x) (Subgroup.zpowers_le.2 hxF) hxel K hK_cs
  have hW : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) = ⨆ L' ∈ 𝒞, L' := by
    rw [Kf, y9x_closureIn_eq_iSup, hC2]
  have hMK : ∀ L' ∈ 𝒞, L' ≤ Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) := fun L' hL' => by
    rw [hW]
    exact le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) L' hL'
  have hKF_le : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤
      Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
    y9x_closureIn_le (hk.K_comp.1.trans (inf_le_right.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFE))))
      (fun g hg => Subgroup.le_normalizer (y9x_layer_le p _ hg))
  have hWF : (⨆ L' ∈ 𝒞, L') ≤
      Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := by
    rw [← hW]
    exact hKF_le
  have hxN : x ∈ Subgroup.normalizer ((⨆ L' ∈ 𝒞, L' : Subgroup G) : Set G) :=
    y9xB_normalizer_iSup 𝒞
      (fun L' hL' => hC3 L' hL' x⁻¹ ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)))
      (fun L' hL' => hC3 L' hL' x (Subgroup.mem_zpowers x))
  have hIcomp : GLAPComponent p (Jpart p (Ipart p L b) a ⊓ cx x) (Ipart p L b) :=
    I_comp_in_J hc hin.l105.l104 h ha ha1 hxD hxna hJc
  have hBmax : IsBmaxIn p (cx a) B := y9xB_isBmaxIn hp h hess
  rcases ac.c104.2 with ⟨d, hd, hdF⟩ | ⟨hp3, hTD4, ⟨d, hd, hdN⟩, hG2⟩
  ·
    have hda : d ∉ Subgroup.zpowers a := by
      intro hda
      have hdc : CentMod p (Jpart p (Ipart p L b) a) d :=
        centMod_iff.2 ((Subgroup.zpowers_le.2 (centMod_iff.1 hcm_a)) hda)
      have hind : InducesInnerMod p (Jpart p (Ipart p L b) a) d := by
        have h' := (lemma102_inducesInnerMod_mul_cent (Subgroup.one_mem _) hdc).2
          (CFSG.LocalAnalysis.GLTheoremA.S3.inducesInnerMod_one p (Jpart p (Ipart p L b) a))
        rwa [one_mul] at h'
      exact (hin.l105.l103.aut.field_nonInnDiag (cx a) _ d hJc hJch hdF).2
        (hin.l105.l103.aut.inner_innDiag (cx a) _ d hJc hJch hdF.1 hind)
    have hxF' : FieldOn p x (Jpart p (Ipart p L b) a) :=
      fieldOn_of_mem_D hin.fieldpow hp hDel hDc ha ha1 hd hxD hda hxna hcm_a hdF
    have hFN := hin.l105.l103.field_n hp hp2 (cx a) (Jpart p (Ipart p L b) a) x hJc hxF'
    have hI := hin.i1428 p hp hp2 (cx a) (Jpart p (Ipart p L b) a) B hcaK hBmax hJc hJch hFN.1
    rcases hI.2 y hyB hk.y_ne with hA | ⟨hp3, m, hmodd, hm1, hU6, hL2⟩
    · exact (hA M (alpha_Kay_comps hc hin h ha ha1 hk.E_def hk.E_B hk.K_comp M hM)) hxB
    ·
      exfalso
      subst hp3
      have hm3 : 3 ≤ m := by
        obtain ⟨k0, hk0⟩ := hmodd
        omega
      have hcompL2 : ∀ L' ∈ 𝒞, GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ cx y) L' ∧
          catalogIs (PSimple 3 L') (S10.isL2n m) := by
        intro L' hL'
        have hc' := alpha_Kay_comps hc hin h ha ha1 hk.E_def hk.E_B hk.K_comp L'
          (glaPComponent_of_le hp (hC1 L' hL') (hMK L' hL') hKF_le)
        exact ⟨hc', hL2 L' hc'⟩
      have hKW : GLAPComponent 3 ((⨆ L' ∈ 𝒞, L') ⊓ cx x) K := by
        refine glaPComponent_of_le hp hK_cs ?_ ?_
        · refine le_inf ?_ (hk.K_comp.1.trans (inf_le_right.trans hcsE_le))
          rw [← hW]
          exact y9x_le_closureIn K (Subgroup.one_mem _)
        · exact inf_le_inf hWF (le_of_eq (y9x_cs_zpowers x).symm)
      have hx3 : x ^ 3 = 1 := hx_pow
      obtain ⟨k, hkL2⟩ := hin.l2cent (Jpart 3 (Ipart 3 L b) a ⊓ cx y) (⨆ L' ∈ 𝒞, L') 𝒞 x m
        hcompL2 rfl hxN hx3 K hKW
      exact hk.K_U6 rfl m k hm3 hmodd hU6 hkL2
  ·
    subst hp3
    have hda : d ∉ Subgroup.zpowers a := by
      intro hda
      have hdc : CentMod 3 (Jpart 3 (Ipart 3 L b) a) d :=
        centMod_iff.2 ((Subgroup.zpowers_le.2 (centMod_iff.1 hcm_a)) hda)
      have hind : InducesInnerMod 3 (Jpart 3 (Ipart 3 L b) a) d := by
        have h' := (lemma102_inducesInnerMod_mul_cent (Subgroup.one_mem _) hdc).2
          (CFSG.LocalAnalysis.GLTheoremA.S3.inducesInnerMod_one 3 (Jpart 3 (Ipart 3 L b) a))
        rwa [one_mul] at h'
      exact hdN.2 hind
    have hx_NI : NonInner 3 x (Jpart 3 (Ipart 3 L b) a) :=
      nonInner_of_mem_D hp hDel hDc ha ha1 hd hxD hda hxna hcm_a hdN
    have hR2 : R2Prop 3 x (Jpart 3 (Ipart 3 L b) a) := Or.inr ⟨rfl, hTD4, hx_NI⟩
    have hnot : ¬ InnDiagOn 3 (Subgroup.zpowers x) (Jpart 3 (Ipart 3 L b) a) :=
      lemma102_not_innDiagOn_of_R2Prop hin.l105.l103.aut hJc hJch hR2
    have hy3 : y ^ 3 = 1 := hBel.2 y hyB
    have hyx : y ∉ Subgroup.zpowers x := fun hyx' => by
      have hyy : Subgroup.zpowers y = Subgroup.zpowers x :=
        y9x_zpowers_eq hp hxo hy3 hyx' hk.y_ne
      exact hnot (by rw [← hyy]; exact hk.y_inn)
    have hcomm : x * y = y * x := hBcomm x hxB y hyB
    obtain ⟨n, -, hnG2, -⟩ := alpha_I_G2n hc hin h ac hG2
    have hKI : K ≤ Ipart 3 L b :=
      glaPComponent_le_glaPLayer_centralizer_singleton hp hin.l105.lbal hLK hEel hEN hbE hk.K_comp
    have hIsub : Ipart 3 L b ≤ L ⊓ cx b := y9x_layer_le 3 _
    have hcsE' : Subgroup.centralizer ((E : Subgroup G) : Set G) = cx b ⊓ cx x ⊓ cx y := by
      rw [hEb, y9x_cs_sup, y9x_cs_sup, y9x_cs_zpowers, y9x_cs_zpowers, y9x_cs_zpowers]
    have hcsEy : Subgroup.centralizer ((E : Subgroup G) : Set G) ≤ cx y := by
      rw [hcsE']
      exact inf_le_right
    have hIb : Ipart 3 L b ≤ cx b := hIsub.trans inf_le_right
    have hIx : Ipart 3 L b ≤ cx x := (hIsub.trans inf_le_left).trans hLc.1
    have hIy : Ipart 3 L b ⊓ cx y ≤ L ⊓ Subgroup.centralizer ((E : Subgroup G) : Set G) := by
      rw [hcsE']
      exact le_inf (inf_le_left.trans (hIsub.trans inf_le_left))
        (le_inf (le_inf (inf_le_left.trans hIb) (inf_le_left.trans hIx)) inf_le_right)
    have hKIy : K ≤ Ipart 3 L b ⊓ cx y :=
      le_inf hKI (hk.K_comp.1.trans (inf_le_right.trans hcsEy))
    have hK_I : GLAPComponent 3 (Ipart 3 L b ⊓ cx y) K := glaPComponent_of_le hp hk.K_comp hKIy hIy
    have hK_L2 : catalogIs (PSimple 3 K) (S10.isL2n n) := hk.K_G2 rfl n hnG2
    obtain ⟨M₀, -, huniq, -, hFx⟩ := hin.i148f (cx a) (Jpart 3 (Ipart 3 L b) a) (Ipart 3 L b) K x y n
      hJc hJch hTD4 hx_pow hy3 hcomm hyx hx_NI hIcomp hG2 hk.y_inn hK_I hK_L2
    rw [huniq M (alpha_Kay_comps hc hin h ha ha1 hk.E_def hk.E_B hk.K_comp M hM)]
    exact hFx.1

theorem alpha_Kay_norm (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) :
    ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) M →
      x ∈ Subgroup.normalizer (M : Set G) :=
  alpha_Kay_norm_gen hc hin h ac hd.toK

private theorem y9x_cs_zpowers' (z : G) : cs (Subgroup.zpowers z) = cx z :=
  y9x_cs_zpowers z

private theorem y9xC_Kay_comps (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (M : Subgroup G)
    (hM : GLAPComponent p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) M) :
    GLAPComponent p (Jpart p (Ipart p L b) a ⊓ cx y) M := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a := fun he => ac.not_x (he ▸ Subgroup.mem_zpowers a)
  obtain ⟨-, hDel, hDc⟩ := dgrp_facts hc h
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hDeq : Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x :=
    y9x_dgrp_eq hp hDel hDc ha hxD ha1 hx1 hxa
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hxE : x ∈ E := hDE hxD
  have hbE : b ∈ E := hDE hbD
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hd.E₀_el hEE₀
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := (hEE₀.trans hd.E₀_B).trans (sstar_norm h.star)
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hLK : CFSG.Open.IsKGroup ↥L :=
    isKGroup_of_isKProper hc.ctx.kProper (fun e => hCx (top_le_iff.1 (by rw [← e]; exact hLc.1)))
  have hCa : cx a ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha1
  have hcaK : CFSG.Open.IsKGroup ↥(cx a) := isKGroup_of_isKProper hc.ctx.kProper hCa
  have hcsE_le : ∀ z ∈ E, cs E ≤ cx z := fun z hz =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hz))
  have hKI : K ≤ Ipart p L b :=
    glaPComponent_le_glaPLayer_centralizer_singleton hp hin.l105.lbal hLK hEel hEN hbE hd.K_comp
  have hKJ : K ≤ Jpart p (Ipart p L b) a := hKI.trans (y9x_le_closureIn _ (Subgroup.one_mem _))
  have hKcs : K ≤ cs E := hd.K_comp.1.trans inf_le_right
  have hKcy : K ≤ cx y := hKcs.trans (hcsE_le y hyE)
  have hcs_ay : cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) = cx a ⊓ cx y := y9x_cs_pair a y
  have hyca : y ∈ cx a := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE haE)
  have hEF : E = (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers x := by
    rw [hd.E_def, hDeq, sup_right_comm]
  have hcsE : Subgroup.centralizer ((E : Subgroup G) : Set G) =
      Subgroup.centralizer (((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) ⊓ cx x := by
    rw [hEF, y9x_cs_sup (Subgroup.zpowers a ⊔ Subgroup.zpowers y) (Subgroup.zpowers x), y9x_cs_zpowers x]
  have hsubL : IsSubnormal (L ⊓ cs E) (cs E) := by
    have := isSubnormal_inf hLc.2.1 (cs E)
    rwa [inf_eq_right.2 (hcsE_le x hxE)] at this
  have hxX : x ∈ Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
    (y9x_mem_centralizer_iff _ x).2 (sup_le
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel haE hxE)))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE hxE))))
  have hXa : Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) ≤ cx a := by
    rw [← y9x_cs_zpowers a]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left)
  have hXne : Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) ≠ ⊤ :=
    fun e => hCa (top_le_iff.1 (by rw [← e]; exact hXa))
  have hXK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper hXne
  have hXsup : Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) ⊔
      Subgroup.zpowers x = Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
    sup_eq_left.2 (Subgroup.zpowers_le.2 hxX)
  have hbalX := glaPLayer_inf_centralizer_le (X := Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G))
    (P := Subgroup.zpowers x) hp hin.l105.lbal (by rw [hXsup]; exact hXK)
    (isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 hxE)))
    ((Subgroup.zpowers_le.2 hxX).trans Subgroup.le_normalizer)
  have hXx : Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
        Subgroup.centralizer ((E : Subgroup G) : Set G) := by
    rw [y9x_cs_zpowers x, hcsE]
  have hK_layer : K ≤ GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := by
    have h1 : K ≤ GLAPLayer p (L ⊓ cs E) := by
      unfold GLAPLayer
      exact le_sSup hd.K_comp
    have h2 : GLAPLayer p (L ⊓ cs E) ≤ GLAPLayer p (cs E) := glaPLayer_le_of_isSubnormal hp hsubL
    have h3 : GLAPLayer p (Subgroup.centralizer ((E : Subgroup G) : Set G)) ≤
        GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := by
      rw [← hXx]
      exact hbalX
    exact h1.trans (h2.trans h3)
  have hKay_le_layer : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤
      GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
    y9x_closureIn_le hK_layer (fun g hg => Subgroup.le_normalizer hg)
  have hLay_sub : IsSubnormal (GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)))
      (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
    IsSubnormal.step (layer_le p _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (layer_le p _)).2
        (fun g hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)))
      (IsSubnormal.refl _)
  have hKay_sub : IsSubnormal (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
      (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
    IsSubnormal.step hKay_le_layer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKay_le_layer).2 (y9x_le_normalizer_closureIn K _))
      hLay_sub
  have hbal_ay : GLAPLayer p (cx a ⊓ cx y) ≤ GLAPLayer p (cx a) := by
    rw [← y9x_cs_zpowers' y]
    refine glaPLayer_inf_centralizer_le hp hin.l105.lbal ?_
      (isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 hyE)))
      ((Subgroup.zpowers_le.2 hyca).trans Subgroup.le_normalizer)
    rw [sup_eq_left.2 (Subgroup.zpowers_le.2 hyca)]
    exact hcaK
  have hK_ay_le : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤ Jpart p (Ipart p L b) a ⊓ cx y := by
    refine y9x_closureIn_le (le_inf hKJ hKcy) ?_
    intro g hg
    have hgs : g ∈ cx a ⊓ cx y := by
      have := y9x_layer_le p _ hg
      rw [hcs_ay] at this
      exact this
    have hgJ : g ∈ GLAPLayer p (cx a) := hbal_ay (by rw [hcs_ay] at hg; exact hg)
    exact y9x_normalizer_inf (y9x_le_normalizer_closureIn _ _ hgJ) (Subgroup.le_normalizer hgs.2)
  have hY_le : Jpart p (Ipart p L b) a ⊓ cx y ≤ cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) := by
    rw [hcs_ay]
    exact inf_le_inf_right _ (Jpart_le_cx h ha)
  have hsub2 : IsSubnormal (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
      (Jpart p (Ipart p L b) a ⊓ cx y) := by
    have := isSubnormal_inf hKay_sub (Jpart p (Ipart p L b) a ⊓ cx y)
    rwa [inf_eq_left.2 hK_ay_le, inf_eq_right.2 hY_le] at this
  exact glaPComponent_of_isSubnormal' hp hsub2 hM

private theorem y9xC_closureIn_self {J : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (J : Set G)) : closureIn J (Subgroup.zpowers y) = J :=
  le_antisymm (y9x_closureIn_le le_rfl (Subgroup.zpowers_le.2 hy)) (y9x_le_closureIn J (Subgroup.one_mem _))

private theorem y9xC_not_td4_of_L2 (hd : CatDistinctAt) {S : Type} [Group S] [Finite S] {k : ℕ}
    (h1 : catalogIs S (isL2n k)) (h2 : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) :
    False :=
  hd.td4_l2 S k h1 h2

theorem alpha_Kay_acts (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K)
    (hnorm : ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) M →
      x ∈ Subgroup.normalizer (M : Set G)) :
    ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) M →
      (NonInnDiag p x M ∧ ¬ (p = 3 ∧ IsTD4 3 M)) ∧ FGOn p x M := by
  classical
  intro M hM
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hc.ctx.odd
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a := fun he => ac.not_x (he ▸ Subgroup.mem_zpowers a)
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hxE : x ∈ E := hDE hxD
  have hbE : b ∈ E := hDE hbD
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hd.E₀_el hEE₀
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := (hEE₀.trans hd.E₀_B).trans (sstar_norm h.star)
  have hy_pow : y ^ p = 1 := hd.E₀_el.2 y hyE0
  have hx_pow : x ^ p = 1 := hDel.2 x hxD
  have hxB : x ∈ B := hDB hxD
  have hyB : y ∈ B := hd.E₀_B hyE0
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hLK : CFSG.Open.IsKGroup ↥L :=
    isKGroup_of_isKProper hc.ctx.kProper (fun e => hCx (top_le_iff.1 (by rw [← e]; exact hLc.1)))
  have hcs := ac.c105.single a ha ha1
  have hJc : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a) := hcs.1
  have hJchev : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a)) := ac.c104.1.2
  have hBN : B ≤ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    hcs.2 _ hJc ⟨MulEquiv.refl _⟩
  have haB : a ∈ B := (ac.c105.essential a ha ha1).1
  have hCa : cx a ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha1
  have hcaK : CFSG.Open.IsKGroup ↥(cx a) := isKGroup_of_isKProper hc.ctx.kProper hCa
  have hacm : CentMod p (Jpart p (Ipart p L b) a) a :=
    centMod_zpowers_of_le (Jpart_le_cx h ha) (Subgroup.mem_zpowers a)
  have haInn : InnDiagOn p (Subgroup.zpowers a) (Jpart p (Ipart p L b) a) :=
    hin.l105.l103.aut.inner_innDiag (cx a) _ a hJc hJchev (hBN haB) (inducesInnerMod_of_centMod hacm)
  have hMY := y9xC_Kay_comps hc hin h ac hd M hM
  have hnM : x ∈ Subgroup.normalizer (M : Set G) := hnorm M hM
  have hxa' : x ∉ Subgroup.zpowers a := fun hm =>
    hxa (y9x_zpowers_eq hp (orderOf_eq_prime (hDel.2 a ha) ha1) hx_pow hm hx1)
  have hyx : y * x = x * y := isElemAbelian_commute hEel hyE hxE
  have hxy : x * y = y * x := isElemAbelian_commute hEel hxE hyE
  have hx_notin_y : x ∉ Subgroup.zpowers y := fun hm => by
    have hxF : x ∈ F ⊓ Dgrp b x := ⟨Subgroup.zpowers_le.2 hd.y_F hm, hxD⟩
    rw [hd.F_inf, Subgroup.mem_bot] at hxF
    exact hx1 hxF
  have hy_notin_x : y ∉ Subgroup.zpowers x := fun hm => by
    have hyF : y ∈ F ⊓ Dgrp b x := ⟨hd.y_F, Subgroup.zpowers_le.2 hxD hm⟩
    rw [hd.F_inf, Subgroup.mem_bot] at hyF
    exact hd.y_ne hyF
  have hMJ : GLAPComponent p (closureIn (Jpart p (Ipart p L b) a) (Subgroup.zpowers y) ⊓ cx y) M := by
    rw [y9xC_closureIn_self (hBN hyB)]
    exact hMY
  rcases ac.c104.2 with ⟨d, hdD, hdF⟩ | ⟨h3, hT, ⟨d, hdD, hdN⟩, hG2⟩
  ·
    have hdNI : NonInnDiag p d (Jpart p (Ipart p L b) a) :=
      hin.l105.l103.aut.field_nonInnDiag _ _ d hJc hJchev hdF
    have hda : d ∉ Subgroup.zpowers a := fun hm =>
      hdNI.2 (innDiagOn_mono haInn (Subgroup.zpowers_le.2 hm))
    have hFx : FieldOn p x (Jpart p (Ipart p L b) a) :=
      fieldOn_of_mem_D hin.fieldpow hp hDel hDc ha ha1 hdD hxD hda hxa' hacm hdF
    have hxNI : NonInnDiag p x (Jpart p (Ipart p L b) a) :=
      hin.l105.l103.aut.field_nonInnDiag _ _ x hJc hJchev hFx
    have hI := hin.l105.l103.lemma102.i155 hp hp2 (cx a) (Jpart p (Ipart p L b) a) y x hcaK hJc hJchev
      (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE haE))
      hy_pow hx_pow hyx hx_notin_y (hBN hxB)
      (fun _ => ⟨innDiagOn_mono hd.F_innJ (Subgroup.zpowers_le.2 hd.y_F), hFx⟩) M hMJ hnM
    have hFG : FGOn p x M :=
      hin.i158.fg p hp hp2 (cx a) (Jpart p (Ipart p L b) a) y x M hJc hJchev hy_pow hx_pow hyx
        hy_notin_x hx_notin_y (innDiagOn_mono hd.F_innJ (Subgroup.zpowers_le.2 hd.y_F)) hFx hMY hnM
    rcases hI with hI | ⟨-, e, hiso⟩
    · exact ⟨hI, hFG⟩
    · refine ⟨⟨⟨hnM, fun hinn => hxNI.2 (hin.iso _ _ _ _ x e hMY hJc hJchev hnM (hBN hxB) hiso hinn)⟩, ?_⟩, hFG⟩
      rintro ⟨h3, hTM⟩
      subst h3
      have hTJ : IsTD4 3 (Jpart 3 (Ipart 3 L b) a) := (catalogIs_congr e).1 hTM
      exact hin.l105.l103.aut.td4_not_field _ _ x hJc rfl hTJ hFx
  ·
    subst h3
    have hda : d ∉ Subgroup.zpowers a := fun hm =>
      hdN.2 (inducesInnerMod_of_centMod (centMod_zpowers_of_le (Jpart_le_cx h ha) hm))
    have hNx : NonInner 3 x (Jpart 3 (Ipart 3 L b) a) :=
      nonInner_of_mem_D hp hDel hDc ha ha1 hdD hxD hda hxa' hacm hdN
    have hIJ : GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ cx x) (Ipart 3 L b) :=
      I_comp_in_J hc hin.l105.l104 h ha ha1 hxD hxa' hJc
    obtain ⟨n, -, hn, -⟩ := alpha_I_G2n hc hin h ac hG2
    have hL2 : catalogIs (PSimple 3 K) (isL2n n) := hd.K_G2 rfl n hn
    have hKI : K ≤ Ipart 3 L b :=
      glaPComponent_le_glaPLayer_centralizer_singleton hp hin.l105.lbal hLK hEel hEN hbE hd.K_comp
    have hKcy : K ≤ cx y :=
      (hd.K_comp.1.trans inf_le_right).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hyE)))
    have ipL : Ipart 3 L b ≤ L := (layer_le 3 _).trans inf_le_left
    have hIcb : Ipart 3 L b ≤ cx b := (layer_le 3 _).trans inf_le_right
    have hIcx : Ipart 3 L b ≤ cx x := ipL.trans hLc.1
    have hcsD : cs (Dgrp b x) = cx b ⊓ cx x := by
      rw [dgrp_eq_sup]
      exact (y9x_cs_sup (Subgroup.zpowers b) (Subgroup.zpowers x)).trans
        (by rw [y9x_cs_zpowers b, y9x_cs_zpowers x])
    have hIcs : Ipart 3 L b ≤ cs (Dgrp b x) := by
      rw [hcsD]
      exact le_inf hIcb hIcx
    have hcsE' : cs E = cs (Dgrp b x) ⊓ cx y := by
      rw [hd.E_def]
      exact (y9x_cs_sup (Dgrp b x) (Subgroup.zpowers y)).trans (by rw [y9x_cs_zpowers y])
    have hsubI : Ipart 3 L b ⊓ cx y ≤ L ⊓ cs E := by
      refine le_inf (inf_le_left.trans ipL) ?_
      rw [hcsE']
      exact inf_le_inf_right _ hIcs
    have hKIy : GLAPComponent 3 (Ipart 3 L b ⊓ cx y) K :=
      glaPComponent_of_le hp hd.K_comp (le_inf hKI hKcy) hsubI
    obtain ⟨M₀, hM₀, hM₀u, hM₀L2, hFM₀⟩ :=
      hin.i148f (cx a) (Jpart 3 (Ipart 3 L b) a) (Ipart 3 L b) K x y n hJc hJchev hT hx_pow hy_pow hxy hy_notin_x hNx hIJ
        hG2 (innDiagOn_mono hd.F_innJ (Subgroup.zpowers_le.2 hd.y_F)) hKIy hL2
    have hMM₀ : M = M₀ := hM₀u M hMY
    rw [hMM₀]
    have hchevM₀ : IsChevSimple 2 (PSimple 3 M₀) :=
      hin.l105.l103.lemma102.chev2 hp hp2 (cx a) (Jpart 3 (Ipart 3 L b) a) y hcaK hJc hy_pow (hBN hyB) hJchev M₀ hM₀
    refine ⟨⟨hin.l105.l103.aut.field_nonInnDiag _ _ x hM₀ hchevM₀ hFM₀, ?_⟩, Or.inl hFM₀⟩
    rintro ⟨-, hTD⟩
    exact y9xC_not_td4_of_L2 hin.l105.l103.dist hM₀L2 hTD

theorem alpha_Kay_single_of_norm (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K)
    (hnorm : ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) M →
      x ∈ Subgroup.normalizer (M : Set G)) :
    GLAPComponent p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a := fun he => ac.not_x (he ▸ Subgroup.mem_zpowers a)
  obtain ⟨-, hDel, hDc⟩ := dgrp_facts hc h
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hDeq : Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x :=
    casealpha_dgrp_eq hp hDel hDc ha hxD ha1 hx1 hxa
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hxE : x ∈ E := hDE hxD
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hd.E₀_el hEE₀
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hCa : cx a ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha1
  have hcsE_le : ∀ z ∈ E, cs E ≤ cx z := fun z hz =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hz))
  have hFE : Subgroup.zpowers a ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 haE) (Subgroup.zpowers_le.2 hyE)
  have hEF : E = (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers x := by
    rw [hd.E_def, hDeq, sup_right_comm]
  have hcs_E : Subgroup.centralizer ((E : Subgroup G) : Set G) =
      Subgroup.centralizer (((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) ⊓ cx x := by
    rw [hEF, casealpha_cs_sup (Subgroup.zpowers a ⊔ Subgroup.zpowers y) (Subgroup.zpowers x),
      casealpha_cs_zpowers x]
  have hcsF_a : Subgroup.centralizer (((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G)) : Set G)
      ≤ cx a := by
    rw [← casealpha_cs_zpowers a]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left)
  have hXtop : Subgroup.centralizer (((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G)) : Set G)
      ≠ ⊤ := fun e => hCa (top_le_iff.1 (by rw [← e]; exact hcsF_a))
  have hXK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G)) : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper hXtop
  have hxF : x ∈ Subgroup.centralizer (((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) :=
    (casealpha_mem_centralizer_iff _ x).2 (sup_le
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel haE hxE)))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE hxE))))
  have hxel : IsElemAbelian p (Subgroup.zpowers x) := isElemAbelian_mono hEel (Subgroup.zpowers_le.2 hxE)
  have hK_csE : GLAPComponent p (Subgroup.centralizer ((E : Subgroup G) : Set G)) K := by
    refine glaPComponent_of_isSubnormal' hp ?_ hd.K_comp
    have hsn := isSubnormal_inf hLc.2.1 (Subgroup.centralizer ((E : Subgroup G) : Set G))
    rwa [inf_eq_right.2 (hcsE_le x hxE)] at hsn
  have hK_cs : GLAPComponent p (Subgroup.centralizer (((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) ⊓
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) K := by
    rw [casealpha_cs_zpowers x, ← hcs_E]
    exact hK_csE
  obtain ⟨𝒞, h1, h2, h3, h4⟩ :=
    hin.l105.l103.lemma102.i183 G _ hXK p hp (Subgroup.zpowers x) (Subgroup.zpowers_le.2 hxF) hxel K hK_cs
  have hKF : closureIn K (GLAPLayer p (Subgroup.centralizer (((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G)) : Set G)))
      = ⨆ M ∈ 𝒞, M := by
    rw [casealpha_closureIn_eq_iSup, h2]
  have hKF_le : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤
      Subgroup.centralizer (((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) :=
    casealpha_closureIn_le (hd.K_comp.1.trans (inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFE))))
      (fun g hg => Subgroup.le_normalizer (casealpha_layer_le p _ hg))
  have hM_comp : ∀ M ∈ 𝒞, GLAPComponent p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) M := by
    intro M hM
    have hMK : M ≤ Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) := by
      rw [Kf, hKF]
      exact le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) M hM
    exact glaPComponent_of_le hp (h1 M hM) hMK hKF_le
  have hx_norm : ∀ M ∈ 𝒞, x ∈ Subgroup.normalizer (M : Set G) := fun M hM =>
    hnorm M (hM_comp M hM)
  have hsing : ∀ M ∈ 𝒞, ∀ M' ∈ 𝒞, M = M' := by
    intro M hM M' hM'
    obtain ⟨e, he, hem⟩ := h4 M hM M' hM'
    have hN : e ∈ Subgroup.normalizer (M : Set G) := (Subgroup.zpowers_le.2 (hx_norm M hM)) he
    rw [mem_normalizer_iff_gLBConj_eq.1 hN] at hem
    exact hem
  have hK_ne : K ≠ ⊥ := casealpha_component_ne_bot hd.K_comp
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, M₀ ∈ 𝒞 := by
    by_contra hne
    push_neg at hne
    have hle : K ≤ ⊥ := (casealpha_le_closureIn K (H := GLAPLayer p (Subgroup.centralizer
      (((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G)) : Set G))) (Subgroup.one_mem _)).trans
      (hKF ▸ iSup₂_le fun M hM => absurd hM (hne M))
    exact hK_ne (le_bot_iff.1 hle)
  have hKeq : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) = M₀ := by
    rw [Kf, hKF]
    apply le_antisymm
    · exact iSup₂_le fun M hM => le_of_eq (by rw [hsing M hM M₀ hM₀])
    · exact le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) M₀ hM₀
  rw [hKeq]
  exact h1 M₀ hM₀


theorem alpha_Kay_single (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K)
    (hacts : ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) M →
      NonInnDiag p x M ∧ ¬ (p = 3 ∧ IsTD4 3 M)) :
    GLAPComponent p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
  alpha_Kay_single_of_norm hc hin h ac hd (fun M hM => (hacts M hM).1.1)

theorem alpha_Kxy_norm (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) :
    ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) M →
      a ∈ Subgroup.normalizer (M : Set G) := by
  classical
  intro M hM
  have hk := hd.toK
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := B_el h
  have hBcomm : ∀ g ∈ B, ∀ g' ∈ B, g * g' = g' * g := fun g hg g' hg' =>
    isElemAbelian_commute hBel hg hg'
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have haB : a ∈ B := hDB ha
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hb1 : b ≠ 1 := fun h1 => h.not_mem (h1 ▸ Subgroup.one_mem _)
  have hxb : Subgroup.zpowers x ≠ Subgroup.zpowers b := fun he =>
    h.not_mem (he ▸ Subgroup.mem_zpowers b)
  have hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a := fun he =>
    ac.not_x (he ▸ Subgroup.mem_zpowers a)
  have hx_pow : x ^ p = 1 := hDel.2 x hxD
  have ha_pow : a ^ p = 1 := hDel.2 a ha
  have hxo : orderOf x = p := orderOf_eq_prime hx_pow hx1
  have hxna : x ∉ Subgroup.zpowers a := fun hxa' =>
    hxa (y9x_zpowers_eq hp (orderOf_eq_prime ha_pow ha1) hx_pow hxa' hx1)
  have hDeq : Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x :=
    y9x_dgrp_eq hp hDel hDc ha hxD ha1 hx1 hxa
  have hDeqb : Dgrp b x = Subgroup.zpowers b ⊔ Subgroup.zpowers x :=
    y9x_dgrp_eq hp hDel hDc hbD hxD hb1 hx1 hxb
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hCa : cx a ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha1
  have hcxK : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_of_isKProper hc.ctx.kProper hCx
  have hcaK : CFSG.Open.IsKGroup ↥(cx a) := isKGroup_of_isKProper hc.ctx.kProper hCa
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hLchev : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc h.star
  have hLK : CFSG.Open.IsKGroup ↥L := isKGroup_of_isKProper hc.ctx.kProper
    (fun e => hCx (top_le_iff.1 (by rw [← e]; exact hLc.1)))
  have hcm_x : CentMod p L x := centMod_of_mem_centralizer ((y9x_mem_centralizer_iff _ x).2 hLc.1)
  have hJc : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a) := ac.c104.1.1.2.2
  have hJch : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a)) := ac.c104.1.2
  have hcm_a : CentMod p (Jpart p (Ipart p L b) a) a :=
    centMod_of_mem_centralizer ((y9x_mem_centralizer_iff _ a).2 hJc.1)
  have hDE : Dgrp b x ≤ E := by rw [hk.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hk.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hxE : x ∈ E := hDE hxD
  have hbE : b ∈ E := hDE hbD
  have hEB : E ≤ B := hk.E_B
  have hyB : y ∈ B := hk.y_B
  have hEel : IsElemAbelian p E := isElemAbelian_mono hBel hEB
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEB.trans (sstar_norm h.star)
  have hEF' : E = (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers a := by
    rw [hk.E_def, hDeq, sup_comm (Subgroup.zpowers x ⊔ Subgroup.zpowers y), sup_assoc]
  have hEb : E = (Subgroup.zpowers b ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers y := by
    rw [hk.E_def, hDeqb]
  have hFxy : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 hxE) (Subgroup.zpowers_le.2 hyE)
  have hFxyB : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ B :=
    sup_le (Subgroup.zpowers_le.2 hxB) (Subgroup.zpowers_le.2 hyB)
  have haF : a ∈ Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun g hg => hBcomm g (hFxyB hg) a haB
  have hcsF_x : Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G)
      ≤ cx x := by
    rw [← y9x_cs_zpowers x]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left)
  have hXtop : Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) ≠ ⊤ :=
    fun e => hCx (top_le_iff.1 (by rw [← e]; exact hcsF_x))
  have hXK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer
      ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper hXtop
  have hzaF : Subgroup.zpowers a ≤ Subgroup.centralizer
      ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 haF
  have hael : IsElemAbelian p (Subgroup.zpowers a) :=
    isElemAbelian_mono hEel (Subgroup.zpowers_le.2 haE)
  have hcsE_x : Subgroup.centralizer ((E : Subgroup G) : Set G) ≤ cx x :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hxE))
  have hK_csE : GLAPComponent p (Subgroup.centralizer ((E : Subgroup G) : Set G)) K := by
    refine glaPComponent_of_isSubnormal' hp ?_ hk.K_comp
    have hsn := isSubnormal_inf hLc.2.1 (Subgroup.centralizer ((E : Subgroup G) : Set G))
    rwa [inf_eq_right.2 hcsE_x] at hsn
  have hcsE : Subgroup.centralizer ((E : Subgroup G) : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [hEF', y9x_cs_sup]
  have hK_cs : GLAPComponent p (Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) :
      Set G) ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)) K := by
    rw [← hcsE]
    exact hK_csE
  have hcsE_a : Subgroup.centralizer ((E : Subgroup G) : Set G) ≤ cx a :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 haE))
  rcases h.prop with hFb | ⟨hp3, hT, hNIb⟩
  ·
    have hFa : FieldOn p a L :=
      fieldOn_of_mem_D hin.fieldpow hp hDel hDc hxD hx1 hbD ha h.not_mem ac.not_x hcm_x hFb
    have hBmax_x : IsBmaxIn p (cx x) B := y9xB_isBmaxIn hp h (sstar_triple h.star).2.1
    have hMark := (hin.l105.l103.field_n hp hp2 (cx x) L a hLc hFa).1
    have hI := hin.i1428 p hp hp2 (cx x) L B hcxK hBmax_x hLc hLchev hMark
    rcases hI.2 y hyB hk.y_ne with hA | ⟨hp3, m, hmodd, hm1, hU6, hL2⟩
    · exact (hA M (alpha_Kxy_comps hc hin h hk.E_def hk.E_B hk.K_comp M hM)) haB
    ·
      exfalso
      subst hp3
      obtain ⟨n', rfl⟩ := hin.fu6exp (cx x) L a m hLc hFa hU6
      have hodd' : Odd n' := (Nat.odd_mul.1 hmodd).2
      have hIc := Icomp_of_cfg hc hin.l105 h
      have hbb : b ^ 3 = 1 := hBel.2 b h.mem
      have hUI : catalogIs (PSimple 3 (Ipart 3 L b)) (S10.isU6n n') :=
        (hin.i91u6 (cx x) L b (Ipart 3 L b) n' hLc hbb hFb hIc.1 hodd').1 hU6
      have hIcompJ : GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ cx x) (Ipart 3 L b) :=
        I_comp_in_J hc hin.l105.l104 h ha ha1 hxD hxna hJc
      have hUJ : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) (S10.isU6n (3 * n')) := by
        rcases ac.c104.2 with ⟨d, hdJ, hdF⟩ | ⟨-, -, -, hG2J⟩
        · have hda : d ∉ Subgroup.zpowers a := by
            intro hda
            have hdc : CentMod 3 (Jpart 3 (Ipart 3 L b) a) d :=
              centMod_iff.2 ((Subgroup.zpowers_le.2 (centMod_iff.1 hcm_a)) hda)
            have hind : InducesInnerMod 3 (Jpart 3 (Ipart 3 L b) a) d := by
              have h' := (lemma102_inducesInnerMod_mul_cent (Subgroup.one_mem _) hdc).2
                (CFSG.LocalAnalysis.GLTheoremA.S3.inducesInnerMod_one 3 (Jpart 3 (Ipart 3 L b) a))
              rwa [one_mul] at h'
            exact (hin.l105.l103.aut.field_nonInnDiag (cx a) _ d hJc hJch hdF).2
              (hin.l105.l103.aut.inner_innDiag (cx a) _ d hJc hJch hdF.1 hind)
          have hFxJ : FieldOn 3 x (Jpart 3 (Ipart 3 L b) a) :=
            fieldOn_of_mem_D hin.fieldpow hp hDel hDc ha ha1 hdJ hxD hda hxna hcm_a hdF
          exact (hin.i91u6 (cx a) (Jpart 3 (Ipart 3 L b) a) x (Ipart 3 L b) n' hJc hx_pow hFxJ
            hIcompJ hodd').2 hUI
        · exfalso
          obtain ⟨-, hcases⟩ := alpha_g2quot_cases hin.l105.l103.dist hin.g2c hG2J hIc.2
          rcases hcases with ⟨n2, -, hn2⟩ | hU33
          · exact hin.l105.l103.dist.g2_u6 _ n2 n' (Or.inr hodd') hn2 hUI
          · exact hin.l105.l103.dist.u33_u6 _ n' hU33 hUI
      have hm3 : 3 ≤ 3 * n' := by omega
      obtain ⟨𝒞, hC1, hC2, hC3, -⟩ :=
        hin.l105.l103.lemma102.i183 G _ hXK 3 hp (Subgroup.zpowers a) hzaF hael K hK_cs
      have hW : Kf 3 K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = ⨆ L' ∈ 𝒞, L' := by
        rw [Kf, y9x_closureIn_eq_iSup, hC2]
      have hMK : ∀ L' ∈ 𝒞, L' ≤ Kf 3 K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := fun L' hL' => by
        rw [hW]
        exact le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) L' hL'
      have hKF_le : Kf 3 K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤
          Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
        y9x_closureIn_le (hk.K_comp.1.trans (inf_le_right.trans
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFxy))))
          (fun g hg => Subgroup.le_normalizer (y9x_layer_le 3 _ hg))
      have hWF : (⨆ L' ∈ 𝒞, L') ≤
          Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := by
        rw [← hW]
        exact hKF_le
      have haN : a ∈ Subgroup.normalizer ((⨆ L' ∈ 𝒞, L' : Subgroup G) : Set G) :=
        y9xB_normalizer_iSup 𝒞
          (fun L' hL' => hC3 L' hL' a⁻¹ ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)))
          (fun L' hL' => hC3 L' hL' a (Subgroup.mem_zpowers a))
      have hcompL2 : ∀ L' ∈ 𝒞, GLAPComponent 3 (L ⊓ cx y) L' ∧
          catalogIs (PSimple 3 L') (S10.isL2n (3 * n')) := by
        intro L' hL'
        have hc' := alpha_Kxy_comps hc hin h hk.E_def hk.E_B hk.K_comp L'
          (glaPComponent_of_le hp (hC1 L' hL') (hMK L' hL') hKF_le)
        exact ⟨hc', hL2 L' hc'⟩
      have hKW : GLAPComponent 3 ((⨆ L' ∈ 𝒞, L') ⊓ cx a) K := by
        refine glaPComponent_of_le hp hK_cs ?_ ?_
        · refine le_inf ?_ (hk.K_comp.1.trans (inf_le_right.trans hcsE_a))
          rw [← hW]
          exact y9x_le_closureIn K (Subgroup.one_mem _)
        · exact inf_le_inf hWF (le_of_eq (y9x_cs_zpowers a).symm)
      obtain ⟨k, hkL2⟩ := hin.l2cent (L ⊓ cx y) (⨆ L' ∈ 𝒞, L') 𝒞 a (3 * n') hcompL2 rfl haN ha_pow K hKW
      exact hd.K_U6 rfl (3 * n') k hm3 hmodd hUJ hkL2
  ·
    subst hp3
    have hNa : NonInner 3 a L :=
      nonInner_of_mem_D hp hDel hDc hxD hx1 hbD ha h.not_mem ac.not_x hcm_x hNIb
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := sstar_norm h.star h.mem
    have hbb : b ^ 3 = 1 := (B_el h).2 b h.mem
    have hIcomp : GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) := (Icomp_of_cfg hc hin.l105 h).1
    have hbD' : b ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers a := by
      rw [sup_comm, ← hDeq]
      exact hbD
    have haD' : a ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers x := by
      rw [← dgrp_eq_sup b x]
      exact ha
    have hLab : L ⊓ cx a = L ⊓ cx b := by
      ext g
      constructor
      · rintro ⟨hgL, hga⟩
        refine ⟨hgL, ?_⟩
        have hgS : g ∈ Subgroup.centralizer
            ((Subgroup.zpowers x ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
          rw [y9x_cs_sup, y9x_cs_zpowers x, y9x_cs_zpowers a]
          exact ⟨hLc.1 hgL, hga⟩
        exact Subgroup.mem_centralizer_singleton_iff.2
          ((Subgroup.mem_centralizer_iff.1 hgS b hbD').symm)
      · rintro ⟨hgL, hgb⟩
        refine ⟨hgL, ?_⟩
        have hgS : g ∈ Subgroup.centralizer
            ((Subgroup.zpowers b ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
          rw [y9x_cs_sup, y9x_cs_zpowers b, y9x_cs_zpowers x]
          exact ⟨hgb, hLc.1 hgL⟩
        exact Subgroup.mem_centralizer_singleton_iff.2
          ((Subgroup.mem_centralizer_iff.1 hgS a haD').symm)
    have hIa : GLAPComponent 3 (L ⊓ cx a) (Ipart 3 L b) := by
      rw [hLab]
      exact hIcomp
    have hsq : Nat.sqrt (card2 3 L) ≤ 2 * card2 3 (Ipart 3 L b) := by
      rw [← h.td4_g2 rfl hT, ← h.r2_eq]
      exact h.r2_le
    have hIsG : IsG2Quot 3 (Ipart 3 L b) :=
      (hin.l105.l104.i148d (cx x) L (Ipart 3 L b) b hLc hLchev hT hbN hbb
        (fun hcm => hNIb.2 (inducesInnerMod_of_centMod hcm)) hIcomp hsq).2
    obtain ⟨n, -, hn, -⟩ := alpha_I_G2n hc hin h ac hIsG
    have hL2 : catalogIs (PSimple 3 K) (S10.isL2n n) := hk.K_G2 rfl n hn
    have hKI : K ≤ Ipart 3 L b :=
      glaPComponent_le_glaPLayer_centralizer_singleton hp hin.l105.lbal hLK hEel hEN hbE hk.K_comp
    have hcsE' : Subgroup.centralizer ((E : Subgroup G) : Set G) = cx b ⊓ cx x ⊓ cx y := by
      rw [hEb, y9x_cs_sup, y9x_cs_sup, y9x_cs_zpowers, y9x_cs_zpowers, y9x_cs_zpowers]
    have hcsEy : Subgroup.centralizer ((E : Subgroup G) : Set G) ≤ cx y := by
      rw [hcsE']
      exact inf_le_right
    have hIsub : Ipart 3 L b ≤ L ⊓ cx b := y9x_layer_le 3 _
    have hIb : Ipart 3 L b ≤ cx b := hIsub.trans inf_le_right
    have hIx : Ipart 3 L b ≤ cx x := (hIsub.trans inf_le_left).trans hLc.1
    have hIy : Ipart 3 L b ⊓ cx y ≤ L ⊓ Subgroup.centralizer ((E : Subgroup G) : Set G) := by
      rw [hcsE']
      exact le_inf (inf_le_left.trans (hIsub.trans inf_le_left))
        (le_inf (le_inf (inf_le_left.trans hIb) (inf_le_left.trans hIx)) inf_le_right)
    have hKIy : K ≤ Ipart 3 L b ⊓ cx y :=
      le_inf hKI (hk.K_comp.1.trans (inf_le_right.trans hcsEy))
    have hK_I : GLAPComponent 3 (Ipart 3 L b ⊓ cx y) K :=
      glaPComponent_of_le hp hk.K_comp hKIy hIy
    have hyNotA : y ∉ Subgroup.zpowers a := by
      intro hmem
      have hyF : y ∈ F ⊓ Dgrp b x := ⟨hd.y_F, (Subgroup.zpowers_le.2 ha) hmem⟩
      rw [hd.F_inf, Subgroup.mem_bot] at hyF
      exact hk.y_ne hyF
    have hInn : InnDiagOn 3 (Subgroup.zpowers y) L :=
      innDiagOn_mono hd.F_innL (Subgroup.zpowers_le.2 hd.y_F)
    have hy3 : y ^ 3 = 1 := hBel.2 y hyB
    have hcomm : a * y = y * a := hBcomm a haB y hyB
    obtain ⟨M₁, -, hM₁u, -, hFM₁⟩ := hin.i148f (cx x) L (Ipart 3 L b) K a y n hLc hLchev hT ha_pow hy3 hcomm
      hyNotA hNa hIa hIsG hInn hK_I hL2
    rw [hM₁u M (alpha_Kxy_comps hc hin h hk.E_def hk.E_B hk.K_comp M hM)]
    exact hFM₁.1

private theorem y9x_kxy_comp (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) {E₀ F : Subgroup G} {y : G} {E K : Subgroup G}
    (hd : AlphaData p B x L b a E₀ F y E K)
    (h1 : GLAPComponent p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y))
      (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))) :
    GLAPComponent p (L ⊓ cx y) (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hxE : x ∈ E := hDE (Subgroup.subset_closure (by simp))
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hd.E₀_el hEE₀
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := (hEE₀.trans hd.E₀_B).trans (sstar_norm h.star)
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hcxK : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_of_isKProper hc.ctx.kProper hCx
  have hcsE_le : ∀ z ∈ E, cs E ≤ cx z := fun z hz =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hz))
  have hKcs : K ≤ cs E := hd.K_comp.1.trans inf_le_right
  have hKcy : K ≤ cx y := hKcs.trans (hcsE_le y hyE)
  have hyCx : y ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE hxE)
  have hLx : GLAPLayer p (cx x) = L := sstar_layer hc h.star
  have hcs_xy : cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = cx x ⊓ cx y := y9x_cs_pair x y
  have hbal_xy : GLAPLayer p (cx x ⊓ cx y) ≤ L := by
    rw [← hLx, ← y9x_cs_zpowers y]
    refine glaPLayer_inf_centralizer_le hp hin.l105.lbal ?_
      (isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 hyE)))
      ((Subgroup.zpowers_le.2 hyCx).trans Subgroup.le_normalizer)
    rw [sup_eq_left.2 (Subgroup.zpowers_le.2 hyCx)]
    exact hcxK
  have hlay_xy : GLAPLayer p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ≤ L := by
    rw [hcs_xy]; exact hbal_xy
  have hKxy_le_L : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ L := by
    refine y9x_closureIn_le (hd.K_comp.1.trans inf_le_left) ?_
    intro g hg
    exact Subgroup.le_normalizer (hlay_xy hg)
  have hKxy_le_cy : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ cx y := by
    refine y9x_closureIn_le hKcy ?_
    intro g hg
    have hg' : g ∈ cx x ⊓ cx y := by
      have := y9x_layer_le p _ hg
      rw [hcs_xy] at this
      exact this
    exact Subgroup.le_normalizer hg'.2
  have hsub_xy : L ⊓ cx y ≤ cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
    rw [hcs_xy]; exact inf_le_inf_right _ hLc.1
  exact glaPComponent_of_le hp h1 (le_inf hKxy_le_L hKxy_le_cy) hsub_xy

private theorem y9x_kxy_nid (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K)
    (h1 : GLAPComponent p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y))
      (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)))
    (hyM : a ∈ Subgroup.normalizer ((Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) : Subgroup G) : Set G)) :
    NonInnDiag p a (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ∧
      FGOn p a (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  obtain ⟨-, hDel, hDc⟩ := dgrp_facts hc h
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have ha1 : a ≠ 1 := fun h1' => ac.not_x (h1' ▸ Subgroup.one_mem _)
  have hax : Subgroup.zpowers a ≠ Subgroup.zpowers x :=
    fun he => ac.not_x (he ▸ Subgroup.mem_zpowers a)
  have hDeq : Dgrp b x = Subgroup.zpowers x ⊔ Subgroup.zpowers a :=
    y9x_dgrp_eq hp hDel hDc hxD ac.mem hx1 ha1 hax
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ac.mem
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hd.E₀_el hEE₀
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := (hEE₀.trans hd.E₀_B).trans (sstar_norm h.star)
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hLchev : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc h.star
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hcxK : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_of_isKProper hc.ctx.kProper hCx
  have hy_pow : y ^ p = 1 := hd.E₀_el.2 y hyE0
  have ha_pow : a ^ p = 1 := hEel.2 a haE
  have hcomm : y * a = a * y := isElemAbelian_commute hEel hyE haE
  have hnot : a ∉ Subgroup.zpowers y := by
    intro hmem
    have haF : a ∈ F ⊓ Dgrp b x := ⟨Subgroup.zpowers_le.2 hd.y_F hmem, ac.mem⟩
    rw [hd.F_inf, Subgroup.mem_bot] at haF
    exact ha1 haF
  have hyN : a ∈ Subgroup.normalizer (L : Set G) := hEN haE
  have hLy : closureIn L (Subgroup.zpowers y) = L := by
    apply le_antisymm
    · exact y9x_closureIn_le le_rfl (Subgroup.zpowers_le.2 (hEN hyE))
    · exact y9x_le_closureIn L (Subgroup.one_mem _)
  have hkc := y9x_kxy_comp hc hin h hd h1
  have hJ : GLAPComponent p (closureIn L (Subgroup.zpowers y) ⊓ cx y)
      (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) := by
    rw [hLy]; exact hkc
  have hchevKxy : IsChevSimple 2 (PSimple p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))) :=
    hin.l105.l103.lemma102.chev2 hp hp2 (cx x) L y hcxK hLc hy_pow (hEN hyE) hLchev _ hkc
  rcases h.prop with hF | ⟨h3, hT, hNI⟩
  ·
    have hCentx : CentMod p L x := centMod_zpowers_of_le hLc.1 (Subgroup.mem_zpowers x)
    have hFa : FieldOn p a L :=
      fieldOn_of_mem_D hin.fieldpow hp hDel hDc hxD hx1 hbD ac.mem h.not_mem ac.not_x hCentx hF
    have hnonL : NonInnDiag p a L := hin.l105.l103.aut.field_nonInnDiag _ L a hLc hLchev hFa
    have hI := hin.l105.l103.lemma102.i155 hp hp2 (cx x) L y a hcxK hLc hLchev
      (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE (hDE hxD)))
      hy_pow ha_pow hcomm hnot hyN
      (fun _ => ⟨innDiagOn_mono hd.F_innL (Subgroup.zpowers_le.2 hd.y_F), hFa⟩) _ hJ hyM
    have hyna : y ∉ Subgroup.zpowers a := fun hmem => by
      have hyF : y ∈ F ⊓ Dgrp b x := ⟨hd.y_F, Subgroup.zpowers_le.2 ac.mem hmem⟩
      rw [hd.F_inf, Subgroup.mem_bot] at hyF
      exact hd.y_ne hyF
    have hFG : FGOn p a (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) :=
      hin.i158.fg p hp hp2 (cx x) L y a _ hLc hLchev hy_pow ha_pow hcomm hyna hnot
        (innDiagOn_mono hd.F_innL (Subgroup.zpowers_le.2 hd.y_F)) hFa hkc hyM
    rcases hI with ⟨hnid, -⟩ | ⟨-, e, hiso⟩
    · exact ⟨hnid, hFG⟩
    · exact ⟨⟨hyM, fun hinn => hnonL.2 (hin.iso _ _ _ _ a e h1 hLc hLchev hyM hyN hiso hinn)⟩, hFG⟩
  ·
    subst h3
    have hCentx : CentMod 3 L x := centMod_zpowers_of_le hLc.1 (Subgroup.mem_zpowers x)
    have hNa : NonInner 3 a L :=
      nonInner_of_mem_D hp hDel hDc hxD hx1 hbD ac.mem h.not_mem ac.not_x hCentx hNI
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := sstar_norm h.star h.mem
    have hbb : b ^ 3 = 1 := (B_el h).2 b h.mem
    have hIcomp : GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) := (Icomp_of_cfg hc hin.l105 h).1
    have hIch : IsChevSimple 2 (PSimple 3 (Ipart 3 L b)) := (Icomp_of_cfg hc hin.l105 h).2
    have hbD' : b ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers a := by rw [← hDeq]; exact hbD
    have haD' : a ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers x := by rw [← dgrp_eq_sup b x]; exact ac.mem
    have hLab : L ⊓ cx a = L ⊓ cx b := by
      ext g
      constructor
      · rintro ⟨hgL, hga⟩
        refine ⟨hgL, ?_⟩
        have hgS : g ∈ Subgroup.centralizer (((Subgroup.zpowers x ⊔ Subgroup.zpowers a : Subgroup G)) : Set G) := by
          rw [y9x_cs_sup, y9x_cs_zpowers x, y9x_cs_zpowers a]
          exact ⟨hLc.1 hgL, hga⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hgS b hbD').symm)
      · rintro ⟨hgL, hgb⟩
        refine ⟨hgL, ?_⟩
        have hgS : g ∈ Subgroup.centralizer (((Subgroup.zpowers b ⊔ Subgroup.zpowers x : Subgroup G)) : Set G) := by
          rw [y9x_cs_sup, y9x_cs_zpowers b, y9x_cs_zpowers x]
          exact ⟨hgb, hLc.1 hgL⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hgS a haD').symm)
    have hIa : GLAPComponent 3 (L ⊓ cx a) (Ipart 3 L b) := by rw [hLab]; exact hIcomp
    have hsq : Nat.sqrt (card2 3 L) ≤ 2 * card2 3 (Ipart 3 L b) := by
      rw [← h.td4_g2 rfl hT, ← h.r2_eq]
      exact h.r2_le
    have hIsG : IsG2Quot 3 (Ipart 3 L b) :=
      (hin.l105.l104.i148d (cx x) L (Ipart 3 L b) b hLc hLchev hT hbN hbb
        (fun hcm => hNI.2 (inducesInnerMod_of_centMod hcm)) hIcomp hsq).2
    obtain ⟨n, -, hn, -⟩ := alpha_I_G2n hc hin h ac hIsG
    have hL2 : catalogIs (PSimple 3 K) (isL2n n) := hd.K_G2 rfl n hn
    have hLK : CFSG.Open.IsKGroup ↥L :=
      isKGroup_of_isKProper hc.ctx.kProper (fun e => hCx (top_le_iff.1 (by rw [← e]; exact hLc.1)))
    have hbE : b ∈ E := hDE (Subgroup.subset_closure (by simp))
    have hKI : K ≤ Ipart 3 L b :=
      glaPComponent_le_glaPLayer_centralizer_singleton hp hin.l105.lbal hLK hEel hEN hbE hd.K_comp
    have hKcs : K ≤ cs E := hd.K_comp.1.trans inf_le_right
    have hKcy : K ≤ cx y := hKcs.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2
      (SetLike.mem_coe.2 hyE)))
    have ipL : Ipart 3 L b ≤ L := (y9x_layer_le 3 _).trans inf_le_left
    have hIcb : Ipart 3 L b ≤ cx b := (y9x_layer_le 3 _).trans (inf_le_right)
    have hIcx : Ipart 3 L b ≤ cx x := ipL.trans hLc.1
    have hcsD : cs (Dgrp b x) = cx b ⊓ cx x := by
      rw [dgrp_eq_sup]
      exact (y9x_cs_sup (Subgroup.zpowers b) (Subgroup.zpowers x)).trans
        (by rw [y9x_cs_zpowers b, y9x_cs_zpowers x])
    have hIcs : Ipart 3 L b ≤ cs (Dgrp b x) := by
      rw [hcsD]
      exact le_inf hIcb hIcx
    have hcsE' : cs E = cs (Dgrp b x) ⊓ cx y := by
      rw [hd.E_def]
      exact (y9x_cs_sup (Dgrp b x) (Subgroup.zpowers y)).trans (by rw [y9x_cs_zpowers y])
    have hsubI : Ipart 3 L b ⊓ cx y ≤ L ⊓ cs E := by
      refine le_inf (inf_le_left.trans ipL) ?_
      rw [hcsE']
      exact inf_le_inf_right _ hIcs
    have hKIy : GLAPComponent 3 (Ipart 3 L b ⊓ cx y) K :=
      glaPComponent_of_le hp hd.K_comp (le_inf hKI hKcy) hsubI
    have hyNotA : y ∉ Subgroup.zpowers a := by
      intro hmem
      have hyF : y ∈ F ⊓ Dgrp b x := ⟨hd.y_F, (Subgroup.zpowers_le.2 ac.mem) hmem⟩
      rw [hd.F_inf, Subgroup.mem_bot] at hyF
      exact hd.y_ne hyF
    have hInn : InnDiagOn 3 (Subgroup.zpowers y) L := innDiagOn_mono hd.F_innL (Subgroup.zpowers_le.2 hd.y_F)
    obtain ⟨M₁, hM₁, hM₁u, -, hFM₁⟩ :=
      hin.i148f (cx x) L (Ipart 3 L b) K a y n hLc hLchev hT ha_pow hy_pow
        hcomm.symm hyNotA hNa hIa hIsG hInn hKIy hL2
    have hKeqM : Kf 3 K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = M₁ := hM₁u _ hkc
    have hFK : FieldOn 3 a (Kf 3 K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) := by
      rw [hKeqM]; exact hFM₁
    exact ⟨hin.l105.l103.aut.field_nonInnDiag _ _ a h1 hchevKxy hFK, Or.inl hFK⟩

private theorem y9x_component_ne_bot {p : ℕ} {X L : Subgroup G} (h : GLAPComponent p X L) :
    L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

private theorem y9x_kxy_single (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K)
    (hnorm : ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) M →
      a ∈ Subgroup.normalizer (M : Set G)) :
    GLAPComponent p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y))
      (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have hax : Subgroup.zpowers a ≠ Subgroup.zpowers x :=
    fun he => ac.not_x (he ▸ Subgroup.mem_zpowers a)
  obtain ⟨-, hDel, hDc⟩ := dgrp_facts hc h
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hDeq : Dgrp b x = Subgroup.zpowers x ⊔ Subgroup.zpowers a :=
    y9x_dgrp_eq hp hDel hDc hxD ac.mem hx1 ha1 hax
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ac.mem
  have hxE : x ∈ E := hDE hxD
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hd.E₀_el hEE₀
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hcsE_le : ∀ z ∈ E, cs E ≤ cx z := fun z hz =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hz))
  have hFE : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 hxE) (Subgroup.zpowers_le.2 hyE)
  have hEF : E = (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers a := by
    rw [hd.E_def, hDeq, sup_right_comm]
  have hcs_E : Subgroup.centralizer ((E : Subgroup G) : Set G) =
      Subgroup.centralizer (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) ⊓ cx a := by
    rw [hEF, y9x_cs_sup (Subgroup.zpowers x ⊔ Subgroup.zpowers y) (Subgroup.zpowers a), y9x_cs_zpowers a]
  have hcsF_x : Subgroup.centralizer (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) ≤
      cx x := by
    rw [← y9x_cs_zpowers x]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left)
  have hXtop : Subgroup.centralizer (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) ≠ ⊤ :=
    fun e => hCx (top_le_iff.1 (by rw [← e]; exact hcsF_x))
  have hXK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer
      (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G)) : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper hXtop
  have haF : a ∈ Subgroup.centralizer (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) :=
    (y9x_mem_centralizer_iff _ a).2 (sup_le
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hxE haE)))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE haE))))
  have hael : IsElemAbelian p (Subgroup.zpowers a) := isElemAbelian_mono hEel (Subgroup.zpowers_le.2 haE)
  have hK_csE : GLAPComponent p (Subgroup.centralizer ((E : Subgroup G) : Set G)) K := by
    refine glaPComponent_of_isSubnormal' hp ?_ hd.K_comp
    have hsn := isSubnormal_inf hLc.2.1 (Subgroup.centralizer ((E : Subgroup G) : Set G))
    rwa [inf_eq_right.2 (hcsE_le x hxE)] at hsn
  have hK_cs : GLAPComponent p (Subgroup.centralizer
      (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) ⊓
      Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)) K := by
    rw [y9x_cs_zpowers a, ← hcs_E]
    exact hK_csE
  obtain ⟨𝒞, h1, h2, h3, h4⟩ :=
    hin.l105.l103.lemma102.i183 G _ hXK p hp (Subgroup.zpowers a) (Subgroup.zpowers_le.2 haF) hael K hK_cs
  have hKF : closureIn K (GLAPLayer p (Subgroup.centralizer
      (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G)) : Set G))) = ⨆ M ∈ 𝒞, M := by
    rw [y9x_closureIn_eq_iSup, h2]
  have hKF_le : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤
      Subgroup.centralizer (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) :=
    y9x_closureIn_le (hd.K_comp.1.trans (inf_le_right.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFE))))
      (fun g hg => Subgroup.le_normalizer (y9x_layer_le p _ hg))
  have hM_comp : ∀ M ∈ 𝒞, GLAPComponent p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) M := by
    intro M hM
    have hMK : M ≤ Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
      rw [Kf, hKF]
      exact le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) M hM
    exact glaPComponent_of_le hp (h1 M hM) hMK hKF_le
  have ha_norm : ∀ M ∈ 𝒞, a ∈ Subgroup.normalizer (M : Set G) := fun M hM => hnorm M (hM_comp M hM)
  have hsing : ∀ M ∈ 𝒞, ∀ M' ∈ 𝒞, M = M' := by
    intro M hM M' hM'
    obtain ⟨e, he, hem⟩ := h4 M hM M' hM'
    have hN : e ∈ Subgroup.normalizer (M : Set G) := (Subgroup.zpowers_le.2 (ha_norm M hM)) he
    rw [mem_normalizer_iff_gLBConj_eq.1 hN] at hem
    exact hem
  have hK_ne : K ≠ ⊥ := y9x_component_ne_bot hd.K_comp
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, M₀ ∈ 𝒞 := by
    by_contra hne
    push Not at hne
    have hle : K ≤ ⊥ := (y9x_le_closureIn K (H := GLAPLayer p (Subgroup.centralizer
      (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G)) : Set G))) (Subgroup.one_mem _)).trans
      (hKF ▸ iSup₂_le fun M hM => absurd hM (hne M))
    exact hK_ne (le_bot_iff.1 hle)
  have hKeq : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = M₀ := by
    rw [Kf, hKF]
    apply le_antisymm
    · exact iSup₂_le fun M hM => le_of_eq (by rw [hsing M hM M₀ hM₀])
    · exact le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) M₀ hM₀
  rw [hKeq]
  exact h1 M₀ hM₀

theorem alpha_Kxy (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K)
    (hnorm : ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) M →
      a ∈ Subgroup.normalizer (M : Set G)) :
    GLAPComponent p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ∧
      NonInnDiag p a (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ∧
      FGOn p a (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) := by
  have h1 := y9x_kxy_single hc hin h ac hd hnorm
  have hself : GLAPComponent p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))
      (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) :=
    glaPComponent_of_le hc.ctx.prime h1 le_rfl h1.1
  exact ⟨h1, y9x_kxy_nid hc hin h ac hd h1 (hnorm _ hself)⟩

theorem alpha_Kchev (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K)
    (hay : GLAPComponent p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)))
    (hxy : GLAPComponent p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))) :
    IsChevSimple 2 (PSimple p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))) ∧
      IsChevSimple 2 (PSimple p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))) := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hxE : x ∈ E := hDE (Subgroup.subset_closure (by simp))
  have hbE : b ∈ E := hDE (Subgroup.subset_closure (by simp))
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hd.E₀_el hEE₀
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := (hEE₀.trans hd.E₀_B).trans (sstar_norm h.star)
  have hy_pow : y ^ p = 1 := hd.E₀_el.2 y hyE0
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hCx : cx x ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1
  have hCa : cx a ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha1
  have hLK : CFSG.Open.IsKGroup ↥L := isKGroup_of_isKProper hc.ctx.kProper
    (fun e => hCx (top_le_iff.1 (by rw [← e]; exact hLc.1)))
  have hcaK : CFSG.Open.IsKGroup ↥(cx a) := isKGroup_of_isKProper hc.ctx.kProper hCa
  have hcxK : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_of_isKProper hc.ctx.kProper hCx
  have hcsE_le : ∀ z ∈ E, cs E ≤ cx z := fun z hz =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hz))
  have hKI : K ≤ Ipart p L b :=
    glaPComponent_le_glaPLayer_centralizer_singleton hp hin.l105.lbal hLK hEel hEN hbE hd.K_comp
  have hKJ : K ≤ Jpart p (Ipart p L b) a :=
    hKI.trans (casealpha_le_closureIn _ (Subgroup.one_mem _))
  have hKcs : K ≤ cs E := hd.K_comp.1.trans inf_le_right
  have hKcy : K ≤ cx y := hKcs.trans (hcsE_le y hyE)
  have hJc : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a) := (ac.c105.single a ha ha1).1
  have hJchev : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a)) := ac.c104.1.2
  have hJcx : Jpart p (Ipart p L b) a ≤ cx a := Jpart_le_cx h ha
  have hyca : y ∈ cx a := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE haE)
  have hcs_ay : cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) = cx a ⊓ cx y := casealpha_cs_pair a y
  have hbal_ay : GLAPLayer p (cx a ⊓ cx y) ≤ GLAPLayer p (cx a) := by
    rw [← casealpha_cs_zpowers y]
    refine glaPLayer_inf_centralizer_le hp hin.l105.lbal ?_
      (isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 hyE)))
      ((Subgroup.zpowers_le.2 hyca).trans Subgroup.le_normalizer)
    rw [sup_eq_left.2 (Subgroup.zpowers_le.2 hyca)]
    exact hcaK
  have hK_ay_le : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤
      Jpart p (Ipart p L b) a ⊓ cx y := by
    refine casealpha_closureIn_le (le_inf hKJ hKcy) ?_
    intro g hg
    have hgs : g ∈ cx a ⊓ cx y := by
      have := casealpha_layer_le p _ hg
      rw [hcs_ay] at this
      exact this
    have hgJ : g ∈ GLAPLayer p (cx a) := hbal_ay (by rw [hcs_ay] at hg; exact hg)
    exact casealpha_normalizer_inf (casealpha_le_normalizer_closureIn _ _ hgJ)
      (Subgroup.le_normalizer hgs.2)
  have hsub_ay : Jpart p (Ipart p L b) a ⊓ cx y ≤
      cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) := by
    rw [hcs_ay]; exact inf_le_inf_right _ hJcx
  have hKay_comp : GLAPComponent p (Jpart p (Ipart p L b) a ⊓ cx y)
      (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
    glaPComponent_of_le hp hay hK_ay_le hsub_ay
  have hybNb : y ∈ Subgroup.normalizer ((cx b : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE hbE))
  have hyNI : y ∈ Subgroup.normalizer ((Ipart p L b : Subgroup G) : Set G) :=
    mem_normalizer_glaPLayer (casealpha_normalizer_inf (hEN hyE) hybNb)
  have hyNLa : y ∈ Subgroup.normalizer ((GLAPLayer p (cx a) : Subgroup G) : Set G) :=
    mem_normalizer_glaPLayer (Subgroup.le_normalizer hyca)
  have hyNJ : y ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a : Subgroup G) : Set G) :=
    casealpha_normalizer_closureIn hyNI hyNLa
  have hA_chev : IsChevSimple 2 (PSimple p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))) :=
    hin.l105.l103.lemma102.chev2 hp hp2 (cx a) (Jpart p (Ipart p L b) a) y hcaK hJc hy_pow hyNJ
      hJchev _ hKay_comp
  have hLx : GLAPLayer p (cx x) = L := sstar_layer hc h.star
  have hcs_xy : cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = cx x ⊓ cx y := casealpha_cs_pair x y
  have hyCx : y ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE hxE)
  have hbal_xy : GLAPLayer p (cx x ⊓ cx y) ≤ L := by
    rw [← hLx, ← casealpha_cs_zpowers y]
    refine glaPLayer_inf_centralizer_le hp hin.l105.lbal ?_
      (isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 hyE)))
      ((Subgroup.zpowers_le.2 hyCx).trans Subgroup.le_normalizer)
    rw [sup_eq_left.2 (Subgroup.zpowers_le.2 hyCx)]
    exact hcxK
  have hlay_xy : GLAPLayer p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ≤ L := by
    rw [hcs_xy]; exact hbal_xy
  have hKxy_le_L : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ L := by
    refine casealpha_closureIn_le (hd.K_comp.1.trans inf_le_left) ?_
    intro g hg
    exact Subgroup.le_normalizer (hlay_xy hg)
  have hKxy_le_cy : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ cx y := by
    refine casealpha_closureIn_le hKcy ?_
    intro g hg
    have hg' : g ∈ cx x ⊓ cx y := by
      have := casealpha_layer_le p _ hg
      rw [hcs_xy] at this
      exact this
    exact Subgroup.le_normalizer hg'.2
  have hsub_xy : L ⊓ cx y ≤ cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
    rw [hcs_xy]; exact inf_le_inf_right _ hLc.1
  have hKxy_comp : GLAPComponent p (L ⊓ cx y) (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) :=
    glaPComponent_of_le hp hxy (le_inf hKxy_le_L hKxy_le_cy) hsub_xy
  have hB_chev : IsChevSimple 2 (PSimple p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))) :=
    hin.l105.l103.lemma102.chev2 hp hp2 (cx x) L y hcxK hLc hy_pow (hEN hyE)
      (sstar_chev2 hc h.star) _ hKxy_comp
  exact ⟨hA_chev, hB_chev⟩

structure AlphaKay (p : ℕ) (x a y : G) (K : Subgroup G) : Prop where
  Kay_single : GLAPComponent p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
  Kxy_single : GLAPComponent p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))
  x_acts : NonInnDiag p x (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) ∧
    ¬ (p = 3 ∧ IsTD4 3 (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)))
  a_acts : NonInnDiag p a (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))
  chev_ay : IsChevSimple 2 (PSimple p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)))
  chev_xy : IsChevSimple 2 (PSimple p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)))
  x_fg : FGOn p x (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
  a_fg : FGOn p a (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))

theorem alpha_kay (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) : AlphaKay p x a y K := by
  have hacts := alpha_Kay_acts hc hin h ac hd (alpha_Kay_norm hc hin h ac hd)
  have h1 := alpha_Kay_single hc hin h ac hd (fun M hM => (hacts M hM).1)
  obtain ⟨h2, h3, h3'⟩ := alpha_Kxy hc hin h ac hd (alpha_Kxy_norm hc hin h ac hd)
  obtain ⟨h4, h5⟩ := alpha_Kchev hc hin h ac hd h1 h2
  have hself : GLAPComponent p (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
      (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) :=
    glaPComponent_of_le hc.ctx.prime h1 le_rfl h1.1
  exact ⟨h1, h2, (hacts _ hself).1, h3, h4, h5, (hacts _ hself).2, h3'⟩

@[expose] def KyShape (a y : G) (Ky : Subgroup G) : Prop :=
  ∃ K₁ K₂ K₃ : Subgroup G, GLAPComponent 3 (cx y) K₁ ∧ GLAPComponent 3 (cx y) K₂ ∧ GLAPComponent 3 (cx y) K₃ ∧
    K₁ ≠ K₂ ∧ K₁ ≠ K₃ ∧ K₂ ≠ K₃ ∧ Ky = K₁ ⊔ K₂ ⊔ K₃ ∧ K₂ = GLBConj a K₁ ∧ K₃ = GLBConj a K₂

theorem Ky_shape_core (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K)
    (hns : ¬ GLAPComponent p (cx y) (Kf p K (Subgroup.zpowers y))) :
    p = 3 ∧ KyShape a y (Kf p K (Subgroup.zpowers y)) := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have haB : a ∈ B := (ac.c105.essential a ha ha1).1
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hd.E₀_el hEE₀
  have hyB : y ∈ B := hd.E₀_B hyE0
  have hcyK : CFSG.Open.IsKGroup ↥(cx y) :=
    isKGroup_of_isKProper hc.ctx.kProper (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hd.y_ne)
  have hay : a ∈ cx y := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel haE hyE)
  have hyaP : IsPGroup p (Subgroup.zpowers a) :=
    isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 haE))
  have hzaEl : IsElemAbelian p (Subgroup.zpowers a) := isElemAbelian_mono hEel (Subgroup.zpowers_le.2 haE)
  have ha3 : a ^ p = 1 := hEel.2 a haE
  have hcs_ay : cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) = cx a ⊓ cx y := casealpha_cs_pair a y
  have hJ : GLAPComponent p (cx y ⊓ cs (Subgroup.zpowers a)) (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := by
    rw [casealpha_cs_zpowers' a, inf_comm, ← hcs_ay]
    exact hkay.Kay_single
  obtain ⟨𝒞, h1, h2, h3, h4⟩ := hin.l105.l103.lemma102.i183 G (cx y) hcyK p hp (Subgroup.zpowers a)
    (Subgroup.zpowers_le.2 hay) hzaEl _ hJ
  have hKy_eq : Kf p K (Subgroup.zpowers y) = closureIn K (GLAPLayer p (cx y)) := by
    rw [Kf, casealpha_cs_zpowers' y]
  have hLy' : GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) ≤ GLAPLayer p (cx y) := by
    rw [hcs_ay, inf_comm, ← casealpha_cs_zpowers' a]
    exact casealpha_layer_cz_le hp hin.l105.lbal hcyK hay hyaP
  have hJK : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤ closureIn K (GLAPLayer p (cx y)) :=
    casealpha_closureIn_mono hLy'
  have hsupeq : (⨆ L ∈ 𝒞, L) = Kf p K (Subgroup.zpowers y) := by
    rw [h2, ← casealpha_closureIn_eq_iSup, hKy_eq]
    apply le_antisymm
    · exact casealpha_closureIn_le hJK (fun g hg => casealpha_le_normalizer_closureIn K _ hg)
    · refine casealpha_closureIn_le ?_ (fun g hg => casealpha_le_normalizer_closureIn _ _ hg)
      exact (casealpha_le_closureIn K (H := GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)))
        (Subgroup.one_mem _)).trans (casealpha_le_closureIn _ (H := GLAPLayer p (cx y)) (Subgroup.one_mem _))
  have hK_ne : K ≠ ⊥ := casealpha_component_ne_bot hd.K_comp
  have hKle : K ≤ Kf p K (Subgroup.zpowers y) := casealpha_le_closureIn K (Subgroup.one_mem _)
  obtain ⟨L₁, hL₁⟩ : ∃ L₁, L₁ ∈ 𝒞 := by
    by_contra hne
    have hbot : (⨆ L ∈ 𝒞, L) = ⊥ := by
      apply le_bot_iff.1
      exact iSup₂_le fun L hL => absurd ⟨L, hL⟩ hne
    have hK0 : Kf p K (Subgroup.zpowers y) = ⊥ := by rw [← hsupeq, hbot]
    exact hK_ne (le_bot_iff.1 (hK0 ▸ hKle))
  have hK₁comp : GLAPComponent p (cx y) L₁ := h1 L₁ hL₁
  have hK21 : GLBConj a L₁ ≠ L₁ := by
    intro he
    apply hns
    have hN : a ∈ Subgroup.normalizer (L₁ : Set G) := mem_normalizer_iff_gLBConj_eq.2 he
    have h𝒞 : ∀ L ∈ 𝒞, L = L₁ := by
      intro L hL
      obtain ⟨e, he', heq⟩ := h4 L₁ hL₁ L hL
      rw [← heq]
      exact mem_normalizer_iff_gLBConj_eq.1 (Subgroup.zpowers_le.2 hN he')
    have hKeq : Kf p K (Subgroup.zpowers y) = L₁ := by
      rw [← hsupeq]
      apply le_antisymm
      · exact iSup₂_le fun L hL => le_of_eq (h𝒞 L hL)
      · exact le_iSup₂ (f := fun L (_ : L ∈ 𝒞) => L) L₁ hL₁
    rw [hKeq]
    exact hK₁comp
  have hrank : p ^ GLATwoLocalRank p ↥(cx y) ≤ Nat.card B := by
    rw [(sstar_triple h.star).1.2.1]
    exact Nat.pow_le_pow_right hp.pos
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_twoLocalRank_le_of_injective hp
        (cx y).subtype Subtype.val_injective)
  have hBcy : B ≤ cx y := fun b' hb' =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute (B_el h) hb' hyB)
  have hnN : ¬ B ≤ Subgroup.normalizer (L₁ : Set G) := fun hle =>
    hK21 (mem_normalizer_iff_gLBConj_eq.1 (hle haB))
  obtain ⟨hp3, -⟩ := hin.i112one p hp hp2 (cx y) L₁ B hcyK hK₁comp (B_el h) hBcy hrank hnN
  have ha3' : a ^ 3 = 1 := hp3 ▸ ha3
  have ha3s : a * a * a = 1 := by
    rw [← pow_three']
    exact ha3'
  have ha3a : a * (a * a) = 1 := by
    rw [← pow_three]
    exact ha3'
  have hcyc : GLBConj a (GLBConj a (GLBConj a L₁)) = L₁ := by
    rw [gLBConj_gLBConj, gLBConj_gLBConj]
    simp only [ha3a, ha3s, gLBConj_one]
  have hcl : ∀ e ∈ Subgroup.zpowers a, GLBConj e L₁ = L₁ ∨ GLBConj e L₁ = GLBConj a L₁ ∨
      GLBConj e L₁ = GLBConj a (GLBConj a L₁) := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    have hk : a ^ (k % 3) = a ^ k := by
      have := zpow_mod_orderOf a k
      rw [orderOf_eq_prime ha3' ha1] at this
      exact_mod_cast this
    have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · left
      rw [← hk, hr, zpow_zero, gLBConj_one]
    · right; left
      rw [← hk, hr, zpow_one]
    · right; right
      rw [← hk, hr, zpow_two, gLBConj_gLBConj]
  have hK2 : GLBConj a L₁ ∈ 𝒞 := h3 L₁ hL₁ a (Subgroup.mem_zpowers a)
  have hK3 : GLBConj a (GLBConj a L₁) ∈ 𝒞 := h3 _ hK2 a (Subgroup.mem_zpowers a)
  have hsup3 : (⨆ L ∈ 𝒞, L) = L₁ ⊔ GLBConj a L₁ ⊔ GLBConj a (GLBConj a L₁) := by
    apply le_antisymm
    · refine iSup₂_le fun L hL => ?_
      obtain ⟨e, he, rfl⟩ := h4 L₁ hL₁ L hL
      rcases hcl e he with h' | h' | h' <;> rw [h']
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact le_iSup₂ (f := fun L (_ : L ∈ 𝒞) => L) L₁ hL₁
      · exact le_iSup₂ (f := fun L (_ : L ∈ 𝒞) => L) _ hK2
      · exact le_iSup₂ (f := fun L (_ : L ∈ 𝒞) => L) _ hK3
  have hKy3 : Kf p K (Subgroup.zpowers y) = L₁ ⊔ GLBConj a L₁ ⊔ GLBConj a (GLBConj a L₁) := by
    rw [← hsupeq, hsup3]
  have hneq12 : L₁ ≠ GLBConj a L₁ := fun h => hK21 h.symm
  have hneq13 : L₁ ≠ GLBConj a (GLBConj a L₁) := by
    intro h
    apply hK21
    have h' := congrArg (GLBConj a) h
    rw [hcyc] at h'
    exact h'
  have hneq23 : GLBConj a L₁ ≠ GLBConj a (GLBConj a L₁) := by
    intro h
    have h' := congrArg (GLBConj a) h
    rw [hcyc] at h'
    exact hK21 (h.trans h')
  subst hp3
  refine ⟨rfl, ?_⟩
  unfold KyShape
  exact ⟨L₁, GLBConj a L₁, GLBConj a (GLBConj a L₁), hK₁comp, h1 _ hK2, h1 _ hK3,
    hneq12, hneq13, hneq23, hKy3, rfl, rfl⟩

theorem Ky_shape_norm (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K)
    (hns : ¬ GLAPComponent p (cx y) (Kf p K (Subgroup.zpowers y))) :
    B ≤ Subgroup.normalizer ((Kf p K (Subgroup.zpowers y) : Subgroup G) : Set G) := by
  classical
  obtain ⟨hp3, hsh⟩ := Ky_shape_core hc hin h ac hd hkay hns
  unfold KyShape at hsh
  obtain ⟨K₁, K₂, K₃, c1, c2, c3, n12, n13, n23, hKy, e2, e3⟩ := hsh
  subst hp3
  have hp : Nat.Prime 3 := hc.ctx.prime
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have haB : a ∈ B := (ac.c105.essential a ha ha1).1
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hyB : y ∈ B := hd.E₀_B hyE0
  have hcyK : CFSG.Open.IsKGroup ↥(cx y) :=
    isKGroup_of_isKProper hc.ctx.kProper (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hd.y_ne)
  have ha3 : a ^ 3 = 1 := (B_el h).2 a haB
  have hzaEl : IsElemAbelian 3 (Subgroup.zpowers a) := isElemAbelian_mono (B_el h) (Subgroup.zpowers_le.2 haB)
  have hBcy : B ≤ cx y := fun b' hb' =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute (B_el h) hb' hyB)
  have hK21 : GLBConj a K₁ ≠ K₁ := fun h' => n12 (h'.symm.trans e2.symm)
  have hnN : ¬ B ≤ Subgroup.normalizer (K₁ : Set G) := fun hle =>
    hK21 (mem_normalizer_iff_gLBConj_eq.1 (hle haB))
  have hrank : 3 ^ GLATwoLocalRank 3 ↥(cx y) ≤ Nat.card B := by
    rw [(sstar_triple h.star).1.2.1]
    exact Nat.pow_le_pow_right hp.pos
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_twoLocalRank_le_of_injective hp
        (cx y).subtype Subtype.val_injective)
  obtain ⟨-, hidx⟩ := hin.i112one 3 hp hp2 (cx y) K₁ B hcyK c1 (B_el h) hBcy hrank hnN
  have haN : Subgroup.zpowers a ≤ Subgroup.normalizer (B ⊓ Subgroup.normalizer (K₁ : Set G) : Subgroup G) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g hg =>
      (isElemAbelian_commute (B_el h) hg.1 haB)))
  have hMa : (B ⊓ Subgroup.normalizer (K₁ : Set G) : Subgroup G) ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨⟨hgB, hgN⟩, hga⟩
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hgp : g ^ 3 = 1 := hzaEl.2 g hga
    have hzg : Subgroup.zpowers g = Subgroup.zpowers a :=
      casealpha_zpowers_eq hp (orderOf_eq_prime ha3 ha1) hgp hga hg1
    have haM : a ∈ B ⊓ Subgroup.normalizer (K₁ : Set G) := by
      have : Subgroup.zpowers a ≤ B ⊓ Subgroup.normalizer (K₁ : Set G) := by
        rw [← hzg]
        exact Subgroup.zpowers_le.2 ⟨hgB, hgN⟩
      exact this (Subgroup.mem_zpowers a)
    exact hK21 (mem_normalizer_iff_gLBConj_eq.1 haM.2)
  have hcard_a : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hsup_eq : (B ⊓ Subgroup.normalizer (K₁ : Set G) : Subgroup G) ⊔ Subgroup.zpowers a = B := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (Subgroup.zpowers_le.2 haB))
    have h1 := card_sup_mul_card_inf_of_le_normalizer haN
    rw [hMa, Subgroup.card_bot, mul_one, hcard_a] at h1
    rw [hidx, h1, mul_comm]
  have hsup_conj : ∀ (g : G) (H J : Subgroup G), GLBConj g (H ⊔ J) = GLBConj g H ⊔ GLBConj g J := by
    intro g H J
    unfold GLBConj
    exact Subgroup.map_sup _ _ _
  have ha3s : a * a * a = 1 := by
    rw [← pow_three']
    exact ha3
  have ha3a : a * (a * a) = 1 := by
    rw [← pow_three]
    exact ha3
  have hcyc : GLBConj a K₃ = K₁ := by
    rw [e3, e2, gLBConj_gLBConj, gLBConj_gLBConj]
    simp only [ha3a, ha3s, gLBConj_one]
  have hm_fix : ∀ g ∈ (B ⊓ Subgroup.normalizer (K₁ : Set G) : Subgroup G),
      GLBConj g (K₁ ⊔ K₂ ⊔ K₃) = K₁ ⊔ K₂ ⊔ K₃ := by
    rintro g ⟨hgB, hgN⟩
    have hg1 : GLBConj g K₁ = K₁ := mem_normalizer_iff_gLBConj_eq.1 hgN
    have hgc : g * a = a * g := isElemAbelian_commute (B_el h) hgB haB
    have hg2 : GLBConj g K₂ = K₂ := by
      rw [e2, gLBConj_gLBConj, ← hgc, ← gLBConj_gLBConj a g K₁, hg1]
    have hg3 : GLBConj g K₃ = K₃ := by
      rw [e3, gLBConj_gLBConj, ← hgc, ← gLBConj_gLBConj a g K₂, hg2]
    rw [hsup_conj, hsup_conj, hg1, hg2, hg3]
  have ha_fix : GLBConj a (K₁ ⊔ K₂ ⊔ K₃) = K₁ ⊔ K₂ ⊔ K₃ := by
    rw [hsup_conj, hsup_conj, ← e2, ← e3, hcyc]
    ac_rfl
  rw [hKy, ← hsup_eq]
  exact sup_le (fun g hg => mem_normalizer_iff_gLBConj_eq.2 (hm_fix g hg))
    (Subgroup.zpowers_le.2 (mem_normalizer_iff_gLBConj_eq.2 ha_fix))

theorem Ky_shape (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K)
    (hns : ¬ GLAPComponent p (cx y) (Kf p K (Subgroup.zpowers y))) :
    p = 3 ∧ KyShape a y (Kf p K (Subgroup.zpowers y)) ∧
      B ≤ Subgroup.normalizer ((Kf p K (Subgroup.zpowers y) : Subgroup G) : Set G) :=
  ⟨(Ky_shape_core hc hin h ac hd hkay hns).1, (Ky_shape_core hc hin h ac hd hkay hns).2,
    Ky_shape_norm hc hin h ac hd hkay hns⟩

@[expose] def KyShapeDiag (a y : G) (J Ky : Subgroup G) : Prop :=
  ∃ K₁ K₂ K₃ : Subgroup G, GLAPComponent 3 (cx y) K₁ ∧ GLAPComponent 3 (cx y) K₂ ∧ GLAPComponent 3 (cx y) K₃ ∧
    K₁ ≠ K₂ ∧ K₁ ≠ K₃ ∧ K₂ ≠ K₃ ∧ Ky = K₁ ⊔ K₂ ⊔ K₃ ∧ K₂ = GLBConj a K₁ ∧ K₃ = GLBConj a K₂ ∧
    (∀ M : Subgroup G, GLAPComponent 3 (cx y) M → M ≤ Ky → M = K₁ ∨ M = K₂ ∨ M = K₃) ∧
    K₁ ≤ J ⊔ centModSubgroup 3 K₁ ∧ K₂ ≤ J ⊔ centModSubgroup 3 K₂ ∧ K₃ ≤ J ⊔ centModSubgroup 3 K₃

private theorem y9x_closureIn_mono {I H H' : Subgroup G} (h : H ≤ H') :
    closureIn I H ≤ closureIn I H' := by
  unfold closureIn
  exact iSup₂_le fun g hg => le_iSup₂_of_le g (h hg) le_rfl

private theorem y9x_comp_mem {K₁ K₂ K₃ : Subgroup G} {y : G}
    (c1 : GLAPComponent 3 (cx y) K₁) (c2 : GLAPComponent 3 (cx y) K₂) (c3 : GLAPComponent 3 (cx y) K₃)
    {M : Subgroup G} (hM : GLAPComponent 3 (cx y) M) (hMle : M ≤ K₁ ⊔ K₂ ⊔ K₃) :
    M = K₁ ∨ M = K₂ ∨ M = K₃ := by
  classical
  set 𝒞 : Set (Subgroup G) := {K₁, K₂, K₃} with h𝒞
  have hcompS : ∀ C ∈ 𝒞, GLAPComponent 3 (cx y) C := by
    intro C hC
    simp only [h𝒞, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl | rfl
    · exact c1
    · exact c2
    · exact c3
  have hsup : (⨆ C : 𝒞, (C : Subgroup G)) = K₁ ⊔ K₂ ⊔ K₃ := by
    apply le_antisymm
    · refine iSup_le fun C => ?_
      have hC := C.2
      simp only [h𝒞, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
      rcases hC with h' | h' | h'
      · rw [h']; exact le_sup_left.trans le_sup_left
      · rw [h']; exact le_sup_right.trans le_sup_left
      · rw [h']; exact le_sup_right
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact le_iSup (fun C : 𝒞 => (C : Subgroup G)) ⟨K₁, by simp [h𝒞]⟩
      · exact le_iSup (fun C : 𝒞 => (C : Subgroup G)) ⟨K₂, by simp [h𝒞]⟩
      · exact le_iSup (fun C : 𝒞 => (C : Subgroup G)) ⟨K₃, by simp [h𝒞]⟩
  have hMsub : M ≤ ⨆ C : 𝒞, (C : Subgroup G) := hsup ▸ hMle
  have hMq := hM.2.2.1
  have hsubn : IsSubnormal (barX 3 (cx y) M) (⨆ C : 𝒞, barX 3 (cx y) (C : Subgroup G)) := by
    have hle := idiag_barX_le_kb hcompS hMsub
    have h1 : IsSubnormal (barX 3 (cx y) M ⊓ (⨆ C : 𝒞, barX 3 (cx y) (C : Subgroup G)))
        ((⊤ : Subgroup (↥(cx y) ⧸ GLAPPrimeCore 3 ↥(cx y))) ⊓
          (⨆ C : 𝒞, barX 3 (cx y) (C : Subgroup G))) :=
      isSubnormal_inf hMq.2.1 _
    rwa [top_inf_eq, inf_eq_left.2 hle] at h1
  have hL : IsComponentOf (barX 3 (cx y) M) (⨆ C : 𝒞, barX 3 (cx y) (C : Subgroup G)) :=
    ⟨idiag_barX_le_kb hcompS hMsub, hsubn, hMq.2.2⟩
  obtain ⟨C, hC, hCeq⟩ := idiag_component_eq hcompS hL
  have hCM : C = M := glaPComponent_unique (hcompS C hC) hM hCeq
  rw [← hCM]
  simp only [h𝒞, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  exact hC

private theorem y9x_conj_closed {S : Set (Subgroup G)} {a y : G}
    (ha : ∀ C ∈ S, GLBConj a C ∈ S) (hai : ∀ C ∈ S, GLBConj a⁻¹ C ∈ S)
    (hy : ∀ C ∈ S, GLBConj y C ∈ S) (hyi : ∀ C ∈ S, GLBConj y⁻¹ C ∈ S) :
    ∀ e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y, ∀ C ∈ S, GLBConj e C ∈ S := by
  have hcl : Subgroup.zpowers a ⊔ Subgroup.zpowers y = Subgroup.closure ({a} ∪ {y} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, Subgroup.closure_union]
  have key : ∀ e ∈ Subgroup.closure ({a} ∪ {y} : Set G),
      (∀ C ∈ S, GLBConj e C ∈ S) ∧ (∀ C ∈ S, GLBConj e⁻¹ C ∈ S) := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · rw [Set.mem_singleton_iff.1 hx]
        exact ⟨ha, hai⟩
      · rw [Set.mem_singleton_iff.1 hx]
        exact ⟨hy, hyi⟩
    | one =>
      refine ⟨fun C hC => ?_, fun C hC => ?_⟩
      · rw [gLBConj_one]; exact hC
      · rw [inv_one, gLBConj_one]; exact hC
    | mul g h _ _ hg hh =>
      refine ⟨fun C hC => ?_, fun C hC => ?_⟩
      · rw [← gLBConj_gLBConj h g C]
        exact hh.1 _ (hg.1 C hC)
      · rw [mul_inv_rev, ← gLBConj_gLBConj g⁻¹ h⁻¹ C]
        exact hg.2 _ (hh.2 C hC)
    | inv g _ hg =>
      refine ⟨hg.2, fun C hC => ?_⟩
      rw [inv_inv]
      exact hg.1 C hC
  rw [hcl]
  intro e he C hC
  exact (key e he).1 C hC

private theorem y9x_layer_cz_le {p : ℕ} (hp : p.Prime) (hLB : LBalanceAt G p)
    {X : Subgroup G} (hXK : CFSG.Open.IsKGroup ↥X) {z : G} (hzX : z ∈ X)
    (hP : IsPGroup p (Subgroup.zpowers z)) :
    GLAPLayer p (X ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)) ≤ GLAPLayer p X := by
  refine glaPLayer_inf_centralizer_le hp hLB ?_ hP ((Subgroup.zpowers_le.2 hzX).trans Subgroup.le_normalizer)
  rw [sup_eq_left.2 (Subgroup.zpowers_le.2 hzX)]
  exact hXK

theorem Ky_shape_diag (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K) (hp3 : p = 3)
    (hsh : KyShape a y (Kf p K (Subgroup.zpowers y))) :
    KyShapeDiag a y (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers y)) := by
  classical
  subst hp3
  have hp : Nat.Prime 3 := hc.ctx.prime
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨K₁, K₂, K₃, c1, c2, c3, n12, n13, n23, hKy, e2, e3⟩ := hsh
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian 3 E := isElemAbelian_mono hd.E₀_el hEE₀
  have hcyK : CFSG.Open.IsKGroup ↥(cx y) :=
    isKGroup_of_isKProper hc.ctx.kProper (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hd.y_ne)
  have ha3 : a ^ 3 = 1 := hEel.2 a haE
  have hy3 : y ^ 3 = 1 := hEel.2 y hyE
  have hcomm : a * y = y * a := isElemAbelian_commute hEel haE hyE
  have hnot : a ∉ Subgroup.zpowers y := by
    intro hmem
    have haF : a ∈ F ⊓ Dgrp b x := ⟨(Subgroup.zpowers_le.2 hd.y_F) hmem, ha⟩
    rw [hd.F_inf, Subgroup.mem_bot] at haF
    exact ha1 haF
  obtain ⟨hDel, hDc⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hcomm ha3 hy3 hd.y_ne hnot
  have hAD : Subgroup.zpowers y ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers y := le_sup_right
  have hindex : ((Subgroup.zpowers y).subgroupOf (Subgroup.zpowers a ⊔ Subgroup.zpowers y)).index = 3 := by
    have h1 := Subgroup.index_mul_card
      (H := (Subgroup.zpowers y).subgroupOf (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
    have h2 : Nat.card ↥((Subgroup.zpowers y).subgroupOf (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv, Nat.card_zpowers,
        orderOf_eq_prime hy3 hd.y_ne]
    rw [h2, hDc] at h1
    omega
  have hJ : GLAPComponent 3 (Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G))
      (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := hkay.Kay_single
  have hcA : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G)) := by
    rw [y9x_cs_zpowers]; exact hcyK
  set 𝒞 : Set (Subgroup G) := {K₁, K₂, K₃} with h𝒞
  have hcompS : ∀ C ∈ 𝒞, GLAPComponent 3 (cx y) C := by
    intro C hC
    simp only [h𝒞, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with h' | h' | h' <;> rw [h'] <;> assumption
  have hsup' : (⨆ C ∈ 𝒞, C) = K₁ ⊔ K₂ ⊔ K₃ := by
    simp only [h𝒞, iSup_insert, iSup_singleton, sup_assoc]
  have hC1 : ∀ C ∈ 𝒞, GLAPComponent 3 (Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G)) C := by
    intro C hC
    rw [y9x_cs_zpowers]
    exact hcompS C hC
  have hLy' : GLAPLayer 3 (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) ≤ GLAPLayer 3 (cx y) := by
    have hay : a ∈ cx y := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel haE hyE)
    have hyaP : IsPGroup 3 (Subgroup.zpowers a) :=
      isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 haE))
    have hcs_ay : cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) = cx a ⊓ cx y := y9x_cs_pair a y
    rw [hcs_ay, inf_comm, ← y9x_cs_zpowers' a]
    exact y9x_layer_cz_le hp hin.l105.lbal hcyK hay hyaP
  have hJle : Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤ closureIn K (GLAPLayer 3 (cx y)) :=
    y9x_closureIn_mono hLy'
  have hKy_eq : Kf 3 K (Subgroup.zpowers y) = closureIn K (GLAPLayer 3 (cx y)) := by
    rw [Kf, y9x_cs_zpowers' y]
  have hJKy : closureIn (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (GLAPLayer 3 (cx y)) =
      Kf 3 K (Subgroup.zpowers y) := by
    rw [hKy_eq]
    apply le_antisymm
    · exact y9x_closureIn_le hJle (y9x_le_normalizer_closureIn K _)
    · refine y9x_closureIn_le ?_ (y9x_le_normalizer_closureIn _ _)
      exact (y9x_le_closureIn K (H := GLAPLayer 3 (Subgroup.centralizer
        ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G))) (Subgroup.one_mem _)).trans
        (y9x_le_closureIn _ (Subgroup.one_mem _))
  have hlayer : (⨆ C ∈ 𝒞, C) = ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G)),
      GLBConj g (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := by
    rw [← y9x_closureIn_eq_iSup, hsup', ← hKy, y9x_cs_zpowers]
    exact hJKy.symm
  have hA1 : GLBConj a K₁ = K₂ := e2.symm
  have hA2 : GLBConj a K₂ = K₃ := e3.symm
  have haa1 : a * (a * a) = 1 := by rw [← pow_three]; exact ha3
  have hA3 : GLBConj a K₃ = K₁ := by
    rw [e3, gLBConj_gLBConj, e2, gLBConj_gLBConj, haa1, gLBConj_one]
  have hinv : a⁻¹ = a * a := inv_eq_of_mul_eq_one_right haa1
  have hmemS : ∀ C ∈ 𝒞, GLBConj a C ∈ 𝒞 := by
    intro C hC
    simp only [h𝒞, Set.mem_insert_iff, Set.mem_singleton_iff] at hC ⊢
    rcases hC with h' | h' | h'
    · rw [h']; exact Or.inr (Or.inl hA1)
    · rw [h']; exact Or.inr (Or.inr hA2)
    · rw [h']; exact Or.inl hA3
  have hmemS' : ∀ C ∈ 𝒞, GLBConj a⁻¹ C ∈ 𝒞 := by
    intro C hC
    rw [hinv, ← gLBConj_gLBConj]
    exact hmemS _ (hmemS C hC)
  have hmemY : ∀ C ∈ 𝒞, GLBConj y C ∈ 𝒞 := by
    intro C hC
    have hyC : GLBConj y C = C := idiag_gLBConj_eq_of_comm (fun c hc =>
      (Subgroup.mem_centralizer_singleton_iff.1 ((hcompS C hC).1 hc)).symm)
    rw [hyC]
    exact hC
  have hmemYi : ∀ C ∈ 𝒞, GLBConj y⁻¹ C ∈ 𝒞 := by
    intro C hC
    have hyC : GLBConj y⁻¹ C = C := idiag_gLBConj_eq_of_comm (fun c hc =>
      (Commute.inv_left (show Commute y c from
        (Subgroup.mem_centralizer_singleton_iff.1 ((hcompS C hC).1 hc)).symm)).eq)
    rw [hyC]
    exact hC
  have hclosed : ∀ C ∈ 𝒞, ∀ e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y, GLBConj e C ∈ 𝒞 :=
    fun C hC e he => y9x_conj_closed hmemS hmemS' hmemY hmemYi e he C hC
  have hD1 : (1 : G) ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y := Subgroup.one_mem _
  have haD : a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have haaD : a * a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y := Subgroup.mul_mem _ haD haD
  have hcond : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y, GLBConj e C = C' := by
    intro C hC C' hC'
    simp only [h𝒞, Set.mem_insert_iff, Set.mem_singleton_iff] at hC hC'
    have hA2' : GLBConj (a * a) K₁ = K₃ := by
      rw [← gLBConj_gLBConj a a K₁, hA1, hA2]
    have hA3' : GLBConj (a * a) K₂ = K₁ := by
      rw [← gLBConj_gLBConj a a K₂, hA2, hA3]
    have hA4' : GLBConj (a * a) K₃ = K₂ := by
      rw [← gLBConj_gLBConj a a K₃, hA3, hA1]
    rcases hC with h1 | h1 | h1 <;> rcases hC' with h2 | h2 | h2 <;> rw [h1, h2]
    · exact ⟨1, hD1, by rw [gLBConj_one]⟩
    · exact ⟨a, haD, hA1⟩
    · exact ⟨a * a, haaD, hA2'⟩
    · exact ⟨a * a, haaD, hA3'⟩
    · exact ⟨1, hD1, by rw [gLBConj_one]⟩
    · exact ⟨a, haD, hA2⟩
    · exact ⟨a, haD, hA3⟩
    · exact ⟨a * a, haaD, hA4'⟩
    · exact ⟨1, hD1, by rw [gLBConj_one]⟩
  have hsep : ∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂ :=
    ⟨K₁, by simp [h𝒞], K₂, by simp [h𝒞], n12⟩
  have hdiag := i183DiagAt_holds G 3 hp hp2 (Subgroup.zpowers y) (Subgroup.zpowers a ⊔ Subgroup.zpowers y)
    (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) 𝒞 hDel hAD hindex hcA hJ hC1 hlayer hclosed hcond hsep
  have hcomp_in : ∀ M : Subgroup G, GLAPComponent 3 (cx y) M → M ≤ K₁ ⊔ K₂ ⊔ K₃ →
      M = K₁ ∨ M = K₂ ∨ M = K₃ := fun M hM hMle => y9x_comp_mem c1 c2 c3 hM hMle
  refine ⟨K₁, K₂, K₃, c1, c2, c3, n12, n13, n23, hKy, e2, e3, ?_, ?_, ?_, ?_⟩
  · intro M hM hMle
    exact hcomp_in M hM (hKy ▸ hMle)
  · exact hdiag K₁ (by simp [h𝒞])
  · exact hdiag K₂ (by simp [h𝒞])
  · exact hdiag K₃ (by simp [h𝒞])

@[expose] def KyShapeIso (a y : G) (J Ky : Subgroup G) : Prop :=
  ∃ K₁ K₂ K₃ : Subgroup G, GLAPComponent 3 (cx y) K₁ ∧ GLAPComponent 3 (cx y) K₂ ∧ GLAPComponent 3 (cx y) K₃ ∧
    K₁ ≠ K₂ ∧ K₁ ≠ K₃ ∧ K₂ ≠ K₃ ∧ Ky = K₁ ⊔ K₂ ⊔ K₃ ∧ K₂ = GLBConj a K₁ ∧ K₃ = GLBConj a K₂ ∧
    (∀ M : Subgroup G, GLAPComponent 3 (cx y) M → M ≤ Ky → M = K₁ ∨ M = K₂ ∨ M = K₃) ∧
    ∃ e : PSimple 3 J ≃* PSimple 3 K₁, ∀ g : G, g ∈ Subgroup.normalizer (J : Set G) →
      g ∈ Subgroup.normalizer (K₁ : Set G) → g ∈ Subgroup.normalizer (Ky : Set G) →
        IsoPresAct 3 g J K₁ e ∧ IsoPresAct 3 g K₁ J e.symm

structure YCore (G : Type) [Group G] [Finite G] (p : ℕ) (X K₁ K₂ K₃ Y : Subgroup G) : Prop where
  hp : p.Prime
  c1 : GLAPComponent p X K₁
  c2 : GLAPComponent p X K₂
  c3 : GLAPComponent p X K₃
  n12 : K₁ ≠ K₂
  n13 : K₁ ≠ K₃
  n23 : K₂ ≠ K₃
  hY : Y = K₁ ⊔ K₂ ⊔ K₃
  hYX : Y ≤ X

private theorem y9xE_R_normal {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) {u : G} (hu : u ∈ Y) {r : G}
    (hr : r ∈ GLAPPrimeCoreOf p Y) : u * r * u⁻¹ ∈ GLAPPrimeCoreOf p Y := by
  have hn : Y ≤ Subgroup.normalizer (GLAPPrimeCoreOf p Y : Set G) := le_normalizer_glaPPrimeCoreOf p Y
  exact (Subgroup.mem_normalizer_iff.1 (hn hu) r).1 hr

private def y9xE_N {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) : Subgroup G where
  carrier := {g | g ∈ Y ∧ ∀ h ∈ K₁ ⊔ GLAPPrimeCoreOf p Y, ⁅h, g⁆ ∈ GLAPPrimeCoreOf p Y}
  one_mem' := ⟨Y.one_mem, fun h _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
    refine ⟨Y.mul_mem ha hb, fun h hh => ?_⟩
    have e : ⁅h, a * b⁆ = ⁅h, a⁆ * (a * ⁅h, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (hA h hh) (y9xE_R_normal C ha (hB h hh))
  inv_mem' := by
    rintro a ⟨ha, hA⟩
    refine ⟨Y.inv_mem ha, fun h hh => ?_⟩
    have e : ⁅h, a⁻¹⁆ = a⁻¹ * (⁅h, a⁆)⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 := y9xE_R_normal C (Y.inv_mem ha) ((GLAPPrimeCoreOf p Y).inv_mem (hA h hh))
    rw [inv_inv] at h1
    exact h1

private theorem y9xE_core_le {p : ℕ} {H M : Subgroup G} (hMH : M ≤ H)
    (hn : (M.subgroupOf H).Normal) (hcop : Nat.Coprime p (Nat.card M)) : M ≤ GLAPPrimeCoreOf p H := by
  intro x hx
  have hMH' : Nat.card ↥(M.subgroupOf H) = Nat.card ↥M := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv]
  have hcop' : Nat.Coprime p (Nat.card ↥(M.subgroupOf H)) := by rw [hMH']; exact hcop
  have hle : M.subgroupOf H ≤ CFSG.pPrimeCore p ↥H := le_sSup ⟨hn, hcop'⟩
  have hxH : (⟨x, hMH hx⟩ : ↥H) ∈ M.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]; exact hx
  have hmem := hle hxH
  unfold GLAPPrimeCoreOf
  exact ⟨⟨x, hMH hx⟩, hmem, rfl⟩

private theorem y9xE_comm_R {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {L L' : Subgroup G} (hL : GLAPComponent p X L) (hL' : GLAPComponent p X L') (hne : L ≠ L')
    (hLY : L ≤ Y) (hL'Y : L' ≤ Y) {k k' : G} (hk : k ∈ L) (hk' : k' ∈ L') :
    ⁅k, k'⁆ ∈ GLAPPrimeCoreOf p Y := by
  have hcomm := CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne C.hp hL hL' hne
  have hYc : ⁅L, L'⁆ ≤ Y := by
    refine Subgroup.commutator_le.2 fun h hh g hg => ?_
    have hh' : h ∈ Y := hLY hh
    have hg' : g ∈ Y := hL'Y hg
    rw [commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hh' hg') (Y.inv_mem hh')) (Y.inv_mem hg')
  set M : Subgroup G := GLAPPrimeCoreOf p X ⊓ Y with hM
  have hLM : ⁅L, L'⁆ ≤ M := le_inf hcomm hYc
  have hMY : M ≤ Y := inf_le_right
  have hnormM : (M.subgroupOf Y).Normal := by
    refine ⟨fun n hn y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hyX : (y : G) ∈ X := C.hYX y.2
    have hnorm := le_normalizer_glaPPrimeCoreOf p X hyX
    refine ⟨?_, Y.mul_mem (Y.mul_mem y.2 hn.2) (Y.inv_mem y.2)⟩
    exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 hn.1
  have hcopM : Nat.Coprime p (Nat.card M) := by
    have hdvd : Nat.card ↥M ∣ Nat.card ↥(GLAPPrimeCoreOf p X) :=
      Subgroup.card_dvd_of_le (inf_le_left : M ≤ GLAPPrimeCoreOf p X)
    exact Nat.Coprime.coprime_dvd_right hdvd
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf C.hp X)
  have hfin := y9xE_core_le hMY hnormM hcopM
  exact hfin (hLM (Subgroup.commutator_mem_commutator hk hk'))

private theorem y9xE_le1 {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) : K₁ ≤ Y := by
  rw [C.hY]; exact le_sup_of_le_left le_sup_left

private theorem y9xE_le2 {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) : K₂ ≤ Y := by
  rw [C.hY]; exact le_sup_of_le_left le_sup_right

private theorem y9xE_le3 {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) : K₃ ≤ Y := by
  rw [C.hY]; exact le_sup_right

private theorem y9xE_conj_gen {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {k : G} (hk : k ∈ K₂ ∨ k ∈ K₃ ∨ k ∈ K₁) {x : G} (hx : x ∈ K₁) :
    k * x * k⁻¹ ∈ K₁ ⊔ GLAPPrimeCoreOf p Y := by
  rcases hk with hk | hk | hk
  · have hc : ⁅k, x⁆ ∈ GLAPPrimeCoreOf p Y :=
      y9xE_comm_R C C.c2 C.c1 C.n12.symm (y9xE_le2 C) (y9xE_le1 C) hk hx
    have e : k * x * k⁻¹ = ⁅k, x⁆ * x := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hx)
  · have hc : ⁅k, x⁆ ∈ GLAPPrimeCoreOf p Y :=
      y9xE_comm_R C C.c3 C.c1 C.n13.symm (y9xE_le3 C) (y9xE_le1 C) hk hx
    have e : k * x * k⁻¹ = ⁅k, x⁆ * x := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hx)
  · exact Subgroup.mem_sup_left (Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hx) (Subgroup.inv_mem _ hk))

private theorem y9xE_Mset_normal {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {u : G} (hu : u ∈ Y) {h : G} (hh : h ∈ K₁ ⊔ GLAPPrimeCoreOf p Y) :
    u * h * u⁻¹ ∈ K₁ ⊔ GLAPPrimeCoreOf p Y := by
  have key : ∀ k ∈ Y, (∀ x ∈ K₁, k * x * k⁻¹ ∈ K₁ ⊔ GLAPPrimeCoreOf p Y) →
      ∀ g ∈ K₁ ⊔ GLAPPrimeCoreOf p Y, k * g * k⁻¹ ∈ K₁ ⊔ GLAPPrimeCoreOf p Y := by
    intro k hkY hK g hg
    have hle : K₁ ⊔ GLAPPrimeCoreOf p Y ≤
        (K₁ ⊔ GLAPPrimeCoreOf p Y).comap (MulAut.conj k).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun r hr => ?_)
      · rw [Subgroup.mem_comap]
        exact hK x hx
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right (y9xE_R_normal C hkY hr)
    exact hle hg
  let Sg : Subgroup G :=
    { carrier := {g | g ∈ Y ∧ ∀ g' ∈ K₁ ⊔ GLAPPrimeCoreOf p Y,
        g * g' * g⁻¹ ∈ K₁ ⊔ GLAPPrimeCoreOf p Y ∧ g⁻¹ * g' * g ∈ K₁ ⊔ GLAPPrimeCoreOf p Y}
      one_mem' := ⟨Y.one_mem, fun g' hg' => by simp [hg']⟩
      mul_mem' := by
        rintro a b ⟨ha, hab⟩ ⟨hb, hbb⟩
        refine ⟨Y.mul_mem ha hb, fun g' hg' => ⟨?_, ?_⟩⟩
        · have h1 := (hbb g' hg').1
          have h2 := (hab _ h1).1
          have e : a * b * g' * (a * b)⁻¹ = a * (b * g' * b⁻¹) * a⁻¹ := by group
          rw [e]
          exact h2
        · have h1 := (hab g' hg').2
          have h2 := (hbb _ h1).2
          have e : (a * b)⁻¹ * g' * (a * b) = b⁻¹ * (a⁻¹ * g' * a) * b := by group
          rw [e]
          exact h2
      inv_mem' := by
        rintro a ⟨ha, hab⟩
        refine ⟨Y.inv_mem ha, fun g' hg' => ⟨?_, ?_⟩⟩
        · simpa using (hab g' hg').2
        · simpa using (hab g' hg').1 }
  have hgen : ∀ g : G, (g ∈ K₂ ∨ g ∈ K₃ ∨ g ∈ K₁) → g ∈ Sg := by
    intro g hg
    have hgY : g ∈ Y := by
      rcases hg with h | h | h
      · exact y9xE_le2 C h
      · exact y9xE_le3 C h
      · exact y9xE_le1 C h
    have hg' : g⁻¹ ∈ K₂ ∨ g⁻¹ ∈ K₃ ∨ g⁻¹ ∈ K₁ := by
      rcases hg with h | h | h
      · exact Or.inl (Subgroup.inv_mem _ h)
      · exact Or.inr (Or.inl (Subgroup.inv_mem _ h))
      · exact Or.inr (Or.inr (Subgroup.inv_mem _ h))
    refine ⟨hgY, fun g' hg'' => ⟨key g hgY (fun x hx => y9xE_conj_gen C hg hx) g' hg'', ?_⟩⟩
    have := key g⁻¹ (Y.inv_mem hgY) (fun x hx => by
      have := y9xE_conj_gen C hg' hx
      simpa using this) g' hg''
    simpa using this
  have hY : Y ≤ Sg := by
    rw [C.hY]
    exact sup_le (sup_le (fun k hk => hgen k (Or.inr (Or.inr hk)))
      (fun k hk => hgen k (Or.inl hk))) (fun k hk => hgen k (Or.inr (Or.inl hk)))
  exact ((hY hu).2 h hh).1

private theorem y9xE_mem_N {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) {g : G} :
    g ∈ y9xE_N C ↔ g ∈ Y ∧ ∀ h ∈ K₁ ⊔ GLAPPrimeCoreOf p Y, ⁅h, g⁆ ∈ GLAPPrimeCoreOf p Y := Iff.rfl

private theorem y9xE_N_normal {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {u : G} (hu : u ∈ Y) {g : G} (hg : g ∈ y9xE_N C) : u * g * u⁻¹ ∈ y9xE_N C := by
  rw [y9xE_mem_N] at hg ⊢
  refine ⟨Y.mul_mem (Y.mul_mem hu hg.1) (Y.inv_mem hu), fun h hh => ?_⟩
  have e : ⁅h, u * g * u⁻¹⁆ = u * ⁅u⁻¹ * h * u, g⁆ * u⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hm : u⁻¹ * h * u ∈ K₁ ⊔ GLAPPrimeCoreOf p Y := by
    have := y9xE_Mset_normal C (Y.inv_mem hu) hh
    simpa using this
  exact y9xE_R_normal C hu (hg.2 _ hm)

private theorem y9xE_N_sub_normal {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    ((y9xE_N C).subgroupOf Y).Normal := by
  refine ⟨fun n hn y => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h := y9xE_N_normal C y.2 hn
  simpa [mul_assoc] using h

private instance y9xE_N_sub_normal_inst {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    ((y9xE_N C).subgroupOf Y).Normal := y9xE_N_sub_normal C

open CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator in
open scoped Pointwise in
private theorem y9xE_i183_elem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (A D J : Subgroup G)
    (𝒞 : Set (Subgroup G)) (hD : IsElemAbelian p D) (hAD : A ≤ D) (hidx : (A.subgroupOf D).index = p)
    (_hX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (A : Set G)))
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J)
    (hcomp : ∀ C ∈ 𝒞, GLAPComponent p (Subgroup.centralizer (A : Set G)) C)
    (hsup : (⨆ C ∈ 𝒞, C) = ⨆ g ∈ GLAPLayer p (Subgroup.centralizer (A : Set G)), GLBConj g J)
    (hinv : ∀ C ∈ 𝒞, ∀ e ∈ D, GLBConj e C ∈ 𝒞)
    (htrans : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ D, GLBConj e C = C')
    (hne0 : ∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂) :
    ∀ C ∈ 𝒞, ∀ m ∈ C, ∃ j ∈ J, ∃ n ∈ centModSubgroup p C, m = j * n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := Subgroup.centralizer (A : Set G) with hXdef
  have hAX : ∀ a ∈ A, ∀ x ∈ X, a * x = x * a := fun a ha x hx =>
    Subgroup.mem_centralizer_iff.1 hx a ha
  have hne : ∀ C ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₂ ≠ C := by
    intro C hC
    obtain ⟨C₁, h₁, C₂, h₂, h12⟩ := hne0
    by_cases h : C = C₁
    · exact ⟨C₂, h₂, fun e => h12 (e.trans h).symm⟩
    · exact ⟨C₁, h₁, fun e => h e.symm⟩
  obtain ⟨d, hd, hdA⟩ : ∃ d ∈ D, d ∉ A := by
    by_contra hcon
    push Not at hcon
    have h1 : A.relIndex D = 1 := Subgroup.relIndex_eq_one.2 (fun x hx => hcon x hx)
    have h2 : A.relIndex D = p := hidx
    rw [h2] at h1
    exact (hp.one_lt.ne') h1
  have hdX : d ∈ X := Subgroup.mem_centralizer_iff.2 (fun a ha => idiag_commute hD (hAD ha) hd)
  have hdp : d ^ p = 1 := hD.2 d hd
  have hzd : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.2 hd
  have hJX : J ≤ X := hJ.1.trans (Subgroup.centralizer_le (fun x hx => hAD hx))
  have hHX : Subgroup.centralizer (D : Set G) ≤ X :=
    Subgroup.centralizer_le (fun x hx => hAD hx)
  set Kb : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := ⨆ C' : 𝒞, barX p X (C' : Subgroup G) with hKb
  set E : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := barX p X (Subgroup.zpowers d) with hE
  have hlay : GLALayer Kb = Kb := by
    refine le_antisymm (i25_layer_le Kb) ?_
    exact iSup_le fun C' => i25_le_layer (idiag_barX_isComponent hcomp C'.2)
  have hEnorm : E ≤ Subgroup.normalizer (Kb : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    idiag_E_le_normalizer hinv hd hdX
  have hEab : IsElemAbelian p E := isElemAbelian_barX (idiag_elemAbelian_zpowers hdp)
  have htr : ∀ L L' : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X), IsComponentOf L Kb →
      IsComponentOf L' Kb → ∃ e ∈ E, GLBConj e L = L' := fun L L' hL hL' =>
    idiag_trans hp hD hAD hidx hd hdA hdX hAX hcomp htrans hL hL'
  have hfree : ∀ e ∈ E, e ≠ 1 → ∀ L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X),
      IsComponentOf L Kb → GLBConj e L ≠ L := fun e he he1 L hL =>
    idiag_free hp hD hAD hidx hd hdA hdX hAX hcomp hne htrans he he1 hL
  have hI25 := input2_5_proved _ p hp Kb E hlay hEnorm hEab htr hfree
  obtain ⟨hI25a, hI25b⟩ := hI25
  obtain ⟨Dl, hDl⟩ : ∃ Dl : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X),
      Dl = GLALayer (Kb ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X))) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X),
      W = (Subgroup.center ↥Kb).map Kb.subtype ⊓
        Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := ⟨_, rfl⟩
  have hsplit : Kb ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) = Dl ⊔ W := by
    rw [hDl, hW]
    exact hI25b
  have hWK : W ≤ Kb := by
    rw [hW]
    exact inf_le_left.trans (Subgroup.map_subtype_le _)
  have hWc : ∀ w ∈ W, ∀ g ∈ Kb, Commute w g := by
    intro w hw g hg
    rw [hW] at hw
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw.1
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)).symm
  have hJsup : J ≤ ⨆ C' : 𝒞, (C' : Subgroup G) := by
    have h1 : J ≤ ⨆ g ∈ GLAPLayer p X, GLBConj g J :=
      (gLBConj_one J).symm.le.trans
        (le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer p X) => GLBConj g J) (1 : G) (Subgroup.one_mem _))
    rw [← hsup] at h1
    exact h1.trans (iSup_subtype' (p := fun C : Subgroup G => C ∈ 𝒞) (f := fun C _ => C)).le
  have hbarJK : barX p X J ≤ Kb := idiag_barX_le_kb hcomp hJsup
  have hbarJC : barX p X J ≤ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    idiag_barX_le_centralizer hJ.1 hd hzd
  have hbarJKC : barX p X J ≤ Kb ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    le_inf hbarJK hbarJC
  have hJDl : barX p X J ≤ Dl := idiag_barX_le_layer hJ hJX hsplit inf_le_left hWK hWc hbarJKC
  have hDle : Dl ≤ Kb ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rw [hsplit]
    exact le_sup_left
  have hDlC : Dl ≤ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    fun x hx => (hDle hx).2
  have hDlbar : Dl ≤ barX p X (Subgroup.centralizer (D : Set G)) :=
    idiag_layer_le hp hAD hidx hAX hD hd hdX hdA hDlC
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Subgroup G, C₁ ∈ 𝒞 := by
    obtain ⟨C₁, h₁, -⟩ := hne0
    exact ⟨C₁, h₁⟩
  obtain ⟨Z, hZn, hZc, ⟨φ⟩⟩ := hI25a _ (idiag_barX_isComponent hcomp hC₁)
  have hDq : CFSG.Open.IsQuasisimple ↥Dl := by
    rw [hDl]
    exact Components.quasisimple_of_equiv φ
      (Quasisimple.central_quotient (idiag_barX_isComponent hcomp hC₁).2.2 Z hZc)
  have hDJ : Dl ≤ barX p X J :=
    idiag_layer_le_barX hp hJ hJX hHX hDlbar hDq hJDl
  intro C hC m hm
  obtain ⟨j, hj, n, hn, rfl⟩ := idiag_lift hp hp2 hAD hidx hD hd hdX hdA hAX hcomp hinv hne htrans
    hC hm hKb hsplit hWK hWc hDJ
  exact ⟨j, hj, n, hn, rfl⟩

open CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator in
open scoped Pointwise in
private theorem y9xE_cov {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg 3 B x L b) (ac : AlphaCtx G 3 B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hc : S10Ctx G 3) (hin : AlphaInputs G 3) (hd : AlphaData 3 B x L b a E₀ F y E K)
    (hkay : AlphaKay 3 x a y K) (K₁ K₂ K₃ : Subgroup G)
    (c1 : GLAPComponent 3 (cx y) K₁) (c2 : GLAPComponent 3 (cx y) K₂) (c3 : GLAPComponent 3 (cx y) K₃)
    (n12 : K₁ ≠ K₂) (n13 : K₁ ≠ K₃) (n23 : K₂ ≠ K₃)
    (hKy : Kf 3 K (Subgroup.zpowers y) = K₁ ⊔ K₂ ⊔ K₃) (e2 : K₂ = GLBConj a K₁) (e3 : K₃ = GLBConj a K₂) :
    ∀ k ∈ K₁, ∃ j ∈ Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y), ∃ n ∈ centModSubgroup 3 K₁,
      k = j * n := by
  classical
  have hp : Nat.Prime 3 := hc.ctx.prime
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian 3 E := isElemAbelian_mono hd.E₀_el hEE₀
  have hcyK : CFSG.Open.IsKGroup ↥(cx y) :=
    isKGroup_of_isKProper hc.ctx.kProper (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hd.y_ne)
  have ha3 : a ^ 3 = 1 := hEel.2 a haE
  have hy3 : y ^ 3 = 1 := hEel.2 y hyE
  have hcomm : a * y = y * a := isElemAbelian_commute hEel haE hyE
  have hnot : a ∉ Subgroup.zpowers y := by
    intro hmem
    have haF : a ∈ F ⊓ Dgrp b x := ⟨(Subgroup.zpowers_le.2 hd.y_F) hmem, ha⟩
    rw [hd.F_inf, Subgroup.mem_bot] at haF
    exact ha1 haF
  obtain ⟨hDel, hDc⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hcomm ha3 hy3 hd.y_ne hnot
  have hAD : Subgroup.zpowers y ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers y := le_sup_right
  have hindex : ((Subgroup.zpowers y).subgroupOf (Subgroup.zpowers a ⊔ Subgroup.zpowers y)).index = 3 := by
    have h1 := Subgroup.index_mul_card
      (H := (Subgroup.zpowers y).subgroupOf (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
    have h2 : Nat.card ↥((Subgroup.zpowers y).subgroupOf (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv, Nat.card_zpowers,
        orderOf_eq_prime hy3 hd.y_ne]
    rw [h2, hDc] at h1
    omega
  have hJ : GLAPComponent 3 (Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G))
      (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := hkay.Kay_single
  have hcA : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G)) := by
    rw [y9x_cs_zpowers]; exact hcyK
  set 𝒞 : Set (Subgroup G) := {K₁, K₂, K₃} with h𝒞
  have hcompS : ∀ C ∈ 𝒞, GLAPComponent 3 (cx y) C := by
    intro C hC
    simp only [h𝒞, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with h' | h' | h' <;> rw [h'] <;> assumption
  have hsup' : (⨆ C ∈ 𝒞, C) = K₁ ⊔ K₂ ⊔ K₃ := by
    simp only [h𝒞, iSup_insert, iSup_singleton, sup_assoc]
  have hC1 : ∀ C ∈ 𝒞, GLAPComponent 3 (Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G)) C := by
    intro C hC
    rw [y9x_cs_zpowers]
    exact hcompS C hC
  have hLy' : GLAPLayer 3 (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) ≤ GLAPLayer 3 (cx y) := by
    have hay : a ∈ cx y := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel haE hyE)
    have hyaP : IsPGroup 3 (Subgroup.zpowers a) :=
      isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 haE))
    have hcs_ay : cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) = cx a ⊓ cx y := y9x_cs_pair a y
    rw [hcs_ay, inf_comm, ← y9x_cs_zpowers' a]
    exact y9x_layer_cz_le hp hin.l105.lbal hcyK hay hyaP
  have hJle : Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤ closureIn K (GLAPLayer 3 (cx y)) :=
    y9x_closureIn_mono hLy'
  have hKy_eq : Kf 3 K (Subgroup.zpowers y) = closureIn K (GLAPLayer 3 (cx y)) := by
    rw [Kf, y9x_cs_zpowers' y]
  have hJKy : closureIn (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (GLAPLayer 3 (cx y)) =
      Kf 3 K (Subgroup.zpowers y) := by
    rw [hKy_eq]
    apply le_antisymm
    · exact y9x_closureIn_le hJle (y9x_le_normalizer_closureIn K _)
    · refine y9x_closureIn_le ?_ (y9x_le_normalizer_closureIn _ _)
      exact (y9x_le_closureIn K (H := GLAPLayer 3 (Subgroup.centralizer
        ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G))) (Subgroup.one_mem _)).trans
        (y9x_le_closureIn _ (Subgroup.one_mem _))
  have hlayer : (⨆ C ∈ 𝒞, C) = ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G)),
      GLBConj g (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := by
    rw [← y9x_closureIn_eq_iSup, hsup', ← hKy, y9x_cs_zpowers]
    exact hJKy.symm
  have hA1 : GLBConj a K₁ = K₂ := e2.symm
  have hA2 : GLBConj a K₂ = K₃ := e3.symm
  have haa1 : a * (a * a) = 1 := by rw [← pow_three]; exact ha3
  have hA3 : GLBConj a K₃ = K₁ := by
    rw [e3, gLBConj_gLBConj, e2, gLBConj_gLBConj, haa1, gLBConj_one]
  have hinv : a⁻¹ = a * a := inv_eq_of_mul_eq_one_right haa1
  have hmemS : ∀ C ∈ 𝒞, GLBConj a C ∈ 𝒞 := by
    intro C hC
    simp only [h𝒞, Set.mem_insert_iff, Set.mem_singleton_iff] at hC ⊢
    rcases hC with h' | h' | h'
    · rw [h']; exact Or.inr (Or.inl hA1)
    · rw [h']; exact Or.inr (Or.inr hA2)
    · rw [h']; exact Or.inl hA3
  have hmemS' : ∀ C ∈ 𝒞, GLBConj a⁻¹ C ∈ 𝒞 := by
    intro C hC
    rw [hinv, ← gLBConj_gLBConj]
    exact hmemS _ (hmemS C hC)
  have hmemY : ∀ C ∈ 𝒞, GLBConj y C ∈ 𝒞 := by
    intro C hC
    have hyC : GLBConj y C = C := idiag_gLBConj_eq_of_comm (fun c hc =>
      (Subgroup.mem_centralizer_singleton_iff.1 ((hcompS C hC).1 hc)).symm)
    rw [hyC]
    exact hC
  have hmemYi : ∀ C ∈ 𝒞, GLBConj y⁻¹ C ∈ 𝒞 := by
    intro C hC
    have hyC : GLBConj y⁻¹ C = C := idiag_gLBConj_eq_of_comm (fun c hc =>
      (Commute.inv_left (show Commute y c from
        (Subgroup.mem_centralizer_singleton_iff.1 ((hcompS C hC).1 hc)).symm)).eq)
    rw [hyC]
    exact hC
  have hclosed : ∀ C ∈ 𝒞, ∀ e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y, GLBConj e C ∈ 𝒞 :=
    fun C hC e he => y9x_conj_closed hmemS hmemS' hmemY hmemYi e he C hC
  have hD1 : (1 : G) ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y := Subgroup.one_mem _
  have haD : a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have haaD : a * a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y := Subgroup.mul_mem _ haD haD
  have hcond : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers y, GLBConj e C = C' := by
    intro C hC C' hC'
    simp only [h𝒞, Set.mem_insert_iff, Set.mem_singleton_iff] at hC hC'
    have hA2' : GLBConj (a * a) K₁ = K₃ := by
      rw [← gLBConj_gLBConj a a K₁, hA1, hA2]
    have hA3' : GLBConj (a * a) K₂ = K₁ := by
      rw [← gLBConj_gLBConj a a K₂, hA2, hA3]
    have hA4' : GLBConj (a * a) K₃ = K₂ := by
      rw [← gLBConj_gLBConj a a K₃, hA3, hA1]
    rcases hC with h1 | h1 | h1 <;> rcases hC' with h2 | h2 | h2 <;> rw [h1, h2]
    · exact ⟨1, hD1, by rw [gLBConj_one]⟩
    · exact ⟨a, haD, hA1⟩
    · exact ⟨a * a, haaD, hA2'⟩
    · exact ⟨a * a, haaD, hA3'⟩
    · exact ⟨1, hD1, by rw [gLBConj_one]⟩
    · exact ⟨a, haD, hA2⟩
    · exact ⟨a, haD, hA3⟩
    · exact ⟨a * a, haaD, hA4'⟩
    · exact ⟨1, hD1, by rw [gLBConj_one]⟩
  have hsep : ∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂ :=
    ⟨K₁, by simp [h𝒞], K₂, by simp [h𝒞], n12⟩
  have hcov_elem := y9xE_i183_elem hp hp2 (Subgroup.zpowers y) (Subgroup.zpowers a ⊔ Subgroup.zpowers y)
    (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) 𝒞 hDel hAD hindex hcA hJ hC1 hlayer hclosed hcond hsep
  intro k hk
  exact hcov_elem K₁ (by simp [h𝒞]) k hk

private theorem y9xE_normalizes_R {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    GLBConj g (GLAPPrimeCoreOf p Y) = GLAPPrimeCoreOf p Y := by
  have hY : GLBConj g Y = Y := mem_normalizer_iff_gLBConj_eq.1 hg
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_gLBConj p g Y
  rw [hY] at h
  exact h.symm

private theorem y9xE_normalizes_Mset {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G)) (hgK : g ∈ Subgroup.normalizer (K₁ : Set G)) :
    ∀ h ∈ K₁ ⊔ GLAPPrimeCoreOf p Y, g * h * g⁻¹ ∈ K₁ ⊔ GLAPPrimeCoreOf p Y := by
  have hR := y9xE_normalizes_R C hg
  have hgR : g ∈ Subgroup.normalizer (GLAPPrimeCoreOf p Y : Set G) := mem_normalizer_iff_gLBConj_eq.2 hR
  have hle : K₁ ⊔ GLAPPrimeCoreOf p Y ≤
      (K₁ ⊔ GLAPPrimeCoreOf p Y).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun x hx => ?_) (fun r hr => ?_)
    · rw [Subgroup.mem_comap]
      show g * x * g⁻¹ ∈ _
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hgK x).1 hx)
    · rw [Subgroup.mem_comap]
      show g * r * g⁻¹ ∈ _
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hgR r).1 hr)
  intro h hh
  exact hle hh

private theorem y9xE_N_conj {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {g : G} (hgY : g ∈ Subgroup.normalizer (Y : Set G)) (hgK : g ∈ Subgroup.normalizer (K₁ : Set G))
    {x : G} (hx : x ∈ y9xE_N C) : g⁻¹ * x * g ∈ y9xE_N C := by
  have hgR : g ∈ Subgroup.normalizer (GLAPPrimeCoreOf p Y : Set G) :=
    mem_normalizer_iff_gLBConj_eq.2 (y9xE_normalizes_R C hgY)
  have hg'Y : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) := Subgroup.inv_mem _ hgY
  have hg'K : g⁻¹ ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.inv_mem _ hgK
  have hg'R : g⁻¹ ∈ Subgroup.normalizer (GLAPPrimeCoreOf p Y : Set G) := Subgroup.inv_mem _ hgR
  refine ⟨?_, fun h hh => ?_⟩
  · have := (Subgroup.mem_normalizer_iff.1 hg'Y x).1 hx.1
    simpa using this
  · have hm : g * h * g⁻¹ ∈ K₁ ⊔ GLAPPrimeCoreOf p Y := y9xE_normalizes_Mset C hgY hgK h hh
    have hr := hx.2 _ hm
    have e : ⁅h, g⁻¹ * x * g⁆ = g⁻¹ * ⁅g * h * g⁻¹, x⁆ * g := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.1 hg'R _).1 hr
    simpa using this

private abbrev y9xE_Q {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) : Type :=
  ↥Y ⧸ (y9xE_N C).subgroupOf Y

private noncomputable abbrev y9xE_piY {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    ↥Y →* y9xE_Q C :=
  QuotientGroup.mk' ((y9xE_N C).subgroupOf Y)

private noncomputable abbrev y9xE_iota {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    ↥K₁ →* y9xE_Q C :=
  (y9xE_piY C).comp (Subgroup.inclusion (y9xE_le1 C))

private theorem y9xE_N_le_Y {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    y9xE_N C ≤ Y := fun _ hg => hg.1

private def y9xE_Cl {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) (k : G) (hk : k ∈ Y) :
    Subgroup G where
  carrier := {h | h ∈ Y ∧ ⁅h, k⁆ ∈ GLAPPrimeCoreOf p Y}
  one_mem' := ⟨Y.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
    refine ⟨Y.mul_mem ha hb, ?_⟩
    have e : ⁅a * b, k⁆ = a * ⁅b, k⁆ * a⁻¹ * ⁅a, k⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (y9xE_R_normal C ha hB) hA
  inv_mem' := by
    rintro a ⟨ha, hA⟩
    refine ⟨Y.inv_mem ha, ?_⟩
    have e : ⁅a⁻¹, k⁆ = a⁻¹ * (⁅a, k⁆)⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 := y9xE_R_normal C (Y.inv_mem ha) ((GLAPPrimeCoreOf p Y).inv_mem hA)
    simpa using h1

private theorem y9xE_le_N {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {k : G} (hk : k ∈ K₂ ∨ k ∈ K₃) : k ∈ y9xE_N C := by
  have hkY : k ∈ Y := by
    rcases hk with h | h
    · exact y9xE_le2 C h
    · exact y9xE_le3 C h
  refine ⟨hkY, fun h hh => ?_⟩
  have hsub : K₁ ⊔ GLAPPrimeCoreOf p Y ≤ y9xE_Cl C k hkY := by
    refine sup_le (fun x hx => ?_) (fun r hr => ?_)
    · have hc : ⁅x, k⁆ ∈ GLAPPrimeCoreOf p Y := by
        rcases hk with h' | h'
        · exact y9xE_comm_R C C.c1 C.c2 C.n12 (y9xE_le1 C) (y9xE_le2 C) hx h'
        · exact y9xE_comm_R C C.c1 C.c3 C.n13 (y9xE_le1 C) (y9xE_le3 C) hx h'
      exact ⟨y9xE_le1 C hx, hc⟩
    · refine ⟨(Subgroup.map_subtype_le _) hr, ?_⟩
      have e : ⁅r, k⁆ = r * (k * r⁻¹ * k⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hr (y9xE_R_normal C hkY (Subgroup.inv_mem _ hr))
  exact (hsub hh).2

private theorem y9xE_sup_N {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    K₁ ⊔ y9xE_N C = Y := by
  apply le_antisymm
  · exact sup_le (y9xE_le1 C) (fun g hg => hg.1)
  · have hsup : K₁ ⊔ K₂ ⊔ K₃ ≤ K₁ ⊔ y9xE_N C :=
      sup_le (sup_le le_sup_left (fun k hk => Subgroup.mem_sup_right (y9xE_le_N C (Or.inl hk))))
        (fun k hk => Subgroup.mem_sup_right (y9xE_le_N C (Or.inr hk)))
    calc Y = K₁ ⊔ K₂ ⊔ K₃ := C.hY
      _ ≤ K₁ ⊔ y9xE_N C := hsup

private theorem y9xE_surj_K1 {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    (q : y9xE_Q C) : ∃ k : ↥K₁, y9xE_piY C (Subgroup.inclusion (y9xE_le1 C) k) = q := by
  have hsup : K₁.subgroupOf Y ⊔ (y9xE_N C).subgroupOf Y = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (y9xE_le1 C) (y9xE_N_le_Y C), y9xE_sup_N C, Subgroup.subgroupOf_self]
  have hS : (⊤ : Subgroup ↥Y) ≤ (Subgroup.map (y9xE_piY C) (K₁.subgroupOf Y)).comap (y9xE_piY C) := by
    rw [← hsup]
    refine sup_le (fun k hk => ?_) (fun n hn => ?_)
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_map_of_mem _ hk
    · rw [Subgroup.mem_comap]
      have h1 : y9xE_piY C n = 1 := (QuotientGroup.eq_one_iff n).2 hn
      rw [h1]
      exact Subgroup.one_mem _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hyS : y9xE_piY C y ∈ Subgroup.map (y9xE_piY C) (K₁.subgroupOf Y) :=
    hS (Subgroup.mem_top y)
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hyS
  exact ⟨⟨(z : G), (Subgroup.mem_subgroupOf).1 hz⟩, hzy⟩

private theorem y9xE_iota_surj {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    Function.Surjective (y9xE_iota C) := fun q => y9xE_surj_K1 C q

private theorem y9xE_iota_eq_one_iff {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    (k : ↥K₁) : y9xE_iota C k = 1 ↔ (k : G) ∈ y9xE_N C := by
  show QuotientGroup.mk' ((y9xE_N C).subgroupOf Y) (Subgroup.inclusion (y9xE_le1 C) k) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

private noncomputable abbrev y9xE_pi1 {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    ↥K₁ →* PSimple p K₁ :=
  (QuotientGroup.mk' (Subgroup.center (PQuot p K₁))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥K₁))

private theorem y9xE_conj_inv_R_iff {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {u X' : G} (hu : u ∈ Y) :
    u⁻¹ * X' * u ∈ GLAPPrimeCoreOf p Y ↔ X' ∈ GLAPPrimeCoreOf p Y := by
  constructor
  · intro h
    have h' := y9xE_R_normal C hu h
    have e : u * (u⁻¹ * X' * u) * u⁻¹ = X' := by group
    rw [e] at h'
    exact h'
  · intro h
    have h' := y9xE_R_normal C (Y.inv_mem hu) h
    simpa using h'

private theorem y9xE_K1_R {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    K₁ ⊓ GLAPPrimeCoreOf p Y = GLAPPrimeCoreOf p K₁ :=
  CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_inf_eq_of_isSubnormal C.hp
    (isSubnormal_of_le_of_le C.c1.2.1 (y9xE_le1 C) C.hYX)

private theorem y9xE_mem_coreOf_iff {p : ℕ} {L : Subgroup G} (x : ↥L) :
    (x : G) ∈ GLAPPrimeCoreOf p L ↔ x ∈ GLAPPrimeCore p ↥L := by
  unfold GLAPPrimeCoreOf
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem y9xE_core_iff_R {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    (x : ↥K₁) : x ∈ GLAPPrimeCore p ↥K₁ ↔ (x : G) ∈ GLAPPrimeCoreOf p Y := by
  rw [← y9xE_mem_coreOf_iff, ← y9xE_K1_R C]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

private theorem y9xE_mem_N_iff {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {k : G} (hk : k ∈ K₁) : k ∈ y9xE_N C ↔ ∀ l ∈ K₁, ⁅l, k⁆ ∈ GLAPPrimeCoreOf p Y := by
  constructor
  · intro hN l hl
    exact hN.2 l (Subgroup.mem_sup_left hl)
  · intro hl
    refine ⟨y9xE_le1 C hk, fun h hh => ?_⟩
    have hsub : K₁ ⊔ GLAPPrimeCoreOf p Y ≤ y9xE_Cl C k (y9xE_le1 C hk) := by
      refine sup_le (fun x hx => ⟨y9xE_le1 C hx, ?_⟩) (fun r hr => ⟨(Subgroup.map_subtype_le _) hr, ?_⟩)
      · exact hl x hx
      · have e : ⁅r, k⁆ = r * (k * r⁻¹ * k⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ hr (y9xE_R_normal C (y9xE_le1 C hk) (Subgroup.inv_mem _ hr))
    exact (hsub hh).2

private theorem y9xE_key_iff {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {k : G} (hk : k ∈ K₁) :
    (∀ l : ↥K₁, (l * (⟨k, hk⟩ : ↥K₁))⁻¹ * ((⟨k, hk⟩ : ↥K₁) * l) ∈ GLAPPrimeCore p ↥K₁) ↔
      k ∈ y9xE_N C := by
  rw [y9xE_mem_N_iff C hk]
  have hkY : k ∈ Y := y9xE_le1 C hk
  have hconj : ∀ l : G, (l * k)⁻¹ * (k * l) = k⁻¹ * ⁅l⁻¹, k⁆ * k := by
    intro l
    simp only [commutatorElement_def]
    group
  have hmemR : ∀ l ∈ K₁, (l * k)⁻¹ * (k * l) ∈ GLAPPrimeCoreOf p Y ↔
      ⁅l⁻¹, k⁆ ∈ GLAPPrimeCoreOf p Y := by
    intro l _
    rw [hconj l]
    exact y9xE_conj_inv_R_iff C hkY
  constructor
  · intro h l hl
    have hl' : l⁻¹ ∈ K₁ := Subgroup.inv_mem _ hl
    have h1 := (y9xE_core_iff_R C _).1 (h ⟨l⁻¹, hl'⟩)
    have h2 : ((((⟨l⁻¹, hl'⟩ : ↥K₁) * ⟨k, hk⟩)⁻¹ * (⟨k, hk⟩ * ⟨l⁻¹, hl'⟩) : ↥K₁) : G) =
        (l⁻¹ * k)⁻¹ * (k * l⁻¹) := by
      simp
    rw [h2] at h1
    have h3 := (hmemR l⁻¹ hl').1 h1
    rw [inv_inv] at h3
    exact h3
  · intro h l
    have hl' : (l : G) ∈ K₁ := l.2
    have h1 : ((l : G) * k)⁻¹ * (k * (l : G)) ∈ GLAPPrimeCoreOf p Y := by
      refine (hmemR (l : G) hl').2 ?_
      exact h (l : G)⁻¹ (Subgroup.inv_mem _ hl')
    have h2 : (l * (⟨k, hk⟩ : ↥K₁))⁻¹ * ((⟨k, hk⟩ : ↥K₁) * l) ∈ GLAPPrimeCore p ↥K₁ := by
      rw [y9xE_core_iff_R C]
      have h3 : (((l * (⟨k, hk⟩ : ↥K₁))⁻¹ * ((⟨k, hk⟩ : ↥K₁) * l) : ↥K₁) : G) =
          ((l : G) * k)⁻¹ * (k * (l : G)) := by
        simp
      rw [h3]
      exact h1
    exact h2

private theorem y9xE_mk_center_iff {p : ℕ} {L : Subgroup G} (k : ↥L) :
    (QuotientGroup.mk k : PQuot p L) ∈ Subgroup.center (PQuot p L) ↔
      ∀ l : ↥L, (l * k)⁻¹ * (k * l) ∈ GLAPPrimeCore p ↥L := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h l
    have h1 := h (QuotientGroup.mk l)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h1
    exact QuotientGroup.eq.1 h1
  · intro h g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact QuotientGroup.eq.2 (h l)

private theorem y9xE_pi1_eq_one_iff {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    (k : ↥K₁) : y9xE_pi1 C k = 1 ↔ (k : G) ∈ y9xE_N C := by
  show (QuotientGroup.mk (QuotientGroup.mk k : PQuot p K₁) : PSimple p K₁) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, y9xE_mk_center_iff]
  exact y9xE_key_iff C k.2

private theorem y9xE_ker_eq {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    (y9xE_pi1 C).ker = (y9xE_iota C).ker := by
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, y9xE_pi1_eq_one_iff, y9xE_iota_eq_one_iff]

private theorem y9xE_pi1_surj {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    Function.Surjective (y9xE_pi1 C) := by
  intro q
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  exact ⟨k, rfl⟩

private noncomputable def y9xE_Psi {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    y9xE_Q C ≃* PSimple p K₁ :=
  (QuotientGroup.quotientKerEquivOfSurjective (y9xE_iota C) (y9xE_iota_surj C)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (y9xE_ker_eq C).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (y9xE_pi1 C) (y9xE_pi1_surj C)))

private noncomputable abbrev y9xE_W (p : ℕ) (J : Subgroup G) : Subgroup ↥J :=
  (Subgroup.center (PQuot p J)).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥J))

private noncomputable def y9xE_eJ {p : ℕ} (J : Subgroup G) [Fact p.Prime] :
    PSimple p J ≃* ↥J ⧸ y9xE_W p J := by
  classical
  have hZ : Subgroup.center (PQuot p J) =
      (y9xE_W p J).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) :=
    (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _).symm
  have hOW : GLAPPrimeCore p ↥J ≤ y9xE_W p J := fun x hx => by
    refine Subgroup.mem_comap.2 ?_
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [h1]
    exact Subgroup.one_mem _
  haveI : ((y9xE_W p J).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J))).Normal := by
    rw [← hZ]; infer_instance
  haveI : (y9xE_W p J).Normal := by
    unfold y9xE_W; infer_instance
  exact (QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientQuotientEquivQuotient (GLAPPrimeCore p ↥J) (y9xE_W p J) hOW)

private theorem y9xE_center_quot_bot {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ := by
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Subgroup.center Q)) with h | h
  · exact h
  · exfalso
    have hcomm : commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      have ha : a ∈ Subgroup.center (Q ⧸ Subgroup.center Q) := h ▸ Subgroup.mem_top a
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact Subgroup.mem_center_iff.1 ha b
    have htop : commutator (Q ⧸ Subgroup.center Q) = ⊤ := by
      have h1 : commutator (Q ⧸ Subgroup.center Q) =
          (commutator Q).map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      rw [h1, hQ.1, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [htop] at hcomm
    have hnt : Nontrivial (Q ⧸ Subgroup.center Q) := hQ.2.toNontrivial
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    apply hab
    have ha : a ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) := hcomm ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) := hcomm ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

private theorem y9xE_PSimple_center {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    Subgroup.center (PSimple p K₁) = ⊥ :=
  y9xE_center_quot_bot (isQuasisimple_pQuot_of_glaPComponent C.hp C.c1)

private theorem y9xE_PSimple_simple {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y) :
    IsSimpleGroup (PSimple p K₁) :=
  (isQuasisimple_pQuot_of_glaPComponent C.hp C.c1).2

private noncomputable abbrev y9xE_psiJ {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {J : Subgroup G} (hJY : J ≤ Y) : ↥J →* y9xE_Q C :=
  (y9xE_piY C).comp (Subgroup.inclusion hJY)

private theorem y9xE_T_le_N {p : ℕ} {X X' K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {J : Subgroup G} (hJ : GLAPComponent p X' J) (hJY : J ≤ Y)
    (hsurj : Function.Surjective (y9xE_psiJ C hJY)) :
    GLAPPrimeCoreOf p J ≤ y9xE_N C := by
  classical
  obtain ⟨hJX', hJsn, -, hmin⟩ := hJ
  haveI hsimpleQ : IsSimpleGroup (y9xE_Q C) :=
    (MulEquiv.isSimpleGroup_congr (y9xE_Psi C)).mpr (y9xE_PSimple_simple C)
  haveI : Nontrivial (y9xE_Q C) := hsimpleQ.toNontrivial
  let TJ : Subgroup ↥J := GLAPPrimeCore p ↥J
  have hFn : (TJ.map (y9xE_psiJ C hJY)).Normal := Subgroup.Normal.map inferInstance _ hsurj
  haveI := hFn
  have hψN : ∀ j : ↥J, y9xE_psiJ C hJY j = 1 ↔ (j : G) ∈ y9xE_N C := by
    intro j
    show QuotientGroup.mk' ((y9xE_N C).subgroupOf Y) (Subgroup.inclusion hJY j) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (TJ.map (y9xE_psiJ C hJY)) with hF | hF
  ·
    intro t ht
    obtain ⟨t', ht', hte⟩ := Subgroup.mem_map.1 ht
    have h1 : y9xE_psiJ C hJY t' = 1 := by
      have : y9xE_psiJ C hJY t' ∈ TJ.map (y9xE_psiJ C hJY) := Subgroup.mem_map_of_mem _ ht'
      rw [hF, Subgroup.mem_bot] at this
      exact this
    rw [← hte]
    exact (hψN t').1 h1
  · exfalso
    have hsplit : ∀ j : ↥J, ∃ v : ↥J, (v : G) ∈ y9xE_N C ∧ ∃ t ∈ TJ, j = v * t := by
      intro j
      have hj : y9xE_psiJ C hJY j ∈ TJ.map (y9xE_psiJ C hJY) := by
        rw [hF]; exact Subgroup.mem_top _
      obtain ⟨t, ht, hjt⟩ := Subgroup.mem_map.1 hj
      refine ⟨j * t⁻¹, (hψN _).1 ?_, t, ht, by group⟩
      rw [map_mul, map_inv, hjt, mul_inv_cancel]
    have hcoreX' : ∀ t : ↥J, t ∈ TJ → ((⟨(t : G), hJX' t.2⟩ : ↥X') ∈ GLAPPrimeCore p ↥X') := by
      intro t ht
      rw [← y9xE_mem_coreOf_iff]
      exact (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal C.hp hJsn)
        ((y9xE_mem_coreOf_iff t).2 ht)
    let V : Subgroup G := J ⊓ y9xE_N C
    have hVJ : V = J := by
      by_contra hne
      have hlt : V < J := lt_of_le_of_ne inf_le_left hne
      have hVn : (V.subgroupOf J).Normal := by
        refine ⟨fun n hn y => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have hnJ : (n : G) ∈ J := (Subgroup.mem_inf.1 hn).1
        have hnN : (n : G) ∈ y9xE_N C := (Subgroup.mem_inf.1 hn).2
        have hc := y9xE_N_normal C (hJY y.2) hnN
        rw [Subgroup.mem_inf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact ⟨J.mul_mem (J.mul_mem y.2 hnJ) (J.inv_mem y.2), hc⟩
      have hVX : IsSubnormal V X' :=
        isSubnormal_trans' (IsSubnormal.step (inf_le_left : V ≤ J) hVn (IsSubnormal.refl J)) hJsn
      apply hmin V hlt hVX
      apply le_antisymm
      ·
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
        refine Subgroup.mem_map_of_mem _ ?_
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact (Subgroup.mem_inf.1 hx).1
      ·
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
        have hxJ : (x : G) ∈ J := hx
        obtain ⟨v, hvN, t, ht, hjvt⟩ := hsplit ⟨(x : G), hxJ⟩
        have hxeq : x = (⟨(v : G), hJX' v.2⟩ : ↥X') * ⟨(t : G), hJX' t.2⟩ := by
          apply Subtype.ext
          have := congrArg Subtype.val hjvt
          simpa using this
        have htone : (QuotientGroup.mk' (GLAPPrimeCore p ↥X')) (⟨(t : G), hJX' t.2⟩ : ↥X') = 1 :=
          (QuotientGroup.eq_one_iff _).2 (hcoreX' t ht)
        refine Subgroup.mem_map.2 ⟨⟨(v : G), hJX' v.2⟩, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_inf.2 ⟨v.2, hvN⟩
        · rw [hxeq, map_mul, htone, mul_one]
    have hJN : ∀ j ∈ J, j ∈ y9xE_N C := fun j hj => by
      have hjV : j ∈ V := by rw [hVJ]; exact hj
      exact (Subgroup.mem_inf.1 hjV).2
    have hbot : TJ.map (y9xE_psiJ C hJY) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨t, _, rfl⟩
      rw [Subgroup.mem_bot, hψN]
      exact hJN t.1 t.2
    rw [hF] at hbot
    obtain ⟨q, hq⟩ := exists_ne (1 : y9xE_Q C)
    have hqtop : q ∈ (⊤ : Subgroup (y9xE_Q C)) := Subgroup.mem_top q
    rw [hbot, Subgroup.mem_bot] at hqtop
    exact hq hqtop

private theorem y9xE_ker_psiJ {p : ℕ} {X X' K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {J : Subgroup G} (hJ : GLAPComponent p X' J) (hJY : J ≤ Y)
    (hsurj : Function.Surjective (y9xE_psiJ C hJY)) :
    (y9xE_psiJ C hJY).ker = y9xE_W p J := by
  classical
  have hTN := y9xE_T_le_N C hJ hJY hsurj
  have hψN : ∀ j : ↥J, y9xE_psiJ C hJY j = 1 ↔ (j : G) ∈ y9xE_N C := by
    intro j
    show QuotientGroup.mk' ((y9xE_N C).subgroupOf Y) (Subgroup.inclusion hJY j) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hQ := isQuasisimple_pQuot_of_glaPComponent C.hp hJ
  haveI hsimpleQ : IsSimpleGroup (y9xE_Q C) :=
    (MulEquiv.isSimpleGroup_congr (y9xE_Psi C)).mpr (y9xE_PSimple_simple C)
  haveI : Nontrivial (y9xE_Q C) := hsimpleQ.toNontrivial
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    let A : Subgroup (PQuot p J) :=
      ((y9xE_psiJ C hJY).ker).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
    haveI hAn : A.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    have hAc : A ≤ Subgroup.center (PQuot p J) := by
      by_cases hAtop : A = ⊤
      · exfalso
        have hall : ∀ y : ↥J, y9xE_psiJ C hJY y = 1 := by
          intro y
          have hy : QuotientGroup.mk' (GLAPPrimeCore p ↥J) y ∈ A := by
            rw [hAtop]; exact Subgroup.mem_top _
          obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.1 hy
          have h1 : y = v * (v⁻¹ * y) := by group
          have hvo : v⁻¹ * y ∈ GLAPPrimeCore p ↥J := QuotientGroup.eq.1 hvy
          have hoN : ((v⁻¹ * y : ↥J) : G) ∈ y9xE_N C :=
            hTN ((y9xE_mem_coreOf_iff (v⁻¹ * y)).2 hvo)
          rw [h1, map_mul, (hψN _).2 hoN, mul_one]
          exact (MonoidHom.mem_ker).1 hv
        obtain ⟨q, hq⟩ := exists_ne (1 : y9xE_Q C)
        obtain ⟨y, rfl⟩ := hsurj q
        exact hq (hall y)
      · exact le_center_of_normal_of_isQuasisimple hQ hAn hAtop
    have hxA : QuotientGroup.mk' (GLAPPrimeCore p ↥J) x ∈ A := Subgroup.mem_map_of_mem _ hx
    exact Subgroup.mem_comap.2 (hAc hxA)
  · intro hx
    have hcomm_all := (y9xE_mk_center_iff x).1 (Subgroup.mem_comap.1 hx)
    have hcen : y9xE_psiJ C hJY x ∈ Subgroup.center (y9xE_Q C) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hsurj g
      have hu : (((l * x)⁻¹ * (x * l) : ↥J) : G) ∈ GLAPPrimeCoreOf p J :=
        (y9xE_mem_coreOf_iff _).2 (hcomm_all l)
      have hu' : y9xE_psiJ C hJY ((l * x)⁻¹ * (x * l)) = 1 := (hψN _).2 (hTN hu)
      simp only [map_mul, map_inv] at hu'
      exact inv_mul_eq_one.1 hu'
    have h2 : (y9xE_Psi C) (y9xE_psiJ C hJY x) ∈ Subgroup.center (PSimple p K₁) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := (y9xE_Psi C).surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hcen q]
    rw [y9xE_PSimple_center C, Subgroup.mem_bot] at h2
    exact (map_eq_one_iff _ (y9xE_Psi C).injective).1 h2

private noncomputable def y9xE_e {p : ℕ} {X X' K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {J : Subgroup G} (hJ : GLAPComponent p X' J) (hJY : J ≤ Y)
    (hsurj : Function.Surjective (y9xE_psiJ C hJY)) : PSimple p J ≃* PSimple p K₁ := by
  classical
  haveI : Fact p.Prime := ⟨C.hp⟩
  have hker := y9xE_ker_psiJ C hJ hJY hsurj
  haveI : (y9xE_W p J).Normal := by
    unfold y9xE_W; infer_instance
  exact (y9xE_eJ J).trans
    (((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (y9xE_psiJ C hJY) hsurj)).trans (y9xE_Psi C))

private theorem y9xE_Psi_iota {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    (k : ↥K₁) : y9xE_Psi C (y9xE_iota C k) = y9xE_pi1 C k := by
  unfold y9xE_Psi
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective (y9xE_iota C) (y9xE_iota_surj C)).symm
      (y9xE_iota C k) = (QuotientGroup.mk k : ↥K₁ ⧸ (y9xE_iota C).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem y9xE_e_formula {p : ℕ} {X X' K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {J : Subgroup G} (hJ : GLAPComponent p X' J) (hJY : J ≤ Y)
    (hsurj : Function.Surjective (y9xE_psiJ C hJY)) (j : ↥J) (k : ↥K₁)
    (h : y9xE_psiJ C hJY j = y9xE_iota C k) :
    y9xE_e C hJ hJY hsurj (QuotientGroup.mk (QuotientGroup.mk j : PQuot p J)) =
      QuotientGroup.mk (QuotientGroup.mk k : PQuot p K₁) := by
  classical
  haveI : Fact p.Prime := ⟨C.hp⟩
  unfold y9xE_e
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have h1 : (y9xE_eJ J) (QuotientGroup.mk (QuotientGroup.mk j : PQuot p J)) = (QuotientGroup.mk j) := rfl
  rw [h1]
  have h2 : ((QuotientGroup.quotientMulEquivOfEq (y9xE_ker_psiJ C hJ hJY hsurj).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (y9xE_psiJ C hJY) hsurj)) (QuotientGroup.mk j) =
      y9xE_psiJ C hJY j := rfl
  rw [h2, h, y9xE_Psi_iota]
  rfl

private theorem y9xE_piY_eq_iff {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    (x y : ↥Y) : y9xE_piY C x = y9xE_piY C y ↔ (x : G)⁻¹ * (y : G) ∈ y9xE_N C := by
  show QuotientGroup.mk' ((y9xE_N C).subgroupOf Y) x = QuotientGroup.mk' ((y9xE_N C).subgroupOf Y) y ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

private theorem y9xE_centMod_mem_N {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {n : G} (hnY : n ∈ Y) (hn : n ∈ centModSubgroup p K₁) : n ∈ y9xE_N C := by
  refine ⟨hnY, fun h hh => ?_⟩
  have hsub : K₁ ⊔ GLAPPrimeCoreOf p Y ≤ y9xE_Cl C n hnY := by
    refine sup_le (fun x hx => ?_) (fun r hr => ?_)
    · have h1 : ⁅x, n⁆ ∈ GLAPPrimeCoreOf p K₁ := hn.2 x hx
      have h2 : ⁅x, n⁆ ∈ K₁ ⊓ GLAPPrimeCoreOf p Y := by
        rw [y9xE_K1_R C]; exact h1
      exact ⟨y9xE_le1 C hx, h2.2⟩
    · refine ⟨(Subgroup.map_subtype_le _) hr, ?_⟩
      have e : ⁅r, n⁆ = r * (n * r⁻¹ * n⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hr (y9xE_R_normal C hnY (Subgroup.inv_mem _ hr))
  exact (hsub hh).2

private theorem y9xE_psiJ_surj {p : ℕ} {X K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {J : Subgroup G} (hJY : J ≤ Y)
    (hcov : ∀ k ∈ K₁, ∃ j ∈ J, ∃ n ∈ centModSubgroup p K₁, k = j * n) :
    Function.Surjective (y9xE_psiJ C hJY) := by
  intro q
  obtain ⟨k, rfl⟩ := y9xE_iota_surj C q
  obtain ⟨j, hj, n, hn, hkjn⟩ := hcov k.1 k.2
  have hnY : n ∈ Y := by
    have e : n = j⁻¹ * k := by rw [hkjn]; group
    rw [e]
    exact Y.mul_mem (Y.inv_mem (hJY hj)) (y9xE_le1 C k.2)
  have hnN : n ∈ y9xE_N C := y9xE_centMod_mem_N C hnY hn
  have hπn : y9xE_piY C ⟨n, hnY⟩ = 1 := by
    show QuotientGroup.mk' ((y9xE_N C).subgroupOf Y) ⟨n, hnY⟩ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hnN
  refine ⟨⟨j, hj⟩, ?_⟩
  have hsplit : (Subgroup.inclusion (y9xE_le1 C) k : ↥Y) = ⟨j, hJY hj⟩ * ⟨n, hnY⟩ := by
    apply Subtype.ext
    simp [hkjn]
  show y9xE_piY C (Subgroup.inclusion hJY ⟨j, hj⟩) = y9xE_piY C (Subgroup.inclusion (y9xE_le1 C) k)
  rw [hsplit, map_mul, hπn, mul_one]
  rfl

private theorem y9xE_iso_core {p : ℕ} {X X' K₁ K₂ K₃ Y : Subgroup G} (C : YCore G p X K₁ K₂ K₃ Y)
    {J : Subgroup G} (hJ : GLAPComponent p X' J) (hJY : J ≤ Y)
    (hcov : ∀ k ∈ K₁, ∃ j ∈ J, ∃ n ∈ centModSubgroup p K₁, k = j * n) :
    ∃ e : PSimple p J ≃* PSimple p K₁, ∀ g : G, g ∈ Subgroup.normalizer (J : Set G) →
      g ∈ Subgroup.normalizer (K₁ : Set G) → g ∈ Subgroup.normalizer (Y : Set G) →
        IsoPresAct p g J K₁ e ∧ IsoPresAct p g K₁ J e.symm := by
  classical
  haveI : Fact p.Prime := ⟨C.hp⟩
  have hsurj := y9xE_psiJ_surj C hJY hcov
  refine ⟨y9xE_e C hJ hJY hsurj, fun g hgJ hgK hgY => ?_⟩
  have hform := y9xE_e_formula C hJ hJY hsurj
  constructor
  ·
    intro s s' hrel
    obtain ⟨q, q', ⟨l, l', hl, hl', hll⟩, rfl, rfl⟩ := hrel
    subst hl hl'
    obtain ⟨k, hk⟩ := y9xE_iota_surj C (y9xE_psiJ C hJY l)
    have hgK' : g⁻¹ * (k : G) * g ∈ K₁ := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgK) (k : G)).1 k.2
      simpa using this
    let k' : ↥K₁ := ⟨g⁻¹ * (k : G) * g, hgK'⟩
    have hkl : (k : G)⁻¹ * (l : G) ∈ y9xE_N C :=
      (y9xE_piY_eq_iff C (Subgroup.inclusion (y9xE_le1 C) k) (Subgroup.inclusion hJY l)).1 hk
    have hlk : (l : G)⁻¹ * (k : G) ∈ y9xE_N C := by
      have := (y9xE_N C).inv_mem hkl
      simpa [mul_inv_rev] using this
    have hl'k : y9xE_psiJ C hJY l' = y9xE_iota C k' := by
      apply (y9xE_piY_eq_iff C (Subgroup.inclusion hJY l') (Subgroup.inclusion (y9xE_le1 C) k')).2
      have h1 : (l' : G)⁻¹ * (k' : G) ∈ y9xE_N C := by
        have h2 := y9xE_N_conj C hgY hgK hlk
        rw [hll]
        convert h2 using 1
        simp only [k']
        group
      exact h1
    have e1 := hform l k hk.symm
    have e2 := hform l' k' hl'k
    refine ⟨QuotientGroup.mk k, QuotientGroup.mk k', ⟨k, k', rfl, rfl, rfl⟩, ?_, ?_⟩
    · rw [e1]
    · rw [e2]
  ·
    intro t t' hrel
    obtain ⟨q, q', ⟨a, a', ha, ha', haa⟩, rfl, rfl⟩ := hrel
    subst ha ha'
    obtain ⟨j, hj⟩ := hsurj (y9xE_iota C a)
    obtain ⟨j', hj'⟩ := hsurj (y9xE_iota C a')
    have hej : y9xE_e C hJ hJY hsurj (QuotientGroup.mk (QuotientGroup.mk j)) =
        QuotientGroup.mk (QuotientGroup.mk a) := hform j a hj
    have hej' : y9xE_e C hJ hJY hsurj (QuotientGroup.mk (QuotientGroup.mk j')) =
        QuotientGroup.mk (QuotientGroup.mk a') := hform j' a' hj'
    have hsymm1 : (y9xE_e C hJ hJY hsurj).symm (QuotientGroup.mk (QuotientGroup.mk a)) =
        QuotientGroup.mk (QuotientGroup.mk j) := by
      rw [MulEquiv.symm_apply_eq]; exact hej.symm
    have hsymm2 : (y9xE_e C hJ hJY hsurj).symm (QuotientGroup.mk (QuotientGroup.mk a')) =
        QuotientGroup.mk (QuotientGroup.mk j') := by
      rw [MulEquiv.symm_apply_eq]; exact hej'.symm
    rw [hsymm1, hsymm2]
    have hgj : g⁻¹ * (j : G) * g ∈ J := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgJ) (j : G)).1 j.2
      simpa using this
    let j'' : ↥J := ⟨g⁻¹ * (j : G) * g, hgj⟩
    have hjN0 : (a : G)⁻¹ * (j : G) ∈ y9xE_N C :=
      (y9xE_piY_eq_iff C (Subgroup.inclusion (y9xE_le1 C) a) (Subgroup.inclusion hJY j)).1 hj.symm
    have hjN' : (j : G)⁻¹ * (a : G) ∈ y9xE_N C := by
      have := (y9xE_N C).inv_mem hjN0
      simpa [mul_inv_rev] using this
    have hj''a : y9xE_psiJ C hJY j'' = y9xE_iota C a' := by
      apply (y9xE_piY_eq_iff C (Subgroup.inclusion hJY j'') (Subgroup.inclusion (y9xE_le1 C) a')).2
      show (j'' : G)⁻¹ * (a' : G) ∈ y9xE_N C
      have hc : (j'' : G)⁻¹ * (a' : G) = g⁻¹ * ((j : G)⁻¹ * (a : G)) * g := by
        rw [haa]
        simp only [j'']
        group
      rw [hc]
      exact y9xE_N_conj C hgY hgK hjN'
    have hej'' : y9xE_e C hJ hJY hsurj (QuotientGroup.mk (QuotientGroup.mk j'')) =
        QuotientGroup.mk (QuotientGroup.mk a') := hform j'' a' hj''a
    have hinj : (QuotientGroup.mk (QuotientGroup.mk j'') : PSimple p J) =
        QuotientGroup.mk (QuotientGroup.mk j') := by
      apply (y9xE_e C hJ hJY hsurj).injective
      rw [hej'', hej']
    exact ⟨QuotientGroup.mk j, QuotientGroup.mk j'', ⟨j, j'', rfl, rfl, rfl⟩, rfl, hinj⟩

open CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator in
open scoped Pointwise in
theorem Ky_shape_iso (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K) (hp3 : p = 3)
    (hsh : KyShapeDiag a y (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers y))) :
    KyShapeIso a y (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers y)) := by
  classical
  subst hp3
  obtain ⟨K₁, K₂, K₃, c1, c2, c3, n12, n13, n23, hKy, e2, e3, hcl, -, -, -⟩ := hsh
  have hp : Nat.Prime 3 := hc.ctx.prime
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_left ac.mem
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian 3 E := isElemAbelian_mono hd.E₀_el hEE₀
  have hcyK : CFSG.Open.IsKGroup ↥(cx y) :=
    isKGroup_of_isKProper hc.ctx.kProper (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hd.y_ne)
  have hay : a ∈ cx y := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel haE hyE)
  have hyaP : IsPGroup 3 (Subgroup.zpowers a) :=
    isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 haE))
  have hLy' : GLAPLayer 3 (Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) ≤
      GLAPLayer 3 (cx y) := by
    rw [y9x_cs_pair a y, inf_comm, ← y9x_cs_zpowers' a]
    exact y9x_layer_cz_le hp hin.l105.lbal hcyK hay hyaP
  have hJle : Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤ Kf 3 K (Subgroup.zpowers y) := by
    have hKy_eq : Kf 3 K (Subgroup.zpowers y) = closureIn K (GLAPLayer 3 (cx y)) := by
      rw [Kf, y9x_cs_zpowers' y]
    rw [hKy_eq]
    exact y9x_closureIn_mono hLy'
  have hYX : Kf 3 K (Subgroup.zpowers y) ≤ cx y := by
    rw [hKy]; exact sup_le (sup_le c1.1 c2.1) c3.1
  let C : YCore G 3 (cx y) K₁ K₂ K₃ (Kf 3 K (Subgroup.zpowers y)) :=
    ⟨hp, c1, c2, c3, n12, n13, n23, hKy, hYX⟩
  have hcov := y9xE_cov h ac hc hin hd hkay K₁ K₂ K₃ c1 c2 c3 n12 n13 n23 hKy e2 e3
  obtain ⟨e, he⟩ := y9xE_iso_core C hkay.Kay_single hJle hcov
  exact ⟨K₁, K₂, K₃, c1, c2, c3, n12, n13, n23, hKy, e2, e3, hcl, e, fun g hgJ hgK hgY => he g hgJ hgK hgY⟩

private theorem y9xE_gLBConj_cx {d y : G} (hd : d * y = y * d) : GLBConj d (cx y) = cx y := by
  have h := CFSG.LocalAnalysis.GLTheoremB.centralizer_singleton_gLBConj d y
  have e : d⁻¹ * y * d = y := by
    calc d⁻¹ * y * d = d⁻¹ * (y * d) := by group
      _ = d⁻¹ * (d * y) := by rw [hd]
      _ = y := by group
  rw [e] at h
  exact h.symm

open CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator in
open scoped Pointwise in
theorem Ky_a'_exists (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hp3 : p = 3)
    (hsh : KyShapeIso a y (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers y)))
    (hBN : B ≤ Subgroup.normalizer ((Kf p K (Subgroup.zpowers y) : Subgroup G) : Set G)) :
    ∃ a' ∈ Dgrp b x, a' ∉ Subgroup.zpowers a ∧
      ∀ M : Subgroup G, GLAPComponent 3 (cx y) M → M ≤ Kf p K (Subgroup.zpowers y) →
        a' ∈ Subgroup.normalizer (M : Set G) := by
  classical
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨hc.ctx.prime⟩
  obtain ⟨K₁, K₂, K₃, c1, c2, c3, n12, n13, n23, hKy, e2, e3, hcl, -⟩ := hsh
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have ha3 : a ^ 3 = 1 := hDel.2 a ha
  have hyB : y ∈ B := hd.toK.y_B
  have hcomm : ∀ d ∈ Dgrp b x, a * d = d * a := fun d hd' => isElemAbelian_commute hDel ha hd'
  have hK1Ky : K₁ ≤ Kf 3 K (Subgroup.zpowers y) := by
    rw [hKy]; exact le_sup_of_le_left le_sup_left
  have hperm : ∀ d ∈ Dgrp b x, GLBConj d K₁ = K₁ ∨ GLBConj d K₁ = K₂ ∨ GLBConj d K₁ = K₃ := by
    intro d hd'
    have hdy : d * y = y * d := isElemAbelian_commute (B_el h) (hDB hd') hyB
    have hc1 : GLAPComponent 3 (cx y) (GLBConj d K₁) := by
      have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj c1 d
      rwa [y9xE_gLBConj_cx hdy] at h1
    have hle : GLBConj d K₁ ≤ Kf 3 K (Subgroup.zpowers y) := by
      have h1 := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono d hK1Ky
      rwa [mem_normalizer_iff_gLBConj_eq.1 (hBN (hDB hd'))] at h1
    exact hcl _ hc1 hle
  have hA1 : GLBConj a K₁ = K₂ := e2.symm
  have hA2 : GLBConj a K₂ = K₃ := e3.symm
  have haa1 : a * (a * a) = 1 := by rw [← pow_three]; exact ha3
  have hA3 : GLBConj a K₃ = K₁ := by
    rw [e3, gLBConj_gLBConj, e2, gLBConj_gLBConj, haa1, gLBConj_one]
  have hA2' : GLBConj (a * a) K₁ = K₃ := by
    rw [← gLBConj_gLBConj a a K₁, hA1, hA2]
  have hA3' : GLBConj (a * a) K₂ = K₁ := by
    rw [← gLBConj_gLBConj a a K₂, hA2, hA3]
  have hfix : ∀ g : G, g * a = a * g → GLBConj g K₁ = K₁ → GLBConj g K₂ = K₂ ∧ GLBConj g K₃ = K₃ := by
    intro g hg h1
    have hc : ∀ H : Subgroup G, GLBConj g (GLBConj a H) = GLBConj a (GLBConj g H) := by
      intro H
      rw [gLBConj_gLBConj, gLBConj_gLBConj, hg]
    have h2 : GLBConj g K₂ = K₂ := by rw [← hA1, hc, h1]
    have h3 : GLBConj g K₃ = K₃ := by rw [← hA2, hc, h2]
    exact ⟨h2, h3⟩
  obtain ⟨c, hcD, hca⟩ : ∃ c ∈ Dgrp b x, c ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : Dgrp b x ≤ Subgroup.zpowers a := fun c hc' => hcon c hc'
    have hcard := Subgroup.card_le_of_le hle
    rw [hDc, Nat.card_zpowers, orderOf_eq_prime ha3 ha1] at hcard
    norm_num at hcard
  have hca' : c * a = a * c := (hcomm c hcD).symm
  obtain ⟨g, hgD, hga, hgc, hg1⟩ : ∃ g ∈ Dgrp b x, g ∉ Subgroup.zpowers a ∧ g * a = a * g ∧
      GLBConj g K₁ = K₁ := by
    rcases hperm c hcD with h1 | h1 | h1
    · exact ⟨c, hcD, hca, hca', h1⟩
    · refine ⟨c * (a * a), Subgroup.mul_mem _ hcD (Subgroup.mul_mem _ ha ha), ?_, ?_, ?_⟩
      · intro hmem
        apply hca
        have e : c = (c * (a * a)) * (a * a)⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _
          (Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)))
      · calc c * (a * a) * a = c * a * a * a := by group
          _ = a * c * a * a := by rw [hca']
          _ = a * (c * (a * a)) := by group
      · rw [← gLBConj_gLBConj (a * a) c K₁, h1, hA3']
    · refine ⟨c * a, Subgroup.mul_mem _ hcD ha, ?_, ?_, ?_⟩
      · intro hmem
        apply hca
        have e : c = (c * a) * a⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
      · show c * a * a = a * (c * a)
        calc c * a * a = a * c * a := by rw [hca']
          _ = a * (c * a) := mul_assoc a c a
      · rw [← gLBConj_gLBConj a c K₁, h1, hA3]
  refine ⟨g, hgD, hga, fun M hM hMle => ?_⟩
  obtain ⟨h2, h3⟩ := hfix g hgc hg1
  rcases hcl M hM hMle with rfl | rfl | rfl
  · exact mem_normalizer_iff_gLBConj_eq.2 hg1
  · exact mem_normalizer_iff_gLBConj_eq.2 h2
  · exact mem_normalizer_iff_gLBConj_eq.2 h3

private theorem y9xE_chev_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : IsChevSimple 2 S) : IsChevSimple 2 T := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.symm.trans f⟩⟩

private theorem y9xE_conj_iso (p : ℕ) (hp : p.Prime) (L : Subgroup G) (a : G) :
    ∃ ψ : PSimple p L ≃* PSimple p (GLBConj a L), ∀ g : G, a * g = g * a → ∀ s s' : PSimple p L,
      indRelS p L g s s' ↔ indRelS p (GLBConj a L) g (ψ s) (ψ s') := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let e : ↥L ≃* ↥(GLBConj a L) :=
    Subgroup.equivMapOfInjective L (MulAut.conj a⁻¹).toMonoidHom (MulAut.conj a⁻¹).injective
  have he : ∀ l : ↥L, ((e l : ↥(GLBConj a L)) : G) = a⁻¹ * (l : G) * a := by
    intro l
    change (MulAut.conj a⁻¹) (l : G) = _
    simp [MulAut.conj_apply]
  have hmap : Subgroup.map e.toMonoidHom (GLAPPrimeCore p ↥L) = GLAPPrimeCore p ↥(GLBConj a L) :=
    CFSG.pPrimeCore_map_iso p e
  let ζ : PQuot p L ≃* PQuot p (GLBConj a L) :=
    QuotientGroup.congr (GLAPPrimeCore p ↥L) (GLAPPrimeCore p ↥(GLBConj a L)) e hmap
  let ψ : PSimple p L ≃* PSimple p (GLBConj a L) :=
    QuotientGroup.congr (Subgroup.center (PQuot p L)) (Subgroup.center (PQuot p (GLBConj a L))) ζ
      (by simpa using map_center_eq ζ)
  have hζ : ∀ l : ↥L, ζ (QuotientGroup.mk l) = QuotientGroup.mk (e l) := fun l => rfl
  have hψ : ∀ q : PQuot p L, ψ (QuotientGroup.mk q) = QuotientGroup.mk (ζ q) := fun q => rfl
  have hinv : ∀ m : ↥(GLBConj a L), ((e.symm m : ↥L) : G) = a * (m : G) * a⁻¹ := by
    intro m
    have h := he (e.symm m)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    group
  have hzs : ∀ m : ↥(GLBConj a L), ζ.symm (QuotientGroup.mk m) = QuotientGroup.mk (e.symm m) := by
    intro m
    apply ζ.injective
    rw [MulEquiv.apply_symm_apply, hζ, MulEquiv.apply_symm_apply]
  refine ⟨ψ, fun g hag s s' => ?_⟩
  have h1 : a⁻¹ * g⁻¹ = g⁻¹ * a⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hag]
  have hc1 : ∀ u : G, a⁻¹ * (g⁻¹ * u * g) * a = g⁻¹ * (a⁻¹ * u * a) * g := by
    intro u
    calc a⁻¹ * (g⁻¹ * u * g) * a = (a⁻¹ * g⁻¹) * u * (g * a) := by group
      _ = (g⁻¹ * a⁻¹) * u * (a * g) := by rw [h1, hag]
      _ = g⁻¹ * (a⁻¹ * u * a) * g := by group
  have h2 : g⁻¹ * a = a * g⁻¹ := by
    calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hag]
      _ = a * g⁻¹ := by group
  have h3 : g * a⁻¹ = a⁻¹ * g := by
    calc g * a⁻¹ = a⁻¹ * (a * g) * a⁻¹ := by group
      _ = a⁻¹ * (g * a) * a⁻¹ := by rw [hag]
      _ = a⁻¹ * g := by group
  have hc2 : ∀ u : G, a * (g⁻¹ * u * g) * a⁻¹ = g⁻¹ * (a * u * a⁻¹) * g := by
    intro u
    calc a * (g⁻¹ * u * g) * a⁻¹ = (a * g⁻¹) * u * (g * a⁻¹) := by group
      _ = (g⁻¹ * a) * u * (a⁻¹ * g) := by rw [h2, h3]
      _ = g⁻¹ * (a * u * a⁻¹) * g := by group
  constructor
  · rintro ⟨q, q', ⟨l, l', hl, hl', hll⟩, rfl, rfl⟩
    refine ⟨ζ q, ζ q', ⟨e l, e l', ?_, ?_, ?_⟩, (hψ q).symm, (hψ q').symm⟩
    · rw [← hl]; exact (hζ l).symm
    · rw [← hl']; exact (hζ l').symm
    · rw [he, he, hll]; exact hc1 _
  · rintro ⟨r, r', ⟨m, m', hm, hm', hmm⟩, hr, hr'⟩
    refine ⟨ζ.symm r, ζ.symm r', ⟨e.symm m, e.symm m', ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [← hm, hzs]
    · rw [← hm', hzs]
    · rw [hinv m', hinv m, hmm]
      exact hc2 _
    · apply ψ.injective
      rw [hψ, ζ.apply_symm_apply]
      exact hr
    · apply ψ.injective
      rw [hψ, ζ.apply_symm_apply]
      exact hr'

private theorem y9xE_conj_iso' (p : ℕ) (hp : p.Prime) (L L' : Subgroup G) (a : G) (hL' : L' = GLBConj a L) :
    ∃ ψ : PSimple p L ≃* PSimple p L', ∀ g : G, a * g = g * a → ∀ s s' : PSimple p L,
      indRelS p L g s s' ↔ indRelS p L' g (ψ s) (ψ s') := by
  subst hL'
  exact y9xE_conj_iso p hp L a

private theorem y9xE_indRel_congr {p : ℕ} (L : Subgroup G) {g g' : G}
    (h : ∀ l ∈ L, g⁻¹ * l * g = g'⁻¹ * l * g') : indRel p L g = indRel p L g' := by
  funext q q'
  apply propext
  constructor
  · rintro ⟨l, l', hl, hl', he⟩
    exact ⟨l, l', hl, hl', by rw [he]; exact h (l : G) l.2⟩
  · rintro ⟨l, l', hl, hl', he⟩
    exact ⟨l, l', hl, hl', by rw [he]; exact (h (l : G) l.2).symm⟩

private theorem y9xE_isoPresAct_of_iff {p : ℕ} {J K : Subgroup G} {g : G} (e : PSimple p J ≃* PSimple p K)
    (h : ∀ s s' : PSimple p J, indRelS p J g s s' ↔ indRelS p K g (e s) (e s')) :
    IsoPresAct p g J K e ∧ IsoPresAct p g K J e.symm :=
  ⟨fun s s' hs => (h s s').1 hs,
    fun t t' ht => (h (e.symm t) (e.symm t')).2 (by
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact ht)⟩

private theorem y9x_conj_closureIn {I H : Subgroup G} {g : G}
    (hI : ∀ i ∈ I, g * i * g⁻¹ ∈ I) (hH : ∀ h ∈ H, g * h * g⁻¹ ∈ H) :
    closureIn I H ≤ (closureIn I H).comap (MulAut.conj g).toMonoidHom := by
  unfold closureIn
  refine iSup₂_le fun h hh => Subgroup.map_le_iff_le_comap.2 fun i hi => ?_
  have e : (MulAut.conj g).toMonoidHom ((MulAut.conj h).toMonoidHom i) =
      (MulAut.conj (g * h * g⁻¹)).toMonoidHom ((MulAut.conj g).toMonoidHom i) := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.mem_comap, Subgroup.mem_comap, e]
  exact (le_iSup₂ (f := fun k (_ : k ∈ H) => I.map (MulAut.conj k).toMonoidHom) (g * h * g⁻¹)
    (hH h hh)) (Subgroup.mem_map.2 ⟨(MulAut.conj g).toMonoidHom i, hI i hi, rfl⟩)

private theorem y9x_normalizer_closureIn {I H : Subgroup G} {g : G}
    (hI : g ∈ Subgroup.normalizer (I : Set G)) (hH : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((closureIn I H : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact y9x_conj_closureIn (fun i hi => (Subgroup.mem_normalizer_iff.1 hI i).1 hi)
      (fun h hh => (Subgroup.mem_normalizer_iff.1 hH h).1 hh) hk
  · intro hk
    have hI' := Subgroup.inv_mem _ hI
    have hH' := Subgroup.inv_mem _ hH
    have := y9x_conj_closureIn (g := g⁻¹)
      (fun i hi => (Subgroup.mem_normalizer_iff.1 hI' i).1 hi)
      (fun h hh => (Subgroup.mem_normalizer_iff.1 hH' h).1 hh) hk
    simpa [MulAut.conj_apply, mul_assoc] using this

open CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator in
open scoped Pointwise in
theorem Ky_a'_nonInn (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K) (hp3 : p = 3)
    (hsh : KyShapeIso a y (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers y)))
    (hBN : B ≤ Subgroup.normalizer ((Kf p K (Subgroup.zpowers y) : Subgroup G) : Set G)) {a' : G}
    (ha'D : a' ∈ Dgrp b x) (ha'a : a' ∉ Subgroup.zpowers a)
    (hnorm : ∀ M : Subgroup G, GLAPComponent 3 (cx y) M → M ≤ Kf p K (Subgroup.zpowers y) →
      a' ∈ Subgroup.normalizer (M : Set G)) :
    ∀ M : Subgroup G, GLAPComponent 3 (cx y) M → M ≤ Kf p K (Subgroup.zpowers y) → NonInnDiag 3 a' M := by
  classical
  subst hp3
  have hp3 : Nat.Prime 3 := hc.ctx.prime
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨K₁, K₂, K₃, c1, c2, c3, n12, n13, n23, hKy, e2, e3, hcl, e, he⟩ := hsh
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have ha3 : a ^ 3 = 1 := hDel.2 a ha
  have ha'1 : a' ≠ 1 := fun h1 => ha'a (h1 ▸ Subgroup.one_mem _)
  have hyB : y ∈ B := hd.toK.y_B
  have haa' : a * a' = a' * a := isElemAbelian_commute hDel ha ha'D
  have hK1Ky : K₁ ≤ Kf 3 K (Subgroup.zpowers y) := by
    rw [hKy]; exact le_sup_of_le_left le_sup_left
  have hK2Ky : K₂ ≤ Kf 3 K (Subgroup.zpowers y) := by
    rw [hKy]; exact le_sup_of_le_left le_sup_right
  have hK3Ky : K₃ ≤ Kf 3 K (Subgroup.zpowers y) := by
    rw [hKy]; exact le_sup_right
  have haS : a ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hS_cx : Subgroup.zpowers a ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({a'} : Set G) := by
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 haa'
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute (B_el h) hyB (hDB ha'D))
  have ha'cs : a' ∈ Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (hS_cx hs)
  have ha'L : a' ∈ Subgroup.normalizer ((GLAPLayer 3 (Subgroup.centralizer
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) : Subgroup G) : Set G) :=
    mem_normalizer_glaPLayer (Subgroup.le_normalizer ha'cs)
  have hEa' : a' ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_left ha'D
  have hKE : K ≤ Subgroup.centralizer (E : Set G) := hd.K_comp.1.trans inf_le_right
  have ha'K : a' ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun k hk =>
      (Subgroup.mem_centralizer_iff.1 (hKE hk) a' hEa').symm)
  have ha'J : a' ∈ Subgroup.normalizer ((Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) : Subgroup G) : Set G) :=
    y9x_normalizer_closureIn ha'K ha'L
  have hJa : ∀ l ∈ Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y), l * a = a * l := by
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.1 (hkay.Kay_single.1 hl)) a haS).symm
  have hidx : (Subgroup.zpowers a).relIndex (Dgrp b x) = 3 := by
    show ((Subgroup.zpowers a).subgroupOf (Dgrp b x)).index = 3
    have h1 := Subgroup.index_mul_card ((Subgroup.zpowers a).subgroupOf (Dgrp b x))
    have h2 : Nat.card ↥((Subgroup.zpowers a).subgroupOf (Dgrp b x)) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 ha)).toEquiv, Nat.card_zpowers,
        orderOf_eq_prime ha3 ha1]
    rw [h2, hDc] at h1
    omega
  have hDdec : ∀ g ∈ Dgrp b x, ∃ n : ℤ, ∃ m : ℕ, g = a ^ n * a' ^ m := by
    intro g hg
    obtain ⟨a₀, ha₀, k, hgk⟩ := idiag_decomp hp3 hDel (Subgroup.zpowers_le.2 ha) hidx ha'D ha'a g hg
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 ha₀
    exact ⟨n, k, by rw [hgk, hn]⟩
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hnotJ : ¬ InnDiagOn 3 (Subgroup.zpowers a') (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := by
    intro hA
    apply hkay.x_acts.1.2
    refine ⟨Subgroup.zpowers_le.2 hkay.x_acts.1.1, ?_⟩
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun lab R _ I F θ hP => fun g hg => ?_) hA.2
    obtain ⟨n, m, hgnm⟩ := hDdec g ((Subgroup.zpowers_le.2 hxD) hg)
    have hrel : indRel 3 (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) g =
        indRel 3 (Kf 3 K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (a' ^ m) := by
      apply y9xE_indRel_congr
      intro l hl
      have hal : Commute a l := (hJa l hl).symm
      have hanl : Commute (a ^ n) l := hal.zpow_left n
      have key : (a ^ n)⁻¹ * l * a ^ n = l := by
        rw [mul_assoc, ← hanl.eq, inv_mul_cancel_left]
      rw [hgnm]
      calc (a ^ n * a' ^ m)⁻¹ * l * (a ^ n * a' ^ m) = (a' ^ m)⁻¹ * ((a ^ n)⁻¹ * l * a ^ n) * a' ^ m := by
            group
        _ = (a' ^ m)⁻¹ * l * a' ^ m := by rw [key]
    rw [hrel]
    exact hP (a' ^ m) (Subgroup.pow_mem _ (Subgroup.mem_zpowers a') m)
  have hnotK1 : ¬ InnDiagOn 3 (Subgroup.zpowers a') K₁ := by
    intro hK
    exact hnotJ (hin.iso (cx y) (Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers y : Subgroup G) : Set G))
      K₁ _ a' e.symm c1 hkay.Kay_single hkay.chev_ay (hnorm K₁ c1 hK1Ky) ha'J
      (he a' ha'J (hnorm K₁ c1 hK1Ky) (hBN (hDB ha'D))).2 hK)
  have hchK1 : IsChevSimple 2 (PSimple 3 K₁) := y9xE_chev_congr e hkay.chev_ay
  obtain ⟨ψ₁, hψ₁⟩ := y9xE_conj_iso' 3 hp3 K₁ K₂ a e2
  have hchK2 : IsChevSimple 2 (PSimple 3 K₂) := y9xE_chev_congr ψ₁ hchK1
  have hnotK2 : ¬ InnDiagOn 3 (Subgroup.zpowers a') K₂ := by
    intro hK
    exact hnotK1 (hin.iso (cx y) (cx y) K₂ K₁ a' ψ₁.symm c2 c1 hchK1 (hnorm K₂ c2 hK2Ky) (hnorm K₁ c1 hK1Ky)
      (y9xE_isoPresAct_of_iff ψ₁ (hψ₁ a' haa')).2 hK)
  obtain ⟨ψ₂, hψ₂⟩ := y9xE_conj_iso' 3 hp3 K₂ K₃ a e3
  have hnotK3 : ¬ InnDiagOn 3 (Subgroup.zpowers a') K₃ := by
    intro hK
    exact hnotK2 (hin.iso (cx y) (cx y) K₃ K₂ a' ψ₂.symm c3 c2 hchK2 (hnorm K₃ c3 hK3Ky) (hnorm K₂ c2 hK2Ky)
      (y9xE_isoPresAct_of_iff ψ₂ (hψ₂ a' haa')).2 hK)
  intro M hM hMle
  refine ⟨hnorm M hM hMle, ?_⟩
  rcases hcl M hM hMle with rfl | rfl | rfl
  · exact hnotK1
  · exact hnotK2
  · exact hnotK3

theorem Ky_a' (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K) (hp3 : p = 3)
    (hsh : KyShapeIso a y (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers y)))
    (hBN : B ≤ Subgroup.normalizer ((Kf p K (Subgroup.zpowers y) : Subgroup G) : Set G)) :
    ∃ a' ∈ Dgrp b x, a' ∉ Subgroup.zpowers a ∧
      ∀ M : Subgroup G, GLAPComponent 3 (cx y) M → M ≤ Kf p K (Subgroup.zpowers y) →
        a' ∈ Subgroup.normalizer (M : Set G) ∧ NonInnDiag 3 a' M := by
  obtain ⟨a', ha'D, ha'a, hnorm⟩ := Ky_a'_exists hc hin h ac hd hp3 hsh hBN
  exact ⟨a', ha'D, ha'a, fun M hM hMle =>
    ⟨hnorm M hM hMle, Ky_a'_nonInn hc hin h ac hd hkay hp3 hsh hBN ha'D ha'a hnorm M hM hMle⟩⟩

private theorem y9xF_gLBConj_mono (g : G) {H K : Subgroup G} (h : H ≤ K) :
    GLBConj g H ≤ GLBConj g K :=
  Subgroup.map_mono h

theorem Ky_comp_in_Ki (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K) (hp3 : p = 3)
    (hsh : KyShapeIso a y (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers y)))
    (hBN : B ≤ Subgroup.normalizer ((Kf p K (Subgroup.zpowers y) : Subgroup G) : Set G)) {a' : G}
    (ha'D : a' ∈ Dgrp b x) (ha'a : a' ∉ Subgroup.zpowers a)
    (hact : ∀ M : Subgroup G, GLAPComponent 3 (cx y) M → M ≤ Kf p K (Subgroup.zpowers y) →
      a' ∈ Subgroup.normalizer (M : Set G) ∧ NonInnDiag 3 a' M) :
    ∃ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) M ∧
      ∃ Ki : Subgroup G, GLAPComponent 3 (cx y) Ki ∧ Ki ≤ Kf p K (Subgroup.zpowers y) ∧ M ≤ Ki := by
  classical
  subst hp3
  have hcp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have ha'1 : a' ≠ 1 := fun h1 => ha'a (h1 ▸ Subgroup.one_mem _)
  obtain ⟨-, hDel, hDc⟩ := dgrp_facts hc h
  have hDeq : Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers a' :=
    y9x_dgrp_eq hcp hDel hDc ac.mem ha'D ha1 ha'1 (by
      intro he
      apply ha'a
      rw [← he]
      exact Subgroup.mem_zpowers a')
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have haE : a ∈ E := hDE ac.mem
  have ha'E : a' ∈ E := hDE ha'D
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hxE : x ∈ E := hDE hxD
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian 3 E := isElemAbelian_mono hd.E₀_el hEE₀
  have hEsup : E = Subgroup.zpowers a ⊔ (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) := by
    rw [hd.E_def, hDeq, sup_assoc]
  have hcsE_le : ∀ z ∈ E, cs E ≤ cx z := fun z hz =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hz))
  have hLc : GLAPComponent 3 (cx x) L := (sstar_triple h.star).2.2
  have hK_csE : GLAPComponent 3 (cs E) K := by
    refine glaPComponent_of_isSubnormal' hcp ?_ hd.K_comp
    have hsn := isSubnormal_inf hLc.2.1 (cs E)
    rwa [inf_eq_right.2 (hcsE_le x hxE)] at hsn
  have hcsE : cs E = cs (Subgroup.zpowers a) ⊓ cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) := by
    rw [hEsup]
    exact y9x_cs_sup _ _
  have hK1 : GLAPComponent 3 (cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) ⊓ cs (Subgroup.zpowers a)) K := by
    rw [inf_comm, ← hcsE]
    exact hK_csE
  have hcsF : cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) = cx a' ⊓ cx y :=
    y9x_cs_pair a' y
  have hcsF_le : cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) ≤ cx a' := by
    rw [hcsF]; exact inf_le_left
  have hcaN : cx a' ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha'1
  have hXtop : cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) ≠ ⊤ :=
    fun e => hcaN (top_le_iff.1 (by rw [← e]; exact hcsF_le))
  have hXK : CFSG.Open.IsKGroup ↥(cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) :=
    isKGroup_of_isKProper hc.ctx.kProper hXtop
  have haF : Subgroup.zpowers a' ⊔ Subgroup.zpowers y ≤ cx a :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
      (isElemAbelian_commute hEel ha'E haE)))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
        (isElemAbelian_commute hEel hyE haE)))
  have haCs : a ∈ cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) :=
    (y9x_mem_centralizer_iff _ a).2 haF
  have hza_le : Subgroup.zpowers a ≤ cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) :=
    Subgroup.zpowers_le.2 haCs
  have hEa : IsElemAbelian 3 (Subgroup.zpowers a) :=
    isElemAbelian_mono hEel (Subgroup.zpowers_le.2 haE)
  obtain ⟨𝒞, h1, h2, -, -⟩ := hin.l105.l103.lemma102.i183 G
    (cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) hXK 3 hcp (Subgroup.zpowers a) hza_le hEa K hK1
  have hKF : Kf 3 K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) = ⨆ L ∈ 𝒞, L := by
    rw [Kf, y9x_closureIn_eq_iSup, h2]
  have hKF_le : Kf 3 K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) ≤
      cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) :=
    y9x_closureIn_le (hK1.1.trans inf_le_left)
      (fun g hg => Subgroup.le_normalizer (y9x_layer_le 3 _ hg))
  have hM_comp : ∀ L ∈ 𝒞, GLAPComponent 3 (Kf 3 K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) L := by
    intro L hL
    have hLK : L ≤ Kf 3 K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) := by
      rw [hKF]
      exact le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) L hL
    exact glaPComponent_of_le hcp (h1 L hL) hLK hKF_le
  have hK_ne : K ≠ ⊥ := y9x_component_ne_bot hd.K_comp
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : Subgroup G, L₀ ∈ 𝒞 := by
    by_contra hne
    push_neg at hne
    have hKle : K ≤ Kf 3 K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) :=
      y9x_le_closureIn K (Subgroup.one_mem _)
    rw [hKF] at hKle
    have hbot : (⨆ L ∈ 𝒞, L) ≤ ⊥ := iSup₂_le fun L hL => absurd hL (hne L)
    exact hK_ne (le_bot_iff.1 (hKle.trans hbot))
  have hL₀c : GLAPComponent 3 (cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) L₀ := h1 L₀ hL₀
  have hL₀X : GLAPComponent 3 (Kf 3 K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) L₀ :=
    hM_comp L₀ hL₀
  have hL₀ne : L₀ ≠ ⊥ := y9x_component_ne_bot hL₀c
  have hcyK : CFSG.Open.IsKGroup ↥(cx y) :=
    isKGroup_of_isKProper hc.ctx.kProper
      (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hd.y_ne)
  have hYdef : Kf 3 K (Subgroup.zpowers y) = closureIn K (GLAPLayer 3 (cx y)) := by
    rw [Kf, y9x_cs_zpowers']
  have hLyN : GLAPLayer 3 (cx y) ≤ Subgroup.normalizer ((Kf 3 K (Subgroup.zpowers y) : Subgroup G) : Set G) := by
    rw [hYdef]
    exact y9x_le_normalizer_closureIn K (GLAPLayer 3 (cx y))
  have ha'Cy : a' ∈ cx y :=
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel ha'E hyE)
  have hzaY : Subgroup.zpowers a' ≤ cx y := Subgroup.zpowers_le.2 ha'Cy
  have hEa' : IsElemAbelian 3 (Subgroup.zpowers a') :=
    isElemAbelian_mono hEel (Subgroup.zpowers_le.2 ha'E)
  have hLF_le : GLAPLayer 3 (cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) ≤ GLAPLayer 3 (cx y) := by
    have e : cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) = cx y ⊓ cs (Subgroup.zpowers a') := by
      rw [hcsF, y9x_cs_zpowers', inf_comm]
    rw [e]
    exact y9x_layer_cz_le hcp hin.l105.lbal hcyK ha'Cy (isPGroup_of_isElemAbelian hEa')
  have hXY : Kf 3 K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) ≤ Kf 3 K (Subgroup.zpowers y) := by
    rw [hYdef]
    exact y9x_closureIn_mono hLF_le
  have hL₀Y : L₀ ≤ Kf 3 K (Subgroup.zpowers y) := hL₀X.1.trans hXY
  have hJ2 : GLAPComponent 3 (cx y ⊓ cs (Subgroup.zpowers a')) L₀ := by
    rw [y9x_cs_zpowers', inf_comm, ← hcsF]
    exact hL₀c
  obtain ⟨𝒞₁, k1, k2, -, k4⟩ := hin.l105.l103.lemma102.i183 G (cx y) hcyK 3 hcp
    (Subgroup.zpowers a') hzaY hEa' L₀ hJ2
  have hL₀_le_sup : L₀ ≤ ⨆ N ∈ 𝒞₁, N := by
    rw [k2]
    exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (le_of_eq (gLBConj_one L₀).symm)
  have hNY : ∀ N ∈ 𝒞₁, N ≤ Kf 3 K (Subgroup.zpowers y) := by
    intro N hN
    have hNle : N ≤ ⨆ N' ∈ 𝒞₁, N' := le_iSup₂ (f := fun N' (_ : N' ∈ 𝒞₁) => N') N hN
    rw [k2] at hNle
    refine hNle.trans (iSup₂_le fun g hg => ?_)
    have hgY := mem_normalizer_iff_gLBConj_eq.1 (hLyN hg)
    exact (y9xF_gLBConj_mono g hL₀Y).trans hgY.le
  have hN₀ : ∃ N₀ : Subgroup G, N₀ ∈ 𝒞₁ := by
    by_contra hne
    push_neg at hne
    have hbot : (⨆ N ∈ 𝒞₁, N) ≤ ⊥ := iSup₂_le fun N hN => absurd hN (hne N)
    exact hL₀ne (le_bot_iff.1 (hL₀_le_sup.trans hbot))
  obtain ⟨N₀, hN₀⟩ := hN₀
  have hN₀c : GLAPComponent 3 (cx y) N₀ := k1 N₀ hN₀
  have hN₀Y : N₀ ≤ Kf 3 K (Subgroup.zpowers y) := hNY N₀ hN₀
  have ha'N₀ : a' ∈ Subgroup.normalizer (N₀ : Set G) := (hact N₀ hN₀c hN₀Y).1
  have hsing : ∀ N ∈ 𝒞₁, N = N₀ := by
    intro N hN
    obtain ⟨e, he, heN⟩ := k4 N₀ hN₀ N hN
    have hen : e ∈ Subgroup.normalizer (N₀ : Set G) := (Subgroup.zpowers_le.2 ha'N₀) he
    rw [mem_normalizer_iff_gLBConj_eq.1 hen] at heN
    exact heN.symm
  have hL₀N₀ : L₀ ≤ N₀ := by
    refine hL₀_le_sup.trans (iSup₂_le fun N hN => ?_)
    exact (hsing N hN).le
  exact ⟨L₀, hL₀X, N₀, hN₀c, hN₀Y, hL₀N₀⟩

private theorem y9xF_le_core_self {p : ℕ} {M : Subgroup G} (hM : Nat.Coprime p (Nat.card M)) :
    M ≤ GLAPPrimeCoreOf p M := by
  have htop : (⊤ : Subgroup ↥M) ≤ GLAPPrimeCore p ↥M := by
    refine le_sSup ⟨inferInstance, ?_⟩
    rwa [Subgroup.card_top]
  intro v hv
  exact ⟨⟨v, hv⟩, htop (Subgroup.mem_top _), rfl⟩

private theorem y9xF_no_common {p : ℕ} (hp : p.Prime) {X C M L L' : Subgroup G}
    (hMc : GLAPComponent p X M) (hLc : GLAPComponent p C L) (hL'c : GLAPComponent p C L')
    (hne : L ≠ L') (hML : M ≤ L) (hML' : M ≤ L') : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : ⁅L, L'⁆ ≤ GLAPPrimeCoreOf p C :=
    CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne hp hLc hL'c hne
  have hMC : M ≤ GLAPPrimeCoreOf p C := by
    have h1 : ⁅M, M⁆ ≤ ⁅L, L'⁆ := Subgroup.commutator_mono hML hML'
    rw [glaPComponent_perfect hMc] at h1
    exact h1.trans hcomm
  have hQ : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p C)) := by
    unfold GLAPPrimeCoreOf
    rw [Subgroup.card_subtype]
    exact CFSG.pPrimeCore_coprime_card
  have hcop : Nat.Coprime p (Nat.card M) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hMC) hQ
  have hMX : M ≤ GLAPPrimeCoreOf p X :=
    (y9xF_le_core_self hcop).trans (glaPPrimeCoreOf_le_of_isSubnormal hp hMc.2.1)
  have hbar : (M.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
    have hzM : (z : G) ∈ M := Subgroup.mem_subgroupOf.1 hz
    have h2 := hMX hzM
    unfold GLAPPrimeCoreOf at h2
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 h2
    have huz : u = z := Subtype.ext hue
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← huz]
    exact hu
  obtain ⟨-, hsimple⟩ := hMc.2.2.1.2.2
  have hnt := hsimple.toNontrivial
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥((M.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))) ⧸
    Subgroup.center ↥((M.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))))
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
  apply hg
  have hs : s = 1 := by
    apply Subtype.ext
    have hmem : (s : ↥X ⧸ GLAPPrimeCore p ↥X) ∈ (⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) := by
      rw [← hbar]
      exact s.2
    exact Subgroup.mem_bot.1 hmem
  rw [hs]
  rfl

theorem Ky_a'_comps (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hp3 : p = 3)
    (hsh : KyShapeIso a y (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers y)))
    {a' : G}
    (hM : ∃ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) M ∧
      ∃ Ki : Subgroup G, GLAPComponent 3 (cx y) Ki ∧ Ki ≤ Kf p K (Subgroup.zpowers y) ∧ M ≤ Ki) :
    ∃ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) M ∧
      a ∉ Subgroup.normalizer (M : Set G) := by
  classical
  subst hp3
  obtain ⟨M, hMc, Ki, hKic, hKiY, hMKi⟩ := hM
  refine ⟨M, hMc, fun haM => ?_⟩
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have haE : a ∈ E := hDE ac.mem
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 (hd.F_E₀ hd.y_F))
  have hEel : IsElemAbelian 3 E := isElemAbelian_mono hd.E₀_el hEE₀
  have ha3 : a ^ 3 = 1 := hEel.2 a haE
  obtain ⟨K₁, K₂, K₃, hK₁, hK₂, hK₃, h12, h13, h23, -, h2a, h3a, huniq, -⟩ := hsh
  have hcyc : GLBConj a K₃ = K₁ := by
    have e1 : a * (a * a) = 1 := by rw [← pow_three]; exact ha3
    calc GLBConj a K₃ = GLBConj a (GLBConj a K₂) := by rw [h3a]
      _ = GLBConj (a * a) K₂ := gLBConj_gLBConj a a K₂
      _ = GLBConj (a * a) (GLBConj a K₁) := by rw [h2a]
      _ = GLBConj (a * (a * a)) K₁ := gLBConj_gLBConj (a * a) a K₁
      _ = K₁ := by rw [e1, gLBConj_one]
  have hMa : GLBConj a M = M := mem_normalizer_iff_gLBConj_eq.1 haM
  have hMaKi : M ≤ GLBConj a Ki := by
    calc M = GLBConj a M := hMa.symm
      _ ≤ GLBConj a Ki := y9xF_gLBConj_mono a hMKi
  rcases huniq Ki hKic hKiY with h | h | h
  · rw [h] at hMKi hMaKi
    rw [← h2a] at hMaKi
    exact y9xF_no_common Nat.prime_three hMc hK₁ hK₂ h12 hMKi hMaKi
  · rw [h] at hMKi hMaKi
    rw [← h3a] at hMaKi
    exact y9xF_no_common Nat.prime_three hMc hK₂ hK₃ h23 hMKi hMaKi
  · rw [h] at hMKi hMaKi
    rw [hcyc] at hMaKi
    exact y9xF_no_common Nat.prime_three hMc hK₃ hK₁ h13.symm hMKi hMaKi

private theorem y9xG_core_inf_le {p : ℕ} (hp : p.Prime) {J X : Subgroup G} (hXJ : X ≤ J)
    (hJN : J ≤ Subgroup.normalizer (GLAPPrimeCoreOf p J : Set G)) :
    GLAPPrimeCoreOf p J ⊓ X ≤ GLAPPrimeCoreOf p X := by
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p J ⊓ X)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf hp J)
  refine le_glaPPrimeCoreOf_of_le_normalizer inf_le_right (fun z hz => ?_) hcop
  exact y9x_normalizer_inf (hJN (hXJ hz)) (Subgroup.le_normalizer hz)

private theorem y9xG_decomp {I J O : Subgroup G} (hIJ : I ≤ J)
    (hJN : J ≤ Subgroup.normalizer (O : Set G)) {x : G} (hx : x ∈ I ⊔ O) :
    ∃ i ∈ I, ∃ o ∈ O, x = i * o := by
  let S : Subgroup G :=
    { carrier := {g | ∃ i ∈ I, ∃ o ∈ O, g = i * o}
      mul_mem' := by
        rintro _ _ ⟨i₁, hi₁, o₁, ho₁, rfl⟩ ⟨i₂, hi₂, o₂, ho₂, rfl⟩
        have hc : i₂⁻¹ * o₁ * i₂ ∈ O := by
          have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hJN (hIJ hi₂))) o₁).1 ho₁
          simpa only [inv_inv] using h2
        refine ⟨i₁ * i₂, I.mul_mem hi₁ hi₂, i₂⁻¹ * o₁ * i₂ * o₂, O.mul_mem hc ho₂, ?_⟩
        group
      one_mem' := ⟨1, I.one_mem, 1, O.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, hi, o, ho, rfl⟩
        have hc : i * o⁻¹ * i⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.1 (hJN (hIJ hi)) o⁻¹).1 (O.inv_mem ho)
        refine ⟨i⁻¹, I.inv_mem hi, i * o⁻¹ * i⁻¹, hc, ?_⟩
        group }
  have hle : I ⊔ O ≤ S :=
    sup_le (fun i hi => ⟨i, hi, 1, O.one_mem, by simp⟩) (fun o ho => ⟨1, I.one_mem, o, ho, by simp⟩)
  obtain ⟨i, hi, o, ho, he⟩ := hle hx
  exact ⟨i, hi, o, ho, he⟩

private theorem y9xG_kc {I J O : Subgroup G} (hIJ : I ≤ J) (hJN : J ≤ Subgroup.normalizer (O : Set G))
    (hsup : I ⊔ O = J) {g : G} (hgO : g ∈ Subgroup.normalizer (O : Set G))
    (hgI : ∀ i ∈ I, g * i = i * g) {n : G} (hn : n ∈ J) :
    g * n * g⁻¹ * n⁻¹ ∈ O := by
  have hn' : n ∈ I ⊔ O := by rw [hsup]; exact hn
  obtain ⟨i, hi, o, ho, rfl⟩ := y9xG_decomp hIJ hJN hn'
  have hco : g * o * g⁻¹ * o⁻¹ ∈ O :=
    O.mul_mem ((Subgroup.mem_normalizer_iff.1 hgO o).1 ho) (O.inv_mem ho)
  have hcalc : g * (i * o) * g⁻¹ * (i * o)⁻¹ = i * (g * o * g⁻¹ * o⁻¹) * i⁻¹ := by
    calc g * (i * o) * g⁻¹ * (i * o)⁻¹ = (g * i) * o * g⁻¹ * o⁻¹ * i⁻¹ := by group
      _ = (i * g) * o * g⁻¹ * o⁻¹ * i⁻¹ := by rw [hgI i hi]
      _ = i * (g * o * g⁻¹ * o⁻¹) * i⁻¹ := by group
  rw [hcalc]
  exact (Subgroup.mem_normalizer_iff.1 (hJN (hIJ hi)) _).1 hco

private theorem y9xG_mem_cx_iff {h y : G} : h ∈ cx y ↔ Commute h y :=
  Subgroup.mem_centralizer_singleton_iff

private theorem y9xG_conj_comm {g h y : G} (hg : Commute g y) (hh : Commute h y) :
    Commute (g * h * g⁻¹) y :=
  (hg.mul_left hh).mul_left hg.inv_left

private theorem y9xG_normalizer_cx {a y : G} (hay : Commute a y) :
    a ∈ Subgroup.normalizer ((cx y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  change h ∈ cx y ↔ a * h * a⁻¹ ∈ cx y
  rw [y9xG_mem_cx_iff, y9xG_mem_cx_iff]
  exact ⟨fun hc => y9xG_conj_comm hay hc,
    fun hc => by simpa [mul_assoc] using y9xG_conj_comm hay.inv_left hc⟩

theorem alpha_a'_lt (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) {a' : G} (ha'D : a' ∈ Dgrp b x) (ha'1 : a' ≠ 1)
    (hcomps : ∃ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) M ∧
      a ∉ Subgroup.normalizer (M : Set G)) :
    ¬ (Ipart p L b ⊔ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a') = Jpart p (Ipart p L b) a') := by
  classical
  intro hI
  obtain ⟨M, hM, haM⟩ := hcomps
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := B_el h
  have haD : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have haB : a ∈ B := (dgrp_facts hc h).1 haD
  have hyB : y ∈ B := hd.toK.y_B
  have hMX : GLAPComponent p (Jpart p (Ipart p L b) a' ⊓ cx y) M :=
    alpha_Kay_comps hc hin h ha'D ha'1 hd.E_def hd.toK.E_B hd.K_comp M hM
  have hcom : ∀ i ∈ Ipart p L b, Commute a i := fun i hi =>
    (y9xG_mem_cx_iff.1 (Ipart_le_cx h haD hi)).symm
  have hcomm : Commute a y := isElemAbelian_commute hBel haB hyB
  have haJ : a ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a' : Subgroup G) : Set G) :=
    (B_le_N_J hc h ha'D).2 haB
  have haX : a ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a' ⊓ cx y : Subgroup G) : Set G) :=
    y9x_normalizer_inf haJ (y9xG_normalizer_cx hcomm)
  have haO : a ∈ Subgroup.normalizer ((GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a') : Subgroup G) : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf p _ haJ
  have hIJ : Ipart p L b ≤ Jpart p (Ipart p L b) a' := le_sup_left.trans (le_of_eq hI)
  have hJN := le_normalizer_glaPPrimeCoreOf p (Jpart p (Ipart p L b) a')
  have hk1 : ∀ n ∈ Jpart p (Ipart p L b) a',
      a * n * a⁻¹ * n⁻¹ ∈ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a') :=
    fun n hn => y9xG_kc hIJ hJN hI haO (fun i hi => hcom i hi) hn
  have hk2 : ∀ n ∈ Jpart p (Ipart p L b) a',
      a⁻¹ * n * a⁻¹⁻¹ * n⁻¹ ∈ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a') :=
    fun n hn => y9xG_kc hIJ hJN hI (Subgroup.inv_mem _ haO) (fun i hi => (hcom i hi).inv_left) hn
  have hOX : GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a') ⊓ (Jpart p (Ipart p L b) a' ⊓ cx y) ≤
      GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a' ⊓ cx y) :=
    y9xG_core_inf_le hp (inf_le_left : Jpart p (Ipart p L b) a' ⊓ cx y ≤ Jpart p (Ipart p L b) a') hJN
  have hGX : GLBConj a (Jpart p (Ipart p L b) a' ⊓ cx y) = Jpart p (Ipart p L b) a' ⊓ cx y :=
    mem_normalizer_iff_gLBConj_eq.1 haX
  have hM'X : GLAPComponent p (Jpart p (Ipart p L b) a' ⊓ cx y) (GLBConj a M) := by
    have := glaPComponent_gLBConj hMX a
    rwa [hGX] at this
  have hXle : Jpart p (Ipart p L b) a' ⊓ cx y ≤ Jpart p (Ipart p L b) a' := inf_le_left
  have hb1 : barX p (Jpart p (Ipart p L b) a' ⊓ cx y) (GLBConj a M) ≤
      barX p (Jpart p (Ipart p L b) a' ⊓ cx y) M := by
    refine barX_le_of_forall hMX.1 ?_
    intro k hk
    have hkX : k ∈ Jpart p (Ipart p L b) a' ⊓ cx y := hM'X.1 hk
    have hkJ : k⁻¹ ∈ Jpart p (Ipart p L b) a' := Subgroup.inv_mem _ (hXle hkX)
    refine ⟨a * k * a⁻¹, mem_gLBConj.1 hk, ?_⟩
    have e : (a * k * a⁻¹)⁻¹ * k = a * k⁻¹ * a⁻¹ * k := by group
    have hKC : a * k⁻¹ * a⁻¹ * k ∈ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a') := by
      simpa only [inv_inv] using hk1 k⁻¹ hkJ
    have hXm : a * k⁻¹ * a⁻¹ * k ∈ Jpart p (Ipart p L b) a' ⊓ cx y :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 haX k⁻¹).1 (Subgroup.inv_mem _ hkX)) hkX
    rw [e]
    exact hOX ⟨hKC, hXm⟩
  have hb2 : barX p (Jpart p (Ipart p L b) a' ⊓ cx y) M ≤
      barX p (Jpart p (Ipart p L b) a' ⊓ cx y) (GLBConj a M) := by
    refine barX_le_of_forall hM'X.1 ?_
    intro m hm
    have hmX : m ∈ Jpart p (Ipart p L b) a' ⊓ cx y := hMX.1 hm
    have hmJ : m⁻¹ ∈ Jpart p (Ipart p L b) a' := Subgroup.inv_mem _ (hXle hmX)
    refine ⟨a⁻¹ * m * a, mem_gLBConj.2 ?_, ?_⟩
    · rw [show a * (a⁻¹ * m * a) * a⁻¹ = m by group]
      exact hm
    · have e : (a⁻¹ * m * a)⁻¹ * m = a⁻¹ * m⁻¹ * a * m := by group
      have hKC : a⁻¹ * m⁻¹ * a * m ∈ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a') := by
        simpa only [inv_inv] using hk2 m⁻¹ hmJ
      have hXm : a⁻¹ * m⁻¹ * a * m ∈ Jpart p (Ipart p L b) a' ⊓ cx y := by
        refine Subgroup.mul_mem _ ?_ hmX
        have h3 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ haX) m⁻¹).1
          (Subgroup.inv_mem _ hmX)
        simpa only [inv_inv] using h3
      rw [e]
      exact hOX ⟨hKC, hXm⟩
  have hGM : GLBConj a M = M := glaPComponent_unique hM'X hMX (le_antisymm hb1 hb2)
  exact haM (mem_normalizer_iff_gLBConj_eq.2 hGM)

private theorem y9xG_L_uniq {p : ℕ} (hp : p.Prime) {X I₀ N : Subgroup G}
    (hI₀ : GLAPComponent p X I₀) (hN : GLAPComponent p X N) (hNI : N ≤ I₀) : N = I₀ := by
  have hq : CFSG.Open.IsQuasisimple (PQuot p I₀) := isQuasisimple_pQuot_of_glaPComponent hp hI₀
  have hNI₀ : GLAPComponent p I₀ N := glaPComponent_of_le hp hN hNI hI₀.1
  obtain ⟨-, hall, hbar⟩ := glaPLayer_of_isQuasisimple hq
  have hNlay : N = GLAPLayer p I₀ := hall N hNI₀
  have hbarN : barX p I₀ N = ⊤ := by rw [hNlay]; exact hbar
  have hsub : I₀ ⊓ GLAPPrimeCoreOf p X = GLAPPrimeCoreOf p I₀ :=
    glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hI₀.2.1
  have hdec : ∀ k ∈ I₀, ∃ j ∈ N, j⁻¹ * k ∈ GLAPPrimeCoreOf p X := by
    intro k hk
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (p := p) (X := I₀) (J := N) (K := I₀)
      (le_of_eq (by rw [barX_self, hbarN])) hk hk
    refine ⟨j, hj, ?_⟩
    have hmem : j⁻¹ * k ∈ I₀ ⊓ GLAPPrimeCoreOf p X := by rw [hsub]; exact hjk
    exact hmem.2
  have h1 : barX p X I₀ ≤ barX p X N := barX_le_of_forall hN.1 hdec
  have h2 : barX p X N ≤ barX p X I₀ := barX_mono (X := X) p hNI
  exact glaPComponent_unique hN hI₀ (le_antisymm h2 h1)

private theorem y9xG_le_layer {X L : Subgroup G} {p : ℕ} (h : GLAPComponent p X L) : L ≤ GLAPLayer p X := by
  unfold GLAPLayer
  exact le_sSup h

theorem alpha_a'_inn (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) {a' : G}
    (ac' : AlphaCtx G p B x L b a')
    (hcomps : ∃ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) M ∧
      a ∉ Subgroup.normalizer (M : Set G)) :
    InnDiagOn p (Subgroup.zpowers y) (Jpart p (Ipart p L b) a') := by
  classical
  obtain ⟨M, hM, haM⟩ := hcomps
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := B_el h
  have ha'D : a' ∈ Dgrp b x := ac'.mem
  have ha'1 : a' ≠ 1 := fun h1 => ac'.not_x (h1 ▸ Subgroup.one_mem _)
  have hyB : y ∈ B := hd.toK.y_B
  have hyp : y ^ p = 1 := hBel.2 y hyB
  have hJc : GLAPComponent p (cx a') (Jpart p (Ipart p L b) a') := (ac'.c105.single a' ha'D ha'1).1
  have hch : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a')) := ac'.c104.1.2
  have hST : IsSTriple p B a' (Jpart p (Ipart p L b) a') := ac'.c104.1.1
  have hyN : y ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a' : Subgroup G) : Set G) :=
    (B_le_N_J hc h ha'D).2 hyB
  have hMX : GLAPComponent p (Jpart p (Ipart p L b) a' ⊓ cx y) M :=
    alpha_Kay_comps hc hin h ha'D ha'1 hd.E_def hd.toK.E_B hd.K_comp M hM
  by_contra hnot
  have hdich := hin.l105.l104.lemma102.dich B a' (Jpart p (Ipart p L b) a') hST
    (isKGroup_of_isKProper hc.ctx.kProper
      (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha'1)) hch y hyB ⟨hyN, hnot⟩
  have hR2 : R2Prop p y (Jpart p (Ipart p L b) a') := by
    rcases hdich with hf | ⟨hp3, htd⟩
    · exact Or.inl hf
    · subst hp3
      exact Or.inr ⟨rfl, htd, ⟨hyN, fun hind => hnot
        (hin.l105.l103.aut.inner_innDiag (cx a') _ y hJc hch hyN hind)⟩⟩
  have hIne : Ipart p (Jpart p (Ipart p L b) a') y ≠ ⊥ := by
    intro h0
    have hMle : M ≤ Ipart p (Jpart p (Ipart p L b) a') y := y9xG_le_layer hMX
    rw [h0] at hMle
    exact glaPComponent_ne_bot' hMX (le_bot_iff.1 hMle)
  obtain ⟨hI91, -⟩ := hin.l105.i91comp (cx a') (Jpart p (Ipart p L b) a') y hJc hch hyp hR2 hIne
  have hall : ∀ N : Subgroup G, GLAPComponent p (Jpart p (Ipart p L b) a' ⊓ cx y) N →
      N = Ipart p (Jpart p (Ipart p L b) a') y :=
    fun N hN => y9xG_L_uniq hp hI91 hN (y9xG_le_layer hN)
  have hMeq : M = Ipart p (Jpart p (Ipart p L b) a') y := hall M hMX
  have haB : a ∈ B := (dgrp_facts hc h).1 ac.mem
  have hcomm : Commute a y := isElemAbelian_commute hBel haB hyB
  have haX : a ∈ Subgroup.normalizer ((Jpart p (Ipart p L b) a' ⊓ cx y : Subgroup G) : Set G) :=
    y9x_normalizer_inf ((B_le_N_J hc h ha'D).2 haB) (y9xG_normalizer_cx hcomm)
  have hGX : GLBConj a (Jpart p (Ipart p L b) a' ⊓ cx y) = Jpart p (Ipart p L b) a' ⊓ cx y :=
    mem_normalizer_iff_gLBConj_eq.1 haX
  have hGI : GLAPComponent p (Jpart p (Ipart p L b) a' ⊓ cx y)
      (GLBConj a (Ipart p (Jpart p (Ipart p L b) a') y)) := by
    have := glaPComponent_gLBConj hI91 a
    rwa [hGX] at this
  have hGeq := hall _ hGI
  have haI : a ∈ Subgroup.normalizer ((Ipart p (Jpart p (Ipart p L b) a') y : Subgroup G) : Set G) :=
    mem_normalizer_iff_gLBConj_eq.2 hGeq
  exact haM (by rw [hMeq]; exact haI)

private theorem y9xG_fieldOn_x {p : ℕ} (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b a : G} (h : Cfg p B x L b) (ha : a ∈ Dgrp b x) (ha1 : a ≠ 1)
    (hxa : x ∉ Subgroup.zpowers a) (hxD : x ∈ Dgrp b x)
    (hsingle : GLAPComponent p (cx a) (Jpart p (Ipart p L b) a))
    (hIS : IsS2 p B a (Jpart p (Ipart p L b) a)) {d : G} (hdD : d ∈ Dgrp b x)
    (hFd : FieldOn p d (Jpart p (Ipart p L b) a)) :
    FieldOn p x (Jpart p (Ipart p L b) a) := by
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hDel, hDc⟩ := dgrp_facts hc h
  have hJ : Jpart p (Ipart p L b) a ≤ cx a := Jpart_le_cx h ha
  have hch : IsChevSimple 2 (PSimple p (Jpart p (Ipart p L b) a)) := hIS.2
  have hcm : CentMod p (Jpart p (Ipart p L b) a) a := centMod_zpowers_of_le hJ (Subgroup.mem_zpowers a)
  have hda : d ∉ Subgroup.zpowers a := by
    intro hda
    have hcd : CentMod p (Jpart p (Ipart p L b) a) d := centMod_zpowers_of_le hJ hda
    have hinn := hin.l105.l103.aut.inner_innDiag (cx a) _ d hsingle hch hcd.1
      (inducesInnerMod_of_centMod hcd)
    exact (hin.l105.l103.aut.field_nonInnDiag (cx a) _ d hsingle hch hFd).2 hinn
  exact fieldOn_of_mem_D hin.fieldpow hp hDel hDc ha ha1 hdD hxD hda hxa hcm hFd

private theorem y9xG_not_mem_zpowers {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hDel : IsElemAbelian p D)
    {x a : G} (hx : x ∈ D) (ha : a ∈ D) (hx1 : x ≠ 1) (ha1 : a ≠ 1) (hax : a ∉ Subgroup.zpowers x) :
    x ∉ Subgroup.zpowers a := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hxa
  have hz : Subgroup.zpowers x = Subgroup.zpowers a :=
    y9x_zpowers_eq hp (orderOf_eq_prime (hDel.2 a ha) ha1) (hDel.2 x hx) hxa hx1
  exact hax (by rw [hz]; exact Subgroup.mem_zpowers a)

theorem alpha_a'_U6 (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) {a' : G} (ac' : AlphaCtx G p B x L b a') :
    p = 3 → ∀ m k : ℕ, 3 ≤ m → Odd m → catalogIs (PSimple 3 (Jpart p (Ipart p L b) a')) (isU6n m) →
      ¬ catalogIs (PSimple 3 K) (isL2n k) := by
  intro hp3 m k hm hmodd hU6
  subst hp3
  classical
  have hp : Nat.Prime 3 := hc.ctx.prime
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian 3 B := hS.1.1
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  obtain ⟨-, hDel, hDc⟩ := dgrp_facts hc h
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have haD : a ∈ Dgrp b x := ac.mem
  have ha'D : a' ∈ Dgrp b x := ac'.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have ha'1 : a' ≠ 1 := fun h1 => ac'.not_x (h1 ▸ Subgroup.one_mem _)
  have hxa : x ∉ Subgroup.zpowers a := y9xG_not_mem_zpowers hp hDel hxD haD hx1 ha1 ac.not_x
  have hxa' : x ∉ Subgroup.zpowers a' := y9xG_not_mem_zpowers hp hDel hxD ha'D hx1 ha'1 ac'.not_x
  have hJ'c : GLAPComponent 3 (cx a') (Jpart 3 (Ipart 3 L b) a') := (ac'.c105.single a' ha'D ha'1).1
  have hJc : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a) := (ac.c105.single a haD ha1).1
  have hFx' : FieldOn 3 x (Jpart 3 (Ipart 3 L b) a') := by
    rcases ac'.c104.2 with ⟨d, hdD, hFd⟩ | ⟨-, htd, -, -⟩
    · exact y9xG_fieldOn_x hc hin h ha'D ha'1 hxa' hxD hJ'c ac'.c104.1 hdD hFd
    · exact (hin.l105.l103.dist.td4_u6 _ m hmodd htd hU6).elim
  obtain ⟨n', rfl⟩ : 3 ∣ m := hin.fu6exp (cx a') (Jpart 3 (Ipart 3 L b) a') x m hJ'c hFx' hU6
  have hn'odd : Odd n' := (Nat.odd_mul.1 hmodd).2
  have hIa' : GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a' ⊓ cx x) (Ipart 3 L b) :=
    I_comp_in_J hc hin.l105.l104 h ha'D ha'1 hxD hxa' hJ'c
  have hU6I : catalogIs (PSimple 3 (Ipart 3 L b)) (isU6n n') :=
    (hin.i91u6 (cx a') (Jpart 3 (Ipart 3 L b) a') x (Ipart 3 L b) n' hJ'c hx3 hFx' hIa' hn'odd).1 hU6
  have hFxa : FieldOn 3 x (Jpart 3 (Ipart 3 L b) a) := by
    rcases ac.c104.2 with ⟨d, hdD, hFd⟩ | ⟨-, -, -, hG2⟩
    · exact y9xG_fieldOn_x hc hin h haD ha1 hxa hxD hJc ac.c104.1 hdD hFd
    · obtain ⟨n0, -, hG2n, -⟩ := alpha_I_G2n hc hin h ac hG2
      exact (hin.l105.l103.dist.g2_u6 _ n0 n' (Or.inr hn'odd) hG2n hU6I).elim
  have hIa : GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ cx x) (Ipart 3 L b) :=
    I_comp_in_J hc hin.l105.l104 h haD ha1 hxD hxa hJc
  have hJaU6 : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) (isU6n (3 * n')) :=
    (hin.i91u6 (cx a) (Jpart 3 (Ipart 3 L b) a) x (Ipart 3 L b) n' hJc hx3 hFxa hIa hn'odd).2 hU6I
  exact hd.K_U6 rfl (3 * n') k hm hmodd hJaU6

theorem Ky_norm_a' (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) {a' : G}
    (ha'D : a' ∈ Dgrp b x) (ha'a : a' ∉ Subgroup.zpowers a)
    (hcomps : ∃ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) M ∧
      a ∉ Subgroup.normalizer (M : Set G)) :
    ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) M →
      x ∈ Subgroup.normalizer (M : Set G) := by
  classical
  intro M hM
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have ha'1 : a' ≠ 1 := fun h1 => ha'a (h1 ▸ Subgroup.one_mem _)
  have hBel : IsElemAbelian p B := B_el h
  have hDB : Dgrp b x ≤ B := (dgrp_facts hc h).1
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have ha'E : a' ∈ E := hDE ha'D
  by_cases ha'x : a' ∈ Subgroup.zpowers x
  ·
    have hx3 : x ^ p = 1 := hBel.2 x (hDB hxD)
    have ha'3 : a' ^ p = 1 := hBel.2 a' (hDB ha'D)
    have hzeq : Subgroup.zpowers a' = Subgroup.zpowers x :=
      casealpha_zpowers_eq hp (orderOf_eq_prime hx3 hx1) ha'3 ha'x ha'1
    have hxa' : x ∈ Subgroup.zpowers a' := hzeq ▸ Subgroup.mem_zpowers x
    have hKcs : K ≤ cs E := hd.K_comp.1.trans inf_le_right
    have hFE : Subgroup.zpowers a' ⊔ Subgroup.zpowers y ≤ E :=
      sup_le (Subgroup.zpowers_le.2 ha'E) (Subgroup.zpowers_le.2 hyE)
    have hKf_cs : Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) ≤
        cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) :=
      casealpha_closureIn_le (hKcs.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFE)))
        (fun g hg => Subgroup.le_normalizer (casealpha_layer_le p _ hg))
    have hMa' : M ≤ cx a' := by
      have this : M ≤ Subgroup.centralizer (((Subgroup.zpowers a' ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) :=
        hM.1.trans hKf_cs
      rw [casealpha_cs_pair a' y] at this
      exact this.trans inf_le_left
    have hMx : M ≤ cx x := fun m hm => by
      have hm' : m * a' = a' * m := Subgroup.mem_centralizer_singleton_iff.1 (hMa' hm)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxa'
      rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
      exact (Commute.zpow_right (show Commute m a' from hm') k).eq
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.1 (hMx hm))
  · have hlt := alpha_a'_lt hc hin h ac hd ha'D ha'1 hcomps
    have hT : ∃ T : Subgroup G, T ≤ Jpart p (Ipart p L b) a' ∧ IsPGroup 2 T ∧
        B ≤ Subgroup.normalizer (T : Set G) ∧ ¬ T ≤ GLAPPrimeCoreOf p (Jpart p (Ipart p L b) a') := by
      obtain ⟨T, hTI, hT2, hTB, hTO, -, -⟩ := ac.c105.T_exists
      have hIJ : Ipart p L b ≤ Jpart p (Ipart p L b) a' :=
        casealpha_le_closureIn _ (Subgroup.one_mem _)
      exact ⟨T, hTI.trans hIJ, hT2, hTB, fun hle => hTO ((le_inf hTI hle).trans (core_inf_le hIJ))⟩
    have ac' : AlphaCtx G p B x L b a' :=
      ⟨ac.c105, ha'D, ha'x, hlt,
        lemma104_alpha hc hin.l105.l104 h ac.d5 ac.caseA
          ⟨ha'D, ha'1, ac.c105.essential a' ha'D ha'1, (ac.c105.single a' ha'D ha'1).1, hlt, hT⟩,
        ac.d5, ac.caseA⟩
    have hk := hd.toK
    have hk' : AlphaKData p B x L b a' y E K :=
      ⟨hk.y_B, hk.y_ne, alpha_a'_inn hc hin h ac hd ac' hcomps, hk.E_def, hk.E_B, hk.K_comp, hk.K_G2,
        alpha_a'_U6 hc hin h ac hd ac'⟩
    exact alpha_Kay_norm_gen hc hin h ac' hk' M hM

theorem Ky_contra (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K) {a' : G}
    (ha'D : a' ∈ Dgrp b x) (ha'a : a' ∉ Subgroup.zpowers a)
    (hcomps : ∃ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) M ∧
      a ∉ Subgroup.normalizer (M : Set G))
    (hnorm' : ∀ M : Subgroup G, GLAPComponent p (Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y)) M →
      x ∈ Subgroup.normalizer (M : Set G)) : False := by
  classical
  obtain ⟨M, hM, haM⟩ := hcomps
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have ha : a ∈ Dgrp b x := ac.mem
  have hS := sstar_triple h.star
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have ha'1 : a' ≠ 1 := fun h1 => ha'a (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  have hBel : IsElemAbelian p B := B_el h
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hxE : x ∈ E := hDE hxD
  have ha'E : a' ∈ E := hDE ha'D
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hd.E₀_el hEE₀
  have hcsE_le : ∀ z ∈ E, cs E ≤ cx z := fun z hz =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hz))
  have hKcs : K ≤ cs E := hd.K_comp.1.trans inf_le_right
  have hFE : Subgroup.zpowers a' ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 ha'E) (Subgroup.zpowers_le.2 hyE)
  have hKf_cs : Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) ≤
      cs (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) :=
    casealpha_closureIn_le (hKcs.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFE)))
      (fun g hg => Subgroup.le_normalizer (casealpha_layer_le p _ hg))
  by_cases ha'x : a' ∈ Subgroup.zpowers x
  ·
    have hx3 : x ^ p = 1 := hBel.2 x (hDB hxD)
    have ha'3 : a' ^ p = 1 := hBel.2 a' (hDB ha'D)
    have hzeq : Subgroup.zpowers a' = Subgroup.zpowers x :=
      casealpha_zpowers_eq hp (orderOf_eq_prime hx3 hx1) ha'3 ha'x ha'1
    rw [hzeq] at hM
    have hZ := hkay.Kxy_single
    have hM' : GLAPComponent p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) M :=
      glaPComponent_of_isSubnormal' hp hZ.2.1 hM
    have hbar : barX p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) M ≤
        barX p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) :=
      barX_mono p hM.1
    have heq := CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hM'.2.2.1 hZ.2.2.1 hbar
    have hMZ : M = Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := glaPComponent_unique hM' hZ heq
    apply haM
    rw [hMZ, Kf]
    refine casealpha_normalizer_closureIn ?_ ?_
    · exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun k hk =>
        Subgroup.mem_centralizer_singleton_iff.1 (hcsE_le a haE (hKcs hk)))
    · refine mem_normalizer_glaPLayer (Subgroup.le_normalizer ?_)
      exact (casealpha_mem_centralizer_iff _ a).2 (sup_le
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hxE haE)))
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hyE haE))))
  ·
    have hxa' : Subgroup.zpowers x ≠ Subgroup.zpowers a' := fun he => ha'x (he ▸ Subgroup.mem_zpowers a')
    have hDeq : Dgrp b x = Subgroup.zpowers a' ⊔ Subgroup.zpowers x :=
      casealpha_dgrp_eq hp hDel hDc ha'D hxD ha'1 hx1 hxa'
    have hxN : x ∈ Subgroup.normalizer (M : Set G) := hnorm' M hM
    have hMa' : M ≤ cx a' := by
      have hM_le : M ≤ Kf p K (Subgroup.zpowers a' ⊔ Subgroup.zpowers y) := hM.1
      have this : M ≤ Subgroup.centralizer (((Subgroup.zpowers a' ⊔ Subgroup.zpowers y : Subgroup G)) : Set G) :=
        hM_le.trans hKf_cs
      rw [casealpha_cs_pair a' y] at this
      exact this.trans inf_le_left
    have ha'N : a' ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun m hm =>
        Subgroup.mem_centralizer_singleton_iff.1 (hMa' hm))
    have hsup : Subgroup.zpowers a' ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (M : Set G) :=
      sup_le (Subgroup.zpowers_le.2 ha'N) (Subgroup.zpowers_le.2 hxN)
    apply haM
    apply hsup
    rw [← hDeq]
    exact ha

theorem Ky_single (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K) :
    GLAPComponent p (cx y) (Kf p K (Subgroup.zpowers y)) := by
  by_contra hns
  obtain ⟨hp3, hsh, hBN⟩ := Ky_shape hc hin h ac hd hkay hns
  have hsh' := Ky_shape_iso hc hin h ac hd hkay hp3 (Ky_shape_diag hc hin h ac hd hkay hp3 hsh)
  obtain ⟨a', ha'D, ha'a, hact⟩ := Ky_a' hc hin h ac hd hkay hp3 hsh' hBN
  have hM := Ky_comp_in_Ki hc hin h ac hd hkay hp3 hsh' hBN ha'D ha'a hact
  have hcomps := Ky_a'_comps hc hin h ac hd hp3 hsh' hM
  exact Ky_contra hc hin h ac hd hkay ha'D ha'a hcomps (Ky_norm_a' hc hin h ac hd ha'D ha'a hcomps)

theorem alpha_Ky_sub (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K)
    (hKy : GLAPComponent p (cx y) (Kf p K (Subgroup.zpowers y))) :
    GLAPComponent p (Kf p K (Subgroup.zpowers y) ⊓ cx x) (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ∧
      GLAPComponent p (Kf p K (Subgroup.zpowers y) ⊓ cx a) (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) ∧
      GLAPLayer p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊓ cx a) ≠ ⊥ := by
  classical
  have hp : p.Prime := hc.ctx.prime
  have ha : a ∈ Dgrp b x := ac.mem
  have ha1 : a ≠ 1 := fun h1 => ac.not_x (h1 ▸ Subgroup.one_mem _)
  have hxa : Subgroup.zpowers x ≠ Subgroup.zpowers a := fun he => ac.not_x (he ▸ Subgroup.mem_zpowers a)
  obtain ⟨-, hDel, hDc⟩ := dgrp_facts hc h
  have hx1 : x ≠ 1 := (sstar_triple h.star).2.1.2.1
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  have hDeq : Dgrp b x = Subgroup.zpowers a ⊔ Subgroup.zpowers x :=
    casealpha_dgrp_eq hp hDel hDc ha hxD ha1 hx1 hxa
  have hDE : Dgrp b x ≤ E := by rw [hd.E_def]; exact le_sup_left
  have hyE : y ∈ E := by rw [hd.E_def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haE : a ∈ E := hDE ha
  have hxE : x ∈ E := hDE hxD
  have hyE0 : y ∈ E₀ := hd.F_E₀ hd.y_F
  have hEE₀ : E ≤ E₀ := by
    rw [hd.E_def]; exact sup_le hd.D_E₀ (Subgroup.zpowers_le.2 hyE0)
  have hEel : IsElemAbelian p E := isElemAbelian_mono hd.E₀_el hEE₀
  have hLc : GLAPComponent p (cx x) L := (sstar_triple h.star).2.2
  have hCa : cx a ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian ha1
  have hCy : cx y ≠ ⊤ := centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hd.y_ne
  have hcyK : CFSG.Open.IsKGroup ↥(cx y) := isKGroup_of_isKProper hc.ctx.kProper hCy
  have hcsE_le : ∀ z ∈ E, cs E ≤ cx z := fun z hz =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hz))
  have hFxyE : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 hxE) (Subgroup.zpowers_le.2 hyE)
  have hFayE : Subgroup.zpowers a ⊔ Subgroup.zpowers y ≤ E :=
    sup_le (Subgroup.zpowers_le.2 haE) (Subgroup.zpowers_le.2 hyE)
  have hyP : IsPGroup p (Subgroup.zpowers y) :=
    isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 hyE))
  have hxP : IsPGroup p (Subgroup.zpowers x) :=
    isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 hxE))
  have haP : IsPGroup p (Subgroup.zpowers a) :=
    isPGroup_of_isElemAbelian (isElemAbelian_mono hEel (Subgroup.zpowers_le.2 haE))
  have hxy : x ∈ cx y := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hxE hyE)
  have hay : a ∈ cx y := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel haE hyE)
  have hcs_xy : cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = cx x ⊓ cx y :=
    casealpha_cs_pair x y
  have hcs_ay : cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) = cx a ⊓ cx y :=
    casealpha_cs_pair a y
  have hcs_zy : cs (Subgroup.zpowers y) = cx y := casealpha_cs_zpowers' y
  have hcs_zx : cs (Subgroup.zpowers x) = cx x := casealpha_cs_zpowers' x
  have hcs_za : cs (Subgroup.zpowers a) = cx a := casealpha_cs_zpowers' a
  have hLy : GLAPLayer p (cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) ≤ GLAPLayer p (cx y) := by
    rw [hcs_xy, inf_comm, ← hcs_zx]
    exact casealpha_layer_cz_le hp hin.l105.lbal hcyK hxy hxP
  have hLy' : GLAPLayer p (cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) ≤ GLAPLayer p (cx y) := by
    rw [hcs_ay, inf_comm, ← hcs_za]
    exact casealpha_layer_cz_le hp hin.l105.lbal hcyK hay haP
  have hKy_eq : Kf p K (Subgroup.zpowers y) = closureIn K (GLAPLayer p (cx y)) := by
    rw [Kf, hcs_zy]
  have hKcs : K ≤ cs E := hd.K_comp.1.trans inf_le_right
  have hKxy_cs : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤
      cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    casealpha_closureIn_le (hKcs.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFxyE)))
      (fun g hg => Subgroup.le_normalizer (casealpha_layer_le p _ hg))
  have hKay_cs : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤
      cs (Subgroup.zpowers a ⊔ Subgroup.zpowers y) :=
    casealpha_closureIn_le (hKcs.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFayE)))
      (fun g hg => Subgroup.le_normalizer (casealpha_layer_le p _ hg))
  have hKxy_Ky : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ Kf p K (Subgroup.zpowers y) := by
    rw [hKy_eq]
    exact casealpha_closureIn_mono hLy
  have hKay_Ky : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤ Kf p K (Subgroup.zpowers y) := by
    rw [hKy_eq]
    exact casealpha_closureIn_mono hLy'
  have hKy_cx : Kf p K (Subgroup.zpowers y) ≤ cx y := by
    rw [hKy_eq]
    exact casealpha_closureIn_le (hKcs.trans (hcsE_le y hyE))
      (fun g hg => Subgroup.le_normalizer (casealpha_layer_le p _ hg))
  have hKxy_cx : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ≤ cx x :=
    casealpha_closureIn_le (hKcs.trans (hcsE_le x hxE))
      (fun g hg => Subgroup.le_normalizer ((inf_le_left : cx x ⊓ cx y ≤ cx x) (by rw [← hcs_xy]; exact casealpha_layer_le p _ hg)))
  have hKay_cx : Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y) ≤ cx a :=
    casealpha_closureIn_le (hKcs.trans (hcsE_le a haE))
      (fun g hg => Subgroup.le_normalizer ((inf_le_left : cx a ⊓ cx y ≤ cx a) (by rw [← hcs_ay]; exact casealpha_layer_le p _ hg)))
  have hconj1 : GLAPComponent p (Kf p K (Subgroup.zpowers y) ⊓ cx x)
      (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) := by
    refine glaPComponent_of_le hp hkay.Kxy_single (le_inf hKxy_Ky hKxy_cx) ?_
    rw [hcs_xy]
    exact le_inf inf_le_right (inf_le_left.trans hKy_cx)
  have hconj2 : GLAPComponent p (Kf p K (Subgroup.zpowers y) ⊓ cx a)
      (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y)) := by
    refine glaPComponent_of_le hp hkay.Kay_single (le_inf hKay_Ky hKay_cx) ?_
    rw [hcs_ay]
    exact le_inf inf_le_right (inf_le_left.trans hKy_cx)
  have hEeq : E = (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers a := by
    rw [hd.E_def, hDeq, sup_assoc, sup_comm]
  have hcsEeq : cs E = cs (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊓ cx a := by
    rw [hEeq, ← hcs_za]
    exact casealpha_cs_sup _ _
  have hK_csE : GLAPComponent p (cs E) K := by
    refine glaPComponent_of_isSubnormal' hp ?_ hd.K_comp
    have hsn := isSubnormal_inf hLc.2.1 (cs E)
    rwa [inf_eq_right.2 (hcsE_le x hxE)] at hsn
  have hconj3 : GLAPLayer p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊓ cx a) ≠ ⊥ := by
    have hKZ : K ≤ Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊓ cx a :=
      le_inf (casealpha_le_closureIn K (Subgroup.one_mem _)) (hKcs.trans (hcsE_le a haE))
    have hZE : Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊓ cx a ≤ cs E := by
      rw [hcsEeq]
      exact inf_le_inf_right _ hKxy_cs
    have hZK := glaPComponent_of_le hp hK_csE hKZ hZE
    intro h0
    have hKle : K ≤ GLAPLayer p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊓ cx a) :=
      le_sSup hZK
    exact casealpha_component_ne_bot hd.K_comp (le_bot_iff.1 (h0 ▸ hKle))
  exact ⟨hconj1, hconj2, hconj3⟩

structure AlphaKy (p : ℕ) (x a y : G) (K : Subgroup G) : Prop where
  Ky_comp : GLAPComponent p (cx y) (Kf p K (Subgroup.zpowers y))
  Kxy_comp : GLAPComponent p (Kf p K (Subgroup.zpowers y) ⊓ cx x) (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y))
  Kay_comp : GLAPComponent p (Kf p K (Subgroup.zpowers y) ⊓ cx a) (Kf p K (Subgroup.zpowers a ⊔ Subgroup.zpowers y))
  layer_ne : GLAPLayer p (Kf p K (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊓ cx a) ≠ ⊥

theorem alpha_ky (hc : S10Ctx G p) (hin : AlphaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b a : G} (h : Cfg p B x L b) (ac : AlphaCtx G p B x L b a) {E₀ F : Subgroup G} {y : G}
    {E K : Subgroup G} (hd : AlphaData p B x L b a E₀ F y E K) (hkay : AlphaKay p x a y K) :
    AlphaKy p x a y K := by
  have hKy := Ky_single hc hin h ac hd hkay
  obtain ⟨h1, h2, h3⟩ := alpha_Ky_sub hc hin h ac hd hkay hKy
  exact ⟨hKy, h1, h2, h3⟩

end S10

end CFSG.LocalAnalysis.GLTheoremA
