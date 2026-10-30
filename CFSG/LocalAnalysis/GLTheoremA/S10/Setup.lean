module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem sstar_triple {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax p B x L) :
    IsSTriple p B x L := h.1.1.1

theorem sstar_norm {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax p B x L) :
    B ≤ Subgroup.normalizer (L : Set G) := h.1.2.2

theorem sstar_s0 {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax p B x L) :
    IsS0 p B x L := h.1.1

theorem sstar_cyc {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax p B x L) :
    CycModSylow p L := h.2

theorem centMod_zpowers_of_le {x g : G} {L : Subgroup G} (hL : L ≤ cx x) (hg : g ∈ Subgroup.zpowers x) :
    CentMod p L g := by
  refine centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 fun l hl => ?_)
  have hx : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.1 (hL hl)
  have hz : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.2 hx
  exact Subgroup.mem_centralizer_iff.1 (hz hg) l hl

theorem inducesInnerMod_of_centMod {L : Subgroup G} {g : G} (h : CentMod p L g) :
    InducesInnerMod p L g := by
  refine ⟨1, Subgroup.one_mem _, fun y hy => ?_⟩
  have hg : g⁻¹ ∈ centModSubgroup p L := (centModSubgroup p L).inv_mem (centMod_iff.1 h)
  have := hg.2 y⁻¹ (L.inv_mem hy)
  simpa [commutatorElement_def, mul_assoc] using this

theorem dgrp_eq_sup (b x : G) : Dgrp b x = Subgroup.zpowers b ⊔ Subgroup.zpowers x := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1

theorem sstar_layer (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} (h : IsSStarMax p B x L) :
    GLAPLayer p (cx x) = L := by
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hS := sstar_triple h
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hLc : GLAPComponent p (cx x) L := hS.2.2
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hxL : x ∈ centModSubgroup p L := by
    refine centMod_iff.1 (centMod_of_mem_centralizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLc.1 hl)
  apply le_antisymm
  · refine sSup_le fun J hJ => ?_
    by_cases hJL : J = L
    · exact hJL ▸ le_rfl
    exfalso
    have hJCm : J ≤ centModSubgroup p L := le_centModSubgroup_of_ne hp hJ hLc hJL
    obtain ⟨w, hwJ, hwp, k, hkJ, hkw⟩ := exists_pow_eq_one_noncomm_of_component hp hp2 hJ
    have hkx : Commute k x := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hkJ)
    have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hwJ)
    have hwnx : w ∉ Subgroup.zpowers x := by
      intro hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact hkw (hkx.zpow_right n).eq
    obtain ⟨hE, hcard⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hwx hwp hxp hx1 hwnx
    have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers x ≤ centModSubgroup p L :=
      sup_le (Subgroup.zpowers_le.2 (hJCm hwJ)) (Subgroup.zpowers_le.2 hxL)
    have hcycS : IsCyclic (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) :=
      h.2 (Subgroup.zpowers w ⊔ Subgroup.zpowers x)
        (fun g hg => centMod_iff.2 (hle hg)) (isPGroup_of_isElemAbelian hE)
    have hdiv : Nat.card (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) ≤ p :=
      card_le_of_isCyclic_of_pow hp hcycS (fun d hd => hE.2 d hd)
    rw [hcard] at hdiv
    have h2 := hp.two_le
    nlinarith
  · exact le_sSup hLc

theorem card_Dgrp {B : Subgroup G} {b x : G} (hB : IsElemAbelian p B) (hp : p.Prime) (hbB : b ∈ B)
    (hxB : x ∈ B) (hx1 : x ≠ 1) (hbx : b ∉ Subgroup.zpowers x) :
    Dgrp b x ≤ B ∧ IsElemAbelian p (Dgrp b x) ∧ Nat.card (Dgrp b x) = p ^ 2 := by
  have hbp : b ^ p = 1 := hB.2 b hbB
  have hxp : x ^ p = 1 := hB.2 x hxB
  have hcomm : b * x = x * b := isElemAbelian_commute hB hbB hxB
  obtain ⟨hE, hc⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hcomm hbp hxp hx1 hbx
  rw [dgrp_eq_sup]
  exact ⟨sup_le (Subgroup.zpowers_le.2 hbB) (Subgroup.zpowers_le.2 hxB), hE, hc⟩

structure GoodB (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b : G) : Prop where
  mem : b ∈ B
  not_mem : b ∉ Subgroup.zpowers x
  prop : R2Prop p b L
  td4_g2 : p = 3 → IsTD4 3 L → centCard2 3 L b = Nat.sqrt (card2 3 L)
  r2_eq : r2 p B L = centCard2 p L b

structure Cfg (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (b : G) : Prop extends GoodB p B x L b where
  star : IsSStarMax p B x L
  maximal : ∀ (B' : Subgroup G) (x' : G) (L' : Subgroup G), IsSStarMax p B' x' L' →
    r2 p B' L' ≤ r2 p B L
  I_ne : Ipart p L b ≠ ⊥
  cent_I : ∀ c ∈ B, CentMod p (Ipart p L b) c ↔ c ∈ Dgrp b x
  inner_I : InnDiagOn p B (Ipart p L b)
  b_choice : (∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p L) →
    ∃ T : Subgroup G, T ≤ Ipart p L b ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p (Ipart p L b)
  r2_le : r2 p B L ≤ 2 * card2 p (Ipart p L b)

theorem exists_maxR2 (hc : S10Ctx G p) :
    ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L ∧
      ∀ (B' : Subgroup G) (x' : G) (L' : Subgroup G), IsSStarMax p B' x' L' →
        r2 p B' L' ≤ r2 p B L := by
  obtain ⟨B₀, x₀, L₀, h₀⟩ := hc.stage5.1
  have hne : ({t : Triple G | IsSStarMax p t.1 t.2.1 t.2.2} : Set (Triple G)).Nonempty :=
    ⟨(B₀, x₀, L₀), h₀⟩
  obtain ⟨t, ht, hmax⟩ := Set.exists_max_image _ (fun t : Triple G => r2 p t.1 t.2.2)
    (Set.toFinite _) hne
  exact ⟨t.1, t.2.1, t.2.2, ht, fun B' x' L' h' => hmax (B', x', L') h'⟩

theorem exists_nid (hc : S10Ctx G p) (hin : AutCalcAt G p) (hnot : ¬ Alt1 G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hstar : IsSStarMax p B x L) : ∃ b₀ ∈ B, NonInnDiag p b₀ L := by
  by_contra hcon
  push Not at hcon
  have hch : IsChevSimple 2 (PSimple p L) := hc.stage8.1 B x L hstar
  have hq : CFSG.Open.IsQuasisimple ↥L := (hc.stage9.1 B x L hstar).1
  have hL := (sstar_triple hstar).2.2
  have hN := sstar_norm hstar
  have hall : ∀ a ∈ B, InnDiagOn p (Subgroup.zpowers a) L := fun a ha => by
    by_contra hn
    exact hcon a ha ⟨hN ha, hn⟩
  have hB : InnDiagOn p B L := hin.innDiag_unif _ L B hL hch hN hall
  exact hnot ⟨B, x, L, hstar, (innDiagOn_iff hL hq).2 hB⟩

theorem sstar_chev2 (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : IsChevSimple 2 (PSimple p L) := hc.stage8.1 B x L h

theorem td4_big_of_not_two {S : Type} [Group S] (h6 : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ IsChevSimple r S)
    (hT : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False))
    (hn : ¬ catalogIs S S9.isTD4two) : catalogIs S (onLie isTrialityD4Big) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hT
  cases i with
  | cyclic p hp => simp [onLie] at hi
  | alternating n hn' => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie j =>
    obtain ⟨d, hv⟩ := j
    cases d with
    | trialityD4 q =>
      have hchar : q.p = 2 := by
        by_contra hq2
        exact h6 q.p q.prime_p hq2 (Or.inl ⟨_, by simp [onLie], ⟨e⟩⟩)
      have hq2 : q.card ≠ 2 := fun h => hn ⟨_, by simp only [S9.isTD4two, onLie]; exact h, ⟨e⟩⟩
      refine ⟨_, ?_, ⟨e⟩⟩
      simp only [onLie, isTrialityD4Big]
      have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hchar]
      have hexp := q.exponent_pos
      refine ⟨?_, ?_⟩
      · have : 2 ≤ q.exponent := by
          by_contra hlt
          have h1 : q.exponent = 1 := by omega
          exact hq2 (by rw [hcard, h1]; norm_num)
        rw [hcard]
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) this
      · rw [hcard]
        intro h3
        have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
        omega
    | _ => simp [onLie] at hi

private theorem setup_exists_D {p : ℕ} (hp : p.Prime) {E : Subgroup G} {x : G} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) (hcomm : ∀ e ∈ E, e * x = x * e) (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ D : Subgroup G, D ≤ E ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ D ⊓ Subgroup.zpowers x = ⊥ := by
  have h2 : 2 ≤ p := hp.two_le
  have hxc : Nat.card (Subgroup.zpowers x) = p := card_zpowers_eq_of_pow hp hx hx1
  obtain ⟨d1, hd1E, hd1x⟩ : ∃ d1 ∈ E, d1 ∉ Subgroup.zpowers x := by
    by_contra hno
    push Not at hno
    have hle := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers x from fun e he => hno e he)
    rw [hEc, hxc] at hle
    nlinarith [Nat.mul_le_mul_left p h2, Nat.mul_le_mul_left (p * p) h2]
  have hd1p : d1 ^ p = 1 := hE.2 d1 hd1E
  have hd1ne : d1 ≠ 1 := fun h => hd1x (h ▸ Subgroup.one_mem _)
  have hH1 := Prop53.isElemAbelian_card_sup_zpowers hp (hcomm d1 hd1E) hd1p hx hx1 hd1x
  obtain ⟨d2, hd2E, hd2H⟩ : ∃ d2 ∈ E, d2 ∉ Subgroup.zpowers d1 ⊔ Subgroup.zpowers x := by
    by_contra hno
    push Not at hno
    have hle := Subgroup.card_le_of_le
      (show E ≤ Subgroup.zpowers d1 ⊔ Subgroup.zpowers x from fun e he => hno e he)
    rw [hEc, hH1.2] at hle
    nlinarith [Nat.mul_le_mul_left (p * p) h2, Nat.mul_le_mul h2 h2]
  have hd2p : d2 ^ p = 1 := hE.2 d2 hd2E
  have hd2d1 : d2 ∉ Subgroup.zpowers d1 := fun h => hd2H (Subgroup.mem_sup_left h)
  obtain ⟨hD, hDc⟩ := Prop53.isElemAbelian_card_sup_zpowers hp
    (isElemAbelian_commute hE hd2E hd1E) hd2p hd1p hd1ne hd2d1
  refine ⟨Subgroup.zpowers d2 ⊔ Subgroup.zpowers d1,
    sup_le (Subgroup.zpowers_le.2 hd2E) (Subgroup.zpowers_le.2 hd1E), hD, hDc, ?_⟩
  by_contra hne
  have hdvd : Nat.card ((Subgroup.zpowers d2 ⊔ Subgroup.zpowers d1) ⊓ Subgroup.zpowers x : Subgroup G) ∣
      Nat.card (Subgroup.zpowers x) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hxc] at hdvd
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact hne (Subgroup.eq_bot_of_card_eq _ h)
  · have heq : (Subgroup.zpowers d2 ⊔ Subgroup.zpowers d1) ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [h, hxc]))
    have hxD : Subgroup.zpowers x ≤ Subgroup.zpowers d2 ⊔ Subgroup.zpowers d1 :=
      (le_of_eq heq.symm).trans inf_le_left
    have hH1D : Subgroup.zpowers d1 ⊔ Subgroup.zpowers x ≤ Subgroup.zpowers d2 ⊔ Subgroup.zpowers d1 :=
      sup_le le_sup_right hxD
    have heqD : Subgroup.zpowers d1 ⊔ Subgroup.zpowers x = Subgroup.zpowers d2 ⊔ Subgroup.zpowers d1 :=
      Subgroup.eq_of_le_of_card_ge hH1D (le_of_eq (by rw [hH1.2, hDc]))
    apply hd2H
    rw [heqD]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers d2)

private theorem setup_tripleLevel_le_five (B L : Subgroup G) : tripleLevel 3 B L ≤ 5 := by
  classical
  unfold tripleLevel
  by_cases h : IsGStar 3 B L
  · rw [if_pos h]
  · rw [if_neg h]
    exact (Nat.min_le_left 4 _).trans (by norm_num)

theorem tripleLevel_eq_of_gStar_imp {B B' L : Subgroup G} {x : G}
    (hstar : IsSStarMax 3 B x L) (hS : IsSTriple 3 B' x L)
    (himp : IsGStar 3 B L → IsGStar 3 B' L) : tripleLevel 3 B' L = dLevel G 3 := by
  classical
  have hB0 : tripleLevel 3 B L = dLevel G 3 := hstar.1.1.2
  have hbdd : BddAbove {j | ∃ (B₁ : Subgroup G) (x₁ : G) (L₁ : Subgroup G),
      IsSTriple 3 B₁ x₁ L₁ ∧ tripleLevel 3 B₁ L₁ = j} := by
    refine ⟨5, ?_⟩
    rintro j ⟨B₁, x₁, L₁, -, rfl⟩
    exact setup_tripleLevel_le_five B₁ L₁
  have hle : tripleLevel 3 B' L ≤ dLevel G 3 := by
    unfold dLevel
    exact le_csSup hbdd ⟨B', x, L, hS, rfl⟩
  have hd5 : dLevel G 3 ≤ 5 := by
    rw [← hB0]
    exact setup_tripleLevel_le_five B L
  by_cases hG : IsGStar 3 B' L
  · have h5 : tripleLevel 3 B' L = 5 := by
      unfold tripleLevel
      rw [if_pos hG]
    omega
  · have hGB : ¬ IsGStar 3 B L := fun h => hG (himp h)
    have heq : tripleLevel 3 B' L = tripleLevel 3 B L := by
      unfold tripleLevel
      rw [if_neg hG, if_neg hGB]
    omega

theorem isGStar_of_td4_big (hc : S10Ctx G 3) (hg2 : TD4G2At G) {B' : Subgroup G} {x : G} {L : Subgroup G}
    {b' : G} (hS : IsSTriple 3 B' x L) (hN : B' ≤ Subgroup.normalizer (L : Set G)) (hb'B : b' ∈ B')
    (hnb : NonInner 3 b' L) (hcc : centCard2 3 L b' = Nat.sqrt (card2 3 L))
    (hbig : catalogIs (PSimple 3 L) (onLie isTrialityD4Big)) (hchev : IsChevSimple 2 (PSimple 3 L)) :
    IsGStar 3 B' L := by
  classical
  have hp : Nat.Prime 3 := hc.ctx.prime
  have hBel : IsElemAbelian 3 B' := hS.1.1
  have hcardB : Nat.card B' = 3 ^ GLATwoLocalRank 3 G := hS.1.2.1
  have hrank : 4 ≤ GLATwoLocalRank 3 G := hc.ctx.rank_ge
  have h81 : 81 ≤ Nat.card B' := by
    rw [hcardB]
    calc (81 : ℕ) = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ GLATwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hrank
  have hxB : x ∈ B' := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hxp : x ^ 3 = 1 := hBel.2 x hxB
  have hLc : GLAPComponent 3 (cx x) L := hS.2.2
  have hLx : L ≤ cx x := hLc.1
  have hb'p : b' ^ 3 = 1 := hBel.2 b' hb'B
  have hb'x : b' ∉ Subgroup.zpowers x := fun hz =>
    hnb.2 (inducesInnerMod_of_centMod (centMod_zpowers_of_le hLx hz))
  obtain ⟨hD0, hD0c⟩ := Prop53.isElemAbelian_card_sup_zpowers hp
    (isElemAbelian_commute hBel hb'B hxB) hb'p hxp hx1 hb'x
  set D : Subgroup G := Subgroup.zpowers b' ⊔ Subgroup.zpowers x with hDdef
  have hDB : D ≤ B' := sup_le (Subgroup.zpowers_le.2 hb'B) (Subgroup.zpowers_le.2 hxB)
  obtain ⟨e, heB', heD⟩ : ∃ e ∈ B', e ∉ D := by
    by_contra hno
    push Not at hno
    have hBD : B' ≤ D := fun e he => hno e he
    have hle : Nat.card B' ≤ Nat.card D := Subgroup.card_le_of_le hBD
    rw [hD0c] at hle
    norm_num at hle
    omega
  have he3 : e ^ 3 = 1 := hBel.2 e heB'
  have he1 : e ≠ 1 := fun h => heD (h ▸ D.one_mem)
  have heZ : Subgroup.zpowers e ≤ B' := Subgroup.zpowers_le.2 heB'
  have hEel : IsElemAbelian 3 (D ⊔ Subgroup.zpowers e) :=
    Prop53.isElemAbelian_sup_of_commute hD0 (Prop53.isElemAbelian_zpowers he3)
      (fun d hd c hc => isElemAbelian_commute hBel (hDB hd) (heZ hc))
  have hce : Nat.card (Subgroup.zpowers e) = 3 := card_zpowers_eq_of_pow hp he3 he1
  have hinf : Nat.card (D ⊓ Subgroup.zpowers e : Subgroup G) = 1 := by
    have hdvd : Nat.card (D ⊓ Subgroup.zpowers e : Subgroup G) ∣ 3 := by
      rw [← hce]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact h
    · exfalso
      have heq : D ⊓ Subgroup.zpowers e = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [h, hce]))
      have hem : e ∈ D ⊓ Subgroup.zpowers e := by
        rw [heq]
        exact Subgroup.mem_zpowers e
      exact heD (Subgroup.mem_inf.1 hem).1
  have hnorm : Subgroup.zpowers e ≤ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hBel (hDB hd) heB')
  have hEc : Nat.card (D ⊔ Subgroup.zpowers e : Subgroup G) = 3 ^ 3 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hinf, hD0c, hce] at h1
    norm_num at h1 ⊢
    omega
  set E : Subgroup G := D ⊔ Subgroup.zpowers e with hEdef
  have hEB : E ≤ B' := sup_le hDB heZ
  have hb'E : b' ∈ E := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers b'))
  have heE : e ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  refine ⟨E, hEB, hEel, hEc, ?_⟩
  rw [closureIn_eq_self hN]
  have hsub : L ⊓ Subgroup.centralizer (E : Set G) = L ⊓ cx b' ⊓ cx e := by
    ext g
    constructor
    · intro h
      obtain ⟨hgL, hgE⟩ := Subgroup.mem_inf.1 h
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgL, ?_⟩, ?_⟩
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hgE b' hb'E).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hgE e heE).symm
    · intro h
      obtain ⟨hgLb, hge⟩ := Subgroup.mem_inf.1 h
      obtain ⟨hgL, hgb⟩ := Subgroup.mem_inf.1 hgLb
      have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hLx hgL)
      have hb'g : b' ∈ Subgroup.centralizer ({g} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hgb).symm
      have hxg : x ∈ Subgroup.centralizer ({g} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 hgx.symm
      have heg : e ∈ Subgroup.centralizer ({g} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hge).symm
      have hEle : E ≤ Subgroup.centralizer ({g} : Set G) :=
        sup_le (sup_le (Subgroup.zpowers_le.2 hb'g) (Subgroup.zpowers_le.2 hxg))
          (Subgroup.zpowers_le.2 heg)
      exact Subgroup.mem_inf.2 ⟨hgL, Subgroup.mem_centralizer_iff.2 fun h' hh' =>
        Subgroup.mem_centralizer_singleton_iff.1 (hEle hh')⟩
  rw [hsub]
  exact hg2 (cx x) L b' hLc hchev hbig (hN hb'B) hb'p hnb.2 hcc e (hN heB') he3
    (isElemAbelian_commute hBel heB' hb'B)

theorem not_isGStar_of_td42 (hperf : TD42PerfAt G) {B₀ : Subgroup G} {x : G} {L : Subgroup G}
    (hS : IsSTriple 3 B₀ x L) (hcyc : CycModSylow 3 L) (htd2 : catalogIs (PSimple 3 L) S9.isTD4two)
    (hB : IsElemAbelian 3 B₀) (hN : B₀ ≤ Subgroup.normalizer (L : Set G)) : ¬ IsGStar 3 B₀ L := by
  classical
  rintro ⟨E, hEB, hE, hE27, hLE⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  rw [closureIn_eq_self hN] at hLE
  have hLc : GLAPComponent 3 (cx x) L := hS.2.2
  have hCel : IsElemAbelian 3 (E ⊓ centModSubgroup 3 L) := isElemAbelian_mono hE inf_le_left
  have hCcyc : IsCyclic ↥(E ⊓ centModSubgroup 3 L) :=
    hcyc (E ⊓ centModSubgroup 3 L) (fun g hg => centMod_iff.2 (Subgroup.mem_inf.1 hg).2)
      (isPGroup_of_isElemAbelian hCel)
  obtain ⟨c, hcE, hc1, hCc⟩ : ∃ c ∈ E, c ≠ 1 ∧ ∀ g ∈ E, CentMod 3 L g → g ∈ Subgroup.zpowers c := by
    by_cases hbot : E ⊓ centModSubgroup 3 L = ⊥
    · have hEne : ∃ y ∈ E, y ≠ 1 := by
        by_contra hno
        push Not at hno
        have hEbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hno
        rw [hEbot, Subgroup.card_bot] at hE27
        norm_num at hE27
      obtain ⟨y, hyE, hy1⟩ := hEne
      refine ⟨y, hyE, hy1, fun g hgE hg => ?_⟩
      have hgC : g ∈ E ⊓ centModSubgroup 3 L := Subgroup.mem_inf.2 ⟨hgE, centMod_iff.1 hg⟩
      rw [hbot, Subgroup.mem_bot] at hgC
      rw [hgC]
      exact Subgroup.one_mem _
    · obtain ⟨g0, hg0⟩ := hCcyc.exists_generator
      have hCeq : ∀ y ∈ E ⊓ centModSubgroup 3 L, y ∈ Subgroup.zpowers (g0 : G) := by
        intro y hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg0 ⟨y, hy⟩)
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        have hv := congrArg Subtype.val hk
        simpa using hv
      have hg0E : (g0 : G) ∈ E := (Subgroup.mem_inf.1 g0.2).1
      have hg01 : (g0 : G) ≠ 1 := by
        intro h
        apply hbot
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hCeq y hy)
        rw [h, one_zpow] at hk
        exact Subgroup.mem_bot.2 hk.symm
      exact ⟨g0, hg0E, hg01, fun g hgE hg => hCeq g (Subgroup.mem_inf.2 ⟨hgE, centMod_iff.1 hg⟩)⟩
  obtain ⟨F, hFE, hFel, hFc, hFinf⟩ :=
    setup_exists_D hp hE hE27 (fun e he => isElemAbelian_commute hE he hcE) (hE.2 c hcE) hc1
  have hFN : F ≤ Subgroup.normalizer (L : Set G) := hFE.trans (hEB.trans hN)
  have hFfaith : ∀ g ∈ F, CentMod 3 L g → g = 1 := by
    intro g hgF hg
    have hgz : g ∈ Subgroup.zpowers c := hCc g (hFE hgF) hg
    have hmem : g ∈ F ⊓ Subgroup.zpowers c := Subgroup.mem_inf.2 ⟨hgF, hgz⟩
    rw [hFinf, Subgroup.mem_bot] at hmem
    exact hmem
  have hY : ∃ K, GLAPComponent 3 (L ⊓ Subgroup.centralizer (E : Set G)) K := by
    by_contra hno
    push Not at hno
    apply hLE
    rw [eq_bot_iff]
    exact sSup_le fun K hK => (hno K hK).elim
  obtain ⟨K, hK⟩ := hY
  have hKY : K ≤ L ⊓ Subgroup.centralizer (E : Set G) := hK.1
  have hKL : K ≤ L := hKY.trans inf_le_left
  have hKF : K ≤ L ⊓ Subgroup.centralizer (F : Set G) :=
    le_inf hKL ((hKY.trans inf_le_right).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFE)))
  have hKperf : ⁅K, K⁆ = K := glaPComponent_perfect hK
  have hK3 : K ≤ GLAPPrimeCoreOf 3 L := hperf (cx x) L F hLc htd2 hFel hFN hFc hFfaith K hKF hKperf
  have hKcop : Nat.Coprime 3 (Nat.card K) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h3
    exact not_dvd_card_glaPPrimeCoreOf hp L (h3.trans (Subgroup.card_dvd_of_le hK3))
  have hKO : GLAPPrimeCoreOf 3 K = K := by
    have htop : GLAPPrimeCore 3 ↥K = ⊤ := by
      refine eq_top_iff.2 ?_
      show (⊤ : Subgroup ↥K) ≤ CFSG.pPrimeCore 3 ↥K
      refine le_sSup ⟨Subgroup.normal_top, ?_⟩
      rw [Subgroup.card_top]
      exact hKcop
    unfold GLAPPrimeCoreOf
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hKY' : K ≤ GLAPPrimeCoreOf 3 (L ⊓ Subgroup.centralizer (E : Set G)) := by
    have hinf := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hK.2.1
    have h2 : K ⊓ GLAPPrimeCoreOf 3 (L ⊓ Subgroup.centralizer (E : Set G)) = K := by
      rw [hinf, hKO]
    exact inf_eq_left.1 h2
  have hbar : barX 3 (L ⊓ Subgroup.centralizer (E : Set G)) K = ⊥ := by
    unfold barX
    rw [eq_bot_iff]
    rintro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hz
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.1 (hKY' (Subgroup.mem_subgroupOf.1 hk))
    have hyk' : y = k := Subtype.ext hyk
    rw [← hyk']
    exact hy
  have hcomp : IsComponentOf (barX 3 (L ⊓ Subgroup.centralizer (E : Set G)) K) ⊤ := hK.2.2.1
  rw [hbar] at hcomp
  obtain ⟨-, -, hq⟩ := hcomp
  obtain ⟨-, hsimple⟩ := hq
  have hnt := hsimple.toNontrivial
  exact (not_subsingleton_iff_nontrivial.mpr hnt) inferInstance

theorem star_replace_level (hc : S10Ctx G 3) (hin : SetupInputs G 3) {B B' : Subgroup G} {x : G} {L : Subgroup G} {b' : G}
    (hstar : IsSStarMax 3 B x L) (htd : IsTD4 3 L) (hS : IsSTriple 3 B' x L)
    (hN : B' ≤ Subgroup.normalizer (L : Set G)) (hb'B : b' ∈ B') (hnb : NonInner 3 b' L)
    (hcc : centCard2 3 L b' = Nat.sqrt (card2 3 L)) : tripleLevel 3 B' L = dLevel G 3 := by
  have hchev : IsChevSimple 2 (PSimple 3 L) := sstar_chev2 hc hstar
  have hBS := sstar_triple hstar
  by_cases hq2 : catalogIs (PSimple 3 L) S9.isTD4two
  · refine tripleLevel_eq_of_gStar_imp hstar hS (fun hG => absurd hG ?_)
    exact not_isGStar_of_td42 hin.perf hBS (sstar_cyc hstar) hq2 hBS.1.1 (sstar_norm hstar)
  · exact tripleLevel_eq_of_gStar_imp hstar hS (fun _ =>
      isGStar_of_td4_big hc hin.g2 hS hN hb'B hnb hcc
        (td4_big_of_not_two (fun r hr hr2 => hc.stage6 B x L hstar r hr hr2) htd hq2) hchev)

theorem star_replace (hc : S10Ctx G 3) (hin : SetupInputs G 3) {B B' : Subgroup G} {x : G} {L : Subgroup G} {b' : G}
    (hstar : IsSStarMax 3 B x L) (htd : IsTD4 3 L) (hS : IsSTriple 3 B' x L)
    (hN : B' ≤ Subgroup.normalizer (L : Set G)) (hb'B : b' ∈ B') (hnb : NonInner 3 b' L)
    (hcc : centCard2 3 L b' = Nat.sqrt (card2 3 L)) : IsSStarMax 3 B' x L := by
  have hS0 : IsS0 3 B' x L := ⟨hS, star_replace_level hc hin hstar htd hS hN hb'B hnb hcc⟩
  have hcm : CycModSylow 3 L := sstar_cyc hstar
  exact ⟨hc.stage4o.2.2.2.2.1 B' x L hS0 hcm, hcm⟩

theorem three_pow_four_le_card_of_sstar (hc : S10Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hstar : IsSStarMax 3 B x L) : 3 ^ 4 ≤ Nat.card B := by
  have hS : IsSTriple 3 B x L := hstar.1.1.1
  rw [hS.1.2.1]
  exact Nat.pow_le_pow_right (by norm_num) hc.ctx.rank_ge

theorem i2023C3_of_sstar (hc : S10Ctx G 3) (hpow : Lemma103PowCore G) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hstar : IsSStarMax 3 B x L) : I2023C3 x L := by
  have hS : IsSTriple 3 B x L := hstar.1.1.1
  have hL : GLAPComponent 3 (cx x) L := hS.2.2
  have hLX : GLAPLayer 3 (cx x) = L := sstar_layer hc hstar
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hxp : x ^ 3 = 1 := hS.1.1.2 x hxB
  have hxo : orderOf x = 3 := orderOf_eq_prime hxp hx1
  have hxX : x ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxc : ∀ g ∈ cx x, g * x = x * g := fun g hg => Subgroup.mem_centralizer_singleton_iff.1 hg
  have hN : cx x ≤ Subgroup.normalizer (L : Set G) := fun g hg => by
    rw [← hLX]
    exact mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)
  have hpow3 := hpow 3 Nat.prime_three (by norm_num) hL hLX hN hstar.2 hxX hxo hxc
  intro g hg h
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := hN hg
  have hcm : g ∈ centModSubgroup 3 L := by
    refine mem_centModSubgroup.2 ⟨hgL, fun l hl => ?_⟩
    have hgi : g⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hgL
    have h1 : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 hgi l).1 hl
      simpa using this
    have hy : l⁻¹ * (g⁻¹ * l * g) ∈ L := L.mul_mem (L.inv_mem hl) h1
    have hyO : l⁻¹ * (g⁻¹ * l * g) ∈ GLAPPrimeCoreOf 3 L := by
      have hsub : IsSubnormal L (cx x) := hL.2.1
      have hint : l⁻¹ * (g⁻¹ * l * g) ∈ L ⊓ GLAPPrimeCoreOf 3 (cx x) :=
        Subgroup.mem_inf.2 ⟨hy, h l hl⟩
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hsub] at hint
      exact hint
    have hcomm : ⁅l, g⁆ = l * (g * (l⁻¹ * (g⁻¹ * l * g)) * g⁻¹) * l⁻¹ := by
      rw [commutatorElement_def]
      group
    have hz : g * (l⁻¹ * (g⁻¹ * l * g)) * g⁻¹ ∈ GLAPPrimeCoreOf 3 L :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf 3 L hgL)
        _).1 hyO
    rw [hcomm]
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 L hl) _).1 hz
  obtain ⟨n, hn⟩ := hpow3 g ⟨hg, hcm⟩
  exact ⟨n, hn⟩

theorem exists_goodB (hc : S10Ctx G p) (hin : SetupInputs G p) (hpow : Lemma103PowCore G)
    {B : Subgroup G} {x : G} {L : Subgroup G}
    (hstar : IsSStarMax p B x L)
    (hmax : ∀ (B' : Subgroup G) (x' : G) (L' : Subgroup G), IsSStarMax p B' x' L' → r2 p B' L' ≤ r2 p B L)
    (hnid : ∃ b₀ ∈ B, NonInnDiag p b₀ L) :
    ∃ (B' : Subgroup G) (b : G), IsSStarMax p B' x L ∧
      (∀ (B'' : Subgroup G) (x'' : G) (L'' : Subgroup G), IsSStarMax p B'' x'' L'' →
        r2 p B'' L'' ≤ r2 p B' L) ∧ GoodB p B' x L b := by
  classical
  obtain ⟨b₀, hb₀B, hb₀N, hb₀n⟩ := hnid
  have hch : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc hstar
  have hS := sstar_triple hstar
  have hL := hS.2.2
  have hBel : IsElemAbelian p B := hS.1.1
  have hLx : L ≤ cx x := hL.1
  have hb₀x : b₀ ∉ Subgroup.zpowers x := fun hz =>
    hb₀n (hin.aut.inner_innDiag _ L b₀ hL hch hb₀N
      (inducesInnerMod_of_centMod (centMod_zpowers_of_le hLx hz)))
  have hKx : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper
      (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hS.2.1.2.1)
  rcases hin.dich B x L hS hKx hch b₀ hb₀B ⟨hb₀N, hb₀n⟩ with hf | ⟨hp3, htd⟩
  · have hnTD : ¬ (p = 3 ∧ IsTD4 3 L) := by
      rintro ⟨hp3, htd⟩
      subst hp3
      exact hin.aut.td4_not_field _ L b₀ hL rfl htd hf
    have hnR : ¬ R2TD4 p B L := fun h => hnTD ⟨h.1, h.2.1⟩
    refine ⟨B, b₀, hstar, hmax, hb₀B, hb₀x, Or.inl hf, fun hp3 htd => absurd ⟨hp3, htd⟩ hnTD, ?_⟩
    exact r2_eq_cent ⟨hin.aut, hin.indep, hin.cent⟩ hL hch hBel hb₀B hf hnR
  · subst hp3
    have hnb : NonInner 3 b₀ L := ⟨hb₀N, fun hinn =>
      hb₀n (hin.aut.inner_innDiag _ L b₀ hL hch hb₀N hinn)⟩
    obtain ⟨B', b, hS', hN', hbB', hbx, hnb', hcc⟩ := hin.i2023 B x L b₀ hstar hch htd hb₀B hnb
      (three_pow_four_le_card_of_sstar hc hstar) (i2023C3_of_sstar hc hpow hstar)
    have hstar' : IsSStarMax 3 B' x L := star_replace hc hin hstar htd hS' hN' hbB' hnb' hcc
    have hR : R2TD4 3 B L := ⟨rfl, htd, b₀, hb₀B, ne_one_of_nonInner hnb, hnb⟩
    have hR' : R2TD4 3 B' L := ⟨rfl, htd, b, hbB', ne_one_of_nonInner hnb', hnb'⟩
    have hr : r2 3 B' L = r2 3 B L := by
      unfold r2
      rw [if_pos hR, if_pos hR']
    refine ⟨B', b, hstar', fun B'' x'' L'' h'' => (hmax B'' x'' L'' h'').trans hr.ge, hbB', hbx,
      Or.inr ⟨rfl, htd, hnb'⟩, fun _ _ => hcc, ?_⟩
    unfold r2
    rw [if_pos hR']
    exact hcc.symm

theorem cent_B_eq (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hstar : IsSStarMax p B x L) : B ⊓ centModSubgroup p L = Subgroup.zpowers x := by
  have h := hc.stage5.2.1 B x L hstar.1
  have hxB : x ∈ B := (sstar_triple hstar).2.1.1
  ext g
  constructor
  · rintro ⟨hgB, hg⟩
    exact (h g hgB).1 (centMod_iff.2 hg)
  · intro hg
    have hgB : g ∈ B := Subgroup.zpowers_le.2 hxB hg
    exact ⟨hgB, centMod_iff.1 ((h g hgB).2 hg)⟩

theorem p3_mul_cent_le (hc : S10Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hstar : IsSStarMax p B x L) : p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B := by
  have hS := sstar_triple hstar
  have hp : p.Prime := hc.ctx.prime
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  rw [cent_B_eq hc hstar, Nat.card_zpowers, hord, hS.1.2.1]
  have h4 : 4 ≤ GLATwoLocalRank p G := hc.ctx.rank_ge
  calc p ^ 3 * p = p ^ 4 := by ring
    _ ≤ p ^ GLATwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4

theorem exists_goodB' (hc : S10Ctx G p) (hin : SetupInputs G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} {b : G} (hstar : IsSStarMax p B x L) (hgood : GoodB p B x L b) :
    ∃ a : G, GoodB p B x L a ∧
      ((∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
          ¬ T ≤ GLAPPrimeCoreOf p L) →
        ∃ T : Subgroup G, T ≤ Ipart p L a ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
          ¬ T ≤ GLAPPrimeCoreOf p (Ipart p L a)) := by
  classical
  by_cases hT : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p L
  · obtain ⟨a, haB, hax, hap, hag2, hTa⟩ := hin.i2021 B x L b hstar (sstar_chev2 hc hstar) hgood.mem hgood.not_mem
      hgood.prop hgood.td4_g2 (p3_mul_cent_le hc hstar) hT
    have hL := (sstar_triple hstar).2.2
    have hch : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc hstar
    have hBel : IsElemAbelian p B := (sstar_triple hstar).1.1
    refine ⟨a, ⟨haB, hax, hap, hag2, ?_⟩, fun _ => hTa⟩
    rcases hap with hf | ⟨hp3, htd, hna⟩
    · have hnR : ¬ R2TD4 p B L := by
        rintro ⟨hp3, htd, -⟩
        subst hp3
        exact hin.aut.td4_not_field _ L a hL rfl htd hf
      exact r2_eq_cent ⟨hin.aut, hin.indep, hin.cent⟩ hL hch hBel haB hf hnR
    · subst hp3
      have hR : R2TD4 3 B L := ⟨rfl, htd, a, haB, ne_one_of_nonInner hna, hna⟩
      unfold r2
      rw [if_pos hR]
      exact (hag2 rfl htd).symm
  · exact ⟨b, hgood, fun h => absurd h hT⟩

theorem exclude_U38_notG (hc : S10Ctx G 3) (hin : SetupInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hstar : IsSStarMax 3 B x L) (hU : catalogIs (PSimple 3 L) S9.isU3eight) : ¬ IsGStar 3 B L := by
  rintro ⟨E, hEB, hE, hE27, hLE⟩
  have hp : Nat.Prime 3 := hc.ctx.prime
  have hS := sstar_triple hstar
  have hBel : IsElemAbelian 3 B := hS.1.1
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  have hLc : GLAPComponent 3 (cx x) L := hS.2.2
  have hLx : L ≤ cx x := hLc.1
  have hLay : GLAPLayer 3 (cx x) = L := sstar_layer hc hstar
  have hNL : B ≤ Subgroup.normalizer (L : Set G) := sstar_norm hstar
  rw [closureIn_eq_self hNL] at hLE
  have hBx : B ≤ cx x := isElemAbelian_le_centralizer hBel hxB
  have hKx : CFSG.Open.IsKGroup ↥(cx x) :=
    isKGroup_of_isKProper hc.ctx.kProper
      (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hx1)
  have hEx : ∀ e ∈ E, e * x = x * e := fun e he => isElemAbelian_commute hBel (hEB he) hxB
  obtain ⟨D, hDE, hD, hD9, hDx⟩ := setup_exists_D hp hE hE27 hEx hx3 hx1
  have hDB : D ≤ B := hDE.trans hEB
  have hDcent : D ⊓ centModSubgroup 3 L = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgB : g ∈ B ⊓ centModSubgroup 3 L := ⟨hDB hg.1, hg.2⟩
    rw [cent_B_eq hc hstar] at hgB
    have hgDx : g ∈ D ⊓ Subgroup.zpowers x := ⟨hg.1, hgB⟩
    rw [hDx] at hgDx
    exact hgDx
  have hcardD : Nat.card D = 3 ^ 2 * Nat.card ↥(D ⊓ centModSubgroup 3 L) := by
    rw [hDcent, Subgroup.card_bot, hD9, mul_one]
  have hDN : D ≤ Subgroup.normalizer (L : Set G) := hDB.trans hNL
  have hL269 : catalogIs (PSimple 3 L) S9.isList269 :=
    catalogIs_imp (fun _ hi => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi))))) hU
  have hI269 : GLAPLayer 3 (L ⊓ cs D) = ⊥ := hin.i269 (cx x) L D hKx hLc hL269 hD hDN hcardD
  have hDX : D ≤ cx x := hDB.trans hBx
  have hDp : IsPGroup 3 D := isPGroup_of_isElemAbelian hD
  have hBal1 : GLAPLayer 3 (cx x ⊓ cs D) ≤ L := by
    have h := hin.lbal (cx x) D hKx hDX hDp
    rw [hLay] at h
    exact h
  have hMlay : GLAPLayer 3 (cx x ⊓ cs D) = ⊥ := by
    rw [eq_bot_iff]
    refine sSup_le fun K hK => ?_
    have hKlay : K ≤ GLAPLayer 3 (cx x ⊓ cs D) := le_sSup hK
    have hKL : K ≤ L := hKlay.trans hBal1
    have hKD : K ≤ cs D := hK.1.trans inf_le_right
    have hKc : GLAPComponent 3 (L ⊓ cs D) K :=
      glaPComponent_of_le hp hK (le_inf hKL hKD) (inf_le_inf_right _ hLx)
    have hKl : K ≤ GLAPLayer 3 (L ⊓ cs D) := le_sSup hKc
    rw [hI269] at hKl
    exact hKl
  have hEcD : E ≤ cs D := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hE (hDE hd) he
  have hCD : cs E ≤ cs D := Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDE)
  have hEp : IsPGroup 3 E := isPGroup_of_isElemAbelian hE
  have hEM : E ≤ cx x ⊓ cs D := le_inf (hEB.trans hBx) hEcD
  have hMK : CFSG.Open.IsKGroup ↥(cx x ⊓ cs D) := CFSG.Open.IsKGroup.of_le hKx inf_le_left
  have hKMlay : GLAPLayer 3 ((cx x ⊓ cs D) ⊓ cs E) ≤ GLAPLayer 3 (cx x ⊓ cs D) :=
    hin.lbal (cx x ⊓ cs D) E hMK hEM hEp
  have hMA : (cx x ⊓ cs D) ⊓ cs E = cx x ⊓ cs E := by
    rw [inf_assoc, inf_eq_right.2 hCD]
  have hA1 : GLAPLayer 3 (cx x ⊓ cs E) ≤ ⊥ := by
    rw [← hMA]
    exact hKMlay.trans hMlay.le
  have hNA : L ⊓ cs E ≤ cx x ⊓ cs E := inf_le_inf_right _ hLx
  have hnorm : ((L ⊓ cs E).subgroupOf (cx x ⊓ cs E)).Normal := by
    constructor
    intro n hn g
    obtain ⟨g, hgA⟩ := g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgN : g ∈ Subgroup.normalizer (GLAPLayer 3 (cx x) : Set G) :=
      mem_normalizer_glaPLayer (Subgroup.le_normalizer hgA.1)
    rw [hLay] at hgN
    refine ⟨(Subgroup.mem_normalizer_iff.1 hgN _).1 hn.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
    have h1 : Commute e g := Subgroup.mem_centralizer_iff.1 hgA.2 e he
    have h2 : Commute e (n : G) := Subgroup.mem_centralizer_iff.1 hn.2 e he
    exact ((h1.mul_right h2).mul_right h1.inv_right).eq
  have hsub : IsSubnormal (L ⊓ cs E) (cx x ⊓ cs E) :=
    IsSubnormal.step hNA hnorm (IsSubnormal.refl _)
  apply hLE
  rw [eq_bot_iff]
  refine sSup_le fun K hK => ?_
  have hKA : GLAPComponent 3 (cx x ⊓ cs E) K := glaPComponent_of_isSubnormal' hp hsub hK
  have hKl : K ≤ GLAPLayer 3 (cx x ⊓ cs E) := le_sSup hKA
  exact hKl.trans hA1

theorem exclude_U38 (hc : S10Ctx G 3) (hin : SetupInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hstar : IsSStarMax 3 B x L) (hU : catalogIs (PSimple 3 L) S9.isU3eight) : False := by
  have hS := sstar_triple hstar
  have hnG := exclude_U38_notG hc hin hstar hU
  have hd2 : dLevel G 3 ≤ 2 := by
    have h1 := hstar.1.1.2
    unfold tripleLevel at h1
    rw [if_neg hnG] at h1
    have h2 := hin.lvl (cx x) L hS.2.2 hU
    omega
  have hBel : IsElemAbelian 3 B := hS.1.1
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hS.1.1.2 x hxB) hx1
  obtain ⟨-, -, T, hTc, hT2, hTB, hne, -⟩ := hS.2.1
  have hTO : T ≤ GLAPPrimeCoreOf 3 (cx x) := by
    by_contra hTO
    have hle := hin.u38 x L hx3 hS.2.2 hU (sstar_cyc hstar) (sstar_layer hc hstar) B T
      (isElemAbelian_le_centralizer hBel hxB) hBel hTc hT2 hTB hTO
    have h4 : 4 ≤ GLATwoLocalRank 3 G := hc.ctx.rank_ge
    have h5 : 3 ^ 4 ≤ 3 ^ GLATwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) h4
    rw [← hS.1.2.1] at h5
    omega
  exact hne (hc.stage4.2.2 hd2 B x T hS.1 hxB hx1 hTO hT2 hTB)

theorem cfg_I (hc : S10Ctx G p) (hin : SetupInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (hstar : IsSStarMax p B x L) (hgood : GoodB p B x L b) :
    Ipart p L b ≠ ⊥ ∧ (∀ c ∈ B, CentMod p (Ipart p L b) c ↔ c ∈ Dgrp b x) ∧
      InnDiagOn p B (Ipart p L b) := by
  have hS156 := sstar_triple hstar
  have hch156 : IsChevSimple 2 (PSimple p L) := sstar_chev2 hc hstar
  have hKx156 : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    isKGroup_of_isKProper hc.ctx.kProper
      (centralizer_ne_top_of_ne_one hc.ctx.simple hc.ctx.nonabelian hS156.2.1.2.1)
  rcases hin.i156 B x L b hstar hch156 (fun c hcB hn => hin.dich B x L hS156 hKx156 hch156 c hcB hn)
      hgood.mem hgood.prop hgood.td4_g2 (p3_mul_cent_le hc hstar) with
    ⟨hI, hcI, hinn⟩ | ⟨hp3, hU⟩
  · refine ⟨hI, fun c hcB => ?_, hinn⟩
    rw [hcI c hcB, dgrp_eq_sup, cent_B_eq hc hstar]
  · subst hp3
    exact (exclude_U38 hc hin hstar hU).elim

theorem exists_cfg (hc : S10Ctx G p) (hin : SetupInputs G p) (hpow : Lemma103PowCore G)
    (hnot : ¬ Alt1 G p) :
    ∃ (B : Subgroup G) (x : G) (L : Subgroup G) (b : G), Cfg p B x L b := by
  obtain ⟨B, x, L, hstar, hmax⟩ := exists_maxR2 hc
  obtain ⟨B', b, hstar', hmax', hgood⟩ :=
    exists_goodB hc hin hpow hstar hmax (exists_nid hc hin.aut hnot hstar)
  obtain ⟨a, hgoodA, hchoice⟩ := exists_goodB' hc hin hstar' hgood
  obtain ⟨hI, hcI, hinn⟩ := cfg_I hc hin hstar' hgoodA
  have hS := sstar_triple hstar'
  have hr2 : r2 p B' L ≤ 2 * card2 p (Ipart p L a) := by
    rw [hgoodA.r2_eq]
    exact hin.i91 _ L a hS.2.2 (sstar_chev2 hc hstar') (hS.1.1.2 a hgoodA.mem) hgoodA.prop hI
  exact ⟨B', x, L, a, ⟨hgoodA, hstar', hmax', hI, hcI, hinn, hchoice, hr2⟩⟩

end S10

end CFSG.LocalAnalysis.GLTheoremA
