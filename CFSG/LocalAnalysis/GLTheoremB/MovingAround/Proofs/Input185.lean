module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma114Full
public import CFSG.LocalAnalysis.GLTheoremA.CatA.LStar
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input185

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem layer_join_sylow_eq {p : ℕ} [hp : Fact p.Prime] {Q₀ : Subgroup X}
    (hQ₀ : IsSylowIn p (Lemma114Layer.layerOf X) Q₀) :
    Lemma114Layer.layerOf X ⊔
        ⨆ (Q : Subgroup X) (_ : IsSylowIn p (Lemma114Layer.layerOf X) Q),
          GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set X)) =
      Lemma114Layer.layerOf X ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer (Q₀ : Set X)) := by
  refine le_antisymm (sup_le le_sup_left (iSup₂_le fun Q hQ => ?_))
    (sup_le le_sup_left ((le_iSup₂_of_le (f := fun Q (_ : IsSylowIn p (Lemma114Layer.layerOf X) Q) =>
      GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set X))) Q₀ hQ₀ le_rfl).trans le_sup_right))
  obtain ⟨h, hh, hQeq⟩ := Lemma114Full.l114f_sylow_glbConj hQ₀ hQ
  rw [← hQeq, Lemma114Full.l114f_glaPPrimeCore_centralizer_glbConj]
  intro x hx
  exact Lemma114Full.l114f_glbConj_mem_sup hh hx

theorem pPrimeCore_centralizer_le_of_sylow {p : ℕ} [hp : Fact p.Prime] {Q : Subgroup X}
    (hQ : IsSylowIn p (Lemma114Layer.layerOf X) Q) :
    GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set X)) ≤
      Lemma114Layer.layerOf X ⊔
        ⨆ (Q' : Subgroup X) (_ : IsSylowIn p (Lemma114Layer.layerOf X) Q'),
          GLAPPrimeCoreOf p (Subgroup.centralizer (Q' : Set X)) :=
  (le_iSup₂_of_le (f := fun Q' (_ : IsSylowIn p (Lemma114Layer.layerOf X) Q') =>
    GLAPPrimeCoreOf p (Subgroup.centralizer (Q' : Set X))) Q hQ le_rfl).trans le_sup_right

abbrev layerJoin (p : ℕ) (X : Type) [Group X] [Finite X] : Subgroup X :=
  Lemma114Layer.layerOf X ⊔ ⨆ (Q : Subgroup X) (_ : IsSylowIn p (Lemma114Layer.layerOf X) Q),
    GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set X))

@[expose] def PPrimeStar : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore p X = ⊥ →
    ∀ S : Subgroup X, CFSG.Open.fusionIsSylowIn p S ⊤ →
      ∀ g ∈ Subgroup.centralizer
          ((S ⊓ (Lemma114Layer.layerOf X ⊔ CFSG.pCore p X) : Subgroup X) : Set X),
        ¬ p ∣ orderOf g →
          g ∈ Lemma114Layer.layerOf X ⊔
            GLAPPrimeCoreOf p (Subgroup.centralizer ((S ⊓ Lemma114Layer.layerOf X : Subgroup X) : Set X))

section PartI

def fixerAut {K : Type} [Group K] (P : Subgroup K) : Subgroup (MulAut K) :=
  fixingSubgroup (MulAut K) (P : Set K)

theorem mem_fixerAut {K : Type} [Group K] {P : Subgroup K} {α : MulAut K} :
    α ∈ fixerAut P ↔ ∀ x ∈ P, α x = x :=
  mem_fixingSubgroup_iff (MulAut K) (s := (P : Set K))

@[expose] def Input7_10_1 : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → ∀ P : Subgroup K, CFSG.Open.fusionIsSylowIn p P ⊤ →
      CFSG.HasNormalPComplement p ↥(fixerAut P)

end PartI

section Reduction

variable {X : Type} [Group X] [Finite X]

theorem conj_mem_centralizer {H : Subgroup X} {g n : X} (hg : g ∈ Subgroup.centralizer (H : Set X))
    (hn : n ∈ Subgroup.centralizer (H : Set X)) :
    g * n * g⁻¹ ∈ Subgroup.centralizer (H : Set X) := by
  refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
  have hrg : r * g = g * r := Subgroup.mem_centralizer_iff.1 hg r hr
  have hrn : r * n = n * r := Subgroup.mem_centralizer_iff.1 hn r hr
  have hgi : g⁻¹ * r = r * g⁻¹ := by
    calc g⁻¹ * r = g⁻¹ * (r * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * r) * g⁻¹ := by rw [hrg]
      _ = r * g⁻¹ := by group
  calc r * (g * n * g⁻¹) = (r * g) * n * g⁻¹ := by group
    _ = (g * r) * n * g⁻¹ := by rw [hrg]
    _ = g * (r * n) * g⁻¹ := by group
    _ = g * (n * r) * g⁻¹ := by rw [hrn]
    _ = g * n * (r * g⁻¹) := by group
    _ = g * n * (g⁻¹ * r) := by rw [hgi]
    _ = g * n * g⁻¹ * r := by group

theorem pPrime_mem_layer_of_mem_sup {p : ℕ} [hp : Fact p.Prime] {y : X}
    (hy : y ∈ Lemma114Layer.layerOf X ⊔ CFSG.pCore p X) (hyp : ¬ p ∣ orderOf y) :
    y ∈ Lemma114Layer.layerOf X := by
  haveI : (Lemma114Layer.layerOf X).Normal := Lemma114Layer.layerOf_normal
  obtain ⟨e, he, o, ho, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Lemma114Layer.layerOf X) (t := CFSG.pCore p X)).1 hy
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := X)) ⟨o, ho⟩
  have hok : o ^ (p ^ k) = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have he' : (QuotientGroup.mk' (Lemma114Layer.layerOf X)) e = 1 :=
    (QuotientGroup.eq_one_iff e).2 he
  have hyk : (e * o) ^ (p ^ k) ∈ Lemma114Layer.layerOf X := by
    have h2 : (QuotientGroup.mk' (Lemma114Layer.layerOf X)) ((e * o) ^ (p ^ k)) = 1 := by
      rw [map_pow, map_mul, he', one_mul, ← map_pow, hok, map_one]
    exact (QuotientGroup.eq_one_iff _).1 h2
  exact Lemma114Layer.mem_of_pow_pow_mem hyp (pow_orderOf_eq_one _) hyk

theorem centralizer_le_layerJoin_of_star (hS : PPrimeStar) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hK : CFSG.Open.IsKGroup X) (hO : GLAPPrimeCore p X = ⊥) :
    ∀ n : ℕ, ∀ B : Subgroup X, IsPGroup p B → Nat.card X - Nat.card B = n →
      GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ≤ layerJoin p X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hB hn
  obtain ⟨S, hBS⟩ := IsPGroup.exists_le_sylow hB
  have hSsyl : CFSG.Open.fusionIsSylowIn p (S : Subgroup X) ⊤ :=
    ⟨le_top, S.isPGroup', fun P _ hP hle => S.is_maximal' hP hle⟩
  haveI : (Lemma114Layer.layerOf X).Normal := Lemma114Layer.layerOf_normal
  haveI : (CFSG.pCore p X).Normal := CFSG.pCore_normal (p := p) (G := X)
  have hYn : (Lemma114Layer.layerOf X ⊔ CFSG.pCore p X).Normal := Subgroup.sup_normal _ _
  haveI := hYn
  set Y : Subgroup X := Lemma114Layer.layerOf X ⊔ CFSG.pCore p X with hYdef
  set T : Subgroup X := (S : Subgroup X) ⊓ Y with hTdef
  have hBN : B ≤ Subgroup.normalizer (T : Set X) := by
    refine Lemma114Layer.le_normalizer_of_conj fun w hw y hy => ?_
    obtain ⟨hyS, hyY⟩ := Subgroup.mem_inf.1 hy
    exact Subgroup.mem_inf.2 ⟨(S : Subgroup X).mul_mem ((S : Subgroup X).mul_mem (hBS hw) hyS)
      ((S : Subgroup X).inv_mem (hBS hw)), hYn.conj_mem y hyY w⟩
  have hBT : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T := fun b hb t ht =>
    (Subgroup.mem_normalizer_iff.1 (hBN hb) t).1 ht
  have hTp : IsPGroup p (T : Subgroup X) := (S.isPGroup').to_le inf_le_left
  have hTS : (T : Subgroup X) ≤ (S : Subgroup X) := inf_le_left
  have hTY : (T : Subgroup X) ≤ Y := inf_le_right
  set Q : Subgroup X := T ⊓ Subgroup.normalizer (B : Set X) with hQdef
  have hQp : IsPGroup p Q := hTp.to_le inf_le_left
  have hQT : Q ≤ T := inf_le_left
  have hQN : ∀ q ∈ Q, q ∈ Subgroup.normalizer (B : Set X) := fun q hq => (Subgroup.mem_inf.1 hq).2
  by_cases hQB : Q ≤ B
  ·
    let H : Subgroup X :=
      { carrier := {y | ∃ b ∈ B, ∃ t ∈ T, y = b * t}
        mul_mem' := by
          rintro _ _ ⟨b1, hb1, t1, ht1, rfl⟩ ⟨b2, hb2, t2, ht2, rfl⟩
          exact ⟨b1 * b2, B.mul_mem hb1 hb2, b2⁻¹ * t1 * b2⁻¹⁻¹ * t2,
            T.mul_mem (hBT b2⁻¹ (B.inv_mem hb2) t1 ht1) ht2, by group⟩
        one_mem' := ⟨1, B.one_mem, 1, T.one_mem, by group⟩
        inv_mem' := by
          rintro _ ⟨b, hb, t, ht, rfl⟩
          exact ⟨b⁻¹, B.inv_mem hb, b * t⁻¹ * b⁻¹, hBT b hb t⁻¹ (T.inv_mem ht), by group⟩ }
    have hHS : H ≤ (S : Subgroup X) := by
      rintro _ ⟨b, hb, t, ht, rfl⟩
      exact (S : Subgroup X).mul_mem (hBS hb) (hTS ht)
    have hBH : B ≤ H := fun b hb => ⟨b, hb, 1, T.one_mem, by group⟩
    have hHB : H ≤ B := CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18.pgroup_normalizer_strict
      (S.isPGroup'.to_le hHS) hBH (by
      rintro y ⟨b, hb, t, ht, rfl⟩ hyN
      have htN : t ∈ Subgroup.normalizer (B : Set X) := by
        have h1 := (Subgroup.normalizer (B : Set X)).mul_mem
          ((Subgroup.normalizer (B : Set X)).inv_mem (Subgroup.le_normalizer hb)) hyN
        simpa using h1
      exact B.mul_mem hb (hQB (Subgroup.mem_inf.2 ⟨ht, htN⟩)))
    have hTB : (T : Subgroup X) ≤ B := fun t ht => hHB ⟨1, B.one_mem, t, ht, by group⟩
    have hDT : GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ≤
        Subgroup.centralizer (T : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (Subgroup.mem_centralizer_iff.1
        (CFSG.LocalAnalysis.GLTheoremA.lstar_glaPPrimeCoreOf_le p _ hx)) t (hTB ht)
    have hSE : CFSG.Open.fusionIsSylowIn p ((S : Subgroup X) ⊓ Lemma114Layer.layerOf X)
        (Lemma114Layer.layerOf X) :=
      CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18.fusion_inf_normal hSsyl le_top inferInstance
    have hDS := pPrimeCore_centralizer_le_of_sylow (p := p)
      (show IsSylowIn p (Lemma114Layer.layerOf X) ((S : Subgroup X) ⊓ Lemma114Layer.layerOf X) from hSE)
    intro x hx
    have hxp : ¬ p ∣ orderOf x := Lemma114Layer.not_dvd_orderOf_of_mem_glaPPrimeCoreOf hx
    have hxmem := hS p hp.out hp2 X hK hO (S : Subgroup X) hSsyl x (hDT hx) hxp
    have hEJ : Lemma114Layer.layerOf X ⊔ GLAPPrimeCoreOf p
        (Subgroup.centralizer (((S : Subgroup X) ⊓ Lemma114Layer.layerOf X : Subgroup X) : Set X)) ≤
          layerJoin p X := sup_le le_sup_left hDS
    exact hEJ hxmem
  ·
    set R : Subgroup X := Q ⊔ B with hRdef
    have hRS : R ≤ (S : Subgroup X) := sup_le (hQT.trans hTS) hBS
    have hRp : IsPGroup p R := S.isPGroup'.to_le hRS
    have hBR : B < R := lt_of_le_of_ne le_sup_right (fun h => hQB (le_sup_left.trans (le_of_eq h.symm)))
    have hcardlt : Nat.card B < Nat.card R := Subgroup.card_lt_of_lt hBR
    have hcardle : Nat.card R ≤ Nat.card X := Subgroup.card_le_card_group _
    have hIH := ih (Nat.card X - Nat.card R) (by omega) R hRp rfl
    refine CFSG.LocalAnalysis.GLTheoremA.lstar_coprime_criterion (Q := Q)
      (D := GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X))) (N := layerJoin p X) hQp
      (Lemma114Layer.coprime_card_glaPPrimeCoreOf _)
      (fun q hq => CFSG.LocalAnalysis.GLTheoremA.lstar_normalizer_centralizer (hQN q hq)) ?_ ?_
    ·
      intro d hd q hq
      have hqY : q ∈ Y := hTY (hQT hq)
      have hqN := CFSG.LocalAnalysis.GLTheoremA.lstar_normalizer_centralizer (p := p) (hQN q hq)
      have hqd := (Subgroup.mem_normalizer_iff.1 hqN d).1 hd
      have hz : d⁻¹ * (q * d * q⁻¹) ∈ GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) :=
        (GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X))).mul_mem
          ((GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X))).inv_mem hd) hqd
      have h1 : d⁻¹ * q * d⁻¹⁻¹ ∈ Y := hYn.conj_mem q hqY d⁻¹
      have hzY : d⁻¹ * (q * d * q⁻¹) ∈ Y := by
        have e : d⁻¹ * (q * d * q⁻¹) = (d⁻¹ * q * d⁻¹⁻¹) * q⁻¹ := by group
        rw [e]
        exact Y.mul_mem h1 (Y.inv_mem hqY)
      have hmem := pPrime_mem_layer_of_mem_sup hzY
        (Lemma114Layer.not_dvd_orderOf_of_mem_glaPPrimeCoreOf hz)
      have hEJ : Lemma114Layer.layerOf X ≤ layerJoin p X := le_sup_left
      exact hEJ hmem
    ·
      intro x hx hxQ
      have hxC : x ∈ Subgroup.centralizer (B : Set X) :=
        CFSG.LocalAnalysis.GLTheoremA.lstar_glaPPrimeCoreOf_le p _ hx
      have hxR : R ≤ Subgroup.centralizer ({x} : Set X) := by
        refine sup_le (fun q hq => Subgroup.mem_centralizer_singleton_iff.2 ?_)
          (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 ?_)
        · exact hxQ q hq
        · exact Subgroup.mem_centralizer_iff.1 hxC b hb
      have hxA : x ∈ Subgroup.centralizer (R : Set X) :=
        Subgroup.mem_centralizer_iff.2 fun r hr => Subgroup.mem_centralizer_singleton_iff.1 (hxR hr)
      have hAB : Subgroup.centralizer (R : Set X) ≤ Subgroup.centralizer (B : Set X) :=
        Subgroup.centralizer_le (fun b hb => Subgroup.mem_sup_right hb)
      have hNA : ∀ g ∈ Subgroup.centralizer (R : Set X),
          ∀ n ∈ GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓ Subgroup.centralizer (R : Set X),
            g * n * g⁻¹ ∈
              GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓ Subgroup.centralizer (R : Set X) := by
        intro g hg n hn
        obtain ⟨hnD, hnA⟩ := Subgroup.mem_inf.1 hn
        refine Subgroup.mem_inf.2 ⟨?_, conj_mem_centralizer hg hnA⟩
        have hgN := CFSG.LocalAnalysis.GLTheoremA.lstar_normalizer_centralizer (p := p)
          (Subgroup.centralizer_le_normalizer _ (hAB hg))
        exact (Subgroup.mem_normalizer_iff.1 hgN n).1 hnD
      have hANorm : Subgroup.centralizer (R : Set X) ≤ Subgroup.normalizer
          ((GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓ Subgroup.centralizer (R : Set X) :
            Subgroup X) : Set X) :=
        Lemma114Layer.le_normalizer_of_conj fun g hg n hn => hNA g hg n hn
      have hsub : IsSubnormal
          (GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓ Subgroup.centralizer (R : Set X))
          (Subgroup.centralizer (R : Set X)) :=
        IsSubnormal.step inf_le_right
          ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 hANorm) (IsSubnormal.refl _)
      have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓
          Subgroup.centralizer (R : Set X))) :=
        Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
          (Lemma114Layer.coprime_card_glaPPrimeCoreOf _)
      have hN'D := CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18.le_glaPPrimeCoreOf_of_coprime
        hp.out hsub hcop
      exact hIH (hN'D (Subgroup.mem_inf.2 ⟨hx, hxA⟩))

end Reduction

theorem input18_5_of_pPrimeStar (hS : PPrimeStar) : Lemma114Full.Input18_5 := by
  intro X _ _ hK p hp hp2 hO Q hQ
  haveI : Fact p.Prime := ⟨hp⟩
  exact centralizer_le_layerJoin_of_star hS hp2 hK hO _ Q hQ rfl

section KCore

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem eq_bot_of_normal_coprime {p : ℕ} (hO : GLAPPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : N.Normal) (hc : Nat.Coprime p (Nat.card ↥N)) : N = ⊥ := by
  have h : N ≤ CFSG.pPrimeCore p X := le_sSup ⟨hN, hc⟩
  have hO' : CFSG.pPrimeCore p X = ⊥ := hO
  rw [hO'] at h
  exact eq_bot_iff.2 h

theorem coprime_card_sup_of_commute {p : ℕ} [hp : Fact p.Prime] {A B : Subgroup X}
    (hA : Nat.Coprime p (Nat.card ↥A)) (hB : Nat.Coprime p (Nat.card ↥B))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Nat.Coprime p (Nat.card ↥(A ⊔ B)) := by
  let f : A × B →* X := MonoidHom.mk' (fun x => (x.1 : X) * (x.2 : X)) (by
    intro x y
    show ((x * y).1 : X) * ((x * y).2 : X) = ((x.1 : X) * (x.2 : X)) * ((y.1 : X) * (y.2 : X))
    calc ((x * y).1 : X) * ((x * y).2 : X) = (x.1 : X) * ((y.1 : X) * (x.2 : X)) * (y.2 : X) := by
          simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]; group
      _ = (x.1 : X) * ((x.2 : X) * (y.1 : X)) * (y.2 : X) := by rw [hAB _ y.1.2 _ x.2.2]
      _ = ((x.1 : X) * (x.2 : X)) * ((y.1 : X) * (y.2 : X)) := by group)
  have hsup : A ⊔ B ≤ f.range := by
    refine sup_le (fun a ha => MonoidHom.mem_range.2 ⟨(⟨a, ha⟩, 1), ?_⟩)
      (fun b hb => MonoidHom.mem_range.2 ⟨(1, ⟨b, hb⟩), ?_⟩)
    · simp [f]
    · simp [f]
  have h1 : Nat.card ↥(A ⊔ B) ∣ Nat.card ↥f.range := Subgroup.card_dvd_of_le hsup
  have h2 : Nat.card ↥f.range ∣ Nat.card (↥A × ↥B) := Subgroup.card_range_dvd f
  rw [Nat.card_prod] at h2
  exact Nat.Coprime.coprime_dvd_right (h1.trans h2) (Nat.Coprime.mul_right hA hB)

theorem coprime_card_finset_sup {p : ℕ} [hp : Fact p.Prime] (s : Finset (Subgroup X)) :
    (∀ A ∈ s, Nat.Coprime p (Nat.card ↥A)) →
    (∀ A ∈ s, ∀ B ∈ s, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
    Nat.Coprime p (Nat.card ↥(s.sup id)) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert A s hAs ih =>
    intro hs hc
    rw [Finset.sup_insert]
    show Nat.Coprime p (Nat.card ↥(A ⊔ s.sup id))
    have hs' : ∀ B ∈ s, Nat.Coprime p (Nat.card ↥B) :=
      fun B hB => hs B (Finset.mem_insert_of_mem hB)
    have hc' : ∀ B ∈ s, ∀ C ∈ s, B ≠ C → ∀ a ∈ B, ∀ b ∈ C, a * b = b * a :=
      fun B hB C hC hne => hc B (Finset.mem_insert_of_mem hB) C (Finset.mem_insert_of_mem hC) hne
    have hsub : s.sup id ≤ Subgroup.centralizer (A : Set X) := by
      refine Finset.sup_le fun B hB => ?_
      show B ≤ Subgroup.centralizer (A : Set X)
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hne : B ≠ A := fun h => hAs (h ▸ hB)
      exact (hc B (Finset.mem_insert_of_mem hB) A (Finset.mem_insert_self _ _) hne b hb a ha).symm
    have hAB : ∀ a ∈ A, ∀ b ∈ s.sup id, a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.1 (hsub hb)) a ha
    exact coprime_card_sup_of_commute (hs A (Finset.mem_insert_self _ _)) (ih hs' hc') hAB

noncomputable def conjFamily (A : Subgroup X) : Finset (Subgroup X) :=
  (Set.finite_range fun x : X => A.map (MulAut.conj x).toMonoidHom).toFinset

theorem mem_conjFamily (A B : Subgroup X) :
    B ∈ conjFamily A ↔ ∃ x : X, A.map (MulAut.conj x).toMonoidHom = B := by
  unfold conjFamily
  rw [Set.Finite.mem_toFinset, Set.mem_range]

theorem conjSup_normal (A : Subgroup X) : ((conjFamily A).sup id).Normal := by
  constructor
  intro n hn g
  have key : ∀ B ∈ conjFamily A, B ≤ ((conjFamily A).sup id).comap (MulAut.conj g).toMonoidHom := by
    intro B hB
    obtain ⟨x, rfl⟩ := (mem_conjFamily A _).1 hB
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
    have hmem : (MulAut.conj g).toMonoidHom ((MulAut.conj x).toMonoidHom a) ∈
        A.map (MulAut.conj (g * x)).toMonoidHom :=
      Subgroup.mem_map.2 ⟨a, ha, by simp [MulAut.conj_apply, mul_assoc]⟩
    show (MulAut.conj g).toMonoidHom ((MulAut.conj x).toMonoidHom a) ∈ (conjFamily A).sup id
    exact Finset.le_sup (f := id) ((mem_conjFamily A _).2 ⟨g * x, rfl⟩) hmem
  have hle : (conjFamily A).sup id ≤ ((conjFamily A).sup id).comap (MulAut.conj g).toMonoidHom :=
    Finset.sup_le key
  exact hle hn

theorem conjSup_eq_bot {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) (A : Subgroup X)
    (hA : Nat.Coprime p (Nat.card ↥A))
    (hc : ∀ x y : X, A.map (MulAut.conj x).toMonoidHom ≠ A.map (MulAut.conj y).toMonoidHom →
      ∀ a ∈ A.map (MulAut.conj x).toMonoidHom, ∀ b ∈ A.map (MulAut.conj y).toMonoidHom,
        a * b = b * a) :
    (conjFamily A).sup id = ⊥ := by
  apply eq_bot_of_normal_coprime hO (conjSup_normal A)
  apply coprime_card_finset_sup
  · intro B hB
    obtain ⟨x, rfl⟩ := (mem_conjFamily A _).1 hB
    have hinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
    rw [Nat.card_congr (Subgroup.equivMapOfInjective A _ hinj).symm.toEquiv]
    exact hA
  · intro B hB C hC hne a ha b hb
    obtain ⟨x, rfl⟩ := (mem_conjFamily A _).1 hB
    obtain ⟨y, rfl⟩ := (mem_conjFamily A _).1 hC
    exact hc x y hne a ha b hb

theorem component_card_dvd {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥)
    {L : Subgroup X} (hL : IsComponentOf L ⊤) : p ∣ Nat.card ↥L := by
  by_contra hnd
  have hA : Nat.Coprime p (Nat.card ↥L) := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hnd
  have hbot := conjSup_eq_bot hO L hA (fun x y hne a ha b hb =>
    Lemma114Layer.comm_of_components (Lemma114Layer.isComponent_conj_top hL x)
      (Lemma114Layer.isComponent_conj_top hL y) hne ha hb)
  have hLle : L ≤ (conjFamily L).sup id := by
    intro l hl
    have hmem : l ∈ L.map (MulAut.conj (1 : X)).toMonoidHom :=
      Subgroup.mem_map.2 ⟨l, hl, by simp [MulAut.conj_apply]⟩
    exact Finset.le_sup (f := id) ((mem_conjFamily L _).2 ⟨1, rfl⟩) hmem
  rw [hbot] at hLle
  have hnt : Nontrivial ↥L := by
    haveI := (hL.2.2).2
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  exact ((Subgroup.nontrivial_iff_ne_bot L).1 hnt) (le_bot_iff.1 hLle)

theorem fusion_inf_of_subnormal {p : ℕ} [hp : Fact p.Prime] {K H : Subgroup X}
    (h : CFSG.Open.IsSubnormal H K) :
    ∀ T : Subgroup X, CFSG.Open.fusionIsSylowIn p T K → CFSG.Open.fusionIsSylowIn p (T ⊓ H) H := by
  induction h with
  | refl H' =>
    intro T hT
    rw [inf_eq_left.2 hT.1]
    exact hT
  | step hHM hn hMK ih =>
    intro T hT
    have h1 := ih T hT
    have h2 := CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18.fusion_inf_normal h1 hHM hn
    rw [inf_assoc, inf_eq_right.2 hHM] at h2
    exact h2

theorem not_dvd_card_of_central_sylow {p : ℕ} [hp : Fact p.Prime] {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {P : Subgroup K} (hPs : CFSG.Open.fusionIsSylowIn p P ⊤)
    (hPc : P ≤ Subgroup.center K) : ¬ p ∣ Nat.card K := by
  let Syl' : Sylow p K := ⟨P, hPs.2.1, fun {Q} hQ hle => hPs.2.2 Q le_top hQ hle⟩
  have hP : Subgroup.normalizer (Syl' : Set K) ≤ Subgroup.centralizer ((Syl' : Subgroup K) : Set K) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_center_iff.1 (hPc hh) g).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' Syl' hP
  have hnd := MonoidHom.not_dvd_card_ker_transferSylow Syl' hP
  set N := (MonoidHom.transferSylow Syl' hP).ker with hNdef
  have hdec : ∀ g : K, ∃ n ∈ N, ∃ s ∈ P, n * s = g := by
    intro g
    obtain ⟨⟨⟨n, hn⟩, ⟨s, hs⟩⟩, hns⟩ := (hcomp.existsUnique g).exists
    exact ⟨n, hn, s, hs, hns⟩
  have hcomm : ∀ g h : K, ⁅g, h⁆ ∈ N := by
    intro g h
    obtain ⟨n1, hn1, s1, hs1, rfl⟩ := hdec g
    obtain ⟨n2, hn2, s2, hs2, rfl⟩ := hdec h
    have hc1 : ∀ x : K, x * s1 = s1 * x := fun x => (Subgroup.mem_center_iff.1 (hPc hs1) x)
    have hc2 : ∀ x : K, x * s2 = s2 * x := fun x => (Subgroup.mem_center_iff.1 (hPc hs2) x)
    have e1 : (n1 * s1) * (n2 * s2) = (n1 * n2) * (s1 * s2) := by
      calc (n1 * s1) * (n2 * s2) = n1 * (s1 * n2) * s2 := by group
        _ = n1 * (n2 * s1) * s2 := by rw [← hc1 n2]
        _ = (n1 * n2) * (s1 * s2) := by group
    have e2 : (n2 * s2) * (n1 * s1) = (n2 * n1) * (s2 * s1) := by
      calc (n2 * s2) * (n1 * s1) = n2 * (s2 * n1) * s1 := by group
        _ = n2 * (n1 * s2) * s1 := by rw [← hc2 n1]
        _ = (n2 * n1) * (s2 * s1) := by group
    have e3 : s1 * s2 = s2 * s1 := (hc1 s2).symm
    have hcomm' : ⁅n1 * s1, n2 * s2⁆ = ⁅n1, n2⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc (n1 * s1) * (n2 * s2) * (n1 * s1)⁻¹ * (n2 * s2)⁻¹
          = ((n1 * s1) * (n2 * s2)) * ((n2 * s2) * (n1 * s1))⁻¹ := by group
        _ = ((n1 * n2) * (s1 * s2)) * ((n2 * n1) * (s2 * s1))⁻¹ := by rw [e1, e2]
        _ = ((n1 * n2) * (s1 * s2)) * (s2 * s1)⁻¹ * (n2 * n1)⁻¹ := by group
        _ = (n1 * n2) * (n2 * n1)⁻¹ := by rw [e3]; group
        _ = n1 * n2 * n1⁻¹ * n2⁻¹ := by group
    rw [hcomm', commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn1 hn2) (N.inv_mem hn1)) (N.inv_mem hn2)
  have htop : (⊤ : Subgroup K) ≤ N := by
    have hle : commutator K ≤ N := (Subgroup.commutator_le).2 fun g _ h _ => hcomm g h
    rw [hperf] at hle
    exact hle
  have hNtop : N = ⊤ := eq_top_iff.2 htop
  rw [hNtop, Subgroup.card_top] at hnd
  exact hnd

theorem fusion_subgroupOf {p : ℕ} [hp : Fact p.Prime] {L S : Subgroup X}
    (hLS : CFSG.Open.fusionIsSylowIn p (S ⊓ L) L) :
    CFSG.Open.fusionIsSylowIn p ((S ⊓ L).subgroupOf L) ⊤ := by
  refine ⟨le_top, Lemma114Layer.isPGroup_subgroupOf_of_le hLS.2.1 inf_le_right, ?_⟩
  intro P' _ hP' hle
  have hP'' : IsPGroup p ↥(P'.map L.subtype) :=
    hP'.of_equiv (Subgroup.equivMapOfInjective P' L.subtype L.subtype_injective)
  have hlt : P'.map L.subtype ≤ L := Subgroup.map_subtype_le P'
  have hle'' : S ⊓ L ≤ P'.map L.subtype := by
    intro x hx
    exact Subgroup.mem_map.2 ⟨⟨x, (Subgroup.mem_inf.1 hx).2⟩,
      hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have heq := hLS.2.2 (P'.map L.subtype) hlt hP'' hle''
  have hPeq : (P'.map L.subtype).subgroupOf L = P' := by
    ext x
    rw [Subgroup.mem_subgroupOf, ← Subgroup.mem_map_iff_mem L.subtype_injective]
    rfl
  calc P' = (P'.map L.subtype).subgroupOf L := hPeq.symm
    _ = (S ⊓ L).subgroupOf L := by rw [heq]

end KCore

section Derivation

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

abbrev Yset (p : ℕ) (X : Type) [Group X] : Subgroup X :=
  Lemma114Layer.layerOf X ⊔ CFSG.pCore p X

theorem fittingSubgroup_le_pCore {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) :
    CFSG.fittingSubgroup X ≤ CFSG.pCore p X := by
  rw [CFSG.fitting_eq_sup_pCore]
  refine iSup_le fun q => ?_
  by_cases hq : q.1.1 = p
  · exact (congrArg (fun r => CFSG.pCore r X) hq).le
  · have hqp : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    haveI : Fact q.1.1.Prime := ⟨hqp⟩
    have hcop : Nat.Coprime p (Nat.card ↥(CFSG.pCore q.1.1 X)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := q.1.1) (G := X))
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp.out hqp).2 (fun h => hq h.symm))
    rw [eq_bot_of_normal_coprime hO (CFSG.pCore_normal (p := q.1.1) (G := X)) hcop]
    exact bot_le

theorem genFittingFStar_le_Yset {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) :
    CFSG.Open.genFittingFStar X ≤ Yset p X := by
  rw [CFSG.Open.genFittingFStar.eq_sup]
  refine sup_le ?_ le_sup_left
  exact (fittingSubgroup_le_pCore hO).trans le_sup_right

theorem centralizer_Yset_le_fstar {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) :
    Subgroup.centralizer ((Yset p X : Subgroup X) : Set X) ≤ CFSG.Open.genFittingFStar X :=
  (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (genFittingFStar_le_Yset hO))).trans
    (CFSG.Adapters.generalized_fitting_self_centralizing X)

theorem centralizer_Yset_le_Yset {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) :
    Subgroup.centralizer ((Yset p X : Subgroup X) : Set X) ≤ Yset p X :=
  (centralizer_Yset_le_fstar hO).trans (genFittingFStar_le_Yset hO)

theorem centralizer_Yset_normal {p : ℕ} [hp : Fact p.Prime] :
    (Subgroup.centralizer ((Yset p X : Subgroup X) : Set X)).Normal := by
  haveI : (Lemma114Layer.layerOf X).Normal := Lemma114Layer.layerOf_normal
  haveI : (CFSG.pCore p X).Normal := CFSG.pCore_normal (p := p) (G := X)
  have hYn : (Yset p X).Normal := Subgroup.sup_normal _ _
  constructor
  intro n hn g
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro y hy
  have hw := hn (g⁻¹ * y * g⁻¹⁻¹) (hYn.conj_mem y hy g⁻¹)
  calc y * (g * n * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [hw]
    _ = g * n * g⁻¹ * y := by group

theorem centralizer_Yset_pow_eq_one {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥)
    {z : X} (hz : z ∈ Subgroup.centralizer ((Yset p X : Subgroup X) : Set X)) :
    ∃ k : ℕ, z ^ p ^ k = 1 := by
  haveI : (Lemma114Layer.layerOf X).Normal := Lemma114Layer.layerOf_normal
  haveI : (CFSG.pCore p X).Normal := CFSG.pCore_normal (p := p) (G := X)
  let A : Subgroup X :=
    { carrier := {w | w ∈ Subgroup.centralizer ((Yset p X : Subgroup X) : Set X) ∧
        ∃ m : ℕ, ¬ p ∣ m ∧ w ^ m = 1}
      mul_mem' := by
        rintro a b ⟨ha, m, hm, ham⟩ ⟨hb, n, hn, hbn⟩
        have hbY : b ∈ Yset p X := centralizer_Yset_le_Yset hO hb
        have hab : a * b = b * a := (Subgroup.mem_centralizer_iff.1 ha b hbY).symm
        refine ⟨Subgroup.mul_mem _ ha hb, m * n, fun h => ?_, ?_⟩
        · rcases (Nat.Prime.dvd_mul hp.out).1 h with h' | h'
          · exact hm h'
          · exact hn h'
        · have h1 : a ^ (m * n) = 1 := by rw [pow_mul, ham, one_pow]
          have h2 : b ^ (m * n) = 1 := by rw [mul_comm, pow_mul, hbn, one_pow]
          rw [Commute.mul_pow (show Commute a b from hab) (m * n), h1, h2, one_mul]
      one_mem' := ⟨Subgroup.one_mem _, 1, Nat.Prime.not_dvd_one hp.out, one_pow 1⟩
      inv_mem' := by
        rintro a ⟨ha, m, hm, ham⟩
        exact ⟨Subgroup.inv_mem _ ha, m, hm, by rw [inv_pow, ham, inv_one]⟩ }
  have hAn : A.Normal := by
    constructor
    rintro n ⟨hn, m, hm, hnm⟩ g
    refine ⟨(centralizer_Yset_normal (p := p)).conj_mem n hn g, m, hm, ?_⟩
    rw [conj_pow, hnm, mul_one, mul_inv_cancel]
  have hcop : Nat.Coprime p (Nat.card ↥A) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨-, m, hm, hgm⟩ := g.2
    have h1 : orderOf (g : X) ∣ m := orderOf_dvd_of_pow_eq_one hgm
    rw [Subgroup.orderOf_coe, hg] at h1
    exact hm h1
  have hAbot : A = ⊥ := eq_bot_of_normal_coprime hO hAn hcop
  obtain ⟨e, n', hn', hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' p hp.out.ne_one
  refine ⟨e, ?_⟩
  have hwA : z ^ p ^ e ∈ A := by
    refine ⟨Subgroup.pow_mem _ hz _, n', hn', ?_⟩
    rw [← pow_mul, ← hdec, pow_orderOf_eq_one]
  have hw : z ^ p ^ e ∈ (⊥ : Subgroup X) := hAbot ▸ hwA
  exact Subgroup.mem_bot.1 hw

theorem centralizer_Yset_le_pCore {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) :
    Subgroup.centralizer ((Yset p X : Subgroup X) : Set X) ≤ CFSG.pCore p X := by
  have hpg : IsPGroup p ↥(Subgroup.centralizer ((Yset p X : Subgroup X) : Set X)) := by
    intro z
    obtain ⟨k, hk⟩ := centralizer_Yset_pow_eq_one hO z.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  exact le_sSup ⟨centralizer_Yset_normal, hpg⟩

theorem pCore_le_of_fusionSylow {p : ℕ} [hp : Fact p.Prime] {S : Subgroup X}
    (hS : CFSG.Open.fusionIsSylowIn p S ⊤) : CFSG.pCore p X ≤ S := by
  haveI : (CFSG.pCore p X).Normal := CFSG.pCore_normal (p := p) (G := X)
  let Syl : Sylow p X := ⟨S, hS.2.1, fun {Q} hQ hle => hS.2.2 Q le_top hQ hle⟩
  exact IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := p) (G := X)) Syl

theorem component_le_layerOf {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    K ≤ Lemma114Layer.layerOf X :=
  le_sSup hK

theorem normalizer_of_centralizer_Q0 {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥)
    {S : Subgroup X} (hS : CFSG.Open.fusionIsSylowIn p S ⊤) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) {d : X}
    (hd : d ∈ Subgroup.centralizer ((S ⊓ Lemma114Layer.layerOf X : Subgroup X) : Set X)) :
    d ∈ Subgroup.normalizer (K : Set X) := by
  have hK' := Lemma114Layer.isComponent_conj_top hK d
  by_cases hEq : K.map (MulAut.conj d).toMonoidHom = K
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : d * h * d⁻¹ ∈ K.map (MulAut.conj d).toMonoidHom :=
        Subgroup.mem_map.2 ⟨h, hh, by simp [MulAut.conj_apply]⟩
      rw [hEq] at h1
      exact h1
    · intro hh
      have h3 : d * h * d⁻¹ ∈ K.map (MulAut.conj d).toMonoidHom := by rw [hEq]; exact hh
      obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.1 h3
      have hkh : k = h := by
        have : d * k * d⁻¹ = d * h * d⁻¹ := by simpa [MulAut.conj_apply] using hkeq
        exact mul_left_cancel (mul_right_cancel this)
      rw [← hkh]
      exact hk
  · exfalso
    have hPK : CFSG.Open.fusionIsSylowIn p (S ⊓ K) K :=
      fusion_inf_of_subnormal (K := ⊤) hK.2.1 S hS
    have hPK' : CFSG.Open.fusionIsSylowIn p ((S ⊓ K).subgroupOf K) ⊤ := fusion_subgroupOf hPK
    have hc : (S ⊓ K).subgroupOf K ≤ Subgroup.center ↥K := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      have hxK : x.1 ∈ S ⊓ K := (Subgroup.mem_subgroupOf).1 hx
      have hxd : x.1 * d = d * x.1 :=
        Subgroup.mem_centralizer_iff.1 hd x.1 (Subgroup.mem_inf.2
          ⟨(Subgroup.mem_inf.1 hxK).1, component_le_layerOf hK (Subgroup.mem_inf.1 hxK).2⟩)
      have hxK' : x.1 ∈ K.map (MulAut.conj d).toMonoidHom :=
        Subgroup.mem_map.2 ⟨x.1, x.2, by
          show d * x.1 * d⁻¹ = x.1
          rw [← hxd, mul_inv_cancel_right]⟩
      have hcomm := Lemma114Layer.comm_of_components hK' hK hEq hxK' g.2
      exact Subtype.ext (by simpa using hcomm.symm)
    have hperf : commutator (↥K) = ⊤ := hK.2.2.1
    exact not_dvd_card_of_central_sylow hperf hPK' hc (component_card_dvd hO hK)

end Derivation

theorem pow_mem_pPrimeCore_of_hasNormalPComplement {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (h : CFSG.HasNormalPComplement p G) (x : G) :
    ∃ k : ℕ, x ^ p ^ k ∈ CFSG.pPrimeCore p G := by
  unfold CFSG.HasNormalPComplement at h
  obtain ⟨N, hN, hcop, hquot⟩ := h
  have hNle : N ≤ CFSG.pPrimeCore p G := le_sSup ⟨hN, hcop⟩
  obtain ⟨k, hk⟩ := hquot (QuotientGroup.mk (s := N) x)
  refine ⟨k, hNle ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
  exact hk

theorem exists_complement_of_central_sylow {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p G) (hc : ∀ x ∈ (P : Subgroup G), ∀ g : G, x * g = g * x) :
    ∃ C : Subgroup G, ¬ p ∣ Nat.card C ∧ ∀ g : G, ¬ p ∣ orderOf g → g ∈ C := by
  have hP : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hc x hx g
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hP
  refine ⟨(MonoidHom.transferSylow P hP).ker, MonoidHom.not_dvd_card_ker_transferSylow P hP, ?_⟩
  intro g hgp
  obtain ⟨⟨⟨c, hc'⟩, ⟨s, hs⟩⟩, hcs⟩ := (hcomp.existsUnique g).exists
  have hcs' : c * s = g := hcs
  have hcom : Commute c s := (hc s hs c).symm
  have hpow : c ^ orderOf g * s ^ orderOf g = 1 := by
    rw [← hcom.mul_pow, hcs']
    exact pow_orderOf_eq_one g
  have hs1 : s ^ orderOf g = 1 := by
    have hu := (hcomp.existsUnique 1).unique
      (y₁ := ⟨⟨c ^ orderOf g, pow_mem hc' _⟩, ⟨s ^ orderOf g, pow_mem hs _⟩⟩)
      (y₂ := ⟨⟨1, one_mem _⟩, ⟨1, one_mem _⟩⟩) (by simpa using hpow) (by simp)
    have := congrArg (fun q => (q.2 : G)) hu
    simpa using this
  obtain ⟨j, hj⟩ := P.isPGroup' ⟨s, hs⟩
  have hsj : s ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hd1 : orderOf s ∣ orderOf g := orderOf_dvd_of_pow_eq_one hs1
  have hd2 : orderOf s ∣ p ^ j := orderOf_dvd_of_pow_eq_one hsj
  obtain ⟨i, _, hi'⟩ := (Nat.dvd_prime_pow hp.out).1 hd2
  have hs_one : orderOf s = 1 := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [hi', h0, pow_zero]
    · have hpd : p ∣ orderOf s := hi'.symm ▸ dvd_pow_self p hpos.ne'
      exact absurd (hpd.trans hd1) hgp
  have hs_eq : s = 1 := orderOf_eq_one_iff.1 hs_one
  rw [← hcs', hs_eq, mul_one]
  exact hc'

section Subgroups

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

abbrev sylInter (S K : Subgroup X) : Subgroup K := (S ⊓ K).subgroupOf K

abbrev fixK (S K : Subgroup X) : Subgroup (MulAut K) := fixerAut (sylInter S K)

def NK (p : ℕ) (S K : Subgroup X) : Subgroup (MulAut K) :=
  (CFSG.pPrimeCore p ↥(fixK S K)).map (fixK S K).subtype

abbrev Dset (S : Subgroup X) : Subgroup X :=
  Subgroup.centralizer ((S ⊓ Lemma114Layer.layerOf X : Subgroup X) : Set X)

abbrev Tset (p : ℕ) (S : Subgroup X) : Subgroup X :=
  (S ⊓ Lemma114Layer.layerOf X) ⊔ CFSG.pCore p X

abbrev H2set (p : ℕ) (S : Subgroup X) : Subgroup X :=
  Subgroup.centralizer ((Tset p S : Subgroup X) : Set X)

abbrev K0set (p : ℕ) (S : Subgroup X) : Subgroup X :=
  H2set p S ⊓ Subgroup.centralizer ((Lemma114Layer.layerOf X : Subgroup X) : Set X)

def MK (p : ℕ) (S K : Subgroup X) : Subgroup X :=
  ((NK p S K).comap (Subgroup.normalizerMonoidHom K)).map (Subgroup.normalizer (K : Set X)).subtype

def Mset (p : ℕ) (S : Subgroup X) : Subgroup X :=
  H2set p S ⊓ ⨅ (K : Subgroup X) (_ : IsComponentOf K ⊤), MK p S K

theorem exists_pow_mem_pPrimeCore_fixK (h : Input7_10_1) {p : ℕ} [hp : Fact p.Prime]
    (hX : CFSG.Open.IsKGroup X) {S K : Subgroup X} (hS : CFSG.Open.fusionIsSylowIn p S ⊤)
    (hK : IsComponentOf K ⊤) (f : ↥(fixK S K)) :
    ∃ k : ℕ, f ^ p ^ k ∈ CFSG.pPrimeCore p ↥(fixK S K) := by
  have hsyl : CFSG.Open.fusionIsSylowIn p (sylInter S K) ⊤ :=
    fusion_subgroupOf (fusion_inf_of_subnormal (K := ⊤) hK.2.1 S hS)
  have hkg : CFSG.Open.IsKGroup ↥K :=
    CFSG.KCore.KGroupNonab.subgroup Lemma114Full.isoInvariant_isCatalogGroup_of hX K
  exact pow_mem_pPrimeCore_of_hasNormalPComplement (h p hp.out ↥K hK.2.2 hkg (sylInter S K) hsyl) f

theorem normalizerMonoidHom_coe_apply {K : Subgroup X} {h : X}
    (hh : h ∈ Subgroup.normalizer (K : Set X)) (y : K) :
    ((Subgroup.normalizerMonoidHom K ⟨h, hh⟩ y : K) : X) = h * y * h⁻¹ := by
  rfl

theorem NK_normal_of_fixK {p : ℕ} [hp : Fact p.Prime] {S K : Subgroup X} {g : MulAut K}
    (hg : g ∈ fixK S K) {n : MulAut K} (hn : n ∈ NK p S K) : g * n * g⁻¹ ∈ NK p S K := by
  obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.1 hn
  have hN : (CFSG.pPrimeCore p ↥(fixK S K)).Normal :=
    CFSG.pPrimeCore_normal (p := p) (G := ↥(fixK S K))
  have hmem := hN.conj_mem n' hn' ⟨g, hg⟩
  exact Subgroup.mem_map.2 ⟨_, hmem, by simp⟩

theorem eq_one_of_mem_NK_pow {p : ℕ} [hp : Fact p.Prime] {S K : Subgroup X} {a : MulAut K}
    (ha : a ∈ NK p S K) {k : ℕ} (hk : a ^ p ^ k = 1) : a = 1 := by
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
  have hbk0 : b ^ p ^ k = 1 := by
    apply Subtype.ext
    simpa using hk
  have hcop : Nat.Coprime p (Nat.card ↥(CFSG.pPrimeCore p ↥(fixK S K))) :=
    CFSG.pPrimeCore_coprime_card (p := p) (G := ↥(fixK S K))
  have h1 : orderOf (⟨b, hb⟩ : ↥(CFSG.pPrimeCore p ↥(fixK S K))) ∣
      Nat.card ↥(CFSG.pPrimeCore p ↥(fixK S K)) := orderOf_dvd_natCard _
  have h2 : Nat.Coprime (orderOf (⟨b, hb⟩ : ↥(CFSG.pPrimeCore p ↥(fixK S K)))) p :=
    (Nat.Coprime.coprime_dvd_right h1 hcop).symm
  have hbk : (⟨b, hb⟩ : ↥(CFSG.pPrimeCore p ↥(fixK S K))) ^ p ^ k = 1 :=
    Subtype.ext (by simpa using hbk0)
  have h3 := orderOf_dvd_of_pow_eq_one hbk
  have h4 : orderOf (⟨b, hb⟩ : ↥(CFSG.pPrimeCore p ↥(fixK S K))) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k h2) h3
  have h5 := orderOf_eq_one_iff.1 h4
  have h6 : b = 1 := congrArg Subtype.val h5
  rw [h6, map_one]

theorem mem_MK_iff {p : ℕ} {S K : Subgroup X} {x : X} :
    x ∈ MK p S K ↔ ∃ hx : x ∈ Subgroup.normalizer (K : Set X),
      Subgroup.normalizerMonoidHom K ⟨x, hx⟩ ∈ NK p S K := by
  unfold MK
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hx, hφ⟩
    exact ⟨⟨x, hx⟩, hφ, rfl⟩

theorem mem_Mset_iff {p : ℕ} {S : Subgroup X} {x : X} :
    x ∈ Mset p S ↔ x ∈ H2set p S ∧ ∀ K : Subgroup X, IsComponentOf K ⊤ → x ∈ MK p S K := by
  unfold Mset
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]

theorem H2set_le_Dset {p : ℕ} (S : Subgroup X) : H2set p S ≤ Dset S :=
  Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left)

theorem normalizerMonoidHom_mem_fixK {S K : Subgroup X} (hK : IsComponentOf K ⊤) {g : X}
    (hg : g ∈ Dset S) (hgN : g ∈ Subgroup.normalizer (K : Set X)) :
    Subgroup.normalizerMonoidHom K ⟨g, hgN⟩ ∈ fixK S K := by
  refine mem_fixerAut.2 ?_
  intro y hy
  apply Subtype.ext
  rw [normalizerMonoidHom_coe_apply]
  have hyS : (y : X) ∈ S ⊓ Lemma114Layer.layerOf X :=
    inf_le_inf_left S (component_le_layerOf hK) (Subgroup.mem_subgroupOf.1 hy)
  have hcomm : (y : X) * g = g * (y : X) := Subgroup.mem_centralizer_iff.1 hg (y : X) hyS
  rw [← hcomm, mul_inv_cancel_right]

theorem sup_conj_mem {p : ℕ} [hp : Fact p.Prime] {S : Subgroup X} {d : X} (hd : d ∈ Dset S)
    {t : X} (ht : t ∈ Tset p S) : d * t * d⁻¹ ∈ Tset p S := by
  have hPn : (CFSG.pCore p X).Normal := CFSG.pCore_normal (p := p) (G := X)
  have hle : Tset p S ≤ (Tset p S).comap (MulAut.conj d).toMonoidHom := by
    refine sup_le (fun q hq => ?_) (fun w hw => ?_)
    · show (MulAut.conj d).toMonoidHom q ∈ Tset p S
      have hqd : q * d = d * q := Subgroup.mem_centralizer_iff.1 hd q hq
      have e : d * q * d⁻¹ = q := by rw [← hqd, mul_inv_cancel_right]
      show d * q * d⁻¹ ∈ Tset p S
      rw [e]
      exact Subgroup.mem_sup_left hq
    · show (MulAut.conj d).toMonoidHom w ∈ Tset p S
      exact Subgroup.mem_sup_right (hPn.conj_mem w hw d)
  exact hle ht

theorem H2_conj_mem {p : ℕ} [hp : Fact p.Prime] {S : Subgroup X} {d h : X} (hd : d ∈ Dset S)
    (hh : h ∈ H2set p S) : d * h * d⁻¹ ∈ H2set p S := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have ht' : d⁻¹ * t * d⁻¹⁻¹ ∈ Tset p S := sup_conj_mem (Subgroup.inv_mem _ hd) ht
  have key : (d⁻¹ * t * d⁻¹⁻¹) * h = h * (d⁻¹ * t * d⁻¹⁻¹) :=
    Subgroup.mem_centralizer_iff.1 hh _ ht'
  calc t * (d * h * d⁻¹) = d * ((d⁻¹ * t * d⁻¹⁻¹) * h) * d⁻¹ := by group
    _ = d * (h * (d⁻¹ * t * d⁻¹⁻¹)) * d⁻¹ := by rw [key]
    _ = d * h * d⁻¹ * t := by group

theorem Mset_conj_mem {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥)
    {S : Subgroup X} (hS : CFSG.Open.fusionIsSylowIn p S ⊤) {d x : X} (hd : d ∈ Dset S)
    (hx : x ∈ Mset p S) : d * x * d⁻¹ ∈ Mset p S := by
  rw [mem_Mset_iff] at hx ⊢
  obtain ⟨hxH, hxK⟩ := hx
  refine ⟨H2_conj_mem hd hxH, fun K hK => ?_⟩
  obtain ⟨hxN, hφx⟩ := mem_MK_iff.1 (hxK K hK)
  have hdN := normalizer_of_centralizer_Q0 hO hS hK hd
  have hN : d * x * d⁻¹ ∈ Subgroup.normalizer (K : Set X) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hdN hxN) (Subgroup.inv_mem _ hdN)
  refine mem_MK_iff.2 ⟨hN, ?_⟩
  have hsplit : (⟨d * x * d⁻¹, hN⟩ : ↥(Subgroup.normalizer (K : Set X))) =
      ⟨d, hdN⟩ * ⟨x, hxN⟩ * ⟨d, hdN⟩⁻¹ := Subtype.ext (by simp [mul_assoc])
  rw [hsplit, map_mul, map_mul, map_inv]
  exact NK_normal_of_fixK (normalizerMonoidHom_mem_fixK hK hd hdN) hφx

theorem centralizer_Yset_ge_K0 {p : ℕ} [hp : Fact p.Prime] {S : Subgroup X} :
    K0set p S ≤ Subgroup.centralizer ((Yset p X : Subgroup X) : Set X) := by
  intro k hk
  obtain ⟨hkH, hkL⟩ := Subgroup.mem_inf.1 hk
  have hLk : Lemma114Layer.layerOf X ≤ Subgroup.centralizer ({k} : Set X) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hkL y hy)
  have hPk : CFSG.pCore p X ≤ Subgroup.centralizer ({k} : Set X) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hkH y ((le_sup_right : CFSG.pCore p X ≤ Tset p S) hy))
  have hYk : Yset p X ≤ Subgroup.centralizer ({k} : Set X) := sup_le hLk hPk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (hYk hy)

theorem mem_K0set_of_pelem {p : ℕ} [hp : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥) {S : Subgroup X}
    {u : X} (hu : u ∈ Mset p S) (hpu : ∃ k : ℕ, u ^ p ^ k = 1) : u ∈ K0set p S := by
  obtain ⟨k, hk⟩ := hpu
  rw [mem_Mset_iff] at hu
  obtain ⟨huH, huK⟩ := hu
  have hcentK : ∀ K : Subgroup X, IsComponentOf K ⊤ → K ≤ Subgroup.centralizer ({u} : Set X) := by
    intro K hK y hy
    obtain ⟨hun, hφ⟩ := mem_MK_iff.1 (huK K hK)
    have hupow : (⟨u, hun⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    have hpow : Subgroup.normalizerMonoidHom K ⟨u, hun⟩ ^ p ^ k = 1 := by
      rw [← map_pow, hupow, map_one]
    have h1 := eq_one_of_mem_NK_pow hφ hpow
    have h2 : u * y * u⁻¹ = y := by
      rw [← normalizerMonoidHom_coe_apply hun ⟨y, hy⟩, h1]
      rfl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hLle : Lemma114Layer.layerOf X ≤ Subgroup.centralizer ({u} : Set X) :=
    sSup_le fun K hK => hcentK K hK
  refine Subgroup.mem_inf.2 ⟨huH, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (hLle hy)

theorem mem_Mset_of_pprime {p : ℕ} [hp : Fact p.Prime] (h : Input7_10_1)
    (hX : CFSG.Open.IsKGroup X) (hO : GLAPPrimeCore p X = ⊥) {S : Subgroup X}
    (hS : CFSG.Open.fusionIsSylowIn p S ⊤) {g : X} (hg : g ∈ H2set p S)
    (hgp : ¬ p ∣ orderOf g) : g ∈ Mset p S := by
  rw [mem_Mset_iff]
  refine ⟨hg, fun K hK => ?_⟩
  have hgD : g ∈ Dset S := H2set_le_Dset S hg
  have hgN : g ∈ Subgroup.normalizer (K : Set X) := normalizer_of_centralizer_Q0 hO hS hK hgD
  refine mem_MK_iff.2 ⟨hgN, ?_⟩
  have hf : Subgroup.normalizerMonoidHom K ⟨g, hgN⟩ ∈ fixK S K :=
    normalizerMonoidHom_mem_fixK hK hgD hgN
  have hgpow : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ orderOf g = 1 :=
    Subtype.ext (by simp [pow_orderOf_eq_one])
  have hfk : (⟨Subgroup.normalizerMonoidHom K ⟨g, hgN⟩, hf⟩ : ↥(fixK S K)) ^ orderOf g = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hgpow, map_one]
  obtain ⟨k, hk⟩ := exists_pow_mem_pPrimeCore_fixK h hX hS hK
    (⟨Subgroup.normalizerMonoidHom K ⟨g, hgN⟩, hf⟩ : ↥(fixK S K))
  haveI : (CFSG.pPrimeCore p ↥(fixK S K)).Normal :=
    CFSG.pPrimeCore_normal (p := p) (G := ↥(fixK S K))
  have hq1 : ((⟨Subgroup.normalizerMonoidHom K ⟨g, hgN⟩, hf⟩ : ↥(fixK S K)) :
      ↥(fixK S K) ⧸ CFSG.pPrimeCore p ↥(fixK S K)) ^ p ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have hq2 : ((⟨Subgroup.normalizerMonoidHom K ⟨g, hgN⟩, hf⟩ : ↥(fixK S K)) :
      ↥(fixK S K) ⧸ CFSG.pPrimeCore p ↥(fixK S K)) ^ orderOf g = 1 := by
    rw [← QuotientGroup.mk_pow, hfk]
    rfl
  have hcop : Nat.Coprime (p ^ k) (orderOf g) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hgp)
  have hq : ((⟨Subgroup.normalizerMonoidHom K ⟨g, hgN⟩, hf⟩ : ↥(fixK S K)) :
      ↥(fixK S K) ⧸ CFSG.pPrimeCore p ↥(fixK S K)) = 1 := by
    have h3 := pow_gcd_eq_one.2 ⟨hq1, hq2⟩
    rw [show (p ^ k).gcd (orderOf g) = 1 from hcop, pow_one] at h3
    exact h3
  have hfkN : (⟨Subgroup.normalizerMonoidHom K ⟨g, hgN⟩, hf⟩ : ↥(fixK S K)) ∈
      CFSG.pPrimeCore p ↥(fixK S K) := (QuotientGroup.eq_one_iff _).1 hq
  exact Subgroup.mem_map.2 ⟨_, hfkN, rfl⟩

end Subgroups

section Final

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem exists_C_of_Mset {p : ℕ} [hp : Fact p.Prime] (h : Input7_10_1)
    (hX : CFSG.Open.IsKGroup X) (hO : GLAPPrimeCore p X = ⊥) {S : Subgroup X}
    (hS : CFSG.Open.fusionIsSylowIn p S ⊤) :
    ∃ C : Subgroup X, C ≤ Mset p S ∧ (∀ d ∈ Dset S, ∀ c ∈ C, d * c * d⁻¹ ∈ C) ∧
      Nat.Coprime p (Nat.card C) ∧ ∀ g ∈ Mset p S, ¬ p ∣ orderOf g → g ∈ C := by
  have hK0pg : ∀ z ∈ K0set p S, ∃ j : ℕ, z ^ p ^ j = 1 := fun z hz =>
    centralizer_Yset_pow_eq_one hO (centralizer_Yset_ge_K0 hz)
  let P : Subgroup ↥(Mset p S) := (K0set p S).subgroupOf (Mset p S)
  have hPpg : IsPGroup p ↥P := by
    intro x
    obtain ⟨j, hj⟩ := hK0pg x.1.1 (Subgroup.mem_subgroupOf.1 x.2)
    exact ⟨j, Subtype.ext (Subtype.ext (by simpa using hj))⟩
  have hPmax : ∀ {Q : Subgroup ↥(Mset p S)}, IsPGroup p ↥Q → P ≤ Q → Q = P := by
    intro Q hQ hle
    refine le_antisymm ?_ hle
    intro q hq
    obtain ⟨j, hj⟩ := hQ ⟨q, hq⟩
    have hqpow : (q.1 : X) ^ p ^ j = 1 := by
      have := congrArg (fun z : ↥Q => ((z : ↥(Mset p S)) : X)) hj
      simpa using this
    exact Subgroup.mem_subgroupOf.2 (mem_K0set_of_pelem hO q.2 ⟨j, hqpow⟩)
  let Syl : Sylow p ↥(Mset p S) := ⟨P, hPpg, fun {Q} hQ hle => hPmax hQ hle⟩
  have hc : ∀ x ∈ (Syl : Subgroup ↥(Mset p S)), ∀ g : ↥(Mset p S), x * g = g * x := by
    intro x hx g
    apply Subtype.ext
    have hxK0 : x.1 ∈ K0set p S := Subgroup.mem_subgroupOf.1 hx
    have hxT : x.1 ∈ Tset p S :=
      Subgroup.mem_sup_right (centralizer_Yset_le_pCore hO (centralizer_Yset_ge_K0 hxK0))
    have hgH : g.1 ∈ H2set p S := (mem_Mset_iff.1 g.2).1
    simpa using Subgroup.mem_centralizer_iff.1 hgH _ hxT
  obtain ⟨CM, hCMp, hCMc⟩ := exists_complement_of_central_sylow Syl hc
  have hiv : ∀ g ∈ Mset p S, ¬ p ∣ orderOf g → g ∈ CM.map (Mset p S).subtype := by
    intro g hg hgp
    exact Subgroup.mem_map.2 ⟨⟨g, hg⟩, hCMc ⟨g, hg⟩ (by rwa [Subgroup.orderOf_mk]), rfl⟩
  have hpart : ∀ c ∈ CM.map (Mset p S).subtype, ¬ p ∣ orderOf c := by
    intro c hc'
    obtain ⟨c0, hc0, rfl⟩ := Subgroup.mem_map.1 hc'
    intro hdvd
    apply hCMp
    have h1 : orderOf ((Mset p S).subtype c0) = orderOf (⟨c0, hc0⟩ : ↥CM) :=
      (Subgroup.orderOf_coe c0).trans (Subgroup.orderOf_coe (⟨c0, hc0⟩ : ↥CM))
    rw [h1] at hdvd
    exact hdvd.trans (orderOf_dvd_natCard _)
  have hDnorm : ∀ d ∈ Dset S, ∀ c ∈ CM.map (Mset p S).subtype,
      d * c * d⁻¹ ∈ CM.map (Mset p S).subtype := by
    intro d hd c hc'
    obtain ⟨c0, hc0, rfl⟩ := Subgroup.mem_map.1 hc'
    have hgM : d * (c0 : X) * d⁻¹ ∈ Mset p S := Mset_conj_mem hO hS hd c0.2
    apply hiv _ hgM
    have hdv : orderOf (d * (c0 : X) * d⁻¹) ∣ orderOf (c0 : X) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    intro hdvd
    exact hpart (c0 : X) (Subgroup.mem_map.2 ⟨c0, hc0, rfl⟩) (hdvd.trans hdv)
  have hle : CM.map (Mset p S).subtype ≤ Mset p S := by
    intro c hc'
    obtain ⟨c0, -, rfl⟩ := Subgroup.mem_map.1 hc'
    exact c0.2
  have hcop : Nat.Coprime p (Nat.card ↥(CM.map (Mset p S).subtype)) := by
    rw [Subgroup.card_map_of_injective (Mset p S).subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hCMp
  exact ⟨CM.map (Mset p S).subtype, hle, hDnorm, hcop, hiv⟩

theorem pPrimeStar_of_I710 (h : Input7_10_1) : PPrimeStar := by
  intro p hp _ X _ _ hX hO S hS g hg hgp
  haveI : Fact p.Prime := ⟨hp⟩
  have hTsub : (S ⊓ Lemma114Layer.layerOf X) ⊔ CFSG.pCore p X ≤
      S ⊓ (Lemma114Layer.layerOf X ⊔ CFSG.pCore p X) :=
    sup_le (inf_le_inf_left S le_sup_left) (le_inf (pCore_le_of_fusionSylow hS) le_sup_right)
  have hgH : g ∈ H2set p S := Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hTsub) hg
  have hgM : g ∈ Mset p S := mem_Mset_of_pprime h hX hO hS hgH hgp
  obtain ⟨C, hCM, hCD, hcop, hiv⟩ := exists_C_of_Mset h hX hO hS
  have hgC : g ∈ C := hiv g hgM hgp
  have hCDle : C ≤ Dset S := fun c hc => H2set_le_Dset (p := p) S (mem_Mset_iff.1 (hCM hc)).1
  have hDN : Dset S ≤ Subgroup.normalizer (C : Set X) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hCD d hd c hc
    · intro hc
      have hthis := hCD d⁻¹ (Subgroup.inv_mem _ hd) _ hc
      have e : d⁻¹ * (d * c * d⁻¹) * d⁻¹⁻¹ = c := by group
      rw [e] at hthis
      exact hthis
  exact Subgroup.mem_sup_right (Lemma114Layer.le_glaPPrimeCoreOf_of_normal' hCDle hDN hcop hgC)

theorem input18_5_of_I710 (h : Input7_10_1) : Lemma114Full.Input18_5 :=
  input18_5_of_pPrimeStar (pPrimeStar_of_I710 h)

end Final

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input185
