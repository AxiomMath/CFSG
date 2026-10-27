module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs61
public import CFSG.LocalAnalysis.GL83PartI.I_20_1
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ}

structure Prop61Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  lBalance : LBalanceAt G p
  chevInner : ChevInnerAt G p
  i71 : I71I117At G p
  i196 : I196At G p
  i194 : I194At G p

private theorem p61_card_sup_mul_card_inf [Finite G] (L R : Subgroup G)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup G) * Nat.card (L ⊓ R : Subgroup G) = Nat.card L * Nat.card R := by
  let μ : L × R →* G := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]
  exact this

private theorem p61_layer_top_eq_bot {p : ℕ} (hp : p.Prime) (C : Subgroup G)
    (h : GLAPLayer p C = ⊥) : GLAPLayer p (⊤ : Subgroup C) = ⊥ := by
  have hle : GLAPLayer p (⊤ : Subgroup C) ≤ (GLAPLayer p C).comap C.subtype := by
    unfold GLAPLayer
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup C) ⊓ C.subtype.ker)) := by
      have : (⊤ : Subgroup C) ⊓ C.subtype.ker = ⊥ := by simp
      rw [this, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    have h1 := glaPComponent_map hp C.subtype hker hJ
    have htop : (⊤ : Subgroup C).map C.subtype = C :=
      le_antisymm (by rintro _ ⟨y, -, rfl⟩; exact y.2) fun y hy => ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
    rw [htop] at h1
    exact le_sSup h1
  rw [h, MonoidHom.comap_bot, Subgroup.ker_subtype] at hle
  exact le_bot_iff.1 hle

private theorem p61_primeCoreOf_top_eq (p : ℕ) (X : Type) [Group X] :
    GLAPPrimeCoreOf p (⊤ : Subgroup X) = GLAPPrimeCore p X := by
  have h := glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := X))
  have hsub : (⊤ : Subgroup X).subtype = (Subgroup.topEquiv (G := X)).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  unfold GLAPPrimeCoreOf
  rw [hsub, h]

theorem exists_inner_noncentralizing (hp : p.Prime) {B L : Subgroup G} {x : G}
    (hB : IsElemAbelian p B) (hx1 : x ≠ 1) (hxB : x ∈ B)
    (hcent : CentModEqZpowers p B L x)
    (h1 : Nat.card B ≤ p * Nat.card ↥(B ⊓ innerModSubgroup p L))
    {E : Subgroup G} (hEB : E ≤ B) (hE : Nat.card E = p ^ 3) :
    ∃ y ∈ E, InducesInnerMod p L y ∧ ¬ CentMod p L y := by
  by_contra hno
  push Not at hno
  set C : Subgroup G := B ⊓ innerModSubgroup p L with hCdef
  have hCB : C ≤ B := inf_le_left
  have hcomm : ∀ c ∈ C, ∀ e ∈ E, c * e = e * c := fun c hc e he =>
    isElemAbelian_commute hB (hCB hc) (hEB he)
  have hcard := p61_card_sup_mul_card_inf C E hcomm
  have hsupB : Nat.card (C ⊔ E : Subgroup G) ≤ Nat.card B :=
    Subgroup.card_le_of_le (sup_le hCB hEB)
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hle1 : Nat.card E ≤ p * Nat.card (C ⊓ E : Subgroup G) := by
    have h3 : Nat.card C * Nat.card E ≤ Nat.card C * (p * Nat.card (C ⊓ E : Subgroup G)) := by
      calc Nat.card C * Nat.card E
          = Nat.card (C ⊔ E : Subgroup G) * Nat.card (C ⊓ E : Subgroup G) := hcard.symm
        _ ≤ (p * Nat.card C) * Nat.card (C ⊓ E : Subgroup G) :=
            Nat.mul_le_mul_right _ (hsupB.trans h1)
        _ = Nat.card C * (p * Nat.card (C ⊓ E : Subgroup G)) := by ring
    exact Nat.le_of_mul_le_mul_left h3 hCpos
  have hsub : (C ⊓ E : Subgroup G) ≤ Subgroup.zpowers x := by
    intro y hy
    have hyC : y ∈ C := (Subgroup.mem_inf.1 hy).1
    have hyE : y ∈ E := (Subgroup.mem_inf.1 hy).2
    have hyB : y ∈ B := hCB hyC
    have hyI : y ∈ innerModSubgroup p L := (Subgroup.mem_inf.1 hyC).2
    exact (hcent y hyB).1 (hno y hyE (mem_innerModSubgroup.1 hyI))
  have hZ : Nat.card (Subgroup.zpowers x) = p := by
    haveI := Fact.mk hp
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hB.2 x hxB) hx1
  have hle2 : Nat.card (C ⊓ E : Subgroup G) ≤ p := by
    have := Subgroup.card_le_of_le hsub
    rw [hZ] at this
    exact this
  have h4 : Nat.card E ≤ p * p := hle1.trans (Nat.mul_le_mul_left p hle2)
  rw [hE] at h4
  have hp2 := hp.two_le
  nlinarith

theorem exists_hyperplane_comm_ne_bot (hp : p.Prime) (hp2 : p ≠ 2) {B T : Subgroup G}
    (hB : IsElemAbelian p B) (hBne : B ≠ ⊥) (hT : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hne : (⁅T, B⁆ : Subgroup G) ≠ ⊥) :
    ∃ H : Subgroup G, H ≤ B ∧ (H.subgroupOf B).index = p ∧
      (⁅B, T ⊓ Subgroup.centralizer (H : Set G)⁆ : Subgroup G) ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  have hTC : T ≤ Subgroup.centralizer (B : Set G) := by
    refine (GL83.le_iSup_hyperplane hp hp2 hBne hB hT hBT).trans
      (iSup_le fun H => iSup_le fun hH => ?_)
    have h2 := hcon H hH.1 hH.2
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h2
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.1 (h2 hb) v hv).symm
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hTC

theorem mem_hyperplane_of_comm_ne_bot (hp : p.Prime) {B T H : Subgroup G} {x : G} (hHB : H ≤ B)
    (hidx : (H.subgroupOf B).index = p) (hxB : x ∈ B)
    (hxT : T ≤ Subgroup.centralizer ({x} : Set G))
    (hne : (⁅B, T ⊓ Subgroup.centralizer (H : Set G)⁆ : Subgroup G) ≠ ⊥) : x ∈ H := by
  by_contra hxH
  apply hne
  have hAB : H ⊔ Subgroup.zpowers x ≤ B := sup_le hHB (Subgroup.zpowers_le.2 hxB)
  have hrel : H.relIndex (H ⊔ Subgroup.zpowers x) * (H ⊔ Subgroup.zpowers x).relIndex B = p := by
    rw [Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers x) B le_sup_left hAB]
    exact hidx
  have hne1 : H.relIndex (H ⊔ Subgroup.zpowers x) ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact hxH (h1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  have hBle : B ≤ H ⊔ Subgroup.zpowers x := by
    have hsup1 : (H ⊔ Subgroup.zpowers x).relIndex B = 1 := by
      rcases (Nat.dvd_prime hp).1 (⟨_, hrel.symm⟩ : H.relIndex (H ⊔ Subgroup.zpowers x) ∣ p) with h | h
      · exact absurd h hne1
      · rw [h] at hrel
        have h5 : p * (H ⊔ Subgroup.zpowers x).relIndex B = p * 1 := by rw [mul_one]; exact hrel
        exact Nat.eq_of_mul_eq_mul_left hp.pos h5
    exact Subgroup.relIndex_eq_one.1 hsup1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvT : v ∈ T := (Subgroup.mem_inf.1 hv).1
  have hvH : v ∈ Subgroup.centralizer (H : Set G) := (Subgroup.mem_inf.1 hv).2
  have hCv : H ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({v} : Set G) := by
    refine sup_le ?_ ?_
    · intro h hh
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hvH h hh
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hxT hvT)).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hCv (hBle hb))).symm

theorem exists_elemAbelian_pow_three (hp : p.Prime) {B H : Subgroup G} {x : G}
    (hB : IsElemAbelian p B) (hHB : H ≤ B) (hxH : x ∈ H) (hx1 : x ≠ 1)
    (hcard : p ^ 3 ≤ Nat.card H) :
    ∃ E : Subgroup G, E ≤ H ∧ x ∈ E ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have hH : IsElemAbelian p H := isElemAbelian_mono hB hHB
  have hpf : Fact p.Prime := ⟨hp⟩
  have key : ∀ k : ℕ, 1 ≤ k → p ^ k ≤ Nat.card H →
      ∃ E : Subgroup G, E ≤ H ∧ x ∈ E ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _
      refine ⟨Subgroup.zpowers x, Subgroup.zpowers_le.2 hxH, Subgroup.mem_zpowers x,
        isElemAbelian_mono hH (Subgroup.zpowers_le.2 hxH), ?_⟩
      rw [Nat.card_zpowers, orderOf_eq_prime (hH.2 x hxH) hx1, pow_one]
    | succ k hk ih =>
      intro hk1
      have hkH : p ^ k ≤ Nat.card H :=
        le_trans (Nat.pow_le_pow_right hp.pos (Nat.le_succ k)) hk1
      obtain ⟨E, hEH, hxE, -, hEcard⟩ := ih hkH
      obtain ⟨y, hyH, hyE⟩ : ∃ y ∈ H, y ∉ E := by
        by_contra hno
        push Not at hno
        have h1 : Nat.card H ≤ Nat.card E := Subgroup.card_le_of_le (fun z hz => hno z hz)
        rw [hEcard] at h1
        have h2 : p ^ k < p ^ (k + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self k)
        exact lt_irrefl _ (lt_of_lt_of_le h2 (hk1.trans h1))
      have hy1 : y ≠ 1 := fun h => hyE (h ▸ E.one_mem)
      have hypow : y ^ p = 1 := hH.2 y hyH
      have hZH : Subgroup.zpowers y ≤ H := Subgroup.zpowers_le.2 hyH
      have hZcard : Nat.card (Subgroup.zpowers y) = p := by
        rw [Nat.card_zpowers, orderOf_eq_prime hypow hy1]
      have hcomm : ∀ e ∈ E, ∀ z ∈ Subgroup.zpowers y, e * z = z * e := by
        intro e he z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact (Commute.zpow_right
          (show Commute e y from isElemAbelian_commute hH (hEH he) hyH) n).eq
      have hinf : Nat.card (E ⊓ Subgroup.zpowers y : Subgroup G) = 1 := by
        have hdvd : Nat.card (E ⊓ Subgroup.zpowers y : Subgroup G) ∣ p := by
          rw [← hZcard]
          exact Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime hp).1 hdvd with h | h
        · exact h
        · exfalso
          have heq : E ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hZcard, h]))
          have hyEZ : y ∈ E ⊓ Subgroup.zpowers y := by
            rw [heq]
            exact Subgroup.mem_zpowers y
          exact hyE (Subgroup.mem_inf.1 hyEZ).1
      have hsum := p61_card_sup_mul_card_inf E (Subgroup.zpowers y) hcomm
      rw [hinf, mul_one, hEcard, hZcard] at hsum
      refine ⟨E ⊔ Subgroup.zpowers y, sup_le hEH hZH, Subgroup.mem_sup_left hxE,
        isElemAbelian_mono hH (sup_le hEH hZH), ?_⟩
      rw [pow_succ]
      exact hsum
  exact key 3 (by norm_num) hcard

theorem layer_centralizer_eq_bot (hp : p.Prime) (hbal : LBalanceAt G p) {x : G} {L E : Subgroup G}
    (hKx : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G))) (hxE : x ∈ E)
    (hE : IsElemAbelian p E) (hLx : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = L)
    (hlayer : GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) = ⊥) :
    GLAPLayer p (Subgroup.centralizer (E : Set G)) = ⊥ := by
  have hEx : E ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hE hxE
  have hCEx : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxE)
  have hbal' := hbal (Subgroup.centralizer ({x} : Set G)) E hKx hEx (isPGroup_of_isElemAbelian hE)
  rw [inf_eq_right.2 hCEx, hLx] at hbal'
  have hself : ∀ X : Subgroup G, GLAPLayer p X ≤ X := fun X => by
    unfold GLAPLayer
    exact sSup_le fun J (hJ : GLAPComponent p X J) => hJ.1
  have hle : GLAPLayer p (Subgroup.centralizer (E : Set G)) ≤
      L ⊓ Subgroup.centralizer (E : Set G) :=
    le_inf hbal' (hself _)
  unfold GLAPLayer
  refine eq_bot_iff.2 (sSup_le fun J hJ => ?_)
  have hJc : GLAPComponent p (Subgroup.centralizer (E : Set G)) J := hJ
  have hJle : J ≤ L ⊓ Subgroup.centralizer (E : Set G) := le_trans (le_sSup hJ) hle
  have hJ' : GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set G)) J :=
    glaPComponent_of_le hp hJc hJle inf_le_right
  have hJ2 : J ≤ GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) := le_sSup hJ'
  rw [hlayer] at hJ2
  exact hJ2

theorem bender_E (hp : p.Prime) (hp2 : p ≠ 2) {B E S : Subgroup G}
    (hB : IsElemAbelian p B) (hEB : E ≤ B) (hSC : IsSC p B)
    (hlayer : GLAPLayer p (Subgroup.centralizer (E : Set G)) = ⊥)
    (hS2 : IsPGroup 2 S) (hSE : S ≤ Subgroup.centralizer (E : Set G))
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer (E : Set G)) := by
  set C := Subgroup.centralizer (E : Set G) with hC
  have hBC : B ≤ C := fun b hb => Subgroup.mem_centralizer_iff.2 fun h hh =>
    isElemAbelian_commute hB (hEB hh) hb
  have hB'el : IsElemAbelian p (B.subgroupOf C) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (isElemAbelian_commute hB a.2 b.2))⟩⟩,
      fun y hy => Subtype.ext (by simpa using hB.2 (y : G) hy)⟩
  have hmax : ∀ F : Subgroup C, IsElemAbelian p F → B.subgroupOf C ≤ F → F = B.subgroupOf C := by
    intro F hF hBF
    refine le_antisymm (fun e he => ?_) hBF
    rw [Subgroup.mem_subgroupOf]
    have hcomm : (e : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := hF.1.1.comm ⟨⟨b, hBC hb⟩, hBF (Subgroup.mem_subgroupOf.2 hb)⟩ ⟨e, he⟩
      simpa using congrArg (fun z : F => ((z : C) : G)) h1
    have hpow : (e : G) ^ p = 1 := by
      have := hF.2 e he
      simpa using congrArg (fun z : C => (z : G)) this
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
    · rw [orderOf_eq_one_iff.1 h1]; exact B.one_mem
    · exact hSC.2 _ hcomm h1
  have hS'cop : Nat.Coprime p (Nat.card (S.subgroupOf C)) := by
    have hcard : Nat.card (S.subgroupOf C) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSE).toEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS2
    rw [hcard, hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hBS' : B.subgroupOf C ≤ Subgroup.normalizer ((S.subgroupOf C : Subgroup C) : Set C) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hBS (Subgroup.mem_subgroupOf.1 hb)) (s : G)
  have key := GL83.I_20_1_proved C p hp hp2 (p61_layer_top_eq_bot hp C hlayer) (B.subgroupOf C)
    hB'el hmax
  have hle : S.subgroupOf C ≤ GLAPPrimeCoreOf p (⊤ : Subgroup C) := by
    rw [← key]
    exact le_iSup_of_le (S.subgroupOf C) (le_iSup_of_le hS'cop (le_iSup_of_le hBS' le_rfl))
  intro s hs
  have h1 : (⟨s, hSE hs⟩ : C) ∈ GLAPPrimeCoreOf p (⊤ : Subgroup C) :=
    hle (Subgroup.mem_subgroupOf.2 hs)
  rw [p61_primeCoreOf_top_eq] at h1
  exact ⟨_, h1, rfl⟩

theorem glaPPrimeCoreOf_inf_le_of_le (hp : p.Prime) {Y H : Subgroup G} (hHY : H ≤ Y) :
    GLAPPrimeCoreOf p Y ⊓ H ≤ GLAPPrimeCoreOf p H := by
  have h := CFSG.HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp Y H
  rwa [inf_eq_right.2 hHY] at h

theorem commutator_facts (hp : p.Prime) (hp2 : p ≠ 2) {B T E S : Subgroup G}
    (hB : IsElemAbelian p B) (hEB : E ≤ B) (hT : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hS : S = ⁅B, T ⊓ Subgroup.centralizer (E : Set G)⁆) :
    S ≤ T ⊓ Subgroup.centralizer (E : Set G) ∧ IsPGroup 2 S ∧
      B ≤ Subgroup.normalizer (S : Set G) ∧ (⁅S, B⁆ : Subgroup G) = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hS
  have hfwd : ∀ b ∈ B, ∀ v ∈ T ⊓ Subgroup.centralizer (E : Set G),
      b * v * b⁻¹ ∈ T ⊓ Subgroup.centralizer (E : Set G) := by
    intro b hb v hv
    have hvT : v ∈ T := (Subgroup.mem_inf.1 hv).1
    have hvC : v ∈ Subgroup.centralizer (E : Set G) := (Subgroup.mem_inf.1 hv).2
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hBT hb) v).1 hvT, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hcb : Commute e b := isElemAbelian_commute hB (hEB he) hb
    have hch : Commute e v := Subgroup.mem_centralizer_iff.1 hvC e he
    exact ((hcb.mul_right hch).mul_right hcb.inv_right).eq
  have hBV : B ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact hfwd b hb v
    · intro hv
      have h := hfwd b⁻¹ (B.inv_mem hb) _ hv
      simpa [mul_assoc] using h
  set V : Subgroup G := T ⊓ Subgroup.centralizer (E : Set G) with hVdef
  have hV2 : IsPGroup 2 V := IsPGroup.to_le hT inf_le_left
  have hSV : ⁅B, V⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro b hb v hv
    rw [commutatorElement_def]
    exact V.mul_mem (hfwd b hb v hv) (V.inv_mem hv)
  have hS2 : IsPGroup 2 (⁅B, V⁆ : Subgroup G) := IsPGroup.to_le hT (hSV.trans inf_le_left)
  have hcop : Nat.Coprime (Nat.card B) (Nat.card V) := by
    obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian hp hB
    obtain ⟨c, hc⟩ := (IsPGroup.iff_card).1 hV2
    rw [ha, hc]
    exact Nat.Coprime.pow a c ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hsolv : Group.IsSolvable V := by
    haveI := IsPGroup.isNilpotent hV2
    infer_instance
  have hdbl := GL83.commutator_double_eq_self B V hBV hcop hsolv
  have hBS : B ≤ Subgroup.normalizer ((⁅B, V⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [mem_normalizer_iff_gLBConj_eq]
    have hBb : GLBConj b B = B := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hb)
    have hVb : GLBConj b V = V := mem_normalizer_iff_gLBConj_eq.1 (hBV hb)
    have hmap : GLBConj b ⁅B, V⁆ = ⁅GLBConj b B, GLBConj b V⁆ :=
      Subgroup.map_commutator B V (MulAut.conj b⁻¹).toMonoidHom
    rw [hmap, hBb, hVb]
  refine ⟨hSV, hS2, hBS, ?_⟩
  rw [Subgroup.commutator_comm B V]
  exact hdbl

theorem exists_glaPComponent_of_layer_ne_bot {X : Subgroup G} (h : GLAPLayer p X ≠ ⊥) :
    ∃ J : Subgroup G, GLAPComponent p X J := by
  by_contra hne
  push Not at hne
  apply h
  have : {L | GLAPComponent p X L} = (∅ : Set (Subgroup G)) :=
    Set.eq_empty_iff_forall_notMem.2 fun J hJ => hne J hJ
  unfold GLAPLayer
  rw [this, sSup_empty]

theorem prop61_holds (hc : S6Ctx G p) (hin : Prop61Inputs G p) : Prop61At G p := by
  intro B x L h hchev
  have hp := hc.prime
  have hp2 := hc.odd
  have hB := IsSStarMax.bmax h
  have hxE := IsSStarMax.essential h
  have hL := IsSStarMax.component h
  have hBL := IsSStarMax.normalizes h
  have hx1 : x ≠ 1 := hxE.2.1
  have hxB : x ∈ B := hxE.1
  have hKx := kGroup_centralizer hc hx1
  have hcent : CentModEqZpowers p B L x := hc.stage5.2.1 B x L h.1
  have hBel : IsElemAbelian p B := hB.1
  have h1 := hin.i71 hp hp2 B x L hKx hB hxE hL hBL hchev
  have hlayer : ∀ E : Subgroup G, E ≤ B → IsElemAbelian p E → Nat.card E = p ^ 3 →
      GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) = ⊥ := by
    intro E hEB hEel hE3
    by_contra hne
    obtain ⟨J, hJ⟩ := exists_glaPComponent_of_layer_ne_bot hne
    obtain ⟨y, hyE, hyin, hycent⟩ := exists_inner_noncentralizing hp hBel hx1 hxB hcent h1 hEB hE3
    rcases hin.chevInner hp hp2 _ L E hKx hL hchev hEel (hEB.trans hBL) ⟨J, hJ⟩ y hyE with h' | h'
    · exact hycent h'
    · exact h' hyin
  have hnoG : ¬ IsGStar p B L := by
    rintro ⟨E, hEB, hEel, hE3, hne⟩
    rw [closureIn_eq_self hBL] at hne
    exact hne (hlayer E hEB hEel hE3)
  have hlev : tripleLevel p B L = 1 := (tripleLevel_eq_one_iff hp B hL).2 ⟨hnoG, hchev⟩
  have hd : dLevel G p = 1 := (IsSStarMax.level h).symm.trans hlev
  have hSC : IsSC p B :=
    hc.stage3.2.2.2.1 B hB fun x' L' hx' hL' => (triple_of_dLevel_eq_one hp hd ⟨hB, hx', hL'⟩).2
  have hcf : ∀ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x} : Set G)) J →
      IsCompCoreFreeLocalType p B J := by
    intro J hJ
    have hJchev : IsChevSimple p (PSimple p J) := (triple_of_dLevel_eq_one hp hd ⟨hB, hxE, hJ⟩).2
    rcases hin.i196 hp hp2 _ J B hKx hJ hJchev hBel with h' | ⟨hp3, hL27, b, hbB, hbin⟩
    · exact h'
    · subst hp3
      exact absurd ((hc.stage3.2.2.2.2 rfl B x J hB hxB hx1 hJ hL27).2 b hbB.1) hbin
  have hsig : ∀ A : Subgroup G, A ≤ B →
      GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set G)) ⊓ Subgroup.centralizer ({x} : Set G) ≤
        GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
    intro A hAB
    have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := fun b hb => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact isElemAbelian_commute hBel hb hxB
    have h2 := hin.i194 hp (Subgroup.centralizer ({x} : Set G)) B A hKx hBx hBel hAB hcf
    have h3 := glaPPrimeCoreOf_inf_le_of_le hp (Y := Subgroup.centralizer (A : Set G))
      (H := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (A : Set G)) inf_le_right
    exact fun g hg => h2 (h3 ⟨hg.1, hg.2, Subgroup.map_subtype_le _ hg.1⟩)
  obtain ⟨T, hTC, hT2, hBT, hTB, hTne⟩ :=
    exists_two_group_comm_eq hp hp2 (CFSG.Open.IsElemAbelian.isPGroup hBel) hxE
  have hBne : B ≠ ⊥ := fun h0 => hx1 (by simpa [h0] using hxB)
  obtain ⟨H, hHB, hHidx, hHne⟩ := exists_hyperplane_comm_ne_bot hp hp2 hBel hBne hT2 hBT
    (by rw [hTB]; exact hTne)
  have hxH : x ∈ H := mem_hyperplane_of_comm_ne_bot hp hHB hHidx hxB hTC hHne
  have hcardH : p ^ 3 ≤ Nat.card H := by
    have h4 := pow_four_le_card_of_bmax hc hB
    have h5 : Nat.card H * p = Nat.card B := by
      have h6 := Subgroup.card_mul_index (H.subgroupOf B)
      rw [hHidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHB).toEquiv] at h6
      exact h6
    have h7 : p ^ 3 * p ≤ Nat.card H * p := by
      rw [h5, ← pow_succ]
      exact h4
    exact Nat.le_of_mul_le_mul_right h7 hp.pos
  obtain ⟨E, hEH, hxE', hEel, hE3⟩ := exists_elemAbelian_pow_three hp hBel hHB hxH hx1 hcardH
  have hLx : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = L := sstarMax_layer_eq hc h
  have hlayerE : GLAPLayer p (Subgroup.centralizer (E : Set G)) = ⊥ :=
    layer_centralizer_eq_bot hp hin.lBalance hKx hxE' hEel hLx (hlayer E (hEH.trans hHB) hEel hE3)
  set S : Subgroup G := ⁅B, T ⊓ Subgroup.centralizer (E : Set G)⁆ with hSdef
  obtain ⟨hSV, hS2, hBS, hSB⟩ := commutator_facts hp hp2 hBel (hEH.trans hHB) hT2 hBT hSdef
  have hSne : S ≠ ⊥ := by
    intro h0
    apply hHne
    refine eq_bot_iff.2 (le_trans ?_ h0.le)
    exact Subgroup.commutator_mono le_rfl (inf_le_inf_left T (Subgroup.centralizer_le hEH))
  have hSE : S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer (E : Set G)) :=
    bender_E hp hp2 hBel (hEH.trans hHB) hSC hlayerE hS2 (fun s hs => (hSV hs).2) hBS
  have hSx : S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) :=
    fun s hs => hsig E (hEH.trans hHB) ⟨hSE hs, hTC (hSV hs).1⟩
  have h414 := hc.stage4.2.2 (hd ▸ (by norm_num : 1 ≤ 2)) B x S hB hxB hx1 hSx hS2 hBS
  exact hSne (hSB ▸ h414)

end CFSG.LocalAnalysis.GLTheoremA
