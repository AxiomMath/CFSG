module

public import CFSG.GH74.Generic.BProg.Stage1Split
public import CFSG.GH74.GLS.C3.Layer1.Th2BalGlobal
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComponentMinimalPerfectLift
public import CFSG.GH74.GLS.C3.Layer1.BackBasic

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

section Obs

variable {G : Type} [Group G]

structure Obs32 (A : Subgroup G) (y : G) (D J : Subgroup G) : Prop where
  y_ord : orderOf y = 2
  y_cent : y ∈ centralizer (A : Set G)
  D_le : IsE 1 A D
  D_rank : pRank 2 ↥D ≤ 2
  comp : IsPCompIn 2 (centralizer ({y} : Set G)) J
  D_norm : D ≤ normalizer (J : Set G)
  D_faith : ∀ d ∈ D, d ≠ 1 → d ∉ centralizerSection J (pPrimeCoreOf 2 J)
  unbal : (pRank 2 ↥D = 2 ∧
      ¬ AG D ⊓ centralizer ({y} : Set G) ≤ centralizerSection J (pPrimeCoreOf 2 J)) ∨
    (pRank 2 ↥D = 1 ∧ ∃ c ∈ AG D ⊓ centralizer ({y} : Set G), ∃ b ∈ A,
      ⁅c, b⁆ ∉ centralizerSection J (pPrimeCoreOf 2 J))

end Obs

section LocBal

noncomputable abbrev rhoL {X : Type*} [Group X] (L : Subgroup X) :
    ↥(normalizer (L : Set X)) →* MulAut (↥L ⧸ center ↥L) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L).comp
    (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom L)

@[expose] def IsLocBal32 (Jt : Type*) [Group Jt] (B : Subgroup (MulAut Jt)) : Prop :=
  ∀ H : Subgroup (MulAut Jt), (MulAut.conj : Jt →* MulAut Jt).range ≤ H → B ≤ H →
    (∀ b ∈ B.subgroupOf H, b ≠ 1 → ∀ c ∈ CFSG.Assembly.Dichotomy.involutionOddCore b,
      ∀ b' ∈ B.subgroupOf H, ⁅c, b'⁆ = 1) ∧
    (∀ D : Subgroup ↥H, D ≤ B.subgroupOf H → Nat.card ↥D = 4 → (∀ d ∈ D, d * d = 1) →
      deltaCore D = ⊥)

structure Ctx21 (G : Type) [Group G] [Finite G] (x : G) (K A : Subgroup G) (a : G) (D J : Subgroup G) :
    Prop where
  hyp : Hyp2 G
  noAlt : NoAltJ2 G
  circ : IsJ2Circ x K
  src : IsSource2 x K A
  notAllow : ¬ IsAllowable x K A
  theta : thetaHalfPrime A ≠ ⊥
  notBal : ¬ IsBal32 A
  a_mem : a ∈ A
  obs : Obs32 A a D J

end LocBal

namespace Obs

open CFSG.GH74.GLS.Th2.Bal CFSG.ClassicalInvolution.Balance.LocalBalance

variable {G : Type} [Group G]

section Lift

variable [Finite G]

theorem piBar_commute_of_mem_centralizerSection {a : G} {J : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J) {z : ↥(centralizer ({a} : Set G))}
    (hz : (z : G) ∈ centralizerSection J (pPrimeCoreOf 2 J)) :
    ∀ x ∈ (J.subgroupOf (centralizer ({a} : Set G))).map (piBar a),
      piBar a z * x = x * piBar a z := by
  rintro _ ⟨j₀, hj₀, rfl⟩
  have hjJ : (j₀ : G) ∈ J := Subgroup.mem_subgroupOf.mp hj₀
  have hcomm : ⁅(j₀ : G), (z : G)⁆ ∈ pPrimeCoreOf 2 J := hz.2.2 _ hjJ
  have hO : ⁅(j₀ : G), (z : G)⁆ ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G)) :=
    pPrimeCoreOf_le_of_pCompIn hJ hcomm
  obtain ⟨o, ho, hoe⟩ := hO
  have hoeq : o = ⁅j₀, z⁆ := Subtype.ext hoe
  have h1 : piBar a ⁅j₀, z⁆ = 1 := by
    rw [piBar_eq_one_iff, ← hoeq]
    exact ho
  rw [map_commutatorElement] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem exists_J {k : ℕ} (hk : 1 ≤ k) {a : G} {D Y : Subgroup G}
    (hDH : D ≤ centralizer ({a} : Set G)) (hDk : 2 ^ k ≤ Nat.card ↥D) (hD2 : ∀ d ∈ D, d * d = 1)
    (hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)))
    {N : Subgroup (CentralizerBar a)}
    (hNY : N ≤ (Y.subgroupOf (centralizer ({a} : Set G))).map (piBar a)) (hN1 : N ≠ ⊥) :
    ∃ J : Subgroup G, IsPCompIn 2 (centralizer ({a} : Set G)) J ∧ D ≤ normalizer (J : Set G) ∧
      (∀ d ∈ D, d ≠ 1 → d ∉ centralizerSection J (pPrimeCoreOf 2 J)) ∧
      ¬ ∀ n ∈ N, ∀ x ∈ (J.subgroupOf (centralizer ({a} : Set G))).map (piBar a),
        n * x = x * n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({a} : Set G) with hH
  obtain ⟨L, hL, hFL, hFfaith, -, hNnc, -⟩ :=
    exists_component_of_image (k := k) hk hDH hDk hD2 hY hNY hN1
  obtain ⟨J₀, hJ₀, hJ₀map⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hL
  set J : Subgroup G := J₀.map H.subtype with hJdef
  have hJH : J ≤ H := Subgroup.map_subtype_le J₀
  have hJsub : J.subgroupOf H = J₀ :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective H) J₀
  have hJc : IsPCompIn 2 H J := ⟨hJH, by rw [hJsub]; exact hJ₀⟩
  have hLeq : (J.subgroupOf H).map (piBar a) = L := by rw [hJsub]; exact hJ₀map
  refine ⟨J, hJc, ?_, ?_, ?_⟩
  · intro d hdD
    have hdH : d ∈ H := hDH hdD
    set d₀ : ↥H := ⟨d, hdH⟩ with hd₀
    have hF : piBar a d₀ ∈ (D.subgroupOf H).map (piBar a) :=
      ⟨d₀, Subgroup.mem_subgroupOf.mpr hdD, rfl⟩
    have hLd := hFL _ hF
    have hnorm : piBar a d₀ ∈
        normalizer ((J₀.map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) : Subgroup _) : Set _) := by
      rw [hJ₀map]
      exact mem_normalizer_of_conjSub_eq hLd
    have hn' := CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hJ₀ hnorm
    have h2 : d₀ ∈ normalizer ((J.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
        d ∈ normalizer (J : Set G) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hJH]
      rfl
    exact h2.mp (hJsub ▸ hn')
  · intro d hdD hd1 hdS
    have hdH : d ∈ H := hDH hdD
    set d₀ : ↥H := ⟨d, hdH⟩ with hd₀
    have hF : piBar a d₀ ∈ (D.subgroupOf H).map (piBar a) :=
      ⟨d₀, Subgroup.mem_subgroupOf.mpr hdD, rfl⟩
    have hf1 : piBar a d₀ ≠ 1 := by
      intro h
      rw [piBar_eq_one_iff] at h
      have hsq : d₀ * d₀ = 1 := Subtype.ext (hD2 _ hdD)
      exact hd1 (congrArg Subtype.val (eq_one_of_sq_of_mem_pPrimeCore hsq h))
    apply hFfaith _ hF hf1
    intro x hx
    rw [← hLeq] at hx
    exact piBar_commute_of_mem_centralizerSection hJc hdS x hx
  · rw [hLeq]
    exact hNnc

theorem exists_obs32_of_isElementaryAbelian {A : Subgroup G} (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hnot : ¬ IsBal32 A) : ∃ (a : G) (D J : Subgroup G), a ∈ A ∧ Obs32 A a D J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAc, hAsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hAel
  have hnot' : ¬ IsKBal 2 A ∨ ¬ IsWeakKBal 1 A := by
    by_contra h
    push Not at h
    exact hnot h
  rcases hnot' with h2 | h1
  ·
    unfold IsKBal at h2
    push Not at h2
    obtain ⟨D₀, hD₀, a, haA, ha1, hnle⟩ := h2
    obtain ⟨hD₀A, hD₀el, hD₀rk⟩ := hD₀
    obtain ⟨D, hDD₀, hDcard⟩ := Th2Sig6.exists_sub_card hD₀el (k := 2) hD₀rk
    have hDA : D ≤ A := hDD₀.trans hD₀A
    have hDel : CFSG.IsElementaryAbelian 2 ↥D := Th2Sig6.isElementaryAbelian_of_le hAel hDA
    have hDrk : pRank 2 ↥D = 2 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hDcard
    obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
    have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hAsq a haA) ha1
    set H := centralizer ({a} : Set G) with hH
    have hDH : D ≤ H := fun d hd => mem_centralizer_singleton_iff.mpr (hAc d (hDA hd) a haA)
    set Y : Subgroup G := AG D ⊓ H with hYdef
    have hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
      fun d hd hd1 => inf_le_left.trans (iInf₂_le d ⟨hd, hd1⟩)
    obtain ⟨c, hc, hcn⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    have hcY : c ∈ Y := ⟨Th2Sig6.AG_anti hDD₀ hc.1, hc.2⟩
    have hN1 : (Y.subgroupOf H).map (piBar a) ≠ ⊥ := by
      intro h
      apply hcn
      have hmem : piBar a ⟨c, hc.2⟩ ∈ (Y.subgroupOf H).map (piBar a) :=
        ⟨⟨c, hc.2⟩, Subgroup.mem_subgroupOf.mpr hcY, rfl⟩
      rw [h, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
      exact ⟨⟨c, hc.2⟩, hmem, rfl⟩
    have hDk : 2 ^ 2 ≤ Nat.card ↥D := hDcard.ge
    obtain ⟨J, hJc, hDJ, hfaith, hnc⟩ :=
      exists_J (k := 2) (by norm_num) hDH hDk hDsq hY (le_refl _) hN1
    refine ⟨a, D, J, haA, ⟨ha2, mem_centralizer_iff.mpr fun h hh => hAc h hh a haA,
      ⟨hDA, hDel, hDrk.ge.trans' (by norm_num)⟩, hDrk.le, hJc, hDJ, hfaith, Or.inl ⟨hDrk, ?_⟩⟩⟩
    intro hle
    apply hnc
    rintro _ ⟨y₀, hy₀, rfl⟩ x hx
    exact piBar_commute_of_mem_centralizerSection hJc (hle (Subgroup.mem_subgroupOf.mp hy₀)) x hx
  ·
    unfold IsWeakKBal at h1
    push Not at h1
    obtain ⟨D₀, hD₀, a, haA, ha1, c, hc, b, hbA, hcb⟩ := h1
    obtain ⟨hD₀A, hD₀el, hD₀rk⟩ := hD₀
    obtain ⟨D, hDD₀, hDcard⟩ := Th2Sig6.exists_sub_card hD₀el (k := 1) hD₀rk
    have hDA : D ≤ A := hDD₀.trans hD₀A
    have hDel : CFSG.IsElementaryAbelian 2 ↥D := Th2Sig6.isElementaryAbelian_of_le hAel hDA
    have hDrk : pRank 2 ↥D = 1 := CFSG.pRank_eq_of_card_eq_pow one_lt_two (by simpa using hDcard)
    obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
    have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hAsq a haA) ha1
    set H := centralizer ({a} : Set G) with hH
    have hAH : A ≤ H := fun x hx => mem_centralizer_singleton_iff.mpr (hAc x hx a haA)
    have hDH : D ≤ H := hDA.trans hAH
    set Y : Subgroup G := AG D ⊓ H with hYdef
    have hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
      fun d hd hd1 => inf_le_left.trans (iInf₂_le d ⟨hd, hd1⟩)
    have hcY : c ∈ Y := ⟨Th2Sig6.AG_anti hDD₀ hc.1, hc.2⟩
    set W : Subgroup (CentralizerBar a) := (Y.subgroupOf H).map (piBar a) with hW
    set E : Subgroup (CentralizerBar a) := (A.subgroupOf H).map (piBar a) with hE
    set N : Subgroup (CentralizerBar a) := ⁅W, E⁆ with hN
    have hNW : N ≤ W := by
      rw [hN, Subgroup.commutator_le]
      rintro _ ⟨y₀, hy₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩
      have hyY : (y₀ : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy₀
      have hbA' : (b₀ : G) ∈ A := Subgroup.mem_subgroupOf.mp hb₀
      refine ⟨⁅y₀, b₀⁆, Subgroup.mem_subgroupOf.mpr ?_, map_commutatorElement _ _ _⟩
      have hcomm : ((⁅y₀, b₀⁆ : ↥H) : G) =
          (y₀ : G) * ((b₀ : G) * (y₀ : G)⁻¹ * (b₀ : G)⁻¹) := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hcomm]
      refine Y.mul_mem hyY ⟨?_, ?_⟩
      · exact conj_mem_AG (fun d hd => hAc _ hbA' d (hDA hd)) ((AG D).inv_mem hyY.1)
      · exact H.mul_mem (H.mul_mem b₀.2 (H.inv_mem y₀.2)) (H.inv_mem b₀.2)
    have hN1 : N ≠ ⊥ := by
      intro h
      apply hcb
      have hcH : c ∈ H := hc.2
      have hbH : b ∈ H := hAH hbA
      have hmem : piBar a ⁅(⟨c, hcH⟩ : ↥H), ⟨b, hbH⟩⁆ ∈ N := by
        rw [map_commutatorElement]
        exact Subgroup.commutator_mem_commutator ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hcY, rfl⟩
          ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hbA, rfl⟩
      rw [h, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
      exact ⟨_, hmem, rfl⟩
    have hDk : 2 ^ 1 ≤ Nat.card ↥D := hDcard.ge
    obtain ⟨J, hJc, hDJ, hfaith, hnc⟩ :=
      exists_J (k := 1) le_rfl hDH hDk hDsq hY hNW hN1
    refine ⟨a, D, J, haA, ⟨ha2, mem_centralizer_iff.mpr fun h hh => hAc h hh a haA,
      ⟨hDA, hDel, hDrk.ge⟩, hDrk.le.trans (by norm_num), hJc, hDJ, hfaith, Or.inr ⟨hDrk, ?_⟩⟩⟩
    by_contra hall
    push Not at hall
    apply hnc
    have hle : N ≤ Subgroup.centralizer
        (((J.subgroupOf H).map (piBar a) : Subgroup (CentralizerBar a)) :
          Set (CentralizerBar a)) := by
      rw [hN, Subgroup.commutator_le]
      rintro _ ⟨y₀, hy₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hyY : (y₀ : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy₀
      have hbA' : (b₀ : G) ∈ A := Subgroup.mem_subgroupOf.mp hb₀
      have hsec := hall _ hyY _ hbA'
      have key := piBar_commute_of_mem_centralizerSection hJc (z := ⁅y₀, b₀⁆) hsec x hx
      rw [map_commutatorElement] at key
      exact key.symm
    intro n hn x hx
    exact (Subgroup.mem_centralizer_iff.mp (hle hn) x hx).symm

theorem inf_AG_le_normalizer {a : G} {D : Subgroup G}
    (hDH : D ≤ centralizer ({a} : Set G)) (hD2 : ∀ d ∈ D, d * d = 1) {J : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J) (hDJ : D ≤ normalizer (J : Set G))
    {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) :
    AG D ⊓ centralizer ({a} : Set G) ≤ normalizer (J : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({a} : Set G) with hH
  have hJH : J ≤ H := hJ.1
  set J₀ : Subgroup ↥H := J.subgroupOf H with hJ₀
  have hJ₀c : IsPComponent 2 J₀ := hJ.2
  have hL : IsComponent (J₀.map (piBar a)) :=
    ((CFSG.ComponentClassification.PrimeComponentLift.prime_component_minimal_perfect_lift 2).2 J₀
      hJ₀c).2.2
  have hdH : d ∈ H := hDH hdD
  set d₀ : ↥H := ⟨d, hdH⟩ with hd₀
  have hsq : d₀ * d₀ = 1 := Subtype.ext (hD2 _ hdD)
  have hnormiff : ∀ g : ↥H, g ∈ normalizer (J₀ : Set ↥H) ↔ (g : G) ∈ normalizer (J : Set G) := by
    intro g
    rw [← Subgroup.subgroupOf_normalizer_eq hJH]
    rfl
  have hd₀N : d₀ ∈ normalizer (J₀ : Set ↥H) := (hnormiff d₀).mpr (hDJ hdD)
  have hπd : piBar a d₀ ∈ normalizer ((J₀.map (piBar a) : Subgroup _) : Set _) :=
    Subgroup.le_normalizer_map (piBar a) ⟨d₀, hd₀N, rfl⟩
  have hfL : conjSub (piBar a d₀) (J₀.map (piBar a)) = J₀.map (piBar a) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hπd
  have hFd : piBar a d₀ ∈ (D.subgroupOf H).map (piBar a) :=
    ⟨d₀, Subgroup.mem_subgroupOf.mpr hdD, rfl⟩
  have hf1 : piBar a d₀ ≠ 1 := by
    intro h
    rw [piBar_eq_one_iff] at h
    exact hd1 (congrArg Subtype.val (eq_one_of_sq_of_mem_pPrimeCore hsq h))
  have hf2 : piBar a d₀ * piBar a d₀ = 1 := by rw [← map_mul, hsq, map_one]
  have hY : ∀ d ∈ D, d ≠ 1 → AG D ⊓ H ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
    fun d hd hd1 => inf_le_left.trans (iInf₂_le d ⟨hd, hd1⟩)
  intro y hy
  have hyH : y ∈ H := hy.2
  have hπy : piBar a ⟨y, hyH⟩ ∈ deltaCore ((D.subgroupOf H).map (piBar a)) :=
    map_le_deltaCore hD2 hY ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hodd := deltaCore_le_involutionOddCore hFd hf1 hπy
  have hyL := conjSub_eq_of_mem_involutionOddCore hL hf2 hfL hodd
  have hn1 : piBar a ⟨y, hyH⟩ ∈ normalizer ((J₀.map (piBar a) : Subgroup _) : Set _) :=
    mem_normalizer_of_conjSub_eq hyL
  have hn2 := CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hJ₀c hn1
  exact (hnormiff ⟨y, hyH⟩).mp hn2

end Lift

section Counting

variable [Finite G] {A D C : Subgroup G}

private def mulMap (hDA : D ≤ A) (hCA : C ≤ A) : ↥D × ↥C → ↥A :=
  fun p => ⟨(p.1 : G) * (p.2 : G), A.mul_mem (hDA p.1.2) (hCA p.2.2)⟩

omit [Finite G] in
private theorem mulMap_injective (hDA : D ≤ A) (hCA : C ≤ A) (h : ∀ x ∈ D, x ∈ C → x = 1) :
    Function.Injective (mulMap hDA hCA) := by
  rintro ⟨d, c⟩ ⟨d', c'⟩ hEq
  have h1 : (d : G) * c = d' * c' := congrArg Subtype.val hEq
  have hD : (d' : G)⁻¹ * d ∈ D := D.mul_mem (D.inv_mem d'.2) d.2
  have hC : (c' : G) * (c : G)⁻¹ ∈ C := C.mul_mem c'.2 (C.inv_mem c.2)
  have heq : (d' : G)⁻¹ * d = c' * (c : G)⁻¹ := by
    calc (d' : G)⁻¹ * d = (d' : G)⁻¹ * (d * c) * (c : G)⁻¹ := by group
      _ = (d' : G)⁻¹ * (d' * c') * (c : G)⁻¹ := by rw [h1]
      _ = c' * (c : G)⁻¹ := by group
  have h2 : (d' : G)⁻¹ * d = 1 := h _ hD (heq ▸ hC)
  have hdd : (d : G) = d' := by
    have := congrArg (fun x => (d' : G) * x) h2
    simpa using this
  have hcc : (c : G) = c' := by
    have h3 : (c' : G) * (c : G)⁻¹ = 1 := heq ▸ h2
    have := congrArg (fun x => x * (c : G)) h3
    simpa using this.symm
  exact Prod.ext (Subtype.ext hdd) (Subtype.ext hcc)

theorem card_mul_le_of_trivial_inter (hDA : D ≤ A) (hCA : C ≤ A) (h : ∀ x ∈ D, x ∈ C → x = 1) :
    Nat.card ↥D * Nat.card ↥C ≤ Nat.card ↥A := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ (mulMap_injective hDA hCA h)

theorem exists_mul_of_card_eq (hDA : D ≤ A) (hCA : C ≤ A) (h : ∀ x ∈ D, x ∈ C → x = 1)
    (hcard : Nat.card ↥D * Nat.card ↥C = Nat.card ↥A) :
    ∀ b ∈ A, ∃ d ∈ D, ∃ c ∈ C, b = d * c := by
  intro b hb
  have hbij : Function.Bijective (mulMap hDA hCA) :=
    (Nat.bijective_iff_injective_and_card _).mpr
      ⟨mulMap_injective hDA hCA h, by rw [Nat.card_prod, hcard]⟩
  obtain ⟨⟨d, c⟩, hdc⟩ := hbij.2 ⟨b, hb⟩
  exact ⟨d, d.2, c, c.2, (congrArg Subtype.val hdc).symm⟩

theorem two_mul_card_le_of_lt {H K : Subgroup G} (h : H < K) :
    2 * Nat.card ↥H ≤ Nat.card ↥K := by
  have hdvd : Nat.card ↥H ∣ Nat.card ↥K := Subgroup.card_dvd_of_le h.le
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  have hKpos : 0 < Nat.card ↥K := Nat.card_pos
  have hne : Nat.card ↥H < Nat.card ↥K := by
    by_contra hge
    push Not at hge
    exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hge)
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    interval_cases m <;> simp_all
  calc 2 * Nat.card ↥H ≤ m * Nat.card ↥H := Nat.mul_le_mul_right _ hm2
    _ = Nat.card ↥K := by rw [hm, mul_comm]

end Counting

theorem conj_mem_centralizerSection {J : Subgroup G} {m s : G} (hmJ : m ∈ normalizer (J : Set G))
    (hmO : m ∈ normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G))
    (hs : s ∈ centralizerSection J (pPrimeCoreOf 2 J)) :
    m * s * m⁻¹ ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  obtain ⟨hsJ, hsO, hsc⟩ := hs
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · exact (normalizer (J : Set G)).mul_mem ((normalizer (J : Set G)).mul_mem hmJ hsJ)
      ((normalizer (J : Set G)).inv_mem hmJ)
  · exact (normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G)).mul_mem
      ((normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G)).mul_mem hmO hsO)
      ((normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G)).inv_mem hmO)
  · have hk' : m⁻¹ * k * m ∈ J := by
      have h1 := (Subgroup.mem_normalizer_iff.mp ((normalizer (J : Set G)).inv_mem hmJ) k).mp hk
      simpa using h1
    have h1 : ⁅k, m * s * m⁻¹⁆ = m * ⁅m⁻¹ * k * m, s⁆ * m⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp hmO _).mp (hsc _ hk')

end Obs

section Interface

variable {G : Type} [Group G]

theorem Obs32.y_mem_centralizerSection {A : Subgroup G} {a : G} {D J : Subgroup G}
    (h : Obs32 A a D J) : a ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
  C3.Layer1.Back.mem_centralizerSection_of_centralizes
    (fun _ hk => (mem_centralizer_singleton_iff.mp (h.comp.1 hk)).symm) Th2Sig6.pPrimeCoreOf_le

theorem Obs32.y_not_mem_D {A : Subgroup G} {a : G} {D J : Subgroup G} (h : Obs32 A a D J) :
    a ∉ D := fun haD =>
  have ha1 : a ≠ 1 := fun h1 => by simpa [h1] using h.y_ord
  h.D_faith a haD ha1 h.y_mem_centralizerSection

variable [Finite G]

theorem exists_obs32 {A : Subgroup G} (hA : IsE 3 ⊤ A) (hnot : ¬ IsBal32 A) :
    ∃ (a : G) (D J : Subgroup G), a ∈ A ∧ Obs32 A a D J :=
  Obs.exists_obs32_of_isElementaryAbelian hA.2.1 hnot

theorem Obs32.AG_inf_le_normalizer {A : Subgroup G} {a : G} {D J : Subgroup G} (h : Obs32 A a D J) :
    AG D ⊓ centralizer ({a} : Set G) ≤ normalizer (J : Set G) := by
  obtain ⟨-, hDel, hDrk⟩ := h.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  obtain ⟨d, hdD, hd1⟩ := Th2Sig6.exists_ne_one_of_card (k := pRank 2 ↥D) hDrk
    (C3.Layer1.Back.card_eq_two_pow_pRank hDel)
  have hDH : D ≤ centralizer ({a} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.y_cent x (h.D_le.1 hx))
  exact Obs.inf_AG_le_normalizer hDH hDsq h.comp h.D_norm hdD hd1

theorem Obs32.cA_eq {A D J : Subgroup G} {a : G} (hA : IsE 3 ⊤ A) (hA3 : pRank 2 ↥A ≤ 3)
    (h : Obs32 A a D J) (ha : a ∈ A) :
    ∀ b ∈ A, b ∈ centralizerSection J (pPrimeCoreOf 2 J) → b = 1 ∨ b = a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hAel, hA3'⟩ := hA
  have hAcard : Nat.card ↥A = 8 := by
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hAel
    have h2 : pRank 2 ↥A = 3 := le_antisymm hA3 hA3'
    rw [h1, h2]
    norm_num
  set S := centralizerSection J (pPrimeCoreOf 2 J) with hS
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = A ⊓ S := ⟨_, rfl⟩
  have hmemC : ∀ x, x ∈ C ↔ x ∈ A ∧ x ∈ S := fun x => by rw [hCdef]; exact Subgroup.mem_inf
  have hCA : C ≤ A := fun x hx => ((hmemC x).mp hx).1
  obtain ⟨hDA, hDel, hDrk⟩ := h.D_le
  have haS : a ∈ S := h.y_mem_centralizerSection
  have hDC : ∀ x ∈ D, x ∈ C → x = 1 := fun x hx hxC => by
    by_contra hx1
    exact h.D_faith x hx hx1 ((hmemC x).mp hxC).2
  have hDcard := C3.Layer1.Back.card_eq_two_pow_pRank hDel
  have hCle : Nat.card ↥C ≤ 2 := by
    rcases h.unbal with ⟨hD2, -⟩ | ⟨hD1, c, hc, b, hbA, hcb⟩
    · have hle := Obs.card_mul_le_of_trivial_inter hDA hCA hDC
      rw [hDcard, hD2, hAcard] at hle
      norm_num at hle
      omega
    · by_contra hlt
      push Not at hlt
      rw [hD1] at hDcard
      have hle := Obs.card_mul_le_of_trivial_inter hDA hCA hDC
      have hCdvd : Nat.card ↥C ∣ 8 := hAcard ▸ Subgroup.card_dvd_of_le hCA
      rw [hDcard, hAcard] at hle
      norm_num at hle
      have hC4 : Nat.card ↥C = 4 := by
        have hle' : Nat.card ↥C ≤ 4 := by omega
        generalize Nat.card ↥C = m at hlt hle' hCdvd ⊢
        interval_cases m <;> omega
      have hsurj := Obs.exists_mul_of_card_eq hDA hCA hDC
        (by rw [hDcard, hC4, hAcard]; norm_num)
      have hcN : c ∈ normalizer (J : Set G) := h.AG_inf_le_normalizer hc
      have hcO := TwoThin.mem_normalizer_pPrimeCoreOf hcN
      obtain ⟨d', hd'D, c', hc'C, hbeq⟩ := hsurj b hbA
      have hc'S : c' ∈ S := ((hmemC c').mp hc'C).2
      apply hcb
      rw [hbeq]
      have hcd : c * d' = d' * c :=
        (mem_centralizer_iff.mp (Th2Sig6.AG_le_centralizer hc.1) d' hd'D).symm
      have hd'N : d' ∈ normalizer (J : Set G) := h.D_norm hd'D
      have hd'O := TwoThin.mem_normalizer_pPrimeCoreOf hd'N
      have hcc' : ⁅c, c'⁆ ∈ S := by
        have h1 := Obs.conj_mem_centralizerSection hcN hcO hc'S
        have h2 : ⁅c, c'⁆ = (c * c' * c⁻¹) * c'⁻¹ := by
          simp only [commutatorElement_def]
        rw [h2]
        exact S.mul_mem h1 (S.inv_mem hc'S)
      have h3 : ⁅c, d' * c'⁆ = d' * ⁅c, c'⁆ * d'⁻¹ := by
        calc ⁅c, d' * c'⁆ = (c * d') * c' * c⁻¹ * c'⁻¹ * d'⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = (d' * c) * c' * c⁻¹ * c'⁻¹ * d'⁻¹ := by rw [hcd]
          _ = d' * ⁅c, c'⁆ * d'⁻¹ := by simp only [commutatorElement_def]; group
      rw [h3]
      exact Obs.conj_mem_centralizerSection hd'N hd'O hcc'
  have haC : a ∈ C := (hmemC a).mpr ⟨ha, haS⟩
  have hza : zpowers a ≤ C := (Subgroup.zpowers_le).mpr haC
  have hzcard : Nat.card ↥(zpowers a) = 2 := by rw [Nat.card_zpowers, h.y_ord]
  have hCz : zpowers a = C :=
    Subgroup.eq_of_le_of_card_ge hza (by rw [hzcard]; exact hCle)
  intro b hb hbS
  have hbz : b ∈ zpowers a := hCz ▸ (hmemC b).mpr ⟨hb, hbS⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hbz
  have hk : a ^ (k % 2) = a ^ k := by
    have := zpow_mod_orderOf a k
    rwa [h.y_ord, Nat.cast_ofNat] at this
  rw [← hk]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero]
  · right
    rw [h1, zpow_one]

theorem Obs32.cases {A D J : Subgroup G} {a : G} (hA : IsE 3 ⊤ A) (hA3 : pRank 2 ↥A ≤ 3)
    (h : Obs32 A a D J) (ha : a ∈ A) :
    pRank 2 ↥D = 2 ∨ (pRank 2 ↥D = 1 ∧ A ≤ normalizer (J : Set G)) ∨
      (pRank 2 ↥D = 1 ∧ ∃ e' ∈ A, e' ∉ normalizer (J : Set G) ∧
        A = D ⊔ closure ({a, e'} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD1 := h.D_le.2.2
  have hD2 := h.D_rank
  have hr : pRank 2 ↥D = 1 ∨ pRank 2 ↥D = 2 := by omega
  rcases hr with h1 | h2
  · right
    by_cases hAN : A ≤ normalizer (J : Set G)
    · exact Or.inl ⟨h1, hAN⟩
    · right
      obtain ⟨e', he'A, he'N⟩ := IsConcreteLE.not_le_iff_exists.mp hAN
      refine ⟨h1, e', he'A, he'N, ?_⟩
      obtain ⟨-, hAel, hA3'⟩ := hA
      have hAcard : Nat.card ↥A = 8 := by
        have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hAel
        have h2 : pRank 2 ↥A = 3 := le_antisymm hA3 hA3'
        rw [h1, h2]
        norm_num
      obtain ⟨hDA, hDel, -⟩ := h.D_le
      have hDcard : Nat.card ↥D = 2 := by
        rw [C3.Layer1.Back.card_eq_two_pow_pRank hDel, h1]
        rfl
      have haN : a ∈ normalizer (J : Set G) := h.y_mem_centralizerSection.1
      have hBN : D ⊔ closure ({a} : Set G) ≤ normalizer (J : Set G) :=
        sup_le h.D_norm ((Subgroup.closure_le _).mpr (by simpa using haN))
      have he'B : e' ∉ D ⊔ closure ({a} : Set G) := fun he => he'N (hBN he)
      have haB : a ∈ D ⊔ closure ({a} : Set G) :=
        Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
      have hDB : D < D ⊔ closure ({a} : Set G) :=
        lt_of_le_of_ne le_sup_left (fun heq => h.y_not_mem_D (heq ▸ haB))
      have hBT : D ⊔ closure ({a} : Set G) < D ⊔ closure ({a, e'} : Set G) := by
        refine lt_of_le_of_ne (sup_le_sup_left (Subgroup.closure_mono
          (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))) D) fun heq => he'B ?_
        rw [heq]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      have hTA : D ⊔ closure ({a, e'} : Set G) ≤ A :=
        sup_le hDA ((Subgroup.closure_le _).mpr (by
          intro x hx
          rcases hx with rfl | hx
          · exact ha
          · rw [Set.mem_singleton_iff] at hx
            rw [hx]
            exact he'A))
      have h4 := Obs.two_mul_card_le_of_lt hDB
      have h8 := Obs.two_mul_card_le_of_lt hBT
      exact (Subgroup.eq_of_le_of_card_ge hTA (by omega)).symm
  · exact Or.inl h2

theorem stage1BalFor_of_ctx {P : ∀ (Kt : Type) [Group Kt], Prop}
    (h : ∀ (G : Type) [Group G] [Finite G] (x : G) (K A : Subgroup G) (a : G) (D J : Subgroup G),
      Ctx21 G x K A a D J → P (↥K ⧸ pPrimeCore 2 ↥K) → False) : Stage1BalFor P := by
  intro G _ _ hyp noAlt x K hcirc hP A hsrc hnotAllow htheta
  by_contra hnot
  obtain ⟨a, D, J, haA, hobs⟩ := exists_obs32 (isE3_of_isSource2 hsrc) hnot
  exact h G x K A a D J ⟨hyp, noAlt, hcirc, hsrc, hnotAllow, htheta, hnot, haA, hobs⟩ hP

namespace Ctx21

variable {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem isE3 (hc : Ctx21 G x K A a D J) : IsE 3 ⊤ A := isE3_of_isSource2 hc.src

theorem pRank_eq (hc : Ctx21 G x K A a D J) : pRank 2 ↥A = 3 := by
  obtain ⟨-, hel, hcard, -⟩ := hc.src
  have := hel
  exact CFSG.pRank_eq_of_card_eq_pow one_lt_two (by simpa using hcard)

theorem cA_eq (hc : Ctx21 G x K A a D J) :
    ∀ b ∈ A, b ∈ centralizerSection J (pPrimeCoreOf 2 J) → b = 1 ∨ b = a :=
  hc.obs.cA_eq hc.isE3 hc.pRank_eq.le hc.a_mem

theorem obs_cases (hc : Ctx21 G x K A a D J) :
    pRank 2 ↥D = 2 ∨ (pRank 2 ↥D = 1 ∧ A ≤ normalizer (J : Set G)) ∨
      (pRank 2 ↥D = 1 ∧ ∃ e' ∈ A, e' ∉ normalizer (J : Set G) ∧
        A = D ⊔ closure ({a, e'} : Set G)) :=
  hc.obs.cases hc.isE3 hc.pRank_eq.le hc.a_mem

end Ctx21

end Interface

end CFSG.GH74.Generic.BProg.B3
