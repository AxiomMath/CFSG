module

public import CFSG.CGT.PushingUpLit.SolKNA.Config
import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1e
import CFSG.CGT.PushingUpLit.SolKNA.FrattiniCenter
public import CFSG.CGT.PushingUpLit.SolKNA.PairFrameA

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.RankThree.GF2n
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.CGT.PushingUpLit.SolKAb (IsCommSubgroup)
open CFSG.Open (IsElemAbelian)
open CFSG.ComponentClassification.AschbacherTheorem3 (Thm3Conclusion centerOf frattiniOf omegaOne)

variable {G : Type} [Group G]

theorem isElemAbelian_two_iff {A : Subgroup G} (hA : IsCommSubgroup A) :
    IsElemAbelian 2 A ↔ ∀ a ∈ A, a * a = 1 := by
  constructor
  · rintro ⟨-, h⟩ a ha
    simpa [sq] using h a ha
  · intro h
    refine ⟨⟨⟨fun a b => Subtype.ext (hA a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
    simpa [sq] using h x hx

theorem four_le_card_of_not_isCyclic [Finite G] {A : Subgroup G} (hA : IsPGroup 2 A)
    (hnc : ¬ IsCyclic A) : 4 ≤ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  rcases k with _ | _ | k
  · exfalso
    apply hnc
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    exact isCyclic_of_subsingleton
  · exfalso
    exact hnc (isCyclic_of_prime_card (p := 2) (by simpa using hk))
  · rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

open scoped MatrixGroups in
theorem sq_eq_one_psl2 {n : ℕ} {b : PSL(2, GaloisField 2 n)} {m : ℕ} (hb : b ^ 2 ^ m = 1) :
    b ^ 2 = 1 :=
  CFSG.ComponentClassification.Asc76.Sec5.sq_eq_one_of_pow_two_pow_eq_one
    (fun _ _ ht hx => CFSG.Walter.psl2_sq_eq_one_of_mem_centralizer_of_charTwo ht hx) hb

theorem sq_of_mem_omegaOne {A : Subgroup G} (hA : IsCommSubgroup A) {x : G}
    (hx : x ∈ omegaOne A) : x * x = 1 := by
  have key : ∀ y (hy : y ∈ omegaOne A), y ∈ A ∧ y * y = 1 := by
    intro y hy
    refine Subgroup.closure_induction (p := fun y _ => y ∈ A ∧ y * y = 1) ?_ ?_ ?_ ?_ hy
    · rintro z ⟨hzA, hz2⟩
      exact ⟨hzA, by simpa [sq] using hz2⟩
    · exact ⟨A.one_mem, mul_one 1⟩
    · rintro a b - - ⟨haA, ha2⟩ ⟨hbA, hb2⟩
      refine ⟨A.mul_mem haA hbA, ?_⟩
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hA b hbA a haA]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, mul_one]
    · rintro a - ⟨haA, ha2⟩
      refine ⟨A.inv_mem haA, ?_⟩
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [ha2, inv_one]
  exact (key x hx).2

section Alt

variable [Finite G] {R T : Subgroup G}

theorem aData_of_alt5 {W : Subgroup G} (P : TIPair R T) (hTW : T ≤ W) (hWS : W ≤ R ⊔ T)
    (hnorm : R ⊔ T ≤ Subgroup.normalizer (W : Set G)) (hcard : Nat.card ↥W = Nat.card ↥T ^ 3)
    (hZW : centerOf W = ⁅W, W⁆) (hZF : centerOf W = frattiniOf W)
    (hiso : Nonempty (↥(centerOf W) ≃* ↥T)) (hΩ : omegaOne T = T)
    (hrel : W.relIndex (R ⊔ T) = 2)
    (hγ : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card ↥T) : AData R T W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 W := P.two_S.to_le hWS
  have : Fact (IsPGroup 2 ↥W) := ⟨hW2⟩
  refine ⟨P, ?_, hTW, hWS, hnorm, hcard, ?_, ?_, hZW.le, hiso, hrel, hγ⟩
  · intro t ht
    exact sq_of_mem_omegaOne P.comm_T (by rw [hΩ]; exact ht)
  · intro x hx
    have h1 : (⟨x, hx⟩ : ↥W) ^ 2 ∈ frattini ↥W :=
      CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x, hx⟩ : ↥W)
    have h2 : x ^ 2 ∈ frattiniOf W := ⟨_, h1, rfl⟩
    rw [← hZF, sq] at h2
    exact h2
  · intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ ⁅W, W⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [← hZW] at h1
    exact h1

end Alt

namespace NAConfig

variable [Finite G] {K R T : Subgroup G} {g : G}

theorem inf_sup_eq (h : NAConfig G K R T g) : K ⊓ (R ⊔ T) = R := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.R_le_K le_sup_left)
  obtain ⟨r, hr, t, ht, rfl⟩ := exists_mul_of_mem_sup h.T_norm hx.2
  have htK : t ∈ T ⊓ K := ⟨ht, by
    have := K.mul_mem (K.inv_mem (h.R_le_K hr)) hx.1
    simpa using this⟩
  rw [h.inf_K, Subgroup.mem_bot] at htK
  rw [htK, mul_one]
  exact hr

theorem inf_R_eq_inf_K (h : NAConfig G K R T g) {W : Subgroup G} (hW : W ≤ R ⊔ T) :
    W ⊓ R = W ⊓ K := by
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hw, hr⟩
    exact ⟨hw, h.R_le_K hr⟩
  · rintro ⟨hw, hk⟩
    have : x ∈ K ⊓ (R ⊔ T) := ⟨hk, hW hw⟩
    rw [h.inf_sup_eq] at this
    exact ⟨hw, this⟩

theorem subgroupOf_normal (h : NAConfig G K R T g) {W : Subgroup G} (hW : W ≤ R ⊔ T)
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) : ((W ⊓ R).subgroupOf K).Normal := by
  rw [h.inf_R_eq_inf_K hW, Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxW, hxK⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hKW hk) x).mp hxW,
      K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)⟩
  · rintro ⟨hxW, hxK⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hKW hk) x).mpr hxW, ?_⟩
    have := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
    simpa [mul_assoc] using this

theorem exists_not_mem_N (h : NAConfig G K R T g)
    (hcard : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥T) :
    ∃ y ∈ R, y ∉ R ⊓ Subgroup.normalizer (T : Set G) := by
  by_contra hcon
  have hle : R ≤ R ⊓ Subgroup.normalizer (T : Set G) := fun y hy => by
    by_contra hy'
    exact hcon ⟨y, hy, hy'⟩
  have := Subgroup.card_le_of_le hle
  have := h.T_lt
  omega

theorem tiPair (h : NAConfig G K R T g) (hcomm : IsCommSubgroup T) : TIPair R T :=
  ⟨h.sylowR.isPGroup, h.T_isPGroup, h.T_ne, h.T_norm, by rw [inf_comm]; exact h.inf_R, hcomm,
    h.isTI_T⟩

theorem bData (h : NAConfig G K R T g) (hcomm : IsCommSubgroup T)
    (hcard : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥T)
    (hnorm : K ⊔ T ≤ Subgroup.normalizer
      ((((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G)) : Set G)) :
    BData R T ((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G)) :=
  { h.tiPair hcomm with
    hW := rfl
    normal := le_trans (sup_le_sup_right h.R_le_K T) hnorm
    card_N := hcard }

theorem eq_of_caseII4 (h : NAConfig G K R T g) (h4 : CaseII4 K R T) : K = R :=
  eq_of_forall_comm_mem h.perfect h.sylowR h.stSetting.inf_centralizer_pCoreOf_le h4.normal
    inf_le_left h4.comm_mem h4.central

end NAConfig


section Application


open CFSG.ComponentClassification.AS76b (tightlyEmbedded_rightConjugate)
open CFSG.ComponentClassification.Asc76.Lemma22 (isSylowOf_sup isSylowOf_sup_inf_normalizer
  relIndex_sup_inf_normalizer_le)
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix (tightlyEmbedded_subgroupOf_iff)
open CFSG.SignalizerFunctor.Helpers (relativeWeakClosure subgroup_le_relative_weak_closure
  relative_weak_closure_le)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {K R T : Subgroup G} {g : G}

theorem NAConfig.thm3 (h : NAConfig G K R T g) : Thm3Conclusion K T (R ⊔ T) := by
  have hJ : TightlyEmbedded (rightConjugate K g) := tightlyEmbedded_rightConjugate h.tight g
  have hKJ : Odd (Nat.card (K ⊓ rightConjugate K g : Subgroup G)) := h.tight.2 g h.g_not
  have hfac : (Nat.card K).factorization 2 = (Nat.card (rightConjugate K g)).factorization 2 := by
    rw [rightConjugate_card]
  have hT := h.sylowT
  have hT1 := h.T_ne
  have hR := h.sylowR
  have hTR := h.T_norm
  have hTK := h.T_le_normalizer
  have hT2 := h.T_isPGroup
  have hTKb := h.inf_K
  have hTJ := h.T_le_J
  have hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  set P : Subgroup G := rightConjugate K g ⊓ (K ⊔ T) with hP
  have hTP : IsSylowOf 2 T P := hT.of_le (le_inf hTJ le_sup_right) (inf_le_inf_left _ hKTN)
  have heven : Even (Nat.card ↥P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by rw [hn, pow_zero]))
    have h2T : 2 ∣ Nat.card T := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact even_iff_two_dvd.mpr (h2T.trans (Subgroup.card_dvd_of_le hTP.le))
  have htight : ∀ y ∈ K ⊔ T, y ∉ Subgroup.normalizer (P : Set G) →
      Odd (Nat.card (P ⊓ rightConjugate P y : Subgroup G)) := by
    intro y hy hyN
    have hyJ : y ∉ Subgroup.normalizer ((rightConjugate K g : Subgroup G) : Set G) := by
      intro hyn
      apply hyN
      rw [← rightConjugate_eq_self_iff] at hyn ⊢
      rw [hP, CFSG.ComponentClassification.AschbacherTheorem3.rightConjugate_inf, hyn,
        (rightConjugate_eq_self_iff _ y).mpr (Subgroup.le_normalizer hy)]
    exact (hJ.2 y hyJ).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_inf inf_le_left (Subgroup.map_mono inf_le_left)))
  have hodd : CFSG.oddCore ↥K = ⊥ := by
    have h0 := h.oddCoreIn_eq_bot
    unfold CFSG.ComponentClassification.AS76b.oddCoreIn at h0
    rw [Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h0
    exact h0
  exact CFSG.ComponentClassification.AschbacherTheorem3.theorem_3_holds G K T P (R ⊔ T)
    ⟨hT1, ⟨⟨hTK, hTKb, hT2⟩, isSylowOf_sup hR hT2 hTK hTR hTKb,
      isSylowOf_sup_inf_normalizer h.tight hJ hKJ hfac hT hT1 hR hTR⟩, hTP,
      inf_le_right,
      (tightlyEmbedded_subgroupOf_iff (inf_le_right : P ≤ K ⊔ T)).mpr ⟨heven, htight⟩,
      relIndex_sup_inf_normalizer_le h.tight hJ hKJ hfac hT hT1 hR hTR, hodd⟩


theorem NAConfig.four_or_five (h : NAConfig G K R T g) :
    K ⊔ T ≤ Subgroup.normalizer
      ((((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G)) : Set G) ∨
    ∃ W : Subgroup G, K ⊔ T ≤ Subgroup.normalizer (W : Set G) ∧ T ≤ W ∧ W ≤ R ⊔ T ∧
      Nat.card ↥W = Nat.card ↥T ^ 3 ∧ centerOf W = ⁅W, W⁆ ∧ centerOf W = frattiniOf W ∧
      Nonempty (↥(centerOf W) ≃* ↥T) ∧ omegaOne T = T ∧ W.relIndex (R ⊔ T) = 2 := by
  obtain ⟨-, -, hcard, -, -, hcomm, hnotcyc, -, -⟩ := h.basic
  rcases h.thm3 with h1 | h2 | h3 | h4 | h5
  · exact absurd h1.1 hnotcyc
  · exfalso
    have hR : R ≤ Subgroup.normalizer (T : Set G) := (h.R_le_K.trans le_sup_left).trans h2
    rw [inf_of_le_left hR] at hcard
    have := h.T_lt
    omega
  · exfalso
    obtain ⟨n, -, -, -, -, -, -, ⟨e⟩⟩ := h3
    have hK : CFSG.ComponentClassification.AschbacherTheorem3.oTwoPrime K = K := h.perfect
    have hrsq : ∀ r ∈ R, r * r = 1 := by
      intro r hr
      have hrK : r ∈ CFSG.ComponentClassification.AschbacherTheorem3.oTwoPrime K := by
        rw [hK]
        exact h.R_le_K hr
      obtain ⟨m, hm⟩ := h.sylowR.isPGroup ⟨r, hr⟩
      have hm' : r ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have h1 : (e ⟨r, hrK⟩) ^ 2 ^ m = 1 := by
        rw [← map_pow]
        have : (⟨r, hrK⟩ : ↥(CFSG.ComponentClassification.AschbacherTheorem3.oTwoPrime K)) ^ 2 ^ m
            = 1 := Subtype.ext (by simpa using hm')
        rw [this, map_one]
      have h2 : (e ⟨r, hrK⟩) ^ 2 = 1 := sq_eq_one_psl2 h1
      have h4 : (⟨r, hrK⟩ : ↥(CFSG.ComponentClassification.AschbacherTheorem3.oTwoPrime K)) ^ 2
          = 1 := e.injective (by rw [map_pow, h2, map_one])
      simpa [sq] using congrArg Subtype.val h4
    apply h.noncomm
    intro a ha b hb
    have ha2 := hrsq a ha
    have hb2 := hrsq b hb
    have hab2 := hrsq (a * b) (R.mul_mem ha hb)
    have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab2
    rw [mul_inv_rev, e1, e2] at e3
    exact e3.symm
  · left
    obtain ⟨x, hx, -, -, -, hW, hnorm, -⟩ := h4
    rw [hW] at hnorm
    exact hnorm
  · right
    exact ⟨relativeWeakClosure K T (R ⊔ T), h5.1,
      subgroup_le_relative_weak_closure _ _ _ le_sup_right, relative_weak_closure_le _ _ _,
      h5.2.1, h5.2.2.1, h5.2.2.2.1, h5.2.2.2.2.1, h5.2.2.2.2.2.1, h5.2.2.2.2.2.2⟩

theorem NAConfig.caseI (h : NAConfig G K R T g) (hel : ¬ IsElemAbelian 2 T) : CaseI K R T := by
  obtain ⟨-, -, hcard, -, -, hcomm, hnotcyc, -, -⟩ := h.basic
  rcases h.four_or_five with hnorm | ⟨W, -, -, -, -, -, -, -, hΩ, -⟩
  swap
  · exfalso
    apply hel
    rw [isElemAbelian_two_iff hcomm]
    intro t ht
    exact sq_of_mem_omegaOne hcomm (by rw [hΩ]; exact ht)
  have B := h.bData hcomm hcard hnorm
  obtain ⟨y, hy, hyN⟩ := h.exists_not_mem_N hcard
  have hyW : y ∉ ((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) := fun hyW =>
    hyN (by rw [← B.inf_R]; exact ⟨hyW, hy⟩)
  obtain ⟨e⟩ := B.nonempty_mulEquiv (Subgroup.mem_sup_left hy) hyW
  have hex : ∃ n ∈ R ⊓ Subgroup.normalizer (T : Set G), n * n ≠ 1 := by
    by_contra hcon
    have hall : ∀ n ∈ R ⊓ Subgroup.normalizer (T : Set G), n * n = 1 := fun n hn => by
      by_contra hne
      exact hcon ⟨n, hn, hne⟩
    apply hel
    rw [isElemAbelian_two_iff hcomm]
    intro t ht
    have h1 : e (⟨t, ht⟩ * ⟨t, ht⟩) = 1 := by
      rw [map_mul]
      exact Subtype.ext (hall _ (e ⟨t, ht⟩).2)
    have h2 : (⟨t, ht⟩ : ↥T) * ⟨t, ht⟩ = 1 := e.injective (by rw [h1, map_one])
    simpa using congrArg Subtype.val h2
  refine ⟨B.relIndex_eq_two hex ⟨y, hy, hyN⟩, fun x hx hxN n hn => B.inv_of_mem_R hx hxN hn,
    fun a ha b hb => B.N_comm_of_exists ⟨y, hy, hyN⟩ ha hb, ⟨e.symm⟩, hex, ?_, ?_⟩
  · intro hc
    have : IsCyclic ↥(R ⊓ Subgroup.normalizer (T : Set G)) := hc
    exact hnotcyc (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  · have := h.subgroupOf_normal (inf_le_left : (R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) ≤ R ⊔ T)
      (le_sup_left.trans hnorm)
    rwa [B.inf_R] at this


theorem NAConfig.caseII4_of (h : NAConfig G K R T g) (hel : IsElemAbelian 2 T)
    (hnorm : K ⊔ T ≤ Subgroup.normalizer
      ((((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G)) : Set G)) :
    CaseII4 K R T := by
  obtain ⟨-, -, hcard, -, -, hcomm, hnotcyc, -, -⟩ := h.basic
  have hel' := (isElemAbelian_two_iff hcomm).mp hel
  have B := h.bData hcomm hcard hnorm
  obtain ⟨y, hy, hyN⟩ := h.exists_not_mem_N hcard
  have hyW : y ∉ ((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) := fun hyW =>
    hyN (by rw [← B.inf_R]; exact ⟨hyW, hy⟩)
  have hyS : y ∈ R ⊔ T := Subgroup.mem_sup_left hy
  obtain ⟨e⟩ := B.nonempty_mulEquiv hyS hyW
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.T_ne
  have hNcomm : IsCommSubgroup (R ⊓ Subgroup.normalizer (T : Set G)) := fun a ha b hb =>
    B.N_comm_of_exists ⟨y, hy, hyN⟩ ha hb
  refine ⟨hel, four_le_card_of_not_isCyclic h.T_isPGroup hnotcyc,
    (isElemAbelian_two_iff hNcomm).mpr fun n hn => B.N_mul_self hel' hyS hyW hn, ⟨e.symm⟩,
    fun n hn r hr => B.N_central hel' ⟨y, hy, hyN⟩ hn hr, fun x hx => B.sq_mem_R hx,
    fun x hx z hz => B.comm_mem_R hx hz, ?_,
    B.relIndex_le_card ht₀ (fun h1 => ht₀1 (Subtype.ext h1)), ?_⟩
  · have hne1 : (R ⊓ Subgroup.normalizer (T : Set G)).relIndex R ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact hyN (h1 hy)
    have hne0 : (R ⊓ Subgroup.normalizer (T : Set G)).relIndex R ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    omega
  · have := h.subgroupOf_normal (inf_le_left : (R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) ≤ R ⊔ T)
      (le_sup_left.trans hnorm)
    rwa [B.inf_R] at this


theorem NAConfig.caseII (h : NAConfig G K R T g) (hel : IsElemAbelian 2 T) :
    CaseII4 K R T ∨ ∃ H, CaseII5 K R T H := by
  obtain ⟨-, -, hcard, -, -, hcomm, hnotcyc, -, -⟩ := h.basic
  rcases h.four_or_five with hnorm | ⟨W, hKW, hTW, hWS, hcardW, hZW, hZF, hiso, hΩ, hrel⟩
  · exact Or.inl (h.caseII4_of hel hnorm)
  · right
    have hA : AData R T W := aData_of_alt5 (h.tiPair hcomm) hTW hWS
      (le_trans (sup_le_sup_right h.R_le_K T) hKW) hcardW hZW hZF hiso hΩ hrel hcard.le
    exact ⟨W ⊓ R, hA.toCaseII5 (four_le_card_of_not_isCyclic h.T_isPGroup hnotcyc)
      (h.subgroupOf_normal hWS (le_sup_left.trans hKW))⟩

theorem NAConfig.card_dichotomy (h : NAConfig G K R T g) (hel : IsElemAbelian 2 T) :
    (R ⊓ Subgroup.normalizer (T : Set G)).relIndex R ≤
        Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) ∨
      Nat.card ↥R = 2 * Nat.card ↥T ^ 2 := by
  rcases h.caseII hel with h4 | ⟨H, h5⟩
  · exact Or.inl h4.relIndex_le
  · right
    have := Subgroup.relIndex_mul_card H R
    rw [h5.relIndex_two, inf_of_le_left h5.H_le, h5.card_H] at this
    exact this.symm

end Application

end CFSG.CGT.PushingUpLit.SolKNA
