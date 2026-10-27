module

public import CFSG.GH74.GLS.C3.Layer1.EvenAltModel
public import CFSG.GH74.GLS.C3.Layer1.EvenAlt
public import CFSG.GH74.GLS.C3.Layer1.EvenCore
public import CFSG.GH74.GLS.C3.Layer1.BackAuxSA

public section

namespace CFSG.GH74.GLS.EvenAlt

open Equiv Perm Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

section Abstract

variable {C : Type*} [Group C] {n : ℕ}

@[expose] def theta (Φ : C ≃* ↥(Fgrp n)) : C →* Amb n := (Fgrp n).subtype.comp Φ.toMonoidHom

theorem theta_apply (Φ : C ≃* ↥(Fgrp n)) (c : C) : theta Φ c = ((Φ c : ↥(Fgrp n)) : Amb n) := rfl

theorem theta_injective (Φ : C ≃* ↥(Fgrp n)) : Function.Injective (theta Φ) := fun _ _ h =>
  Φ.injective (Subtype.ext h)

theorem theta_mem (Φ : C ≃* ↥(Fgrp n)) (c : C) : theta Φ c ∈ Fgrp n := (Φ c).2

theorem exists_theta_eq (Φ : C ≃* ↥(Fgrp n)) {p : Amb n} (hp : p ∈ Fgrp n) : ∃ c, theta Φ c = p :=
  ⟨Φ.symm ⟨p, hp⟩, by simp [theta_apply]⟩

theorem map_theta_eq_altSub (hn : 5 ≤ n) (Φ : C ≃* ↥(Fgrp n)) {KC : Subgroup C}
    (eK : ↥KC ≃* alternatingGroup (Fin n)) : KC.map (theta Φ) = altSub n := by
  have hle : KC.map (theta Φ) ≤ Fgrp n := by
    rintro _ ⟨c, -, rfl⟩
    exact theta_mem Φ c
  exact eq_altSub_of_equiv n hn hle
    ((KC.equivMapOfInjective (theta Φ) (theta_injective Φ)).symm.trans eK)

theorem centralizes_iff_theta_mem_vSub (hn : 5 ≤ n) (Φ : C ≃* ↥(Fgrp n)) {KC : Subgroup C}
    (eK : ↥KC ≃* alternatingGroup (Fin n)) (c : C) :
    (∀ k ∈ KC, k * c = c * k) ↔ theta Φ c ∈ vSub n := by
  rw [mem_vSub_iff_centralizes n hn (theta_mem Φ c)]
  constructor
  · intro h f hf
    rw [← map_theta_eq_altSub hn Φ eK] at hf
    obtain ⟨k, hk, rfl⟩ := hf
    rw [← map_mul, ← map_mul, h k hk]
  · intro h k hk
    have := h (theta Φ k) (by rw [← map_theta_eq_altSub hn Φ eK]; exact ⟨k, hk, rfl⟩)
    apply theta_injective Φ
    rw [map_mul, map_mul]
    exact this.symm

end Abstract

theorem fgrp_equiv_centralizer (n : ℕ) (hn2 : 2 ≤ n)
    (y : alternatingGroup (Fin (n + 4))) (hy : orderOf y = 2)
    (h4 : numMoved ((y : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 4) :
    Nonempty (↥(Fgrp n) ≃* ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin (n + 4)))))) := by
  have hconj : IsConj (xstarA n) y :=
    isConj_alternating_of_numMoved_eq (n + 4) _ _ (orderOf_xstarA n) hy
      (by rw [numMoved_xstarA, h4])
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj hconj
  exact ⟨((MonoidHom.ofInjective (embA_injective n)).trans
    (MulEquiv.subgroupCongr (range_embA_eq n hn2))).trans e⟩

theorem numMoved_eq_four (n : ℕ) (hn : 5 ≤ n ∧ n ≤ 7) (y : alternatingGroup (Fin (n + 4)))
    (hy : orderOf y = 2) (K' : Subgroup (alternatingGroup (Fin (n + 4))))
    (hK' : K' ≤ Subgroup.centralizer ({y} : Set (alternatingGroup (Fin (n + 4)))))
    (hcard : Nat.card K' = Nat.card (alternatingGroup (Fin n))) :
    numMoved ((y : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 4 := by
  obtain ⟨hn5, hn7⟩ := hn
  have hm : n + 4 ≤ 11 := by omega
  rcases numMoved_eq_of_involution_alternating (n + 4) hm y hy with h | h
  · exact h
  · exfalso
    have h8 : 8 ≤ n + 4 := by omega
    have hYo := Layer3.orderOf_altY h8
    have hY8 : numMoved ((Layer3.altY h8 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 8 := by
      have hc : ((Layer3.altY h8 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) =
          Layer3.yPerm h8 := rfl
      rw [hc, numMoved_eq_card_support, ← Equiv.Perm.sum_cycleType, Layer3.yPerm_cycleType]
      simp
    have hconj : IsConj y (Layer3.altY h8) :=
      isConj_alternating_of_numMoved_eq (n + 4) _ _ hy hYo (by rw [h, hY8])
    obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj hconj
    have hcC : Nat.card (Subgroup.centralizer ({y} : Set (alternatingGroup (Fin (n + 4))))) =
        Nat.card (Subgroup.centralizer ({Layer3.altY h8} : Set (alternatingGroup (Fin (n + 4))))) :=
      Nat.card_congr e.toEquiv
    have hY := Layer3.card_centralizer_altY h8
    have hdvd : Nat.card K' ∣
        Nat.card (Subgroup.centralizer ({y} : Set (alternatingGroup (Fin (n + 4))))) :=
      Subgroup.card_dvd_of_le hK'
    rw [hcard, hcC] at hdvd
    generalize Nat.card (Subgroup.centralizer ({Layer3.altY h8} : Set (alternatingGroup (Fin (n + 4))))) = c at hdvd hY
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7) with rfl | rfl | rfl
    · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hdvd
      simp [Nat.factorial] at hdvd hY
      omega
    · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hdvd
      simp [Nat.factorial] at hdvd hY
      omega
    · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hdvd
      simp [Nat.factorial] at hdvd hY
      omega

section GLevel

variable {G : Type} [Group G]

theorem exists_modelIso {x : G} {K N : Subgroup G} {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 7) (hxN : x ∈ N)
    (hx2 : orderOf x = 2) (hCN : centralizer ({x} : Set G) ≤ N) (hKC : K ≤ centralizer ({x} : Set G))
    (σ : ↥N ≃* alternatingGroup (Fin (n + 4))) (eK : ↥K ≃* alternatingGroup (Fin n)) :
    Nonempty (↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp n)) := by
  set xN : ↥N := ⟨x, hxN⟩ with hxNdef
  have hxN2 : orderOf xN = 2 := by rw [Subgroup.orderOf_mk]; exact hx2
  set y : alternatingGroup (Fin (n + 4)) := σ xN with hy
  have hy2 : orderOf y = 2 := by rw [hy, MulEquiv.orderOf_eq]; exact hxN2
  set K' : Subgroup (alternatingGroup (Fin (n + 4))) := (K.subgroupOf N).map σ.toMonoidHom with hK'
  have hK'C : K' ≤ Subgroup.centralizer ({y} : Set (alternatingGroup (Fin (n + 4)))) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hkx : (k : G) * x = x * (k : G) :=
      mem_centralizer_singleton_iff.1 (hKC hk)
    have : k * xN = xN * k := Subtype.ext hkx
    simp only [MulEquiv.coe_toMonoidHom, hy]
    rw [← map_mul, ← map_mul, this]
  have hcard : Nat.card K' = Nat.card (alternatingGroup (Fin n)) := by
    rw [hK', Nat.card_congr ((K.subgroupOf N).equivMapOfInjective σ.toMonoidHom σ.injective).symm.toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKC.trans hCN)).toEquiv,
      Nat.card_congr eK.toEquiv]
  have hnum := numMoved_eq_four n hn y hy2 K' hK'C hcard
  obtain ⟨e3⟩ := fgrp_equiv_centralizer n (by omega) y hy2 hnum
  obtain ⟨e2⟩ := centralizer_singleton_mulEquiv σ xN
  let e1 : ↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({xN} : Set ↥N)) :=
    (Subgroup.subgroupOfEquivOfLe hCN).symm.trans
      (MulEquiv.subgroupCongr (EvenCore.centralizer_singleton_mk_eq x hxN).symm)
  exact ⟨e1.trans (e2.trans e3.symm)⟩

end GLevel

section Config

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_map_theta {C : Type*} [Group C] [Finite C] {n : ℕ} (Φ : C ≃* ↥(Fgrp n))
    {TC : Subgroup C} (hT : Nat.card TC = 2 ^ (Nat.card C).factorization 2) :
    IsSylowOf 2 (TC.map (theta Φ)) (Fgrp n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : TC.map (theta Φ) ≤ Fgrp n := by
    rintro _ ⟨c, -, rfl⟩
    exact theta_mem Φ c
  refine isSylowOf_of_card hle ?_
  rw [← Nat.card_congr (TC.equivMapOfInjective (theta Φ) (theta_injective Φ)).toEquiv, hT,
    Nat.card_congr Φ.toEquiv]

end Config

end CFSG.GH74.GLS.EvenAlt

namespace CFSG.GH74.GLS.EvenSel

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q : Subgroup G}

theorem x_mem_Q (hs : EvenSel x K T Q) : x ∈ Q := by
  rw [hs.hQ]
  refine ⟨?_, ?_⟩
  · exact C3.Layer1.Back.mem_of_isSylowOf_of_central hs.sylowT (mem_centralizer_singleton_iff.2 rfl)
      (fun _ hs' => mem_centralizer_singleton_iff.1 hs') hs.terminal.1
  · refine ⟨mem_centralizer_singleton_iff.2 rfl, ?_⟩
    refine C3.Layer1.Back.mem_centralizerSection_of_centralizes ?_ (by
      intro k hk
      exact (TwoThin.pPrimeCoreOf_le K) hk)
    intro k hk
    exact (mem_centralizer_singleton_iff.1 (hs.K_le_C hk)).symm

theorem mem_CxK_iff
    (hs : EvenSel x K T Q) {c : G} :
    c ∈ CxK x K ↔ c ∈ centralizer ({x} : Set G) ∧ ∀ k ∈ K, k * c = c * k := by
  unfold CxK
  rw [Subgroup.mem_inf, hs.pPrimeCoreOf_K, mem_centralizerSection_bot_iff']

end CFSG.GH74.GLS.EvenSel

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.EvenAlt Equiv Perm
  CFSG.GH74.GLS.C3.Layer2.Model

theorem isElementaryAbelian_of_mulEquiv' {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsElementaryAbelian p B) : CFSG.IsElementaryAbelian p A :=
  { is_comm := ⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact h.1.1.1 (e a) (e b))⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g => e.injective (by
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 h.2 (e g)) }

theorem b_even_alt_config_proved
    : B_even_alt_config := by
  intro G _ _ hG hE hV x K T Q N hs hstd hgam hMN hN n hn hKn hNn
  have hn' : n = 5 ∨ n = 6 := by simpa using hn
  have hn5 : 5 ≤ n := by omega
  have hn7 : n ≤ 7 := by omega
  obtain ⟨eK⟩ := hKn
  obtain ⟨σ⟩ := hNn
  have hMle : normalizer (K : Set G) ≤ N := hMN.le
  have hx2 : orderOf x = 2 := hs.terminal.1
  have hxQ : x ∈ Q := hs.x_mem_Q
  have hKC : K ≤ centralizer ({x} : Set G) := hs.K_le_C
  have hxcK : x ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.1 (hKC hk)
  have hCN : centralizer ({x} : Set G) ≤ N :=
    EvenCore.centralizer_le_of_mem_centralizer hs.sylowQ hgam hMle hxcK hx2
  have hxN : x ∈ N := hCN (mem_centralizer_singleton_iff.2 rfl)
  have hCnorm : centralizer ({x} : Set G) ≤ normalizer (K : Set G) :=
    EvenCore.centralizer_le_normalizer_of_mem hgam hxQ hx2
  obtain ⟨Φ⟩ := exists_modelIso ⟨hn5, hn7⟩ hxN hx2 hCN hKC σ eK
  set C := centralizer ({x} : Set G) with hCdef
  have eKC : ↥(K.subgroupOf C) ≃* alternatingGroup (Fin n) :=
    (Subgroup.subgroupOfEquivOfLe hKC).trans eK
  have hP2 : ∀ c : ↥C, (∀ k ∈ K, k * (c : G) = (c : G) * k) ↔ theta Φ c ∈ vSub n := by
    intro c
    rw [← centralizes_iff_theta_mem_vSub hn5 Φ eKC c]
    constructor
    · intro h k' hk'
      exact Subtype.ext (h k' hk')
    · intro h k hk
      have := h ⟨k, hKC hk⟩ hk
      exact congrArg Subtype.val this
  have hCxK : ∀ c : ↥C, (c : G) ∈ CxK x K ↔ theta Φ c ∈ vSub n := fun c => by
    rw [hs.mem_CxK_iff]
    exact ⟨fun h => (hP2 c).1 h.2, fun h => ⟨c.2, (hP2 c).2 h⟩⟩
  have hCxKC : CxK x K ≤ C := inf_le_left
  set CC := (CxK x K).subgroupOf C with hCC
  have hCCmap : CC.map (theta Φ) = vSub n := by
    ext p
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (hCxK c).1 hc
    · intro hp
      obtain ⟨c, hc⟩ := exists_theta_eq Φ (vSub_le n hp)
      refine ⟨c, ?_, hc⟩
      rw [← hc] at hp
      exact (hCxK c).2 hp
  have hcardCxK : Nat.card ↥(CxK x K) = 4 := by
    have h1 : Nat.card ↥CC = 4 := by
      rw [Nat.card_congr (CC.equivMapOfInjective (theta Φ) (theta_injective Φ)).toEquiv, hCCmap,
        card_vSub]
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCxKC).toEquiv] at h1
  have hCCp : IsPGroup 2 ↥CC := by
    have : Nat.card ↥CC = 2 ^ 2 := by
      rw [Nat.card_congr (CC.equivMapOfInjective (theta Φ) (theta_injective Φ)).toEquiv, hCCmap,
        card_vSub]
      norm_num
    exact IsPGroup.of_card this
  have hCCnormal : CC.Normal := by
    refine ⟨fun c hc c0 => ?_⟩
    have hc' : (c : G) ∈ CxK x K := hc
    rw [hs.mem_CxK_iff] at hc'
    show ((c0 * c * c0⁻¹ : ↥C) : G) ∈ CxK x K
    rw [hs.mem_CxK_iff]
    refine ⟨(c0 * c * c0⁻¹).2, fun k hk => ?_⟩
    have hk' : (c0 : G)⁻¹ * k * (c0 : G) ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (hCnorm (C.inv_mem c0.2)) k).1 hk
      simpa using this
    have hcomm := hc'.2 _ hk'
    have h1 : k = (c0 : G) * ((c0 : G)⁻¹ * k * (c0 : G)) * (c0 : G)⁻¹ := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc k * ((c0 : G) * (c : G) * (c0 : G)⁻¹)
        = (c0 : G) * (((c0 : G)⁻¹ * k * (c0 : G)) * (c : G)) * (c0 : G)⁻¹ := by group
      _ = (c0 : G) * ((c : G) * ((c0 : G)⁻¹ * k * (c0 : G))) * (c0 : G)⁻¹ := by rw [hcomm]
      _ = (c0 : G) * (c : G) * (c0 : G)⁻¹ * k := by
        conv_rhs => rw [h1]
        group
  obtain ⟨Q0, hQ0⟩ := hs.sylowT.exists_sylow_eq_subgroupOf
  have hCCle : CC ≤ T.subgroupOf C := by
    rw [← hQ0]
    have := hCCnormal
    exact hCCp.le_sylow_of_normal Q0
  have hCxKT : CxK x K ≤ T := fun g hg => by
    have : (⟨g, hCxKC hg⟩ : ↥C) ∈ CC := hg
    exact hCCle this
  have hQeq : Q = CxK x K := hs.hQ.trans (inf_eq_right.mpr hCxKT)
  have hcardQ : Nat.card ↥Q = 4 := by rw [hQeq]; exact hcardCxK
  have hCxKelem : CFSG.IsElementaryAbelian 2 ↥(CxK x K) := by
    let e : ↥(CxK x K) ≃* ↥(vSub n) :=
      ((Subgroup.subgroupOfEquivOfLe hCxKC).symm.trans
        (CC.equivMapOfInjective (theta Φ) (theta_injective Φ))).trans
        (MulEquiv.subgroupCongr hCCmap)
    exact isElementaryAbelian_of_mulEquiv' e (vSub_isElementaryAbelian n)
  have hQelem : CFSG.IsElementaryAbelian 2 ↥Q := by rw [hQeq]; exact hCxKelem
  have hTp : IsPGroup 2 ↥T := hs.sylowT.isPGroup
  have hCcard : Nat.card ↥C = 4 * n.factorial := by
    rw [Nat.card_congr Φ.toEquiv, card_Fgrp_eq]
  have hNcard : Nat.card ↥N = (n + 4).factorial / 2 := by
    rw [Nat.card_congr σ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  have hnotSyl : ¬ IsSylowOf 2 T ⊤ := by
    intro h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 := hs.sylowT.card_eq
    have h2 := h.card_eq
    rw [Subgroup.card_top] at h2
    have hdvd : Nat.card ↥N ∣ Nat.card G := Subgroup.card_subgroup_dvd_card N
    have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hN0 : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
    have hle : (Nat.card ↥N).factorization 2 ≤ (Nat.card G).factorization 2 :=
      (Nat.factorization_le_iff_dvd hN0 hG0).2 hdvd 2
    have heq : (Nat.card ↥C).factorization 2 = (Nat.card G).factorization 2 :=
      Nat.pow_right_injective (le_refl 2) (h1.symm.trans h2)
    rw [hCcard] at heq
    rw [hNcard] at hle
    rcases hn' with rfl | rfl
    · rw [Nat.factorization_def _ Nat.prime_two] at heq hle
      have e1 : padicValNat 2 (4 * Nat.factorial 5) = 5 := by decide +kernel
      have e2 : padicValNat 2 ((5 + 4).factorial / 2) = 6 := by decide +kernel
      rw [e1] at heq
      rw [e2] at hle
      omega
    · rw [Nat.factorization_def _ Nat.prime_two] at heq hle
      have e1 : padicValNat 2 (4 * Nat.factorial 6) = 6 := by decide +kernel
      have e2 : padicValNat 2 ((6 + 4).factorial / 2) = 7 := by decide +kernel
      rw [e1] at heq
      rw [e2] at hle
      omega
  obtain ⟨S, hS, hTS, a, haS, haN, haT, ha2⟩ := C3.Layer1.Back.exists_sylow_gt_and_a hTp hnotSyl
  have hCxKle : CxK x K ≤ centralizer (K : Set G) := fun c hc => by
    rw [hs.mem_CxK_iff] at hc
    exact mem_centralizer_iff.2 hc.2
  refine ⟨S, a, ?_⟩
  refine
    { twoTerminal := hs.twoTerminal
      terminal := hs.terminal
      kbar := ?_
      normalInC := ?_
      sylowT := hs.sylowT
      hQ := hs.hQ
      sylowQ := ?_
      card_Q := hcardQ
      elemQ := hQelem
      sylowS := hS
      T_lt_S := hTS
      a_mem := ⟨haS, haN, haT, ha2⟩
      cond6 := ?_
      noOddCore := hE.2.1 x hx2
      quotientType := ?_
      fiveCase := ?_ }
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hs.pPrimeCore_K).trans
      (QuotientGroup.quotientBot.trans eK)⟩
  · intro c hc k hk
    exact (Subgroup.mem_normalizer_iff.1 (hCnorm hc) k).1 hk
  · exact IsSylowOf.of_le hs.sylowQ (by rw [hQeq]) hCxKle
  · intro hQZ u hu hu1
    have hu2 : orderOf u = 2 :=
      orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian u hu) hu1
    exact hs.cent5 u hu (fun t ht => hQZ u hu t ht) hu2
  · let ψ : ↥C →* Perm (Fin n) := (MonoidHom.fst (Perm (Fin n)) (Perm (Fin 4))).comp (theta Φ)
    refine ⟨ψ, ?_, Or.inl ?_⟩
    · ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hQeq, hCxK c]
      exact fst_eq_one_iff_mem_vSub n (theta_mem Φ c)
    · refine MonoidHom.range_eq_top.2 fun σ0 => ?_
      obtain ⟨p, hp, hp1⟩ := exists_mem_Fgrp_fst_eq n σ0
      obtain ⟨c, hc⟩ := exists_theta_eq Φ hp
      exact ⟨c, by simp [ψ, hc, hp1]⟩
  · intro h5
    subst h5
    have hTC : Nat.card ↥(T.subgroupOf C) = 2 ^ (Nat.card ↥C).factorization 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.sylowT.le).toEquiv]
      exact hs.sylowT.card_eq
    have hTF := isSylowOf_map_theta Φ hTC
    obtain ⟨yF, hyF, hy2, hTFeq, qF, hqF, hne⟩ := fiveCase_model hTF
    obtain ⟨cy, hcy, hcyF⟩ := hyF
    have hqF' : qF ∈ CC.map (theta Φ) := by rw [hCCmap]; exact hqF
    obtain ⟨cq, hcq, hcqF⟩ := hqF'
    refine ⟨(cy : G), hcy, ?_, ?_, (cq : G), ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, ← hy2, ← hcyF]
      exact (orderOf_injective (theta Φ) (theta_injective Φ) cy).symm
    · have hKCmap : (K.subgroupOf C).map (theta Φ) = altSub 5 :=
        map_theta_eq_altSub (by omega : 5 ≤ 5) Φ eKC
      have hzp : (zpowers cy).map (theta Φ) = zpowers yF := by
        rw [MonoidHom.map_zpowers, hcyF]
      have hEq : T.subgroupOf C =
          (T.subgroupOf C ⊓ K.subgroupOf C) ⊔ CC ⊔ zpowers cy := by
        apply Subgroup.map_injective (theta_injective Φ)
        rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_inf _ _ _ (theta_injective Φ), hKCmap,
          hCCmap, hzp]
        exact hTFeq
      have h2 := congrArg (Subgroup.map C.subtype) hEq
      rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_inf _ _ _ C.subtype_injective] at h2
      simp only [Subgroup.subgroupOf_map_subtype] at h2
      have hCCs : CC.map C.subtype = Q := by
        rw [hCC, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCxKC, hQeq]
      rw [inf_eq_left.mpr hs.sylowT.le, inf_eq_left.mpr hKC, hCCs, MonoidHom.map_zpowers] at h2
      simpa using h2
    · rw [hQeq]; exact hcq
    · intro h
      apply hne
      rw [← hcyF, ← hcqF, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h

theorem b_even_N_alt_proved
    : B_even_N_alt :=
  b_even_N_alt_of_config b_even_alt_config_proved

end CFSG.GH74.GLS
