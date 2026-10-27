module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4K6
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Cnt

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N.P4

variable {Γ : Type*} [Group Γ]

theorem normalizer_of_conj_mem [Finite Γ] {Q : Subgroup Γ} {g : Γ} (h : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) :
    g ∈ normalizer (Q : Set Γ) := by
  have hle : Q.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    exact h q hq
  have heq : Q.map (MulAut.conj g).toMonoidHom = Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

theorem card_modEq_commuting [Finite Γ] (p : ℕ) [Fact p.Prime] {x : Γ} (hx : x ^ p = 1) (S : Set Γ)
    (hS : ∀ d ∈ S, x * d * x⁻¹ ∈ S) :
    Nat.card S ≡ {c : Γ | c ∈ S ∧ x * c = c * x}.ncard [MOD p] := by
  classical
  let f : S → S := fun d => ⟨x * d * x⁻¹, hS d d.2⟩
  have hit : ∀ (n : ℕ) (d : S), ((f^[n] d : S) : Γ) = x ^ n * d * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro d; simp
    | succ n ih =>
      intro d
      rw [Function.iterate_succ_apply']
      show x * ((f^[n] d : S) : Γ) * x⁻¹ = _
      rw [ih, pow_succ']
      group
  have hf : ∀ d, f^[p] d = d := fun d => Subtype.ext (by rw [hit, hx]; simp)
  haveI := Fintype.ofFinite S
  let F : Function.End S := f
  have hF : F ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext d
    exact hf d
  have h := Equiv.Perm.card_fixedPoints_modEq (f := F) (p := p) (n := 1) hF
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  have himg : Subtype.val '' Function.fixedPoints f = {c : Γ | c ∈ S ∧ x * c = c * x} := by
    ext c
    constructor
    · rintro ⟨d, hd, rfl⟩
      have hd' : x * (d : Γ) * x⁻¹ = d := congrArg Subtype.val hd
      exact ⟨d.2, mul_inv_eq_iff_eq_mul.1 hd'⟩
    · rintro ⟨hcS, hc⟩
      refine ⟨⟨c, hcS⟩, ?_, rfl⟩
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.2 hc
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact h

@[expose] def cls (K : Subgroup Γ) (t : Γ) : Set Γ := {d | ∃ k ∈ K, d = k * t * k⁻¹}

structure KSetup (U K : Subgroup Γ) (x v t : Γ) : Prop where
  hF : IsF20 U x v
  htt : t * t = 1
  htnU : t ∉ U
  htU : ∀ u ∈ U, t * u = u * t
  htx : t * x = x * t
  htv : t * v = v * t
  hCK : zpowers t ⊔ IsF20.Pgrp U x v ≤ K
  hKN : K ≤ normalizer ((U ⊔ zpowers t : Subgroup Γ) : Set Γ)
  hCt : ∀ k ∈ K, k * t = t * k → k ∈ zpowers t ⊔ IsF20.Pgrp U x v
  hΔ : ∀ k ∈ K, ∃ u ∈ U, k * t * k⁻¹ = t * u
  hne : ∃ u ∈ U, ∀ k ∈ K, k * t * k⁻¹ ≠ t * u
  h7 : ∃ u ∈ U, u ≠ 1 ∧ ∃ k ∈ K, k * t * k⁻¹ = t * u

namespace KSetup

variable {U K : Subgroup Γ} {x v t : Γ}

theorem t_comm_P (h : KSetup U K x v t) : ∀ p ∈ IsF20.Pgrp U x v, t * p = p * t := by
  have hle : IsF20.Pgrp U x v ≤ centralizer ({t} : Set Γ) := by
    refine sup_le ?_ (sup_le ?_ ?_)
    · intro u hu
      exact mem_centralizer_singleton_iff.2 (h.htU u hu).symm
    · rw [Subgroup.zpowers_le]
      exact mem_centralizer_singleton_iff.2 h.htx.symm
    · rw [Subgroup.zpowers_le]
      exact mem_centralizer_singleton_iff.2 h.htv.symm
  intro p hp
  exact (mem_centralizer_singleton_iff.1 (hle hp)).symm

theorem t_mem_cls (h : KSetup U K x v t) : t ∈ cls K t := by
  exact ⟨1, one_mem K, by simp⟩

theorem conj_mem_cls (h : KSetup U K x v t) {k : Γ} (hk : k ∈ K) {d : Γ} (hd : d ∈ cls K t) :
    k * d * k⁻¹ ∈ cls K t := by
  obtain ⟨k', hk', rfl⟩ := hd
  exact ⟨k * k', mul_mem hk hk', by group⟩

theorem cls_subset (h : KSetup U K x v t) {d : Γ} (hd : d ∈ cls K t) : ∃ u ∈ U, d = t * u := by
  obtain ⟨k, hk, rfl⟩ := hd
  exact h.hΔ k hk

theorem U0_data (h : KSetup U K x v t) :
    IsElemAbelian 2 (U ⊔ zpowers t) ∧ Nat.card ↥(U ⊔ zpowers t) = 32 := by
  refine ⟨?_, card_U0 h.hF h.htt h.htU h.htnU⟩
  refine IsElemAbelian.sup_of_commute
    ⟨⟨⟨fun a b => Subtype.ext (h.hF.comm a a.2 b b.2)⟩⟩, fun a ha => by
      rw [pow_two]
      exact h.hF.sq a ha⟩
    (isElemAbelian_zpowers (by rw [pow_two]; exact h.htt)) ?_
  rintro a ha b ⟨n, rfl⟩
  exact (Commute.zpow_right (show Commute a t from (h.htU a ha).symm) n).eq

theorem eq_bot_or_top [Finite Γ] (h : KSetup U K x v t) {T : Subgroup Γ} (hTU : T ≤ U)
    (hT : ∀ a ∈ T, x * a * x⁻¹ ∈ T) : T = ⊥ ∨ T = U := by
  exact h.hF.subgroup_eq_bot_or_top hTU (normalizer_of_conj_mem hT)

theorem inf_zpowers_Pgrp_eq_bot (h : KSetup U K x v t) :
    zpowers t ⊓ IsF20.Pgrp U x v = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyt, hyP⟩ := Subgroup.mem_inf.1 hy
  rcases eq_one_or_eq_of_mem_zpowers_invol h.htt hyt with h1 | h1
  · rw [Subgroup.mem_bot]
    exact h1
  · exfalso
    rw [h1] at hyP
    exact h.htnU (h.hF.centralizer_Pgrp hyP h.htU)

theorem card_C (h : KSetup U K x v t) : Nat.card ↥(zpowers t ⊔ IsF20.Pgrp U x v) = 640 :=
  card_zpowers_sup_Pgrp h.hF h.htt h.htnU h.t_comm_P h.inf_zpowers_Pgrp_eq_bot

theorem C_comm (h : KSetup U K x v t) {c : Γ} (hc : c ∈ zpowers t ⊔ IsF20.Pgrp U x v) :
    c * t = t * c := by
  have hle : zpowers t ⊔ IsF20.Pgrp U x v ≤ centralizer ({t} : Set Γ) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mem_centralizer_singleton_iff.2 rfl
    · intro p hp
      exact mem_centralizer_singleton_iff.2 (h.t_comm_P p hp).symm
  exact mem_centralizer_singleton_iff.1 (hle hc)

theorem x_mem_K (h : KSetup U K x v t) : x ∈ K :=
  h.hCK (mem_sup_right (mem_sup_right (mem_sup_left (mem_zpowers x))))

theorem card_cls_mul [Finite Γ] (h : KSetup U K x v t) :
    Nat.card ↥(cls K t) * 640 = Nat.card K := by
  classical
  set C : Subgroup Γ := zpowers t ⊔ IsF20.Pgrp U x v with hCdef
  let Kc : Subgroup ↥K := C.subgroupOf K
  have hKc : Nat.card Kc = 640 := by
    rw [← h.card_C]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.hCK).toEquiv
  let φ : ↥K ⧸ Kc → ↥(cls K t) := Quotient.lift
    (fun k : ↥K => (⟨(k : Γ) * t * (k : Γ)⁻¹, k, k.2, rfl⟩ : ↥(cls K t)))
    (fun a b hab => by
      have hab' : a⁻¹ * b ∈ Kc := QuotientGroup.leftRel_apply.mp hab
      have hc : ((a : Γ)⁻¹ * b) * t = t * ((a : Γ)⁻¹ * b) := h.C_comm hab'
      apply Subtype.ext
      show (a : Γ) * t * (a : Γ)⁻¹ = (b : Γ) * t * (b : Γ)⁻¹
      calc (a : Γ) * t * (a : Γ)⁻¹
          = (a : Γ) * (t * ((a : Γ)⁻¹ * b) * ((a : Γ)⁻¹ * b)⁻¹) * (a : Γ)⁻¹ := by group
        _ = (a : Γ) * (((a : Γ)⁻¹ * b) * t * ((a : Γ)⁻¹ * b)⁻¹) * (a : Γ)⁻¹ := by rw [hc]
        _ = (b : Γ) * t * (b : Γ)⁻¹ := by group)
  have hbij : Function.Bijective φ := by
    constructor
    · intro p q hpq
      induction p using Quotient.inductionOn with | _ a =>
      induction q using Quotient.inductionOn with | _ b =>
      have hab : (a : Γ) * t * (a : Γ)⁻¹ = (b : Γ) * t * (b : Γ)⁻¹ := congrArg Subtype.val hpq
      refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
      have hcomm : ((a : Γ)⁻¹ * b) * t = t * ((a : Γ)⁻¹ * b) := by
        have e : ((a : Γ)⁻¹ * b) * t * ((a : Γ)⁻¹ * b)⁻¹ = t := by
          calc ((a : Γ)⁻¹ * b) * t * ((a : Γ)⁻¹ * b)⁻¹
              = (a : Γ)⁻¹ * ((b : Γ) * t * (b : Γ)⁻¹) * a := by group
            _ = (a : Γ)⁻¹ * ((a : Γ) * t * (a : Γ)⁻¹) * a := by rw [hab]
            _ = t := by group
        calc ((a : Γ)⁻¹ * b) * t = (((a : Γ)⁻¹ * b) * t * ((a : Γ)⁻¹ * b)⁻¹) * ((a : Γ)⁻¹ * b) := by
              group
          _ = t * ((a : Γ)⁻¹ * b) := by rw [e]
      exact h.hCt _ (mul_mem (inv_mem a.2) b.2) hcomm
    · rintro ⟨d, k, hk, rfl⟩
      exact ⟨Quotient.mk'' ⟨k, hk⟩, rfl⟩
  have hidx : Nat.card ↥(cls K t) = Kc.index := by
    rw [Subgroup.index, Nat.card_congr (Equiv.ofBijective φ hbij).symm]
  have := Subgroup.card_mul_index Kc
  rw [hKc, ← hidx] at this
  omega

theorem card_cls_modEq [Finite Γ] (h : KSetup U K x v t) : Nat.card ↥(cls K t) ≡ 1 [MOD 5] := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := card_modEq_commuting 5 h.hF.x5 (cls K t) (fun d hd => h.conj_mem_cls h.x_mem_K hd)
  have hset : {c : Γ | c ∈ cls K t ∧ x * c = c * x} = {t} := by
    ext c
    constructor
    · rintro ⟨hc, hxc⟩
      obtain ⟨u, hu, rfl⟩ := h.cls_subset hc
      have hxu : x * u * x⁻¹ = u := by
        have h1 : t * (x * u) = t * (u * x) := by
          calc t * (x * u) = (t * x) * u := by group
            _ = (x * t) * u := by rw [h.htx]
            _ = x * (t * u) := by group
            _ = (t * u) * x := hxc
            _ = t * (u * x) := by group
        have h2 : x * u = u * x := mul_left_cancel h1
        rw [h2]
        group
      have hu1 : u = 1 := h.hF.fpf u hu hxu
      rw [hu1, mul_one]
      rfl
    · intro hc
      rw [Set.mem_singleton_iff] at hc
      subst hc
      exact ⟨h.t_mem_cls, h.htx.symm⟩
  rw [hset, Set.ncard_singleton] at hmod
  exact hmod

theorem card_cls_le [Finite Γ] (h : KSetup U K x v t) : Nat.card ↥(cls K t) ≤ 16 := by
  have hsub : cls K t ⊆ (fun u => t * u) '' (U : Set Γ) := by
    intro d hd
    obtain ⟨u, hu, rfl⟩ := h.cls_subset hd
    exact ⟨u, hu, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ (mul_right_injective t)] at h1
  have h2 : (U : Set Γ).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact h.hF.card
  rw [Nat.card_coe_set_eq]
  omega

theorem two_le_card_cls [Finite Γ] (h : KSetup U K x v t) : 2 ≤ Nat.card ↥(cls K t) := by
  obtain ⟨u, hu, hu1, k, hk, hkt⟩ := h.h7
  have hne : t ≠ t * u := by
    intro he
    apply hu1
    have := mul_left_cancel (a := t) (b := 1) (c := u) (by rw [mul_one]; exact he)
    exact this.symm
  have hsub : ({t, t * u} : Set Γ) ⊆ cls K t := by
    intro d hd
    rcases hd with rfl | rfl
    · exact h.t_mem_cls
    · exact ⟨k, hk, hkt.symm⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hne] at h1
  rw [Nat.card_coe_set_eq]
  exact h1

theorem card_cls_ne_sixteen [Finite Γ] (h : KSetup U K x v t) : Nat.card ↥(cls K t) ≠ 16 := by
  intro h16
  obtain ⟨u, hu, hnot⟩ := h.hne
  have hsub : cls K t ⊆ (fun u => t * u) '' (U : Set Γ) := by
    intro d hd
    obtain ⟨u, hu, rfl⟩ := h.cls_subset hd
    exact ⟨u, hu, rfl⟩
  have hU : ((fun u => t * u) '' (U : Set Γ)).ncard = 16 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective t), ← Nat.card_coe_set_eq]
    exact h.hF.card
  have heq : cls K t = (fun u => t * u) '' (U : Set Γ) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hU, ← Nat.card_coe_set_eq, h16]) (Set.toFinite _)
  have hmem : t * u ∈ cls K t := by
    rw [heq]
    exact ⟨u, hu, rfl⟩
  obtain ⟨k, hk, hkt⟩ := hmem
  exact hnot k hk hkt.symm

theorem card_cls_ne_eleven [Finite Γ] (h : KSetup U K x v t) : Nat.card ↥(cls K t) ≠ 11 := by
  intro h11
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hK : Nat.card K = 11 * 640 := by
    rw [← h.card_cls_mul, h11]
  have hdvd : 11 ∣ Nat.card K := ⟨640, hK⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 11 hdvd
  have hgord : orderOf (g : Γ) = 11 := by rw [Subgroup.orderOf_coe]; exact hg
  have hg11 : (g : Γ) ^ 11 = 1 := by
    rw [← hgord]
    exact pow_orderOf_eq_one _
  have hgK : (g : Γ) ∈ K := g.2
  obtain ⟨hab, hcard⟩ := h.U0_data
  have hS : ∀ d ∈ ((U ⊔ zpowers t : Subgroup Γ) : Set Γ),
      (g : Γ) * d * (g : Γ)⁻¹ ∈ ((U ⊔ zpowers t : Subgroup Γ) : Set Γ) := fun d hd =>
    (mem_normalizer_iff.1 (h.hKN hgK) d).1 hd
  have hmod := card_modEq_commuting 11 hg11 ((U ⊔ zpowers t : Subgroup Γ) : Set Γ) hS
  have hD : {c : Γ | c ∈ ((U ⊔ zpowers t : Subgroup Γ) : Set Γ) ∧ (g : Γ) * c = c * (g : Γ)} =
      ((U ⊔ zpowers t) ⊓ centralizer ({(g : Γ)} : Set Γ) : Subgroup Γ) := by
    ext c
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hc, hgc⟩
      exact ⟨hc, hgc.symm⟩
    · rintro ⟨hc, hgc⟩
      exact ⟨hc, hgc.symm⟩
  rw [hD, ← Nat.card_coe_set_eq] at hmod
  have hmod' : 32 ≡ Nat.card ↥((U ⊔ zpowers t) ⊓ centralizer ({(g : Γ)} : Set Γ) : Subgroup Γ)
      [MOD 11] := by
    have e : Nat.card ↥(((U ⊔ zpowers t : Subgroup Γ) : Set Γ)) = 32 := hcard
    rw [e] at hmod
    exact hmod
  have hdiv : Nat.card ↥((U ⊔ zpowers t) ⊓ centralizer ({(g : Γ)} : Set Γ) : Subgroup Γ) ∣ 2 ^ 5 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : (U ⊔ zpowers t) ⊓ centralizer ({(g : Γ)} : Set Γ)
      ≤ U ⊔ zpowers t)
    rw [hcard] at this
    norm_num
    exact this
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv
  have hfull : Nat.card ↥((U ⊔ zpowers t) ⊓ centralizer ({(g : Γ)} : Set Γ) : Subgroup Γ) = 32 := by
    rw [hci] at hmod' ⊢
    interval_cases i <;> simp_all [Nat.ModEq]
  have hDeq : (U ⊔ zpowers t) ⊓ centralizer ({(g : Γ)} : Set Γ) = U ⊔ zpowers t :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hfull, hcard])
  have htU0 : t ∈ U ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hgt : (g : Γ) * t = t * (g : Γ) := by
    have : t ∈ (U ⊔ zpowers t) ⊓ centralizer ({(g : Γ)} : Set Γ) := by
      rw [hDeq]
      exact htU0
    exact (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 this).2).symm
  have hgC : (g : Γ) ∈ zpowers t ⊔ IsF20.Pgrp U x v := h.hCt _ hgK hgt
  have hdvd640 : orderOf (⟨(g : Γ), hgC⟩ : ↥(zpowers t ⊔ IsF20.Pgrp U x v)) ∣ 640 := by
    rw [← h.card_C]
    exact orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hgord] at hdvd640
  omega

theorem card_cls [Finite Γ] (h : KSetup U K x v t) : Nat.card ↥(cls K t) = 6 := by
  have h1 := h.card_cls_modEq
  have h2 := h.card_cls_le
  have h3 := h.two_le_card_cls
  have h4 := h.card_cls_ne_sixteen
  have h5 := h.card_cls_ne_eleven
  unfold Nat.ModEq at h1
  omega

theorem card_K [Finite Γ] (h : KSetup U K x v t) : Nat.card K = 3840 := by
  have := h.card_cls_mul
  rw [h.card_cls] at this
  omega

theorem centralizer_U0 [Finite Γ] (h : KSetup U K x v t) {k : Γ} (hk : k ∈ K)
    (hc : ∀ a ∈ U ⊔ zpowers t, k * a = a * k) : k ∈ U ⊔ zpowers t := by
  have htU0 : t ∈ U ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hkt : k * t = t * k := hc t htU0
  obtain ⟨a, p, hp, hkp⟩ := exists_zpow_mul_of_mem_sup h.t_comm_P (h.hCt k hk hkt)
  have hpk : p = (t ^ a)⁻¹ * k := by
    rw [hkp]
    group
  have hpU : p ∈ U := by
    refine h.hF.centralizer_Pgrp hp (fun u hu => ?_)
    have h1 : Commute (t ^ a) u := Commute.zpow_left (show Commute t u from h.htU u hu) a
    have h2 : Commute k u := hc u (mem_sup_left hu)
    rw [hpk]
    exact ((h1.inv_left).mul_left h2).eq
  rw [hkp]
  exact mul_mem (mem_sup_right (zpow_mem (mem_zpowers t) a)) (mem_sup_left hpU)

theorem centralizer_U [Finite Γ] (h : KSetup U K x v t) {k : Γ} (hk : k ∈ K)
    (hc : ∀ u ∈ U, k * u = u * k) : k ∈ U ⊔ zpowers t := by
  let T : Subgroup Γ :=
    { carrier := {u | u ∈ U ∧ ∃ k ∈ K, (∀ a ∈ U, k * a = a * k) ∧ k * t * k⁻¹ = t * u}
      one_mem' := ⟨one_mem U, 1, one_mem K, fun a _ => by simp, by simp⟩
      mul_mem' := by
        rintro u₁ u₂ ⟨hu₁, k₁, hk₁, hc₁, he₁⟩ ⟨hu₂, k₂, hk₂, hc₂, he₂⟩
        refine ⟨mul_mem hu₁ hu₂, k₁ * k₂, mul_mem hk₁ hk₂, fun a ha => ?_, ?_⟩
        · calc k₁ * k₂ * a = k₁ * (k₂ * a) := by group
            _ = k₁ * (a * k₂) := by rw [hc₂ a ha]
            _ = (k₁ * a) * k₂ := by group
            _ = (a * k₁) * k₂ := by rw [hc₁ a ha]
            _ = a * (k₁ * k₂) := by group
        · have hk₁u₂ : k₁ * u₂ * k₁⁻¹ = u₂ := by
            rw [hc₁ u₂ hu₂]
            group
          calc k₁ * k₂ * t * (k₁ * k₂)⁻¹ = k₁ * (k₂ * t * k₂⁻¹) * k₁⁻¹ := by group
            _ = k₁ * (t * u₂) * k₁⁻¹ := by rw [he₂]
            _ = (k₁ * t * k₁⁻¹) * (k₁ * u₂ * k₁⁻¹) := by group
            _ = (t * u₁) * u₂ := by rw [he₁, hk₁u₂]
            _ = t * (u₁ * u₂) := by group
      inv_mem' := by
        rintro u ⟨hu, k, hk, hck, he⟩
        refine ⟨inv_mem hu, k⁻¹, inv_mem hk, fun a ha => ?_, ?_⟩
        · have : Commute k a := hck a ha
          exact this.inv_left.eq
        · have hu' : k⁻¹ * u * k = u := by
            calc k⁻¹ * u * k = k⁻¹ * (u * k) := by group
              _ = k⁻¹ * (k * u) := by rw [hck u hu]
              _ = u := by group
          have e1 : k⁻¹ * (t * u) * k = t := by
            rw [← he]
            group
          have e3 : k⁻¹ * (t * u) * k = (k⁻¹ * t * k) * (k⁻¹ * u * k) := by group
          rw [e3, hu'] at e1
          have e2 : k⁻¹ * t * k = t * u⁻¹ := by
            calc k⁻¹ * t * k = ((k⁻¹ * t * k) * u) * u⁻¹ := by group
              _ = t * u⁻¹ := by rw [e1]
          simpa using e2 }
  have hTU : T ≤ U := fun u hu => hu.1
  have hTx : ∀ a ∈ T, x * a * x⁻¹ ∈ T := by
    rintro u ⟨hu, k', hk', hck', he'⟩
    have hxk : x * k' * x⁻¹ ∈ K := mul_mem (mul_mem h.x_mem_K hk') (inv_mem h.x_mem_K)
    refine ⟨h.hF.x_norm |> fun hx => (mem_normalizer_iff.1 hx u).1 hu, x * k' * x⁻¹, hxk,
      fun a ha => ?_, ?_⟩
    · have hxa : x⁻¹ * a * x ∈ U := by
        have := (mem_normalizer_iff.1 (inv_mem h.hF.x_norm)) a
        simpa using this.1 ha
      have h1 := hck' _ hxa
      calc x * k' * x⁻¹ * a = x * (k' * (x⁻¹ * a * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * a * x) * k') * x⁻¹ := by rw [h1]
        _ = a * (x * k' * x⁻¹) := by group
    · have hxt : x * t * x⁻¹ = t := by
        rw [← h.htx]
        group
      have hxt' : x⁻¹ * t * x = t := by
        calc x⁻¹ * t * x = x⁻¹ * (t * x) := by group
          _ = x⁻¹ * (x * t) := by rw [h.htx]
          _ = t := by group
      calc x * k' * x⁻¹ * t * (x * k' * x⁻¹)⁻¹
          = x * k' * (x⁻¹ * t * x) * k'⁻¹ * x⁻¹ := by group
        _ = x * k' * t * k'⁻¹ * x⁻¹ := by rw [hxt']
        _ = x * (k' * t * k'⁻¹) * x⁻¹ := by group
        _ = x * (t * u) * x⁻¹ := by rw [he']
        _ = (x * t * x⁻¹) * (x * u * x⁻¹) := by group
        _ = t * (x * u * x⁻¹) := by rw [hxt]
  have hcards := h.card_cls
  rcases h.eq_bot_or_top hTU hTx with hbot | htop
  ·
    obtain ⟨u, hu, hkt⟩ := h.hΔ k hk
    have huT : u ∈ T := ⟨hu, k, hk, hc, hkt⟩
    rw [hbot, Subgroup.mem_bot] at huT
    rw [huT, mul_one] at hkt
    have hkt' : k * t = t * k := by
      calc k * t = (k * t * k⁻¹) * k := by group
        _ = t * k := by rw [hkt]
    refine h.centralizer_U0 hk (fun a ha => ?_)
    rcases (mem_sup_zpowers_iff_of_comm_invol h.htt h.htU).1 ha with haU | hta
    · exact hc a haU
    · have h1 : k * (t * a) = (t * a) * k := hc _ hta
      have h2 : t * (k * a) = t * (a * k) := by
        calc t * (k * a) = (t * k) * a := by group
          _ = (k * t) * a := by rw [hkt']
          _ = k * (t * a) := by group
          _ = (t * a) * k := h1
          _ = t * (a * k) := by group
      exact mul_left_cancel h2
  ·
    exfalso
    have hsub : (fun u => t * u) '' (U : Set Γ) ⊆ cls K t := by
      rintro _ ⟨u, hu, rfl⟩
      have huT : u ∈ T := by rw [htop]; exact hu
      obtain ⟨-, k', hk', -, he⟩ := huT
      exact ⟨k', hk', he.symm⟩
    have h2 : (U : Set Γ).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]
      exact h.hF.card
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_image_of_injective _ (mul_right_injective t), h2, ← Nat.card_coe_set_eq,
      hcards] at h1
    omega

theorem closure_cls [Finite Γ] (h : KSetup U K x v t) :
    Subgroup.closure (cls K t) = U ⊔ zpowers t := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro d hd
    obtain ⟨u, hu, rfl⟩ := h.cls_subset hd
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hu)
  · have hxCl : ∀ a ∈ Subgroup.closure (cls K t), x * a * x⁻¹ ∈ Subgroup.closure (cls K t) := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem a ha => exact Subgroup.subset_closure (h.conj_mem_cls h.x_mem_K ha)
      | one => simpa using one_mem _
      | mul a b _ _ iha ihb =>
        have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
        rw [this]
        exact mul_mem iha ihb
      | inv a _ iha =>
        have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
        rw [this]
        exact inv_mem iha
    have hTU : Subgroup.closure (cls K t) ⊓ U ≤ U := inf_le_right
    have hTx : ∀ a ∈ Subgroup.closure (cls K t) ⊓ U, x * a * x⁻¹ ∈ Subgroup.closure (cls K t) ⊓ U := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.1 ha
      exact Subgroup.mem_inf.2 ⟨hxCl a ha1, (mem_normalizer_iff.1 h.hF.x_norm a).1 ha2⟩
    have htcl : t ∈ Subgroup.closure (cls K t) := Subgroup.subset_closure h.t_mem_cls
    have hUle : U ≤ Subgroup.closure (cls K t) := by
      rcases h.eq_bot_or_top hTU hTx with hbot | htop
      · exfalso
        obtain ⟨u, hu, hu1, k, hk, hkt⟩ := h.h7
        have hmem : u ∈ Subgroup.closure (cls K t) ⊓ U := by
          refine Subgroup.mem_inf.2 ⟨?_, hu⟩
          have h2 : t * u ∈ Subgroup.closure (cls K t) := Subgroup.subset_closure ⟨k, hk, hkt.symm⟩
          have := mul_mem htcl h2
          rwa [← mul_assoc, h.htt, one_mul] at this
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hu1 hmem
      · intro u hu
        have : u ∈ Subgroup.closure (cls K t) ⊓ U := by
          rw [htop]
          exact hu
        exact (Subgroup.mem_inf.1 this).1
    exact sup_le hUle ((Subgroup.zpowers_le).2 htcl)

theorem kernel_cls [Finite Γ] (h : KSetup U K x v t) {k : Γ} (hk : k ∈ K)
    (hc : ∀ d ∈ cls K t, k * d * k⁻¹ = d) : k ∈ U ⊔ zpowers t := by
  refine h.centralizer_U0 hk (fun a ha => ?_)
  rw [← h.closure_cls] at ha
  have hle : Subgroup.closure (cls K t) ≤ centralizer ({k} : Set Γ) := by
    rw [Subgroup.closure_le]
    intro d hd
    refine mem_centralizer_singleton_iff.2 ?_
    have h1 := hc d hd
    calc d * k = (k * d * k⁻¹) * k := by rw [h1]
      _ = k * d := by group
  exact (mem_centralizer_singleton_iff.1 (hle ha)).symm

theorem v_sq_not_mem [Finite Γ] (h : KSetup U K x v t) : v ^ 2 ∉ U ⊔ zpowers t := by
  intro hmem
  rcases (mem_sup_zpowers_iff_of_comm_invol h.htt h.htU).1 hmem with hU | hU
  · have h1 : v ^ 2 ∈ U ⊓ (zpowers x ⊔ zpowers v : Subgroup Γ) :=
      Subgroup.mem_inf.2 ⟨hU, (Subgroup.pow_mem _ (mem_sup_right (mem_zpowers v)) 2)⟩
    rw [h.hF.U_inf_F, Subgroup.mem_bot] at h1
    exact h.hF.sq_ne_one h1
  · have htP : t ∈ IsF20.Pgrp U x v := by
      have h1 : (t * v ^ 2) * (v ^ 2)⁻¹ = t := by group
      rw [← h1]
      refine mul_mem (IsF20.U_le_Pgrp U x v hU) (inv_mem ?_)
      exact mem_sup_right (Subgroup.pow_mem _ (mem_sup_right (mem_zpowers v)) 2)
    exact h.htnU (h.hF.centralizer_Pgrp htP h.htU)

end KSetup

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst
