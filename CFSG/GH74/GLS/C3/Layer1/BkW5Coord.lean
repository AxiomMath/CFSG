module

public import CFSG.GH74.GLS.C3.Layer1.BkP46W
public import CFSG.GH74.GLS.C3.Layer2.CentralizerModel
public import CFSG.GH74.GLS.C3.Layer2.L5A1
public import CFSG.GH74.GLS.C3.Prop121.G5Iota

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.W5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
open scoped commutatorElement
open CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem card_T (h : IsAConfigW 5 x K T Q S a) : Nat.card ↥T = 32 := by
  obtain ⟨y, hyT, hyy, hyR, hTcases, q₀, hq₀, hyq₀⟩ := Bk.aconfigW_five_y h
  obtain ⟨hRel, hRcard⟩ := Bk.aconfigW_five_R h
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left h.Q_le_T
  have hle : Nat.card ↥T ≤ 2 * Nat.card ↥((T ⊓ K) ⊔ Q) := by
    refine Bk.card_le_two_mul_of_cover (e := y) (fun t ht => ?_)
    rcases hTcases t ht with h1 | ⟨r, hr, rfl⟩
    · exact Or.inl h1
    · right
      have e : r * y * y⁻¹ = r := by group
      rw [e]
      exact hr
  have hdvd : Nat.card ↥((T ⊓ K) ⊔ Q) ∣ Nat.card ↥T := Subgroup.card_dvd_of_le hRT
  have hne : Nat.card ↥((T ⊓ K) ⊔ Q) ≠ Nat.card ↥T := by
    intro heq
    have h1 := Subgroup.eq_of_le_of_card_ge hRT (le_of_eq heq.symm)
    apply hyR
    rw [h1]
    exact hyT
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  rw [hRcard] at hdvd hne hle
  obtain ⟨m, hm⟩ := hdvd
  omega


abbrev Wc (x : G) : Subgroup ↥(centralizer ({x} : Set G)) := pPrimeCore 2 ↥(centralizer ({x} : Set G))

omit [Finite G] in
theorem mem_Wc {c : ↥(centralizer ({x} : Set G))} :
    c ∈ Wc x ↔ (c : G) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
  rw [Setup91.mem_pPrimeCoreOf_iff]
  exact ⟨fun hc => ⟨c.2, hc⟩, fun ⟨_, hc⟩ => hc⟩

theorem W_odd (x : G) : Odd (Nat.card ↥(pPrimeCoreOf 2 (centralizer ({x} : Set G)))) :=
  TwoThin.card_pPrimeCoreOf_odd _

omit [Finite G] in
theorem W_norm {c w : G} (hc : c ∈ centralizer ({x} : Set G))
    (hw : w ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G))) :
    c * w * c⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) :=
  TwoThin.pPrimeCoreOf_normalized _ hc hw

theorem W_orderOf_odd {w : G} (hw : w ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G))) :
    Odd (orderOf w) := odd_orderOf_of_mem_pPrimeCoreOf hw

section Odd

variable (h : IsAConfigW 5 x K T Q S a)
include h

theorem T_inf_W : T ⊓ pPrimeCoreOf 2 (centralizer ({x} : Set G)) = ⊥ :=
  Setup91.inf_pPrimeCoreOf_eq_bot _ h.sylowT.isPGroup

theorem Q_inf_W : Q ⊓ pPrimeCoreOf 2 (centralizer ({x} : Set G)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : z ∈ T ⊓ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := ⟨h.Q_le_T hz.1, hz.2⟩
  rw [T_inf_W h] at this
  exact this

end Odd


section Psi

variable (h : IsAConfigW 5 x K T Q S a)

theorem exists_psi :
    ∃ (e5 : kBar K ≃* alternatingGroup (Fin 5)) (ψ : ↥(centralizer ({x} : Set G)) →* Perm (Fin 5)),
      ψ.ker = (CxK x K).subgroupOf (centralizer ({x} : Set G)) ∧
      (∀ (k : G) (hk : k ∈ K), ψ ⟨k, h.K_le_C hk⟩ =
        ((e5 (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) : alternatingGroup (Fin 5)) : Perm (Fin 5))) ∧
      ψ.range = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e5⟩ := h.kbar
  obtain ⟨ψ, hker, hψK⟩ :=
    lemma113d_alt h.K_le_C h.normalInC (n := 5) (by norm_num) (by norm_num) e5
  refine ⟨e5, ψ, hker, hψK, ?_⟩
  have hA5 : alternatingGroup (Fin 5) ≤ ψ.range := by
    intro σ hσ
    obtain ⟨k', hk'⟩ := e5.surjective ⟨σ, hσ⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k'
    refine ⟨⟨(k : G), h.K_le_C k.2⟩, ?_⟩
    rw [hψK (k : G) k.2]
    have : (⟨(k : G), k.2⟩ : ↥K) = k := rfl
    rw [this, hk']
  set f : ↥T →* Perm (Fin 5) := ψ.comp (Subgroup.inclusion h.T_le_C) with hf
  have hkerf : f.ker = Q.subgroupOf T := by
    ext ⟨t, ht⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : (⟨t, h.T_le_C ht⟩ : ↥(centralizer ({x} : Set G))) ∈ ψ.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      rw [h.hQ]
      exact ⟨ht, h2⟩
    · intro h1
      have h2 : t ∈ CxK x K := h.Q_le_CxK h1
      have h3 : (⟨t, h.T_le_C ht⟩ : ↥(centralizer ({x} : Set G))) ∈ ψ.ker := by
        rw [hker, Subgroup.mem_subgroupOf]
        exact h2
      exact h3
  have hcardf : Nat.card f.range = 8 := by
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hkerf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q_le_T).toEquiv, h.card_Q,
      card_T h] at h1
    omega
  have hfle : f.range ≤ ψ.range := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  have h8 : 8 ∣ Nat.card ψ.range := hcardf ▸ Subgroup.card_dvd_of_le hfle
  have h60 : 60 ∣ Nat.card ψ.range := by
    have hA : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    exact hA ▸ Subgroup.card_dvd_of_le hA5
  have hle : Nat.card ψ.range ≤ 120 := by
    have hP : Nat.card (Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    exact hP ▸ Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_subgroup_dvd_card _)
  have hpos : 0 < Nat.card ψ.range := Nat.card_pos
  have h120 : Nat.card ψ.range = 120 := by omega
  apply Subgroup.eq_top_of_card_eq
  rw [h120]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

end Psi


abbrev Ct (x : G) : Type := ↥(centralizer ({x} : Set G)) ⧸ Wc x

abbrev piC (x : G) : ↥(centralizer ({x} : Set G)) →* Ct x := QuotientGroup.mk' (Wc x)

omit [Finite G] in
theorem piC_eq_one_iff {c : ↥(centralizer ({x} : Set G))} : piC x c = 1 ↔ c ∈ Wc x :=
  QuotientGroup.eq_one_iff c

section CxKQW

variable (h : IsAConfigW 5 x K T Q S a)
include h

theorem piC_inj_Q {q₁ q₂ : ↥(centralizer ({x} : Set G))} (h₁ : (q₁ : G) ∈ Q) (h₂ : (q₂ : G) ∈ Q)
    (hq : piC x q₁ = piC x q₂) : q₁ = q₂ := by
  have h1 : q₂⁻¹ * q₁ ∈ Wc x := by
    rw [← piC_eq_one_iff, map_mul, map_inv, hq, inv_mul_cancel]
  have h2 : ((q₂⁻¹ * q₁ : ↥(centralizer ({x} : Set G))) : G) ∈ Q ⊓
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) :=
    ⟨by simpa using Q.mul_mem (Q.inv_mem h₂) h₁, mem_Wc.1 h1⟩
  rw [Q_inf_W h, Subgroup.mem_bot] at h2
  have h3 : (q₂ : G)⁻¹ * q₁ = 1 := h2
  exact Subtype.ext (inv_mul_eq_one.1 h3).symm

theorem card_piQ :
    Nat.card ↥(((Q.subgroupOf (centralizer ({x} : Set G))).map (piC x))) = 4 := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Q₀ : Subgroup ↥C := Q.subgroupOf C with hQ₀
  have h4 : Nat.card ↥Q₀ = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.Q_le_T.trans h.T_le_C)).toEquiv).trans
      h.card_Q
  rw [← h4]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun q : ↥Q₀ =>
    (⟨piC x q, Subgroup.mem_map_of_mem _ q.2⟩ : ↥(Q₀.map (piC x)))) ⟨fun q₁ q₂ hq => ?_, ?_⟩
  · have := congrArg Subtype.val hq
    exact Subtype.ext (piC_inj_Q h (Subgroup.mem_subgroupOf.1 q₁.2)
      (Subgroup.mem_subgroupOf.1 q₂.2) this)
  · rintro ⟨z, hz⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hz
    exact ⟨⟨u, hu⟩, rfl⟩

theorem CxK_le_Q_W {c : G} (hc : c ∈ CxK x K) :
    ∃ q ∈ Q, q⁻¹ * c ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set X₀ : Subgroup ↥C := (CxK x K).subgroupOf C with hX₀
  set Q₀ : Subgroup ↥C := Q.subgroupOf C with hQ₀
  have hCxKC : CxK x K ≤ C := IsAConfigW.CxK_le_C
  have hW_le_X₀ : Wc x ≤ X₀ := fun w hw => Subgroup.mem_subgroupOf.2 (h.W_le_CxK (mem_Wc.1 hw))
  have hQ₀X₀ : Q₀ ≤ X₀ := fun q hq =>
    Subgroup.mem_subgroupOf.2 (h.Q_le_CxK (Subgroup.mem_subgroupOf.1 hq))
  have h2grp : IsPGroup 2 ↥(X₀.map (piC x)) := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨z, hz⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf u)
      (orderOf_pos u).ne'
    have hpow : orderOf (u ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (by positivity) (hord ▸ dvd_mul_right _ _), hord]
      simp [Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ k)]
    have huC : ((u : ↥C) : G) ∈ CxK x K := Subgroup.mem_subgroupOf.1 hu
    have hupow : (((u ^ (2 ^ k) : ↥C)) : G) ∈ CxK x K := by
      rw [Subgroup.coe_pow]
      exact (CxK x K).pow_mem huC _
    have hodd' : Odd (orderOf (((u ^ (2 ^ k) : ↥C)) : G)) := by
      rw [Subgroup.orderOf_coe, hpow]
      exact hm
    have hW : u ^ (2 ^ k) ∈ Wc x := mem_Wc.2 (h.odd_mem_W hupow hodd')
    have h1 : (piC x u) ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      exact (piC_eq_one_iff).2 hW
    have h2 : orderOf (piC x u) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    exact ⟨j, by rw [Subgroup.orderOf_mk]; exact hj⟩
  let g : ↥X₀ →* Ct x := (piC x).comp X₀.subtype
  have hker : g.ker = (Wc x).subgroupOf X₀ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact piC_eq_one_iff
  have hrange : g.range = X₀.map (piC x) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  have hcard := Subgroup.card_ker_mul_card_range g
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_X₀).toEquiv] at hcard
  have hX₀card : Nat.card ↥X₀ = Nat.card ↥(CxK x K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCxKC).toEquiv
  have hWodd : Odd (Nat.card ↥(Wc x)) := Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have hv2 : (Nat.card ↥(CxK x K)).factorization 2 = 2 := by
    have h1 := h.sylowQ.card_eq
    rw [h.card_Q] at h1
    have : (2 : ℕ) ^ 2 = 2 ^ (Nat.card ↥(CxK x K)).factorization 2 := by rw [← h1]; norm_num
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  obtain ⟨b, hb⟩ := h2grp.exists_card_eq
  have hb2 : b = 2 := by
    rw [hb, hX₀card] at hcard
    have h1 := congrArg (fun n => n.factorization 2) hcard
    rw [Nat.factorization_mul (Nat.card_pos).ne' (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by
        rintro ⟨c', hc'⟩
        rw [hc'] at hWodd
        exact (Nat.not_even_iff_odd.2 hWodd) ⟨c', by ring⟩), hv2] at h1
    simpa using h1
  have hQ₀card : Nat.card ↥(Q₀.map (piC x)) = 4 := card_piQ h
  have hle : Q₀.map (piC x) ≤ X₀.map (piC x) := Subgroup.map_mono hQ₀X₀
  have heq : Q₀.map (piC x) = X₀.map (piC x) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hb, hb2, hQ₀card]
    norm_num
  have hcmem : (⟨c, hCxKC hc⟩ : ↥C) ∈ X₀ := Subgroup.mem_subgroupOf.2 hc
  have : piC x ⟨c, hCxKC hc⟩ ∈ Q₀.map (piC x) := by
    rw [heq]
    exact Subgroup.mem_map_of_mem _ hcmem
  obtain ⟨q, hq, hqc⟩ := Subgroup.mem_map.1 this
  refine ⟨(q : G), Subgroup.mem_subgroupOf.1 hq, ?_⟩
  have h1 : q⁻¹ * ⟨c, hCxKC hc⟩ ∈ Wc x := (QuotientGroup.eq).1 hqc
  exact mem_Wc.1 h1

theorem WK_le_W : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
  refine Setup91.le_pPrimeCoreOf_of_normalized ((TwoThin.pPrimeCoreOf_le K).trans h.K_le_C) ?_
    (TwoThin.card_pPrimeCoreOf_odd K)
  intro c hc w hw
  exact U1a.mem_normalizer_pPrimeCoreOf h.normalInC hc |> fun hn =>
    (Subgroup.mem_normalizer_iff.1 hn w).1 hw

omit h in
theorem Wc_le_ker (h : IsAConfigW 5 x K T Q S a)
    (ψ : ↥(centralizer ({x} : Set G)) →* Perm (Fin 5))
    (hker : ψ.ker = (CxK x K).subgroupOf (centralizer ({x} : Set G))) : Wc x ≤ ψ.ker := fun w hw => by
  rw [hker, Subgroup.mem_subgroupOf]
  exact h.W_le_CxK (mem_Wc.1 hw)

theorem exists_coord0 :
    ∃ co : ↥(centralizer ({x} : Set G)) →* ↥(Fgrp 5), Function.Surjective co ∧
      (∀ c, co c = 1 ↔ c ∈ Wc x) ∧ ((co (xC x) : Fgrp 5) : Amb 5) = x0 5 ∧
      (∀ c, (((co c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ CxK x K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  obtain ⟨e5, ψ, hker, hψK, hrange⟩ := exists_psi h
  let ψt : Ct x →* Perm (Fin 5) := QuotientGroup.lift (Wc x) ψ (fun w hw => Wc_le_ker h ψ hker hw)
  have hψt : ∀ c, ψt (piC x c) = ψ c := fun c => rfl
  have hQC : ∀ {q : G}, q ∈ Q → q ∈ C := fun hq => h.T_le_C (h.Q_le_T hq)
  have hkerψt : ψt.ker = (Q.subgroupOf C).map (piC x) := by
    ext z
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Wc x) z
    rw [MonoidHom.mem_ker, hψt]
    constructor
    · intro h1
      have h2 : c ∈ ψ.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      obtain ⟨q, hq, hqW⟩ := CxK_le_Q_W h h2
      refine ⟨⟨q, hQC hq⟩, Subgroup.mem_subgroupOf.2 hq, ?_⟩
      show piC x ⟨q, hQC hq⟩ = piC x c
      apply (QuotientGroup.eq).2
      exact mem_Wc.2 hqW
    · rintro ⟨q, hq, hqc⟩
      have : (q : G) ∈ CxK x K := h.Q_le_CxK (Subgroup.mem_subgroupOf.1 hq)
      have h3 : q ∈ ψ.ker := by rw [hker]; exact Subgroup.mem_subgroupOf.2 this
      have h4 : ψ q = 1 := h3
      have h5 : piC x c = piC x q := hqc.symm
      rw [← hψt c, h5, hψt q, h4]
  have hrangeψt : ψt.range = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    have : σ ∈ ψ.range := by rw [hrange]; exact Subgroup.mem_top _
    obtain ⟨c, rfl⟩ := this
    exact ⟨piC x c, rfl⟩
  have hKn : (K.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.K_le_C).mpr (Bk.aconfigW_C_le_normalizer h)
  let K' : Subgroup (Ct x) := (K.subgroupOf C).map (piC x)
  have hK'n : K'.Normal := hKn.map (piC x) (QuotientGroup.mk'_surjective _)
  let Q' : Subgroup (Ct x) := (Q.subgroupOf C).map (piC x)
  have hQ'ker : Q' = ψt.ker := hkerψt.symm
  have hQ'n : Q'.Normal := hQ'ker ▸ MonoidHom.normal_ker ψt
  let Φ : kBar K →* Ct x := QuotientGroup.lift (pPrimeCore 2 ↥K)
    ((piC x).comp (Subgroup.inclusion h.K_le_C)) (fun k hk => by
      have hk' : (k : G) ∈ pPrimeCoreOf 2 K := Setup91.mem_pPrimeCoreOf_iff.2 ⟨k.2, hk⟩
      exact piC_eq_one_iff.2 (mem_Wc.2 (WK_le_W h hk')))
  have hΦ : ∀ k : ↥K, Φ (QuotientGroup.mk k) = piC x ⟨k, h.K_le_C k.2⟩ := fun k => rfl
  have hΦinj : Function.Injective Φ := by
    have hs : IsSimpleGroup (kBar K) := e5.isSimpleGroup
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hs.eq_bot_or_eq_top_of_normal Φ.ker with hb | ht
    · exact hb
    · exfalso
      obtain ⟨hPcard, hPel⟩ := Bk.aconfigW_five_P h
      obtain ⟨u, hu, hu1⟩ : ∃ u ∈ T ⊓ K, u ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : T ⊓ K = ⊥ := eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 (hcon z hz)
        rw [this, Subgroup.card_bot] at hPcard
        omega
      have hmem : (QuotientGroup.mk (⟨u, hu.2⟩ : ↥K) : kBar K) ∈ Φ.ker := by rw [ht]; trivial
      have h1 : Φ (QuotientGroup.mk (⟨u, hu.2⟩ : ↥K)) = 1 := hmem
      rw [hΦ] at h1
      have h2 : (⟨u, h.K_le_C hu.2⟩ : ↥C) ∈ Wc x := piC_eq_one_iff.1 h1
      have h3 := W_orderOf_odd (mem_Wc.1 h2)
      obtain ⟨hPc, hPs⟩ := forall_of_isElementaryAbelian hPel
      have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hPs u hu) hu1
      rw [hu2] at h3
      exact absurd h3 (by decide)
  have hrangeΦ : Φ.range = K' := by
    ext z
    constructor
    · rintro ⟨k', rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k'
      exact ⟨⟨k, h.K_le_C k.2⟩, Subgroup.mem_subgroupOf.2 k.2, (hΦ k).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨QuotientGroup.mk ⟨u, Subgroup.mem_subgroupOf.1 hu⟩, hΦ _⟩
  let eK : ↥K' ≃* ↥(alternatingGroup (Fin 5)) :=
    ((MulEquiv.subgroupCongr hrangeΦ.symm).trans (MonoidHom.ofInjective hΦinj).symm).trans e5
  obtain ⟨hQc, hQs⟩ := forall_of_isElementaryAbelian h.elemQ
  have hQcard' : Nat.card Q' = 4 := card_piQ h
  have hQe : ∀ q ∈ Q', q ^ 2 = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' := Subgroup.mem_subgroupOf.1 hu
    rw [← map_pow]
    have : u ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact hQs _ hu')
    rw [this, map_one]
  have hQab : ∀ q ∈ Q', ∀ r ∈ Q', q * r = r * q := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hQc _ (Subgroup.mem_subgroupOf.1 hu) _ (Subgroup.mem_subgroupOf.1 hv))
  have hKQ : ∀ k ∈ K', ∀ q ∈ Q', k * q = q * k := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨u, hu, rfl⟩
    have hk' := Subgroup.mem_subgroupOf.1 hk
    have hu' := Subgroup.mem_subgroupOf.1 hu
    have hc : ⁅(k : G), (u : G)⁆ ∈ pPrimeCoreOf 2 K := (h.Q_le_CxK hu').2.2.2 (k : G) hk'
    have h1 : ((⁅k, u⁆ : ↥C) : G) ∈ pPrimeCoreOf 2 C := WK_le_W h (by
      have : ((⁅k, u⁆ : ↥C) : G) = ⁅(k : G), (u : G)⁆ := rfl
      rw [this]; exact hc)
    have h2 : piC x ⁅k, u⁆ = 1 := piC_eq_one_iff.2 (mem_Wc.2 h1)
    rw [commutatorElement_def, map_mul, map_mul, map_inv, map_inv] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.1 (by
      rw [commutatorElement_def]; exact h2))
  have hxQ : piC x (xC x) ∈ Q' := ⟨xC x, Subgroup.mem_subgroupOf.2 h.x_mem_Q, rfl⟩
  have hx1 : piC x (xC x) ≠ 1 := by
    intro h1
    have h2 : xC x ∈ Wc x := piC_eq_one_iff.1 h1
    have h3 := W_orderOf_odd (mem_Wc.1 h2)
    have : orderOf (xC x : G) = 2 := h.x_order
    rw [show ((xC x : ↥C) : G) = x from rfl, h.x_order] at h3
    exact absurd h3 (by decide)
  have hxc : ∀ c : Ct x, c * piC x (xC x) = piC x (xC x) * c := by
    intro c
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Wc x) c
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 u.2)
  have hnt : ∃ c : Ct x, ∃ q ∈ Q', c * q ≠ q * c := by
    obtain ⟨y, hyT, hyy, hyR, hTcases, q₀, hq₀, hyq₀⟩ := Bk.aconfigW_five_y h
    refine ⟨piC x ⟨y, h.T_le_C hyT⟩, piC x ⟨q₀, hQC hq₀⟩,
      ⟨⟨q₀, hQC hq₀⟩, Subgroup.mem_subgroupOf.2 hq₀, rfl⟩, fun hcomm => hyq₀ ?_⟩
    have h1 : piC x ⟨y * q₀ * y⁻¹ * q₀⁻¹, mul_mem (mul_mem (mul_mem (h.T_le_C hyT) (hQC hq₀))
        (inv_mem (h.T_le_C hyT))) (inv_mem (hQC hq₀))⟩ = 1 := by
      have : (⟨y * q₀ * y⁻¹ * q₀⁻¹, _⟩ : ↥C) = ⟨y, h.T_le_C hyT⟩ * ⟨q₀, hQC hq₀⟩ *
          ⟨y, h.T_le_C hyT⟩⁻¹ * ⟨q₀, hQC hq₀⟩⁻¹ := rfl
      rw [this]
      simp only [map_mul, map_inv, hcomm]
      group
    have h2 := piC_eq_one_iff.1 h1
    have h3 : y * q₀ * y⁻¹ * q₀⁻¹ ∈ Q := Q.mul_mem (Bk.aconfigW_Q_norm h y hyT q₀ hq₀)
      (Q.inv_mem hq₀)
    have h4 : y * q₀ * y⁻¹ * q₀⁻¹ ∈ Q ⊓ pPrimeCoreOf 2 C := ⟨h3, mem_Wc.1 h2⟩
    rw [Q_inf_W h, Subgroup.mem_bot] at h4
    have h5 : y * q₀ * y⁻¹ * q₀⁻¹ = 1 := h4
    have h6 : y * q₀ = q₀ * y := by
      have := mul_inv_eq_one.1 h5
      calc y * q₀ = y * q₀ * y⁻¹ * y := by group
        _ = q₀ * y := by rw [mul_inv_eq_one.1 h5]
    exact h6
  obtain ⟨ι, hι1, hιψ⟩ := exists_mulEquiv_fgrp (n := 5) (by norm_num) K' Q' eK ψt hkerψt hrangeψt
    hQcard' hQe hQab hKQ (x := piC x (xC x)) hxQ hx1 hxc hnt
  refine ⟨ι.toMonoidHom.comp (piC x), ?_, ?_, ?_, ?_⟩
  · intro p
    obtain ⟨z, hz⟩ := ι.surjective p
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Wc x) z
    exact ⟨c, hz⟩
  · intro c
    show ι (piC x c) = 1 ↔ _
    rw [show ι (piC x c) = 1 ↔ piC x c = 1 from ⟨fun h1 => ι.injective (h1.trans (map_one ι).symm),
      fun h1 => by rw [h1, map_one]⟩]
    exact piC_eq_one_iff
  · exact hι1
  · intro c
    show ((ι (piC x c) : Fgrp 5) : Amb 5).1 = 1 ↔ _
    rw [hιψ, hψt]
    constructor
    · intro h1
      have h2 : c ∈ ψ.ker := h1
      rw [hker, Subgroup.mem_subgroupOf] at h2
      exact h2
    · intro h1
      have h2 : c ∈ ψ.ker := by rw [hker]; exact Subgroup.mem_subgroupOf.2 h1
      exact h2

theorem exists_coord1 :
    ∃ co : ↥(centralizer ({x} : Set G)) →* ↥(Fgrp 5), Function.Surjective co ∧
      (∀ c, co c = 1 ↔ c ∈ Wc x) ∧ ((co (xC x) : Fgrp 5) : Amb 5) = x0 5 ∧
      (∀ c, (((co c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ CxK x K)) ∧
      (∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ T → ((co c : Fgrp 5) : Amb 5) ∈ T5) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  obtain ⟨co₀, hsurj, hker, hx, hQ⟩ := exists_coord0 h
  obtain ⟨P0, hP0⟩ := isSylow_T5
  set Tm : Subgroup ↥(Fgrp 5) := (T.subgroupOf C).map co₀ with hTm
  have hTinj : ∀ t₁ t₂ : ↥C, (t₁ : G) ∈ T → (t₂ : G) ∈ T → co₀ t₁ = co₀ t₂ → t₁ = t₂ := by
    intro t₁ t₂ h₁ h₂ hc
    have h1 : t₂⁻¹ * t₁ ∈ Wc x := by
      rw [← hker, map_mul, map_inv, hc, inv_mul_cancel]
    have h2 : ((t₂⁻¹ * t₁ : ↥C) : G) ∈ T ⊓ pPrimeCoreOf 2 C :=
      ⟨by simpa using T.mul_mem (T.inv_mem h₂) h₁, mem_Wc.1 h1⟩
    rw [T_inf_W h, Subgroup.mem_bot] at h2
    have h3 : (t₂ : G)⁻¹ * t₁ = 1 := h2
    exact Subtype.ext (inv_mul_eq_one.1 h3).symm
  have hTmcard : Nat.card ↥Tm = 32 := by
    rw [← card_T h]
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.T_le_C).toEquiv]
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective (fun t : ↥(T.subgroupOf C) =>
      (⟨co₀ t, Subgroup.mem_map_of_mem _ t.2⟩ : ↥Tm)) ⟨fun t₁ t₂ hq => ?_, ?_⟩
    · exact Subtype.ext (hTinj t₁ t₂ (Subgroup.mem_subgroupOf.1 t₁.2) (Subgroup.mem_subgroupOf.1 t₂.2)
        (congrArg Subtype.val hq))
    · rintro ⟨z, hz⟩
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hz
      exact ⟨⟨u, hu⟩, rfl⟩
  have hTmSyl : IsSylowOf 2 Tm ⊤ := by
    refine isSylowOf_of_card le_top ?_
    have hcardF : (Nat.card (Fgrp 5)).factorization 2 = 5 := by
      rw [card_Fgrp_eq, Nat.factorization_def _ Nat.prime_two]
      decide +kernel
    rw [Nat.card_congr (Subgroup.topEquiv (G := ↥(Fgrp 5))).toEquiv, hcardF, hTmcard]
    norm_num
  have hP0' : IsSylowOf 2 (P0 : Subgroup (Fgrp 5)) ⊤ :=
    isSylowOf_iff.2 ⟨le_top, P0.isPGroup', by
      rw [Subgroup.relIndex_top_right]; exact P0.not_dvd_index⟩
  obtain ⟨g, -, hg⟩ := hTmSyl.exists_mem_conj hP0'
  have hP0mem : ∀ y : Fgrp 5, y ∈ (P0 : Subgroup (Fgrp 5)) ↔ ((y : Fgrp 5) : Amb 5) ∈ T5 := by
    intro y
    rw [← hP0]
    exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).symm
  refine ⟨(MulAut.conj g).toMonoidHom.comp co₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    obtain ⟨c, hc⟩ := hsurj (g⁻¹ * p * g)
    exact ⟨c, by show g * co₀ c * g⁻¹ = p; rw [hc]; group⟩
  · intro c
    show g * co₀ c * g⁻¹ = 1 ↔ _
    rw [← hker]
    constructor
    · intro h1
      have : co₀ c = g⁻¹ * (g * co₀ c * g⁻¹) * g := by group
      rw [this, h1]; group
    · intro h1
      rw [h1]; group
  · show ((g * co₀ (xC x) * g⁻¹ : Fgrp 5) : Amb 5) = x0 5
    have hcen := x0_central_aux 5 g.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hx, hcen, mul_inv_cancel_right]
  · intro c
    rw [← hQ c]
    show ((g * co₀ c * g⁻¹ : Fgrp 5) : Amb 5).1 = 1 ↔ _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv]
    exact conj_eq_one_iff
  · intro c hcT
    show ((g * co₀ c * g⁻¹ : Fgrp 5) : Amb 5) ∈ T5
    rw [← hP0mem, hg]
    have : g⁻¹ * (g * co₀ c * g⁻¹) * g = co₀ c := by group
    rw [this]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hcT)

theorem co_K_snd
    (co : ↥(centralizer ({x} : Set G)) →* ↥(Fgrp 5)) (hsurj : Function.Surjective co)
    (hker : ∀ c, co c = 1 ↔ c ∈ Wc x)
    (hQ : ∀ c, (((co c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ CxK x K)) {k : ↥(centralizer ({x} : Set G))}
    (hk : (k : G) ∈ K) : ((co k : Fgrp 5) : Amb 5).2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e5⟩ := h.kbar
  have hcomm : ∀ (k : ↥(centralizer ({x} : Set G))), (k : G) ∈ K → ∀ f : Amb 5, f ∈ Qm → ((co k : Fgrp 5) : Amb 5).2 * f.2 =
      f.2 * ((co k : Fgrp 5) : Amb 5).2 := by
    intro k hk f hf
    obtain ⟨c, hc⟩ := hsurj ⟨f, Qm_le_Fgrp hf⟩
    have hc1 : ((co c : Fgrp 5) : Amb 5).1 = 1 := by
      rw [hc]
      exact ((Qm_coord (Qm_le_T5 hf)).2 hf)
    have hcCxK : (c : G) ∈ CxK x K := (hQ c).1 hc1
    have hcomm' : ⁅(k : G), (c : G)⁆ ∈ pPrimeCoreOf 2 K := hcCxK.2.2.2 (k : G) hk
    have h1 : ((⁅k, c⁆ : ↥(centralizer ({x} : Set G))) : G) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := WK_le_W h (by
      have : ((⁅k, c⁆ : ↥(centralizer ({x} : Set G))) : G) = ⁅(k : G), (c : G)⁆ := rfl
      rw [this]; exact hcomm')
    have h2 : co ⁅k, c⁆ = 1 := (hker _).2 (mem_Wc.2 h1)
    rw [commutatorElement_def] at h2
    simp only [map_mul, map_inv, hc] at h2
    have h3 := (commutatorElement_eq_one_iff_mul_comm (g₁ := co k)
      (g₂ := (⟨f, Qm_le_Fgrp hf⟩ : ↥(Fgrp 5)))).1 (by rw [commutatorElement_def]; exact h2)
    have h4 := congrArg (fun z : ↥(Fgrp 5) => ((z : Fgrp 5) : Amb 5).2) h3
    simpa using h4
  let φ₀ : ↥K →* Perm (Fin 4) := (MonoidHom.snd (Perm (Fin 5)) (Perm (Fin 4))).comp
    ((Fgrp 5).subtype.comp (co.comp (Subgroup.inclusion h.K_le_C)))
  have hφ₀ : ∀ k : ↥K, φ₀ k = ((co ⟨k, h.K_le_C k.2⟩ : Fgrp 5) : Amb 5).2 := fun k => rfl
  let φ : kBar K →* Perm (Fin 4) := QuotientGroup.lift (pPrimeCore 2 ↥K) φ₀ (fun k hk => by
    have hk' : (k : G) ∈ pPrimeCoreOf 2 K := Setup91.mem_pPrimeCoreOf_iff.2 ⟨k.2, hk⟩
    have h1 : co ⟨k, h.K_le_C k.2⟩ = 1 := (hker _).2 (mem_Wc.2 (WK_le_W h hk'))
    exact (MonoidHom.mem_ker).2 (by rw [hφ₀, h1]; rfl))
  have hV : ∀ z : kBar K, φ z ∈ V4l := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 := hcomm ⟨k, h.K_le_C k.2⟩ k.2 f1 f1_mem_Qm
    have h2 := hcomm ⟨k, h.K_le_C k.2⟩ k.2 f2 f2_mem_Qm
    rw [f1_snd] at h1
    rw [f2_snd] at h2
    exact V4_cent h1 h2
  have hs : IsSimpleGroup (kBar K) := e5.isSimpleGroup
  have hker1 : φ.ker = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
    · exfalso
      have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hb
      have hle : Nat.card (kBar K) ≤ Nat.card {τ : Perm (Fin 4) // τ ∈ V4l} :=
        Nat.card_le_card_of_injective (fun z => ⟨φ z, hV z⟩)
          (fun z z' hzz => hinj (congrArg Subtype.val hzz))
      have h4 : Nat.card {τ : Perm (Fin 4) // τ ∈ V4l} ≤ 4 := by
        classical
        have hset : {τ : Perm (Fin 4) | τ ∈ V4l} = (V4l.toFinset : Set (Perm (Fin 4))) := by
          ext τ
          simp
        calc Nat.card {τ : Perm (Fin 4) // τ ∈ V4l} = Set.ncard {τ : Perm (Fin 4) | τ ∈ V4l} :=
              (Nat.card_coe_set_eq _).symm
          _ = V4l.toFinset.card := by rw [hset, Set.ncard_coe_finset]
          _ ≤ V4l.length := List.toFinset_card_le V4l
          _ = 4 := rfl
      have h60 : Nat.card (kBar K) = 60 := by
        rw [Nat.card_congr e5.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      omega
    · exact ht
  have : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) ∈ φ.ker := by rw [hker1]; trivial
  have h1 : φ₀ ⟨k, hk⟩ = 1 := this
  rw [hφ₀] at h1
  exact h1

theorem co_K_mem_Km
    (co : ↥(centralizer ({x} : Set G)) →* ↥(Fgrp 5)) (hsurj : Function.Surjective co)
    (hker : ∀ c, co c = 1 ↔ c ∈ Wc x)
    (hQ : ∀ c, (((co c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ CxK x K))
    {k : ↥(centralizer ({x} : Set G))} (hk : (k : G) ∈ K) : ((co k : Fgrp 5) : Amb 5) ∈ Km := by
  have h2 := co_K_snd h co hsurj hker hQ hk
  rw [mem_Km]
  refine ⟨h2, ?_⟩
  have hF := (co k).2
  rw [mem_Fgrp5, h2] at hF
  simpa using hF.2

theorem co_K_onto
    (co : ↥(centralizer ({x} : Set G)) →* ↥(Fgrp 5)) (hsurj : Function.Surjective co)
    (hker : ∀ c, co c = 1 ↔ c ∈ Wc x)
    (hQ : ∀ c, (((co c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ CxK x K)) {m : Amb 5} (hm : m ∈ Km) :
    ∃ k : ↥(centralizer ({x} : Set G)), (k : G) ∈ K ∧ ((co k : Fgrp 5) : Amb 5) = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e5⟩ := h.kbar
  let Φ : kBar K →* ↥(Fgrp 5) := QuotientGroup.lift (pPrimeCore 2 ↥K)
    (co.comp (Subgroup.inclusion h.K_le_C)) (fun k hk => by
      have hk' : (k : G) ∈ pPrimeCoreOf 2 K := Setup91.mem_pPrimeCoreOf_iff.2 ⟨k.2, hk⟩
      exact (MonoidHom.mem_ker).2 ((hker _).2 (mem_Wc.2 (WK_le_W h hk'))))
  have hΦ : ∀ k : ↥K, Φ (QuotientGroup.mk k) = co ⟨k, h.K_le_C k.2⟩ := fun k => rfl
  have hΦinj : Function.Injective Φ := by
    have hs : IsSimpleGroup (kBar K) := e5.isSimpleGroup
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hs.eq_bot_or_eq_top_of_normal Φ.ker with hb | ht
    · exact hb
    · exfalso
      obtain ⟨hPcard, hPel⟩ := Bk.aconfigW_five_P h
      obtain ⟨u, hu, hu1⟩ : ∃ u ∈ T ⊓ K, u ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : T ⊓ K = ⊥ := eq_bot_iff.2 fun z hz => Subgroup.mem_bot.2 (hcon z hz)
        rw [this, Subgroup.card_bot] at hPcard
        omega
      have hmem : (QuotientGroup.mk (⟨u, hu.2⟩ : ↥K) : kBar K) ∈ Φ.ker := by rw [ht]; trivial
      have h1 : Φ (QuotientGroup.mk (⟨u, hu.2⟩ : ↥K)) = 1 := hmem
      rw [hΦ] at h1
      have h2 : (⟨u, h.K_le_C hu.2⟩ : ↥(centralizer ({x} : Set G))) ∈ Wc x := (hker _).1 h1
      have h3 := W_orderOf_odd (mem_Wc.1 h2)
      obtain ⟨hPc, hPs⟩ := forall_of_isElementaryAbelian hPel
      have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hPs u hu) hu1
      rw [hu2] at h3
      exact absurd h3 (by decide)
  let Kc : Subgroup (Amb 5) := Φ.range.map (Fgrp 5).subtype
  have hKcle : Kc ≤ Km := by
    rintro _ ⟨z, ⟨k', rfl⟩, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k'
    rw [hΦ]
    exact co_K_mem_Km h co hsurj hker hQ k.2
  have h60 : Nat.card (kBar K) = 60 := by
    rw [Nat.card_congr e5.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hKccard : Nat.card Kc = 60 := by
    rw [Subgroup.card_map_of_injective (Fgrp 5).subtype_injective,
      ← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv, h60]
  have hKceq : Kc = Km := Subgroup.eq_of_le_of_card_ge hKcle (by rw [hKccard, card_Km])
  have hmKc : m ∈ Kc := hKceq ▸ hm
  obtain ⟨z, ⟨k', hk'⟩, hzm⟩ := hmKc
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k'
  refine ⟨⟨k, h.K_le_C k.2⟩, k.2, ?_⟩
  rw [← hΦ k, hk']
  exact hzm

theorem mem_K_of_co_Km
    (co : ↥(centralizer ({x} : Set G)) →* ↥(Fgrp 5)) (hsurj : Function.Surjective co)
    (hker : ∀ c, co c = 1 ↔ c ∈ Wc x)
    (hQ : ∀ c, (((co c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ CxK x K))
    {c : ↥(centralizer ({x} : Set G))} (hcT : (c : G) ∈ T) (hm : ((co c : Fgrp 5) : Amb 5) ∈ Km) :
    (c : G) ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkK, hk⟩ := co_K_onto h co hsurj hker hQ hm
  have hck : co c = co k := Subtype.ext hk.symm
  have hw : c * k⁻¹ ∈ Wc x := by
    rw [← hker, map_mul, map_inv, hck, mul_inv_cancel]
  have hwG : ((c * k⁻¹ : ↥(centralizer ({x} : Set G))) : G) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) :=
    mem_Wc.1 hw
  set w : G := (c : G) * (k : G)⁻¹ with hwdef
  have hcomm : (k : G) * w = w * (k : G) := h.W_centralizes_K hwG hkK
  have hcw : (c : G) = w * (k : G) := by rw [hwdef]; group
  set m : ℕ := orderOf w with hm'
  have hmodd : Odd m := W_orderOf_odd hwG
  have hpowc : (c : G) ^ m = (k : G) ^ m := by
    rw [hcw, (Commute.mul_pow (show Commute w (k : G) from hcomm.symm)), hm', pow_orderOf_eq_one, one_mul]
  have hkm : (k : G) ^ m ∈ K := K.pow_mem hkK m
  have hT2 : IsPGroup 2 ↥T := h.sylowT.isPGroup
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.1 hT2) ⟨(c : G), hcT⟩
  have hordc : orderOf (c : G) = 2 ^ a := by rw [← ha, Subgroup.orderOf_mk]
  have hcop : Nat.Coprime m (orderOf (c : G)) := by
    rw [hordc]
    exact Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hmodd)
  obtain ⟨m', hm'1⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm'1, hpowc]
  exact K.pow_mem hkm m'

end CxKQW

structure Coord (h : IsAConfigW 5 x K T Q S a) where
  co : ↥(centralizer ({x} : Set G)) →* ↥(Fgrp 5)
  co_surj : Function.Surjective co
  co_ker : ∀ c, co c = 1 ↔ c ∈ Wc x
  hι1 : ((co (xC x) : Fgrp 5) : Amb 5) = x0 5
  hιQ : ∀ c, (((co c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ CxK x K)
  hιT : ∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ T → ((co c : Fgrp 5) : Amb 5) ∈ T5

theorem exists_coord
    (h : IsAConfigW 5 x K T Q S a) : Nonempty (Coord h) := by
  obtain ⟨co, hs, hk, h1, hq, ht⟩ := exists_coord1 h
  exact ⟨⟨co, hs, hk, h1, hq, ht⟩⟩

end CFSG.GH74.GLS.C3.Layer1.Bk.W5
