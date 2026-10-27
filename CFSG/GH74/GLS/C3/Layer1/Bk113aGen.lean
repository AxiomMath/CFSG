module

public import CFSG.GH74.GLS.C3.Layer1.Bk113aNorm
public import CFSG.GH74.GLS.C3.Layer1.Back112Glue
public import CFSG.GH74.GLS.C3.Layer1.Back112Top

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
  CFSG.GH74.GLS.C3.Layer1.U1a
open CFSG.GH74.GLS.C3.Layer1.Back.Setup91 (mem_pPrimeCoreOf_iff)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {x : G} {K L M T Q : Subgroup G}

omit [Finite G] in
theorem mem_CxK_of_mem_Q (hh : Hyp9A x K L M T Q) {q : G} (hq : q ∈ Q) : q ∈ CxK x K := by
  have h := hq
  rw [hh.hQ] at h
  exact h.2

@[expose] noncomputable def PtoBarL (K T : Subgroup G) : ↥((T ⊓ K).subgroupOf K) →* kBar K :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp ((T ⊓ K).subgroupOf K).subtype

theorem PtoBarL_injective {K T : Subgroup G} (hT : IsPGroup 2 ↥T) :
    Function.Injective (PtoBarL K T) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  have ha' : ((a : ↥K)) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 ha
  have hO : ((a : ↥K) : G) ∈ pPrimeCoreOf 2 K :=
    Setup91.mem_pPrimeCoreOf_iff.2 ⟨(a : ↥K).2, ha'⟩
  have hT' : ((a : ↥K) : G) ∈ T := (Subgroup.mem_subgroupOf.1 a.2).1
  have hmem : ((a : ↥K) : G) ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hT', hO⟩
  rw [Setup91.inf_pPrimeCoreOf_eq_bot K hT, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  exact hmem

theorem exists_zL (hh : Hyp9A x K L M T Q)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hinv : ∃ a : kBar K, orderOf a = 2) :
    ∃ z ∈ T ⊓ K, orderOf z = 2 ∧ ∀ t ∈ T, z * t = t * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := hh.sylowT.le
  have hP2 : 2 ∣ Nat.card ↥(T ⊓ K) := by
    rw [card_P_eq hh]
    obtain ⟨a, ha⟩ := hinv
    have hd : 2 ∣ Nat.card (kBar K) := by
      have := orderOf_dvd_natCard a
      rwa [ha] at this
    have hf : 1 ≤ (Nat.card (kBar K)).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').1 hd
    exact dvd_pow_self 2 (by omega)
  exact exists_central_involution_of_normal hTp inf_le_left
    (fun t ht p hp => ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), hKN t (hTC ht) p hp.2⟩) hP2

theorem exists_noncomm_in_PL (hh : Hyp9A x K L M T Q)
    (h : HasL2Model (kBar K) (fun r => r = 7 ∨ r = 9) ∨
      Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    ∃ a ∈ T ⊓ K, ∃ b ∈ T ⊓ K, a * a = 1 ∧ b * b = 1 ∧ a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hinj := PtoBarL_injective (K := K) hTp
  have hcard : Nat.card ↥(PtoBarL K T).range =
      2 ^ (Nat.card ↥(⊤ : Subgroup (kBar K))).factorization 2 := by
    rw [Subgroup.card_top, ← card_P_eq hh]
    have h1 : Nat.card ↥(PtoBarL K T).range = Nat.card ↥((T ⊓ K).subgroupOf K) :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv
  have hSyl : IsSylowOf 2 (PtoBarL K T).range ⊤ := isSylowOf_of_card le_top hcard
  obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ := sylow_noncomm_involutions h _ hSyl
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have hsq : ∀ c : ↥((T ⊓ K).subgroupOf K), orderOf (PtoBarL K T c) = 2 →
      ((c : ↥K) : G) * ((c : ↥K) : G) = 1 := by
    intro c hc
    have h1 : PtoBarL K T c ^ 2 = 1 := by simpa [hc] using pow_orderOf_eq_one (PtoBarL K T c)
    have h2 : c ^ 2 = 1 := hinj (by rw [map_pow, h1, map_one])
    have h3 := congrArg (fun y : ↥((T ⊓ K).subgroupOf K) => ((y : ↥K) : G)) h2
    simpa [sq] using h3
  refine ⟨((a' : ↥K) : G), Subgroup.mem_subgroupOf.1 a'.2, ((b' : ↥K) : G),
    Subgroup.mem_subgroupOf.1 b'.2, hsq a' ha2, hsq b' hb2, fun hc => hab ?_⟩
  have hc' : a' * b' = b' * a' := by
    apply Subtype.ext; apply Subtype.ext
    exact hc
  rw [← map_mul, ← map_mul, hc']

theorem not_centralizes_PL (hh : Hyp9A x K L M T Q)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hs : IsSimpleGroup (kBar L)) (hn : ∃ a b : kBar L, a * b ≠ b * a)
    (e5 : kBar K ≃* alternatingGroup (Fin 5))
    {y : G} (hyT : y ∈ T) (hyR : y ∉ (T ⊓ K) ⊔ Q) :
    ∃ p ∈ T ⊓ K, y * p * y⁻¹ ≠ p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hR, -, -⟩ := hh.R_eq hs hn
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hyC : y ∈ centralizer ({x} : Set G) := hh.sylowT.le hyT
  have hinj := PtoBarL_injective (K := K) hTp
  have hP4 : Nat.card ↥(PtoBarL K T).range = 4 := by
    have h1 : Nat.card ↥(PtoBarL K T).range = Nat.card ↥((T ⊓ K).subgroupOf K) :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv]
    exact card_P_five hh e5
  have hfix : ∀ p ∈ (PtoBarL K T).range, actHom hKN ⟨y, hyC⟩ p = p := by
    rintro _ ⟨c, rfl⟩
    have hc : y * ((c : ↥K) : G) * y⁻¹ = ((c : ↥K) : G) :=
      hcon _ (Subgroup.mem_subgroupOf.1 c.2)
    show actHom hKN ⟨y, hyC⟩ (QuotientGroup.mk (c : ↥K)) = QuotientGroup.mk (c : ↥K)
    rw [actHom_mk]
    congr 1
    exact Subtype.ext hc
  obtain ⟨h, hh'⟩ := a5_aut_centralizer_inner e5 _ hP4 (actHom hKN ⟨y, hyC⟩) hfix
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective h
  have hk'C : ((k' : ↥K) : G) ∈ centralizer ({x} : Set G) := hh.K_le_centralizer k'.2
  have h2 := actHom_of_mem hKN (l := ((k' : ↥K) : G)) k'.2 hk'C
  have h3 : actHom hKN ⟨y, hyC⟩ = actHom hKN ⟨((k' : ↥K) : G), hk'C⟩ := by
    rw [hh', h2]
  have h4 : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) *
      (⟨((k' : ↥K) : G), hk'C⟩ : ↥(centralizer ({x} : Set G)))⁻¹ ∈ (actHom hKN).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h3, mul_inv_cancel]
  rw [actHom_ker, Subgroup.mem_subgroupOf] at h4
  have h4' : y * ((k' : ↥K) : G)⁻¹ ∈ CxK x K := h4
  have h5 : y ∈ L ⊔ CMK M L := by
    have e : y = (y * ((k' : ↥K) : G)⁻¹) * ((k' : ↥K) : G) := by group
    rw [e]
    exact (L ⊔ CMK M L).mul_mem (mem_sup_right (CxK_le_CMK hh h4'))
      (mem_sup_left (hh.K_le_L k'.2))
  have h6 : y ∈ T ⊓ (L ⊔ CMK M L) := ⟨hyT, h5⟩
  rw [hR] at h6
  exact hyR h6

theorem card_T_leL (hh : Hyp9A x K L M T Q)
    (ψ : ↥(centralizer ({x} : Set G)) →* Equiv.Perm (Fin 5))
    (hker : ψ.ker = (CxK x K).subgroupOf (centralizer ({x} : Set G))) :
    Nat.card ↥T ≤ 8 * Nat.card ↥Q := by
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := hh.sylowT.le
  let φ : ↥(T.subgroupOf (centralizer ({x} : Set G))) →* Equiv.Perm (Fin 5) :=
    ψ.comp (T.subgroupOf (centralizer ({x} : Set G))).subtype
  have hTpM : IsPGroup 2 ↥(T.subgroupOf (centralizer ({x} : Set G))) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card ↥φ.range ∣ 8 := card_perm_five_dvd_two_part φ hTpM
  have hmemQ : ∀ t : ↥φ.ker,
      (((t : ↥(T.subgroupOf (centralizer ({x} : Set G)))) : ↥(centralizer ({x} : Set G))) : G) ∈ Q := by
    intro t
    have ht : φ (t : ↥(T.subgroupOf (centralizer ({x} : Set G)))) = 1 := t.2
    have h3 : ((t : ↥(T.subgroupOf (centralizer ({x} : Set G)))) : ↥(centralizer ({x} : Set G))) ∈
        ψ.ker := ht
    rw [hker, Subgroup.mem_subgroupOf] at h3
    have h4 : (((t : ↥(T.subgroupOf (centralizer ({x} : Set G)))) :
        ↥(centralizer ({x} : Set G))) : G) ∈ T :=
      Subgroup.mem_subgroupOf.1 (t : ↥(T.subgroupOf (centralizer ({x} : Set G)))).2
    rw [hh.hQ]
    exact ⟨h4, h3⟩
  let f : ↥φ.ker → ↥Q := fun t => ⟨_, hmemQ t⟩
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact this
  have h6 : Nat.card ↥φ.ker ≤ Nat.card ↥Q := Nat.card_le_card_of_injective f hf
  have h7 : Nat.card ↥φ.range ≤ 8 := Nat.le_of_dvd (by norm_num) h2
  have h8 : Nat.card ↥T = Nat.card ↥(T.subgroupOf (centralizer ({x} : Set G))) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv).symm
  rw [h8, ← h1]
  calc Nat.card ↥φ.ker * Nat.card ↥φ.range ≤ Nat.card ↥Q * 8 := Nat.mul_le_mul h6 h7
    _ = 8 * Nat.card ↥Q := by ring

theorem claim112L (hh : Hyp9A x K L M T Q)
    (hG : IsKProperSimple G) (h81 : B_iv2_8_1) (h92 : B_lemma92)
    (hlistL : HasL2Model (kBar L) Odd ∨ Nonempty (kBar L ≃* alternatingGroup (Fin 7)))
    (hsL : IsSimpleGroup (kBar L)) (hnL : ∃ a b : kBar L, a * b ≠ b * a)
    (hconj : ∀ a b : kBar K, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (hQe : CFSG.IsElementaryAbelian 2 ↥Q ∧ Nat.card ↥Q = 4)
    {g : G} (hgR : conjugate Q g ≤ (T ⊓ K) ⊔ Q) (hgQ : conjugate Q g ⊓ Q = ⊥)
    {z : G} (hzP : z ∈ T ⊓ K) (hz2 : orderOf z = 2)
    {W : Subgroup G} (hWT : W ≤ T)
    (hwc : ∀ g : G, conjugate W g ≤ T → conjugate W g = W)
    (hQE : Q ≤ omegaZ W) (hzE : z ∈ omegaZ W) (hcard : Nat.card ↥(omegaZ W) ≤ 8) : False := by
  set E : Subgroup G := omegaZ W with hEdef
  have hET : E ≤ T := (omegaZ_le W).trans hWT
  have hEW : ∀ e ∈ E, ∀ w ∈ W, e * w = w * e := fun e he w hw => he.2.1 w hw
  have hEN : ∀ n ∈ normalizer (W : Set G), ∀ e ∈ E, n⁻¹ * e * n ∈ E :=
    fun n hn e he => omegaZ_conj hn he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR, hcomm, hPQ⟩ := hh.R_eq hsL hnL
  have hQ2 : IsPGroup 2 ↥Q := hh.sylowQ.isPGroup
  obtain ⟨hQab, hQsq⟩ := forall_of_isElementaryAbelian hQe.1
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hQT : Q ≤ T := Setup91.Q_le_T hh
  have hTM : T ≤ M := hh.sylowTM.le
  have hxQ : x ∈ Q := hh.x_mem_Q
  have hx1 : x ≠ 1 := by
    intro h1
    have := hh.orderOf_x
    rw [h1, orderOf_one] at this
    omega
  have hNM : ∀ n ∈ normalizer (W : Set G), n ∈ M := by
    intro n hnW
    by_contra hnM
    have hVE : conjugate Q n ≤ E := by
      intro v hv
      have hv' := mem_conjugate_iff'.1 hv
      have h1 := hEN n hnW _ (hQE hv')
      have e : n⁻¹ * (n * v * n⁻¹) * n = v := by group
      rw [e] at h1; exact h1
    have hVT : conjugate Q n ≤ T := hVE.trans hET
    have hV0 : conjugate Q n ≠ ⊥ := by
      intro h0
      have h1 : Nat.card ↥(conjugate Q n) = 4 := by rw [card_conjugate']; exact hQe.2
      rw [h0, Subgroup.card_bot] at h1
      omega
    have hV2 : 2 ≤ pRank 2 ↥(conjugate Q n) := by
      rw [pRank_conjugate']; exact hh.rankQ
    have hbot : conjugate Q n ⊓ CMK M L = ⊥ :=
      inf_CMK_eq_bot_of_not_mem hh hG h81 h92 hlistL hnM le_rfl (hVT.trans hTM) hV0 hV2
    have hQV : conjugate Q n ⊓ Q = ⊥ := by
      refine eq_bot_iff.2 fun y hy => ?_
      have hy' : y ∈ conjugate Q n ⊓ CMK M L := ⟨hy.1, hh.sylowQ.le hy.2⟩
      rw [hbot] at hy'
      exact hy'
    have hcardprod := CFSG.GH74.GLS.C3.Layer1.P34.card_mul_inf (conjugate Q n) Q
    rw [hQV, Subgroup.card_bot, mul_one, card_conjugate', hQe.2] at hcardprod
    have hsub : ((conjugate Q n : Subgroup G) : Set G) * (Q : Set G) ⊆ (E : Set G) := by
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact E.mul_mem (hVE ha) (hQE hb)
    have hle : Nat.card ↥(((conjugate Q n : Subgroup G) : Set G) * (Q : Set G)) ≤
        Nat.card ↥(E : Set G) := Nat.card_mono (Set.toFinite _) hsub
    have hE' : Nat.card ↥(E : Set G) = Nat.card ↥E := rfl
    omega
  have hux : g⁻¹ * x * g ∈ conjugate Q g := by
    rw [mem_conjugate_iff']
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]; exact hxQ
  obtain ⟨p, hpP, q, hqQ, hpq⟩ := exists_mul_of_mem_sup_of_commute hcomm (hgR hux)
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hh.orderOf_x, sq] at this
  have hu2 : (p * q) * (p * q) = 1 := by
    rw [← hpq]
    have e : g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    rw [e, hx2]; group
  have hq2 : q * q = 1 := hQsq q hqQ
  have hpqc : p * q = q * p := hcomm p hpP q hqQ
  have hp2 : p * p = 1 := by
    have e : (p * q) * (p * q) = (p * p) * (q * q) := by
      calc (p * q) * (p * q) = p * (q * p) * q := by group
        _ = p * (p * q) * q := by rw [← hpqc]
        _ = (p * p) * (q * q) := by group
    rw [e, hq2, mul_one] at hu2
    exact hu2
  have hp1 : p ≠ 1 := by
    intro hp1
    rw [hp1, one_mul] at hpq
    have hq' : g⁻¹ * x * g ∈ Q := by rw [hpq]; exact hqQ
    have hmem : g⁻¹ * x * g ∈ conjugate Q g ⊓ Q := ⟨hux, hq'⟩
    rw [hgQ, Subgroup.mem_bot] at hmem
    exact hx1 (eq_one_of_conj_eq_one hmem)
  have hpo : orderOf p = 2 := orderOf_eq_prime (by rw [sq]; exact hp2) hp1
  have hpK : p ∈ K := hpP.2
  have hzK : z ∈ K := hzP.2
  have hbarP : (QuotientGroup.mk (⟨p, hpK⟩ : ↥K) : kBar K) ≠ 1 := by
    intro h1
    have hO : p ∈ pPrimeCoreOf 2 K := mem_pPrimeCoreOf_iff.2 ⟨hpK, (QuotientGroup.eq_one_iff _).1 h1⟩
    have hmem : p ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hpP.1, hO⟩
    rw [Setup91.inf_pPrimeCoreOf_eq_bot K hTp, Subgroup.mem_bot] at hmem
    exact hp1 hmem
  have hbarZ : (QuotientGroup.mk (⟨z, hzK⟩ : ↥K) : kBar K) ≠ 1 := by
    intro h1
    have hO : z ∈ pPrimeCoreOf 2 K := mem_pPrimeCoreOf_iff.2 ⟨hzK, (QuotientGroup.eq_one_iff _).1 h1⟩
    have hmem : z ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hzP.1, hO⟩
    rw [Setup91.inf_pPrimeCoreOf_eq_bot K hTp, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hz2
    omega
  have hz2' : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hbarP2 : orderOf (QuotientGroup.mk (⟨p, hpK⟩ : ↥K) : kBar K) = 2 := by
    refine orderOf_eq_prime ?_ hbarP
    rw [sq, ← QuotientGroup.mk_mul]
    have : (⟨p, hpK⟩ : ↥K) * ⟨p, hpK⟩ = 1 := Subtype.ext hp2
    rw [this]; rfl
  have hbarZ2 : orderOf (QuotientGroup.mk (⟨z, hzK⟩ : ↥K) : kBar K) = 2 := by
    refine orderOf_eq_prime ?_ hbarZ
    rw [sq, ← QuotientGroup.mk_mul]
    have : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 := Subtype.ext hz2'
    rw [this]; rfl
  have hbar := exists_bar_of_conj hpK hzK (hconj _ _ hbarP2 hbarZ2)
  have hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K := fun q hq k hk =>
    (mem_normalizer_iff.1 (mem_CxK_of_mem_Q hh hq).2.1 k).1 hk
  have hQt : ∀ q ∈ Q, ∀ k ∈ K, ⁅k, q⁆ ∈ pPrimeCoreOf 2 K := fun q hq k hk =>
    (mem_CxK_of_mem_Q hh hq).2.2.2 k hk
  obtain ⟨h, hhK, hhQ, hpz⟩ := exists_conj_centralizing hQ2 hQK hQt hpK hzK hpo hz2
    (fun q hq => hcomm p hpP q hq) (fun q hq => hcomm z hzP q hq) hbar
  have hqh : h⁻¹ * q * h = q := by
    have h1 := hhQ q hqQ
    calc h⁻¹ * q * h = h⁻¹ * (q * h) := by group
      _ = h⁻¹ * (h * q) := by rw [h1]
      _ = q := by group
  have hw : (g * h)⁻¹ * x * (g * h) = z * q := by
    have e : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
    rw [e, hpq]
    calc h⁻¹ * (p * q) * h = (h⁻¹ * p * h) * (h⁻¹ * q * h) := by group
      _ = z * q := by rw [hpz, hqh]
  have hwE : z * q ∈ E := E.mul_mem hzE (hQE hqQ)
  have hwy : z * q ∈ centralizer (W : Set G) ⊓ T :=
    ⟨Subgroup.mem_centralizer_iff.2 fun w hw' => (hEW _ hwE w hw').symm, hET hwE⟩
  obtain ⟨n, hnW, hn⟩ := iv2_3_2 hh.sylowT hWT hwc hwy hw.symm
  have hnM : n ∈ M := hNM n hnW
  have hxC : x ∈ CMK M L := hh.sylowQ.le hxQ
  have hnC : n⁻¹ * x * n ∈ CMK M L := by
    have := conj_mem_CMK hh.L_normal.2 (M.inv_mem hnM) hxC
    rwa [inv_inv] at this
  have hTC : T ⊓ CMK M L = Q := T_inf_CMK hh
  have hwQ : z * q ∈ Q := by
    have hmem : z * q ∈ T ⊓ CMK M L := ⟨hwy.2, by rw [hn]; exact hnC⟩
    rwa [hTC] at hmem
  have hu : g⁻¹ * x * g ∈ Q := by
    have e : g⁻¹ * x * g = h * (z * q) * h⁻¹ := by
      rw [← hw]; group
    have hc := hhQ (z * q) hwQ
    rw [e, hc]
    simpa using hwQ
  have hmem : g⁻¹ * x * g ∈ conjugate Q g ⊓ Q := ⟨hux, hu⟩
  rw [hgQ, Subgroup.mem_bot] at hmem
  exact hx1 (eq_one_of_conj_eq_one hmem)

theorem lemma112L
    (h81 : B_iv2_8_1) (h92 : B_lemma92) (hG : C3Hyp G)
    (hh : Hyp9A x K L M T Q) (p91 : Prop91Concl K M T Q)
    (hQZ : ∀ q ∈ Q, ∀ t ∈ closure {u : G | u ∈ T ∧ u * u = 1}, q * t = t * q) :
    Nonempty (kBar K ≃* alternatingGroup (Fin 5)) ∧ (T ⊓ K) ⊔ Q = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hQT : Q ≤ T := Setup91.Q_le_T hh
  have hTC : T ≤ centralizer ({x} : Set G) := hh.sylowT.le
  have hcases := kBar_cases p91
  have hlist := hlist_of_cases hcases
  have hs : IsSimpleGroup (kBar K) := by
    rcases hlist with h | h
    · exact isSimpleGroup_of_hasL2Model h
    · exact isSimpleGroup_of_alt7 h
  have hn : ∃ a b : kBar K, a * b ≠ b * a :=
    nonab_of_quasisimple (TwoThin.isQuasisimple_hat hh.twoTerminal.1.2.2)
  have hconj : ∀ a b : kBar K, orderOf a = 2 → orderOf b = 2 → IsConj a b :=
    fun a b ha hb => involutions_conj_of_model hlist a b ha hb
  obtain ⟨eKL⟩ := hh.kBar_equiv
  have hsL : IsSimpleGroup (kBar L) := by
    have := hs
    exact eKL.symm.isSimpleGroup
  have hnL : ∃ a b : kBar L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hn
    exact ⟨eKL a, eKL b, fun h => hab (eKL.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hlistL : HasL2Model (kBar L) Odd ∨ Nonempty (kBar L ≃* alternatingGroup (Fin 7)) := by
    rcases hlist with h | h
    · exact Or.inl (TwoThin.hasL2Model_of_mulEquiv eKL h)
    · obtain ⟨e7⟩ := h
      exact Or.inr ⟨eKL.symm.trans e7⟩
  have heven : 2 ∣ Nat.card ↥K := by
    obtain ⟨a, ha⟩ := exists_involution_of_model hlist
    have hd : 2 ∣ Nat.card (kBar K) := by
      have := orderOf_dvd_natCard a
      rwa [ha] at this
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)]
    exact Dvd.dvd.mul_right hd _
  have hKN := hh.K_normal hsL hnL heven
  obtain ⟨hQe, ⟨g, -, hgR, hgQ⟩, -, -⟩ := p91
  obtain ⟨-, hcomm, hPQ⟩ := hh.R_eq hsL hnL
  obtain ⟨z, hzP, hz2, hzc⟩ := exists_zL hh hKN (exists_involution_of_model hlist)
  have hz2' : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hrk := card_le_sixteen hG
  obtain ⟨hQab, hQsq⟩ := forall_of_isElementaryAbelian hQe.1
  have hQE₁ : Q ≤ omegaZ (omegaOneT T) := fun q hq =>
    ⟨mem_omegaOneT (hQT hq) (hQsq q hq), fun w hw => hQZ q hq w hw, hQsq q hq⟩
  have hzE₁ : z ∈ omegaZ (omegaOneT T) :=
    ⟨mem_omegaOneT hzP.1 hz2', fun w hw => hzc w (omegaOneT_le T hw), hz2'⟩
  have hbig : 8 < Nat.card ↥(omegaZ (omegaOneT T)) := by
    by_contra hle
    push Not at hle
    exact claim112L hh hG.kproper h81 h92 hlistL hsL hnL hconj hQe hgR hgQ hzP hz2
      (omegaOneT_le T) (omegaOneT_weakly_closed T) hQE₁ hzE₁ hle
  obtain ⟨hE16, hEinv⟩ := omegaZ_structure (T := T) (W := omegaOneT T)
    (fun u hu hu2 => mem_omegaOneT hu hu2) hrk hbig
  have hnc : ∀ a ∈ T ⊓ K, ∀ b ∈ T ⊓ K, a * a = 1 → b * b = 1 → a * b = b * a :=
    fun a ha b hb ha2 hb2 =>
      (hEinv a ha.1 ha2).2.1 b (omegaZ_le _ (hEinv b hb.1 hb2))
  have hK5 : HasL2Model (kBar K) (fun r => r = 5) := by
    rcases hcases with h | h | h | h
    · exact h
    · obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ :=
        exists_noncomm_in_PL hh (Or.inl (hasL2Model_mono (fun r hr => Or.inl hr) h))
      exact absurd (hnc a ha b hb ha2 hb2) hab
    · obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ :=
        exists_noncomm_in_PL hh (Or.inl (hasL2Model_mono (fun r hr => Or.inr hr) h))
      exact absurd (hnc a ha b hb ha2 hb2) hab
    · obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ := exists_noncomm_in_PL hh (Or.inr h)
      exact absurd (hnc a ha b hb ha2 hb2) hab
  obtain ⟨e5⟩ := nonempty_alt5_of_hasL2Model5 hK5
  have hP4 : Nat.card ↥(T ⊓ K) = 4 := card_P_five hh e5
  have hQ4 : Nat.card ↥Q = 4 := hQe.2
  have hPsq : ∀ p ∈ T ⊓ K, p * p = 1 := by
    intro p hp
    have hp4 : p ^ 4 = 1 := by
      have h1 : (⟨p, hp⟩ : ↥(T ⊓ K)) ^ Nat.card ↥(T ⊓ K) = 1 := pow_card_eq_one'
      rw [hP4] at h1
      have h2 := congrArg (fun y : ↥(T ⊓ K) => (y : G)) h1
      simpa using h2
    have hpK : p ∈ K := hp.2
    have h3 : (QuotientGroup.mk (⟨p, hpK⟩ : ↥K) : kBar K) ^ 4 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨p, hpK⟩ : ↥K) ^ 4 = 1 := Subtype.ext (by simpa using hp4)
      rw [this]; rfl
    have h4 := a5_no_order_four e5 _ h3
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h4
    have hO : p ^ 2 ∈ pPrimeCoreOf 2 K := by
      refine Setup91.mem_pPrimeCoreOf_iff.2 ⟨K.pow_mem hpK 2, ?_⟩
      exact h4
    have hmem : p ^ 2 ∈ T ⊓ pPrimeCoreOf 2 K := ⟨T.pow_mem hp.1 2, hO⟩
    rw [Setup91.inf_pPrimeCoreOf_eq_bot K hTp, Subgroup.mem_bot] at hmem
    rw [← sq]; exact hmem
  have hPE : T ⊓ K ≤ omegaZ (omegaOneT T) := fun p hp => hEinv p hp.1 (hPsq p hp)
  have hRE : (T ⊓ K) ⊔ Q = omegaZ (omegaOneT T) :=
    Subgroup.eq_of_le_of_card_ge (sup_le hPE hQE₁)
      (Nat.le_of_eq (by
        have hc := Setup91.card_sup_Q hh hsL hnL
        rw [hE16, hc, hP4, hQ4]))
  have hR16 : Nat.card ↥((T ⊓ K) ⊔ Q) = 16 := by rw [hRE, hE16]
  have hRab : ∀ a ∈ (T ⊓ K) ⊔ Q, ∀ b ∈ (T ⊓ K) ⊔ Q, a * b = b * a := by
    rw [hRE]; exact (forall_of_isElementaryAbelian (omegaZ_isElementaryAbelian _)).1
  have hR2 : ∀ a ∈ (T ⊓ K) ⊔ Q, a * a = 1 := by
    rw [hRE]; exact (forall_of_isElementaryAbelian (omegaZ_isElementaryAbelian _)).2
  have hno : ∀ u ∈ T, u * u = 1 → u ∈ (T ⊓ K) ⊔ Q := fun u hu hu2 => by
    rw [hRE]; exact hEinv u hu hu2
  have hRT : (T ⊓ K) ⊔ Q = T := by
    by_contra hne
    have hlt : (T ⊓ K) ⊔ Q < T := lt_of_le_of_ne (sup_le inf_le_left hQT) hne
    obtain ⟨ψ, hψ⟩ := lemma113d_ne6 (K := K) (M := centralizer ({x} : Set G))
      hh.K_le_centralizer hKN (n := 5) (by norm_num) (by norm_num) e5
    have hidx : Nat.card ↥T ≤ 2 * Nat.card ↥((T ⊓ K) ⊔ Q) := by
      have := card_T_leL hh ψ hψ
      rw [hR16]; rw [hQ4] at this; omega
    have hPn : ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
      ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), hKN t (hTC ht) p hp.2⟩
    have hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := fun t ht q hq => by
      have h1 : t * q * t⁻¹ ∈ T ⊓ CxK x K :=
        ⟨T.mul_mem (T.mul_mem ht (hQT hq)) (T.inv_mem ht),
          conj_mem_CMK hKN (hTC ht) (mem_CxK_of_mem_Q hh hq)⟩
      rwa [← hh.hQ] at h1
    obtain ⟨hQZT, hcardT⟩ := omegaZ_T_of_ne inf_le_left hQT hPn hQn hPQ hcomm hP4 hQ4 hRab hR2
      hR16 hno hidx (fun y hyT hyR => not_centralizes_PL hh hKN hsL hnL e5 hyT hyR) hlt
    have hzET : z ∈ omegaZ T := ⟨hzP.1, hzc, hz2'⟩
    exact claim112L hh hG.kproper h81 h92 hlistL hsL hnL hconj hQe hgR hgQ hzP hz2 le_rfl
      (weakly_closed_self T) hQZT hzET hcardT
  exact ⟨⟨e5⟩, hRT⟩

end CFSG.GH74.GLS.C3.Layer1.Bk
