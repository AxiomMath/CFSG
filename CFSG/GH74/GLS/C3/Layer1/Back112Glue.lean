module

public import CFSG.GH74.GLS.C3.Layer1.Back112A5
public import CFSG.GH74.GLS.C3.Layer1.Back112Kfacts
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.GH74.GLS.C3.Layer1.Back91
public import CFSG.GH74.GLS.C3.Layer1.Back112Claim

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.U1a
open scoped commutatorElement

variable {G : Type} [Group G]

theorem kBar_cases {K M T Q : Subgroup G} (p91 : Prop91Concl K M T Q) :
    HasL2Model (kBar K) (fun r => r = 5) ∨ HasL2Model (kBar K) (fun r => r = 7) ∨
      HasL2Model (kBar K) (fun r => r = 9) ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨-, -, hc, hd⟩ := p91
  by_cases hex : ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K'
  · rcases hd hex with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · obtain ⟨q, hq, hqm⟩ := hc hex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inl hqm
    · exact Or.inr (Or.inl hqm)
    · exact Or.inr (Or.inr (Or.inl hqm))

theorem hlist_of_cases {K : Subgroup G}
    (h : HasL2Model (kBar K) (fun r => r = 5) ∨ HasL2Model (kBar K) (fun r => r = 7) ∨
      HasL2Model (kBar K) (fun r => r = 9) ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) := by
  rcases h with h | h | h | h
  · exact Or.inl (hasL2Model_mono (fun r hr => by rw [hr]; decide) h)
  · exact Or.inl (hasL2Model_mono (fun r hr => by rw [hr]; decide) h)
  · exact Or.inl (hasL2Model_mono (fun r hr => by rw [hr]; decide) h)
  · exact Or.inr h

variable [Finite G]

theorem pRank_le_top (A : Subgroup G) : pRank 2 ↥A ≤ pRank 2 G := by
  have h1 := pRank_mono' (le_top : A ≤ ⊤)
  have h2 : pRank 2 ↥(⊤ : Subgroup G) = pRank 2 G :=
    CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two (Subgroup.topEquiv (G := G))
  rw [h2] at h1
  exact h1

theorem card_le_sixteen (hG : C3Hyp G) (A : Subgroup G) (hA : CFSG.IsElementaryAbelian 2 ↥A) :
    Nat.card ↥A ≤ 16 := by
  rw [card_eq_two_pow_pRank hA]
  have h := (pRank_le_top A).trans hG.pRank_eq_four.le
  calc 2 ^ pRank 2 ↥A ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h
    _ = 16 := by norm_num

theorem card_P_eq {x : G} {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q) :
    Nat.card ↥(T ⊓ K) = 2 ^ (Nat.card (kBar K)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(Setup91.inf_isSylowOf hh).card_eq]
  have hK := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have h0 : Nat.card ↥(pPrimeCore 2 ↥K) ≠ 0 := Nat.card_pos.ne'
  have h1 : Nat.card (kBar K) ≠ 0 := Nat.card_pos.ne'
  rw [hK, Nat.factorization_mul h1 h0, Finsupp.add_apply, Setup91.factorization_two_of_odd hodd,
    add_zero]

theorem exists_central_involution_of_normal {T P : Subgroup G} (hTp : IsPGroup 2 ↥T)
    (hPT : P ≤ T) (hPn : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P) (hP2 : 2 ∣ Nat.card ↥P) :
    ∃ z ∈ P, orderOf z = 2 ∧ ∀ t ∈ T, z * t = t * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPN : (P.subgroupOf T).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := hPn g g.2 n hn
    simpa using h1⟩
  have : Group.IsNilpotent ↥T := hTp.isNilpotent
  have hne : P.subgroupOf T ≠ ⊥ := by
    intro h0
    have h1 : Nat.card ↥(P.subgroupOf T) = 1 := by rw [h0]; exact Subgroup.card_bot
    have h2 : Nat.card ↥P = 1 := by
      rw [← h1]; exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT).toEquiv).symm
    rw [h2] at hP2
    omega
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hZp : IsPGroup 2 ↥(P.subgroupOf T ⊓ Subgroup.center ↥T) := hTp.to_subgroup _
  have hZ2 : 2 ∣ Nat.card ↥(P.subgroupOf T ⊓ Subgroup.center ↥T) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZp
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hZ
      rw [← Subgroup.card_eq_one]
      simpa using hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
  refine ⟨((z : ↥T) : G), Subgroup.mem_subgroupOf.1 z.2.1, ?_, fun t ht => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  · have hc := (Subgroup.mem_center_iff.1 z.2.2) ⟨t, ht⟩
    exact congrArg Subtype.val hc.symm

theorem exists_z {x : G} {K M T Q : Subgroup G} (hh : Hyp9A x K K M T Q)
    (hinv : ∃ a : kBar K, orderOf a = 2) :
    ∃ z ∈ T ⊓ K, orderOf z = 2 ∧ ∀ t ∈ T, z * t = t * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hTM : T ≤ M := hh.sylowTM.le
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
    (fun t ht p hp => ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht),
      hh.L_normal.2 t (hTM ht) p hp.2⟩) hP2

theorem factorization_two_sixty : (60 : ℕ).factorization 2 = 2 := by
  have h : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Setup91.factorization_two_of_odd (by decide : Odd 15)]

theorem card_P_five {x : G} {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q)
    (e5 : kBar K ≃* alternatingGroup (Fin 5)) : Nat.card ↥(T ⊓ K) = 4 := by
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]; simp [Nat.factorial]
  rw [card_P_eq hh, Nat.card_congr e5.toEquiv, h60, factorization_two_sixty]
  norm_num

theorem T_inf_CMK {x : G} {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q) :
    T ⊓ CMK M L = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hh.sylowQ.eq_of_le (le_inf (Setup91.Q_le_T hh) hh.sylowQ.le) inf_le_right
    hh.sylowT.isPGroup.to_inf_left

noncomputable def PtoBar (K T : Subgroup G) : ↥((T ⊓ K).subgroupOf K) →* kBar K :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp ((T ⊓ K).subgroupOf K).subtype

theorem PtoBar_injective {K T : Subgroup G} (hT : IsPGroup 2 ↥T) :
    Function.Injective (PtoBar K T) := by
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

theorem exists_noncomm_in_P {x : G} {K M T Q : Subgroup G} (hh : Hyp9A x K K M T Q)
    (h : HasL2Model (kBar K) (fun r => r = 7 ∨ r = 9) ∨
      Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    ∃ a ∈ T ⊓ K, ∃ b ∈ T ⊓ K, a * a = 1 ∧ b * b = 1 ∧ a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hinj := PtoBar_injective (K := K) hTp
  have hcard : Nat.card ↥(PtoBar K T).range =
      2 ^ (Nat.card ↥(⊤ : Subgroup (kBar K))).factorization 2 := by
    rw [Subgroup.card_top, ← card_P_eq hh]
    have h1 : Nat.card ↥(PtoBar K T).range = Nat.card ↥((T ⊓ K).subgroupOf K) :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv
  have hSyl : IsSylowOf 2 (PtoBar K T).range ⊤ := isSylowOf_of_card le_top hcard
  obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ := sylow_noncomm_involutions h _ hSyl
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have hsq : ∀ c : ↥((T ⊓ K).subgroupOf K), orderOf (PtoBar K T c) = 2 →
      ((c : ↥K) : G) * ((c : ↥K) : G) = 1 := by
    intro c hc
    have h1 : PtoBar K T c ^ 2 = 1 := by simpa [hc] using pow_orderOf_eq_one (PtoBar K T c)
    have h2 : c ^ 2 = 1 := hinj (by rw [map_pow, h1, map_one])
    have h3 := congrArg (fun y : ↥((T ⊓ K).subgroupOf K) => ((y : ↥K) : G)) h2
    simpa [sq] using h3
  refine ⟨((a' : ↥K) : G), Subgroup.mem_subgroupOf.1 a'.2, ((b' : ↥K) : G),
    Subgroup.mem_subgroupOf.1 b'.2, hsq a' ha2, hsq b' hb2, fun hc => hab ?_⟩
  have hc' : a' * b' = b' * a' := by
    apply Subtype.ext; apply Subtype.ext
    exact hc
  rw [← map_mul, ← map_mul, hc']

theorem not_centralizes_P
    {x : G} {K M T Q : Subgroup G} (hh : Hyp9A x K K M T Q)
    (hs : IsSimpleGroup (kBar K)) (hn : ∃ a b : kBar K, a * b ≠ b * a)
    (e5 : kBar K ≃* alternatingGroup (Fin 5))
    {y : G} (hyT : y ∈ T) (hyR : y ∉ (T ⊓ K) ⊔ Q) :
    ∃ p ∈ T ⊓ K, y * p * y⁻¹ ≠ p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hR, -, -⟩ := hh.R_eq hs hn
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hTM : T ≤ M := hh.sylowTM.le
  have hyM : y ∈ M := hTM hyT
  have hnorm := hh.L_normal.2
  have hinj := PtoBar_injective (K := K) hTp
  have hP4 : Nat.card ↥(PtoBar K T).range = 4 := by
    have h1 : Nat.card ↥(PtoBar K T).range = Nat.card ↥((T ⊓ K).subgroupOf K) :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv]
    exact card_P_five hh e5
  have hfix : ∀ p ∈ (PtoBar K T).range, actHom hnorm ⟨y, hyM⟩ p = p := by
    rintro _ ⟨c, rfl⟩
    have hc : y * ((c : ↥K) : G) * y⁻¹ = ((c : ↥K) : G) :=
      hcon _ (Subgroup.mem_subgroupOf.1 c.2)
    show actHom hnorm ⟨y, hyM⟩ (QuotientGroup.mk (c : ↥K)) = QuotientGroup.mk (c : ↥K)
    rw [actHom_mk]
    congr 1
    exact Subtype.ext hc
  obtain ⟨h, hh'⟩ := a5_aut_centralizer_inner e5 _ hP4 (actHom hnorm ⟨y, hyM⟩) hfix
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective h
  have hk'M : ((k' : ↥K) : G) ∈ M := hh.L_normal.1 k'.2
  have h2 := actHom_of_mem hnorm (l := ((k' : ↥K) : G)) k'.2 hk'M
  have h3 : actHom hnorm ⟨y, hyM⟩ = actHom hnorm ⟨((k' : ↥K) : G), hk'M⟩ := by
    rw [hh', h2]
  have h4 : (⟨y, hyM⟩ : ↥M) * (⟨((k' : ↥K) : G), hk'M⟩ : ↥M)⁻¹ ∈ (actHom hnorm).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h3, mul_inv_cancel]
  rw [actHom_ker, Subgroup.mem_subgroupOf] at h4
  have h4' : y * ((k' : ↥K) : G)⁻¹ ∈ CMK M K := h4
  have h5 : y ∈ CMK M K ⊔ K := by
    have e : y = (y * ((k' : ↥K) : G)⁻¹) * ((k' : ↥K) : G) := by group
    rw [e]
    exact Subgroup.mul_mem_sup h4' k'.2
  have h6 : y ∈ T ⊓ (K ⊔ CMK M K) := ⟨hyT, by rwa [sup_comm] at h5⟩
  rw [hR] at h6
  exact hyR h6

theorem card_T_le {x : G} {K M T Q : Subgroup G} (hh : Hyp9A x K K M T Q)
    (ψ : ↥M →* Equiv.Perm (Fin 5)) (hker : ψ.ker = (CMK M K).subgroupOf M) :
    Nat.card ↥T ≤ 8 * Nat.card ↥Q := by
  have hTp : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hTM : T ≤ M := hh.sylowTM.le
  let φ : ↥(T.subgroupOf M) →* Equiv.Perm (Fin 5) := ψ.comp (T.subgroupOf M).subtype
  have hTpM : IsPGroup 2 ↥(T.subgroupOf M) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card ↥φ.range ∣ 8 := card_perm_five_dvd_two_part φ hTpM
  have hmemQ : ∀ t : ↥φ.ker, (((t : ↥(T.subgroupOf M)) : ↥M) : G) ∈ Q := by
    intro t
    have ht : φ (t : ↥(T.subgroupOf M)) = 1 := t.2
    have h3 : ((t : ↥(T.subgroupOf M)) : ↥M) ∈ ψ.ker := ht
    rw [hker, Subgroup.mem_subgroupOf] at h3
    have h4 : (((t : ↥(T.subgroupOf M)) : ↥M) : G) ∈ T :=
      Subgroup.mem_subgroupOf.1 (t : ↥(T.subgroupOf M)).2
    have h5 : (((t : ↥(T.subgroupOf M)) : ↥M) : G) ∈ T ⊓ CMK M K := ⟨h4, h3⟩
    rwa [T_inf_CMK hh] at h5
  let f : ↥φ.ker → ↥Q := fun t => ⟨(((t : ↥(T.subgroupOf M)) : ↥M) : G), hmemQ t⟩
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact this
  have h6 : Nat.card ↥φ.ker ≤ Nat.card ↥Q := Nat.card_le_card_of_injective f hf
  have h7 : Nat.card ↥φ.range ≤ 8 := Nat.le_of_dvd (by norm_num) h2
  have h8 : Nat.card ↥T = Nat.card ↥(T.subgroupOf M) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv).symm
  rw [h8, ← h1]
  calc Nat.card ↥φ.ker * Nat.card ↥φ.range ≤ Nat.card ↥Q * 8 := Nat.mul_le_mul h6 h7
    _ = 8 * Nat.card ↥Q := by ring

theorem exists_conj_mem_sylow {C T : Subgroup G} (hT : IsSylowOf 2 T C) {y : G} (hyC : y ∈ C)
    (hy : orderOf y = 2) : ∃ c ∈ C, c⁻¹ * y * c ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYp : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; simp)
  have hYp' : IsPGroup 2 ↥((Subgroup.zpowers y).subgroupOf C) := hYp.comap_subtype
  obtain ⟨S, hS⟩ := hYp'.exists_le_sylow
  have hS' : IsSylowOf 2 ((S : Subgroup ↥C).map C.subtype) C := ⟨S, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hT.exists_mem_conj hS'
  refine ⟨k, hk, ?_⟩
  have hyS : y ∈ (S : Subgroup ↥C).map C.subtype := by
    refine ⟨⟨y, hyC⟩, hS ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers y
  exact (hconj y).1 hyS

theorem K_equiv_kBar_of_B2
    {x : G} {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q)
    (hB2 : Hyp9B2 x K M T Q) : Nonempty (↥K ≃* kBar K) := by
  have hqs : IsQuasisimple (kBar K) := TwoThin.isQuasisimple_hat hh.twoTerminal.1.2.2
  have hnon := nonab_of_quasisimple hqs
  have hKs : IsSimpleGroup ↥K := isSimpleGroup_of_hasL2Model hB2.isL2
  have hbot : pPrimeCore 2 ↥K = ⊥ := by
    rcases hKs.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnon
      apply hab
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rw [h]; exact Subgroup.mem_top _
  exact ⟨QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)⟩

theorem not_v2_of_T_eq_R {x : G} {K M T Q : Subgroup G} (hh : Hyp9A x K K M T Q)
    (hcomm : ∀ p ∈ T ⊓ K, ∀ q ∈ Q, p * q = q * p) (hRT : (T ⊓ K) ⊔ Q = T)
    (h102a : B_ivk_10_2a) (hG : C3Hyp G) (hFM : HasL2Model (kBar K) IsFM9) {y : G}
    (hy : IsV2Triple x y K) : False := by
  have hyC : y ∈ centralizer ({x} : Set G) := hy.1.2.2.1
  obtain ⟨c, hcC, hcy⟩ := exists_conj_mem_sylow hh.sylowT hyC hy.1.2.1
  have hcM : c ∈ M := hh.centralizer_le hcC
  have hy' : c⁻¹ * y * c ∈ (T ⊓ K) ⊔ Q := by rw [hRT]; exact hcy
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_mul_of_mem_sup_of_commute hcomm hy'
  have e1 : y = c * (p * q) * c⁻¹ := by rw [← hpq]; group
  have hpK : c * p * c⁻¹ ∈ K := hh.L_normal.2 c hcM p hp.2
  have hqC : c * q * c⁻¹ ∈ CMK M K := conj_mem_CMK hh.L_normal.2 hcM (hh.sylowQ.le hq)
  have hmem : y ∈ K ⊔ centralizerSection K (pPrimeCoreOf 2 K) := by
    have e2 : c * (p * q) * c⁻¹ = (c * p * c⁻¹) * (c * q * c⁻¹) := by group
    rw [e1, e2]
    exact Subgroup.mul_mem_sup hpK hqC.2
  exact h102a G hG x y K hy hFM hmem

end CFSG.GH74.GLS.C3.Layer1.Back
