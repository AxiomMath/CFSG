module

public import CFSG.GH74.GLS.C3.Layer1.Thm1A7Loc
public import CFSG.GH74.GLS.C3.Layer1.Thm1GlueJ
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33RF
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3A7

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1G33
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1A7

section TStruct

variable {G : Type} [Group G] [Finite G] {x y : G} {K T : Subgroup G} {f z : G}

theorem A7Env.hTC (E : A7Env x y K T f z) : T ≤ centralizer ({x} : Set G) :=
  E.hsetup.sylowT.le

theorem A7Env.hfC (E : A7Env x y K T f z) : f ∈ centralizer ({x} : Set G) := E.hTC E.hfT

theorem A7Env.hKC (E : A7Env x y K T f z) : K ≤ centralizer ({x} : Set G) := E.hu2.1.1.2.1

theorem A7Env.hf2' (E : A7Env x y K T f z) : f * f = 1 := by
  have := pow_orderOf_eq_one f
  rwa [E.hf2, sq] at this

theorem A7Env.hz2' (E : A7Env x y K T f z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [E.hz2, sq] at this

theorem A7Env.hx1 (E : A7Env x y K T f z) : x ≠ 1 := fun h => by
  have := E.hu2.1.1.1; rw [h, orderOf_one] at this; omega

theorem A7Env.hz1 (E : A7Env x y K T f z) : z ≠ 1 := fun h => by
  have := E.hz2; rw [h, orderOf_one] at this; omega

theorem A7Env.hxT (E : A7Env x y K T f z) : x ∈ T :=
  Back.mem_of_isSylowOf_of_central E.hsetup.sylowT (mem_centralizer_singleton_iff.2 rfl)
    (fun _ hs => mem_centralizer_singleton_iff.1 hs) E.hu2.1.1.1

theorem A7Env.hxcommK (E : A7Env x y K T f z) : ∀ q ∈ K, q * x = x * q := fun _ hq =>
  mem_centralizer_singleton_iff.1 (E.hKC hq)

theorem A7Env.hPK (E : A7Env x y K T f z) : IsSylowOf 2 (T ⊓ K) K :=
  E.hsetup.sylowT.inf_of_le_normalizer E.hKC (fun c hc => U1a.mem_normalizer_of_norm E.hKN hc)

theorem A7Env.hcen (E : A7Env x y K T f z) :
    Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) := conj_injective_of_A7 E.e7.some

theorem A7Env.hxker (E : A7Env x y K T f z) :
    Back.actHom E.hKN ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ = 1 :=
  (Back.actHom_eq_one_iff_commutator_mem E.hKN _).2 (fun k hk => by
    have : ⁅k, x⁆ = 1 := by
      rw [commutatorElement_def, E.hxcommK k hk]
      group
    rw [this]
    exact (pPrimeCoreOf 2 K).one_mem)

theorem A7Env.hPker (E : A7Env x y K T f z) :
    ∀ p ∈ T ⊓ K, ∀ hp : p ∈ centralizer ({x} : Set G), Back.actHom E.hKN ⟨p, hp⟩ = 1 → p = 1 := by
  intro p hpP hpC hφ
  have hpK : p ∈ K := hpP.2
  have h1 := Back.actHom_of_mem E.hKN hpK hpC
  have h2 : MulAut.conj (QuotientGroup.mk (⟨p, hpK⟩ : ↥K) : kBar K) = MulAut.conj 1 := by
    rw [map_one, ← h1]
    exact hφ
  have h3 := E.hcen h2
  have h4 : (⟨p, hpK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h3
  have h5 : p ∈ pPrimeCoreOf 2 K := Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hpK, h4⟩
  have h6 := Back.Setup91.inf_pPrimeCoreOf_eq_bot K E.hPK.isPGroup
  have h7 : p ∈ (T ⊓ K) ⊓ pPrimeCoreOf 2 K := ⟨hpP, h5⟩
  rw [h6, Subgroup.mem_bot] at h7
  exact h7

theorem A7Env.card_P (E : A7Env x y K T f z) : Nat.card ↥(T ⊓ K) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := E.hPK.card_eq
  have hK : Nat.card ↥K = Nat.card (pPrimeCore 2 ↥K) * Nat.card (kBar K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K), mul_comm]
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcard : Nat.card (kBar K) = 2520 := Thm1L34.card_kBar_of_alt7 E.e7
  rw [hK, hcard, Thm1L3A7.factorization_two_mul_odd hodd (by norm_num)] at h1
  rw [h1]
  have : (2520 : ℕ).factorization 2 = 3 := by
    have h2520 : (2520 : ℕ) = 2 ^ 3 * 315 := by norm_num
    rw [h2520, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [this]
  norm_num

theorem A7Env.hxmemCMK (E : A7Env x y K T f z) : x ∈ CxK x K := by
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hker : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom E.hKN).ker := E.hxker
  rw [Back.actHom_ker E.hKN] at hker
  exact hker

theorem A7Env.hPnorm (E : A7Env x y K T f z) :
    ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
  ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), E.hKN t (E.hTC ht) p hp.2⟩

theorem A7Env.hQnorm (E : A7Env x y K T f z) :
    ∀ t ∈ T, ∀ q ∈ T ⊓ CxK x K, t * q * t⁻¹ ∈ T ⊓ CxK x K := fun t ht q hq =>
  ⟨T.mul_mem (T.mul_mem ht hq.1) (T.inv_mem ht), P34Real.CMK_conj E.hKN (E.hTC ht) hq.2⟩

theorem A7Env.hQcentP (E : A7Env x y K T f z) :
    ∀ q ∈ T ⊓ CxK x K, ∀ p ∈ T ⊓ K, q * p = p * q := by
  intro q hq p hp
  have hqC : q ∈ centralizer ({x} : Set G) := E.hTC hq.1
  have hφ : Back.actHom E.hKN ⟨q, hqC⟩ = 1 := by
    have : (⟨q, hqC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom E.hKN).ker := by
      rw [Back.actHom_ker E.hKN]
      exact hq.2
    exact this
  have hcom := (Back.actHom_eq_one_iff_commutator_mem E.hKN ⟨q, hqC⟩).1 hφ p hp.2
  have hPmem : ⁅p, q⁆ ∈ T ⊓ K := by
    have : ⁅p, q⁆ = p * (q * p⁻¹ * q⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact (T ⊓ K).mul_mem hp (E.hPnorm q hq.1 p⁻¹ ((T ⊓ K).inv_mem hp)) |> fun h => by
      simpa [mul_assoc] using h
  have h6 := Back.Setup91.inf_pPrimeCoreOf_eq_bot K E.hPK.isPGroup
  have h7 : ⁅p, q⁆ ∈ (T ⊓ K) ⊓ pPrimeCoreOf 2 K := ⟨hPmem, hcom⟩
  rw [h6, Subgroup.mem_bot, commutatorElement_def] at h7
  calc q * p = (p * q * p⁻¹ * q⁻¹) * (q * p) := by rw [h7]; group
    _ = p * q := by group

theorem A7Env.hPQ (E : A7Env x y K T f z) : (T ⊓ K) ⊓ (T ⊓ CxK x K) = ⊥ := by
  rw [eq_bot_iff]
  rintro p ⟨hpP, hpQ⟩
  rw [Subgroup.mem_bot]
  have hpC : p ∈ centralizer ({x} : Set G) := E.hTC hpP.1
  apply E.hPker p hpP hpC
  have : (⟨p, hpC⟩ : ↥(centralizer ({x} : Set G))) ∈ (Back.actHom E.hKN).ker := by
    rw [Back.actHom_ker E.hKN]
    exact hpQ.2
  exact this

theorem A7Env.hQ_unique (E : A7Env x y K T f z) :
    ∀ u ∈ T ⊓ CxK x K, u * u = 1 → u = 1 ∨ u = x := by
  intro u hu huu
  by_contra hcon
  push Not at hcon
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact huu) hcon.1
  have hcomm : u * x = x * u :=
    (mem_centralizer_singleton_iff.1 (E.hTC hu.1))
  have := U1a.two_le_pRank_of_commute (D := CxK x K) hu.2 E.hxmemCMK hu2 E.hu2.1.1.1 hcomm hcon.2
  have := E.hrk
  omega

theorem A7Env.outer_mul_inn (E : A7Env x y K T f z) {σ τ : MulAut (kBar K)}
    (hσ : σ ∉ innAut (kBar K)) (hτ : τ ∉ innAut (kBar K)) : σ * τ⁻¹ ∈ innAut (kBar K) := by
  have hinn : ∀ a : MulAut (kBar K), psiEquiv E.e7.some a ∈ alternatingGroup (Fin 7) ↔
      a ∈ innAut (kBar K) := by
    intro a
    have h := (Subgroup.mem_map_equiv (f := psiEquiv E.e7.some) (K := innAut (kBar K))
      (x := psiEquiv E.e7.some a))
    rw [psi_map_innAut E.e7.some] at h
    simpa using h
  have hs : ∀ a : MulAut (kBar K), a ∉ innAut (kBar K) →
      Equiv.Perm.sign (psiEquiv E.e7.some a) = -1 := by
    intro a ha
    rcases Int.units_eq_one_or (Equiv.Perm.sign (psiEquiv E.e7.some a)) with h | h
    · exact absurd ((hinn a).1 (Equiv.Perm.mem_alternatingGroup.2 h)) ha
    · exact h
  rw [← hinn, Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_inv, hs σ hσ, hs τ hτ]
  decide

theorem A7Env.exists_mem_PQ_of_inn (E : A7Env x y K T f z) :
    ∀ n (hn : n ∈ T), Back.actHom E.hKN ⟨n, E.hTC hn⟩ ∈ innAut (kBar K) →
      ∃ p ∈ T ⊓ K, ∃ q ∈ T ⊓ CxK x K, n = p * q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥T →* MulAut (kBar K) := (Back.actHom E.hKN).comp (Subgroup.inclusion E.hTC)
  set P' : Subgroup ↥T := (T ⊓ K).subgroupOf T with hP'
  have hker : ∀ p ∈ P', ρ p = 1 → p = 1 := by
    intro p hp hρp
    have hpP : (p : G) ∈ T ⊓ K := hp
    exact Subtype.ext (E.hPker (p : G) hpP (E.hTC p.2) hρp)
  have hPE : ∀ p ∈ P', ρ p ∈ innAut (kBar K) := by
    intro p hp
    have hpP : (p : G) ∈ T ⊓ K := hp
    show Back.actHom E.hKN ⟨(p : G), E.hTC p.2⟩ ∈ innAut (kBar K)
    rw [Back.actHom_of_mem E.hKN hpP.2 (E.hTC p.2)]
    exact ⟨_, rfl⟩
  have hE : Nat.card ↥(innAut (kBar K)) = Nat.card (kBar K) :=
    (Nat.card_congr (MonoidHom.ofInjective E.hcen).toEquiv).symm
  have hcard : ∀ j : ℕ, 2 ^ j ∣ Nat.card ↥(innAut (kBar K)) → 2 ^ j ≤ Nat.card ↥P' := by
    intro j hj
    rw [hE] at hj
    have h2 : 2 ^ j ∣ Nat.card ↥K := hj.trans (Subgroup.card_quotient_dvd_card _)
    have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
    have h3 : j ≤ (Nat.card ↥K).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hK0).1 h2
    have h4 : Nat.card ↥P' = Nat.card ↥(T ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ K ≤ T)).toEquiv
    rw [h4, E.hPK.card_eq]
    exact Nat.pow_le_pow_right (by norm_num) h3
  have himg := image_inf_eq_image E.hsetup.sylowT.isPGroup ρ (innAut (kBar K)) P' hker hPE hcard
  intro n hn hinn
  obtain ⟨p, hp, hpn⟩ := himg ⟨n, hn⟩ hinn
  have hpP : (p : G) ∈ T ⊓ K := hp
  have hcN : (p : G)⁻¹ * n ∈ T := T.mul_mem (T.inv_mem p.2) hn
  have hcC : (p : G)⁻¹ * n ∈ centralizer ({x} : Set G) := E.hTC hcN
  have hφc : Back.actHom E.hKN ⟨(p : G)⁻¹ * n, hcC⟩ = 1 := by
    have h1 : (⟨(p : G)⁻¹ * n, hcC⟩ : ↥(centralizer ({x} : Set G))) =
        (⟨(p : G), E.hTC p.2⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * ⟨n, E.hTC hn⟩ := rfl
    rw [h1, map_mul, map_inv]
    have h' : Back.actHom E.hKN ⟨(p : G), E.hTC p.2⟩ = Back.actHom E.hKN ⟨n, E.hTC hn⟩ := hpn
    rw [h']
    group
  have hcmk : (p : G)⁻¹ * n ∈ CxK x K := by
    have hkerc : (⟨(p : G)⁻¹ * n, hcC⟩ : ↥(centralizer ({x} : Set G))) ∈
        (Back.actHom E.hKN).ker := hφc
    rw [Back.actHom_ker E.hKN] at hkerc
    exact hkerc
  refine ⟨p, hpP, (p : G)⁻¹ * n, ⟨hcN, hcmk⟩, ?_⟩
  group

theorem A7Env.T_decomp (E : A7Env x y K T f z) :
    ∀ t ∈ T, (∃ p ∈ T ⊓ K, ∃ q ∈ T ⊓ CxK x K, t = p * q) ∨
      (∃ p ∈ T ⊓ K, ∃ q ∈ T ⊓ CxK x K, t = p * q * f) := by
  intro t ht
  by_cases hin : Back.actHom E.hKN ⟨t, E.hTC ht⟩ ∈ innAut (kBar K)
  · exact Or.inl (E.exists_mem_PQ_of_inn t ht hin)
  · right
    have hft : t * f⁻¹ ∈ T := T.mul_mem ht (T.inv_mem E.hfT)
    have hinn' : Back.actHom E.hKN ⟨t * f⁻¹, E.hTC hft⟩ ∈ innAut (kBar K) := by
      have h1 : (⟨t * f⁻¹, E.hTC hft⟩ : ↥(centralizer ({x} : Set G))) =
          ⟨t, E.hTC ht⟩ * (⟨f, E.hfC⟩ : ↥(centralizer ({x} : Set G)))⁻¹ := rfl
      rw [h1, map_mul, map_inv]
      exact E.outer_mul_inn hin E.hfout
    obtain ⟨p, hp, q, hq, hpq⟩ := E.exists_mem_PQ_of_inn _ hft hinn'
    exact ⟨p, hp, q, hq, by rw [← hpq]; group⟩

end TStruct

end CFSG.GH74.GLS.C3.Layer1.Thm1A7

end
