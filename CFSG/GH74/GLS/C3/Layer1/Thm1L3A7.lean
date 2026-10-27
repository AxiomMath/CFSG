module

public import CFSG.GH74.GLS.C3.Layer1.Thm1L3Aux
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3L34
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L3A7

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1

variable {G : Type} [Group G]

theorem card_le_32_of_A7 [Finite G] {f : G} (hf2 : orderOf f = 2) {V J : Subgroup G}
    (hVp : IsPGroup 2 ↥V) (hVC : V ≤ centralizer ({f} : Set G)) (hJC : J ≤ centralizer ({f} : Set G))
    (hJn : ∀ c ∈ centralizer ({f} : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (e : kBar J ≃* alternatingGroup (Fin 7)) (hS : IsSylowOf 2 (zpowers f) (CxK f J)) :
    Nat.card ↥V ≤ 32 := by
  obtain ⟨ψ, hψ⟩ := Back.lemma113d_ne6 hJC hJn (by norm_num : 5 ≤ 7) (by norm_num : 7 ≠ 6) e
  let ρ : ↥V →* Equiv.Perm (Fin 7) := ψ.comp (Subgroup.inclusion hVC)
  have hρker : ∀ v : ↥V, ρ v = 1 → (v : G) ∈ CxK f J := by
    intro v hv
    have h1 : Subgroup.inclusion hVC v ∈ ψ.ker := hv
    rw [hψ, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hker2 : Nat.card ↥ρ.ker ≤ 2 := by
    have hN : IsPGroup 2 ↥(ρ.ker.map V.subtype) := hVp.to_le (Subgroup.map_subtype_le _)
    have hNC : ρ.ker.map V.subtype ≤ CxK f J := by
      rintro _ ⟨v, hv, rfl⟩
      exact hρker v hv
    have h1 := Thm1L3.card_le_of_isPGroup_of_isSylowOf hN hNC hS
    rw [Subgroup.card_map_of_injective V.subtype_injective, Nat.card_zpowers, hf2] at h1
    exact h1
  have hrange : Nat.card ↥ρ.range ≤ 16 := by
    have hp : IsPGroup 2 ↥ρ.range := hVp.of_surjective ρ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ρ)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hp
    have hdvd : Nat.card ↥ρ.range ∣ Nat.card (Equiv.Perm (Fin 7)) :=
      Subgroup.card_subgroup_dvd_card ρ.range
    have h5040 : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    rw [h5040, hm] at hdvd
    rw [hm]
    by_contra hlt
    push Not at hlt
    have hm5 : 5 ≤ m := by
      by_contra hm5
      push Not at hm5
      have : 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h32 : 2 ^ 5 ∣ 2 ^ m := pow_dvd_pow 2 hm5
    have := h32.trans hdvd
    revert this
    decide
  have hcard : Nat.card ↥V = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  rw [hcard]
  calc Nat.card ↥ρ.range * Nat.card ↥ρ.ker ≤ 16 * 2 := Nat.mul_le_mul hrange hker2
    _ = 32 := by norm_num

theorem factorization_two_mul_odd {n m : ℕ} (hn : Odd n) (hm : m ≠ 0) :
    (n * m).factorization 2 = m.factorization 2 := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  rw [Nat.factorization_mul hn0 hm, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.odd_iff, Nat.two_dvd_ne_zero] using hn),
    zero_add]

theorem card_sylow_eq_eight [Finite G] {P K : Subgroup G} (hP : IsSylowOf 2 P K)
    (hK25 : HasL2Model (kBar K) (fun q => q = 5 ^ 2)) : Nat.card ↥P = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hP.card_eq
  have hK : Nat.card ↥K = Nat.card (pPrimeCore 2 ↥K) * Nat.card (kBar K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K), mul_comm]
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcard : Nat.card (kBar K) = 7800 := by
    rw [Thm1L34.card_kBar_of_hasL2Model hK25, show (5 : ℕ) ^ 2 = 25 by norm_num,
      Thm1L34.ordA_one_25]
  rw [hK, hcard, factorization_two_mul_odd hodd (by norm_num)] at h1
  rw [h1]
  have : (7800 : ℕ).factorization 2 = 3 := by
    have h7800 : (7800 : ℕ) = 2 ^ 3 * 975 := by norm_num
    rw [h7800, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [this]
  norm_num

open scoped commutatorElement in
theorem card_ge_32_of_L2_25 [Finite G] {x : G} {K T : Subgroup G} (hx2 : orderOf x = 2)
    (hKC : K ≤ centralizer ({x} : Set G))
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hK25 : HasL2Model (kBar K) (fun q => q = 5 ^ 2)) (hcen : center (kBar K) = ⊥)
    (hout : ∃ (f' : G) (hf' : f' ∈ T), Back.actHom hKN ⟨f', hT.le hf'⟩ ∉ IVK.innAut (kBar K)) :
    32 ≤ Nat.card ↥T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f', hf'T, hf'out⟩ := hout
  let ρ : ↥T →* MulAut (kBar K) := (Back.actHom hKN).comp (Subgroup.inclusion hT.le)
  have hKnorm : centralizer ({x} : Set G) ≤ normalizer (K : Set G) := fun c hc =>
    Thm1L3.mem_normalizer_of_conj_le (hKN c hc)
  have hPsyl : IsSylowOf 2 (T ⊓ K) K := hT.inf_of_le_normalizer hKC hKnorm
  have hP8 : Nat.card ↥(T ⊓ K) = 8 := card_sylow_eq_eight hPsyl hK25
  let ρP : ↥(T ⊓ K) →* MulAut (kBar K) := ρ.comp (Subgroup.inclusion inf_le_left)
  have hρP_act : ∀ v : ↥(T ⊓ K),
      ρP v = MulAut.conj (QuotientGroup.mk (⟨(v : G), v.2.2⟩ : ↥K) : kBar K) :=
    fun v => Back.actHom_of_mem hKN v.2.2 (hT.le v.2.1)
  have hρP_inj : Function.Injective ρP := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have h1 : ρP v = 1 := hv
    rw [hρP_act] at h1
    have h2 : (QuotientGroup.mk (⟨(v : G), v.2.2⟩ : ↥K) : kBar K) ∈ center (kBar K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun a : MulAut (kBar K) => a g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h2
    have hodd : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥K)) := pPrimeCore_coprime_card
    have h3 : orderOf (v : G) ∣ Nat.card (pPrimeCore 2 ↥K) := by
      have := orderOf_dvd_natCard (⟨_, h2⟩ : ↥(pPrimeCore 2 ↥K))
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at this
    have h4 : orderOf (v : G) ∣ 8 := by
      have := orderOf_dvd_natCard v
      rw [hP8, ← Subgroup.orderOf_coe] at this
      exact this
    have h8 : Nat.Coprime 8 (Nat.card (pPrimeCore 2 ↥K)) := by
      simpa using Nat.Coprime.pow_left 3 hodd
    have h5 : orderOf (v : G) = 1 := Nat.eq_one_of_dvd_coprimes h8 h4 h3
    have h6 : (v : G) = 1 := orderOf_eq_one_iff.1 h5
    exact Subtype.ext h6
  have hle : ρP.range ≤ ρ.range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨Subgroup.inclusion inf_le_left v, rfl⟩
  have hR0 : Nat.card ↥ρP.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρP_inj).toEquiv, hP8]
  have hf'R : ρ ⟨f', hf'T⟩ ∈ ρ.range := ⟨_, rfl⟩
  have hf'notR0 : ρ ⟨f', hf'T⟩ ∉ ρP.range := by
    rintro ⟨v, hv⟩
    apply hf'out
    have h1 : Back.actHom hKN ⟨f', hT.le hf'T⟩ =
        MulAut.conj (QuotientGroup.mk (⟨(v : G), v.2.2⟩ : ↥K) : kBar K) := by
      rw [← hρP_act v, hv]
      rfl
    rw [h1]
    exact ⟨_, rfl⟩
  have hne : ρP.range ≠ ρ.range := fun h => hf'notR0 (h ▸ hf'R)
  have h16 : 16 ≤ Nat.card ↥ρ.range := by
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hle
    have hc1 : c ≠ 1 := by
      rintro rfl
      exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, mul_one]))
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact Nat.card_pos.ne' hc
    rw [hc, hR0]
    omega
  have hxT : x ∈ T :=
    Back.mem_of_isSylowOf_of_central hT (mem_centralizer_singleton_iff.2 rfl)
      (fun _ hs => mem_centralizer_singleton_iff.1 hs) hx2
  have hxk : ρ ⟨x, hxT⟩ = 1 := by
    refine (Back.actHom_eq_one_iff_commutator_mem hKN ⟨x, hT.le hxT⟩).2 (fun k hk => ?_)
    have hxk' : k * x = x * k := mem_centralizer_singleton_iff.1 (hKC hk)
    have : ⁅k, x⁆ = 1 := by
      rw [commutatorElement_def, hxk']
      group
    rw [this]
    exact (pPrimeCoreOf 2 K).one_mem
  have hker2 : 2 ≤ Nat.card ↥ρ.ker := by
    have hz : zpowers (⟨x, hxT⟩ : ↥T) ≤ ρ.ker := by
      rw [zpowers_le]
      exact hxk
    have := Subgroup.card_le_of_le hz
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2] at this
    exact this
  have hcard : Nat.card ↥T = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  rw [hcard]
  calc 32 = 16 * 2 := by norm_num
    _ ≤ Nat.card ↥ρ.range * Nat.card ↥ρ.ker := Nat.mul_le_mul h16 hker2

end CFSG.GH74.GLS.C3.Layer1.Thm1L3A7
