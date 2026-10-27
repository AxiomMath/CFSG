module

public import CFSG.GH74.GLS.Bg.TwoGroups.Vocab
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Pair
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundAut

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20
  CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

open scoped IsMulCommutative

section Q9

theorem central_pow_index_eq_one {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {p : ℕ}
    [Fact p.Prime] (P : Sylow p K) (hPc : ∀ a b : ↥P, a * b = b * a) {y : K}
    (hy : y ∈ Subgroup.center K) : y ^ (P : Subgroup K).index = 1 := by
  classical
  have : IsMulCommutative ↥P := ⟨⟨hPc⟩⟩
  have hkey : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * y ^ k * g₀ ∈ (P : Subgroup K) → g₀⁻¹ * y ^ k * g₀ = y ^ k := by
    intro k g₀ _
    have h1 : g₀ * y ^ k = y ^ k * g₀ := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hy k) g₀
    rw [mul_assoc, ← h1]
    group
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id ↥(P : Subgroup K)) y hkey
  have h2 : MonoidHom.transfer (MonoidHom.id ↥(P : Subgroup K)) y = 1 := by
    have hker : commutator K ≤ (MonoidHom.transfer (MonoidHom.id ↥(P : Subgroup K))).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_inv, map_inv]
      simp [mul_assoc]
    exact hker (Group.IsPerfect.mem_commutator)
  rw [h2] at h1
  have h3 := congrArg Subtype.val h1.symm
  simpa using h3

variable {G : Type} [Group G] [Finite G]

theorem sylow5_comm_of_dvd {K : Type} [Group K] [Finite K] (hK : Nat.card K ∣ 3600) (P : Sylow 5 K) :
    ∀ a b : ↥(P : Subgroup K), a * b = b * a := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card ↥(P : Subgroup K) = 5 ^ (Nat.card K).factorization 5 := Sylow.card_eq_multiplicity P
  have hdvd : Nat.card ↥(P : Subgroup K) ∣ Nat.card K := Subgroup.card_subgroup_dvd_card (P : Subgroup K)
  generalize (Nat.card K).factorization 5 = n at hcard
  rw [hcard] at hdvd
  have hn2 : n ≤ 2 := by
    by_contra hlt
    have hlt' : 3 ≤ n := by omega
    have h125 : 5 ^ 3 ∣ 5 ^ n := pow_dvd_pow 5 hlt'
    have := (h125.trans hdvd).trans hK
    norm_num at this
  interval_cases n
  · have h1 : Nat.card ↥(P : Subgroup K) = 1 := by rw [hcard]; norm_num
    have hs : Subsingleton ↥(P : Subgroup K) := (Nat.card_eq_one_iff_unique.1 h1).1
    intro a b
    exact Subsingleton.elim _ _
  · have h1 : Nat.card ↥(P : Subgroup K) = 5 := by rw [hcard]; norm_num
    have : Fact (Nat.Prime (Nat.card ↥(P : Subgroup K))) := ⟨by rw [h1]; norm_num⟩
    have : IsCyclic ↥(P : Subgroup K) := isCyclic_of_prime_card h1
    intro a b
    exact (IsCyclic.commGroup (α := ↥(P : Subgroup K))).mul_comm a b
  · have h1 : Nat.card ↥(P : Subgroup K) = 5 ^ 2 := by rw [hcard]
    have h2 := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (G := ↥(P : Subgroup K)) h1
    intro a b
    exact h2.is_comm.comm a b


theorem inf_oddCore_eq_one_q9 {z : G} {K : Subgroup G} {L : Subgroup (CentralizerBar z)}
    (hKC : K ≤ Cen z) (hperf : ⁅K, K⁆ = K) (hbar : barOf z K = L)
    (hcen : ∀ (k : G) (hk : k ∈ K), toBar z ⟨k, hKC hk⟩ = 1 → ∀ k' ∈ K, k * k' = k' * k)
    (hL : HasSL2Model ↥L (fun r => r = 9)) (hA5 : Nat.card ↥(OddCore z) ∣ 5) :
    ∀ x ∈ K, x ∈ OddCore z → x = 1 := by
  classical
  obtain ⟨F, iF, fF, hFq, ⟨eL⟩⟩ := hL
  have hFq' : Nat.card F = 9 := hFq
  have hmem : ∀ k : ↥K, toBar z ⟨(k : G), hKC k.2⟩ ∈ L := by
    intro k
    rw [← hbar]
    exact ⟨⟨(k : G), hKC k.2⟩, k.2, rfl⟩
  let β : ↥K →* ↥L :=
    MonoidHom.codRestrict ((toBar z).comp (Subgroup.inclusion hKC)) L (fun k => hmem k)
  have hβsurj : Function.Surjective β := by
    intro l
    have hl : (l : CentralizerBar z) ∈ barOf z K := hbar ▸ l.2
    obtain ⟨y, hy, hyl⟩ := hl
    refine ⟨⟨(y : G), hy⟩, ?_⟩
    apply Subtype.ext
    exact hyl
  have hcardL : Nat.card ↥L = 720 := by
    have h2 : Nat.card ↥L = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Nat.card_congr eL.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv]
    rw [h2, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFq']
    norm_num
  have hcardK : Nat.card ↥K = Nat.card ↥β.ker * Nat.card ↥L := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβsurj).toEquiv] at h1
    rw [h1, mul_comm]
  have hkerA : ∀ k : ↥K, k ∈ β.ker → (k : G) ∈ OddCore z := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have h1 : toBar z ⟨(k : G), hKC k.2⟩ = 1 := congrArg Subtype.val hk
    have h2 : (⟨(k : G), hKC k.2⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := by
      rw [← ker_toBar]; exact h1
    exact ⟨_, h2, rfl⟩
  have hkerdvd : Nat.card ↥β.ker ∣ 5 := by
    let ι : ↥β.ker →* ↥(OddCore z) :=
      { toFun := fun k => ⟨((k : ↥K) : G), hkerA k k.2⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    have hι : Function.Injective ι := by
      intro a b hab
      have h1 : ((a : ↥K) : G) = ((b : ↥K) : G) := congrArg (fun w : ↥(OddCore z) => (w : G)) hab
      exact Subtype.ext (Subtype.ext h1)
    exact (Subgroup.card_dvd_of_injective ι hι).trans hA5
  have hK3600 : Nat.card ↥K ∣ 3600 := by
    rw [hcardK, hcardL]
    have := Nat.mul_dvd_mul_right hkerdvd 720
    simpa using this
  intro x hxK hxA
  by_contra hx1
  have hxA' : (⟨x, hxA⟩ : ↥(OddCore z)) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hord5 : orderOf x = 5 := by
    have h1 : orderOf (⟨x, hxA⟩ : ↥(OddCore z)) ∣ 5 := (_root_.orderOf_dvd_natCard _).trans hA5
    have h2 : orderOf (⟨x, hxA⟩ : ↥(OddCore z)) = orderOf x := Subgroup.orderOf_mk _ _
    rw [h2] at h1
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  let y : ↥K := ⟨x, hxK⟩
  have hy : y ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have h1 : toBar z ⟨x, hKC hxK⟩ = 1 := by
      have : (⟨x, hKC hxK⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := by
        obtain ⟨c, hc, hcx⟩ := hxA
        have : c = ⟨x, hKC hxK⟩ := Subtype.ext hcx
        exact this ▸ hc
      rw [← ker_toBar] at this
      exact this
    exact (hcen x hxK h1 (k : G) k.2).symm
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 ↥K) := inferInstance
  have hPc := sylow5_comm_of_dvd hK3600 P
  have hpow := central_pow_index_eq_one P hPc hy
  have hyord : orderOf y = 5 := by rw [Subgroup.orderOf_mk]; exact hord5
  have hdvd : 5 ∣ (P : Subgroup ↥K).index := by
    have := orderOf_dvd_of_pow_eq_one hpow
    rwa [hyord] at this
  exact P.not_dvd_index hdvd

end Q9

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
