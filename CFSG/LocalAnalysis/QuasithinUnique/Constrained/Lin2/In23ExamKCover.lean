module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.J4SChain

public section

namespace CFSG.QuasithinUnique.Lin2

@[expose] def oddCentral (K : Type) [Group K] : Subgroup K where
  carrier := {z | z ∈ Subgroup.center K ∧ Odd (orderOf z)}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hao⟩ ⟨hb, hbo⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    have hcomm : Commute a b := Subgroup.mem_center_iff.mp hb a
    have hdvd : orderOf (a * b) ∣ orderOf a * orderOf b := hcomm.orderOf_mul_dvd_mul_orderOf
    exact (hao.mul hbo).of_dvd_nat hdvd
  inv_mem' := by
    rintro a ⟨ha, hao⟩
    exact ⟨Subgroup.inv_mem _ ha, by rwa [orderOf_inv]⟩

theorem oddCentral_normal (K : Type) [Group K] : (oddCentral K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h1 := Subgroup.mem_center_iff.mp hn.1 g
  have h2 : g * n * g⁻¹ = n := by rw [h1, mul_inv_cancel_right]
  rw [h2]
  exact hn

theorem center_no_involution_of_cover {K X : Type} [Group K] [Finite K] [Group X] [Finite X]
    (hperf : Group.IsPerfect K) (θ : K →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker = Subgroup.center K)
    (hcover : ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E → ∀ η : E →* X,
      Function.Surjective η → η.ker ≤ Subgroup.center E → IsPGroup 2 η.ker → η.ker = ⊥) :
    ∀ z ∈ Subgroup.center K, z ^ 2 = 1 → z = 1 := by
  intro z hz hz2
  by_contra hz1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (oddCentral K).Normal := oddCentral_normal K
  have : Group.IsPerfect K := hperf
  have hHker : ∀ x ∈ oddCentral K, θ x = 1 := fun x hx => by
    have : x ∈ θ.ker := by rw [hker]; exact hx.1
    simpa using this
  let η : K ⧸ oddCentral K →* X := QuotientGroup.lift (oddCentral K) θ hHker
  have hηmk : ∀ c : K, η (QuotientGroup.mk c) = θ c := fun c => rfl
  have hηsurj : Function.Surjective η := by
    intro x
    obtain ⟨k, rfl⟩ := hθ x
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hkerc : ∀ c : K, θ c = 1 → c ∈ Subgroup.center K := fun c hc => by
    rw [← hker]; exact hc
  have hηker : ∀ y ∈ η.ker, ∃ c ∈ Subgroup.center K, y = QuotientGroup.mk c := by
    intro y hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨c, hkerc c (by rw [← hηmk]; exact hy), rfl⟩
  have hcentral : η.ker ≤ Subgroup.center (K ⧸ oddCentral K) := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := hηker y hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hc k]
  have hp : IsPGroup 2 η.ker := by
    intro y
    obtain ⟨c, hc, hy⟩ := hηker y y.2
    obtain ⟨a, k', hk', hord⟩ := Nat.exists_eq_two_pow_mul_odd
      (n := orderOf c) (orderOf_pos c).ne'
    refine ⟨a, ?_⟩
    apply Subtype.ext
    have hdvd : 2 ^ a ∣ orderOf c := ⟨k', hord⟩
    have hcpow : c ^ (2 ^ a) ∈ oddCentral K := by
      refine ⟨Subgroup.pow_mem _ hc _, ?_⟩
      rw [orderOf_pow_of_dvd (pow_ne_zero a (by norm_num)) hdvd, hord,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hk'
    change ((y : K ⧸ oddCentral K)) ^ (2 ^ a) = 1
    rw [hy, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hcpow
  have hbot := hcover (K ⧸ oddCentral K) inferInstance η hηsurj hcentral hp
  have hzker : (QuotientGroup.mk z : K ⧸ oddCentral K) ∈ η.ker := by
    have : θ z = 1 := by
      have : z ∈ θ.ker := by rw [hker]; exact hz
      simpa using this
    rw [MonoidHom.mem_ker, hηmk]
    exact this
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzker
  have hodd := hzker.2
  rw [orderOf_eq_prime hz2 hz1] at hodd
  exact absurd hodd (by decide)

end CFSG.QuasithinUnique.Lin2
