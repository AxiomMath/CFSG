module

public import CFSG.CharacterTheory.Semidihedral.CentralPrimeExtensions
public import CFSG.CharacterTheory.Semidihedral.QuaternionAutomorphismLifting

public section

namespace CFSG.Semidihedral.QuaternionDoubleCoverUniqueness

universe u v w

variable {E : Type u} {G : Type v} [Group E] [Group G]

theorem central_double_cover_kernel_card (z : E) (hz : orderOf z = 2)
    (pi : E →* G) (hker : pi.ker = Subgroup.zpowers z) :
    Nat.card pi.ker = 2 := by
  rw [hker, Nat.card_zpowers, hz]

theorem central_double_cover_kernel_twoGroup (z : E) (hz : orderOf z = 2)
    (pi : E →* G) (hker : pi.ker = Subgroup.zpowers z) : IsPGroup 2 pi.ker := by
  apply IsPGroup.of_card (n := 1)
  simpa using central_double_cover_kernel_card z hz pi hker

@[expose] noncomputable def preimageSylow (z : E) (hz : orderOf z = 2)
    (pi : E →* G) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z) (P : Sylow 2 G) : Sylow 2 E :=
  P.comapOfKerIsPGroup pi (central_double_cover_kernel_twoGroup z hz pi hker)
    (by rw [MonoidHom.range_eq_top.mpr hpi]; exact le_top)

theorem preimageSylow_coe (z : E) (hz : orderOf z = 2)
    (pi : E →* G) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z) (P : Sylow 2 G) :
    (preimageSylow z hz pi hpi hker P : Subgroup E) = (P : Subgroup G).comap pi := rfl

@[expose] def preimageProjection (pi : E →* G) (P : Subgroup G) :
    P.comap pi →* P :=
  (pi.comp (P.comap pi).subtype).codRestrict P (fun x => x.property)

theorem preimageProjection_surjective (pi : E →* G) (hpi : Function.Surjective pi)
    (P : Subgroup G) : Function.Surjective (preimageProjection pi P) := by
  intro g
  obtain ⟨x, hx⟩ := hpi g
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change pi x ∈ P
  rw [hx]
  exact g.property

theorem preimageProjection_ker (pi : E →* G) (P : Subgroup G) :
    (preimageProjection pi P).ker = pi.ker.subgroupOf (P.comap pi) := by
  ext x
  change ((preimageProjection pi P x : P) = 1) ↔ pi x = 1
  exact Subtype.ext_iff

theorem preimageProjection_kernel_card (z : E) (hz : orderOf z = 2)
    (pi : E →* G) (hker : pi.ker = Subgroup.zpowers z) (P : Subgroup G) :
    Nat.card (preimageProjection pi P).ker = 2 := by
  rw [preimageProjection_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (P.ker_le_comap pi)).toEquiv]
  exact central_double_cover_kernel_card z hz pi hker

theorem two_mul_card_preimage (z : E) (hz : orderOf z = 2)
    (pi : E →* G) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z) (P : Subgroup G) :
    2 * Nat.card P = Nat.card (P.comap pi) := by
  have h := Subgroup.card_ker_mul_card_of_surjective (preimageProjection_surjective pi hpi P)
  rwa [preimageProjection_kernel_card z hz pi hker P] at h

theorem central_involution_mem_preimage (z : E)
    (pi : E →* G) (hker : pi.ker = Subgroup.zpowers z) (P : Subgroup G) :
    z ∈ P.comap pi :=
  P.ker_le_comap pi (hker.symm ▸ Subgroup.mem_zpowers z)

theorem quaternion_natCard (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (QuaternionGroup (2 ^ (n - 2))) = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  calc
    4 * 2 ^ (n - 2) = 2 ^ (n - 2) * 2 ^ 2 := by ring
    _ = 2 ^ (n - 2 + 2) := (pow_add 2 (n - 2) 2).symm
    _ = 2 ^ n := by congr 1; omega

theorem preimage_quaternion_equiv [Finite E] [Finite G]
    (z : E) (hz : orderOf z = 2) (pi : E →* G) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z) (S : Sylow 2 E)
    (n : ℕ) (e : S ≃* QuaternionGroup (2 ^ (n - 2))) (P : Sylow 2 G) :
    Nonempty ((P : Subgroup G).comap pi ≃* QuaternionGroup (2 ^ (n - 2))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨(Sylow.equiv (preimageSylow z hz pi hpi hker P) S).trans e⟩

theorem preimageProjection_kernel_eq_center
    (z : E) (hz : orderOf z = 2) (hc : z ∈ Subgroup.center E)
    (pi : E →* G) (hker : pi.ker = Subgroup.zpowers z) (P : Subgroup G)
    (n : ℕ) (hn : 3 ≤ n) (e : P.comap pi ≃* QuaternionGroup (2 ^ (n - 2))) :
    (preimageProjection pi P).ker = Subgroup.center (P.comap pi) := by
  have hm : 2 ≤ 2 ^ (n - 2) := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ n - 2)
  have hcenter : Nat.card (Subgroup.center (P.comap pi)) = 2 := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    change Nat.card ((Subgroup.center (P.comap pi)).map (e : P.comap pi →*
      QuaternionGroup (2 ^ (n - 2)))) = 2
    rw [Subgroup.map_center_eq e]
    exact QuaternionAutomorphismLifting.center_card _ hm
  let : Finite (Subgroup.center (P.comap pi)) :=
    Nat.finite_of_card_ne_zero (by rw [hcenter]; decide)
  have hle : (preimageProjection pi P).ker ≤ Subgroup.center (P.comap pi) := by
    intro x hx
    have hxker : (x : E) ∈ pi.ker := by
      change pi (x : E) = 1
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxcentral : (x : E) ∈ Subgroup.center E :=
      (Subgroup.zpowers_le.mpr hc) (hker ▸ hxker)
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxcentral y
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hcenter, preimageProjection_kernel_card z hz pi hker P]

theorem equiv_over_surjections {S₁ : Type u} {S₂ : Type v} {P : Type w}
    [Group S₁] [Group S₂] [Group P]
    (n : ℕ) (hn : 3 ≤ n)
    (e₁ : S₁ ≃* QuaternionGroup (2 ^ (n - 2)))
    (e₂ : S₂ ≃* QuaternionGroup (2 ^ (n - 2)))
    (pi₁ : S₁ →* P) (hpi₁ : Function.Surjective pi₁)
    (hker₁ : pi₁.ker = Subgroup.center S₁)
    (pi₂ : S₂ →* P) (hpi₂ : Function.Surjective pi₂)
    (hker₂ : pi₂.ker = Subgroup.center S₂) :
    ∃ alpha : S₁ ≃* S₂, ∀ s, pi₂ (alpha s) = pi₁ s := by
  let gamma := e₁.trans e₂.symm
  let c₁ : S₁ ⧸ Subgroup.center S₁ ≃* P :=
    QuotientGroup.liftEquiv (Subgroup.center S₁) hpi₁ hker₁.symm
  let c₂ : S₂ ⧸ Subgroup.center S₂ ≃* P :=
    QuotientGroup.liftEquiv (Subgroup.center S₂) hpi₂ hker₂.symm
  let c : S₁ ⧸ Subgroup.center S₁ ≃* S₂ ⧸ Subgroup.center S₂ :=
    QuotientGroup.congr (Subgroup.center S₁) (Subgroup.center S₂) gamma
      (Subgroup.map_center_eq gamma)
  let delta : MulAut P := c₁.symm.trans (c.trans c₂)
  have hc₁ (s : S₁) : c₁ (QuotientGroup.mk' (Subgroup.center S₁) s) = pi₁ s :=
    QuotientGroup.liftEquiv_mk _ _ _ _
  have hc₂ (s : S₂) : c₂ (QuotientGroup.mk' (Subgroup.center S₂) s) = pi₂ s :=
    QuotientGroup.liftEquiv_mk _ _ _ _
  have hgamma (s : S₁) : pi₂ (gamma s) = delta (pi₁ s) := by
    change pi₂ (gamma s) = c₂ (c (c₁.symm (pi₁ s)))
    rw [← hc₁ s, c₁.symm_apply_apply]
    change pi₂ (gamma s) = c₂ (QuotientGroup.congr _ _ gamma
      (Subgroup.map_center_eq gamma) (QuotientGroup.mk' (Subgroup.center S₁) s))
    rw [QuotientGroup.congr_mk', hc₂]
  obtain ⟨beta, hbeta⟩ := QuaternionAutomorphismLifting.surjection_automorphism_lifts
    n hn e₂.symm pi₂ hpi₂ hker₂ delta.symm
  refine ⟨gamma.trans beta, fun s => ?_⟩
  change pi₂ (beta (gamma s)) = pi₁ s
  rw [hbeta, hgamma, delta.symm_apply_apply]

theorem equiv_carries_quaternion_involution {S₁ : Type u} {S₂ : Type v}
    [Group S₁] [Group S₂] (m : ℕ) (hm : 0 < m)
    (e : S₂ ≃* QuaternionGroup m) (alpha : S₁ ≃* S₂)
    (z₁ : S₁) (hz₁ : orderOf z₁ = 2) (z₂ : S₂) (hz₂ : orderOf z₂ = 2) :
    alpha z₁ = z₂ := by
  apply e.injective
  have h₁ : orderOf (e (alpha z₁)) = 2 := by rw [e.orderOf_eq, alpha.orderOf_eq, hz₁]
  have h₂ : orderOf (e z₂) = 2 := by rw [e.orderOf_eq, hz₂]
  exact ((QuaternionAutomorphismLifting.unique_involution m hm _).mp h₁).trans
    ((QuaternionAutomorphismLifting.unique_involution m hm _).mp h₂).symm

@[expose] noncomputable def involutionEquiv (z : E) (hz : orderOf z = 2) :
    Multiplicative (ZMod 2) ≃* Subgroup.zpowers z :=
  zmodMulEquivOfGenerator (g := (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z))
    (fun x => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.property
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩)
    (by rw [Nat.card_zpowers, hz])

@[expose] noncomputable def involutionEmbedding (z : E) (hz : orderOf z = 2) :
    Multiplicative (ZMod 2) →* E :=
  (Subgroup.zpowers z).subtype.comp (involutionEquiv z hz).toMonoidHom

theorem involutionEmbedding_injective (z : E) (hz : orderOf z = 2) :
    Function.Injective (involutionEmbedding z hz) :=
  (Subgroup.zpowers z).subtype_injective.comp (involutionEquiv z hz).injective

theorem involutionEmbedding_generator (z : E) (hz : orderOf z = 2) :
    involutionEmbedding z hz (Multiplicative.ofAdd 1) = z := by
  change ((involutionEquiv z hz (Multiplicative.ofAdd 1) : Subgroup.zpowers z) : E) = z
  exact congrArg Subtype.val (zmodMulEquivOfGenerator_apply_ofAdd_one _ _)

theorem involutionEmbedding_range (z : E) (hz : orderOf z = 2) :
    (involutionEmbedding z hz).range = Subgroup.zpowers z := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact (involutionEquiv z hz a).property
  · intro hx
    refine ⟨(involutionEquiv z hz).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((involutionEquiv z hz).apply_symm_apply ⟨x, hx⟩)

theorem cyclic_two_card : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem cyclic_two_eq_one_or_generator (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  by_cases ha : a = 1
  · exact Or.inl ha
  · right
    obtain ⟨b, _, hb⟩ := (Nat.card_eq_two_iff' (1 : Multiplicative (ZMod 2))).mp cyclic_two_card
    exact (hb a ha).trans (hb (Multiplicative.ofAdd 1) (by decide)).symm

theorem quaternion_sylow_central_double_cover_uniqueness
    {E₁ : Type u} {E₂ : Type v} {G : Type w}
    [Group E₁] [Group E₂] [Group G] [Finite E₁] [Finite E₂] [Finite G]
    (z₁ : E₁) (hz₁ : orderOf z₁ = 2) (hc₁ : z₁ ∈ Subgroup.center E₁)
    (pi₁ : E₁ →* G) (hpi₁ : Function.Surjective pi₁)
    (hker₁ : pi₁.ker = Subgroup.zpowers z₁)
    (S₁ : Sylow 2 E₁) (n₁ : ℕ) (hn₁ : 3 ≤ n₁)
    (e₁ : S₁ ≃* QuaternionGroup (2 ^ (n₁ - 2)))
    (z₂ : E₂) (hz₂ : orderOf z₂ = 2) (hc₂ : z₂ ∈ Subgroup.center E₂)
    (pi₂ : E₂ →* G) (hpi₂ : Function.Surjective pi₂)
    (hker₂ : pi₂.ker = Subgroup.zpowers z₂)
    (S₂ : Sylow 2 E₂) (n₂ : ℕ) (hn₂ : 3 ≤ n₂)
    (e₂ : S₂ ≃* QuaternionGroup (2 ^ (n₂ - 2))) :
    n₁ = n₂ ∧ ∃ F : E₁ ≃* E₂, (∀ x, pi₂ (F x) = pi₁ x) ∧ F z₁ = z₂ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := Classical.choice inferInstance
  obtain ⟨f₁⟩ := preimage_quaternion_equiv z₁ hz₁ pi₁ hpi₁ hker₁ S₁ n₁ e₁ P
  obtain ⟨f₂⟩ := preimage_quaternion_equiv z₂ hz₂ pi₂ hpi₂ hker₂ S₂ n₂ e₂ P
  have hcard₁ : Nat.card ((P : Subgroup G).comap pi₁) = 2 ^ n₁ :=
    (Nat.card_congr f₁.toEquiv).trans (quaternion_natCard n₁ hn₁)
  have hcard₂ : Nat.card ((P : Subgroup G).comap pi₂) = 2 ^ n₂ :=
    (Nat.card_congr f₂.toEquiv).trans (quaternion_natCard n₂ hn₂)
  have hsamecard : Nat.card ((P : Subgroup G).comap pi₁) =
      Nat.card ((P : Subgroup G).comap pi₂) :=
    (two_mul_card_preimage z₁ hz₁ pi₁ hpi₁ hker₁ P).symm.trans
      (two_mul_card_preimage z₂ hz₂ pi₂ hpi₂ hker₂ P)
  have hparameter : n₁ = n₂ :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) (hcard₁.symm.trans (hsamecard.trans hcard₂))
  subst n₂
  refine ⟨rfl, ?_⟩
  let U₁ := (P : Subgroup G).comap pi₁
  let U₂ := (P : Subgroup G).comap pi₂
  have hcenter₁ : (preimageProjection pi₁ P).ker = Subgroup.center U₁ :=
    preimageProjection_kernel_eq_center z₁ hz₁ hc₁ pi₁ hker₁ P n₁ hn₁ f₁
  have hcenter₂ : (preimageProjection pi₂ P).ker = Subgroup.center U₂ :=
    preimageProjection_kernel_eq_center z₂ hz₂ hc₂ pi₂ hker₂ P n₁ hn₂ f₂
  obtain ⟨alpha, halpha⟩ := equiv_over_surjections n₁ hn₁ f₁ f₂
    (preimageProjection pi₁ P) (preimageProjection_surjective pi₁ hpi₁ P) hcenter₁
    (preimageProjection pi₂ P) (preimageProjection_surjective pi₂ hpi₂ P) hcenter₂
  let t₁ : U₁ := ⟨z₁, central_involution_mem_preimage z₁ pi₁ hker₁ P⟩
  let t₂ : U₂ := ⟨z₂, central_involution_mem_preimage z₂ pi₂ hker₂ P⟩
  have ht₁ : orderOf t₁ = 2 := (Subgroup.orderOf_coe t₁).symm.trans hz₁
  have ht₂ : orderOf t₂ = 2 := (Subgroup.orderOf_coe t₂).symm.trans hz₂
  have halphaz : alpha t₁ = t₂ :=
    equiv_carries_quaternion_involution (2 ^ (n₁ - 2)) (by positivity)
      f₂ alpha t₁ ht₁ t₂ ht₂
  let i₁ := involutionEmbedding z₁ hz₁
  let i₂ := involutionEmbedding z₂ hz₂
  have hk₁ : pi₁.ker = i₁.range := hker₁.trans (involutionEmbedding_range z₁ hz₁).symm
  have hk₂ : pi₂.ker = i₂.range := hker₂.trans (involutionEmbedding_range z₂ hz₂).symm
  have hi₁ : i₁.range ≤ Subgroup.center E₁ := by
    rw [involutionEmbedding_range]
    exact Subgroup.zpowers_le.mpr hc₁
  have hi₂ : i₂.range ≤ Subgroup.center E₂ := by
    rw [involutionEmbedding_range]
    exact Subgroup.zpowers_le.mpr hc₂
  have halphapi : ∀ x : U₁, pi₂ (alpha x) = pi₁ x :=
    fun x => congrArg Subtype.val (halpha x)
  have halphai : ∀ a : Multiplicative (ZMod 2),
      (alpha (CentralPrimeExtensions.kernelInto pi₁ i₁ hk₁ P a) : E₂) = i₂ a := by
    intro a
    rcases cyclic_two_eq_one_or_generator a with rfl | rfl
    · rw [map_one, map_one, map_one]
      rfl
    · have ht : CentralPrimeExtensions.kernelInto pi₁ i₁ hk₁ P
          (Multiplicative.ofAdd 1) = t₁ := by
        apply Subtype.ext
        exact involutionEmbedding_generator z₁ hz₁
      rw [ht, halphaz]
      exact (involutionEmbedding_generator z₂ hz₂).symm
  obtain ⟨F, hFpi, hFi⟩ := CentralPrimeExtensions.central_prime_extensions_determined_on_sylow
    2 Nat.prime_two cyclic_two_card
    i₁ (involutionEmbedding_injective z₁ hz₁) hi₁ pi₁ hpi₁ hk₁
    i₂ (involutionEmbedding_injective z₂ hz₂) hi₂ pi₂ hpi₂ hk₂
    P alpha halphapi halphai
  refine ⟨F, hFpi, ?_⟩
  have h := hFi (Multiplicative.ofAdd 1)
  rwa [involutionEmbedding_generator z₁ hz₁, involutionEmbedding_generator z₂ hz₂] at h

end CFSG.Semidihedral.QuaternionDoubleCoverUniqueness
