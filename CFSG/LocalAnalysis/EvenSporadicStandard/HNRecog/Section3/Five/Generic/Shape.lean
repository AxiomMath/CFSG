module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type*} [Group G]

theorem nonempty_quotient_mulEquiv_of_complement {K N T : Subgroup G} (hNK : N ≤ K)
    (hNn : (N.subgroupOf K).Normal) (hT : T ≤ K) (hinf : N ⊓ T = ⊥) (hsup : N ⊔ T = K) :
    Nonempty (↥K ⧸ N.subgroupOf K ≃* ↥T) := by
  haveI : (N.subgroupOf K).Normal := hNn
  let ψ : ↥T →* (↥K) ⧸ N.subgroupOf K :=
    (QuotientGroup.mk' (N.subgroupOf K)).comp (Subgroup.inclusion hT)
  have hker : MonoidHom.ker ψ = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have htN : (t : G) ∈ N := by
      change (QuotientGroup.mk' (N.subgroupOf K)) (Subgroup.inclusion hT t) = 1 at ht
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ht
      exact ht
    have hmem : (t : G) ∈ N ⊓ T := ⟨htN, t.2⟩
    rw [hinf] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  refine ⟨(MulEquiv.ofBijective ψ ⟨?_, ?_⟩).symm⟩
  · exact (MonoidHom.ker_eq_bot_iff ψ).mp hker
  · intro q
    refine QuotientGroup.induction_on q fun k => ?_
    have hsup' : N.subgroupOf K ⊔ T.subgroupOf K = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hNK hT, hsup, Subgroup.subgroupOf_self]
    have hk : k ∈ N.subgroupOf K ⊔ T.subgroupOf K := by
      rw [hsup']; exact Subgroup.mem_top k
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hk
    let t : ↥T := ⟨z.1, Subgroup.mem_subgroupOf.mp hz⟩
    have ht : Subgroup.inclusion hT t = z := by ext; rfl
    refine ⟨t, ?_⟩
    show (QuotientGroup.mk' (N.subgroupOf K)) (Subgroup.inclusion hT t) =
      (QuotientGroup.mk' (N.subgroupOf K)) k
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨z⁻¹ * y * z, ?_, ?_⟩
    · simpa using hNn.conj_mem y hy z⁻¹
    · rw [ht]
      calc z * (z⁻¹ * y * z) = y * z := by rw [← mul_assoc, mul_inv_cancel_left]
        _ = k := hyz

theorem isShapeFiveCubeByTwoTwo_of_le {K L N : Subgroup G} [Finite K] (hLK : L ≤ K) (hNK : N ≤ K)
    (hNn : (N.subgroupOf K).Normal) (hN5 : IsPGroup 5 ↥N)
    (hKN : Nonempty (↥K ⧸ N.subgroupOf K ≃* Elem2 2)) (hL : Nat.card ↥L = 4 * 5 ^ 3) :
    IsShapeFiveCubeByTwoTwo ↥L := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : (N.subgroupOf K).Normal := hNn
  haveI : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion hLK) (Subgroup.inclusion_injective hLK)
  have hN'normal : (N.subgroupOf L).Normal := by
    have h := hNn.comap (Subgroup.inclusion hLK)
    rwa [Subgroup.comap_inclusion_subgroupOf hLK N] at h
  haveI : (N.subgroupOf L).Normal := hN'normal
  have hN'5 : IsPGroup 5 (N.subgroupOf L) := by
    let f : ↥(N.subgroupOf L) →* ↥N :=
      { toFun := fun x => ⟨(x.1 : G), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hN5.of_injective f fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : ↥N => (x : G)) h))
  have hElem : Nat.card (Elem2 2) = 4 := by
    show Nat.card (Multiplicative (Fin 2 → ZMod 2)) = 4
    rw [Nat.card_congr
      (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 2) ≃ (Fin 2 → ZMod 2))]
    rw [Nat.card_fun, Nat.card_zmod]
    simp [Nat.card_eq_fintype_card]
  let φ : ↥L →* (↥K) ⧸ (N.subgroupOf K) :=
    (QuotientGroup.mk' (N.subgroupOf K)).comp (Subgroup.inclusion hLK)
  have hker : MonoidHom.ker φ = N.subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk' (N.subgroupOf K)) (Subgroup.inclusion hLK x) = 1 ↔ (x : G) ∈ N
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_inclusion]
  have hlift_inj : Function.Injective (QuotientGroup.lift (N.subgroupOf L) φ hker.ge) :=
    (QuotientGroup.injective_lift_iff (N := N.subgroupOf L) φ hker.ge).mpr hker.symm
  haveI : Finite ((↥K) ⧸ (N.subgroupOf K)) :=
    Finite.of_surjective (QuotientGroup.mk' (N.subgroupOf K))
      (QuotientGroup.mk'_surjective (N := N.subgroupOf K))
  obtain ⟨e⟩ := hKN
  have hcardKN : Nat.card ((↥K) ⧸ (N.subgroupOf K)) = 4 :=
    (Nat.card_congr e.toEquiv).trans hElem
  have hd_le : Nat.card ((↥L) ⧸ (N.subgroupOf L)) ≤ 4 := by
    have hle := Nat.card_le_card_of_injective
      (QuotientGroup.lift (N.subgroupOf L) φ hker.ge) hlift_inj
    rwa [hcardKN] at hle
  set d : ℕ := Nat.card ((↥L) ⧸ (N.subgroupOf L)) with hd
  set n : ℕ := Nat.card (N.subgroupOf L) with hn
  have hd_le' : d ≤ 4 := by rw [hd]; exact hd_le
  have hmul : Nat.card ↥L = d * n := by
    rw [hd, hn]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf L)
  have hdn : d * n = 4 * 5 ^ 3 := by
    rw [← hmul, hL]
  haveI : Nonempty ((↥L) ⧸ (N.subgroupOf L)) := ⟨1⟩
  have hd_ge : 1 ≤ d := by
    rw [hd]
    exact Nat.card_pos
  have hn_le : n ≤ 4 * 5 ^ 3 := by
    have h1 : n * 1 ≤ n * d := Nat.mul_le_mul_left n hd_ge
    rw [mul_one, mul_comm n d, hdn] at h1
    exact h1
  have hn_ge : 5 ^ 3 ≤ n := by
    have h1 : d * n ≤ 4 * n := Nat.mul_le_mul_right n hd_le'
    rw [hdn] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by norm_num)
  obtain ⟨m, hm⟩ := hN'5.exists_card_eq
  have hnm : n = 5 ^ m := by
    rw [hn]
    exact hm
  have hm_ge : 3 ≤ m := by
    have h : 5 ^ 3 ≤ 5 ^ m := by rw [← hnm]; exact hn_ge
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).mp h
  have hm_le : m ≤ 3 := by
    by_contra h
    have hm4 : 4 ≤ m := by omega
    have hge : 5 ^ 4 ≤ 5 ^ m :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).mpr hm4
    have hle : 5 ^ m ≤ 4 * 5 ^ 3 := by rw [← hnm]; exact hn_le
    norm_num at hge hle
    omega
  have hn_eq : n = 5 ^ 3 := by
    rw [hnm, le_antisymm hm_le hm_ge]
  have hd_eq : d = 4 := by
    have h : d * 5 ^ 3 = 4 * 5 ^ 3 := by
      have := hdn
      rw [hn_eq] at this
      exact this
    norm_num at h
    omega
  have hcardN' : Nat.card (N.subgroupOf L) = 5 ^ 3 := by rw [← hn]; exact hn_eq
  have hdquot : Nat.card ((↥L) ⧸ (N.subgroupOf L)) = 4 := by rw [← hd]; exact hd_eq
  refine ⟨N.subgroupOf L, hN'normal, hN'5, hcardN', ?_⟩
  let e' : (↥L) ⧸ (N.subgroupOf L) →* Elem2 2 :=
    e.toMonoidHom.comp (QuotientGroup.lift (N.subgroupOf L) φ hker.ge)
  refine ⟨MulEquiv.ofBijective e' ?_⟩
  refine (Nat.bijective_iff_injective_and_card e').mpr ⟨?_, ?_⟩
  · intro a b hab
    exact hlift_inj (e.injective hab)
  · rw [hdquot, hElem]

theorem eq_of_le_of_card_le {K L : Subgroup G} [Finite K] (hLK : L ≤ K)
    (hcard : Nat.card ↥K ≤ Nat.card ↥L) : L = K :=
  Subgroup.eq_of_le_of_card_ge hLK hcard

end CFSG.EvenSporadicStandard.HNRecog.Section3
