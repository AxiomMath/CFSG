module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerTorusIndex

public section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Count

open CFSG.Semidihedral.Principal CFSG.ProperTwoGeneratedCore.CosetNormalizer
open scoped commutatorElement

theorem relIndex_centralizer_eq_ncard {G : Type*} [Group G] (K : Subgroup G) (t : G) :
    (Subgroup.centralizer {t}).relIndex K = {y | ∃ k ∈ K, k * t * k⁻¹ = y}.ncard := by
  rw [← MulAction.stabilizer_comap_conj_eq_centralizer_singleton, Subgroup.relIndex_comap,
    Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]
  congr 1
  ext y
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨k, hk, ?_⟩
    rw [Subgroup.smul_def, MulAut.smul_def, MulAut.conj_apply]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨MulAut.conj k, Subgroup.mem_map_of_mem _ hk⟩, ?_⟩
    rw [Subgroup.smul_def, MulAut.smul_def, MulAut.conj_apply]

theorem relIndex_eq_ncard_conj {G : Type*} [Group G] [Finite G] (E I X : Subgroup G) {t w : G}
    (ht : orderOf t = 2) (_hw : orderOf w = 2) (hwt : Commute w t) (_hwE : w ∈ E)
    (_htE : t ∈ Subgroup.normalizer (E : Set G)) (hIE : I ≤ E)
    (_hIn : (I.subgroupOf E).Normal) (hIodd : Odd (Nat.card I))
    (hEt : ⁅E, Subgroup.zpowers t⁆ ≤ I) (hX : X ≤ I ⊓ Subgroup.centralizer {w * t})
    (_hXn : t ∈ Subgroup.normalizer (X : Set G))
    (hXt : ∀ c ∈ I ⊓ Subgroup.centralizer {w * t}, t * (c * t * c⁻¹) ∈ X) :
    (E ⊓ Subgroup.centralizer ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) :
        Set G)).relIndex (E ⊓ Subgroup.centralizer {w * t}) =
      {y | ∃ x ∈ X, x * t * x⁻¹ = y}.ncard := by
  set Z : Subgroup G := Subgroup.centralizer {w * t} with hZ
  set K : Subgroup G := E ⊓ Z
  set C : Subgroup G := I ⊓ Z
  have htinv : t⁻¹ = t := inv_eq_of_orderOf_eq_two ht
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htZ : t ∈ Z := by
    rw [hZ, Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, hwt.eq]
  have hcommI : ∀ x ∈ E, ⁅x, t⁆ ∈ I := fun x hx =>
    hEt (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers t))
  have hconjC : ∀ c ∈ C, t * c * t⁻¹ ∈ C := by
    intro c hc
    refine ⟨?_, Z.mul_mem (Z.mul_mem htZ hc.2) (Z.inv_mem htZ)⟩
    have h := hcommI _ (E.inv_mem (hIE hc.1))
    rw [commutatorElement_def, inv_inv] at h
    have h' : t * c * t⁻¹ = c * (c⁻¹ * t * c * t⁻¹) := by group
    rw [h']
    exact I.mul_mem hc.1 h
  have hcop : ¬ 2 ∣ Nat.card C :=
    (hIodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)).not_two_dvd_nat
  let α : Subgroup.zpowers t →* MulAut G := MulAut.conj.comp (Subgroup.zpowers t).subtype
  have hp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hKC : ∀ k ∈ K, ∃ c ∈ C, k * t * k⁻¹ = c * t * c⁻¹ := by
    intro k hk
    have hinv : ∀ a : Subgroup.zpowers t, ∀ x : G, x * k⁻¹ ∈ C → α a x * k⁻¹ ∈ C := by
      rintro ⟨a, ha⟩ x hx
      change a * x * a⁻¹ * k⁻¹ ∈ C
      rcases eq_one_or_eq_of_mem_zpowers ht ha with h | h
      · simpa [h] using hx
      · rw [h]
        have h1 : t * k * t⁻¹ * k⁻¹ ∈ C := by
          have h2 : t * k * t⁻¹ * k⁻¹ = ⁅k, t⁆⁻¹ := by
            rw [commutatorElement_inv, commutatorElement_def]
          rw [h2]
          refine C.inv_mem ⟨hcommI k hk.1, ?_⟩
          rw [commutatorElement_def]
          exact Z.mul_mem (Z.mul_mem (Z.mul_mem hk.2 htZ) (Z.inv_mem hk.2)) (Z.inv_mem htZ)
        have h3 : t * x * t⁻¹ * k⁻¹ = t * (x * k⁻¹) * t⁻¹ * (t * k * t⁻¹ * k⁻¹) := by group
        rw [h3]
        exact C.mul_mem (hconjC _ hx) h1
    obtain ⟨c₀, hc₀, hfix⟩ := (coprime_invariant_coset_fixed 2 hp α C hcop k).1 hinv
    have hc₀t : t * c₀ * t⁻¹ = c₀ := hfix ⟨t, Subgroup.mem_zpowers t⟩
    refine ⟨k * c₀⁻¹, ?_, ?_⟩
    · have h := C.inv_mem hc₀
      rwa [mul_inv_rev, inv_inv] at h
    · have h : c₀⁻¹ * t * c₀ = t := by
        calc c₀⁻¹ * t * c₀ = c₀⁻¹ * (t * c₀ * t⁻¹) * t := by group
          _ = t := by rw [hc₀t, inv_mul_cancel, one_mul]
      calc k * t * k⁻¹ = k * (c₀⁻¹ * t * c₀) * k⁻¹ := by rw [h]
        _ = k * c₀⁻¹ * t * (k * c₀⁻¹)⁻¹ := by group
  have hset : {y | ∃ k ∈ K, k * t * k⁻¹ = y} = {y | ∃ x ∈ X, x * t * x⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨c, hc, hkc⟩ := hKC k hk
      rw [hkc]
      obtain ⟨d, hd⟩ : ∃ d, d = t * (c * t * c⁻¹) := ⟨_, rfl⟩
      have hdX : d ∈ X := hd ▸ hXt c hc
      have hct : c * t * c⁻¹ = t * d := by rw [hd, ← mul_assoc, htt, one_mul]
      have hsq : t * d * (t * d) = 1 := by
        rw [← hct]
        calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
          _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
      have hdinv : t⁻¹ * d * t = d⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [htinv, mul_assoc (t * d) t d]
        exact hsq
      have hdodd : Odd (orderOf d) := hIodd.of_dvd_nat (I.orderOf_dvd_natCard (hX hdX).1)
      obtain ⟨n, hn⟩ := exists_pow_sq_eq_of_odd hdodd
      have hmt := conj_pow_eq_inv hdinv n
      refine ⟨(d ^ n)⁻¹, X.inv_mem (X.pow_mem hdX n), ?_⟩
      rw [hct, inv_inv, ← hmt, mul_assoc (t⁻¹ * d ^ n) t t, htt, mul_one, htinv, mul_assoc,
        ← pow_two, hn]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hIE (hX hx).1, (hX hx).2⟩, rfl⟩
  have hinf : E ⊓ Subgroup.centralizer ((Subgroup.zpowers w ⊔ Subgroup.zpowers t :
      Subgroup G) : Set G) ⊓ K = Subgroup.centralizer {t} ⊓ K := by
    ext x
    constructor
    · rintro ⟨⟨-, hxS⟩, hxK⟩
      refine ⟨Subgroup.centralizer_le ?_ hxS, hxK⟩
      exact Set.singleton_subset_iff.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    · rintro ⟨hxt, hxK⟩
      have hxt' : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp hxt
      have hxwt : Commute x (w * t) := Subgroup.mem_centralizer_singleton_iff.mp hxK.2
      have hxw : Commute x w := by
        have h := hxwt.mul_right hxt'.inv_right
        rwa [mul_inv_cancel_right] at h
      have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer {x} :=
        sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxw.symm.eq))
          (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxt'.symm.eq))
      have hxS : x ∈ Subgroup.centralizer
          ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun h hh =>
          Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
      exact ⟨⟨hxK.1, hxS⟩, hxK⟩
  calc (E ⊓ Subgroup.centralizer ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) :
        Set G)).relIndex K
      = (E ⊓ Subgroup.centralizer ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) :
          Set G) ⊓ K).relIndex K := (Subgroup.inf_relIndex_right _ _).symm
    _ = (Subgroup.centralizer {t} ⊓ K).relIndex K := by rw [hinf]
    _ = (Subgroup.centralizer {t}).relIndex K := Subgroup.inf_relIndex_right _ _
    _ = {y | ∃ x ∈ X, x * t * x⁻¹ = y}.ncard := by rw [relIndex_centralizer_eq_ncard, hset]

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Count
