module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_commute_mul_mem {N : Subgroup G} (hN : Odd (Nat.card N)) {x k : G}
    (hxx : x * x = 1) (hk : k⁻¹ * (x * k * x⁻¹) ∈ N) : ∃ o ∈ N, x * (k * o) = k * o * x := by
  set o₀ := k⁻¹ * (x * k * x⁻¹) with ho₀
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hconj : x * o₀ * x⁻¹ = o₀⁻¹ := by
    calc x * o₀ * x⁻¹ = x * k⁻¹ * x * k * (x⁻¹ * x⁻¹) := by rw [ho₀]; group
      _ = x * k⁻¹ * x * k := by rw [← mul_inv_rev, hxx, inv_one, mul_one]
      _ = o₀⁻¹ := by rw [ho₀, show (k⁻¹ * (x * k * x⁻¹))⁻¹ = x * k⁻¹ * x⁻¹ * k by group, hxi]
  have hm : Odd (orderOf o₀) := hN.of_dvd_nat (N.orderOf_dvd_natCard hk)
  obtain ⟨r, hr⟩ := hm
  have h2r : o₀ ^ (r + 1) * o₀ ^ (r + 1) = o₀ := by
    rw [← pow_add, show r + 1 + (r + 1) = orderOf o₀ + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  refine ⟨o₀ ^ (r + 1), pow_mem hk _, ?_⟩
  have hpow : x * o₀ ^ (r + 1) * x⁻¹ = (o₀ ^ (r + 1))⁻¹ := by
    rw [← conj_pow, hconj, inv_pow]
  have hxk : x * k * x⁻¹ = k * o₀ := by rw [ho₀]; group
  calc x * (k * o₀ ^ (r + 1)) = x * k * x⁻¹ * (x * o₀ ^ (r + 1) * x⁻¹) * x := by group
    _ = k * (o₀ ^ (r + 1) * o₀ ^ (r + 1)) * (o₀ ^ (r + 1))⁻¹ * x := by rw [hpow, hxk, h2r]
    _ = k * o₀ ^ (r + 1) * x := by simp only [mul_assoc, mul_inv_cancel_left]

section Held

variable
  {K : Subgroup G}
  (e : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)

include e in
theorem exists_commute_heN_eq {x : G} (hxN : x ∈ normalizer (K : Set G)) (hxx : x * x = 1)
    {p : Equiv.Perm (Fin 8330)} (hp : p ∈ heP) (hps : p * heN e x = heN e x * p) :
    ∃ c ∈ K, c * x = x * c ∧ heN e c = p := by
  obtain ⟨k, hk, rfl⟩ := exists_heL_eq (e := e) hp
  have hm : x * k * x⁻¹ ∈ K := (mem_normalizer_iff.mp hxN k).mp hk
  have h1 : heL e (x * k * x⁻¹) = heL e k := by
    rw [heL_conj hxN hk, ← hps, mul_inv_cancel_right]
  have h2 : k⁻¹ * (x * k * x⁻¹) ∈ (pPrimeCore 2 ↥K).map K.subtype := by
    rw [← heL_eq_one_iff (e := e) (mul_mem (inv_mem hk) hm), heL_mul (inv_mem hk) hm,
      heL_inv hk, h1, inv_mul_cancel]
  obtain ⟨o, ho, hxo⟩ := exists_commute_mul_mem (odd_card_map_pPrimeCore K) hxx h2
  have hoK : o ∈ K := map_subtype_le _ ho
  refine ⟨k * o, mul_mem hk hoK, hxo.symm, ?_⟩
  rw [heN_eq_heL (mul_mem hk hoK), heL_mul hk hoK, (heL_eq_one_iff hoK).mpr ho, mul_one]


include e in
theorem mem_coreActionKernel_of_oddCore {x : G} (hxN : x ∈ normalizer (K : Set G))
    (hxx : x * x = 1) (hxK : x ∈ K ⊔ coreActionKernel K) (hx1 : x ∉ coreActionKernel K) {d : G}
    (hd : d ∈ (pPrimeCore 2 ↥(centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype)
    (hdN : d ∈ normalizer (K : Set G)) : d ∈ coreActionKernel K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set N : Subgroup G := normalizer (K : Set G) with hN
  set U : Subgroup G := (pPrimeCore 2 ↥C).map C.subtype ⊓ N with hU
  have hUN : U ≤ N := inf_le_right
  set s := heN e x with hs
  have hsP : s ∈ heP := (heN_mem_heP_iff hxN).mpr hxK
  have hs1 : s ≠ 1 := fun h => hx1 ((heN_eq_one_iff hxN).mp h)
  have hss : s ^ 2 = 1 := by
    rw [pow_two, hs, ← heN_mul hxN hxN, hxx]
    exact (heN_eq_one_iff (one_mem _)).mpr (one_mem _)
  have hs2 : orderOf s = 2 := orderOf_eq_prime hss hs1
  set R : Subgroup (Equiv.Perm (Fin 8330)) :=
    ((U.subgroupOf N).map (heModelN e)).map heAutGroup.subtype with hR
  have hmemR : ∀ y, y ∈ R ↔ ∃ u ∈ U, heN e u = y := fun y => by
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨l, hl, by rw [heN_of_mem l.2]; rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨heModelN e ⟨u, hUN hu⟩, ⟨⟨u, hUN hu⟩, hu, rfl⟩, by rw [heN_of_mem (hUN hu)]; rfl⟩
  have hUodd : Odd (Nat.card U) :=
    (odd_card_map_pPrimeCore C).of_dvd_nat (card_dvd_of_le inf_le_left)
  have hRodd : Odd (Nat.card R) := by
    refine hUodd.of_dvd_nat ?_
    rw [hR, card_map_of_injective heAutGroup.subtype_injective,
      ← Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv]
    exact card_map_dvd _ _
  have hRP : R ≤ heP := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := (hmemR _).mp hr
    have hrA : heN e u ∈ heAutGroup := heN_mem (hUN hu)
    obtain ⟨q, hq⟩ : Odd (orderOf (heN e u)) := hRodd.of_dvd_nat (R.orderOf_dvd_natCard hr)
    by_contra hrP
    have hsq : heN e u * heN e u ∈ heP := by
      have h := inv_mul_mem_heP (inv_mem hrA) hrA (fun h => hrP (by simpa using inv_mem h)) hrP
      rwa [inv_inv] at h
    have hpow : heN e u = (heN e u * heN e u) ^ (q + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (q + 1) = orderOf (heN e u) + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    exact hrP (hpow ▸ pow_mem hsq _)
  have hRs : R ≤ centralizer ({s} : Set (Equiv.Perm (Fin 8330))) := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := (hmemR _).mp hr
    have huC : u ∈ C := map_subtype_le _ (mem_inf.mp hu).1
    rw [mem_centralizer_singleton_iff, hs, ← heN_mul (hUN hu) hxN, ← heN_mul hxN (hUN hu),
      (mem_centralizer_singleton_iff.mp huC)]
  set C' : Subgroup (Equiv.Perm (Fin 8330)) := CFSG.Sporadic.Schreier.centralizerIn heP s with hC'
  have hRC' : R ≤ C' := le_inf hRP hRs
  have hnorm : (R.subgroupOf C').Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨u, hu, hun⟩ := (hmemR _).mp hn
    obtain ⟨hgP, hgs⟩ := mem_inf.mp g.2
    obtain ⟨c, hcK, hcx, hcg⟩ := exists_commute_heN_eq e hxN hxx hgP
      (mem_centralizer_singleton_iff.mp hgs)
    have hcN : c ∈ N := le_normalizer hcK
    have hcC : c ∈ C := mem_centralizer_singleton_iff.mpr hcx
    have hcu : c * u * c⁻¹ ∈ U := by
      refine mem_inf.mpr ⟨?_, mul_mem (mul_mem hcN (hUN hu)) (inv_mem hcN)⟩
      exact (mem_normalizer_iff.mp (le_normalizer_oddIn hcC) u).mp (mem_inf.mp hu).1
    refine (hmemR _).mpr ⟨c * u * c⁻¹, hcu, ?_⟩
    rw [heN_mul (mul_mem hcN (hUN hu)) (inv_mem hcN), heN_mul hcN (hUN hu), heN_inv hcN, hcg,
      hun]
    simp
  have hodd' : Odd (Nat.card (R.subgroupOf C')) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hRC').toEquiv]
  have hcore : CFSG.oddCore ↥C' = ⊥ := heP_centralizerIn_oddCore hsP hs2
  have hle : R.subgroupOf C' ≤ CFSG.oddCore ↥C' := le_sSup ⟨hnorm, hodd'⟩
  rw [hcore, le_bot_iff] at hle
  have hdU : d ∈ U := mem_inf.mpr ⟨hd, hdN⟩
  have hdR : heN e d ∈ R := (hmemR _).mpr ⟨d, hdU, rfl⟩
  have h1 : (⟨heN e d, hRC' hdR⟩ : C') ∈ R.subgroupOf C' := mem_subgroupOf.mpr hdR
  rw [hle, mem_bot] at h1
  exact (heN_eq_one_iff hdN).mp (congrArg Subtype.val h1)

end Held

theorem commutator_mem_oddIn {K M : Subgroup G} (hKM : K ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) {q : G} (hqM : q ∈ M) (hq : q ∈ coreActionKernel K)
    {j : G} (hj : j ∈ K ⊔ oddIn M) : j⁻¹ * q⁻¹ * j * q ∈ oddIn M := by
  have hON : M ≤ normalizer ((oddIn M : Subgroup G) : Set G) := le_normalizer_oddIn
  have hKO : oddIn K ≤ oddIn M := Sol25.oddIn_le_of_isPComponent hKM hK
  have hj' : j ∈ ((oddIn M : Subgroup G) : Set G) * (K : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hKM.trans hON), sup_comm]
    exact hj
  obtain ⟨o, ho, k, hk, rfl⟩ := hj'
  have h1 : o⁻¹ * (q⁻¹ * o * q) ∈ oddIn M := by
    refine mul_mem (inv_mem ho) ?_
    have := (mem_normalizer_iff.mp (inv_mem (hON hqM)) o).mp ho
    rwa [inv_inv] at this
  have h2 : k⁻¹ * (o⁻¹ * (q⁻¹ * o * q)) * k ∈ oddIn M := by
    have := (mem_normalizer_iff.mp (inv_mem (hON (hKM hk))) _).mp h1
    rwa [inv_inv] at this
  have h3 : k⁻¹ * q⁻¹ * k * q ∈ oddIn M := hKO ((mem_coreActionKernel.mp hq).2 k hk)
  have h4 := mul_mem h2 h3
  rwa [show k⁻¹ * (o⁻¹ * (q⁻¹ * o * q)) * k * (k⁻¹ * q⁻¹ * k * q) =
    (o * k)⁻¹ * q⁻¹ * (o * k) * q by group] at h4

end CFSG.ComponentClassification.GrSLit.GrS4
