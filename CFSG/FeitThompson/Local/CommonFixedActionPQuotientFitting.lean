module

public import CFSG.FeitThompson.Local.PrimeActionChiefFactorsBelowFitting
import CFSG.FeitThompson.Local.FittingFixedFreeDisplacementInFitting
import CFSG.FeitThompson.Local.FixedFreeComplementNilpotentSections
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.SplitKernelSubgroupInheritsComplement
import CFSG.FeitThompson.Representations.AbelianNormalLayerDegreeBound
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Local.ChiefFactorCentralizationFittingBound
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem map_subtype_fittingOfNormal_subgroupOf [Finite G] {K L : Subgroup G} (hKL : K ≤ L) :
    (fittingOfNormal (K.subgroupOf L)).map L.subtype = fittingOfNormal K := by
  have he : L.subtype.comp (K.subgroupOf L).subtype
      = K.subtype.comp (subgroupOfEquivOfLe hKL : ↥(K.subgroupOf L) →* ↥K) := by
    ext y; simp
  rw [← map_fittingRaw_subtype_eq_fittingOfNormal, ← map_fittingRaw_subtype_eq_fittingOfNormal,
    Subgroup.map_map, he, ← Subgroup.map_map, map_fittingRaw_of_mulEquiv]

theorem relIndex_fittingOfNormal_subgroupOf [Finite G] {K L : Subgroup G} (hKL : K ≤ L) :
    (fittingOfNormal (K.subgroupOf L)).relIndex (K.subgroupOf L)
      = (fittingOfNormal K).relIndex K := by
  rw [relIndex_fittingOfNormal, relIndex_fittingOfNormal]
  exact Nat.card_congr (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKL)
    (map_fittingRaw_of_mulEquiv _)).toEquiv

theorem commutator_le_fittingOfNormal_of_le_of_prime [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {K R T : Subgroup G} [K.Normal] (hKR : K.IsComplement' R)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R)) (hTR : T ≤ R)
    (hTprime : (Nat.card ↥T).Prime) {p a : ℕ} (hp : p.Prime)
    (hKF : (fittingOfNormal K).relIndex K = p ^ a)
    (hcent : fittingOfNormal K ⊓ centralizer (T : Set G) = ⊥) :
    ⁅K, T⁆ ≤ fittingOfNormal K := by
  set L : Subgroup G := K ⊔ T with hLdef
  have hKL : K ≤ L := le_sup_left
  have hTL : T ≤ L := le_sup_right
  have : (K.subgroupOf L).Normal := ‹K.Normal›.subgroupOf L
  have hLR : L ⊓ R = T := sup_inf_eq_of_isComplement' hKR hTR
  have hcompl : (K.subgroupOf L).IsComplement' (T.subgroupOf L) := by
    have := isComplement'_subgroupOf_of_isComplement' hKR hKL
    rwa [hLR] at this
  have hcardK : Nat.card ↥(K.subgroupOf L) = Nat.card ↥K :=
    Nat.card_congr (subgroupOfEquivOfLe hKL).toEquiv
  have hcardT : Nat.card ↥(T.subgroupOf L) = Nat.card ↥T :=
    Nat.card_congr (subgroupOfEquivOfLe hTL).toEquiv
  have hcop' : (Nat.card ↥(K.subgroupOf L)).Coprime (Nat.card ↥(T.subgroupOf L)) := by
    rw [hcardK, hcardT]
    exact hcop.coprime_dvd_right (card_dvd_of_le hTR)
  have hcent' : fittingOfNormal (K.subgroupOf L)
      ⊓ centralizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    have hxF : (x : G) ∈ fittingOfNormal K := by
      rw [← map_subtype_fittingOfNormal_subgroupOf hKL]
      exact ⟨x, hx1, rfl⟩
    have hxC : (x : G) ∈ centralizer (T : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      have : (⟨y, hTL hy⟩ : ↥L) * x = x * ⟨y, hTL hy⟩ :=
        Subgroup.mem_centralizer_iff.1 hx2 _
          (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hy)
      exact congrArg (Subtype.val) this
    have := (Subgroup.eq_bot_iff_forall _).1 hcent (x : G) (Subgroup.mem_inf.2 ⟨hxF, hxC⟩)
    exact Subtype.ext this
  have key : ⁅K.subgroupOf L, T.subgroupOf L⁆ ≤ fittingOfNormal (K.subgroupOf L) :=
    commutator_le_fittingOfNormal (odd_natCard_subgroup hodd L) hcompl hcop'
      (by rwa [hcardT]) hp (by rwa [relIndex_fittingOfNormal_subgroupOf hKL]) hcent'
  have := Subgroup.map_mono (f := L.subtype) key
  rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hKL, inf_eq_left.2 hTL, map_subtype_fittingOfNormal_subgroupOf hKL] at this

theorem exists_mem_inf_centralizer_mul_mem_fittingOfNormal [Finite G] [Group.IsSolvable G]
    {K T : Subgroup G} [K.Normal] (hcop : (Nat.card ↥T).Coprime (Nat.card ↥K))
    (hKT : ⁅K, T⁆ ≤ fittingOfNormal K) {k : G} (hk : k ∈ K) :
    ∃ c ∈ K ⊓ centralizer (T : Set G), ∃ f ∈ fittingOfNormal K, k = c * f := by
  set ρ : ↥T →* MulAut ↥K := conjSubgroupAut K T with hρ
  set v : ↥K := ⟨k, hk⟩ with hv
  have hmemF : ∀ x : ↥K, ((x : G) ∈ fittingOfNormal K) ↔ x ∈ fittingRaw ↥K := fun x => by
    rw [← subgroupOf_fittingOfNormal K, Subgroup.mem_subgroupOf]
  have hfix : ∀ b : ↥T, v⁻¹ * ρ b v ∈ fittingRaw ↥K := by
    intro b
    refine (hmemF _).1 (hKT ?_)
    have hcm := Subgroup.commutator_mem_commutator (H₁ := K) (H₂ := T) (K.inv_mem hk) b.2
    rw [commutatorElement_def] at hcm
    have hco : ((v⁻¹ * ρ b v : ↥K) : G) = k⁻¹ * (b : G) * (k⁻¹)⁻¹ * ((b : G))⁻¹ := by
      rw [Subgroup.coe_mul, hρ, coe_conjSubgroupAut_apply]
      simp only [InvMemClass.coe_inv, hv]
      group
    rw [hco]
    exact hcm
  obtain ⟨n, hn, hfixed⟩ :=
    exists_mem_forall_apply_mul_eq (isInvariantSubgroup_of_characteristic ρ (fittingRaw ↥K))
      hcop hfix
  refine ⟨k * (n : G), Subgroup.mem_inf.2 ⟨K.mul_mem hk n.2, ?_⟩, (n : G)⁻¹,
    (fittingOfNormal K).inv_mem ((hmemF n).2 hn), by group⟩
  refine Subgroup.mem_centralizer_iff.2 fun b hb => ?_
  have h := hfixed ⟨b, hb⟩
  have h' : b * (k * (n : G)) * b⁻¹ = k * (n : G) := by
    have h2 := congrArg (Subtype.val) h
    rw [hρ, coe_conjSubgroupAut_apply] at h2
    simpa [hv] using h2
  calc b * (k * (n : G)) = (b * (k * (n : G)) * b⁻¹) * b := by group
    _ = (k * (n : G)) * b := by rw [h']

theorem commutator_le_fittingOfNormal_of_forall_inf_centralizer_eq [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal] (hKR : K.IsComplement' R)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R))
    {p a : ℕ} (hp : p.Prime) (hKF : (fittingOfNormal K).relIndex K = p ^ a)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ centralizer ({x} : Set G) = K ⊓ centralizer (R : Set G))
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥) :
    ⁅K, R⁆ ≤ fittingOfNormal K := by
  have hFn : (fittingOfNormal K).Normal := normal_fittingOfNormal ‹K.Normal›
  rcases eq_or_ne R ⊥ with rfl | hR
  · simp
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (n := Nat.card ↥R) (fun h => hR (Subgroup.card_eq_one.1 h))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨t0, ht0⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) q hqd
  set t : G := (t0 : G) with htdef
  have htR : t ∈ R := t0.2
  have hord : orderOf t = q := by rw [htdef, Subgroup.orderOf_coe]; exact ht0
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact hq.one_lt.ne hord
  set T : Subgroup G := zpowers t with hTdef
  have hTR : T ≤ R := zpowers_le.2 htR
  have hTcard : Nat.card ↥T = q := by rw [hTdef, Nat.card_zpowers, hord]
  have hCT : centralizer (T : Set G) = centralizer ({t} : Set G) := centralizer_coe_zpowers t
  have hcentT : fittingOfNormal K ⊓ centralizer (T : Set G) = ⊥ := by
    rw [hCT, show fittingOfNormal K ⊓ centralizer ({t} : Set G)
        = fittingOfNormal K ⊓ (K ⊓ centralizer ({t} : Set G)) by
      rw [← inf_assoc, inf_eq_left.2 (fittingOfNormal_le K)], hC t htR ht1, ← inf_assoc,
      inf_eq_left.2 (fittingOfNormal_le K), hcent]
  have hKT : ⁅K, T⁆ ≤ fittingOfNormal K :=
    commutator_le_fittingOfNormal_of_le_of_prime hodd hKR hcop hTR (hTcard ▸ hq) hp hKF hcentT
  have hcop' : (Nat.card ↥T).Coprime (Nat.card ↥K) :=
    (hcop.coprime_dvd_right (card_dvd_of_le hTR)).symm
  refine Subgroup.commutator_le.2 fun k hk r hr => ?_
  rw [commutatorElement_def]
  obtain ⟨c, hcmem, f, hf, hkcf⟩ :=
    exists_mem_inf_centralizer_mul_mem_fittingOfNormal hcop' hKT hk
  obtain ⟨hcK, hcC⟩ := Subgroup.mem_inf.1 hcmem
  have hcR : c ∈ centralizer (R : Set G) := by
    have hmem : c ∈ K ⊓ centralizer (R : Set G) := by
      rw [← hC t htR ht1]
      exact Subgroup.mem_inf.2 ⟨hcK, by rwa [hCT] at hcC⟩
    exact (Subgroup.mem_inf.1 hmem).2
  have hcr : c * r = r * c := (Subgroup.mem_centralizer_iff.1 hcR r hr).symm
  have hcr' : c⁻¹ * r⁻¹ = r⁻¹ * c⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hcr]
  have hfr : f * (r * f⁻¹ * r⁻¹) ∈ fittingOfNormal K :=
    (fittingOfNormal K).mul_mem hf
      (by simpa [mul_assoc] using hFn.conj_mem _ ((fittingOfNormal K).inv_mem hf) r)
  have hfinal : k * r * k⁻¹ * r⁻¹ = c * (f * (r * f⁻¹ * r⁻¹)) * c⁻¹ := by
    calc k * r * k⁻¹ * r⁻¹ = c * f * r * (c * f)⁻¹ * r⁻¹ := by rw [hkcf]
      _ = c * f * r * f⁻¹ * (c⁻¹ * r⁻¹) := by group
      _ = c * f * r * f⁻¹ * (r⁻¹ * c⁻¹) := by rw [hcr']
      _ = c * (f * (r * f⁻¹ * r⁻¹)) * c⁻¹ := by group
  rw [hfinal]
  exact hFn.conj_mem _ hfr c

theorem commutator_le_fittingOfNormal_of_forall_inf_centralizer_eq_of_natCard_quotient [Finite G]
    [Group.IsSolvable G] (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal]
    (hKR : K.IsComplement' R) (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R))
    {p a : ℕ} (hp : p.Prime) (hKF : Nat.card (↥K ⧸ fittingRaw ↥K) = p ^ a)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ centralizer ({x} : Set G) = K ⊓ centralizer (R : Set G))
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥) :
    ⁅K, R⁆ ≤ fittingOfNormal K :=
  commutator_le_fittingOfNormal_of_forall_inf_centralizer_eq hodd hKR hcop hp
    ((relIndex_fittingOfNormal K).trans hKF) hC hcent

theorem subgroupOf_commutator_le_fittingRaw_of_forall_inf_centralizer_eq [Finite G]
    [Group.IsSolvable G] (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal]
    (hKR : K.IsComplement' R) (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R))
    {p a : ℕ} (hp : p.Prime) (hKF : (fittingOfNormal K).relIndex K = p ^ a)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ centralizer ({x} : Set G) = K ⊓ centralizer (R : Set G))
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥) :
    (⁅K, R⁆ : Subgroup G).subgroupOf K ≤ fittingRaw ↥K :=
  (le_map_fittingRaw_subtype_iff (Subgroup.commutator_le_left K R)).1
    (map_fittingRaw_subtype_eq_fittingOfNormal K ▸
      commutator_le_fittingOfNormal_of_forall_inf_centralizer_eq hodd hKR hcop hp hKF hC hcent)

end CFSG.FeitThompson
