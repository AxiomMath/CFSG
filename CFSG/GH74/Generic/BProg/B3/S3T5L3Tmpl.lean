module

public import CFSG.Assembly.OddCoreSpan
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T5L3

open Subgroup CFSG CFSG.Assembly.Dichotomy

variable {K : Type} [Group K]

theorem aut_mul_conj_mul_inv (α : MulAut K) (k : K) :
    α * MulAut.conj k * α⁻¹ = MulAut.conj (α k) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem conj_range_normal : (MulAut.conj : K →* MulAut K).range.Normal :=
  ⟨fun _ ⟨k, hk⟩ α => ⟨α k, by rw [← hk, aut_mul_conj_mul_inv]⟩⟩

theorem conj_injective_of (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  refine hZ z fun x => ?_
  have h := congrArg (fun φ : MulAut K => φ x) hz
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc z * x = z * x * z⁻¹ * z := by group
    _ = x * z := by rw [h]

theorem apply_eq_of_commute (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1) {α : MulAut K}
    {k : K} (h : α * MulAut.conj k = MulAut.conj k * α) : α k = k := by
  apply conj_injective_of hZ
  rw [← aut_mul_conj_mul_inv, h, mul_inv_cancel_right]

theorem center_trivial_of_simple_perfect [IsSimpleGroup K] (hK : Group.IsPerfect K) :
    ∀ z : K, (∀ x, z * x = x * z) → z = 1 := by
  have hcen : center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
    · exact h
    · exfalso
      have hle : (⊤ : Subgroup K) ≤ centralizer ((⊤ : Subgroup K) : Set K) :=
        h ▸ center_le_centralizer _
      have hcomm : _root_.commutator K = ⊥ := by
        rw [_root_.commutator, commutator_eq_bot_iff_le_centralizer]
        exact hle
      exact bot_ne_top (hcomm.symm.trans hK.commutator_eq_top)
  intro z hz
  have hz' : z ∈ center K := mem_center_iff.2 fun x => (hz x).symm
  rwa [hcen, mem_bot] at hz'

theorem odd_card_oddCore (C : Type*) [Group C] [Finite C] :
    Odd (Nat.card (Assembly.oddCore C)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

theorem eq_bot_of_simple_normal [Finite K] {S Q N : Subgroup K} (hQS : Q ≤ S)
    (hQn : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) [IsSimpleGroup Q]
    (hCQ : ∀ k : K, (∀ q ∈ Q, k * q = q * k) → k = 1) (hNS : N ≤ S)
    (hNn : ∀ s ∈ S, ∀ k ∈ N, s * k * s⁻¹ ∈ N) (hNodd : Odd (Nat.card N)) : N = ⊥ := by
  have hnonab : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hab
    simp only [not_exists, ne_eq, not_not] at hab
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    refine hq (Subtype.ext (hCQ q fun r hr => ?_))
    exact congrArg Subtype.val (hab q ⟨r, hr⟩)
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnonab).1
  have hM : ((N ⊓ Q).subgroupOf Q).Normal := by
    refine ⟨fun k hk q => ?_⟩
    rw [mem_subgroupOf] at hk ⊢
    exact ⟨hNn q (hQS q.2) k hk.1, Q.mul_mem (Q.mul_mem q.2 hk.2) (Q.inv_mem q.2)⟩
  have hNQ : ∀ k ∈ N, k ∈ Q → k = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ Q).subgroupOf Q) with h | h
    · intro k hkN hkQ
      have : (⟨k, hkQ⟩ : Q) ∈ (N ⊓ Q).subgroupOf Q := by
        rw [mem_subgroupOf]; exact ⟨hkN, hkQ⟩
      rw [h, mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hle : Q ≤ N := fun q hq => by
        have : (⟨q, hq⟩ : Q) ∈ (N ⊓ Q).subgroupOf Q := by rw [h]; exact mem_top _
        rw [mem_subgroupOf] at this
        exact this.1
      exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hNodd (card_dvd_of_le hle))) heven
  rw [eq_bot_iff_forall]
  intro k hk
  refine hCQ k fun q hq => ?_
  have h1 : k * q * k⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hQn k (hNS hk) q hq) (Q.inv_mem hq)
  have h2 : k * q * k⁻¹ * q⁻¹ ∈ N := by
    have := N.mul_mem hk (hNn q (hQS hq) k⁻¹ (N.inv_mem hk))
    rwa [show k * (q * k⁻¹ * q⁻¹) = k * q * k⁻¹ * q⁻¹ by group] at this
  have h3 := hNQ _ h2 h1
  calc k * q = k * q * k⁻¹ * q⁻¹ * (q * k) := by group
    _ = q * k := by rw [h3, one_mul]

theorem involutionOddCore_eq_bot_of_fix [Finite K] (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1)
    {H : Subgroup (MulAut K)} (hH : (MulAut.conj : K →* MulAut K).range ≤ H) (u : H)
    (hA : ∀ N : Subgroup K, Odd (Nat.card N) → (∀ k ∈ N, (u : MulAut K) k = k) →
      (∀ c, (u : MulAut K) c = c → ∀ k ∈ N, c * k * c⁻¹ ∈ N) → N = ⊥)
    (hB : ∀ w : MulAut K, Odd (orderOf w) → (∀ c, (u : MulAut K) c = c → w c = c) → w = 1) :
    involutionOddCore u = ⊥ := by
  set C := centralizer ({u} : Set H) with hC
  set W := Assembly.oddCore C with hW
  let ι : C →* MulAut K := H.subtype.comp C.subtype
  have hι : Function.Injective ι :=
    (Subgroup.subtype_injective H).comp (Subgroup.subtype_injective C)
  have hWodd : Odd (Nat.card W) := odd_card_oddCore C
  have hcomm : ∀ c : C, ι c * (u : MulAut K) = u * ι c := fun c => by
    have h := mem_centralizer_singleton_iff.1 c.2
    exact congrArg Subtype.val h
  have hconjC : ∀ c : K, (u : MulAut K) c = c → ∃ c' : C, ι c' = MulAut.conj c := by
    intro c hc
    refine ⟨⟨⟨MulAut.conj c, hH ⟨c, rfl⟩⟩, mem_centralizer_singleton_iff.2 (Subtype.ext ?_)⟩, rfl⟩
    change MulAut.conj c * (u : MulAut K) = u * MulAut.conj c
    have h := aut_mul_conj_mul_inv (u : MulAut K) c
    rw [hc] at h
    calc MulAut.conj c * (u : MulAut K) = (u * MulAut.conj c * (u : MulAut K)⁻¹) * u := by
          rw [h]
      _ = u * MulAut.conj c := by group
  set N : Subgroup K := (W.map ι).comap MulAut.conj with hN
  have hNodd : Odd (Nat.card N) := by
    have h1 : N.map MulAut.conj ≤ W.map ι := map_comap_le _ _
    have h2 := card_dvd_of_le h1
    rw [card_map_of_injective (conj_injective_of hZ), card_map_of_injective hι] at h2
    exact Odd.of_dvd_nat hWodd h2
  have hNfix : ∀ k ∈ N, (u : MulAut K) k = k := by
    intro k hk
    obtain ⟨w, -, hw⟩ := mem_map.1 (mem_comap.1 hk)
    refine apply_eq_of_commute hZ ?_
    rw [← hw]; exact (hcomm w).symm
  have hNn : ∀ c, (u : MulAut K) c = c → ∀ k ∈ N, c * k * c⁻¹ ∈ N := by
    intro c hc k hk
    obtain ⟨c', hc'⟩ := hconjC c hc
    obtain ⟨w, hwW, hw⟩ := mem_map.1 (mem_comap.1 hk)
    refine mem_comap.2 (mem_map.2 ⟨c' * w * c'⁻¹,
      (Assembly.oddCore_normal C).conj_mem w hwW c', ?_⟩)
    rw [map_mul, map_mul, map_inv, hc', hw, map_mul, map_mul, map_inv]
  have hN1 := hA N hNodd hNfix hNn
  have hWfix : ∀ w ∈ W, ∀ c, (u : MulAut K) c = c → ι w c = c := by
    intro w hw c hc
    obtain ⟨c', hc'⟩ := hconjC c hc
    have hx : w * c' * w⁻¹ * c'⁻¹ ∈ W := by
      have := W.mul_mem hw ((Assembly.oddCore_normal C).conj_mem w⁻¹ (W.inv_mem hw) c')
      rwa [show w * (c' * w⁻¹ * c'⁻¹) = w * c' * w⁻¹ * c'⁻¹ by group] at this
    have hmem : ι w c * c⁻¹ ∈ N := by
      refine mem_comap.2 (mem_map.2 ⟨_, hx, ?_⟩)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc', aut_mul_conj_mul_inv, map_mul,
        map_inv]
    rw [hN1, mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hW1 : W = ⊥ := by
    rw [eq_bot_iff_forall]
    intro w hw
    have hodd : Odd (orderOf (ι w)) := by
      rw [orderOf_injective ι hι]
      exact Odd.of_dvd_nat hWodd (W.orderOf_dvd_natCard hw)
    exact hι (by rw [hB _ hodd (hWfix w hw), map_one])
  change W.map C.subtype = ⊥
  rw [hW1, Subgroup.map_bot]

theorem exists_pCore_ne_bot {W : Type*} [Group W] [Finite W] (hW : Odd (Nat.card W))
    (hW1 : Nat.card W ≠ 1) : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ pCore p W ≠ ⊥ := by
  have := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hW
  have hF : fittingSubgroup W ≠ ⊥ := fun h =>
    hW1 ((fitting_eq_bot_iff_card_eq_one_of_solvable W).1 h)
  rw [fitting_eq_sup_pCore, Ne, iSup_eq_bot, not_forall] at hF
  obtain ⟨x, hne⟩ := hF
  obtain ⟨⟨p, hp⟩, hx⟩ := x
  refine ⟨p, Nat.prime_of_mem_primeFactors hp, ?_, hne⟩
  rintro rfl
  exact (Nat.not_even_iff_odd.2 hW) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))

theorem involutionOddCore_eq_bot_of_pGroup [Finite K] {H : Subgroup (MulAut K)} (u : H)
    (hP : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup (MulAut K), IsPGroup p X → X ≠ ⊥ →
      (∀ c ∈ H, c * (u : MulAut K) = u * c → c ∈ normalizer (X : Set (MulAut K))) → False) :
    involutionOddCore u = ⊥ := by
  set C := centralizer ({u} : Set H) with hC
  set W := Assembly.oddCore C with hW
  by_contra hne
  have hW1 : Nat.card W ≠ 1 := fun h => hne (by
    change W.map C.subtype = ⊥
    rw [card_eq_one.1 h, Subgroup.map_bot])
  obtain ⟨p, hp, hp2, hX⟩ := exists_pCore_ne_bot (odd_card_oddCore C) hW1
  have : Fact p.Prime := ⟨hp⟩
  let ι : W →* MulAut K := (H.subtype.comp C.subtype).comp W.subtype
  have hι : Function.Injective ι := ((Subgroup.subtype_injective H).comp
    (Subgroup.subtype_injective C)).comp (Subgroup.subtype_injective W)
  refine hP p hp hp2 ((pCore p W).map ι) (pCore_isPGroup.map ι)
    (by rwa [Ne, map_eq_bot_iff_of_injective _ hι]) fun c hcH hcu => ?_
  have hc' : (⟨c, hcH⟩ : H) ∈ C := mem_centralizer_singleton_iff.2 (Subtype.ext hcu)
  let φ : MulAut W := MulAut.conjNormal (⟨⟨c, hcH⟩, hc'⟩ : C)
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
  refine mem_map.2 ⟨φ y, ?_, ?_⟩
  · have h := (inferInstance : (pCore p W).Characteristic).fixed φ
    rw [← h] at hy
    exact hy
  · change (((φ y : W) : C) : H).1 = _
    rw [MulAut.conjNormal_apply]
    rfl

end CFSG.GH74.Generic.BProg.B3.S3T5L3
