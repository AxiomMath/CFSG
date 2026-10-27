module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeKAux

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

theorem isShapeK_of_data {G : Type*} [Group G] (K N Zc Q E : Subgroup G) (x y c : G)
    (φ : ↥K →* Equiv.Perm (Fin 5)) (hNK : N ≤ K)
    (hNker : ∀ (n : G) (h : n ∈ N), φ ⟨n, hNK h⟩ = 1)
    (hK : Nat.card ↥K = 15360) (hN : Nat.card ↥N = 128) (hrange : Nat.card ↥φ.range = 120)
    (hZN : Zc ≤ N) (hZcen : ∀ z ∈ Zc, ∀ n ∈ N, z * n = n * z)
    (hZ : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n ∈ Zc) (hZc : Nat.card ↥Zc = 8)
    (hx : x ∈ Zc) (hy : y ∈ Zc) (hx4 : orderOf x = 4) (hy2 : orderOf y = 2)
    (hxy : y ∉ zpowers x)
    (hQN : Q ≤ N) (hQ : Nat.card ↥Q = 32) (hcQ : c ∈ Q) (hcZ : c ∈ Zc) (hc1 : c ≠ 1)
    (hc2 : c * c = 1)
    (hQcen : ∀ q ∈ Q, (∀ r ∈ Q, q * r = r * q) → q = 1 ∨ q = c)
    (hQcomm : ∀ q ∈ Q, ∀ r ∈ Q, q * r * (r * q)⁻¹ = 1 ∨ q * r * (r * q)⁻¹ = c)
    (hQsq : ∀ q ∈ Q, q * q = 1 ∨ q * q = c)
    (hE : E ≤ Q) (hEcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hEsq : ∀ e ∈ E, e * e = 1)
    (hE8 : Nat.card ↥E = 8) (hjoin : ∀ n ∈ N, ∃ z ∈ Zc, z⁻¹ * n ∈ Q) :
    IsShapeK ↥K := by
  let N' : Subgroup ↥K := N.subgroupOf K
  have hN'card : Nat.card ↥N' = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv, hN]
  have hcard_ker : Nat.card ↥φ.ker = 128 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hK, hrange] at h
    omega
  have hN'le : N' ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    simpa using hNker (n : G) hnN
  haveI : Finite ↥φ.ker := Nat.finite_of_card_ne_zero (by rw [hcard_ker]; norm_num)
  have hN'eq : N' = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hN'le (by rw [hcard_ker, hN'card])
  have hN'Normal : N'.Normal := by rw [hN'eq]; infer_instance
  have hcardPerm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]; norm_num
  haveI : Finite ↥φ.range := Nat.finite_of_card_ne_zero (by rw [hrange]; norm_num)
  have hrange_top : φ.range = ⊤ :=
    Subgroup.eq_top_of_card_eq (G := Equiv.Perm (Fin 5)) (H := φ.range)
      (by rw [hrange, hcardPerm])
  have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hrange_top
  haveI : N'.Normal := hN'Normal
  have hisoQ : Nonempty (↥K ⧸ N' ≃* Equiv.Perm (Fin 5)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hN'eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩
  have hN'p : IsPGroup 2 ↥N' := IsPGroup.of_card (n := 7) (by rw [hN'card]; norm_num)
  have hcenterN : Subgroup.center ↥N = Zc.subgroupOf N := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_center_iff] at hz
      refine Subgroup.mem_subgroupOf.mpr (hZ (z : G) z.2 (fun m hm => ?_))
      have := congrArg (fun t : ↥N => (t : G)) (hz ⟨m, hm⟩)
      simpa using this.symm
    · intro z hz
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext
      exact (hZcen (z : G) (Subgroup.mem_subgroupOf.mp hz) (m : G) m.2).symm
  have hcenterNiso : Subgroup.center ↥N ≃* ↥Zc :=
    (MulEquiv.subgroupCongr hcenterN).trans (Subgroup.subgroupOfEquivOfLe hZN)
  let iota : ↥N' ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNK
  have hcenterN'iso : Subgroup.center ↥N' ≃* ↥Zc :=
    (Subgroup.centerCongr iota).trans hcenterNiso
  have hZcComm : ∀ a b : ↥Zc, a * b = b * a := by
    intro a b
    apply Subtype.ext
    exact hZcen (a : G) a.2 (b : G) (hZN b.2)
  have hx' : orderOf (⟨x, hx⟩ : ↥Zc) = 4 := by
    rw [Subgroup.orderOf_mk, hx4]
  have hy' : orderOf (⟨y, hy⟩ : ↥Zc) = 2 := by
    rw [Subgroup.orderOf_mk, hy2]
  have hxy' : (⟨y, hy⟩ : ↥Zc) ∉ Subgroup.zpowers (⟨x, hx⟩ : ↥Zc) := by
    intro hmem
    apply hxy
    rcases Subgroup.mem_zpowers_iff.mp hmem with ⟨k, hk⟩
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg (fun t : ↥Zc => (t : G)) hk
    simpa using this
  have hZciso : Nonempty (↥Zc ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) :=
    nonempty_mulEquiv_two_four hZcComm hZc hx' hy' hxy'
  have hcenterFinal :
      Nonempty (Subgroup.center ↥N' ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) :=
    ⟨hcenterN'iso.trans hZciso.some⟩
  have hQK : Q ≤ K := hQN.trans hNK
  have hEK : E ≤ K := hE.trans hQK
  have hQ'le : Q.subgroupOf K ≤ N' := Subgroup.subgroupOf_mono K hQN
  let Q' : Subgroup ↥N' := (Q.subgroupOf K).subgroupOf N'
  let eQ : ↥Q' ≃* ↥Q :=
    (Subgroup.subgroupOfEquivOfLe hQ'le).trans (Subgroup.subgroupOfEquivOfLe hQK)
  have heQcoe : ∀ q : ↥Q', (eQ q : G) = (q : G) := fun q => rfl
  let cK : ↥K := ⟨c, hNK (hQN hcQ)⟩
  have hcN' : cK ∈ N' := Subgroup.mem_subgroupOf.mpr (hQN hcQ)
  let cN' : ↥N' := ⟨cK, hcN'⟩
  have hcQ' : cN' ∈ Q' := by
    show cN' ∈ (Q.subgroupOf K).subgroupOf N'
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hcQ)
  let c' : ↥Q' := ⟨cN', hcQ'⟩
  have heQc' : eQ c' = (⟨c, hcQ⟩ : ↥Q) := by
    apply Subtype.ext
    rfl
  have hQG : ∀ q : ↥Q', (q : G) ∈ Q := by
    intro q
    have h1 : (q : ↥K) ∈ Q.subgroupOf K := Subgroup.mem_subgroupOf.mp q.2
    simpa using Subgroup.mem_subgroupOf.mp h1
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    have h2 : (c' : G) = ((1 : ↥Q') : G) := congrArg (fun t : ↥Q' => (t : G)) h
    exact h2
  have hc'2 : c' * c' = 1 := by
    apply eQ.injective
    rw [map_mul, heQc', map_one]
    apply Subtype.ext
    show c * c = 1
    rw [hc2]
  have hc'en : ∀ g : ↥Q', g * c' = c' * g := by
    intro g
    apply eQ.injective
    rw [map_mul, map_mul, heQc']
    apply Subtype.ext
    show (eQ g : G) * c = c * (eQ g : G)
    exact (hZcen c hcZ (eQ g : G) (hQN (eQ g).2)).symm
  have hc'entr : ∀ q : ↥Q', (∀ r : ↥Q', q * r = r * q) → q = 1 ∨ q = c' := by
    intro q hq
    have hqQ : ∀ r ∈ Q, (eQ q : G) * r = r * (eQ q : G) := by
      intro r hr
      obtain ⟨r', hr'⟩ := eQ.surjective ⟨r, hr⟩
      have hcoe_r : (eQ r' : G) = r := by rw [hr']
      rw [← hcoe_r, heQcoe q, heQcoe r']
      exact congrArg (fun t : ↥Q' => (t : G)) (hq r')
    rcases hQcen (eQ q : G) (eQ q).2 hqQ with h | h
    · left
      apply eQ.injective
      rw [map_one]
      apply Subtype.ext
      simpa using h
    · right
      apply eQ.injective
      rw [heQc']
      apply Subtype.ext
      simpa using h
  have hcomm' : ∀ q r : ↥Q', q * r * (r * q)⁻¹ = 1 ∨ q * r * (r * q)⁻¹ = c' := by
    intro q r
    have h := hQcomm (q : G) (hQG q) (r : G) (hQG r)
    have h' : (eQ q * eQ r * (eQ r * eQ q)⁻¹ : ↥Q) = 1 ∨
        (eQ q * eQ r * (eQ r * eQ q)⁻¹ : ↥Q) = ⟨c, hcQ⟩ := by
      rcases h with h | h
      · left; apply Subtype.ext; simpa [heQcoe] using h
      · right; apply Subtype.ext; simpa [heQcoe] using h
    have hmap : eQ (q * r * (r * q)⁻¹) = eQ q * eQ r * (eQ r * eQ q)⁻¹ := by
      simp only [map_mul, map_inv]
    rcases h' with h' | h'
    · left; apply eQ.injective; rw [hmap, h']; simp
    · right; apply eQ.injective; rw [hmap, h', heQc']
  have hsq' : ∀ q : ↥Q', q * q = 1 ∨ q * q = c' := by
    intro q
    have h := hQsq (q : G) (hQG q)
    have h' : (eQ q * eQ q : ↥Q) = 1 ∨ (eQ q * eQ q : ↥Q) = ⟨c, hcQ⟩ := by
      rcases h with h | h
      · left; apply Subtype.ext; simpa [heQcoe] using h
      · right; apply Subtype.ext; simpa [heQcoe] using h
    have hmap : eQ (q * q) = eQ q * eQ q := by simp only [map_mul]
    rcases h' with h' | h'
    · left; apply eQ.injective; rw [hmap, h']; simp
    · right; apply eQ.injective; rw [hmap, h', heQc']
  have hQ'card : Nat.card ↥Q' = 32 := by
    rw [Nat.card_congr eQ.toEquiv, hQ]
  have hnt' : ∃ q : ↥Q', q ≠ 1 ∧ q ≠ c' := by
    by_contra h
    have h' : ∀ q : ↥Q', q = 1 ∨ q = c' := fun q => by
      by_cases h1 : q = 1
      · exact Or.inl h1
      · exact Or.inr (by
          by_contra h2
          exact h ⟨q, h1, h2⟩)
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : ↥Q') else c') := by
      intro q
      rcases h' q with hq | hq
      · exact ⟨true, by simp [hq]⟩
      · exact ⟨false, by simp [hq]⟩
    have hle := Nat.card_le_card_of_surjective
      (fun b : Bool => if b then (1 : ↥Q') else c') hsurj
    rw [show Nat.card Bool = 2 by rw [Nat.card_eq_fintype_card, Fintype.card_bool]] at hle
    omega
  have hExtQ' : CFSG.IsExtraspecial 2 ↥Q' :=
    isExtraspecial_two_of_elements c' hc'1 hc'2 hc'en hc'entr hcomm' hsq' hnt'
  have hE'le_N' : E.subgroupOf K ≤ N' := Subgroup.subgroupOf_mono K (hE.trans hQN)
  let E' : Subgroup ↥N' := (E.subgroupOf K).subgroupOf N'
  let eE : ↥E' ≃* ↥E :=
    (Subgroup.subgroupOfEquivOfLe hE'le_N').trans (Subgroup.subgroupOfEquivOfLe hEK)
  have heEcoe : ∀ e : ↥E', (eE e : G) = (e : G) := fun e => rfl
  have hE'subQ : E' ≤ Q' := by
    show (E.subgroupOf K).subgroupOf N' ≤ (Q.subgroupOf K).subgroupOf N'
    exact Subgroup.subgroupOf_mono N' (Subgroup.subgroupOf_mono K hE)
  have hE'comm : IsMulCommutative ↥E' := by
    refine IsMulCommutative.of_comm (fun a b => ?_)
    apply eE.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    exact hEcomm (eE a) (eE a).2 (eE b) (eE b).2
  have hE'sq : ∀ a ∈ E', a ^ 2 = 1 := by
    intro a ha
    apply Subtype.ext; apply Subtype.ext
    have := hEsq (eE ⟨a, ha⟩ : G) (eE ⟨a, ha⟩).2
    simpa [heEcoe, pow_two] using this
  have hE'card : Nat.card ↥E' = 8 := by
    rw [Nat.card_congr eE.toEquiv, hE8]
  have hElemE' : CFSG.Open.IsElemAbelian 2 E' := ⟨hE'comm, hE'sq⟩
  have hE'cardPow : Nat.card ↥E' = 2 ^ (2 + 1) := by rw [hE'card]; norm_num
  have hQ'cardPow : Nat.card Q' = 2 ^ (1 + 2 * 2) := by rw [hQ'card]; norm_num
  have hPlus : IsPlusExtraspecial 2 Q' :=
    ⟨hExtQ', hQ'cardPow, E', hE'subQ, hElemE', hE'cardPow⟩
  have hnN_of : ∀ n : ↥N', (n : G) ∈ N := by
    intro n
    have h1 := Subgroup.mem_subgroupOf.mp n.2
    simpa using h1
  have hsup : Subgroup.center ↥N' ⊔ Q' = ⊤ := by
    apply le_antisymm le_top
    intro n _
    obtain ⟨z, hz, hzq⟩ := hjoin (n : G) (hnN_of n)
    let zK : ↥K := ⟨z, hNK (hZN hz)⟩
    have hzN' : zK ∈ N' := Subgroup.mem_subgroupOf.mpr (hZN hz)
    let z' : ↥N' := ⟨zK, hzN'⟩
    have hz'center : z' ∈ Subgroup.center ↥N' := by
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext; apply Subtype.ext
      show (m : G) * z = z * (m : G)
      exact (hZcen z hz (m : G) (hnN_of m)).symm
    let q' : ↥N' := z'⁻¹ * n
    have hq'Q' : q' ∈ Q' := by
      show q' ∈ (Q.subgroupOf K).subgroupOf N'
      apply Subgroup.mem_subgroupOf.mpr
      apply Subgroup.mem_subgroupOf.mpr
      show z⁻¹ * (n : G) ∈ Q
      exact hzq
    have hn_eq : n = z' * q' := by
      rw [show q' = z'⁻¹ * n from rfl, mul_inv_cancel_left]
    rw [hn_eq]
    exact Subgroup.mul_mem_sup hz'center hq'Q'
  have hcN'1 : cN' ≠ 1 := by
    intro h
    exact hc'1 (Subtype.ext h)
  have hcN'2 : cN' * cN' = 1 := by
    have := congrArg (fun t : ↥Q' => (t : ↥N')) hc'2
    simpa using this
  have hmeet : Subgroup.center ↥N' ⊓ Q' = Subgroup.zpowers cN' := by
    apply le_antisymm
    · intro m hm
      rw [Subgroup.mem_inf] at hm
      obtain ⟨hmc, hmQ⟩ := hm
      let mq : ↥Q' := ⟨m, hmQ⟩
      have hmcentral : ∀ r' : ↥Q', mq * r' = r' * mq := by
        intro r'
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp hmc (r' : ↥N')).symm
      have hcentral : ∀ r ∈ Q, (eQ mq : G) * r = r * (eQ mq : G) := by
        intro r hr
        obtain ⟨r', hr'⟩ := eQ.surjective ⟨r, hr⟩
        have hcoe_r : (eQ r' : G) = r := by rw [hr']
        rw [← hcoe_r, heQcoe mq, heQcoe r']
        exact congrArg (fun t : ↥Q' => (t : G)) (hmcentral r')
      rcases hQcen (eQ mq : G) (eQ mq).2 hcentral with h | h
      · have hm1 : m = 1 := by
          have : mq = 1 := by
            apply eQ.injective
            rw [map_one]
            apply Subtype.ext
            simpa [heQcoe] using h
          exact congrArg (fun t : ↥Q' => (t : ↥N')) this
        rw [hm1]; exact Subgroup.one_mem _
      · have hmcN' : m = cN' := by
          have : mq = c' := by
            apply eQ.injective
            rw [heQc']
            apply Subtype.ext
            simpa [heQcoe] using h
          exact congrArg (fun t : ↥Q' => (t : ↥N')) this
        rw [hmcN']; exact Subgroup.mem_zpowers cN'
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.mpr ⟨?_, hcQ'⟩
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext; apply Subtype.ext
      show (m : G) * c = c * (m : G)
      exact (hZcen c hcZ (m : G) (hnN_of m)).symm
  have horder_cN' : orderOf cN' = 2 := orderOf_eq_prime (by rwa [pow_two]) hcN'1
  have hmeet_card : Nat.card ↥(Subgroup.center ↥N' ⊓ Q') = 2 := by
    rw [hmeet, Nat.card_zpowers cN', horder_cN']
  exact ⟨N', hN'Normal, hN'p, by rw [hN'card]; norm_num, hisoQ, hcenterFinal, Q', hPlus,
    hsup, hmeet_card⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
