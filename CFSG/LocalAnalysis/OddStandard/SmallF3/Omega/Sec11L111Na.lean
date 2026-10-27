module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L106A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TQ8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem oddCoreIn_le_X (X : Subgroup G) : oddCoreIn X ≤ X :=
  Subgroup.map_subtype_le (CFSG.oddCore X)

private theorem odd_card_oddCoreIn_X [Finite G] (X : Subgroup G) :
    Odd (Nat.card (oddCoreIn X)) :=
  CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X

private theorem twoCoreIn_le_X (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem conj_mem_twoCoreIn {X : Subgroup G} {x y : G} (hx : x ∈ X)
    (hy : y ∈ twoCoreIn X) : x * y * x⁻¹ ∈ twoCoreIn X := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * m * ⟨x, hx⟩⁻¹, ?_, ?_⟩
  · exact (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem m hm ⟨x, hx⟩
  · simp

theorem sl23_exists_q_c (g : SL23) : ∃ q c : SL23, q ^ 4 = 1 ∧ c ^ 3 = 1 ∧ g = q * c := by
  have h : ∀ g : SL23, ∃ c : SL23, c ^ 3 = 1 ∧ (g * c⁻¹) ^ 4 = 1 := by decide
  obtain ⟨c, hc, hq⟩ := h g
  exact ⟨g * c⁻¹, c, hq, hc, by group⟩

theorem sec11_pocket_decomp [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {k : G} (hk : k ∈ K1) :
    ∃ q c : G, q ∈ secQ K1 K2 ∧ c ∈ K1 ∧ c ^ 3 = 1 ∧ k = q * c := by
  obtain ⟨e⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  obtain ⟨q0, c0, hq0, hc0, hg⟩ := sl23_exists_q_c (e ⟨k, hk⟩)
  have hq4 : (e.symm q0 : G) ^ 4 = 1 := by
    have h : e.symm q0 ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hq0, map_one]
    simpa using congrArg Subtype.val h
  have hc3 : (e.symm c0 : G) ^ 3 = 1 := by
    have h : e.symm c0 ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hc0, map_one]
    simpa using congrArg Subtype.val h
  have hqQ1 : (e.symm q0 : G) ∈ twoCoreIn K1 :=
    sec10T_two_elem_Q1 hP5 hC5 hpsp hctx (e.symm q0).2 ⟨2, by simpa using hq4⟩
  have hqQ : (e.symm q0 : G) ∈ secQ K1 K2 := by
    rw [sec10KS_twoCore_sup hP5 hC5 hpsp hctx]
    exact Subgroup.mem_sup_left hqQ1
  refine ⟨e.symm q0, e.symm c0, hqQ, (e.symm c0).2, hc3, ?_⟩
  have h : (⟨k, hk⟩ : ↥K1) = e.symm q0 * e.symm c0 := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hg
  exact congrArg Subtype.val h

theorem sec11_secQ_swap (K1 K2 : Subgroup G) : secQ K2 K1 = secQ K1 K2 := by
  unfold secQ
  rw [sup_comm]

theorem sec11_pocket_decomp2 [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {k : G} (hk : k ∈ K2) :
    ∃ q c : G, q ∈ secQ K1 K2 ∧ c ∈ K2 ∧ c ^ 3 = 1 ∧ k = q * c := by
  have h := sec11_pocket_decomp hP5 hC5 hpsp hctx.swap hk
  rwa [sec11_secQ_swap] at h

theorem sec11_Q_le_sup (K1 K2 : Subgroup G) : secQ K1 K2 ≤ K1 ⊔ K2 :=
  twoCoreIn_le_X (K1 ⊔ K2)

theorem sec11_conj_mem_Q {K1 K2 : Subgroup G} {k q : G} (hk : k ∈ K1 ⊔ K2)
    (hq : q ∈ secQ K1 K2) : k * q * k⁻¹ ∈ secQ K1 K2 :=
  conj_mem_twoCoreIn hk hq

theorem sec11_Q_isPGroup [Finite G] (K1 K2 : Subgroup G) : IsPGroup 2 (secQ K1 K2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold secQ twoCoreIn CFSG.inSubgroup
  exact (CFSG.pCore_isPGroup (G := ↥(K1 ⊔ K2)) (p := 2)).map (K1 ⊔ K2).subtype

theorem sec11_Q_inf_oddCore [Finite G] {K1 K2 X : Subgroup G} {y : G} (hy : y ∈ secQ K1 K2)
    (hyX : y ∈ oddCoreIn X) : y = 1 := by
  obtain ⟨k, hk⟩ := (sec11_Q_isPGroup K1 K2).exists_orderOf_eq_pow (⟨y, hy⟩ : secQ K1 K2)
  have hk' : orderOf y = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨y, hy⟩ : secQ K1 K2)).trans hk
  have hodd : Odd (orderOf y) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn_X X) (Subgroup.orderOf_dvd_natCard _ hyX)
  rw [hk'] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk'
  exact orderOf_eq_one_iff.mp hk'

theorem sec11_K0_le (t z : G) :
    secK0 t z ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
  unfold secK0 oTwoRes
  exact (Subgroup.closure_le _).mpr (fun x hx => hx.1)

theorem sec11_conj_mem_oddCoreIn [Finite G] {X : Subgroup G} {c : G}
    (hc : c ∈ normalizer (X : Set G)) {y : G} (hy : y ∈ oddCoreIn X) :
    c * y * c⁻¹ ∈ oddCoreIn X := by
  have hc1 : ∀ h ∈ X, c * h * c⁻¹ ∈ X := fun h hh => (Subgroup.mem_normalizer_iff.mp hc h).mp hh
  have hc2 : ∀ h ∈ X, c⁻¹ * h * c ∈ X := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp hc (c⁻¹ * h * c)).mpr (by simpa [mul_assoc] using hh)
  set S : Subgroup G := (oddCoreIn X).map (MulAut.conj c).toMonoidHom with hS
  have hSH : S ≤ X := by
    rintro _ ⟨u, hu, rfl⟩
    exact hc1 u (oddCoreIn_le_X X hu)
  have hSodd : Odd (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact odd_card_oddCoreIn_X X
  have hSn : ∀ h ∈ X, ∀ s ∈ S, h * s * h⁻¹ ∈ S := by
    intro h hh s hs
    obtain ⟨u, hu, rfl⟩ := hs
    refine ⟨(c⁻¹ * h * c) * u * (c⁻¹ * h * c)⁻¹,
      CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (hc2 h hh) hu, ?_⟩
    show c * ((c⁻¹ * h * c) * u * (c⁻¹ * h * c)⁻¹) * c⁻¹ = h * (c * u * c⁻¹) * h⁻¹
    group
  have hnorm : X ≤ Subgroup.normalizer (S : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hSn h hh s hs, fun hs => ?_⟩
    have := hSn h⁻¹ (X.inv_mem hh) _ hs
    simpa [mul_assoc] using this
  exact CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes hSH hnorm hSodd ⟨y, hy, rfl⟩

theorem sec11_K_le_K0 [Finite G] (hK0 : Asc82Lemma10K0) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) : K1 ⊔ K2 ≤ secK0 t z := by
  rw [(hK0 G t L S z K1 K2 hctx).1]
  exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

theorem sec11_K0_eq_sup [Finite G] (hK0 : Asc82Lemma10K0) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    secK0 t z = oddCoreIn (secK0 t z) ⊔ K1 ⊔ K2 := by
  have h1 := (hK0 G t L S z K1 K2 hctx).1
  have hKle : K1 ⊔ K2 ≤ secK0 t z := sec11_K_le_K0 hK0 hctx
  have hOle : oddCoreIn (centralizer ({t} : Set G)) ≤ secK0 t z := by
    rw [h1]
    exact le_sup_left.trans le_sup_left
  have hO2 : oddCoreIn (centralizer ({t} : Set G)) ≤ oddCoreIn (secK0 t z) := by
    refine CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes hOle ?_
      (odd_card_oddCoreIn_X _)
    intro k hk
    exact CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ ((sec11_K0_le t z hk).1)
  apply le_antisymm
  · calc secK0 t z = oddCoreIn (centralizer ({t} : Set G)) ⊔ K1 ⊔ K2 := h1
      _ ≤ oddCoreIn (secK0 t z) ⊔ K1 ⊔ K2 := sup_le_sup_right (sup_le_sup_right hO2 K1) K2
  · exact sup_le (sup_le (oddCoreIn_le_X _) (le_sup_left.trans hKle)) (le_sup_right.trans hKle)

theorem sec11_K0_decomp [Finite G] (hK0 : Asc82Lemma10K0) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {g : G} (hg : g ∈ secK0 t z) :
    ∃ n ∈ oddCoreIn (secK0 t z), ∃ k ∈ K1 ⊔ K2, g = n * k := by
  have hK := sec11_K0_eq_sup hK0 hctx
  have hKle : K1 ⊔ K2 ≤ secK0 t z := sec11_K_le_K0 hK0 hctx
  have hnorm : K1 ⊔ K2 ≤ normalizer (oddCoreIn (secK0 t z) : Set G) :=
    hKle.trans (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _)
  have hg' : g ∈ oddCoreIn (secK0 t z) ⊔ (K1 ⊔ K2) := by
    rw [← sup_assoc, ← hK]
    exact hg
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hg'
  obtain ⟨n, hn, k, hk, rfl⟩ := Set.mem_mul.mp hg'
  exact ⟨n, hn, k, hk, rfl⟩

theorem sec11_cent_K0_Q [Finite G] (hK0 : Asc82Lemma10K0) (hP5 : Asc82FactPockets5)
    (hC5 : Asc82FactCentZ5) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) {g : G} (hg : g ∈ secK0 t z)
    (hc : ∀ q ∈ secQ K1 K2, g * q = q * g) :
    ∃ n ∈ oddCoreIn (secK0 t z), ∃ e ∈ zpowers z, g = n * e := by
  obtain ⟨n, hn, k, hk, rfl⟩ := sec11_K0_decomp hK0 hctx hg
  have hKle : K1 ⊔ K2 ≤ secK0 t z := sec11_K_le_K0 hK0 hctx
  have hcomm12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a := sec10Z_comm hP5 hpsp hctx
  have hQsup := sec10KS_twoCore_sup hP5 hC5 hpsp hctx
  have hkc : ∀ q ∈ secQ K1 K2, k * q = q * k := by
    intro q hq
    have hq' : k * q * k⁻¹ ∈ secQ K1 K2 := sec11_conj_mem_Q hk hq
    have h1 : n * (k * q * k⁻¹) * n⁻¹ = q := by
      calc n * (k * q * k⁻¹) * n⁻¹ = (n * k) * q * (n * k)⁻¹ := by group
        _ = q := by rw [hc q hq]; group
    have hqK0 : k * q * k⁻¹ ∈ secK0 t z := hKle (sec11_Q_le_sup K1 K2 hq')
    have hcN : n * (k * q * k⁻¹) * n⁻¹ * (k * q * k⁻¹)⁻¹ ∈ oddCoreIn (secK0 t z) := by
      have hin : n⁻¹ ∈ oddCoreIn (secK0 t z) := Subgroup.inv_mem _ hn
      have hconj := Subgroup.mul_mem _ hn
        (CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hqK0 hin)
      simpa only [mul_assoc] using hconj
    have hcQ : n * (k * q * k⁻¹) * n⁻¹ * (k * q * k⁻¹)⁻¹ ∈ secQ K1 K2 := by
      rw [h1]
      exact (secQ K1 K2).mul_mem hq ((secQ K1 K2).inv_mem hq')
    have hone := sec11_Q_inf_oddCore hcQ hcN
    have h2 : n * (k * q * k⁻¹) * n⁻¹ = k * q * k⁻¹ := mul_inv_eq_one.mp hone
    have h3 : q = k * q * k⁻¹ := h1.symm.trans h2
    calc k * q = (k * q * k⁻¹) * k := by group
      _ = q * k := by rw [← h3]
  obtain ⟨a1, ha1, a2, ha2, hka⟩ := exists_mul_of_mem_sup_of_commute hcomm12 hk
  have hz1 : a1 ∈ zpowers z := by
    refine sec10KS_cent_Qi hP5 hC5 hpsp hctx a1 ha1 ?_
    intro b hb
    have hbK1 : b ∈ K1 := twoCoreIn_le_X K1 hb
    have hbQ : b ∈ secQ K1 K2 := by rw [hQsup]; exact Subgroup.mem_sup_left hb
    have hkb : k * b = b * k := hkc b hbQ
    have key : a1 * b * a2 = b * a1 * a2 := by
      calc a1 * b * a2 = a1 * (b * a2) := by group
        _ = a1 * (a2 * b) := by rw [hcomm12 b hbK1 a2 ha2]
        _ = (a1 * a2) * b := by group
        _ = k * b := by rw [← hka]
        _ = b * k := hkb
        _ = b * (a1 * a2) := by rw [hka]
        _ = b * a1 * a2 := by group
    exact mul_right_cancel key
  have hz2 : a2 ∈ zpowers z := by
    refine sec10KS_cent_Qi hP5 hC5 hpsp hctx.swap a2 ha2 ?_
    intro b hb
    have hbK2 : b ∈ K2 := twoCoreIn_le_X K2 hb
    have hbQ : b ∈ secQ K1 K2 := by rw [hQsup]; exact Subgroup.mem_sup_right hb
    have hkb : k * b = b * k := hkc b hbQ
    have key : a1 * (a2 * b) = a1 * (b * a2) := by
      calc a1 * (a2 * b) = (a1 * a2) * b := by group
        _ = k * b := by rw [← hka]
        _ = b * k := hkb
        _ = b * (a1 * a2) := by rw [hka]
        _ = (b * a1) * a2 := by group
        _ = (a1 * b) * a2 := by rw [hcomm12 a1 ha1 b hbK2]
        _ = a1 * (b * a2) := by group
    exact mul_left_cancel key
  exact ⟨n, hn, k, by rw [hka]; exact Subgroup.mul_mem _ hz1 hz2, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
