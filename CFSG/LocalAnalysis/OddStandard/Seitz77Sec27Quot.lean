module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

section QuotA
variable {G : Type*} [Group G]

theorem odd_card_oddCore_s27 [Finite G] : Odd (Nat.card (CFSG.oddCore G)) := by
  have h2 : CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
    simp only [CFSG.oddCore, CFSG.pPrimeCore, Nat.coprime_two_left]
  rw [h2]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := G))

theorem le_oddCore_of_normal_odd {N : Subgroup G} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ CFSG.oddCore G :=
  le_sSup ⟨hN, hodd⟩

theorem card_comap_of_surjective_s27 {X Y : Type*} [Group X] [Group Y] [Finite X] {f : X →* Y}
    (hf : Function.Surjective f) (L : Subgroup Y) :
    Nat.card (L.comap f) = Nat.card f.ker * Nat.card L := by
  have : Finite Y := Finite.of_surjective f hf
  have h1 := card_mul_index (L.comap f)
  rw [index_comap_of_surjective L hf] at h1
  have h2 := card_mul_index L
  have h3 : Nat.card X = Nat.card f.ker * Nat.card Y := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, mul_comm]
  have hidx : L.index ≠ 0 := index_ne_zero_of_finite
  rw [h3, ← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx) (by rw [h1]; ring)

theorem perfect_odd_image_trivial [Finite G] {P : Subgroup G} (hP : ⁅P, P⁆ = P) {H : Type*}
    [Group H] (f : G →* H) (hodd : Odd (Nat.card (P.map f))) : P ≤ f.ker := by
  have hPerfP : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  have hPerfQ : Group.IsPerfect (P.map f) := Group.IsPerfect.map f
  have : Finite (P.map f) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hsolv : Group.IsSolvable (P.map f) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Subsingleton (P.map f) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (P.map f) hsolv
  exact (Subgroup.map_eq_bot_iff P).mp (Subgroup.eq_bot_of_subsingleton _)

theorem oddCore_quotient_bot [Finite G] : CFSG.oddCore (G ⧸ CFSG.oddCore G) = ⊥ := by
  set N := CFSG.oddCore G with hN
  set K := CFSG.oddCore (G ⧸ N) with hK
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hKnormal : K.Normal := CFSG.oddCore_normal _
  have hcomapNormal : (K.comap (QuotientGroup.mk' N)).Normal := hKnormal.comap _
  have hcard := card_comap_of_surjective_s27 hsurj K
  have hodd : Odd (Nat.card (K.comap (QuotientGroup.mk' N))) := by
    rw [hcard, QuotientGroup.ker_mk']
    exact (odd_card_oddCore_s27 (G := G)).mul (odd_card_oddCore_s27 (G := G ⧸ N))
  have hle : K.comap (QuotientGroup.mk' N) ≤ N := le_oddCore_of_normal_odd hcomapNormal hodd
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg : g ∈ N := hle hx
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff g).mpr hg

theorem exists_two_part_lift {H : Type*} [Group H] [Finite G] (f : G →* H) (c : G)
    (h2 : ∃ n : ℕ, orderOf (f c) = 2 ^ n) :
    ∃ c' ∈ zpowers c, f c' = f c ∧ ∃ n : ℕ, orderOf c' = 2 ^ n := by
  obtain ⟨n, hn⟩ := h2
  have hpos : orderOf c ≠ 0 := (orderOf_pos c).ne'
  obtain ⟨a, m, hmodd, hom⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have hcop : Nat.Coprime (2 ^ n) m :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hmodd)
  obtain ⟨u, hu1, hu2⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨c ^ u, Subgroup.pow_mem _ (Subgroup.mem_zpowers c) u, ?_, ?_⟩
  · rw [map_pow]
    have : (f c) ^ u = (f c) ^ 1 := by
      rw [pow_eq_pow_iff_modEq, hn]
      exact hu1
    rw [this, pow_one]
  · have hmu : m ∣ u := (Nat.modEq_zero_iff_dvd).mp hu2
    have hdvd : orderOf (c ^ u) ∣ 2 ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul]
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hom]
      obtain ⟨k, hk⟩ := hmu
      exact ⟨k, by rw [hk]; ring⟩
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨b, hb⟩

theorem rangeEquiv_of_ker_eq {B C₁ C₂ : Type*} [Group B] [Group C₁] [Group C₂] (f₁ : B →* C₁)
    (f₂ : B →* C₂) (h : f₁.ker = f₂.ker) : Nonempty (f₁.range ≃* f₂.range) :=
  ⟨(QuotientGroup.quotientKerEquivRange f₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivRange f₂))⟩
end QuotA

section
variable {G : Type*} [Group G]

theorem exists_mem_conj_eq_mul_of_odd (M : Subgroup G) (hM : Odd (Nat.card M)) {t m : G}
    (ht : t * t = 1) (hm : m ∈ M) (hs : (t * m) * (t * m) = 1) :
    ∃ r ∈ M, r * t * r⁻¹ = t * m := by
  obtain ⟨k, hk⟩ := hM
  have hmn : m ^ (2 * k + 1) = 1 := by
    have h := pow_card_eq_one' (G := M) (x := ⟨m, hm⟩)
    rw [hk] at h
    simpa using congrArg Subtype.val h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * m * t = m⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    simpa [mul_assoc] using hs
  have h3 : t * m⁻¹ * t = m := by
    have h := congrArg (fun z => z⁻¹) h1
    simpa [hti, mul_assoc] using h
  have hc : ∀ (y : G) (j : ℕ), t * y ^ j * t = (t * y * t) ^ j := by
    intro y j
    simpa [MulAut.conj_apply, hti] using map_pow (MulAut.conj t) y j
  obtain ⟨r, hr⟩ : ∃ r : G, r = (m⁻¹) ^ (k + 1) := ⟨_, rfl⟩
  have hrM : r ∈ M := hr ▸ M.pow_mem (M.inv_mem hm) _
  have h2 : t * r * t = r⁻¹ := by
    rw [hr, hc, h3, inv_pow, inv_inv]
  have h4 : r * r = m⁻¹ := by
    have h5 : (m⁻¹) ^ (2 * k + 1) = 1 := by rw [inv_pow, hmn, inv_one]
    rw [hr, ← pow_add]
    calc (m⁻¹) ^ (k + 1 + (k + 1)) = (m⁻¹) ^ (2 * k + 1) * m⁻¹ := by
          rw [← pow_succ]; congr 1; omega
      _ = m⁻¹ := by rw [h5, one_mul]
  refine ⟨r, hrM, ?_⟩
  calc r * t * r⁻¹ = r * t * (t * r * t) := by rw [h2]
    _ = r * (t * t) * r * t := by simp only [mul_assoc]
    _ = m⁻¹ * t := by rw [ht, mul_one, h4]
    _ = (t * m * t) * t := by rw [h1]
    _ = t * m * (t * t) := by simp only [mul_assoc]
    _ = t * m := by rw [ht, mul_one]

theorem centralizer_map_of_odd [Finite G] (M : Subgroup G) [M.Normal] (hM : Odd (Nat.card M))
    {t : G} (ht : orderOf t = 2) :
    centralizer ({(QuotientGroup.mk t : G ⧸ M)} : Set (G ⧸ M)) =
      (centralizer ({t} : Set G)).map (QuotientGroup.mk' M) := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, pow_two] at h
  ext q
  rw [Subgroup.mem_map]
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Subgroup.mem_centralizer_singleton_iff] at hq
    have hs1 : ((t * (x * t * x⁻¹) : G) : G ⧸ M) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        hq, mul_assoc (↑t : G ⧸ M) (↑x : G ⧸ M), mul_inv_cancel, mul_one,
        ← QuotientGroup.mk_mul, ht2, QuotientGroup.mk_one]
    have hm : t * (x * t * x⁻¹) ∈ M := (QuotientGroup.eq_one_iff _).mp hs1
    have hs2 : (t * (t * (x * t * x⁻¹))) * (t * (t * (x * t * x⁻¹))) = 1 := by
      have e1 : t * (t * (x * t * x⁻¹)) = x * t * x⁻¹ := by rw [← mul_assoc, ht2, one_mul]
      rw [e1]
      calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    obtain ⟨r, hrM, hr⟩ := exists_mem_conj_eq_mul_of_odd M hM ht2 hm hs2
    have e2 : t * (t * (x * t * x⁻¹)) = x * t * x⁻¹ := by rw [← mul_assoc, ht2, one_mul]
    rw [e2] at hr
    refine ⟨r⁻¹ * x, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc r⁻¹ * x * t = r⁻¹ * (x * t * x⁻¹) * x := by group
        _ = r⁻¹ * (r * t * r⁻¹) * x := by rw [hr]
        _ = t * (r⁻¹ * x) := by group
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        (QuotientGroup.eq_one_iff r).mpr hrM, inv_one, one_mul]
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hy]
end

section QuotB
variable {M : Type*} [Group M] [Finite M] (K : Subgroup M) [K.Normal]

@[expose] def qPi : M →* (M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K) :=
  (QuotientGroup.mk' (CFSG.oddCore (M ⧸ K))).comp (QuotientGroup.mk' K)

omit [Finite M] in
theorem qPi_surjective : Function.Surjective (qPi K) := by
  intro y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  exact ⟨x, rfl⟩

omit [Finite M] in
theorem le_ker_qPi : K ≤ (qPi K).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have h : (QuotientGroup.mk x : M ⧸ K) = 1 := (QuotientGroup.eq_one_iff x).2 hx
  show (QuotientGroup.mk (QuotientGroup.mk x : M ⧸ K) : (M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K)) = 1
  rw [h]
  rfl

omit [Finite M] in
theorem mem_ker_qPi {x : M} :
    x ∈ (qPi K).ker ↔ (QuotientGroup.mk x : M ⧸ K) ∈ CFSG.oddCore (M ⧸ K) := by
  rw [MonoidHom.mem_ker]
  exact QuotientGroup.eq_one_iff (N := CFSG.oddCore (M ⧸ K)) (QuotientGroup.mk x : M ⧸ K)

theorem exists_odd_pow_mem_of_mem_ker_qPi {x : M} (hx : x ∈ (qPi K).ker) :
    ∃ m : ℕ, Odd m ∧ x ^ m ∈ K := by
  have hx' := (mem_ker_qPi K).1 hx
  have hdvd : orderOf (QuotientGroup.mk x : M ⧸ K) ∣ Nat.card (CFSG.oddCore (M ⧸ K)) :=
    Subgroup.orderOf_dvd_natCard _ hx'
  refine ⟨orderOf (QuotientGroup.mk x : M ⧸ K), Odd.of_dvd_nat odd_card_oddCore_s27 hdvd, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact pow_orderOf_eq_one _

theorem inf_ker_qPi_le {T : Subgroup M} (hT : IsPGroup 2 T) : T ⊓ (qPi K).ker ≤ K := by
  intro x hx
  obtain ⟨hxT, hxk⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨m, hm, hxm⟩ := exists_odd_pow_mem_of_mem_ker_qPi K hxk
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.1 hT ⟨x, hxT⟩
  have hn' : orderOf x = 2 ^ n := by
    rw [← Subgroup.orderOf_mk x hxT]
    exact hn
  have hcop : m.gcd (orderOf x) = 1 := by
    rw [hn']
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hm)
  exact Subgroup.zpowers_le.2 hxm (mem_zpowers_pow_iff.2 hcop)

theorem card_ker_qPi :
    Nat.card (qPi K).ker = Nat.card K * Nat.card (CFSG.oddCore (M ⧸ K)) := by
  have h1 : Nat.card (qPi K).ker * Nat.card ((M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K)) = Nat.card M :=
    Subgroup.card_ker_mul_card_of_surjective (qPi_surjective K)
  have h2 : Nat.card K * Nat.card (M ⧸ K) = Nat.card M := Subgroup.card_mul_index K
  have h3 : Nat.card (CFSG.oddCore (M ⧸ K)) * Nat.card ((M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K)) =
      Nat.card (M ⧸ K) := Subgroup.card_mul_index (CFSG.oddCore (M ⧸ K))
  have hpos : 0 < Nat.card ((M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K)) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, mul_assoc, h3, h2]

theorem oddCore_qPi_bot :
    CFSG.oddCore ((M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K)) = ⊥ :=
  oddCore_quotient_bot

theorem exists_pre_centralizer_qPi {t : M} (ht2 : t * t ∈ K) (ht : t ∉ (qPi K).ker)
    {y : (M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K)} (hy : y ∈ centralizer ({qPi K t} : Set _)) :
    ∃ x : M, qPi K x = y ∧ x * t * x⁻¹ * t⁻¹ ∈ K := by
  have hsq : (QuotientGroup.mk t : M ⧸ K) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact ht2
  have hne : (QuotientGroup.mk t : M ⧸ K) ≠ 1 := fun h =>
    ht (le_ker_qPi K ((QuotientGroup.eq_one_iff t).1 h))
  have hord : orderOf (QuotientGroup.mk t : M ⧸ K) = 2 := orderOf_eq_prime hsq hne
  have hcen := centralizer_map_of_odd (CFSG.oddCore (M ⧸ K)) odd_card_oddCore_s27 hord
  have hy' : y ∈ centralizer ({(QuotientGroup.mk (QuotientGroup.mk t : M ⧸ K) :
      (M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K))} : Set _) := hy
  rw [hcen] at hy'
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy'
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  refine ⟨x, rfl, ?_⟩
  have hc : (QuotientGroup.mk x : M ⧸ K) * QuotientGroup.mk t =
      QuotientGroup.mk t * QuotientGroup.mk x := mem_centralizer_singleton_iff.1 hz
  rw [← QuotientGroup.eq_one_iff (N := K)]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hc]
  group
end QuotB

section
variable {G : Type*} [Group G]

theorem perfect_le_normalizer_sylow_core {H : Type*} [Group H] [Finite H] (N O W T : Subgroup H)
    [N.Normal] (hdec : ∀ x ∈ N, ∃ o ∈ O, ∃ w ∈ W, x = o * w) (hWN : W ≤ N)
    (hO : ∀ o ∈ O, (∃ k : ℕ, o ^ 2 ^ k = 1) → o = 1)
    (hW2 : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k = 1) (hT2 : ∀ t ∈ T, ∃ k : ℕ, t ^ 2 ^ k = 1)
    (hTO : ∀ t ∈ T, ∀ o ∈ O, t * o = o * t) (hH : ∀ h : H, ∃ t ∈ T, ∃ n ∈ N, h = t * n) :
    ∀ t ∈ T, ∀ w ∈ W, t * w * t⁻¹ ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWp : IsPGroup 2 W := fun x => by
    obtain ⟨k, hk⟩ := hW2 x.1 x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hTp : IsPGroup 2 T := fun x => by
    obtain ⟨k, hk⟩ := hT2 x.1 x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨Y', hY'⟩ := hWp.exists_le_sylow
  obtain ⟨Y, hY⟩ := hTp.exists_le_sylow
  have h1 : ∀ x ∈ N, x ∈ Y' → x ∈ W := by
    intro x hxN hxY
    obtain ⟨o, ho, w, hw, rfl⟩ := hdec x hxN
    have hoY : o ∈ Y' := by
      have : o * w * w⁻¹ ∈ Y' := Subgroup.mul_mem _ hxY (Subgroup.inv_mem _ (hY' hw))
      simpa using this
    obtain ⟨k, hk⟩ := Y'.isPGroup' ⟨o, hoY⟩
    have : o = 1 := hO o ho ⟨k, by simpa using congrArg Subtype.val hk⟩
    subst this
    simpa using hw
  have h2 : ∀ t ∈ T, t ∈ Y' := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Y' Y
    obtain ⟨t₀, ht₀, n, hn, rfl⟩ := hH g
    obtain ⟨o, ho, w, hw, rfl⟩ := hdec n hn
    have hw' : w • Y' = Y' := Sylow.smul_eq_iff_mem_normalizer.mpr (le_normalizer (hY' hw))
    have ht₀Y : t₀ • Y = Y := Sylow.smul_eq_iff_mem_normalizer.mpr (le_normalizer (hY ht₀))
    rw [mul_smul, mul_smul, hw'] at hg
    have hoY : o • Y' = Y := (eq_inv_smul_iff.mpr hg).trans (inv_smul_eq_iff.mpr ht₀Y.symm)
    intro t ht
    have hmem : t ∈ ((o • Y' : Sylow 2 H) : Subgroup H) := by rw [hoY]; exact hY ht
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨s, hs, hst⟩ := hmem
    change o * s * o⁻¹ = t at hst
    have hc := hTO t ht o ho
    have : s = t := by
      calc s = o⁻¹ * (o * s * o⁻¹) * o := by group
        _ = o⁻¹ * t * o := by rw [hst]
        _ = t := by rw [mul_assoc, hc, inv_mul_cancel_left]
    exact this ▸ hs
  intro t ht w hw
  have htY : t ∈ Y' := h2 t ht
  have hwY : w ∈ Y' := hY' hw
  refine h1 _ ?_ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htY hwY) (Subgroup.inv_mem _ htY))
  exact ‹N.Normal›.conj_mem w (hWN hw) t

open scoped Pointwise in
theorem perfect_le_normalizer_sylow_two_subgroup [Finite G] {O W T : Subgroup G}
    (hOn : ∀ w ∈ W, ∀ o ∈ O, w * o * w⁻¹ ∈ O)
    (hO : ∀ o ∈ O, (∃ k : ℕ, o ^ 2 ^ k = 1) → o = 1)
    (hW2 : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k = 1) (hT2 : ∀ t ∈ T, ∃ k : ℕ, t ^ 2 ^ k = 1)
    (hTn : T ≤ normalizer ((O ⊔ W : Subgroup G) : Set G))
    (hTO : ∀ t ∈ T, ∀ o ∈ O, t * o = o * t) :
    ∀ t ∈ T, ∀ w ∈ W, t * w * t⁻¹ ∈ W := by
  have hWnO : W ≤ normalizer (O : Set G) := le_normalizer_iff.mpr hOn
  have hdecN : ∀ x ∈ O ⊔ W, ∃ o ∈ O, ∃ w ∈ W, x = o * w := by
    intro x hx
    have : x ∈ (O : Set G) * W := by
      rw [← coe_mul_of_right_le_normalizer_left O W hWnO]; exact hx
    obtain ⟨o, ho, w, hw, rfl⟩ := this
    exact ⟨o, ho, w, hw, rfl⟩
  have hdecX : ∀ x ∈ T ⊔ (O ⊔ W), ∃ t ∈ T, ∃ n ∈ O ⊔ W, x = t * n := by
    intro x hx
    have : x ∈ (T : Set G) * ((O ⊔ W : Subgroup G) : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right T (O ⊔ W) hTn]; exact hx
    obtain ⟨t, ht, n, hn, rfl⟩ := this
    exact ⟨t, ht, n, hn, rfl⟩
  have hON : O ≤ O ⊔ W := le_sup_left
  have hWN : W ≤ O ⊔ W := le_sup_right
  have hNX : O ⊔ W ≤ T ⊔ (O ⊔ W) := le_sup_right
  have hTX : T ≤ T ⊔ (O ⊔ W) := le_sup_left
  have hXn : T ⊔ (O ⊔ W) ≤ normalizer ((O ⊔ W : Subgroup G) : Set G) :=
    sup_le hTn le_normalizer
  have : ((O ⊔ W).subgroupOf (T ⊔ (O ⊔ W))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNX).mpr hXn
  have key := perfect_le_normalizer_sylow_core (H := ↥(T ⊔ (O ⊔ W)))
    ((O ⊔ W).subgroupOf (T ⊔ (O ⊔ W))) (O.subgroupOf (T ⊔ (O ⊔ W)))
    (W.subgroupOf (T ⊔ (O ⊔ W))) (T.subgroupOf (T ⊔ (O ⊔ W)))
    (by
      rintro ⟨x, hxX⟩ hx
      obtain ⟨o, ho, w, hw, rfl⟩ := hdecN x hx
      exact ⟨⟨o, hNX (hON ho)⟩, ho, ⟨w, hNX (hWN hw)⟩, hw, rfl⟩)
    (fun x hx => hWN hx)
    (by
      rintro ⟨o, hoX⟩ ho ⟨k, hk⟩
      exact Subtype.ext (hO o ho ⟨k, by simpa using congrArg Subtype.val hk⟩))
    (by
      rintro ⟨w, hwX⟩ hw
      obtain ⟨k, hk⟩ := hW2 w hw
      exact ⟨k, Subtype.ext (by simpa using hk)⟩)
    (by
      rintro ⟨t, htX⟩ ht
      obtain ⟨k, hk⟩ := hT2 t ht
      exact ⟨k, Subtype.ext (by simpa using hk)⟩)
    (by
      rintro ⟨t, htX⟩ ht ⟨o, hoX⟩ ho
      exact Subtype.ext (hTO t ht o ho))
    (by
      rintro ⟨x, hxX⟩
      obtain ⟨t, ht, n, hn, rfl⟩ := hdecX x hxX
      exact ⟨⟨t, hTX ht⟩, ht, ⟨n, hNX hn⟩, hn, rfl⟩)
  intro t ht w hw
  exact key ⟨t, hTX ht⟩ ht ⟨w, hNX (hWN hw)⟩ hw

theorem perfect_le_normalizer_sylow_eq_top {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (S : Subgroup A) (hS : ∀ a : A, (∃ k : ℕ, a ^ 2 ^ k = 1) → a ∈ S) : S = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T₀ : Sylow 2 A := default
  have hT₀ : (T₀ : Subgroup A) ≤ S.normalCore := by
    intro a ha g
    apply hS
    obtain ⟨k, hk⟩ := T₀.isPGroup' ⟨a, ha⟩
    refine ⟨k, ?_⟩
    have h1 : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [conj_pow, h1]
    simp
  have hdvd : S.normalCore.index ∣ (T₀ : Subgroup A).index := Subgroup.index_dvd_of_le hT₀
  have hodd : Odd S.normalCore.index := by
    rw [Nat.odd_iff]
    by_contra h
    exact T₀.not_dvd_index (dvd_trans (by omega) hdvd)
  have hsolv : Group.IsSolvable (A ⧸ S.normalCore) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by rwa [Subgroup.index_eq_card] at hodd)
  have hsub : Subsingleton (A ⧸ S.normalCore) := by
    by_contra h
    have : Nontrivial (A ⧸ S.normalCore) := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable (A ⧸ S.normalCore) hsolv
  have h1 : S.normalCore.index = 1 := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_of_subsingleton 1
  rw [Subgroup.index_eq_one] at h1
  exact eq_top_iff.mpr (h1 ▸ S.normalCore_le)

theorem perfect_le_normalizer_sylow [Finite G] {O W P : Subgroup G} (hO : Odd (Nat.card O))
    (hW : IsPGroup 2 W) (hOn : ∀ w ∈ W, ∀ o ∈ O, w * o * w⁻¹ ∈ O) (hP : ⁅P, P⁆ = P)
    (hPn : P ≤ normalizer ((O ⊔ W : Subgroup G) : Set G))
    (hPc : P ≤ centralizer (O : Set G)) : P ≤ normalizer (W : Set G) := by
  have hO' : ∀ o ∈ O, (∃ k : ℕ, o ^ 2 ^ k = 1) → o = 1 := by
    rintro o ho ⟨k, hk⟩
    have h1 : orderOf o ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf o ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O ho
    have h3 : Nat.Coprime (2 ^ k) (Nat.card O) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hO)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2)
  have hW' : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have key : ∀ x ∈ P, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ normalizer (W : Set G) := by
    rintro x hx ⟨k, hk⟩
    have hTP : zpowers x ≤ P := zpowers_le.mpr hx
    have hT := perfect_le_normalizer_sylow_two_subgroup (T := zpowers x) hOn hO' hW'
      (by
        intro t ht
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ht
        refine ⟨k, ?_⟩
        rw [← zpow_natCast (x ^ m), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow])
      (hTP.trans hPn)
      (fun t ht o ho => (mem_centralizer_iff.mp (hPc (hTP ht)) o ho).symm)
    exact (le_normalizer_iff.mpr hT) (mem_zpowers x)
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  have hS : (normalizer (W : Set G)).comap P.subtype = ⊤ := by
    apply perfect_le_normalizer_sylow_eq_top
    rintro a ⟨k, hk⟩
    exact key a a.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  intro p hp
  have : (⟨p, hp⟩ : P) ∈ (normalizer (W : Set G)).comap P.subtype := by rw [hS]; trivial
  exact this

end

end CFSG.OddStandard.Seitz77
