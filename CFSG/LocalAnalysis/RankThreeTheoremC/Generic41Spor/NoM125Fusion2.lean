module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125Fusion1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

namespace IsM125

private abbrev Zc (S : Subgroup G) : Subgroup G := centralizer (S : Set G) ⊓ S

private theorem mem_Zc {S : Subgroup G} {x : G} :
    x ∈ Zc S ↔ x ∈ S ∧ ∀ t ∈ S, t * x = x * t := by
  rw [Zc, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact ⟨fun ⟨hc, hS⟩ => ⟨hS, fun t ht => hc t ht⟩, fun ⟨hS, hc⟩ => ⟨fun t ht => hc t ht, hS⟩⟩

private theorem card_Zc {R : Subgroup G} (hR : IsM125 p R) : Nat.card (Zc R) = p :=
  card_Z hR

private theorem conj_comm_aux {g x y : G} (hxy : x * y = y * x) :
    (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) := by
  calc (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [hxy]
    _ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group

private theorem pow_eq_pow_mod' {w : G} (hw : w ^ p = 1) (n : ℕ) : w ^ n = w ^ (n % p) := by
  conv_lhs => rw [← Nat.mod_add_div n p]
  rw [pow_add, pow_mul, hw, one_pow, mul_one]

private theorem exists_nat_pow_of_mem_zpowers {w x : G} (hw : w ^ p = 1) (hw1 : w ≠ 1)
    (hx : x ∈ Subgroup.zpowers w) : ∃ k : ℕ, w ^ k = x := by
  have hord : orderOf w = p := orderOf_eq_prime hw hw1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hne : (orderOf w : ℤ) ≠ 0 := by
    rw [hord]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hnn : 0 ≤ k % (orderOf w : ℤ) := Int.emod_nonneg _ hne
  refine ⟨(k % (orderOf w : ℤ)).toNat, ?_⟩
  rw [← hk, ← zpow_mod_orderOf, ← zpow_natCast, Int.toNat_of_nonneg hnn]

private theorem card_le_of_isPGroup {S : Sylow p G} (h : IsM125 p (S : Subgroup G))
    {Q : Subgroup G} (hQ : IsPGroup p Q) : Nat.card Q ≤ Nat.card (S : Subgroup G) := by
  have hp := h.prime
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  have hdvd : p ^ n ∣ Nat.card G := by
    rw [← hn]
    exact Subgroup.card_subgroup_dvd_card Q
  have hle : n ≤ (Nat.card G).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.card_pos (α := G)).ne').1 hdvd
  have hS : Nat.card (S : Subgroup G) = p ^ (Nat.card G).factorization p :=
    Sylow.card_eq_multiplicity S
  rw [hn, hS]
  exact Nat.pow_le_pow_right hp.pos hle

private theorem exists_not_mem_E' {R : Subgroup G} (hR : IsM125 p R) :
    ∃ a ∈ R, a ∉ hR.E := by
  by_contra hcon
  push Not at hcon
  have h1 : Nat.card R ≤ Nat.card hR.E := Subgroup.card_le_of_le (fun a ha => hcon a ha)
  rw [hR.card, card_E hR] at h1
  have := Nat.pow_lt_pow_right hR.prime.one_lt (show 2 < 3 by norm_num)
  omega

private theorem zpowers_eq_Zc {R : Subgroup G} (hR : IsM125 p R) {w : G} (hw : w ∈ Zc R)
    (hw1 : w ≠ 1) : Subgroup.zpowers w = Zc R := by
  have hwp : w ^ p = 1 := ((mem_E hR).1 (Z_le_E hR hw)).2
  have hord : orderOf w = p := orderOf_eq_prime hwp hw1
  have hle : Subgroup.zpowers w ≤ Zc R := Subgroup.zpowers_le.2 hw
  have hcard : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, hord]
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcard, card_Zc hR]))

private theorem core_false {S : Sylow p G} (h : IsM125 p (S : Subgroup G)) {R : Subgroup G}
    (hR : IsM125 p R) (hER : hR.E = h.E) {b : G} (hbE : b ∈ h.E)
    (hbZ : b ∉ Zc (S : Subgroup G)) (hbR : b ∈ Zc R) : False := by
  have hp := h.prime
  have hbS : b ∈ (S : Subgroup G) := E_le h hbE
  have hbZ' : b ∉ centralizer ((S : Subgroup G) : Set G) := fun hc =>
    hbZ (mem_Zc.2 ⟨hbS, fun t ht => Subgroup.mem_centralizer_iff.1 hc t ht⟩)
  have hER_le : h.E ≤ R := by rw [← hER]; exact E_le hR
  obtain ⟨s, hsS, hsE⟩ := exists_not_mem_E' h
  obtain ⟨z', hz'⟩ : ∃ z' : G, z' = s * b * s⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hz'Z : z' ∈ Zc (S : Subgroup G) := by
    rw [hz']; exact commutator_mem_Z h hsS hbS
  have hz'ne : z' ≠ 1 := by
    intro h1
    have hcomm : s * b = b * s := by
      calc s * b = (s * b * s⁻¹ * b⁻¹) * (b * s) := by group
        _ = b * s := by rw [← hz', h1, one_mul]
    exact hsE (mem_E_of_commute h hbE hbZ' hsS hcomm)
  have hz'E : z' ∈ h.E := Z_le_E h hz'Z
  have hz'p : z' ^ p = 1 := ((mem_E h).1 hz'E).2
  have hz'R : z' ∈ R := hER_le hz'E
  have hsz : s * z' = z' * s := (mem_Zc.1 hz'Z).2 s hsS
  obtain ⟨r, hrR, hrE⟩ := exists_not_mem_E' hR
  obtain ⟨v, hv⟩ : ∃ v : G, v = r * z' * r⁻¹ * z'⁻¹ := ⟨_, rfl⟩
  have hvZR : v ∈ Zc R := by
    rw [hv]; exact commutator_mem_Z hR hrR hz'R
  have hrv : r * v = v * r := (mem_Zc.1 hvZR).2 r hrR
  have hvER : v ∈ hR.E := Z_le_E hR hvZR
  have hvE : v ∈ h.E := by rw [← hER]; exact hvER
  have hvS : v ∈ (S : Subgroup G) := E_le h hvE
  have hvp : v ^ p = 1 := ((mem_E h).1 hvE).2
  have hvcomm : v * z' = z' * v := E_comm h hvE hz'E
  have hvne : v ≠ 1 := by
    intro hv1
    have hcomm : r * z' = z' * r := by
      calc r * z' = (r * z' * r⁻¹ * z'⁻¹) * (z' * r) := by group
        _ = z' * r := by rw [← hv, hv1, one_mul]
    have hz'nc : z' ∉ centralizer (R : Set G) := by
      intro hc
      have hz'ZR : z' ∈ Zc R :=
        mem_Zc.2 ⟨hz'R, fun t ht => Subgroup.mem_centralizer_iff.1 hc t ht⟩
      have hbz : b ∈ Subgroup.zpowers z' := by
        rw [zpowers_eq_Zc hR hz'ZR hz'ne]; exact hbR
      exact hbZ (Subgroup.zpowers_le.2 hz'Z hbz)
    exact hrE (mem_E_of_commute hR (by rw [hER]; exact hz'E) hz'nc hrR hcomm)
  have hvZ : v ∉ Zc (S : Subgroup G) := by
    intro hvZS
    have hbv : b ∈ Subgroup.zpowers v := by
      rw [zpowers_eq_Zc hR hvZR hvne]; exact hbR
    exact hbZ (Subgroup.zpowers_le.2 hvZS hbv)
  have hvZ' : v ∉ centralizer ((S : Subgroup G) : Set G) := fun hc =>
    hvZ (mem_Zc.2 ⟨hvS, fun t ht => Subgroup.mem_centralizer_iff.1 hc t ht⟩)
  have hZS : Zc (S : Subgroup G) = Subgroup.zpowers z' :=
    (zpowers_eq_Zc h hz'Z hz'ne).symm
  obtain ⟨i, hi⟩ : ∃ i : ℕ, z' ^ i = s * v * s⁻¹ * v⁻¹ := by
    have hc : s * v * s⁻¹ * v⁻¹ ∈ Zc (S : Subgroup G) := commutator_mem_Z h hsS hvS
    rw [hZS] at hc
    exact exists_nat_pow_of_mem_zpowers hz'p hz'ne hc
  have hsvs : s * v * s⁻¹ = z' ^ i * v := by
    calc s * v * s⁻¹ = (s * v * s⁻¹ * v⁻¹) * v := by group
      _ = z' ^ i * v := by rw [← hi]
  have hpi : ¬ p ∣ i := by
    intro hdvd
    obtain ⟨c0, hc0⟩ := hdvd
    have h1 : s * v * s⁻¹ * v⁻¹ = 1 := by
      rw [← hi, hc0, pow_mul, hz'p, one_pow]
    have hc : s * v = v * s := by
      calc s * v = (s * v * s⁻¹ * v⁻¹) * (v * s) := by group
        _ = v * s := by rw [h1, one_mul]
    exact hsE (mem_E_of_commute h hvE hvZ' hsS hc)
  have hcop : Nat.Coprime i p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpi).symm
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hspow : ∀ m : ℕ, s ^ m * v * (s ^ m)⁻¹ = z' ^ (i * m) * v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hszc : s * z' * s⁻¹ = z' := by rw [hsz, mul_inv_cancel_right]
      calc s ^ (m + 1) * v * (s ^ (m + 1))⁻¹
          = s * (s ^ m * v * (s ^ m)⁻¹) * s⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = s * (z' ^ (i * m) * v) * s⁻¹ := by rw [ih]
        _ = (s * z' ^ (i * m) * s⁻¹) * (s * v * s⁻¹) := by group
        _ = z' ^ (i * m) * (z' ^ i * v) := by rw [← conj_pow, hszc, hsvs]
        _ = z' ^ (i * (m + 1)) * v := by
            rw [← mul_assoc, ← pow_add, show i * m + i = i * (m + 1) by ring]
  have hs₁v : s ^ j * v * (s ^ j)⁻¹ = z' * v := by
    rw [hspow j, pow_eq_pow_mod' hz'p (i * j), hj, pow_one]
  have hsj : s ^ j ∈ (S : Subgroup G) := Subgroup.pow_mem _ hsS j
  have hs₁z : s ^ j * z' * (s ^ j)⁻¹ = z' := by
    rw [(mem_Zc.1 hz'Z).2 _ hsj, mul_inv_cancel_right]
  obtain ⟨c, hc⟩ := hp.odd_of_ne_two h.odd
  have hrv' : r * v * r⁻¹ = v := by rw [hrv, mul_inv_cancel_right]
  have hrz : r * z' * r⁻¹ = v * z' := by
    calc r * z' * r⁻¹ = (r * z' * r⁻¹ * z'⁻¹) * z' := by group
      _ = v * z' := by rw [← hv]
  have hrvpow : ∀ k : ℕ, r * v ^ k * r⁻¹ = v ^ k := fun k => by
    rw [← conj_pow, hrv']
  have hrk : ∀ k : ℕ, r ^ k * z' * (r ^ k)⁻¹ = v ^ k * z' := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc r ^ (k + 1) * z' * (r ^ (k + 1))⁻¹
          = r * (r ^ k * z' * (r ^ k)⁻¹) * r⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = r * (v ^ k * z') * r⁻¹ := by rw [ih]
        _ = (r * v ^ k * r⁻¹) * (r * z' * r⁻¹) := by group
        _ = v ^ k * (v * z') := by rw [hrvpow, hrz]
        _ = v ^ (k + 1) * z' := by rw [← mul_assoc, ← pow_succ]
  have hrc : r ^ c * v * (r ^ c)⁻¹ = v := by
    have hcomm : Commute r v := hrv
    rw [(hcomm.pow_left c).eq, mul_inv_cancel_right]
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : G, n₀ = r * s ^ j * r ^ c := ⟨_, rfl⟩
  have hn₀v : n₀ * v * n₀⁻¹ = z' * v ^ 2 := by
    calc n₀ * v * n₀⁻¹ = r * (s ^ j * (r ^ c * v * (r ^ c)⁻¹) * (s ^ j)⁻¹) * r⁻¹ := by
          rw [hn₀]; group
      _ = r * (s ^ j * v * (s ^ j)⁻¹) * r⁻¹ := by rw [hrc]
      _ = r * (z' * v) * r⁻¹ := by rw [hs₁v]
      _ = (r * z' * r⁻¹) * (r * v * r⁻¹) := by group
      _ = z' * v ^ 2 := by rw [hrz, hrv', pow_two, ← mul_assoc, hvcomm]
  have hn₀z : n₀ * z' * n₀⁻¹ = z' ^ (c + 1) := by
    have hcomm1 : Commute z' v := hvcomm.symm
    have hcomm2 : Commute v z' := hvcomm
    have hw : z' ^ c * v = v * z' ^ c := (hcomm1.pow_left c).eq
    have hw' : z' ^ c * v ^ c = v ^ c * z' ^ c := (hcomm1.pow_pow c c).eq
    have hcj : s ^ j * (v ^ c * z') * (s ^ j)⁻¹ = z' ^ c * v ^ c * z' := by
      calc s ^ j * (v ^ c * z') * (s ^ j)⁻¹
          = (s ^ j * v ^ c * (s ^ j)⁻¹) * (s ^ j * z' * (s ^ j)⁻¹) := by group
        _ = (s ^ j * v * (s ^ j)⁻¹) ^ c * z' := by rw [hs₁z, ← conj_pow]
        _ = (z' * v) ^ c * z' := by rw [hs₁v]
        _ = z' ^ c * v ^ c * z' := by rw [hcomm1.mul_pow c]
    have hrz_c : r * z' ^ c * r⁻¹ = (v * z') ^ c := by rw [← hrz, conj_pow]
    have hfin : r * (z' ^ c * v ^ c * z') * r⁻¹ = (v * z') ^ c * v ^ c * (v * z') := by
      calc r * (z' ^ c * v ^ c * z') * r⁻¹
          = (r * z' ^ c * r⁻¹) * (r * v ^ c * r⁻¹) * (r * z' * r⁻¹) := by group
        _ = (v * z') ^ c * v ^ c * (v * z') := by rw [hrz_c, hrvpow, hrz]
    have hvc : v ^ c * v ^ c * v = 1 := by
      have e : c + c + 1 = p := by omega
      rw [← pow_add, ← pow_succ, e]
      exact hvp
    calc n₀ * z' * n₀⁻¹ = r * (s ^ j * (r ^ c * z' * (r ^ c)⁻¹) * (s ^ j)⁻¹) * r⁻¹ := by
          rw [hn₀]; group
      _ = r * (s ^ j * (v ^ c * z') * (s ^ j)⁻¹) * r⁻¹ := by rw [hrk c]
      _ = r * (z' ^ c * v ^ c * z') * r⁻¹ := by rw [hcj]
      _ = (v * z') ^ c * v ^ c * (v * z') := hfin
      _ = v ^ c * z' ^ c * v ^ c * (v * z') := by rw [hcomm2.mul_pow c]
      _ = v ^ c * (z' ^ c * v ^ c) * (v * z') := by group
      _ = v ^ c * (v ^ c * z' ^ c) * (v * z') := by rw [hw']
      _ = v ^ c * v ^ c * (z' ^ c * v) * z' := by group
      _ = v ^ c * v ^ c * (v * z' ^ c) * z' := by rw [hw]
      _ = (v ^ c * v ^ c * v) * (z' ^ c * z') := by group
      _ = z' ^ c * z' := by rw [hvc, one_mul]
      _ = z' ^ (c + 1) := (pow_succ z' c).symm
  have hEK : h.E ≤ Subgroup.zpowers v ⊔ Zc (S : Subgroup G) := by
    obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = Subgroup.zpowers v ⊔ Zc (S : Subgroup G) :=
      ⟨_, rfl⟩
    have hKE : K ≤ h.E := by
      rw [hK]
      exact sup_le (Subgroup.zpowers_le.2 hvE) (Z_le_E h)
    have hZK : Zc (S : Subgroup G) < K := by
      refine lt_of_le_of_ne ?_ ?_
      · rw [hK]; exact le_sup_right
      · intro heq
        apply hvZ
        have hvK : v ∈ K := by
          rw [hK]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers v)
        rw [← heq] at hvK
        exact hvK
    have hlt : Nat.card (Zc (S : Subgroup G)) < Nat.card K := Subgroup.card_lt_of_lt hZK
    have hdvd : Nat.card K ∣ p ^ 2 := by
      rw [← card_E h]
      exact Subgroup.card_dvd_of_le hKE
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hk2 : k = 2 := by
      by_contra hne
      have hle : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      rw [pow_one] at hle
      rw [card_Zc h, hk'] at hlt
      omega
    have hKeq : K = h.E :=
      Subgroup.eq_of_le_of_card_ge hKE (le_of_eq (by rw [card_E h, hk', hk2]))
    rw [hK] at hKeq
    exact le_of_eq hKeq.symm
  have hn₀z_mem : n₀ * z' * n₀⁻¹ ∈ Zc (S : Subgroup G) := by
    rw [hn₀z]; exact Subgroup.pow_mem _ hz'Z (c + 1)
  have hn₀v_mem : n₀ * v * n₀⁻¹ ∈ h.E := by
    rw [hn₀v]; exact h.E.mul_mem hz'E (h.E.pow_mem hvE 2)
  have hnE : ∀ e ∈ h.E, n₀ * e * n₀⁻¹ ∈ h.E := by
    intro e he
    have hK1 : Subgroup.zpowers v ≤ Subgroup.comap (MulAut.conj n₀).toMonoidHom h.E :=
      Subgroup.zpowers_le.2 hn₀v_mem
    have hK2 : Zc (S : Subgroup G) ≤ Subgroup.comap (MulAut.conj n₀).toMonoidHom h.E := by
      rw [hZS]; exact Subgroup.zpowers_le.2 (Z_le_E h hn₀z_mem)
    exact Subgroup.mem_comap.1 (sup_le hK1 hK2 (hEK he))
  have hnZ : ∀ z ∈ Zc (S : Subgroup G), n₀ * z * n₀⁻¹ ∈ Zc (S : Subgroup G) := by
    intro z hz
    have hK : Subgroup.zpowers z' ≤
        Subgroup.comap (MulAut.conj n₀).toMonoidHom (Zc (S : Subgroup G)) :=
      Subgroup.zpowers_le.2 hn₀z_mem
    rw [← hZS] at hK
    exact Subgroup.mem_comap.1 (hK hz)
  obtain ⟨m, hm, hmE⟩ := exists_normalizer_act h hnE hnZ
  have hmv : m * v * m⁻¹ = z' * v ^ 2 := by rw [hmE v hvE, hn₀v]
  have hcomm := conj_mul_inv_mem_Z h hm hvE
  rw [hmv] at hcomm
  have e2 : z' * v ^ 2 * v⁻¹ = z' * v := by group
  rw [e2] at hcomm
  have h4 := (Zc (S : Subgroup G)).mul_mem ((Zc (S : Subgroup G)).inv_mem hz'Z) hcomm
  rw [inv_mul_cancel_left] at h4
  exact hvZ h4

private theorem exists_max_le {C A : Subgroup G} (hA : IsPGroup p A) (hAC : A ≤ C) :
    ∃ B : Subgroup G, A ≤ B ∧ B ≤ C ∧ IsPGroup p B ∧
      ∀ Q : Subgroup G, Q ≤ C → IsPGroup p Q → B ≤ Q → Q = B := by
  have hA' : IsPGroup p (A.subgroupOf C) := hA.comap_subtype
  obtain ⟨P, hP⟩ := hA'.exists_le_sylow
  refine ⟨P.toSubgroup.map C.subtype, ?_, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩
  · intro x hx
    exact ⟨⟨x, hAC hx⟩, hP (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · intro Q hQC hQp hBQ
    have hQ' : IsPGroup p (Q.subgroupOf C) := hQp.comap_subtype
    have hle : P.toSubgroup ≤ Q.subgroupOf C := by
      intro y hy
      exact Subgroup.mem_subgroupOf.2 (hBQ ⟨y, hy, rfl⟩)
    have heq : Q.subgroupOf C = P.toSubgroup := P.is_maximal' hQ' hle
    calc Q = Q ⊓ C := (inf_eq_left.2 hQC).symm
      _ = (Q.subgroupOf C).map C.subtype := (Subgroup.subgroupOf_map_subtype Q C).symm
      _ = P.toSubgroup.map C.subtype := by rw [heq]

private theorem exists_conj_le_of_max {C A B : Subgroup G} (hA : IsPGroup p A) (hAC : A ≤ C)
    (hAm : ∀ Q : Subgroup G, Q ≤ C → IsPGroup p Q → A ≤ Q → Q = A)
    (hB : IsPGroup p B) (hBC : B ≤ C)
    (hBm : ∀ Q : Subgroup G, Q ≤ C → IsPGroup p Q → B ≤ Q → Q = B) :
    ∃ c ∈ C, ∀ x ∈ A, c * x * c⁻¹ ∈ B := by
  have hinj : Function.Injective C.subtype := fun a b hab => Subtype.ext hab
  haveI : Finite (Sylow p C) :=
    Finite.of_injective (fun P : Sylow p C => (P : Set C)) SetLike.coe_injective
  have hmaxA : ∀ {Q : Subgroup C}, IsPGroup p Q → A.subgroupOf C ≤ Q → Q = A.subgroupOf C := by
    intro Q hQ hle
    have hQ0 : Q.map C.subtype ≤ C := Subgroup.map_subtype_le Q
    have hAle : A ≤ Q.map C.subtype := fun x hx =>
      ⟨⟨x, hAC hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have hmapA : (A.subgroupOf C).map C.subtype = A := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAC]
    have hQeq : Q.map C.subtype = A := hAm _ hQ0 (hQ.map _) hAle
    apply Subgroup.map_injective hinj
    rw [hQeq, hmapA]
  have hmaxB : ∀ {Q : Subgroup C}, IsPGroup p Q → B.subgroupOf C ≤ Q → Q = B.subgroupOf C := by
    intro Q hQ hle
    have hQ0 : Q.map C.subtype ≤ C := Subgroup.map_subtype_le Q
    have hBle : B ≤ Q.map C.subtype := fun x hx =>
      ⟨⟨x, hBC hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have hmapB : (B.subgroupOf C).map C.subtype = B := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hBC]
    have hQeq : Q.map C.subtype = B := hBm _ hQ0 (hQ.map _) hBle
    apply Subgroup.map_injective hinj
    rw [hQeq, hmapB]
  let PA : Sylow p C := ⟨A.subgroupOf C, hA.comap_subtype, fun {Q} hQ hle => hmaxA hQ hle⟩
  let PB : Sylow p C := ⟨B.subgroupOf C, hB.comap_subtype, fun {Q} hQ hle => hmaxB hQ hle⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C PA PB
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  have hxC : x ∈ C := hAC hx
  have hmem : (⟨x, hxC⟩ : C) ∈ PA.toSubgroup := Subgroup.mem_subgroupOf.2 hx
  have h2 : MulAut.conj g • (⟨x, hxC⟩ : C) ∈ MulAut.conj g • PA.toSubgroup :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hmem
  have h3 : MulAut.conj g • PA.toSubgroup = PB.toSubgroup := by
    rw [← hg]
    exact Sylow.coe_subgroup_smul.symm
  rw [h3] at h2
  exact Subgroup.mem_subgroupOf.1 h2

theorem conj_mem_Z_of_mem_E {S : Sylow p G} (h : IsM125 p (S : Subgroup G)) {z : G}
    (hz : z ∈ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G)) (hz1 : z ≠ 1) {g : G}
    (hg : g * z * g⁻¹ ∈ h.E) :
    g * z * g⁻¹ ∈ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G) := by
  by_contra hb
  have hzZ : z ∈ Zc (S : Subgroup G) := hz
  have hzc : ∀ t ∈ (S : Subgroup G), t * z = z * t := (mem_Zc.1 hzZ).2
  obtain ⟨b, hbdef⟩ : ∃ b : G, b = g * z * g⁻¹ := ⟨_, rfl⟩
  rw [← hbdef] at hg hb
  have hbE : b ∈ h.E := hg
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup G,
      T = (S : Subgroup G).map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hT : IsM125 p T := by rw [hTdef]; exact map_conj h g
  have hTmem : ∀ x, x ∈ T ↔ ∃ s ∈ (S : Subgroup G), g * s * g⁻¹ = x := by
    intro x
    rw [hTdef, Subgroup.mem_map]
    exact Iff.rfl
  have hTCb : T ≤ centralizer ({b} : Set G) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := (hTmem t).1 ht
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw, hbdef]
    exact conj_comm_aux (hzc s hs).symm
  have hECb : h.E ≤ centralizer ({b} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact E_comm h hbE he
  obtain ⟨P, hEP, hPCb, hPp, hPmax⟩ := exists_max_le (IsPGroup.of_card (card_E h)) hECb
  have hTp : IsPGroup p T := IsPGroup.of_card hT.card
  have hTmax : ∀ Q : Subgroup G, Q ≤ centralizer ({b} : Set G) → IsPGroup p Q → T ≤ Q →
      Q = T := by
    intro Q _ hQ hTQ
    exact (Subgroup.eq_of_le_of_card_ge hTQ
      ((card_le_of_isPGroup h hQ).trans (le_of_eq (by rw [h.card, hT.card])))).symm
  obtain ⟨c, hcCb, hcP⟩ := exists_conj_le_of_max hPp hPCb hPmax hTp hTCb hTmax
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup G,
      R = (S : Subgroup G).map (MulAut.conj (c⁻¹ * g)).toMonoidHom := ⟨_, rfl⟩
  have hR : IsM125 p R := by rw [hRdef]; exact map_conj h (c⁻¹ * g)
  have hRmem : ∀ x, x ∈ R ↔ ∃ s ∈ (S : Subgroup G), c⁻¹ * g * s * (c⁻¹ * g)⁻¹ = x := by
    intro x
    rw [hRdef, Subgroup.mem_map]
    exact Iff.rfl
  have hERle : h.E ≤ R := by
    intro x hx
    obtain ⟨s, hs, hgs⟩ := (hTmem _).1 (hcP x (hEP hx))
    refine (hRmem x).2 ⟨s, hs, ?_⟩
    calc c⁻¹ * g * s * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * s * g⁻¹) * c := by group
      _ = c⁻¹ * (c * x * c⁻¹) * c := by rw [hgs]
      _ = x := by group
  have hEexp : ∀ a ∈ h.E, a ^ p = 1 := fun a ha => ((mem_E h).1 ha).2
  have hER : hR.E = h.E := (eq_E hR hERle hEexp (card_E h)).symm
  have hbc : b * c = c * b := Subgroup.mem_centralizer_iff.1 hcCb b (Set.mem_singleton b)
  have hcinv : b * c⁻¹ = c⁻¹ * b := (show Commute b c from hbc).inv_right.eq
  have hbR : b ∈ Zc R := by
    refine mem_Zc.2 ⟨hERle hbE, fun t ht => ?_⟩
    obtain ⟨s, hs, rfl⟩ := (hRmem t).1 ht
    have hub : (g * s * g⁻¹) * b = b * (g * s * g⁻¹) := by
      rw [hbdef]; exact (conj_comm_aux (hzc s hs).symm).symm
    calc c⁻¹ * g * s * (c⁻¹ * g)⁻¹ * b = c⁻¹ * (g * s * g⁻¹) * (c * b) := by group
      _ = c⁻¹ * (g * s * g⁻¹) * (b * c) := by rw [hbc]
      _ = c⁻¹ * ((g * s * g⁻¹) * b) * c := by group
      _ = c⁻¹ * (b * (g * s * g⁻¹)) * c := by rw [hub]
      _ = (c⁻¹ * b) * (g * s * g⁻¹) * c := by group
      _ = (b * c⁻¹) * (g * s * g⁻¹) * c := by rw [hcinv]
      _ = b * (c⁻¹ * g * s * (c⁻¹ * g)⁻¹) := by group
  exact core_false h hR hER hbE hb hbR

theorem conj_mul_inv_mem_Z_of_mem_E {S : Sylow p G} (h : IsM125 p (S : Subgroup G)) {x : G}
    (hx : x ∈ h.E) (hxZ : x ∉ centralizer ((S : Subgroup G) : Set G)) {g : G}
    (hg : g * x * g⁻¹ ∈ (S : Subgroup G)) :
    g * x * g⁻¹ * x⁻¹ ∈ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G) := by
  have hxS : x ∈ (S : Subgroup G) := E_le h hx
  have hxZ' : x ∉ Zc (S : Subgroup G) := fun hc =>
    hxZ (Subgroup.mem_centralizer_iff.2 (mem_Zc.1 hc).2)
  obtain ⟨y, hydef⟩ : ∃ y : G, y = g * x * g⁻¹ := ⟨_, rfl⟩
  rw [← hydef] at hg ⊢
  have hyS : y ∈ (S : Subgroup G) := hg
  have hyp : y ^ p = 1 := by
    rw [hydef, conj_pow, ((mem_E h).1 hx).2, mul_one, mul_inv_cancel]
  have hyE : y ∈ h.E := (mem_E h).2 ⟨hyS, hyp⟩
  have hy1 : y ≠ 1 := by
    intro h1
    apply hxZ'
    have hx1 : x = 1 := by
      have h2 : g * x * g⁻¹ = 1 := hydef.symm.trans h1
      calc x = g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ := by group
        _ = 1 := by rw [h2]; group
    rw [hx1]
    exact (Zc (S : Subgroup G)).one_mem
  have hyZ : y ∉ Zc (S : Subgroup G) := by
    intro hyZ
    have e : g⁻¹ * y * g⁻¹⁻¹ = x := by rw [hydef]; group
    have hcon := conj_mem_Z_of_mem_E h hyZ hy1 (g := g⁻¹) (by rw [e]; exact hx)
    rw [e] at hcon
    exact hxZ' hcon
  obtain ⟨Cy, hCy⟩ : ∃ C : Subgroup G, C = centralizer ({y} : Set G) := ⟨_, rfl⟩
  have hECy : h.E ≤ Cy := by
    rw [hCy]
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact E_comm h hyE he
  have hEmax : ∀ Q : Subgroup G, Q ≤ Cy → IsPGroup p Q → h.E ≤ Q → Q = h.E := by
    intro Q hQC hQp hEQ
    by_contra hne
    have hlt : h.E < Q := lt_of_le_of_ne hEQ (Ne.symm hne)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQp
    have hcardlt : Nat.card h.E < Nat.card Q := Subgroup.card_lt_of_lt hlt
    have hle3 : Nat.card Q ≤ p ^ 3 := (card_le_of_isPGroup h hQp).trans (le_of_eq h.card)
    rw [card_E h, hn] at hcardlt
    rw [hn] at hle3
    have hn3 : n = 3 := by
      rcases lt_trichotomy n 3 with hlt3 | heq3 | hgt3
      · have h1 : p ^ n ≤ p ^ 2 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
        omega
      · exact heq3
      · have h1 : p ^ 4 ≤ p ^ n := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
        have h2 : p ^ 3 < p ^ 4 :=
          Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
        omega
    have hQcard : Nat.card Q = p ^ 3 := by rw [hn, hn3]
    have hQmax : ∀ Q' : Subgroup G, Q' ≤ ⊤ → IsPGroup p Q' → Q ≤ Q' → Q' = Q := by
      intro Q' _ hQ' hQQ'
      exact (Subgroup.eq_of_le_of_card_ge hQQ'
        ((card_le_of_isPGroup h hQ').trans (le_of_eq (by rw [h.card, hQcard])))).symm
    have hSmax : ∀ Q' : Subgroup G, Q' ≤ ⊤ → IsPGroup p Q' → (S : Subgroup G) ≤ Q' →
        Q' = S := fun _ _ hQ' hSQ' => S.is_maximal' hQ' hSQ'
    obtain ⟨k, -, hk⟩ :=
      exists_conj_le_of_max (C := ⊤) S.isPGroup' le_top hSmax hQp le_top hQmax
    have hSk : (S : Subgroup G).map (MulAut.conj k).toMonoidHom ≤ Q := by
      intro x' hx'
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx'
      exact hk s hs
    have hQeq : (S : Subgroup G).map (MulAut.conj k).toMonoidHom = Q :=
      Subgroup.eq_of_le_of_card_ge hSk (le_of_eq (by rw [(map_conj h k).card, hQcard]))
    have hyQ : y ∈ Q := hEQ hyE
    rw [← hQeq] at hyQ
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.1 hyQ
    have hsy' : k * s * k⁻¹ = y := hsy
    have hscomm : ∀ t ∈ (S : Subgroup G), t * s = s * t := by
      intro t ht
      have htQ : k * t * k⁻¹ ∈ Q := by
        rw [← hQeq]; exact Subgroup.mem_map.2 ⟨t, ht, rfl⟩
      have hcomm : y * (k * t * k⁻¹) = (k * t * k⁻¹) * y := by
        have hc := hQC htQ
        rw [hCy] at hc
        exact Subgroup.mem_centralizer_iff.1 hc y (Set.mem_singleton y)
      rw [← hsy'] at hcomm
      have e1 : k * (s * t) * k⁻¹ = k * (t * s) * k⁻¹ := by
        calc k * (s * t) * k⁻¹ = k * s * k⁻¹ * (k * t * k⁻¹) := by group
          _ = (k * t * k⁻¹) * (k * s * k⁻¹) := hcomm
          _ = k * (t * s) * k⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel e1)).symm
    have hsZ : s ∈ Zc (S : Subgroup G) := mem_Zc.2 ⟨hs, hscomm⟩
    have hs1 : s ≠ 1 := by
      rintro rfl
      apply hy1
      rw [← hsy']
      group
    have hkk := conj_mem_Z_of_mem_E h hsZ hs1 (g := k) (by rw [hsy']; exact hyE)
    rw [hsy'] at hkk
    exact hyZ hkk
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup G, E' = h.E.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hE'Cy : E' ≤ Cy := by
    intro w hw
    rw [hE'] at hw
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hw
    rw [hCy, Subgroup.mem_centralizer_iff]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    rw [hq, hydef]
    exact conj_comm_aux (E_comm h hx he)
  have hEp : IsPGroup p h.E := IsPGroup.of_card (card_E h)
  have hE'p : IsPGroup p E' := by
    rw [hE']; exact hEp.map _
  obtain ⟨P', hE'P', hP'Cy, hP'p, hP'max⟩ := exists_max_le hE'p hE'Cy
  obtain ⟨c, hcCy, hcP'⟩ := exists_conj_le_of_max hP'p hP'Cy hP'max hEp hECy hEmax
  have hcy : y * c = c * y := by
    rw [hCy] at hcCy
    exact Subgroup.mem_centralizer_iff.1 hcCy y (Set.mem_singleton y)
  have hnE : ∀ e ∈ h.E, c * g * e * (c * g)⁻¹ ∈ h.E := by
    intro e he
    have h1 : g * e * g⁻¹ ∈ P' := hE'P' (by rw [hE']; exact ⟨e, he, rfl⟩)
    have h2 := hcP' _ h1
    have e2 : c * g * e * (c * g)⁻¹ = c * (g * e * g⁻¹) * c⁻¹ := by group
    rw [e2]
    exact h2
  have hnZ : ∀ z ∈ Zc (S : Subgroup G), c * g * z * (c * g)⁻¹ ∈ Zc (S : Subgroup G) := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      have e3 : c * g * 1 * (c * g)⁻¹ = 1 := by group
      rw [e3]
      exact (Zc (S : Subgroup G)).one_mem
    · exact conj_mem_Z_of_mem_E h hz hz1 (hnE z (Z_le_E h hz))
  obtain ⟨m, hm, hmE⟩ := exists_normalizer_act h hnE hnZ
  have hmx : m * x * m⁻¹ = y := by
    rw [hmE x hx]
    calc c * g * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ := by group
      _ = c * y * c⁻¹ := by rw [← hydef]
      _ = y := by rw [← hcy]; group
  have hres := conj_mul_inv_mem_Z h hm hx
  rw [hmx] at hres
  exact hres

end IsM125

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125
