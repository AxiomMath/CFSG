module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreLift
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Fixed

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_fixed_of_odd {P : Subgroup Y} (hP : IsPGroup 2 P) {S : Set Y}
    (hS : ∀ p ∈ P, ∀ s ∈ S, p * s * p⁻¹ ∈ S) (hodd : Odd (Nat.card S)) :
    ∃ s ∈ S, P ≤ Subgroup.centralizer ({s} : Set Y) := by
  let _ : MulAction P S :=
    { smul := fun p s => ⟨(p : Y) * s * (p : Y)⁻¹, hS p p.2 s s.2⟩
      one_smul := fun s => Subtype.ext
        (show ((1 : P) : Y) * (s : Y) * ((1 : P) : Y)⁻¹ = s by simp)
      mul_smul := fun a b s => Subtype.ext
        (show ((a * b : P) : Y) * (s : Y) * ((a * b : P) : Y)⁻¹ =
          (a : Y) * ((b : Y) * (s : Y) * (b : Y)⁻¹) * (a : Y)⁻¹ by simp [mul_assoc]) }
  have hnd : ¬ 2 ∣ Nat.card S := fun h2 =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hP' : IsPGroup 2 ↥P := hP
  obtain ⟨s, hs⟩ := hP'.nonempty_fixed_point_of_prime_not_dvd_card S hnd
  refine ⟨s, s.2, fun p hp => ?_⟩
  have h1 : (p : Y) * s * p⁻¹ = s := congrArg Subtype.val (hs ⟨p, hp⟩)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc p * (s : Y) = (p * s * p⁻¹) * p := by group
    _ = s * p := by rw [h1]

theorem exists_conj_normalizer_of_perm' {N : Subgroup Y} (hN : Odd (Nat.card N))
    (T : Subgroup Y) {V : Subgroup Y} (hV : IsPGroup 2 V)
    (hVN : V ≤ Subgroup.normalizer (N : Set Y))
    (hperm : ∀ v ∈ V, ∃ n ∈ N, conjSub v T = conjSub n T) :
    ∃ n ∈ N, V ≤ Subgroup.normalizer ((conjSub n T : Subgroup Y) : Set Y) := by
  set X : Set (Subgroup Y) := {M | ∃ n ∈ N, M = conjSub n T} with hX
  have hclosed : ∀ v ∈ V, ∀ M ∈ X, conjSub v M ∈ X := by
    rintro v hv _ ⟨n, hn, rfl⟩
    obtain ⟨n', hn', hvT⟩ := hperm v hv
    have hvn : v * n * v⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hVN hv) n).mp hn
    refine ⟨(v * n * v⁻¹) * n', N.mul_mem hvn hn', ?_⟩
    calc conjSub v (conjSub n T) = conjSub (v * n) T := (conjSub_mul v n T).symm
      _ = conjSub ((v * n * v⁻¹) * v) T := by congr 1; group
      _ = conjSub (v * n * v⁻¹) (conjSub v T) := conjSub_mul _ _ _
      _ = conjSub (v * n * v⁻¹) (conjSub n' T) := by rw [hvT]
      _ = conjSub ((v * n * v⁻¹) * n') T := (conjSub_mul _ _ _).symm
  let _ : MulAction V X :=
    { smul := fun v M => ⟨conjSub (v : Y) M.1, hclosed v v.2 M.1 M.2⟩
      one_smul := fun M => Subtype.ext (conjSub_one M.1)
      mul_smul := fun a b M => Subtype.ext (conjSub_mul (a : Y) (b : Y) M.1) }
  have hodd : ¬ 2 ∣ Nat.card X := by
    have h := odd_natCard_conjSubClass hN T
    exact fun h2 => (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)
  have hVp : IsPGroup 2 ↥V := hV
  obtain ⟨M₀, hM₀⟩ := hVp.nonempty_fixed_point_of_prime_not_dvd_card X hodd
  obtain ⟨n, hn, hMn⟩ := M₀.2
  refine ⟨n, hn, fun v hv => ?_⟩
  have hfix : conjSub (v : Y) M₀.1 = M₀.1 := congrArg Subtype.val (hM₀ ⟨v, hv⟩)
  rw [hMn] at hfix
  exact mem_normalizer_iff_conjSub_eq.mpr hfix

end Fixed

section Involutions

variable {Y : Type} [Group Y] [Finite Y]

theorem involution_coset_conj {X : Subgroup Y} (hX : Odd (Nat.card X)) {s t : Y}
    (hs : s * s = 1) (ht : t * t = 1) (h : s⁻¹ * t ∈ X) : ∃ x ∈ X, x * s * x⁻¹ = t := by
  have h' : t⁻¹ * s ∈ X := by
    have := X.inv_mem h
    rwa [mul_inv_rev, inv_inv] at this
  exact OddQuot.exists_conj_of_involutions hX hs ht h'

theorem involution_ne_mod_odd {X : Subgroup Y} (hX : Odd (Nat.card X)) {s t : Y}
    (hs : s * s = 1) (ht : t * t = 1) (hst : s * t = t * s) (hne : s ≠ t) : s⁻¹ * t ∉ X := by
  intro h
  refine hne (OddQuot.eq_of_commute_of_mem hX ⟨1, ?_⟩ ⟨1, ?_⟩ hst h)
  · rw [pow_one, pow_two, hs]
  · rw [pow_one, pow_two, ht]

theorem involution_map_ne {X : Subgroup Y} [X.Normal] (hX : Odd (Nat.card X)) {s t : Y}
    (hs : s * s = 1) (ht : t * t = 1) (hst : s * t = t * s) (hne : s ≠ t) :
    QuotientGroup.mk' X s ≠ QuotientGroup.mk' X t := fun h =>
  involution_ne_mod_odd hX hs ht hst hne (OddQuot.inv_mul_mem_of_mk_eq h)

theorem conj_eq_of_mem_normalizer_zpowers {t g : Y} (ht : t * t = 1)
    (hg : g ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup Y) : Set Y)) :
    g * t * g⁻¹ = t := by
  by_cases ht1 : t = 1
  · rw [ht1]
    group
  have hmem : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have ht2 : t ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, ht]
  rw [zpow_eq_zpow_emod k ht2] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hk
    exfalso
    apply ht1
    have : g * t * g⁻¹ * g = 1 * g := by rw [← hk]
    have h2 : g * t = g := by simpa [mul_assoc] using this
    simpa using h2
  · rw [h1, zpow_one] at hk
    exact hk.symm

theorem exists_centralizes_involution_coset {X P : Subgroup Y} (hX : Odd (Nat.card X))
    (hP : IsPGroup 2 P) (hPX : P ≤ Subgroup.normalizer (X : Set Y)) {s : Y} (hs : s * s = 1)
    (hPs : ∀ p ∈ P, s⁻¹ * (p * s * p⁻¹) ∈ X) :
    ∃ x ∈ X, P ≤ Subgroup.centralizer ({x * s * x⁻¹} : Set Y) := by
  have hzp : ∀ g : Y, conjSub g (Subgroup.zpowers s) = Subgroup.zpowers (g * s * g⁻¹) := by
    intro g
    unfold conjSub
    rw [MonoidHom.map_zpowers]
    rfl
  have hperm : ∀ p ∈ P, ∃ n ∈ X,
      conjSub p (Subgroup.zpowers s) = conjSub n (Subgroup.zpowers s) := by
    intro p hp
    have hps : (p * s * p⁻¹) * (p * s * p⁻¹) = 1 := by
      calc (p * s * p⁻¹) * (p * s * p⁻¹) = p * (s * s) * p⁻¹ := by group
        _ = 1 := by rw [hs]; group
    obtain ⟨w, hw, hws⟩ := involution_coset_conj hX hs hps (hPs p hp)
    exact ⟨w, hw, by rw [hzp, hzp, hws]⟩
  obtain ⟨n, hn, hPn⟩ := exists_conj_normalizer_of_perm' hX (Subgroup.zpowers s) hP hPX hperm
  refine ⟨n, hn, fun p hp => ?_⟩
  have hp' := hPn hp
  rw [hzp] at hp'
  have hns : (n * s * n⁻¹) * (n * s * n⁻¹) = 1 := by
    calc (n * s * n⁻¹) * (n * s * n⁻¹) = n * (s * s) * n⁻¹ := by group
      _ = 1 := by rw [hs]; group
  have h1 := conj_eq_of_mem_normalizer_zpowers hns hp'
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc p * (n * s * n⁻¹) = (p * (n * s * n⁻¹) * p⁻¹) * p := by group
    _ = (n * s * n⁻¹) * p := by rw [h1]

theorem exists_fixed_mem_coset {H U : Subgroup Y} (hH : Odd (Nat.card H)) (hU : IsPGroup 2 U)
    (hUH : U ≤ Subgroup.normalizer (H : Set Y)) {m : Y}
    (hUm : ∀ u ∈ U, m⁻¹ * (u * m * u⁻¹) ∈ H) :
    ∃ h ∈ H, U ≤ Subgroup.centralizer ({m * h} : Set Y) := by
  set S : Set Y := {c | m⁻¹ * c ∈ H} with hS
  have hSU : ∀ u ∈ U, ∀ c ∈ S, u * c * u⁻¹ ∈ S := by
    intro u hu c hc
    have h1 : u * (m⁻¹ * c) * u⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hUH hu) _).mp hc
    have e : m⁻¹ * (u * c * u⁻¹) = (m⁻¹ * (u * m * u⁻¹)) * (u * (m⁻¹ * c) * u⁻¹) := by group
    show m⁻¹ * (u * c * u⁻¹) ∈ H
    rw [e]
    exact H.mul_mem (hUm u hu) h1
  have hcard : Nat.card S = Nat.card H := by
    refine (Nat.card_congr ?_).symm
    exact
      { toFun := fun h => ⟨m * h, show m⁻¹ * (m * h) ∈ H by simpa using h.2⟩
        invFun := fun c => ⟨m⁻¹ * c, c.2⟩
        left_inv := fun h => Subtype.ext (by simp)
        right_inv := fun c => Subtype.ext (by simp) }
  obtain ⟨c, hc, hUc⟩ := exists_fixed_of_odd hU hSU (hcard ▸ hH)
  exact ⟨m⁻¹ * c, hc, by simpa using hUc⟩

end Involutions

section Fibres

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {X : Subgroup Y} [X.Normal]

theorem eq_of_map_eq_of_inv_eq (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {K K' : Subgroup Y}
    (hK : K ∈ Φ) (hK' : K' ∈ Φ) {z : Y} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z)
    (h : K.map (QuotientGroup.mk' X) = K'.map (QuotientGroup.mk' X)) : K = K' := by
  by_contra hne
  set mk := QuotientGroup.mk' X with hmk
  obtain ⟨T, hT, hTsyl, -⟩ :=
    exists_mem_RSet_ge hK' (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup Y)) bot_le
  have hT8 := Sec6Gen.eight_le_of_mem_RSet hΦ hT
  have hTX : T ⊓ X = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd X hTsyl.2.1 hTsyl.1 (odd_natCard_inf hX K')
  have hsub : ∀ y ∈ T.map mk, y = 1 ∨ y = mk z := by
    rintro _ ⟨x, hxT, rfl⟩
    have hxK' : x ∈ K' := hTsyl.1 hxT
    have hxbar : mk x ∈ K.map mk := by
      rw [h]
      exact Subgroup.mem_map_of_mem _ hxK'
    have hx2 : IsPGroup 2 (Subgroup.zpowers (mk x)) :=
      (hTsyl.2.1.map mk).to_le (Subgroup.zpowers_le.mpr ⟨x, hxT, rfl⟩)
    obtain ⟨k, hk, hkx, hk2⟩ := exists_isPGroup_lift_of_mem_map hxbar hx2
    rcases Q3T6.eq_one_or_eq_of_map_eq_of_twin_gen hΦ hX hK hK' hne hz hz' hxK' hk hk2
      hkx.symm with h1 | h1
    · left
      rw [← hkx, h1, map_one]
    · right
      rw [← hkx, h1]
  have hcard2 : Nat.card ↥(T.map mk) ≤ 2 := natCard_subgroup_le_two_of_subset hsub
  have hcardT : Nat.card ↥(T.map mk) = Nat.card T :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv hTX).toEquiv).symm
  omega

theorem exists_conj_of_map_eq (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {K L : Subgroup Y}
    (hK : K ∈ Φ) (hL : L ∈ Φ)
    (h : K.map (QuotientGroup.mk' X) = L.map (QuotientGroup.mk' X)) :
    ∃ n ∈ X, L = conjSub n K :=
  Q3T6.exists_conj_of_map_eq_gen hΦ hX hK hL h

theorem inf_normalizer_eq_inf_centralizer (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X))
    {K : Subgroup Y} (hK : K ∈ Φ) {z : Y} (hz : IsUniqueInvolution K z) :
    X ⊓ Subgroup.normalizer (K : Set Y) = X ⊓ Subgroup.centralizer ({z} : Set Y) := by
  ext x
  simp only [Subgroup.mem_inf]
  refine and_congr_right fun hx => ⟨fun hxN => ?_, fun hxC => ?_⟩
  · have h1 := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hxN)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [h1]
  · have hxz : x * z * x⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hxC
      rw [this]
      group
    have hz' : IsUniqueInvolution (conjSub x K) z := by
      have := hz.conj x
      rwa [hxz] at this
    have heq := eq_of_map_eq_of_inv_eq hΦ hX (hΦ.conjInvariant x K hK) hK hz' hz
      (OddQuot.map_conjSub_of_mem hx K)
    exact mem_normalizer_iff_conjSub_eq.mpr heq

theorem le_normalizer_of_le_centralizer (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X))
    {K : Subgroup Y} (hK : K ∈ Φ) {z : Y} (hz : IsUniqueInvolution K z) :
    X ⊓ Subgroup.centralizer ({z} : Set Y) ≤ Subgroup.normalizer (K : Set Y) := by
  rw [← inf_normalizer_eq_inf_centralizer hΦ hX hK hz]
  exact inf_le_right

end Fibres

section Elements

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_of_isPGroup_of_mem_sup {A D : Subgroup Y} (hD : Odd (Nat.card D))
    (hDA : D ≤ Subgroup.normalizer (A : Set Y)) {w : Y} (hw : w ∈ A ⊔ D)
    (hw2 : IsPGroup 2 (Subgroup.zpowers w)) : w ∈ A := by
  set H : Subgroup Y := A ⊔ D with hH
  have hHN : H ≤ Subgroup.normalizer (A : Set Y) := sup_le Subgroup.le_normalizer hDA
  haveI : (A.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHN
  set ψ : ↥D →* ↥H ⧸ A.subgroupOf H :=
    (QuotientGroup.mk' (A.subgroupOf H)).comp (Subgroup.inclusion le_sup_right) with hψ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha, d, hd, rfl⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hDA hx
    refine ⟨⟨d, hd⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    show ((Subgroup.inclusion le_sup_right ⟨d, hd⟩ : ↥H)⁻¹ * ⟨a * d, hx⟩ : ↥H) ∈ A.subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    have e : (((Subgroup.inclusion le_sup_right ⟨d, hd⟩ : ↥H)⁻¹ * ⟨a * d, hx⟩ : ↥H) : Y) =
        d⁻¹ * a * d := by
      simp [mul_assoc]
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (hDA hd)) a).mp ha
    simpa using this
  have hQodd : Odd (Nat.card (↥H ⧸ A.subgroupOf H)) :=
    hD.of_dvd_nat (Subgroup.card_dvd_of_surjective hψs)
  obtain ⟨k, hk⟩ := hw2.exists_card_eq
  rw [Nat.card_zpowers] at hk
  set wq : ↥H ⧸ A.subgroupOf H := QuotientGroup.mk' (A.subgroupOf H) ⟨w, hw⟩ with hwq
  have h1 : orderOf wq ∣ 2 ^ k := by
    rw [← hk, ← Subgroup.orderOf_mk w hw]
    exact orderOf_map_dvd _ _
  have h2 : orderOf wq ∣ Nat.card (↥H ⧸ A.subgroupOf H) := orderOf_dvd_natCard wq
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (↥H ⧸ A.subgroupOf H)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hQodd)
  have h3 : orderOf wq = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : wq = 1 := orderOf_eq_one_iff.mp h3
  rw [hwq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h4
  exact h4

theorem mem_of_forall_pow {S : Subgroup Y} (g : Y)
    (h2 : ∀ k : ℕ, IsPGroup 2 (Subgroup.zpowers (g ^ k)) → g ^ k ∈ S)
    (hodd : ∀ k : ℕ, Odd (orderOf (g ^ k)) → g ^ k ∈ S) : g ∈ S := by
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hx : (g ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
  have hy : (g ^ 2 ^ a) ^ m = 1 := by
    rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hxS : g ^ m ∈ S := h2 m (OddQuot.isPGroup_zpowers_of_pow hx)
  have hyS : g ^ 2 ^ a ∈ S := hodd (2 ^ a) (hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hy))
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have e : g = (g ^ 2 ^ a) ^ u * (g ^ m) ^ v := by
    calc g = g ^ (1 : ℤ) := (zpow_one g).symm
      _ = g ^ (u * ((2 ^ a : ℕ) : ℤ) + v * (m : ℤ)) := by rw [huv]
      _ = (g ^ 2 ^ a) ^ u * (g ^ m) ^ v := by
          rw [zpow_add, mul_comm u, mul_comm v, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [e]
  exact S.mul_mem (S.zpow_mem hyS u) (S.zpow_mem hxS v)

end Elements

section Pair

variable {Y : Type} [Group Y]

theorem eq_one_or_eq_of_mem_zpowers {t x : Y} (ht : t * t = 1) (hx : x ∈ Subgroup.zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ht2 : t ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, ht]
  rw [zpow_eq_zpow_emod k ht2]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero]
  · right
    rw [h1, zpow_one]

theorem mem_closure_pair_iff {z j : Y} (hz : z * z = 1) (hj : j * j = 1) (hzj : z * j = j * z)
    {x : Y} : x ∈ Subgroup.closure ({z, j} : Set Y) ↔ x = 1 ∨ x = z ∨ x = j ∨ x = z * j := by
  constructor
  · intro hx
    have hcl : Subgroup.closure ({z, j} : Set Y) = Subgroup.zpowers z ⊔ Subgroup.zpowers j := by
      rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
        Subgroup.zpowers_eq_closure]
    rw [hcl] at hx
    have hN : Subgroup.zpowers z ≤
        Subgroup.normalizer ((Subgroup.zpowers j : Subgroup Y) : Set Y) := by
      refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute j z from hzj.symm) k).eq
    obtain ⟨a, ha, b, hb, rfl⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hN
      (by rwa [sup_comm] at hx)
    rcases eq_one_or_eq_of_mem_zpowers hj ha with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers hz hb with rfl | rfl
    · left
      rw [one_mul]
    · right; left
      rw [one_mul]
    · right; right; left
      rw [mul_one]
    · right; right; right
      exact hzj.symm
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem mul_self_eq_one_of_mem_closure_pair {z j : Y} (hz : z * z = 1) (hj : j * j = 1)
    (hzj : z * j = j * z) {x : Y} (hx : x ∈ Subgroup.closure ({z, j} : Set Y)) : x * x = 1 := by
  rcases (mem_closure_pair_iff hz hj hzj).mp hx with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact hz
  · exact hj
  · calc z * j * (z * j) = z * (j * z) * j := by group
      _ = z * (z * j) * j := by rw [hzj]
      _ = (z * z) * (j * j) := by group
      _ = 1 := by rw [hz, hj, one_mul]

theorem isPGroup_closure_pair {z j : Y} (hz : z * z = 1) (hj : j * j = 1) (hzj : z * j = j * z) :
    IsPGroup 2 (Subgroup.closure ({z, j} : Set Y)) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp only [pow_one, pow_two, Subgroup.coe_mul, OneMemClass.coe_one]
  exact mul_self_eq_one_of_mem_closure_pair hz hj hzj x.2

theorem eq_of_odd_swap [Finite Y] {g x y : Y} (hg : Odd (orderOf g)) (hxy : g * x * g⁻¹ = y)
    (hyx : g * y * g⁻¹ = x) : x = y := by
  have h2x : (g * g) * x * (g * g)⁻¹ = x := by
    calc (g * g) * x * (g * g)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by group
      _ = x := by rw [hxy, hyx]
  have h2 : ∀ i : ℕ, (g * g) ^ i * x * ((g * g) ^ i)⁻¹ = x := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc (g * g) ^ (i + 1) * x * ((g * g) ^ (i + 1))⁻¹
          = (g * g) ^ i * ((g * g) * x * (g * g)⁻¹) * ((g * g) ^ i)⁻¹ := by
            rw [pow_succ (g * g) i]
            group
        _ = x := by rw [h2x, ih]
  obtain ⟨i, hi⟩ := hg
  have h1 : (g * g) ^ i * g = 1 := by
    rw [← pow_two, ← pow_mul, ← pow_succ, ← hi]
    exact pow_orderOf_eq_one g
  have hgi : (g * g) ^ i = g⁻¹ := eq_inv_of_mul_eq_one_left h1
  calc x = (g * g) ^ i * x * ((g * g) ^ i)⁻¹ := (h2 i).symm
    _ = g⁻¹ * x * g := by rw [hgi, inv_inv]
    _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hyx]
    _ = y := by group

theorem conj_eq_of_odd_of_fix [Finite Y] {z j g : Y} (hz : z * z = 1) (hj : j * j = 1)
    (hzj : z * j = j * z) (hz1 : z ≠ 1) (hne : z ≠ j)
    (hgZ : g ∈ Subgroup.normalizer ((Subgroup.closure ({z, j} : Set Y) : Subgroup Y) : Set Y))
    (hgz : g * z * g⁻¹ = z) (hg : Odd (orderOf g)) : g * j * g⁻¹ = j := by
  have hjZ : j ∈ Subgroup.closure ({z, j} : Set Y) := Subgroup.subset_closure (by simp)
  have hmem : g * j * g⁻¹ ∈ Subgroup.closure ({z, j} : Set Y) :=
    (Subgroup.mem_normalizer_iff.mp hgZ j).mp hjZ
  rcases (mem_closure_pair_iff hz hj hzj).mp hmem with h | h | h | h
  · have hj1 : j = 1 := by
      have := congrArg (fun t => g⁻¹ * t * g) h
      simpa [mul_assoc] using this
    rw [h, hj1]
  · exfalso
    apply hne
    have h1 := congrArg (fun t => g⁻¹ * t * g) h
    have h2 := congrArg (fun t => g⁻¹ * t * g) hgz
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h1 h2
    rw [h1]
    exact h2
  · exact h
  · exfalso
    have hzj' : g * (z * j) * g⁻¹ = j := by
      calc g * (z * j) * g⁻¹ = (g * z * g⁻¹) * (g * j * g⁻¹) := by group
        _ = z * (z * j) := by rw [hgz, h]
        _ = j := by rw [← mul_assoc, hz, one_mul]
    have := eq_of_odd_swap hg h hzj'
    apply hz1
    calc z = z * j * j := by rw [mul_assoc, hj, mul_one]
      _ = j * j := by rw [← this]
      _ = 1 := hj

theorem mem_centralizer_closure_pair {z j g : Y} (hgz : g * z * g⁻¹ = z) (hgj : g * j * g⁻¹ = j) :
    g ∈ Subgroup.centralizer ((Subgroup.closure ({z, j} : Set Y) : Subgroup Y) : Set Y) := by
  have key : ∀ w : Y, g * w * g⁻¹ = w → w * g = g * w := fun w hw => by
    calc w * g = (g * w * g⁻¹) * g := by rw [hw]
      _ = g * w := by group
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro w (rfl | rfl)
  · exact key _ hgz
  · exact key _ hgj

theorem eq_of_odd_swap_conjSub [Finite Y] {g : Y} {A B : Subgroup Y} (hg : Odd (orderOf g))
    (hAB : conjSub g A = B) (hBA : conjSub g B = A) : A = B := by
  have h2A : conjSub (g ^ 2) A = A := by rw [pow_two, conjSub_mul, hAB, hBA]
  have h2 : ∀ i : ℕ, conjSub ((g ^ 2) ^ i) A = A := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ (g ^ 2) i, conjSub_mul, h2A, ih]
  obtain ⟨i, hi⟩ := hg
  have h1 : (g ^ 2) ^ i * g = 1 := by
    rw [← pow_mul, ← pow_succ, ← hi]
    exact pow_orderOf_eq_one g
  have hgi : (g ^ 2) ^ i = g⁻¹ := eq_inv_of_mul_eq_one_left h1
  calc A = conjSub ((g ^ 2) ^ i) A := (h2 i).symm
    _ = conjSub g⁻¹ A := by rw [hgi]
    _ = conjSub g⁻¹ (conjSub g B) := by rw [hBA]
    _ = B := conjSub_inv_conjSub g B

end Pair

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot
