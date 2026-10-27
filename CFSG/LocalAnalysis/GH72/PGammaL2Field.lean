module

public import CFSG.LocalAnalysis.GH72.PGammaL2Local

public section

namespace CFSG.GH72

open Subgroup Finset
open scoped MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.GorensteinWalter (PSL2 PGL2 PGammaL2 IsOddPrimePower pGammaL2PSLRange)

section Arithmetic

theorem pow_eq_self_of_odd {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : Odd p) : ε ^ p = ε := by
  rcases hε with rfl | rfl
  · exact one_pow p
  · exact hp.neg_one_pow

theorem geom_sum_mul_sub_eq {x ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : Odd p) :
    (∑ i ∈ range p, x ^ i * ε ^ (p - 1 - i)) * (x - ε) = x ^ p - ε := by
  rw [geom_sum₂_mul, pow_eq_self_of_odd hε hp]

theorem odd_geom_sum {x ε : ℤ} (hx : Odd x) (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : Odd p) :
    Odd (∑ i ∈ range p, x ^ i * ε ^ (p - 1 - i)) := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hx2 : (x : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hx
  have hε2 : (ε : ZMod 2) = 1 := by
    rcases hε with rfl | rfl
    · simp
    · decide
  push_cast
  simp only [hx2, hε2, one_pow, mul_one, sum_const, card_range, nsmul_eq_mul]
  exact (ZMod.natCast_eq_one_iff_odd).mpr hp

theorem one_lt_geom_sum {x ε : ℤ} (hx : 3 ≤ x) (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : Odd p)
    (hp3 : 3 ≤ p) : 1 < ∑ i ∈ range p, x ^ i * ε ^ (p - 1 - i) := by
  have hpos : 0 < x - ε := by rcases hε with rfl | rfl <;> omega
  have hxp : x < x ^ p := lt_self_pow₀ (by omega) (by omega)
  have h := geom_sum_mul_sub_eq (x := x) hε hp
  by_contra hle
  push Not at hle
  have : (∑ i ∈ range p, x ^ i * ε ^ (p - 1 - i)) * (x - ε) ≤ 1 * (x - ε) :=
    mul_le_mul_of_nonneg_right hle hpos.le
  rw [h, one_mul] at this
  omega

end Arithmetic

theorem card_inf_centralizer_of_psl2 {X : Type*} [Group X] [Finite X] {J : Subgroup X}
    {F : Type} [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F)) (e : J ≃* PSL2 F) {ε : ℤ}
    (hε : (Nat.card F : ℤ) ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1) {a : X} (haJ : a ∈ J)
    (ha : orderOf a = 2) :
    (Nat.card ↥(J ⊓ centralizer ({a} : Set X)) : ℤ) = Nat.card F - ε := by
  set f : PSL2 F →* X := J.subtype.comp e.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := J.subtype_injective.comp e.symm.injective
  have hfr : f.range = J := range_subtype_comp_symm e
  have ht : orderOf (e ⟨a, haJ⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact ha
  have hft : f (e ⟨a, haJ⟩) = a := by simp [f]
  obtain ⟨m, hm, ⟨eC⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hF hε hε1 ht
  have hmap := CFSG.ABGDGroups.map_inf_centralizer_of_injective f hf ⊤ (e ⟨a, haJ⟩)
  rw [top_inf_eq, ← MonoidHom.range_eq_map, hfr, hft] at hmap
  have h3 : 3 ≤ Nat.card F := three_le_of_isOddPrimePower hF
  have : NeZero m := ⟨by rintro rfl; rcases hε1 with rfl | rfl <;> omega⟩
  rw [← hmap, card_map_of_injective hf, Nat.card_congr eC.toEquiv, DihedralGroup.nat_card]
  push_cast
  exact hm

theorem mem_centralizer_zpowers_iff {G : Type*} [Group G] {g z : G} :
    z ∈ centralizer ((zpowers g : Subgroup G) : Set G) ↔ z * g = g * z := by
  constructor
  · intro h
    exact (mem_centralizer_iff.mp h g (mem_zpowers g)).symm
  · intro h
    rw [mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact ((Commute.zpow_left h.symm n)).eq

theorem card_inf_centralizer_inf_centralizer_eq
    {X : Type} [Group X] [Finite X] {J V U : Subgroup X} {r k : ℕ}
    [Fact r.Prime] (hr : r ≠ 2) (hq : 5 ≤ r ^ k) (e : J ≃* PSL(2, GaloisField r k))
    (hV : IsKleinFour V) (hVJ : V ≤ J) (hUJ : U ≤ normalizer (J : Set X)) (hU : Odd (Nat.card U))
    (hUV : U ≤ centralizer (V : Set X)) (hfaith : (J ⊔ U) ⊓ centralizer (J : Set X) = ⊥)
    {u : X} (hu : u ∈ U) {p : ℕ} (hp : p.Prime) (hup : orderOf u = p) {a : X} (ha : a ∈ V)
    (ha1 : a ≠ 1) :
    ∃ (q₀ : ℕ) (ε : ℤ), r ^ k = q₀ ^ p ∧ IsOddPrimePower q₀ ∧ (q₀ : ℤ) ≡ ε [ZMOD 4] ∧
      (ε = 1 ∨ ε = -1) ∧
      (Nat.card ↥(J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X)) : ℤ) = q₀ - ε := by
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq
    omega
  obtain ⟨ι, E, S, hd, hcore, -, hUE⟩ := exists_isLinearDecomposition_sup hr hq e hV hVJ hUJ hU
    hUV hfaith
  set u' : ↥(J ⊔ U) := ⟨u, mem_sup_right hu⟩ with hu'def
  have hE₀E : zpowers u' ≤ E := by
    rw [zpowers_le, ← hUE]
    exact hu
  obtain ⟨F₀, _, _, hcardF, ⟨ψ⟩⟩ := hd.centralizer_fieldSubgroup_mulEquiv hE₀E
  have hE₀card : Nat.card (zpowers u') = p := by
    rw [Nat.card_zpowers, hu'def, Subgroup.orderOf_mk, hup]
  rw [hE₀card, GaloisField.card r k hk] at hcardF
  have hq₀ : IsOddPrimePower (Nat.card F₀) := by
    have hdvd : Nat.card F₀ ∣ r ^ k := hcardF ▸ dvd_pow_self _ hp.ne_zero
    obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow (Fact.out : r.Prime)).mp hdvd
    have h1 : 1 < Nat.card F₀ := Finite.one_lt_card
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      omega
    exact ⟨r, j, Fact.out, (Fact.out : r.Prime).odd_of_ne_two hr, Nat.one_le_iff_ne_zero.mpr hj0,
      hj⟩
  obtain ⟨ε, hε, hε1⟩ := exists_modEq_four_of_odd (odd_of_isOddPrimePower hq₀)
  refine ⟨Nat.card F₀, ε, hcardF, hq₀, hε, hε1, ?_⟩
  set D₀ := CFSG.ABGDGroups.linearCore ι ⊓
    centralizer ((zpowers u' : Subgroup ↥(J ⊔ U)) : Set ↥(J ⊔ U)) with hD₀def
  have haH : a ∈ J ⊔ U := mem_sup_left (hVJ ha)
  have hau : a * u = u * a := mem_centralizer_iff.mp (hUV hu) a ha
  have haD : (⟨a, haH⟩ : ↥(J ⊔ U)) ∈ D₀ := by
    refine ⟨?_, mem_centralizer_zpowers_iff.mpr (Subtype.ext hau)⟩
    rw [hcore]
    exact hVJ ha
  have ha2 : orderOf a = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV ha) ha1
  have ht : orderOf (ψ ⟨⟨a, haH⟩, haD⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact ha2
  obtain ⟨m, hm, ⟨eC⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hq₀ hε hε1 ht
  have h3 : 3 ≤ Nat.card F₀ := three_le_of_isOddPrimePower hq₀
  have : NeZero m := ⟨by rintro rfl; rcases hε1 with rfl | rfl <;> omega⟩
  have hmapψ := CFSG.ABGDGroups.map_inf_centralizer_of_injective ψ.toMonoidHom ψ.injective ⊤
    (⟨⟨a, haH⟩, haD⟩ : D₀)
  rw [top_inf_eq, map_top_of_surjective _ ψ.surjective, top_inf_eq] at hmapψ
  have hcard1 : Nat.card ↥(centralizer ({(⟨⟨a, haH⟩, haD⟩ : D₀)} : Set D₀)) = 2 * m := by
    have := congrArg (fun K : Subgroup (PSL2 F₀) => Nat.card K) hmapψ
    rw [card_map_of_injective ψ.injective] at this
    rw [this]
    exact (Nat.card_congr eC.toEquiv).trans DihedralGroup.nat_card
  have hKH : J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X) ≤ J ⊔ U :=
    inf_le_left.trans (inf_le_left.trans le_sup_left)
  have hsub : (J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X)).subgroupOf (J ⊔ U) =
      (centralizer ({(⟨⟨a, haH⟩, haD⟩ : D₀)} : Set D₀)).map D₀.subtype := by
    ext z
    constructor
    · intro hz
      have hz' : (z : X) ∈ J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X) := hz
      obtain ⟨⟨hzJ, hza⟩, hzu⟩ := hz'
      have hza' : (z : X) * a = a * z := mem_centralizer_singleton_iff.mp hza
      have hzu' : (z : X) * u = u * z := mem_centralizer_singleton_iff.mp hzu
      have hzD : z ∈ D₀ :=
        ⟨by rw [hcore]; exact hzJ, mem_centralizer_zpowers_iff.mpr (Subtype.ext hzu')⟩
      exact ⟨⟨z, hzD⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext (Subtype.ext hza')), rfl⟩
    · rintro ⟨⟨w, hwD⟩, hwa, rfl⟩
      have hwa' : (⟨w, hwD⟩ : D₀) * ⟨⟨a, haH⟩, haD⟩ = ⟨⟨a, haH⟩, haD⟩ * ⟨w, hwD⟩ :=
        mem_centralizer_singleton_iff.mp hwa
      have hwa'' : (w : X) * a = a * w := congrArg (fun x : D₀ => ((x : ↥(J ⊔ U)) : X)) hwa'
      have hwJ : (w : X) ∈ J := by
        have := hwD.1
        rw [hcore] at this
        exact this
      have hwu : (w : X) * u = u * w :=
        congrArg Subtype.val (mem_centralizer_zpowers_iff.mp hwD.2)
      show (w : X) ∈ J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X)
      exact ⟨⟨hwJ, mem_centralizer_singleton_iff.mpr hwa''⟩, mem_centralizer_singleton_iff.mpr hwu⟩
  have hcardK : Nat.card ↥(J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X)) = 2 * m := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv, hsub,
      card_map_of_injective D₀.subtype_injective, hcard1]
  rw [hcardK]
  push_cast
  exact hm

section Configuration

variable {X : Type} [Group X] [Finite X] {J V : Subgroup X}

theorem exists_orderOf_eq_of_isPGroup_ne_bot {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {K : Subgroup G} (hK : IsPGroup p K) (hK1 : K ≠ ⊥) :
    ∃ x ∈ K, orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card K := by
    obtain ⟨n, hn⟩ := hK.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hK1 (Subgroup.card_eq_one.mp hn)
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨⟨x, hx⟩, hxp⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨x, hx, by rwa [Subgroup.orderOf_mk] at hxp⟩

theorem modEq_four_pow {q₀ : ℕ} {ε : ℤ} (hε : (q₀ : ℤ) ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1)
    {p : ℕ} (hp : Odd p) : ((q₀ ^ p : ℕ) : ℤ) ≡ ε [ZMOD 4] := by
  push_cast
  rw [← pow_eq_self_of_odd hε1 hp]
  exact hε.pow p

theorem not_dvd_card_inf_centralizer_of_isMaxInvIn
    {r k : ℕ} [Fact r.Prime] (hr : r ≠ 2) (hq : 5 ≤ r ^ k)
    (e : J ≃* PSL(2, GaloisField r k)) (hV : IsKleinFour V) (hVJ : V ≤ J) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsPGroup p P) (hPJ : P ≤ normalizer (J : Set X))
    (hPV : P ≤ centralizer (V : Set X)) (hmax : IsMaxInvIn p V (J ⊔ P) P) {a : X} (ha : a ∈ V)
    (ha1 : a ≠ 1) : ¬ p ∣ Nat.card (J ⊓ centralizer ({a} : Set X) : Subgroup X) := by
  intro hpa
  have : Fact p.Prime := ⟨hp⟩
  have hJL : IsL2PGL2OrA7OrV4 J := Or.inl (Or.inr ⟨r, k, inferInstance, hr, hq, ⟨e⟩⟩)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV ha) ha1
  obtain ⟨W, hWs, hWall⟩ := exists_isSylowOf_inf_centralizer_forall_le hJL hp hp2 (hVJ ha) ha2
  have hW1 : W ≠ ⊥ := by
    intro hW
    have hcard := hWs.card_eq
    rw [hW, card_bot] at hcard
    have hpos := hp.factorization_pos_of_dvd Nat.card_pos.ne' hpa
    have : 1 < p ^ (Nat.card ↥(J ⊓ centralizer ({a} : Set X))).factorization p :=
      Nat.one_lt_pow hpos.ne' hp.one_lt
    omega
  have hconj : ∀ g ∈ normalizer (J : Set X), g * a * g⁻¹ = a → g ∈ normalizer (W : Set X) := by
    intro g hgJ hga
    apply mem_normalizer_fintype
    intro y hy
    have hle : W.map (MulAut.conj g).toMonoidHom ≤ J ⊓ centralizer ({a} : Set X) := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' := hWs.le hz
      refine ⟨(mem_normalizer_iff.mp hgJ z).mp hz'.1, ?_⟩
      change g * z * g⁻¹ ∈ centralizer ({a} : Set X)
      rw [mem_centralizer_singleton_iff]
      have hza := mem_centralizer_singleton_iff.mp hz'.2
      calc g * z * g⁻¹ * a = g * z * g⁻¹ * (g * a * g⁻¹) := by rw [hga]
        _ = g * (z * a) * g⁻¹ := by group
        _ = g * (a * z) * g⁻¹ := by rw [hza]
        _ = g * a * g⁻¹ * (g * z * g⁻¹) := by group
        _ = a * (g * z * g⁻¹) := by rw [hga]
    exact hWall _ hle (hWs.isPGroup.map _) ⟨y, hy, rfl⟩
  have hPW : P ≤ normalizer (W : Set X) := fun x hx => hconj x (hPJ hx) (by
    have h := mem_centralizer_iff.mp (hPV hx) a ha
    calc x * a * x⁻¹ = a * x * x⁻¹ := by rw [← h]
      _ = a := by group)
  have hVW : V ≤ normalizer (W : Set X) := fun v hv => hconj v (le_normalizer (hVJ hv)) (by
    rw [mul_comm_of_mem_kleinFour hV hv ha]
    group)
  have hVP : V ≤ normalizer (P : Set X) := fun v hv =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx =>
      (mem_centralizer_iff.mp (hPV hx) v hv).symm)
  have hPWp : IsPGroup p (P ⊔ W : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' hP hWs.isPGroup hPW
  have hVPW : V ≤ normalizer ((P ⊔ W : Subgroup X) : Set X) := fun v hv => by
    have hA := hVP hv
    have hB := hVW hv
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
    rw [Subgroup.map_sup, hA, hB]
  have hPWle : P ⊔ W ≤ J ⊔ P := sup_le le_sup_right (hWs.le.trans (inf_le_left.trans le_sup_left))
  have hPWeq := hmax.2.2.2 (P ⊔ W) hPWle hPWp hVPW le_sup_left
  have hWP : W ≤ P := hPWeq ▸ le_sup_right
  have hPJbot : P ⊓ J = ⊥ := inf_eq_bot_of_odd_of_le_centralizer_kleinFour hr hq e hV hVJ
    (odd_card_of_isPGroup hp hp2 hP) hPV
  apply hW1
  rw [eq_bot_iff, ← hPJbot]
  exact le_inf hWP (hWs.le.trans inf_le_left)

theorem eps_eq_of_modEq_four {q₀ : ℤ} {ε ε' : ℤ} (hε : q₀ ≡ ε [ZMOD 4]) (hε1 : ε = 1 ∨ ε = -1)
    (hε' : q₀ ≡ ε' [ZMOD 4]) (hε'1 : ε' = 1 ∨ ε' = -1) : ε = ε' := by
  have h := hε.symm.trans hε'
  rw [Int.ModEq] at h
  rcases hε1 with rfl | rfl <;> rcases hε'1 with rfl | rfl <;> first | rfl | (norm_num at h)

theorem card_inf_centralizer_eq_mul
    {U : Subgroup X} {r k : ℕ} [Fact r.Prime] (hr : r ≠ 2) (hq : 5 ≤ r ^ k)
    (e : J ≃* PSL(2, GaloisField r k)) (hV : IsKleinFour V) (hVJ : V ≤ J)
    (hUJ : U ≤ normalizer (J : Set X)) (hU : Odd (Nat.card U)) (hUV : U ≤ centralizer (V : Set X))
    (hfaith : (J ⊔ U) ⊓ centralizer (J : Set X) = ⊥) {u : X} (hu : u ∈ U) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hup : orderOf u = p) {a : X} (ha : a ∈ V) (ha1 : a ≠ 1) :
    ∃ (q₀ : ℕ) (ε : ℤ), r ^ k = q₀ ^ p ∧ (q₀ : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) ∧
      (Nat.card ↥(J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X)) : ℤ) = q₀ - ε ∧
      Odd (∑ i ∈ range p, (q₀ : ℤ) ^ i * ε ^ (p - 1 - i)) ∧
      1 < ∑ i ∈ range p, (q₀ : ℤ) ^ i * ε ^ (p - 1 - i) ∧
      (Nat.card ↥(J ⊓ centralizer ({a} : Set X)) : ℤ) =
        (∑ i ∈ range p, (q₀ : ℤ) ^ i * ε ^ (p - 1 - i)) *
          Nat.card ↥(J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X)) := by
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq
    omega
  have hF := isOddPrimePower_card_galoisField hr (by omega : 3 ≤ r ^ k)
  obtain ⟨q₀, ε, hqq₀, hq₀, hε, hε1, hD⟩ :=
    card_inf_centralizer_inf_centralizer_eq hr hq e hV hVJ hUJ hU hUV hfaith hu hp hup ha ha1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨j, hj⟩ := hpodd
    omega
  have hεq : (Nat.card (GaloisField r k) : ℤ) ≡ ε [ZMOD 4] := by
    rw [GaloisField.card r k hk, hqq₀]
    exact modEq_four_pow hε hε1 hpodd
  have ha2 : orderOf a = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV ha) ha1
  have hC := card_inf_centralizer_of_psl2 hF e hεq hε1 (hVJ ha) ha2
  rw [GaloisField.card r k hk, hqq₀] at hC
  refine ⟨q₀, ε, hqq₀, hε, hε1, hD, ?_, ?_, ?_⟩
  · exact odd_geom_sum (by exact_mod_cast odd_of_isOddPrimePower hq₀) hε1 hpodd
  · exact one_lt_geom_sum (by exact_mod_cast three_le_of_isOddPrimePower hq₀) hε1 hpodd hp3
  · rw [hC, hD, geom_sum_mul_sub_eq hε1 hpodd]
    push_cast
    ring

theorem exists_isSylowOf_inf_centralizer_eq_bot
    {r k : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (hq : 5 ≤ r ^ k) (e : J ≃* PSL(2, GaloisField r k)) (hV : IsKleinFour V)
    (hVJ : V ≤ J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsPGroup p P)
    (hP1 : P ≠ ⊥) (hPJ : P ≤ normalizer (J : Set X)) (hPV : P ≤ centralizer (V : Set X))
    (hfaith : (J ⊔ P) ⊓ centralizer (J : Set X) = ⊥) {a : X} (ha : a ∈ V) (ha1 : a ≠ 1)
    (hpa : ¬ p ∣ Nat.card (J ⊓ centralizer ({a} : Set X) : Subgroup X)) :
    ∃ (t : ℕ) (T : Subgroup X), t.Prime ∧ t ≠ 2 ∧ t ≠ p ∧
      IsSylowOf t T (J ⊓ centralizer ({a} : Set X)) ∧ T ≠ ⊥ ∧
      normalizer (J : Set X) ⊓ centralizer ({a} : Set X) ≤ normalizer (T : Set X) ∧
      P ⊓ centralizer (T : Set X) = ⊥ := by
  have hPodd := odd_card_of_isPGroup hp hp2 hP
  have hJL : IsL2PGL2OrA7OrV4 J := Or.inl (Or.inr ⟨r, k, inferInstance, hr, hq, ⟨e⟩⟩)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV ha) ha1
  obtain ⟨u, hu, hup⟩ := exists_orderOf_eq_of_isPGroup_ne_bot hp hP hP1
  obtain ⟨q₀, ε, hqq₀, hε, hε1, hD, hσodd, hσ1, hn⟩ :=
    card_inf_centralizer_eq_mul hr hq e hV hVJ hPJ hPodd hPV hfaith hu hp hp2 hup ha ha1
  set σ := ∑ i ∈ range p, (q₀ : ℤ) ^ i * ε ^ (p - 1 - i) with hσdef
  set n := Nat.card ↥(J ⊓ centralizer ({a} : Set X)) with hndef
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  set t := σ.toNat.minFac with htdef
  have hσnat : (σ.toNat : ℤ) = σ := Int.toNat_of_nonneg (by omega)
  have ht : t.Prime := Nat.minFac_prime (by omega)
  have htσ : (t : ℤ) ∣ σ := by
    rw [← hσnat]
    exact Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd _)
  have ht2 : t ≠ 2 := by
    intro h
    rw [h] at htσ
    exact (Int.not_even_iff_odd.mpr hσodd) (even_iff_two_dvd.mpr (by exact_mod_cast htσ))
  have htn : t ∣ n := by
    have : (t : ℤ) ∣ (n : ℤ) := by rw [hn]; exact dvd_mul_of_dvd_left htσ _
    exact_mod_cast this
  have htp : t ≠ p := fun h => hpa (h ▸ htn)
  obtain ⟨T, hTs, hTall⟩ := exists_isSylowOf_inf_centralizer_forall_le hJL ht ht2 (hVJ ha) ha2
  have : Fact t.Prime := ⟨ht⟩
  have hTcard := hTs.card_eq
  have hT1 : T ≠ ⊥ := by
    intro hT
    rw [hT, card_bot] at hTcard
    have hpos := ht.factorization_pos_of_dvd hn0 htn
    have : 1 < t ^ n.factorization t := Nat.one_lt_pow hpos.ne' ht.one_lt
    exact absurd hTcard (ne_of_lt this)
  refine ⟨t, T, ht, ht2, htp, hTs, hT1, ?_, ?_⟩
  · rintro g ⟨hgJ, hga⟩
    have hga' : g * a * g⁻¹ = a := by
      rw [mem_centralizer_singleton_iff.mp hga, mul_inv_cancel_right]
    apply mem_normalizer_fintype
    intro y hy
    have hle : T.map (MulAut.conj g).toMonoidHom ≤ J ⊓ centralizer ({a} : Set X) := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' := hTs.le hz
      refine ⟨(mem_normalizer_iff.mp hgJ z).mp hz'.1, ?_⟩
      change g * z * g⁻¹ ∈ centralizer ({a} : Set X)
      rw [mem_centralizer_singleton_iff]
      have hza := mem_centralizer_singleton_iff.mp hz'.2
      calc g * z * g⁻¹ * a = g * z * g⁻¹ * (g * a * g⁻¹) := by rw [hga']
        _ = g * (z * a) * g⁻¹ := by group
        _ = g * (a * z) * g⁻¹ := by rw [hza]
        _ = g * a * g⁻¹ * (g * z * g⁻¹) := by group
        _ = a * (g * z * g⁻¹) := by rw [hga']
    exact hTall _ hle (hTs.isPGroup.map _) ⟨y, hy, rfl⟩
  · by_contra hne
    obtain ⟨w, ⟨hwP, hwT⟩, hwp⟩ := exists_orderOf_eq_of_isPGroup_ne_bot hp
      (hP.to_le inf_le_left) hne
    obtain ⟨q₁, ε₁, hqq₁, hε₁, hε₁1, hD₁, -, -, -⟩ :=
      card_inf_centralizer_eq_mul hr hq e hV hVJ hPJ hPodd hPV hfaith hwP hp hp2 hwp ha ha1
    have hq₁ : q₁ = q₀ := Nat.pow_left_injective hp.ne_zero (hqq₁.symm.trans hqq₀)
    subst hq₁
    have hε₁ε : ε₁ = ε := eps_eq_of_modEq_four hε₁ hε₁1 hε hε1
    subst hε₁ε
    set d := Nat.card ↥(J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({w} : Set X)) with hddef
    have hTd : T ≤ J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({w} : Set X) := fun z hz =>
      ⟨hTs.le hz, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hwT z hz)⟩
    have hTdvd : t ^ n.factorization t ∣ d := hTcard ▸ Subgroup.card_dvd_of_le hTd
    have hcd : (Nat.card ↥(J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X)) : ℤ) =
        (d : ℤ) := by rw [hD, hD₁]
    have hdn : t * d ∣ n := by
      have : ((t * d : ℕ) : ℤ) ∣ (n : ℤ) := by
        rw [hn, hcd]
        push_cast
        exact mul_dvd_mul_right htσ _
      exact_mod_cast this
    apply Nat.pow_succ_factorization_not_dvd hn0 ht
    rw [pow_succ']
    exact (Nat.mul_dvd_mul_left t hTdvd).trans hdn

theorem inf_centralizer_eq_bot_of_isMaxInvIn
    {r k : ℕ} [Fact r.Prime] (hr : r ≠ 2) (hq : 5 ≤ r ^ k) (e : J ≃* PSL(2, GaloisField r k))
    (hV : IsKleinFour V) (hVJ : V ≤ J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Subgroup X}
    (hU : IsPGroup p U) (hUJ : U ≤ normalizer (J : Set X)) (hUV : U ≤ centralizer (V : Set X))
    (hfaith : (J ⊔ U) ⊓ centralizer (J : Set X) = ⊥) {W : Subgroup X} (hW : IsMaxInvIn p V J W)
    (hW1 : W ≠ ⊥) : U ⊓ centralizer (W : Set X) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hUodd := odd_card_of_isPGroup hp hp2 hU
  have hJL : IsL2PGL2OrA7OrV4 J := Or.inl (Or.inr ⟨r, k, inferInstance, hr, hq, ⟨e⟩⟩)
  obtain ⟨a, ha, ha1, hWs, -⟩ := exists_isSylowOf_of_isMaxInvIn hJL hV hVJ hp hp2 hW
  by_contra hne
  obtain ⟨w, ⟨hwU, hwW⟩, hwp⟩ := exists_orderOf_eq_of_isPGroup_ne_bot hp (hU.to_le inf_le_left) hne
  obtain ⟨q₀, ε, -, -, -, hD, -, -, hn⟩ :=
    card_inf_centralizer_eq_mul hr hq e hV hVJ hUJ hUodd hUV hfaith hwU hp hp2 hwp ha ha1
  set n := Nat.card ↥(J ⊓ centralizer ({a} : Set X)) with hndef
  set d := Nat.card ↥(J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({w} : Set X)) with hddef
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  have hWcard := hWs.card_eq
  have hWd : W ≤ J ⊓ centralizer ({a} : Set X) ⊓ centralizer ({w} : Set X) := fun z hz =>
    ⟨hWs.le hz, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hwW z hz)⟩
  have hWdvd : p ^ n.factorization p ∣ d := hWcard ▸ Subgroup.card_dvd_of_le hWd
  have hpW : p ∣ p ^ n.factorization p := by
    have hpos : 0 < n.factorization p := by
      by_contra h0
      push Not at h0
      have : n.factorization p = 0 := by omega
      rw [this, pow_zero] at hWcard
      exact hW1 (Subgroup.card_eq_one.mp hWcard)
    exact dvd_pow_self p hpos.ne'
  have hpd : (p : ℤ) ∣ (q₀ : ℤ) - ε := by
    rw [← hD]
    exact_mod_cast hpW.trans hWdvd
  have hpσ := dvd_geom_sum₂_self hpd
  have hdn : p * d ∣ n := by
    have : ((p * d : ℕ) : ℤ) ∣ (n : ℤ) := by
      rw [hn]
      push_cast
      exact mul_dvd_mul hpσ dvd_rfl
    exact_mod_cast this
  apply Nat.pow_succ_factorization_not_dvd hn0 hp
  rw [pow_succ']
  exact (Nat.mul_dvd_mul_left p hWdvd).trans hdn

end Configuration

end CFSG.GH72
