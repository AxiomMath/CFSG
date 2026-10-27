module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Odd

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

structure QuatTwinDatum {M : Type} [Group M] (K : Subgroup M) (s : M) : Prop where
  q8 : Nonempty (↥K ≃* QuaternionGroup 2)
  inv : IsUniqueInvolution K s
  twins : ∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
    ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x
  sq : ∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub (c * c) K = K

namespace Vtx

variable {Y : Type} [Group Y] [Finite Y]

theorem isPGroup_center_of_oddFree (hO : classicalInvolutionOddCore Y = ⊥) :
    IsPGroup 2 ↥(Subgroup.center Y) := by
  intro z
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (z : Y)).ne'
  have hwZ : (z : Y) ^ 2 ^ a ∈ Subgroup.center Y := Subgroup.pow_mem _ z.2 _
  have hord : orderOf ((z : Y) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hn⟩, hn]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos a)
  have hn' : (Subgroup.zpowers ((z : Y) ^ 2 ^ a)).Normal := ⟨fun x hx g => by
    have hxZ : x ∈ Subgroup.center Y := Subgroup.zpowers_le.mpr hwZ hx
    rw [Subgroup.mem_center_iff.mp hxZ g, mul_inv_cancel_right]
    exact hx⟩
  have hle : Subgroup.zpowers ((z : Y) ^ 2 ^ a) ≤ classicalInvolutionOddCore Y :=
    le_sSup ⟨hn', by rw [Nat.card_zpowers, hord]; exact hm⟩
  rw [hO] at hle
  have hw1 : (z : Y) ^ 2 ^ a = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  exact ⟨a, Subtype.ext (by simpa using hw1)⟩

omit [Finite Y] in
theorem not_mem_center_of_not_tightInO2 {t : Y} (ht : orderOf t = 2) (hO2 : ¬ TightInO2 t) :
    t ∉ Subgroup.center Y := by
  intro htZ
  refine hO2 ⟨Subgroup.zpowers t, ⟨fun x hx g => ?_⟩, ?_, Subgroup.mem_zpowers t⟩
  · have hxZ : x ∈ Subgroup.center Y := Subgroup.zpowers_le.mpr htZ hx
    rw [Subgroup.mem_center_iff.mp hxZ g, mul_inv_cancel_right]
    exact hx
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])

theorem inf_eq_bot_of_ne_involution {A B : Subgroup Y} {a b : Y} (hA : IsPGroup 2 ↥A)
    (ha : IsUniqueInvolution A a) (hb : IsUniqueInvolution B b) (hab : a ≠ b) : A ⊓ B = ⊥ := by
  by_contra hne
  have hnt : Nontrivial ↥(A ⊓ B) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have h2 : IsPGroup 2 ↥(A ⊓ B) := hA.to_le inf_le_left
  have hdvd : 2 ∣ Nat.card ↥(A ⊓ B) := by
    rcases h2.card_eq_or_dvd with h1 | h1
    · exact absurd h1 Finite.one_lt_card.ne'
    · exact h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hx2 : (x : Y) * x = 1 := by
    have h3 := pow_orderOf_eq_one x
    rw [hx, sq] at h3
    exact congrArg Subtype.val h3
  have hx1 : (x : Y) ≠ 1 := fun h => by
    have h4 : x = 1 := Subtype.ext h
    rw [h4, orderOf_one] at hx
    norm_num at hx
  have h5 := (ha.unique _ x.2.1 hx2).resolve_left hx1
  have h6 := (hb.unique _ x.2.2 hx2).resolve_left hx1
  exact hab (h5.symm.trans h6)

omit [Finite Y] in
theorem exists_center_of_mem_centralizer_mk {t m : Y}
    (hc : QuotientGroup.mk' (Subgroup.center Y) m ∈
      Subgroup.centralizer ({QuotientGroup.mk' (Subgroup.center Y) t} : Set _)) :
    ∃ ν ∈ Subgroup.center Y, m * t * m⁻¹ = t * ν := by
  have h1 : QuotientGroup.mk' (Subgroup.center Y) t =
      QuotientGroup.mk' (Subgroup.center Y) (m * t * m⁻¹) := by
    rw [map_mul, map_mul, map_inv, Subgroup.mem_centralizer_singleton_iff.mp hc,
      mul_inv_cancel_right]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  exact ⟨_, h1, by group⟩

section Datum

variable {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem commute_conj_core_of_twin (hd : TightDatum R S t) (h2 : IsPGroup 2 ↥(tightCore R))
    {m ν : Y} (hνZ : ν ∈ Subgroup.center Y) (hν1 : ν ≠ 1) (hm : m * t * m⁻¹ = t * ν) :
    ∀ x ∈ tightCore R, ∀ y ∈ conjSub m (tightCore R), x * y = y * x := by
  have hK := hd.isUniqueInvolution_core
  have hJ := hK.conj m
  rw [hm] at hJ
  have hne : t ≠ t * ν := fun h => hν1 (by
    have h3 := congrArg (t⁻¹ * ·) h
    simpa using h3.symm)
  have h0 := inf_eq_bot_of_ne_involution h2 hK hJ hne
  have hKC : ∀ x ∈ tightCore R, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hd.cent (tightCore_le R hx))
  have hCν : ∀ y : Y, y * (t * ν) = (t * ν) * y ↔ y * t = t * y := by
    intro y
    have hνy : y * ν = ν * y := Subgroup.mem_center_iff.mp hνZ y
    constructor
    · intro hy
      calc y * t = y * (t * ν) * ν⁻¹ := by group
        _ = (t * ν) * y * ν⁻¹ := by rw [hy]
        _ = t * (ν * y) * ν⁻¹ := by group
        _ = t * (y * ν) * ν⁻¹ := by rw [hνy]
        _ = t * y := by group
    · intro hy
      calc y * (t * ν) = (y * t) * ν := by group
        _ = (t * y) * ν := by rw [hy]
        _ = t * (y * ν) := by group
        _ = t * (ν * y) := by rw [hνy]
        _ = (t * ν) * y := by group
  have hJC : ∀ y ∈ conjSub m (tightCore R), y * t = t * y := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    refine (hCν y).mp ?_
    have h1 := hKC _ hy
    rw [← hm]
    calc y * (m * t * m⁻¹) = m * ((m⁻¹ * y * m) * t) * m⁻¹ := by group
      _ = m * (t * (m⁻¹ * y * m)) * m⁻¹ := by rw [h1]
      _ = m * t * m⁻¹ * y := by group
  intro x hx y hy
  have hxC : m⁻¹ * x * m ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 : x * (m * t * m⁻¹) = (m * t * m⁻¹) * x := by
      rw [hm]
      exact (hCν x).mpr (hKC x hx)
    calc m⁻¹ * x * m * t = m⁻¹ * (x * (m * t * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * t * m⁻¹) * x) * m := by rw [h3]
      _ = t * (m⁻¹ * x * m) := by group
  have hxN : x * y * x⁻¹ ∈ conjSub m (tightCore R) := by
    rw [mem_conjSub_iff] at hy ⊢
    have h4 := (Subgroup.mem_normalizer_iff.mp (hd.le_normalizer_core hxC) _).mp hy
    have e : m⁻¹ * (x * y * x⁻¹) * m =
        (m⁻¹ * x * m) * (m⁻¹ * y * m) * (m⁻¹ * x * m)⁻¹ := by group
    rw [e]
    exact h4
  have hyN : y * x⁻¹ * y⁻¹ ∈ tightCore R := by
    have hyC : y ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hJC y hy)
    exact (Subgroup.mem_normalizer_iff.mp (hd.le_normalizer_core hyC) _).mp
      ((tightCore R).inv_mem hx)
  have hc : x * y * x⁻¹ * y⁻¹ ∈ tightCore R ⊓ conjSub m (tightCore R) := by
    refine ⟨?_, (conjSub m (tightCore R)).mul_mem hxN ((conjSub m (tightCore R)).inv_mem hy)⟩
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact (tightCore R).mul_mem hx hyN
  rw [h0, Subgroup.mem_bot] at hc
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [hc, one_mul]

theorem quatTwinDatum_quot (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : ¬ TightInO2 t) (hZ : Subgroup.center Y ≠ ⊥)
    (hM : PhilipHall.QuaternionBridge.ExLie (Y ⧸ Subgroup.center Y)) :
    QuatTwinDatum ((tightCore R).map (QuotientGroup.mk' (Subgroup.center Y)))
      (QuotientGroup.mk' (Subgroup.center Y) t) := by
  have hO := secIdE4OddCent_proved Y R S t hd hc hO2 hZ hM
  have h2R := hd.isPGroup_of_oddCent hO
  have hcore := tightCore_eq_self_of_isPGroup h2R
  have h2 : IsPGroup 2 ↥(tightCore R) := by rw [hcore]; exact h2R
  have hN2 := isPGroup_center_of_oddFree hc.2.2
  have htN := not_mem_center_of_not_tightInO2 hd.order hO2
  have hconj : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      conjSub (QuotientGroup.mk' (Subgroup.center Y) c)
        ((tightCore R).map (QuotientGroup.mk' (Subgroup.center Y))) =
        (tightCore R).map (QuotientGroup.mk' (Subgroup.center Y)) := by
    intro c hc'
    rw [← TwistQ.conjSub_map, mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer_core hc')]
  refine ⟨?_, PhilipHall.QuaternionBridge.isUniqueInvolution_map_core hd hN2 htN, ?_, ?_⟩
  · obtain ⟨eS⟩ := hc.1
    have hS : (S : Subgroup R) = ⊤ := (S.is_maximal' (h2R.to_subgroup ⊤) le_top).symm
    let e₁ := (AscQuot.quotRestrictEquiv
      (PhilipHall.QuaternionBridge.core_inf_eq_bot hd hN2 htN)).symm
    let e₂ : ↥(tightCore R) ≃* ↥R := MulEquiv.subgroupCongr hcore
    let e₃ : ↥R ≃* ↥(S : Subgroup R) :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hS.symm)
    exact ⟨((e₁.trans e₂).trans e₃).trans eS⟩
  · intro c hc'
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) c
    obtain ⟨ν, hνZ, hm⟩ := exists_center_of_mem_centralizer_mk hc'
    by_cases hν1 : ν = 1
    · left
      refine hconj m (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      have h1 : m * t * m⁻¹ = t := by rw [hm, hν1, mul_one]
      calc m * t = (m * t * m⁻¹) * m := by group
        _ = t * m := by rw [h1]
    · right
      intro x hx y hy
      rw [← TwistQ.conjSub_map] at hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_mul, ← map_mul, commute_conj_core_of_twin hd h2 hνZ hν1 hm x' hx' y' hy']
  · intro c hc'
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) c
    obtain ⟨ν, hνZ, hm⟩ := exists_center_of_mem_centralizer_mk hc'
    have ht2 : t * t = 1 := hd.isUniqueInvolution_core.sq
    have hνt : ν * t = t * ν := (Subgroup.mem_center_iff.mp hνZ t).symm
    have hν2 : ν * ν = 1 := by
      calc ν * ν = t * t * (ν * ν) := by rw [ht2, one_mul]
        _ = t * (t * ν) * ν := by group
        _ = t * (ν * t) * ν := by rw [hνt]
        _ = (t * ν) * (t * ν) := by group
        _ = (m * t * m⁻¹) * (m * t * m⁻¹) := by rw [hm]
        _ = m * (t * t) * m⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hmν : m * ν * m⁻¹ = ν := by
      rw [Subgroup.mem_center_iff.mp hνZ m, mul_inv_cancel_right]
    have hmm : m * m * t * (m * m)⁻¹ = t := by
      calc m * m * t * (m * m)⁻¹ = m * (m * t * m⁻¹) * m⁻¹ := by group
        _ = m * (t * ν) * m⁻¹ := by rw [hm]
        _ = (m * t * m⁻¹) * (m * ν * m⁻¹) := by group
        _ = t * ν * ν := by rw [hm, hmν]
        _ = t := by rw [mul_assoc, hν2, mul_one]
    rw [← map_mul]
    refine hconj (m * m) (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    calc m * m * t = (m * m * t * (m * m)⁻¹) * (m * m) := by group
      _ = t * (m * m) := by rw [hmm]

end Datum

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
