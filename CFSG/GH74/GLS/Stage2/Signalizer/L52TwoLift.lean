module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Abstract

variable {K : Type} [Group K]

theorem exists_fixed_mem_coset_of_odd {E N : Subgroup K} (hE : IsPGroup 2 ↥E)
    (hN : Odd (Nat.card ↥N)) (hEN : ∀ e ∈ E, ∀ n ∈ N, e * n * e⁻¹ ∈ N) {x : K}
    (hx : ∀ e ∈ E, x⁻¹ * (e * x * e⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ e ∈ E, e * (x * n) * e⁻¹ = x * n := by
  classical
  set 𝒞 : Set K := {c | x⁻¹ * c ∈ N} with h𝒞
  have hmem : ∀ e ∈ E, ∀ c ∈ 𝒞, e * c * e⁻¹ ∈ 𝒞 := by
    intro e he c hc
    show x⁻¹ * (e * c * e⁻¹) ∈ N
    have h1 : x⁻¹ * (e * c * e⁻¹) = (x⁻¹ * (e * x * e⁻¹)) * (e * (x⁻¹ * c) * e⁻¹) := by group
    rw [h1]
    exact N.mul_mem (hx e he) (hEN e he _ hc)
  let inst : MulAction ↥E ↥𝒞 :=
    { smul := fun e c => ⟨(e : K) * c * (e : K)⁻¹, hmem e e.2 c c.2⟩
      one_smul := fun c => Subtype.ext (by
        change (1 : K) * (c : K) * (1 : K)⁻¹ = c
        group)
      mul_smul := fun e e' c => Subtype.ext (by
        change ((e * e' : ↥E) : K) * (c : K) * ((e * e' : ↥E) : K)⁻¹ =
          (e : K) * ((e' : K) * (c : K) * (e' : K)⁻¹) * (e : K)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hcard : Nat.card ↥𝒞 = Nat.card ↥N := by
    refine Nat.card_congr ⟨fun c => ⟨x⁻¹ * c, c.2⟩, fun n => ⟨x * n, ?_⟩, ?_, ?_⟩
    · show x⁻¹ * (x * (n : K)) ∈ N
      simp
    · intro c
      apply Subtype.ext
      simp
    · intro n
      apply Subtype.ext
      simp
  have hodd : ¬ 2 ∣ Nat.card ↥𝒞 := by
    rw [hcard]
    exact fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨c, hc⟩, hfix⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (↥𝒞) hodd
  refine ⟨x⁻¹ * c, hc, fun e he => ?_⟩
  have h1 : (e : K) * c * (e : K)⁻¹ = c := congrArg Subtype.val (hfix ⟨e, he⟩)
  have h2 : x * (x⁻¹ * c) = c := by group
  rw [h2]
  exact h1

theorem exists_two_lift [Finite K] {N : Subgroup K} [N.Normal] (hN : Odd (Nat.card ↥N))
    {E A : Subgroup K} (hE2 : IsPGroup 2 ↥E) (hA2 : IsPGroup 2 ↥A)
    (hAE : A ≤ centralizer (E : Set K)) {B : Subgroup (K ⧸ N)} (hB2 : IsPGroup 2 ↥B)
    (hBE : ∀ b ∈ B, ∀ e ∈ E, b * QuotientGroup.mk' N e = QuotientGroup.mk' N e * b)
    (hAB : A.map (QuotientGroup.mk' N) ≤ B) :
    ∃ Q : Subgroup K, Q ≤ centralizer (E : Set K) ∧ IsPGroup 2 ↥Q ∧ A ≤ Q ∧
      Q.map (QuotientGroup.mk' N) = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y : Subgroup K := centralizer (E : Set K) ⊓ B.comap (QuotientGroup.mk' N)
  have hAY : A ≤ Y := fun a ha => ⟨hAE ha, hAB (Subgroup.mem_map_of_mem _ ha)⟩
  have hYB : ∀ b ∈ B, ∃ y ∈ Y, QuotientGroup.mk' N y = b := by
    intro b hb
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : ∀ e ∈ E, k⁻¹ * (e * k * e⁻¹) ∈ N := by
      intro e he
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      have h : QuotientGroup.mk' N k * QuotientGroup.mk' N e =
          QuotientGroup.mk' N e * QuotientGroup.mk' N k := hBE _ hb e he
      simp only [map_mul, map_inv]
      rw [← h]
      group
    obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset_of_odd hE2 hN
      (fun e _ n hn => (inferInstance : N.Normal).conj_mem n hn e) hx
    have hn1 : QuotientGroup.mk' N n = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hn
    have hkn : QuotientGroup.mk' N (k * n) = (k : K ⧸ N) := by
      rw [map_mul, hn1, mul_one]
      rfl
    refine ⟨k * n, Subgroup.mem_inf.2 ⟨?_, ?_⟩, hkn⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      calc e * (k * n) = (e * (k * n) * e⁻¹) * e := by group
        _ = (k * n) * e := by rw [hfix e he]
    · show QuotientGroup.mk' N (k * n) ∈ B
      rw [hkn]
      exact hb
  let f : ↥Y →* ↥B := ((QuotientGroup.mk' N).comp Y.subtype).codRestrict B (fun y => y.2.2)
  have hf : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨y, hy, hyb⟩ := hYB b hb
    exact ⟨⟨y, hy⟩, Subtype.ext hyb⟩
  obtain ⟨S, hAS⟩ := (hA2.comap_subtype (K := Y)).exists_le_sylow
  have hS_top : (⊤ : Subgroup ↥B) ≤ (S.mapSurjective hf : Subgroup ↥B) :=
    IsPGroup.le_sylow_of_normal (hB2.of_equiv Subgroup.topEquiv.symm) (S.mapSurjective hf)
  refine ⟨(S : Subgroup ↥Y).map Y.subtype, ?_, S.isPGroup'.map Y.subtype, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact s.2.1
  · intro a ha
    exact ⟨⟨a, hAY ha⟩, hAS (show (⟨a, hAY ha⟩ : ↥Y) ∈ A.comap Y.subtype from ha), rfl⟩
  · apply le_antisymm
    · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact s.2.2
    · intro b hb
      have hb' : (⟨b, hb⟩ : ↥B) ∈ (S.mapSurjective hf : Subgroup ↥B) :=
        hS_top (Subgroup.mem_top _)
      obtain ⟨s, hs, hsb⟩ := hb'
      exact ⟨s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsb⟩

end Abstract

section Lift

variable {G : Type} [Group G] [Finite G]

theorem odd_card_pPrimeCore {X : Type} [Group X] [Finite X] : Odd (Nat.card ↥(pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := X))

theorem exists_lift_centralizer_gen {H E A : Subgroup G} (hEH : E ≤ H) (hE2 : IsPGroup 2 ↥E)
    (hAH : A ≤ H) (hA2 : IsPGroup 2 ↥A) (hAE : A ≤ centralizer (E : Set G))
    {Qb : Subgroup (HBar H)} (hQ2 : IsPGroup 2 ↥Qb)
    (hQC : Qb ≤ centralizer ((barIn H E : Subgroup (HBar H)) : Set (HBar H)))
    (hAQ : barIn H A ≤ Qb) :
    ∃ Q : Subgroup G, Q ≤ H ∧ Q ≤ centralizer (E : Set G) ∧ IsPGroup 2 ↥Q ∧ A ≤ Q ∧
      barIn H Q = Qb := by
  have hN : Odd (Nat.card ↥(pPrimeCore 2 ↥H)) := odd_card_pPrimeCore
  have hAE' : A.subgroupOf H ≤ centralizer ((E.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hAE ha) e he)
  have hBE : ∀ b ∈ Qb, ∀ e ∈ E.subgroupOf H,
      b * QuotientGroup.mk' (pPrimeCore 2 ↥H) e = QuotientGroup.mk' (pPrimeCore 2 ↥H) e * b := by
    intro b hb e he
    exact (Subgroup.mem_centralizer_iff.1 (hQC hb) _ ⟨e, he, rfl⟩).symm
  obtain ⟨Q', hQ'C, hQ'2, hAQ', hQ'B⟩ := exists_two_lift (K := ↥H) (N := pPrimeCore 2 ↥H) hN
    (E := E.subgroupOf H) (A := A.subgroupOf H) hE2.comap_subtype hA2.comap_subtype hAE' hQ2 hBE hAQ
  refine ⟨Q'.map H.subtype, Subgroup.map_subtype_le _, ?_, hQ'2.map H.subtype, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (hQ'C hq) ⟨e, hEH he⟩ he)
  · intro a ha
    exact ⟨⟨a, hAH ha⟩, hAQ' (show (⟨a, hAH ha⟩ : ↥H) ∈ A.subgroupOf H from ha), rfl⟩
  · have hQQ : (Q'.map H.subtype).subgroupOf H = Q' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective Q'
    show ((Q'.map H.subtype).subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) = Qb
    rw [hQQ]
    exact hQ'B

theorem exists_lift_centralizer {H A : Subgroup G} (hAH : A ≤ H) (hA2 : IsPGroup 2 ↥A)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {Qb : Subgroup (HBar H)} (hQ2 : IsPGroup 2 ↥Qb)
    (hQC : Qb ≤ centralizer ((barIn H A : Subgroup (HBar H)) : Set (HBar H)))
    (hAQ : barIn H A ≤ Qb) :
    ∃ Q : Subgroup G, Q ≤ H ∧ Q ≤ centralizer (A : Set G) ∧ IsPGroup 2 ↥Q ∧ A ≤ Q ∧
      barIn H Q = Qb :=
  exists_lift_centralizer_gen hAH hA2 hAH hA2
    (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => hAcomm b hb a ha) hQ2 hQC hAQ

end Lift

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
