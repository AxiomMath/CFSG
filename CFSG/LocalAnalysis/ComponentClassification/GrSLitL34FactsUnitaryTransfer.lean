
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandardBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryFixBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] {J P : Subgroup G} {x : G}

theorem betaHat_mk (hxN : x ∈ normalizer (J : Set G)) {p : G} (hp : p ∈ J) :
    betaHat J hxN (jq J ⟨p, hp⟩) = jq J ⟨x⁻¹ * p * x, conj_mem_of_mem_normalizer hxN hp⟩ := rfl

theorem conj_eq_of_mem_centralizer {u : G} (hu : u ∈ centralizer ({x} : Set G)) :
    x⁻¹ * u * x = u := by
  have hc := mem_centralizer_singleton_iff.mp hu
  calc x⁻¹ * u * x = x⁻¹ * (u * x) := by group
    _ = x⁻¹ * (x * u) := by rw [hc]
    _ = u := by group

theorem mem_centralizer_of_conj_eq {u : G} (hu : x⁻¹ * u * x = u) :
    u ∈ centralizer ({x} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  calc u * x = x * (x⁻¹ * u * x) := by group
    _ = x * u := by rw [hu]

variable [Finite G]

theorem exists_theta (hxN : x ∈ normalizer (J : Set G)) (hP : IsSylowTwoIn P J)
    (hxP : x ∈ normalizer (P : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e) :
    ∃ θ : ↥(P ⊓ centralizer ({x} : Set G)) ≃* ↥(fixT0 q (betaHat J hxN)),
      ∀ u, (θ u : Jhat J) = jq J ⟨u, hP.1 u.2.1⟩ := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hle : P ⊓ centralizer ({x} : Set G) ≤ J := inf_le_left.trans hP.1
  have hfix : ∀ u : ↥(P ⊓ centralizer ({x} : Set G)),
      jq J (Subgroup.inclusion hle u) ∈ fixT0 q (betaHat J hxN) := by
    intro u
    refine ⟨(hT _).2 ⟨u, u.2.1, _, rfl⟩, ?_⟩
    show betaHat J hxN (jq J ⟨u, hle u.2⟩) = jq J ⟨u, hle u.2⟩
    rw [betaHat_mk]
    congr 1
    exact Subtype.ext (conj_eq_of_mem_centralizer u.2.2)
  set f := ((jq J).comp (Subgroup.inclusion hle)).codRestrict (fixT0 q (betaHat J hxN)) hfix
    with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : jq J ⟨a, hP.1 a.2.1⟩ = jq J ⟨b, hP.1 b.2.1⟩ := congrArg Subtype.val hab
    exact Subtype.ext (eq_of_jq_eq hP.1 hP2 a.2.1 b.2.1 h1)
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e).1 he.1
    have hfixe := he.2
    rw [betaHat_mk] at hfixe
    have hc : x⁻¹ * p * x = p :=
      eq_of_jq_eq hP.1 hP2 (conj_mem_of_mem_normalizer hxP hpP) hpP hfixe
    exact ⟨⟨p, hpP, mem_centralizer_of_conj_eq hc⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun u => rfl⟩

theorem exists_zeta (hP : IsSylowTwoIn P J) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hqker : q.ker = center (Jhat J)) :
    ∃ ζ : ↥(P ⊓ zStarIn J) ≃* ↥q.ker, ∀ z, (ζ z : Jhat J) = jq J ⟨z, hP.1 z.2.1⟩ := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hle : P ⊓ zStarIn J ≤ J := inf_le_left.trans hP.1
  have hmem : ∀ z : ↥(P ⊓ zStarIn J), jq J (Subgroup.inclusion hle z) ∈ q.ker := by
    intro z
    rw [hqker]
    exact (mem_zStarIn_iff (hle z.2)).1 z.2.2
  set f := ((jq J).comp (Subgroup.inclusion hle)).codRestrict q.ker hmem with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : jq J ⟨a, hP.1 a.2.1⟩ = jq J ⟨b, hP.1 b.2.1⟩ := congrArg Subtype.val hab
    exact Subtype.ext (eq_of_jq_eq hP.1 hP2 a.2.1 b.2.1 h1)
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    rw [hqker] at he
    obtain ⟨p, hpP, hpJ, rfl⟩ := exists_mem_of_mem_center hP he
    exact ⟨⟨p, hpP, (mem_zStarIn_iff hpJ).2 he⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun z => rfl⟩

theorem card_CZ (hxN : x ∈ normalizer (J : Set G)) (hP : IsSylowTwoIn P J)
    (hxP : x ∈ normalizer (P : Set G)) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hqker : q.ker = center (Jhat J))
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e) :
    Nat.card ↥(P ⊓ zStarIn J ⊓ centralizer ({x} : Set G)) =
      Nat.card ↥(fixT0 q (betaHat J hxN) ⊓ q.ker) := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hmem : ∀ z : ↥(P ⊓ zStarIn J ⊓ centralizer ({x} : Set G)),
      jq J ⟨z, hP.1 z.2.1.1⟩ ∈ fixT0 q (betaHat J hxN) ⊓ q.ker := by
    intro z
    refine ⟨⟨(hT _).2 ⟨z, z.2.1.1, _, rfl⟩, ?_⟩, ?_⟩
    · rw [betaHat_mk]
      congr 1
      exact Subtype.ext (conj_eq_of_mem_centralizer z.2.2)
    · rw [hqker]
      exact (mem_zStarIn_iff _).1 z.2.1.2
  refine Nat.card_congr (Equiv.ofBijective (fun z => ⟨_, hmem z⟩) ⟨fun a b hab => ?_, ?_⟩)
  · have h1 : jq J ⟨a, hP.1 a.2.1.1⟩ = jq J ⟨b, hP.1 b.2.1.1⟩ := congrArg Subtype.val hab
    exact Subtype.ext (eq_of_jq_eq hP.1 hP2 a.2.1.1 b.2.1.1 h1)
  · rintro ⟨e, he1, he2⟩
    have he2' := he2
    rw [hqker] at he2'
    obtain ⟨p, hpP, hpJ, rfl⟩ := exists_mem_of_mem_center hP he2'
    have hfixe := he1.2
    rw [betaHat_mk] at hfixe
    have hc : x⁻¹ * p * x = p :=
      eq_of_jq_eq hP.1 hP2 (conj_mem_of_mem_normalizer hxP hpP) hpP hfixe
    exact ⟨⟨p, ⟨hpP, (mem_zStarIn_iff hpJ).2 he2'⟩, mem_centralizer_of_conj_eq hc⟩, rfl⟩

theorem card_P (hP : IsSylowTwoIn P J) {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e) :
    Nat.card P = Nat.card (T0.comap q) := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ⟨jq J ⟨p, hP.1 p.2⟩, (hT _).2 ⟨p, p.2, _, rfl⟩⟩) ⟨fun a b hab => ?_, ?_⟩)
  · have h1 : jq J ⟨a, hP.1 a.2⟩ = jq J ⟨b, hP.1 b.2⟩ := congrArg Subtype.val hab
    exact Subtype.ext (eq_of_jq_eq hP.1 hP2 a.2 b.2 h1)
  · rintro ⟨e, he⟩
    obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e).1 he
    exact ⟨⟨p, hpP⟩, rfl⟩

theorem card_inv_P (hxN : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1) (hP : IsSylowTwoIn P J)
    {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e) :
    Nat.card {p : P // (p : G) * x * (p * x) = 1} ≤
      Nat.card {e : Jhat J // q e ∈ T0 ∧ betaHat J hxN e = e⁻¹} := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  refine Nat.card_le_card_of_injective
    (fun p => ⟨jq J ⟨p.1, hP.1 p.1.2⟩, (hT _).2 ⟨p.1, p.1.2, _, rfl⟩, ?_⟩) ?_
  · rw [betaHat_mk, ← map_inv]
    congr 1
    apply Subtype.ext
    have h1 := p.2
    show x⁻¹ * (p.1 : G) * x = (p.1 : G)⁻¹
    rw [hxi]
    calc x * (p.1 : G) * x = (p.1 : G)⁻¹ * ((p.1 : G) * x * ((p.1 : G) * x)) := by group
      _ = (p.1 : G)⁻¹ := by rw [h1, mul_one]
  · intro a b hab
    have h1 : jq J ⟨a.1, hP.1 a.1.2⟩ = jq J ⟨b.1, hP.1 b.1.2⟩ := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext (eq_of_jq_eq hP.1 hP2 a.1.2 b.1.2 h1))

theorem exists_fixed_lift (hxN : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1) {e : Jhat J}
    (he : betaHat J hxN e = e) : ∃ j : J, jq J j = e ∧ conjJ J hxN j = j := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ j : J, conjJ J hxN (conjJ J hxN j) = j := fun j => Subtype.ext (by
    rw [coe_conjJ, coe_conjJ, inv_eq_of_mul_eq_one_right hx2]
    calc x * (x * ↑j * x) * x = (x * x) * ↑j * (x * x) := by group
      _ = ↑j := by rw [hx2]; group)
  have hmaps : ∀ j : {j : J // jq J j = e}, jq J (conjJ J hxN j.1) = e := fun j => by
    rw [← betaHat_jq, j.2, he]
  let σ : Equiv.Perm {j : J // jq J j = e} :=
    { toFun := fun j => ⟨conjJ J hxN j.1, hmaps j⟩
      invFun := fun j => ⟨conjJ J hxN j.1, hmaps j⟩
      left_inv := fun j => Subtype.ext (hinv j.1)
      right_inv := fun j => Subtype.ext (hinv j.1) }
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact Equiv.ext fun j => Subtype.ext (hinv j.1)
  have : Fintype {j : J // jq J j = e} := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  obtain ⟨j₀, hj₀⟩ := jq_surjective J e
  have hcardF : Nat.card {j : J // jq J j = e} = Nat.card (pPrimeCore 2 ↥J) := by
    refine Nat.card_congr
      { toFun := fun j => ⟨j₀⁻¹ * j.1, by
          rw [← QuotientGroup.eq_one_iff]
          show jq J (j₀⁻¹ * j.1) = 1
          rw [map_mul, map_inv, hj₀, j.2, inv_mul_cancel]⟩
        invFun := fun k => ⟨j₀ * k.1, by
          have hk : jq J k.1 = 1 := (QuotientGroup.eq_one_iff _).2 k.2
          rw [map_mul, hj₀, hk, mul_one]⟩
        left_inv := fun j => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
  have hodd : ¬ 2 ∣ Fintype.card {j : J // jq J j = e} := by
    rw [← Nat.card_eq_fintype_card, hcardF]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
  have hne : σ.supportᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.card_empty] at hmod
    exact hodd (Nat.modEq_zero_iff_dvd.mp hmod.symm)
  obtain ⟨j, hj⟩ := hne
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hj
  exact ⟨j.1, j.2, congrArg Subtype.val hj⟩

theorem card_centralizer_J (hxN : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1) :
    Nat.card ↥(J ⊓ centralizer ({x} : Set G)) =
      Nat.card {e : Jhat J // betaHat J hxN e = e} *
        Nat.card ↥(oddIn J ⊓ centralizer ({x} : Set G)) := by
  set f : ↥(J ⊓ centralizer ({x} : Set G)) →* Jhat J :=
    (jq J).comp (Subgroup.inclusion inf_le_left) with hf
  have hoddJ : oddIn J ≤ J := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hker : Nat.card f.ker = Nat.card ↥(oddIn J ⊓ centralizer ({x} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun u => ⟨u.1, (mem_oddIn_iff u.1.2.1).2 u.2, u.1.2.2⟩
        invFun := fun v => ⟨⟨v, hoddJ v.2.1, v.2.2⟩, (mem_oddIn_iff (hoddJ v.2.1)).1 v.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : Nat.card f.range = Nat.card {e : Jhat J // betaHat J hxN e = e} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ⟨?_, fun he => ?_⟩)
    · rintro ⟨u, rfl⟩
      show betaHat J hxN (jq J ⟨u, u.2.1⟩) = jq J ⟨u, u.2.1⟩
      rw [betaHat_mk]
      congr 1
      exact Subtype.ext (conj_eq_of_mem_centralizer u.2.2)
    · obtain ⟨j, rfl, hj⟩ := exists_fixed_lift hxN hx2 he
      refine ⟨⟨j, j.2, mem_centralizer_of_conj_eq ?_⟩, rfl⟩
      have := congrArg Subtype.val hj
      rwa [coe_conjJ] at this
  rw [← Subgroup.card_ker_mul_card_range f, hker, hrange, mul_comm]

end CFSG.ComponentClassification.GrSLit.L34Facts
