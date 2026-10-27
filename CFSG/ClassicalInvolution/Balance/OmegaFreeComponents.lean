module

public import CFSG.ClassicalInvolution.Balance.LocalBalance.Moved
public import CFSG.ClassicalInvolution.Balance.FrameIndex.Pairing

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

variable {G : Type*} [Group G]

abbrev OddQuot (a : G) : Type _ :=
  ↥(Subgroup.centralizer ({a} : Set G)) ⧸
    componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G))

@[expose] def oddQuotMk (a : G) : ↥(Subgroup.centralizer ({a} : Set G)) →* OddQuot a :=
  QuotientGroup.mk' (componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G)))

@[expose] def modOdd (a : G) (K : Subgroup G) : Subgroup (OddQuot a) :=
  (K.subgroupOf (Subgroup.centralizer ({a} : Set G))).map (oddQuotMk a)

@[expose] def OmegaFreeAt (Ω : Set (Subgroup G)) (a : G) (L : Subgroup (OddQuot a)) : Prop :=
  ∀ K ∈ Ω, K ≤ Subgroup.centralizer ({a} : Set G) →
    ∀ x ∈ modOdd a K, ∀ y ∈ L, x * y = y * x

@[expose] def RankOneAt (Ω : Set (Subgroup G)) (a : G) (L : Subgroup (OddQuot a)) : Prop :=
  (∃ K ∈ Ω, K ≤ Subgroup.centralizer ({a} : Set G) ∧ modOdd a K = L) ∧
    ∀ K ∈ Ω, K ≤ Subgroup.centralizer ({a} : Set G) →
      modOdd a K = L ∨ ∀ x ∈ modOdd a K, ∀ y ∈ L, x * y = y * x

theorem mem_modOdd_iff {a : G} {K : Subgroup G} {x : OddQuot a} :
    x ∈ modOdd a K ↔ ∃ k : ↥(Subgroup.centralizer ({a} : Set G)), (k : G) ∈ K ∧ oddQuotMk a k = x :=
  Iff.rfl

theorem oddQuotMk_mem_modOdd {a : G} {K : Subgroup G} {k : G}
    (hk : k ∈ K) (hkC : k ∈ Subgroup.centralizer ({a} : Set G)) :
    oddQuotMk a ⟨k, hkC⟩ ∈ modOdd a K :=
  ⟨⟨k, hkC⟩, hk, rfl⟩

theorem oddQuotMk_eq_one_iff {a : G} {k : ↥(Subgroup.centralizer ({a} : Set G))} :
    oddQuotMk a k = 1 ↔ k ∈ componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G)) :=
  QuotientGroup.eq_one_iff k

theorem eq_one_of_oddQuotMk_eq_one [Finite G] {a : G} {x : ↥(Subgroup.centralizer ({a} : Set G))}
    (hx : x * x = 1) (h : oddQuotMk a x = 1) : x = 1 := by
  have hmem := oddQuotMk_eq_one_iff.mp h
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [h1] at hdvd
    exact (Nat.not_even_iff_odd.mpr
      (OddCore.odd_card ↥(Subgroup.centralizer ({a} : Set G)))) (even_iff_two_dvd.mpr hdvd)

theorem omegaFreeAt_of_le_closure [Finite G] {Ω : Set (Subgroup G)} {a : G}
    {𝒞 : Set (Subgroup (OddQuot a))} (h𝒞 : ∀ M ∈ 𝒞, CFSG.IsComponent M)
    (hle : ∀ K ∈ Ω, K ≤ Subgroup.centralizer ({a} : Set G) →
      modOdd a K ≤ Subgroup.closure (⋃ M ∈ 𝒞, (M : Set (OddQuot a))))
    {L : Subgroup (OddQuot a)} (hL : CFSG.IsComponent L) (hL𝒞 : L ∉ 𝒞) : OmegaFreeAt Ω a L := by
  intro K hKΩ hKC x hx y hy
  have hcl : Subgroup.closure (⋃ M ∈ 𝒞, (M : Set (OddQuot a))) ≤
      Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a)) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro u hu
    obtain ⟨M, hM, huM⟩ := Set.mem_iUnion₂.mp hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    exact (LocalBalance.commute_of_isComponent_of_ne (h𝒞 M hM) hL
      (fun h => hL𝒞 (h ▸ hM)) u huM v hv).symm
  exact (Subgroup.mem_centralizer_iff.mp (hcl (hle K hKΩ hKC hx)) y hy).symm

theorem rankOneAt_of_le_component [Finite G] {Ω : Set (Subgroup G)} {a : G}
    {𝒞 : Set (Subgroup (OddQuot a))} (h𝒞 : ∀ M ∈ 𝒞, CFSG.IsComponent M)
    (hle : ∀ K ∈ Ω, K ≤ Subgroup.centralizer ({a} : Set G) → ∃ M ∈ 𝒞, modOdd a K ≤ M)
    {L : Subgroup (OddQuot a)} (hL : L ∈ 𝒞)
    (hex : ∃ K ∈ Ω, K ≤ Subgroup.centralizer ({a} : Set G) ∧ modOdd a K = L)
    (hmin : ∀ K ∈ Ω, K ≤ Subgroup.centralizer ({a} : Set G) → modOdd a K ≤ L →
      modOdd a K = L) : RankOneAt Ω a L := by
  refine ⟨hex, fun K hKΩ hKC => ?_⟩
  obtain ⟨M, hM, hKM⟩ := hle K hKΩ hKC
  by_cases hML : M = L
  · subst hML
    exact Or.inl (hmin K hKΩ hKC hKM)
  · refine Or.inr fun x hx y hy => ?_
    exact LocalBalance.commute_of_isComponent_of_ne (h𝒞 M hM) (h𝒞 L hL) hML x (hKM hx) y hy

section Frame

variable {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem mem_centralizer_of_mem_frame (Fr : ToralFrame F Ω E S) {a z : G} (ha : a ∈ E)
    {K : Subgroup G} (hK : K ∈ S) (hz : IsUniqueInvolution K z) :
    z ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (frame_comm Fr ha (Fr.mem_of_isUniqueInvolution hK hz)).symm

theorem le_centralizer_of_mem_axisSub {a : G} {E K : Subgroup G} (h : a ∈ axisSub E K) :
    K ≤ Subgroup.centralizer ({a} : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (mem_axisSub_iff.mp h).2 k hk

theorem oddQuotMk_centralizes_of_omegaFree_or_rankOne (Fr : ToralFrame F Ω E S) {a z : G}
    (ha : a ∈ E) {K : Subgroup G} (hK : K ∈ S) (haK : a ∈ axisSub E K)
    (hz : IsUniqueInvolution K z) {L : Subgroup (OddQuot a)}
    (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) (y : OddQuot a) (hy : y ∈ L) :
    oddQuotMk a ⟨z, mem_centralizer_of_mem_frame Fr ha hK hz⟩ * y =
      y * oddQuotMk a ⟨z, mem_centralizer_of_mem_frame Fr ha hK hz⟩ := by
  have hKC := le_centralizer_of_mem_axisSub haK
  have hKΩ : K ∈ Ω := Fr.subset hK
  have hzmem : oddQuotMk a ⟨z, mem_centralizer_of_mem_frame Fr ha hK hz⟩ ∈ modOdd a K :=
    oddQuotMk_mem_modOdd hz.mem _
  rcases hL with hL | ⟨-, hL⟩
  · exact hL K hKΩ hKC _ hzmem y hy
  · rcases hL K hKΩ hKC with h | h
    ·
      rw [← h] at hy
      obtain ⟨k, hkK, rfl⟩ := hy
      have hkK' : (k : G) ∈ K := hkK
      have hzk : z * (k : G) = (k : G) * z := by
        have h1 := hz.conj_eq (conjSub_eq_self_of_mem hkK')
        calc z * (k : G) = ((k : G) * z * (k : G)⁻¹) * (k : G) := by rw [h1]
          _ = (k : G) * z := by group
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext hzk)
    · exact h _ hzmem y hy

theorem oddQuotMk_centralizes_of_mem_zClosure (Fr : ToralFrame F Ω E S) {a : G} (ha : a ∈ E)
    {L : Subgroup (OddQuot a)} (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) {f : G}
    (hf : f ∈ zClosure E S a) (hfC : f ∈ Subgroup.centralizer ({a} : Set G)) (y : OddQuot a)
    (hy : y ∈ L) : oddQuotMk a ⟨f, hfC⟩ * y = y * oddQuotMk a ⟨f, hfC⟩ := by
  let Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))).comap (oddQuotMk a)
  have hsub : zClosure E S a ≤ Q.map (Subgroup.centralizer ({a} : Set G)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨K, ⟨hK, haK⟩, hz⟩
    refine ⟨⟨z, mem_centralizer_of_mem_frame Fr ha hK hz⟩, ?_, rfl⟩
    show oddQuotMk a _ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (oddQuotMk_centralizes_of_omegaFree_or_rankOne Fr ha hK haK hz hL y hy).symm
  obtain ⟨q, hq, hqf⟩ := hsub hf
  have hqe : q = ⟨f, hfC⟩ := Subtype.ext hqf
  subst hqe
  exact (Subgroup.mem_centralizer_iff.mp hq y hy).symm

private theorem exists_two_ne_one {F₀ : Subgroup G} (h4 : Nat.card F₀ = 4) :
    ∃ x ∈ F₀, ∃ y ∈ F₀, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hfin : Finite F₀ := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F₀
  have hc : 2 < Fintype.card F₀ := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
  by_cases ha1 : a = 1
  · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro h
      exact hab (ha1.trans (Subtype.ext h).symm)
    · intro h
      exact hac (ha1.trans (Subtype.ext h).symm)
  · by_cases hb1 : b = 1
    · refine ⟨a, a.2, c, c.2, fun h => ha1 (Subtype.ext h), ?_, fun h => hac (Subtype.ext h)⟩
      intro h
      exact hbc (hb1.trans (Subtype.ext h).symm)
    · by_cases hc1 : c = 1
      · exact ⟨a, a.2, b, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
          fun h => hab (Subtype.ext h)⟩
      · exact ⟨a, a.2, b, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
          fun h => hab (Subtype.ext h)⟩

theorem exists_mem_ne_one_centralizes_of_omegaFree_or_rankOne [Finite G]
    (Fr : ToralFrame F Ω E S) (hsym : PairingSymmetric E S) (hconn : PairingConnected E S) {a : G}
    (ha : a ∈ E) {F₀ : Subgroup G} (hF₀ : F₀ ≤ E) (h4 : Nat.card F₀ = 4)
    {L : Subgroup (OddQuot a)} (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) :
    ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ ∀ y ∈ L, f * y = y * f := by
  have finish : ∀ f ∈ F₀, f ≠ 1 → f ∈ zClosure E S a →
      ∃ f' ∈ modOdd a F₀, f' ≠ 1 ∧ ∀ y ∈ L, f' * y = y * f' := by
    intro f hfF hf1 hfA
    have hfE : f ∈ E := hF₀ hfF
    have hfC : f ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (frame_comm Fr ha hfE).symm
    refine ⟨oddQuotMk a ⟨f, hfC⟩, oddQuotMk_mem_modOdd hfF hfC, ?_, fun y hy =>
      oddQuotMk_centralizes_of_mem_zClosure Fr ha hL hfA hfC y hy⟩
    intro h
    have hsq : (⟨f, hfC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) *
        ⟨f, hfC⟩ = 1 := Subtype.ext (Fr.elem f hfE)
    exact hf1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := exists_two_ne_one h4
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hxy
    have hyy : y * y = 1 := Fr.elem y (hF₀ hy)
    calc x = x * (y * y) := by rw [hyy, mul_one]
      _ = (x * y) * y := (mul_assoc _ _ _).symm
      _ = y := by rw [h, one_mul]
  rcases mem_or_mem_or_mul_mem_zClosure Fr hsym hconn ha (hF₀ hx) (hF₀ hy) with h | h | h
  · exact finish x hx hx1 h
  · exact finish y hy hy1 h
  · exact finish (x * y) (F₀.mul_mem hx hy) hxy1 h

end Frame

end CFSG.ClassicalInvolution.Balance
