module

public import CFSG.ClassicalInvolution.Q3.TL3T25

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TC.Graph

section E8Section

variable {G : Type} [Group G] {X E : Subgroup G}

theorem le_normalizer_of_le_e8Struct (hE : E8Struct X E) {K : Subgroup G} (hKX : K ≤ X) :
    K ≤ Subgroup.normalizer (E : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro e
  refine ⟨fun he => hE.normal k (hKX hk) e he, fun he => ?_⟩
  have := hE.normal k⁻¹ (X.inv_mem (hKX hk)) _ he
  simpa [mul_assoc] using this

theorem card_inf_e8Struct (hE : E8Struct X E) {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hzE : z ∈ E) : Nat.card ↥(K ⊓ E) = 2 := by
  have hset : ((K ⊓ E : Subgroup G) : Set G) = {1, z} := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxK, hxE⟩
      exact hz.unique x hxK (hE.sq x hxE)
    · rintro (rfl | rfl)
      · exact ⟨K.one_mem, E.one_mem⟩
      · exact ⟨hz.mem, hzE⟩
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_pair hz.ne_one.symm]

variable [Finite G]

theorem card_sup_e8Struct (hE : E8Struct X E) {K : Subgroup G} (hKX : K ≤ X) {z : G}
    (hz : IsUniqueInvolution K z) (hzE : z ∈ E) : Nat.card ↥(K ⊔ E) * 2 = Nat.card K * 8 := by
  have h := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := K) (B := E)
    (le_normalizer_of_le_e8Struct hE hKX)
  rw [card_inf_e8Struct hE hz hzE, hE.card] at h
  exact h

variable {Ω : Set (Subgroup G)}

theorem e8Struct_le_normalizer (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (hE : E8Struct X E) {K : Subgroup G} (hK : K ∈ Ω) (hKX : K ≤ X) {z : G}
    (hz : IsUniqueInvolution K z) (hzE : z ∈ E) : E ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN := le_normalizer_of_le_e8Struct hE hKX
  intro e he
  by_contra hne
  have hJK : conjSub e K ≠ K := fun h => hne (mem_normalizer_iff_conjSub_eq.mpr h)
  have hJ : conjSub e K ∈ Ω := hΩ.conjInvariant e K hK
  have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card (n := 3) (by rw [hE.card]; norm_num)
  have hKE2 : IsPGroup 2 ↥(K ⊔ E) := (h2 K hK).to_sup_of_normal_right' hE2 hKN
  have hJKE : conjSub e K ≤ K ⊔ E := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have : x = e * (e⁻¹ * x * e) * e⁻¹ := by group
    rw [this]
    exact (K ⊔ E).mul_mem ((K ⊔ E).mul_mem (Subgroup.mem_sup_right he)
      (Subgroup.mem_sup_left hx)) ((K ⊔ E).inv_mem (Subgroup.mem_sup_right he))
  obtain ⟨S, hS⟩ := hKE2.exists_le_sylow
  have hcomm : ∀ x ∈ K, ∀ y ∈ conjSub e K, x * y = y * x :=
    Q3CP.l67Gen G Ω hΩ S K (TC.mem_RSet_of_isPGroup hK (h2 K hK)) (conjSub e K)
      (TC.mem_RSet_of_isPGroup hJ (h2 _ hJ)) (le_sup_left.trans hS) (hJKE.trans hS) hJK.symm
  have hq : IsQuatSub K := Sec6Gen.isQuatSub_of_mem_RSet hΩ
    (TC.mem_RSet_of_isPGroup hK (h2 K hK))
  have hinf : Nat.card ↥(K ⊓ conjSub e K) ≤ 2 := by
    refine natCard_subgroup_le_two_of_subset (a := 1) (b := z) fun x hx => ?_
    refine hz.unique x hx.1 (hq.sq_eq_one_of_central hx.1 fun w hw => ?_)
    exact (hcomm w hw x hx.2).symm
  have hprod := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer (A := K) (B := conjSub e K)
    (le_normalizer_of_comm hcomm)
  have hcardJ : Nat.card ↥(conjSub e K) = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj e).injective
  have hle : Nat.card ↥(K ⊔ conjSub e K) ≤ Nat.card ↥(K ⊔ E) :=
    Subgroup.card_le_of_le (sup_le le_sup_left hJKE)
  have hKE := card_sup_e8Struct hE hKX hz hzE
  have h8 := hq.eight_le
  have hinf1 : 1 ≤ Nat.card ↥(K ⊓ conjSub e K) := Nat.card_pos
  rw [hcardJ] at hprod
  have hK8 : Nat.card K = 8 := by nlinarith
  have hge : Nat.card ↥(K ⊔ E) ≤ Nat.card ↥(K ⊔ conjSub e K) := by nlinarith
  have heq : K ⊔ conjSub e K = K ⊔ E :=
    Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hJKE) hge
  have heN : e ∈ K ⊔ conjSub e K := heq ▸ Subgroup.mem_sup_right he
  exact hne ((sup_le (Subgroup.le_normalizer) (le_normalizer_of_comm fun x hx y hy =>
    (hcomm y hy x hx).symm)) heN)

theorem conj_mem_or_of_e8Struct (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (hE : E8Struct X E) {K : Subgroup G} (hK : K ∈ Ω) (hKX : K ≤ X) {z : G}
    (hz : IsUniqueInvolution K z) (hzE : z ∈ E) {k : G} (hk : k ∈ K) {e : G} (he : e ∈ E) :
    k * e * k⁻¹ = e ∨ k * e * k⁻¹ = z * e := by
  have hc : k * e * k⁻¹ * e⁻¹ ∈ K := by
    have h1 : e * k⁻¹ * e⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp
        (e8Struct_le_normalizer hΩ h2 hE hK hKX hz hzE he) _).mp (K.inv_mem hk)
    have : k * e * k⁻¹ * e⁻¹ = k * (e * k⁻¹ * e⁻¹) := by group
    rw [this]
    exact K.mul_mem hk h1
  have hcE : k * e * k⁻¹ * e⁻¹ ∈ E :=
    E.mul_mem (hE.normal k (hKX hk) e he) (E.inv_mem he)
  rcases hz.unique _ hc (hE.sq _ hcE) with h | h
  · left
    calc k * e * k⁻¹ = k * e * k⁻¹ * e⁻¹ * e := by group
      _ = e := by rw [h, one_mul]
  · right
    calc k * e * k⁻¹ = k * e * k⁻¹ * e⁻¹ * e := by group
      _ = z * e := by rw [h]

omit [Finite G] in
theorem exists_ne_of_card_eight {E : Subgroup G} (hcard : Nat.card E = 8) (z : G) :
    ∃ j ∈ E, j ≠ 1 ∧ j ≠ z := by
  by_contra hcon
  push Not at hcon
  have h := natCard_subgroup_le_two_of_subset (A := E) (a := 1) (b := z) fun x hx => by
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hcon x hx h1)
  rw [hcard] at h
  omega

omit [Finite G] in
theorem exists_frame_of_card_eight [DecidableEq G] {E : Subgroup G} (hcard : Nat.card E = 8)
    (hsq : ∀ x ∈ E, x * x = 1) {z j : G} (hzE : z ∈ E) (hz1 : z ≠ 1) (hjE : j ∈ E)
    (hj1 : j ≠ 1) (hzj : z ≠ j) : ∃ e₀, E8Frame E z j e₀ := by
  obtain ⟨e, heE, heV⟩ : ∃ e ∈ E, e ∉ kleinSet z j := by
    by_contra hcon
    push Not at hcon
    have hsub : (E : Set G) ⊆ ((kleinSet z j : Finset G) : Set G) := fun x hx => hcon x hx
    have h1 : Nat.card E ≤ (kleinSet z j).card := by
      rw [← Nat.card_eq_finsetCard, ← SetLike.coe_sort_coe]
      exact Nat.card_mono (Finset.finite_toSet _) hsub
    have h2 : (kleinSet z j).card ≤ 4 := Finset.card_le_four
    rw [hcard] at h1
    omega
  exact ⟨e, hcard, hsq, hzE, hjE, hz1, hj1, hzj, heE, heV⟩

theorem card_inf_centralizer_le_of_e8Struct (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (hE : E8Struct X E) {K : Subgroup G} (hK : K ∈ Ω) (hKX : K ≤ X) {z : G}
    (hz : IsUniqueInvolution K z) (hzE : z ∈ E) [DecidableEq G] {j e₀ : G}
    (F : E8Frame E z j e₀) : Nat.card ↥(K ⊓ Subgroup.centralizer {j}) ≤ 4 := by
  have hzc : ∀ k ∈ K ⊓ Subgroup.centralizer {j}, k * z = z * k :=
    fun k hk => isUniqueInvolution_comm hz hk.1
  have h1 := card_le_two_mul_centralizer hzc hz.sq
    (fun k hk => conj_mem_or_of_e8Struct hΩ h2 hE hK hKX hz hzE hk.1 F.eE)
  have h3 : Nat.card ↥((K ⊓ Subgroup.centralizer {j}) ⊓ Subgroup.centralizer {e₀}) ≤ 2 := by
    refine natCard_subgroup_le_two_of_subset (a := 1) (b := z) fun x hx => ?_
    have hxK : x ∈ K := hx.1.1
    have hxj : x * j = j * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1.2
    have hxe : x * e₀ = e₀ * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hxz : x * z = z * x := isUniqueInvolution_comm hz hxK
    have hxE : x ∈ E := hE.cent x (hKX hxK) (F.comm_of_comm hxz hxj hxe)
    exact hz.unique x hxK (hE.sq x hxE)
  omega

theorem card_eq_eight_of_e8Struct (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (hE : E8Struct X E) {K : Subgroup G} (hK : K ∈ Ω) (hKX : K ≤ X) {z : G}
    (hz : IsUniqueInvolution K z) (hzE : z ∈ E) : Nat.card K = 8 := by
  classical
  obtain ⟨j, hjE, hj1, hjz⟩ := exists_ne_of_card_eight hE.card z
  obtain ⟨e₀, F⟩ := exists_frame_of_card_eight hE.card hE.sq hzE hz.ne_one hjE hj1 (Ne.symm hjz)
  have h1 := card_le_two_mul_centralizer (K := K) (y := j)
    (fun k hk => isUniqueInvolution_comm hz hk) hz.sq
    (fun k hk => conj_mem_or_of_e8Struct hΩ h2 hE hK hKX hz hzE hk hjE)
  have h3 := card_inf_centralizer_le_of_e8Struct hΩ h2 hE hK hKX hz hzE F
  have h8 := (Sec6Gen.isQuatSub_of_mem_RSet hΩ
    (TC.mem_RSet_of_isPGroup hK (h2 K hK))).eight_le
  omega

end E8Section

end CFSG.CGT.PushingUpLit.SolKNA.R4
