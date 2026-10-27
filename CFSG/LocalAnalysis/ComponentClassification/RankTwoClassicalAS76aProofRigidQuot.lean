module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsLift

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Quot

variable {G : Type} [Group G] [Finite G] {P : Type*} [Group P] [Finite P] {A : Subgroup G}
  {θ : ↥A →* P}

omit [Finite G] [Finite P] in
theorem eq_one_of_sq_eq_one_of_mem_center (hodd : Odd (Nat.card (center ↥A))) {c : ↥A}
    (hc : c ∈ center ↥A) (h2 : c ^ 2 = 1) : c = 1 := by
  have hd := orderOf_dvd_of_pow_eq_one h2
  have hcd : orderOf c ∣ Nat.card (center ↥A) := by
    have h1 := orderOf_dvd_natCard (⟨c, hc⟩ : center ↥A)
    rwa [Subgroup.orderOf_mk] at h1
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hcd
    exact absurd (Nat.odd_iff.mp hodd) (by rw [Nat.dvd_iff_mod_eq_zero.mp hcd]; decide)

omit [Finite G] [Finite P] in
theorem map_centralizer_eq_of_quot (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {x : ↥A} (hx2 : x ^ 2 = 1) :
    (centralizer ({x} : Set ↥A)).map θ = centralizer ({θ x} : Set P) := by
  refine le_antisymm (map_centralizer_le θ x) ?_
  intro c hc
  obtain ⟨a, rfl⟩ := hθ c
  rw [mem_centralizer_singleton_iff] at hc
  have hzc : ⁅a, x⁆ ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc
  have hzx : a * x * a⁻¹ = ⁅a, x⁆ * x := by
    rw [commutatorElement_def, inv_mul_cancel_right]
  have hcomm : Commute ⁅a, x⁆ x := ((Subgroup.mem_center_iff.1 hzc) x).symm
  have hz2 : ⁅a, x⁆ ^ 2 = 1 := by
    have h1 : (a * x * a⁻¹) ^ 2 = 1 := by
      rw [sq, show a * x * a⁻¹ * (a * x * a⁻¹) = a * (x * x) * a⁻¹ by group, ← sq, hx2,
        mul_one, mul_inv_cancel]
    rw [hzx, hcomm.mul_pow, hx2, mul_one] at h1
    exact h1
  have hz1 := eq_one_of_sq_eq_one_of_mem_center hodd hzc hz2
  exact ⟨a, mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.mp hz1), rfl⟩

theorem map_perfectCore_centralizer_eq_of_quot (hθ : Function.Surjective θ)
    (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A))) {x : ↥A} (hx2 : x ^ 2 = 1) :
    (perfectCore (centralizer ({x} : Set ↥A))).map θ =
      perfectCore (centralizer ({θ x} : Set P)) := by
  rw [CFSG.Quasithin.map_perfectCore, map_centralizer_eq_of_quot hθ hker hodd hx2]

theorem perfectCore_inf_centralizer_eq_map (x : ↥A) :
    perfectCore (A ⊓ centralizer ({(x : G)} : Set G)) =
      (perfectCore (centralizer ({x} : Set ↥A))).map A.subtype := by
  rw [CFSG.Quasithin.map_perfectCore, map_subtype_centralizer]

theorem factorization_two_card_eq_of_quot (hθ : Function.Surjective θ)
    (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A))) :
    (Nat.card ↥A).factorization 2 = (Nat.card P).factorization 2 := by
  have hcard : Nat.card ↥A = Nat.card P * Nat.card (center ↥A) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker, hker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv.symm, hker]
  have hZ : (Nat.card (center ↥A)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hodd)
  rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hZ,
    add_zero]

omit [Finite G] [Finite P] in
theorem orderOf_map_eq_two_of_quot (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {z : ↥A} (hz2 : orderOf z = 2) : orderOf (θ z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [← map_pow, ← hz2, pow_orderOf_eq_one, map_one]) ?_
  intro h1
  have hzc : z ∈ center ↥A := by rw [← hker]; exact h1
  have := eq_one_of_sq_eq_one_of_mem_center hodd hzc (by rw [← hz2, pow_orderOf_eq_one])
  rw [this, orderOf_one] at hz2
  exact absurd hz2 (by decide)

theorem exists_isSylowOf_le_perfectCore_of_quot (hθ : Function.Surjective θ)
    (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A))) {x : G} (hx : x ∈ A)
    (hx2 : x ^ 2 = 1) (h : ∃ S : Subgroup P, IsSylowOf 2 S ⊤ ∧
      S ≤ perfectCore (centralizer ({θ ⟨x, hx⟩} : Set P))) :
    ∃ S : Subgroup G, IsSylowOf 2 S A ∧ S ≤ perfectCore (A ⊓ centralizer ({x} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hSX⟩ := h
  have hx2' : (⟨x, hx⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
  set XA := perfectCore (centralizer ({(⟨x, hx⟩ : ↥A)} : Set ↥A))
  have hSv : Nat.card S = 2 ^ (Nat.card ↥A).factorization 2 := by
    rw [hS.card_eq, card_top, ← factorization_two_card_eq_of_quot hθ hker hodd]
  have hdvd : 2 ^ (Nat.card ↥A).factorization 2 ∣ Nat.card XA := by
    rw [← hSv]
    refine (Subgroup.card_dvd_of_le hSX).trans ?_
    rw [← map_perfectCore_centralizer_eq_of_quot hθ hker hodd hx2']
    exact Subgroup.card_map_dvd _ _
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 XA))
  have hQ : 2 ^ (Nat.card ↥A).factorization 2 ∣ Nat.card Q := Q.pow_dvd_card_of_pow_dvd_card hdvd
  set S₀ : Subgroup ↥A := (Q : Subgroup XA).map XA.subtype
  have hS₀ : Nat.card S₀ = Nat.card Q := Subgroup.card_map_of_injective XA.subtype_injective
  obtain ⟨T, hT⟩ := (Q.isPGroup'.map XA.subtype).exists_le_sylow
  have hS₀v : Nat.card S₀ = 2 ^ (Nat.card ↥A).factorization 2 := by
    refine Nat.dvd_antisymm ?_ (hS₀ ▸ hQ)
    rw [← T.card_eq_multiplicity]
    exact Subgroup.card_dvd_of_le hT
  refine ⟨S₀.map A.subtype, isSylowOf_of_card (map_subtype_le _) ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hS₀v]
  · rw [show x = ((⟨x, hx⟩ : ↥A) : G) from rfl, perfectCore_inf_centralizer_eq_map]
    exact map_mono (map_subtype_le _)

theorem exists_conj_of_quot (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {p : G} (hp : p ∈ A) (hp2 : p ^ 2 = 1)
    (h : ∀ z : P, orderOf z = 2 →
      (∃ S : Subgroup P, IsSylowOf 2 S ⊤ ∧ S ≤ centralizer ({z} : Set P)) →
        ∃ a : P, a * z * a⁻¹ = θ ⟨p, hp⟩) :
    ∀ z ∈ A, orderOf z = 2 →
      (∃ S : Subgroup G, IsSylowOf 2 S A ∧ S ≤ centralizer ({z} : Set G)) →
        ∃ a ∈ A, a * z * a⁻¹ = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro z hz hz2 ⟨S, hS, hSz⟩
  set z' : ↥A := ⟨z, hz⟩
  have hz'2 : orderOf z' = 2 := by rwa [Subgroup.orderOf_mk]
  have hθz : orderOf (θ z') = 2 := orderOf_map_eq_two_of_quot hker hodd hz'2
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have hSbar : IsSylowOf 2 ((Q : Subgroup ↥A).map θ) ⊤ := by
    have h1 := (Q.mapSurjective hθ).card_eq_multiplicity
    rw [Sylow.coe_mapSurjective] at h1
    exact isSylowOf_of_card le_top (by rw [card_top, h1])
  have hSbarz : (Q : Subgroup ↥A).map θ ≤ centralizer ({θ z'} : Set P) := by
    refine (map_mono ?_).trans (map_centralizer_le θ z')
    intro s hs
    rw [hQ] at hs
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hSz hs))
  obtain ⟨ab, hab⟩ := h _ hθz ⟨_, hSbar, hSbarz⟩
  obtain ⟨a, rfl⟩ := hθ ab
  set c : ↥A := (a * z' * a⁻¹)⁻¹ * ⟨p, hp⟩
  have hc : c ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hab,
      inv_mul_cancel]
  have hcomm : Commute (a * z' * a⁻¹) c := (Subgroup.mem_center_iff.1 hc) _
  have hpc : (⟨p, hp⟩ : ↥A) = a * z' * a⁻¹ * c := by
    simp only [c]
    group
  have hz'sq : (a * z' * a⁻¹) ^ 2 = 1 := by
    rw [sq, show a * z' * a⁻¹ * (a * z' * a⁻¹) = a * (z' * z') * a⁻¹ by group, ← sq,
      ← hz'2, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hc2 : c ^ 2 = 1 := by
    have hp2' : (⟨p, hp⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hp2)
    rw [hpc, hcomm.mul_pow, hz'sq, one_mul] at hp2'
    exact hp2'
  have hc1 := eq_one_of_sq_eq_one_of_mem_center hodd hc hc2
  refine ⟨a, a.2, ?_⟩
  have h1 : a * z' * a⁻¹ = ⟨p, hp⟩ := by rw [hpc, hc1, mul_one]
  exact congrArg Subtype.val h1

theorem map_mem_centralizer_perfectCore_of_quot (hθ : Function.Surjective θ)
    (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A))) {x : G} (hx : x ∈ A)
    (hx2 : x ^ 2 = 1) {z : G} (hz : z ∈ A)
    (hzX : z ∈ centralizer (perfectCore (A ⊓ centralizer ({x} : Set G)) : Set G)) :
    θ ⟨z, hz⟩ ∈ centralizer (perfectCore (centralizer ({θ ⟨x, hx⟩} : Set P)) : Set P) := by
  have hx2' : (⟨x, hx⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
  rw [← map_perfectCore_centralizer_eq_of_quot hθ hker hodd hx2', mem_centralizer_iff]
  rintro _ ⟨w, hw, rfl⟩
  have hwX : (w : G) ∈ perfectCore (A ⊓ centralizer ({x} : Set G)) := by
    rw [show x = ((⟨x, hx⟩ : ↥A) : G) from rfl, perfectCore_inf_centralizer_eq_map]
    exact mem_map_of_mem _ hw
  have h1 : (w : G) * z = z * w := mem_centralizer_iff.mp hzX _ hwX
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h1

end Quot

section Model

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ι K : Type} [Fintype ι]
  [DecidableEq ι] [Field K] [Finite K] {H : Subgroup (GL ι K)}

@[expose] noncomputable def statedModelHom (e : rankTwoQuot A ≃* StatedProj H) :
    ↥A →* StatedProj H :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center ↥A))

omit [Finite G] [Finite K] in
theorem statedModelHom_surjective (e : rankTwoQuot A ≃* StatedProj H) :
    Function.Surjective (statedModelHom e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] [Finite K] in
theorem statedModelHom_ker (e : rankTwoQuot A ≃* StatedProj H) :
    (statedModelHom e).ker = center ↥A := by
  ext a
  rw [MonoidHom.mem_ker, statedModelHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem leviRigid_of_model (e : rankTwoQuot A ≃* StatedProj H)
    (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1) {M : GL ι K}
    (hMH : M ∈ H) (he : e (QuotientGroup.mk ⟨p, hpA⟩) = QuotientGroup.mk ⟨M, hMH⟩)
    (hM2 : orderOf M = 2)
    (hS : ∃ S : Subgroup (StatedProj H), IsSylowOf 2 S ⊤ ∧
      S ≤ perfectCore (centralizer ({(QuotientGroup.mk ⟨M, hMH⟩ : StatedProj H)} :
        Set (StatedProj H))))
    (hconj : ∀ z : StatedProj H, orderOf z = 2 →
      (∃ S : Subgroup (StatedProj H), IsSylowOf 2 S ⊤ ∧ S ≤ centralizer ({z} : Set _)) →
        ∃ a : StatedProj H, a * z * a⁻¹ = QuotientGroup.mk ⟨M, hMH⟩)
    (hcen : ∀ z : StatedProj H, orderOf z = 2 →
      z ∈ centralizer (perfectCore (centralizer ({(QuotientGroup.mk ⟨M, hMH⟩ : StatedProj H)} :
        Set (StatedProj H))) : Set (StatedProj H)) →
        ∃ (N : GL ι K) (hN : N ∈ H), (QuotientGroup.mk ⟨N, hN⟩ : StatedProj H) = z ∧
          ∃ a : K, (N : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1))
    {Y : Subgroup G} (hY : Y ≤ centralizer (alphaGroup e p : Set G)) (hcore : RigidCore A p Y) :
    LeviRigid A p Y := by
  have hθ := statedModelHom_surjective e
  have hker := statedModelHom_ker e
  have hθp : statedModelHom e ⟨p, hpA⟩ = QuotientGroup.mk ⟨M, hMH⟩ := he
  refine leviRigid_of_rigidCore ?_ ?_ ?_ hcore
  · exact exists_isSylowOf_le_perfectCore_of_quot hθ hker hodd hpA hp2 (by rwa [hθp])
  · exact exists_conj_of_quot hθ hker hodd hpA hp2 (by rwa [hθp])
  · intro z hz hz2 hzX
    have hz'2 : orderOf (⟨z, hz⟩ : ↥A) = 2 := by rwa [Subgroup.orderOf_mk]
    have h1 := map_mem_centralizer_perfectCore_of_quot hθ hker hodd hpA hp2 hz hzX
    rw [hθp] at h1
    obtain ⟨N, hN, hNz, a, ha⟩ :=
      hcen _ (orderOf_map_eq_two_of_quot hker hodd hz'2) h1
    have hzα : z ∈ alphaGroup e p := by
      refine subset_closure ⟨⟨1, by rw [pow_one, ← hz2, pow_orderOf_eq_one]⟩, M, N,
        ⟨hpA, hMH, he⟩, hM2, ⟨hz, hN, hNz.symm⟩, a, ha⟩
    exact hY.trans (centralizer_le (Set.singleton_subset_iff.mpr hzα))

end Model

end CFSG.ComponentClassification.RankTwoClassical
