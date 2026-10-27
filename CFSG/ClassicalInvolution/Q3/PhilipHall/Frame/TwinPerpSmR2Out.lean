module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmR2Rank
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Aut
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import CFSG.GH74.Generic.S3.Lem36

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.R2

open CFSG CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.CGT.PushingUpLit.SolKNA.R4

theorem rankLeTwo_outer_of_mulEquiv {F F' : Type*} [Group F] [Group F'] (e : F ≃* F')
    (h : RankLeTwo (Outer F')) : RankLeTwo (Outer F) :=
  RankLeTwo.of_injective (equivalence e).toMonoidHom (equivalence e).injective h

theorem finite_ringEquiv_self' (K : Type*) [Field K] [Finite K] : Finite (K ≃+* K) :=
  Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) fun _ _ h => RingEquiv.ext (congrFun h)

theorem rankLeTwo_outer_psl2 (K : Type) [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (h3 : 3 < Nat.card K) : RankLeTwo (Outer (PSL2 K)) := by
  haveI : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  haveI := finite_ringEquiv_self' K
  set ε := (odd_outerEquivSemilinearQuotient K hK h3).symm with hε
  set f : Outer (PSL2 K) →* (K ≃+* K) := (quotientFieldProjection K).comp ε.toMonoidHom with hf
  refine rankLeTwo_of_pred (fun u => f u = 1) ?_ ?_
  · intro u v hu hv _ hu1 hv1
    have hu2 : f u ^ 2 = 1 := by rw [← map_pow, hu, map_one]
    have hv2 : f v ^ 2 = 1 := by rw [← map_pow, hv, map_one]
    rcases eq_of_sq_eq_one_of_isCyclic hu2 hv2 with h | h | h
    · exact absurd h hu1
    · exact absurd h hv1
    · show f (u * v) = 1
      rw [map_mul, ← h, ← pow_two, hu2]
  · intro u v _ _ _ hu1 hv1
    have hker : ∀ w, f w = 1 → ε w ∈ (diagonalHom K).range := fun w hw => by
      rw [← quotientFieldProjection_ker K]
      exact MonoidHom.mem_ker.mpr hw
    rcases eq_of_mem_of_card_dvd_two
        (CFSG.Walter.W67.JROut.card_diagonalHom_range_dvd_two K hK) (hker u hu1) (hker v hv1) with
      h | h | h
    · exact Or.inl (ε.injective (h.trans (map_one ε).symm))
    · exact Or.inr (Or.inl (ε.injective (h.trans (map_one ε).symm)))
    · exact Or.inr (Or.inr (ε.injective h))

theorem rankLeTwo_outer_psl3 (K : Type) [Field K] [Finite K] :
    RankLeTwo (Outer (projectiveSL 3 K)) := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨hID, -, hDn, -, -, ⟨g, hgE, hg⟩, -, -, -, -⟩ :=
    standard_outer_quotients (n := 3) (K := K)
  haveI : Finite (MulAut (projectiveSL 3 K)) := ProjectivePlane.finite_mulAut_projectiveSL 3
  set I := inner (projectiveSL 3 K) with hI
  set D := linearAutGroup 3 K with hD
  set E := semilinearAutGroup 3 K with hE
  set mk : MulAut (projectiveSL 3 K) →* Outer (projectiveSL 3 K) := QuotientGroup.mk' I with hmk
  have hID' : I ≤ D := hID
  have hDE : D ≤ E := linearAutGroup_le_semilinearAutGroup
  have hDnorm : ∀ d ∈ D, ∀ γ : MulAut (projectiveSL 3 K), γ * d * γ⁻¹ ∈ D := by
    intro d hd γ
    have hγ : γ ∈ standardAutGroup 3 K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup 3 K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact Subgroup.mem_subgroupOf.mp this
  haveI hN : (D.subgroupOf E).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hDE]
    intro d k hd _
    exact hDnorm d hd k
  haveI hcyc : IsCyclic (↥E ⧸ D.subgroupOf E) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun x => ?_⟩⟩
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := hg x hx
    refine ⟨-k, ?_⟩
    show (QuotientGroup.mk ⟨g, hgE⟩ : ↥E ⧸ D.subgroupOf E) ^ (-k) = QuotientGroup.mk ⟨x, hx⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [zpow_neg] using hk
  have hD2 : ∀ δ ∈ D, δ ^ 2 ∈ I → δ ∈ I := fun δ hδ h2 =>
    CFSG.RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two le_rfl (by
      intro h
      have := h.trans (Nat.gcd_dvd_left 3 _)
      omega) δ hδ 1 (by rwa [pow_one])
  have hmk1 : ∀ α, mk α = 1 ↔ α ∈ I := fun α => QuotientGroup.eq_one_iff α
  refine rankLeTwo_of_pred (fun u => u ∈ E.map mk) ?_ ?_
  · intro u v _ _ _ hu hv
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective I u
    obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective I v
    have hα : α ∉ E := fun h => hu ⟨α, h, rfl⟩
    have hβ : β ∉ E := fun h => hv ⟨β, h, rfl⟩
    exact ⟨α * β, Q5L3.mul_mem_semilinearAutGroup hα hβ, map_mul _ _ _⟩
  · intro u v hu hv huv hu' hv'
    obtain ⟨α, hαE, rfl⟩ := hu'
    obtain ⟨β, hβE, rfl⟩ := hv'
    have hα2 : α ^ 2 ∈ I := (hmk1 _).mp (by rw [map_pow]; exact hu)
    have hβ2 : β ^ 2 ∈ I := (hmk1 _).mp (by rw [map_pow]; exact hv)
    have hbar : ∀ (γ : MulAut (projectiveSL 3 K)) (hγ : γ ∈ E), γ ^ 2 ∈ I →
        (QuotientGroup.mk ⟨γ, hγ⟩ : ↥E ⧸ D.subgroupOf E) ^ 2 = 1 := by
      intro γ hγ h2
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hID' (by simpa using h2)
    rcases eq_of_sq_eq_one_of_isCyclic (hbar α hαE hα2) (hbar β hβE hβ2) with h | h | h
    · rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
      exact Or.inl ((hmk1 α).mpr (hD2 α h hα2))
    · rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
      exact Or.inr (Or.inl ((hmk1 β).mpr (hD2 β h hβ2)))
    · rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      have hδ : α⁻¹ * β ∈ D := by simpa using h
      have hu' : (mk α)⁻¹ = mk α := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two]
        exact hu
      have hsq : mk ((α⁻¹ * β) ^ 2) = 1 := by
        rw [map_pow, map_mul, map_inv, hu']
        exact sq_mul_eq_one hu hv huv
      have h3 : α⁻¹ * β ∈ I := hD2 _ hδ ((hmk1 _).mp hsq)
      refine Or.inr (Or.inr ?_)
      have h4 : mk (α⁻¹ * β) = 1 := (hmk1 _).mpr h3
      rw [map_mul, map_inv, inv_mul_eq_one] at h4
      exact h4

theorem rankLeTwo_outer_l2 {F : Type} [Group F] (h : SmallL2 F) : RankLeTwo (Outer F) := by
  obtain ⟨p, f, K, _, _, hp, hpodd, hf, h3, hK, ⟨e⟩⟩ := soc_l2_data h
  exact rankLeTwo_outer_of_mulEquiv e
    (rankLeTwo_outer_psl2 K ⟨p, f, hp, hpodd, by omega, hK⟩ (by rw [hK]; exact h3))

theorem rankLeTwo_outer_l3 {F : Type} [Group F] (h : SmallL3Ne3 F) : RankLeTwo (Outer F) := by
  obtain ⟨p, f, -, -, -, -, hm⟩ := h
  obtain ⟨K, _, _, -, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (Or.inl ⟨by decide, hm⟩ : CFSG.Blueprint.LieModel F .PSL 3 p f)
  exact rankLeTwo_outer_of_mulEquiv e (rankLeTwo_outer_psl3 K)

theorem rankLeTwo_cent_l2 {Y : Type} [Group Y] {T : Subgroup Y} (hF : SmallL2 ↥T) {t : Y}
    (htT : t ∈ T) (ht : orderOf t = 2) :
    RankLeTwo ↥(T ⊓ Subgroup.centralizer ({t} : Set Y)) := by
  obtain ⟨p, f, K, _, _, hp, hpodd, hf, h3, hK, ⟨e⟩⟩ := soc_l2_data hF
  haveI : Fact p.Prime := ⟨hp⟩
  have ht' : orderOf (e ⟨t, htT⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact ht
  obtain ⟨m, hm, ⟨ψ⟩⟩ := soc_l2_centralizer_dihedral K hK hpodd hf h3 ht'
  haveI := hm
  have hmem : ∀ x : ↥(T ⊓ Subgroup.centralizer ({t} : Set Y)),
      e ⟨(x : Y), (Subgroup.mem_inf.mp x.2).1⟩ ∈
        Subgroup.centralizer ({e ⟨t, htT⟩} : Set (PSL2 K)) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
  let ι : ↥(T ⊓ Subgroup.centralizer ({t} : Set Y)) →*
      ↥(Subgroup.centralizer ({e ⟨t, htT⟩} : Set (PSL2 K))) :=
    { toFun := fun x => ⟨e ⟨(x : Y), (Subgroup.mem_inf.mp x.2).1⟩, hmem x⟩
      map_one' := Subtype.ext (by
        show e ⟨1, _⟩ = 1
        exact (congrArg e (Subtype.ext rfl : (⟨1, _⟩ : ↥T) = 1)).trans (map_one e))
      map_mul' := fun x y => Subtype.ext (by
        show e ⟨(x : Y) * y, _⟩ = e ⟨(x : Y), _⟩ * e ⟨(y : Y), _⟩
        rw [← map_mul]
        rfl) }
  have hι : Function.Injective ι := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    have h2 := e.injective h1
    have h3 : (x : Y) = y := congrArg (fun w : ↥T => (w : Y)) h2
    exact Subtype.ext h3
  exact RankLeTwo.of_injective (ψ.toMonoidHom.comp ι) (ψ.injective.comp hι)
    (rankLeTwo_dihedral m)

theorem rankLeTwo_cent_l3 {Y : Type} [Group Y] {T : Subgroup Y} (hF : SmallL3Ne3 ↥T) {t : Y}
    (htT : t ∈ T) (ht : orderOf t = 2) :
    RankLeTwo ↥(T ⊓ Subgroup.centralizer ({t} : Set Y)) := by
  obtain ⟨p, f, hp, hp2, hf, h3, -, K, hKf, hKfin, hK, ⟨e⟩⟩ := hF
  obtain ⟨hodd, -⟩ := Q5L5U5.five_le hp hp2 hf h3
  have hK' : Odd (Nat.card K) := by rw [hK]; exact hodd
  have h2 : (2 : K) ≠ 0 :=
    Ring.two_ne_zero (CFSG.GH74.Generic.S3.ringChar_ne_two_of_card_pow hp hp2 hK)
  let e0 : ↥T ≃* projectiveSL 3 K :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 K))
  obtain ⟨-, π, hπr, hk, -⟩ := Q5L3.exists_frame hK' e0 htT ht
  rw [← hπr]
  exact rankLeTwo_range_of_cubeKer h2 hk

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.R2
