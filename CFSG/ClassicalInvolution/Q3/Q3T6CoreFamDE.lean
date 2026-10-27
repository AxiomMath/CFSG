module

public import CFSG.ClassicalInvolution.Q3.Q3T6CoreFam
public import CFSG.ClassicalInvolution.AschTight.Sec6GenL62
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {C : Subgroup G} {z : G}

omit [Finite G] in
theorem centralizer_le_normalizer_conj (hN : Subgroup.centralizer ({z} : Set G) ≤
    Subgroup.normalizer (K : Set G)) (c : G) :
    Subgroup.centralizer ({c * z * c⁻¹} : Set G) ≤
      Subgroup.normalizer ((conjSub c K : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hg' : c⁻¹ * g * c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * g * c * z = c⁻¹ * (g * (c * z * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * z * c⁻¹) * g) * c := by rw [hg]
      _ = z * (c⁻¹ * g * c) := by group
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  have h1 : conjSub (c⁻¹ * g * c) K = K := conjSub_eq_of_mem_normalizer (hN hg')
  have e : conjSub g (conjSub c K) = conjSub c (conjSub (c⁻¹ * g * c) K) := by
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  rw [e, h1]

omit [Finite G] in
theorem conjSub_eq_of_conj_eq (hN : Subgroup.centralizer ({z} : Set G) ≤
    Subgroup.normalizer (K : Set G)) {a b : G} (h : a * z * a⁻¹ = b * z * b⁻¹) :
    conjSub a K = conjSub b K := by
  have hab : b⁻¹ * a ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc b⁻¹ * a * z = b⁻¹ * (a * z * a⁻¹) * a := by group
      _ = b⁻¹ * (b * z * b⁻¹) * a := by rw [h]
      _ = z * (b⁻¹ * a) := by group
  have h1 := conjSub_eq_of_mem_normalizer (hN hab)
  calc conjSub a K = conjSub (b * (b⁻¹ * a)) K := by rw [mul_inv_cancel_left]
    _ = conjSub b (conjSub (b⁻¹ * a) K) := conjSub_mul _ _ _
    _ = conjSub b K := by rw [h1]

theorem dEdgeless_conjFamily_sec (hK : Q3.IsClassicalMember3 K z)
    (hΩ : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K))
    (hDE : DEdgeless (CoreAssembly.conjClass K))
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G)) (hzC : z ∈ C)
    (hL : Q3.IsClassicalMember3 ((K ⊓ C).subgroupOf C) (⟨z, hzC⟩ : C)) :
    DEdgeless (conjFamily ((K ⊓ C).subgroupOf C)) := by
  have hI : IsUniqueInvolution K z :=
    (isClassicalMember3_iff_U.mp hK).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have hΩg : HypOmegaGen (CoreAssembly.conjClass K) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  have hΩΛ := hypOmegaModU_conjFamily_sec hK hΩ hzC hL
  have hΩΛg : HypOmegaGen (conjFamily ((K ⊓ C).subgroupOf C)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩΛ
  have key : ∀ M₁ ∈ conjFamily ((K ⊓ C).subgroupOf C), ∀ M₂ ∈ conjFamily ((K ⊓ C).subgroupOf C),
      M₂ ∉ omegaNbr (conjFamily ((K ⊓ C).subgroupOf C)) M₁ := by
    rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ ⟨-, hne, R, hR, hRle, hRN⟩
    have hq := Sec6Gen.isQuatSub_of_mem_RSet hΩΛg hR
    obtain ⟨x, hx, y, hy, hxy⟩ := hq.exists_not_commute
    have h8 := hq.eight_le
    have hR2 : IsPGroup 2 R := isPGroup_of_mem_rSet hR
    have hJne := conjSub_ne_of_ne_sec hne.symm
    set R' := R.map C.subtype with hR'
    have hR'2 : IsPGroup 2 R' := hR2.map _
    have hR'card : Nat.card R' = Nat.card R := Subgroup.card_map_of_injective C.subtype_injective
    have hR'K₂ : R' ≤ conjSub (c₂ : G) K := by
      rintro _ ⟨r, hr, rfl⟩
      exact le_conjSub_of_mem_sec c₂ (hRle hr)
    have hw : ((c₁ : ↥C) * (⟨z, hzC⟩ : ↥C) * (c₁ : ↥C)⁻¹) ∈
        conjSub c₁ ((K ⊓ C).subgroupOf C) := conj_mem_conjSub hL.mem
    have hRz : R' ≤ Subgroup.centralizer ({(c₁ : G) * z * (c₁ : G)⁻¹} : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := (Subgroup.mem_normalizer_iff.mp (hRN hr) _).mp hw
      have h2 : (r : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) * (r : G)⁻¹ ∈ conjSub (c₁ : G) K :=
        le_conjSub_of_mem_sec c₁ h1
      have h3 : ((r : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) * (r : G)⁻¹) *
          ((r : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) * (r : G)⁻¹) = 1 := by
        calc _ = (r : G) * (((c₁ : G) * z * (c₁ : G)⁻¹) * ((c₁ : G) * z * (c₁ : G)⁻¹)) *
              (r : G)⁻¹ := by group
          _ = 1 := by rw [(hI.conj (c₁ : G)).sq]; group
      rcases (hI.conj (c₁ : G)).unique _ h2 h3 with h | h
      · exfalso
        apply (hI.conj (c₁ : G)).ne_one
        calc (c₁ : G) * z * (c₁ : G)⁻¹ = (r : G)⁻¹ * ((r : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) *
            (r : G)⁻¹) * (r : G) := by group
          _ = 1 := by rw [h]; group
      · calc (r : G) * ((c₁ : G) * z * (c₁ : G)⁻¹)
            = (r : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) * (r : G)⁻¹ * (r : G) := by group
          _ = (c₁ : G) * z * (c₁ : G)⁻¹ * (r : G) := by rw [h]
    obtain ⟨V, hV, hRV⟩ := IsSylow2In.exists_ge hR'2 (le_inf hR'K₂ hRz)
    have hz₂R : (c₂ : G) * z * (c₂ : G)⁻¹ ∈ R' :=
      AscL62.mem_of_uniqueInvolution_of_pGroup (hI.conj (c₂ : G)) hR'K₂ hR'2 (by omega)
    have hz₂V : (c₂ : G) * z * (c₂ : G)⁻¹ ∈ V := hRV hz₂R
    have hzne : (c₁ : G) * z * (c₁ : G)⁻¹ ≠ (c₂ : G) * z * (c₂ : G)⁻¹ := fun h =>
      hJne (conjSub_eq_of_conj_eq hN h)
    have hK₁Ω : conjSub (c₁ : G) K ∈ CoreAssembly.conjClass K := ⟨(c₁ : G), rfl⟩
    have hK₂Ω : conjSub (c₂ : G) K ∈ CoreAssembly.conjClass K := ⟨(c₂ : G), rfl⟩
    have hcard : Nat.card R' ≤ Nat.card V := Subgroup.card_le_of_le hRV
    rcases Sec6Gen.Pair.six_two hΩg ⟨hK₁Ω, hK₂Ω, hI.conj (c₁ : G), hI.conj (c₂ : G), hzne⟩ hV
        hz₂V with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, -⟩
    · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact (hI.conj (c₂ : G)).sq)
        (hI.conj (c₂ : G)).ne_one] at hcard
      omega
    · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact (hI.conj (c₂ : G)).sq)
        (hI.conj (c₂ : G)).ne_one] at hcard
      omega
    · obtain ⟨-, -, -, hcyc, -⟩ := hV3
      exact hxy (Subtype.ext (commute_of_isCyclic hcyc (hRV ⟨x, hx, rfl⟩) (hRV ⟨y, hy, rfl⟩)))
    · exact hDE _ hK₁Ω _ hK₂Ω (Or.inl ⟨hK₂Ω, hJne.symm, V, hV4, hV.1.trans inf_le_left,
        (hV.1.trans inf_le_right).trans (centralizer_le_normalizer_conj hN (c₁ : G))⟩)
  intro M₁ hM₁ M₂ hM₂ hadj
  rcases hadj with h | h
  · exact key M₁ hM₁ M₂ hM₂ h
  · exact key M₂ hM₂ M₁ hM₁ h

end CFSG.ClassicalInvolution.Q3.Q3T6
