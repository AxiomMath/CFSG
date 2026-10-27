module

public import CFSG.ClassicalInvolution.Asc77.AscE189Basic
public import CFSG.ClassicalInvolution.Asc77.AscE189SD
public import CFSG.ClassicalInvolution.Asc77.AscL62Main
public import CFSG.ClassicalInvolution.Asc77.AscSix610
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

section CaseA

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem isPGroup_zpowers_of_involution {t : G} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1

theorem E187C.e189_caseA_of
    (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    (hl62 : ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
      ∀ J ∈ Ω, J ∉ twinSet Ω K → ∀ t : G, IsUniqueInvolution J t →
        ∀ V : Subgroup G, IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set G)) → t ∈ V →
          (V = Subgroup.zpowers t ∧ conjSub t K ≠ K) ∨
          (V = Subgroup.zpowers t ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
            ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧
              IsSemidihedral (R ⊔ V)) ∨
          (V ∈ USet Ω ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
            ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧
              IsWreathed (R ⊔ V)) ∨
          (V ∈ RSet Ω ∧ ⁅V, K⁆ ≤ oddCoreOf K))
     {K J : Subgroup G}
    {z t : G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (htz : t ≠ z) (hzt : z * t = t * z)
    (hnorm : conjSub t K = K) : (∃ g : G, g * t * g⁻¹ = z * t) ∨ J ∈ KPerp Ω K := by
  have hJnt : J ∉ twinSet Ω K := by
    rintro ⟨-, z', hz', hz'J⟩
    exact htz ((ht.eq hz'J).trans (hz.eq hz').symm)
  have hKcent : ∀ w ∈ K, z * w = w * z := fun w hw => e189_commute_of_mem hz hw
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := fun w hw => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hKcent w hw).symm
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) := isPGroup_zpowers_of_involution ht.ne_one ht.sq
  have htle : Subgroup.zpowers t ≤ J ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact ⟨ht.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  obtain ⟨V, hV, htV⟩ := IsSylow2In.exists_ge ht2 htle
  have htVm : t ∈ V := htV (Subgroup.mem_zpowers t)
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  have hVC : V ≤ Subgroup.centralizer ({z} : Set G) := hV.1.trans inf_le_right
  rcases hl62 K hK z hz J hJ hJnt t ht V hV htVm with
    ⟨-, hne⟩ | ⟨hVeq, hVN, R₁, hR₁, hR₁K, hVR, hsd⟩ | ⟨hVU, hVN, R₁, hR₁, hR₁K, hVR, hwr⟩ |
    ⟨hVR, hcomm⟩
  · exact absurd hnorm hne
  ·
    left
    have hR₁2 : IsPGroup 2 R₁ := by
      obtain ⟨-, -, -, h, -⟩ := mem_RSet_iff.mp hR₁
      exact h
    have hV2 : IsPGroup 2 V := hVeq ▸ ht2
    have hP2 : IsPGroup 2 ↥(R₁ ⊔ V) := hR₁2.to_sup_of_normal_left' hV2 hVR
    have hzR : z ∈ R₁ := mem_of_isUniqueInvolution_of_isPGroup hz hR₁K hR₁2
      (by have := h8R hR₁; omega)
    have hzc : ∀ x ∈ R₁ ⊔ V, z * x = x * z := by
      have : R₁ ⊔ V ≤ Subgroup.centralizer ({z} : Set G) := sup_le (hR₁K.trans hKC) hVC
      intro x hx
      exact (Subgroup.mem_centralizer_singleton_iff.mp (this hx)).symm
    obtain ⟨g, -, hg⟩ := exists_conj_of_isSemidihedral hsd hP2 (Subgroup.mem_sup_left hzR) hz.sq
      hz.ne_one hzc (Subgroup.mem_sup_right htVm) ht.sq ht.ne_one htz
    exact ⟨g, hg⟩
  ·
    left
    have hR₁2 : IsPGroup 2 R₁ := by
      obtain ⟨-, -, -, h, -⟩ := mem_RSet_iff.mp hR₁
      exact h
    have hV2 : IsPGroup 2 V := hV.2.1
    have hP2 : IsPGroup 2 ↥(R₁ ⊔ V) := hR₁2.to_sup_of_normal_left' hV2 hVR
    have hzR : z ∈ R₁ := mem_of_isUniqueInvolution_of_isPGroup hz hR₁K hR₁2
      (by have := h8R hR₁; omega)
    have hzc : ∀ x ∈ R₁ ⊔ V, z * x = x * z := by
      have : R₁ ⊔ V ≤ Subgroup.centralizer ({z} : Set G) := sup_le (hR₁K.trans hKC) hVC
      intro x hx
      exact (Subgroup.mem_centralizer_singleton_iff.mp (this hx)).symm
    obtain ⟨g, -, hg⟩ := exists_conj_of_isWreathed hwr hP2 (Subgroup.mem_sup_left hzR) hz.sq
      hz.ne_one hzc (Subgroup.mem_sup_right htVm) ht.sq ht.ne_one htz
    exact ⟨g, hg⟩
  ·
    right
    have hJK : J ≠ K := by
      rintro rfl
      exact htz (hz.eq ht).symm
    refine Or.inr ⟨hJ, hJK, V, hVR, hVJ, fun v hv => ?_⟩
    exact le_normalizer_of_commutator_le_oddCoreOf hcomm hv

theorem e189_caseA (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G}
    {z t : G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (htz : t ≠ z) (hzt : z * t = t * z)
    (hnorm : conjSub t K = K) : (∃ g : G, g * t * g⁻¹ = z * t) ∨ J ∈ KPerp Ω K :=
  E187C.e189_caseA_of (fun hQ => hΩ.eight_le_of_mem_RSet hp hQ) (l6_2 p f hp hq G Ω hΩ) hK hJ hz ht
    htz hzt hnorm

end CaseA

end CFSG.ClassicalInvolution.Asc77
