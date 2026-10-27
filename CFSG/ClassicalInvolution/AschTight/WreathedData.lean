module

public import CFSG.ClassicalInvolution.AschTight.MuZ2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def L6_2ModTmp : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
        ∀ J ∈ Ω, J ∉ twinSet Ω K → ∀ t : G, IsUniqueInvolution J t →
          ∀ V : Subgroup G, IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set G)) → t ∈ V →
            (V = Subgroup.zpowers t ∧ conjSub t K ≠ K) ∨
            (V = Subgroup.zpowers t ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
              ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧
                IsSemidihedral (R ⊔ V)) ∨
            (V ∈ USet Ω ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
              ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧
                IsWreathed (R ⊔ V)) ∨
            (V ∈ RSet Ω ∧ ⁅V, K⁆ ≤ oddCoreOf K)

variable {p f}

variable {G : Type} [Group G]

theorem exists_conj_le_of_sylow_le [Finite G] (S : Sylow 2 G) {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) {W : Subgroup G} (hWH : W ≤ H) (hW : IsPGroup 2 W) :
    ∃ c ∈ H, conjSub c W ≤ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 H := S.subtype hSH
  have hW' : IsPGroup 2 (W.subgroupOf H) :=
    hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWH).symm
  obtain ⟨P, hP⟩ := hW'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P S'
  refine ⟨(g : G), g.2, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hwP : (⟨w, hWH hw⟩ : H) ∈ (P : Subgroup H) := hP hw
  have hmem : MulAut.conj g (⟨w, hWH hw⟩ : H) ∈ ((g • P : Sylow 2 H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hwP
  rw [hg] at hmem
  have hmem' : MulAut.conj g (⟨w, hWH hw⟩ : H) ∈ (S : Subgroup G).subgroupOf H := by
    rw [← Sylow.coe_subtype S hSH]
    exact hmem
  exact hmem'

variable [Finite G] {K : Subgroup G} {z : G}

theorem exists_data_of_not_allTypeTwo (h62 : L6_2ModTmp p f) [IsSimpleGroup G]
    (ht : S19R.TightStd p f K z) (hA : ¬ AllTypeTwo K z) (S : Sylow 2 G)
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ L ∈ CoreAssembly.conjClass K, ∃ t : G, IsUniqueInvolution L t ∧ t ≠ z ∧
      ∃ V ∈ USet (CoreAssembly.conjClass K), V ≤ (S : Subgroup G) ∧ t ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hΩ := hypOmegaMod_of_tightD ht
  have hNC := normalizer_eq_centralizer_of_tight htb
  simp only [AllTypeTwo, not_forall, not_le, exists_prop] at hA
  obtain ⟨J, hJ, u, w, hJu, ⟨x, hx⟩, hwu, hwuc, Q, hQ2, hQJ, hQw, hQ⟩ := hA
  set J₁ := conjSub x⁻¹ J with hJ₁
  set u₁ := x⁻¹ * u * x⁻¹⁻¹ with hu₁
  set Q₁ := conjSub x⁻¹ Q with hQ₁
  have hJ₁Ω : J₁ ∈ CoreAssembly.conjClass K := hΩ.conjInvariant x⁻¹ J hJ
  have hJ₁u : IsUniqueInvolution J₁ u₁ := hJu.conj x⁻¹
  have hQ₁J : Q₁ ≤ J₁ := conjSub_mono hQJ
  have hQ₁2 : IsPGroup 2 Q₁ := isPGroup_conjSub x⁻¹ hQ2
  have hQ₁card : 2 < Nat.card Q₁ := by
    rw [hQ₁, conjSub, ← Nat.card_congr (Subgroup.equivMapOfInjective Q _
      (MulAut.conj x⁻¹).injective).toEquiv]
    exact hQ
  have hQ₁z : Q₁ ≤ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqw := Subgroup.mem_centralizer_singleton_iff.mp (hQw hq)
    rw [← hx] at hqw
    change x⁻¹ * q * x⁻¹⁻¹ * z = z * (x⁻¹ * q * x⁻¹⁻¹)
    calc x⁻¹ * q * x⁻¹⁻¹ * z = x⁻¹ * (q * (x * z * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * z * x⁻¹ * q) * x := by rw [hqw]
      _ = z * (x⁻¹ * q * x⁻¹⁻¹) := by group
  have hu₁z : u₁ ≠ z := by
    intro h1
    apply hwu
    rw [← hx]
    calc x * z * x⁻¹ = x * u₁ * x⁻¹ := by rw [h1]
      _ = u := by rw [hu₁]; group
  have hu₁Q : u₁ ∈ Q₁ := by
    obtain ⟨k, hk⟩ := hQ₁2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk, pow_zero] at hQ₁card
      omega
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q₁) 2 (hk ▸ dvd_pow_self 2 hk0)
    have hq' : orderOf (q : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hq
    have hqq : (q : G) * q = 1 := by rw [← _root_.sq, ← hq', pow_orderOf_eq_one]
    have hq1 : (q : G) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hq'
      omega
    have := (hJ₁u.unique q (hQ₁J q.2) hqq).resolve_left hq1
    exact this ▸ q.2
  obtain ⟨V₁, hV₁, hQV₁⟩ := IsSylow2In.exists_ge hQ₁2 (le_inf hQ₁J hQ₁z)
  have hu₁V : u₁ ∈ V₁ := hQV₁ hu₁Q
  have htwin : J₁ ∉ twinSet (CoreAssembly.conjClass K) K := by
    rintro ⟨-, z', hz'K, hz'J⟩
    exact hu₁z ((hJ₁u.eq hz'J).trans (hI.eq hz'K).symm)
  have hV₁z : V₁ ≤ Subgroup.centralizer ({z} : Set G) := hV₁.1.trans inf_le_right
  have hV₁card : 2 < Nat.card V₁ := lt_of_lt_of_le hQ₁card (Subgroup.card_le_of_le hQV₁)
  have hzt2 : Nat.card (Subgroup.zpowers u₁) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [_root_.sq]; exact hJ₁u.sq) hJ₁u.ne_one
  have hV₁U : V₁ ∈ USet (CoreAssembly.conjClass K) := by
    rcases h62 ht.branch.odd ht.branch.five G _ hΩ K (CoreAssembly.mem_conjClass_self K) z hI J₁
        hJ₁Ω htwin u₁ hJ₁u V₁ hV₁ hu₁V with
      ⟨hV, -⟩ | ⟨hV, -⟩ | ⟨hV, -⟩ | ⟨hVR, -⟩
    · rw [hV, hzt2] at hV₁card; omega
    · rw [hV, hzt2] at hV₁card; omega
    · exact hV
    ·
      exfalso
      obtain ⟨J', hJ', P, hVP⟩ := hVR
      have hVJ' : V₁ ≤ J' := hVP ▸ Subgroup.map_subtype_le _
      by_cases hJK : J' = K
      · have hu₁K : u₁ ∈ K := hJK ▸ hVJ' hu₁V
        have hord : orderOf u₁ = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact hJ₁u.sq)
          hJ₁u.ne_one
        exact hu₁z ((uniqueInvolutionNormal_of_tight htb).2.2.1 u₁ hu₁K hord)
      · apply ht.edgeless K (CoreAssembly.mem_conjClass_self K) J' hJ'
        left
        refine ⟨hJ', hJK, V₁, ⟨J', hJ', P, hVP⟩, hVJ', ?_⟩
        rw [hNC]
        exact hV₁z
  obtain ⟨c, hc, hcV⟩ := exists_conj_le_of_sylow_le S hSz hV₁z hV₁.2.1
  refine ⟨conjSub c J₁, hΩ.conjInvariant c J₁ hJ₁Ω, c * u₁ * c⁻¹, hJ₁u.conj c, ?_,
    conjSub c V₁, USet.conj hΩ.conjInvariant hV₁U c, hcV, conj_mem_conjSub hu₁V⟩
  intro h1
  apply hu₁z
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  calc u₁ = c⁻¹ * (c * u₁ * c⁻¹) * c := by group
    _ = c⁻¹ * (z * c) := by rw [h1, mul_assoc]
    _ = z := by rw [← hcz]; group

end CFSG.ClassicalInvolution.Disconnected.AschTight
