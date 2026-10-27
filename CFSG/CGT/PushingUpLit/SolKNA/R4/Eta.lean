module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Data

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement Pointwise

section Data

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

namespace TightMemStdR

variable (ht : TightMemStdR r K z)
include ht

theorem exists_data_of_not_allTypeTwo (hA : ¬ AllTypeTwo K z) (S : Sylow 2 G)
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ L ∈ CoreAssembly.conjClass K, ∃ t : G, IsUniqueInvolution L t ∧ t ≠ z ∧
      ∃ V ∈ USet (CoreAssembly.conjClass K), V ≤ (S : Subgroup G) ∧ t ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI := ht.isUniqueInvolution
  have hΩ := ht.hypGen
  have hNC := ht.normEq
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
    rcases Sec6Gen.l6_2Gen G _ hΩ K (CoreAssembly.mem_conjClass_self K) z hI J₁ hJ₁Ω htwin u₁
        hJ₁u V₁ hV₁ hu₁V with
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
        exact hu₁z ((hI.unique u₁ hu₁K hJ₁u.sq).resolve_left hJ₁u.ne_one)
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

end TightMemStdR

namespace TightSylowDataR

variable {S : Sylow 2 G} {W : Subgroup G} (hd : TightSylowDataR r K z S W)
include hd

theorem exists_dataT :
    ∃ (L : Subgroup G) (t : G) (V : Subgroup G), TightSylowDataTR r K z S W L t V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hd.tight
  have hI := ht.isUniqueInvolution
  have hΩ := ht.hypGen
  have huniq : ∀ J ∈ CoreAssembly.conjClass K, IsUniqueInvolution J z → J = K := by
    intro J hJ hJz
    obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
    have h1 := (hI.conj g).eq hJz
    rw [ht.conjSub_eq_conjSub (a := g) (b := 1) (by rw [h1]; group)]
    exact conjSub_eq_self_of_mem K.one_mem
  have hinv : ∀ J ∈ CoreAssembly.conjClass K, ∃ u, IsUniqueInvolution J u := fun J hJ =>
    ht.exists_isUniqueInvolution_member hJ
  have h4 : ∀ U ∈ USet (CoreAssembly.conjClass K), ∀ J ∈ CoreAssembly.conjClass K, U ≤ J →
      ∀ u, IsUniqueInvolution J u → u ∈ U := by
    intro U hU J hJ hUJ u hu
    obtain ⟨R', hR', hUR', -, hidx⟩ := hU
    have h8 := ht.eight_le_natCard_rSet hR'
    have hcard : Nat.card R' = 2 * Nat.card U := by
      have h1 := Subgroup.relIndex_mul_card (H := U) (K := R')
      rw [inf_eq_left.mpr hUR', hidx] at h1
      exact h1.symm
    exact S1911.mem_of_le_member hu hUJ ((isPGroup_of_mem_rSet hR').to_le hUR') (by omega)
  obtain ⟨η, ⟨S', hηS', hinvη⟩, rfl⟩ := hd.hW
  have hex : ∃ U ∈ η, ¬ U ≤ K := by
    by_contra hcon
    push Not at hcon
    have hle1 : η.ncard ≤ 1 := by
      rw [Set.ncard_le_one]
      intro U hU U' hU'
      by_contra hne
      exact hηS'.2.1 U hU U' hU' hne K (CoreAssembly.mem_conjClass_self K)
        ⟨hcon U hU, hcon U' hU'⟩
    obtain ⟨Q₀, hQ₀S⟩ := hd.sylow
    have hR : (Q₀ : Subgroup K).map K.subtype ∈ RSet (CoreAssembly.conjClass K) :=
      ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩
    obtain ⟨J₀, hJ₀, hRJ₀, hR2, hmax⟩ := mem_RSet_iff.mp
      (show (Q₀ : Subgroup K).map K.subtype ∈ RSet ({K} : Set (Subgroup G)) from
        ⟨K, rfl, Q₀, rfl⟩)
    rw [Set.mem_singleton_iff] at hJ₀
    have hRsyl : IsSylow2In ((Q₀ : Subgroup K).map K.subtype) K := by
      have h : IsSylow2In ((Q₀ : Subgroup K).map K.subtype) J₀ := ⟨hRJ₀, hR2, hmax⟩
      rwa [hJ₀] at h
    obtain ⟨U₀, hU₀R, hU₀c, hU₀card⟩ :=
      (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_cyclic_index_two
    have hU₀ : U₀ ∈ USet (CoreAssembly.conjClass K) :=
      mem_USet_of_natCard (CoreAssembly.mem_conjClass_self K) hRsyl hU₀R hU₀c hU₀card
    have hzU₀ : z ∈ U₀ := h4 U₀ hU₀ K (CoreAssembly.mem_conjClass_self K)
      (hU₀R.trans (Subgroup.map_subtype_le _)) z hI
    obtain ⟨L₁, hL₁, t₁, hL₁t, ht₁z, V₁, hV₁, hV₁S, ht₁V⟩ :=
      ht.exists_data_of_not_allTypeTwo hd.mu S hd.hSz
    have ht₁K : t₁ ∉ K := fun h => ht₁z ((hI.unique t₁ h hL₁t.sq).resolve_left hL₁t.ne_one)
    have hdist : ∀ J ∈ CoreAssembly.conjClass K, ¬ (U₀ ≤ J ∧ V₁ ≤ J) := by
      rintro J hJ ⟨hU₀J, hV₁J⟩
      obtain ⟨u, hu⟩ := hinv J hJ
      have hzJ : z = u := (hu.unique z (hU₀J hzU₀) hI.sq).resolve_left hI.ne_one
      have hJK : J = K := huniq J hJ (hzJ ▸ hu)
      exact ht₁K (hJK ▸ hV₁J ht₁V)
    have hne : U₀ ≠ V₁ := fun h => ht₁K ((hU₀R.trans (Subgroup.map_subtype_le _)) (h ▸ ht₁V))
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
    have hconjS : ∀ A : Subgroup G, A ≤ (S : Subgroup G) → conjSub g A ≤ (S' : Subgroup G) := by
      rintro A hA _ ⟨a, ha, rfl⟩
      have h1 : (MulAut.conj g) • a ∈ (MulAut.conj g) • (S : Subgroup G) :=
        Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) _ (hA ha)
      rw [← Sylow.coe_subgroup_smul, hg] at h1
      exact h1
    have hinj : ∀ A B : Subgroup G, conjSub g A = conjSub g B → A = B := by
      intro A B h
      have h1 := congrArg (conjSub g⁻¹) h
      rwa [← conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_one] at h1
    have hsub : ({conjSub g U₀, conjSub g V₁} : Set (Subgroup G)) ⊆
        {U | U ∈ USet (CoreAssembly.conjClass K) ∧ U ≤ (S' : Subgroup G)} := by
      rintro U (rfl | rfl)
      · exact ⟨USet.conj hΩ.conjInvariant hU₀ g, hconjS _ (hU₀R.trans hQ₀S)⟩
      · exact ⟨USet.conj hΩ.conjInvariant hV₁ g, hconjS _ hV₁S⟩
    have hdist' : InDistinctMembers (CoreAssembly.conjClass K)
        ({conjSub g U₀, conjSub g V₁} : Set (Subgroup G)) := by
      have key : ∀ J ∈ CoreAssembly.conjClass K, ¬ (conjSub g U₀ ≤ J ∧ conjSub g V₁ ≤ J) := by
        rintro J hJ ⟨h1, h2⟩
        refine hdist (conjSub g⁻¹ J) (hΩ.conjInvariant g⁻¹ J hJ) ⟨?_, ?_⟩
        · intro x hx
          rw [mem_conjSub_iff, inv_inv]
          exact h1 (conj_mem_conjSub hx)
        · intro x hx
          rw [mem_conjSub_iff, inv_inv]
          exact h2 (conj_mem_conjSub hx)
      rintro U (rfl | rfl) U' (rfl | rfl) hUU' J hJ
      · exact absurd rfl hUU'
      · exact key J hJ
      · exact fun h => key J hJ ⟨h.2, h.1⟩
      · exact absurd rfl hUU'
    have h2 := hηS'.2.2 _ hsub hdist'
    rw [Set.ncard_pair (fun h => hne (hinj _ _ h))] at h2
    omega
  obtain ⟨U, hUη, hUK⟩ := hex
  have hU := (hηS'.1 hUη).1
  obtain ⟨R', hR', hUR', hUc, hUidx⟩ := id hU
  obtain ⟨J, hJ, P, hR'P⟩ := hR'
  have hUJ : U ≤ J := hUR'.trans (hR'P ▸ Subgroup.map_subtype_le _)
  obtain ⟨u, hu⟩ := hinv J hJ
  have huz : u ≠ z := by
    intro h
    exact hUK (huniq J hJ (h ▸ hu) ▸ hUJ)
  exact ⟨J, u, U, ⟨hd, hJ, hu, huz, hU,
    le_iSup₂ (f := fun (V : Subgroup G) (_ : V ∈ η) => V) U hUη, h4 U hU J hJ hUJ u hu⟩⟩

end TightSylowDataR

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem le_member : V ≤ L := by
  have hΩ := hd.tight.hypGen
  obtain ⟨J, hJ, hVJ⟩ := Sec6Gen.exists_member_of_mem_USet hΩ hd.memV
  obtain ⟨u, hu⟩ := hd.tight.exists_isUniqueInvolution_member hJ
  have htu : t = u := S1911.eq_of_mem_member hu hVJ hd.memT hd.invL.sq hd.invL.ne_one
  rw [hd.tight.eq_of_isUniqueInvolution_member hd.memL hJ hd.invL (htu ▸ hu)]
  exact hVJ

theorem mem_W : t ∈ W := hd.leW hd.memT

end TightSylowDataTR

namespace TightSylowDataR

variable {W : Subgroup G} (hd : TightSylowDataR r K z S W)
include hd

theorem not_mem_centralizer_inf_of_member {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    (hJK : J ≠ K) {u : G} (hu : IsUniqueInvolution J u) :
    u ∉ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  intro hC
  refine hd.tight.not_le_centralizer_of_mem_rSet (CoreAssembly.mem_conjClass_self K) hJ
    (Ne.symm hJK) hu hd.inf_mem_rSet inf_le_right ?_
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hC r hr

theorem card_inf_eq : Nat.card ↥((S : Subgroup G) ⊓ K) = 2 * Nat.card ↥(K ⊓ W) := by
  have hΩ := hd.tight.hypGen
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := hd.exists_eta
  have hU : K ⊓ W ∈ USet (CoreAssembly.conjClass K) :=
    (hη.1 (hd.inf_mem_eta hη hinv hWη hηS)).1
  obtain ⟨R', -, J, hJ, hR'J, hUR', -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hJK : J = K := Sec6Gen.eq_of_mem_USet hΩ hU hJ (CoreAssembly.mem_conjClass_self K)
    (hUR'.trans hR'J.1) inf_le_left
  subst hJK
  rw [hd.isSylow2In_inf.natCard_eq hR'J, hcard]

theorem le_centralizer_of_mem {u : G} (hu : u ∈ W) : W ≤ Subgroup.centralizer ({u} : Set G) :=
  fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hd.comm_of_mem w hw u hu)

theorem mul_mem_centralizer_inf {J₁ J₂ : Subgroup G} (h₁ : J₁ ∈ CoreAssembly.conjClass K)
    (h₂ : J₂ ∈ CoreAssembly.conjClass K) (h₁K : J₁ ≠ K) (h₂K : J₂ ≠ K) {u₁ u₂ : G}
    (hu₁ : IsUniqueInvolution J₁ u₁) (hu₂ : IsUniqueInvolution J₂ u₂) (hu₁W : u₁ ∈ W)
    (hu₂W : u₂ ∈ W) :
    u₁ * u₂ ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hI := hd.tight.isUniqueInvolution
  have hcomm := hd.comm_of_mem
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hUz : ∀ x ∈ K ⊓ W, x * x = 1 → x = 1 ∨ x = z := fun x hx hx2 => hI.unique x hx.1 hx2
  have hN : ∀ x ∈ W, x ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    fun x hx => hd.le_normalizer_inf (hd.hWS hx)
  have hC : ∀ x ∈ W, ∀ y ∈ K ⊓ W, x * y = y * x := fun x hx y hy => hcomm x hx y hy.2
  have hsq : ∀ u : G, u * u = 1 →
      u * u ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    intro u hu
    rw [hu]
    exact Subgroup.one_mem _
  exact S1911.mul_mem_centralizer_of_not_mem hUR hd.card_inf_eq hUz (hN u₁ hu₁W) (hN u₂ hu₂W)
    (hC u₁ hu₁W) (hC u₂ hu₂W) (hsq u₁ hu₁.sq) (hsq u₂ hu₂.sq)
    (hd.not_mem_centralizer_inf_of_member h₁ h₁K hu₁)
    (hd.not_mem_centralizer_inf_of_member h₂ h₂K hu₂)

end TightSylowDataR

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem invol_eq_or {η : Set (Subgroup G)} {S' : Sylow 2 G}
    (hη : η ∈ etaSet (CoreAssembly.conjClass K) S')
    (hinv : ∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) (hWη : W = ⨆ U ∈ η, U)
    {A : Subgroup G} (hA : A ∈ η) {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    (hAJ : A ≤ J) {u : G} (hu : IsUniqueInvolution J u) : u = z ∨ u = t ∨ u = t * z := by
  have hd0 := hd.toTightSylowDataR
  have hΩ := hd.tight.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hcomm := hd0.comm_of_mem
  have hAU : A ∈ USet (CoreAssembly.conjClass K) := (hη.1 hA).1
  have hAW : A ≤ W := hWη ▸ le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ η) => B) A hA
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hAU
  have huW : u ∈ W :=
    hAW (S1911.mem_of_le_member hu hAJ (Sec6Gen.isPGroup_of_mem_USet hΩ hAU) (by omega))
  by_contra hcon
  push Not at hcon
  obtain ⟨huz, hut, hutz⟩ := hcon
  have hJK : J ≠ K := fun h => huz ((h ▸ hu).eq hI)
  have hJL : J ≠ L := fun h => hut ((h ▸ hu).eq hd.invL)
  have htW := hd.mem_W
  have hWL : W ≤ Subgroup.normalizer (L : Set G) :=
    (hd0.le_centralizer_of_mem htW).trans
      (hd.tight.centralizer_le_normalizer_member hd.memL hd.invL)
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hd.hWS
  obtain ⟨R₁, hR₁, hR₁W⟩ := exists_sylow_normalized hW2 hWL
  have hR₁mem : R₁ ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hd.memL hR₁
  have hWR₁ : W ≤ Subgroup.normalizer (R₁ : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₁W w hw)
  obtain ⟨S₁, hS₁⟩ := (IsPGroup.to_sup_of_normal_right' hW2 hR₁.2.1 hWR₁).exists_le_sylow
  have hηS₁ : ∀ B ∈ η, B ≤ (S₁ : Subgroup G) := fun B hB =>
    ((hWη ▸ le_iSup₂ (f := fun (C : Subgroup G) (_ : C ∈ η) => C) B hB : B ≤ W).trans
      le_sup_left).trans hS₁
  have hxW : ∀ x ∈ R₁, conjSub x W = W := fun x hx => by
    rw [hWη]
    exact S1911.conjSub_iSup_eq
      (hd0.conjSub_mem_eta hη hinv hηS₁ hR₁mem (le_sup_right.trans hS₁) hx)
  have hdich : ∀ x ∈ R₁, x * u * x⁻¹ * u⁻¹ = 1 ∨ x * u * x⁻¹ * u⁻¹ = t := by
    intro x hx
    have hxu : x * u * x⁻¹ ∈ W := (hxW x hx) ▸ conj_mem_conjSub huW
    exact S1911.conj_mul_inv_eq_or hd.invL (hR₁.1 hx) (hWL huW) hu.sq (hcomm _ hxu u huW)
  by_cases hall : ∀ x ∈ R₁, x * u * x⁻¹ * u⁻¹ = 1
  · refine hd.tight.not_le_centralizer_of_mem_rSet hd.memL hJ (Ne.symm hJL) hu hR₁mem hR₁.1 ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hall x hx
    calc x * u = x * u * x⁻¹ * u⁻¹ * (u * x) := by group
      _ = u * x := by rw [h1, one_mul]
  push Not at hall
  obtain ⟨x, hx, hx1⟩ := hall
  have hxt : x * u * x⁻¹ = t * u := by
    have h1 := (hdich x hx).resolve_left hx1
    calc x * u * x⁻¹ = x * u * x⁻¹ * u⁻¹ * u := by group
      _ = t * u := by rw [h1]
  have hJ' : conjSub x J ∈ CoreAssembly.conjClass K := hΩ.conjInvariant x J hJ
  have hu' : IsUniqueInvolution (conjSub x J) (t * u) := hxt ▸ hu.conj x
  have hJ'K : conjSub x J ≠ K := by
    intro h
    apply hutz
    have h1 : t * u = z := (h ▸ hu').eq hI
    have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right hd.invL.sq
    calc u = t⁻¹ * (t * u) := by group
      _ = t * z := by rw [h1, htt]
  exact hd0.not_mem_centralizer_inf_of_member hJ' hJ'K hu'
    (hd0.mul_mem_centralizer_inf hd.memL hJ hd.member_ne hJK hd.invL hu htW huW)

end TightSylowDataTR

namespace TightSylowDataR

variable {W : Subgroup G} (hd : TightSylowDataR r K z S W)
include hd

theorem conjSub_eq_of_mem_inf {r : G} (hr : r ∈ (S : Subgroup G) ⊓ K) : conjSub r W = W := by
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := hd.exists_eta
  rw [hWη]
  exact S1911.conjSub_iSup_eq (hd.conjSub_mem_eta hη hinv hηS hd.inf_mem_rSet inf_le_left hr)

theorem mem_normalizer_of_mem_W {u : G} (hu : u ∈ W) : u ∈ Subgroup.normalizer (K : Set G) :=
  hd.hSN (hd.hWS hu)

end TightSylowDataR

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem exists_conj_eq_mul : ∃ r ∈ (S : Subgroup G) ⊓ K, r * t * r⁻¹ = t * z := by
  have hd0 := hd.toTightSylowDataR
  have hI := hd.tight.isUniqueInvolution
  have htW := hd.mem_W
  have hdich : ∀ r ∈ (S : Subgroup G) ⊓ K, r * t * r⁻¹ * t⁻¹ = 1 ∨ r * t * r⁻¹ * t⁻¹ = z := by
    intro r hr
    have hrt : r * t * r⁻¹ ∈ W := (hd0.conjSub_eq_of_mem_inf hr) ▸ conj_mem_conjSub htW
    exact S1911.conj_mul_inv_eq_or hI hr.2 (hd0.mem_normalizer_of_mem_W htW) hd.invL.sq
      (hd0.comm_of_mem _ hrt t htW)
  by_cases hall : ∀ r ∈ (S : Subgroup G) ⊓ K, r * t * r⁻¹ * t⁻¹ = 1
  · exfalso
    refine hd.tight.not_le_centralizer_of_mem_rSet (CoreAssembly.mem_conjClass_self K) hd.memL
      hd.member_ne.symm hd.invL hd0.inf_mem_rSet inf_le_right ?_
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hall r hr
    calc r * t = r * t * r⁻¹ * t⁻¹ * (t * r) := by group
      _ = t * r := by rw [h1, one_mul]
  push Not at hall
  obtain ⟨r, hr, hr1⟩ := hall
  refine ⟨r, hr, ?_⟩
  have h1 := (hdich r hr).resolve_left hr1
  have hzt : t * z = z * t :=
    Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz (hd.hWS htW))
  calc r * t * r⁻¹ = r * t * r⁻¹ * t⁻¹ * t := by group
    _ = t * z := by rw [h1, hzt]

theorem conjSub_le_inf_sup {r : G} (hr : r ∈ (S : Subgroup G) ⊓ K) :
    conjSub r V ≤ (K ⊓ W) ⊔ V := by
  have hd0 := hd.toTightSylowDataR
  intro y hy
  have hv : r⁻¹ * y * r ∈ V := mem_conjSub_iff.mp hy
  obtain ⟨v, hvV, hvy⟩ : ∃ v ∈ V, r⁻¹ * y * r = v := ⟨_, hv, rfl⟩
  have hvW : v ∈ W := hd.leW hvV
  have hy' : y = (r * v * r⁻¹ * v⁻¹) * v := by rw [← hvy]; group
  have hc : r * v * r⁻¹ * v⁻¹ ∈ K ⊓ W := by
    refine ⟨?_, ?_⟩
    · have h1 : v * r⁻¹ * v⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hd0.mem_normalizer_of_mem_W hvW) _).mp
          (K.inv_mem hr.2)
      have e : r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) := by group
      rw [e]
      exact K.mul_mem hr.2 h1
    · have h1 : r * v * r⁻¹ ∈ W := (hd0.conjSub_eq_of_mem_inf hr) ▸ conj_mem_conjSub hvW
      exact W.mul_mem h1 (W.inv_mem hvW)
  rw [hy']
  exact Subgroup.mul_mem_sup hc hvV

theorem sup_eq_inf_sup : W = (K ⊓ W) ⊔ V := by
  have hd0 := hd.toTightSylowDataR
  have hΩ := hd.tight.hypGen
  have hI := hd.tight.isUniqueInvolution
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := hd0.exists_eta
  have hVη : V ∈ η := hd0.mem_eta_of_le hη hinv hWη hd.memV hd.leW
  refine le_antisymm ?_ (sup_le inf_le_right hd.leW)
  have hW' : W ≤ (K ⊓ W) ⊔ V := by
    conv_lhs => rw [hWη]
    refine iSup₂_le fun A hA => ?_
    have hAW : A ≤ W := hWη ▸ le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ η) => B) A hA
    obtain ⟨J, hJ, hAJ⟩ := Sec6Gen.exists_member_of_mem_USet hΩ (hη.1 hA).1
    obtain ⟨u, hu⟩ := hd.tight.exists_isUniqueInvolution_member hJ
    rcases hd.invol_eq_or hη hinv hWη hA hJ hAJ hu with rfl | rfl | rfl
    · have hJK : J = K :=
        hd.tight.eq_of_isUniqueInvolution_member hJ (CoreAssembly.mem_conjClass_self K) hu hI
      exact le_sup_of_le_left (le_inf (hJK ▸ hAJ) hAW)
    · have hJL : J = L := hd.tight.eq_of_isUniqueInvolution_member hJ hd.memL hu hd.invL
      by_cases hAV : A = V
      · exact hAV ▸ le_sup_right
      · exact absurd ⟨hJL ▸ hAJ, hd.le_member⟩ (hη.2.1 A hA V hVη hAV L hd.memL)
    · obtain ⟨r, hr, hrt⟩ := hd.exists_conj_eq_mul
      have hrV : conjSub r V ∈ η :=
        hd0.conjSub_mem_eta hη hinv hηS hd0.inf_mem_rSet inf_le_left hr V hVη
      have hrL : IsUniqueInvolution (conjSub r L) (t * z) := hrt ▸ hd.invL.conj r
      have hJr : J = conjSub r L :=
        hd.tight.eq_of_isUniqueInvolution_member hJ (hΩ.conjInvariant r L hd.memL) hu hrL
      by_cases hAr : A = conjSub r V
      · rw [hAr]
        exact hd.conjSub_le_inf_sup hr
      · exact absurd ⟨hAJ, hJr ▸ conjSub_mono hd.le_member⟩ (hη.2.1 A hA _ hrV hAr J hJ)
  exact hW'

theorem inf_inf_eq_bot : K ⊓ W ⊓ V = ⊥ := by
  have hodd := hd.tight.odd_card_inf (CoreAssembly.mem_conjClass_self K) hd.memL
    hd.member_ne.symm
  rw [eq_bot_iff]
  intro x hx
  have hxKL : x ∈ K ⊓ L := ⟨hx.1.1, hd.le_member hx.2⟩
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    (S.isPGroup'.to_le hd.hWS).to_le (Subgroup.zpowers_le.mpr hx.1.2)
  exact Subgroup.mem_bot.mpr (eq_one_of_isPGroup_of_mem_odd hodd hxKL hx2)

theorem card_inf_eq_card : Nat.card ↥(K ⊓ W) = Nat.card V := by
  have hd0 := hd.toTightSylowDataR
  have hΩ := hd.tight.hypGen
  obtain ⟨R', -, J, hJ, hR'J, hVR', -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hd.memV
  have h1 := Sec6Gen.natCard_isSylow2In_eq hΩ (CoreAssembly.mem_conjClass_self K) hJ
    hd0.isSylow2In_inf hR'J
  have h3 := hd0.card_inf_eq
  omega

theorem card_eq_mul : Nat.card W = Nat.card ↥(K ⊓ W) * Nat.card V := by
  conv_lhs => rw [hd.sup_eq_inf_sup]
  refine S1911.card_sup_of_comm
    (fun a ha b hb => hd.comm_of_mem a ha.2 b (hd.leW hb)) ?_
  exact hd.inf_inf_eq_bot

end TightSylowDataTR

end Data

end CFSG.CGT.PushingUpLit.SolKNA.R4
