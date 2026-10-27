module

public import CFSG.ClassicalInvolution.SmallCases.NDBG7
import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
import CFSG.ClassicalInvolution.Asc77.WP3ChainVRank3
import CFSG.ClassicalInvolution.Asc77.WP3ChainVToral

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace NDBG

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem nbar_ne_zbar (C : Asc77.XCtx p f Ω z) {N : Subgroup G} (hN : N ∈ tqMembers Ω z) {n : G}
    (hn : IsClassicalMember p f N n) (hnz : n ≠ z) :
    oddQuotMk z ⟨n, C.involution_mem_centralizer hN hn⟩ ≠ oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ :=
  fun h => hnz (Asc77.eq_of_oddQuotMk_eq' (C.involution_mem_centralizer hN hn)
    (Asc77.XCtx.hzC z) hn.isCentralInvolution.sq C.hKz.sq
    (Subgroup.mem_centralizer_singleton_iff.mp (C.involution_mem_centralizer hN hn)) h)

theorem exists_range_eq (C : Asc77.XCtx p f Ω z) (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2)
    {N : Subgroup G} (hN : N ∈ tqMembers Ω z) :
    ∃ j : Fin C.D.card, modOdd z (exactCore z N) = (C.psi j).range := by
  obtain ⟨j, R, hR, hRN⟩ := C.exists_fund_of_mem hN
  refine ⟨j, ?_⟩
  rw [← hRN, C.fund_eq_top j (hall j) hR, Subgroup.map_top]

theorem nbar_eq_or_mul_eq (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) {N₁ N₂ : Subgroup G}
    (h₁ : N₁ ∈ tqMembers Ω z) (h₂ : N₂ ∈ tqMembers Ω z) {n₁ n₂ : G}
    (hn₁ : IsClassicalMember p f N₁ n₁) (hn₂ : IsClassicalMember p f N₂ n₂) (hz₁ : n₁ ≠ z)
    (hz₂ : n₂ ≠ z) :
    oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ =
        oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ ∨
      oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ *
          oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ =
        oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ := by
  obtain ⟨j₁, e₁⟩ := exists_range_eq C hall h₁
  obtain ⟨j₂, e₂⟩ := exists_range_eq C hall h₂
  by_cases hj : j₁ = j₂
  · subst hj
    left
    have u₁ := C.isUniqueInvolution_modOdd h₁ hn₁
    have u₂ := C.isUniqueInvolution_modOdd h₂ hn₂
    rw [e₁] at u₁
    rw [e₂] at u₂
    exact u₁.eq u₂
  · refine Cover.eq_or_mul_eq C hnoF h₁ h₂ hn₁ hn₂ ?_ (nbar_ne_zbar C h₁ hn₁ hz₁)
      (nbar_ne_zbar C h₂ hn₂ hz₂)
    rw [e₁, e₂]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact C.psi_commute hj a b

theorem nbar_mul_eq_of_ne (C : Asc77.XCtx p f Ω z)
    (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hnoT : ¬ ∃ T ∈ Ω, T ≠ C.K ∧ IsClassicalMember p f T z)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) {N₁ N₂ : Subgroup G}
    (h₁ : N₁ ∈ tqMembers Ω z) (h₂ : N₂ ∈ tqMembers Ω z) {n₁ n₂ : G}
    (hn₁ : IsClassicalMember p f N₁ n₁) (hn₂ : IsClassicalMember p f N₂ n₂) (hz₁ : n₁ ≠ z)
    (hz₂ : n₂ ≠ z) (hne : modOdd z (exactCore z N₁) ≠ modOdd z (exactCore z N₂)) :
    oddQuotMk z ⟨n₁, C.involution_mem_centralizer h₁ hn₁⟩ *
        oddQuotMk z ⟨n₂, C.involution_mem_centralizer h₂ hn₂⟩ =
      oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ :=
  (nbar_eq_or_mul_eq C hnoF hall h₁ h₂ hn₁ hn₂ hz₁ hz₂).resolve_left fun h =>
    hnoT (Cover.exists_twin_of_eq C htrans h₁ h₂ hn₁ hn₂ hne h)

theorem false_of_three_images (C : Asc77.XCtx p f Ω z)
    (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hnoT : ¬ ∃ T ∈ Ω, T ≠ C.K ∧ IsClassicalMember p f T z)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) {N₁ N₂ N₃ : Subgroup G}
    (h₁ : N₁ ∈ tqMembers Ω z) (h₂ : N₂ ∈ tqMembers Ω z) (h₃ : N₃ ∈ tqMembers Ω z)
    {n₁ n₂ n₃ : G} (hn₁ : IsClassicalMember p f N₁ n₁) (hn₂ : IsClassicalMember p f N₂ n₂)
    (hn₃ : IsClassicalMember p f N₃ n₃) (hz₁ : n₁ ≠ z) (hz₂ : n₂ ≠ z) (hz₃ : n₃ ≠ z)
    (h12 : modOdd z (exactCore z N₁) ≠ modOdd z (exactCore z N₂))
    (h13 : modOdd z (exactCore z N₁) ≠ modOdd z (exactCore z N₃))
    (h23 : modOdd z (exactCore z N₂) ≠ modOdd z (exactCore z N₃)) : False := by
  have e12 := nbar_mul_eq_of_ne C htrans hnoF hnoT hall h₁ h₂ hn₁ hn₂ hz₁ hz₂ h12
  have e13 := nbar_mul_eq_of_ne C htrans hnoF hnoT hall h₁ h₃ hn₁ hn₃ hz₁ hz₃ h13
  exact hnoT (Cover.exists_twin_of_eq C htrans h₂ h₃ hn₂ hn₃ h23
    (mul_left_cancel (e12.trans e13.symm)))

variable [IsSimpleGroup G] in
theorem exists_image_ne_of_twin (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hT : HasTwin p f K z) {N : Subgroup G}
    (hN : N ∈ tqMembers (𝒞 K) z) {n : G} (hn : IsClassicalMember p f N n) (hnz : n ≠ z) :
    ∃ N' ∈ tqMembers (𝒞 K) z, IsClassicalMember p f N' n ∧
      modOdd z (exactCore z N') ≠ modOdd z (exactCore z N) := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  obtain ⟨T, ⟨h, rfl⟩, hTK, hTz⟩ : ∃ T ∈ 𝒞 K, T ≠ K ∧ IsClassicalMember p f T z := hT
  obtain ⟨g, rfl⟩ := hN.1
  have hgz : n = g * z * g⁻¹ :=
    (hz.conj g).eq_of_isCentralInvolution hp2 hf hn.isCentralInvolution
  subst hgz
  have hT' : conjSub g (conjSub h K) ∈ 𝒞 K := ⟨g * h, conjSub_mul g h K⟩
  have hT'n : IsClassicalMember p f (conjSub g (conjSub h K)) (g * z * g⁻¹) := hTz.conj g
  have hT'tq := Cover.twin_mem_tq hnab hp2 hq hz hBelow hN hn hnz hT' hT'n
  refine ⟨_, hT'tq, hT'n, fun he => hTK ?_⟩
  have e := Cover.eq_of_modOdd_exactCore_eq hT'n hn
    (isPGroup_zpowers_of_sq_eq_one hz.isCentralInvolution.sq) hT'tq.2 hN.2 he
  have e' := congrArg (conjSub g⁻¹) e
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at e'

end NDBG

variable (p f : ℕ) [Fact p.Prime]

@[expose] def NoAllA1Narrow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → Disconnected.DConnected (𝒞 K) →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) →
      ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, (∀ i, D.tag i = .PSL ∧ D.rank i = 2) →
      ∀ N ∈ tqMembers (𝒞 K) z, ∀ n : G, IsClassicalMember p f N n → n ≠ z →
        (¬ HasTwin p f K z → (∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m →
          m ≠ z → modOdd z (exactCore z M) = modOdd z (exactCore z N)) → False) ∧
        (¬ HasTwin p f K z → ∀ N' ∈ tqMembers (𝒞 K) z, ∀ n' : G, IsClassicalMember p f N' n' →
          n' ≠ z → modOdd z (exactCore z N') ≠ modOdd z (exactCore z N) →
          (∃ (h : n ∈ Subgroup.centralizer ({z} : Set G))
            (h' : n' ∈ Subgroup.centralizer ({z} : Set G)),
            oddQuotMk z ⟨n, h⟩ * oddQuotMk z ⟨n', h'⟩ = oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩) →
          (∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m → m ≠ z →
            modOdd z (exactCore z M) = modOdd z (exactCore z N) ∨
              modOdd z (exactCore z M) = modOdd z (exactCore z N')) → False) ∧
        (HasTwin p f K z → ∀ N' ∈ tqMembers (𝒞 K) z, IsClassicalMember p f N' n →
          modOdd z (exactCore z N') ≠ modOdd z (exactCore z N) → False)

variable {p f}

theorem noAllA1Other_of_narrow (h : NoAllA1Narrow p f) : NoAllA1Other p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz
  obtain ⟨h₁, h₂, h₃⟩ := h G hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz
  by_cases hT : HasTwin p f K z
  · obtain ⟨N', hN', hN'n, hne⟩ :=
      NDBG.exists_image_ne_of_twin hnab hp2 hq hz hBelow hT hN hn hnz
    exact h₃ hT N' hN' hN'n hne
  by_cases hone : ∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m → m ≠ z →
      modOdd z (exactCore z M) = modOdd z (exactCore z N)
  · exact h₁ hT hone
  push Not at hone
  obtain ⟨N', hN', n', hn', hn'z, hne⟩ := hone
  set C := Cover.toXCtx hnab hp2 hq hz hBelow D
  have htrans : ∀ M ∈ 𝒞 K, ∃ g : G, conjSub g C.K = M := fun M hM => hM
  have hnoT : ¬ ∃ T ∈ 𝒞 K, T ≠ C.K ∧ IsClassicalMember p f T z := hT
  have hall' : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2 := hall
  refine h₂ hT N' hN' n' hn' hn'z hne ⟨C.involution_mem_centralizer hN hn,
    C.involution_mem_centralizer hN' hn',
    NDBG.nbar_mul_eq_of_ne C htrans hno hnoT hall' hN hN' hn hn' hnz hn'z (Ne.symm hne)⟩ ?_
  intro M hM m hm hmz
  by_contra hcon
  push Not at hcon
  exact NDBG.false_of_three_images C htrans hno hnoT hall' hN hN' hM hn hn' hm hnz hn'z hmz
    (Ne.symm hne) (Ne.symm hcon.1) (Ne.symm hcon.2)

theorem noAllA1Narrow_of_other (h : NoAllA1Other p f) : NoAllA1Narrow p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz
  have e := h G hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz
  exact ⟨fun _ _ => e, fun _ _ _ _ _ _ _ _ _ => e, fun _ _ _ _ _ => e⟩

theorem noAllA1_of_narrow (h : NoAllA1Narrow p f) : NoAllA1 p f :=
  noAllA1_of_core (noAllA1Core_of_other (noAllA1Other_of_narrow h))

theorem bootNoAllA1_of_narrow (h : NoAllA1Narrow p f) : Asc77.BSC.BootNoAllA1 p f :=
  bootNoAllA1_of_core (noAllA1Core_of_other (noAllA1Other_of_narrow h))

end CFSG.ClassicalInvolution.NDB
