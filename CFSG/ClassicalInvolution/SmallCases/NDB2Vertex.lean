module

public import CFSG.ClassicalInvolution.SmallCases.NDB2Alpha
public import CFSG.ClassicalInvolution.SmallCases.NDB1Main
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpMain
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

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.StrongBalance CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

namespace Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_four {t : G} (h : t ^ 4 = 1) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  have h4 : orderOf t ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num [h])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem mem_exactCore_of_isPGroup {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {c : G} (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {N : Subgroup G}
    (hN : N ∈ tqMembers Ω c) {t : G} (htN : t ∈ N) (htc : t * c = c * t)
    (ht2 : IsPGroup 2 (Subgroup.zpowers t)) : t ∈ exactCore c N := by
  obtain ⟨R, hR, hRc⟩ := (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2 hN.1).mp hN.2
  obtain ⟨V, hV, htV⟩ := Asc77.IsSylow2In.exists_ge ht2 (Subgroup.zpowers_le.mpr
    (Subgroup.mem_inf.mpr ⟨htN, Subgroup.mem_centralizer_singleton_iff.mpr htc⟩))
  have hRV : Nat.card R ≤ Nat.card V := hV.natCard_le hR.2.1 (le_inf hR.1 hRc)
  have hVN : Asc77.IsSylow2In V N := hR.of_natCard_le hV.2.1 (hV.1.trans inf_le_left) hRV
  have hVX : Asc77.IsSylow2In V (exactCore c N) :=
    (isSylow2In_exactCore_iff hΩ hc2 hN.1 hN.2).mpr ⟨hVN, hV.1.trans inf_le_right⟩
  exact hVX.1 (htV (Subgroup.mem_zpowers t))

end Vertex

section Shape

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_pspVertex {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (hsh : PSpShape p f Ω z) :
    ∃ (D : LocalLieSystemAt p f (exactFamily Ω z) z) (i₀ i₁ : Fin D.card),
      D.card = 2 ∧ i₀ ≠ i₁ ∧ D.tag i₁ = .PSp ∧ D.rank i₁ = 2 ∧
      modOdd z K = (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₀).range ∧
      Function.Injective (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₁) ∧
      (∀ a ∈ (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₀).range,
        ∀ b ∈ (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₁).range,
          a * b = b * a) ∧
      ∀ N ∈ tqMembers Ω z, ∀ w : G, IsClassicalMember p f N w →
        ∀ hw : w ∈ Subgroup.centralizer ({z} : Set G),
          oddQuotMk z ⟨w, hw⟩ ≠ oddQuotMk z ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ →
            ∃ R ∈ fundamentalSubgroups (D.tag i₁) (compModel D i₁).D,
              R.map (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₁) =
                modOdd z (exactCore z N) := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁, x, hx1, hx₀, hx₁⟩ := hsh
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz
  let C : XCtx p f Ω z := { K := K, hK := hK, hKz := hKz, hΩ := hΩ, hp := hp, hq := hq, D := D }
  have h4 : 4 ≤ p ^ D.exp i₁ := C.four_le i₁ (by rw [ht₁]; decide)
  obtain ⟨R₂, R₃, τ₂, τ₃, hP⟩ := exists_pspPair_model hp (D.tag i₁) (D.rank i₁) (D.exp i₁) ht₁
    hr₁ (D.admissible i₁) h4
  have := hP.perfect
  obtain ⟨j₀, hj₀, hKimg⟩ := C.exists_A1_of_K
  have hj₀ne : j₀ ≠ i₁ := by
    rintro rfl
    rw [ht₁] at hj₀
    exact absurd hj₀.1 (by decide)
  have hj₀i₀ : j₀ = i₀ := (Seed.eq_or_eq_of_card_two hcard hne j₀).resolve_right hj₀ne
  have hexK : exactCore z K = K := C.exactCore_K
  have hKbar : modOdd z K = (C.psi i₀).range := by
    rw [← hj₀i₀, ← hKimg, hexK]
  have hθinj := sectionQuotientHom_injective C.hs.normalizes
  set x' := sectionQuotientHom C.hs.normalizes x with hx'
  have hx'1 : x' ≠ 1 := fun h => hx1 (hθinj (h.trans (map_one _).symm))
  have hx'₀ : x' ∈ (C.psi i₀).range := by
    obtain ⟨a, ha⟩ := hx₀
    refine ⟨a, ?_⟩
    show sectionQuotientHom C.hs.normalizes (D.hom i₀ a) = x'
    rw [ha]
  have hx'₁ : x' ∈ (C.psi i₁).range := by
    obtain ⟨a, ha⟩ := hx₁
    refine ⟨a, ?_⟩
    show sectionQuotientHom C.hs.normalizes (D.hom i₁ a) = x'
    rw [ha]
  have hcomm : ∀ y ∈ (C.psi i₁).range, x' * y = y * x' := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := hx'₀
    rw [← ha]
    exact C.psi_commute hne a b
  obtain ⟨ε, hε, hεx⟩ := Seed.exists_central_lift (C.psi i₁) (C.psi_ker i₁) hx'₁ hcomm
  have hετ : ε = τ₂ * τ₃ :=
    (hP.center ε hε).resolve_left fun h => hx'1 (by rw [← hεx, h, map_one])
  have hinj : Function.Injective (C.psi i₁) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rcases hP.center k (C.psi_ker i₁ (MonoidHom.mem_ker.mpr hk)) with h | h
    · exact h
    · exact absurd (by rw [← hεx, hετ, ← h, hk]) hx'1
  refine ⟨D, i₀, i₁, hcard, hne, ht₁, hr₁, hKbar, hinj, fun a ha b hb => ?_,
    fun N hN w hw hwC hwz => ?_⟩
  · obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact C.psi_commute hne a' b'
  · obtain ⟨j, R, hR, hRimg⟩ := C.exists_fund_of_mem hN
    rcases Seed.eq_or_eq_of_card_two hcard hne j with rfl | rfl
    · exfalso
      have hR1 : R = ⊤ := C.fund_eq_top j ⟨ht₀, hr₀⟩ hR
      have hU := C.isUniqueInvolution_modOdd C.K_tq C.K_cl
      have hwc := isCentralInvolution_of_isClassicalMember hw
      have hwmem : oddQuotMk z ⟨w, hwC⟩ ∈ modOdd z (exactCore z C.K) := by
        have h1 : oddQuotMk z ⟨w, hwC⟩ ∈ modOdd z (exactCore z N) :=
          oddQuotMk_mem_modOdd (mem_exactCore hw C.hc2 hN.2) hwC
        rw [← hRimg, hR1, Subgroup.map_top] at h1
        show oddQuotMk z ⟨w, hwC⟩ ∈ modOdd z (exactCore z K)
        rw [hexK, hKbar]
        exact h1
      have hw2 : (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨w, hwC⟩ = 1 :=
        Subtype.ext hwc.sq
      have hwsq : oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨w, hwC⟩ = 1 := by
        rw [← map_mul, hw2, map_one]
      have hw1 : oddQuotMk z ⟨w, hwC⟩ ≠ 1 := fun h =>
        hwc.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hw2 h))
      exact hwz ((hU.unique _ hwmem hwsq).resolve_left hw1)
    · exact ⟨R, hR, hRimg⟩

end Shape

section Axis

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem hyp51At_axis_vertex {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hBelow : CITBelowU p f (Nat.card G)) {K₁ K₂ K₃ : Subgroup G}
    {z₁ z₂ z₃ t₁ t₂ t₃ : G} (hnc : ¬ ({z₁} : Set G) ⊆ Subgroup.center G) (hK₁ : K₁ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hsh : PSpShape p f Ω z₁) (hK₂ : K₂ ∈ tqMembers Ω z₁)
    (hz₂ : IsClassicalMember p f K₂ z₂) (hK₃ : K₃ ∈ tqMembers Ω z₁)
    (hz₃ : IsClassicalMember p f K₃ z₃) (hprod : z₁ * z₂ = z₃) (ht₁ : t₁ ∈ K₁)
    (ht₂ : t₂ ∈ K₂) (ht₃ : t₃ ∈ K₃) (hsq₁ : t₁ * t₁ = z₁) (hsq₂ : t₂ * t₂ = z₂)
    (hsq₃ : t₃ * t₃ = z₃) (c₁₂ : t₁ * t₂ = t₂ * t₁) (c₁₃ : t₁ * t₃ = t₃ * t₁)
    (c₂₃ : t₂ * t₃ = t₃ * t₂)
    (helem : CFSG.Open.IsElemAbelian 2 (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃))
    (hcard : Nat.card (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) = 8) :
    Asc77.Hyp51At (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) z₁ := by
  have hz₁c := isCentralInvolution_of_isClassicalMember hz₁
  have hz₂c := isCentralInvolution_of_isClassicalMember hz₂
  have hz₃c := isCentralInvolution_of_isClassicalMember hz₃
  have hc2 := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz₁c.sq
  have hz₁B : z₁ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hz₂B : z₂ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hBC : TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ ≤ Subgroup.centralizer ({z₁} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem helem hz₁B
  have hz₂z₁ : z₂ ≠ z₁ := fun h => hz₃c.ne_one (by rw [← hprod, h, hz₁c.sq])
  have hzC : z₁ ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hz₂C : z₂ ∈ Subgroup.centralizer ({z₁} : Set G) := hBC hz₂B
  have hz₃C : z₃ ∈ Subgroup.centralizer ({z₁} : Set G) := by
    rw [← hprod]
    exact Subgroup.mul_mem _ hzC hz₂C
  have hcomm₁ : ∀ {u : G}, t₁ * u = u * t₁ → u ∈ Subgroup.centralizer ({z₁} : Set G) :=
    fun h => Subgroup.mem_centralizer_singleton_iff.mpr
      (by rw [← hsq₁]; exact (Axis.comm_sq h).symm)
  have ht₁C : t₁ ∈ Subgroup.centralizer ({z₁} : Set G) := hcomm₁ rfl
  have ht₂C : t₂ ∈ Subgroup.centralizer ({z₁} : Set G) := hcomm₁ c₁₂
  have ht₃C : t₃ ∈ Subgroup.centralizer ({z₁} : Set G) := hcomm₁ c₁₃
  obtain ⟨D, i₀, i₁, hcard2, hne, htag₁, hrank₁, hKbar, hinj, hcomm01, hcomp⟩ :=
    exists_pspVertex hΩ hp hq hK₁ hz₁ hsh
  set ψ₀ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₀ with hψ₀
  set ψ₁ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₁ with hψ₁
  have hz₁sq : oddQuotMk z₁ ⟨z₁, hzC⟩ * oddQuotMk z₁ ⟨z₁, hzC⟩ = 1 := by
    rw [← map_mul]
    exact (congrArg (oddQuotMk z₁) (Subtype.ext hz₁c.sq : (⟨z₁, hzC⟩ :
      ↥(Subgroup.centralizer ({z₁} : Set G))) * ⟨z₁, hzC⟩ = 1)).trans (map_one _)
  have hne₂ : oddQuotMk z₁ ⟨z₂, hz₂C⟩ ≠ oddQuotMk z₁ ⟨z₁, hzC⟩ := by
    intro h
    apply hz₃c.ne_one
    have h1 : oddQuotMk z₁ ⟨z₃, hz₃C⟩ = 1 := by
      have e : (⟨z₃, hz₃C⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) = ⟨z₁, hzC⟩ * ⟨z₂, hz₂C⟩ :=
        Subtype.ext hprod.symm
      rw [e, map_mul, h, hz₁sq]
    exact congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hz₃c.sq) h1)
  have hne₃ : oddQuotMk z₁ ⟨z₃, hz₃C⟩ ≠ oddQuotMk z₁ ⟨z₁, hzC⟩ := by
    intro h
    apply hz₂c.ne_one
    have h1 : oddQuotMk z₁ ⟨z₂, hz₂C⟩ = 1 := by
      have e : (⟨z₂, hz₂C⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) = ⟨z₁, hzC⟩ * ⟨z₃, hz₃C⟩ :=
        Subtype.ext (show z₂ = z₁ * z₃ by rw [← hprod, ← mul_assoc, hz₁c.sq, one_mul])
      rw [e, map_mul, h, hz₁sq]
    exact congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hz₂c.sq) h1)
  have hX₂ : modOdd z₁ (exactCore z₁ K₂) ≤ ψ₁.range := by
    obtain ⟨R, -, hR⟩ := hcomp K₂ hK₂ z₂ hz₂ hz₂C hne₂
    rw [← hR]
    exact Subgroup.map_le_range _ _
  have hX₃ : modOdd z₁ (exactCore z₁ K₃) ≤ ψ₁.range := by
    obtain ⟨R, -, hR⟩ := hcomp K₃ hK₃ z₃ hz₃ hz₃C hne₃
    rw [← hR]
    exact Subgroup.map_le_range _ _
  have h4 : ∀ {t z : G}, t * t = z → z * z = 1 → t ^ 4 = 1 := fun ht hz => by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, ht, hz]
  have ht₂E : t₂ ∈ exactCore z₁ K₂ := Vertex.mem_exactCore_of_isPGroup hΩ hp hq hc2 hK₂ ht₂
    (Subgroup.mem_centralizer_singleton_iff.mp ht₂C)
    (Vertex.isPGroup_zpowers_of_pow_four (h4 hsq₂ hz₂c.sq))
  have ht₃E : t₃ ∈ exactCore z₁ K₃ := Vertex.mem_exactCore_of_isPGroup hΩ hp hq hc2 hK₃ ht₃
    (Subgroup.mem_centralizer_singleton_iff.mp ht₃C)
    (Vertex.isPGroup_zpowers_of_pow_four (h4 hsq₃ hz₃c.sq))
  obtain ⟨r₂, hr₂⟩ := hX₂ (oddQuotMk_mem_modOdd ht₂E ht₂C)
  obtain ⟨r₃, hr₃⟩ := hX₃ (oddQuotMk_mem_modOdd ht₃E ht₃C)
  have hr23 : r₂ * r₃ = r₃ * r₂ := by
    apply hinj
    rw [map_mul, map_mul, hr₂, hr₃, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk z₁) (Subtype.ext c₂₃)
  have hpow : ∀ {u : G} (hu : u ∈ Subgroup.centralizer ({z₁} : Set G))
      {x : (compModel D i₁).K}, ψ₁ x = oddQuotMk z₁ ⟨u, hu⟩ → u ^ 4 = 1 → x ^ 4 = 1 := by
    intro u hu x hx hu4
    apply hinj
    have e : (⟨u, hu⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) ^ 4 = 1 :=
      Subtype.ext (by simpa using hu4)
    rw [map_pow, hx, ← map_pow, e, map_one, map_one]
  have hx₂ : ψ₁ (r₂ * r₂) = oddQuotMk z₁ ⟨z₂, hz₂C⟩ := by
    rw [map_mul, hr₂, ← map_mul]
    exact congrArg (oddQuotMk z₁) (Subtype.ext hsq₂)
  have hts : t₂ * t₃ ∈ Subgroup.centralizer ({z₁} : Set G) := Subgroup.mul_mem _ ht₂C ht₃C
  have hx₂₃ : ψ₁ (r₂ * r₃) = oddQuotMk z₁ ⟨t₂ * t₃, hts⟩ := by
    rw [map_mul, hr₂, hr₃, ← map_mul]
    rfl
  have hz₂4 : z₂ ^ 4 = 1 := h4 hz₂c.sq (mul_one 1)
  have ht₂₃4 : (t₂ * t₃) ^ 4 = 1 := by
    rw [(show Commute t₂ t₃ from c₂₃).mul_pow, h4 hsq₂ hz₂c.sq, h4 hsq₃ hz₃c.sq, one_mul]
  have hz₂ψ : oddQuotMk z₁ ⟨z₂, hz₂C⟩ ∈ ψ₁.range :=
    hX₂ (oddQuotMk_mem_modOdd (mem_exactCore hz₂ hc2 hK₂.2) hz₂C)
  have hnot₀ : ¬ MovedByAll (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) z₁ ψ₀.range := by
    intro hmov
    obtain ⟨y, hy, hne'⟩ := hmov _ (oddQuotMk_mem_modOdd hz₂B hz₂C)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers helem hz₁B hz₁c.ne_one hz₂B hz₂c.ne_one hz₂z₁
        hz₂C)
    exact hne' (hcomm01 y hy _ hz₂ψ).symm
  have ht₁ψ : oddQuotMk z₁ ⟨t₁, ht₁C⟩ ∈ ψ₀.range := by
    rw [← hKbar]
    exact oddQuotMk_mem_modOdd ht₁ ht₁C
  have hconj : ∀ {w y : OddQuot z₁}, w ∈ ψ₁.range → y ∈ ψ₁.range → w * y * w⁻¹ ∈ ψ₁.range :=
    fun hw hy => Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hy) (Subgroup.inv_mem _ hw)
  have htoral : Vertex.ToralOnComponentPow 4 z₁ (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) ψ₁ := by
    refine Vertex.toralOnComponentPow_of_closure hBC (P := Subgroup.closure {r₂, r₃})
      (Asc77.ChainFrame.commutes_closure ?_) ?_
    · rintro a (rfl | rfl) b (rfl | rfl)
      exacts [rfl, hr23, hr23.symm, rfl]
    · rintro s (rfl | rfl | rfl) hs
      · refine ⟨1, Subgroup.one_mem _, one_pow 4, fun y _ => ?_⟩
        rw [map_one, one_mul, inv_one, mul_one, oddQuotMk_central hs y, mul_inv_cancel_right]
      · refine ⟨r₂ * r₂, Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert _ _)), hpow hz₂C hx₂ hz₂4, fun y _ => ?_⟩
        rw [hx₂]
      · refine ⟨r₂ * r₃, Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)), hpow hts hx₂₃ ht₂₃4,
          fun y hy => ?_⟩
        have e : oddQuotMk z₁ ⟨t₁ * t₂ * t₃, hs⟩ =
            oddQuotMk z₁ ⟨t₁, ht₁C⟩ * oddQuotMk z₁ ⟨t₂ * t₃, hts⟩ := by
          rw [← map_mul]
          exact congrArg (oddQuotMk z₁) (Subtype.ext (mul_assoc t₁ t₂ t₃))
        have hu := hconj (⟨r₂ * r₃, hx₂₃⟩ : _ ∈ ψ₁.range) hy
        rw [hx₂₃, e, mul_inv_rev]
        calc oddQuotMk z₁ ⟨t₁, ht₁C⟩ * oddQuotMk z₁ ⟨t₂ * t₃, hts⟩ * y *
              ((oddQuotMk z₁ ⟨t₂ * t₃, hts⟩)⁻¹ * (oddQuotMk z₁ ⟨t₁, ht₁C⟩)⁻¹)
            = oddQuotMk z₁ ⟨t₁, ht₁C⟩ * (oddQuotMk z₁ ⟨t₂ * t₃, hts⟩ * y *
              (oddQuotMk z₁ ⟨t₂ * t₃, hts⟩)⁻¹) * (oddQuotMk z₁ ⟨t₁, ht₁C⟩)⁻¹ := by group
          _ = oddQuotMk z₁ ⟨t₂ * t₃, hts⟩ * y * (oddQuotMk z₁ ⟨t₂ * t₃, hts⟩)⁻¹ := by
            rw [hcomm01 _ ht₁ψ _ hu, mul_inv_cancel_right]
  refine Vertex.hyp51At_of_systemPow (m := 4) hp hq hΩ.conjInvariant hΩ.classical hBelow hc2 hnc
    helem hcard hz₁B hz₁c.ne_one hz₂B hz₂c.ne_one hz₂z₁ hK₂ hz₂ ⟨D, fun j hmov => ?_⟩
  rcases Seed.eq_or_eq_of_card_two hcard2 hne j with rfl | rfl
  · exact absurd hmov hnot₀
  · have hexp : D.exp j = f := by
      rcases D.exp_eq j with h | ⟨h, -⟩
      · exact h
      · rw [htag₁] at h
        cases h
    refine ⟨by rw [hexp]; omega, ⟨fun n _ _ => n = 2, hrank₁, ?_⟩, htoral⟩
    rw [htag₁]
    exact Sp.strongLocalTwoBalanceToralFourOn_PSp_two

end Axis

end CFSG.ClassicalInvolution.NDB
