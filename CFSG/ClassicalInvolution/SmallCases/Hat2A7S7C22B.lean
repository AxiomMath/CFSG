module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7C22A
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Hyp51
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Component

variable {G : Type} [Group G]

theorem isClassical_of_uniqueInvolution {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hcl : ∃ u : G, Hat2A7.IsClassical2A7 ⊤ K u) : Hat2A7.IsClassical2A7 ⊤ K z := by
  obtain ⟨u, hu⟩ := hcl
  have hune : u ≠ 1 := by
    intro h
    have := hu.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hzu : u = z := (hz.unique u hu.mem hu.mul_self).resolve_left hune
  rw [hzu] at hu
  exact hu

theorem isSubnormal_centralizer_of_classical {K : Subgroup G} {z : G}
    (hu : Hat2A7.IsClassical2A7 ⊤ K z) : IsSubnormal K (Subgroup.centralizer ({z} : Set G)) := by
  have h := hu.subnormal
  rwa [top_inf_eq] at h

theorem le_centralizer_of_isUniqueInvolution {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) : K ≤ Subgroup.centralizer ({z} : Set G) := fun _ hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hw).symm

variable [Finite G]

theorem isComponent_modOdd_of_classical {K : Subgroup G} {z : G}
    (hu : Hat2A7.IsClassical2A7 ⊤ K z) : CFSG.IsComponent (modOdd z K) := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have hKC : K ≤ C := hu.le_centralizer
  have hsn : IsSubnormal K C := isSubnormal_centralizer_of_classical hu
  have hsubH : (K.subgroupOf C).IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
      ((CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hKC).mpr hsn)
      Subgroup.IsSubnormal.top
  let π : ↥C →* OddQuot z := oddQuotMk z
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  let ψ : ↥K →* ↥(modOdd z K) :=
    (π.comp (Subgroup.inclusion hKC)).codRestrict (modOdd z K)
      fun x => ⟨Subgroup.inclusion hKC x, x.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨(a : G), ha⟩, rfl⟩
  have hψker : ψ.ker = classicalInvolutionOddCore ↥K := by
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    have h1 := CFSG.ComponentClassification.OddCore.subnormal_mem_iff hsn (x : G) x.2
    have h2 : (π (Subgroup.inclusion hKC x) = 1) ↔
        (Subgroup.inclusion hKC x) ∈ componentClassificationOddCore ↥C :=
      QuotientGroup.eq_one_iff _
    constructor
    · intro h
      refine h1.mpr ⟨hKC x.2, ?_⟩
      exact h2.mp h
    · intro h
      obtain ⟨hup, h3⟩ := h1.mp h
      exact h2.mpr h3
  let e' : ↥(modOdd z K) ≃* ↥K ⧸ classicalInvolutionOddCore ↥K :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hψker)
  have hqs : CFSG.IsQuasisimple ↥(modOdd z K) :=
    CFSG.ComponentClassification.AS76b.Lemma34.isQuasisimple_of_open
      (CFSG.ComponentClassification.Components.quasisimple_of_equiv e' hu.witness.1)
  exact ⟨hqs, hsubH.map hπs⟩

theorem isComponent_modOdd_of_member {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hcl : ∃ u : G, Hat2A7.IsClassical2A7 ⊤ K u) : CFSG.IsComponent (modOdd z K) :=
  isComponent_modOdd_of_classical (isClassical_of_uniqueInvolution hz hcl)

end Component

section Twins

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem modOdd_commute_of_twin (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z)
    (hcl : ∃ u : G, Hat2A7.IsClassical2A7 ⊤ K u) :
    ∀ x ∈ modOdd z K, ∀ y ∈ modOdd z J, x * y = y * x := by
  have hsn : IsSubnormal K (Subgroup.centralizer ({z} : Set G)) :=
    isSubnormal_centralizer_of_classical (isClassical_of_uniqueInvolution hzK hcl)
  have hcomm := Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hKJ hzK hzJ
  rintro _ ⟨a, haK, rfl⟩ _ ⟨b, hbJ, rfl⟩
  have haK' : (a : G) ∈ K := haK
  have hbJ' : (b : G) ∈ J := hbJ
  have hab : ⁅(a : G), (b : G)⁆ ∈ oddCoreOf K :=
    (hcomm (Subgroup.commutator_mem_commutator haK' hbJ')).1
  obtain ⟨hmemK, hOK⟩ := mem_oddCoreOf_iff.mp hab
  obtain ⟨hmemC, hOC⟩ :=
    (CFSG.ComponentClassification.OddCore.subnormal_mem_iff hsn _ hmemK).mp hOK
  have h1 : oddQuotMk z (a * b * a⁻¹ * b⁻¹) = 1 := oddQuotMk_eq_one_iff.mpr hOC
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact h1)

theorem modOdd_ne_of_twin (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) {z : G} (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z)
    (hcl : ∃ u : G, Hat2A7.IsClassical2A7 ⊤ K u) : modOdd z K ≠ modOdd z J := by
  intro h
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    LocalBalance.exists_noncomm_of_isQuasisimple (isComponent_modOdd_of_member hzK hcl).1
  have hy' : y ∈ modOdd z J := h ▸ hy
  exact hxy (modOdd_commute_of_twin hΩ hK hJ hKJ hzK hzJ hcl x hx y hy')

theorem oddQuotMk_mul_commute_of_ne {K K' : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hK : CFSG.IsComponent (modOdd z K))
    (hK' : CFSG.IsComponent (modOdd z K')) {L : Subgroup (OddQuot z)} (hL : CFSG.IsComponent L)
    (hLK : modOdd z K ≠ L) (hLK' : modOdd z K' ≠ L) {a b : G} (ha : a ∈ K) (hb : b ∈ K')
    (hab : a * b ∈ Subgroup.centralizer ({z} : Set G)) :
    ∀ y ∈ L, oddQuotMk z ⟨a * b, hab⟩ * y = y * oddQuotMk z ⟨a * b, hab⟩ := by
  have haC := le_centralizer_of_isUniqueInvolution hz ha
  have hbC := le_centralizer_of_isUniqueInvolution hz' hb
  intro y hy
  have h1 := LocalBalance.commute_of_isComponent_of_ne hK hL hLK _
    (oddQuotMk_mem_modOdd ha haC) y hy
  have h2 := LocalBalance.commute_of_isComponent_of_ne hK' hL hLK' _
    (oddQuotMk_mem_modOdd hb hbC) y hy
  have e : oddQuotMk z ⟨a * b, hab⟩ = oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨b, hbC⟩ :=
    map_mul (oddQuotMk z) ⟨a, haC⟩ ⟨b, hbC⟩
  rw [e]
  exact (Commute.mul_left (show Commute _ y from h1) (show Commute _ y from h2)).eq

end Twins

section Frame3

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}
  {K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G} {u₁ u₂ u₃ : G}


theorem Frame3.exists_centralizing_element [Finite G] (hΩ : HypOmegaGen Ω)
    (hcl : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u)
    (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) {L : Subgroup (OddQuot z)}
    (hL : CFSG.IsComponent L) :
    ∃ b ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G),
      ∃ hbC : b ∈ Subgroup.centralizer ({z} : Set G), b ∉ Subgroup.zpowers z ∧
        ∀ y ∈ L, oddQuotMk z ⟨b, hbC⟩ * y = y * oddQuotMk z ⟨b, hbC⟩ := by
  set B : Subgroup G := Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)
  have hzB : z ∈ B := Subgroup.subset_closure (by simp)
  have hxB : u₁ * u₂ ∈ B := Subgroup.subset_closure (by simp)
  have hyB : u₂ * u₃ ∈ B := Subgroup.subset_closure (by simp)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact F.z_sq) F.z_ne_one
  have notz : ∀ b : G, b ≠ 1 → b ≠ z → b ∉ Subgroup.zpowers z := fun b h1 h2 hb =>
    (T7A.eq_one_or_eq_of_mem_zpowers hz2 hb).elim h1 h2
  have c₁ := isComponent_modOdd_of_member F.hz₁ (hcl K₁ F.mem₁)
  have c₂ := isComponent_modOdd_of_member F.hz₂ (hcl K₂ F.mem₂)
  have c₃ := isComponent_modOdd_of_member F.hz₃ (hcl K₃ F.mem₃)
  have n₂₁ : modOdd z K₂ ≠ modOdd z K₁ :=
    modOdd_ne_of_twin hΩ F.mem₂ F.mem₁ F.ne₁₂ F.hz₂ F.hz₁ (hcl K₂ F.mem₂)
  have n₃₁ : modOdd z K₃ ≠ modOdd z K₁ :=
    modOdd_ne_of_twin hΩ F.mem₃ F.mem₁ F.ne₁₃ F.hz₃ F.hz₁ (hcl K₃ F.mem₃)
  have n₃₂ : modOdd z K₃ ≠ modOdd z K₂ :=
    modOdd_ne_of_twin hΩ F.mem₃ F.mem₂ F.ne₂₃ F.hz₃ F.hz₂ (hcl K₃ F.mem₃)
  by_cases h1 : modOdd z K₁ = L
  ·
    have hbC : u₂ * u₃ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr F.z_comm_y.symm
    exact ⟨u₂ * u₃, hyB, hbC, notz _ (F.y_ne_one hΩ) (F.y_ne_z hΩ),
      oddQuotMk_mul_commute_of_ne F.hz₂ F.hz₃ c₂ c₃ hL (fun h => n₂₁ (h.trans h1.symm))
        (fun h => n₃₁ (h.trans h1.symm)) F.mem_K₂ F.mem_K₃ hbC⟩
  · by_cases h2 : modOdd z K₂ = L
    ·
      have hbC : u₁ * u₃ ∈ Subgroup.centralizer ({z} : Set G) :=
        (Subgroup.centralizer ({z} : Set G)).mul_mem
          (le_centralizer_of_isUniqueInvolution F.hz₁ F.mem_K₁)
          (le_centralizer_of_isUniqueInvolution F.hz₃ F.mem_K₃)
      have hbB : u₁ * u₃ ∈ B := by
        rw [← F.x_mul_z_mul_y]
        exact B.mul_mem (B.mul_mem hxB hzB) hyB
      exact ⟨u₁ * u₃, hbB, hbC, notz _ (F.swap₂₃.x_ne_one hΩ) (F.swap₂₃.x_ne_z hΩ),
        oddQuotMk_mul_commute_of_ne F.hz₁ F.hz₃ c₁ c₃ hL h1 (fun h => n₃₂ (h.trans h2.symm))
          F.mem_K₁ F.mem_K₃ hbC⟩
    ·
      have hbC : u₁ * u₂ ∈ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr F.z_comm_x.symm
      exact ⟨u₁ * u₂, hxB, hbC, notz _ (F.x_ne_one hΩ) (F.x_ne_z hΩ),
        oddQuotMk_mul_commute_of_ne F.hz₁ F.hz₂ c₁ c₂ hL h1 h2 F.mem_K₁ F.mem_K₂ hbC⟩

theorem Frame3.hyp51At_z [Finite G] (hΩ : HypOmegaGen Ω)
    (hcl : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u)
    (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) :
    Hyp51At (Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)) z := by
  set B : Subgroup G := Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)
  have hzB : z ∈ B := Subgroup.subset_closure (by simp)
  have hB2 : ∀ x ∈ B, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact (F.isElemAbelian_B hΩ).2 x hx
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L → ¬ MovedByAll B z L := by
    intro L hL hmov
    obtain ⟨b, hbB, hbC, hbz, hcen⟩ := F.exists_centralizing_element hΩ hcl hL
    obtain ⟨y, hy, hne⟩ := hmov (oddQuotMk z ⟨b, hbC⟩) (oddQuotMk_mem_modOdd hbB hbC)
      (Hat2A7S8.oddQuotMk_not_mem_modOdd_zpowers hB2 hzB hbB hbz hbC)
    exact hne (hcen y hy)
  exact ⟨fun L₁ _ h₁ _ m₁ _ => absurd m₁ (hno L₁ h₁), fun L hL hm => absurd hm (hno L hL)⟩

end Frame3

end CFSG.ClassicalInvolution.Hat2A7S
