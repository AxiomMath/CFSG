module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightNextNormalizerUnique
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

theorem factorization_two_N₂ : (2 ^ 13 * 21 : ℕ).factorization 2 = 13 := by
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem isElementaryAbelian_map {G H : Type*} [Group G] [Group H] {E : Subgroup G}
    (hE : IsElementaryAbelian 2 E) (f : G →* H) : IsElementaryAbelian 2 (E.map f) :=
  CFSG.IsElementaryAbelian.subgroup_map hE _

theorem isElementaryAbelian_subgroupOf {G : Type*} [Group G] {E : Subgroup G}
    (hE : IsElementaryAbelian 2 E) (K : Subgroup G) : IsElementaryAbelian 2 (E.subgroupOf K) :=
  isElementaryAbelian_of_forall
    (fun _ hx _ hy => Subtype.ext (mul_comm_of_isElementaryAbelian hE hx hy))
    fun _ hx => Subtype.ext (mul_self_of_isElementaryAbelian hE hx)

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒟" => CFSG.Assembly.pCoreOf 2 𝒩
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)

include hzC hsup hinf hz hb hnd hV he halt in
theorem card_N₂ : Nat.card 𝒩 = 2 ^ 13 * 21 := by
  obtain ⟨hcardD, -, -, hDN, -, -, μ, hμs, hμk⟩ :=
    setting_facts hzC hsup hinf hz hb hnd hV φ he halt
  have h := μ.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hμs, Subgroup.card_top, card_GL_three_two,
    hμk, Nat.card_congr (subgroupOfEquivOfLe hDN).toEquiv, hcardD] at h
  rw [← h]
  norm_num

include hzC hsup hinf hz hb hnd hV he halt in
theorem card_sylow_N₂ (S : Sylow 2 𝒩) : Nat.card S = 2 ^ 13 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [S.card_eq_multiplicity, card_N₂ hzC hsup hinf hz hb hnd hV φ he halt, factorization_two_N₂]

include hzC hsup hinf hz hb hnd hV he halt in
theorem two_pow_fourteen_dvd : 2 ^ 14 ∣ Nat.card G := by
  have h := (ptLin hzC hsup hinf hz hb hnd hV φ he halt).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (ptLin_surjective hzC hsup hinf hz hb hnd hV φ
    he halt), Subgroup.card_top, OddQuadraticFive.Orth.card_bilinIsometryGroup
      (finrank_pairOrth_eq he hb hnd) (restrict_isAlt hb) (restrict_nondegenerate hb hnd he),
    ← ptD₁_subgroupOf, Nat.card_congr (subgroupOfEquivOfLe
      (ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt)).toEquiv,
    card_ptD₁] at h
  have h1 : 2 ^ 14 ∣ Nat.card 𝒩₁ := by
    rw [← h]
    norm_num
  exact h1.trans (Subgroup.card_subgroup_dvd_card _)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem C₂_le_sylow {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂) (S : Sylow 2 𝒩) :
    C₂ ≤ (S : Subgroup 𝒩).map (𝒩).subtype := by
  have hDN : 𝒟 ≤ 𝒩 := map_subtype_le _
  have hC₂n : (C₂.subgroupOf 𝒩).Normal :=
    ⟨fun c hc g => by
      rw [mem_subgroupOf] at hc ⊢
      exact hC₂N g g.2 c hc⟩
  have hC₂2 : IsPGroup 2 (C₂.subgroupOf 𝒩) :=
    isPGroup_of_mul_self fun x hx => mul_self_of_isElementaryAbelian
      (isElementaryAbelian_subgroupOf hC₂e 𝒩) hx
  have h1 : C₂.subgroupOf 𝒩 ≤ S := hC₂2.le_sylow_of_normal S
  have h2 := Subgroup.map_mono (f := (𝒩).subtype) h1
  rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hC₂D.trans hDN)] at h2

include hzC hsup hinf hz hb hnd hV he halt in
theorem mem_normalizer_of_mem_normalizer {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟)
    (hC₂c : Nat.card C₂ = 512) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂z' : ((zpowers z : Set G) * (C₂ : Set G)) = 𝒟)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    {S : Subgroup G} (hC₂S : C₂ ≤ S) (hSN : S ≤ 𝒩) {g : G}
    (hg : g ∈ normalizer (S : Set G)) : g ∈ normalizer (C₂ : Set G) := by
  have hle : C₂.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro _ ⟨c, hc, rfl⟩
    exact (mem_normalizer_iff.1 hg c).1 (hC₂S hc)
  have hF := eq_C₂_of_isElementaryAbelian hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂c hC₂R
    hC₂z' hC₂z hC₂e (hle.trans hSN) (isElementaryAbelian_map hC₂e _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hC₂c])
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hF]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hF] at hh
    obtain ⟨c, hc, hcx⟩ := hh
    have hch : c = h := by
      have h1 : g * c * g⁻¹ = g * h * g⁻¹ := hcx
      simpa using h1
    rwa [← hch]

include hzC hsup hinf hz hb hnd hV he halt in
theorem characteristic_C₂ {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂c : Nat.card C₂ = 512)
    (hC₂R : C₂ ⊓ ℛ = 𝒜) (hC₂z' : ((zpowers z : Set G) * (C₂ : Set G)) = 𝒟)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂) (S : Sylow 2 𝒩) :
    (C₂.subgroupOf ((S : Subgroup 𝒩).map (𝒩).subtype)).Characteristic := by
  set S' := (S : Subgroup 𝒩).map (𝒩).subtype with hS'
  have hC₂S : C₂ ≤ S' := C₂_le_sylow φ hC₂D hC₂e hC₂N S
  have hS'N : S' ≤ 𝒩 := map_subtype_le _
  rw [characteristic_iff_map_le]
  intro ϕ
  set K := (C₂.subgroupOf S').map (S'.subtype.comp ϕ.toMonoidHom) with hK
  have hKe : IsElementaryAbelian 2 K :=
    isElementaryAbelian_map (isElementaryAbelian_subgroupOf hC₂e S') _
  have hKc : Nat.card K = 512 := by
    rw [hK, Subgroup.card_map_of_injective (f := S'.subtype.comp ϕ.toMonoidHom)
        (fun x y h => ϕ.injective (S'.subtype_injective h)),
      Nat.card_congr (subgroupOfEquivOfLe hC₂S).toEquiv, hC₂c]
  have hKS : K ≤ S' := by
    rintro _ ⟨x, -, rfl⟩
    exact (ϕ x).2
  have hKeq := eq_C₂_of_isElementaryAbelian hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂c hC₂R
    hC₂z' hC₂z hC₂e (hKS.trans hS'N) hKe hKc
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_subgroupOf, ← hKeq]
  exact ⟨x, hx, rfl⟩

include hzC hsup hinf hz hb hnd hV he halt in
theorem ne_sylow (S : Sylow 2 𝒩) (P : Sylow 2 G) :
    (P : Subgroup G) ≠ (S : Subgroup 𝒩).map (𝒩).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hPS
  have h1 : Nat.card P = 2 ^ 13 := by
    rw [hPS, Subgroup.card_map_of_injective (𝒩).subtype_injective,
      card_sylow_N₂ hzC hsup hinf hz hb hnd hV φ he halt]
  have h2 := P.card_eq_multiplicity
  have h3 : 14 ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1
      (two_pow_fourteen_dvd hzC hsup hinf hz hb hnd hV φ he halt)
  rw [h1] at h2
  have h4 := Nat.pow_right_injective (le_refl 2) h2
  omega

include hzC hsup hinf hz hb hnd hV he halt in
theorem lt_inf_normalizer {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂c : Nat.card C₂ = 512)
    (hC₂R : C₂ ⊓ ℛ = 𝒜) (hC₂z' : ((zpowers z : Set G) * (C₂ : Set G)) = 𝒟)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂) (S : Sylow 2 𝒩) (P : Sylow 2 G)
    (hSP : (S : Subgroup 𝒩).map (𝒩).subtype ≤ P) :
    (S : Subgroup 𝒩).map (𝒩).subtype <
        (P : Subgroup G) ⊓ normalizer (((S : Subgroup 𝒩).map (𝒩).subtype : Subgroup G) : Set G) ∧
      (P : Subgroup G) ⊓ normalizer (((S : Subgroup 𝒩).map (𝒩).subtype : Subgroup G) : Set G) ≤
        normalizer (C₂ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' := (S : Subgroup 𝒩).map (𝒩).subtype with hS'
  have hC₂S : C₂ ≤ S' := C₂_le_sylow φ hC₂D hC₂e hC₂N S
  have hS'N : S' ≤ 𝒩 := map_subtype_le _
  refine ⟨?_, fun g hg => mem_normalizer_of_mem_normalizer hzC hsup hinf hz hb hnd hV φ he halt
    hC₂D hC₂c hC₂R hC₂z' hC₂z hC₂e hC₂S hS'N hg.2⟩
  have hne : (P : Subgroup G) ≠ S' := ne_sylow hzC hsup hinf hz hb hnd hV φ he halt S P
  have hlt : S'.subgroupOf P < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hne (le_antisymm (Subgroup.subgroupOf_eq_top.mp h) hSP)
  have := P.isPGroup'.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (S'.subgroupOf P) hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hSP] at hnc
  obtain ⟨x, hx, hxS⟩ := IsConcreteLE.exists_of_lt hnc
  refine lt_of_le_of_ne (le_inf hSP le_normalizer) fun h => hxS ?_
  have hx' : (x : G) ∈ (P : Subgroup G) ⊓ normalizer (S' : Set G) := ⟨x.2, hx⟩
  rw [← h] at hx'
  exact hx'

include hzC hsup hinf hz hb hnd hV he halt in
theorem two_pow_five_dvd {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂c : Nat.card C₂ = 512)
    (hC₂R : C₂ ⊓ ℛ = 𝒜) (hC₂z' : ((zpowers z : Set G) * (C₂ : Set G)) = 𝒟)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂) :
    2 ^ 5 ∣ Nat.card (normalizer (C₂ : Set G) ⧸ C₂.subgroupOf (normalizer (C₂ : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 𝒩))
  set S' := (S : Subgroup 𝒩).map (𝒩).subtype with hS'
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map (𝒩).subtype
  obtain ⟨P, hP⟩ := hS'2.exists_le_sylow
  obtain ⟨hlt, hle⟩ := lt_inf_normalizer hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂c hC₂R
    hC₂z' hC₂z hC₂e hC₂N S P hP
  set T := (P : Subgroup G) ⊓ normalizer (S' : Set G) with hT
  have hT2 : IsPGroup 2 T := P.isPGroup'.to_le inf_le_left
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hS'c : Nat.card S' = 2 ^ 13 := by
    rw [hS', Subgroup.card_map_of_injective (𝒩).subtype_injective,
      card_sylow_N₂ hzC hsup hinf hz hb hnd hV φ he halt]
  have h14 : 2 ^ 14 ∣ Nat.card T := by
    have h1 : 2 ^ 13 ∣ 2 ^ k := by
      rw [← hS'c, ← hk]
      exact Subgroup.card_dvd_of_le hlt.le
    have h2 : 2 ^ 13 ≠ 2 ^ k := by
      rw [← hS'c, ← hk]
      exact fun h => hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.ge)
    have h3 : 13 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
    have h4 : 13 ≠ k := fun h => h2 (by rw [h])
    rw [hk]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hX : 2 ^ 14 ∣ Nat.card (normalizer (C₂ : Set G)) :=
    h14.trans (Subgroup.card_dvd_of_le hle)
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (C₂.subgroupOf (normalizer (C₂ : Set G)))
  rw [Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : C₂ ≤ normalizer (C₂ : Set G))).toEquiv,
    hC₂c] at hcard
  rw [hcard, show (2 : ℕ) ^ 14 = 2 ^ 5 * 512 by norm_num] at hX
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hX

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
