module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightNextNormalizerSylow

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

theorem not_two_pow_five_dvd : ¬ 2 ^ 5 ∣ 2 * 168 := by
  norm_num

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
local notation "𝒮" => (𝒩 ⊓ centralizer (Singleton.singleton z : Set G) : Subgroup G)
local notation "𝒟" => CFSG.Assembly.pCoreOf 2 𝒩
local notation "θ₂" => RadicalLabels.radLabel φ he hzC hz hinf

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hz in
theorem z_mul_self : z * z = 1 := by
  rw [← sq, ← hz]
  exact pow_orderOf_eq_one z

include hzC hsup hinf hz hb hnd hV he halt in
theorem exists_conj_eq_mul {C₂ : Subgroup G}
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂comm : {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} =
      (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G))
    {g c₀ : G} (hc₀ : c₀ ∈ C₂) (hg : g * z * g⁻¹ = z * c₀) :
    ∃ c ∈ C₂, c * z * c⁻¹ = z * c₀ := by
  have hz2 := z_mul_self hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hc₀2 : c₀ * c₀ = 1 := mul_self_of_isElementaryAbelian hC₂e hc₀
  have hx2 : z * c₀ * (z * c₀) = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
  have hcz : c₀ * z = z * c₀ := by
    calc c₀ * z = c₀ * z * (z * c₀ * (z * c₀)) := by rw [hx2, mul_one]
      _ = c₀ * (z * z) * c₀ * z * c₀ := by group
      _ = z * c₀ := by rw [hz2, mul_one, hc₀2, one_mul]
  have hc₀A : c₀ ∈ 𝒜 := (hC₂z c₀ hc₀).1 hcz
  have heq := conj_set_eq hzC hsup hinf hz hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  have hmem : z * c₀ ∈ {x | ∃ g : G, g * z * g⁻¹ = x} ∩ (ℛ : Set G) :=
    ⟨⟨g, hg⟩, mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left hc₀A)⟩
  rw [← heq] at hmem
  have hN : z * c₀ ∈ conjClass 𝒩 z := hmem
  have h1 : conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) := halt
  rw [h1] at hN
  rcases hN with h | ⟨t, ht, hzt⟩
  · have hc1 : c₀ = 1 := by
      have h2 := Set.mem_singleton_iff.1 h
      rwa [mul_eq_left] at h2
    exact ⟨1, one_mem _, by rw [hc1]; group⟩
  · have hzt' : z * t = z * c₀ := hzt
    have htc : t = c₀ := mul_left_cancel hzt'
    have hI : c₀ ∈ (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G) := by
      rw [← tauSet_alt_eq_radI hzC hinf hz φ he, ← htc]
      obtain ⟨B, hB, rfl⟩ := (mem_tauSet_iff φ he).1 ht
      exact (mem_tauSet_iff φ he).2 ⟨B, hB.2, rfl⟩
    rw [← hC₂comm] at hI
    obtain ⟨c, hc, hcc⟩ := hI
    refine ⟨c⁻¹, inv_mem hc, ?_⟩
    rw [inv_inv]
    calc c⁻¹ * z * c = c⁻¹ * z⁻¹ * c := by rw [hzi]
      _ = c⁻¹ * z⁻¹ * c * z * z⁻¹ := by group
      _ = c₀ * z⁻¹ := by rw [hcc]
      _ = c₀ * z := by rw [hzi]
      _ = z * c₀ := hcz

include hzC hsup hinf hz hb hnd hV he halt in
theorem exists_mul_iff_mem {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂comm : {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} =
      (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G))
    {x : G} (hx : x ∈ normalizer (C₂ : Set G)) :
    (∃ c ∈ C₂, x * z * x⁻¹ = z * c) ↔ x ∈ 𝒩 := by
  have hAC₂ : 𝒜 ≤ C₂ := hC₂R ▸ inf_le_left
  have hDN : 𝒟 ≤ 𝒩 := map_subtype_le _
  have hzN : z ∈ 𝒩 := le_normalizer (mem_sup_right (mem_zpowers z))
  constructor
  · rintro ⟨c₀, hc₀, hxz⟩
    obtain ⟨c, hc, hcz⟩ := exists_conj_eq_mul hzC hsup hinf hz hb hnd hV φ he halt hC₂z hC₂e
      hC₂comm hc₀ hxz
    set y := c⁻¹ * x with hy
    have hyz : y * z = z * y := by
      have h1 : y * z * y⁻¹ = z := by
        calc y * z * y⁻¹ = c⁻¹ * (x * z * x⁻¹) * c := by rw [hy]; group
          _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hxz, ← hcz]
          _ = z := by group
      calc y * z = y * z * y⁻¹ * y := by group
        _ = z * y := by rw [h1]
    have hyX : y ∈ normalizer (C₂ : Set G) := mul_mem (inv_mem (le_normalizer hc)) hx
    have hyA : ∀ {g : G}, g ∈ normalizer (C₂ : Set G) → g * z = z * g → ∀ a ∈ 𝒜,
        g * a * g⁻¹ ∈ 𝒜 := by
      intro g hg hgz a ha
      have h1 : g * a * g⁻¹ ∈ C₂ := (mem_normalizer_iff.1 hg a).1 (hAC₂ ha)
      refine (hC₂z _ h1).1 ?_
      have haz : a * z = z * a := (hC₂z a (hAC₂ ha)).2 ha
      have hgz' : g⁻¹ * z = z * g⁻¹ := (Commute.inv_left (show Commute g z from hgz)).eq
      calc g * a * g⁻¹ * z = g * a * (g⁻¹ * z) := by group
        _ = g * (a * z) * g⁻¹ := by rw [hgz']; group
        _ = g * (z * a) * g⁻¹ := by rw [haz]
        _ = (g * z) * a * g⁻¹ := by group
        _ = z * (g * a * g⁻¹) := by rw [hgz]; group
    have hyN : y ∈ 𝒩 := by
      have hyz' : y⁻¹ * z = z * y⁻¹ := (Commute.inv_left (show Commute y z from hyz)).eq
      have hmap : ∀ {g : G}, g ∈ normalizer (C₂ : Set G) → g * z = z * g → ∀ r ∈ ℛ,
          g * r * g⁻¹ ∈ ℛ := by
        intro g hg hgz r hr
        obtain ⟨a, ha, t, ht, rfl⟩ := (mem_sup_of_le_centralizer
          (FusionOrbits.zpowers_le_centralizer_pullSub φ hzC _)).1 hr
        have htg : g * t * g⁻¹ = t := by
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
          rw [mul_inv_eq_iff_eq_mul, (Commute.zpow_right hgz k).eq]
        rw [show g * (a * t) * g⁻¹ = (g * a * g⁻¹) * (g * t * g⁻¹) by group, htg]
        exact mul_mem (mem_sup_left (hyA hg hgz a ha)) (mem_sup_right ht)
      rw [mem_normalizer_iff]
      intro r
      constructor
      · exact hmap hyX hyz r
      · intro hr
        have h1 := hmap (inv_mem hyX) hyz' _ hr
        rwa [show y⁻¹ * (y * r * y⁻¹) * y⁻¹⁻¹ = r by group] at h1
    rw [show x = c * y by rw [hy]; group]
    exact mul_mem (hDN (hC₂D hc)) hyN
  · intro hxN
    have h1 : conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) :=
      halt
    have hmem : x * z * x⁻¹ ∈ conjClass 𝒩 z := show ∃ m ∈ 𝒩, m * z * m⁻¹ = x * z * x⁻¹ from
      ⟨x, hxN, rfl⟩
    rw [h1] at hmem
    rcases hmem with h | ⟨t, ht, hzt⟩
    · exact ⟨1, one_mem _, by rw [Set.mem_singleton_iff.1 h, mul_one]⟩
    · have hzt' : z * t = x * z * x⁻¹ := hzt
      obtain ⟨B, -, rfl⟩ := (mem_tauSet_iff φ he).1 ht
      exact ⟨_, hAC₂ ((mem_pullSub_iff φ he).2 ⟨B, rfl⟩), hzt'.symm⟩

include hzC hsup hinf hz hb hnd hV he halt in
theorem centralizer_eq_map {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂comm : {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} =
      (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G))
    (hzX : z ∈ normalizer (C₂ : Set G)) :
    centralizer {(QuotientGroup.mk ⟨z, hzX⟩ :
        normalizer (C₂ : Set G) ⧸ C₂.subgroupOf (normalizer (C₂ : Set G)))} =
      ((𝒩).subgroupOf (normalizer (C₂ : Set G))).map
        (QuotientGroup.mk' (C₂.subgroupOf (normalizer (C₂ : Set G)))) := by
  have hDN : 𝒟 ≤ 𝒩 := map_subtype_le _
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [mem_centralizer_singleton_iff, Subgroup.mem_map]
  have key : (QuotientGroup.mk x : normalizer (C₂ : Set G) ⧸ C₂.subgroupOf
      (normalizer (C₂ : Set G))) * QuotientGroup.mk ⟨z, hzX⟩ =
        QuotientGroup.mk ⟨z, hzX⟩ * QuotientGroup.mk x ↔
      ∃ c ∈ C₂, (x : G) * z * (x : G)⁻¹ = z * c := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, eq_comm, QuotientGroup.eq,
      mem_subgroupOf]
    change ((z * (x : G))⁻¹ * ((x : G) * z)) ∈ C₂ ↔ _
    constructor
    · intro h
      refine ⟨z⁻¹ * ((x : G) * z * (x : G)⁻¹), ?_, by group⟩
      have h1 := (mem_normalizer_iff.1 x.2 _).1 h
      rwa [show (x : G) * ((z * (x : G))⁻¹ * ((x : G) * z)) * (x : G)⁻¹ =
        z⁻¹ * ((x : G) * z * (x : G)⁻¹) by group] at h1
    · rintro ⟨c, hc, hcx⟩
      have h1 := (mem_normalizer_iff.1 (inv_mem x.2) c).1 hc
      have hc' : c = z⁻¹ * ((x : G) * z * (x : G)⁻¹) := by
        rw [hcx]
        group
      rw [hc'] at h1
      rwa [show (x : G)⁻¹ * (z⁻¹ * ((x : G) * z * (x : G)⁻¹)) * (x : G)⁻¹⁻¹ =
        (z * (x : G))⁻¹ * ((x : G) * z) by group] at h1
  rw [key, exists_mul_iff_mem hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂R hC₂z hC₂e hC₂comm
    x.2]
  constructor
  · intro hxN
    exact ⟨x, hxN, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have h1 := QuotientGroup.eq.1 hyx
    rw [mem_subgroupOf] at h1 hy
    have h2 : (x : G) = y * ((y⁻¹ * x : normalizer (C₂ : Set G)) : G) := by
      change (x : G) = y * ((y : G)⁻¹ * x)
      group
    rw [h2]
    exact mul_mem hy (hDN (hC₂D h1))

include hzC hsup hinf hz hb hnd hV he halt in
theorem exists_mulEquiv {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂z' : ((zpowers z : Set G) * (C₂ : Set G)) = 𝒟)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂)
    (hC₂comm : {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} =
      (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G))
    (hzX : z ∈ normalizer (C₂ : Set G)) :
    ∃ ψ : Multiplicative (ZMod 2) × GL (Fin 3) (ZMod 2) ≃*
        centralizer {(QuotientGroup.mk ⟨z, hzX⟩ :
          normalizer (C₂ : Set G) ⧸ C₂.subgroupOf (normalizer (C₂ : Set G)))},
      ∀ (s : ZMod 2) (g : GL (Fin 3) (ZMod 2))
        (h : z ^ s.val * leviHom φ he g ∈ normalizer (C₂ : Set G)),
        (ψ (Multiplicative.ofAdd s, g) :
          normalizer (C₂ : Set G) ⧸ C₂.subgroupOf (normalizer (C₂ : Set G))) =
          QuotientGroup.mk ⟨_, h⟩ := by
  classical
  set X := normalizer (C₂ : Set G) with hX
  have h𝒩X : 𝒩 ≤ X := by
    intro g hg
    rw [hX, mem_normalizer_iff]
    intro c
    refine ⟨hC₂N g hg c, fun hc => ?_⟩
    have h1 := hC₂N g⁻¹ (inv_mem hg) _ hc
    rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at h1
  have hzS : z ∈ 𝒮 := mem_inf.2 ⟨le_normalizer (mem_sup_right (mem_zpowers z)),
    mem_centralizer_singleton_iff.2 rfl⟩
  have hLX : ∀ D : GL (Fin 3) (ZMod 2), leviHom φ he D ∈ X := fun D =>
    h𝒩X (mem_inf.1 (leviHom_mem_stab hzC hsup hinf hb hnd hV φ he D)).1
  obtain ⟨hAe, hAc, -, -⟩ := pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  obtain ⟨hAz, -, -⟩ := sup_facts hzC hinf hz (pullSub_le φ _) hAe hAc
  obtain ⟨-, hDS, -, hDN, -, -, -⟩ := setting_facts hzC hsup hinf hz hb hnd hV φ he halt
  obtain ⟨-, σ, -, -, -, -, -, hσker, -, -, hσL⟩ :=
    exists_nu_sigma hzC hsup hinf hz hb hnd hV φ he halt
  set a : X ⧸ C₂.subgroupOf X := QuotientGroup.mk ⟨z, hzX⟩ with ha
  have ha2 : a ^ 2 = 1 := by
    rw [ha, ← QuotientGroup.mk_pow]
    rw [show (⟨z, hzX⟩ : X) ^ 2 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, sq, z_mul_self hz]
      rfl), QuotientGroup.mk_one]
  let fz : Multiplicative (ZMod 2) →* X ⧸ C₂.subgroupOf X :=
    MonoidHom.mk' (fun s => a ^ (Multiplicative.toAdd s).val) fun s t => by
      rw [toAdd_mul, OddQuadraticFive.pow_val_add_of_sq ha2]
  let gL : GL (Fin 3) (ZMod 2) →* X ⧸ C₂.subgroupOf X :=
    (QuotientGroup.mk' (C₂.subgroupOf X)).comp ((leviHom φ he).codRestrict X hLX)
  have hca : ∀ D : GL (Fin 3) (ZMod 2), Commute a (gL D) := by
    intro D
    change a * QuotientGroup.mk ⟨leviHom φ he D, hLX D⟩ =
      QuotientGroup.mk ⟨leviHom φ he D, hLX D⟩ * a
    rw [ha, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (RadicalLabels.leviHom_mul_z φ he hzC D).symm
  have hcomm : ∀ (s : Multiplicative (ZMod 2)) (D : GL (Fin 3) (ZMod 2)),
      Commute (fz s) (gL D) := fun s D => (hca D).pow_left _
  set ψ₀ := fz.noncommCoprod gL hcomm with hψ₀def
  have hψ₀ : ∀ (s : ZMod 2) (D : GL (Fin 3) (ZMod 2)) (h : z ^ s.val * leviHom φ he D ∈ X),
      ψ₀ (Multiplicative.ofAdd s, D) = QuotientGroup.mk ⟨_, h⟩ := by
    intro s D h
    rw [hψ₀def, MonoidHom.noncommCoprod_apply]
    change a ^ s.val * QuotientGroup.mk ⟨leviHom φ he D, hLX D⟩ = _
    rw [ha, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
    congr 1
  have hinj : Function.Injective ψ₀ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨s, D⟩ h1
    obtain ⟨s, rfl⟩ : ∃ s' : ZMod 2, Multiplicative.ofAdd s' = s := ⟨Multiplicative.toAdd s, rfl⟩
    have hmem : z ^ s.val * leviHom φ he D ∈ X := mul_mem (pow_mem hzX _) (hLX D)
    rw [hψ₀ s D hmem, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    change z ^ s.val * leviHom φ he D ∈ C₂ at h1
    have hcz : z ^ s.val * leviHom φ he D * z = z * (z ^ s.val * leviHom φ he D) := by
      calc z ^ s.val * leviHom φ he D * z = z ^ s.val * (leviHom φ he D * z) := mul_assoc _ _ _
        _ = z ^ s.val * (z * leviHom φ he D) := by rw [RadicalLabels.leviHom_mul_z φ he hzC D]
        _ = z ^ s.val * z * leviHom φ he D := (mul_assoc _ _ _).symm
        _ = z * z ^ s.val * leviHom φ he D := by rw [(Commute.self_pow z s.val).eq]
        _ = z * (z ^ s.val * leviHom φ he D) := mul_assoc _ _ _
    have hA : z ^ s.val * leviHom φ he D ∈ 𝒜 := (hC₂z _ h1).1 hcz
    have hLS := leviHom_mem_stab hzC hsup hinf hb hnd hV φ he D
    have hzsS : z ^ s.val ∈ 𝒮 := pow_mem hzS _
    have hσ1 : σ (⟨z ^ s.val, hzsS⟩ * ⟨leviHom φ he D, hLS⟩) = 1 := by
      have h2 : (⟨z ^ s.val, hzsS⟩ * ⟨leviHom φ he D, hLS⟩ : 𝒮) ∈ σ.ker := by
        rw [hσker, mem_subgroupOf]
        exact mem_sup_left hA
      exact h2
    have hσz : σ ⟨z ^ s.val, hzsS⟩ = 1 := by
      have h2 : (⟨z ^ s.val, hzsS⟩ : 𝒮) ∈ σ.ker := by
        rw [hσker, mem_subgroupOf]
        exact mem_sup_right (pow_mem (mem_zpowers z) _)
      exact h2
    rw [map_mul, hσz, one_mul, hσL] at hσ1
    subst hσ1
    rw [map_one, mul_one] at hA
    have hs : z ^ s.val = 1 := by
      have h2 : z ^ s.val ∈ 𝒜 ⊓ zpowers z := mem_inf.2 ⟨hA, pow_mem (mem_zpowers z) _⟩
      rwa [hAz, mem_bot] at h2
    have hs0 : s = 0 := (RadicalLabels.zPow_eq_one_iff hz).1 hs
    subst hs0
    rfl
  have hrange : ∀ p, ψ₀ p ∈ centralizer {a} := by
    rintro ⟨s, D⟩
    rw [mem_centralizer_singleton_iff, hψ₀def, MonoidHom.noncommCoprod_apply]
    exact (((Commute.refl a).pow_left _).mul_left (hca D).symm).eq
  have hsurj : ∀ q ∈ centralizer {a}, ∃ p, ψ₀ p = q := by
    intro q hq
    rw [ha, centralizer_eq_map hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂R hC₂z hC₂e hC₂comm
      hzX] at hq
    obtain ⟨x, hxN, rfl⟩ := hq
    have hxN' : (x : G) ∈ 𝒩 := hxN
    have hxm : (x : G) ∈ (𝒟 : Set G) * (𝒮 : Set G) := by
      rw [hDS]
      exact hxN'
    obtain ⟨d, hd, m, hm, hdm⟩ := Set.mem_mul.1 hxm
    have hd' : d ∈ (zpowers z : Set G) * (C₂ : Set G) := by
      rw [hC₂z']
      exact hd
    obtain ⟨t, ht, c, hc, rfl⟩ := Set.mem_mul.1 hd'
    set D₀ := σ ⟨m, hm⟩ with hD₀
    have hLS := leviHom_mem_stab hzC hsup hinf hb hnd hV φ he D₀
    have hr : m * (leviHom φ he D₀)⁻¹ ∈ ℛ := by
      have h2 : (⟨m, hm⟩ * (⟨leviHom φ he D₀, hLS⟩ : 𝒮)⁻¹ : 𝒮) ∈ σ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσL, ← hD₀, mul_inv_cancel]
      rw [hσker, mem_subgroupOf] at h2
      exact h2
    obtain ⟨a', ha', t', ht', hat'⟩ := (mem_sup_of_le_centralizer
      (FusionOrbits.zpowers_le_centralizer_pullSub φ hzC _)).1 hr
    have hAC₂ : 𝒜 ≤ C₂ := hC₂R ▸ inf_le_left
    obtain ⟨s, hs⟩ : ∃ s : ZMod 2, t * t' = z ^ s.val := by
      rcases eq_one_or_eq_of_mem_zpowers hz (mul_mem ht ht') with h | h
      · exact ⟨0, by rw [h, ZMod.val_zero, pow_zero]⟩
      · exact ⟨1, by rw [h]; exact (pow_one z).symm⟩
    have ht'X : t' ∈ X := zpowers_le.2 hzX ht'
    have hc' : t'⁻¹ * (c * a') * t' ∈ C₂ := by
      have h2 := (mem_normalizer_iff.1 (inv_mem ht'X) _).1 (mul_mem hc (hAC₂ ha'))
      rwa [inv_inv] at h2
    have hx : (x : G) = z ^ s.val * (t'⁻¹ * (c * a') * t') * leviHom φ he D₀ := by
      rw [← hs, ← hdm, show m = a' * t' * leviHom φ he D₀ by rw [hat']; group]
      group
    refine ⟨(Multiplicative.ofAdd s, D₀), ?_⟩
    rw [hψ₀ s D₀ (mul_mem (pow_mem hzX _) (hLX D₀)), QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    change (z ^ s.val * leviHom φ he D₀)⁻¹ * (x : G) ∈ C₂
    rw [hx, show (z ^ s.val * leviHom φ he D₀)⁻¹ * (z ^ s.val * (t'⁻¹ * (c * a') * t') *
      leviHom φ he D₀) = (leviHom φ he D₀)⁻¹ * (t'⁻¹ * (c * a') * t') * (leviHom φ he D₀)⁻¹⁻¹ by
        group]
    exact (mem_normalizer_iff.1 (inv_mem (hLX D₀)) _).1 hc'
  refine ⟨MulEquiv.ofBijective (ψ₀.codRestrict _ hrange) ⟨fun p p' h =>
    hinj (congrArg Subtype.val h), fun q => ?_⟩, fun s g h => ?_⟩
  · obtain ⟨p, hp⟩ := hsurj q q.2
    exact ⟨p, Subtype.ext hp⟩
  · exact hψ₀ s g h

include hzC hsup hinf hz hb hnd hV he halt in
theorem card_centralizer {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂z' : ((zpowers z : Set G) * (C₂ : Set G)) = 𝒟)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂)
    (hC₂comm : {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} =
      (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G))
    (hzX : z ∈ normalizer (C₂ : Set G)) :
    Nat.card (centralizer {(QuotientGroup.mk ⟨z, hzX⟩ :
      normalizer (C₂ : Set G) ⧸ C₂.subgroupOf (normalizer (C₂ : Set G)))}) = 2 * 168 := by
  obtain ⟨ψ, -⟩ := exists_mulEquiv hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂R hC₂z' hC₂z hC₂e
    hC₂N hC₂comm hzX
  rw [← Nat.card_congr ψ.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod, card_GL_three_two]

include hzC hsup hinf hz hb hnd hV he halt in
theorem exists_ne_comm {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂c : Nat.card C₂ = 512)
    (hC₂R : C₂ ⊓ ℛ = 𝒜) (hC₂z' : ((zpowers z : Set G) * (C₂ : Set G)) = 𝒟)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂)
    (hC₂comm : {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} =
      (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G))
    (hzX : z ∈ normalizer (C₂ : Set G))
    (P : Sylow 2 (normalizer (C₂ : Set G) ⧸ C₂.subgroupOf (normalizer (C₂ : Set G)))) :
    ∃ y ∈ P, y * QuotientGroup.mk ⟨z, hzX⟩ ≠ QuotientGroup.mk ⟨z, hzX⟩ * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  simp only [not_exists, not_and, ne_eq, not_not] at hcon
  have hle : (P : Subgroup (normalizer (C₂ : Set G) ⧸ C₂.subgroupOf (normalizer (C₂ : Set G)))) ≤
      centralizer {(QuotientGroup.mk ⟨z, hzX⟩ :
        normalizer (C₂ : Set G) ⧸ C₂.subgroupOf (normalizer (C₂ : Set G)))} :=
    fun y hy => mem_centralizer_singleton_iff.2 (hcon y hy)
  have h1 := Subgroup.card_dvd_of_le hle
  rw [card_centralizer hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂R hC₂z' hC₂z hC₂e hC₂N hC₂comm
    hzX] at h1
  have h2 : 2 ^ 5 ∣ Nat.card P := by
    rw [P.card_eq_multiplicity]
    exact Nat.pow_dvd_pow 2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      Nat.card_pos.ne').1 (two_pow_five_dvd hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂c hC₂R
        hC₂z' hC₂z hC₂e hC₂N))
  exact not_two_pow_five_dvd (h2.trans h1)

omit [Finite G] in
include hzC hinf hz hb hnd hV he in
theorem orderOf_mk_z {C₂ : Subgroup G} (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜)
    (hzX : z ∈ normalizer (C₂ : Set G)) :
    orderOf (QuotientGroup.mk ⟨z, hzX⟩ :
      normalizer (C₂ : Set G) ⧸ C₂.subgroupOf (normalizer (C₂ : Set G))) = 2 := by
  obtain ⟨hAe, hAc, -, -⟩ := pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  obtain ⟨hAz, -, -⟩ := sup_facts hzC hinf hz (pullSub_le φ _) hAe hAc
  have hzC₂ : z ∉ C₂ := by
    intro h
    have h1 : z ∈ 𝒜 ⊓ zpowers z := mem_inf.2 ⟨(hC₂z z h).1 rfl, mem_zpowers z⟩
    rw [hAz, mem_bot] at h1
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← QuotientGroup.mk_mul, show (⟨z, hzX⟩ : normalizer (C₂ : Set G)) * ⟨z, hzX⟩ = 1 from
      Subtype.ext (z_mul_self hz), QuotientGroup.mk_one]
  · rw [Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hzC₂

include hzC hsup hinf hz hb hnd hV he halt in
theorem pCore_eq_bot {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂c : Nat.card C₂ = 512)
    (hC₂R : C₂ ⊓ ℛ = 𝒜) (hC₂z' : ((zpowers z : Set G) * (C₂ : Set G)) = 𝒟)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂)
    (hC₂comm : {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} =
      (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G))
    (hzX : z ∈ normalizer (C₂ : Set G)) :
    CFSG.Assembly.pCore 2 (normalizer (C₂ : Set G) ⧸ C₂.subgroupOf (normalizer (C₂ : Set G))) =
      ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := normalizer (C₂ : Set G) with hX
  set a : X ⧸ C₂.subgroupOf X := QuotientGroup.mk ⟨z, hzX⟩ with ha
  set Q := CFSG.Assembly.pCore 2 (X ⧸ C₂.subgroupOf X) with hQdef
  have hQn : Q.Normal :=
    CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_normal_assembly 2 _
  have hQ2 : IsPGroup 2 Q :=
    CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 _
  have hao : orderOf a = 2 := orderOf_mk_z hzC hinf hz hb hnd hV φ he hC₂z hzX
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hao
    exact absurd hao (by norm_num)
  have hnc : ¬ ∀ y : X ⧸ C₂.subgroupOf X, y * a = a * y := by
    intro hall
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (X ⧸ C₂.subgroupOf X)))
    obtain ⟨y, -, hy⟩ := exists_ne_comm hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂c hC₂R
      hC₂z' hC₂z hC₂e hC₂N hC₂comm hzX P
    exact hy (hall y)
  by_contra hQ
  have hfix : ∃ q ∈ Q, q ≠ 1 ∧ q * a = a * q := by
    let _ : MulAction (zpowers a) Q :=
      MulAction.compHom Q ((MulAut.conjNormal (H := Q)).comp (zpowers a).subtype)
    have hW : IsPGroup 2 (zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
    have hmod := hW.card_modEq_card_fixedPoints Q
    have h1mem : (1 : Q) ∈ MulAction.fixedPoints (zpowers a) Q := by
      intro g
      apply Subtype.ext
      change (g : X ⧸ C₂.subgroupOf X) * 1 * (g : X ⧸ C₂.subgroupOf X)⁻¹ = 1
      group
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hQ (Subgroup.card_eq_one.1 (by rw [hk, pow_zero]))
    have hpos : 0 < Nat.card (MulAction.fixedPoints (zpowers a) Q) := by
      have : Nonempty (MulAction.fixedPoints (zpowers a) Q) := ⟨⟨1, h1mem⟩⟩
      exact Nat.card_pos
    have h2 : 1 < Nat.card (MulAction.fixedPoints (zpowers a) Q) := by
      rw [hk] at hmod
      unfold Nat.ModEq at hmod
      have h3 : 2 ^ k % 2 = 0 := by
        obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        rw [pow_succ, Nat.mul_mod_left]
      omega
    have : Nontrivial (MulAction.fixedPoints (zpowers a) Q) :=
      Finite.one_lt_card_iff_nontrivial.mp h2
    obtain ⟨⟨q, hq⟩, hq1⟩ := exists_ne (⟨1, h1mem⟩ : MulAction.fixedPoints (zpowers a) Q)
    refine ⟨q, q.2, fun h => hq1 (Subtype.ext (Subtype.ext h)), ?_⟩
    have h4 : a * (q : X ⧸ C₂.subgroupOf X) * a⁻¹ = q :=
      congrArg Subtype.val (hq ⟨a, mem_zpowers a⟩)
    calc (q : X ⧸ C₂.subgroupOf X) * a = a * q * a⁻¹ * a := by rw [h4]
      _ = a * q := by group
  have hLX : ∀ D : GL (Fin 3) (ZMod 2), leviHom φ he D ∈ X := by
    intro D
    have hl := (mem_inf.1 (leviHom_mem_stab hzC hsup hinf hb hnd hV φ he D)).1
    rw [hX, mem_normalizer_iff]
    intro c
    refine ⟨hC₂N _ hl c, fun hc => ?_⟩
    have h1 := hC₂N _ (inv_mem hl) _ hc
    rwa [show (leviHom φ he D)⁻¹ * (leviHom φ he D * c * (leviHom φ he D)⁻¹) *
      (leviHom φ he D)⁻¹⁻¹ = c by group] at h1
  set C := centralizer ({a} : Set (X ⧸ C₂.subgroupOf X)) with hC
  set M := Q ⊓ C with hM
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂R hC₂z' hC₂z
    hC₂e hC₂N hC₂comm hzX
  have hMC : (M.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact ⟨hQn.conj_mem _ hn.1 (g : X ⧸ C₂.subgroupOf X), (g * n * g⁻¹).2⟩⟩
  have hM2 : IsPGroup 2 (M.subgroupOf C) :=
    (hQ2.to_le inf_le_left).comap_of_injective C.subtype C.subtype_injective
  set N := ((M.subgroupOf C).map ψ.symm.toMonoidHom).map
    (MonoidHom.snd (Multiplicative (ZMod 2)) (GL (Fin 3) (ZMod 2))) with hN
  have hNn : N.Normal :=
    (hMC.map _ ψ.symm.surjective).map _ fun g => ⟨(1, g), rfl⟩
  have hN2 : IsPGroup 2 N := (hM2.map _).map _
  have hNbot : N = ⊥ := eq_bot_of_normal_isPGroup_two N hNn hN2
  have hMa : M ≤ zpowers a := by
    intro m hm
    have hmC : m ∈ C := hm.2
    set p := ψ.symm ⟨m, hmC⟩ with hp
    have hp2 : p.2 = 1 := by
      have h1 : p.2 ∈ N := ⟨p, ⟨⟨m, hmC⟩, hm, rfl⟩, rfl⟩
      rw [hNbot, mem_bot] at h1
      exact h1
    have hmψ : (⟨m, hmC⟩ : C) = ψ p := by rw [hp, MulEquiv.apply_symm_apply]
    have hp' : p = (Multiplicative.ofAdd (Multiplicative.toAdd p.1), 1) := Prod.ext rfl hp2
    rw [hp'] at hmψ
    have h5 := congrArg Subtype.val hmψ
    rw [hψ _ _ (mul_mem (pow_mem hzX _) (hLX 1))] at h5
    change m = _ at h5
    rw [h5, show (⟨z ^ (Multiplicative.toAdd p.1).val * leviHom φ he 1,
      mul_mem (pow_mem hzX _) (hLX 1)⟩ : X) = ⟨z, hzX⟩ ^ (Multiplicative.toAdd p.1).val from
        Subtype.ext (by
          change z ^ (Multiplicative.toAdd p.1).val * leviHom φ he 1 =
            z ^ (Multiplicative.toAdd p.1).val
          rw [map_one, mul_one]), QuotientGroup.mk_pow]
    exact pow_mem (mem_zpowers a) _
  obtain ⟨q, hqQ, hq1, hqa⟩ := hfix
  have haQ : a ∈ Q := by
    rcases eq_one_or_eq_of_mem_zpowers hao (hMa ⟨hqQ, mem_centralizer_singleton_iff.2 hqa⟩) with
      h | h
    · exact absurd h hq1
    · exact h ▸ hqQ
  have hQa : Q ≤ zpowers a := by
    by_contra hle
    have hlt : (zpowers a).subgroupOf Q < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => hle fun y hy => ?_
      have h1 : (⟨y, hy⟩ : Q) ∈ (zpowers a).subgroupOf Q := h ▸ mem_top _
      exact h1
    have := hQ2.isNilpotent
    have hnc' := Group.normalizerCondition_of_isNilpotent _ hlt
    obtain ⟨x, hx, hxa⟩ := IsConcreteLE.exists_of_lt hnc'
    have hxa' : (x : X ⧸ C₂.subgroupOf X) * a * (x : X ⧸ C₂.subgroupOf X)⁻¹ ∈ zpowers a := by
      have h1 := (mem_normalizer_iff.1 hx ⟨a, haQ⟩).1 (by
        rw [mem_subgroupOf]
        exact mem_zpowers a)
      exact h1
    have hx1 : (x : X ⧸ C₂.subgroupOf X) * a * (x : X ⧸ C₂.subgroupOf X)⁻¹ = a := by
      rcases eq_one_or_eq_of_mem_zpowers hao hxa' with h | h
      · exfalso
        apply ha1
        calc a = (x : X ⧸ C₂.subgroupOf X)⁻¹ * ((x : X ⧸ C₂.subgroupOf X) * a *
              (x : X ⧸ C₂.subgroupOf X)⁻¹) * x := by group
          _ = 1 := by rw [h]; group
      · exact h
    apply hxa
    rw [mem_subgroupOf]
    refine hMa ⟨x.2, mem_centralizer_singleton_iff.2 ?_⟩
    calc (x : X ⧸ C₂.subgroupOf X) * a = (x : X ⧸ C₂.subgroupOf X) * a *
          (x : X ⧸ C₂.subgroupOf X)⁻¹ * x := by group
      _ = a * x := by rw [hx1]
  apply hnc
  intro y
  have h1 : y * a * y⁻¹ ∈ zpowers a := hQa (hQn.conj_mem a haQ y)
  rcases eq_one_or_eq_of_mem_zpowers hao h1 with h | h
  · exfalso
    apply ha1
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  · calc y * a = y * a * y⁻¹ * y := by group
      _ = a * y := by rw [h]

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
