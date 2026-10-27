module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64PointStabilizer
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64Lagrangian
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveFullCoset
public import CFSG.ClassicalGroups.Alternating.Generation

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open OddQuadraticFive
open LinearMap (BilinForm)
open scoped Pointwise commutatorElement

section Transport

variable {X : Type*} [Group X]

theorem mem_map_center_subtype_iff {K : Subgroup X} {x : X} :
    x ∈ (center K).map K.subtype ↔ x ∈ K ∧ ∀ k ∈ K, k * x = x * k := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun k hk => congrArg Subtype.val (mem_center_iff.1 hy ⟨k, hk⟩)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.2 fun k => Subtype.ext (hc k k.2), rfl⟩

theorem mem_map_upperCentralSeries_two_iff {K : Subgroup X} {x : X} :
    x ∈ (Subgroup.upperCentralSeries K 2).map K.subtype ↔
      x ∈ K ∧ ∀ y ∈ K, ∀ k ∈ K, k * ⁅x, y⁆ = ⁅x, y⁆ * k := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.2, fun y hy k hk => ?_⟩
    have h1 := Subgroup.mem_upperCentralSeries_succ_iff.1 hu ⟨y, hy⟩
    rw [Subgroup.upperCentralSeries_one] at h1
    exact congrArg Subtype.val (mem_center_iff.1 h1 ⟨k, hk⟩)
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_upperCentralSeries_succ_iff.2 fun y => ?_, rfl⟩
    rw [Subgroup.upperCentralSeries_one]
    exact mem_center_iff.2 fun k => Subtype.ext (hc y y.2 k k.2)

end Transport

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "ℬ₁" => ptSub φ z hb e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)

instance ptSub_subgroupOf_normal :
    ((ptSub φ z hb e).subgroupOf (normalizer ((ptSub φ z hb e : Subgroup G) : Set G))).Normal :=
  Subgroup.normal_in_normalizer

abbrev θN₁ : (ptSub φ z hb e).subgroupOf (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) ≃*
    Multiplicative ((𝔼 × ZMod 2) × ZMod 2) :=
  ptLabelOf he hb φ hzC hz hinf le_normalizer

omit hsup in
theorem coe_zz_θN₁ : ((zz (θN₁ he hb φ hzC hinf hz) : 𝒩₁) : G) = z :=
  ptHom_z he hb φ hzC hz

omit hsup in
theorem mem_subA_θN₁_iff (x : 𝒩₁) : x ∈ subA (θN₁ he hb φ hzC hinf hz) ↔ (x : G) ∈ 𝒜₁ := by
  rw [mem_subA]
  constructor
  · rintro ⟨v, rfl⟩
    exact (mem_ptA_iff he hb φ).2 ⟨v, (ptHom_pt he hb φ hzC hz v).symm⟩
  · intro hx
    obtain ⟨v, hv⟩ := (mem_ptA_iff he hb φ).1 hx
    exact ⟨v, Subtype.ext ((ptHom_pt he hb φ hzC hz v).trans hv)⟩

abbrev ptB₁ : G :=
  ptHom he hb φ hzC hz (Multiplicative.ofAdd (((0 : 𝔼), (1 : ZMod 2)), 0))

omit hsup in
theorem ptB₁_mem_normalizer : ptB₁ he hb φ hzC hz ∈ 𝒩₁ := by
  refine le_normalizer ?_
  rw [← range_ptHom he hb φ hzC hz]
  exact ⟨_, rfl⟩

omit hsup in
theorem map_subI_θN₁ :
    (subI (θN₁ he hb φ hzC hinf hz)).map (Subgroup.subtype 𝒩₁) = zpowers (ptB₁ he hb φ hzC hz) := by
  refine le_antisymm ?_ (zpowers_le.2 ⟨bv (θN₁ he hb φ hzC hinf hz) ((1 : ZMod 2) • rV, 0),
    ⟨1, rfl⟩, by rw [one_smul]; rfl⟩)
  rintro _ ⟨x, ⟨c, rfl⟩, rfl⟩
  rcases zmod_two_eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul, Prod.mk_zero_zero, bv_zero, map_one]
    exact one_mem _
  · rw [one_smul]
    exact mem_zpowers _

omit hsup in
theorem mem_subI_θN₁_iff (x : 𝒩₁) :
    x ∈ subI (θN₁ he hb φ hzC hinf hz) ↔ (x : G) ∈ zpowers (ptB₁ he hb φ hzC hz) := by
  rw [← map_subI_θN₁ he hb φ hzC hinf hz]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

omit hsup in
theorem map_subA_θN₁ :
    (subA (θN₁ he hb φ hzC hinf hz)).map (Subgroup.subtype 𝒩₁) = 𝒜₁ := by
  ext x
  rw [mem_map_subtype_iff]
  constructor
  · rintro ⟨hx, hxA⟩
    exact (mem_subA_θN₁_iff he hb φ hzC hinf hz _).1 hxA
  · intro hx
    have hxN : x ∈ 𝒩₁ := le_normalizer (mem_sup_left hx)
    exact ⟨hxN, (mem_subA_θN₁_iff he hb φ hzC hinf hz ⟨x, hxN⟩).2 hx⟩

omit he hnd in
theorem map_ptSub_subgroupOf :
    ((ptSub φ z hb e).subgroupOf 𝒩₁).map (Subgroup.subtype 𝒩₁) = ℬ₁ := by
  rw [subgroupOf_map_subtype, inf_of_le_left le_normalizer]

include hnd hsup hinf in
theorem degree64_point_two_group [Finite G] [FiniteDimensional (ZMod 2) V]
    (hfull₁ : conjClass 𝒩₁ z = z • (𝒜₁ : Set G)) :
    ∃ (lam : ZMod 2) (D₁ F₁ : Subgroup G) (ν₁ : G → 𝔼 × ZMod 2),
      D₁ = CFSG.Assembly.pCoreOf 2 𝒩₁ ∧ F₁ ≤ D₁ ∧ D₁ ≤ 𝒩₁ ∧ ℬ₁ ≤ F₁ ∧
      (∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁) ∧ (∀ n ∈ 𝒩₁, ∀ f ∈ F₁, n * f * n⁻¹ ∈ F₁) ∧
      Nat.card D₁ = 2048 ∧ Nat.card F₁ = 128 ∧
      ((∀ d ∈ D₁, d ^ 2 ∈ ℬ₁) ∧ (∀ d ∈ D₁, ∀ d' ∈ D₁, ⁅d, d'⁆ ∈ ℬ₁) ∧
        Subgroup.relIndex ℬ₁ D₁ = 32) ∧
      Subgroup.relIndex ℬ₁ F₁ = 2 ∧
      ((∀ d ∈ D₁, d ^ 2 ∈ F₁) ∧ (∀ d ∈ D₁, ∀ d' ∈ D₁, ⁅d, d'⁆ ∈ F₁) ∧ F₁.relIndex D₁ = 16) ∧
      (∀ d ∈ D₁, d⁻¹ * z * d = ptHom he hb φ hzC hz (Multiplicative.ofAdd (ν₁ d, 1))) ∧
      (∀ d ∈ D₁, ∀ d' ∈ D₁, ν₁ d = ν₁ d' ↔ d⁻¹ * d' ∈ ℬ₁) ∧
      (∀ v : 𝔼 × ZMod 2, ∃ d ∈ D₁, ν₁ d = v) ∧
      (∀ d ∈ D₁, ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
        d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
          ptHom he hb φ hzC hz (Multiplicative.ofAdd
            (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : 𝔼), (1 : ZMod 2)) + ε • ν₁ d, ε))) ∧
      (∀ d : G, d ∈ F₁ ↔ d ∈ D₁ ∧ (ν₁ d).1 = 0) ∧
      (∀ m ∈ 𝒩₁, ∃ d ∈ D₁, ∃ c ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G), m = d * c) ∧
      D₁ ⊓ centralizer ({z} : Set G) = ℬ₁ ∧
      (∀ n ∈ 𝒩₁, ∀ a ∈ 𝒜₁, n * a * n⁻¹ ∈ 𝒜₁) ∧
      (∀ n ∈ 𝒩₁, n * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * n) ∧
      (center F₁).map F₁.subtype = 𝒜₁ ∧
      closure {x | ∃ f ∈ F₁, f ^ 2 = x} = zpowers (ptB₁ he hb φ hzC hz) ∧
      ⁅ℬ₁, D₁⁆ = 𝒜₁ ∧ ⁅zpowers (ptB₁ he hb φ hzC hz), D₁⁆ = ⊥ ∧
      (lam = 0 → (center D₁).map D₁.subtype = 𝒜₁ ∧ ⁅𝒜₁, D₁⁆ = ⊥) ∧
      (lam = 1 → (center D₁).map D₁.subtype = zpowers (ptB₁ he hb φ hzC hz) ∧
        ⁅𝒜₁, D₁⁆ = zpowers (ptB₁ he hb φ hzC hz) ∧
        𝒜₁ ≤ (Subgroup.upperCentralSeries D₁ 2).map D₁.subtype) ∧
      ((∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁) ∧
        (∀ d ∈ D₁, ∀ d' ∈ D₁, z⁻¹ * ((d * d')⁻¹ * z * (d * d')) *
          (z⁻¹ * (d⁻¹ * z * d) * (z⁻¹ * (d'⁻¹ * z * d')))⁻¹ ∈ zpowers (ptB₁ he hb φ hzC hz)) ∧
        (∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz) ↔ d ∈ F₁) ∧
        (∀ a ∈ 𝒜₁, ∃ d ∈ D₁, (z⁻¹ * (d⁻¹ * z * d))⁻¹ * a ∈ zpowers (ptB₁ he hb φ hzC hz))) ∧
      ((∀ f ∈ F₁, z⁻¹ * (f⁻¹ * z * f) ∈ zpowers (ptB₁ he hb φ hzC hz)) ∧
        (∀ f ∈ F₁, ∀ f' ∈ F₁, z⁻¹ * ((f * f')⁻¹ * z * (f * f')) =
          z⁻¹ * (f⁻¹ * z * f) * (z⁻¹ * (f'⁻¹ * z * f'))) ∧
        (∀ f ∈ F₁, z⁻¹ * (f⁻¹ * z * f) = 1 ↔ f ∈ ℬ₁) ∧
        (∀ i ∈ zpowers (ptB₁ he hb φ hzC hz), ∃ f ∈ F₁, z⁻¹ * (f⁻¹ * z * f) = i)) ∧
      (∀ c ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G), ∀ d : G,
        z⁻¹ * ((c⁻¹ * d * c)⁻¹ * z * (c⁻¹ * d * c)) = c⁻¹ * (z⁻¹ * (d⁻¹ * z * d)) * c) := by
  classical
  set θ := θN₁ he hb φ hzC hinf hz with hθ
  have hzz : ((zz θ : 𝒩₁) : G) = z := coe_zz_θN₁ he hb φ hzC hinf hz
  have hcz : ∀ d : 𝒩₁, (((zz θ)⁻¹ * (d⁻¹ * zz θ * d) : 𝒩₁) : G) = z⁻¹ * ((d : G)⁻¹ * z * d) :=
    fun d => by simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzz]
  have hmem : ∀ v : 𝔼 × ZMod 2,
      ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) ∈ conjClass 𝒩₁ z := fun v => by
    rw [hfull₁]
    exact (mem_smul_ptA_iff he hb φ hzC hz).2 ⟨v, rfl⟩
  have hinvc : ∀ x ∈ conjClass 𝒩₁ z, ∃ v : 𝔼 × ZMod 2,
      ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) = x := fun x hx => by
    rw [hfull₁] at hx
    exact (mem_smul_ptA_iff he hb φ hzC hz).1 hx
  have hE : finrank (ZMod 2) 𝔼 = 4 := finrank_pairOrth_eq he hb hnd
  have hb' : (b.restrict 𝔼).IsAlt := fun x => hb x
  have hnd' : (b.restrict 𝔼).Nondegenerate :=
    hb.restrict_nondegenerate_orthogonal_span_pair (bilin_f_u he) hnd
  have hΩ : ∀ (m : 𝒩₁) (v : 𝔼 × ZMod 2), ∃ v' : 𝔼 × ZMod 2,
      m⁻¹ * bv θ (v, 1) * m = bv θ (v', 1) := by
    intro m v
    obtain ⟨v', hv'⟩ := hinvc _ (conj_mem_conjClass_right m.2 (hmem v))
    exact ⟨v', Subtype.ext hv'.symm⟩
  have hfaith : ∀ m : 𝒩₁, (∀ v : 𝔼 × ZMod 2, m⁻¹ * bv θ (v, 1) * m = bv θ (v, 1)) →
      m ∈ (ptSub φ z hb e).subgroupOf 𝒩₁ := by
    intro m h
    rw [mem_subgroupOf]
    refine mem_ptSub_of_forall_conj he hb hnd φ hzC hsup hinf hz fun v => ?_
    have h1 : (m : G)⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) * m =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) := congrArg Subtype.val (h v)
    rw [mul_assoc, inv_mul_eq_iff_eq_mul] at h1
    exact h1.symm
  have htrans : ∀ v v' : 𝔼 × ZMod 2, ∃ m : 𝒩₁, m⁻¹ * bv θ (v, 1) * m = bv θ (v', 1) := by
    intro v v'
    obtain ⟨n, hn, hnx⟩ := mem_conjClass_iff_right.1 (hmem v)
    obtain ⟨n', hn', hnx'⟩ := mem_conjClass_iff_right.1 (hmem v')
    refine ⟨⟨n, hn⟩⁻¹ * ⟨n', hn'⟩, Subtype.ext ?_⟩
    change (n⁻¹ * n')⁻¹ * ptHom he hb φ hzC hz _ * (n⁻¹ * n') = ptHom he hb φ hzC hz _
    rw [← hnx, ← hnx']
    group
  have hstab : ∀ m : 𝒩₁, m⁻¹ * zz θ * m = zz θ → ∃ s : bilinIsometryGroup (b.restrict 𝔼),
      ∀ v : 𝔼 × ZMod 2, m⁻¹ * bv θ (v, 1) * m = bv θ (hV (polarBilin_ptQuad he) s v, 1) := by
    intro m hm
    have hm' : (m : G)⁻¹ * z * m = z := by
      have h1 := congrArg Subtype.val hm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzz] at h1
      exact h1
    have hmz : (m : G)⁻¹ * z = z * (m : G)⁻¹ := by
      calc (m : G)⁻¹ * z = (m : G)⁻¹ * z * m * (m : G)⁻¹ := by group
        _ = z * (m : G)⁻¹ := by rw [hm']
    obtain ⟨s, hs⟩ := exists_hV_of_mem_stab he hb hnd φ hzC hsup hinf hz (inv_mem m.2) hmz
    refine ⟨s, fun v => Subtype.ext ?_⟩
    have h1 := hs v 1
    rw [inv_inv] at h1
    exact h1
  have hstab' : ∀ s : bilinIsometryGroup (b.restrict 𝔼), ∃ m : 𝒩₁,
      ∀ v : 𝔼 × ZMod 2, m⁻¹ * bv θ (v, 1) * m = bv θ (hV (polarBilin_ptQuad he) s v, 1) := by
    intro s
    refine ⟨⟨(ptLevi he hb φ s)⁻¹, inv_mem (ptLevi_mem_normalizer he hb φ hzC hz s)⟩,
      fun v => Subtype.ext ?_⟩
    change ((ptLevi he hb φ s)⁻¹)⁻¹ * ptHom he hb φ hzC hz _ * (ptLevi he hb φ s)⁻¹ =
      ptHom he hb φ hzC hz _
    rw [inv_inv, ptLevi_conj_ptHom]
  obtain ⟨lam, D, F, ν, hFD, hDn, hFn, hpc, hDc, hFc, hRF, ⟨hsqD, hcomD, -⟩, -,
    ⟨hsqF, hcomF, -⟩, hνz, hνeq, hνsurj, hact, hFiff, hprod, hDH, hAn, hIc, hZF, hsqcl,
    hcomRD, hcomID, hlam0, hlam1, ⟨hqA, hqHom, hqKer, hqSurj⟩, ⟨hiI, hiHom, hiKer, hiSurj⟩, -⟩ :=
    binary_odd_quadratic_five_full_coset_two_group_structure hE hb' hnd' (polarBilin_ptQuad he)
      ((ptSub φ z hb e).subgroupOf 𝒩₁) θ hΩ hfaith htrans hstab hstab'
  set ν₁ : G → 𝔼 × ZMod 2 := fun g => if h : g ∈ 𝒩₁ then ν ⟨g, h⟩ else 0 with hν₁def
  have hν₁ : ∀ (g : G) (h : g ∈ 𝒩₁), ν₁ g = ν ⟨g, h⟩ := fun g h => by
    simp only [hν₁def, h, ↓reduceDIte]
  have hmemD : ∀ {x : G}, x ∈ D.map (Subgroup.subtype 𝒩₁) ↔ ∃ h : x ∈ 𝒩₁, (⟨x, h⟩ : 𝒩₁) ∈ D :=
    mem_map_subtype_iff
  have hmemF : ∀ {x : G}, x ∈ F.map (Subgroup.subtype 𝒩₁) ↔ ∃ h : x ∈ 𝒩₁, (⟨x, h⟩ : 𝒩₁) ∈ F :=
    mem_map_subtype_iff
  have hBF : ℬ₁ ≤ F.map (Subgroup.subtype 𝒩₁) := fun r hr =>
    hmemF.2 ⟨le_normalizer hr, hRF (by rw [mem_subgroupOf]; exact hr)⟩
  have hFD' : F.map (Subgroup.subtype 𝒩₁) ≤ D.map (Subgroup.subtype 𝒩₁) := map_mono hFD
  have hcardB : Nat.card ℬ₁ = 64 := (ptSub_facts he hb hnd φ hzC hinf hz).2.2.1
  have hcardD : Nat.card (D.map (Subgroup.subtype 𝒩₁)) = 2048 := by
    rw [card_map_of_injective (subtype_injective _), hDc]
  have hcardF : Nat.card (F.map (Subgroup.subtype 𝒩₁)) = 128 := by
    rw [card_map_of_injective (subtype_injective _), hFc]
  have hAN : ∀ {a : G}, a ∈ 𝒜₁ → a ∈ 𝒩₁ := fun ha => le_normalizer (mem_sup_left ha)
  have hIN : zpowers (ptB₁ he hb φ hzC hz) ≤ 𝒩₁ :=
    zpowers_le.2 (ptB₁_mem_normalizer he hb φ hzC hz)
  refine ⟨lam, D.map (Subgroup.subtype 𝒩₁), F.map (Subgroup.subtype 𝒩₁), ν₁, ?_, hFD',
    map_subtype_le _, hBF, fun n hn d hd => ?_, fun n hn f hf => ?_, hcardD, hcardF,
    ⟨fun d hd => ?_, fun d hd d' hd' => ?_, ?_⟩, ?_, ⟨fun d hd => ?_, fun d hd d' hd' => ?_, ?_⟩,
    fun d hd => ?_, fun d hd d' hd' => ?_, fun v => ?_, fun d hd v ε => ?_, fun d => ?_,
    fun m hm => ?_, ?_, fun n hn a ha => ?_, fun n hn => ?_, ?_, ?_, ?_, ?_, fun hl => ?_,
    fun hl => ?_, ⟨fun d hd => ?_, fun d hd d' hd' => ?_, fun d hd => ?_, fun a ha => ?_⟩,
    ⟨fun f hf => ?_, fun f hf f' hf' => ?_, fun f hf => ?_, fun i hi => ?_⟩, fun c hc d => ?_⟩
  · rw [CFSG.Assembly.pCoreOf, hpc]
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    exact hmemD.2 ⟨mul_mem (mul_mem hn hd') (inv_mem hn), hDn.conj_mem _ hdD ⟨n, hn⟩⟩
  · obtain ⟨hf', hfF⟩ := hmemF.1 hf
    exact hmemF.2 ⟨mul_mem (mul_mem hn hf') (inv_mem hn), hFn.conj_mem _ hfF ⟨n, hn⟩⟩
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    have h1 := hsqD _ hdD
    rw [mem_subgroupOf] at h1
    exact h1
  · obtain ⟨h1, h1D⟩ := hmemD.1 hd
    obtain ⟨h2, h2D⟩ := hmemD.1 hd'
    have h3 := hcomD _ h1D _ h2D
    rw [mem_subgroupOf] at h3
    exact h3
  · have h := Subgroup.relIndex_mul_card (H := ℬ₁) (K := D.map (Subgroup.subtype 𝒩₁))
    rw [inf_of_le_left (hBF.trans hFD'), hcardB, hcardD] at h
    omega
  · have h := Subgroup.relIndex_mul_card (H := ℬ₁) (K := F.map (Subgroup.subtype 𝒩₁))
    rw [inf_of_le_left hBF, hcardB, hcardF] at h
    omega
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    exact hmemF.2 ⟨pow_mem hd' 2, hsqF _ hdD⟩
  · obtain ⟨h1, h1D⟩ := hmemD.1 hd
    obtain ⟨h2, h2D⟩ := hmemD.1 hd'
    exact hmemF.2 ⟨(⁅(⟨d, h1⟩ : 𝒩₁), (⟨d', h2⟩ : 𝒩₁)⁆).2, hcomF _ h1D _ h2D⟩
  · have h := Subgroup.relIndex_mul_card (H := F.map (Subgroup.subtype 𝒩₁))
      (K := D.map (Subgroup.subtype 𝒩₁))
    rw [inf_of_le_left hFD', hcardF, hcardD] at h
    omega
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    calc d⁻¹ * z * d = ((⟨d, hd'⟩⁻¹ * zz θ * ⟨d, hd'⟩ : 𝒩₁) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzz]
      _ = _ := by rw [hνz _ hdD, hν₁ d hd']; rfl
  · obtain ⟨h1, h1D⟩ := hmemD.1 hd
    obtain ⟨h2, h2D⟩ := hmemD.1 hd'
    rw [hν₁ d h1, hν₁ d' h2, hνeq _ h1D _ h2D, mem_subgroupOf]
    rfl
  · obtain ⟨d, hdD, hdv⟩ := hνsurj v
    refine ⟨d, ⟨d, hdD, rfl⟩, ?_⟩
    rw [hν₁ d d.2]
    exact hdv
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    have h1 := congrArg Subtype.val (hact _ hdD v ε)
    rw [hν₁ d hd']
    exact h1
  · constructor
    · intro hdF
      obtain ⟨hd', hdF'⟩ := hmemF.1 hdF
      obtain ⟨hdD, hd0⟩ := (hFiff _).1 hdF'
      exact ⟨hmemD.2 ⟨hd', hdD⟩, by rw [hν₁ d hd']; exact hd0⟩
    · rintro ⟨hdD, hd0⟩
      obtain ⟨hd', hdD'⟩ := hmemD.1 hdD
      exact hmemF.2 ⟨hd', (hFiff _).2 ⟨hdD', by rw [hν₁ d hd'] at hd0; exact hd0⟩⟩
  · obtain ⟨d, hdD, c, hc, hdc⟩ := hprod ⟨m, hm⟩
    refine ⟨d, ⟨d, hdD, rfl⟩, c, mem_inf.2 ⟨c.2, ?_⟩, congrArg Subtype.val hdc⟩
    have hc' := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hc)
    simp only [Subgroup.coe_mul, hzz] at hc'
    exact mem_centralizer_singleton_iff.2 hc'
  · ext x
    rw [mem_inf, hmemD]
    constructor
    · rintro ⟨⟨hx, hxD⟩, hxz⟩
      have h1 : (⟨x, hx⟩ : 𝒩₁) ∈ D ⊓ centralizer {zz θ} := by
        refine mem_inf.2 ⟨hxD, mem_centralizer_singleton_iff.2 (Subtype.ext ?_)⟩
        simp only [Subgroup.coe_mul, hzz]
        exact mem_centralizer_singleton_iff.1 hxz
      rw [hDH, mem_subgroupOf] at h1
      exact h1
    · intro hx
      have h1 : (⟨x, le_normalizer hx⟩ : 𝒩₁) ∈ (ptSub φ z hb e).subgroupOf 𝒩₁ := by
        rw [mem_subgroupOf]
        exact hx
      rw [← hDH, mem_inf] at h1
      refine ⟨⟨le_normalizer hx, h1.1⟩, mem_centralizer_singleton_iff.2 ?_⟩
      have h2 := congrArg Subtype.val (mem_centralizer_singleton_iff.1 h1.2)
      simp only [Subgroup.coe_mul, hzz] at h2
      exact h2
  · have h1 := hAn.conj_mem ⟨a, hAN ha⟩ ((mem_subA_θN₁_iff he hb φ hzC hinf hz _).2 ha) ⟨n, hn⟩
    exact (mem_subA_θN₁_iff he hb φ hzC hinf hz _).1 h1
  · have hb₁ : bv θ (rV, 0) ∈ subI θ := ⟨1, by rw [one_smul]⟩
    exact congrArg Subtype.val (mem_center_iff.1 (hIc hb₁) ⟨n, hn⟩)
  · ext x
    rw [mem_map_center_subtype_iff]
    constructor
    · rintro ⟨hxF, hc⟩
      obtain ⟨hxN, hxF'⟩ := hmemF.1 hxF
      have h1 : (⟨x, hxN⟩ : 𝒩₁) ∈ (center F).map F.subtype :=
        mem_map_center_subtype_iff.2 ⟨hxF', fun k hk => Subtype.ext (hc k (hmemF.2 ⟨k.2, hk⟩))⟩
      rw [hZF] at h1
      exact (mem_subA_θN₁_iff he hb φ hzC hinf hz _).1 h1
    · intro hx
      have h1 : (⟨x, hAN hx⟩ : 𝒩₁) ∈ (center F).map F.subtype := by
        rw [hZF]
        exact (mem_subA_θN₁_iff he hb φ hzC hinf hz _).2 hx
      obtain ⟨hxF', hc⟩ := mem_map_center_subtype_iff.1 h1
      refine ⟨hmemF.2 ⟨hAN hx, hxF'⟩, fun k hk => ?_⟩
      obtain ⟨hkN, hkF⟩ := hmemF.1 hk
      exact congrArg Subtype.val (hc ⟨k, hkN⟩ hkF)
  · have himg : (Subgroup.subtype 𝒩₁) '' {x | ∃ f ∈ F, f ^ 2 = x} =
        {x | ∃ f ∈ F.map (Subgroup.subtype 𝒩₁), f ^ 2 = x} := by
      ext x
      constructor
      · rintro ⟨y, ⟨f, hf, rfl⟩, rfl⟩
        exact ⟨f, ⟨f, hf, rfl⟩, (map_pow (Subgroup.subtype 𝒩₁) f 2).symm⟩
      · rintro ⟨f, ⟨f', hf', rfl⟩, rfl⟩
        exact ⟨f' ^ 2, ⟨f', hf', rfl⟩, map_pow (Subgroup.subtype 𝒩₁) f' 2⟩
    rw [← himg, ← MonoidHom.map_closure, hsqcl, map_subI_θN₁]
  · calc ⁅ℬ₁, D.map (Subgroup.subtype 𝒩₁)⁆ =
          ⁅((ptSub φ z hb e).subgroupOf 𝒩₁).map (Subgroup.subtype 𝒩₁),
            D.map (Subgroup.subtype 𝒩₁)⁆ := by rw [map_ptSub_subgroupOf]
      _ = ⁅(ptSub φ z hb e).subgroupOf 𝒩₁, D⁆.map (Subgroup.subtype 𝒩₁) :=
          (Subgroup.map_commutator _ _ _).symm
      _ = 𝒜₁ := by rw [hcomRD, map_subA_θN₁]
  · calc ⁅zpowers (ptB₁ he hb φ hzC hz), D.map (Subgroup.subtype 𝒩₁)⁆ =
          ⁅(subI θ).map (Subgroup.subtype 𝒩₁), D.map (Subgroup.subtype 𝒩₁)⁆ := by
            rw [map_subI_θN₁]
      _ = ⁅subI θ, D⁆.map (Subgroup.subtype 𝒩₁) := (Subgroup.map_commutator _ _ _).symm
      _ = ⊥ := by rw [hcomID, Subgroup.map_bot]
  · obtain ⟨h1, h2⟩ := hlam0 hl
    refine ⟨?_, ?_⟩
    · ext x
      rw [mem_map_center_subtype_iff]
      constructor
      · rintro ⟨hxD, hc⟩
        obtain ⟨hxN, hxD'⟩ := hmemD.1 hxD
        have h3 : (⟨x, hxN⟩ : 𝒩₁) ∈ (center D).map D.subtype :=
          mem_map_center_subtype_iff.2 ⟨hxD', fun k hk => Subtype.ext (hc k (hmemD.2 ⟨k.2, hk⟩))⟩
        rw [h1] at h3
        exact (mem_subA_θN₁_iff he hb φ hzC hinf hz _).1 h3
      · intro hx
        have h3 : (⟨x, hAN hx⟩ : 𝒩₁) ∈ (center D).map D.subtype := by
          rw [h1]
          exact (mem_subA_θN₁_iff he hb φ hzC hinf hz _).2 hx
        obtain ⟨hxD', hc⟩ := mem_map_center_subtype_iff.1 h3
        refine ⟨hmemD.2 ⟨hAN hx, hxD'⟩, fun k hk => ?_⟩
        obtain ⟨hkN, hkD⟩ := hmemD.1 hk
        exact congrArg Subtype.val (hc ⟨k, hkN⟩ hkD)
    · calc ⁅𝒜₁, D.map (Subgroup.subtype 𝒩₁)⁆ =
            ⁅(subA θ).map (Subgroup.subtype 𝒩₁), D.map (Subgroup.subtype 𝒩₁)⁆ := by
              rw [map_subA_θN₁]
        _ = ⁅subA θ, D⁆.map (Subgroup.subtype 𝒩₁) := (Subgroup.map_commutator _ _ _).symm
        _ = ⊥ := by rw [h2, Subgroup.map_bot]
  · obtain ⟨h1, h2, h3⟩ := hlam1 hl
    refine ⟨?_, ?_, fun a ha => ?_⟩
    · ext x
      rw [mem_map_center_subtype_iff]
      constructor
      · rintro ⟨hxD, hc⟩
        obtain ⟨hxN, hxD'⟩ := hmemD.1 hxD
        have h4 : (⟨x, hxN⟩ : 𝒩₁) ∈ (center D).map D.subtype :=
          mem_map_center_subtype_iff.2 ⟨hxD', fun k hk => Subtype.ext (hc k (hmemD.2 ⟨k.2, hk⟩))⟩
        rw [h1] at h4
        exact (mem_subI_θN₁_iff he hb φ hzC hinf hz _).1 h4
      · intro hx
        have h4 : (⟨x, hIN hx⟩ : 𝒩₁) ∈ (center D).map D.subtype := by
          rw [h1]
          exact (mem_subI_θN₁_iff he hb φ hzC hinf hz _).2 hx
        obtain ⟨hxD', hc⟩ := mem_map_center_subtype_iff.1 h4
        refine ⟨hmemD.2 ⟨hIN hx, hxD'⟩, fun k hk => ?_⟩
        obtain ⟨hkN, hkD⟩ := hmemD.1 hk
        exact congrArg Subtype.val (hc ⟨k, hkN⟩ hkD)
    · calc ⁅𝒜₁, D.map (Subgroup.subtype 𝒩₁)⁆ =
            ⁅(subA θ).map (Subgroup.subtype 𝒩₁), D.map (Subgroup.subtype 𝒩₁)⁆ := by
              rw [map_subA_θN₁]
        _ = ⁅subA θ, D⁆.map (Subgroup.subtype 𝒩₁) := (Subgroup.map_commutator _ _ _).symm
        _ = zpowers (ptB₁ he hb φ hzC hz) := by rw [h2, map_subI_θN₁]
    · have h4 := h3 ((mem_subA_θN₁_iff he hb φ hzC hinf hz ⟨a, hAN ha⟩).2 ha)
      obtain ⟨haD, hc⟩ := mem_map_upperCentralSeries_two_iff.1 h4
      refine mem_map_upperCentralSeries_two_iff.2 ⟨hmemD.2 ⟨hAN ha, haD⟩, fun y hy k hk => ?_⟩
      obtain ⟨hyN, hyD⟩ := hmemD.1 hy
      obtain ⟨hkN, hkD⟩ := hmemD.1 hk
      exact congrArg Subtype.val (hc ⟨y, hyN⟩ hyD ⟨k, hkN⟩ hkD)
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    have h1 := (mem_subA_θN₁_iff he hb φ hzC hinf hz _).1 (hqA _ hdD)
    rw [hcz] at h1
    exact h1
  · obtain ⟨h1, h1D⟩ := hmemD.1 hd
    obtain ⟨h2, h2D⟩ := hmemD.1 hd'
    have h3 := (mem_subI_θN₁_iff he hb φ hzC hinf hz _).1 (hqHom _ h1D _ h2D)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzz] at h3
    exact h3
  · obtain ⟨hd', hdD⟩ := hmemD.1 hd
    have h1 := hqKer _ hdD
    rw [mem_subI_θN₁_iff, hcz] at h1
    refine h1.trans ⟨fun h => hmemF.2 ⟨hd', h⟩, fun h => ?_⟩
    obtain ⟨_, h2⟩ := hmemF.1 h
    exact h2
  · obtain ⟨d, hdD, hd⟩ := hqSurj ⟨a, hAN ha⟩ ((mem_subA_θN₁_iff he hb φ hzC hinf hz _).2 ha)
    refine ⟨d, ⟨d, hdD, rfl⟩, ?_⟩
    have h1 := (mem_subI_θN₁_iff he hb φ hzC hinf hz _).1 hd
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzz] at h1
    exact h1
  · obtain ⟨hf', hfF⟩ := hmemF.1 hf
    have h1 := (mem_subI_θN₁_iff he hb φ hzC hinf hz _).1 (hiI _ hfF)
    rw [hcz] at h1
    exact h1
  · obtain ⟨h1, h1F⟩ := hmemF.1 hf
    obtain ⟨h2, h2F⟩ := hmemF.1 hf'
    have h3 := congrArg Subtype.val (hiHom _ h1F _ h2F)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzz] at h3
    exact h3
  · obtain ⟨hf', hfF⟩ := hmemF.1 hf
    have h1 := hiKer _ hfF
    rw [mem_subgroupOf, ← OneMemClass.coe_eq_one, hcz] at h1
    exact h1
  · have hiI' : (⟨i, hIN hi⟩ : 𝒩₁) ∈ subI θ := (mem_subI_θN₁_iff he hb φ hzC hinf hz _).2 hi
    obtain ⟨f, hfF, hf⟩ := hiSurj _ hiI'
    refine ⟨f, ⟨f, hfF, rfl⟩, ?_⟩
    have h1 := congrArg Subtype.val hf
    rw [hcz] at h1
    exact h1
  · have hcz' : c * z = z * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
    have h1 : c * z * c⁻¹ = z := by rw [hcz', mul_inv_cancel_right]
    have h2 : z⁻¹ * c⁻¹ = c⁻¹ * z⁻¹ := by rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hcz']
    calc z⁻¹ * ((c⁻¹ * d * c)⁻¹ * z * (c⁻¹ * d * c)) =
        z⁻¹ * c⁻¹ * (d⁻¹ * (c * z * c⁻¹) * d) * c := by group
      _ = c⁻¹ * (z⁻¹ * (d⁻¹ * z * d)) * c := by rw [h1, h2]; group

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
