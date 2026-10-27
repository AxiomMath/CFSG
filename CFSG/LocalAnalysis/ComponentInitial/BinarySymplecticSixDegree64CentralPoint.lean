module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NoncentralPoint
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveCentral

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

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

include hnd hsup hinf in
theorem degree64_central_point [Finite G] [FiniteDimensional (ZMod 2) V] {D₁ : Subgroup G}
    {ν₁ : G → 𝔼 × ZMod 2} {lam : ZMod 2} (hlam : lam = 0)
    (hD₁N : D₁ ≤ 𝒩₁) (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁) (hBD₁ : ℬ₁ ≤ D₁)
    (hν₁surj : ∀ v : 𝔼 × ZMod 2, ∃ d ∈ D₁, ν₁ d = v)
    (hact₁ : ∀ d ∈ D₁, ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : 𝔼), (1 : ZMod 2)) + ε • ν₁ d, ε)))
    (hprod₁ : ∀ m ∈ 𝒩₁, ∃ d ∈ D₁, ∃ c ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G),
      m = d * c) :
    ∃ (C₁ : Subgroup G) (τ₁ : G → 𝔼 × ZMod 2) (α β : ZMod 2),
      C₁ ≤ D₁ ∧ (∀ m ∈ 𝒩₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁) ∧ Nat.card C₁ = 1024 ∧
      zpowers z ⊔ C₁ = D₁ ∧ C₁ ⊓ ℬ₁ = 𝒜₁ ∧
      (∀ c ∈ C₁, z⁻¹ * c⁻¹ * z * c = ptHom he hb φ hzC hz (Multiplicative.ofAdd (τ₁ c, 0))) ∧
      (∀ c ∈ C₁, ∀ c' ∈ C₁, τ₁ (c * c') = τ₁ c + τ₁ c') ∧
      (∀ v : 𝔼 × ZMod 2, ∃ c ∈ C₁, τ₁ c = v) ∧ (∀ c ∈ C₁, τ₁ c = 0 ↔ c ∈ 𝒜₁) ∧
      (∀ (s : bilinIsometryGroup (b.restrict 𝔼)), ∀ c ∈ C₁,
        τ₁ (ptLevi he hb φ s * c * (ptLevi he hb φ s)⁻¹) =
          OddQuadraticFive.hV (polarBilin_ptQuad he) s (τ₁ c)) ∧
      (∀ x ∈ C₁, z⁻¹ * (x⁻¹ * z * x) ∈ zpowers (ptB₁ he hb φ hzC hz) →
        ∀ y ∈ C₁, x * y = y * x) ∧
      Nat.card ↥((C₁ : Set G) ∩ {d | d ∈ D₁ ∧
        z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)}) = 64 ∧
      (∀ c ∈ C₁, c ^ 2 = ptHom he hb φ hzC hz (Multiplicative.ofAdd
        (α • τ₁ c + (β * OddQuadraticFive.qV (ptQuad e) (τ₁ c)) • OddQuadraticFive.rV, 0))) ∧
      ⁅C₁, C₁⁆ ≤ zpowers (ptB₁ he hb φ hzC hz) ∧
      (α = 1 → ∀ c ∈ C₁, c ^ 2 = 1 →
        z⁻¹ * (c⁻¹ * z * c) ∈ zpowers (ptB₁ he hb φ hzC hz)) ∧
      (α = 0 → closure {x | ∃ y ∈ C₁, y ^ 2 = x} ≤ zpowers (ptB₁ he hb φ hzC hz)) := by
  classical
  subst hlam
  have hE : finrank (ZMod 2) 𝔼 = 4 := finrank_pairOrth_eq he hb hnd
  have hb' : (b.restrict 𝔼).IsAlt := fun x => hb x
  have hnd' : (b.restrict 𝔼).Nondegenerate :=
    hb.restrict_nondegenerate_orthogonal_span_pair (bilin_f_u he) hnd
  have hBn : ((ptSub φ z hb e).subgroupOf D₁).Normal := ⟨fun x hx d => by
    rw [mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.1 (hD₁N d.2) x).1 hx⟩
  set θ := ptLabelOf he hb φ hzC hz hinf hBD₁ with hθ
  have hzz : ((OddQuadraticFive.zz θ : D₁) : G) = z := ptHom_z he hb φ hzC hz
  have hconj : ∀ d : D₁, ∃ a : 𝔼 × ZMod 2, ∀ v : 𝔼 × ZMod 2,
      d⁻¹ * OddQuadraticFive.bv θ (v, 1) * d = OddQuadraticFive.bv θ (v + a, 1) := by
    intro d
    refine ⟨ν₁ d, fun v => Subtype.ext ?_⟩
    have h := hact₁ d d.2 v 1
    rw [zero_mul, zero_smul, add_zero, one_smul] at h
    exact h
  have hsurj : ∀ a : 𝔼 × ZMod 2, ∃ d : D₁, ∀ v : 𝔼 × ZMod 2,
      d⁻¹ * OddQuadraticFive.bv θ (v, 1) * d = OddQuadraticFive.bv θ (v + a, 1) := by
    intro a
    obtain ⟨d, hd, hda⟩ := hν₁surj a
    refine ⟨⟨d, hd⟩, fun v => Subtype.ext ?_⟩
    have h := hact₁ d hd v 1
    rw [hda, zero_mul, zero_smul, add_zero, one_smul] at h
    exact h
  have hfaith : ∀ d : D₁, (∀ v : 𝔼 × ZMod 2,
      d⁻¹ * OddQuadraticFive.bv θ (v, 1) * d = OddQuadraticFive.bv θ (v, 1)) →
        d ∈ (ptSub φ z hb e).subgroupOf D₁ := by
    intro d h
    rw [mem_subgroupOf]
    refine mem_ptSub_of_forall_conj he hb hnd φ hzC hsup hinf hz fun v => ?_
    have h1 : (d : G)⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 1)) := congrArg Subtype.val (h v)
    rw [mul_assoc, inv_mul_eq_iff_eq_mul] at h1
    exact h1.symm
  have hLD : ∀ s, ptLevi he hb φ s ∈ normalizer (D₁ : Set G) := fun s =>
    mem_normalizer_of_map_le (by
      rintro _ ⟨d, hd, rfl⟩
      exact hD₁n _ (ptLevi_mem_normalizer he hb φ hzC hz s) d hd)
  set act : bilinIsometryGroup (b.restrict 𝔼) →* MulAut D₁ :=
    (conjNormalizer D₁).comp ((ptLevi he hb φ).codRestrict _ hLD) with hact_def
  have hcoe : ∀ s (d : D₁), ((act s d : D₁) : G) = ptLevi he hb φ s * d * (ptLevi he hb φ s)⁻¹ :=
    fun s d => rfl
  have hact : ∀ (s : bilinIsometryGroup (b.restrict 𝔼)) (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      act s (OddQuadraticFive.bv θ (v, ε)) =
        OddQuadraticFive.bv θ (OddQuadraticFive.hV (polarBilin_ptQuad he) s v, ε) := by
    intro s v ε
    apply Subtype.ext
    exact ptLevi_conj_ptHom he hb φ hzC hz s v ε
  obtain ⟨-, -, -, -, F, hF, -, -, -, -, C, hCn, hCs, hCc, hCz, hCB, τ, hτz, hτmul, hτsurj, hτker,
    hτs, hCF, hCFc, α, β, hsq, hCC, -, hα1, hα0⟩ :=
    binary_odd_quadratic_five_central_action_index_two_subgroup hE (b.restrict 𝔼) hb' hnd'
      (ptQuad e) (polarBilin_ptQuad he) ((ptSub φ z hb e).subgroupOf D₁) θ hconj hsurj hfaith act
      hact
  have hmemC : ∀ {x : G}, x ∈ C.map D₁.subtype ↔ ∃ h : x ∈ D₁, (⟨x, h⟩ : D₁) ∈ C :=
    mem_map_subtype_iff
  set τ₁ : G → 𝔼 × ZMod 2 := fun g => if h : g ∈ D₁ then τ ⟨g, h⟩ else 0 with hτ₁def
  have hτ₁ : ∀ (g : G) (h : g ∈ D₁), τ₁ g = τ ⟨g, h⟩ := fun g h => by
    simp only [hτ₁def, h, ↓reduceDIte]
  have hFset : ∀ x : G, ∀ hx : x ∈ D₁, ((⟨x, hx⟩ : D₁) ∈ F ↔
      z⁻¹ * (x⁻¹ * z * x) ∈ zpowers (ptB₁ he hb φ hzC hz)) := by
    intro x hx
    rw [hF, mem_subI_ptLabelOf_iff he hb φ hzC hinf hz hBD₁]
    have h1 : (((OddQuadraticFive.zz θ)⁻¹ * (⟨x, hx⟩ : D₁)⁻¹ * OddQuadraticFive.zz θ *
        ⟨x, hx⟩ : D₁) : G) = z⁻¹ * (x⁻¹ * z * x) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzz]
      group
    rw [h1]
  refine ⟨C.map D₁.subtype, τ₁, α, β, map_subtype_le _, fun m hm c hc => ?_, ?_, ?_, ?_,
    fun c hc => ?_, fun c hc c' hc' => ?_, fun v => ?_, fun c hc => ?_, fun s c hc => ?_,
    fun x hx hxF y hy => ?_, ?_, fun c hc => ?_, ?_, fun h1 c hc hc2 => ?_, fun h0 => ?_⟩
  ·
    obtain ⟨d, hd, c', hc', rfl⟩ := hprod₁ m hm
    obtain ⟨s, b', hb'B, rfl⟩ := exists_ptLevi_mul he hb hnd φ hzC hsup hinf hz hc'
    obtain ⟨hcD, hcC⟩ := hmemC.1 hc
    have h1 : b' * c * b'⁻¹ ∈ C.map D₁.subtype :=
      hmemC.2 ⟨_, hCn.conj_mem _ hcC ⟨b', hBD₁ hb'B⟩⟩
    obtain ⟨h1D, h1C⟩ := hmemC.1 h1
    have h2 : ptLevi he hb φ s * (b' * c * b'⁻¹) * (ptLevi he hb φ s)⁻¹ ∈ C.map D₁.subtype :=
      hmemC.2 ⟨_, hCs s _ h1C⟩
    obtain ⟨h2D, h2C⟩ := hmemC.1 h2
    have h3 := hmemC.2 ⟨_, hCn.conj_mem _ h2C ⟨d, hd⟩⟩
    have h4 : d * (ptLevi he hb φ s * b') * c * (d * (ptLevi he hb φ s * b'))⁻¹ =
        d * (ptLevi he hb φ s * (b' * c * b'⁻¹) * (ptLevi he hb φ s)⁻¹) * d⁻¹ := by group
    rw [h4]
    exact h3
  · rw [card_map_of_injective D₁.subtype_injective, hCc]
  · have h := congrArg (Subgroup.map D₁.subtype) hCz
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    have h' : D₁.subtype (OddQuadraticFive.zz θ) = z := hzz
    rw [h'] at h
    exact h
  · have h := congrArg (Subgroup.map D₁.subtype) hCB
    rw [Subgroup.map_inf_eq _ _ _ D₁.subtype_injective, map_ptSub_subgroupOf' hb φ hBD₁,
      map_subA_ptLabelOf he hb φ hzC hinf hz hBD₁] at h
    exact h
  · obtain ⟨hcD, hcC⟩ := hmemC.1 hc
    have h := congrArg Subtype.val (hτz _ hcC)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzz] at h
    rw [hτ₁ c hcD]
    exact h
  · obtain ⟨h1, h1C⟩ := hmemC.1 hc
    obtain ⟨h2, h2C⟩ := hmemC.1 hc'
    rw [hτ₁ c h1, hτ₁ c' h2, hτ₁ (c * c') (mul_mem h1 h2)]
    exact hτmul _ h1C _ h2C
  · obtain ⟨c, hcC, hcv⟩ := hτsurj v
    refine ⟨c, hmemC.2 ⟨c.2, hcC⟩, ?_⟩
    rw [hτ₁ c c.2]
    exact hcv
  · obtain ⟨hcD, hcC⟩ := hmemC.1 hc
    rw [hτ₁ c hcD, hτker _ hcC, mem_subA_ptLabelOf_iff he hb φ hzC hinf hz hBD₁]
  · obtain ⟨hcD, hcC⟩ := hmemC.1 hc
    have h := hτs s _ hcC
    rw [hτ₁ c hcD, ← h, hτ₁ _ (by rw [← hcoe s ⟨c, hcD⟩]; exact (act s ⟨c, hcD⟩).2)]
    rfl
  · obtain ⟨hxD, hxC⟩ := hmemC.1 hx
    obtain ⟨hyD, hyC⟩ := hmemC.1 hy
    have h := hCF _ (mem_inf.2 ⟨hxC, (hFset x hxD).2 hxF⟩) _ hyC
    exact congrArg Subtype.val h
  · have h1 : ((C.map D₁.subtype : Subgroup G) : Set G) ∩ {d | d ∈ D₁ ∧
        z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)} =
        (((C ⊓ F).map D₁.subtype : Subgroup G) : Set G) := by
      ext x
      constructor
      · rintro ⟨hxC, hxD, hxF⟩
        obtain ⟨h, hxC'⟩ := hmemC.1 hxC
        exact ⟨⟨x, h⟩, mem_inf.2 ⟨hxC', (hFset x h).2 hxF⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨hyC, hyF⟩ := mem_inf.1 hy
        exact ⟨⟨y, hyC, rfl⟩, y.2, (hFset y y.2).1 hyF⟩
    rw [h1, SetLike.coe_sort_coe, card_map_of_injective D₁.subtype_injective, hCFc]
  · obtain ⟨hcD, hcC⟩ := hmemC.1 hc
    have h := congrArg Subtype.val (hsq _ hcC)
    rw [hτ₁ c hcD]
    exact h
  · rw [← map_subI_ptLabelOf he hb φ hzC hinf hz hBD₁, ← Subgroup.map_commutator]
    exact map_mono hCC
  · obtain ⟨hcD, hcC⟩ := hmemC.1 hc
    have h := hα1 h1 _ hcC (Subtype.ext (by rw [Subgroup.coe_pow]; exact hc2))
    exact (hFset c hcD).1 (mem_inf.1 h).2
  · obtain ⟨hsq0, -⟩ := hα0 h0
    have himg : (D₁.subtype) '' {x | ∃ y ∈ C, y ^ 2 = x} =
        {x | ∃ y ∈ C.map D₁.subtype, y ^ 2 = x} := by
      ext x
      constructor
      · rintro ⟨y, ⟨f, hf, rfl⟩, rfl⟩
        exact ⟨f, ⟨f, hf, rfl⟩, (map_pow D₁.subtype f 2).symm⟩
      · rintro ⟨f, ⟨f', hf', rfl⟩, rfl⟩
        exact ⟨f' ^ 2, ⟨f', hf', rfl⟩, map_pow D₁.subtype f' 2⟩
    rw [← himg, ← MonoidHom.map_closure, ← map_subI_ptLabelOf he hb φ hzC hinf hz hBD₁]
    exact map_mono hsq0

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
