module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerLagAction
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverComplement

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} {he : IsSymplecticBasis b e}

variable {G : Type} [Group G] {L : Subgroup G} {φ : L ≃* bilinIsometryGroup b} {z : G}
  {hzC : z ∈ centralizer (L : Set G)} {hz : orderOf z = 2}

local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}

theorem card_AGL32 : Nat.card AGL32 = 1344 := by
  rw [SemidirectProduct.card, card_GL_three_two]
  have h8 : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [h8]

theorem card_range_inr : Nat.card (SemidirectProduct.inr : GL (Fin 3) (ZMod 2) →* AGL32).range =
    168 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inr_injective).toEquiv,
    card_GL_three_two]

theorem card_range_inl : Nat.card (SemidirectProduct.inl :
    Multiplicative (Fin 3 → ZMod 2) →* AGL32).range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv,
    Nat.card_eq_fintype_card]
  rfl

section Main

variable [Finite G] (h : LagData he φ hzC hz D₂ C₂ E₂ ν₂ σ) (hinf : L ⊓ zpowers z = ⊥)
  {sec : (Fin 3 → ZMod 2) → G}
  (hsec : ∀ w, sec w ∈ C₂ ∧ symThreeDiag (ν₂ (sec w) : M₃) = w)

include h hinf hsec

theorem actVec_levi (g : GL (Fin 3) (ZMod 2)) : actVec ν₂ z (leviHom φ he g) = 0 := by
  have h1 := congrArg (fun p : AGL32 => Multiplicative.toAdd p.left)
    (psiHom_levi h.toLagBase hinf hsec g (h.N₂_le_Q₂ (leviHom_mem_normalizer_radSub φ he hzC hz g)))
  exact h1

theorem actMat_levi (g : GL (Fin 3) (ZMod 2)) : actMat ν₂ sec (leviHom φ he g) = g := by
  have h1 := congrArg (fun p : AGL32 => (p.right : M₃))
    (psiHom_levi h.toLagBase hinf hsec g (h.N₂_le_Q₂ (leviHom_mem_normalizer_radSub φ he hzC hz g)))
  exact h1

theorem exists_actVec_eq (w : Fin 3 → ZMod 2) :
    ∃ y : normalizer (D₂ : Set G), actVec ν₂ z y = w := by
  by_cases hw : w = 0
  · refine ⟨1, ?_⟩
    subst hw
    change symThreeDiag (ν₂ (1 * z * 1⁻¹) : M₃) = 0
    rw [one_mul, inv_one, mul_one, h.nu_eq_zero_of_mem hinf (mem_sup_right (mem_zpowers z))]
    rfl
  obtain ⟨x₀, hx₀Q, hx₀N⟩ := h.hgrow
  have hv₀ : actVec ν₂ z x₀ ≠ 0 := fun h0 => hx₀N ((h.mem_N₂_iff hinf hsec hx₀Q).2 h0)
  obtain ⟨g₁, hg₁⟩ := exists_mulVec_single_zero hv₀
  obtain ⟨g₂, hg₂⟩ := exists_mulVec_single_zero hw
  have hlQ := h.N₂_le_Q₂ (leviHom_mem_normalizer_radSub φ he hzC hz (g₂ * g₁⁻¹))
  refine ⟨⟨_, hlQ⟩ * ⟨x₀, hx₀Q⟩, ?_⟩
  change actVec ν₂ z (leviHom φ he (g₂ * g₁⁻¹) * x₀) = w
  rw [h.actVec_mul hinf hsec hlQ hx₀Q, actVec_levi h hinf hsec, actMat_levi h hinf hsec,
    zero_add, ← hg₁, mulVec_mulVec, Units.val_mul, Matrix.mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.mul_one, hg₂]

theorem psiHom_surjective : Function.Surjective (psiHom h.toLagBase hinf hsec) := by
  intro a
  obtain ⟨y, hy⟩ := exists_actVec_eq h hinf hsec (Multiplicative.toAdd a.left)
  set g₀ := (psiHom h.toLagBase hinf hsec y).right with hg₀
  have hlQ := h.N₂_le_Q₂ (leviHom_mem_normalizer_radSub φ he hzC hz (g₀⁻¹ * a.right))
  refine ⟨y * ⟨_, hlQ⟩, ?_⟩
  rw [map_mul, psiHom_levi h.toLagBase hinf hsec _ hlQ]
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inr, map_one, mul_one, psiHom_left,
      hy, ofAdd_toAdd]
  · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inr, ← hg₀, mul_inv_cancel_left]

theorem card_Q₂ : Nat.card (normalizer (D₂ : Set G)) = 2 ^ 19 * 21 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (psiHom h.toLagBase hinf hsec).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (psiHom_surjective h hinf hsec)).toEquiv, card_AGL32, ker_psiHom,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_normalizer : D₂ ≤ _)).toEquiv,
    h.hD₂card] at h1
  rw [h1]
  norm_num

theorem subgroupOf_N₂_eq : (𝒩₂).subgroupOf (normalizer (D₂ : Set G)) =
    (SemidirectProduct.inr : GL (Fin 3) (ZMod 2) →* AGL32).range.comap
      (psiHom h.toLagBase hinf hsec) := by
  ext x
  rw [mem_subgroupOf, mem_comap, h.mem_N₂_iff hinf hsec x.2]
  constructor
  · intro hv
    refine ⟨(psiHom h.toLagBase hinf hsec x).right, SemidirectProduct.ext ?_ rfl⟩
    rw [SemidirectProduct.left_inr, psiHom_left, hv]
    rfl
  · rintro ⟨g, hg⟩
    have h1 := congrArg (fun p : AGL32 => Multiplicative.toAdd p.left) hg
    exact h1.symm

theorem relIndex_N₂_Q₂ : (𝒩₂).relIndex (normalizer (D₂ : Set G)) = 8 := by
  rw [Subgroup.relIndex, subgroupOf_N₂_eq h hinf hsec,
    Subgroup.index_comap_of_surjective _ (psiHom_surjective h hinf hsec)]
  have h1 := Subgroup.card_mul_index
    (SemidirectProduct.inr : GL (Fin 3) (ZMod 2) →* AGL32).range
  rw [card_range_inr, card_AGL32] at h1
  omega

theorem mem_transl_iff (y : normalizer (D₂ : Set G)) :
    y ∈ (SemidirectProduct.inl : Multiplicative (Fin 3 → ZMod 2) →* AGL32).range.comap
      (psiHom h.toLagBase hinf hsec) ↔ (psiHom h.toLagBase hinf hsec y).right = 1 := by
  rw [mem_comap, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
    SemidirectProduct.rightHom_eq_right]

theorem card_transl : Nat.card ((SemidirectProduct.inl : Multiplicative (Fin 3 → ZMod 2) →*
    AGL32).range.comap (psiHom h.toLagBase hinf hsec)) = 2 ^ 16 := by
  have h1 := Subgroup.card_mul_index ((SemidirectProduct.inl :
    Multiplicative (Fin 3 → ZMod 2) →* AGL32).range.comap (psiHom h.toLagBase hinf hsec))
  rw [Subgroup.index_comap_of_surjective _ (psiHom_surjective h hinf hsec),
    card_Q₂ h hinf hsec] at h1
  have h2 := Subgroup.card_mul_index
    (SemidirectProduct.inl : Multiplicative (Fin 3 → ZMod 2) →* AGL32).range
  rw [card_range_inl, card_AGL32] at h2
  have h3 : (SemidirectProduct.inl : Multiplicative (Fin 3 → ZMod 2) →* AGL32).range.index =
      168 := by omega
  rw [h3] at h1
  omega

theorem mem_Dhat_iff (x : normalizer (D₂ : Set G)) :
    (x : G) ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)) ↔
      (psiHom h.toLagBase hinf hsec x).right = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hx
    set ρ := (SemidirectProduct.rightHom : AGL32 →* GL (Fin 3) (ZMod 2)).comp
      (psiHom h.toLagBase hinf hsec) with hρ
    have hρs : Function.Surjective ρ :=
      SemidirectProduct.rightHom_surjective.comp (psiHom_surjective h hinf hsec)
    set P := (CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G))).subgroupOf
      (normalizer (D₂ : Set G)) with hP
    have hPn : P.Normal := ⟨fun n hn g => by
      rw [hP, mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact conj_mem_pCoreOf 2 g.2 hn⟩
    have hPp : IsPGroup 2 P := (isPGroup_pCoreOf 2 _).of_equiv
      (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 _)).symm
    have hbot := eq_bot_of_normal_isPGroup_GL (P.map ρ) (hPn.map ρ hρs) (hPp.map ρ)
    have hxP : x ∈ P := by
      rw [hP, mem_subgroupOf]
      exact hx
    have h1 : ρ x ∈ P.map ρ := ⟨x, hxP, rfl⟩
    rw [hbot, mem_bot] at h1
    exact h1
  · intro hx
    have hle : ((SemidirectProduct.inl : Multiplicative (Fin 3 → ZMod 2) →* AGL32).range.comap
        (psiHom h.toLagBase hinf hsec)).map (normalizer (D₂ : Set G)).subtype ≤
        CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)) := by
      refine le_pCoreOf 2 (map_subtype_le _) ?_ ?_
      · rintro y hy _ ⟨t, ht, rfl⟩
        refine ⟨⟨y, hy⟩ * t * ⟨y, hy⟩⁻¹, ?_, rfl⟩
        rw [SetLike.mem_coe, mem_transl_iff h hinf hsec] at ht ⊢
        rw [map_mul, map_mul, map_inv, SemidirectProduct.mul_right, SemidirectProduct.mul_right,
          ht, mul_one, SemidirectProduct.inv_right, mul_inv_cancel]
      · refine IsPGroup.of_card (n := 16) ?_
        rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _
          (normalizer (D₂ : Set G)).subtype_injective).toEquiv]
        exact card_transl h hinf hsec
    exact hle ⟨x, (mem_transl_iff h hinf hsec x).2 hx, rfl⟩

theorem card_Dhat : Nat.card (CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G))) = 2 ^ 16 := by
  have heq : CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)) =
      ((SemidirectProduct.inl : Multiplicative (Fin 3 → ZMod 2) →* AGL32).range.comap
        (psiHom h.toLagBase hinf hsec)).map (normalizer (D₂ : Set G)).subtype := by
    ext y
    constructor
    · intro hy
      have hyQ := pCoreOf_le 2 _ hy
      exact ⟨⟨y, hyQ⟩, (mem_transl_iff h hinf hsec _).2
        ((mem_Dhat_iff h hinf hsec ⟨y, hyQ⟩).1 hy), rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact (mem_Dhat_iff h hinf hsec t).2 ((mem_transl_iff h hinf hsec t).1 ht)
  rw [heq, ← Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (normalizer (D₂ : Set G)).subtype_injective).toEquiv]
  exact card_transl h hinf hsec

theorem D₂_le_Dhat : D₂ ≤ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)) := by
  intro x hx
  refine (mem_Dhat_iff h hinf hsec ⟨x, le_normalizer hx⟩).2 ?_
  rw [psiHom_of_mem h.toLagBase hinf hsec _ hx]
  rfl

omit hsec in
theorem mul_inv_mem_E₂_of_kap_eq {d d' : G} (hd : d ∈ D₂) (hd' : d' ∈ D₂)
    (hk : kap C₂ ν₂ d = kap C₂ ν₂ d') : d' * d⁻¹ ∈ E₂ := by
  have h1 := (h.kap_eq_kap_iff hinf hd hd').1 hk
  have h2 := h.conj_mem_E₂ (le_normalizer hd) h1
  rwa [show d * (d⁻¹ * d') * d⁻¹ = d' * d⁻¹ by group] at h2

theorem actMat_of_mem_Dhat {x : G} (hx : x ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G))) :
    actMat ν₂ sec x = 1 := by
  have hxQ := pCoreOf_le 2 _ hx
  have h1 := (mem_Dhat_iff h hinf hsec ⟨x, hxQ⟩).1 hx
  have h2 := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : M₃)) h1
  exact h2

theorem actVec_inv_of_mem_Dhat {x : G}
    (hx : x ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G))) :
    actVec ν₂ z x⁻¹ = actVec ν₂ z x := by
  have hxQ := pCoreOf_le 2 _ hx
  have h1 := h.actVec_mul hinf hsec hxQ (inv_mem hxQ)
  rw [mul_inv_cancel, actMat_of_mem_Dhat h hinf hsec hx, one_mulVec] at h1
  have h0 : actVec ν₂ z 1 = 0 := by
    change symThreeDiag (ν₂ (1 * z * 1⁻¹) : M₃) = 0
    rw [one_mul, inv_one, mul_one, h.nu_eq_zero_of_mem hinf (mem_sup_right (mem_zpowers z))]
    rfl
  rw [h0] at h1
  have h2 : actVec ν₂ z x⁻¹ = -actVec ν₂ z x := eq_neg_of_add_eq_zero_right h1.symm
  rw [h2]
  exact funext fun i => ZModModule.neg_eq_self _

theorem kap_comm_z {x : G} (hx : x ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G))) :
    kap C₂ ν₂ (z⁻¹ * (x⁻¹ * z * x)) = (0, actVec ν₂ z x) := by
  have hxQ := pCoreOf_le 2 _ hx
  have hzi : z⁻¹ ∈ D₂ := inv_mem h.zD₂
  have hc : x⁻¹ * z * x ∈ D₂ := by
    have := (mem_normalizer_iff.1 (inv_mem hxQ) z).1 h.zD₂
    rwa [inv_inv] at this
  rw [h.kap_mul hinf hzi hc, h.kap_inv hinf h.zD₂, h.kap_z hinf]
  have h1 := h.kap_conj hinf hsec (inv_mem hxQ) h.zD₂
  rw [inv_inv, h.kap_z hinf, mulVec_zero, zero_add, one_smul,
    actVec_inv_of_mem_Dhat h hinf hsec hx] at h1
  rw [h1]
  refine Prod.ext ?_ (zero_add _)
  change (1 : ZMod 2) + 1 = 0
  decide

theorem comm_z_mem_C₂ {x : G} (hx : x ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G))) :
    z⁻¹ * (x⁻¹ * z * x) ∈ C₂ :=
  kap_fst_eq_zero_iff.1 (congrArg Prod.fst (kap_comm_z h hinf hsec hx))

theorem psiHom_of_mem_Dhat (x : normalizer (D₂ : Set G))
    (hx : (x : G) ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G))) :
    psiHom h.toLagBase hinf hsec x = SemidirectProduct.inl (Multiplicative.ofAdd
      (symThreeDiag (ν₂ (z⁻¹ * ((x : G)⁻¹ * z * x)) : M₃))) := by
  have h1 := congrArg Prod.snd (kap_comm_z h hinf hsec hx)
  rw [kap_snd] at h1
  refine SemidirectProduct.ext ?_ ?_
  · rw [psiHom_left, SemidirectProduct.left_inl, h1]
  · rw [SemidirectProduct.right_inl]
    exact (mem_Dhat_iff h hinf hsec x).1 hx

theorem comm_z_mul {x y : G} (hx : x ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)))
    (hy : y ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G))) :
    z⁻¹ * ((x * y)⁻¹ * z * (x * y)) * (z⁻¹ * (x⁻¹ * z * x) * (z⁻¹ * (y⁻¹ * z * y)))⁻¹ ∈ E₂ := by
  have hxQ := pCoreOf_le 2 _ hx
  have hyQ := pCoreOf_le 2 _ hy
  have hxy := mul_mem hx hy
  have hcx := h.C₂D₂ (comm_z_mem_C₂ h hinf hsec hx)
  have hcy := h.C₂D₂ (comm_z_mem_C₂ h hinf hsec hy)
  refine mul_inv_mem_E₂_of_kap_eq h hinf (mul_mem hcx hcy)
    (h.C₂D₂ (comm_z_mem_C₂ h hinf hsec hxy)) ?_
  rw [h.kap_mul hinf hcx hcy, kap_comm_z h hinf hsec hx, kap_comm_z h hinf hsec hy,
    kap_comm_z h hinf hsec hxy, h.actVec_mul hinf hsec hxQ hyQ,
    actMat_of_mem_Dhat h hinf hsec hx, one_mulVec]
  exact Prod.ext (zero_add 0) rfl

theorem comm_z_mem_E₂_iff {x : G} (hx : x ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G))) :
    z⁻¹ * (x⁻¹ * z * x) ∈ E₂ ↔ x ∈ D₂ := by
  have hxQ := pCoreOf_le 2 _ hx
  rw [← h.kap_eq_zero_iff, kap_comm_z h hinf hsec hx]
  have hΨ := psiHom_of_mem_Dhat h hinf hsec ⟨x, hxQ⟩ hx
  rw [← psiHom_eq_one_iff h.toLagBase hinf hsec ⟨x, hxQ⟩]
  constructor
  · intro h0
    have hv : actVec ν₂ z x = 0 := congrArg Prod.snd h0
    refine SemidirectProduct.ext ?_ ((mem_Dhat_iff h hinf hsec ⟨x, hxQ⟩).1 hx)
    rw [psiHom_left, hv]
    rfl
  · intro h1
    have h2 := congrArg (fun p : AGL32 => Multiplicative.toAdd p.left) h1
    exact Prod.ext rfl h2

theorem exists_comm_z {c : G} (hc : c ∈ C₂) :
    ∃ x ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)), (z⁻¹ * (x⁻¹ * z * x))⁻¹ * c ∈ E₂ := by
  obtain ⟨x, hx⟩ := psiHom_surjective h hinf hsec
    (SemidirectProduct.inl (Multiplicative.ofAdd (symThreeDiag (ν₂ c : M₃))))
  have hxD : (x : G) ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)) := by
    rw [mem_Dhat_iff h hinf hsec, hx]
    rfl
  refine ⟨x, hxD, (h.kap_eq_kap_iff hinf (h.C₂D₂ (comm_z_mem_C₂ h hinf hsec hxD))
    (h.C₂D₂ hc)).1 ?_⟩
  rw [kap_comm_z h hinf hsec hxD]
  have hv := congrArg (fun p : AGL32 => Multiplicative.toAdd p.left) hx
  change actVec ν₂ z x = symThreeDiag (ν₂ c : M₃) at hv
  rw [hv]
  exact Prod.ext (kap_fst_of_mem hc).symm rfl

theorem actVec_conj_of_mem_Dhat {x y : G}
    (hx : x ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)))
    (hy : y ∈ normalizer (D₂ : Set G)) :
    actVec ν₂ z (y * x * y⁻¹) = actMat ν₂ sec y *ᵥ actVec ν₂ z x := by
  have hxQ := pCoreOf_le 2 _ hx
  rw [h.actVec_mul hinf hsec (mul_mem hy hxQ) (inv_mem hy), h.actVec_mul hinf hsec hy hxQ,
    h.actMat_mul hinf hsec hy hxQ, actMat_of_mem_Dhat h hinf hsec hx, Matrix.mul_one]
  have h1 := h.actVec_mul hinf hsec hy (inv_mem hy)
  have h0 : actVec ν₂ z 1 = 0 := by
    change symThreeDiag (ν₂ (1 * z * 1⁻¹) : M₃) = 0
    rw [one_mul, inv_one, mul_one, h.nu_eq_zero_of_mem hinf (mem_sup_right (mem_zpowers z))]
    rfl
  rw [mul_inv_cancel, h0] at h1
  have h2 : actMat ν₂ sec y *ᵥ actVec ν₂ z y⁻¹ = actVec ν₂ z y := by
    have h3 : actMat ν₂ sec y *ᵥ actVec ν₂ z y⁻¹ = -actVec ν₂ z y :=
      eq_neg_of_add_eq_zero_right h1.symm
    rw [h3]
    exact funext fun i => ZModModule.neg_eq_self _
  rw [add_assoc, h2, add_comm]
  have h4 : actVec ν₂ z y + actVec ν₂ z y = 0 := funext fun i => ZModModule.add_self _
  rw [add_assoc, h4, add_zero]

theorem comm_z_conj {x y : G} (hx : x ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)))
    (hy : y ∈ normalizer (D₂ : Set G)) :
    z⁻¹ * ((y * x * y⁻¹)⁻¹ * z * (y * x * y⁻¹)) * (y * (z⁻¹ * (x⁻¹ * z * x)) * y⁻¹)⁻¹ ∈ E₂ := by
  have hyx : y * x * y⁻¹ ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)) :=
    conj_mem_pCoreOf 2 hy hx
  have hc := h.C₂D₂ (comm_z_mem_C₂ h hinf hsec hx)
  have hyc : y * (z⁻¹ * (x⁻¹ * z * x)) * y⁻¹ ∈ D₂ := (mem_normalizer_iff.1 hy _).1 hc
  refine mul_inv_mem_E₂_of_kap_eq h hinf hyc (h.C₂D₂ (comm_z_mem_C₂ h hinf hsec hyx)) ?_
  rw [h.kap_conj hinf hsec hy hc, kap_comm_z h hinf hsec hx, kap_comm_z h hinf hsec hyx,
    actVec_conj_of_mem_Dhat h hinf hsec hx hy, zero_smul, add_zero]

theorem C₂_le_Dhat : C₂ ≤ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)) :=
  h.C₂D₂.trans (D₂_le_Dhat h hinf hsec)

theorem center_Dhat_iff {x : G} (hx : x ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G))) :
    (∀ y ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)), x⁻¹ * y⁻¹ * x * y ∈ E₂) ↔
      x ∈ C₂ := by
  have hxQ := pCoreOf_le 2 _ hx
  constructor
  · intro hc
    have hxD : x ∈ D₂ := by
      have h1 := hc z (D₂_le_Dhat h hinf hsec h.zD₂)
      have hd : x⁻¹ * z⁻¹ * x ∈ D₂ := by
        have := (mem_normalizer_iff.1 (inv_mem hxQ) z⁻¹).1 (inv_mem h.zD₂)
        rwa [inv_inv] at this
      have h2 := (h.kap_eq_zero_iff).2 h1
      rw [h.kap_mul hinf hd h.zD₂] at h2
      have h3 := h.kap_conj hinf hsec (inv_mem hxQ) (inv_mem h.zD₂)
      rw [inv_inv, h.kap_inv hinf h.zD₂, h.kap_z hinf, mulVec_zero, zero_add, one_smul,
        actVec_inv_of_mem_Dhat h hinf hsec hx] at h3
      rw [h3, h.kap_z hinf] at h2
      have hv : actVec ν₂ z x = 0 := by
        have := congrArg Prod.snd h2
        simpa using this
      rw [← psiHom_eq_one_iff h.toLagBase hinf hsec ⟨x, hxQ⟩]
      refine SemidirectProduct.ext ?_ ((mem_Dhat_iff h hinf hsec ⟨x, hxQ⟩).1 hx)
      rw [psiHom_left, hv]
      rfl
    obtain ⟨y, hy⟩ := psiHom_surjective h hinf hsec
      (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single 0 1)))
    have hyD : (y : G) ∈ CFSG.Assembly.pCoreOf 2 (normalizer (D₂ : Set G)) := by
      rw [mem_Dhat_iff h hinf hsec, hy]
      rfl
    have hvy : actVec ν₂ z y = Pi.single 0 1 :=
      congrArg (fun p : AGL32 => Multiplicative.toAdd p.left) hy
    have h1 := hc y hyD
    have hd : (y : G)⁻¹ * x * y ∈ D₂ := by
      have := (mem_normalizer_iff.1 (inv_mem y.2) x).1 hxD
      rwa [inv_inv] at this
    have h2 : kap C₂ ν₂ x = kap C₂ ν₂ ((y : G)⁻¹ * x * y) :=
      (h.kap_eq_kap_iff hinf hxD hd).2 (by
        rw [show x⁻¹ * ((y : G)⁻¹ * x * y) = x⁻¹ * (y : G)⁻¹ * x * y by group]
        exact h1)
    have h3 := h.kap_conj hinf hsec (inv_mem y.2) hxD
    rw [inv_inv, actMat_of_mem_Dhat h hinf hsec (inv_mem hyD), one_mulVec,
      actVec_inv_of_mem_Dhat h hinf hsec hyD, hvy] at h3
    rw [h3] at h2
    have h4 := congrFun (congrArg Prod.snd h2) 0
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      left_eq_add] at h4
    exact kap_fst_eq_zero_iff.1 h4
  · intro hxC y hy
    have hyQ := pCoreOf_le 2 _ hy
    have hd : y⁻¹ * x * y ∈ D₂ := by
      have := (mem_normalizer_iff.1 (inv_mem hyQ) x).1 (h.C₂D₂ hxC)
      rwa [inv_inv] at this
    have h1 := h.kap_conj hinf hsec (inv_mem hyQ) (h.C₂D₂ hxC)
    rw [inv_inv, actMat_of_mem_Dhat h hinf hsec (inv_mem hy), one_mulVec, kap_fst_of_mem hxC,
      zero_smul, add_zero] at h1
    have h2 := (h.kap_eq_kap_iff hinf (h.C₂D₂ hxC) hd).1 (by
      rw [h1]
      exact Prod.ext (kap_fst_of_mem hxC) rfl)
    rwa [show x⁻¹ * (y⁻¹ * x * y) = x⁻¹ * y⁻¹ * x * y by group] at h2

omit hsec in
theorem Q₂_inf_centralizer : normalizer (D₂ : Set G) ⊓ centralizer ({z} : Set G) =
    𝒩₂ ⊓ centralizer ({z} : Set G) := by
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_right _ h.N₂_le_Q₂)
  obtain ⟨hxQ, hxz⟩ := mem_inf.1 hx
  refine mem_inf.2 ⟨h.mem_N₂_of_conj_z hinf hxQ ?_, hxz⟩
  rw [mem_centralizer_singleton_iff.1 hxz, mul_inv_cancel_right, inv_mul_cancel]
  exact one_mem _

theorem card_N₂ : Nat.card 𝒩₂ = 2 ^ 16 * 21 := by
  have h1 := Subgroup.relIndex_mul_card (H := 𝒩₂) (K := normalizer (D₂ : Set G))
  rw [inf_of_le_left h.N₂_le_Q₂, relIndex_N₂_Q₂ h hinf hsec, card_Q₂ h hinf hsec] at h1
  omega

theorem card_N₂₀ : Nat.card (𝒩₂ ⊓ centralizer ({z} : Set G) : Subgroup G) = 2 ^ 10 * 21 := by
  have h1 := card_eq_card_conjClass_mul 𝒩₂ z
  rw [h.hfull, card_smul_set, SetLike.coe_sort_coe, card_pullSub_radA he φ,
    card_N₂ h hinf hsec] at h1
  omega

theorem card_conjClass_Q₂ : Nat.card (conjClass (normalizer (D₂ : Set G)) z) = 512 := by
  have h1 := card_eq_card_conjClass_mul (normalizer (D₂ : Set G)) z
  rw [Q₂_inf_centralizer h hinf, card_N₂₀ h hinf hsec, card_Q₂ h hinf hsec] at h1
  omega

omit [Finite G] hinf hsec in
theorem z_mul_sq {c : G} (hc : c ∈ C₂) : (z * c) ^ 2 = tauHom φ he (Multiplicative.ofAdd
    (symThreeSquare 1 (symThreeDiag (ν₂ c : M₃)) + ν₂ c)) := by
  set τ := tauHom φ he (Multiplicative.ofAdd (ν₂ c)) with hτ
  have hτA : τ ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have h1 : c⁻¹ * z * c = z * τ := by rw [h.hν₂z c (h.C₂D₂ hc), radHom_one_eq]
  have hzc : z * c = c * (z * τ) := by rw [← h1]; group
  have hτc : τ * c = c * τ := (h.D₂A (h.C₂D₂ hc) hτA).symm
  have hτz : τ * z = z * τ := mul_comm_z hzC (tauHom_mem φ he _)
  have hz2 : z * z = 1 := z_mul_self hz
  calc (z * c) ^ 2 = (z * c) * (z * c) := sq _
    _ = (c * (z * τ)) * (z * c) := by rw [← hzc]
    _ = c * (z * τ) * z * c := by group
    _ = c * (τ * z) * z * c := by rw [← hτz]
    _ = c * τ * (z * z) * c := by group
    _ = c * (τ * c) := by rw [hz2]; group
    _ = c * (c * τ) := by rw [hτc]
    _ = c ^ 2 * τ := by rw [sq, mul_assoc]
    _ = _ := by rw [h.hsq c hc, hτ, ← map_mul, ← ofAdd_add]

omit hsec in
theorem card_involutions_le :
    Nat.card {x : G | x ∈ D₂ ∧ x ∉ C₂ ∧ x ^ 2 = 1} ≤ 512 := by
  classical
  choose sec2 hsec2 using fun w : Fin 3 → ZMod 2 => h.hνs (symThreeSquare 1 w)
  have hinvν : ∀ d ∈ D₂, ν₂ d⁻¹ = ν₂ d := fun d hd => by
    have h1 := h.nu_mul hinf hd (inv_mem hd)
    rw [mul_inv_cancel, h.nu_eq_zero_of_mem hinf (one_mem _)] at h1
    have h2 : ν₂ d⁻¹ = -ν₂ d := eq_neg_of_add_eq_zero_right h1.symm
    rw [h2]
    exact Subtype.ext (by ext i j; exact ZModModule.neg_eq_self _)
  have key : ∀ x : {x : G | x ∈ D₂ ∧ x ∉ C₂ ∧ x ^ 2 = 1},
      z⁻¹ * (x : G) * (sec2 (symThreeDiag (ν₂ (z⁻¹ * (x : G)) : M₃)))⁻¹ ∈ 𝒜₂ := by
    rintro ⟨x, hxD, hxC, hx2⟩
    have hc : z⁻¹ * x ∈ C₂ := (h.mem_D₂_cases hxD).resolve_left hxC
    set w := symThreeDiag (ν₂ (z⁻¹ * x) : M₃) with hw
    obtain ⟨hsC, hsν⟩ := hsec2 w
    have hsq := z_mul_sq h hc
    rw [show z * (z⁻¹ * x) = x by group, hx2, ← hw] at hsq
    have h1 := tauHom_injective φ he (hsq.symm.trans (map_one _).symm)
    have h2 : symThreeSquare 1 w + ν₂ (z⁻¹ * x) = 0 := Multiplicative.ofAdd.injective h1
    have h3 : ν₂ (z⁻¹ * x) = symThreeSquare 1 w := by
      have := eq_neg_of_add_eq_zero_right h2
      rw [this]
      exact Subtype.ext (by ext i j; exact ZModModule.neg_eq_self _)
    refine (h.hνk _ (mul_mem hc (inv_mem hsC))).1 ?_
    rw [h.nu_mul hinf (h.C₂D₂ hc) (inv_mem (h.C₂D₂ hsC)), hinvν _ (h.C₂D₂ hsC), h3, hsν]
    exact Subtype.ext (by ext i j; exact ZModModule.add_self _)
  let F : {x : G | x ∈ D₂ ∧ x ∉ C₂ ∧ x ^ 2 = 1} → (Fin 3 → ZMod 2) × 𝒜₂ := fun x =>
    (symThreeDiag (ν₂ (z⁻¹ * (x : G)) : M₃), ⟨_, key x⟩)
  have hF : Function.Injective F := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    rw [h1] at h2
    exact Subtype.ext (by simpa using h2)
  have h1 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, card_pullSub_radA he φ] at h1
  have h8 : Nat.card (Fin 3 → ZMod 2) = 8 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [h8] at h1
  exact h1

theorem conjClass_Q₂_eq : conjClass (normalizer (D₂ : Set G)) z =
    {x : G | x ∈ D₂ ∧ x ∉ C₂ ∧ x ^ 2 = 1} := by
  have hsub : conjClass (normalizer (D₂ : Set G)) z ⊆ {x : G | x ∈ D₂ ∧ x ∉ C₂ ∧ x ^ 2 = 1} := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨(mem_normalizer_iff.1 hm z).1 h.zD₂, fun h1 => ?_, ?_⟩
    · have h2 := h.conj_mem_C₂ (inv_mem hm) h1
      rw [inv_inv, show m⁻¹ * (m * z * m⁻¹) * m = z by group] at h2
      exact h.z_not_mem_C₂ hinf h2
    · rw [sq, show m * z * m⁻¹ * (m * z * m⁻¹) = m * (z * z) * m⁻¹ by group, z_mul_self hz]
      group
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_conjClass_Q₂ h hinf hsec]
  exact card_involutions_le h hinf

omit h hinf hsec in
theorem exists_sub_card (hQ : Nat.card (normalizer (D₂ : Set G)) = 2 ^ 19 * 21) :
    ∃ P : Subgroup G, P ≤ normalizer (D₂ : Set G) ∧ Nat.card P = 2 ^ 19 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 19)
    (G := normalizer (D₂ : Set G)) (by rw [hQ]; exact Dvd.intro 21 rfl)
  refine ⟨K.map (normalizer (D₂ : Set G)).subtype, map_subtype_le _, ?_⟩
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (normalizer (D₂ : Set G)).subtype_injective).toEquiv, hK]

theorem kap_conj_trivial_iff {x : G} (hx : x ∈ normalizer (D₂ : Set G)) :
    (∀ d ∈ D₂, kap C₂ ν₂ (x * d * x⁻¹) = kap C₂ ν₂ d) ↔ x ∈ D₂ := by
  refine ⟨fun hk => ?_, fun hxD d hd => h.kap_conj_of_mem hinf hxD hd⟩
  have hv : actVec ν₂ z x = 0 := by
    have h1 := hk z h.zD₂
    rw [h.kap_conj hinf hsec hx h.zD₂, h.kap_z hinf, mulVec_zero, zero_add, one_smul] at h1
    exact congrArg Prod.snd h1
  have hM : actMat ν₂ sec x = 1 := by
    refine matrix_ext_mulVec fun w => ?_
    obtain ⟨hsC, hsw⟩ := hsec w
    have h1 := congrArg Prod.snd (hk _ (h.C₂D₂ hsC))
    rw [h.kap_conj hinf hsec hx (h.C₂D₂ hsC), kap_fst_of_mem hsC, zero_smul, add_zero,
      kap_snd, hsw] at h1
    exact h1.trans (one_mulVec w).symm
  rw [← psiHom_eq_one_iff h.toLagBase hinf hsec ⟨x, hx⟩]
  refine SemidirectProduct.ext ?_ (Units.ext ?_)
  · rw [psiHom_left, hv]
    rfl
  · rw [psiHom_right, hM]
    rfl

omit hsec in
theorem mem_N₂_iff_conj {x : G} (hx : x ∈ normalizer (D₂ : Set G)) :
    x ∈ 𝒩₂ ↔ x * z * x⁻¹ ∈ z • (E₂ : Set G) := by
  constructor
  · intro hxN
    have h1 : x * z * x⁻¹ ∈ conjClass 𝒩₂ z := ⟨x, hxN, rfl⟩
    rw [h.hfull] at h1
    obtain ⟨a, ha, ha'⟩ := h1
    exact ⟨a, h.hA₂E₂ ha, ha'⟩
  · rintro ⟨y, hy, hy'⟩
    refine h.mem_N₂_of_conj_z hinf hx ?_
    change z * y = x * z * x⁻¹ at hy'
    rw [← hy', inv_mul_cancel_left]
    exact hy

end Main


theorem lagrangian_core [Finite G] (h : LagData he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) :
    let N₂ := 𝒩₂
    let H := centralizer ({z} : Set G)
    let N₂₀ := N₂ ⊓ H
    let κ := kap C₂ ν₂
    let Q₂ := normalizer (D₂ : Set G)
    let Dhat₂ := CFSG.Assembly.pCoreOf 2 Q₂
    (∀ d ∈ D₂, z⁻¹ * (d⁻¹ * z * d) = tauHom φ he (Multiplicative.ofAdd (ν₂ d))) ∧
    N₂ ≤ Q₂ ∧ (∀ x ∈ Q₂, ∀ c ∈ C₂, x * c * x⁻¹ ∈ C₂) ∧ (∀ x ∈ Q₂, ∀ y ∈ E₂, x * y * x⁻¹ ∈ E₂) ∧
    (∀ d ∈ D₂, ∀ d' ∈ D₂, κ (d * d') = κ d + κ d') ∧ (∀ d ∈ D₂, κ d = 0 ↔ d ∈ E₂) ∧
    (∀ p : ZMod 2 × (Fin 3 → ZMod 2), ∃ d ∈ D₂, κ d = p) ∧
    (∀ s : ZMod 2, ∀ c ∈ C₂, κ (z ^ s.val * c) = (s, symThreeDiag (ν₂ c : M₃))) ∧
    (∀ x ∈ Q₂, (∀ d ∈ D₂, κ (x * d * x⁻¹) = κ d) ↔ x ∈ D₂) ∧
    (∃ Ψ : Q₂ →* AGL32, Function.Surjective Ψ ∧ Ψ.ker = D₂.subgroupOf Q₂ ∧
      (∀ x : Q₂, ∀ d ∈ D₂, κ ((x : G) * d * (x : G)⁻¹) = aglLin (Ψ x) (κ d)) ∧
      (∀ g : GL (Fin 3) (ZMod 2), ∃ hg : leviHom φ he g ∈ Q₂,
        Ψ ⟨_, hg⟩ = SemidirectProduct.inr g) ∧
      (∀ x : Q₂, (x : G) ∈ N₂ ↔ (Ψ x).left = 1) ∧
      (∀ x : Q₂, (x : G) ∈ Dhat₂ ↔ (Ψ x).right = 1) ∧
      ∀ x : Q₂, (x : G) ∈ Dhat₂ → Ψ x = SemidirectProduct.inl (Multiplicative.ofAdd
        (symThreeDiag (ν₂ (z⁻¹ * ((x : G)⁻¹ * z * x)) : M₃)))) ∧
    N₂.relIndex Q₂ = 8 ∧ (∀ x ∈ Q₂, x ∈ N₂ ↔ x * z * x⁻¹ ∈ z • (E₂ : Set G)) ∧
    D₂ ≤ Dhat₂ ∧ Nat.card Dhat₂ = 2 ^ 16 ∧
    (∀ x ∈ Dhat₂, z⁻¹ * (x⁻¹ * z * x) ∈ C₂) ∧
    (∀ x ∈ Dhat₂, ∀ y ∈ Dhat₂, z⁻¹ * ((x * y)⁻¹ * z * (x * y)) *
      (z⁻¹ * (x⁻¹ * z * x) * (z⁻¹ * (y⁻¹ * z * y)))⁻¹ ∈ E₂) ∧
    (∀ x ∈ Dhat₂, z⁻¹ * (x⁻¹ * z * x) ∈ E₂ ↔ x ∈ D₂) ∧
    (∀ c ∈ C₂, ∃ x ∈ Dhat₂, (z⁻¹ * (x⁻¹ * z * x))⁻¹ * c ∈ E₂) ∧
    (∀ y ∈ Q₂, ∀ x ∈ Dhat₂, z⁻¹ * ((y * x * y⁻¹)⁻¹ * z * (y * x * y⁻¹)) *
      (y * (z⁻¹ * (x⁻¹ * z * x)) * y⁻¹)⁻¹ ∈ E₂) ∧
    C₂ ≤ Dhat₂ ∧ (∀ x ∈ Dhat₂, (∀ y ∈ Dhat₂, x⁻¹ * y⁻¹ * x * y ∈ E₂) ↔ x ∈ C₂) ∧
    Q₂ ⊓ H = N₂₀ ∧ conjClass Q₂ z = {x | x ∈ D₂ ∧ x ∉ C₂ ∧ x ^ 2 = 1} ∧
    Nat.card (conjClass Q₂ z) = 512 ∧
    Nat.card Q₂ = 2 ^ 19 * 21 ∧ ∃ P : Subgroup G, P ≤ Q₂ ∧ Nat.card P = 2 ^ 19 := by
  intro N₂ H N₂₀ κ Q₂ Dhat₂
  choose sec hsec using h.hδs
  have hcard := card_Q₂ h hinf hsec
  refine ⟨fun d hd => (h.tau_nu hd).symm, h.N₂_le_Q₂, fun x hx c hc => h.conj_mem_C₂ hx hc,
    fun x hx y hy => h.conj_mem_E₂ hx hy, fun d hd d' hd' => h.kap_mul hinf hd hd',
    fun d _ => h.kap_eq_zero_iff, h.kap_surjective hinf, fun s c hc => h.kap_zpow_mul hinf s hc,
    fun x hx => kap_conj_trivial_iff h hinf hsec hx,
    ⟨psiHom h.toLagBase hinf hsec, psiHom_surjective h hinf hsec, ker_psiHom h.toLagBase hinf hsec,
      fun x d hd => kap_conj_psiHom h.toLagBase hinf hsec x hd,
      fun g => ⟨h.N₂_le_Q₂ (leviHom_mem_normalizer_radSub φ he hzC hz g),
        psiHom_levi h.toLagBase hinf hsec g _⟩,
      fun x => ?_, mem_Dhat_iff h hinf hsec, psiHom_of_mem_Dhat h hinf hsec⟩,
    relIndex_N₂_Q₂ h hinf hsec, fun x hx => mem_N₂_iff_conj h hinf hx,
    D₂_le_Dhat h hinf hsec, card_Dhat h hinf hsec, fun x hx => comm_z_mem_C₂ h hinf hsec hx,
    fun x hx y hy => comm_z_mul h hinf hsec hx hy, fun x hx => comm_z_mem_E₂_iff h hinf hsec hx,
    fun c hc => exists_comm_z h hinf hsec hc, fun y hy x hx => comm_z_conj h hinf hsec hx hy,
    C₂_le_Dhat h hinf hsec, fun x hx => center_Dhat_iff h hinf hsec hx,
    Q₂_inf_centralizer h hinf, conjClass_Q₂_eq h hinf hsec, card_conjClass_Q₂ h hinf hsec,
    hcard, exists_sub_card hcard⟩
  rw [h.mem_N₂_iff hinf hsec x.2, psiHom_left]
  constructor
  · intro hv
    rw [hv]
    rfl
  · intro hv
    exact Multiplicative.ofAdd.injective hv

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
