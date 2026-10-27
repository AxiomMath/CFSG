module

public import CFSG.CGT.Harada80.Block
public import CFSG.CGT.Harada80.OmegaReflect
public import CFSG.ClassicalGroups.Orthogonal.NormalizerOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo Matrix

noncomputable def mulAutEquivGL (ι : Type) [Fintype ι] [DecidableEq ι] :
    MulAut (Multiplicative (ι → ZMod 2)) ≃* GL ι (ZMod 2) :=
  (CFSG.QuasithinUnique.Setup.Layer.binPsi
    (MulEquiv.refl (Multiplicative (ι → ZMod 2)))).trans
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).symm

theorem mulAutEquivGL_mulVec {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : MulAut (Multiplicative (ι → ZMod 2))) (v : ι → ZMod 2) :
    (mulAutEquivGL ι φ : Matrix ι ι (ZMod 2)) *ᵥ v =
      Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) := by
  have h : (mulAutEquivGL ι φ : GL ι (ZMod 2)) =
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).symm
        (CFSG.QuasithinUnique.Setup.Layer.binPsi
          (MulEquiv.refl (Multiplicative (ι → ZMod 2))) φ) := rfl
  rw [h, ← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
    MulEquiv.apply_symm_apply]
  exact CFSG.QuasithinUnique.Setup.Layer.binPsi_apply _ φ v

namespace Setting

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)
include S

theorem beta_injective (hZ : blockZ J = ⊥) : Function.Injective S.beta := by
  rw [← MonoidHom.ker_eq_bot_iff, S.ker_beta, hZ]
  simp

noncomputable def betaEquiv (hZ : blockZ J = ⊥) :
    ↥(blockU J) ≃* Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
  MulEquiv.ofBijective S.beta ⟨S.beta_injective hZ, S.beta_surjective⟩

noncomputable def conjAut : ↥M →* MulAut ↥(blockU J) :=
  (blockU J).normalizerMonoidHom.comp (Subgroup.inclusion (normalizer_blockU_eq S).ge)

noncomputable def rho (hZ : blockZ J = ⊥) : ↥M →* GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) :=
  ((MulAut.congr (S.betaEquiv hZ)).trans (mulAutEquivGL _)).toMonoidHom.comp S.conjAut

theorem rho_mulVec (hZ : blockZ J = ⊥) (x : ↥M) (u : ↥(blockU J)) :
    ((S.rho hZ x : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (S.beta u) =
      Multiplicative.toAdd
        (S.beta ⟨(x : G) * u * (x : G)⁻¹, conj_mem_blockU S x.2 u.2⟩) := by
  have h := mulAutEquivGL_mulVec (ι := Fin m ⊕ Fin m ⊕ Fin 2)
    ((MulAut.congr (S.betaEquiv hZ)) (S.conjAut x))
    (Multiplicative.toAdd (S.beta u))
  rw [ofAdd_toAdd] at h
  have hrho : S.rho hZ x =
      (mulAutEquivGL (Fin m ⊕ Fin m ⊕ Fin 2))
        ((MulAut.congr (S.betaEquiv hZ)) (S.conjAut x)) := rfl
  rw [hrho, h, ← Multiplicative.ext_iff]
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  rw [show S.beta u = (S.betaEquiv hZ) u from rfl, MulEquiv.symm_apply_apply]
  have hconj : S.conjAut x u =
      ⟨(x : G) * u * (x : G)⁻¹, conj_mem_blockU S x.2 u.2⟩ := by
    apply Subtype.ext
    simp only [conjAut, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
  rw [hconj]
  rfl

theorem rho_eq_one_iff (hZ : blockZ J = ⊥) (x : ↥M) :
    S.rho hZ x = 1 ↔ ∀ v ∈ blockU J, (x : G) * v * (x : G)⁻¹ = v := by
  constructor
  · intro h v hv
    have h1 := S.rho_mulVec hZ x ⟨v, hv⟩
    rw [h] at h1
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at h1
    have h2 : (⟨(x : G) * v * (x : G)⁻¹, conj_mem_blockU S x.2 hv⟩ : ↥(blockU J)) =
        ⟨v, hv⟩ :=
      (S.beta_injective hZ (Multiplicative.toAdd.injective h1)).symm
    exact congrArg Subtype.val h2
  · intro h
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro w
    obtain ⟨u, hu⟩ := S.beta_surjective (Multiplicative.ofAdd w)
    have hw : w = Multiplicative.toAdd (S.beta u) := by rw [hu]; rfl
    rw [hw, S.rho_mulVec hZ x u, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    rw [show (⟨(x : G) * (u : G) * (x : G)⁻¹, conj_mem_blockU S x.2 u.2⟩ :
        ↥(blockU J)) = u from Subtype.ext (h (u : G) u.2)]

theorem rho_inclusion (hZ : blockZ J = ⊥) (ℓ : ↥J) :
    S.rho hZ (Subgroup.inclusion S.le ℓ) =
      ((S.alpha ℓ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro w
  obtain ⟨u, hu⟩ := S.beta_surjective (Multiplicative.ofAdd w)
  have hw : w = Multiplicative.toAdd (S.beta u) := by rw [hu]; rfl
  rw [hw, S.rho_mulVec hZ (Subgroup.inclusion S.le ℓ) u]
  rw [← S.beta_conj ℓ u ⟨(ℓ : G) * (u : G) * (ℓ : G)⁻¹,
    conj_mem_blockU S (S.le ℓ.2) u.2⟩ rfl]
  rw [show (⟨↑(Subgroup.inclusion S.le ℓ) * ↑u * (↑(Subgroup.inclusion S.le ℓ))⁻¹,
      conj_mem_blockU S ((Subgroup.inclusion S.le ℓ).2) u.2⟩ : ↥(blockU J)) =
    ⟨(ℓ : G) * (u : G) * (ℓ : G)⁻¹, conj_mem_blockU S (S.le ℓ.2) u.2⟩ from
    Subtype.ext (by simp only [Subgroup.coe_inclusion])]

theorem rho_conj_mem (hZ : blockZ J = ⊥) (x : ↥M) {g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)}
    (hg : g ∈ omegaMinusTwo m) : S.rho hZ x * g * (S.rho hZ x)⁻¹ ∈ omegaMinusTwo m := by
  obtain ⟨ℓ, hℓ⟩ := S.alpha_surjective ⟨g, hg⟩
  have hℓg : (S.alpha ℓ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) = g := congrArg Subtype.val hℓ
  let ℓ' : ↥J := ⟨(x : G) * (ℓ : G) * (x : G)⁻¹, S.normal x.2 ℓ.2⟩
  have hxinc : x * Subgroup.inclusion S.le ℓ * x⁻¹ = Subgroup.inclusion S.le ℓ' :=
    Subtype.ext rfl
  have hcalc : S.rho hZ x * g * (S.rho hZ x)⁻¹ =
      ((S.alpha ℓ' : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) := by
    calc S.rho hZ x * g * (S.rho hZ x)⁻¹
        = S.rho hZ x * S.rho hZ (Subgroup.inclusion S.le ℓ) * (S.rho hZ x)⁻¹ := by
          rw [← hℓg, S.rho_inclusion hZ ℓ]
      _ = S.rho hZ (x * Subgroup.inclusion S.le ℓ * x⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = S.rho hZ (Subgroup.inclusion S.le ℓ') := by rw [hxinc]
      _ = ((S.alpha ℓ' : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :=
          S.rho_inclusion hZ ℓ'
  rw [hcalc]
  exact (S.alpha ℓ').2

theorem minusQuadForm_rho_mulVec (hZ : blockZ J = ⊥) (x : ↥M)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :
    CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1
        (((S.rho hZ x : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
      CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 v := by
  have h6 : 6 ≤ Fintype.card (Fin m ⊕ Fin m ⊕ Fin 2) := by
    have hm : 2 ≤ m := by rcases S.m_eq with h | h <;> omega
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hh : ∀ y ∈ omegaMinusTwo m,
      S.rho hZ x * y * (S.rho hZ x)⁻¹ ∈ omegaMinusTwo m :=
    fun y hy => S.rho_conj_mem hZ x hy
  have h := CFSG.ClassicalGroups.Orthogonal.isometry_of_normalizes_statedOmega
    (Q := quadQ m) (Q₀ := CFSG.Open.StatedQuadMinus (m + 1) (ZMod 2) 1 1)
    (CFSG.LieType.Universal.Spin.coe_quadMinus (m + 1) (ZMod 2) 1 1)
    (nondegenerate_quadQ m) h6 hh v
  have hfun : CFSG.Open.StatedQuadMinus (m + 1) (ZMod 2) 1 1 =
      CFSG.PGLModel.minusQuadForm m (1 : ZMod 2) 1 := rfl
  simpa only [hfun] using h

end Setting

end CFSG.CGT.Harada80
