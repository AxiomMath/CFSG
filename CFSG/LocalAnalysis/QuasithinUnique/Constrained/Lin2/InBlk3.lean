module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.CfgBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InSL2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

section FixedField

variable {K : Type} [Field K]

def fixedField (σ : K ≃+* K) : Subfield K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)

theorem mem_fixedField {σ : K ≃+* K} {x : K} : x ∈ fixedField σ ↔ σ x = x := Iff.rfl

@[expose] noncomputable def slFix (σ : K ≃+* K) : SL(2, fixedField σ) →* SL(2, K) :=
  Matrix.SpecialLinearGroup.map (fixedField σ).subtype

theorem slFix_apply (σ : K ≃+* K) (Y : SL(2, fixedField σ)) (i j : Fin 2) :
    (slFix σ Y : Matrix (Fin 2) (Fin 2) K) i j = ((Y : Matrix (Fin 2) (Fin 2) (fixedField σ)) i j : K) :=
  rfl

theorem slFix_injective (σ : K ≃+* K) : Function.Injective (slFix σ) := by
  intro Y Z h
  apply Subtype.ext
  ext i j
  have := congrArg (fun W : SL(2, K) => (W : Matrix (Fin 2) (Fin 2) K) i j) h
  exact this

theorem map_slFix (σ : K ≃+* K) (Y : SL(2, fixedField σ)) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (slFix σ Y) = slFix σ Y := by
  apply Subtype.ext
  ext i j
  exact ((Y : Matrix (Fin 2) (Fin 2) (fixedField σ)) i j).2

theorem exists_slFix (σ : K ≃+* K) {Y : SL(2, K)}
    (hY : Matrix.SpecialLinearGroup.map σ.toRingHom Y = Y) :
    ∃ Y₀ : SL(2, fixedField σ), slFix σ Y₀ = Y := by
  have hfix : ∀ i j, σ ((Y : Matrix (Fin 2) (Fin 2) K) i j) = (Y : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => by
      have := congrArg (fun W : SL(2, K) => (W : Matrix (Fin 2) (Fin 2) K) i j) hY
      exact this
  let M : Matrix (Fin 2) (Fin 2) (fixedField σ) := fun i j => ⟨(Y : Matrix (Fin 2) (Fin 2) K) i j, hfix i j⟩
  have hM : M.map (fixedField σ).subtype = (Y : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    rfl
  have hdet : M.det = 1 := by
    apply (fixedField σ).subtype_injective
    rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact Y.det_coe
  exact ⟨⟨M, hdet⟩, Subtype.ext hM⟩

end FixedField

section Factor

theorem exists_factor {A B C : Type*} [Group A] [Group B] [Group C] (i : C →* B)
    (hi : Function.Injective i) (h : A →* B) (hrange : ∀ a, h a ∈ i.range) :
    ∃ h' : A →* C, ∀ a, i (h' a) = h a := by
  refine ⟨(MonoidHom.ofInjective hi).symm.toMonoidHom.comp (h.codRestrict i.range hrange),
    fun a => ?_⟩
  have := (MonoidHom.ofInjective hi).apply_symm_apply (h.codRestrict i.range hrange a)
  exact congrArg Subtype.val this

end Factor

section VecFix

variable {K : Type} [Field K]

@[expose] noncomputable def vecFix (σ : K ≃+* K) :
    Multiplicative (Fin 2 → fixedField σ) →* Multiplicative (Fin 2 → K) :=
  AddMonoidHom.toMultiplicative
    (AddMonoidHom.compLeft (fixedField σ).subtype.toAddMonoidHom (Fin 2))

theorem vecFix_injective (σ : K ≃+* K) : Function.Injective (vecFix σ) := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext i
  exact Subtype.ext (congrFun (congrArg Multiplicative.toAdd h) i)

theorem slFix_mulVec (σ : K ≃+* K) (Y : SL(2, fixedField σ)) (w : Fin 2 → fixedField σ) (i : Fin 2) :
    (((Y : Matrix (Fin 2) (Fin 2) (fixedField σ)).mulVec w i : fixedField σ) : K) =
      (slFix σ Y : Matrix (Fin 2) (Fin 2) K).mulVec (fun j => (w j : K)) i := by
  simp [Matrix.mulVec, dotProduct, slFix_apply, Fin.sum_univ_two]

end VecFix

section Norm

variable {G : Type} [Group G] {L R : Subgroup G} {n : ℕ} {K : Type} [Field K] [Fintype K] {f : G}

noncomputable instance fixedFieldFintype (σ : K ≃+* K) : Fintype (fixedField σ) :=
  Fintype.ofFinite _

structure NormData (L R : Subgroup G) (n : ℕ) (K : Type) [Field K] [Fintype K] (f : G) where
  A : Adapted L R n K
  σ : K ≃+* K
  hff : f * f = 1
  hfL : ∀ x ∈ L, f * x * f⁻¹ ∈ L
  hfU : ∀ x ∈ blockU L, f * x * f⁻¹ ∈ blockU L
  hσσ : ∀ v, σ (σ v) = v
  hα : ∀ ℓ : L, A.α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ =
    Matrix.SpecialLinearGroup.map σ.toRingHom (A.α ℓ)
  hβ : ∀ u : blockU L, Multiplicative.toAdd (A.β ⟨f * u * f⁻¹, hfU u u.2⟩) =
    fun i => σ (Multiplicative.toAdd (A.β u) i)

theorem NormData.exists_lift (N : NormData L R n K f) (hOL : pCoreOf 2 L = blockU L)
    (hTrU : ∀ x ∈ blockU L, (f * x) * (f * x) = 1 → ∃ m ∈ blockU L, m⁻¹ * f * m = f * x)
    {Y : SL(2, K)} (hY : Matrix.SpecialLinearGroup.map N.σ.toRingHom Y = Y) :
    ∃ ℓ : L, (ℓ : G) ∈ Subgroup.centralizer ({f} : Set G) ∧ N.A.α ℓ = Y := by
  have hUcond : ∀ ℓ : L, (ℓ : G) ∈ blockU L ↔ N.A.α ℓ = 1 := fun ℓ => by
    rw [← hOL]; exact N.A.mem_pCoreOf_iff ℓ
  have hff' : f⁻¹ * f⁻¹ = 1 := by rw [← mul_inv_rev, N.hff, inv_one]
  obtain ⟨ℓ₀, hℓ₀⟩ := N.A.α_surj Y
  have hα₀ : N.A.α ⟨f * ℓ₀ * f⁻¹, N.hfL ℓ₀ ℓ₀.2⟩ = N.A.α ℓ₀ := by rw [N.hα, hℓ₀, hY]
  set w : G := (ℓ₀ : G)⁻¹ * f * ℓ₀ with hw
  have hu₀ : w * f⁻¹ ∈ blockU L := by
    have h1 : (ℓ₀ : G)⁻¹ * (f * ℓ₀ * f⁻¹) ∈ blockU L := by
      refine (hUcond (ℓ₀⁻¹ * ⟨f * ℓ₀ * f⁻¹, N.hfL ℓ₀ ℓ₀.2⟩)).2 ?_
      rw [map_mul, map_inv, hα₀, inv_mul_cancel]
    have e : w * f⁻¹ = (ℓ₀ : G)⁻¹ * (f * ℓ₀ * f⁻¹) := by rw [hw]; group
    rwa [e]
  set x : G := f * (w * f⁻¹) * f⁻¹ with hx
  have hxU : x ∈ blockU L := N.hfU _ hu₀
  have hfx : f * x = w := by
    calc f * x = (f * f) * w * (f⁻¹ * f⁻¹) := by rw [hx]; group
      _ = w := by rw [N.hff, hff']; group
  have hww : w * w = 1 := by
    calc w * w = (ℓ₀ : G)⁻¹ * (f * f) * ℓ₀ := by rw [hw]; group
      _ = 1 := by rw [N.hff]; group
  obtain ⟨m, hm, hmf⟩ := hTrU x hxU (by rw [hfx]; exact hww)
  rw [hfx] at hmf
  have hmL : m ∈ L := blockU_le L hm
  refine ⟨⟨(ℓ₀ : G) * m⁻¹, L.mul_mem ℓ₀.2 (L.inv_mem hmL)⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    show (ℓ₀ : G) * m⁻¹ * f = f * ((ℓ₀ : G) * m⁻¹)
    have h1 : (ℓ₀ : G) * m⁻¹ * f * (m * (ℓ₀ : G)⁻¹) = f := by
      calc (ℓ₀ : G) * m⁻¹ * f * (m * (ℓ₀ : G)⁻¹) = (ℓ₀ : G) * (m⁻¹ * f * m) * (ℓ₀ : G)⁻¹ := by
            group
        _ = (ℓ₀ : G) * w * (ℓ₀ : G)⁻¹ := by rw [hmf]
        _ = f := by rw [hw]; group
    calc (ℓ₀ : G) * m⁻¹ * f = ((ℓ₀ : G) * m⁻¹ * f * (m * (ℓ₀ : G)⁻¹)) * ((ℓ₀ : G) * m⁻¹) := by
          group
      _ = f * ((ℓ₀ : G) * m⁻¹) := by rw [h1]
  · have : N.A.α ⟨(ℓ₀ : G) * m⁻¹, L.mul_mem ℓ₀.2 (L.inv_mem hmL)⟩ =
        N.A.α ℓ₀ * (N.A.α ⟨m, hmL⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [this, (hUcond ⟨m, hmL⟩).1 hm, inv_one, mul_one, hℓ₀]

theorem NormData.slFix_exists_of_mem (N : NormData L R n K f) (c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G))) :
    ∃ Y₀ : SL(2, fixedField N.σ), slFix N.σ Y₀ = N.A.α ⟨c, c.2.1⟩ := by
  apply exists_slFix
  have hc : (c : G) * f = f * c := Subgroup.mem_centralizer_singleton_iff.1 c.2.2
  have hconj : f * (c : G) * f⁻¹ = c := by rw [← hc]; group
  have h1 := N.hα ⟨c, c.2.1⟩
  have h2 : (⟨f * (c : G) * f⁻¹, N.hfL _ c.2.1⟩ : L) = ⟨c, c.2.1⟩ := Subtype.ext hconj
  rw [h2] at h1
  exact h1.symm

theorem NormData.exists_alphaC (N : NormData L R n K f) (hOL : pCoreOf 2 L = blockU L)
    (hTrU : ∀ x ∈ blockU L, (f * x) * (f * x) = 1 → ∃ m ∈ blockU L, m⁻¹ * f * m = f * x) :
    ∃ α' : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)) →* SL(2, fixedField N.σ),
      (∀ c, slFix N.σ (α' c) = N.A.α ⟨c, c.2.1⟩) ∧ Function.Surjective α' ∧
        ∀ c, α' c = 1 ↔ (c : G) ∈ blockU L := by
  have hUcond : ∀ ℓ : L, (ℓ : G) ∈ blockU L ↔ N.A.α ℓ = 1 := fun ℓ => by
    rw [← hOL]; exact N.A.mem_pCoreOf_iff ℓ
  obtain ⟨α', hα'⟩ := exists_factor (slFix N.σ) (slFix_injective N.σ)
    (N.A.α.comp (Subgroup.inclusion (inf_le_left : L ⊓ Subgroup.centralizer ({f} : Set G) ≤ L)))
    (fun c => N.slFix_exists_of_mem c)
  refine ⟨α', hα', ?_, ?_⟩
  · intro Y₀
    obtain ⟨ℓ, hℓC, hℓ⟩ := N.exists_lift hOL hTrU (Y := slFix N.σ Y₀) (map_slFix N.σ Y₀)
    refine ⟨⟨ℓ, ℓ.2, hℓC⟩, slFix_injective N.σ ?_⟩
    rw [hα']
    exact hℓ
  · intro c
    constructor
    · intro h
      have := hα' c
      rw [h, map_one] at this
      exact (hUcond ⟨c, c.2.1⟩).2 this.symm
    · intro h
      apply slFix_injective N.σ
      rw [hα', map_one]
      exact (hUcond ⟨c, c.2.1⟩).1 h

theorem NormData.exists_betaV (N : NormData L R n K f)
    (hTrZ : ∀ x ∈ blockZ L, (f * x) * (f * x) = 1 → ∃ m ∈ blockZ L, m⁻¹ * f * m = f * x) :
    ∃ β' : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G)) →*
        Multiplicative (Fin 2 → fixedField N.σ),
      (∀ v, vecFix N.σ (β' v) = N.A.β ⟨v, v.2.1⟩) ∧ Function.Surjective β' ∧
        ∀ v, β' v = 1 ↔ (v : G) ∈ blockZ L := by
  have hff' : f⁻¹ * f⁻¹ = 1 := by rw [← mul_inv_rev, N.hff, inv_one]
  have hfixed : ∀ v : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G)), ∀ i,
      N.σ (Multiplicative.toAdd (N.A.β ⟨v, v.2.1⟩) i) =
        Multiplicative.toAdd (N.A.β ⟨v, v.2.1⟩) i := by
    intro v i
    have hc : (v : G) * f = f * v := Subgroup.mem_centralizer_singleton_iff.1 v.2.2
    have hconj : f * (v : G) * f⁻¹ = v := by rw [← hc]; group
    have h2 : (⟨f * (v : G) * f⁻¹, N.hfU _ v.2.1⟩ : blockU L) = ⟨v, v.2.1⟩ := Subtype.ext hconj
    have h3 : N.A.β ⟨f * (v : G) * f⁻¹, N.hfU _ v.2.1⟩ = N.A.β ⟨v, v.2.1⟩ := congrArg N.A.β h2
    have h1 : Multiplicative.toAdd (N.A.β ⟨f * (v : G) * f⁻¹, N.hfU _ v.2.1⟩) =
        fun i => N.σ (Multiplicative.toAdd (N.A.β ⟨v, v.2.1⟩) i) := N.hβ ⟨v, v.2.1⟩
    rw [h3] at h1
    exact (congrFun h1 i).symm
  obtain ⟨β', hβ'⟩ := exists_factor (vecFix N.σ) (vecFix_injective N.σ)
    (N.A.β.comp (Subgroup.inclusion
      (inf_le_left : blockU L ⊓ Subgroup.centralizer ({f} : Set G) ≤ blockU L)))
    (fun v => ⟨Multiplicative.ofAdd (fun i => ⟨Multiplicative.toAdd (N.A.β ⟨v, v.2.1⟩) i,
      hfixed v i⟩), Multiplicative.toAdd.injective (funext fun i => rfl)⟩)
  have hβ'' : ∀ v : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G)),
      vecFix N.σ (β' v) = N.A.β ⟨v, v.2.1⟩ := hβ'
  refine ⟨β', hβ'', ?_, ?_⟩
  · intro y
    obtain ⟨u, hu⟩ := N.A.β_surj (vecFix N.σ y)
    have hfu : f * (u : G) * f⁻¹ ∈ blockU L := N.hfU u u.2
    have hβfu : N.A.β ⟨f * (u : G) * f⁻¹, hfu⟩ = N.A.β u := by
      apply Multiplicative.toAdd.injective
      rw [N.hβ u, hu]
      funext i
      exact (Multiplicative.toAdd y i).2
    have hz : (⟨f * (u : G) * f⁻¹, hfu⟩ * u⁻¹ : blockU L) ∈ N.A.β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβfu, mul_inv_cancel]
    rw [N.A.β_ker, Subgroup.mem_subgroupOf] at hz
    set z : G := f * (u : G) * f⁻¹ * (u : G)⁻¹ with hzdef
    have hzZ : z ∈ blockZ L := hz
    have hfz : f * z * f⁻¹ = z⁻¹ := by
      have h1 : f * z * f⁻¹ * z = 1 := by
        calc f * z * f⁻¹ * z = (f * f) * (u : G) * (f⁻¹ * f⁻¹) * (u : G)⁻¹ := by
              rw [hzdef]; group
          _ = 1 := by rw [N.hff, hff']; group
      exact mul_eq_one_iff_eq_inv.1 h1
    have hz2 : (f * z) * (f * z) = 1 := by
      calc (f * z) * (f * z) = (f * z * f⁻¹) * (f * f) * z := by group
        _ = 1 := by rw [hfz, N.hff]; group
    obtain ⟨m, hm, hmf⟩ := hTrZ z hzZ hz2
    have hmU : m ∈ blockU L := blockZ_le_blockU L hm
    have hfm : f * m = m * (f * z) := by
      calc f * m = m * (m⁻¹ * f * m) := by group
        _ = m * (f * z) := by rw [hmf]
    have hzu : (u : G) * z = z * u :=
      Subgroup.mem_centralizer_iff.1 hzZ.2 u (blockU_le L u.2)
    have hzm : m * z = z * m := Subgroup.mem_centralizer_iff.1 hzZ.2 m (blockU_le L hmU)
    have hfu' : f * (u : G) * f⁻¹ = z * u := by rw [hzdef]; group
    have hfm' : f * m * f⁻¹ = m * z⁻¹ := by
      calc f * m * f⁻¹ = (m * (f * z)) * f⁻¹ := by rw [hfm]
        _ = m * (f * z * f⁻¹) := by group
        _ = m * z⁻¹ := by rw [hfz]
    have hfum : f * ((u : G) * m) * f⁻¹ = (u : G) * m := by
      calc f * ((u : G) * m) * f⁻¹ = (f * (u : G) * f⁻¹) * (f * m * f⁻¹) := by group
        _ = (z * u) * (m * z⁻¹) := by rw [hfu', hfm']
        _ = (u : G) * (z * m) * z⁻¹ := by rw [← hzu]; group
        _ = (u : G) * (m * z) * z⁻¹ := by rw [← hzm]
        _ = (u : G) * m := by group
    have hcent : (u : G) * m * f = f * ((u : G) * m) := by
      calc (u : G) * m * f = (f * ((u : G) * m) * f⁻¹) * f := by rw [hfum]
        _ = f * ((u : G) * m) := by group
    have hum : (u : G) * m ∈ blockU L := (blockU L).mul_mem u.2 hmU
    have hcm : (u : G) * m ∈ Subgroup.centralizer ({f} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hcent
    refine ⟨⟨(u : G) * m, hum, hcm⟩, ?_⟩
    apply vecFix_injective N.σ
    rw [hβ'']
    have hmk : N.A.β ⟨m, hmU⟩ = 1 := by
      have : (⟨m, hmU⟩ : blockU L) ∈ N.A.β.ker := by
        rw [N.A.β_ker, Subgroup.mem_subgroupOf]
        exact hm
      exact this
    have e : (⟨(u : G) * m, hum⟩ : blockU L) = u * ⟨m, hmU⟩ := rfl
    rw [e, map_mul, hmk, mul_one, hu]
  · intro v
    constructor
    · intro h
      have h1 : N.A.β ⟨v, v.2.1⟩ = 1 := by
        rw [← hβ'' v, h, map_one]
      have : (⟨v, v.2.1⟩ : blockU L) ∈ N.A.β.ker := h1
      rw [N.A.β_ker, Subgroup.mem_subgroupOf] at this
      exact this
    · intro h
      apply vecFix_injective N.σ
      rw [hβ'' v, map_one]
      have : (⟨v, v.2.1⟩ : blockU L) ∈ N.A.β.ker := by
        rw [N.A.β_ker, Subgroup.mem_subgroupOf]
        exact h
      exact this

end Norm

end CFSG.QuasithinUnique.Lin2
