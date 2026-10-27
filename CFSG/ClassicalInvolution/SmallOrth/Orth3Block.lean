module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3Comm
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmas

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def stabSub (W : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {c | ∀ x, x ∈ W ↔ c x ∈ W}
  one_mem' := fun x => Iff.rfl
  mul_mem' := fun {c d} hc hd x => by
    rw [LinearEquiv.mul_apply, ← hc (d x), ← hd x]
  inv_mem' := fun {c} hc x => by
    rw [hc (c⁻¹ x), LinearEquiv.apply_inv_apply']

theorem mem_stabSub {W : Submodule K V} {c : V ≃ₗ[K] V} :
    c ∈ stabSub W ↔ ∀ x, x ∈ W ↔ c x ∈ W := Iff.rfl

@[expose] noncomputable def resHom (W : Submodule K V) : stabSub W →* (W ≃ₗ[K] W) where
  toFun c :=
    { toFun := fun w => ⟨c.1 w, (c.2 w).mp w.2⟩
      invFun := fun w => ⟨c.1⁻¹ w, (c.2 _).mpr (by rw [LinearEquiv.apply_inv_apply']; exact w.2)⟩
      map_add' := fun x y => Subtype.ext (map_add c.1 (x : V) (y : V))
      map_smul' := fun a x => Subtype.ext (map_smul c.1 a (x : V))
      left_inv := fun x => Subtype.ext (LinearEquiv.inv_apply_apply' _ _)
      right_inv := fun x => Subtype.ext (LinearEquiv.apply_inv_apply' _ _) }
  map_one' := LinearEquiv.ext fun x => rfl
  map_mul' c d := LinearEquiv.ext fun x => rfl

theorem resHom_apply (W : Submodule K V) (c : stabSub W) (w : W) :
    ((resHom W c w : W) : V) = c.1 w := rfl

theorem resHom_inv_apply (W : Submodule K V) (c : stabSub W) (w : W) :
    (((resHom W c)⁻¹ w : W) : V) = c.1⁻¹ w := rfl

section Ext

variable {W W' : Submodule K V}

theorem conj_orthExtend (hc : IsCompl W W') {c : V ≃ₗ[K] V} (hW : c ∈ stabSub W)
    (hW' : c ∈ stabSub W') (φ : W ≃ₗ[K] W) :
    c * orthExtend hc φ * c⁻¹ =
      orthExtend hc (resHom W ⟨c, hW⟩ * φ * (resHom W ⟨c, hW⟩)⁻¹) := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, w, rfl⟩ := exists_add_of_isCompl hc x
  have hu : c⁻¹ (u : V) ∈ W := (hW (c⁻¹ (u : V))).mpr (by
    rw [LinearEquiv.apply_inv_apply']
    exact u.2)
  have hw : c⁻¹ (w : V) ∈ W' := (hW' (c⁻¹ (w : V))).mpr (by
    rw [LinearEquiv.apply_inv_apply']
    exact w.2)
  have h1 := orthExtend_apply hc φ ⟨c⁻¹ (u : V), hu⟩ ⟨c⁻¹ (w : V), hw⟩
  have h2 := orthExtend_apply hc (resHom W ⟨c, hW⟩ * φ * (resHom W ⟨c, hW⟩)⁻¹) u w
  rw [h2, LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_add]
  change c ((orthExtend hc φ) (((⟨c⁻¹ (u : V), hu⟩ : W) : V) + ((⟨c⁻¹ (w : V), hw⟩ : W') : V))) = _
  rw [h1, map_add]
  have h3 : (resHom W ⟨c, hW⟩)⁻¹ u = ⟨c⁻¹ (u : V), hu⟩ :=
    Subtype.ext (resHom_inv_apply W ⟨c, hW⟩ u)
  simp only [LinearEquiv.mul_apply, resHom_apply, h3]
  rw [LinearEquiv.apply_inv_apply']

theorem commute_orthExtend_of_commute (hc : IsCompl W W') {c : V ≃ₗ[K] V} (hW : c ∈ stabSub W)
    (hW' : c ∈ stabSub W') {φ : W ≃ₗ[K] W}
    (h : resHom W ⟨c, hW⟩ * φ = φ * resHom W ⟨c, hW⟩) :
    c * orthExtend hc φ = orthExtend hc φ * c := by
  have h1 := conj_orthExtend hc hW hW' φ
  have h2 : resHom W ⟨c, hW⟩ * φ * (resHom W ⟨c, hW⟩)⁻¹ = φ := by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  rw [h2] at h1
  calc c * orthExtend hc φ = c * orthExtend hc φ * c⁻¹ * c := by group
    _ = orthExtend hc φ * c := by rw [h1]

theorem commute_of_commute_orthExtend (hc : IsCompl W W') {c : V ≃ₗ[K] V} (hW : c ∈ stabSub W)
    (hW' : c ∈ stabSub W') {φ : W ≃ₗ[K] W}
    (h : c * orthExtend hc φ = orthExtend hc φ * c)
    (hinj : Function.Injective (orthExtend hc (K := K) (U := W) (W := W'))) :
    resHom W ⟨c, hW⟩ * φ = φ * resHom W ⟨c, hW⟩ := by
  have h1 := conj_orthExtend hc hW hW' φ
  have h1' : c * orthExtend hc φ * c⁻¹ = orthExtend hc φ := by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1'] at h1
  have h2 := hinj h1
  calc resHom W ⟨c, hW⟩ * φ = resHom W ⟨c, hW⟩ * φ * (resHom W ⟨c, hW⟩)⁻¹ *
        resHom W ⟨c, hW⟩ := by group
    _ = φ * resHom W ⟨c, hW⟩ := by rw [← h2]

end Ext

theorem polar_comp_subtype_apply (W : Submodule K V) (u w : W) :
    polar (Q.comp W.subtype) u w = polar Q (u : V) (w : V) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]
  rfl

theorem nondegenerate_comp_subtype {W W' : Submodule K V} (hQ : (polarBilin Q).Nondegenerate)
    (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0) :
    (polarBilin (Q.comp W.subtype)).Nondegenerate := by
  have key : ∀ v : W, (∀ w : W, polar (Q.comp W.subtype) v w = 0) → v = 0 := by
    intro v hv
    refine Subtype.ext (hQ.1 (v : V) fun y => ?_)
    obtain ⟨u, w, rfl⟩ := exists_add_of_isCompl hc y
    rw [polarBilin_apply_apply, polar_add_right, horth _ v.2 _ w.2,
      ← polar_comp_subtype_apply W, hv u, add_zero]
  exact ⟨fun v hv => key v fun w => by simpa using hv w,
    fun w hw => key w fun v => by rw [polar_comm]; simpa using hw v⟩

theorem resHom_mem_orthogonalGroup {W : Submodule K V} {c : V ≃ₗ[K] V}
    (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hW : c ∈ stabSub W) :
    resHom W ⟨c, hW⟩ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hc ⊢
  exact fun x => hc x

theorem resHom_pow_apply {W : Submodule K V} {ν : V ≃ₗ[K] V} (hW : ν ∈ stabSub W) (n : ℕ)
    (w : W) : (((resHom W ⟨ν, hW⟩ ^ n) w : W) : V) = (ν ^ n) w := by
  have h : resHom W ⟨ν, hW⟩ ^ n = resHom W (⟨ν, hW⟩ ^ n) := (map_pow _ _ _).symm
  rw [h, resHom_apply]
  rfl

section Block

variable {W W' : Submodule K V}

variable (Q) in
@[expose] noncomputable def blockHom (hc : IsCompl W W')
    (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0) :
    ↥(elementaryGroup (Q.comp W.subtype)) →* ↥(elementaryGroup Q) :=
  ((orthExtend hc).comp (elementaryGroup (Q.comp W.subtype)).subtype).codRestrict
    (elementaryGroup Q)
    fun g => (orthogonal_complement_elementary_embedding Q hc horth).2.2.1 g.1 g.2

theorem coe_blockHom (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0)
    (φ : ↥(elementaryGroup (Q.comp W.subtype))) :
    ((blockHom Q hc horth φ : ↥(elementaryGroup Q)) : V ≃ₗ[K] V) =
      orthExtend hc (φ : W ≃ₗ[K] W) := rfl

theorem blockHom_injective (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0) :
    Function.Injective (blockHom Q hc horth) := fun _ _ h =>
  Subtype.ext ((orthogonal_complement_elementary_embedding Q hc horth).1
    (congrArg Subtype.val h))

theorem conj_blockHom_mem_range (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0)
    {b : ↥(elementaryGroup Q)} (hW : (b : V ≃ₗ[K] V) ∈ stabSub W)
    (hW' : (b : V ≃ₗ[K] V) ∈ stabSub W') {x : ↥(elementaryGroup Q)}
    (hx : x ∈ (blockHom Q hc horth).range) : b * x * b⁻¹ ∈ (blockHom Q hc horth).range := by
  obtain ⟨φ, rfl⟩ := hx
  have hb : (b : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q b.2
  refine ⟨⟨resHom W ⟨b, hW⟩ * φ * (resHom W ⟨b, hW⟩)⁻¹, ?_⟩, Subtype.ext ?_⟩
  · exact conj_mem_elementaryGroup (resHom_mem_orthogonalGroup hb hW) φ.2
  · exact (conj_orthExtend hc hW hW' (φ : W ≃ₗ[K] W)).symm

theorem blockHom_commute (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0)
    {g : ↥(elementaryGroup Q)} (hW : (g : V ≃ₗ[K] V) ∈ stabSub W)
    (hW' : (g : V ≃ₗ[K] V) ∈ stabSub W')
    (hφ : ∀ φ : ↥(elementaryGroup (Q.comp W.subtype)),
      resHom W ⟨g, hW⟩ * φ = φ * resHom W ⟨g, hW⟩)
    (φ : ↥(elementaryGroup (Q.comp W.subtype))) :
    blockHom Q hc horth φ * g = g * blockHom Q hc horth φ :=
  Subtype.ext (commute_orthExtend_of_commute hc hW hW' (hφ φ)).symm

theorem exists_pow_res_eq_one [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hc : IsCompl W W')
    (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0) {ν : ↥(elementaryGroup Q)}
    (hW : (ν : V ≃ₗ[K] V) ∈ stabSub W) (hW' : (ν : V ≃ₗ[K] V) ∈ stabSub W')
    (hcomm : ∀ φ, blockHom Q hc horth φ * ν = ν * blockHom Q hc horth φ) :
    ∃ e : ℕ, resHom W ⟨ν, hW⟩ ^ (2 ^ e) = 1 := by
  have hQW := nondegenerate_comp_subtype hQ hc horth
  have hν : (ν : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q ν.2
  have hcomm' : ∀ g ∈ elementaryGroup (Q.comp W.subtype),
      resHom W ⟨ν, hW⟩ * g = g * resHom W ⟨ν, hW⟩ := fun g hg =>
    commute_of_commute_orthExtend hc hW hW' (congrArg Subtype.val (hcomm ⟨g, hg⟩)).symm
      (orthogonal_complement_elementary_embedding Q hc horth).1
  obtain ⟨e, he⟩ := exists_pow_two_pow_eq_one_of_commute hK hQW
    (resHom_mem_orthogonalGroup hν hW) hcomm'
  exact ⟨e, he⟩

theorem pow_eq_one_of_pow_res_eq_one (hc : IsCompl W W') {ν : V ≃ₗ[K] V}
    (hW : ν ∈ stabSub W) (hW' : ν ∈ stabSub W') {n : ℕ}
    (h1 : resHom W ⟨ν, hW⟩ ^ n = 1) (h2 : resHom W' ⟨ν, hW'⟩ ^ n = 1) : ν ^ n = 1 := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, w, rfl⟩ := exists_add_of_isCompl hc x
  have e1 := resHom_pow_apply hW n u
  have e2 := resHom_pow_apply hW' n w
  rw [h1] at e1
  rw [h2] at e2
  rw [map_add, ← e1, ← e2]
  rfl

end Block

end CFSG.ClassicalGroups.Orthogonal.Small
