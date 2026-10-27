module

public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm CFSG.Open

@[expose] def cls {G : Type*} [Group G] (t : G) : Set G := {x | ∃ e : G, x = e * t * e⁻¹}

section Cls

variable {G : Type*} [Group G] {t x : G}

theorem self_mem_cls : t ∈ cls t := ⟨1, by simp⟩

theorem conj_mem_cls (hx : x ∈ cls t) (g : G) : g * x * g⁻¹ ∈ cls t := by
  obtain ⟨e, rfl⟩ := hx
  exact ⟨g * e, by group⟩

theorem exists_conj_of_mem_cls (hx : x ∈ cls t) : ∃ e : G, x = e * t * e⁻¹ := hx

theorem orderOf_of_mem_cls_of (ht : orderOf t = 2) (hx : x ∈ cls t) : orderOf x = 2 := by
  obtain ⟨e, rfl⟩ := hx
  have := MulEquiv.orderOf_eq (MulAut.conj e) t
  rw [MulAut.conj_apply] at this
  rw [this, ht]

end Cls

structure Cfg (G : Type) [Group G] (n : ℕ) where
  t : G
  ht : orderOf t = 2
  ot : ∀ e : G, orderOf (t * (e * t * e⁻¹)) = 1 ∨ orderOf (t * (e * t * e⁻¹)) = 2 ∨
    Odd (orderOf (t * (e * t * e⁻¹)))
  hn : 7 ≤ n
  Y : Subgroup G
  hY : IsComponentOf Y (Subgroup.centralizer ({t} : Set G))
  hYle : Y ≤ Subgroup.closure (cls t)
  ε : Y ≃* alternatingGroup (Fin n)
  k2 : ∀ e ∈ cls t, e ≠ t → t * e = e * t → e ∉ Subgroup.centralizer (Y : Set G)

namespace Cfg

variable {G : Type} [Group G] {n : ℕ} (c : Cfg G n)

theorem mul_self_of_mem_cls {x : G} (hx : x ∈ cls c.t) : x * x = 1 := by
  obtain ⟨e, rfl⟩ := hx
  have h : c.t * c.t = 1 := by
    have := pow_orderOf_eq_one c.t
    rwa [c.ht, pow_two] at this
  calc e * c.t * e⁻¹ * (e * c.t * e⁻¹) = e * (c.t * c.t) * e⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem inv_of_mem_cls {x : G} (hx : x ∈ cls c.t) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (c.mul_self_of_mem_cls hx)

theorem ot_cls {x y : G} (hx : x ∈ cls c.t) (hy : y ∈ cls c.t) :
    Odd (orderOf (x * y)) ∨ orderOf (x * y) = 2 := by
  obtain ⟨e, rfl⟩ := hx
  obtain ⟨f, rfl⟩ := hy
  have h1 : e * c.t * e⁻¹ * (f * c.t * f⁻¹) =
      MulAut.conj e (c.t * ((e⁻¹ * f) * c.t * (e⁻¹ * f)⁻¹)) := by
    simp only [MulAut.conj_apply]; group
  rw [h1, MulEquiv.orderOf_eq]
  rcases c.ot (e⁻¹ * f) with h | h | h
  · left; rw [h]; exact odd_one
  · right; exact h
  · left; exact h

@[expose] def Dloc (d : G) : Set G := {x | x ∈ cls c.t ∧ x ≠ d ∧ d * x = x * d}

@[expose] def Dt : Set G := c.Dloc c.t

@[expose] def N : Subgroup G := Subgroup.normalizer (c.Y : Set G)

@[expose] noncomputable def autEquiv : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
  MulEquiv.ofBijective
    (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by have := c.hn; omega)
      (by have := c.hn; omega))

@[expose] def iotaHom : c.Y →* Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype.comp c.ε.toMonoidHom

@[expose] noncomputable def piHom : c.N →* Perm (Fin n) :=
  c.autEquiv.symm.toMonoidHom.comp ((MulAut.congr c.ε).toMonoidHom.comp c.Y.normalizerMonoidHom)

open scoped Classical in
@[expose] noncomputable def ι (y : G) : Perm (Fin n) :=
  if h : y ∈ c.Y then c.iotaHom ⟨y, h⟩ else 1

open scoped Classical in
@[expose] noncomputable def φ (g : G) : Perm (Fin n) :=
  if h : g ∈ c.N then c.piHom ⟨g, h⟩ else 1

variable {x y g : G}

theorem autEquiv_apply (σ : Perm (Fin n)) (u : alternatingGroup (Fin n)) :
    ((c.autEquiv σ u : alternatingGroup (Fin n)) : Perm (Fin n)) = σ * u * σ⁻¹ := by
  simp [autEquiv, MulAut.conjNormal_apply]

theorem piHom_spec (hg : g ∈ c.N) (u : alternatingGroup (Fin n)) :
    c.piHom ⟨g, hg⟩ * (u : Perm (Fin n)) * (c.piHom ⟨g, hg⟩)⁻¹ =
      ((c.ε (c.Y.normalizerMonoidHom ⟨g, hg⟩ (c.ε.symm u)) : alternatingGroup (Fin n)) :
        Perm (Fin n)) := by
  rw [← c.autEquiv_apply]
  have : c.autEquiv (c.piHom ⟨g, hg⟩) = MulAut.congr c.ε (c.Y.normalizerMonoidHom ⟨g, hg⟩) := by
    simp only [piHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl
  rw [this]
  rfl

theorem ι_of_mem (hy : y ∈ c.Y) : c.ι y = c.iotaHom ⟨y, hy⟩ := by
  simp [ι, hy]

theorem ι_one : c.ι 1 = 1 := by
  rw [c.ι_of_mem c.Y.one_mem]
  exact map_one c.iotaHom

theorem ι_mul (hx : x ∈ c.Y) (hy : y ∈ c.Y) : c.ι (x * y) = c.ι x * c.ι y := by
  rw [c.ι_of_mem (c.Y.mul_mem hx hy), c.ι_of_mem hx, c.ι_of_mem hy]
  exact map_mul c.iotaHom ⟨x, hx⟩ ⟨y, hy⟩

theorem ι_inv (hx : x ∈ c.Y) : c.ι x⁻¹ = (c.ι x)⁻¹ := by
  rw [c.ι_of_mem (c.Y.inv_mem hx), c.ι_of_mem hx]
  exact map_inv c.iotaHom ⟨x, hx⟩

theorem ι_injOn : Set.InjOn c.ι c.Y := by
  intro x hx y hy h
  rw [c.ι_of_mem hx, c.ι_of_mem hy] at h
  have h1 : c.ε ⟨x, hx⟩ = c.ε ⟨y, hy⟩ := Subtype.ext h
  have := c.ε.injective h1
  exact congrArg Subtype.val this

theorem exists_ι_eq {u : Perm (Fin n)} (hu : u ∈ alternatingGroup (Fin n)) :
    ∃ y ∈ c.Y, c.ι y = u := by
  refine ⟨(c.ε.symm ⟨u, hu⟩ : c.Y), (c.ε.symm ⟨u, hu⟩).2, ?_⟩
  rw [c.ι_of_mem (c.ε.symm ⟨u, hu⟩).2]
  simp [iotaHom]

theorem orderOf_ι (hx : x ∈ c.Y) : orderOf (c.ι x) = orderOf x := by
  rw [c.ι_of_mem hx]
  have hinj : Function.Injective c.iotaHom := by
    intro a b h
    exact c.ε.injective (Subtype.ext h)
  rw [orderOf_injective c.iotaHom hinj ⟨x, hx⟩]
  exact Subgroup.orderOf_mk x hx

theorem Y_le_N : c.Y ≤ c.N :=
  Subgroup.le_normalizer

theorem φ_of_mem (hg : g ∈ c.N) : c.φ g = c.piHom ⟨g, hg⟩ := by
  simp [φ, hg]

theorem φ_mul (hx : x ∈ c.N) (hy : y ∈ c.N) : c.φ (x * y) = c.φ x * c.φ y := by
  rw [c.φ_of_mem (c.N.mul_mem hx hy), c.φ_of_mem hx, c.φ_of_mem hy]
  have h := map_mul c.piHom ⟨x, hx⟩ ⟨y, hy⟩
  exact h

theorem φ_one : c.φ 1 = 1 := by
  rw [c.φ_of_mem (c.N.one_mem)]
  exact map_one c.piHom

theorem φ_inv (hx : x ∈ c.N) : c.φ x⁻¹ = (c.φ x)⁻¹ := by
  rw [c.φ_of_mem (c.N.inv_mem hx), c.φ_of_mem hx]
  have h := map_inv c.piHom ⟨x, hx⟩
  exact h

theorem conj_mem_Y (hx : x ∈ c.N) (hy : y ∈ c.Y) : x * y * x⁻¹ ∈ c.Y := by
  have hx' : x ∈ Subgroup.normalizer (c.Y : Set G) := hx
  exact (Subgroup.mem_normalizer_iff.1 hx' y).1 hy

theorem ι_conj (hx : x ∈ c.N) (hy : y ∈ c.Y) :
    c.ι (x * y * x⁻¹) = c.φ x * c.ι y * (c.φ x)⁻¹ := by
  have hz := c.conj_mem_Y hx hy
  rw [c.ι_of_mem hz, c.ι_of_mem hy, c.φ_of_mem hx]
  have h := c.piHom_spec hx (c.ε ⟨y, hy⟩)
  rw [MulEquiv.symm_apply_apply] at h
  have h2 : c.Y.normalizerMonoidHom ⟨x, hx⟩ ⟨y, hy⟩ = ⟨x * y * x⁻¹, hz⟩ :=
    Subtype.ext (by simp)
  rw [h2] at h
  exact h.symm

theorem φ_of_mem_Y (hy : y ∈ c.Y) : c.φ y = c.ι y := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n
    (by have := c.hn; omega)
  apply hinj
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  obtain ⟨z, hz, hzu⟩ := c.exists_ι_eq u.2
  simp only [MulAut.conjNormal_apply]
  rw [← hzu, ← c.ι_conj (c.Y_le_N hy) hz, c.ι_mul (c.Y.mul_mem hy hz) (c.Y.inv_mem hy),
    c.ι_mul hy hz, c.ι_inv hy]

theorem commute_of_φ_eq_one (hx : x ∈ c.N) (h1 : c.φ x = 1) : ∀ z ∈ c.Y, x * z = z * x := by
  intro z hz
  have h2 := c.ι_conj hx hz
  rw [h1] at h2
  simp only [one_mul, inv_one, mul_one] at h2
  have h3 : x * z * x⁻¹ = z := c.ι_injOn (c.conj_mem_Y hx hz) hz h2
  calc x * z = x * z * x⁻¹ * x := by group
    _ = z * x := by rw [h3]

theorem Y_center : ∀ z ∈ c.Y, (∀ w ∈ c.Y, z * w = w * z) → z = 1 := by
  intro z hz hc
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n
    (by have := c.hn; omega)
  have h1 : c.ι z = 1 := by
    apply hinj
    rw [map_one]
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    obtain ⟨w, hw, hwu⟩ := c.exists_ι_eq u.2
    simp only [MulAut.conjNormal_apply]
    have h2 : c.ι z * c.ι w = c.ι w * c.ι z := by
      rw [← c.ι_mul hz hw, ← c.ι_mul hw hz, hc w hw]
    have h3 : c.ι z * (u : Perm (Fin n)) * (c.ι z)⁻¹ = u := by
      rw [← hwu, h2, mul_inv_cancel_right]
    simpa using h3
  exact c.ι_injOn hz c.Y.one_mem (by rw [h1, c.ι_one])

theorem Y_commute_t (hy : y ∈ c.Y) : c.t * y = y * c.t :=
  (Subgroup.mem_centralizer_singleton_iff.1 (c.hY.1 hy)).symm

theorem t_mem_cls : c.t ∈ cls c.t := self_mem_cls

end Cfg

end CFSG.EvenSmallLie.OddTranspAlt
