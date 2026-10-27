module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement


variable {H H' : Type} [Group H] [Group H']

theorem mem_map_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (N : Subgroup G) (x : G) : e x ∈ N.map e.toMonoidHom ↔ x ∈ N := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [e.injective hxy] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem isConj_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {x y : G} (h : IsConj x y) : IsConj (e x) (e y) := by
  rw [isConj_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact ⟨e c, by rw [← map_mul, ← map_inv, ← map_mul, hc]⟩

theorem isConj_of_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {x y : G} (h : IsConj (e x) (e y)) : IsConj x y := by
  rw [isConj_iff] at h ⊢
  obtain ⟨c', hc'⟩ := h
  exact ⟨e.symm c',
    e.injective (by simpa only [map_mul, map_inv, e.apply_symm_apply] using hc')⟩

theorem mem_center_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (g : G) : e g ∈ Subgroup.center G' ↔ g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro hg k
    have := hg (e k)
    rw [← map_mul, ← map_mul] at this
    exact e.injective this
  · intro hg k
    obtain ⟨k', rfl⟩ := e.surjective k
    rw [← map_mul, ← map_mul, hg k']

theorem map_sup_zpowers {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (x y : G) :
    (Subgroup.zpowers x ⊔ Subgroup.zpowers y).map e.toMonoidHom
      = Subgroup.zpowers (e x) ⊔ Subgroup.zpowers (e y) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

theorem orderOf_symm {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (x' : G') :
    orderOf (e.symm x') = orderOf x' :=
  orderOf_injective e.symm.toMonoidHom e.symm.injective x'

theorem conj_comp_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (g : G) :
    e.toMonoidHom.comp (MulAut.conj g).toMonoidHom
      = (MulAut.conj (e g)).toMonoidHom.comp e.toMonoidHom := by
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem map_map_subtype_mulEquiv {G G' A A' : Type*} [Group G] [Group G']
    [Group A] [Group A'] (e : A ≃* A') (φ : G ≃* G') (f : G →* A) (f' : G' →* A')
    (hsub : ∀ x : G, e (f x) = f' (φ x)) (T : Subgroup G) :
    (T.map f).map e.toMonoidHom = (T.map φ.toMonoidHom).map f' := by
  simp only [Subgroup.map_map]
  congr 1
  ext x
  exact hsub x

theorem vec_apply_map (e : H ≃* H') (a z b z₁ : H) (i : Fin 5) :
    (![e a, e z, e a * e z, e b, e z₁] : Fin 5 → H') i
      = e (![a, z, a * z, b, z₁] i) := by
  fin_cases i <;> simp

theorem map_centralizer_singleton (e : H ≃* H') (x : H) :
    (centralizer ({x} : Set H)).map e.toMonoidHom = centralizer ({e x} : Set H') := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hw]
  · intro hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [Subgroup.mem_map]
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy

@[expose] noncomputable def mapSubgroupMulEquiv (e : H ≃* H') (K : Subgroup H) :
    K ≃* K.map e.toMonoidHom where
  toFun x := ⟨e x, Subgroup.mem_map.mpr ⟨(x : H), x.2, rfl⟩⟩
  invFun y := ⟨e.symm y, by
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp y.2
    rw [← hky]
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using hk⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; exact map_mul e (x : H) (y : H)

theorem mapSubgroupMulEquiv_coe (e : H ≃* H') (K : Subgroup H) (y : K) :
    (mapSubgroupMulEquiv e K y : H') = e (y : H) := rfl

@[expose] noncomputable def centralizerMulEquiv (e : H ≃* H') (x : H) :
    ↥(centralizer ({x} : Set H)) ≃* ↥(centralizer ({e x} : Set H')) where
  toFun y := ⟨e y, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [← map_mul, ← map_mul, hy]⟩
  invFun y := ⟨e.symm y, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp
  map_mul' y z := by ext; simp [map_mul]

theorem centralizerMulEquiv_coe (e : H ≃* H') (x : H)
    (y : ↥(centralizer ({x} : Set H))) :
    (centralizerMulEquiv e x y : H') = e (y : H) := rfl

@[expose] noncomputable def centralizerMulEquiv' (e : H ≃* H') (x' : H') :
    ↥(centralizer ({e.symm x'} : Set H)) ≃* ↥(centralizer ({x'} : Set H')) :=
  (centralizerMulEquiv e (e.symm x')).trans
    (MulEquiv.subgroupCongr (by rw [e.apply_symm_apply]))

theorem centralizerMulEquiv'_coe (e : H ≃* H') (x' : H')
    (y : ↥(centralizer ({e.symm x'} : Set H))) :
    (centralizerMulEquiv' e x' y : H') = e (y : H) := by
  simp only [centralizerMulEquiv', MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
  exact centralizerMulEquiv_coe e (e.symm x') y

theorem nonempty_centralizer_mulEquiv (e : H ≃* H') (x : H) :
    Nonempty (↥(centralizer ({x} : Set H)) ≃* ↥(centralizer ({e x} : Set H'))) :=
  ⟨centralizerMulEquiv e x⟩

theorem map_commutator_mulEquiv (e : H ≃* H') :
    (commutator H).map e.toMonoidHom = commutator H' := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator]
  simp

theorem map_K_eq (e : H ≃* H') (z : H) :
    (commutator H ⊓ centralizer ({z} : Set H)).map e.toMonoidHom
      = commutator H' ⊓ centralizer ({e z} : Set H') := by
  rw [Subgroup.map_inf_eq (commutator H) (centralizer ({z} : Set H)) e.toMonoidHom e.injective,
    map_commutator_mulEquiv e, map_centralizer_singleton e z]

theorem center_K_of_mulEquiv (e : H ≃* H') (a z : H)
    (h : ∀ g : ↥(commutator H ⊓ centralizer ({z} : Set H)),
      g ∈ center ↥(commutator H ⊓ centralizer ({z} : Set H)) ↔
        (g : H) ∈ zpowers a ⊔ zpowers z) :
    ∀ g' : ↥(commutator H' ⊓ centralizer ({e z} : Set H')),
      g' ∈ center ↥(commutator H' ⊓ centralizer ({e z} : Set H')) ↔
        (g' : H') ∈ zpowers (e a) ⊔ zpowers (e z) := by
  let K : Subgroup H := commutator H ⊓ centralizer ({z} : Set H)
  let K' : Subgroup H' := commutator H' ⊓ centralizer ({e z} : Set H')
  have hKmap : K.map e.toMonoidHom = K' := by
    change (commutator H ⊓ centralizer ({z} : Set H)).map e.toMonoidHom
      = commutator H' ⊓ centralizer ({e z} : Set H')
    exact map_K_eq e z
  let φ : K ≃* K' :=
    (mapSubgroupMulEquiv e K).trans (MulEquiv.subgroupCongr hKmap)
  have hφcoe : ∀ g : K, (φ g : H') = e (g : H) := fun g => mapSubgroupMulEquiv_coe e K g
  intro g'
  have h1 : g' ∈ center K' ↔ φ.symm g' ∈ center K := by
    simpa using mem_center_mulEquiv φ (φ.symm g')
  have h2 := h (φ.symm g')
  have hcoe : e ((φ.symm g' : K) : H) = (g' : H') := by
    rw [← hφcoe (φ.symm g'), φ.apply_symm_apply]
  calc
    g' ∈ center K' ↔ φ.symm g' ∈ center K := h1
    _ ↔ ((φ.symm g' : K) : H) ∈ zpowers a ⊔ zpowers z := h2
    _ ↔ e ((φ.symm g' : K) : H) ∈ zpowers (e a) ⊔ zpowers (e z) := by
          rw [← map_sup_zpowers e a z]
          exact (mem_map_iff e _ _).symm
    _ ↔ (g' : H') ∈ zpowers (e a) ⊔ zpowers (e z) := by rw [hcoe]

theorem isSectionOf_of_mulEquiv {X : Type*} [Group X] (e : H ≃* H')
    (h : CFSG.SignalizerFunctorTheorem.IsSectionOf X H) :
    CFSG.SignalizerFunctorTheorem.IsSectionOf X H' := by
  obtain ⟨K, f, hf⟩ := h
  refine ⟨K.map e.toMonoidHom, ?_⟩
  refine ⟨f.comp (mapSubgroupMulEquiv e K).symm.toMonoidHom, ?_⟩
  intro x
  obtain ⟨y, hy⟩ := hf x
  exact ⟨mapSubgroupMulEquiv e K y, by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hy]⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
