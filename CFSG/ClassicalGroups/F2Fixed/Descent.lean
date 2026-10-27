module

public import CFSG.ClassicalGroups.F2Fixed

public section

namespace CFSG.ClassicalGroups.F2Fixed

variable {X H : Type*} [Group X] [Group H] {M : Type*} [AddCommGroup M] [DistribMulAction X M]

theorem smul_eq_smul_of_map_eq (ρ : X →* H) (hker : ∀ x ∈ ρ.ker, ∀ a : M, x • a = a)
    {x y : X} (h : ρ x = ρ y) (a : M) : x • a = y • a := by
  have hk : x⁻¹ * y ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  calc x • a = x • ((x⁻¹ * y) • a) := by rw [hker _ hk a]
    _ = y • a := by rw [← mul_smul, mul_inv_cancel_left]

@[expose, instance_reducible] noncomputable def descendAction (ρ : X →* H)
    (hρ : Function.Surjective ρ) (hker : ∀ x ∈ ρ.ker, ∀ a : M, x • a = a) :
    DistribMulAction H M where
  smul h a := (Function.surjInv hρ h) • a
  one_smul a := by
    show (Function.surjInv hρ 1) • a = a
    exact hker _ (by rw [MonoidHom.mem_ker, Function.surjInv_eq hρ 1]) a
  mul_smul h h' a := by
    show (Function.surjInv hρ (h * h')) • a =
      (Function.surjInv hρ h) • (Function.surjInv hρ h') • a
    rw [← mul_smul]
    exact smul_eq_smul_of_map_eq ρ hker (by
      rw [map_mul, Function.surjInv_eq hρ, Function.surjInv_eq hρ, Function.surjInv_eq hρ]) a
  smul_zero h := smul_zero _
  smul_add h a b := smul_add _ a b

theorem descendAction_smul (ρ : X →* H) (hρ : Function.Surjective ρ)
    (hker : ∀ x ∈ ρ.ker, ∀ a : M, x • a = a) (x : X) (a : M) :
    @HSMul.hSMul H M M (@instHSMul H M (descendAction ρ hρ hker).toSMul) (ρ x) a = x • a :=
  smul_eq_smul_of_map_eq ρ hker (Function.surjInv_eq hρ (ρ x)) a

theorem fixedSub_descend (ρ : X →* H) (hρ : Function.Surjective ρ)
    (hker : ∀ x ∈ ρ.ker, ∀ a : M, x • a = a) (S : Subgroup H) :
    @fixedSub H _ M _ (descendAction ρ hρ hker) (S : Set H) =
      fixedSub M ((S.comap ρ : Subgroup X) : Set X) := by
  ext a
  constructor
  · intro h x hx
    have := h (ρ x) hx
    rwa [descendAction_smul] at this
  · intro h g hg
    obtain ⟨x, rfl⟩ := hρ g
    rw [descendAction_smul]
    exact h x hg

section ViaMatrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {Y : Type*} [Group Y]
  {H : Type*} [Group H] (X : Subgroup (GL ι K)) (e : X ≃* H)

@[expose] def viaMatrix (φ : Y →* GL ι K) (hφ : φ.range = X) : Y →* H :=
  e.toMonoidHom.comp (φ.codRestrict X fun y => hφ ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩)

@[expose] def matrixOf (S : Subgroup H) : Subgroup (GL ι K) :=
  (S.comap e.toMonoidHom).map X.subtype

variable {X e}

theorem viaMatrix_apply (φ : Y →* GL ι K) (hφ : φ.range = X) (y : Y) :
    viaMatrix X e φ hφ y = e ⟨φ y, hφ ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩ :=
  rfl

theorem viaMatrix_surjective (φ : Y →* GL ι K) (hφ : φ.range = X) :
    Function.Surjective (viaMatrix X e φ hφ) := by
  intro g
  have h : (e.symm g : GL ι K) ∈ φ.range := by
    rw [hφ]
    exact (e.symm g).2
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp h
  refine ⟨y, ?_⟩
  rw [viaMatrix_apply]
  apply e.symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact Subtype.ext hy

theorem ker_viaMatrix (φ : Y →* GL ι K) (hφ : φ.range = X) :
    (viaMatrix X e φ hφ).ker = φ.ker := by
  ext y
  simp only [MonoidHom.mem_ker, viaMatrix_apply]
  constructor
  · intro h
    have h1 : e ⟨φ y, hφ ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩ = e 1 := by rw [h, map_one]
    exact congrArg Subtype.val (e.injective h1)
  · intro h
    have h1 : (⟨φ y, hφ ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩ : X) = 1 := Subtype.ext h
    rw [h1, map_one]

theorem map_viaMatrix_eq_iff (φ : Y →* GL ι K) (hφ : φ.range = X) (L : Subgroup Y)
    (S : Subgroup H) : L.map (viaMatrix X e φ hφ) = S ↔ L.map φ = matrixOf X e S := by
  set φ' := φ.codRestrict X fun y => hφ ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩ with hφ'
  have hmap : L.map φ = (L.map φ').map X.subtype := by
    rw [Subgroup.map_map]
    rfl
  have e1 : L.map (viaMatrix X e φ hφ) = (L.map φ').map e.toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [e1, hmap]
  unfold matrixOf
  rw [(Subgroup.map_injective X.subtype_injective).eq_iff]
  constructor
  · intro h
    rw [← h, Subgroup.comap_map_eq_self_of_injective e.injective]
  · intro h
    rw [h, Subgroup.map_comap_eq_self_of_surjective e.surjective]

theorem mem_matrixOf_iff {S : Subgroup H} {A : GL ι K} :
    A ∈ matrixOf X e S ↔ ∃ hA : A ∈ X, e ⟨A, hA⟩ ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hA, h⟩
    exact ⟨⟨A, hA⟩, h, rfl⟩

theorem mem_matrixOf_conj_iff {S S' : Subgroup H} (A : X)
    (hS : ∀ h : H, h ∈ S' ↔ (e A)⁻¹ * h * e A ∈ S) (B : GL ι K) :
    B ∈ matrixOf X e S' ↔ (A : GL ι K)⁻¹ * B * (A : GL ι K) ∈ matrixOf X e S := by
  have key : ∀ (hB : B ∈ X) (hB' : (A : GL ι K)⁻¹ * B * (A : GL ι K) ∈ X),
      e ⟨(A : GL ι K)⁻¹ * B * (A : GL ι K), hB'⟩ = (e A)⁻¹ * e ⟨B, hB⟩ * e A := by
    intro hB hB'
    have e2 : (⟨(A : GL ι K)⁻¹ * B * (A : GL ι K), hB'⟩ : X) = A⁻¹ * ⟨B, hB⟩ * A := rfl
    rw [e2, map_mul, map_mul, map_inv]
  constructor
  · intro h
    obtain ⟨hB, hmem⟩ := mem_matrixOf_iff.mp h
    have hB' : (A : GL ι K)⁻¹ * B * (A : GL ι K) ∈ X :=
      mul_mem (mul_mem (inv_mem A.2) hB) A.2
    refine mem_matrixOf_iff.mpr ⟨hB', ?_⟩
    rw [key hB hB']
    exact (hS _).mp hmem
  · intro h
    obtain ⟨hB', hmem⟩ := mem_matrixOf_iff.mp h
    have hB : B ∈ X := by
      have := mul_mem (mul_mem A.2 hB') (inv_mem A.2)
      simpa [mul_assoc] using this
    refine mem_matrixOf_iff.mpr ⟨hB, ?_⟩
    rw [key hB hB'] at hmem
    exact (hS _).mpr hmem

theorem comap_toMonoidHom_eq_map_symm {N G' : Type*} [Group N] [Group G'] (f : N ≃* G')
    (S : Subgroup G') : S.comap f.toMonoidHom = S.map f.symm.toMonoidHom :=
  Subgroup.comap_equiv_eq_map_symm f S

theorem matrixOf_sup (S S' : Subgroup H) :
    matrixOf X e (S ⊔ S') = matrixOf X e S ⊔ matrixOf X e S' := by
  unfold matrixOf
  rw [comap_toMonoidHom_eq_map_symm, comap_toMonoidHom_eq_map_symm,
    comap_toMonoidHom_eq_map_symm, Subgroup.map_sup, Subgroup.map_sup]

theorem matrixOf_top : matrixOf X e (⊤ : Subgroup H) = X := by
  unfold matrixOf
  rw [Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem matrixOf_inf_eq_bot_iff (S S' : Subgroup H) :
    matrixOf X e S ⊓ matrixOf X e S' = ⊥ ↔ S ⊓ S' = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    rintro g ⟨hg1, hg2⟩
    have hA : ((e.symm g : X) : GL ι K) ∈ matrixOf X e S ⊓ matrixOf X e S' :=
      ⟨mem_matrixOf_iff.mpr ⟨(e.symm g).2, by simpa using hg1⟩,
        mem_matrixOf_iff.mpr ⟨(e.symm g).2, by simpa using hg2⟩⟩
    rw [h, Subgroup.mem_bot] at hA
    have : e.symm g = 1 := Subtype.ext hA
    rw [Subgroup.mem_bot]
    simpa using congrArg e this
  · intro h
    rw [eq_bot_iff]
    rintro A ⟨hA1, hA2⟩
    obtain ⟨hAs, hg1⟩ := mem_matrixOf_iff.mp hA1
    obtain ⟨hAs', hg2⟩ := mem_matrixOf_iff.mp hA2
    have hmem : e ⟨A, hAs⟩ ∈ S ⊓ S' := ⟨hg1, hg2⟩
    rw [h, Subgroup.mem_bot] at hmem
    have : (⟨A, hAs⟩ : X) = 1 := e.injective (by rw [hmem, map_one])
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this

theorem fixedSub_viaMatrix_eq {M : Type*} [AddCommGroup M] [DistribMulAction Y M]
    (φ : Y →* GL ι K) (hφ : φ.range = X) (hker : ∀ y ∈ φ.ker, ∀ a : M, y • a = a)
    {L : Subgroup Y} {S : Subgroup H} (hL : L.map φ = matrixOf X e S) :
    fixedSub M ((S.comap (viaMatrix X e φ hφ) : Subgroup Y) : Set Y) =
      fixedSub M (L : Set Y) := by
  have hLs : L.map (viaMatrix X e φ hφ) = S := (map_viaMatrix_eq_iff φ hφ L S).mpr hL
  have hle : L ≤ S.comap (viaMatrix X e φ hφ) := by
    intro y hy
    rw [Subgroup.mem_comap, ← hLs]
    exact Subgroup.mem_map_of_mem _ hy
  refine le_antisymm (fixedSub_anti hle) fun a ha y hy => ?_
  have hy' : viaMatrix X e φ hφ y ∈ L.map (viaMatrix X e φ hφ) := by rw [hLs]; exact hy
  obtain ⟨l, hl, hly⟩ := hy'
  have hk : ∀ x ∈ (viaMatrix X e φ hφ).ker, ∀ a : M, x • a = a := by
    intro x hx a
    rw [ker_viaMatrix] at hx
    exact hker x hx a
  rw [← smul_eq_smul_of_map_eq (viaMatrix X e φ hφ) hk hly]
  exact ha l hl

end ViaMatrix

end CFSG.ClassicalGroups.F2Fixed
