module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusSetup2
public import CFSG.CGT.PushingUpLit.CGT6.Diag.NatSchur
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenPlus
public import CFSG.CGT.PushingUpLit.CGT6.EmbOmega

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 Matrix Multiplicative

variable {V : Type} [CommGroup V]

theorem eq_one_of_fst_fix {Y : Subgroup (MulAut V)} {n : ℕ} (θ : ↥Y ≃* SLq n × SLq n)
    (φ : ↥(commV Y) ≃* Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)))
    (hφ : ∀ (y : ↥Y) (u : ↥(commV Y)) (hp : (y : MulAut V) u ∈ commV Y),
      φ ⟨(y : MulAut V) u, hp⟩ = omegaPlusAct n (θ y) (φ u))
    (u : ↥(commV Y)) (h : ∀ A : SLq n, ((θ.symm (A, 1) : ↥Y) : MulAut V) u = u) : u = 1 := by
  have hM : toAdd (φ u) = 0 := by
    apply eq_zero_of_forall_sl_mul
    intro s
    have hp : ((θ.symm (s, 1) : ↥Y) : MulAut V) u ∈ commV Y := by rw [h s]; exact u.2
    have h1 := hφ (θ.symm (s, 1)) u hp
    have h2 : (⟨((θ.symm (s, 1) : ↥Y) : MulAut V) u, hp⟩ : ↥(commV Y)) = u := Subtype.ext (h s)
    rw [h2, MulEquiv.apply_symm_apply] at h1
    have h3 := congrArg toAdd h1
    simp [omegaPlusAct] at h3
    exact h3.symm
  have h1 : φ u = 1 := by rw [← ofAdd_toAdd (φ u), hM, ofAdd_zero]
  exact φ.injective (h1.trans (map_one φ).symm)

theorem fixV_eq_of_complement {Y : Subgroup (MulAut V)} {n : ℕ} (θ : ↥Y ≃* SLq n × SLq n)
    (φ : ↥(commV Y) ≃* Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)))
    (hφ : ∀ (y : ↥Y) (u : ↥(commV Y)) (hp : (y : MulAut V) u ∈ commV Y),
      φ ⟨(y : MulAut V) u, hp⟩ = omegaPlusAct n (θ y) (φ u))
    {C : Subgroup V} (hC : ∀ y ∈ Y, ∀ c ∈ C, y c = c) (hsup : C ⊔ commV Y = ⊤) :
    fixV Y = C := by
  refine le_antisymm (fun v hv => ?_) (fun v hv y hy => hC y hy v hv)
  have hv' : v ∈ C ⊔ commV Y := hsup ▸ Subgroup.mem_top v
  obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup.mp hv'
  have hfix : ∀ y ∈ Y, y u = u := fun y hy => by
    have h1 := hv y hy
    rw [map_mul, hC y hy c hc] at h1
    exact mul_left_cancel h1
  have h1 := eq_one_of_fst_fix θ φ hφ ⟨u, hu⟩ fun A => hfix _ (θ.symm (A, 1)).2
  have h2 : u = 1 := congrArg Subtype.val h1
  rw [h2, mul_one]
  exact hc

structure PlusCoord (Y : Subgroup (MulAut V)) (n : ℕ) where
  θ : ↥Y ≃* SLq n × SLq n
  φ : ↥(commV Y) ≃* Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n))
  mapsTo : ∀ y ∈ Y, ∀ p ∈ commV Y, y p ∈ commV Y
  act : ∀ (y : ↥Y) (u : ↥(commV Y)) (hp : (y : MulAut V) u ∈ commV Y),
    φ ⟨(y : MulAut V) u, hp⟩ = omegaPlusAct n (θ y) (φ u)
  sup : fixV Y ⊔ commV Y = ⊤
  inf : fixV Y ⊓ commV Y = ⊥

namespace PlusCoord

variable {Y : Subgroup (MulAut V)} {n : ℕ} (c : PlusCoord Y n)

@[expose] noncomputable def vec (M : Matrix (Fin 2) (Fin 2) (Fq n)) : V :=
  ((c.φ.symm (ofAdd M) : ↥(commV Y)) : V)

theorem vec_mem (M : Matrix (Fin 2) (Fin 2) (Fq n)) : c.vec M ∈ commV Y := (c.φ.symm _).2

theorem vec_add (M N : Matrix (Fin 2) (Fin 2) (Fq n)) : c.vec (M + N) = c.vec M * c.vec N := by
  simp [vec, ofAdd_add]

theorem vec_zero : c.vec 0 = 1 := by simp [vec]

theorem vec_neg (M : Matrix (Fin 2) (Fin 2) (Fq n)) : c.vec (-M) = (c.vec M)⁻¹ := by
  simp [vec, ofAdd_neg]

theorem vec_sub (M N : Matrix (Fin 2) (Fin 2) (Fq n)) :
    c.vec (M - N) = c.vec M * (c.vec N)⁻¹ := by
  simp [vec, sub_eq_add_neg, ofAdd_add, ofAdd_neg]

theorem vec_injective : Function.Injective c.vec := fun _ _ h =>
  ofAdd.injective (c.φ.symm.injective (Subtype.ext h))

theorem vec_eq_one_iff {M : Matrix (Fin 2) (Fin 2) (Fq n)} : c.vec M = 1 ↔ M = 0 := by
  rw [← c.vec_zero]
  exact c.vec_injective.eq_iff

theorem vec_toAdd (u : ↥(commV Y)) : c.vec (toAdd (c.φ u)) = u := by simp [vec]

theorem exists_vec {u : V} (hu : u ∈ commV Y) : ∃ M, c.vec M = u := ⟨_, c.vec_toAdd ⟨u, hu⟩⟩

theorem φ_vec (M : Matrix (Fin 2) (Fin 2) (Fq n)) (h : c.vec M ∈ commV Y) :
    c.φ ⟨c.vec M, h⟩ = ofAdd M := by
  simp [vec]

theorem apply_vec (y : ↥Y) (M : Matrix (Fin 2) (Fin 2) (Fq n)) :
    (y : MulAut V) (c.vec M) = c.vec (((c.θ y).1 : Matrix (Fin 2) (Fin 2) (Fq n)) * M *
      ((c.θ y).2 : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ) := by
  have hp := c.mapsTo y y.2 _ (c.vec_mem M)
  have h := c.act y (c.φ.symm (ofAdd M)) hp
  rw [MulEquiv.apply_symm_apply] at h
  have h2 : (⟨(y : MulAut V) (c.vec M), hp⟩ : ↥(commV Y)) = c.φ.symm (ofAdd
      (((c.θ y).1 : Matrix (Fin 2) (Fin 2) (Fq n)) * M *
        ((c.θ y).2 : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ)) := by
    rw [MulEquiv.eq_symm_apply]
    exact h
  exact congrArg Subtype.val h2

theorem exists_decomp (v : V) : ∃ w ∈ fixV Y, ∃ M, w * c.vec M = v := by
  have hv : v ∈ fixV Y ⊔ commV Y := c.sup ▸ Subgroup.mem_top v
  obtain ⟨w, hw, u, hu, rfl⟩ := Subgroup.mem_sup.mp hv
  obtain ⟨M, rfl⟩ := c.exists_vec hu
  exact ⟨w, hw, M, rfl⟩

theorem aut_ext {g h : MulAut V} (hW : ∀ w ∈ fixV Y, g w = h w)
    (hU : ∀ M, g (c.vec M) = h (c.vec M)) : g = h := by
  ext v
  obtain ⟨w, hw, M, rfl⟩ := c.exists_decomp v
  rw [map_mul, map_mul, hW w hw, hU M]

@[expose] noncomputable def ι₁ : SLq n →* MulAut V :=
  Y.subtype.comp (c.θ.symm.toMonoidHom.comp (MonoidHom.inl (SLq n) (SLq n)))

@[expose] noncomputable def ι₂ : SLq n →* MulAut V :=
  Y.subtype.comp (c.θ.symm.toMonoidHom.comp (MonoidHom.inr (SLq n) (SLq n)))

theorem ι₁_apply (A : SLq n) : c.ι₁ A = ((c.θ.symm (A, 1) : ↥Y) : MulAut V) := rfl

theorem ι₂_apply (B : SLq n) : c.ι₂ B = ((c.θ.symm (1, B) : ↥Y) : MulAut V) := rfl

theorem ι₁_mem (A : SLq n) : c.ι₁ A ∈ Y := (c.θ.symm (A, 1)).2

theorem ι₂_mem (B : SLq n) : c.ι₂ B ∈ Y := (c.θ.symm (1, B)).2

theorem ι₁_vec (A : SLq n) (M : Matrix (Fin 2) (Fin 2) (Fq n)) :
    c.ι₁ A (c.vec M) = c.vec ((A : Matrix (Fin 2) (Fin 2) (Fq n)) * M) := by
  rw [ι₁_apply, apply_vec]
  simp

theorem ι₂_vec (B : SLq n) (M : Matrix (Fin 2) (Fin 2) (Fq n)) :
    c.ι₂ B (c.vec M) = c.vec (M * (B : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ) := by
  rw [ι₂_apply, apply_vec]
  simp

theorem ι₁_injective : Function.Injective c.ι₁ := fun A B h => by
  have : c.θ.symm (A, 1) = c.θ.symm (B, 1) := Subtype.ext h
  exact congrArg Prod.fst (c.θ.symm.injective this)

theorem ι₂_injective : Function.Injective c.ι₂ := fun A B h => by
  have : c.θ.symm (1, A) = c.θ.symm (1, B) := Subtype.ext h
  exact congrArg Prod.snd (c.θ.symm.injective this)

theorem ι₁_mul_ι₂ (A B : SLq n) : c.ι₁ A * c.ι₂ B = c.ι₂ B * c.ι₁ A := by
  rw [ι₁_apply, ι₂_apply, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
  congr 2
  ext <;> simp

theorem ι₁_mul_ι₂_eq (y : ↥Y) : c.ι₁ (c.θ y).1 * c.ι₂ (c.θ y).2 = y := by
  rw [ι₁_apply, ι₂_apply, ← Subgroup.coe_mul, ← map_mul]
  congr 1
  apply c.θ.injective
  rw [MulEquiv.apply_symm_apply]
  ext <;> simp

@[expose] noncomputable def fac₁ : Subgroup (MulAut V) := c.ι₁.range

@[expose] noncomputable def fac₂ : Subgroup (MulAut V) := c.ι₂.range

theorem fac₁_le : c.fac₁ ≤ Y := by
  rintro _ ⟨A, rfl⟩
  exact c.ι₁_mem A

theorem fac₂_le : c.fac₂ ≤ Y := by
  rintro _ ⟨B, rfl⟩
  exact c.ι₂_mem B

@[expose] noncomputable def swap : PlusCoord Y n where
  θ := c.θ.trans MulEquiv.prodComm
  φ := c.φ.trans (AddEquiv.toMultiplicative (Matrix.transposeAddEquiv (Fin 2) (Fin 2) (Fq n)))
  mapsTo := c.mapsTo
  act := plus_equivariant_swap c.θ c.φ c.act
  sup := c.sup
  inf := c.inf

theorem exists_rmat {g : MulAut V} (hgU : ∀ u ∈ commV Y, g u ∈ commV Y)
    (hg : ∀ A : SLq n, g * c.ι₁ A = c.ι₁ A * g) :
    ∃ γ : Matrix (Fin 2) (Fin 2) (Fq n), ∀ M, g (c.vec M) = c.vec (M * γ) := by
  choose Φ hΦ using fun M => c.exists_vec (hgU _ (c.vec_mem M))
  have hadd : ∀ M N, Φ (M + N) = Φ M + Φ N := fun _ _ => c.vec_injective (by
    rw [hΦ, c.vec_add, map_mul, ← hΦ, ← hΦ, c.vec_add])
  have hequiv : ∀ (s : SLq n) M, Φ ((s : Matrix (Fin 2) (Fin 2) (Fq n)) * M) =
      (s : Matrix (Fin 2) (Fin 2) (Fq n)) * Φ M := fun s M => c.vec_injective (by
    rw [hΦ, ← c.ι₁_vec, ← MulAut.mul_apply, hg, MulAut.mul_apply, ← hΦ, c.ι₁_vec])
  refine ⟨Φ 1, fun M => ?_⟩
  rw [← hΦ, Diag.Nat.schur_mat Φ hadd hequiv M]

end PlusCoord

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
