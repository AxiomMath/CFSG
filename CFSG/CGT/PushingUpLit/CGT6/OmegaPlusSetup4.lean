module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusSetup3
public import CFSG.CGT.PushingUpLit.CGT6.Diag.NatMatrix
public import CFSG.Quasithin.Background.B19Basic

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 Matrix Multiplicative

variable {V : Type} [CommGroup V]

theorem commV_mapsTo_of_comm {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ X, g * x = x * g) {p : V} (hp : p ∈ commV X) : g p ∈ commV X :=
  CFSG.Quasithin.apply_mem_commV_of_forall_commute hg hp

theorem fixV_mapsTo_of_comm {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ X, g * x = x * g) {w : V} (hw : w ∈ fixV X) : g w ∈ fixV X := fun x hx => by
  rw [← MulAut.mul_apply, ← hg x hx, MulAut.mul_apply, hw x hx]

namespace PlusCoord

variable {Y : Subgroup (MulAut V)} {n : ℕ} (c : PlusCoord Y n)

theorem fac₁_sup_fac₂ : c.fac₁ ⊔ c.fac₂ = Y := by
  refine le_antisymm (sup_le c.fac₁_le c.fac₂_le) (fun y hy => ?_)
  have h : y = c.ι₁ (c.θ ⟨y, hy⟩).1 * c.ι₂ (c.θ ⟨y, hy⟩).2 := (c.ι₁_mul_ι₂_eq ⟨y, hy⟩).symm
  rw [h]
  exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

theorem fac₁_inf_fac₂ : c.fac₁ ⊓ c.fac₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨A, rfl⟩, ⟨B, hB⟩⟩
  have h1 : c.θ.symm (1, B) = c.θ.symm (A, 1) := Subtype.ext hB
  have h2 : (1 : SLq n) = A := congrArg Prod.fst (c.θ.symm.injective h1)
  rw [Subgroup.mem_bot, ← h2, map_one]

theorem fac_comm : ∀ d ∈ c.fac₁, ∀ b ∈ c.fac₂, d * b = b * d := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact c.ι₁_mul_ι₂ A B

@[expose] noncomputable def fac₁Equiv : ↥c.fac₁ ≃* SLq n :=
  (MonoidHom.ofInjective c.ι₁_injective).symm

theorem ι₁_fac₁Equiv (d : ↥c.fac₁) : c.ι₁ (c.fac₁Equiv d) = d := by
  have h := congrArg Subtype.val ((MonoidHom.ofInjective c.ι₁_injective).apply_symm_apply d)
  rw [MonoidHom.ofInjective_apply] at h
  exact h

theorem commV_fac₁ : commV c.fac₁ = commV Y := by
  refine le_antisymm (B19.commV_mono c.fac₁_le) (fun u hu => ?_)
  obtain ⟨M, rfl⟩ := c.exists_vec hu
  let T : AddSubgroup (Matrix (Fin 2) (Fin 2) (Fq n)) :=
    { carrier := {X | c.vec X ∈ commV c.fac₁}
      zero_mem' := by
        show c.vec 0 ∈ commV c.fac₁
        rw [c.vec_zero]
        exact Subgroup.one_mem _
      add_mem' := fun {a b} ha hb => by
        show c.vec (a + b) ∈ commV c.fac₁
        rw [c.vec_add]
        exact Subgroup.mul_mem _ ha hb
      neg_mem' := fun {a} ha => by
        show c.vec (-a) ∈ commV c.fac₁
        rw [c.vec_neg]
        exact Subgroup.inv_mem _ ha }
  have hT : ∀ (s : SLq n) (N : Matrix (Fin 2) (Fin 2) (Fq n)),
      (s : Matrix (Fin 2) (Fin 2) (Fq n)) * N - N ∈ T := fun s N => by
    show c.vec (_ - N) ∈ commV c.fac₁
    rw [c.vec_sub, ← c.ι₁_vec]
    exact Subgroup.subset_closure ⟨c.ι₁ s, ⟨s, rfl⟩, c.vec N, rfl⟩
  exact Diag.Nat.mem_of_forall_sub T hT M

theorem fixV_fac₁ : fixV c.fac₁ = fixV Y := by
  refine le_antisymm (fun v hv => ?_) (fun v hv y hy => hv y (c.fac₁_le hy))
  obtain ⟨w, hw, M, rfl⟩ := c.exists_decomp v
  have hM : M = 0 := by
    apply eq_zero_of_forall_sl_mul
    intro A
    apply c.vec_injective
    have h1 := hv (c.ι₁ A) ⟨A, rfl⟩
    rw [map_mul, hw _ (c.ι₁_mem A), c.ι₁_vec] at h1
    exact mul_left_cancel h1
  rw [hM, c.vec_zero, mul_one]
  exact hw

include c in
theorem eq_one_of_forall_commV {y : MulAut V} (hy : y ∈ Y) (h : ∀ u ∈ commV Y, y u = u) :
    y = 1 :=
  c.aut_ext (fun w hw => by rw [hw _ hy, MulAut.one_apply])
    (fun M => by rw [h _ (c.vec_mem M), MulAut.one_apply])

theorem pow_vec_of_smul {g : MulAut V} {l : Fq n} (hg : ∀ M, g (c.vec M) = c.vec (l • M))
    (m : ℕ) (M : Matrix (Fin 2) (Fin 2) (Fq n)) : (g ^ m) (c.vec M) = c.vec (l ^ m • M) := by
  induction m generalizing M with
  | zero => simp
  | succ m ih => rw [pow_succ, MulAut.mul_apply, hg, ih, smul_smul, ← pow_succ]

include c in
theorem trivial_on_commV {z : MulAut V} (hz : z ∈ Subgroup.centralizer (Y : Set (MulAut V)))
    {k : ℕ} (hk : z ^ 2 ^ k = 1) : ∀ u ∈ commV Y, z u = u := by
  have hcomm : ∀ y ∈ Y, z * y = y * z := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hz y hy).symm
  obtain ⟨γ, hγ⟩ := c.exists_rmat (fun u hu => commV_mapsTo_of_comm hcomm hu)
    (fun A => hcomm _ (c.ι₁_mem A))
  have hγc : ∀ s : SLq n, (s : Matrix (Fin 2) (Fin 2) (Fq n)) * γ =
      γ * (s : Matrix (Fin 2) (Fin 2) (Fq n)) := by
    intro s
    have h1 : z (c.ι₂ s.transpose (c.vec 1)) = c.ι₂ s.transpose (z (c.vec 1)) := by
      rw [← MulAut.mul_apply, hcomm _ (c.ι₂_mem _), MulAut.mul_apply]
    rw [c.ι₂_vec, hγ, hγ, c.ι₂_vec] at h1
    simpa [SpecialLinearGroup.coe_transpose] using c.vec_injective h1
  obtain ⟨l, hl⟩ : ∃ l, γ 0 0 = l := ⟨_, rfl⟩
  have hscal := eq_smul_one_of_forall_sl_comm γ hγc
  rw [hl] at hscal
  have hz' : ∀ M, z (c.vec M) = c.vec (l • M) := fun M => by
    rw [hγ, hscal, Matrix.mul_smul, Matrix.mul_one]
  have h1 := c.pow_vec_of_smul hz' (2 ^ k) 1
  rw [hk, MulAut.one_apply] at h1
  have h2 := congrFun (congrFun (c.vec_injective h1) 0) 0
  have hl2 : l ^ 2 ^ k = 1 := by simpa using h2.symm
  have hl1 : l = 1 := by
    have h3 : (l - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, hl2, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).mp h3)
  intro u hu
  obtain ⟨M, rfl⟩ := c.exists_vec hu
  rw [hz', hl1, one_smul]

theorem exists_decomp_centralizer {G : Subgroup (MulAut V)} (hYG : Y ≤ G) {x : MulAut V}
    (hx : x ∈ G ⊓ Subgroup.centralizer (c.fac₁ : Set (MulAut V))) :
    ∃ β ∈ c.fac₂, ∃ z ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), x = β * z := by
  obtain ⟨hxG, hxD⟩ := Subgroup.mem_inf.mp hx
  have hcomm : ∀ d ∈ c.fac₁, x * d = d * x := fun d hd =>
    (Subgroup.mem_centralizer_iff.mp hxD d hd).symm
  have hcomm' : ∀ d ∈ c.fac₁, x⁻¹ * d = d * x⁻¹ := fun d hd =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hxD) d hd).symm
  have hU : ∀ u ∈ commV Y, x u ∈ commV Y := fun u hu => by
    rw [← c.commV_fac₁] at hu ⊢
    exact commV_mapsTo_of_comm hcomm hu
  have hU' : ∀ u ∈ commV Y, x⁻¹ u ∈ commV Y := fun u hu => by
    rw [← c.commV_fac₁] at hu ⊢
    exact commV_mapsTo_of_comm hcomm' hu
  have hW : ∀ w ∈ fixV Y, x w ∈ fixV Y := fun w hw => by
    rw [← c.fixV_fac₁] at hw ⊢
    exact fixV_mapsTo_of_comm hcomm hw
  obtain ⟨γ, hγ⟩ := c.exists_rmat hU (fun A => hcomm _ ⟨A, rfl⟩)
  obtain ⟨γ', hγ'⟩ := c.exists_rmat hU' (fun A => hcomm' _ ⟨A, rfl⟩)
  have hinv : γ' * γ = 1 := by
    have h1 : x (x⁻¹ (c.vec 1)) = c.vec 1 := by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    rw [hγ', hγ] at h1
    simpa using c.vec_injective h1
  have hdet : γ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hinv
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h1
    exact zero_ne_one h1
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq (Fq n) 2) γ.det
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hdet (by rw [hl, mul_zero])
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀, l⁻¹ • γ = γ₀ := ⟨_, rfl⟩
  have hdet₀ : γ₀.det = 1 := by
    rw [← hγ₀, Matrix.det_smul, hl, Fintype.card_fin]
    field_simp
  have hγl : γ = l • γ₀ := by rw [← hγ₀, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  let B₀ : SLq n := ⟨γ₀ᵀ, by rw [Matrix.det_transpose, hdet₀]⟩
  have hzU : ∀ M, ((c.ι₂ B₀)⁻¹ * x) (c.vec M) = c.vec (l • M) := fun M => by
    apply (c.ι₂ B₀).injective
    rw [← MulAut.mul_apply, mul_inv_cancel_left, hγ, c.ι₂_vec]
    congr 1
    show M * γ = l • M * (γ₀ᵀ)ᵀ
    rw [Matrix.transpose_transpose, hγl, Matrix.mul_smul, Matrix.smul_mul]
  have hzW : ∀ w ∈ fixV Y, ((c.ι₂ B₀)⁻¹ * x) w = x w := fun w hw => by
    rw [MulAut.mul_apply]
    exact hW w hw _ (Subgroup.inv_mem _ (c.ι₂_mem B₀))
  refine ⟨c.ι₂ B₀, ⟨B₀, rfl⟩, (c.ι₂ B₀)⁻¹ * x, ?_, by group⟩
  refine Subgroup.mem_inf.mpr
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hYG (c.ι₂_mem B₀))) hxG, ?_⟩
  generalize (c.ι₂ B₀)⁻¹ * x = z at hzU hzW
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : ∀ M, y (c.vec M) = c.vec (((c.θ ⟨y, hy⟩).1 : Matrix (Fin 2) (Fin 2) (Fq n)) * M *
      ((c.θ ⟨y, hy⟩).2 : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ) := c.apply_vec ⟨y, hy⟩
  apply c.aut_ext
  · intro w hw
    rw [MulAut.mul_apply, MulAut.mul_apply, hw _ hy, hzW w hw, hW w hw _ hy]
  · intro M
    rw [MulAut.mul_apply, MulAut.mul_apply, hzU, hy', hy', hzU, Matrix.mul_smul,
      Matrix.smul_mul]

end PlusCoord

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
