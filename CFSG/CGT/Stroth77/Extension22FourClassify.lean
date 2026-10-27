module

public import CFSG.CGT.Stroth77.Extension22FourBasis

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] {B C : Subgroup S} {m : ℕ}

@[expose] noncomputable def basisElemsFour (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (e f : C) : Fin 3 → C :=
  ![⟨D.c, hBC D.c.2⟩, e, f]

@[simp]
theorem basisElemsFour_zero (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (e f : C) :
    basisElemsFour D hBC e f 0 = ⟨D.c, hBC D.c.2⟩ := rfl

@[simp]
theorem basisElemsFour_one (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (e f : C) :
    basisElemsFour D hBC e f 1 = e := rfl

@[simp]
theorem basisElemsFour_two (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (e f : C) :
    basisElemsFour D hBC e f 2 = f := rfl

@[expose] noncomputable def TorusBasisEquivFour.symm
    {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}
    (E : TorusBasisEquivFour D hBC e f) : Additive C ≃+ Torus (Type200.k m) :=
  E.E.symm

theorem TorusBasisEquivFour.symm_gen_zero
    {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}
    (E : TorusBasisEquivFour D hBC e f) :
    E.symm (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = gen (Type200.k m) 0 := by
  show E.E.symm (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = gen (Type200.k m) 0
  rw [← E.E_gen0]
  exact E.E.symm_apply_apply _

theorem TorusBasisEquivFour.symm_gen_one
    {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}
    (E : TorusBasisEquivFour D hBC e f) :
    E.symm (Additive.ofMul e) = gen (Type200.k m) 1 := by
  show E.E.symm (Additive.ofMul e) = gen (Type200.k m) 1
  rw [← E.E_gen1]
  exact E.E.symm_apply_apply _

theorem TorusBasisEquivFour.symm_gen_two
    {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}
    (E : TorusBasisEquivFour D hBC e f) :
    E.symm (Additive.ofMul f) = gen (Type200.k m) 2 := by
  show E.E.symm (Additive.ofMul f) = gen (Type200.k m) 2
  rw [← E.E_gen2]
  exact E.E.symm_apply_apply _

structure HasGeneratorImagesFour (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C) (e f : C)
    {k : Fin 3 → ℕ} (E : Additive C ≃+ Torus k)
    (φuv φt φu φρ : Torus k →+ Torus k) : Prop where
  uv : ∀ j : Fin 3,
    E (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElemsFour D hBC e f j))) =
      φuv (gen k j)
  t : ∀ j : Fin 3,
    E (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElemsFour D hBC e f j))) =
      φt (gen k j)
  u : ∀ j : Fin 3,
    E (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElemsFour D hBC e f j))) =
      φu (gen k j)
  ρ : ∀ j : Fin 3,
    E (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElemsFour D hBC e f j))) =
      φρ (gen k j)

@[expose] def Type200Images (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C) (e f : C)
    (E : TorusBasisEquivFour D hBC e f) : Prop :=
  HasGeneratorImagesFour D hBC hL e f (k := Type200.k m) E.symm
    (Type200.action m).φuv (Type200.action m).φt (Type200.action m).φu
    (Type200.action m).φρ

@[expose] def Type201Images (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C) (e f : C)
    (E : TorusBasisEquivFour D hBC e f) : Prop :=
  HasGeneratorImagesFour D hBC hL e f (k := Type201.k m)
    (show Additive C ≃+ Torus (Type201.k m) from E.symm)
    (Type201.action m).φuv (Type201.action m).φt (Type201.action m).φu
    (Type201.action m).φρ

theorem hasStrothType_t200_of_generator_images [Finite S]
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e f : C}
    (E : TorusBasisEquivFour D hBC e f)
    (huv : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElemsFour D hBC e f j))) =
        (Type200.action m).φuv (gen (Type200.k m) j))
    (ht : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElemsFour D hBC e f j))) =
        (Type200.action m).φt (gen (Type200.k m) j))
    (hu : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElemsFour D hBC e f j))) =
        (Type200.action m).φu (gen (Type200.k m) j))
    (hρ : ∀ j : Fin 3,
      E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElemsFour D hBC e f j))) =
        (Type200.action m).φρ (gen (Type200.k m) j)) :
    HasStrothType C (StrothTypeIndex.t200 m) := by
  let xc : C := ⟨D.c, hBC D.c.2⟩
  let xe : C := e
  let xf : C := f
  have hxc : E.symm (Additive.ofMul xc) = gen (Type200.k m) 0 := by
    simpa [xc] using TorusBasisEquivFour.symm_gen_zero (E := E)
  have hxe : E.symm (Additive.ofMul xe) = gen (Type200.k m) 1 := by
    simpa [xe] using TorusBasisEquivFour.symm_gen_one (E := E)
  have hxf : E.symm (Additive.ofMul xf) = gen (Type200.k m) 2 := by
    simpa [xf] using TorusBasisEquivFour.symm_gen_two (E := E)
  have huv0 : E.symm (Additive.ofMul (conjBy (hL D.uv_mem_L) xc)) =
      (Type200.action m).φuv (gen (Type200.k m) 0) := by
    simpa [basisElemsFour, xc] using huv 0
  have huv1 : E.symm (Additive.ofMul (conjBy (hL D.uv_mem_L) xe)) =
      (Type200.action m).φuv (gen (Type200.k m) 1) := by
    simpa [basisElemsFour, xe] using huv 1
  have huv2 : E.symm (Additive.ofMul (conjBy (hL D.uv_mem_L) xf)) =
      (Type200.action m).φuv (gen (Type200.k m) 2) := by
    simpa [basisElemsFour, xf] using huv 2
  have ht0 : E.symm (Additive.ofMul (conjBy (hL D.t_mem_L) xc)) =
      (Type200.action m).φt (gen (Type200.k m) 0) := by
    simpa [basisElemsFour, xc] using ht 0
  have ht1 : E.symm (Additive.ofMul (conjBy (hL D.t_mem_L) xe)) =
      (Type200.action m).φt (gen (Type200.k m) 1) := by
    simpa [basisElemsFour, xe] using ht 1
  have ht2 : E.symm (Additive.ofMul (conjBy (hL D.t_mem_L) xf)) =
      (Type200.action m).φt (gen (Type200.k m) 2) := by
    simpa [basisElemsFour, xf] using ht 2
  have hu0 : E.symm (Additive.ofMul (conjBy (hL D.u_mem_L) xc)) =
      (Type200.action m).φu (gen (Type200.k m) 0) := by
    simpa [basisElemsFour, xc] using hu 0
  have hu1 : E.symm (Additive.ofMul (conjBy (hL D.u_mem_L) xe)) =
      (Type200.action m).φu (gen (Type200.k m) 1) := by
    simpa [basisElemsFour, xe] using hu 1
  have hu2 : E.symm (Additive.ofMul (conjBy (hL D.u_mem_L) xf)) =
      (Type200.action m).φu (gen (Type200.k m) 2) := by
    simpa [basisElemsFour, xf] using hu 2
  have hρ0 : E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) xc)) =
      (Type200.action m).φρ (gen (Type200.k m) 0) := by
    simpa [basisElemsFour, xc] using hρ 0
  have hρ1 : E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) xe)) =
      (Type200.action m).φρ (gen (Type200.k m) 1) := by
    simpa [basisElemsFour, xe] using hρ 1
  have hρ2 : E.symm (Additive.ofMul (conjBy (hL D.ρ_mem_L) xf)) =
      (Type200.action m).φρ (gen (Type200.k m) 2) := by
    simpa [basisElemsFour, xf] using hρ 2
  refine ⟨{
    e := E.symm
    uv := D.uv
    t := D.t
    u := D.u
    ρ := D.ρ
    uv_sq := D.uv_sq
    t_sq := D.t_sq
    uv_comm_t := D.uv_comm_t
    rho_cube := D.rho_cube
    u_sq := D.u_sq
    u_rho := D.u_rho
    uv_rho := D.uv_rho
    t_rho := D.t_rho
    uv_comm_u := D.uv_comm_u
    t_u := D.t_u
    uv_mem := hL D.uv_mem_L
    t_mem := hL D.t_mem_L
    u_mem := hL D.u_mem_L
    ρ_mem := hL D.ρ_mem_L
    uv_conj := conj_eq_of_generator_images (hL D.uv_mem_L) E.symm
      (Type200.action m).φuv hxc hxe hxf huv0 huv1 huv2
    t_conj := conj_eq_of_generator_images (hL D.t_mem_L) E.symm
      (Type200.action m).φt hxc hxe hxf ht0 ht1 ht2
    u_conj := conj_eq_of_generator_images (hL D.u_mem_L) E.symm
      (Type200.action m).φu hxc hxe hxf hu0 hu1 hu2
    ρ_conj := conj_eq_of_generator_images (hL D.ρ_mem_L) E.symm
      (Type200.action m).φρ hxc hxe hxf hρ0 hρ1 hρ2 }⟩

theorem hasStrothType_t201_of_generator_images [Finite S]
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e f : C}
    (E : TorusBasisEquivFour D hBC e f)
    (huv : ∀ j : Fin 3,
      (show Additive C ≃+ Torus (Type201.k m) from E.symm)
        (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElemsFour D hBC e f j))) =
        (Type201.action m).φuv (gen (Type201.k m) j))
    (ht : ∀ j : Fin 3,
      (show Additive C ≃+ Torus (Type201.k m) from E.symm)
        (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElemsFour D hBC e f j))) =
        (Type201.action m).φt (gen (Type201.k m) j))
    (hu : ∀ j : Fin 3,
      (show Additive C ≃+ Torus (Type201.k m) from E.symm)
        (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElemsFour D hBC e f j))) =
        (Type201.action m).φu (gen (Type201.k m) j))
    (hρ : ∀ j : Fin 3,
      (show Additive C ≃+ Torus (Type201.k m) from E.symm)
        (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElemsFour D hBC e f j))) =
        (Type201.action m).φρ (gen (Type201.k m) j)) :
    HasStrothType C (StrothTypeIndex.t201 m) := by
  let xc : C := ⟨D.c, hBC D.c.2⟩
  let xe : C := e
  let xf : C := f
  let E' : Additive C ≃+ Torus (Type201.k m) := E.symm
  have hxc : E' (Additive.ofMul xc) = gen (Type201.k m) 0 := by
    change E.symm (Additive.ofMul xc) = gen (Type200.k m) 0
    simpa [xc] using TorusBasisEquivFour.symm_gen_zero (E := E)
  have hxe : E' (Additive.ofMul xe) = gen (Type201.k m) 1 := by
    change E.symm (Additive.ofMul xe) = gen (Type200.k m) 1
    simpa [xe] using TorusBasisEquivFour.symm_gen_one (E := E)
  have hxf : E' (Additive.ofMul xf) = gen (Type201.k m) 2 := by
    change E.symm (Additive.ofMul xf) = gen (Type200.k m) 2
    simpa [xf] using TorusBasisEquivFour.symm_gen_two (E := E)
  have huv0 : E' (Additive.ofMul (conjBy (hL D.uv_mem_L) xc)) =
      (Type201.action m).φuv (gen (Type201.k m) 0) := by
    simpa [E', basisElemsFour, xc] using huv 0
  have huv1 : E' (Additive.ofMul (conjBy (hL D.uv_mem_L) xe)) =
      (Type201.action m).φuv (gen (Type201.k m) 1) := by
    simpa [E', basisElemsFour, xe] using huv 1
  have huv2 : E' (Additive.ofMul (conjBy (hL D.uv_mem_L) xf)) =
      (Type201.action m).φuv (gen (Type201.k m) 2) := by
    simpa [E', basisElemsFour, xf] using huv 2
  have ht0 : E' (Additive.ofMul (conjBy (hL D.t_mem_L) xc)) =
      (Type201.action m).φt (gen (Type201.k m) 0) := by
    simpa [E', basisElemsFour, xc] using ht 0
  have ht1 : E' (Additive.ofMul (conjBy (hL D.t_mem_L) xe)) =
      (Type201.action m).φt (gen (Type201.k m) 1) := by
    simpa [E', basisElemsFour, xe] using ht 1
  have ht2 : E' (Additive.ofMul (conjBy (hL D.t_mem_L) xf)) =
      (Type201.action m).φt (gen (Type201.k m) 2) := by
    simpa [E', basisElemsFour, xf] using ht 2
  have hu0 : E' (Additive.ofMul (conjBy (hL D.u_mem_L) xc)) =
      (Type201.action m).φu (gen (Type201.k m) 0) := by
    simpa [E', basisElemsFour, xc] using hu 0
  have hu1 : E' (Additive.ofMul (conjBy (hL D.u_mem_L) xe)) =
      (Type201.action m).φu (gen (Type201.k m) 1) := by
    simpa [E', basisElemsFour, xe] using hu 1
  have hu2 : E' (Additive.ofMul (conjBy (hL D.u_mem_L) xf)) =
      (Type201.action m).φu (gen (Type201.k m) 2) := by
    simpa [E', basisElemsFour, xf] using hu 2
  have hρ0 : E' (Additive.ofMul (conjBy (hL D.ρ_mem_L) xc)) =
      (Type201.action m).φρ (gen (Type201.k m) 0) := by
    simpa [E', basisElemsFour, xc] using hρ 0
  have hρ1 : E' (Additive.ofMul (conjBy (hL D.ρ_mem_L) xe)) =
      (Type201.action m).φρ (gen (Type201.k m) 1) := by
    simpa [E', basisElemsFour, xe] using hρ 1
  have hρ2 : E' (Additive.ofMul (conjBy (hL D.ρ_mem_L) xf)) =
      (Type201.action m).φρ (gen (Type201.k m) 2) := by
    simpa [E', basisElemsFour, xf] using hρ 2
  refine ⟨{
    e := E'
    uv := D.uv
    t := D.t
    u := D.u
    ρ := D.ρ
    uv_sq := D.uv_sq
    t_sq := D.t_sq
    uv_comm_t := D.uv_comm_t
    rho_cube := D.rho_cube
    u_sq := D.u_sq
    u_rho := D.u_rho
    uv_rho := D.uv_rho
    t_rho := D.t_rho
    uv_comm_u := D.uv_comm_u
    t_u := D.t_u
    uv_mem := hL D.uv_mem_L
    t_mem := hL D.t_mem_L
    u_mem := hL D.u_mem_L
    ρ_mem := hL D.ρ_mem_L
    uv_conj := conj_eq_of_generator_images (hL D.uv_mem_L) E'
      (Type201.action m).φuv hxc hxe hxf huv0 huv1 huv2
    t_conj := conj_eq_of_generator_images (hL D.t_mem_L) E'
      (Type201.action m).φt hxc hxe hxf ht0 ht1 ht2
    u_conj := conj_eq_of_generator_images (hL D.u_mem_L) E'
      (Type201.action m).φu hxc hxe hxf hu0 hu1 hu2
    ρ_conj := conj_eq_of_generator_images (hL D.ρ_mem_L) E'
      (Type201.action m).φρ hxc hxe hxf hρ0 hρ1 hρ2 }⟩

theorem hasStrothType_t200_of_images [Finite S]
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e f : C}
    (E : TorusBasisEquivFour D hBC e f)
    (h : Type200Images D hBC hL e f E) :
    HasStrothType C (StrothTypeIndex.t200 m) :=
  hasStrothType_t200_of_generator_images D hBC hL E h.uv h.t h.u h.ρ

theorem hasStrothType_t201_of_images [Finite S]
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e f : C}
    (E : TorusBasisEquivFour D hBC e f)
    (h : Type201Images D hBC hL e f E) :
    HasStrothType C (StrothTypeIndex.t201 m) :=
  hasStrothType_t201_of_generator_images D hBC hL E h.uv h.t h.u h.ρ

@[expose] def HasType200Or201AdjustedBasis
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C) (e f : C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (E : TorusBasisEquivFour D hBC e f) : Prop :=
  ∃ z w : C, z * z = 1 ∧ w * w = 1 ∧
    ∃ E' : TorusBasisEquivFour D hBC (e * z) (f * w),
      Type200Images D hBC hL (e * z) (f * w) E' ∨
        Type201Images D hBC hL (e * z) (f * w) E'

theorem hasStrothType_t200_or_t201_of_torusBasis [Finite S]
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e f : C}
    (E : TorusBasisEquivFour D hBC e f)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hclass : HasType200Or201AdjustedBasis D hBC hL e f he hf E) :
    HasStrothType C (StrothTypeIndex.t200 m) ∨
      HasStrothType C (StrothTypeIndex.t201 m) := by
  obtain ⟨z, w, -, -, E', hE'⟩ := hclass
  rcases hE' with h200 | h201
  · exact Or.inl (hasStrothType_t200_of_images D hBC hL E' h200)
  · exact Or.inr (hasStrothType_t201_of_images D hBC hL E' h201)

theorem hasStrothType_t200_or_t201_of_images [Finite S]
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hBC : B ≤ C)
    (hL : D.L ≤ Subgroup.normalizer C) {e f : C}
    (E : TorusBasisEquivFour D hBC e f)
    (h : Type200Images D hBC hL e f E ∨ Type201Images D hBC hL e f E) :
    HasStrothType C (StrothTypeIndex.t200 m) ∨
      HasStrothType C (StrothTypeIndex.t201 m) := by
  rcases h with h200 | h201
  · exact Or.inl (hasStrothType_t200_of_images D hBC hL E h200)
  · exact Or.inr (hasStrothType_t201_of_images D hBC hL E h201)

theorem sq_mem_B_of_torusBasisFour
    [Finite S] [hN : (B.subgroupOf C).Normal]
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) {e f : C} :
    ((e : S) * (e : S)) ∈ B ∧ ((f : S) * (f : S)) ∈ B :=
  ⟨sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc e,
    sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc f⟩

end CFSG.CGT.Stroth77
