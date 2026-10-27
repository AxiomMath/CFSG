module

public import CFSG.CGT.Stroth77.Extension22FourClassify3
public import CFSG.CGT.Stroth77.Extension23

public section

namespace CFSG.CGT.Stroth77

open scoped IsMulCommutative

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}

theorem isMulCommutative_of_torusBasisEquivFour (E : TorusBasisEquivFour D hBC e f) :
    IsMulCommutative C :=
  IsMulCommutative.of_comm fun x y => by
    apply E.E.symm.injective
    change E.E.symm (Additive.ofMul (x * y)) = E.E.symm (Additive.ofMul (y * x))
    rw [ofMul_mul, ofMul_mul, map_add, map_add, add_comm]

theorem map_two_torsion (φ : Torus (Type200.k m) →+ Torus (Type200.k m))
    {x : Torus (Type200.k m)} (hx : 2 • x = 0) : 2 • φ x = 0 := by
  rw [← map_nsmul, hx, map_zero]

theorem cocycleUV_eq_zero_of_two_torsion
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    {x : Torus (Type200.k m)} (hx : 2 • x = 0) :
    cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x = 0 := by
  refine hom_two_torsion_eq_zero (δ := cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL)
    (cocycleUV_gen0 he hf E hL) ?_ ?_ hx
  · simpa [two_zsmul, two_nsmul] using cocycleUV_two_gen1 he hf E hL
  · simpa [two_zsmul, two_nsmul] using cocycleUV_two_gen2 he hf E hL

theorem cocycleT_eq_zero_of_two_torsion
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    {x : Torus (Type200.k m)} (hx : 2 • x = 0) :
    cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL x = 0 := by
  refine hom_two_torsion_eq_zero (δ := cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL)
    (cocycleT_gen0 he hf E hL) ?_ ?_ hx
  · simpa [two_zsmul, two_nsmul] using cocycleT_two_gen1 he hf E hL
  · simpa [two_zsmul, two_nsmul] using cocycleT_two_gen2 he hf E hL

theorem cocycleU_eq_zero_of_two_torsion
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    {x : Torus (Type200.k m)} (hx : 2 • x = 0) :
    cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL x = 0 := by
  refine hom_two_torsion_eq_zero (δ := cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL)
    (cocycleU_gen0 he hf E hL) ?_ ?_ hx
  · simpa [two_zsmul, two_nsmul] using cocycleU_two_gen1 he hf E hL
  · simpa [two_zsmul, two_nsmul] using cocycleU_two_gen2 he hf E hL

theorem cocycleR_eq_zero_of_two_torsion
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    {x : Torus (Type200.k m)} (hx : 2 • x = 0) :
    cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL x = 0 := by
  refine hom_two_torsion_eq_zero (δ := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL)
    (cocycleR_gen0 he hf E hL) ?_ ?_ hx
  · simpa [two_zsmul, two_nsmul] using cocycleR_two_gen1 he hf E hL
  · simpa [two_zsmul, two_nsmul] using cocycleR_two_gen2 he hf E hL

@[expose] noncomputable def basisChange
    (E : TorusBasisEquivFour D hBC e f)
    (P Q : Torus (Type200.k m)) (h2P : 2 • P = 0) (h2Q : 2 • Q = 0) :
    TorusBasisEquivFour D hBC (e * Additive.toMul (E.E P))
      (f * Additive.toMul (E.E Q)) where
  E := (psiBasis h2P h2Q).trans E.E
  E_gen0 := by
    rw [AddEquiv.trans_apply]
    change E.E (psiBasis h2P h2Q (gen (Type200.k m) 0)) = _
    rw [psiBasis_gen0]
    exact E.E_gen0
  E_gen1 := by
    rw [AddEquiv.trans_apply]
    change E.E (psiBasis h2P h2Q (gen (Type200.k m) 1)) =
      Additive.ofMul (e * Additive.toMul (E.E P))
    rw [psiBasis_gen1]
    change E.E (gen (Type200.k m) 1 + P) = Additive.ofMul (e * Additive.toMul (E.E P))
    rw [map_add, E.E_gen1, ofMul_mul, ofMul_toMul]
  E_gen2 := by
    rw [AddEquiv.trans_apply]
    change E.E (psiBasis h2P h2Q (gen (Type200.k m) 2)) =
      Additive.ofMul (f * Additive.toMul (E.E Q))
    rw [psiBasis_gen2]
    change E.E (gen (Type200.k m) 2 + Q) = Additive.ofMul (f * Additive.toMul (E.E Q))
    rw [map_add, E.E_gen2, ofMul_mul, ofMul_toMul]

theorem conjTorusFour_basisChange
    (E : TorusBasisEquivFour D hBC e f)
    (P Q : Torus (Type200.k m)) (h2P : 2 • P = 0) (h2Q : 2 • Q = 0)
    {g : S} (hg : g ∈ Subgroup.normalizer C) (x : Torus (Type200.k m)) :
    conjTorusFour D hBC (basisChange E P Q h2P h2Q) hg x =
      psiBasis h2P h2Q (conjTorusFour D hBC E hg (psiBasis h2P h2Q x)) := by
  have hψsymm : (psiBasis h2P h2Q).symm = psiBasis h2P h2Q := by
    refine AddEquiv.ext fun y => ?_
    have hy : psiBasis h2P h2Q (psiBasis h2P h2Q y) = y :=
      psiBasis_apply_self h2P h2Q y
    calc (psiBasis h2P h2Q).symm y
        = (psiBasis h2P h2Q).symm (psiBasis h2P h2Q (psiBasis h2P h2Q y)) := by rw [hy]
      _ = psiBasis h2P h2Q y := AddEquiv.symm_apply_apply _ _
  have hEsymm : (basisChange E P Q h2P h2Q).E.symm =
      E.E.symm.trans (psiBasis h2P h2Q) := by
    rw [show (basisChange E P Q h2P h2Q).E =
      (psiBasis h2P h2Q).trans E.E from rfl]
    rw [show ((psiBasis h2P h2Q).trans E.E).symm =
      E.E.symm.trans (psiBasis h2P h2Q).symm from rfl, hψsymm]
  rw [conjTorusFour_apply, conjTorusFour_apply, hEsymm]
  rw [AddEquiv.trans_apply]
  change psiBasis h2P h2Q
      (E.E.symm (Additive.ofMul (conjBy hg (Additive.toMul (E.E (psiBasis h2P h2Q x))))) ) =
    psiBasis h2P h2Q
      (E.E.symm (Additive.ofMul (conjBy hg (Additive.toMul (E.E (psiBasis h2P h2Q x))))))
  rfl

theorem cocycle_basisChange_gen1
    (E : TorusBasisEquivFour D hBC e f)
    (P Q : Torus (Type200.k m)) (h2P : 2 • P = 0) (h2Q : 2 • Q = 0)
    (φ : Torus (Type200.k m) →+ Torus (Type200.k m)) {g : S}
    (hgC : g ∈ Subgroup.normalizer C)
    (hδ : ∀ y : Torus (Type200.k m), 2 • y = 0 → cocycle φ E hgC y = 0)
    (h2p : 2 • cocycle φ E hgC (gen (Type200.k m) 1) = 0) :
    cocycle φ (basisChange E P Q h2P h2Q) hgC (gen (Type200.k m) 1) =
      cocycle φ E hgC (gen (Type200.k m) 1) + φ P +
        piBasis h2P h2Q (φ (gen (Type200.k m) 1)) := by
  have hδP : cocycle φ E hgC P = 0 := hδ P h2P
  have hφP : piBasis h2P h2Q (φ P) = 0 :=
    piBasis_two_torsion_eq_zero h2P h2Q (map_two_torsion φ h2P)
  have hπδ : piBasis h2P h2Q (cocycle φ E hgC (gen (Type200.k m) 1)) = 0 :=
    piBasis_two_torsion_eq_zero h2P h2Q h2p
  rw [cocycle_apply, conjTorusFour_basisChange, psiBasis_gen1,
    action_eq_printed_add_cocycle E hgC φ]
  simp only [map_add, psiBasis_apply, hδP, hφP, hπδ, map_zero, add_zero, zero_add]
  abel

theorem cocycle_basisChange_gen2
    (E : TorusBasisEquivFour D hBC e f)
    (P Q : Torus (Type200.k m)) (h2P : 2 • P = 0) (h2Q : 2 • Q = 0)
    (φ : Torus (Type200.k m) →+ Torus (Type200.k m)) {g : S}
    (hgC : g ∈ Subgroup.normalizer C)
    (hδ : ∀ y : Torus (Type200.k m), 2 • y = 0 → cocycle φ E hgC y = 0)
    (h2q : 2 • cocycle φ E hgC (gen (Type200.k m) 2) = 0) :
    cocycle φ (basisChange E P Q h2P h2Q) hgC (gen (Type200.k m) 2) =
      cocycle φ E hgC (gen (Type200.k m) 2) + φ Q +
        piBasis h2P h2Q (φ (gen (Type200.k m) 2)) := by
  have hδQ : cocycle φ E hgC Q = 0 := hδ Q h2Q
  have hφQ : piBasis h2P h2Q (φ Q) = 0 :=
    piBasis_two_torsion_eq_zero h2P h2Q (map_two_torsion φ h2Q)
  have hπδ : piBasis h2P h2Q (cocycle φ E hgC (gen (Type200.k m) 2)) = 0 :=
    piBasis_two_torsion_eq_zero h2P h2Q h2q
  rw [cocycle_apply, conjTorusFour_basisChange, psiBasis_gen2,
    action_eq_printed_add_cocycle E hgC φ]
  simp only [map_add, psiBasis_apply, hδQ, hφQ, hπδ, map_zero, add_zero, zero_add]
  abel

theorem exists_u_normalized_all
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    ∃ z w : C, z * z = 1 ∧ w * w = 1 ∧
      (e * z) * (e * z) = ⟨D.a, hBC D.a.2⟩ ∧
      (f * w) * (f * w) = ⟨D.b, hBC D.b.2⟩ ∧
      ∃ E1 : TorusBasisEquivFour D hBC (e * z) (f * w),
        cocycleU (D := D) (hBC := hBC) (e := e * z) (f := f * w) E1 hL = 0 := by
  classical
  let p : Torus (Type200.k m) := cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 1)
  have h2p : 2 • p = 0 := by
    simpa [p, two_zsmul, two_nsmul] using cocycleU_two_gen1 he hf E hL
  have h2q : 2 • cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleU_two_gen2 he hf E hL
  let z : C := Additive.toMul (E.E 0)
  let w : C := Additive.toMul (E.E p)
  have hz : z * z = 1 := by simp [z]
  have hw : w * w = 1 := by
    apply Additive.ofMul.injective
    change Additive.ofMul (w * w) = Additive.ofMul (1 : C)
    rw [ofMul_mul, ofMul_one]
    have h : (2 : ℕ) • (E.E p) = 0 := by
      rw [← map_nsmul]
      rw [h2p, map_zero]
    rw [show E.E p = Additive.ofMul w from rfl] at h
    rwa [two_nsmul] at h
  have he1 : (e * z) * (e * z) = ⟨D.a, hBC D.a.2⟩ := by
    haveI : IsMulCommutative C := isMulCommutative_of_torusBasisEquivFour E
    rw [mul_mul_mul_comm, he, hz, mul_one]
  have hf1 : (f * w) * (f * w) = ⟨D.b, hBC D.b.2⟩ := by
    haveI : IsMulCommutative C := isMulCommutative_of_torusBasisEquivFour E
    rw [mul_mul_mul_comm, hf, hw, mul_one]
  refine ⟨z, w, hz, hw, he1, hf1, basisChange E 0 p (by simp) h2p, ?_⟩
  have hgen : ∀ j : Fin 3,
      cocycleU (D := D) (hBC := hBC) (e := e * z) (f := f * w)
        (basisChange E 0 p (by simp) h2p) hL (gen (Type200.k m) j) = 0 := by
    intro j
    fin_cases j
    · exact cocycleU_gen0 (D := D) (hBC := hBC) (e := e * z) (f := f * w)
        (he := he1) (hf := hf1) (E := basisChange E 0 p (by simp) h2p) (hL := hL)
    · change cocycle ((Type200.action m).φu)
        (basisChange E 0 p (by simp) h2p) (hL D.u_mem_L) (gen (Type200.k m) 1) = 0
      rw [cocycle_basisChange_gen1 E 0 p (by simp) h2p
        ((Type200.action m).φu) (hL D.u_mem_L)
        (fun y hy => cocycleU_eq_zero_of_two_torsion he hf E hL hy) h2p]
      rw [show (Type200.action m).φu (gen (Type200.k m) 1) = gen (Type200.k m) 2 from by
        simpa [Torus.a] using Type200.u_a m]
      rw [map_zero, piBasis_gen2, add_zero]
      show p + p = 0
      rw [← two_nsmul]
      exact h2p
    · change cocycle ((Type200.action m).φu)
        (basisChange E 0 p (by simp) h2p) (hL D.u_mem_L) (gen (Type200.k m) 2) = 0
      rw [cocycle_basisChange_gen2 E 0 p (by simp) h2p
        ((Type200.action m).φu) (hL D.u_mem_L)
        (fun y hy => cocycleU_eq_zero_of_two_torsion he hf E hL hy) h2q]
      rw [show (Type200.action m).φu (gen (Type200.k m) 2) = gen (Type200.k m) 1 from by
        simpa [Torus.b] using Type200.u_b m]
      rw [piBasis_gen1, add_zero]
      have hq : cocycle ((Type200.action m).φu) E (hL D.u_mem_L)
          (gen (Type200.k m) 2) = (Type200.action m).φu p := by
        change cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 2) = (Type200.action m).φu p
        rw [show p = cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 1) from rfl]
        exact cocycleU_gen2_eq E hL he hf
      rw [hq]
      show (Type200.action m).φu p + (Type200.action m).φu p = 0
      rw [← two_nsmul, ← map_nsmul, h2p, map_zero]
  exact cocycle_eq_zero_of_gen_eq_zero (basisChange E 0 p (by simp) h2p)
    (hL D.u_mem_L) _ hgen

theorem cocycleR_apply_zsmul_gens
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (i j l : ℤ) :
    cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (i • gen (Type200.k m) 0 + j • gen (Type200.k m) 1 +
          l • gen (Type200.k m) 2) =
      j • cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 1) +
        l • cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 2) := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, cocycleR_gen0 he hf E hL]
  simp

theorem phiR_neg_sum (m : ℕ) :
    (Type200.action m).φρ
        ((-1 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b) =
      Torus.a := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
    Type200.rho_c, Type200.rho_a, Type200.rho_b]
  module

theorem cocycleR_u_rho_eq
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) :
    let p := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1)
    let q := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2)
    p + q + (Type200.action m).φρ ((Type200.action m).φu q) = 0 := by
  classical
  let p := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 1)
  let q := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 2)
  have hp2 : 2 • p = 0 := by
    simpa [p, two_zsmul, two_nsmul] using cocycleR_two_gen1 he hf E hL
  have hq2 : 2 • q = 0 := by
    simpa [q, two_zsmul, two_nsmul] using cocycleR_two_gen2 he hf E hL
  have hαu : ∀ x : Torus (Type200.k m),
      conjTorusFour D hBC E (hL D.u_mem_L) x = (Type200.action m).φu x := by
    intro x
    rw [action_eq_printed_add_cocycle E (hL D.u_mem_L) ((Type200.action m).φu)]
    have hx : cocycle ((Type200.action m).φu) E (hL D.u_mem_L) x = 0 := by
      change cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL x = 0
      rw [hu]; rfl
    rw [hx, add_zero]
  have hrel := congrArg (fun f => f (gen (Type200.k m) 1))
    (conjTorusFour_rels (E := E) hL).u_rho
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hrel
  change conjTorusFour D hBC E (hL D.ρ_mem_L)
      (conjTorusFour D hBC E (hL D.u_mem_L)
        (conjTorusFour D hBC E (hL D.ρ_mem_L)
          (conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) 1)))) =
    gen (Type200.k m) 1 at hrel
  rw [show conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) 1) =
      (Type200.action m).φu (gen (Type200.k m) 1) from hαu _] at hrel
  rw [show (Type200.action m).φu (gen (Type200.k m) 1) = gen (Type200.k m) 2 from by
    simpa [Torus.a] using Type200.u_a m] at hrel
  have hρgen2 : conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) 2) =
      (Type200.action m).φρ (gen (Type200.k m) 2) + q := by
    have h := action_eq_printed_add_cocycle E (hL D.ρ_mem_L) ((Type200.action m).φρ)
      (gen (Type200.k m) 2)
    change conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) 2) =
      (Type200.action m).φρ (gen (Type200.k m) 2) +
        cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 2)
    exact h
  rw [show conjTorusFour D hBC E (hL D.u_mem_L)
      (conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) 2)) =
      (Type200.action m).φu (conjTorusFour D hBC E (hL D.ρ_mem_L)
        (gen (Type200.k m) 2)) from hαu _] at hrel
  rw [hρgen2] at hrel
  have hρgen2' : (Type200.action m).φρ (gen (Type200.k m) 2) =
      (-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2 := by
    simpa [Torus.c, Torus.a, Torus.b] using Type200.rho_b m
  rw [hρgen2'] at hrel
  have hmapu : (Type200.action m).φu
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2 + q) =
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2) + (Type200.action m).φu q := by
    rw [map_add]
    congr 1
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
      show gen (Type200.k m) 0 = Torus.c from rfl,
      show gen (Type200.k m) 1 = Torus.a from rfl,
      show gen (Type200.k m) 2 = Torus.b from rfl,
      Type200.u_c, Type200.u_a, Type200.u_b]
    module
  rw [hmapu] at hrel
  have hρouter : conjTorusFour D hBC E (hL D.ρ_mem_L)
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2 + (Type200.action m).φu q) =
      (Type200.action m).φρ ((-1 : ℤ) • gen (Type200.k m) 0 +
        (-1 : ℤ) • gen (Type200.k m) 1 + (-1 : ℤ) • gen (Type200.k m) 2) +
      (Type200.action m).φρ ((Type200.action m).φu q) +
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
          (-1 : ℤ) • gen (Type200.k m) 2) +
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φu q) := by
    have h := action_eq_printed_add_cocycle E (hL D.ρ_mem_L) ((Type200.action m).φρ)
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2 + (Type200.action m).φu q)
    have hz : ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2 + (Type200.action m).φu q) =
        ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
          (-1 : ℤ) • gen (Type200.k m) 2) + (Type200.action m).φu q := by abel
    rw [h]
    simp only [map_add]
    abel
  rw [hρouter] at hrel
  have hδq : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((Type200.action m).φu q) = 0 := by
    refine cocycleR_eq_zero_of_two_torsion he hf E hL ?_
    rw [← map_nsmul]
    rw [show (2 : ℕ) • q = 0 from hq2, map_zero]
  have hδX : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2) = -p - q := by
    rw [cocycleR_apply_zsmul_gens E hL he hf]
    change (-1 : ℤ) • p + (-1 : ℤ) • q = -p - q
    abel
  rw [hδq, hδX, add_zero] at hrel
  have hβX : (Type200.action m).φρ
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2) = gen (Type200.k m) 1 := by
    simpa [Torus.c, Torus.a, Torus.b] using phiR_neg_sum m
  rw [hβX] at hrel
  have hr : (Type200.action m).φρ ((Type200.action m).φu q) = p + q := by
    have h' : (Type200.action m).φρ ((Type200.action m).φu q) + (-p - q) = 0 :=
      add_left_cancel (a := gen (Type200.k m) 1) (by simpa [add_assoc] using hrel)
    calc (Type200.action m).φρ ((Type200.action m).φu q)
        = (Type200.action m).φρ ((Type200.action m).φu q) + (-p - q) + (p + q) := by
          abel
      _ = 0 + (p + q) := by rw [h']
      _ = p + q := zero_add _
  have hp : p + p = 0 := by rw [← two_nsmul]; exact hp2
  have hq : q + q = 0 := by rw [← two_nsmul]; exact hq2
  have hfin : p + q + (Type200.action m).φρ ((Type200.action m).φu q) = 0 := by
    rw [hr]
    calc p + q + (p + q) = (p + p) + (q + q) := by abel
      _ = 0 := by rw [hp, hq, add_zero]
  simpa [p, q] using hfin

theorem cocycleR_rho_cube_eq
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    let p := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1)
    let q := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2)
    ((Type200.action m).φρ ((Type200.action m).φρ p) + p) +
      ((Type200.action m).φρ q + q) = 0 := by
  classical
  let p := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 1)
  let q := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 2)
  have hq2 : 2 • q = 0 := by
    simpa [q, two_zsmul, two_nsmul] using cocycleR_two_gen2 he hf E hL
  have hp2 : 2 • p = 0 := by
    simpa [p, two_zsmul, two_nsmul] using cocycleR_two_gen1 he hf E hL
  have hrel := congrArg (fun f => f (gen (Type200.k m) 1))
    (conjTorusFour_rels (E := E) hL).rho_cube
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hrel
  change conjTorusFour D hBC E (hL D.ρ_mem_L)
      (conjTorusFour D hBC E (hL D.ρ_mem_L)
        (conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) 1))) =
    gen (Type200.k m) 1 at hrel
  have hρ1 : conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) 1) =
      (Type200.action m).φρ (gen (Type200.k m) 1) + p := by
    have h := action_eq_printed_add_cocycle E (hL D.ρ_mem_L) ((Type200.action m).φρ)
      (gen (Type200.k m) 1)
    change conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) 1) =
      (Type200.action m).φρ (gen (Type200.k m) 1) +
        cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 1)
    exact h
  rw [hρ1] at hrel
  have hρ1' : (Type200.action m).φρ (gen (Type200.k m) 1) = gen (Type200.k m) 2 := by
    simpa [Torus.a] using Type200.rho_a m
  rw [hρ1'] at hrel
  rw [map_add] at hrel
  have hρp : conjTorusFour D hBC E (hL D.ρ_mem_L) p = (Type200.action m).φρ p := by
    rw [action_eq_printed_add_cocycle E (hL D.ρ_mem_L) ((Type200.action m).φρ)]
    have hzero : cocycle ((Type200.action m).φρ) E (hL D.ρ_mem_L) p = 0 := by
      change cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL p = 0
      exact cocycleR_eq_zero_of_two_torsion he hf E hL hp2
    rw [hzero, add_zero]
  have hρ2 : conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) 2) =
      (Type200.action m).φρ (gen (Type200.k m) 2) + q := by
    have h := action_eq_printed_add_cocycle E (hL D.ρ_mem_L) ((Type200.action m).φρ)
      (gen (Type200.k m) 2)
    change conjTorusFour D hBC E (hL D.ρ_mem_L) (gen (Type200.k m) 2) =
      (Type200.action m).φρ (gen (Type200.k m) 2) +
        cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 2)
    exact h
  rw [hρ2, hρp] at hrel
  have hρ2' : (Type200.action m).φρ (gen (Type200.k m) 2) =
      (-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2 := by
    simpa [Torus.c, Torus.a, Torus.b] using Type200.rho_b m
  rw [hρ2'] at hrel
  have hρ3 : conjTorusFour D hBC E (hL D.ρ_mem_L)
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2 + q +
        ((Type200.action m).φρ p)) =
      (Type200.action m).φρ ((-1 : ℤ) • gen (Type200.k m) 0 +
        (-1 : ℤ) • gen (Type200.k m) 1 + (-1 : ℤ) • gen (Type200.k m) 2) +
      (Type200.action m).φρ q + (Type200.action m).φρ ((Type200.action m).φρ p) +
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
          (-1 : ℤ) • gen (Type200.k m) 2) +
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL q +
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φρ p) := by
    have h := action_eq_printed_add_cocycle E (hL D.ρ_mem_L) ((Type200.action m).φρ)
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2 + q + ((Type200.action m).φρ p))
    rw [h]
    simp only [map_add]
    abel
  rw [hρ3] at hrel
  have hδX : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2) = -p - q := by
    rw [cocycleR_apply_zsmul_gens E hL he hf]
    change (-1 : ℤ) • p + (-1 : ℤ) • q = -p - q
    abel
  have hδq : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL q = 0 := by
    exact cocycleR_eq_zero_of_two_torsion he hf E hL hq2
  have hδBp : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((Type200.action m).φρ p) = 0 := by
    refine cocycleR_eq_zero_of_two_torsion he hf E hL ?_
    rw [← map_nsmul]
    rw [show (2 : ℕ) • p = 0 from hp2, map_zero]
  rw [hδX, hδq, hδBp, add_zero, add_zero] at hrel
  have hβX : (Type200.action m).φρ
      ((-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2) = gen (Type200.k m) 1 := by
    simpa [Torus.c, Torus.a, Torus.b] using phiR_neg_sum m
  rw [hβX] at hrel
  have hfin : ((Type200.action m).φρ ((Type200.action m).φρ p) + p) +
      ((Type200.action m).φρ q + q) = 0 := by
    have h' : (Type200.action m).φρ q + (Type200.action m).φρ
        ((Type200.action m).φρ p) + (-p - q) = 0 :=
      add_left_cancel (a := gen (Type200.k m) 1) (by simpa [add_assoc] using hrel)
    have hEq : (Type200.action m).φρ ((Type200.action m).φρ p) +
        (Type200.action m).φρ q = p + q := by
      have h'' : (Type200.action m).φρ q + (Type200.action m).φρ
          ((Type200.action m).φρ p) = p + q := by
        calc (Type200.action m).φρ q + (Type200.action m).φρ
              ((Type200.action m).φρ p)
            = (Type200.action m).φρ q + (Type200.action m).φρ
                ((Type200.action m).φρ p) + (-p - q) + (p + q) := by abel
          _ = 0 + (p + q) := by rw [h']
          _ = p + q := zero_add _
      rwa [add_comm] at h''
    have hp : p + p = 0 := by rw [← two_nsmul]; exact hp2
    have hq : q + q = 0 := by rw [← two_nsmul]; exact hq2
    calc ((Type200.action m).φρ ((Type200.action m).φρ p) + p) +
          ((Type200.action m).φρ q + q)
        = ((Type200.action m).φρ ((Type200.action m).φρ p) +
            (Type200.action m).φρ q) + (p + q) := by abel
      _ = (p + q) + (p + q) := by rw [hEq]
      _ = (p + p) + (q + q) := by abel
      _ = 0 := by rw [hp, hq, add_zero]
  simpa [p, q] using hfin

@[expose] noncomputable def eBasis (m : ℕ) : Fin 3 → Torus (Type200.k m)
  | 0 => (2 ^ (m - 1) : ℕ) • gen (Type200.k m) 0
  | 1 => (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 1
  | 2 => (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 2

@[expose] noncomputable def eBit {m : ℕ} (x : Torus (Type200.k m)) (i : Fin 3) : ℤ :=
  if x i = 0 then 0 else 1

@[simp]
theorem eBasis_zero (m : ℕ) :
    eBasis m 0 = (2 ^ (m - 1) : ℕ) • gen (Type200.k m) 0 := rfl

@[simp]
theorem eBasis_one (m : ℕ) :
    eBasis m 1 = (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 1 := rfl

@[simp]
theorem eBasis_two (m : ℕ) :
    eBasis m 2 = (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 2 := rfl

theorem eBit_spec_gen {k : Fin 3 → ℕ} {x : Torus k} (hx : 2 • x = 0) (i : Fin 3)
    (hi : 1 ≤ k i) :
    x i = (if x i = 0 then (0 : ℤ) else 1) •
      ((2 ^ (k i - 1) : ℕ) : ZMod (2 ^ k i)) := by
  have h2 : (2 : ZMod (2 ^ k i)) * x i = 0 := by
    simpa [Pi.smul_apply, nsmul_eq_mul] using congrFun hx i
  rcases (zmod_two_mul_eq_zero_iff hi (x i)).1 h2 with h | h
  · simp [h]
  · by_cases h0 : x i = 0
    · simp [h0]
    · rw [if_neg h0, h, one_zsmul]

theorem eBit_spec {x : Torus (Type200.k m)} (hx : 2 • x = 0) (i : Fin 3) :
    x i = eBit x i • eBasis m i i := by
  fin_cases i
  · change x 0 = eBit x 0 • eBasis m 0 0
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 : 2 ^ Type200.k 0 0 = 1 := by
        rw [show Type200.k 0 0 = 0 from rfl]; norm_num
      haveI : Subsingleton (ZMod (2 ^ Type200.k 0 0)) := by
        rw [h1]; infer_instance
      have hx0 : x 0 = 0 := Subsingleton.elim _ _
      simp [eBit, hx0, eBasis]
    · have hk : 1 ≤ Type200.k m 0 := by
        show 1 ≤ m
        omega
      have h := eBit_spec_gen (k := Type200.k m) hx 0 hk
      have hEq : eBasis m 0 0 = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        simp [eBasis, gen, Pi.single_apply, nsmul_eq_mul]
        rfl
      rw [hEq]
      change x 0 = (if x 0 = 0 then (0 : ℤ) else 1) •
        ((2 ^ (Type200.k m 0 - 1) : ℕ) : ZMod (2 ^ Type200.k m 0))
      exact h
  · change x 1 = eBit x 1 • eBasis m 1 1
    have hk : 1 ≤ Type200.k m 1 := by
      show 1 ≤ m + 2
      omega
    have h := eBit_spec_gen (k := Type200.k m) hx 1 hk
    have hEq : eBasis m 1 1 = ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
      simp [eBasis, gen, Pi.single_apply, nsmul_eq_mul]
      rfl
    rw [hEq]
    change x 1 = (if x 1 = 0 then (0 : ℤ) else 1) •
      ((2 ^ (Type200.k m 1 - 1) : ℕ) : ZMod (2 ^ Type200.k m 1))
    exact h
  · change x 2 = eBit x 2 • eBasis m 2 2
    have hk : 1 ≤ Type200.k m 2 := by
      show 1 ≤ m + 2
      omega
    have h := eBit_spec_gen (k := Type200.k m) hx 2 hk
    have hEq : eBasis m 2 2 = ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
      simp [eBasis, gen, Pi.single_apply, nsmul_eq_mul]
      rfl
    rw [hEq]
    change x 2 = (if x 2 = 0 then (0 : ℤ) else 1) •
      ((2 ^ (Type200.k m 2 - 1) : ℕ) : ZMod (2 ^ Type200.k m 2))
    exact h

theorem two_torsion_decomp {x : Torus (Type200.k m)} (hx : 2 • x = 0) :
    x = eBit x 0 • eBasis m 0 + eBit x 1 • eBasis m 1 + eBit x 2 • eBasis m 2 := by
  funext i
  fin_cases i
  · simpa [Pi.add_apply, Pi.smul_apply, eBasis, gen, Pi.single_apply, nsmul_eq_mul]
      using eBit_spec hx 0
  · simpa [Pi.add_apply, Pi.smul_apply, eBasis, gen, Pi.single_apply, nsmul_eq_mul]
      using eBit_spec hx 1
  · simpa [Pi.add_apply, Pi.smul_apply, eBasis, gen, Pi.single_apply, nsmul_eq_mul]
      using eBit_spec hx 2

theorem phiU_eBasis_zero (m : ℕ) :
    (Type200.action m).φu (eBasis m 0) = eBasis m 0 := by
  change (matAct (Type200.k m) Type200.uM (Type200.compat_u m))
      ((2 ^ (m - 1) : ℕ) • gen (Type200.k m) 0) =
    (2 ^ (m - 1) : ℕ) • gen (Type200.k m) 0
  rw [map_nsmul]
  rw [show matAct (Type200.k m) Type200.uM (Type200.compat_u m)
      (gen (Type200.k m) 0) = gen (Type200.k m) 0 from by
    change (Type200.action m).φu (gen (Type200.k m) 0) = gen (Type200.k m) 0
    simpa [Torus.c] using Type200.u_c m]

theorem phiU_eBasis_one (m : ℕ) :
    (Type200.action m).φu (eBasis m 1) = eBasis m 2 := by
  change (matAct (Type200.k m) Type200.uM (Type200.compat_u m))
      ((2 ^ (m + 1) : ℕ) • gen (Type200.k m) 1) =
    (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 2
  rw [map_nsmul]
  rw [show matAct (Type200.k m) Type200.uM (Type200.compat_u m)
      (gen (Type200.k m) 1) = gen (Type200.k m) 2 from by
    change (Type200.action m).φu (gen (Type200.k m) 1) = gen (Type200.k m) 2
    simpa [Torus.a, Torus.b] using Type200.u_a m]

theorem phiU_eBasis_two (m : ℕ) :
    (Type200.action m).φu (eBasis m 2) = eBasis m 1 := by
  change (matAct (Type200.k m) Type200.uM (Type200.compat_u m))
      ((2 ^ (m + 1) : ℕ) • gen (Type200.k m) 2) =
    (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 1
  rw [map_nsmul]
  rw [show matAct (Type200.k m) Type200.uM (Type200.compat_u m)
      (gen (Type200.k m) 2) = gen (Type200.k m) 1 from by
    change (Type200.action m).φu (gen (Type200.k m) 2) = gen (Type200.k m) 1
    simpa [Torus.a, Torus.b] using Type200.u_b m]

theorem phiR_eBasis_zero (m : ℕ) :
    (Type200.action m).φρ (eBasis m 0) = eBasis m 0 := by
  change (matAct (Type200.k m) Type200.ρM (Type200.compat_rho m))
      ((2 ^ (m - 1) : ℕ) • gen (Type200.k m) 0) =
    (2 ^ (m - 1) : ℕ) • gen (Type200.k m) 0
  rw [map_nsmul]
  rw [show matAct (Type200.k m) Type200.ρM (Type200.compat_rho m)
      (gen (Type200.k m) 0) = gen (Type200.k m) 0 from by
    change (Type200.action m).φρ (gen (Type200.k m) 0) = gen (Type200.k m) 0
    simpa [Torus.c] using Type200.rho_c m]

theorem phiR_eBasis_one (m : ℕ) :
    (Type200.action m).φρ (eBasis m 1) = eBasis m 2 := by
  change (matAct (Type200.k m) Type200.ρM (Type200.compat_rho m))
      ((2 ^ (m + 1) : ℕ) • gen (Type200.k m) 1) =
    (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 2
  rw [map_nsmul]
  rw [show matAct (Type200.k m) Type200.ρM (Type200.compat_rho m)
      (gen (Type200.k m) 1) = gen (Type200.k m) 2 from by
    change (Type200.action m).φρ (gen (Type200.k m) 1) = gen (Type200.k m) 2
    simpa [Torus.a, Torus.b] using Type200.rho_a m]

theorem zmod_two_pow_succ_cast_eq_zero (m : ℕ) :
    ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
  rw [show 2 ^ (m + 1) = 2 ^ m * 2 by ring, Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem zmod_two_pow_succ_pow_eq_zero (m : ℕ) :
    (2 : ZMod (2 ^ m)) ^ (m + 1) = 0 := by
  change (((2 : ℕ) : ZMod (2 ^ m)) ^ (m + 1)) = 0
  rw [← Nat.cast_pow]
  exact zmod_two_pow_succ_cast_eq_zero m

theorem zmod_two_pow_succ_neg (m : ℕ) :
    -((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) = ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) := by
  rw [neg_eq_iff_add_eq_zero]
  rw [← Nat.cast_add, show 2 ^ (m + 1) + 2 ^ (m + 1) = 2 ^ (m + 2) by ring,
    ZMod.natCast_self]

theorem zmod_two_pow_succ_pow_neg (m : ℕ) :
    -((2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) = (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) := by
  change -(((2 : ℕ) : ZMod (2 ^ (m + 2))) ^ (m + 1)) =
    (((2 : ℕ) : ZMod (2 ^ (m + 2))) ^ (m + 1))
  rw [← Nat.cast_pow]
  exact zmod_two_pow_succ_neg m

theorem phiR_eBasis_two (m : ℕ) :
    (Type200.action m).φρ (eBasis m 2) = eBasis m 1 + eBasis m 2 := by
  change (matAct (Type200.k m) Type200.ρM (Type200.compat_rho m))
      ((2 ^ (m + 1) : ℕ) • gen (Type200.k m) 2) =
    (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 1 +
      (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 2
  rw [map_nsmul]
  rw [show matAct (Type200.k m) Type200.ρM (Type200.compat_rho m)
      (gen (Type200.k m) 2) = (-1 : ℤ) • gen (Type200.k m) 0 +
        (-1 : ℤ) • gen (Type200.k m) 1 + (-1 : ℤ) • gen (Type200.k m) 2 from by
      change (Type200.action m).φρ (gen (Type200.k m) 2) = (-1 : ℤ) • gen (Type200.k m) 0 +
        (-1 : ℤ) • gen (Type200.k m) 1 + (-1 : ℤ) • gen (Type200.k m) 2
      simpa [Torus.c, Torus.a, Torus.b] using Type200.rho_b m]
  funext i
  fin_cases i
  · simp [Pi.add_apply, Pi.smul_apply, gen, Pi.single_apply, nsmul_eq_mul, zsmul_eq_mul,
      show Type200.k m 0 = m from rfl]
    exact zmod_two_pow_succ_pow_eq_zero m
  · simp [Pi.add_apply, Pi.smul_apply, gen, Pi.single_apply, nsmul_eq_mul, zsmul_eq_mul,
      show Type200.k m 1 = m + 2 from rfl]
    exact zmod_two_pow_succ_pow_neg m
  · simp [Pi.add_apply, Pi.smul_apply, gen, Pi.single_apply, nsmul_eq_mul, zsmul_eq_mul,
      show Type200.k m 2 = m + 2 from rfl]
    exact zmod_two_pow_succ_pow_neg m

theorem zmod_two_pow_pow_eq_zero (N : ℕ) :
    (2 : ZMod (2 ^ N)) ^ N = 0 := by
  change (((2 : ℕ) : ZMod (2 ^ N)) ^ N) = 0
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self _

theorem zmod_two_pow_pred_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact Nat.not_dvd_of_pos_of_lt (Nat.pow_pos (by norm_num))
    (Nat.pow_lt_pow_right (by norm_num) (by omega)) h

theorem zmod_two_pow_succ_ne_zero (m : ℕ) :
    ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 2))) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact Nat.not_dvd_of_pos_of_lt (Nat.pow_pos (by norm_num))
    (Nat.pow_lt_pow_right (by norm_num) (by omega)) h

theorem zmod_two_pow_pred_pow_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    (2 : ZMod (2 ^ m)) ^ (m - 1) ≠ 0 := by
  change (((2 : ℕ) : ZMod (2 ^ m)) ^ (m - 1)) ≠ 0
  rw [← Nat.cast_pow]
  exact zmod_two_pow_pred_ne_zero m hm

theorem zmod_two_pow_succ_pow_ne_zero (m : ℕ) :
    (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) ≠ 0 := by
  change (((2 : ℕ) : ZMod (2 ^ (m + 2))) ^ (m + 1)) ≠ 0
  rw [← Nat.cast_pow]
  exact zmod_two_pow_succ_ne_zero m

theorem eBit_eq_zero_of_mul_eq_zero (x : Torus (Type200.k m)) (i : Fin 3)
    (t : ZMod (2 ^ Type200.k m i)) (ht : t ≠ 0)
    (h : (↑(eBit x i) : ZMod (2 ^ Type200.k m i)) * t = 0) : eBit x i = 0 := by
  have hbit : eBit x i = 0 ∨ eBit x i = 1 := by
    by_cases h0 : x i = 0
    · left; simp only [eBit]; rw [if_pos h0]
    · right; simp only [eBit]; rw [if_neg h0]
  rcases hbit with h0 | h1
  · exact h0
  · rw [h1] at h
    norm_num at h
    exact absurd h ht

theorem cocycleR_forms
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) :
    ∃ a l : ℤ,
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL (gen (Type200.k m) 1) =
        l • eBasis m 2 ∧
      cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL (gen (Type200.k m) 2) =
        a • eBasis m 0 + l • eBasis m 1 := by
  classical
  let p := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 1)
  let q := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 2)
  have hp2 : 2 • p = 0 := by
    simpa [p, two_zsmul, two_nsmul] using cocycleR_two_gen1 he hf E hL
  have hq2 : 2 • q = 0 := by
    simpa [q, two_zsmul, two_nsmul] using cocycleR_two_gen2 he hf E hL
  have hp := two_torsion_decomp (m := m) hp2
  have hq := two_torsion_decomp (m := m) hq2
  have h1 := cocycleR_u_rho_eq E hL he hf hu
  have h2 := cocycleR_rho_cube_eq E hL he hf
  change p + q + (Type200.action m).φρ ((Type200.action m).φu q) = 0 at h1
  change ((Type200.action m).φρ ((Type200.action m).φρ p) + p) +
    ((Type200.action m).φρ q + q) = 0 at h2
  rw [hp, hq] at h1 h2
  simp only [map_add, map_zsmul, map_nsmul, phiU_eBasis_zero, phiU_eBasis_one,
    phiU_eBasis_two, phiR_eBasis_zero, phiR_eBasis_one, phiR_eBasis_two] at h1 h2
  have h10 := congrFun h1 0
  have h11 := congrFun h1 1
  have h12 := congrFun h1 2
  have h21 := congrFun h2 1
  simp [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, eBasis, gen, Pi.single_apply,
    nsmul_eq_mul, Pi.one_apply, Pi.zero_apply] at h10 h11 h12 h21
  have h2t1 : (2 : ZMod (2 ^ (m + 2))) * (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) = 0 := by
    rw [← pow_succ', show m + 1 + 1 = m + 2 by omega]
    exact zmod_two_pow_pow_eq_zero (m + 2)
  have hq1d : (↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
        (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
      (↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
        (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) = 0 := by
    calc (↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
          (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
        (↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
          (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)
        = (↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
            ((2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
              (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) := by ring
      _ = (↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
            (2 * (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) := by rw [two_mul]
      _ = (↑(eBit q 1) : ZMod (2 ^ (m + 2))) * 0 := by rw [h2t1]
      _ = 0 := mul_zero _
  have hp1t : (↑(eBit p 1) : ZMod (2 ^ (m + 2))) *
      (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) = 0 := by
    have h' : (↑(eBit p 1) : ZMod (2 ^ (m + 2))) *
          (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
        ((↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
            (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
          (↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
            (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) = 0 := by
      rw [← add_assoc]; exact h11
    rw [hq1d, add_zero] at h'
    exact h'
  have hp1 : eBit p 1 = 0 :=
    eBit_eq_zero_of_mul_eq_zero p 1 ((2 : ZMod (2 ^ (m + 2))) ^ (m + 1))
      (zmod_two_pow_succ_pow_ne_zero m) hp1t
  have hq2d : (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
        (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
      (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
        (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) = 0 := by
    calc (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
          (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
        (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
          (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)
        = (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
            ((2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
              (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) := by ring
      _ = (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
            (2 * (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) := by rw [two_mul]
      _ = (↑(eBit q 2) : ZMod (2 ^ (m + 2))) * 0 := by rw [h2t1]
      _ = 0 := mul_zero _
  have hp2q1t : ((↑(eBit p 2) + ↑(eBit q 1)) : ZMod (2 ^ (m + 2))) *
      (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) = 0 := by
    have h' : (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
          (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
        ((↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
            (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
          ((↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
              (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
            (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
              (2 : ZMod (2 ^ (m + 2))) ^ (m + 1))) = 0 := by
      calc (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
            (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
          ((↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
              (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
            ((↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
                (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
              (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
                (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)))
          = (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
              (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
            (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
              (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
            ((↑(eBit q 1) : ZMod (2 ^ (m + 2))) *
                (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
              (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
                (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) := by abel
        _ = 0 := h12
    rw [hq2d, add_zero] at h'
    simpa [add_mul] using h'
  have hp2q1 : eBit p 2 = eBit q 1 := by
    have hpbit : eBit p 2 = 0 ∨ eBit p 2 = 1 := by
      by_cases h0 : p 2 = 0
      · left; simp only [eBit]; rw [if_pos h0]
      · right; simp only [eBit]; rw [if_neg h0]
    have hqbit : eBit q 1 = 0 ∨ eBit q 1 = 1 := by
      by_cases h0 : q 1 = 0
      · left; simp only [eBit]; rw [if_pos h0]
      · right; simp only [eBit]; rw [if_neg h0]
    rcases hpbit with hp | hp <;> rcases hqbit with hq | hq
    · rw [hp, hq]
    · exfalso
      rw [hp, hq] at hp2q1t
      norm_num at hp2q1t
      exact zmod_two_pow_succ_pow_ne_zero m hp2q1t
    · exfalso
      rw [hp, hq] at hp2q1t
      norm_num at hp2q1t
      exact zmod_two_pow_succ_pow_ne_zero m hp2q1t
    · rw [hp, hq]
  have hq2t : (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
      (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) = 0 := by
    have hp2d : (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
          (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
        (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
          (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) = 0 := by
      calc (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
            (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
          (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
            (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)
          = (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
              ((2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
                (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) := by ring
        _ = (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
              (2 * (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) := by rw [two_mul]
        _ = (↑(eBit p 2) : ZMod (2 ^ (m + 2))) * 0 := by rw [h2t1]
        _ = 0 := mul_zero _
    rw [hp1, ← hp2q1] at h21
    simp only [Int.cast_zero, zero_mul, zero_add, add_zero] at h21
    have h' : (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
          (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
        ((↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
            (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
          (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
            (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) = 0 := by
      calc (↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
            (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
          ((↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
              (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
            (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
              (2 : ZMod (2 ^ (m + 2))) ^ (m + 1))
          = (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
              (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
            ((↑(eBit q 2) : ZMod (2 ^ (m + 2))) *
                (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) +
              (↑(eBit p 2) : ZMod (2 ^ (m + 2))) *
                (2 : ZMod (2 ^ (m + 2))) ^ (m + 1)) := by abel
        _ = 0 := h21
    rw [hp2d, add_zero] at h'
    exact h'
  have hq2' : eBit q 2 = 0 :=
    eBit_eq_zero_of_mul_eq_zero q 2 ((2 : ZMod (2 ^ (m + 2))) ^ (m + 1))
      (zmod_two_pow_succ_pow_ne_zero m) hq2t
  have hp0 : eBit p 0 = 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 : (2 : ℕ) ^ Type200.k 0 0 = 1 := by
        rw [show Type200.k 0 0 = 0 from rfl]; norm_num
      haveI : Subsingleton (ZMod (2 ^ Type200.k 0 0)) := by
        rw [h1]; infer_instance
      have h0 : p 0 = 0 := Subsingleton.elim _ _
      simp [eBit, h0]
    · have h2t0 : (2 : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1) = 0 := by
        rw [← pow_succ', show m - 1 + 1 = m by omega]
        exact zmod_two_pow_pow_eq_zero m
      have hq0d : (↑(eBit q 0) : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1) +
          (↑(eBit q 0) : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1) = 0 := by
        calc (↑(eBit q 0) : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1) +
              (↑(eBit q 0) : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1)
            = (↑(eBit q 0) : ZMod (2 ^ m)) *
                ((2 : ZMod (2 ^ m)) ^ (m - 1) + (2 : ZMod (2 ^ m)) ^ (m - 1)) := by ring
          _ = (↑(eBit q 0) : ZMod (2 ^ m)) *
                (2 * (2 : ZMod (2 ^ m)) ^ (m - 1)) := by rw [two_mul]
          _ = (↑(eBit q 0) : ZMod (2 ^ m)) * 0 := by rw [h2t0]
          _ = 0 := mul_zero _
      have hat : (↑(eBit p 0) : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1) = 0 := by
        have h' : (↑(eBit p 0) : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1) +
            ((↑(eBit q 0) : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1) +
              (↑(eBit q 0) : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1)) = 0 := by
          rw [← add_assoc]; exact h10
        rw [hq0d, add_zero] at h'
        exact h'
      exact eBit_eq_zero_of_mul_eq_zero p 0 ((2 : ZMod (2 ^ m)) ^ (m - 1))
        (zmod_two_pow_pred_pow_ne_zero m hm) hat
  refine ⟨eBit q 0, eBit p 2, ?_, ?_⟩
  · change p = eBit p 2 • eBasis m 2
    nth_rewrite 1 [hp]
    simp [hp0, hp1]
  · change q = eBit q 0 • eBasis m 0 + eBit p 2 • eBasis m 1
    nth_rewrite 1 [hq]
    rw [← hp2q1]
    simp [hq2']

theorem eBasis_two_torsion (m : ℕ) (i : Fin 3) : 2 • eBasis m i = 0 := by
  fin_cases i
  · change 2 • eBasis m 0 = 0
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · decide
    · rw [eBasis_zero, smul_smul, show 2 * 2 ^ (m - 1) = 2 ^ m by
        rw [← pow_succ', show m - 1 + 1 = m by omega]]
      ext j
      fin_cases j
      · simp [gen, Pi.single_apply, nsmul_eq_mul]
        exact zmod_two_pow_pow_eq_zero m
      · simp [gen, Pi.single_apply]
      · simp [gen, Pi.single_apply]
  · change 2 • eBasis m 1 = 0
    rw [eBasis_one, smul_smul, show 2 * 2 ^ (m + 1) = 2 ^ (m + 2) by
      rw [← pow_succ', show m + 1 + 1 = m + 2 by omega]]
    ext j
    fin_cases j
    · simp [gen, Pi.single_apply]
    · simp [gen, Pi.single_apply, nsmul_eq_mul]
      exact zmod_two_pow_pow_eq_zero (m + 2)
    · simp [gen, Pi.single_apply]
  · change 2 • eBasis m 2 = 0
    rw [eBasis_two, smul_smul, show 2 * 2 ^ (m + 1) = 2 ^ (m + 2) by
      rw [← pow_succ', show m + 1 + 1 = m + 2 by omega]]
    ext j
    fin_cases j
    · simp [gen, Pi.single_apply]
    · simp [gen, Pi.single_apply]
    · simp [gen, Pi.single_apply, nsmul_eq_mul]
      exact zmod_two_pow_pow_eq_zero (m + 2)

theorem smul_eBasis_add_self (m : ℕ) (l : ℤ) (i : Fin 3) :
    l • eBasis m i + l • eBasis m i = 0 := by
  have h2 : (2 : ℤ) • eBasis m i = 0 := by
    rw [two_zsmul, ← two_nsmul, eBasis_two_torsion]
  calc l • eBasis m i + l • eBasis m i
      = (l + l) • eBasis m i := by rw [← add_smul]
    _ = (2 * l) • eBasis m i := by congr 1; ring
    _ = (l * 2) • eBasis m i := by rw [mul_comm]
    _ = l • ((2 : ℤ) • eBasis m i) := by rw [← smul_smul]
    _ = l • 0 := by rw [h2]
    _ = 0 := smul_zero l

theorem rhoP_form {p q : Torus (Type200.k m)} {a l : ℤ}
    (hp : p = l • eBasis m 2) (hq : q = a • eBasis m 0 + l • eBasis m 1) :
    q + (Type200.action m).φρ p = a • eBasis m 0 + l • eBasis m 2 := by
  rw [hq, hp, map_zsmul, phiR_eBasis_two, smul_add]
  rw [show a • eBasis m 0 + l • eBasis m 1 + (l • eBasis m 1 + l • eBasis m 2)
      = a • eBasis m 0 + (l • eBasis m 1 + l • eBasis m 1) + l • eBasis m 2 by abel]
  rw [smul_eBasis_add_self, add_zero]

theorem rhoQ_form {p q : Torus (Type200.k m)} {a l : ℤ}
    (hp : p = l • eBasis m 2) (hq : q = a • eBasis m 0 + l • eBasis m 1) :
    (Type200.action m).φu (q + (Type200.action m).φρ p) =
      a • eBasis m 0 + l • eBasis m 1 := by
  rw [rhoP_form hp hq, map_add]
  simp only [map_zsmul, phiU_eBasis_zero, phiU_eBasis_two]

theorem exists_rho_normalized_all
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) :
    ∃ z w : C, z * z = 1 ∧ w * w = 1 ∧
      (e * z) * (e * z) = ⟨D.a, hBC D.a.2⟩ ∧
      (f * w) * (f * w) = ⟨D.b, hBC D.b.2⟩ ∧
      ∃ E2 : TorusBasisEquivFour D hBC (e * z) (f * w),
        cocycleU (D := D) (hBC := hBC) (e := e * z) (f := f * w) E2 hL = 0 ∧
        cocycleR (D := D) (hBC := hBC) (e := e * z) (f := f * w) E2 hL = 0 := by
  classical
  let p : Torus (Type200.k m) := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 1)
  let q : Torus (Type200.k m) := cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 2)
  have h2p : 2 • p = 0 := by
    simpa [p, two_zsmul, two_nsmul] using cocycleR_two_gen1 he hf E hL
  have h2q : 2 • q = 0 := by
    simpa [q, two_zsmul, two_nsmul] using cocycleR_two_gen2 he hf E hL
  obtain ⟨a, l, hp, hq⟩ := cocycleR_forms E hL he hf hu
  have hp' : p = l • eBasis m 2 := hp
  have hq' : q = a • eBasis m 0 + l • eBasis m 1 := hq
  let P : Torus (Type200.k m) := q + (Type200.action m).φρ p
  let Q : Torus (Type200.k m) := (Type200.action m).φu P
  have hP : P = a • eBasis m 0 + l • eBasis m 2 := rhoP_form hp hq
  have hQ : Q = a • eBasis m 0 + l • eBasis m 1 := rhoQ_form hp hq
  have h2P : 2 • P = 0 := by
    rw [hP, two_nsmul, add_add_add_comm, smul_eBasis_add_self, smul_eBasis_add_self,
      add_zero]
  have h2Q : 2 • Q = 0 := by
    rw [hQ, two_nsmul, add_add_add_comm, smul_eBasis_add_self, smul_eBasis_add_self,
      add_zero]
  let z : C := Additive.toMul (E.E P)
  let w : C := Additive.toMul (E.E Q)
  have hz : z * z = 1 := by
    apply Additive.ofMul.injective
    change Additive.ofMul (z * z) = Additive.ofMul (1 : C)
    rw [ofMul_mul, ofMul_one]
    have h : (2 : ℕ) • (E.E P) = 0 := by
      rw [← map_nsmul]
      rw [h2P, map_zero]
    rw [show E.E P = Additive.ofMul z from rfl] at h
    rwa [two_nsmul] at h
  have hw : w * w = 1 := by
    apply Additive.ofMul.injective
    change Additive.ofMul (w * w) = Additive.ofMul (1 : C)
    rw [ofMul_mul, ofMul_one]
    have h : (2 : ℕ) • (E.E Q) = 0 := by
      rw [← map_nsmul]
      rw [h2Q, map_zero]
    rw [show E.E Q = Additive.ofMul w from rfl] at h
    rwa [two_nsmul] at h
  have he1 : (e * z) * (e * z) = ⟨D.a, hBC D.a.2⟩ := by
    haveI : IsMulCommutative C := isMulCommutative_of_torusBasisEquivFour E
    rw [mul_mul_mul_comm, he, hz, mul_one]
  have hf1 : (f * w) * (f * w) = ⟨D.b, hBC D.b.2⟩ := by
    haveI : IsMulCommutative C := isMulCommutative_of_torusBasisEquivFour E
    rw [mul_mul_mul_comm, hf, hw, mul_one]
  refine ⟨z, w, hz, hw, he1, hf1, basisChange E P Q h2P h2Q, ?_, ?_⟩
  · have hu1 : cocycle ((Type200.action m).φu) E (hL D.u_mem_L)
        (gen (Type200.k m) 1) = 0 := by
      change (cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL)
        (gen (Type200.k m) 1) = 0
      rw [hu]
      rfl
    have hu2 : cocycle ((Type200.action m).φu) E (hL D.u_mem_L)
        (gen (Type200.k m) 2) = 0 := by
      change (cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL)
        (gen (Type200.k m) 2) = 0
      rw [hu]
      rfl
    have hgen : ∀ j : Fin 3,
        cocycleU (D := D) (hBC := hBC) (e := e * z) (f := f * w)
          (basisChange E P Q h2P h2Q) hL (gen (Type200.k m) j) = 0 := by
      intro j
      fin_cases j
      · exact cocycleU_gen0 (D := D) (hBC := hBC) (e := e * z) (f := f * w)
          (he := he1) (hf := hf1) (E := basisChange E P Q h2P h2Q) (hL := hL)
      · change cocycle ((Type200.action m).φu)
          (basisChange E P Q h2P h2Q) (hL D.u_mem_L) (gen (Type200.k m) 1) = 0
        rw [cocycle_basisChange_gen1 E P Q h2P h2Q
          ((Type200.action m).φu) (hL D.u_mem_L)
          (fun y hy => cocycleU_eq_zero_of_two_torsion he hf E hL hy)
          (by rw [hu1]; simp)]
        rw [hu1, zero_add]
        rw [show (Type200.action m).φu (gen (Type200.k m) 1) = gen (Type200.k m) 2 from by
          simpa [Torus.a] using Type200.u_a m]
        rw [piBasis_gen2]
        change Q + Q = 0
        rw [← two_nsmul]
        exact h2Q
      · change cocycle ((Type200.action m).φu)
          (basisChange E P Q h2P h2Q) (hL D.u_mem_L) (gen (Type200.k m) 2) = 0
        rw [cocycle_basisChange_gen2 E P Q h2P h2Q
          ((Type200.action m).φu) (hL D.u_mem_L)
          (fun y hy => cocycleU_eq_zero_of_two_torsion he hf E hL hy)
          (by rw [hu2]; simp)]
        rw [hu2, zero_add]
        rw [show (Type200.action m).φu (gen (Type200.k m) 2) = gen (Type200.k m) 1 from by
          simpa [Torus.b] using Type200.u_b m]
        rw [piBasis_gen1]
        have hφQ : (Type200.action m).φu Q = P := by
          rw [hQ, map_add]
          simp only [map_zsmul, phiU_eBasis_zero, phiU_eBasis_one, phiU_eBasis_two]
          exact hP.symm
        rw [hφQ]
        rw [← two_nsmul]
        exact h2P
    exact cocycle_eq_zero_of_gen_eq_zero (basisChange E P Q h2P h2Q)
      (hL D.u_mem_L) _ hgen
  · have h2p' : 2 • cocycle ((Type200.action m).φρ) E (hL D.ρ_mem_L)
        (gen (Type200.k m) 1) = 0 := by
      change 2 • p = 0
      exact h2p
    have h2q' : 2 • cocycle ((Type200.action m).φρ) E (hL D.ρ_mem_L)
        (gen (Type200.k m) 2) = 0 := by
      change 2 • q = 0
      exact h2q
    have hgen : ∀ j : Fin 3,
        cocycleR (D := D) (hBC := hBC) (e := e * z) (f := f * w)
          (basisChange E P Q h2P h2Q) hL (gen (Type200.k m) j) = 0 := by
      intro j
      fin_cases j
      · exact cocycleR_gen0 (D := D) (hBC := hBC) (e := e * z) (f := f * w)
          (he := he1) (hf := hf1) (E := basisChange E P Q h2P h2Q) (hL := hL)
      · change cocycle ((Type200.action m).φρ)
          (basisChange E P Q h2P h2Q) (hL D.ρ_mem_L) (gen (Type200.k m) 1) = 0
        rw [cocycle_basisChange_gen1 E P Q h2P h2Q
          ((Type200.action m).φρ) (hL D.ρ_mem_L)
          (fun y hy => cocycleR_eq_zero_of_two_torsion he hf E hL hy)
          h2p']
        rw [show cocycle ((Type200.action m).φρ) E (hL D.ρ_mem_L)
          (gen (Type200.k m) 1) = p from rfl]
        rw [show (Type200.action m).φρ (gen (Type200.k m) 1) = gen (Type200.k m) 2 from by
          simpa [Torus.a] using Type200.rho_a m]
        rw [piBasis_gen2]
        rw [hp', hP, hQ, map_add, map_zsmul, map_zsmul, phiR_eBasis_zero, phiR_eBasis_two,
          smul_add]
        have h1 := smul_eBasis_add_self m a 0
        have h2 := smul_eBasis_add_self m l 1
        have h3 := smul_eBasis_add_self m l 2
        linear_combination h1 + h2 + h3
      · change cocycle ((Type200.action m).φρ)
          (basisChange E P Q h2P h2Q) (hL D.ρ_mem_L) (gen (Type200.k m) 2) = 0
        rw [cocycle_basisChange_gen2 E P Q h2P h2Q
          ((Type200.action m).φρ) (hL D.ρ_mem_L)
          (fun y hy => cocycleR_eq_zero_of_two_torsion he hf E hL hy)
          h2q']
        rw [show cocycle ((Type200.action m).φρ) E (hL D.ρ_mem_L)
          (gen (Type200.k m) 2) = q from rfl]
        have hρ2 : (Type200.action m).φρ (gen (Type200.k m) 2) =
            (-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
              (-1 : ℤ) • gen (Type200.k m) 2 := by
          simpa only [Torus.c, Torus.a, Torus.b] using Type200.rho_b m
        rw [hρ2, piBasis_apply_gens]
        have hφQ : (Type200.action m).φρ Q = a • eBasis m 0 + l • eBasis m 2 := by
          rw [hQ, map_add, map_zsmul, map_zsmul, phiR_eBasis_zero, phiR_eBasis_one]
        rw [hφQ, hq', hP, hQ]
        abel
    exact cocycle_eq_zero_of_gen_eq_zero (basisChange E P Q h2P h2Q)
      (hL D.ρ_mem_L) _ hgen

theorem two_pow_succ_gen0_eq_zero (m : ℕ) :
    (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 0 = 0 := by
  ext j
  fin_cases j
  · simp [gen, Pi.single_apply, nsmul_eq_mul]
    change (((2 : ℕ) : ZMod (2 ^ m)) ^ (m + 1) = 0)
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow 2 (Nat.le_succ m)
  · simp [gen, Pi.single_apply]
  · simp [gen, Pi.single_apply]

theorem phiUV_eBasis_one (m : ℕ) :
    (Type200.action m).φuv (eBasis m 1) = eBasis m 1 := by
  change Type200.PhiUV m ((2 ^ (m + 1) : ℕ) • gen (Type200.k m) 1) = eBasis m 1
  rw [← natCast_zsmul (gen (Type200.k m) 1) (2 ^ (m + 1))]
  rw [show ((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 1 =
      (0 : ℤ) • gen (Type200.k m) 0 + ((2 ^ (m + 1) : ℕ) : ℤ) •
        gen (Type200.k m) 1 + (0 : ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiUV_apply_gens]
  simp only [zero_mul, zero_add, mul_zero, add_zero]
  rw [show (2 * ((2 ^ (m + 1) : ℕ) : ℤ)) = ((2 ^ (m + 2) : ℕ) : ℤ) by
    push_cast; ring]
  have h₂ : (((2 ^ (m + 2) : ℕ) : ℤ) • gen (Type200.k m) 2) = 2 • eBasis m 2 := by
    rw [natCast_zsmul, eBasis_two, smul_smul,
      show 2 * 2 ^ (m + 1) = 2 ^ (m + 2) by ring]
  rw [h₂, eBasis_two_torsion, add_zero]
  have h₁ : (((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 1) = eBasis m 1 := by
    rw [natCast_zsmul]; exact (eBasis_one m).symm
  rw [h₁]
  rw [show (((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 0) =
      (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 0 by rw [natCast_zsmul]]
  rw [two_pow_succ_gen0_eq_zero m, zero_add]

theorem phiUV_eBasis_two (m : ℕ) :
    (Type200.action m).φuv (eBasis m 2) = eBasis m 2 := by
  change Type200.PhiUV m ((2 ^ (m + 1) : ℕ) • gen (Type200.k m) 2) = eBasis m 2
  rw [← natCast_zsmul (gen (Type200.k m) 2) (2 ^ (m + 1))]
  rw [show ((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 2 =
      (0 : ℤ) • gen (Type200.k m) 0 + (0 : ℤ) • gen (Type200.k m) 1 +
        ((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiUV_apply_gens]
  simp only [zero_mul, zero_add, mul_zero, add_zero]
  rw [show (((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 0) =
      (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 0 by rw [natCast_zsmul]]
  rw [two_pow_succ_gen0_eq_zero m, zero_add]
  rw [show (2 * ((2 ^ (m + 1) : ℕ) : ℤ)) = ((2 ^ (m + 2) : ℕ) : ℤ) by
    push_cast; ring]
  have h₁ : (((2 ^ (m + 2) : ℕ) : ℤ) • gen (Type200.k m) 1) = 2 • eBasis m 1 := by
    rw [natCast_zsmul, eBasis_one, smul_smul,
      show 2 * 2 ^ (m + 1) = 2 ^ (m + 2) by ring]
  rw [h₁, eBasis_two_torsion, zero_add]
  have h₂ : (((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 2) = eBasis m 2 := by
    rw [natCast_zsmul]; exact (eBasis_two m).symm
  rw [h₂]

theorem phiT_eBasis_one (m : ℕ) :
    (Type200.action m).φt (eBasis m 1) = eBasis m 1 := by
  change Type200.PhiT m ((2 ^ (m + 1) : ℕ) • gen (Type200.k m) 1) = eBasis m 1
  rw [← natCast_zsmul (gen (Type200.k m) 1) (2 ^ (m + 1))]
  rw [show ((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 1 =
      (0 : ℤ) • gen (Type200.k m) 0 + ((2 ^ (m + 1) : ℕ) : ℤ) •
        gen (Type200.k m) 1 + (0 : ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiT_apply_gens]
  simp only [zero_mul, zero_sub, mul_zero, add_zero, sub_zero]
  have h₁ : (((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 1) = eBasis m 1 := by
    rw [natCast_zsmul]; exact (eBasis_one m).symm
  rw [neg_smul, h₁]
  simp only [zero_smul, neg_zero, zero_add, add_zero]
  rw [neg_eq_iff_add_eq_zero]
  rw [← two_nsmul]; exact eBasis_two_torsion m 1

theorem phiT_eBasis_two (m : ℕ) :
    (Type200.action m).φt (eBasis m 2) = eBasis m 2 := by
  change Type200.PhiT m ((2 ^ (m + 1) : ℕ) • gen (Type200.k m) 2) = eBasis m 2
  rw [← natCast_zsmul (gen (Type200.k m) 2) (2 ^ (m + 1))]
  rw [show ((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 2 =
      (0 : ℤ) • gen (Type200.k m) 0 + (0 : ℤ) • gen (Type200.k m) 1 +
        ((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiT_apply_gens]
  simp only [zero_mul, zero_sub, mul_zero, add_zero, sub_zero]
  rw [neg_smul]
  rw [show (((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 0) =
      (2 ^ (m + 1) : ℕ) • gen (Type200.k m) 0 by rw [natCast_zsmul]]
  rw [two_pow_succ_gen0_eq_zero m, neg_zero, zero_add]
  rw [show (2 * ((2 ^ (m + 1) : ℕ) : ℤ)) = ((2 ^ (m + 2) : ℕ) : ℤ) by
    push_cast; ring]
  have h₁ : (((2 ^ (m + 2) : ℕ) : ℤ) • gen (Type200.k m) 1) = 2 • eBasis m 1 := by
    rw [natCast_zsmul, eBasis_one, smul_smul,
      show 2 * 2 ^ (m + 1) = 2 ^ (m + 2) by ring]
  rw [neg_smul, h₁, eBasis_two_torsion, neg_zero, zero_add]
  have h₂ : (((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 2) = eBasis m 2 := by
    rw [natCast_zsmul]; exact (eBasis_two m).symm
  rw [neg_smul, h₂]
  rw [neg_eq_iff_add_eq_zero]
  rw [← two_nsmul]; exact eBasis_two_torsion m 2

theorem four_mul_two_pow_pred (m : ℕ) (hm : 1 ≤ m) :
    (4 : ℕ) * 2 ^ (m - 1) = 2 ^ (m + 1) := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add,
    show 2 + (m - 1) = m + 1 by omega]

theorem phiUV_eBasis_zero (m : ℕ) (hm : 1 ≤ m) :
    (Type200.action m).φuv (eBasis m 0) =
      eBasis m 0 + eBasis m 1 + eBasis m 2 := by
  change Type200.PhiUV m ((2 ^ (m - 1) : ℕ) • gen (Type200.k m) 0) =
    eBasis m 0 + eBasis m 1 + eBasis m 2
  rw [← natCast_zsmul (gen (Type200.k m) 0) (2 ^ (m - 1))]
  rw [show ((2 ^ (m - 1) : ℕ) : ℤ) • gen (Type200.k m) 0 =
      ((2 ^ (m - 1) : ℕ) : ℤ) • gen (Type200.k m) 0 +
        (0 : ℤ) • gen (Type200.k m) 1 + (0 : ℤ) • gen (Type200.k m) 2 by simp]
  rw [Type200.PhiUV_apply_gens]
  simp only [zero_mul, zero_add, mul_zero, add_zero]
  have h4 : (4 : ℤ) * ((2 ^ (m - 1) : ℕ) : ℤ) = ((2 ^ (m + 1) : ℕ) : ℤ) := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, ← Nat.cast_mul,
      four_mul_two_pow_pred m hm]
  have h3 : ((-3 : ℤ) * ((2 ^ (m - 1) : ℕ) : ℤ)) =
      ((2 ^ (m - 1) : ℕ) : ℤ) - ((2 ^ (m + 1) : ℕ) : ℤ) := by
    rw [← h4]; ring
  have h4' : ((-4 : ℤ) * ((2 ^ (m - 1) : ℕ) : ℤ)) =
      -((2 ^ (m + 1) : ℕ) : ℤ) := by
    rw [← h4]; ring
  rw [h3, h4']
  have ha0 : ((2 ^ (m - 1) : ℕ) : ℤ) • gen (Type200.k m) 0 = eBasis m 0 := by
    rw [natCast_zsmul]; exact (eBasis_zero m).symm
  have hb0 : ((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 0 = 0 := by
    rw [natCast_zsmul]; exact two_pow_succ_gen0_eq_zero m
  have hb1 : ((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 1 = eBasis m 1 := by
    rw [natCast_zsmul]; exact (eBasis_one m).symm
  have hb2 : ((2 ^ (m + 1) : ℕ) : ℤ) • gen (Type200.k m) 2 = eBasis m 2 := by
    rw [natCast_zsmul]; exact (eBasis_two m).symm
  have hterm0 : (((2 ^ (m - 1) : ℕ) : ℤ) - ((2 ^ (m + 1) : ℕ) : ℤ)) •
      gen (Type200.k m) 0 = eBasis m 0 := by
    rw [sub_smul, ha0, hb0, sub_zero]
  have hterm1 : (-((2 ^ (m + 1) : ℕ) : ℤ)) • gen (Type200.k m) 1 = eBasis m 1 := by
    rw [neg_smul, hb1]
    rw [neg_eq_iff_add_eq_zero]
    rw [← two_nsmul]; exact eBasis_two_torsion m 1
  have hterm2 : (-((2 ^ (m + 1) : ℕ) : ℤ)) • gen (Type200.k m) 2 = eBasis m 2 := by
    rw [neg_smul, hb2]
    rw [neg_eq_iff_add_eq_zero]
    rw [← two_nsmul]; exact eBasis_two_torsion m 2
  rw [hterm0, hterm1, hterm2]

end TorusBasisEquivFour

end CFSG.CGT.Stroth77
