module

public import CFSG.CGT.Stroth77.Extension22FourClassify2
public import CFSG.CGT.Stroth77.Extension22FourC4

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ}

namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}
  (E : TorusBasisEquivFour D hBC e f)

theorem conjTorusFour_comp_apply {g h : S}
    (hg : g ∈ Subgroup.normalizer C) (hh : h ∈ Subgroup.normalizer C)
    (x : Torus (Type200.k m)) :
    conjTorusFour D hBC E hg (conjTorusFour D hBC E hh x) =
      conjTorusFour D hBC E (Subgroup.mul_mem _ hh hg) x := by
  rw [conjTorusFour_apply, conjTorusFour_apply, conjTorusFour_apply]
  rw [AddEquiv.apply_symm_apply]
  congr 1
  exact (DFunLike.congr_fun (conjByHom_mul h g hh hg)
    (Additive.toMul (E.E x))).symm

theorem conjTorusFour_congr {g g' : S}
    (hg : g ∈ Subgroup.normalizer C) (hg' : g' ∈ Subgroup.normalizer C) (h : g = g') :
    conjTorusFour D hBC E hg = conjTorusFour D hBC E hg' := by
  subst h
  rfl

theorem conjTorusFour_one_apply (x : Torus (Type200.k m)) :
    conjTorusFour (C := C) (D := D) (hBC := hBC) (E := E)
      (Subgroup.one_mem _) x = x := by
  rw [conjTorusFour_apply]
  simp [conjBy]

theorem conjTorusFour_one :
    conjTorusFour (C := C) (D := D) (hBC := hBC) (E := E) (Subgroup.one_mem _) =
      AddEquiv.refl (Torus (Type200.k m)) := by
  refine AddEquiv.ext fun x => ?_
  exact conjTorusFour_one_apply E x

theorem conjTorusFour_mul_hom {g h : S}
    (hg : g ∈ Subgroup.normalizer C) (hh : h ∈ Subgroup.normalizer C) :
    (conjTorusFour D hBC E (Subgroup.mul_mem _ hg hh)).toAddMonoidHom =
      (conjTorusFour D hBC E hh).toAddMonoidHom.comp
        (conjTorusFour D hBC E hg).toAddMonoidHom := by
  refine AddMonoidHom.ext fun x => ?_
  exact (conjTorusFour_comp_apply E hh hg x).symm

theorem conjTorusFour_rels
    (hL : D.L ≤ Subgroup.normalizer C) :
    SigmaFourRels (A := Torus (Type200.k m))
      (conjTorusFour D hBC E (hL D.uv_mem_L)).toAddMonoidHom
      (conjTorusFour D hBC E (hL D.t_mem_L)).toAddMonoidHom
      (conjTorusFour D hBC E (hL D.u_mem_L)).toAddMonoidHom
      (conjTorusFour D hBC E (hL D.ρ_mem_L)).toAddMonoidHom := by
  have huv := hL D.uv_mem_L
  have ht := hL D.t_mem_L
  have hu := hL D.u_mem_L
  have hρ := hL D.ρ_mem_L
  have H {a b : S} (ha : a ∈ Subgroup.normalizer C) (hb : b ∈ Subgroup.normalizer C)
      (h : a = b) :
      (conjTorusFour D hBC E ha).toAddMonoidHom =
        (conjTorusFour D hBC E hb).toAddMonoidHom :=
    congrArg AddEquiv.toAddMonoidHom (conjTorusFour_congr E ha hb h)
  have Hone {a : S} (ha : a ∈ Subgroup.normalizer C) (h : a = 1) :
      (conjTorusFour D hBC E ha).toAddMonoidHom = AddMonoidHom.id _ := by
    trans (conjTorusFour D hBC E (Subgroup.one_mem _)).toAddMonoidHom
    · exact H ha (Subgroup.one_mem _) h
    · exact congrArg AddEquiv.toAddMonoidHom (conjTorusFour_one E)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← conjTorusFour_mul_hom (E := E) (g := D.uv) (h := D.uv) huv huv]
    exact Hone (Subgroup.mul_mem _ huv huv) D.uv_sq
  · rw [← conjTorusFour_mul_hom (E := E) (g := D.t) (h := D.t) ht ht]
    exact Hone (Subgroup.mul_mem _ ht ht) D.t_sq
  · rw [← conjTorusFour_mul_hom (E := E) (g := D.uv) (h := D.t) huv ht,
      ← conjTorusFour_mul_hom (E := E) (g := D.t) (h := D.uv) ht huv]
    exact H (Subgroup.mul_mem _ huv ht) (Subgroup.mul_mem _ ht huv) D.uv_comm_t
  · rw [← conjTorusFour_mul_hom (E := E) (g := D.ρ) (h := D.ρ) hρ hρ,
      ← conjTorusFour_mul_hom (E := E) (g := D.ρ * D.ρ) (h := D.ρ)
        (Subgroup.mul_mem _ hρ hρ) hρ]
    exact Hone (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρ hρ) hρ) D.rho_cube
  · rw [← conjTorusFour_mul_hom (E := E) (g := D.u) (h := D.u) hu hu]
    exact Hone (Subgroup.mul_mem _ hu hu) D.u_sq
  · rw [← conjTorusFour_mul_hom (E := E) (g := D.u) (h := D.ρ) hu hρ,
      ← conjTorusFour_mul_hom (E := E) (g := D.u * D.ρ) (h := D.u)
        (Subgroup.mul_mem _ hu hρ) hu,
      ← conjTorusFour_mul_hom (E := E) (g := (D.u * D.ρ) * D.u) (h := D.ρ)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hρ) hu) hρ]
    exact Hone (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hρ) hu) hρ)
      D.u_rho
  · rw [← conjTorusFour_mul_hom (E := E) (g := D.uv) (h := D.ρ) huv hρ,
      ← conjTorusFour_mul_hom (E := E) (g := D.ρ) (h := D.t) hρ ht]
    exact H (Subgroup.mul_mem _ huv hρ) (Subgroup.mul_mem _ hρ ht) D.uv_rho
  · rw [← conjTorusFour_mul_hom (E := E) (g := D.t) (h := D.ρ) ht hρ,
      ← conjTorusFour_mul_hom (E := E) (g := D.ρ) (h := D.uv) hρ huv,
      ← conjTorusFour_mul_hom (E := E) (g := D.ρ * D.uv) (h := D.t)
        (Subgroup.mul_mem _ hρ huv) ht]
    exact H (Subgroup.mul_mem _ ht hρ)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρ huv) ht) D.t_rho
  · rw [← conjTorusFour_mul_hom (E := E) (g := D.uv) (h := D.u) huv hu,
      ← conjTorusFour_mul_hom (E := E) (g := D.u) (h := D.uv) hu huv]
    exact H (Subgroup.mul_mem _ huv hu) (Subgroup.mul_mem _ hu huv) D.uv_comm_u
  · rw [← conjTorusFour_mul_hom (E := E) (g := D.t) (h := D.u) ht hu,
      ← conjTorusFour_mul_hom (E := E) (g := D.u) (h := D.uv) hu huv,
      ← conjTorusFour_mul_hom (E := E) (g := D.u * D.uv) (h := D.t)
        (Subgroup.mul_mem _ hu huv) ht]
    exact H (Subgroup.mul_mem _ ht hu)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu huv) ht) D.t_u

section BasisChange

variable {p w : Torus (Type200.k m)} (h2p : 2 • p = 0) (h2w : 2 • w = 0)

theorem two_pow_succ_nsmul_eq_zero {x : Torus (Type200.k m)} (h : 2 • x = 0) (n : ℕ) :
    (2 ^ (n + 1) : ℕ) • x = 0 := by
  rw [show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 by ring, mul_smul, h, smul_zero]

theorem two_pow_smul_eq_zero {x : Torus (Type200.k m)} (h : 2 • x = 0) (n : ℕ)
    (hn : 1 ≤ n) : ((2 ^ n : ℕ) : ℤ) • x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using two_pow_succ_nsmul_eq_zero h k

@[expose] noncomputable def piBasis : Torus (Type200.k m) →+ Torus (Type200.k m) :=
  torusHomOfGens (Type200.k m) ![0, p, w] (by
    intro i
    fin_cases i
    · simp
    · simpa [show Type200.k m 1 = m + 2 by simp [Type200.k]] using
        two_pow_succ_nsmul_eq_zero h2p (m + 1)
    · simpa [show Type200.k m 2 = m + 2 by simp [Type200.k]] using
        two_pow_succ_nsmul_eq_zero h2w (m + 1))

@[simp]
theorem piBasis_gen0 : piBasis h2p h2w (gen (Type200.k m) 0) = 0 := by
  rw [piBasis, torusHomOfGens_gen]
  rfl

@[simp]
theorem piBasis_gen1 : piBasis h2p h2w (gen (Type200.k m) 1) = p := by
  rw [piBasis, torusHomOfGens_gen]
  rfl

@[simp]
theorem piBasis_gen2 : piBasis h2p h2w (gen (Type200.k m) 2) = w := by
  rw [piBasis, torusHomOfGens_gen]
  rfl

theorem piBasis_apply_gens (i j l : ℤ) :
    piBasis h2p h2w (i • gen (Type200.k m) 0 + j • gen (Type200.k m) 1 +
        l • gen (Type200.k m) 2) = j • p + l • w := by
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, piBasis_gen0, piBasis_gen1,
    piBasis_gen2]
  simp

theorem piBasis_two_smul (x : Torus (Type200.k m)) :
    2 • piBasis h2p h2w x = 0 := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type200.k m) x
  rw [piBasis_apply_gens, smul_add]
  rw [smul_comm (2 : ℕ) j p, smul_comm (2 : ℕ) l w]
  rw [h2p, h2w, smul_zero, smul_zero, add_zero]

theorem piBasis_add_self (x : Torus (Type200.k m)) :
    piBasis h2p h2w x + piBasis h2p h2w x = 0 := by
  rw [← two_nsmul]
  exact piBasis_two_smul h2p h2w x

theorem piBasis_two_torsion_eq_zero {x : Torus (Type200.k m)} (hx : 2 • x = 0) :
    piBasis h2p h2w x = 0 := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type200.k m) x
  rw [piBasis_apply_gens]
  have hx' : (2 : ℤ) • (i • gen (Type200.k m) 0 + j • gen (Type200.k m) 1 +
      l • gen (Type200.k m) 2) = 0 := by
    simpa [two_zsmul] using hx
  rw [zsmul_gens] at hx'
  have h2j : 2 * (j : ZMod (2 ^ (m + 2))) = 0 := by
    have h := gens_coord_one_of_eq_zero hx'
    rw [show Type200.k m 1 = m + 2 by simp [Type200.k]] at h
    simpa [Int.cast_mul] using h
  have h2l : 2 * (l : ZMod (2 ^ (m + 2))) = 0 := by
    have h := gens_coord_two_of_eq_zero hx'
    rw [show Type200.k m 2 = m + 2 by simp [Type200.k]] at h
    simpa [Int.cast_mul] using h
  have hk : 1 ≤ m + 2 := by omega
  have hj_dvd : ((2 ^ (m + 1) : ℕ) : ℤ) ∣ j := by
    have h := dvd_two_mul_of_two_mul_cast_eq_zero h2j
    exact dvd_of_dvd_two_mul (k := m + 1) (by
      simpa [show m + 2 = (m + 1) + 1 by omega] using h)
  have hl_dvd : ((2 ^ (m + 1) : ℕ) : ℤ) ∣ l := by
    have h := dvd_two_mul_of_two_mul_cast_eq_zero h2l
    exact dvd_of_dvd_two_mul (k := m + 1) (by
      simpa [show m + 2 = (m + 1) + 1 by omega] using h)
  obtain ⟨k, hk⟩ := hj_dvd
  obtain ⟨q, hq⟩ := hl_dvd
  have hj0 : j • p = 0 := by
    rw [hk, mul_comm, mul_zsmul, two_pow_smul_eq_zero h2p (m + 1) (by omega),
      smul_zero]
  have hl0 : l • w = 0 := by
    rw [hq, mul_comm, mul_zsmul, two_pow_smul_eq_zero h2w (m + 1) (by omega),
      smul_zero]
  rw [hj0, hl0, add_zero]

theorem piBasis_comp_self (x : Torus (Type200.k m)) :
    piBasis h2p h2w (piBasis h2p h2w x) = 0 :=
  piBasis_two_torsion_eq_zero h2p h2w (piBasis_two_smul h2p h2w x)

@[expose] noncomputable def psiBasis : Torus (Type200.k m) ≃+ Torus (Type200.k m) where
  toFun x := x + piBasis h2p h2w x
  invFun x := x + piBasis h2p h2w x
  left_inv x := by
    show (x + piBasis h2p h2w x) + piBasis h2p h2w (x + piBasis h2p h2w x) = x
    rw [map_add, piBasis_comp_self, add_zero, add_assoc, piBasis_add_self, add_zero]
  right_inv x := by
    show (x + piBasis h2p h2w x) + piBasis h2p h2w (x + piBasis h2p h2w x) = x
    rw [map_add, piBasis_comp_self, add_zero, add_assoc, piBasis_add_self, add_zero]
  map_add' x y := by
    show (x + y) + piBasis h2p h2w (x + y) =
      (x + piBasis h2p h2w x) + (y + piBasis h2p h2w y)
    rw [map_add]
    abel

@[simp]
theorem psiBasis_apply (x : Torus (Type200.k m)) :
    psiBasis h2p h2w x = x + piBasis h2p h2w x := rfl

theorem psiBasis_apply_self (x : Torus (Type200.k m)) :
    psiBasis h2p h2w (psiBasis h2p h2w x) = x := by
  rw [psiBasis_apply, psiBasis_apply, map_add, piBasis_comp_self, add_zero,
    add_assoc, piBasis_add_self, add_zero]

theorem psiBasis_gen0 : psiBasis h2p h2w (gen (Type200.k m) 0) = gen (Type200.k m) 0 := by
  rw [psiBasis_apply, piBasis_gen0, add_zero]

theorem psiBasis_gen1 : psiBasis h2p h2w (gen (Type200.k m) 1) = gen (Type200.k m) 1 + p := by
  rw [psiBasis_apply, piBasis_gen1]

theorem psiBasis_gen2 : psiBasis h2p h2w (gen (Type200.k m) 2) = gen (Type200.k m) 2 + w := by
  rw [psiBasis_apply, piBasis_gen2]

end BasisChange

theorem hom_eq_piBasis {δ : Torus (Type200.k m) →+ Torus (Type200.k m)}
    (h0 : δ (gen (Type200.k m) 0) = 0)
    (h2p : 2 • δ (gen (Type200.k m) 1) = 0)
    (h2w : 2 • δ (gen (Type200.k m) 2) = 0) :
    δ = piBasis h2p h2w := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type200.k m) x
  rw [piBasis_apply_gens, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, h0]
  simp

theorem hom_two_torsion_eq_zero {δ : Torus (Type200.k m) →+ Torus (Type200.k m)}
    (h0 : δ (gen (Type200.k m) 0) = 0)
    (h2p : 2 • δ (gen (Type200.k m) 1) = 0)
    (h2w : 2 • δ (gen (Type200.k m) 2) = 0)
    {x : Torus (Type200.k m)} (hx : 2 • x = 0) : δ x = 0 := by
  rw [hom_eq_piBasis h0 h2p h2w]
  exact piBasis_two_torsion_eq_zero h2p h2w hx



theorem cocycleU_involution (E : TorusBasisEquivFour D hBC e f)
    (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (x : Torus (Type200.k m)) :
    cocycleU E hL ((Type200.action m).φu x) +
      (Type200.action m).φu (cocycleU E hL x) = 0 := by
  let p : Torus (Type200.k m) := cocycleU E hL (gen (Type200.k m) 1)
  let q : Torus (Type200.k m) := cocycleU E hL (gen (Type200.k m) 2)
  have h2p : 2 • p = 0 := by
    simpa [p] using cocycleU_two_gen1 he hf E hL
  have h2q : 2 • q = 0 := by
    simpa [q] using cocycleU_two_gen2 he hf E hL
  have hδeq : cocycleU E hL = piBasis h2p h2q :=
    hom_eq_piBasis (cocycleU_gen0 he hf E hL) (by simpa [p] using h2p)
      (by simpa [q] using h2q)
  have hδself : cocycleU E hL (cocycleU E hL x) = 0 := by
    refine hom_two_torsion_eq_zero (δ := cocycleU E hL)
      (cocycleU_gen0 he hf E hL) (by simpa [p] using h2p)
      (by simpa [q] using h2q) ?_
    rw [hδeq]
    exact piBasis_two_smul h2p h2q x
  have hβ2 : (Type200.action m).φu ((Type200.action m).φu x) = x := by
    have h := congrArg (fun f => f x) (Type200.action m).rels.u_sq
    simpa [AddMonoidHom.comp_apply] using h
  have hα2 := congrArg (fun f => f x) (conjTorusFour_rels (E := E) hL).u_sq
  change conjTorusFour D hBC E (hL D.u_mem_L)
      (conjTorusFour D hBC E (hL D.u_mem_L) x) = x at hα2
  rw [action_eq_printed_add_cocycle (E := E) (hL D.u_mem_L)
    ((Type200.action m).φu)] at hα2
  rw [action_eq_printed_add_cocycle (E := E) (hL D.u_mem_L)
    ((Type200.action m).φu)] at hα2
  rw [map_add, map_add, hβ2] at hα2
  change x + (Type200.action m).φu (cocycleU E hL x) +
      (cocycleU E hL ((Type200.action m).φu x) +
        cocycleU E hL (cocycleU E hL x)) = x at hα2
  rw [hδself, add_zero] at hα2
  have h' : (Type200.action m).φu (cocycleU E hL x) +
      cocycleU E hL ((Type200.action m).φu x) = 0 := by
    apply add_left_cancel (a := x)
    simpa [add_assoc] using hα2
  rwa [add_comm] at h'

theorem cocycleU_gen2_eq (E : TorusBasisEquivFour D hBC e f)
    (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    cocycleU E hL (gen (Type200.k m) 2) =
      (Type200.action m).φu (cocycleU E hL (gen (Type200.k m) 1)) := by
  have h := cocycleU_involution E hL he hf (gen (Type200.k m) 2)
  rw [show (Type200.action m).φu (gen (Type200.k m) 2) = gen (Type200.k m) 1 from by
    simpa [Torus.b] using Type200.u_b m] at h
  have hp2 : cocycleU E hL (gen (Type200.k m) 1) +
      cocycleU E hL (gen (Type200.k m) 1) = 0 := by
    let p : Torus (Type200.k m) := cocycleU E hL (gen (Type200.k m) 1)
    have h2p : 2 • p = 0 := by
      simpa [p] using cocycleU_two_gen1 he hf E hL
    rw [← two_nsmul]
    exact h2p
  have hφ : (Type200.action m).φu (cocycleU E hL (gen (Type200.k m) 2)) =
      cocycleU E hL (gen (Type200.k m) 1) := by
    have h' := h
    rw [add_comm] at h'
    have hneg := eq_neg_of_add_eq_zero_left h'
    rwa [neg_eq_iff_add_eq_zero.mpr hp2] at hneg
  have hinv : (Type200.action m).φu ((Type200.action m).φu
      (cocycleU E hL (gen (Type200.k m) 2))) =
      cocycleU E hL (gen (Type200.k m) 2) := by
    have h := congrArg (fun f => f (cocycleU E hL (gen (Type200.k m) 2)))
      (Type200.action m).rels.u_sq
    simpa [AddMonoidHom.comp_apply] using h
  calc cocycleU E hL (gen (Type200.k m) 2)
      = (Type200.action m).φu ((Type200.action m).φu
          (cocycleU E hL (gen (Type200.k m) 2))) := hinv.symm
    _ = (Type200.action m).φu (cocycleU E hL (gen (Type200.k m) 1)) := by rw [hφ]

section UNormalize

variable (hL : D.L ≤ Subgroup.normalizer C)
  (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) (hm : 1 ≤ m)

theorem exists_u_normalized (E : TorusBasisEquivFour D hBC e f)
    (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hm : 1 ≤ m) :
    ∃ z w : C, z * z = 1 ∧ w * w = 1 ∧
      ∃ E1 : TorusBasisEquivFour D hBC (e * z) (f * w), cocycleU E1 hL = 0 := by
  classical
  let p : Torus (Type200.k m) := cocycleU E hL (gen (Type200.k m) 1)
  have h2p : 2 • p = 0 := by
    simpa using cocycleU_two_gen1 he hf E hL
  let q : Torus (Type200.k m) := p + (Type200.action m).φu p
  have h2q : 2 • q = 0 := by
    change 2 • (p + (Type200.action m).φu p) = 0
    rw [smul_add, h2p]
    rw [show (2 : ℕ) • (Type200.action m).φu p =
      (Type200.action m).φu (2 • p) by rw [map_nsmul], h2p, map_zero, add_zero]
  let π : Torus (Type200.k m) →+ Torus (Type200.k m) := piBasis h2p h2q
  have hpπ : p = π (gen (Type200.k m) 1) :=
    (piBasis_gen1 (p := p) (w := q) h2p h2q).symm
  have hqπ : q = π (gen (Type200.k m) 2) :=
    (piBasis_gen2 (p := p) (w := q) h2p h2q).symm
  let ψ : Torus (Type200.k m) ≃+ Torus (Type200.k m) := psiBasis h2p h2q
  let z : C := Additive.toMul (E.E (π (gen (Type200.k m) 1)))
  let w : C := Additive.toMul (E.E (π (gen (Type200.k m) 2)))
  have hz : z * z = 1 := by
    apply Additive.ofMul.injective
    change Additive.ofMul (z * z) = Additive.ofMul (1 : C)
    rw [ofMul_mul, ofMul_one]
    have h : (2 : ℕ) • (E.E (π (gen (Type200.k m) 1))) = 0 := by
      rw [← map_nsmul]
      rw [show (2 : ℕ) • π (gen (Type200.k m) 1) = 0 from piBasis_two_smul h2p h2q _]
      simp
    rw [show E.E (π (gen (Type200.k m) 1)) = Additive.ofMul z from rfl] at h
    rwa [two_nsmul] at h
  have hw : w * w = 1 := by
    apply Additive.ofMul.injective
    change Additive.ofMul (w * w) = Additive.ofMul (1 : C)
    rw [ofMul_mul, ofMul_one]
    have h : (2 : ℕ) • (E.E (π (gen (Type200.k m) 2))) = 0 := by
      rw [← map_nsmul]
      rw [show (2 : ℕ) • π (gen (Type200.k m) 2) = 0 from piBasis_two_smul h2p h2q _]
      simp
    rw [show E.E (π (gen (Type200.k m) 2)) = Additive.ofMul w from rfl] at h
    rwa [two_nsmul] at h
  have hδp : cocycleU E hL p = 0 := by
    refine hom_two_torsion_eq_zero (δ := cocycleU E hL)
      (cocycleU_gen0 he hf E hL) ?_ ?_ h2p
    · have h := cocycleU_two_gen1 he hf E hL
      simpa [two_zsmul] using h
    · have h := cocycleU_two_gen2 he hf E hL
      simpa [two_zsmul] using h
  have hδq : cocycleU E hL q = 0 := by
    refine hom_two_torsion_eq_zero (δ := cocycleU E hL)
      (cocycleU_gen0 he hf E hL) ?_ ?_ h2q
    · have h := cocycleU_two_gen1 he hf E hL
      simpa [two_zsmul] using h
    · have h := cocycleU_two_gen2 he hf E hL
      simpa [two_zsmul] using h
  have hδ2 : cocycleU E hL (gen (Type200.k m) 2) = (Type200.action m).φu p := by
    have h := cocycleU_gen2_eq E hL he hf
    rwa [show cocycleU E hL (gen (Type200.k m) 1) = p from rfl] at h
  let E1 : TorusBasisEquivFour D hBC (e * z) (f * w) :=
    { E := ψ.trans E.E
      E_gen0 := by
        rw [AddEquiv.trans_apply]
        change E.E (ψ (gen (Type200.k m) 0)) = _
        rw [psiBasis_gen0]
        exact E.E_gen0
      E_gen1 := by
        rw [AddEquiv.trans_apply]
        change E.E (ψ (gen (Type200.k m) 1)) = Additive.ofMul (e * z)
        rw [psiBasis_gen1]
        change E.E (gen (Type200.k m) 1 + p) = Additive.ofMul (e * z)
        rw [map_add, E.E_gen1, ofMul_mul]
        have hzp : Additive.ofMul z = E.E p := by
          rw [show z = Additive.toMul (E.E p) from by
            rw [show p = π (gen (Type200.k m) 1) from
              (piBasis_gen1 (p := p) (w := q) h2p h2q).symm]]
          exact ofMul_toMul _
        rw [hzp]
      E_gen2 := by
        rw [AddEquiv.trans_apply]
        change E.E (ψ (gen (Type200.k m) 2)) = Additive.ofMul (f * w)
        rw [psiBasis_gen2]
        change E.E (gen (Type200.k m) 2 + q) = Additive.ofMul (f * w)
        rw [map_add, E.E_gen2, ofMul_mul]
        have hzq : Additive.ofMul w = E.E q := by
          rw [show w = Additive.toMul (E.E q) from by
            rw [show q = π (gen (Type200.k m) 2) from
              (piBasis_gen2 (p := p) (w := q) h2p h2q).symm]]
          exact ofMul_toMul _
        rw [hzq] }
  have hψsymm : ψ.symm = ψ := by
    refine AddEquiv.ext fun x => ?_
    have hx : ψ (ψ x) = x := psiBasis_apply_self h2p h2q x
    calc ψ.symm x = ψ.symm (ψ (ψ x)) := by rw [hx]
      _ = ψ x := AddEquiv.symm_apply_apply ψ (ψ x)
  have hE1symm : E1.E.symm = E.E.symm.trans ψ := by
    rw [show E1.E = ψ.trans E.E from rfl]
    rw [show (ψ.trans E.E).symm = E.E.symm.trans ψ.symm from rfl, hψsymm]
  have hconj : ∀ x, conjTorusFour D hBC E1 (hL D.u_mem_L) x =
      ψ (conjTorusFour D hBC E (hL D.u_mem_L) (ψ x)) := by
    intro x
    rw [conjTorusFour_apply, conjTorusFour_apply, hE1symm]
    rw [AddEquiv.trans_apply]
    change ψ (E.E.symm (Additive.ofMul (conjBy _ (Additive.toMul (E.E (ψ x)))))) =
      ψ (E.E.symm (Additive.ofMul (conjBy _ (Additive.toMul (E.E (ψ x))))))
    rfl
  have hψ_gen2 : ψ (gen (Type200.k m) 2 + q) = gen (Type200.k m) 2 := by
    rw [map_add, psiBasis_gen2, psiBasis_apply]
    rw [show π q = 0 from piBasis_two_torsion_eq_zero h2p h2q h2q, add_zero]
    rw [add_assoc, show q + q = 0 from by rw [hqπ]; exact piBasis_add_self h2p h2q (gen (Type200.k m) 2), add_zero]
  have hψ_gen1 : ψ (gen (Type200.k m) 1 + p) = gen (Type200.k m) 1 := by
    rw [map_add, psiBasis_gen1, psiBasis_apply]
    rw [show π p = 0 from piBasis_two_torsion_eq_zero h2p h2q h2p, add_zero]
    rw [add_assoc, show p + p = 0 from by rw [hpπ]; exact piBasis_add_self h2p h2q (gen (Type200.k m) 1), add_zero]
  have hαq : conjTorusFour D hBC E (hL D.u_mem_L) q = (Type200.action m).φu p + p := by
    rw [action_eq_printed_add_cocycle (E := E) (hL D.u_mem_L)
      ((Type200.action m).φu)]
    change (Type200.action m).φu q + cocycleU E hL q = (Type200.action m).φu p + p
    rw [hδq, add_zero]
    rw [show q = p + (Type200.action m).φu p from rfl, map_add]
    rw [show (Type200.action m).φu ((Type200.action m).φu p) = p from by
      have h := congrArg (fun f => f p) (Type200.action m).rels.u_sq
      simpa [AddMonoidHom.comp_apply] using h]
  have hα2 : conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) 2) + q =
      gen (Type200.k m) 1 + p := by
    rw [action_eq_printed_add_cocycle (E := E) (hL D.u_mem_L)
      ((Type200.action m).φu)]
    rw [show (Type200.action m).φu (gen (Type200.k m) 2) = gen (Type200.k m) 1 from by
      simpa [Torus.b] using Type200.u_b m]
    change gen (Type200.k m) 1 + cocycleU E hL (gen (Type200.k m) 2) + q =
      gen (Type200.k m) 1 + p
    rw [hδ2, show q = p + (Type200.action m).φu p from rfl]
    have hβ2 : (Type200.action m).φu p + (Type200.action m).φu p = 0 := by
      rw [← two_nsmul, ← map_nsmul, h2p, map_zero]
    calc gen (Type200.k m) 1 + (Type200.action m).φu p +
          (p + (Type200.action m).φu p)
        = gen (Type200.k m) 1 + p +
          ((Type200.action m).φu p + (Type200.action m).φu p) := by abel
      _ = gen (Type200.k m) 1 + p + 0 := by rw [hβ2]
      _ = gen (Type200.k m) 1 + p := add_zero _
  have hα_gen1 : conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) 1 + p) =
      gen (Type200.k m) 2 + q := by
    rw [map_add, action_eq_printed_add_cocycle (E := E) (hL D.u_mem_L)
      ((Type200.action m).φu)]
    rw [show cocycle (Type200.action m).φu E (hL D.u_mem_L)
      (gen (Type200.k m) 1) = p from rfl,
      action_eq_printed_add_cocycle (E := E) (hL D.u_mem_L)
        ((Type200.action m).φu)]
    change (Type200.action m).φu (gen (Type200.k m) 1) + p +
      ((Type200.action m).φu p + cocycleU E hL p) = gen (Type200.k m) 2 + q
    rw [hδp, add_zero, Type200.u_a]
    rw [show q = p + (Type200.action m).φu p from rfl]
    abel
  have hα_gen2 : conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) 2 + q) =
      gen (Type200.k m) 1 + p := by
    rw [map_add, action_eq_printed_add_cocycle (E := E) (hL D.u_mem_L)
      ((Type200.action m).φu)]
    rw [show cocycle (Type200.action m).φu E (hL D.u_mem_L)
      (gen (Type200.k m) 2) = (Type200.action m).φu p from hδ2]
    rw [action_eq_printed_add_cocycle (E := E) (hL D.u_mem_L)
      ((Type200.action m).φu)]
    change (Type200.action m).φu (gen (Type200.k m) 2) +
      (Type200.action m).φu p +
      ((Type200.action m).φu q + cocycleU E hL q) = gen (Type200.k m) 1 + p
    rw [hδq, add_zero]
    rw [show (Type200.action m).φu (gen (Type200.k m) 2) = gen (Type200.k m) 1 from by
      simpa [Torus.b] using Type200.u_b m]
    rw [show q = p + (Type200.action m).φu p from rfl, map_add]
    rw [show (Type200.action m).φu ((Type200.action m).φu p) = p from by
      have h := congrArg (fun f => f p) (Type200.action m).rels.u_sq
      simpa [AddMonoidHom.comp_apply] using h]
    have hβ2 : (Type200.action m).φu p + (Type200.action m).φu p = 0 := by
      rw [← two_nsmul, ← map_nsmul, h2p, map_zero]
    calc gen (Type200.k m) 1 + (Type200.action m).φu p +
          ((Type200.action m).φu p + p)
        = gen (Type200.k m) 1 + p +
          ((Type200.action m).φu p + (Type200.action m).φu p) := by abel
      _ = gen (Type200.k m) 1 + p + 0 := by rw [hβ2]
      _ = gen (Type200.k m) 1 + p := add_zero _
  have hgen : ∀ j : Fin 3, cocycleU E1 hL (gen (Type200.k m) j) = 0 := by
    intro j
    fin_cases j
    · change conjTorusFour D hBC E1 (hL D.u_mem_L) (gen (Type200.k m) 0) -
        (Type200.action m).φu (gen (Type200.k m) 0) = 0
      rw [hconj, psiBasis_gen0]
      rw [action_eq_printed_add_cocycle (E := E) (hL D.u_mem_L)
        ((Type200.action m).φu)]
      change ψ ((Type200.action m).φu (gen (Type200.k m) 0) +
        cocycleU E hL (gen (Type200.k m) 0)) -
        (Type200.action m).φu (gen (Type200.k m) 0) = 0
      rw [cocycleU_gen0 he hf E hL, add_zero]
      rw [show (Type200.action m).φu (gen (Type200.k m) 0) = gen (Type200.k m) 0 from
        by simpa [Torus.c] using Type200.u_c m]
      rw [psiBasis_gen0, sub_self]
    · change conjTorusFour D hBC E1 (hL D.u_mem_L) (gen (Type200.k m) 1) -
        (Type200.action m).φu (gen (Type200.k m) 1) = 0
      rw [hconj]
      rw [show ψ (gen (Type200.k m) 1) = gen (Type200.k m) 1 + p from
        psiBasis_gen1 h2p h2q]
      rw [show conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) 1 + p) =
        gen (Type200.k m) 2 + q from hα_gen1]
      rw [hψ_gen2]
      rw [show (Type200.action m).φu (gen (Type200.k m) 1) = gen (Type200.k m) 2 from
        by simpa [Torus.a] using Type200.u_a m]
      rw [sub_self]
    · change conjTorusFour D hBC E1 (hL D.u_mem_L) (gen (Type200.k m) 2) -
        (Type200.action m).φu (gen (Type200.k m) 2) = 0
      rw [hconj]
      rw [show ψ (gen (Type200.k m) 2) = gen (Type200.k m) 2 + q from
        psiBasis_gen2 h2p h2q]
      rw [show conjTorusFour D hBC E (hL D.u_mem_L) (gen (Type200.k m) 2 + q) =
        gen (Type200.k m) 1 + p from hα_gen2]
      rw [hψ_gen1]
      rw [show (Type200.action m).φu (gen (Type200.k m) 2) = gen (Type200.k m) 1 from by
        simpa [Torus.b] using Type200.u_b m]
      rw [sub_self]
  exact ⟨z, w, hz, hw, E1, by
    change cocycleU E1 hL = 0
    exact cocycle_eq_zero_of_gen_eq_zero E1 (hL D.u_mem_L) _ hgen⟩




end UNormalize

end TorusBasisEquivFour

end CFSG.CGT.Stroth77
