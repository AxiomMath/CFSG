module

public import CFSG.GH74.Tits83.DesignC.Induction
public import CFSG.GH74.Tits83.Windows

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

section Collection

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

variable {G G' : Type u} [Group G] [Group G']
variable {T : TitsSystem G 8} {T' : TitsSystem G' 8}
variable (c : OctCoord T.U) (c' : OctCoord T'.U) (θ : c.K ≃+* c'.K)

theorem Delta_le_prod (k : ℤ) :
    Delta c c' θ k ≤ (T.U k).prod (T'.U k) := by
  rw [Delta]
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  rcases hx with ⟨t, rfl⟩ | ⟨hk, t, rfl⟩
  · exact Subgroup.mem_prod.2 ⟨c.X_mem k t, c'.X_mem k (θ t)⟩
  · exact Subgroup.mem_prod.2 ⟨c.X'_mem k t hk, c'.X'_mem k (θ t) hk⟩

theorem Delta_fst_mem {k : ℤ} {x : G × G'} (hx : x ∈ Delta c c' θ k) : x.1 ∈ T.U k :=
  (Subgroup.mem_prod.1 (Delta_le_prod c c' θ k hx)).1

theorem Delta_snd_mem {k : ℤ} {x : G × G'} (hx : x ∈ Delta c c' θ k) : x.2 ∈ T'.U k :=
  (Subgroup.mem_prod.1 (Delta_le_prod c c' θ k hx)).2

@[expose] def Gamma : Subgroup (G × G') :=
  ⨆ k ∈ intList 1 8, Delta c c' θ k

theorem DeltaWin_le_iSup {i j : ℤ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ 8) :
    DeltaWin c c' θ i j ≤ ⨆ k ∈ intList 1 8, ⨆ (_ : i < k), Delta c c' θ k := by
  rw [DeltaWin]
  refine iSup₂_le fun k hk => ?_
  have hk' := mem_intList_iff.1 hk
  exact le_iSup₂_of_le k (mem_intList_iff.2 ⟨by omega, by omega⟩)
    (le_iSup_of_le (by omega) le_rfl)

theorem Gamma_commutator_mem (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
    {a b : ℤ} (ha : a ∈ intList 1 8) (hb : b ∈ intList 1 8)
    (hab : a ≠ b) {x y : G × G'} (hx : x ∈ Delta c c' θ a)
    (hy : y ∈ Delta c c' θ b) :
    ⁅x, y⁆ ∈ ⨆ k ∈ intList 1 8, ⨆ (_ : min a b < k), Delta c c' θ k := by
  have ha' := mem_intList_iff.1 ha
  have hb' := mem_intList_iff.1 hb
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hmin : min a b = a := min_eq_left hlt.le
    rw [hmin]
    have hcomm : ⁅x, y⁆ ∈ DeltaWin c c' θ a b :=
      (Subgroup.commutator_le.1
        (Delta_commutator_le c c' θ hθ a b ha'.1 hlt hb'.2)) x hx y hy
    exact DeltaWin_le_iSup c c' θ ha'.1 hlt hb'.2 hcomm
  · have hmin : min a b = b := min_eq_right hgt.le
    rw [hmin]
    have hcomm : ⁅y, x⁆ ∈ DeltaWin c c' θ b a :=
      (Subgroup.commutator_le.1
        (Delta_commutator_le c c' θ hθ b a hb'.1 hgt ha'.2)) y hy x hx
    have e : ⁅x, y⁆ = ⁅y, x⁆⁻¹ := (commutatorElement_inv y x).symm
    rw [e]
    have hle : DeltaWin c c' θ b a ≤
        ⨆ k ∈ intList 1 8, ⨆ (_ : b < k), Delta c c' θ k :=
      DeltaWin_le_iSup c c' θ hb'.1 hgt ha'.2
    exact hle ((DeltaWin c c' θ b a).inv_mem hcomm)

theorem Gamma_collection (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) {g : G × G'}
    (hg : g ∈ Gamma c c' θ) :
    ∃ f : ℤ → G × G', (∀ k ∈ intList 1 8, f k ∈ Delta c c' θ k) ∧
      g = ((intList 1 8).map f).prod := by
  refine CFSG.LieType.Steinberg.exists_prod_eq_of_commutator_mem
    (fun k => Delta c c' θ k) (fun k => k) (by decide) (by decide) ?_ g ?_
  · intro a ha b hb hab x hx y hy
    exact Gamma_commutator_mem c c' θ hθ ha hb hab hx hy
  · simpa [Gamma] using hg

end Collection

section Phi

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

variable {G G' : Type u} [Group G] [Group G']
variable {T : TitsSystem G 8} {T' : TitsSystem G' 8}

@[expose] noncomputable def coordFun (x : win T.U 1 8) : ℤ → G :=
  Classical.choose ((TitsSystem.mem_win_iff_prod (T := T) (a := 1) (b := 8)
    (g := (x : G)) (by norm_num)).1 x.2)

theorem coordFun_mem (x : win T.U 1 8) :
    ∀ k ∈ intList 1 8, coordFun x k ∈ T.U k :=
  (Classical.choose_spec ((TitsSystem.mem_win_iff_prod (T := T) (a := 1) (b := 8)
    (g := (x : G)) (by norm_num)).1 x.2)).1

theorem coordFun_prod (x : win T.U 1 8) :
    (x : G) = ((intList 1 8).map (coordFun x)).prod :=
  (Classical.choose_spec ((TitsSystem.mem_win_iff_prod (T := T) (a := 1) (b := 8)
    (g := (x : G)) (by norm_num)).1 x.2)).2

@[expose] noncomputable def coord (x : win T.U 1 8) (k : ℤ) : T.U k :=
  if hk : k ∈ intList 1 8 then ⟨coordFun x k, coordFun_mem x k hk⟩ else 1

theorem coord_of_mem {x : win T.U 1 8} {k : ℤ} (hk : k ∈ intList 1 8) :
    coord x k = ⟨coordFun x k, coordFun_mem x k hk⟩ := by
  simp [coord, hk]

theorem coord_prod (x : win T.U 1 8) :
    (x : G) = ((intList 1 8).map (fun k => (coord x k : G))).prod := by
  rw [coordFun_prod x]
  apply congrArg List.prod
  apply List.map_congr_left
  intro k hk
  rw [coord_of_mem (x := x) hk]

theorem coord_eq_of_prod (x : win T.U 1 8) {f : ℤ → G}
    (hf : ∀ k ∈ intList 1 8, f k ∈ T.U k)
    (hprod : (x : G) = ((intList 1 8).map f).prod) :
    ∀ k ∈ intList 1 8, (coord x k : G) = f k := by
  have huniq := TitsSystem.prod_unique (T := T) (a := 1) (b := 8) (by norm_num)
    (f := coordFun x) (g := f) (coordFun_mem x) hf (by
      rw [← coordFun_prod x, hprod])
  intro k hk
  rw [coord_of_mem (x := x) hk]
  exact huniq k hk

end Phi




section PhiMul

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

variable {G G' : Type u} [Group G] [Group G']
variable {T : TitsSystem G 8} {T' : TitsSystem G' 8}
variable (c : OctCoord T.U) (c' : OctCoord T'.U) (θ : c.K ≃+* c'.K)
variable (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))

theorem psi_mem_Delta (k : ℤ) (x : T.U k) :
    psi c c' θ hθ k x ∈ Delta c c' θ k := by
  by_cases hk : Even k
  · obtain ⟨p, rfl⟩ := (c.eEven k hk).surjective x
    have hpsi : psi c c' θ hθ k (c.eEven k hk p) =
        gpX c c' θ k p.1 * gpX' c c' θ k p.2 := by
      ext
      · simp [psi, gpX, gpX', c.eEven_apply]
      · simp [psi, gpX, gpX', g_eEven c c' θ hθ k hk p, c'.eEven_apply, thetaPair]
    rw [hpsi]
    exact (Delta c c' θ k).mul_mem (gpX_mem_Delta c c' θ k p.1)
      (gpX'_mem_Delta c c' θ k hk p.2)
  · have ho : Odd k := Int.not_even_iff_odd.mp hk
    obtain ⟨t, rfl⟩ := (c.eOdd k ho).surjective x
    have hpsi : psi c c' θ hθ k (c.eOdd k ho t) = gpX c c' θ k t := by
      ext
      · simp [psi, gpX, c.eOdd_apply]
      · simp [psi, gpX, g_eOdd c c' θ hθ k ho t, c'.eOdd_apply]
    rw [hpsi]
    exact gpX_mem_Delta c c' θ k t

@[expose] noncomputable def gammaOf (x : win T.U 1 8) : G × G' :=
  ((intList 1 8).map (fun k => psi c c' θ hθ k (coord x k))).prod

theorem gammaOf_mem (x : win T.U 1 8) : gammaOf c c' θ hθ x ∈ Gamma c c' θ := by
  rw [Gamma]
  refine (⨆ k ∈ intList 1 8, Delta c c' θ k).list_prod_mem ?_
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  exact SetLike.le_def.mp
    (le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 8) => Delta c c' θ k) k hk le_rfl)
    (psi_mem_Delta c c' θ hθ k (coord x k))

@[expose] noncomputable def phiFun (x : win T.U 1 8) : win T'.U 1 8 :=
  ⟨((intList 1 8).map (fun k => ((g c c' θ hθ k) (coord x k) : G'))).prod,
   (win T'.U 1 8).list_prod_mem (fun y hy => by
     obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
     exact SetLike.le_def.mp
       (le_iSup₂_of_le (f := fun k (_ : k ∈ Set.Icc (1 : ℤ) 8) => T'.U k)
         k (by exact mem_intList_iff.1 hk) le_rfl)
       ((g c c' θ hθ k (coord x k)).2))⟩

theorem gammaOf_fst (x : win T.U 1 8) : (gammaOf c c' θ hθ x).1 = (x : G) := by
  rw [gammaOf]
  change (MonoidHom.fst G G')
    ((intList 1 8).map (fun k => psi c c' θ hθ k (coord x k))).prod = (x : G)
  rw [map_list_prod (MonoidHom.fst G G'), List.map_map]
  rw [show (⇑(MonoidHom.fst G G') ∘ fun k => psi c c' θ hθ k (coord x k)) =
      (fun k => (coord x k : G)) by rfl]
  exact (coord_prod x).symm

theorem gammaOf_snd (x : win T.U 1 8) :
    (gammaOf c c' θ hθ x).2 = (phiFun c c' θ hθ x : G') := by
  rw [gammaOf]
  change (MonoidHom.snd G G')
    ((intList 1 8).map (fun k => psi c c' θ hθ k (coord x k))).prod =
      (phiFun c c' θ hθ x : G')
  rw [map_list_prod (MonoidHom.snd G G')]
  rfl

theorem coord_phi (x : win T.U 1 8) {k : ℤ} (hk : k ∈ intList 1 8) :
    coord (phiFun c c' θ hθ x) k = g c c' θ hθ k (coord x k) := by
  apply Subtype.ext
  refine coord_eq_of_prod (phiFun c c' θ hθ x)
    (f := fun k => (g c c' θ hθ k (coord x k) : G')) ?_ ?_ k hk
  · intro k hk
    exact (g c c' θ hθ k (coord x k)).2
  · rfl

theorem phiFun_mul (x y : win T.U 1 8) :
    phiFun c c' θ hθ (x * y) = phiFun c c' θ hθ x * phiFun c c' θ hθ y := by
  apply Subtype.ext
  have hγ : gammaOf c c' θ hθ x * gammaOf c c' θ hθ y ∈ Gamma c c' θ :=
    (Gamma c c' θ).mul_mem (gammaOf_mem c c' θ hθ x) (gammaOf_mem c c' θ hθ y)
  obtain ⟨f, hf, hprod⟩ := Gamma_collection c c' θ hθ hγ
  have hfst : (x : G) * (y : G) = ((intList 1 8).map (fun k => (f k).1)).prod := by
    have h := congrArg Prod.fst hprod
    rw [Prod.fst_mul, gammaOf_fst c c' θ hθ x, gammaOf_fst c c' θ hθ y] at h
    change (x : G) * (y : G) =
      (MonoidHom.fst G G') ((intList 1 8).map f).prod at h
    rw [map_list_prod (MonoidHom.fst G G'), List.map_map] at h
    rw [show (⇑(MonoidHom.fst G G') ∘ f) = (fun k => (f k).1) by rfl] at h
    simpa using h
  have hcoord : ∀ k ∈ intList 1 8, (coord (x * y) k : G) = (f k).1 :=
    coord_eq_of_prod (x * y) (fun k hk => Delta_fst_mem c c' θ (hf k hk)) hfst
  have hgraph : ∀ k (hk : k ∈ intList 1 8),
      (f k).2 = (g c c' θ hθ k ⟨(f k).1, Delta_fst_mem c c' θ (hf k hk)⟩ : G') := by
    intro k hk
    obtain ⟨z, hz⟩ := Delta_eq_psi c c' θ hθ (hf k hk)
    have hz1 : (z : G) = (f k).1 := by
      have h := congrArg Prod.fst hz
      simpa [psi] using h.symm
    have hz2 : (f k).2 = (g c c' θ hθ k z : G') := by
      rw [hz]
      rfl
    have hzeq : z = ⟨(f k).1, Delta_fst_mem c c' θ (hf k hk)⟩ := Subtype.ext hz1
    rw [hz2, hzeq]
  calc
    (phiFun c c' θ hθ (x * y) : G')
        = ((intList 1 8).map (fun k =>
            (g c c' θ hθ k (coord (x * y) k) : G'))).prod := rfl
    _ = ((intList 1 8).map (fun k => (f k).2)).prod := by
          apply congrArg List.prod
          apply List.map_congr_left
          intro k hk
          rw [hgraph k hk]
          exact congrArg (fun z : T.U k => (g c c' θ hθ k z : G'))
            (Subtype.ext (hcoord k hk))
    _ = ((intList 1 8).map f).prod.2 := by
          change ((intList 1 8).map (fun k => (f k).2)).prod =
            (MonoidHom.snd G G') ((intList 1 8).map f).prod
          rw [map_list_prod (MonoidHom.snd G G'), List.map_map]
          rfl
    _ = (gammaOf c c' θ hθ x * gammaOf c c' θ hθ y).2 := by rw [← hprod]
    _ = ((phiFun c c' θ hθ x * phiFun c c' θ hθ y : win T'.U 1 8) : G') := by
          rw [Prod.snd_mul, gammaOf_snd, gammaOf_snd]
          rfl

end PhiMul




section PhiEquiv

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

variable {G G' : Type u} [Group G] [Group G']
variable {T : TitsSystem G 8} {T' : TitsSystem G' 8}
variable (c : OctCoord T.U) (c' : OctCoord T'.U) (θ : c.K ≃+* c'.K)
variable (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
variable (hθsymm : ∀ t, θ.symm (c'.σ t) = c.σ (θ.symm t))

theorem phiFun_one : phiFun c c' θ hθ (1 : win T.U 1 8) = 1 := by
  have h := phiFun_mul c c' θ hθ (1 : win T.U 1 8) (1 : win T.U 1 8)
  simp only [mul_one] at h
  exact (mul_right_inj (phiFun c c' θ hθ 1)).mp (by simpa using h.symm)

@[expose] noncomputable def phi : win T.U 1 8 →* win T'.U 1 8 where
  toFun := phiFun c c' θ hθ
  map_one' := phiFun_one c c' θ hθ
  map_mul' := phiFun_mul c c' θ hθ

theorem thetaPair_symm (p : c.K × c.K) :
    thetaPair c' c θ.symm (thetaPair c c' θ p) = p := by
  ext <;> simp [thetaPair]

theorem gOdd_rev_comp (j : ℤ) (hj : Odd j) (x : T.U j) :
    gOdd c' c θ.symm j hj (gOdd c c' θ j hj x) = x := by
  change c.eOdd j hj (θ.symm ((c'.eOdd j hj).symm
    (c'.eOdd j hj (θ ((c.eOdd j hj).symm x))))) = x
  rw [Equiv.symm_apply_apply, RingEquiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem gEven_rev_comp (j : ℤ) (hj : Even j) (x : T.U j) :
    gEven c' c θ.symm hθsymm j hj (gEven c c' θ hθ j hj x) = x := by
  change c.eEven j hj (thetaPair c' c θ.symm
    ((c'.eEven j hj).symm (c'.eEven j hj
      (thetaPair c c' θ ((c.eEven j hj).symm x))))) = x
  rw [Equiv.symm_apply_apply, thetaPair_symm, Equiv.apply_symm_apply]

theorem g_rev_comp (j : ℤ) (x : T.U j) :
    g c' c θ.symm hθsymm j (g c c' θ hθ j x) = x := by
  by_cases hj : Even j
  · rw [g_of_even c c' θ hθ hj, g_of_even c' c θ.symm hθsymm hj]
    exact gEven_rev_comp c c' θ hθ hθsymm j hj x
  · have ho : Odd j := Int.not_even_iff_odd.mp hj
    rw [g_of_odd c c' θ hθ ho, g_of_odd c' c θ.symm hθsymm ho]
    exact gOdd_rev_comp c c' θ j ho x

theorem phi_rev_phi (x : win T.U 1 8) :
    phiFun c' c θ.symm hθsymm (phiFun c c' θ hθ x) = x := by
  apply Subtype.ext
  calc
    (phiFun c' c θ.symm hθsymm (phiFun c c' θ hθ x) : G)
        = ((intList 1 8).map (fun k =>
            (g c' c θ.symm hθsymm k (coord (phiFun c c' θ hθ x) k) : G))).prod := rfl
    _ = ((intList 1 8).map (fun k => (coord x k : G))).prod := by
          apply congrArg List.prod
          apply List.map_congr_left
          intro k hk
          rw [coord_phi c c' θ hθ x hk, g_rev_comp c c' θ hθ hθsymm k (coord x k)]
    _ = (x : G) := (coord_prod x).symm

end PhiEquiv




section Core

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

variable {G G' : Type u} [Group G] [Group G']
variable {T : TitsSystem G 8} {T' : TitsSystem G' 8}
variable (c : OctCoord T.U) (c' : OctCoord T'.U) (θ : c.K ≃+* c'.K)
variable (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t))
variable (hθsymm : ∀ t, θ.symm (c'.σ t) = c.σ (θ.symm t))

theorem phi_phi_rev (y : win T'.U 1 8) :
    phiFun c c' θ hθ (phiFun c' c θ.symm hθsymm y) = y := by
  have hθ' : ∀ t : c.K, (θ.symm).symm (c.σ t) = c'.σ ((θ.symm).symm t) := by
    simpa using hθ
  exact phi_rev_phi (T := T') (T' := T) (c := c') (c' := c) (θ := θ.symm)
    (hθ := hθsymm) (hθsymm := hθ') y

theorem g_injective (hθsymm : ∀ t, θ.symm (c'.σ t) = c.σ (θ.symm t)) (k : ℤ) :
    Function.Injective (g c c' θ hθ k) := by
  intro a b hab
  have h := congrArg (g c' c θ.symm hθsymm k) hab
  simpa [g_rev_comp c c' θ hθ hθsymm k a, g_rev_comp c c' θ hθ hθsymm k b] using h

theorem g_eq_one_iff (hθsymm : ∀ t, θ.symm (c'.σ t) = c.σ (θ.symm t))
    (k : ℤ) (x : T.U k) : g c c' θ hθ k x = 1 ↔ x = 1 := by
  constructor
  · intro h
    exact g_injective c c' θ hθ hθsymm k (by simpa using h)
  · intro h
    rw [h, map_one]

theorem mem_root_iff_coord (x : win T.U 1 8) (j : ℤ) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) :
    (x : G) ∈ T.U j ↔
      ∀ k ∈ intList 1 8, (k < j ∨ j < k) → coord x k = 1 := by
  have h := TitsSystem.mem_win_iff_coord (T := T) (i := 0) (a := j) (b := j)
    (by omega) (by omega) (f := fun k => (coord x k : G))
    (fun k hk => (coord x k).2)
  have h' : ((intList 1 8).map (fun k => (coord x k : G))).prod ∈ win T.U j j ↔
      ∀ k ∈ intList 1 8, (k < j ∨ j < k) → coord x k = 1 := by
    simpa [zero_add] using h
  rw [← coord_prod x] at h'
  simpa [win] using h'

theorem core_of_coord {G' : Type u} [Group G'] [Finite G] [Finite G']
    (T : TitsSystem G 8) (T' : TitsSystem G' 8) (c : OctCoord T.U) (c' : OctCoord T'.U)
    (θ : c.K ≃+* c'.K) (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ∃ φ : win T.U 1 8 ≃* win T'.U 1 8, ∀ j : ℤ, 1 ≤ j → j ≤ 8 → ∀ x : win T.U 1 8,
      ((x : G) ∈ T.U j ↔ ((φ x : win T'.U 1 8) : G') ∈ T'.U j) := by
  have hθsymm : ∀ t, θ.symm (c'.σ t) = c.σ (θ.symm t) := by
    intro t
    apply θ.injective
    rw [RingEquiv.apply_symm_apply, hθ (θ.symm t), RingEquiv.apply_symm_apply]
  let φ : win T.U 1 8 →* win T'.U 1 8 := phi c c' θ hθ
  let φ' : win T'.U 1 8 →* win T.U 1 8 := phi c' c θ.symm hθsymm
  have h1 : φ'.comp φ = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact phi_rev_phi c c' θ hθ hθsymm x
  have h2 : φ.comp φ' = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro y
    exact phi_phi_rev c c' θ hθ hθsymm y
  refine ⟨φ.toMulEquiv φ' h1 h2, ?_⟩
  intro j hj1 hj8 x
  change (x : G) ∈ T.U j ↔
    ((phiFun c c' θ hθ x : win T'.U 1 8) : G') ∈ T'.U j
  rw [mem_root_iff_coord (T := T) x j hj1 hj8,
    mem_root_iff_coord (T := T') (phiFun c c' θ hθ x) j hj1 hj8]
  constructor
  · intro h k hk hout
    rw [coord_phi c c' θ hθ x hk]
    exact (g_eq_one_iff c c' θ hθ hθsymm k (coord x k)).2 (h k hk hout)
  · intro h k hk hout
    have hk' := h k hk hout
    rw [coord_phi c c' θ hθ x hk] at hk'
    exact (g_eq_one_iff c c' θ hθ hθsymm k (coord x k)).1 hk'

end Core

end CFSG.GH74.Tits83
