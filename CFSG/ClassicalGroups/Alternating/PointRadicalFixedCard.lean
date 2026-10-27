module

public import CFSG.ClassicalGroups.Alternating.PointRadicalFixed
public import CFSG.ClassicalGroups.F2Fixed.SL2Fixed
public import CFSG.ClassicalGroups.ExtendIdentity

public section

namespace CFSG.ClassicalGroups.Alternating

open CFSG.ClassicalGroups.F2Fixed CFSG.LocalAnalysis.ComponentInitial
open LinearMap (BilinForm)
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

@[expose] def Tsp (hB : B.IsAlt) (v : V) (c : K) : Gsp B :=
  ⟨symplecticTransvection B hB v c, symplecticTransvection_mem_bilinIsometryGroup hB v c⟩

theorem Tsp_app (hB : B.IsAlt) (v : V) (c : K) (x : V) :
    (Tsp hB v c).app x = x + (c * B x v) • v := rfl

theorem Tsp_mem_Lsp (hB : B.IsAlt) (v : V) (c : K) : Tsp hB v c ∈ Lsp B hB v :=
  symplecticTransvection_mem_pointRadical hB v c

theorem Tsp_mul_self [CharP K 2] (hB : B.IsAlt) (v : V) (c : K) :
    Tsp hB v c * Tsp hB v c = 1 := by
  apply Subtype.ext
  show symplecticTransvection B hB v c * symplecticTransvection B hB v c = 1
  rw [symplecticTransvection_mul, CharTwo.add_self_eq_zero, symplecticTransvection_zero]

theorem siegel_zero_eq (hB : B.IsAlt) (v : V) (c : K) :
    siegel B hB v 0 c = symplecticTransvection B hB v c := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [siegel_apply hB (map_zero (B v)), symplecticTransvection_apply]
  simp

theorem closure_Lsp_insert_Tsp [FiniteDimensional K V] [CharP K 2] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) {u v : V} (huv : B u v ≠ 0) {c : K} (hc : c ≠ 0) :
    Subgroup.closure ((Lsp B hB v : Set (Gsp B)) ∪ {Tsp hB u c}) = ⊤ := by
  have h := pointRadical_sup_zpowers_siegel (CharTwo.two_eq_zero) hB hBn huv
    (map_zero (B u)) hc
  rw [siegel_zero_eq] at h
  exact closure_subgroupOf_insert_eq_top (bilinIsometryGroup B) (pointRadical B hB v)
    (pointRadical_le_bilinIsometryGroup hB v) _
    (symplecticTransvection_mem_bilinIsometryGroup hB u c) h

@[expose] def listProdTsp (hB : B.IsAlt) (l : List (V × K)) : Gsp B :=
  (l.map fun p => Tsp hB p.1 p.2).prod

theorem listProdTsp_app (hB : B.IsAlt) (l : List (V × K)) (x : V) :
    (listProdTsp hB l).app x =
      ((l.map fun p => symplecticTransvection B hB p.1 p.2).prod : V →ₗ[K] V) x := by
  have : ((listProdTsp hB l : Gsp B) : LinearMap.GeneralLinearGroup K V) =
      (l.map fun p => symplecticTransvection B hB p.1 p.2).prod := by
    have h := map_list_prod (bilinIsometryGroup B).subtype (l.map fun p => Tsp hB p.1 p.2)
    rw [List.map_map] at h
    exact h
  show (((listProdTsp hB l : Gsp B) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x = _
  rw [this]

theorem exists_gsp_pair [FiniteDimensional K V] (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {u u' v v' : V} (h : B u u' = 1) (h' : B v v' = 1) :
    ∃ g : Gsp B, g.app u = v ∧ g.app u' = v' := by
  have hu : u ≠ 0 := by rintro rfl; simp at h
  have hv : v ≠ 0 := by rintro rfl; simp at h'
  obtain ⟨l₁, -, hl₁⟩ := (alternating_transvection_vector_transitivity hB hBn).1 u v hu hv
  set g₁ : Gsp B := listProdTsp hB l₁ with hg₁
  have hg₁u : g₁.app u = v := by rw [hg₁, listProdTsp_app]; exact hl₁
  have hx : B v (g₁.app u') = 1 := by
    rw [← hg₁u, Gsp.form_app, h]
  obtain ⟨l₂, -, -, hl₂v, hl₂x⟩ := alternating_fixed_vector_pair_adjustment hB hx h'
  set g₂ : Gsp B := listProdTsp hB l₂ with hg₂
  refine ⟨g₂ * g₁, ?_, ?_⟩
  · rw [Gsp.app_mul, hg₁u, hg₂, listProdTsp_app]; exact hl₂v
  · rw [Gsp.app_mul, hg₂, listProdTsp_app]; exact hl₂x

section Ext

open CFSG.ClassicalGroups

variable {P W : Submodule K V} (hPW : IsCompl P W)

theorem extLin_form (hB : B.IsAlt) (horth : ∀ p ∈ P, ∀ w ∈ W, B p w = 0) (g : W →ₗ[K] W)
    (hg : ∀ x y : W, B (g x) (g y) = B x y) (v v' : V) :
    B (extLin hPW g v) (extLin hPW g v') = B v v' := by
  have horth' : ∀ w ∈ W, ∀ p ∈ P, B w p = 0 := fun w hw p hp => by
    rw [← hB.neg_eq p w, horth p hp w hw, neg_zero]
  obtain ⟨p, hp, w, hw, rfl⟩ := exists_add_eq hPW v
  obtain ⟨p', hp', w', hw', rfl⟩ := exists_add_eq hPW v'
  rw [extLin_add hPW g hp hw, extLin_add hPW g hp' hw']
  simp only [map_add, LinearMap.add_apply]
  rw [horth p hp _ (g ⟨w', hw'⟩).2, horth' _ (g ⟨w, hw⟩).2 p' hp', horth p hp w' hw',
    horth' w hw p' hp']
  have := hg ⟨w, hw⟩ ⟨w', hw'⟩
  simp only [add_zero, zero_add]
  exact congrArg (B p p' + ·) this

@[expose] noncomputable def extId (hB : B.IsAlt) (horth : ∀ p ∈ P, ∀ w ∈ W, B p w = 0) :
    Gsp (B.restrict W) →* Gsp B :=
  ((Units.map (extHom hPW)).comp (bilinIsometryGroup (B.restrict W)).subtype).codRestrict
    (bilinIsometryGroup B) (fun g' x y => by
      have := g'.2
      exact extLin_form hPW hB horth _ (fun a b => this a b) x y)

theorem extId_app (hB : B.IsAlt) (horth : ∀ p ∈ P, ∀ w ∈ W, B p w = 0)
    (g' : Gsp (B.restrict W)) {p w : V} (hp : p ∈ P) (hw : w ∈ W) :
    (extId hPW hB horth g').app (p + w) = p + (g'.app ⟨w, hw⟩ : V) :=
  extLin_add hPW _ hp hw

end Ext

theorem Gsp.map_zero' (g : Gsp B) : g.app 0 = 0 := by simp [Gsp.app]

theorem Gsp.ext' {g h : Gsp B} (H : ∀ x, g.app x = h.app x) : g = h :=
  Subtype.ext (Units.ext (LinearMap.ext H))


@[expose] noncomputable def Ssp (hB : B.IsAlt) (v w : V) (c : K) : Gsp B :=
  ⟨siegel B hB v w c, siegel_mem_bilinIsometryGroup hB v w c⟩

theorem Ssp_eq (hB : B.IsAlt) (v w : V) (c : K) :
    Ssp hB v w c = Tsp hB (v + w) 1 * Tsp hB w (-1) * Tsp hB v (c - 1) := rfl

theorem Ssp_mem_Lsp (hB : B.IsAlt) {v w : V} (hw : B v w = 0) (c : K) :
    Ssp hB v w c ∈ Lsp B hB v := siegel_mem_pointRadical hB hw c

section ExtSp

variable {P W : Submodule K V} (hPW : IsCompl P W) (hB : B.IsAlt)
  (horth : ∀ p ∈ P, ∀ w ∈ W, B p w = 0)

include hPW horth in
theorem extId_Tsp (x : W) (c : K) :
    extId hPW hB horth (Tsp (isAlt_restrict hB W) x c) = Tsp hB (x : V) c := by
  refine Gsp.ext' fun v => ?_
  obtain ⟨p, hp, w, hw, rfl⟩ := exists_add_eq hPW v
  rw [extId_app hPW hB horth _ hp hw, Tsp_app, Tsp_app]
  have h1 : B (p + w) (x : V) = B w (x : V) := by
    rw [map_add, LinearMap.add_apply, horth p hp x x.2, zero_add]
  rw [h1]
  simp only [Submodule.coe_add, Submodule.coe_smul]
  rw [← add_assoc]
  rfl

include hPW horth in
theorem extId_Ssp (x y : W) (c : K) :
    extId hPW hB horth (Ssp (isAlt_restrict hB W) x y c) = Ssp hB (x : V) (y : V) c := by
  rw [Ssp_eq, Ssp_eq, map_mul, map_mul, extId_Tsp hPW hB horth, extId_Tsp hPW hB horth,
    extId_Tsp hPW hB horth]
  rfl

include hPW horth in
theorem extId_mem_Lsp (x : W) {g : Gsp (B.restrict W)}
    (hg : g ∈ Lsp (B.restrict W) (isAlt_restrict hB W) x) :
    extId hPW hB horth g ∈ Lsp B hB (x : V) := by
  obtain ⟨y, c, hy, hgy⟩ := mem_Lsp.mp hg
  have : g = Ssp (isAlt_restrict hB W) x y c := Subtype.ext hgy.symm
  rw [this, extId_Ssp hPW hB horth]
  exact Ssp_mem_Lsp hB hy c

include hPW horth in
theorem extId_app_of_mem (g : Gsp (B.restrict W)) {p : V} (hp : p ∈ P) :
    (extId hPW hB horth g).app p = p := by
  have := extId_app hPW hB horth g hp W.zero_mem
  have h0 : g.app ⟨0, W.zero_mem⟩ = 0 := Gsp.map_zero' g
  rw [h0] at this
  simpa using this

end ExtSp

section Base

open scoped MatrixGroups

variable [FiniteDimensional K V]

@[expose] noncomputable def hypBasis (hB : B.IsAlt) {e f : V} (hef : B e f = 1)
    (hdim : finrank K V = 2) : Basis (Fin 2) K V :=
  basisOfLinearIndependentOfCardEqFinrank (b := ![e, f])
    (linearIndependent_pair_of_apply_eq_one hB hef) (by simp [hdim])

theorem hypBasis_zero (hB : B.IsAlt) {e f : V} (hef : B e f = 1) (hdim : finrank K V = 2) :
    hypBasis hB hef hdim 0 = e := by
  simp [hypBasis]

theorem hypBasis_one (hB : B.IsAlt) {e f : V} (hef : B e f = 1) (hdim : finrank K V = 2) :
    hypBasis hB hef hdim 1 = f := by
  simp [hypBasis]

theorem toLin_isometry (hB : B.IsAlt) (bs : Basis (Fin 2) K V) (h01 : B (bs 0) (bs 1) = 1)
    (g : SL(2, K)) (x y : V) :
    B (Matrix.toLin bs bs (g : Matrix (Fin 2) (Fin 2) K) x)
      (Matrix.toLin bs bs (g : Matrix (Fin 2) (Fin 2) K) y) = B x y := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have h10 : B (bs 1) (bs 0) = -1 := by rw [← hB.neg_eq, h01]
  have key : B.compl₁₂ (Matrix.toLin bs bs (g : Matrix (Fin 2) (Fin 2) K))
      (Matrix.toLin bs bs (g : Matrix (Fin 2) (Fin 2) K)) = B := by
    apply LinearMap.BilinForm.ext_basis bs
    intro i j
    simp only [LinearMap.compl₁₂_apply, Matrix.toLin_self, Fin.sum_univ_two, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [hB.self_eq_zero, h01, h10] <;>
      first
        | ring1
        | linear_combination hdet
        | linear_combination (-1 : K) * hdet
  exact LinearMap.congr_fun₂ key x y

@[expose] noncomputable def slToGsp (hB : B.IsAlt) (bs : Basis (Fin 2) K V)
    (h01 : B (bs 0) (bs 1) = 1) : SL(2, K) →* Gsp B :=
  ((Units.map (Matrix.toLinAlgEquiv bs).toAlgHom.toMonoidHom).comp
    Matrix.SpecialLinearGroup.toGL).codRestrict (bilinIsometryGroup B)
    (fun g x y => toLin_isometry hB bs h01 g x y)

theorem slToGsp_app (hB : B.IsAlt) (bs : Basis (Fin 2) K V) (h01 : B (bs 0) (bs 1) = 1)
    (g : SL(2, K)) (x : V) :
    (slToGsp hB bs h01 g).app x = Matrix.toLin bs bs (g : Matrix (Fin 2) (Fin 2) K) x := rfl

section BaseCard

variable [CharP K 2]

theorem slToGsp_upper (hB : B.IsAlt) (bs : Basis (Fin 2) K V) (h01 : B (bs 0) (bs 1) = 1)
    (s : K) : slToGsp hB bs h01 (sl2Upper K s) = Tsp hB (bs 0) s := by
  have h10 : B (bs 1) (bs 0) = -1 := by rw [← hB.neg_eq, h01]
  have hlin : Matrix.toLin bs bs (sl2Upper K s : Matrix (Fin 2) (Fin 2) K) =
      ((symplecticTransvection B hB (bs 0) s : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) := by
    refine Basis.ext bs fun i => ?_
    rw [Matrix.toLin_self, symplecticTransvection_apply]
    fin_cases i <;> simp [Fin.sum_univ_two, hB.self_eq_zero, h10, CharTwo.neg_eq] <;> try abel
  refine Gsp.ext' fun x => ?_
  rw [slToGsp_app, hlin]
  rfl

theorem slToGsp_lower (hB : B.IsAlt) (bs : Basis (Fin 2) K V) (h01 : B (bs 0) (bs 1) = 1)
    (t : K) : slToGsp hB bs h01 (sl2Lower K t) = Tsp hB (bs 1) t := by
  have hlin : Matrix.toLin bs bs (sl2Lower K t : Matrix (Fin 2) (Fin 2) K) =
      ((symplecticTransvection B hB (bs 1) t : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) := by
    refine Basis.ext bs fun i => ?_
    rw [Matrix.toLin_self, symplecticTransvection_apply]
    fin_cases i <;> simp [Fin.sum_univ_two, hB.self_eq_zero, h01]
  refine Gsp.ext' fun x => ?_
  rw [slToGsp_app, hlin]
  rfl

theorem exists_smul_of_orth_zero (hB : B.IsAlt) (bs : Basis (Fin 2) K V)
    (h01 : B (bs 0) (bs 1) = 1) {w : V} (hw : B (bs 0) w = 0) : ∃ t : K, w = t • bs 0 := by
  have h := bs.sum_repr w
  rw [Fin.sum_univ_two] at h
  have h1 : bs.repr w 1 = 0 := by
    have := congrArg (B (bs 0)) h
    rw [hw, map_add, map_smul, map_smul, hB.self_eq_zero, h01] at this
    simpa using this
  refine ⟨bs.repr w 0, ?_⟩
  rw [h1, zero_smul, add_zero] at h
  exact h.symm

theorem exists_smul_of_orth_one (hB : B.IsAlt) (bs : Basis (Fin 2) K V)
    (h01 : B (bs 0) (bs 1) = 1) {w : V} (hw : B (bs 1) w = 0) : ∃ t : K, w = t • bs 1 := by
  have h10 : B (bs 1) (bs 0) = -1 := by rw [← hB.neg_eq, h01]
  have h := bs.sum_repr w
  rw [Fin.sum_univ_two] at h
  have h1 : bs.repr w 0 = 0 := by
    have := congrArg (B (bs 1)) h
    rw [hw, map_add, map_smul, map_smul, hB.self_eq_zero, h10] at this
    simpa using this
  refine ⟨bs.repr w 1, ?_⟩
  rw [h1, zero_smul, zero_add] at h
  exact h.symm

theorem Ssp_smul_self (hB : B.IsAlt) (v : V) (t c : K) : Ssp hB v (t • v) c = Tsp hB v c := by
  refine Gsp.ext' fun x => ?_
  have hv : B v (t • v) = 0 := by rw [map_smul, hB.self_eq_zero, smul_zero]
  show (siegel B hB v (t • v) c : V →ₗ[K] V) x = _
  rw [siegel_apply hB hv, Tsp_app]
  simp only [map_smul, smul_eq_mul]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : x + B x v • t • v + (t * B x v) • v + (c * B x v) • v =
      x + (c * B x v) • v + ((2 : K) * (t * B x v)) • v := by module
  rw [this, h2]; simp

theorem mem_Lsp_dim_two (hB : B.IsAlt) (bs : Basis (Fin 2) K V) (h01 : B (bs 0) (bs 1) = 1)
    {g : Gsp B} (hg : g ∈ Lsp B hB (bs 0)) : ∃ c : K, g = Tsp hB (bs 0) c := by
  obtain ⟨w, c, hw, hgw⟩ := mem_Lsp.mp hg
  obtain ⟨t, rfl⟩ := exists_smul_of_orth_zero hB bs h01 hw
  refine ⟨c, ?_⟩
  have : g = Ssp hB (bs 0) (t • bs 0) c := Subtype.ext hgw.symm
  rw [this, Ssp_smul_self]

theorem mem_Lsp_dim_two' (hB : B.IsAlt) (bs : Basis (Fin 2) K V) (h01 : B (bs 0) (bs 1) = 1)
    {g : Gsp B} (hg : g ∈ Lsp B hB (bs 1)) : ∃ c : K, g = Tsp hB (bs 1) c := by
  obtain ⟨w, c, hw, hgw⟩ := mem_Lsp.mp hg
  obtain ⟨t, rfl⟩ := exists_smul_of_orth_one hB bs h01 hw
  refine ⟨c, ?_⟩
  have : g = Ssp hB (bs 1) (t • bs 1) c := Subtype.ext hgw.symm
  rw [this, Ssp_smul_self]

end BaseCard

end Base

section BaseThm

open scoped MatrixGroups

variable [FiniteDimensional K V] [Finite K] [CharP K 2]

theorem sp_card_eq_pow_two (hB : B.IsAlt) (hdim : finrank K V = 2) {u u' : V}
    (huu' : B u u' ≠ 0) {M : Type*} [AddCommGroup M] [Finite M] (h2 : ∀ m : M, m + m = 0)
    [DistribMulAction (Gsp B) M]
    (hdec : IsCompl (fixedSub M (Lsp B hB u : Set (Gsp B)))
      (fixedSub M (Lsp B hB u' : Set (Gsp B)))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 * n) := by
  set f := (B u u')⁻¹ • u' with hf
  have huf : B u f = 1 := by rw [hf, map_smul, smul_eq_mul, inv_mul_cancel₀ huu']
  have hLf : Lsp B hB f = Lsp B hB u' := Lsp_smul hB (inv_ne_zero huu')
  rw [← hLf] at hdec
  set bs := hypBasis hB huf hdim with hbs
  have hu0 : bs 0 = u := hypBasis_zero hB huf hdim
  have hf1 : bs 1 = f := hypBasis_one hB huf hdim
  have h01 : B (bs 0) (bs 1) = 1 := by rw [hu0, hf1]; exact huf
  letI inst : DistribMulAction SL(2, K) M :=
    DistribMulAction.compHom M (slToGsp hB bs h01)
  have hU : fixedSub M (sl2UpperSub K : Set SL(2, K)) =
      fixedSub M (Lsp B hB u : Set (Gsp B)) := by
    ext m
    simp only [mem_fixedSub]
    constructor
    · intro h g hg
      rw [← hu0] at hg
      obtain ⟨c, rfl⟩ := mem_Lsp_dim_two hB bs h01 hg
      have := h (sl2Upper K c) (sl2Upper_mem_sub c)
      rw [← slToGsp_upper hB bs h01 c]
      exact this
    · intro h x hx
      obtain ⟨s, rfl⟩ := hx
      have := h (Tsp hB (bs 0) s) (by rw [hu0]; exact Tsp_mem_Lsp hB u s)
      show (slToGsp hB bs h01 (sl2Upper K s)) • m = m
      rw [slToGsp_upper hB bs h01 s]
      exact this
  have hL : fixedSub M (sl2LowerSub K : Set SL(2, K)) =
      fixedSub M (Lsp B hB f : Set (Gsp B)) := by
    ext m
    simp only [mem_fixedSub]
    constructor
    · intro h g hg
      rw [← hf1] at hg
      obtain ⟨c, rfl⟩ := mem_Lsp_dim_two' hB bs h01 hg
      have := h (sl2Lower K c) (sl2Lower_mem_sub c)
      rw [← slToGsp_lower hB bs h01 c]
      exact this
    · intro h x hx
      obtain ⟨s, rfl⟩ := hx
      have := h (Tsp hB (bs 1) s) (by rw [hf1]; exact Tsp_mem_Lsp hB f s)
      show (slToGsp hB bs h01 (sl2Lower K s)) • m = m
      rw [slToGsp_lower hB bs h01 s]
      exact this
  obtain ⟨n, hn⟩ := sl2_card_eq_pow (E := K) h2 (by rw [hU, hL]; exact hdec)
  exact ⟨n, hn⟩

end BaseThm

theorem smul_mem_fixedSub_Lsp (hB : B.IsAlt) {M : Type*} [AddCommGroup M]
    [DistribMulAction (Gsp B) M] {x : Gsp B} {v : V} (hx : x.app v = v) {a : M}
    (ha : a ∈ fixedSub M (Lsp B hB v : Set (Gsp B))) :
    x • a ∈ fixedSub M (Lsp B hB v : Set (Gsp B)) := by
  intro l hl
  have hxv : x⁻¹.app v = v := by
    have := Gsp.app_inv_app x v
    rwa [hx] at this
  have hconj : x⁻¹ * l * x⁻¹⁻¹ ∈ Lsp B hB v := by
    have := conj_mem_Lsp hB x⁻¹ hl
    rwa [hxv] at this
  calc l • x • a = x • (x⁻¹ * l * x⁻¹⁻¹) • a := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
    _ = x • a := by rw [ha _ hconj]

universe uK uV uM

section Induction

variable {K : Type uK} [Field K] [Finite K] [CharP K 2]

theorem sp_card_eq_pow_aux :
    ∀ m : ℕ, 1 ≤ m → ∀ {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (B : BilinForm K V) (hB : B.IsAlt), B.Nondegenerate → finrank K V = 2 * m →
      ∀ {M : Type uM} [AddCommGroup M] [Finite M], (∀ x : M, x + x = 0) →
      ∀ [DistribMulAction (Gsp B) M] {u u' : V}, B u u' ≠ 0 →
      IsCompl (fixedSub M (Lsp B hB u : Set (Gsp B))) (fixedSub M (Lsp B hB u' : Set (Gsp B))) →
      ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 ^ m * n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro V _ _ _ B hB hBn hdim M _ _ h2 _ u u' huu' hdec
    obtain ⟨n, hn⟩ := sp_card_eq_pow_two hB (by simpa using hdim) huu' h2 hdec
    exact ⟨n, by simpa using hn⟩
  | succ m hm ih =>
    intro V _ _ _ B hB hBn hdim M _ _ h2 _ u u' huu' hdec
    set f := (B u u')⁻¹ • u' with hf
    have huf : B u f = 1 := by rw [hf, map_smul, smul_eq_mul, inv_mul_cancel₀ huu']
    have hLf : Lsp B hB f = Lsp B hB u' := Lsp_smul hB (inv_ne_zero huu')
    rw [← hLf] at hdec
    have hu0 : u ≠ 0 := by rintro rfl; simp at huf
    have h1 : (1 : K) ≠ 0 := one_ne_zero
    have hneg : ∀ x y : V, B x y = 1 → B y x = 1 := fun x y hxy => by
      rw [← hB.neg_eq x y, hxy, CharTwo.neg_eq]
    obtain ⟨-, hsplit⟩ := alternating_hyperbolic_splitting hB hBn hu0
    obtain ⟨-, -, hmemW, hcompl, hndW, hdimW⟩ := hsplit f huf
    set P : Submodule K V := Submodule.span K {u, f} with hP
    set W' : Submodule K V := B.orthogonal P with hW'
    have horth : ∀ p ∈ P, ∀ w ∈ W', B p w = 0 := fun p hp w hw => by
      have := (hmemW w).mp hw p hp
      rw [← hB.neg_eq w p, this, neg_zero]
    have hu : u ∈ P := Submodule.subset_span (by simp)
    have hfP : f ∈ P := Submodule.subset_span (by simp)
    have hB' : (B.restrict W').IsAlt := isAlt_restrict hB W'
    have hdim' : finrank K W' = 2 * m := by
      have h3 : finrank K W' = finrank K V - 2 := hdimW
      rw [h3, hdim]; omega
    have hpos : 0 < finrank K W' := by omega
    obtain ⟨u₁, hu₁⟩ : ∃ u₁ : W', u₁ ≠ 0 := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    obtain ⟨⟨u₁', hu₁'⟩, -⟩ := alternating_hyperbolic_splitting hB' hndW hu₁
    have hxx : B (u₁ : V) (u₁' : V) = 1 := hu₁'
    have hxx' : B (u₁' : V) (u₁ : V) = 1 := hneg _ _ hxx
    obtain ⟨g₁, hg₁u, hg₁f⟩ := exists_gsp_pair hB hBn huf hxx
    obtain ⟨g₂, hg₂, -⟩ := exists_gsp_pair hB hBn hxx hxx'
    obtain ⟨g₃, hg₃, -⟩ := exists_gsp_pair hB hBn huf (hneg _ _ huf)
    have hdecP : IsCompl (fixedSub M (Lsp B hB (u₁ : V) : Set (Gsp B)))
        (fixedSub M (Lsp B hB (u₁' : V) : Set (Gsp B))) := by
      have := isCompl_fixedSub_conj g₁ hdec
      rwa [image_conj_Lsp hB g₁ u, image_conj_Lsp hB g₁ f, hg₁u, hg₁f] at this
    have hcardP : Nat.card (fixedSub M (Lsp B hB (u₁ : V) : Set (Gsp B))) =
        Nat.card (fixedSub M (Lsp B hB (u₁' : V) : Set (Gsp B))) := by
      have := card_fixedSub_Lsp hB (M := M) g₂ (u₁ : V)
      rw [hg₂] at this
      exact this.symm
    have hcardu : Nat.card (fixedSub M (Lsp B hB f : Set (Gsp B))) =
        Nat.card (fixedSub M (Lsp B hB u : Set (Gsp B))) := by
      have := card_fixedSub_Lsp hB (M := M) g₃ u
      rwa [hg₃] at this
    have hB1 : B (u₁ : V) (u₁' : V) ≠ 0 := by rw [hxx]; exact h1
    have hB1' : B (u₁' : V) (u₁ : V) ≠ 0 := by rw [hxx']; exact h1
    have hgen₁ := closure_Lsp_insert_Tsp hB hBn hB1 h1
    have hgen₂ := closure_Lsp_insert_Tsp hB hBn hB1' h1
    set π := extId hcompl hB horth with hπ
    have hau : (Tsp hB (u₁ : V) 1).app u = u := by
      rw [Tsp_app, horth u hu _ u₁.2]; simp
    have hcu : (Tsp hB (u₁' : V) 1).app u = u := by
      rw [Tsp_app, horth u hu _ u₁'.2]; simp
    obtain ⟨hsup, hinf⟩ := step_decomp h2 (P₁ := Lsp B hB (u₁ : V)) (P₂ := Lsp B hB (u₁' : V))
      (a := Tsp hB (u₁ : V) 1) (c := Tsp hB (u₁' : V) 1) (Tsp_mem_Lsp hB _ _)
      (Tsp_mem_Lsp hB _ _) (Tsp_mul_self hB _ _) (Tsp_mul_self hB _ _) hgen₁ hgen₂ hdecP hcardP
      (E₁ := π '' (Lsp (B.restrict W') hB' u₁ : Set (Gsp (B.restrict W'))))
      (E₂ := π '' (Lsp (B.restrict W') hB' u₁' : Set (Gsp (B.restrict W'))))
      ⟨Tsp hB' u₁ 1, Tsp_mem_Lsp hB' u₁ 1, extId_Tsp hcompl hB horth u₁ 1⟩
      (by rintro _ ⟨g, hg, rfl⟩; exact extId_mem_Lsp hcompl hB horth u₁ hg)
      ⟨Tsp hB' u₁' 1, Tsp_mem_Lsp hB' u₁' 1, extId_Tsp hcompl hB horth u₁' 1⟩
      (by rintro _ ⟨g, hg, rfl⟩; exact extId_mem_Lsp hcompl hB horth u₁' hg)
      (W := fixedSub M (Lsp B hB u : Set (Gsp B)))
      (fun w hw => smul_mem_fixedSub_Lsp hB hau hw)
      (fun w hw => smul_mem_fixedSub_Lsp hB hcu hw)
    have hW : ∀ (g' : Gsp (B.restrict W')) (w : M),
        w ∈ fixedSub M (Lsp B hB u : Set (Gsp B)) →
          π g' • w ∈ fixedSub M (Lsp B hB u : Set (Gsp B)) := fun g' w hw =>
      smul_mem_fixedSub_Lsp hB (extId_app_of_mem hcompl hB horth g' hu) hw
    letI inst : DistribMulAction (Gsp (B.restrict W')) (fixedSub M (Lsp B hB u : Set (Gsp B))) :=
      restrictAction π (fixedSub M (Lsp B hB u : Set (Gsp B))) hW
    have hdec' := isCompl_fixedSub_restrict π (fixedSub M (Lsp B hB u : Set (Gsp B))) hW
      (Lsp (B.restrict W') hB' u₁ : Set (Gsp (B.restrict W')))
      (Lsp (B.restrict W') hB' u₁' : Set (Gsp (B.restrict W'))) hsup hinf
    have h2' : ∀ x : fixedSub M (Lsp B hB u : Set (Gsp B)), x + x = 0 := fun x =>
      Subtype.ext (h2 x)
    obtain ⟨n, hn⟩ := ih (B.restrict W') hB' hndW hdim' h2' (u := u₁) (u' := u₁')
      (by rw [show (B.restrict W') u₁ u₁' = 1 from hu₁']; exact h1) hdec'
    refine ⟨n, ?_⟩
    have hsq := card_eq_sq (M := M) hdec.symm hcardu
    rw [hsq, hn, ← pow_mul]
    congr 1
    ring

end Induction

section Final

variable [FiniteDimensional K V] [Finite K] [CharP K 2]

@[expose] def Gsp.NonA2 (x : Gsp B) : Prop := ∃ y : V, B y (x.app y) ≠ 0

theorem exists_ssp_of_nonA2 (hB : B.IsAlt) {v : V} {x : Gsp B} (hx : x ∈ Lsp B hB v)
    (hn : x.NonA2) : ∃ w c, B v w = 0 ∧ c ≠ 0 ∧ x = Ssp hB v w c := by
  obtain ⟨w, c, hw, hxw⟩ := mem_Lsp.mp hx
  have hx' : x = Ssp hB v w c := Subtype.ext hxw.symm
  refine ⟨w, c, hw, ?_, hx'⟩
  rintro rfl
  obtain ⟨y, hy⟩ := hn
  apply hy
  have := siegel_form_apply_self (CharTwo.two_eq_zero) hB hw 0 y
  rw [hx']
  simpa [Ssp, Gsp.app] using this

theorem Ssp_mul_self (hB : B.IsAlt) {v w : V} (hw : B v w = 0) (c : K) :
    Ssp hB v w c * Ssp hB v w c = 1 := by
  apply Subtype.ext
  show siegel B hB v w c * siegel B hB v w c = 1
  rw [siegel_mul hB hw hw, ← two_smul K w, CharTwo.two_eq_zero, zero_smul]
  have : c + c + B w w = 0 := by rw [hB.self_eq_zero, add_zero]; exact CharTwo.add_self_eq_zero c
  rw [this, siegel_zero]

theorem stroth_2_1_ii_sp_fixed (hB : B.IsAlt) (hBn : B.Nondegenerate) {u u' : V}
    (huu' : B u u' ≠ 0) {M : Type*} [AddCommGroup M] [Finite M] (h2 : ∀ x : M, x + x = 0)
    [DistribMulAction (Gsp B) M]
    (hdec : IsCompl (fixedSub M (Lsp B hB u : Set (Gsp B)))
      (fixedSub M (Lsp B hB u' : Set (Gsp B))))
    {x : Gsp B} (hx : x ∈ Lsp B hB u') (hn : x.NonA2) :
    fixedSub M {x} = fixedSub M (Lsp B hB u' : Set (Gsp B)) ∧
      (comm M x).range = fixedSub M (Lsp B hB u' : Set (Gsp B)) ∧
      Nat.card M = Nat.card (fixedSub M (Lsp B hB u' : Set (Gsp B))) ^ 2 := by
  obtain ⟨w, c, hw, hc, rfl⟩ := exists_ssp_of_nonA2 hB hx hn
  have hu'u : B u' u ≠ 0 := by
    rw [← hB.neg_eq]; exact neg_ne_zero.mpr huu'
  set f := (B u u')⁻¹ • u' with hf
  have huf : B u f = 1 := by rw [hf, map_smul, smul_eq_mul, inv_mul_cancel₀ huu']
  have hLf : Lsp B hB f = Lsp B hB u' := Lsp_smul hB (inv_ne_zero huu')
  have hfu : B f u = 1 := by rw [← hB.neg_eq, huf, CharTwo.neg_eq]
  obtain ⟨g, hg, -⟩ := exists_gsp_pair hB hBn huf hfu
  have hcard : Nat.card (fixedSub M (Lsp B hB u : Set (Gsp B))) =
      Nat.card (fixedSub M (Lsp B hB u' : Set (Gsp B))) := by
    have := card_fixedSub_Lsp hB (M := M) g u
    rw [hg, hLf] at this
    exact this.symm
  have hgen : Subgroup.closure ((Lsp B hB u : Set (Gsp B)) ∪ {Ssp hB u' w c}) = ⊤ := by
    have h := pointRadical_sup_zpowers_siegel (CharTwo.two_eq_zero) hB hBn hu'u hw hc
    exact closure_subgroupOf_insert_eq_top (bilinIsometryGroup B) (pointRadical B hB u)
      (pointRadical_le_bilinIsometryGroup hB u) _ (siegel_mem_bilinIsometryGroup hB u' w c) h
  exact pair_facts h2 (L₁ := Lsp B hB u) (L₂ := Lsp B hB u') hx (Ssp_mul_self hB hw c) hgen hdec
    hcard

theorem stroth_2_1_ii_sp (hB : B.IsAlt) (hBn : B.Nondegenerate) {m : ℕ} (hm : 1 ≤ m)
    (hdim : finrank K V = 2 * m) {M : Type*} [AddCommGroup M] [Finite M]
    (h2 : ∀ x : M, x + x = 0) [DistribMulAction (Gsp B) M] {u u' : V} (huu' : B u u' ≠ 0)
    (hdec : IsCompl (fixedSub M (Lsp B hB u : Set (Gsp B)))
      (fixedSub M (Lsp B hB u' : Set (Gsp B)))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 ^ m * n) :=
  sp_card_eq_pow_aux m hm B hB hBn hdim h2 huu' hdec

end Final

end CFSG.ClassicalGroups.Alternating
