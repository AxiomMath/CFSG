module

public import CFSG.ClassicalInvolution.WeakCT.B2Modules
public import CFSG.ClassicalInvolution.WeakCT.B2Signs

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open scoped commutatorElement MatrixGroups

section Conj

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {s l : Fin D.rank}

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem comm_eq_one (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0)
    (hl : eList z w = []) (c d : F) : ⁅x (pair s l z) c, x (pair s l w) d⁆ = 1 :=
  comm_rel_nil hE hdiv hcsl hcls hz hw hzw hl c d

theorem comm_eq_term (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w u : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0)
    (hl : eList z w = [(1, 1)]) (hu : z + w = u) (c d : F) :
    ⁅x (pair s l z) c, x (pair s l w) d⁆ = x (pair s l u) (Cz F C s l z w (1, 1) * c * d) := by
  have h := comm_rel hE hdiv hcsl hcls hz hw hzw c d
  rw [hl] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
    one_smul, hu] at h
  exact h

theorem comm_eq_two (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w u₁ u₂ : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2)
    (hzw : z + w ≠ 0) (hl : eList z w = [(1, 1), (2, 1)]) (hu₁ : z + w = u₁)
    (hu₂ : 2 • z + w = u₂) (c d : F) :
    ⁅x (pair s l z) c, x (pair s l w) d⁆ = x (pair s l u₁) (Cz F C s l z w (1, 1) * c * d) *
      x (pair s l u₂) (Cz F C s l z w (2, 1) * c ^ 2 * d) := by
  have h := comm_rel hE hdiv hcsl hcls hz hw hzw c d
  rw [hl] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
    one_smul, hu₁, hu₂] at h
  exact h

theorem comm_eq_two' (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w u₁ u₂ : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2)
    (hzw : z + w ≠ 0) (hl : eList z w = [(1, 1), (1, 2)]) (hu₁ : z + w = u₁)
    (hu₂ : z + 2 • w = u₂) (c d : F) :
    ⁅x (pair s l z) c, x (pair s l w) d⁆ = x (pair s l u₁) (Cz F C s l z w (1, 1) * c * d) *
      x (pair s l u₂) (Cz F C s l z w (1, 2) * c * d ^ 2) := by
  have h := comm_rel hE hdiv hcsl hcls hz hw hzw c d
  rw [hl] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
    one_smul, hu₁, hu₂] at h
  exact h

end Conj

section VModule

theorem comm_pair_aux {G : Type*} [Group G] (b c d : G) (hbc : b * c = c * b)
    (hbd : b * d = d * b) : c * d * b = b * c * d := by
  calc c * d * b = c * (d * b) := by group
    _ = c * (b * d) := by rw [← hbd]
    _ = (c * b) * d := by group
    _ = (b * c) * d := by rw [← hbc]

theorem comm_pair_aux' {G : Type*} [Group G] (c b d : G) (hcd : c * d = d * c)
    (hbd : b * d = d * b) : c * b * d = d * c * b := by
  calc c * b * d = c * (b * d) := by group
    _ = c * (d * b) := by rw [hbd]
    _ = (c * d) * b := by group
    _ = (d * c) * b := by rw [hcd]

theorem unit_zpow_even {F : Type} [Field F] (t : Fˣ) (ht : t = 1 ∨ t = -1) {k : ℤ}
    (hk : Even k) : ((t ^ k : Fˣ) : F) = 1 := by
  rcases ht with rfl | rfl
  · simp
  · rw [hk.neg_one_zpow]
    simp

theorem even_neg_pairing (z : ℤ × ℤ) : Even (-(z.1 * 2 + z.2 * (-2))) :=
  ⟨-(z.1 - z.2), by ring⟩

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {s l : Fin D.rank}

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem b2_V (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (t : Fˣ) (ht : t = 1 ∨ t = -1)
    (hn : x (pair s l (σ, 0)) 1 * x (pair s l (-σ, 0)) (-1) * x (pair s l (σ, 0)) 1 =
      Steinberg.weylElement x s t) :
    Cz F C s l (σ, 0) (0, σ) (2, 1) = wsign hE s (pair s l (2 * σ, σ)) ∧
      Cz F C s l (σ, 0) (0, σ) (1, 1) * Cz F C s l (σ, 0) (σ, σ) (1, 1) =
        2 * wsign hE s (pair s l (2 * σ, σ)) ∧
      wsign hE s (pair s l (σ, σ)) = -1 ∧
      wsign hE s (pair s l (0, σ)) = wsign hE s (pair s l (2 * σ, σ)) := by
  have mA : ((σ, 0) : ℤ × ℤ) ∈ zB2 := by rcases hσ with rfl | rfl <;> decide
  have mA' : ((-σ, 0) : ℤ × ℤ) ∈ zB2 := by rcases hσ with rfl | rfl <;> decide
  have mB : ((0, σ) : ℤ × ℤ) ∈ zB2 := by rcases hσ with rfl | rfl <;> decide
  have mC : ((σ, σ) : ℤ × ℤ) ∈ zB2 := by rcases hσ with rfl | rfl <;> decide
  have mD : ((2 * σ, σ) : ℤ × ℤ) ∈ zB2 := by rcases hσ with rfl | rfl <;> decide
  have lAB : eList (σ, 0) (0, σ) = [(1, 1), (2, 1)] := by rcases hσ with rfl | rfl <;> decide
  have lAC : eList (σ, 0) (σ, σ) = [(1, 1)] := by rcases hσ with rfl | rfl <;> decide
  have lAD : eList (σ, 0) (2 * σ, σ) = [] := by rcases hσ with rfl | rfl <;> decide
  have lA'B : eList (-σ, 0) (0, σ) = [] := by rcases hσ with rfl | rfl <;> decide
  have lA'C : eList (-σ, 0) (σ, σ) = [(1, 1)] := by rcases hσ with rfl | rfl <;> decide
  have lA'D : eList (-σ, 0) (2 * σ, σ) = [(1, 1), (2, 1)] := by
    rcases hσ with rfl | rfl <;> decide
  have lBC : eList (0, σ) (σ, σ) = [] := by rcases hσ with rfl | rfl <;> decide
  have lBD : eList (0, σ) (2 * σ, σ) = [] := by rcases hσ with rfl | rfl <;> decide
  have lCD : eList (σ, σ) (2 * σ, σ) = [] := by rcases hσ with rfl | rfl <;> decide
  have zAB : ((σ, 0) : ℤ × ℤ) + (0, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have zAC : ((σ, 0) : ℤ × ℤ) + (σ, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have zAD : ((σ, 0) : ℤ × ℤ) + (2 * σ, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have zA'B : ((-σ, 0) : ℤ × ℤ) + (0, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have zA'C : ((-σ, 0) : ℤ × ℤ) + (σ, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have zA'D : ((-σ, 0) : ℤ × ℤ) + (2 * σ, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have zBC : ((0, σ) : ℤ × ℤ) + (σ, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have zBD : ((0, σ) : ℤ × ℤ) + (2 * σ, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have zCD : ((σ, σ) : ℤ × ℤ) + (2 * σ, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have sAB₁ : ((σ, 0) : ℤ × ℤ) + (0, σ) = (σ, σ) := by rcases hσ with rfl | rfl <;> decide
  have sAB₂ : 2 • ((σ, 0) : ℤ × ℤ) + (0, σ) = (2 * σ, σ) := by
    rcases hσ with rfl | rfl <;> decide
  have sAC : ((σ, 0) : ℤ × ℤ) + (σ, σ) = (2 * σ, σ) := by rcases hσ with rfl | rfl <;> decide
  have sA'C : ((-σ, 0) : ℤ × ℤ) + (σ, σ) = (0, σ) := by rcases hσ with rfl | rfl <;> decide
  have sA'D₁ : ((-σ, 0) : ℤ × ℤ) + (2 * σ, σ) = (σ, σ) := by rcases hσ with rfl | rfl <;> decide
  have sA'D₂ : 2 • ((-σ, 0) : ℤ × ℤ) + (2 * σ, σ) = (0, σ) := by
    rcases hσ with rfl | rfl <;> decide
  have rA := pair_mem_roots_zB2 hcsl hcls _ mA
  have rA' := pair_mem_roots_zB2 hcsl hcls _ mA'
  have rB := pair_mem_roots_zB2 hcsl hcls _ mB
  have rC := pair_mem_roots_zB2 hcsl hcls _ mC
  have rD := pair_mem_roots_zB2 hcsl hcls _ mD
  have hsl : s ≠ l := ne_of_cartan_neg_two hcsl
  have cBC : ∀ u v, x (pair s l (0, σ)) u * x (pair s l (σ, σ)) v =
      x (pair s l (σ, σ)) v * x (pair s l (0, σ)) u := fun u v =>
    (commute_of_nil hE hdiv hcsl hcls mB mC zBC lBC u v).eq
  have cBD : ∀ u v, x (pair s l (0, σ)) u * x (pair s l (2 * σ, σ)) v =
      x (pair s l (2 * σ, σ)) v * x (pair s l (0, σ)) u := fun u v =>
    (commute_of_nil hE hdiv hcsl hcls mB mD zBD lBD u v).eq
  have cCD : ∀ u v, x (pair s l (σ, σ)) u * x (pair s l (2 * σ, σ)) v =
      x (pair s l (2 * σ, σ)) v * x (pair s l (σ, σ)) u := fun u v =>
    (commute_of_nil hE hdiv hcsl hcls mC mD zCD lCD u v).eq
  have hpair : ∀ z ∈ ({(0, σ), (σ, σ), (2 * σ, σ)} : Finset (ℤ × ℤ)), ∀ u : F,
      Steinberg.weylElement x s t * x (pair s l z) u * (Steinberg.weylElement x s t)⁻¹ =
        x (reflection D.cartan s (pair s l z)) (wsign hE s (pair s l z) * u) := by
    intro z hz u
    have hzm : z ∈ zB2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    rw [(wsign_spec hE (pair_mem_roots_zB2 hcsl hcls z hzm)).2 t u]
    congr 2
    rw [pairing_pair, hcsl, D.isFiniteType.apply_self s,
      unit_zpow_even t ht (by simpa using even_neg_pairing z), mul_one]
  have hNb : ∀ v, x (pair s l (σ, 0)) 1 * x (pair s l (-σ, 0)) (-1) * x (pair s l (σ, 0)) 1 *
      x (pair s l (0, σ)) v * (x (pair s l (σ, 0)) 1 * x (pair s l (-σ, 0)) (-1) *
        x (pair s l (σ, 0)) 1)⁻¹ = x (pair s l (2 * σ, σ)) (wsign hE s (pair s l (0, σ)) * v) := by
    intro v
    rw [hn, hpair (0, σ) (by simp) v, reflection_pair_bS hcsl]
    congr 2
    rcases hσ with rfl | rfl <;> decide
  have hNc : ∀ v, x (pair s l (σ, 0)) 1 * x (pair s l (-σ, 0)) (-1) * x (pair s l (σ, 0)) 1 *
      x (pair s l (σ, σ)) v * (x (pair s l (σ, 0)) 1 * x (pair s l (-σ, 0)) (-1) *
        x (pair s l (σ, 0)) 1)⁻¹ = x (pair s l (σ, σ)) (wsign hE s (pair s l (σ, σ)) * v) := by
    intro v
    rw [hn, hpair (σ, σ) (by simp) v, reflection_pair_bS hcsl]
    congr 2
    rcases hσ with rfl | rfl <;> decide
  have hNd : ∀ v, x (pair s l (σ, 0)) 1 * x (pair s l (-σ, 0)) (-1) * x (pair s l (σ, 0)) 1 *
      x (pair s l (2 * σ, σ)) v * (x (pair s l (σ, 0)) 1 * x (pair s l (-σ, 0)) (-1) *
        x (pair s l (σ, 0)) 1)⁻¹ = x (pair s l (0, σ)) (wsign hE s (pair s l (2 * σ, σ)) * v) := by
    intro v
    rw [hn, hpair (2 * σ, σ) (by simp) v, reflection_pair_bS hcsl]
    congr 2
    rcases hσ with rfl | rfl <;> decide
  have fB : 0 < funcl s l (0, σ) (pair s l (0, σ)) := by
    rw [funcl_pair hsl]; rcases hσ with rfl | rfl <;> decide
  have fC : 0 < funcl s l (0, σ) (pair s l (σ, σ)) := by
    rw [funcl_pair hsl]; rcases hσ with rfl | rfl <;> decide
  have fD : 0 < funcl s l (0, σ) (pair s l (2 * σ, σ)) := by
    rw [funcl_pair hsl]; rcases hσ with rfl | rfl <;> decide
  have fBC : funcl s l (0, σ) (pair s l (0, σ)) ≤ funcl s l (0, σ) (pair s l (σ, σ)) := by
    rw [funcl_pair hsl, funcl_pair hsl]; rcases hσ with rfl | rfl <;> decide
  have fCD : funcl s l (0, σ) (pair s l (σ, σ)) ≤ funcl s l (0, σ) (pair s l (2 * σ, σ)) := by
    rw [funcl_pair hsl, funcl_pair hsl]; rcases hσ with rfl | rfl <;> decide
  have nBC : ((0, σ) : ℤ × ℤ) ≠ (σ, σ) := by rcases hσ with rfl | rfl <;> decide
  have nBD : ((0, σ) : ℤ × ℤ) ≠ (2 * σ, σ) := by rcases hσ with rfl | rfl <;> decide
  have nCD : ((σ, σ) : ℤ × ℤ) ≠ (2 * σ, σ) := by rcases hσ with rfl | rfl <;> decide
  let V : VData K F :=
    { xa := x (pair s l (σ, 0))
      xa' := x (pair s l (-σ, 0))
      xb := x (pair s l (0, σ))
      xc := x (pair s l (σ, σ))
      xd := x (pair s l (2 * σ, σ))
      κ₁ := Cz F C s l (σ, 0) (0, σ) (1, 1)
      κ₂ := Cz F C s l (σ, 0) (σ, σ) (1, 1)
      κ₃ := Cz F C s l (σ, 0) (0, σ) (2, 1)
      μ₁ := Cz F C s l (-σ, 0) (σ, σ) (1, 1)
      μ₂ := Cz F C s l (-σ, 0) (2 * σ, σ) (1, 1)
      μ₃ := Cz F C s l (-σ, 0) (2 * σ, σ) (2, 1)
      ηb := wsign hE s (pair s l (0, σ))
      ηc := wsign hE s (pair s l (σ, σ))
      ηd := wsign hE s (pair s l (2 * σ, σ))
      add_a := x_add' hE rA
      add_a' := x_add' hE rA'
      add_b := x_add' hE rB
      add_c := x_add' hE rC
      add_d := x_add' hE rD
      comm_bc := cBC
      comm_bd := cBD
      comm_cd := cCD
      conj_a_b := fun t' v => by
        rw [conj_eq_comm hE rA, comm_eq_two hE hdiv hcsl hcls mA mB zAB lAB sAB₁ sAB₂]
        exact comm_pair_aux _ _ _ (cBC _ _) (cBD _ _)
      conj_a_c := fun t' v => by
        rw [conj_eq_comm hE rA, comm_eq_term hE hdiv hcsl hcls mA mC zAC lAC sAC]
        exact (cCD _ _).symm
      conj_a_d := fun t' v => by
        rw [conj_eq_comm hE rA, comm_eq_one hE hdiv hcsl hcls mA mD zAD lAD, one_mul]
      conj_a'_b := fun t' v => by
        rw [conj_eq_comm hE rA', comm_eq_one hE hdiv hcsl hcls mA' mB zA'B lA'B, one_mul]
      conj_a'_c := fun t' v => by
        rw [conj_eq_comm hE rA', comm_eq_term hE hdiv hcsl hcls mA' mC zA'C lA'C sA'C]
        exact cBC _ _
      conj_a'_d := fun t' v => by
        rw [conj_eq_comm hE rA', comm_eq_two hE hdiv hcsl hcls mA' mD zA'D lA'D sA'D₁ sA'D₂]
        exact comm_pair_aux' _ _ _ (cCD _ _) (cBD _ _)
      conj_n_b := hNb
      conj_n_c := hNc
      conj_n_d := hNd
      ext := fun u₁ u₂ u₃ u₁' u₂' u₃' h =>
        ext3 hE rB rC rD (fun e => nBC (pair_injective hsl e)) (fun e => nBD (pair_injective hsl e))
          (fun e => nCD (pair_injective hsl e)) (funcl s l (0, σ)) fB (by
            rw [funcl_pair hsl]; rcases hσ with rfl | rfl <;> decide) fD fBC fCD h
      sq_d := wsign_mul_self hE (pair_mem_roots_zB2 hcsl hcls _ mD) }
  obtain ⟨h1, h2, h3, h4⟩ := V.result
  exact ⟨h1, h2, h3, h4⟩

end VModule

section HModule

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {s l : Fin D.rank}

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem b2_H (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    Cz F C s l (0, 1) (1, 0) (1, 1) = wsign hE l (pair s l (1, 0)) ∧
      Cz F C s l (0, -1) (1, 1) (1, 1) = -wsign hE l (pair s l (1, 1)) ∧
      Cz F C s l (0, -1) (1, 1) (1, 1) * Cz F C s l (0, 1) (1, 0) (1, 1) = 1 := by
  have hsl : s ≠ l := ne_of_cartan_neg_two hcsl
  have mA : ((1, 0) : ℤ × ℤ) ∈ zB2 := by decide
  have mB : ((0, 1) : ℤ × ℤ) ∈ zB2 := by decide
  have mB' : ((0, -1) : ℤ × ℤ) ∈ zB2 := by decide
  have mC : ((1, 1) : ℤ × ℤ) ∈ zB2 := by decide
  have mD : ((2, 1) : ℤ × ℤ) ∈ zB2 := by decide
  have rA := pair_mem_roots_zB2 hcsl hcls _ mA
  have rB := pair_mem_roots_zB2 hcsl hcls _ mB
  have rB' := pair_mem_roots_zB2 hcsl hcls _ mB'
  have rC := pair_mem_roots_zB2 hcsl hcls _ mC
  have rD := pair_mem_roots_zB2 hcsl hcls _ mD
  have cDA : ∀ u v, x (pair s l (2, 1)) u * x (pair s l (1, 0)) v =
      x (pair s l (1, 0)) v * x (pair s l (2, 1)) u := fun u v =>
    (commute_of_nil hE hdiv hcsl hcls mA mD (by decide) (by decide) v u).symm.eq
  have cDC : ∀ u v, x (pair s l (2, 1)) u * x (pair s l (1, 1)) v =
      x (pair s l (1, 1)) v * x (pair s l (2, 1)) u := fun u v =>
    (commute_of_nil hE hdiv hcsl hcls mC mD (by decide) (by decide) v u).symm.eq
  have hrel : ∀ m n, x (pair s l (1, 1)) m * x (pair s l (1, 0)) n =
      x (pair s l (2, 1)) (Cz F C s l (1, 1) (1, 0) (1, 1) * m * n) *
        (x (pair s l (1, 0)) n * x (pair s l (1, 1)) m) := fun m n => by
    have h := comm_eq_term hE hdiv hcsl hcls (z := (1, 1)) (w := (1, 0)) (u := (2, 1)) mC mA
      (by decide) (by decide) (by decide) m n
    rw [commutatorElement_def] at h
    calc x (pair s l (1, 1)) m * x (pair s l (1, 0)) n
        = (x (pair s l (1, 1)) m * x (pair s l (1, 0)) n * (x (pair s l (1, 1)) m)⁻¹ *
            (x (pair s l (1, 0)) n)⁻¹) * (x (pair s l (1, 0)) n * x (pair s l (1, 1)) m) := by
          group
      _ = _ := by rw [h]
  have hn : x (pair s l (0, 1)) 1 * x (pair s l (0, -1)) (-1) * x (pair s l (0, 1)) 1 =
      Steinberg.weylElement x l 1 := by
    simp [Steinberg.weylElement, pair_zero_one, pair_zero_neg_one]
  have hNa : ∀ v, x (pair s l (0, 1)) 1 * x (pair s l (0, -1)) (-1) * x (pair s l (0, 1)) 1 *
      x (pair s l (1, 0)) v * (x (pair s l (0, 1)) 1 * x (pair s l (0, -1)) (-1) *
        x (pair s l (0, 1)) 1)⁻¹ = x (pair s l (1, 1)) (wsign hE l (pair s l (1, 0)) * v) := by
    intro v
    rw [hn, weyl_conj_one hE rA, reflection_pair_bL hcls]
    rfl
  have hNc : ∀ v, x (pair s l (0, 1)) 1 * x (pair s l (0, -1)) (-1) * x (pair s l (0, 1)) 1 *
      x (pair s l (1, 1)) v * (x (pair s l (0, 1)) 1 * x (pair s l (0, -1)) (-1) *
        x (pair s l (0, 1)) 1)⁻¹ = x (pair s l (1, 0)) (wsign hE l (pair s l (1, 1)) * v) := by
    intro v
    rw [hn, weyl_conj_one hE rC, reflection_pair_bL hcls]
    rfl
  have hNd : ∀ v, x (pair s l (0, 1)) 1 * x (pair s l (0, -1)) (-1) * x (pair s l (0, 1)) 1 *
      x (pair s l (2, 1)) v * (x (pair s l (0, 1)) 1 * x (pair s l (0, -1)) (-1) *
        x (pair s l (0, 1)) 1)⁻¹ = x (pair s l (2, 1)) (wsign hE l (pair s l (2, 1)) * v) := by
    intro v
    rw [hn, weyl_conj_one hE rD, reflection_pair_bL hcls]
    rfl
  let H : HData K F :=
    { xa := x (pair s l (1, 0))
      xc := x (pair s l (1, 1))
      xd := x (pair s l (2, 1))
      xb := x (pair s l (0, 1))
      xb' := x (pair s l (0, -1))
      ν₁ := Cz F C s l (0, 1) (1, 0) (1, 1)
      ν₂ := Cz F C s l (0, 1) (1, 0) (1, 2)
      ρ₁ := Cz F C s l (0, -1) (1, 1) (1, 1)
      ρ₂ := Cz F C s l (0, -1) (1, 1) (1, 2)
      lam := Cz F C s l (1, 1) (1, 0) (1, 1)
      ηa := wsign hE l (pair s l (1, 0))
      ηc := wsign hE l (pair s l (1, 1))
      ηd := wsign hE l (pair s l (2, 1))
      add_a := x_add' hE rA
      add_c := x_add' hE rC
      add_d := x_add' hE rD
      add_b := x_add' hE rB
      add_b' := x_add' hE rB'
      comm_da := cDA
      comm_dc := cDC
      rel_ca := hrel
      conj_b_a := fun t' v => by
        rw [conj_eq_comm hE rB, comm_eq_two' hE hdiv hcsl hcls (u₁ := (1, 1)) (u₂ := (2, 1)) mB mA
          (by decide) (by decide) (by decide) (by decide)]
      conj_b_c := fun t' v => by
        rw [conj_eq_comm hE rB, comm_eq_one hE hdiv hcsl hcls mB mC (by decide) (by decide),
          one_mul]
      conj_b_d := fun t' v => by
        rw [conj_eq_comm hE rB, comm_eq_one hE hdiv hcsl hcls mB mD (by decide) (by decide),
          one_mul]
      conj_b'_a := fun t' v => by
        rw [conj_eq_comm hE rB', comm_eq_one hE hdiv hcsl hcls mB' mA (by decide) (by decide),
          one_mul]
      conj_b'_c := fun t' v => by
        rw [conj_eq_comm hE rB', comm_eq_two' hE hdiv hcsl hcls (u₁ := (1, 0)) (u₂ := (2, 1)) mB' mC
          (by decide) (by decide) (by decide) (by decide)]
      conj_b'_d := fun t' v => by
        rw [conj_eq_comm hE rB', comm_eq_one hE hdiv hcsl hcls mB' mD (by decide) (by decide),
          one_mul]
      conj_n_a := hNa
      conj_n_c := hNc
      conj_n_d := hNd
      ext := fun u₁ u₂ u₃ u₁' u₂' u₃' h =>
        ext3 hE rA rC rD (fun e => absurd (pair_injective hsl e) (by decide))
          (fun e => absurd (pair_injective hsl e) (by decide))
          (fun e => absurd (pair_injective hsl e) (by decide)) (funcl s l (1, 0))
          (by rw [funcl_pair hsl]; decide) (by rw [funcl_pair hsl]; decide)
          (by rw [funcl_pair hsl]; decide) (by rw [funcl_pair hsl, funcl_pair hsl]; decide)
          (by rw [funcl_pair hsl, funcl_pair hsl]; decide) h }
  exact H.result

end HModule

end CFSG.ClassicalInvolution.WeakCT
