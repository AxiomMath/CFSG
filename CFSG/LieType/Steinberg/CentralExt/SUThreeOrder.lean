module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.LieType.Universal.Unitary.Extras.RankOneLast
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.LieType.Steinberg

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras

theorem card_eq_of_rankOne_bruhat {G : Type*} [Group G] [Finite G] (H X : Subgroup G) (w : G)
    (hHX : ∀ g ∈ H, g ∈ X → g = 1)
    (hcell : ∀ h ∈ H, ∀ u ∈ X, ∀ u' ∈ X, ∀ h' ∈ H, ∀ v' ∈ X, h * u ≠ u' * w * h' * v')
    (hw : ∀ y ∈ X, ∀ h ∈ H, ∀ v ∈ X, ∀ h' ∈ H, ∀ v' ∈ X, y * w * h * v = w * h' * v' → y = 1)
    (hcov : ∀ g : G, (∃ h ∈ H, ∃ u ∈ X, g = h * u) ∨
      ∃ u ∈ X, ∃ h ∈ H, ∃ v ∈ X, g = u * w * h * v) :
    Nat.card G = Nat.card H * Nat.card X + Nat.card X * (Nat.card H * Nat.card X) := by
  have hB : ∀ h ∈ H, ∀ u ∈ X, ∀ h' ∈ H, ∀ u' ∈ X, h * u = h' * u' → h = h' ∧ u = u' := by
    intro h hh u hu h' hh' u' hu' heq
    have e : h'⁻¹ * h = u' * u⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq, mul_inv_cancel_right]
    have h1 : h'⁻¹ * h = 1 :=
      hHX _ (H.mul_mem (H.inv_mem hh') hh) (e ▸ X.mul_mem hu' (X.inv_mem hu))
    have hh_eq : h = h' := (inv_mul_eq_one.mp h1).symm
    subst hh_eq
    exact ⟨rfl, mul_left_cancel heq⟩
  let φ : (H × X) ⊕ (X × H × X) → G := fun
    | .inl (h, u) => h * u
    | .inr (u, h, v) => u * w * h * v
  have hφ : Function.Bijective φ := by
    constructor
    · rintro (⟨⟨h, hh⟩, ⟨u, hu⟩⟩ | ⟨⟨u, hu⟩, ⟨h, hh⟩, ⟨v, hv⟩⟩)
        (⟨⟨h', hh'⟩, ⟨u', hu'⟩⟩ | ⟨⟨u', hu'⟩, ⟨h', hh'⟩, ⟨v', hv'⟩⟩) heq
      · obtain ⟨rfl, rfl⟩ := hB h hh u hu h' hh' u' hu' heq
        rfl
      · exact absurd heq (hcell h hh u hu u' hu' h' hh' v' hv')
      · exact absurd heq.symm (hcell h' hh' u' hu' u hu h hh v hv)
      · change u * w * h * v = u' * w * h' * v' at heq
        have hy : u'⁻¹ * u * w * h * v = w * h' * v' := by
          simp only [mul_assoc] at heq ⊢
          rw [heq, inv_mul_cancel_left]
        have huu : u = u' :=
          (inv_mul_eq_one.mp (hw _ (X.mul_mem (X.inv_mem hu') hu) h hh v hv h' hh' v' hv' hy)).symm
        subst huu
        have hhv : h * v = h' * v' := by
          simp only [mul_assoc] at heq
          exact mul_left_cancel (mul_left_cancel heq)
        obtain ⟨rfl, rfl⟩ := hB h hh v hv h' hh' v' hv' hhv
        rfl
    · intro g
      rcases hcov g with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
      · exact ⟨.inl (⟨h, hh⟩, ⟨u, hu⟩), rfl⟩
      · exact ⟨.inr (⟨u, hu⟩, ⟨h, hh⟩, ⟨v, hv⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_sum, Nat.card_prod, Nat.card_prod,
    Nat.card_prod]

section Cells

variable {F : Type*} [Field F] {σ : F ≃+* F}

theorem heisenbergMatrix_three (a b : F) :
    heisenbergMatrix σ (0 : Fin 3) 1 a b = !![1, a, b; 0, 1, -σ a; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisenbergMatrix]

variable (hσ : ∀ c, σ (σ c) = c)

theorem rootGroup_three_eq_heisenbergSubgroup :
    rootGroup σ hσ 3 (Pi.single 0 1) =
      heisenbergSubgroup σ hσ (i := 0) (k := 1) (by decide) (by decide) (by decide) := by
  refine le_antisymm ?_ (heisenberg_le hσ _ _ _ (by decide))
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun _ => ?_
    exfalso
    revert hij hi hj hji
    fin_cases i <;> fin_cases j <;> decide
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    exfalso
    revert hw
    fin_cases i <;> decide
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    have hi0 : i = 0 := by
      revert hw
      fin_cases i <;> decide
    have hk1 : k = 1 := by
      revert hk
      fin_cases k <;> decide
    subst hi0 hk1
    exact le_rfl

theorem mem_rootGroup_three {x : SU σ 3} :
    x ∈ rootGroup σ hσ 3 (Pi.single 0 1) ↔
      ∃ a b : F, b + σ b + σ a * a = 0 ∧ mat σ 3 x = !![1, a, b; 0, 1, -σ a; 0, 0, 1] := by
  rw [rootGroup_three_eq_heisenbergSubgroup hσ]
  simp only [← heisenbergMatrix_three]
  rfl

omit hσ in
theorem exists_mat_eq_diagonal_of_mem_levelTorus_three {h : SU σ 3}
    (hh : h ∈ levelTorus σ (0 : Fin (3 / 2))) :
    ∃ t : Fˣ, mat σ 3 h = diagonal ![(t : F), σ t / t, (σ t)⁻¹] := by
  obtain ⟨c, hc⟩ := exists_tFun_of_mem_levelTorus hh
  refine ⟨c, ?_⟩
  rw [hc]
  congr 1
  funext s
  have h3 : ¬Even 3 := by decide
  fin_cases s <;> simp [tFun, heisTorusFun, lowIdx, h3]

theorem mat_levelWeyl_three {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) :
    mat σ 3 (levelWeyl hσ ζ (0 : Fin (3 / 2))) =
      !![0, 0, (ζ : F); 0, 1, 0; -(ζ : F)⁻¹, 0, 0] := by
  rw [mat_apply, coe_levelWeyl hσ hζ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Universal.SpecialLinear.signedPerm_apply, levelPerm, levelSign, longSign,
      Equiv.swap_apply_def, lowIdx]

theorem blockTriangular_of_mem_rootGroup_three {x : SU σ 3}
    (hx : x ∈ rootGroup σ hσ 3 (Pi.single 0 1)) : (mat σ 3 x).BlockTriangular id := by
  obtain ⟨a, b, -, hx⟩ := (mem_rootGroup_three hσ).1 hx
  rw [hx]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

omit hσ in
theorem blockTriangular_of_mem_levelTorus_three {h : SU σ 3}
    (hh : h ∈ levelTorus σ (0 : Fin (3 / 2))) : (mat σ 3 h).BlockTriangular id := by
  obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh
  rw [ht]
  exact blockTriangular_diagonal _

theorem eq_one_of_mem_levelTorus_three {g : SU σ 3} (hg : g ∈ levelTorus σ (0 : Fin (3 / 2)))
    (hg' : g ∈ rootGroup σ hσ 3 (Pi.single 0 1)) : g = 1 := by
  obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hg
  obtain ⟨a, b, -, hx⟩ := (mem_rootGroup_three hσ).1 hg'
  apply mat_injective
  rw [map_one]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [hx, one_apply_eq]
    fin_cases i <;> simp
  · rw [ht, diagonal_apply_ne _ hij, one_apply_ne hij]

theorem mul_ne_mul_levelWeyl_three {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) {h u u' h' v' : SU σ 3}
    (hh : h ∈ levelTorus σ (0 : Fin (3 / 2))) (hu : u ∈ rootGroup σ hσ 3 (Pi.single 0 1))
    (hu' : u' ∈ rootGroup σ hσ 3 (Pi.single 0 1)) (hh' : h' ∈ levelTorus σ (0 : Fin (3 / 2)))
    (hv' : v' ∈ rootGroup σ hσ 3 (Pi.single 0 1)) :
    h * u ≠ u' * levelWeyl hσ ζ 0 * h' * v' := by
  intro heq
  have e : levelWeyl hσ ζ 0 * h' = u'⁻¹ * h * u * v'⁻¹ := by
    rw [mul_assoc u'⁻¹ h u, heq]
    group
  have hUT : (mat σ 3 (u'⁻¹ * h * u * v'⁻¹)).BlockTriangular id := by
    simp only [map_mul]
    exact (((blockTriangular_of_mem_rootGroup_three hσ (inv_mem hu')).mul
      (blockTriangular_of_mem_levelTorus_three hh)).mul
        (blockTriangular_of_mem_rootGroup_three hσ hu)).mul
      (blockTriangular_of_mem_rootGroup_three hσ (inv_mem hv'))
  have h20 := hUT (i := 2) (j := 0) (by decide)
  rw [← e, map_mul, mat_levelWeyl_three hσ hζ] at h20
  obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh'
  rw [ht] at h20
  simp [Matrix.mul_apply, Fin.sum_univ_three, hζ] at h20

theorem eq_one_of_mul_levelWeyl_three {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) {y h v h' v' : SU σ 3}
    (hy : y ∈ rootGroup σ hσ 3 (Pi.single 0 1)) (hh : h ∈ levelTorus σ (0 : Fin (3 / 2)))
    (hv : v ∈ rootGroup σ hσ 3 (Pi.single 0 1)) (hh' : h' ∈ levelTorus σ (0 : Fin (3 / 2)))
    (hv' : v' ∈ rootGroup σ hσ 3 (Pi.single 0 1))
    (heq : y * levelWeyl hσ ζ 0 * h * v = levelWeyl hσ ζ 0 * h' * v') : y = 1 := by
  have e : y * levelWeyl hσ ζ 0 = levelWeyl hσ ζ 0 * (h' * v' * v⁻¹ * h⁻¹) := by
    calc y * levelWeyl hσ ζ 0 = y * levelWeyl hσ ζ 0 * h * v * v⁻¹ * h⁻¹ := by group
      _ = levelWeyl hσ ζ 0 * h' * v' * v⁻¹ * h⁻¹ := by rw [heq]
      _ = levelWeyl hσ ζ 0 * (h' * v' * v⁻¹ * h⁻¹) := by group
  have hUT : (mat σ 3 (h' * v' * v⁻¹ * h⁻¹)).BlockTriangular id := by
    simp only [map_mul]
    exact (((blockTriangular_of_mem_levelTorus_three hh').mul
      (blockTriangular_of_mem_rootGroup_three hσ hv')).mul
        (blockTriangular_of_mem_rootGroup_three hσ (inv_mem hv))).mul
      (blockTriangular_of_mem_levelTorus_three (inv_mem hh))
  have h20 := hUT (i := 2) (j := 0) (by decide)
  have h21 := hUT (i := 2) (j := 1) (by decide)
  obtain ⟨a, b, -, hy'⟩ := (mem_rootGroup_three hσ).1 hy
  have e' := congrArg (mat σ 3) e
  rw [map_mul, map_mul (mat σ 3) (levelWeyl hσ ζ 0), hy', mat_levelWeyl_three hσ hζ] at e'
  generalize mat σ 3 (h' * v' * v⁻¹ * h⁻¹) = M at h20 h21 e'
  have h00 := congrFun (congrFun e' 0) 0
  have h01 := congrFun (congrFun e' 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21, hζ] at h00 h01
  apply mat_injective
  rw [hy', map_one, h00, h01]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Cells

section Finite

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem card_rootGroup_three :
    Nat.card (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 3
      (Pi.single 0 1)) = (p ^ f) ^ 3 := by
  set σ := unitaryInvolution F p f
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  set X := rootGroup σ hσ 3 (Pi.single 0 1)
  have key : ∀ x : X,
      mat σ 3 x 0 2 + σ (mat σ 3 x 0 2) + σ (mat σ 3 x 0 1) * mat σ 3 x 0 1 = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨a, b, hab, hx'⟩ := (mem_rootGroup_three hσ).1 hx
    simpa [hx'] using hab
  let ψ : X → {ab : F × F // ab.2 + σ ab.2 + σ ab.1 * ab.1 = 0} :=
    fun x => ⟨(mat σ 3 x 0 1, mat σ 3 x 0 2), key x⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · rintro ⟨x, hx⟩ ⟨x', hx'⟩ hxx
      obtain ⟨a, b, -, hm⟩ := (mem_rootGroup_three hσ).1 hx
      obtain ⟨a', b', -, hm'⟩ := (mem_rootGroup_three hσ).1 hx'
      have h1 := congrArg (fun ab => ab.1.1) hxx
      have h2 := congrArg (fun ab => ab.1.2) hxx
      simp only [ψ, hm, hm'] at h1 h2
      simp at h1 h2
      refine Subtype.ext (mat_injective ?_)
      rw [hm, hm', h1, h2]
    · rintro ⟨⟨a, b⟩, hab⟩
      refine ⟨⟨heisRootElt hσ (i := 0) (k := 1) (by decide) (by decide) (by decide) a b hab,
        (rootGroup_three_eq_heisenbergSubgroup hσ).symm ▸ heisRootElt_mem hσ _ _ _ a b hab⟩, ?_⟩
      have hm : mat σ 3 (heisRootElt hσ (i := 0) (k := 1) (by decide) (by decide) (by decide)
          a b hab) = !![1, a, b; 0, 1, -σ a; 0, 0, 1] := heisenbergMatrix_three a b
      simp only [ψ, hm]
      rfl
  have htr : ∀ a : F, ∃ c : F, c + σ c = -(σ a * a) := fun a =>
    exists_add_unitaryInvolution_eq hF (by rw [map_neg, map_mul, hσ, mul_comm])
  choose c hc using htr
  let e : {ab : F × F // ab.2 + σ ab.2 + σ ab.1 * ab.1 = 0} ≃ F × traceZero σ :=
    { toFun := fun ab => (ab.1.1, ⟨ab.1.2 - c ab.1.1, by
        rw [mem_traceZero, map_sub]
        linear_combination ab.2 - hc ab.1.1⟩)
      invFun := fun az => ⟨(az.1, az.2 + c az.1), by
        have h := (mem_traceZero σ).1 az.2.2
        simp only [map_add]
        linear_combination h + hc az.1⟩
      left_inv := fun ab => by ext <;> simp
      right_inv := fun az => by ext <;> simp }
  rw [Nat.card_congr (Equiv.ofBijective ψ hψ), Nat.card_congr e, Nat.card_prod, hF,
    card_traceZero hF]
  ring

theorem card_levelTorus_three :
    Nat.card (levelTorus (unitaryInvolution F p f) (0 : Fin (3 / 2))) = (p ^ f) ^ 2 - 1 := by
  set σ := unitaryInvolution F p f
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  set H := levelTorus σ (0 : Fin (3 / 2))
  have hne : ∀ h : H, mat σ 3 h 0 0 ≠ 0 := by
    rintro ⟨h, hh⟩
    obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh
    simp [ht]
  let ψ : H → Fˣ := fun h => Units.mk0 _ (hne h)
  have hψ : Function.Bijective ψ := by
    constructor
    · rintro ⟨h, hh⟩ ⟨h', hh'⟩ hhh
      obtain ⟨t, ht⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh
      obtain ⟨t', ht'⟩ := exists_mat_eq_diagonal_of_mem_levelTorus_three hh'
      have h1 := congrArg (fun u : Fˣ => (u : F)) hhh
      simp only [ψ, Units.val_mk0, ht, ht'] at h1
      simp at h1
      have htt : t = t' := Units.ext h1
      subst htt
      exact Subtype.ext (mat_injective (ht.trans ht'.symm))
    · intro t
      obtain ⟨g, -, hg⟩ := exists_heisGen_mem_rankOne hσ hζ (fun _ hx => exists_norm_eq hF hx)
        (k := (0 : Fin (3 / 2))) (by decide) (by decide) t
      refine ⟨⟨g, heisGen_mem_levelTorus (by decide) (by decide) t hg⟩, Units.ext ?_⟩
      simp only [ψ, Units.val_mk0, mat_apply, hg]
      simp [heisTorusFun, lowIdx]
  rw [Nat.card_congr (Equiv.ofBijective ψ hψ), CFSG.ClassicalGroups.Unitary.card_units_of_card hF]

theorem rankOne_three_eq_top :
    CFSG.LieType.CurtisTits.rankOne
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 3)
      (0 : Fin (3 / 2)) = ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hD := isCTGroupDatum hF 3 (by norm_num) ζ hζ
  rw [eq_top_iff, ← hD.iSup_eq_top]
  refine iSup₂_le fun γ hγ => hD.le_rankOne 0 γ hγ fun k hk => absurd ?_ hk
  fin_cases k
  rfl

end Finite

theorem card_SU_three {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) :
    Nat.card (SU (unitaryInvolution F p f) 3) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  rw [card_eq_of_rankOne_bruhat (levelTorus _ 0) (rootGroup _ hσ 3 (Pi.single 0 1))
    (levelWeyl hσ ζ 0) (fun g hg hg' => eq_one_of_mem_levelTorus_three hσ hg hg')
    (fun h hh u hu u' hu' h' hh' v' hv' => mul_ne_mul_levelWeyl_three hσ hζ hh hu hu' hh' hv')
    (fun y hy h hh v hv h' hh' v' hv' heq =>
      eq_one_of_mul_levelWeyl_three hσ hζ hy hh hv hh' hv' heq)
    (fun g => rankOne_bruhat_last_odd (hσ := hσ) (k := 0) (by decide) (by decide) hζ
      (fun _ hx => exists_norm_eq hF hx) g (by rw [rankOne_three_eq_top hF]; trivial)),
    card_rootGroup_three hF, card_levelTorus_three hF]
  ring

end CFSG.LieType.Steinberg
