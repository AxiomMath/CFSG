module

public import CFSG.LargeExtraspecial.AS35KFixB
public import CFSG.LargeExtraspecial.AS35KBridgeMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.Blueprint.Fischer (K)

namespace AS35K

variable {m : ℕ} {A : GL (Fin m) K} {φ : K ≃+* K}

theorem herm_sub_smul_eq_zero {e f : Fin m → K} (hef : herm frob e f = 1) (x : Fin m → K) :
    herm frob e (x - herm frob e x • f) = 0 := by
  rw [sub_eq_add_neg, herm_add_right, herm_neg_right, herm_smul_right, hef, mul_one, add_neg_cancel]

theorem semi_formula (hm : 4 ≤ m) {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0)
    (hA : A ∈ primeFormUnitary AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))
    (hcomm : ∀ a ∈ Rhat m e, ∀ x, semi A φ (a • x) = a • semi A φ x) :
    ∃ l : K, l ≠ 0 ∧ ∃ s : K, (s = 0 ∨ s = 1) ∧
      ∀ x, semi A φ x = l • (x + (s * herm frob e x) • e) := by
  have hm3 : 3 ≤ m := by omega
  have hφ := phi_eq hm he0 he hcomm
  obtain ⟨f, hff, hef, -⟩ := exists_flag_data hm he0 he
  set l := herm frob e (semi A φ f) with hl
  have hSe : semi A φ e = l • e := semi_e hm3 he0 he hef hcomm
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hSe
    exact semi_ne_zero A φ he0 hSe
  set d := semi A φ f - l • f with hd
  have hSf : semi A φ f = l • f + d := by rw [hd]; abel
  have hed : herm frob e d = 0 := by
    rw [hd, sub_eq_add_neg, herm_add_right, herm_neg_right, herm_smul_right, hef, mul_one, ← hl,
      add_neg_cancel]
  have hud_eq : ∀ u, herm frob u d = herm frob u (semi A φ f) - l * herm frob u f := by
    intro u
    rw [hd, sub_eq_add_neg (semi A φ f), herm_add_right, herm_neg_right, herm_smul_right,
      sub_eq_add_neg]
  have hSu : ∀ u, herm frob e u = 0 → semi A φ u = l • u + herm frob u d • e := by
    intro u heu
    obtain ⟨c, hc⟩ := exists_add_frob_eq (herm_self_eq_zero_or_one u)
    rw [semi_flag hm3 he0 he hef heu hc hcomm, hφ, ← hl, hud_eq]
    congr 2
    ring
  have ht : ∀ u, herm frob e u = 0 →
      frob l * herm frob u d = 0 ∨ frob l * herm frob u d = 1 := by
    intro u heu
    have h1 := herm_semi hA φ u f
    rw [hSu u heu, hφ, hSf] at h1
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hef, hed] at h1
    apply (add_frob_eq_zero_iff _).mp
    rw [map_mul, frob_frob]
    linear_combination h1 - herm frob u f * frob_mul_self hl0
  have hud : ∀ u, herm frob e u = 0 → herm frob u d = 0 := by
    intro u heu
    rcases ht u heu with h0 | h1
    · rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (frob_ne_zero hl0)
      · exact h
    · exfalso
      have heωu : herm frob e (ω • u) = 0 := by rw [herm_smul_right, heu, mul_zero]
      have h2 := ht (ω • u) heωu
      have h3 : frob l * herm frob (ω • u) d = frob ω := by
        rw [herm_smul_left]
        linear_combination frob ω * h1
      rw [h3] at h2
      rcases h2 with h | h
      · exact frob_ne_zero omega_ne_zero h
      · exact frob_omega_ne_one h
  set γ := herm frob f d with hγ
  have hdγ : d = γ • e := by
    have h0 : ∀ x, herm frob x (d - γ • e) = 0 := by
      intro x
      have h1 := hud _ (herm_sub_smul_eq_zero hef x)
      have h2 : herm frob x d = frob (herm frob e x) * γ := by
        have hx : x = (x - herm frob e x • f) + herm frob e x • f := by abel
        rw [hx, herm_add_left, h1, herm_smul_left, zero_add]
        congr 2
        rw [herm_add_right, herm_smul_right, hef, mul_one, herm_sub_smul_eq_zero hef, zero_add]
      have h3 : herm frob x e = frob (herm frob e x) := herm_conj frob frob_frob e x
      rw [sub_eq_add_neg, herm_add_right, herm_neg_right, herm_smul_right, h2, h3]
      ring
    have h1 : d - γ • e = 0 := eq_zero_of_herm (σ := frob) fun y => by
      rw [herm_conj frob frob_frob, h0 y, map_zero]
    exact sub_eq_zero.mp h1
  have hfe : herm frob f e = 1 := by rw [herm_conj frob frob_frob, hef, map_one]
  set s := frob l * γ with hs
  have hs01 : s = 0 ∨ s = 1 := by
    have h1 := herm_semi hA φ f f
    rw [hSf, hdγ, hff, map_zero] at h1
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hff, hfe, hef,
      he] at h1
    apply (add_frob_eq_zero_iff _).mp
    rw [hs, map_mul, frob_frob]
    linear_combination h1
  have hγs : γ = l * s := by
    rw [hs, ← mul_assoc, mul_frob_self hl0, one_mul]
  refine ⟨l, hl0, s, hs01, fun x => ?_⟩
  have hx : x = (x - herm frob e x • f) + herm frob e x • f := by abel
  conv_lhs => rw [hx]
  rw [semi_add, semi_smul, hSu _ (herm_sub_smul_eq_zero hef x), hud _ (herm_sub_smul_eq_zero hef x),
    hSf, hdγ, hγs, hφ]
  module

theorem scalar_mulVec (c : Kˣ) (x : Fin m → K) :
    ((GeneralLinearGroup.scalar (Fin m) c : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x =
      (c : K) • x := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  funext i
  simp [mulVec_diagonal]

theorem eq_one_or_conj_of_fix (hm : 4 ≤ m) {e : Fin m → K} (he0 : e ≠ 0)
    (he : herm frob e e = 0) (β : MulAut (PG m)) (hβ : ∀ x ∈ Rbar m e, β x = x) :
    β = 1 ∨ β = MulAut.conj (tq e) := by
  have hm3 : 3 ≤ m := by omega
  obtain ⟨A, φ, hreal⟩ := exists_realize hm β
  have hcomm : ∀ a ∈ Rhat m e, ∀ x,
      semi (A : GL (Fin m) K) φ (a • x) = a • semi (A : GL (Fin m) K) φ x := by
    intro a ha x
    obtain ⟨g', hg', hβg⟩ := hreal a
    have hfix := hβ (QuotientGroup.mk a) ⟨a, ha, rfl⟩
    rw [hβg, QuotientGroup.eq] at hfix
    obtain ⟨k, hk⟩ := isPGroup_Rhat hm3 he0 he ⟨a, ha⟩
    have hak : a ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hg'k : g' ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, hg', conj_pow, ← map_pow, ← SubgroupClass.coe_pow, hak]
      simp
    have hcz : Commute g'⁻¹ a := by
      have hz := Subgroup.mem_center_iff.mp hfix g'⁻¹
      have : g'⁻¹ * a = a * g'⁻¹ := by
        calc g'⁻¹ * a = g' * (g'⁻¹ * (g'⁻¹ * a)) := by group
          _ = g' * ((g'⁻¹ * a) * g'⁻¹) := by rw [hz]
          _ = a * g'⁻¹ := by group
      exact this
    have hζ : (g'⁻¹ * a) ^ 2 ^ k = 1 := by rw [hcz.mul_pow, inv_pow, hg'k, hak, inv_one, one_mul]
    have hga : g' = a := inv_mul_eq_one.mp (AS35U.eq_one_of_mem_center hm3 hfix hζ)
    refine semi_smul_of_conj ?_ x
    rw [← hg', hga]
  obtain ⟨l, hl, s, hs, hSx⟩ := semi_formula hm he0 he A.2 hcomm
  have hφ := phi_eq hm he0 he hcomm
  have hglφ : ∀ g : GL (Fin m) K, glAut φ g = g := fun g => Units.ext (by
    rw [coe_glAut]
    ext i j
    simp [hφ])
  have hAx : ∀ x, ((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x =
      l • (x + (s * herm frob e x) • e) := by
    intro x
    have h1 := hSx x
    rwa [semi, show (φ ∘ x) = x from funext fun i => hφ (x i)] at h1
  set lu : Kˣ := Units.mk0 l hl
  have hconj : ∀ T g : GL (Fin m) K, (GeneralLinearGroup.scalar (Fin m) lu * T) * g *
      (GeneralLinearGroup.scalar (Fin m) lu * T)⁻¹ = T * g * T⁻¹ := by
    intro T g
    have h1 := (commute_scalar lu (T * g * T⁻¹)).eq
    calc (GeneralLinearGroup.scalar (Fin m) lu * T) * g *
          (GeneralLinearGroup.scalar (Fin m) lu * T)⁻¹ =
        GeneralLinearGroup.scalar (Fin m) lu * (T * g * T⁻¹) *
          (GeneralLinearGroup.scalar (Fin m) lu)⁻¹ := by group
      _ = T * g * T⁻¹ := by rw [← h1, mul_inv_cancel_right]
  rcases hs with rfl | rfl
  · have hAsc : (A : GL (Fin m) K) = GeneralLinearGroup.scalar (Fin m) lu * 1 := gl_ext fun x => by
      rw [hAx x, mul_one, scalar_mulVec, Units.val_mk0, zero_mul, zero_smul, add_zero]
    left
    refine MulEquiv.ext fun y => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g', hg', hβg⟩ := hreal g
    rw [hβg, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [hg', hglφ, hAsc, hconj, one_mul, inv_one, mul_one]
  · have hAsc : (A : GL (Fin m) K) = GeneralLinearGroup.scalar (Fin m) lu * (tvU e : GL _ _) :=
      gl_ext fun x => by
        rw [hAx x, Units.val_mul, ← mulVec_mulVec, scalar_mulVec, Units.val_mk0, one_mul,
          coe_tvU_mulVec he]
    right
    refine MulEquiv.ext fun y => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g', hg', hβg⟩ := hreal g
    rw [hβg, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    rw [hg', hglφ, hAsc, hconj]
    rfl

end AS35K

namespace S14

theorem unitaryAutFacts {m : ℕ} (hm : 4 ≤ m) : UnitaryAutFacts m :=
  ⟨fun β _ hd => AS35K.map_DG hm β hd,
    fun _ he0 he β hβ => AS35K.eq_one_or_conj_of_fix hm he0 he β hβ⟩

theorem aschTwoAutStmt_of_unitaryModel
    (hId : AschTwoUnitaryModelStmt) : AschTwoAutStmt :=
  aschTwoAutStmt_of_model (fun _ hm => unitaryAutFacts hm) hId

end S14

end CFSG.LargeExtraspecial
