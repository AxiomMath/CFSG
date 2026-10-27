module

public import CFSG.GF2Type.Aschbacher1976Full.WidthCbit

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG Subgroup
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section Form

variable {z : G} {F : Subgroup G}

noncomputable def rep (q : ↥F ⧸ Subgroup.center ↥F) : ↥F :=
  Classical.choose (QuotientGroup.mk_surjective q)

theorem mk_rep (q : ↥F ⧸ Subgroup.center ↥F) :
    (QuotientGroup.mk (rep q) : ↥F ⧸ Subgroup.center ↥F) = q :=
  Classical.choose_spec (QuotientGroup.mk_surjective q)

theorem center_comm {c : ↥F} (hc : c ∈ Subgroup.center ↥F) (f : G) (hf : f ∈ F) :
    (c : G) * f = f * c := by
  have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨f, hf⟩)
  simp only [Subgroup.coe_mul] at h2
  exact h2.symm

theorem cbit_rep_left (hF : CData z F) (u v : ↥F) :
    cbit z (rep (QuotientGroup.mk u) : G) (v : G) = cbit z (u : G) (v : G) := by
  have h := QuotientGroup.eq.mp (mk_rep (QuotientGroup.mk u))
  have hu : (u : G) = ((rep (QuotientGroup.mk u) : ↥F) : G) *
      (((rep (QuotientGroup.mk u))⁻¹ * u : ↥F) : G) := by
    simp
  rw [hu, cbit_mul_central hF (rep (QuotientGroup.mk u)).2 ((rep (QuotientGroup.mk u))⁻¹ * u).2
    (center_comm h) v.2]

theorem cbit_rep_right (hF : CData z F) (u v : ↥F) :
    cbit z (u : G) (rep (QuotientGroup.mk v) : G) = cbit z (u : G) (v : G) := by
  have h := QuotientGroup.eq.mp (mk_rep (QuotientGroup.mk v))
  have hv : ((((rep (QuotientGroup.mk v))⁻¹ * v : ↥F) : G)) * ((rep (QuotientGroup.mk v) : ↥F) : G)
      = (v : G) := by
    rw [center_comm h (rep (QuotientGroup.mk v) : G) (rep (QuotientGroup.mk v)).2]
    simp
  rw [← hv, cbit_central_mul hF u.2 ((rep (QuotientGroup.mk v))⁻¹ * v).2 (center_comm h)
    (rep (QuotientGroup.mk v)).2]

noncomputable def bV (z : G) (F : Subgroup G) (a b : Additive (↥F ⧸ Subgroup.center ↥F)) :
    ZMod 2 :=
  cbit z ((rep (Additive.toMul a) : ↥F) : G) ((rep (Additive.toMul b) : ↥F) : G)

theorem bV_zero_left (hF : CData z F) (n : Additive (↥F ⧸ Subgroup.center ↥F)) :
    bV z F 0 n = 0 := by
  unfold bV
  have h2 := cbit_rep_left hF 1 (rep (Additive.toMul n))
  rw [QuotientGroup.mk_one] at h2
  have h1 : Additive.toMul (0 : Additive (↥F ⧸ Subgroup.center ↥F)) = 1 := rfl
  rw [h1, h2]
  simp [cbit]

theorem bV_zero_right (hF : CData z F) (m : Additive (↥F ⧸ Subgroup.center ↥F)) :
    bV z F m 0 = 0 := by
  unfold bV
  have h2 := cbit_rep_right hF (rep (Additive.toMul m)) 1
  rw [QuotientGroup.mk_one] at h2
  have h1 : Additive.toMul (0 : Additive (↥F ⧸ Subgroup.center ↥F)) = 1 := rfl
  rw [h1, h2]
  simp [cbit]

theorem bV_add_left (hF : CData z F) (m₁ m₂ n : Additive (↥F ⧸ Subgroup.center ↥F)) :
    bV z F (m₁ + m₂) n = bV z F m₁ n + bV z F m₂ n := by
  unfold bV
  have hu : (QuotientGroup.mk (rep (Additive.toMul m₁) * rep (Additive.toMul m₂)) :
      ↥F ⧸ Subgroup.center ↥F) = Additive.toMul (m₁ + m₂) := by
    rw [QuotientGroup.mk_mul, mk_rep, mk_rep]
    rfl
  rw [← hu, cbit_rep_left hF]
  simp only [Subgroup.coe_mul]
  exact cbit_mul_left hF (rep _).2 (rep _).2 (rep _).2

theorem bV_add_right (hF : CData z F) (m n₁ n₂ : Additive (↥F ⧸ Subgroup.center ↥F)) :
    bV z F m (n₁ + n₂) = bV z F m n₁ + bV z F m n₂ := by
  unfold bV
  have hu : (QuotientGroup.mk (rep (Additive.toMul n₁) * rep (Additive.toMul n₂)) :
      ↥F ⧸ Subgroup.center ↥F) = Additive.toMul (n₁ + n₂) := by
    rw [QuotientGroup.mk_mul, mk_rep, mk_rep]
    rfl
  rw [← hu, cbit_rep_right hF]
  simp only [Subgroup.coe_mul]
  exact cbit_mul_right hF (rep _).2 (rep _).2 (rep _).2

theorem isEA_quot (hF : CData z F) : CFSG.IsElementaryAbelian 2 (↥F ⧸ Subgroup.center ↥F) := by
  have hcen : ∀ t : ↥F, ((t : G) = 1 ∨ (t : G) = z) → t ∈ Subgroup.center ↥F := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rcases ht with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]
      exact (hF.zc g.1 g.2).symm
  have hcomm : ∀ a b : ↥F ⧸ Subgroup.center ↥F, a * b = b * a := by
    intro a b
    obtain ⟨r1, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨r2, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    apply hcen
    have e : (((r1 * r2)⁻¹ * (r2 * r1) : ↥F) : G) = ⁅((r2 : G))⁻¹, ((r1 : G))⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact hF.comm _ (Subgroup.inv_mem _ r2.2) _ (Subgroup.inv_mem _ r1.2)
  have hexp : Monoid.exponent (↥F ⧸ Subgroup.center ↥F) ∣ 2 := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply hcen
    have hcoe : (((r ^ 2 : ↥F)) : G) = (r : G) ^ 2 := by simp
    rw [hcoe]
    exact hF.sq _ r.2
  exact { is_comm := ⟨hcomm⟩, exponent_dvd_p := hexp }

section Bil

variable [Fact (Nat.Prime 2)] [CFSG.IsElementaryAbelian 2 (↥F ⧸ Subgroup.center ↥F)]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  exacts [Or.inl rfl, Or.inr rfl]

theorem bV_smul_left (hF : CData z F) (c : ZMod 2) (m n : Additive (↥F ⧸ Subgroup.center ↥F)) :
    bV z F (c • m) n = c • bV z F m n := by
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul, zero_smul, bV_zero_left hF]
  · rw [one_smul, one_smul]

theorem bV_smul_right (hF : CData z F) (c : ZMod 2) (m n : Additive (↥F ⧸ Subgroup.center ↥F)) :
    bV z F m (c • n) = c • bV z F m n := by
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul, zero_smul, bV_zero_right hF]
  · rw [one_smul, one_smul]

noncomputable def bil (hF : CData z F) :
    LinearMap.BilinForm (ZMod 2) (Additive (↥F ⧸ Subgroup.center ↥F)) :=
  LinearMap.mk₂ (ZMod 2) (bV z F) (bV_add_left hF) (bV_smul_left hF) (bV_add_right hF)
    (bV_smul_right hF)

theorem bil_apply (hF : CData z F) (m n : Additive (↥F ⧸ Subgroup.center ↥F)) :
    bil hF m n = bV z F m n := by
  unfold bil
  rw [LinearMap.mk₂_apply]

theorem cbit_comm (x y : G) : cbit z x y = cbit z y x := by
  have hiff : ⁅x, y⁆ = 1 ↔ ⁅y, x⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm, commutatorElement_eq_one_iff_mul_comm]
    exact eq_comm
  by_cases h : ⁅x, y⁆ = 1
  · have h' := hiff.mp h
    simp [cbit, h, h']
  · have h' : ¬ ⁅y, x⁆ = 1 := fun h'' => h (hiff.mpr h'')
    simp [cbit, h, h']

theorem bil_symm (hF : CData z F) (m n : Additive (↥F ⧸ Subgroup.center ↥F)) :
    bil hF m n = bil hF n m := by
  rw [bil_apply, bil_apply]
  unfold bV
  exact cbit_comm _ _

theorem bil_sep_left (hF : CData z F) (m : Additive (↥F ⧸ Subgroup.center ↥F))
    (hm : ∀ n, bil hF m n = 0) : m = 0 := by
  have hc : ∀ v : ↥F, ⁅(rep (Additive.toMul m) : G), (v : G)⁆ = 1 := by
    intro v
    have h := hm (Additive.ofMul (QuotientGroup.mk v))
    rw [bil_apply] at h
    unfold bV at h
    change cbit z ((rep (Additive.toMul m) : ↥F) : G) ((rep (QuotientGroup.mk v) : ↥F) : G) = 0 at h
    rw [cbit_rep_right hF] at h
    by_contra hne
    simp [cbit, hne] at h
  have hcen : rep (Additive.toMul m) ∈ Subgroup.center ↥F := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hc g)).symm
  have hq : Additive.toMul m = 1 := by
    rw [← mk_rep (Additive.toMul m), QuotientGroup.eq_one_iff]
    exact hcen
  have hm0 : m = Additive.ofMul (Additive.toMul m) := rfl
  rw [hm0, hq]
  rfl

theorem bil_nondegenerate (hF : CData z F) : (bil hF).Nondegenerate :=
  ⟨fun m hm => bil_sep_left hF m hm, fun n hn => bil_sep_left hF n (fun m => by
    rw [bil_symm]; exact hn m)⟩

theorem bil_alt (hF : CData z F) : (bil hF).IsAlt := by
  intro v
  rw [bil_apply]
  unfold bV
  exact cbit_self _

theorem bil_hrule (hF : CData z F) (x y : ↥F) :
    ⁅x, y⁆ = (⟨z, hF.zF⟩ : ↥F) ^ (bil hF (Additive.ofMul (QuotientGroup.mk x))
      (Additive.ofMul (QuotientGroup.mk y))).val := by
  have hb : bil hF (Additive.ofMul (QuotientGroup.mk x)) (Additive.ofMul (QuotientGroup.mk y)) =
      cbit z (x : G) (y : G) := by
    rw [bil_apply]
    unfold bV
    change cbit z ((rep (QuotientGroup.mk x) : ↥F) : G) ((rep (QuotientGroup.mk y) : ↥F) : G) = _
    rw [cbit_rep_left hF, cbit_rep_right hF]
  rw [hb]
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  show ⁅(x : G), (y : G)⁆ = z ^ (cbit z (x : G) (y : G)).val
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  rcases hF.comm (x : G) x.2 (y : G) y.2 with h | h
  · rw [h]
    simp [cbit, h]
  · rw [h]
    simp [cbit, h, hF.z1, hv1]

end Bil

end Form

end CFSG.GF2Type.Aschbacher1976Full.Width
