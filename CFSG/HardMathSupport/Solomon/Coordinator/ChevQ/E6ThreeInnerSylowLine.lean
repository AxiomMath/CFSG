module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenSylow

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.HardMathSupport.Timmesfeld.Torality (familyCentralizer familyKernel
  familyStabilizerSubgroup mem_familyCentralizer card_familyCentralizer
  card_familyCentralizer_inf_monomial exists_conj_le_of_isPGroup_of_not_dvd_relIndex)
open CFSG.HardMathSupport.Timmesfeld.Steinberg (rootCharHom3)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (e6Inndiag)
open CFSG.StandardType.TableBExc.E6Three (hatGroup hatAut monoHat psiHat adjointGroup_le_hatGroup
  hatGroup_le_normalizer coe_hatAut_apply rootDiagUnit_mem_monoHat rootDiagUnit_mem_hatGroup
  monomial_le_monoHat finite_hatGroup index_eq_relIndex_of_sup_eq_top)

set_option linter.unusedSectionVars false

private def e6InS_cw : Fin 3 → Fin 2 → List (Fin 6) :=
  ![![[], []], ![[], []], ![[], [3, 2, 0, 4, 3, 1, 2, 3, 4]]]

private def e6InS_node : Fin 3 → Fin 2 → Fin 6 :=
  ![![0, 2], ![4, 5], ![1, 5]]

private def e6InS_u : Fin 3 → Fin Tag.E6.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0]]

private def e6InS_v : Fin 3 → Fin Tag.E6.rank → ℤ :=
  ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![1, 1, 2, 3, 2, 1]]

private def e6InS_gw (m : Fin 3) (b : Fin 2) : List (Fin 6) :=
  e6InS_cw m b ++ [e6InS_node m b] ++ (e6InS_cw m b).reverse

private def e6InS_wd : Fin 6 → List (Fin 2) :=
  ![[], [0], [1], [0, 1], [1, 0], [0, 1, 0]]

private def e6InS_fw (m : Fin 3) (t : Fin 6) : List (Fin 6) :=
  (e6InS_wd t).flatMap (e6InS_gw m)

private def e6InS_mu : Fin 2 → Fin 6 → Fin 6 :=
  ![![1, 0, 3, 2, 5, 4], ![2, 4, 0, 5, 1, 3]]

private def e6InS_len : Fin 6 → ℕ := ![0, 1, 1, 2, 2, 3]

private def e6InS_pos : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1],
    ![1, 2, 2, 3, 2, 1]]

private theorem e6InS_roots_check : ∀ m : Fin 3,
    e6WordAct (e6InS_cw m 0) (Pi.single (e6InS_node m 0 : Fin Tag.E6.rank) 1) = e6InS_u m ∧
      e6WordAct (e6InS_cw m 1) (Pi.single (e6InS_node m 1 : Fin Tag.E6.rank) 1) =
        e6InS_v m := by
  decide +kernel

private theorem e6InS_root_mem_check : ∀ (m : Fin 3) (b : Fin 2),
    e6WordAct (e6InS_cw m b) (Pi.single (e6InS_node m b : Fin Tag.E6.rank) 1) ∈
      e6LineRoots m := by
  decide +kernel

private theorem e6InS_table_check : ∀ (m : Fin 3) (b : Fin 2) (t : Fin 6) (j : Fin Tag.E6.rank),
    e6WordAct (e6InS_gw m b ++ e6InS_fw m t) (Pi.single j 1) =
      e6WordAct (e6InS_fw m (e6InS_mu b t)) (Pi.single j 1) := by
  decide +kernel

private theorem e6InS_comm_check : ∀ (m m' : Fin 3), m ≠ m' → ∀ (b b' : Fin 2)
    (j : Fin Tag.E6.rank), e6WordAct (e6InS_gw m b ++ e6InS_gw m' b') (Pi.single j 1) =
      e6WordAct (e6InS_gw m' b' ++ e6InS_gw m b) (Pi.single j 1) := by
  decide +kernel

private theorem e6InS_orbit_check : ∀ (m : Fin 3) (t t' : Fin 6),
    e6WordAct (e6InS_fw m t) (e6InS_u m) = e6WordAct (e6InS_fw m t') (e6InS_u m) → t = t' := by
  decide +kernel

private theorem e6InS_fix_check : ∀ t : Fin 6,
    e6WordAct (e6InS_fw 1 t) (e6InS_u 0) = e6InS_u 0 ∧
      e6WordAct (e6InS_fw 2 t) (e6InS_u 0) = e6InS_u 0 ∧
        e6WordAct (e6InS_fw 2 t) (e6InS_u 1) = e6InS_u 1 := by
  decide +kernel

private theorem e6InS_sum_check : ∀ m : Fin 3,
    e6WordAct (e6InS_gw m 0) (e6InS_v m) = e6InS_u m + e6InS_v m := by
  decide +kernel

private theorem e6InS_pos_check :
    (∀ α ∈ e6InS_pos, (∃ i, α ∈ e6LineRoots i) ∧ 0 < height α) ∧
      ∀ i, ∀ α ∈ e6LineRoots i, 0 < height α → α ∈ e6InS_pos := by
  decide +kernel

private theorem e6InS_pos_nodup : e6InS_pos.Nodup := by
  decide +kernel

private theorem e6InS_k_check : ∀ x : Fin 6 × Fin 6 × Fin 6,
    (e6InS_pos.filter fun α => decide (height (e6WordAct (e6InS_fw 0 x.1)
      (e6WordAct (e6InS_fw 1 x.2.1) (e6WordAct (e6InS_fw 2 x.2.2) α))) < 0)).length =
      e6InS_len x.1 + e6InS_len x.2.1 + e6InS_len x.2.2 := by
  decide +kernel

private theorem e6InS_cube_check : ∀ r < 81, r % 3 = 1 →
    (1 + 2 * r + 2 * r ^ 2 + r ^ 3) ^ 3 % 81 = 54 := by
  decide +kernel

private theorem e6InS_arith {I H Ω Q q : ℕ} (hH : 0 < H) (hΩ : 0 < Ω) (hq : q % 3 = 1)
    (hQ : Nat.Coprime 3 Q)
    (h : I * (H * (216 * Ω)) = H * Q * (Ω * (1 + 2 * q + 2 * q ^ 2 + q ^ 3) ^ 3)) :
    ¬ 3 ∣ I := by
  have key : 216 * I = Q * (1 + 2 * q + 2 * q ^ 2 + q ^ 3) ^ 3 := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hH hΩ) ?_
    calc H * Ω * (216 * I) = I * (H * (216 * Ω)) := by ring
      _ = H * Q * (Ω * (1 + 2 * q + 2 * q ^ 2 + q ^ 3) ^ 3) := h
      _ = H * Ω * (Q * (1 + 2 * q + 2 * q ^ 2 + q ^ 3) ^ 3) := by ring
  rintro ⟨j, rfl⟩
  have h81 : 81 ∣ Q * (1 + 2 * q + 2 * q ^ 2 + q ^ 3) ^ 3 := ⟨8 * j, by rw [← key]; ring⟩
  have hcop : Nat.Coprime 81 Q := by
    have h4 := Nat.Coprime.pow_left 4 hQ
    norm_num at h4
    exact h4
  have hdiv := hcop.dvd_of_dvd_mul_left h81
  have hm : q ≡ q % 81 [MOD 81] := (Nat.mod_modEq q 81).symm
  have hF := ((((hm.mul_left 2).add_left 1).add ((hm.pow 2).mul_left 2)).add (hm.pow 3)).pow 3
  have hmod : (1 + 2 * q + 2 * q ^ 2 + q ^ 3) ^ 3 % 81 = 54 :=
    Eq.trans hF (e6InS_cube_check (q % 81) (Nat.mod_lt _ (by norm_num)) (by omega))
  omega

private def e6InS_wp (l : List (Fin 6)) : WeylGroup .E6 :=
  (l.map fun i : Fin 6 => simple .E6 i).prod

private def e6InS_gen (m : Fin 3) (b : Fin 2) : WeylGroup .E6 := e6InS_wp (e6InS_gw m b)

private def e6InS_F (m : Fin 3) (t : Fin 6) : WeylGroup .E6 := e6InS_wp (e6InS_fw m t)

private def e6InS_elt (x : Fin 6 × Fin 6 × Fin 6) : WeylGroup .E6 :=
  e6InS_F 0 x.1 * e6InS_F 1 x.2.1 * e6InS_F 2 x.2.2

private theorem e6InS_wp_append (l l' : List (Fin 6)) :
    e6InS_wp (l ++ l') = e6InS_wp l * e6InS_wp l' := by
  simp only [e6InS_wp, List.map_append, List.prod_append]

private theorem e6InS_wp_smul (l : List (Fin 6)) (v : Fin Tag.E6.rank → ℤ) :
    e6InS_wp l • v = e6WordAct l v :=
  prod_simple_smul_eq_e6WordAct l v

private theorem e6InS_F_smul (m : Fin 3) (t : Fin 6) (v : Fin Tag.E6.rank → ℤ) :
    e6InS_F m t • v = e6WordAct (e6InS_fw m t) v :=
  e6InS_wp_smul _ _

private theorem e6InS_wp_eq {l l' : List (Fin 6)}
    (h : ∀ j : Fin Tag.E6.rank, e6WordAct l (Pi.single j 1) = e6WordAct l' (Pi.single j 1)) :
    e6InS_wp l = e6InS_wp l' :=
  ext_single fun j => by rw [e6InS_wp_smul, e6InS_wp_smul]; exact h j

private theorem e6InS_wp_reverse (l : List (Fin 6)) : e6InS_wp l.reverse = (e6InS_wp l)⁻¹ := by
  induction l with
  | nil => simp [e6InS_wp]
  | cons i l ih =>
    rw [List.reverse_cons, e6InS_wp_append, ih]
    simp only [e6InS_wp, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      mul_inv_rev]
    exact congrArg (_ * ·) (simple_inv (τ := .E6) i).symm

private theorem e6InS_wp_flatMap (l : List (Fin 2)) (f : Fin 2 → List (Fin 6)) :
    e6InS_wp (l.flatMap f) = (l.map fun b => e6InS_wp (f b)).prod := by
  induction l with
  | nil => simp [e6InS_wp]
  | cons b l ih => rw [List.flatMap_cons, e6InS_wp_append, ih, List.map_cons, List.prod_cons]

private theorem e6InS_F_eq (m : Fin 3) (t : Fin 6) :
    e6InS_F m t = ((e6InS_wd t).map (e6InS_gen m)).prod :=
  e6InS_wp_flatMap _ _

private theorem e6InS_elt_zero : e6InS_elt (0, 0, 0) = 1 := by
  simp [e6InS_elt, e6InS_F, e6InS_fw, e6InS_wd, e6InS_wp]

private theorem e6InS_gen_conj (m : Fin 3) (b : Fin 2) :
    e6InS_gen m b = e6InS_wp (e6InS_cw m b) * simple .E6 (e6InS_node m b) *
      (e6InS_wp (e6InS_cw m b))⁻¹ := by
  rw [e6InS_gen, e6InS_gw, e6InS_wp_append, e6InS_wp_append, e6InS_wp_reverse]
  simp only [e6InS_wp, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

private theorem e6InS_gen_eq (m : Fin 3) (b : Fin 2) :
    e6InS_gen m b = rootReflection (e6WordAct (e6InS_cw m b)
      (Pi.single (e6InS_node m b : Fin Tag.E6.rank) 1)) :=
  (e6InS_gen_conj m b).trans ((conj_simple_eq_rootReflection _ _).trans
    (congrArg rootReflection (e6InS_wp_smul _ _)))

private theorem e6InS_gen_zero (m : Fin 3) : e6InS_gen m 0 = rootReflection (e6InS_u m) :=
  (e6InS_gen_eq m 0).trans (congrArg rootReflection (e6InS_roots_check m).1)

private theorem e6InS_gen_one (m : Fin 3) : e6InS_gen m 1 = rootReflection (e6InS_v m) :=
  (e6InS_gen_eq m 1).trans (congrArg rootReflection (e6InS_roots_check m).2)

private theorem e6InS_lineRoots (m : Fin 3) :
    e6LineRoots m = e6A2Roots (e6InS_u m) (e6InS_v m) := by
  fin_cases m <;> rfl

private theorem e6InS_isRoot_u (m : Fin 3) : IsRoot .E6 (e6InS_u m) :=
  isRoot_of_mem_e6LineRoots (i := m) (by rw [e6InS_lineRoots]; simp [e6A2Roots])

private theorem e6InS_isRoot_v (m : Fin 3) : IsRoot .E6 (e6InS_v m) :=
  isRoot_of_mem_e6LineRoots (i := m) (by rw [e6InS_lineRoots]; simp [e6A2Roots])

private theorem e6InS_gen_mul_F (m : Fin 3) (b : Fin 2) (t : Fin 6) :
    e6InS_gen m b * e6InS_F m t = e6InS_F m (e6InS_mu b t) := by
  show e6InS_wp _ * e6InS_wp _ = e6InS_wp _
  rw [← e6InS_wp_append]
  exact e6InS_wp_eq (e6InS_table_check m b t)

private theorem e6InS_commute_gen {m m' : Fin 3} (h : m ≠ m') (b b' : Fin 2) :
    Commute (e6InS_gen m b) (e6InS_gen m' b') := by
  show e6InS_wp _ * e6InS_wp _ = e6InS_wp _ * e6InS_wp _
  rw [← e6InS_wp_append, ← e6InS_wp_append]
  exact e6InS_wp_eq (e6InS_comm_check m m' h b b')

private theorem e6InS_commute_F {m m' : Fin 3} (h : m ≠ m') (b : Fin 2) (t : Fin 6) :
    Commute (e6InS_gen m b) (e6InS_F m' t) := by
  rw [e6InS_F_eq]
  exact Commute.list_prod_right _ _ fun g hg => by
    obtain ⟨b', -, rfl⟩ := List.mem_map.1 hg
    exact e6InS_commute_gen h b b'

private theorem e6InS_gen_mul_elt0 (b : Fin 2) (x₀ x₁ x₂ : Fin 6) :
    e6InS_gen 0 b * e6InS_elt (x₀, x₁, x₂) = e6InS_elt (e6InS_mu b x₀, x₁, x₂) := by
  simp only [e6InS_elt, mul_assoc]
  rw [← mul_assoc (e6InS_gen 0 b), e6InS_gen_mul_F]

private theorem e6InS_gen_mul_elt1 (b : Fin 2) (x₀ x₁ x₂ : Fin 6) :
    e6InS_gen 1 b * e6InS_elt (x₀, x₁, x₂) = e6InS_elt (x₀, e6InS_mu b x₁, x₂) := by
  simp only [e6InS_elt, mul_assoc]
  rw [(e6InS_commute_F (m := 1) (m' := 0) (by decide) b x₀).left_comm,
    ← mul_assoc (e6InS_gen 1 b), e6InS_gen_mul_F]

private theorem e6InS_gen_mul_elt2 (b : Fin 2) (x₀ x₁ x₂ : Fin 6) :
    e6InS_gen 2 b * e6InS_elt (x₀, x₁, x₂) = e6InS_elt (x₀, x₁, e6InS_mu b x₂) := by
  simp only [e6InS_elt, mul_assoc]
  rw [(e6InS_commute_F (m := 2) (m' := 0) (by decide) b x₀).left_comm,
    (e6InS_commute_F (m := 2) (m' := 1) (by decide) b x₁).left_comm, e6InS_gen_mul_F]

private theorem e6InS_gen_mul_elt (m : Fin 3) (b : Fin 2) (x : Fin 6 × Fin 6 × Fin 6) :
    ∃ y, e6InS_gen m b * e6InS_elt x = e6InS_elt y := by
  obtain ⟨x₀, x₁, x₂⟩ := x
  fin_cases m
  · exact ⟨_, e6InS_gen_mul_elt0 b x₀ x₁ x₂⟩
  · exact ⟨_, e6InS_gen_mul_elt1 b x₀ x₁ x₂⟩
  · exact ⟨_, e6InS_gen_mul_elt2 b x₀ x₁ x₂⟩

private theorem e6InS_inj : Function.Injective e6InS_elt := by
  rintro ⟨x₀, x₁, x₂⟩ ⟨y₀, y₁, y₂⟩ h
  simp only [e6InS_elt] at h
  have h₀ : x₀ = y₀ := by
    have e := congrArg (· • e6InS_u 0) h
    simp only [mul_smul, e6InS_F_smul, fun t => (e6InS_fix_check t).1,
      fun t => (e6InS_fix_check t).2.1] at e
    exact e6InS_orbit_check 0 x₀ y₀ e
  subst h₀
  have h' : e6InS_F 1 x₁ * e6InS_F 2 x₂ = e6InS_F 1 y₁ * e6InS_F 2 y₂ := by
    rw [mul_assoc, mul_assoc] at h
    exact mul_left_cancel h
  have h₁ : x₁ = y₁ := by
    have e := congrArg (· • e6InS_u 1) h'
    simp only [mul_smul, e6InS_F_smul, fun t => (e6InS_fix_check t).2.2] at e
    exact e6InS_orbit_check 1 x₁ y₁ e
  subst h₁
  have h₂ : x₂ = y₂ := by
    have e := congrArg (· • e6InS_u 2) (mul_left_cancel h')
    simp only [e6InS_F_smul] at e
    exact e6InS_orbit_check 2 x₂ y₂ e
  subst h₂
  rfl

section Char

variable {K : Type} [Field K] {ω : Kˣ}

private theorem e6InS_kernelRoots (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    kernelRoots (rootCharHom3 (e6LineChar ω)) =
      ⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)) := by
  rw [← e6Line_kernel h3 h1]
  rfl

private theorem e6InS_gen_mem (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (m : Fin 3) (b : Fin 2) :
    e6InS_gen m b ∈ kernelWeylGroup (rootCharHom3 (e6LineChar ω)) := by
  rw [e6InS_gen_eq]
  refine rootReflection_mem_kernelWeylGroup ?_
  rw [e6InS_kernelRoots h3 h1]
  exact Set.mem_iUnion.2 ⟨m, e6InS_root_mem_check m b⟩

private theorem e6InS_elt_mem (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (x : Fin 6 × Fin 6 × Fin 6) :
    e6InS_elt x ∈ kernelWeylGroup (rootCharHom3 (e6LineChar ω)) := by
  have hF : ∀ m t, e6InS_F m t ∈ kernelWeylGroup (rootCharHom3 (e6LineChar ω)) := by
    intro m t
    rw [e6InS_F_eq]
    exact list_prod_mem fun g hg => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
      exact e6InS_gen_mem h3 h1 m b
  exact mul_mem (mul_mem (hF 0 x.1) (hF 1 x.2.1)) (hF 2 x.2.2)

private theorem e6InS_rr_mul (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ kernelRoots (rootCharHom3 (e6LineChar ω))) (x : Fin 6 × Fin 6 × Fin 6) :
    ∃ y, rootReflection α * e6InS_elt x = e6InS_elt y := by
  rw [e6InS_kernelRoots h3 h1, Set.mem_iUnion] at hα
  obtain ⟨m, hm⟩ := hα
  rw [Finset.mem_coe, e6InS_lineRoots] at hm
  have hu := e6InS_isRoot_u m
  have hv := e6InS_isRoot_v m
  have hs : e6InS_gen m 0 • e6InS_v m = e6InS_u m + e6InS_v m := by
    rw [e6InS_gen, e6InS_wp_smul]
    exact e6InS_sum_check m
  have huv : IsRoot .E6 (e6InS_u m + e6InS_v m) := hs ▸ IsRoot.smul hv _
  have ru : ∀ x, ∃ y, rootReflection (e6InS_u m) * e6InS_elt x = e6InS_elt y := fun x => by
    rw [← e6InS_gen_zero]
    exact e6InS_gen_mul_elt m 0 x
  have rv : ∀ x, ∃ y, rootReflection (e6InS_v m) * e6InS_elt x = e6InS_elt y := fun x => by
    rw [← e6InS_gen_one]
    exact e6InS_gen_mul_elt m 1 x
  have ruv : ∀ x, ∃ y, rootReflection (e6InS_u m + e6InS_v m) * e6InS_elt x = e6InS_elt y := by
    intro x
    have e : rootReflection (e6InS_u m + e6InS_v m) =
        e6InS_gen m 0 * e6InS_gen m 1 * e6InS_gen m 0 := by
      rw [← hs, rootReflection_smul_root _ hv, ← e6InS_gen_one, e6InS_gen_zero,
        rootReflection_inv hu]
    obtain ⟨y₁, hy₁⟩ := e6InS_gen_mul_elt m 0 x
    obtain ⟨y₂, hy₂⟩ := e6InS_gen_mul_elt m 1 y₁
    obtain ⟨y₃, hy₃⟩ := e6InS_gen_mul_elt m 0 y₂
    exact ⟨y₃, by rw [e, mul_assoc, mul_assoc, hy₁, hy₂, hy₃]⟩
  simp only [e6A2Roots, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ru x
  · exact rv x
  · exact ruv x
  · rw [rootReflection_neg hu]
    exact ru x
  · rw [rootReflection_neg hv]
    exact rv x
  · rw [rootReflection_neg huv]
    exact ruv x

private theorem e6InS_surj (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) {w : WeylGroup .E6}
    (hw : w ∈ kernelWeylGroup (rootCharHom3 (e6LineChar ω))) : ∃ x, e6InS_elt x = w := by
  rw [kernelWeylGroup_eq_closure] at hw
  induction hw using Subgroup.closure_induction_left with
  | one => exact ⟨(0, 0, 0), e6InS_elt_zero⟩
  | mul_left r hr y _ ih =>
    obtain ⟨α, hα, rfl⟩ := hr
    obtain ⟨x, rfl⟩ := ih
    obtain ⟨z, hz⟩ := e6InS_rr_mul h3 h1 hα x
    exact ⟨z, hz.symm⟩
  | inv_mul_cancel r hr y _ ih =>
    obtain ⟨α, hα, rfl⟩ := hr
    obtain ⟨x, rfl⟩ := ih
    obtain ⟨z, hz⟩ := e6InS_rr_mul h3 h1 hα x
    exact ⟨z, by rw [rootReflection_inv hα.1]; exact hz.symm⟩

private theorem e6InS_mem_inter {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} {v : WeylGroup .E6}
    {α : Fin Tag.E6.rank → ℤ} :
    α ∈ kernelRoots χ ∩ inversionSet v ↔
      α ∈ posRoots (kernelRoots χ) ∧ height (v • α) < 0 := by
  constructor
  · rintro ⟨hk, -, hpos, -, hneg⟩
    exact ⟨⟨hk, hpos⟩, hneg⟩
  · rintro ⟨⟨hk, hpos⟩, hneg⟩
    exact ⟨hk, hk.1, hpos, IsRoot.smul hk.1 v, hneg⟩

theorem ncard_kernelRoots_inter_inversionSet_mul {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} (w : WeylGroup .E6) {o : WeylGroup .E6}
    (ho : o ∈ kernelPosStabilizer χ) :
    (kernelRoots χ ∩ inversionSet (w * o)).ncard = (kernelRoots χ ∩ inversionSet w).ncard := by
  have himg : (o • ·) '' (kernelRoots χ ∩ inversionSet (w * o)) =
      kernelRoots χ ∩ inversionSet w := by
    ext β
    simp only [Set.mem_image, e6InS_mem_inter]
    constructor
    · rintro ⟨α, ⟨hα, hneg⟩, rfl⟩
      refine ⟨?_, by rwa [mul_smul] at hneg⟩
      rw [← ho.2]
      exact ⟨α, hα, rfl⟩
    · rintro ⟨hβ, hneg⟩
      rw [← ho.2] at hβ
      obtain ⟨α, hα, rfl⟩ := hβ
      exact ⟨α, ⟨hα, by rwa [mul_smul]⟩, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ (MulAction.injective o)]

private theorem e6InS_pos_iff (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (α : Fin Tag.E6.rank → ℤ) :
    α ∈ posRoots (kernelRoots (rootCharHom3 (e6LineChar ω))) ↔ α ∈ e6InS_pos := by
  change α ∈ kernelRoots (rootCharHom3 (e6LineChar ω)) ∧ 0 < height α ↔ _
  rw [e6InS_kernelRoots h3 h1, Set.mem_iUnion]
  simp only [Finset.mem_coe]
  constructor
  · rintro ⟨⟨i, hi⟩, hpos⟩
    exact e6InS_pos_check.2 i α hi hpos
  · exact fun h => e6InS_pos_check.1 α h

private theorem e6InS_ncard (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (x : Fin 6 × Fin 6 × Fin 6) :
    (kernelRoots (rootCharHom3 (e6LineChar ω)) ∩ inversionSet (e6InS_elt x)).ncard =
      e6InS_len x.1 + e6InS_len x.2.1 + e6InS_len x.2.2 := by
  classical
  have hset : kernelRoots (rootCharHom3 (e6LineChar ω)) ∩ inversionSet (e6InS_elt x) =
      ((e6InS_pos.filter fun α => decide (height (e6InS_elt x • α) < 0)).toFinset :
        Set (Fin Tag.E6.rank → ℤ)) := by
    ext α
    rw [e6InS_mem_inter, e6InS_pos_iff h3 h1]
    simp [List.mem_filter]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (e6InS_pos_nodup.filter _)]
  have hsm : ∀ α, e6InS_elt x • α = e6WordAct (e6InS_fw 0 x.1)
      (e6WordAct (e6InS_fw 1 x.2.1) (e6WordAct (e6InS_fw 2 x.2.2) α)) := fun α => by
    simp only [e6InS_elt, mul_smul, e6InS_F_smul]
  simp only [hsm]
  exact e6InS_k_check x

private theorem e6InS_sum_len (q : ℕ) :
    ∑ x : Fin 6 × Fin 6 × Fin 6, q ^ (e6InS_len x.1 + e6InS_len x.2.1 + e6InS_len x.2.2) =
      (1 + 2 * q + 2 * q ^ 2 + q ^ 3) ^ 3 := by
  have h6 : ∑ t : Fin 6, q ^ e6InS_len t = 1 + 2 * q + 2 * q ^ 2 + q ^ 3 := by
    simp only [Fin.sum_univ_six, e6InS_len]
    simp
    ring
  simp only [Fintype.sum_prod_type, pow_add, ← Finset.mul_sum, ← Finset.sum_mul, h6]
  ring

theorem card_familyStabilizer_and_cellSum_e6LineChar (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (q : ℕ) :
    Nat.card (familyStabilizerSubgroup fun _ : Unit => e6LineChar ω) =
        216 * Nat.card (kernelPosStabilizer (rootCharHom3 (e6LineChar ω))) ∧
      ∑ᶠ w : familyStabilizerSubgroup (fun _ : Unit => e6LineChar ω),
          q ^ (familyKernel (fun _ : Unit => e6LineChar ω) ∩
            inversionSet (w : WeylGroup .E6)).ncard =
        Nat.card (kernelPosStabilizer (rootCharHom3 (e6LineChar ω))) *
          (1 + 2 * q + 2 * q ^ 2 + q ^ 3) ^ 3 := by
  classical
  have hS : ∀ w : WeylGroup .E6, w ∈ familyStabilizerSubgroup (fun _ : Unit => e6LineChar ω) ↔
      w ∈ charStabilizer (rootCharHom3 (e6LineChar ω)) := fun w => by
    rw [familyStabilizerSubgroup, Subgroup.mem_iInf]
    exact ⟨fun h => h (), fun h _ => h⟩
  have hSig : familyKernel (fun _ : Unit => e6LineChar ω) =
      kernelRoots (rootCharHom3 (e6LineChar ω)) :=
    Set.ext fun α => ⟨fun h => ⟨h.1, h.2 ()⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  have : Fintype (familyStabilizerSubgroup fun _ : Unit => e6LineChar ω) := Fintype.ofFinite _
  have : Fintype (kernelPosStabilizer (rootCharHom3 (e6LineChar ω))) := Fintype.ofFinite _
  let f : (Fin 6 × Fin 6 × Fin 6) × kernelPosStabilizer (rootCharHom3 (e6LineChar ω)) →
      familyStabilizerSubgroup (fun _ : Unit => e6LineChar ω) := fun p =>
    ⟨e6InS_elt p.1 * p.2, (hS _).2 (mul_mem (kernelWeylGroup_le (e6InS_elt_mem h3 h1 p.1))
      (kernelPosStabilizer_le p.2.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, o⟩ ⟨y, o'⟩ h
      have h' : e6InS_elt x * o = e6InS_elt y * o' := congrArg Subtype.val h
      obtain ⟨p, -, hp⟩ := existsUnique_mul_of_mem_charStabilizer ((hS _).1 (f (x, o)).2)
      have e1 := hp (e6InS_elt x, o) ⟨e6InS_elt_mem h3 h1 x, o.2, rfl⟩
      have e2 := hp (e6InS_elt y, o') ⟨e6InS_elt_mem h3 h1 y, o'.2, h'⟩
      have e3 := e1.trans e2.symm
      simp only [Prod.mk.injEq] at e3
      rw [e6InS_inj e3.1, Subtype.ext e3.2]
    · rintro ⟨w, hw⟩
      obtain ⟨p, ⟨hu, ho, hwp⟩, -⟩ := existsUnique_mul_of_mem_charStabilizer ((hS w).1 hw)
      obtain ⟨x, hx⟩ := e6InS_surj h3 h1 hu
      refine ⟨(x, ⟨p.2, ho⟩), Subtype.ext ?_⟩
      change e6InS_elt x * p.2 = w
      rw [hx, hwp]
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod, Nat.card_prod,
      Nat.card_fin]
  · have hterm : ∀ p : (Fin 6 × Fin 6 × Fin 6) × kernelPosStabilizer (rootCharHom3 (e6LineChar ω)),
        q ^ (kernelRoots (rootCharHom3 (e6LineChar ω)) ∩
          inversionSet ((Equiv.ofBijective f hf p :
            familyStabilizerSubgroup (fun _ : Unit => e6LineChar ω)) : WeylGroup .E6)).ncard =
          q ^ (e6InS_len p.1.1 + e6InS_len p.1.2.1 + e6InS_len p.1.2.2) := by
      intro p
      change q ^ (kernelRoots (rootCharHom3 (e6LineChar ω)) ∩
        inversionSet (e6InS_elt p.1 * p.2)).ncard = _
      rw [ncard_kernelRoots_inter_inversionSet_mul _ p.2.2, e6InS_ncard h3 h1]
    rw [hSig, finsum_eq_sum_of_fintype, ← (Equiv.ofBijective f hf).sum_comp]
    simp only [hterm]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Finset.mul_sum, e6InS_sum_len, Nat.card_eq_fintype_card]

end Char

section Index

variable {K : Type} [Field K] {ω : Kˣ}

private theorem e6InS_not_dvd [Finite K] (hK : 3 ∣ Nat.card K - 1) (h3 : ω ^ 3 = 1)
    (h1 : ω ≠ 1) :
    ¬ 3 ∣ (monomialSubgroup .E6 K).relIndex
      (familyCentralizer .E6 K (fun _ : Unit => e6LineChar ω)) := by
  have : Finite (ModGL .E6 K) := finite_modGL
  have hq : Nat.card K % 3 = 1 := by
    have : 0 < Nat.card K := Nat.card_pos
    omega
  have h3q : Nat.Coprime 3 (Nat.card K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  obtain ⟨hcard, hsum⟩ :=
    card_familyStabilizer_and_cellSum_e6LineChar h3 h1 (Nat.card K)
  have hI := Subgroup.relIndex_mul_card (monomialSubgroup .E6 K)
    (familyCentralizer .E6 K (fun _ : Unit => e6LineChar ω))
  rw [inf_comm, card_familyCentralizer_inf_monomial, card_familyCentralizer, hsum, hcard] at hI
  exact e6InS_arith Nat.card_pos Nat.card_pos hq (Nat.Coprime.pow_right _ h3q) hI

private theorem e6InS_relIndex [Finite K] (hK : 3 ∣ Nat.card K - 1) (h3 : ω ^ 3 = 1)
    (h1 : ω ≠ 1) :
    ¬ 3 ∣ (monoHat .E6 K).relIndex
      (hatGroup .E6 K ⊓ Subgroup.centralizer {rootDiagUnit .E6 (e6LineChar ω)}) := by
  have : Finite (ModGL .E6 K) := finite_modGL
  set d := rootDiagUnit .E6 (e6LineChar ω) with hd
  set Y := hatGroup .E6 K ⊓ Subgroup.centralizer {d} with hY
  set C₀ := familyCentralizer .E6 K (fun _ : Unit => e6LineChar ω) with hC₀def
  have hC₀ : ∀ g, g ∈ C₀ ↔ g ∈ adjointGroup .E6 K ∧ g ∈ Subgroup.centralizer {d} := fun g => by
    rw [hC₀def, mem_familyCentralizer]
    exact and_congr_right fun _ =>
      ⟨fun h => conj_eq_iff_mem_centralizer.1 (h ()), fun h _ => conj_eq_iff_mem_centralizer.2 h⟩
  have hC₀Y : C₀ ≤ Y := fun g hg =>
    ⟨adjointGroup_le_hatGroup ((hC₀ g).1 hg).1, ((hC₀ g).1 hg).2⟩
  have hN : (C₀.subgroupOf Y).Normal := by
    constructor
    intro n hn y
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnA, hnc⟩ := (hC₀ _).1 hn
    obtain ⟨hyH, hyc⟩ := Subgroup.mem_inf.1 y.2
    refine (hC₀ _).2 ⟨?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.1 (hatGroup_le_normalizer hyH) n).1 hnA
      simpa using h
    · have h := mul_mem (mul_mem hyc hnc) (inv_mem hyc)
      simpa using h
  have hsup : (monoHat .E6 K).subgroupOf Y ⊔ C₀.subgroupOf Y = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨hyH, hyc⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨g, hg, b, rfl⟩ := hyH
    have hdb : rootDiagUnit .E6 b ∈ Subgroup.centralizer {d} := by
      rw [Subgroup.mem_centralizer_singleton_iff, hd, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
        mul_comm]
    have hgc : g ∈ Subgroup.centralizer {d} := by
      have h := mul_mem hyc (inv_mem hdb)
      simpa using h
    have e : (⟨g * rootDiagUnit .E6 b, hy⟩ : Y) =
        ⟨g, Subgroup.mem_inf.2 ⟨adjointGroup_le_hatGroup hg, hgc⟩⟩ *
          ⟨rootDiagUnit .E6 b, Subgroup.mem_inf.2 ⟨rootDiagUnit_mem_hatGroup b, hdb⟩⟩ := rfl
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.2 ((hC₀ g).2 ⟨hg, hgc⟩))
      (Subgroup.mem_subgroupOf.2 (rootDiagUnit_mem_monoHat b))
  have hidx := index_eq_relIndex_of_sup_eq_top hsup
  rw [Subgroup.relIndex_subgroupOf hC₀Y] at hidx
  have heq : (monoHat .E6 K).subgroupOf C₀ = (monomialSubgroup .E6 K).subgroupOf C₀ := by
    ext ⟨g, hg⟩
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨n, hn, b, hnb⟩
      have hgA := ((hC₀ g).1 hg).1
      have hdA : rootDiagUnit .E6 b ∈ adjointGroup .E6 K := by
        have e : rootDiagUnit .E6 b = n⁻¹ * g := by
          rw [hnb]
          group
        rw [e]
        exact mul_mem (inv_mem (monomialSubgroup_le_adjointGroup' hn)) hgA
      have hdT := CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup b hdA
      rw [hnb]
      exact mul_mem hn (Subgroup.mem_sup_left hdT)
    · exact fun h => monomial_le_monoHat h
  change ¬ 3 ∣ ((monoHat .E6 K).subgroupOf Y).index
  rw [hidx, Subgroup.relIndex, heq]
  exact e6InS_not_dvd hK h3 h1

end Index

theorem e6InnerSylowMonoLine_holds : E6InnerSylowMonoLine := by
  intro K _ _ _ hK ω h3 h1 E hED hE3 hEc
  have := Fact.mk Nat.prime_three
  have : Finite (hatGroup .E6 K) := finite_hatGroup
  have : Finite (ModGL .E6 K) := finite_modGL
  have hcomm : ∀ y : hatGroup .E6 K, Commute (hatAut .E6 K y) (MulAut.conj (e6LineElt ω)) ↔
      (y : ModGL .E6 K) ∈ Subgroup.centralizer {rootDiagUnit .E6 (e6LineChar ω)} := by
    intro y
    have key := e6Cen_mul_conj_mul_inv (hatAut .E6 K y) (e6LineElt ω)
    have hval : ((hatAut .E6 K y (e6LineElt ω) : adjointGroup .E6 K) : ModGL .E6 K) =
        (y : ModGL .E6 K) * rootDiagUnit .E6 (e6LineChar ω) * (y : ModGL .E6 K)⁻¹ := by
      rw [coe_hatAut_apply, coe_e6LineElt]
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hc
      have h2 : MulAut.conj (hatAut .E6 K y (e6LineElt ω)) = MulAut.conj (e6LineElt ω) := by
        rw [← key, hc.eq, mul_inv_cancel_right]
      have h4 := congrArg Subtype.val
        (conj_injective_of_center_eq_bot' center_adjointGroup_eq_bot h2)
      rw [hval, coe_e6LineElt] at h4
      exact mul_inv_eq_iff_eq_mul.1 h4
    · intro hc
      have h2 : hatAut .E6 K y (e6LineElt ω) = e6LineElt ω := by
        apply Subtype.ext
        rw [hval, coe_e6LineElt, hc, mul_inv_cancel_right]
      have h5 : hatAut .E6 K y * MulAut.conj (e6LineElt ω) * (hatAut .E6 K y)⁻¹ =
          MulAut.conj (e6LineElt ω) := by
        rw [key, h2]
      exact mul_inv_eq_iff_eq_mul.1 h5
  have hEκ : E ≤ (hatAut .E6 K).range := by
    rw [cen_range_hatAut]
    exact hED
  set Y : Subgroup (hatGroup .E6 K) := E.comap (hatAut .E6 K) with hY
  set f : Y →* E := ((hatAut .E6 K).comp Y.subtype).codRestrict E (fun y => y.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨x, rfl⟩ := hEκ hφ
    exact ⟨⟨x, hφ⟩, rfl⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 Y))
  have hEp : IsPGroup 3 (⊤ : Subgroup E) := fun g => by
    obtain ⟨k, hk⟩ := hE3 g.1
    exact ⟨k, Subtype.ext hk⟩
  have hQ : (Q₀ : Subgroup Y).map f = ⊤ :=
    ((Q₀.mapSurjective hfs).is_maximal' hEp le_top).symm
  set P : Subgroup (hatGroup .E6 K) := (Q₀ : Subgroup Y).map Y.subtype with hP
  have hP3 : IsPGroup 3 P := Q₀.isPGroup'.map _
  have hPE : P.map (hatAut .E6 K) = E := by
    have hcomp : (hatAut .E6 K).comp Y.subtype = E.subtype.comp f := MonoidHom.ext fun _ => rfl
    rw [hP, Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hA : P.map (hatGroup .E6 K).subtype ≤
      hatGroup .E6 K ⊓ Subgroup.centralizer {rootDiagUnit .E6 (e6LineChar ω)} := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨y, -, rfl⟩ := hp
    exact Subgroup.mem_inf.2 ⟨(y : hatGroup .E6 K).2, (hcomm _).1 (hEc _ y.2)⟩
  obtain ⟨u, hu, hconj⟩ := exists_conj_le_of_isPGroup_of_not_dvd_relIndex hA (hP3.map _)
    (e6InS_relIndex hK h3 h1)
  obtain ⟨hu₁, hu₂⟩ := Subgroup.mem_inf.1 hu
  set c : hatGroup .E6 K := ⟨u, hu₁⟩ with hc
  refine ⟨hatAut .E6 K c, (cen_range_hatAut (K := K)).le ⟨c, rfl⟩, (hcomm c).2 hu₂, ?_⟩
  rintro _ ⟨X₀, hX₀, rfl⟩
  rw [← hPE] at hX₀
  obtain ⟨p, hp, rfl⟩ := hX₀
  have hym : ((c * p * c⁻¹ : hatGroup .E6 K) : ModGL .E6 K) ∈ monoHat .E6 K :=
    hconj _ ⟨p, hp, rfl⟩
  refine ⟨psiHat .E6 K ⟨_, hym⟩, ?_⟩
  have hX : (MulAut.congr (hatAut .E6 K c)).toMonoidHom (hatAut .E6 K p) =
      hatAut .E6 K (c * p * c⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    exact cen_mulAut_congr_apply _ _
  rw [hX]
  exact cen_bmMono_hatAut hym

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
