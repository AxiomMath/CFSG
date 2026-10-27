module

public import CFSG.LargeExtraspecial.SMod20AutMain
import all CFSG.Fischer.F4

public section

namespace CFSG.LargeExtraspecial.SMod20.Aut

open CFSG.Fischer CFSG.F4.Native CFSG.SmithE Matrix Module

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

theorem F4_add_self (a : F4) : a + a = 0 := by
  revert a
  decide

theorem W_add_self (v : W) : v + v = 0 := by
  funext k
  exact F4_add_self (v k)

@[expose] noncomputable def tvG (v : W) : GU0 :=
  if h : hermStd v v = 0 then tvGU v h else 1

theorem tvG_mulVec {v : W} (hv : hermStd v v = 0) (x : W) :
    (((tvG v : GU0) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x = x + hermStd x v • v := by
  rw [tvG, dite_eq_left hv]
  exact tvM_mulVec v x

theorem sum_map_smul_mem {S : Submodule F4 W} (vs : List W) (hvs : ∀ v ∈ vs, v ∈ S)
    (f : W → F4) : (vs.map fun v => f v • v).sum ∈ S := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.sum_cons]
    exact S.add_mem (S.smul_mem _ (hvs v (List.mem_cons_self ..)))
      (ih fun u hu => hvs u (List.mem_cons_of_mem _ hu))

theorem prod_tvG_mulVec {S : Submodule F4 W} (hS : ∀ x ∈ S, ∀ y ∈ S, hermStd x y = 0)
    (vs : List W) (hvs : ∀ v ∈ vs, v ∈ S) (x : W) :
    ((((vs.map tvG).prod : GU0) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x =
      x + (vs.map fun v => hermStd x v • v).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    have hv := hvs v (List.mem_cons_self ..)
    have hvs' : ∀ u ∈ vs, u ∈ S := fun u hu => hvs u (List.mem_cons_of_mem _ hu)
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec,
      ih hvs', tvG_mulVec (hS v hv v hv)]
    have hz : hermStd ((vs.map fun u => hermStd x u • u).sum) v = 0 :=
      hS _ (sum_map_smul_mem vs hvs' _) v hv
    rw [hermStd_add_left, hz, add_zero, List.map_cons, List.sum_cons]
    abel

section Rad


@[expose] noncomputable def UAloc (i : ℕ) : Subgroup (Equiv.Perm (Fin 693)) :=
  Subgroup.closure (tvP '' (planePoints i : Set (Fin 693)))

theorem tvP_mem_UAloc {i : ℕ} {p : Fin 693} (hp : p ∈ planePoints i) : tvP p ∈ UAloc i :=
  Subgroup.subset_closure ⟨p, hp, rfl⟩

theorem UAloc_le_T46 (i : ℕ) : UAloc i ≤ T46 := by
  rw [UAloc, Subgroup.closure_le]
  rintro _ ⟨p, -, rfl⟩
  exact tvP_mem p

theorem tvP_commute_planePts
    {i : ℕ} (hi : i < 891) {p q : Fin 693} (hp : p ∈ planePoints i) (hq : q ∈ planePoints i) :
    tvP p * tvP q = tvP q * tvP p :=
  (tvP_comm_iff p q).2
    (hermStd_planeSub hi ((mem_planePoints i p).1 hp) ((mem_planePoints i q).1 hq))

theorem UAloc_commute {i : ℕ}
    (hi : i < 891) {u v : Equiv.Perm (Fin 693)} (hu : u ∈ UAloc i) (hv : v ∈ UAloc i) :
    u * v = v * u := by
  have h1 : UAloc i ≤ Subgroup.centralizer (tvP '' (planePoints i : Set (Fin 693))) := by
    rw [UAloc, Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    exact tvP_commute_planePts hi hq hp
  have h2 : UAloc i ≤ Subgroup.centralizer {u} := by
    rw [UAloc, Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (Subgroup.mem_centralizer_iff.1 (h1 hu) _ ⟨p, hp, rfl⟩).symm
  exact Subgroup.mem_centralizer_iff.1 (h2 hv) u rfl

theorem tvGU_zero (h : hermStd (0 : W) 0 = 0) : tvGU 0 h = 1 := by
  apply Subtype.ext
  apply Units.ext
  change tvM 0 = 1
  simp [tvM]

theorem piGU_tvG_mem {i : ℕ} (hi : i < 891) {v : W}
    (hv : v ∈ planeSub i) : piGU (tvG v) ∈ UAloc i := by
  have hvi := hermStd_planeSub hi hv hv
  by_cases hv0 : v = 0
  · subst hv0
    rw [tvG, dite_eq_left hvi, tvGU_zero, map_one]
    exact (UAloc i).one_mem
  · have hp : ptOf v hv0 hvi ∈ planePoints i := by
      rw [mem_planePoints]
      obtain ⟨c, hc, hcv⟩ := uVec_ptOf v hv0 hvi
      rw [hcv]
      exact (planeSub i).smul_mem c hv
    have he : piGU (tvG v) = tvP (ptOf v hv0 hvi) := by
      ext q
      rw [tvG, dite_eq_left hvi, tvP, piSU_apply]
      change ptIdx (tvM v *ᵥ uVec q) = ptIdx (tvM (uVec (ptOf v hv0 hvi)) *ᵥ uVec q)
      obtain ⟨c, hc, hcv⟩ := uVec_ptOf v hv0 hvi
      rw [hcv, tvM_smul' hc]
    rw [he]
    exact tvP_mem_UAloc hp

theorem piGU_prod_tvG_mem {i : ℕ} (hi : i < 891) (vs : List W)
    (hvs : ∀ v ∈ vs, v ∈ planeSub i) : piGU (vs.map tvG).prod ∈ UAloc i := by
  rw [map_list_prod, List.map_map]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hg
  exact piGU_tvG_mem hi (hvs v hv)

end Rad

@[expose] def xiLin (i : ℕ) : W →ₗ[F4] (Fin 3 → F4) where
  toFun x k := hermStd x (planeVec i k)
  map_add' x y := by
    funext k
    simp [hermStd_add_left]
  map_smul' c x := by
    funext k
    simp [hermStd_smul_left]

theorem xiLin_surjective {i : ℕ} (hi : i < 891) :
    Function.Surjective (xiLin i) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have hk : LinearMap.ker (xiLin i) = planeSub i := by
    ext x
    rw [LinearMap.mem_ker, mem_planeSub_iff_orth hi]
    constructor
    · intro h k
      exact congrFun h k
    · intro h
      funext k
      exact h k
  have := LinearMap.finrank_range_add_finrank_ker (xiLin i)
  rw [hk, finrank_planeSub hi, Module.finrank_fin_fun] at this
  rw [Module.finrank_fin_fun]
  omega

theorem exists_dual {i : ℕ} (hi : i < 891) :
    ∃ f : Fin 3 → W, ∀ j k, hermStd (f j) (planeVec i k) = if k = j then 1 else 0 := by
  have h := fun j => xiLin_surjective hi (Pi.single j 1)
  choose f hf using h
  refine ⟨f, fun j k => ?_⟩
  have := congrFun (hf j) k
  rw [Pi.single_apply] at this
  exact this

theorem tvTerm_smul (x w : W) (c : F4) :
    hermStd x (c • w) • (c • w) = (c ^ 3 * hermStd x w) • w := by
  rw [hermStd_smul_right, smul_smul]
  congr 1
  ring

theorem tvTerm_diag (x w : W) {h : F4} (hh : h ^ 2 = h) :
    hermStd x (h • w) • (h • w) = (h * hermStd x w) • w := by
  rw [tvTerm_smul]
  have h3 : h ^ 3 = h := by rw [pow_succ, hh, ← pow_two, hh]
  rw [h3]

theorem tvTerm_triple (x u v : W) (c : F4) :
    hermStd x (u + c • v) • (u + c • v) + (hermStd x u • u + hermStd x (c • v) • (c • v)) =
      (c * hermStd x u) • v + (c ^ 2 * hermStd x v) • u := by
  rw [hermStd_add_right, hermStd_smul_right]
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (hermStd x u * u k + c ^ 3 * hermStd x v * v k) * F4.two_eq_zero

theorem hermStd_sum_smul_left (s : Finset (Fin 3)) (a : Fin 3 → F4) (v : Fin 3 → W) (y : W) :
    hermStd (∑ c ∈ s, a c • v c) y = ∑ c ∈ s, a c * hermStd (v c) y := by
  induction s using Finset.induction_on with
  | empty => simp [hermStd]
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, hermStd_add_left, hermStd_smul_left, ih]

theorem hermStd_sum_smul_right (s : Finset (Fin 3)) (a : Fin 3 → F4) (v : Fin 3 → W) (y : W) :
    hermStd y (∑ c ∈ s, a c • v c) = ∑ c ∈ s, a c ^ 2 * hermStd y (v c) := by
  induction s using Finset.induction_on with
  | empty => simp [hermStd]
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, hermStd_add_right, hermStd_smul_right, ih]

theorem piGU_mem_UAloc_of_fix
    {i : ℕ} (hi : i < 891) {A : GU0}
    (hA : ∀ w ∈ planeSub i, ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ w = w) :
    piGU A ∈ UAloc i := by
  set w := planeVec i with hw
  set M := ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) with hM
  obtain ⟨f, hf⟩ := exists_dual hi
  have hwS : ∀ a, w a ∈ planeSub i := planeVec_mem i
  have hN : ∀ x, M *ᵥ x + x ∈ planeSub i := by
    intro x
    rw [mem_planeSub_iff_orth hi]
    intro k
    rw [hermStd_add_left]
    have h1 := hermStd_mulVec A x (w k)
    rw [hA _ (hwS k)] at h1
    rw [h1, F4_add_self]
  have hH : ∀ j, ∃ c : Fin 3 → F4, ∑ a, c a • w a = M *ᵥ f j + f j :=
    fun j => (mem_planeSub_iff i _).1 (hN (f j))
  choose H hH using hH
  have hdec : ∀ x, M *ᵥ x + x = ∑ j, hermStd x (w j) • (M *ᵥ f j + f j) := by
    intro x
    have hy : x + ∑ j, hermStd x (w j) • f j ∈ planeSub i := by
      rw [mem_planeSub_iff_orth hi]
      intro k
      rw [hermStd_add_left, hermStd_sum_smul_left, Finset.sum_eq_single k]
      · rw [hf, ite_eq_left rfl, mul_one, F4_add_self]
      · intro b _ hb
        rw [hf, ite_eq_right (Ne.symm hb), mul_zero]
      · simp
    have h1 := hA _ hy
    have hlin : M *ᵥ (∑ j, hermStd x (w j) • f j) = ∑ j, hermStd x (w j) • (M *ᵥ f j) := by
      rw [Fin.sum_univ_three, Fin.sum_univ_three, mulVec_add, mulVec_add, mulVec_smul,
        mulVec_smul, mulVec_smul]
    rw [mulVec_add, hlin] at h1
    have h2 : M *ᵥ x + x = (∑ j, hermStd x (w j) • (M *ᵥ f j)) +
        ∑ j, hermStd x (w j) • f j := by
      generalize (∑ j, hermStd x (w j) • (M *ᵥ f j)) = S1 at h1 ⊢
      generalize (∑ j, hermStd x (w j) • f j) = S2 at h1 ⊢
      calc M *ᵥ x + x = (M *ᵥ x + S1) + (S1 + x) := by
            rw [add_assoc, ← add_assoc S1, W_add_self, zero_add]
        _ = (x + S2) + (S1 + x) := by rw [h1]
        _ = S1 + S2 + (x + x) := by abel
        _ = S1 + S2 := by rw [W_add_self, add_zero]
    rw [h2, ← Finset.sum_add_distrib]
    simp only [smul_add]
  have hrel : ∀ x y, hermStd (M *ᵥ x + x) y = hermStd x (M *ᵥ y + y) := by
    intro x y
    have e : hermStd (M *ᵥ x) (M *ᵥ y) = hermStd x y := hermStd_mulVec A x y
    have ex : M *ᵥ x = (M *ᵥ x + x) + x := by rw [add_assoc, W_add_self, add_zero]
    have ey : M *ᵥ y = (M *ᵥ y + y) + y := by rw [add_assoc, W_add_self, add_zero]
    have hxy := hermStd_planeSub hi (hN x) (hN y)
    generalize M *ᵥ x + x = nx at ex hxy ⊢
    generalize M *ᵥ y + y = ny at ey hxy ⊢
    rw [ex, ey, hermStd_add_left, hermStd_add_right, hermStd_add_right, hxy, zero_add] at e
    have e2 : hermStd nx y + hermStd x ny = 0 := by
      have := congrArg (· + hermStd x y) e
      rw [add_assoc, add_assoc, F4_add_self, add_zero] at this
      exact this
    calc hermStd nx y = hermStd nx y + (hermStd nx y + hermStd x ny) := by rw [e2, add_zero]
      _ = hermStd x ny := by rw [← add_assoc, F4_add_self, zero_add]
  have hherm : ∀ a b, H a b = H b a ^ 2 := by
    intro a b
    have h2 : hermStd (M *ᵥ f a + f a) (f b) = H a b := by
      rw [← hH a, hermStd_sum_smul_left, Finset.sum_eq_single b]
      · rw [hermStd_swap', hf, ite_eq_left rfl]
        ring
      · intro c _ hc
        rw [hermStd_swap', hf, ite_eq_right hc]
        ring
      · simp
    have h3 : hermStd (f a) (M *ᵥ f b + f b) = H b a ^ 2 := by
      rw [← hH b, hermStd_sum_smul_right, Finset.sum_eq_single a]
      · rw [hf, ite_eq_left rfl, mul_one]
      · intro c _ hc
        rw [hf, ite_eq_right hc, mul_zero]
      · simp
    rw [← h2, ← h3]
    exact hrel (f a) (f b)
  set vs : List W := [H 0 0 • w 0, H 1 1 • w 1, H 2 2 • w 2] ++
    [w 0 + H 0 1 • w 1, w 0, H 0 1 • w 1] ++ [w 0 + H 0 2 • w 2, w 0, H 0 2 • w 2] ++
    [w 1 + H 1 2 • w 2, w 1, H 1 2 • w 2] with hvs
  have hvsS : ∀ v ∈ vs, v ∈ planeSub i := by
    have hsm : ∀ (c : F4) (a : Fin 3), c • w a ∈ planeSub i :=
      fun c a => (planeSub i).smul_mem c (hwS a)
    have had : ∀ (c : F4) (a b : Fin 3), w a + c • w b ∈ planeSub i :=
      fun c a b => (planeSub i).add_mem (hwS a) (hsm c b)
    intro v hv
    simp only [hvs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (((rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)
    all_goals first | exact hsm _ _ | exact had _ _ _ | exact hwS _
  have hAeq : A = (vs.map tvG).prod := by
    apply Subtype.ext
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [prod_tvG_mulVec (fun _ hx _ hy => hermStd_planeSub hi hx hy) vs hvsS x]
    have hx : M *ᵥ x = x + (M *ᵥ x + x) := by
      rw [add_comm (M *ᵥ x), ← add_assoc, W_add_self, zero_add]
    change M *ᵥ x = _
    rw [hx, hdec x]
    congr 1
    simp only [← hH]
    have hd : ∀ c, H c c ^ 2 = H c c := fun c => (hherm c c).symm
    simp only [hvs, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [tvTerm_diag x _ (hd 0), tvTerm_diag x _ (hd 1), tvTerm_diag x _ (hd 2),
      tvTerm_triple x (w 0) (w 1), tvTerm_triple x (w 0) (w 2), tvTerm_triple x (w 1) (w 2),
      Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
      hherm 1 0, hherm 2 0, hherm 2 1]
    module
  rw [hAeq]
  exact piGU_prod_tvG_mem hi vs hvsS

end CFSG.LargeExtraspecial.SMod20.Aut
