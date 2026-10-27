module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFivePModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type*} [Field K]

theorem transvection_mul_pointRadElem {c i j : Fin n} (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c)
    (a : K) (r : Fin n → K) :
    SpecialLinearGroup.transvection hij a * pointRadElem c r =
      pointRadElem c (r - Pi.single j (a * r i)) * SpecialLinearGroup.transvection hij a := by
  apply Subtype.ext
  change ((SpecialLinearGroup.transvection hij a : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * pointRadMat c r = pointRadMat c (r - Pi.single j (a * r i)) *
    ((SpecialLinearGroup.transvection hij a : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one]
  ext k l
  rw [Matrix.add_apply, Matrix.add_apply]
  have h1 : (single i j a * pointRadMat c r : Matrix (Fin n) (Fin n) K) k l =
      if k = i ∧ l = j then a else 0 := by
    rcases eq_or_ne k i with rfl | hk
    · rw [single_mul_apply_same, pointRadMat_apply]
      by_cases hl : l = j
      · subst hl; simp [hjc]
      · simp [hjc, Ne.symm hl, hl]
    · rw [single_mul_apply_of_ne _ _ _ _ _ hk]
      simp [hk]
  have h2 : (pointRadMat c (r - Pi.single j (a * r i)) * single i j a :
      Matrix (Fin n) (Fin n) K) k l =
      if l = j then ((if k = i then 1 else 0) + (if k = c then r i else 0)) * a else 0 := by
    rcases eq_or_ne l j with rfl | hl
    · rw [mul_single_apply_same, pointRadMat_apply]
      by_cases hk : k = c
      · subst hk; simp [hic, Ne.symm hic, hij]
      · simp [hk, Matrix.one_apply, eq_comm]
    · rw [mul_single_apply_of_ne _ _ _ _ _ hl]
      simp [hl]
  rw [h1, h2, pointRadMat_apply, pointRadMat_apply]
  by_cases hkc : k = c
  · subst hkc
    by_cases hlj : l = j
    · subst hlj
      simp [hjc, Ne.symm hic, Ne.symm hjc]
      ring
    · by_cases hlc : l = k
      · subst hlc; simp [hlj, Ne.symm hic]
      · simp [hlj, hlc, Ne.symm hic, Ne.symm hlc]
  · by_cases hlj : l = j
    · subst hlj
      by_cases hki : k = i
      · subst hki; simp [hkc, hij]
      · simp [hkc, hki]
    · simp [hkc, hlj]

theorem xab_mul_proj_pointRadElem {c i j : Fin n} (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c)
    (a : K) (r : Fin n → K) :
    xab hij a * LinearFlag.proj n K (pointRadElem c r) =
      LinearFlag.proj n K (pointRadElem c (r - Pi.single j (a * r i))) * xab hij a := by
  rw [xab, ← map_mul, ← map_mul, transvection_mul_pointRadElem hij hic hjc]

theorem pointRadElem_inv (c : Fin n) (r : Fin n → K) :
    (pointRadElem c r)⁻¹ = pointRadElem c (-r) :=
  inv_eq_of_mul_eq_one_right (by rw [pointRadElem_mul, add_neg_cancel, pointRadElem_zero])

theorem apply_eq_of_proj_pointRadElem_eq (hK : Nat.card K = 2) {c : Fin n} {r s : Fin n → K}
    (h : LinearFlag.proj n K (pointRadElem c r) = LinearFlag.proj n K (pointRadElem c s))
    {m : Fin n} (hm : m ≠ c) : r m = s m := by
  have h1 := proj_injective_of_natCard_eq_two hK h
  have h2 : pointRadMat c r c m = pointRadMat c s c m := by
    rw [← coe_pointRadElem, ← coe_pointRadElem, h1]
  rwa [pointRadMat_apply, pointRadMat_apply, ite_eq_left ⟨rfl, hm⟩, ite_eq_left ⟨rfl, hm⟩,
    add_right_inj] at h2

theorem proj_pointRadElem_single_mem_pointRadical {c m : Fin n} (hm : m ≠ c) (a : K) :
    LinearFlag.proj n K (pointRadElem c (Pi.single m a)) ∈ pointRadical (K := K) c := by
  refine Subgroup.mem_map_of_mem _ ⟨Pi.single m a, fun j hj => ?_, rfl⟩
  have hjc : j = c := by simpa using hj
  rw [hjc, Pi.single_eq_of_ne (Ne.symm hm)]

theorem pointRadOn_le_centralizer_xab {c i j : Fin n} (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c)
    {S : Finset (Fin n)} (hiS : i ∉ S) (a : K) :
    pointRadOn c S ≤ centralizer ({xab hij a} : Set (LinearFlag.projectiveSL n K)) := by
  rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  rw [mem_centralizer_singleton_iff, xab_mul_proj_pointRadElem hij hic hjc, hr i hiS, mul_zero,
    Pi.single_zero, sub_zero]

theorem xab_commutator_mem_pointRadOn {c i j : Fin n} (hij : i ≠ j) (hic : i ≠ c)
    (hjc : j ≠ c) (a : K) {v : LinearFlag.projectiveSL n K} (hv : v ∈ pointRadical (K := K) c) :
    xab hij a * v * (xab hij a)⁻¹ * v⁻¹ ∈ pointRadOn c {j} := by
  obtain ⟨_, ⟨r, -, rfl⟩, rfl⟩ := hv
  have h1 : xab hij a * LinearFlag.proj n K (pointRadElem c r) * (xab hij a)⁻¹ =
      LinearFlag.proj n K (pointRadElem c (r - Pi.single j (a * r i))) := by
    rw [xab_mul_proj_pointRadElem hij hic hjc, mul_inv_cancel_right]
  have h2 : LinearFlag.proj n K (pointRadElem c (r - Pi.single j (a * r i))) *
      (LinearFlag.proj n K (pointRadElem c r))⁻¹ =
      LinearFlag.proj n K (pointRadElem c (r - Pi.single j (a * r i) + -r)) := by
    rw [← map_inv, ← map_mul, pointRadElem_inv, pointRadElem_mul]
  rw [h1, h2]
  refine Subgroup.mem_map_of_mem _ ⟨r - Pi.single j (a * r i) + -r, fun m hm => ?_, rfl⟩
  have hmj : m ≠ j := fun h => hm (Finset.mem_singleton.2 h)
  simp [Pi.single_eq_of_ne hmj]

theorem xab_not_mem_centralizer_pointRadical (hK : Nat.card K = 2) {c i j : Fin n} (hij : i ≠ j)
    (hic : i ≠ c) (hjc : j ≠ c) :
    xab hij (1 : K) ∉ centralizer ((pointRadical (K := K) c :
      Subgroup (LinearFlag.projectiveSL n K)) : Set (LinearFlag.projectiveSL n K)) := by
  intro hC
  have h1 := (mem_centralizer_iff.1 hC) _ (proj_pointRadElem_single_mem_pointRadical hic 1)
  rw [xab_mul_proj_pointRadElem hij hic hjc] at h1
  have h3 := apply_eq_of_proj_pointRadElem_eq hK (mul_right_cancel h1) hjc
  simp [Pi.single_eq_of_ne (Ne.symm hij)] at h3

theorem pointRadMat_single_one {c m : Fin n} (hm : m ≠ c) :
    pointRadMat c (Pi.single m (1 : K)) = 1 + single c m 1 := by
  ext i j
  rw [pointRadMat_apply, Matrix.add_apply, single_apply, add_right_inj]
  by_cases hi : i = c
  · subst hi
    by_cases hj : j = m
    · subst hj
      simp [hm]
    · rw [Pi.single_eq_of_ne hj, ite_self]
      simp [Ne.symm hj]
  · simp [hi, Ne.symm hi]

theorem blockSL_compl_inf_centralizer_pointRadical (hK : Nat.card K = 2) (c : Fin n) :
    blockSL (K := K) ({c}ᶜ : Finset (Fin n)) ⊓
      centralizer ((pointRadical (K := K) c : Subgroup (LinearFlag.projectiveSL n K)) :
        Set (LinearFlag.projectiveSL n K)) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg, hgC⟩
  obtain ⟨A, hA, rfl⟩ := mem_blockSL.1 hg
  rw [Subgroup.mem_bot]
  have hcA : ∀ k, (A : Matrix (Fin n) (Fin n) K) c k = (1 : Matrix (Fin n) (Fin n) K) c k :=
    fun k => hA c k (Or.inl (by simp))
  have hrow : ∀ m l, m ≠ c →
      (A : Matrix (Fin n) (Fin n) K) m l = (1 : Matrix (Fin n) (Fin n) K) m l := by
    intro m l hm
    have h1 := (mem_centralizer_iff.1 hgC) _ (proj_pointRadElem_single_mem_pointRadical hm (1 : K))
    rw [← map_mul, ← map_mul] at h1
    have h2 := proj_injective_of_natCard_eq_two hK h1
    have h3 : pointRadMat c (Pi.single m 1) * (A : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) * pointRadMat c (Pi.single m 1) :=
      congrArg Subtype.val h2
    rw [pointRadMat_single_one hm, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      add_right_inj] at h3
    have h4 := congrFun (congrFun h3 c) l
    rw [single_mul_apply_same, one_mul] at h4
    by_cases hlm : l = m
    · subst hlm
      rw [mul_single_apply_same, hcA, mul_one] at h4
      rw [h4]
      simp
    · rw [mul_single_apply_of_ne _ _ _ _ _ hlm] at h4
      rw [h4, Matrix.one_apply_ne (Ne.symm hlm)]
  have hA1 : A = 1 := by
    ext m l
    by_cases hm : m = c
    · subst hm
      exact hcA l
    · exact hrow m l hm
  rw [hA1, map_one]

theorem pointRadical_inf_centralizer_xab_mul_xab_le (hK : Nat.card K = 2) {c i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) (hic : i ≠ c) (hjc : j ≠ c) (hkc : k ≠ c) (hlc : l ≠ c)
    (hli : l ≠ i) (hjl : j ≠ l) :
    pointRadical (K := K) c ⊓
        centralizer ({xab hij (1 : K) * xab hkl 1} : Set (LinearFlag.projectiveSL n K)) ≤
      pointRadOn c (({c}ᶜ : Finset (Fin n)) \ {i, k}) := by
  rintro _ ⟨⟨_, ⟨r, -, rfl⟩, rfl⟩, hv⟩
  have hv' := mem_centralizer_singleton_iff.1 hv
  have e1 : xab hij (1 : K) * xab hkl 1 * LinearFlag.proj n K (pointRadElem c r) =
      LinearFlag.proj n K (pointRadElem c ((r - Pi.single l (1 * r k)) -
        Pi.single j (1 * (r - Pi.single l (1 * r k) : Fin n → K) i))) *
        (xab hij 1 * xab hkl 1) := by
    rw [mul_assoc, xab_mul_proj_pointRadElem hkl hkc hlc, ← mul_assoc,
      xab_mul_proj_pointRadElem hij hic hjc, mul_assoc]
  have h := mul_right_cancel (hv'.trans e1)
  have hk0 : r k = 0 := by
    have := apply_eq_of_proj_pointRadElem_eq hK h hlc
    simp [Pi.single_eq_of_ne (Ne.symm hjl)] at this
    exact sub_eq_self.1 this.symm
  have hi0 : r i = 0 := by
    have := apply_eq_of_proj_pointRadElem_eq hK h hjc
    simp [Pi.single_eq_of_ne hjl, Pi.single_eq_of_ne (Ne.symm hli)] at this
    exact sub_eq_self.1 this.symm
  refine Subgroup.mem_map_of_mem _ ⟨Function.update r c 0, fun m hm => ?_, ?_⟩
  · by_cases hmc : m = c
    · subst hmc
      simp
    · have hmik : m = i ∨ m = k := by
        simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_singleton, Finset.mem_insert,
          not_and, not_not] at hm
        exact hm hmc
      rw [Function.update_of_ne hmc]
      rcases hmik with rfl | rfl
      · exact hi0
      · exact hk0
  · apply Subtype.ext
    change pointRadMat c (Function.update r c 0) = pointRadMat c r
    rw [pointRadMat, pointRadMat, Function.update_idem]

theorem specialLinearGroup_map_injective_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (SpecialLinearGroup.map (n := ι) f) := by
  intro A B h
  ext i j
  have h1 := congrArg (fun M : SpecialLinearGroup ι S => (M : Matrix ι ι S) i j) h
  exact hf h1

theorem xab_mul_xab_symm_mem_rootSL2 {p q : Fin n} (hpq : p ≠ q) (a b : K) :
    xab hpq a * xab hpq.symm b ∈ rootSL2 p q :=
  mul_mem (xab_mem_rootSL2 hpq a) (by rw [rootSL2_comm]; exact xab_mem_rootSL2 hpq.symm b)

theorem orderOf_xab_mul_xab_symm [CharP K 2] (hn : 3 ≤ n) {p q : Fin n} (hpq : p ≠ q) :
    orderOf (xab hpq (1 : K) * xab hpq.symm 1) = 3 := by
  set f : SpecialLinearGroup (Fin 2) (ZMod 2) →* LinearFlag.projectiveSL n K :=
    ((LinearFlag.proj n K).comp (pairEmbed hpq)).comp
      (SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) K)) with hf
  have hfi : Function.Injective f :=
    (proj_comp_pairEmbed_injective hpq hn).comp
      (specialLinearGroup_map_injective_of_injective (ZMod.castHom (dvd_refl 2) K).injective)
  have hfx : f (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : ZMod 2)) =
      xab hpq (1 : K) * xab hpq.symm 1 := by
    rw [map_mul, hf, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MonoidHom.comp_apply, Matrix.SpecialLinearGroup.map_transvection,
      Matrix.SpecialLinearGroup.map_transvection, map_one, pairEmbed_transvection_zero_one,
      pairEmbed_transvection_one_zero]
    rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← hfx, orderOf_injective f hfi]
  exact orderOf_eq_prime sl2_torus_pow_three sl2_torus_ne_one

end CFSG.SeitzReduction.LinearPilot
