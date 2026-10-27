module

public import CFSG.LargeExtraspecial.DW37Input
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.L2

open Matrix Subgroup CFSG.Open
open scoped MatrixGroups

variable {n : ℕ}

local notation "M[" g "]" =>
  ((g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))

theorem gen_annih {K : Type} [Field K] {m : ℕ} (W : Submodule K (Fin m → K)) (hW : W ≠ ⊤) :
    ∃ f : (Fin m → K) →ₗ[K] K, f ≠ 0 ∧ W ≤ LinearMap.ker f :=
  Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.2 hW)

theorem gen_rn {K : Type} [Field K] {m : ℕ} (f : (Fin m → K) →ₗ[K] (Fin m → K)) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) = m := by
  have := LinearMap.finrank_range_add_finrank_ker f
  rwa [Module.finrank_fin_fun] at this

theorem gen_span {K : Type} [Field K] {m : ℕ} {x : Fin m → K} (hx : x ≠ 0) :
    Module.finrank K (K ∙ x) = 1 :=
  finrank_span_singleton hx

theorem gen_sup_le {K : Type} [Field K] {m : ℕ} (s t : Submodule K (Fin m → K)) :
    Module.finrank K ↥(s ⊔ t) ≤ Module.finrank K s + Module.finrank K t := by
  rw [← Submodule.add_eq_sup]
  exact Submodule.finrank_add_le_finrank_add_finrank s t

theorem gen_top {K : Type} [Field K] {m : ℕ} :
    Module.finrank K (⊤ : Submodule K (Fin m → K)) = m := by
  rw [finrank_top, Module.finrank_fin_fun]

@[expose] def outer (x h : Fin n → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) := vecMulVec x h

theorem outer_mulVec (x h u : Fin n → ZMod 2) : outer x h *ᵥ u = (h ⬝ᵥ u) • x := by
  funext i
  have hij : ∀ j, outer x h i j = x i * h j := fun j => rfl
  simp only [mulVec, dotProduct, hij, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem oneAdd_mulVec (x h v : Fin n → ZMod 2) :
    (1 + outer x h) *ᵥ v = v + (h ⬝ᵥ v) • x := by
  rw [add_mulVec, one_mulVec, outer_mulVec]

theorem zmod2_add_self : ∀ c : ZMod 2, c + c = 0 := by decide

theorem add_self_zmod2 (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  exact zmod2_add_self (x i)

theorem mul_self_eq_one_of_mulVec {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : ∀ v, M *ᵥ (M *ᵥ v) = v) : M * M = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, one_mulVec, ← mulVec_mulVec]
  exact h v

theorem det_eq_one_of_mul_self {M : Matrix (Fin n) (Fin n) (ZMod 2)} (h : M * M = 1) :
    M.det = 1 := by
  have h1 : M.det * M.det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  have key : ∀ d : ZMod 2, d * d = 1 → d = 1 := by decide
  exact key _ h1

theorem oneAdd_mulVec_sq (x h : Fin n → ZMod 2) (hxh : h ⬝ᵥ x = 0) (v : Fin n → ZMod 2) :
    (1 + outer x h) *ᵥ ((1 + outer x h) *ᵥ v) = v := by
  rw [oneAdd_mulVec, oneAdd_mulVec, dotProduct_add, dotProduct_smul, hxh, smul_zero, add_zero,
    add_assoc, ← add_smul, zmod2_add_self, zero_smul, add_zero]

@[expose] def oneAddOuter (x h : Fin n → ZMod 2) (hxh : h ⬝ᵥ x = 0) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  ⟨1 + outer x h, det_eq_one_of_mul_self (mul_self_eq_one_of_mulVec (oneAdd_mulVec_sq x h hxh))⟩

theorem coe_oneAddOuter (x h : Fin n → ZMod 2) (hxh : h ⬝ᵥ x = 0) :
    M[oneAddOuter x h hxh] = 1 + outer x h := rfl

theorem exists_vec_annihilator {W : Submodule (ZMod 2) (Fin n → ZMod 2)} (hW : W ≠ ⊤) :
    ∃ f : Fin n → ZMod 2, f ≠ 0 ∧ ∀ w ∈ W, f ⬝ᵥ w = 0 := by
  obtain ⟨φ, hφ0, hφW⟩ := gen_annih (K := ZMod 2) W hW
  have hrep : ∀ v : Fin n → ZMod 2, φ v = (fun i => φ (Pi.single i 1)) ⬝ᵥ v := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : Pi.single i (v i) = v i • (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) := by
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj, Pi.single_apply]
    rw [hs, map_smul, smul_eq_mul]
    simp only [mul_comm]
  refine ⟨fun i => φ (Pi.single i 1), ?_, fun w hw => ?_⟩
  · intro hf
    apply hφ0
    apply LinearMap.ext
    intro v
    rw [hrep v, hf, zero_dotProduct, LinearMap.zero_apply]
  · rw [← hrep w]
    exact LinearMap.mem_ker.1 (hφW hw)

abbrev unipPred (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Prop :=
  (∀ v, (M[g] - 1) *ᵥ v ∈ W) ∧ ∀ w ∈ W, M[g] *ᵥ w = w

theorem unipPred_one (W : Submodule (ZMod 2) (Fin n → ZMod 2)) : unipPred W 1 := by
  refine ⟨fun v => ?_, fun w _ => ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_one, sub_self, zero_mulVec]
    exact W.zero_mem
  · rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem unipPred_mul {W : Submodule (ZMod 2) (Fin n → ZMod 2)} {g h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : unipPred W g) (hh : unipPred W h) : unipPred W (g * h) := by
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · have e1 : (M[g * h] - 1) *ᵥ v = M[g] *ᵥ (M[h] *ᵥ v) - v := by
      rw [Matrix.SpecialLinearGroup.coe_mul, sub_mulVec, one_mulVec, mulVec_mulVec]
    have e2 : (M[g] - 1) *ᵥ (M[h] *ᵥ v) = M[g] *ᵥ (M[h] *ᵥ v) - M[h] *ᵥ v := by
      rw [sub_mulVec, one_mulVec]
    have e3 : (M[h] - 1) *ᵥ v = M[h] *ᵥ v - v := by
      rw [sub_mulVec, one_mulVec]
    have hsum := W.add_mem (hg1 (M[h] *ᵥ v)) (hh1 v)
    rw [e2, e3] at hsum
    rw [e1]
    have eq : M[g] *ᵥ (M[h] *ᵥ v) - v =
        (M[g] *ᵥ (M[h] *ᵥ v) - M[h] *ᵥ v) + (M[h] *ᵥ v - v) := by abel
    rw [eq]
    exact hsum
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hh2 w hw, hg2 w hw]

theorem unipPred_inv {W : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {g k : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hgk : g * k = 1) (hkg : k * g = 1) (hg : unipPred W g) : unipPred W k := by
  obtain ⟨hg1, hg2⟩ := hg
  have hKG : M[k] * M[g] = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hkg, Matrix.SpecialLinearGroup.coe_one]
  have hfix : ∀ w ∈ W, M[k] *ᵥ w = w := by
    intro w hw
    calc M[k] *ᵥ w = M[k] *ᵥ (M[g] *ᵥ w) := by rw [hg2 w hw]
      _ = w := by rw [mulVec_mulVec, hKG, one_mulVec]
  refine ⟨fun v => ?_, hfix⟩
  have hd : M[g] *ᵥ v - v ∈ W := by
    have := hg1 v
    rwa [sub_mulVec, one_mulVec] at this
  have hsum : M[k] *ᵥ (M[g] *ᵥ v - v) = v - M[k] *ᵥ v := by
    rw [mulVec_sub, mulVec_mulVec, hKG, one_mulVec]
  have rel : M[g] *ᵥ v - v = v - M[k] *ᵥ v := (hfix _ hd).symm.trans hsum
  have key : (M[k] - 1) *ᵥ v = -(M[g] *ᵥ v - v) := by
    rw [sub_mulVec, one_mulVec]
    exact ((congrArg Neg.neg rel).trans (neg_sub _ _)).symm
  rw [key]
  exact W.neg_mem hd

@[expose] def unip (W : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) where
  carrier := {g | unipPred W g}
  mul_mem' := fun {_ _} hg hh => unipPred_mul hg hh
  one_mem' := unipPred_one W
  inv_mem' := fun {g} hg => unipPred_inv (k := g⁻¹) (mul_inv_cancel g) (inv_mul_cancel g) hg

theorem mem_unip {W : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} :
    g ∈ unip W ↔ unipPred W g :=
  Iff.rfl

theorem unip_mul_self (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hg : g ∈ unip W) :
    M[g] * M[g] = 1 := by
  apply mul_self_eq_one_of_mulVec
  intro v
  obtain ⟨hg1, hg2⟩ := mem_unip.1 hg
  obtain ⟨d, hd_def⟩ : ∃ d, d = M[g] *ᵥ v - v := ⟨_, rfl⟩
  have hd : d ∈ W := by
    rw [hd_def]
    have := hg1 v
    rwa [sub_mulVec, one_mulVec] at this
  have hGv : M[g] *ᵥ v = v + d := by
    rw [hd_def]; abel
  rw [hGv, mulVec_add, hg2 d hd, hGv, add_assoc, add_self_zmod2, add_zero]

theorem exists_ne_one_unip {W : Submodule (ZMod 2) (Fin n → ZMod 2)} (hW1 : W ≠ ⊥)
    (hW2 : W ≠ ⊤) : ∃ g ∈ unip W, g ≠ 1 := by
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW1
  obtain ⟨f, hf0, hfW⟩ := exists_vec_annihilator hW2
  have hfu : f ⬝ᵥ u = 0 := hfW u huW
  refine ⟨oneAddOuter u f hfu, mem_unip.2 ⟨fun v => ?_, fun w hw => ?_⟩, ?_⟩
  · rw [coe_oneAddOuter]
    have e : (1 + outer u f - 1 : Matrix (Fin n) (Fin n) (ZMod 2)) = outer u f := by abel
    rw [e, outer_mulVec]
    exact W.smul_mem _ huW
  · rw [coe_oneAddOuter, oneAdd_mulVec, hfW w hw, zero_smul, add_zero]
  · intro h1
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hf0
    have hI : M[oneAddOuter u f hfu] = 1 := by rw [h1, Matrix.SpecialLinearGroup.coe_one]
    have hm : (1 + outer u f) *ᵥ Pi.single i 1 = Pi.single i 1 := by
      rw [← coe_oneAddOuter u f hfu, hI, one_mulVec]
    rw [oneAdd_mulVec, dotProduct_single, mul_one] at hm
    have hfi : f i = 1 := by
      have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
      exact key _ hi
    have hz : (f i) • u = 0 := add_eq_left.1 hm
    rw [hfi, one_smul] at hz
    exact hu0 hz

theorem inv_fix_of_fix {W : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {g k : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hkg : k * g = 1)
    (hg : ∀ w ∈ W, M[g] *ᵥ w = w) : ∀ w ∈ W, M[k] *ᵥ w = w := by
  have hKG : M[k] * M[g] = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hkg, Matrix.SpecialLinearGroup.coe_one]
  intro w hw
  calc M[k] *ᵥ w = M[k] *ᵥ (M[g] *ᵥ w) := by rw [hg w hw]
    _ = w := by rw [mulVec_mulVec, hKG, one_mulVec]

theorem normalizes_unip (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    {g k : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hk : g * k = 1) (hkg : k * g = 1)
    (hW1 : ∀ w ∈ W, M[g] *ᵥ w ∈ W) (hW2 : ∀ w ∈ W, M[k] *ᵥ w ∈ W)
    {u : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hu : u ∈ unip W) :
    g * u * k ∈ unip W := by
  obtain ⟨hu1, hu2⟩ := mem_unip.1 hu
  have hGK : M[g] * M[k] = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hk, Matrix.SpecialLinearGroup.coe_one]
  have hKG : M[k] * M[g] = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hkg, Matrix.SpecialLinearGroup.coe_one]
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · have e : (M[g * u * k] - 1) *ᵥ v = M[g] *ᵥ ((M[u] - 1) *ᵥ (M[k] *ᵥ v)) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      simp only [sub_mulVec, one_mulVec, mulVec_sub, mulVec_mulVec, mul_assoc, sub_mul, mul_sub,
        one_mul, hGK]
    rw [e]
    exact hW1 _ (hu1 _)
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    calc (M[g] * M[u] * M[k]) *ᵥ w = M[g] *ᵥ (M[u] *ᵥ (M[k] *ᵥ w)) := by
          simp only [mulVec_mulVec, mul_assoc]
      _ = M[g] *ᵥ (M[k] *ᵥ w) := by rw [hu2 _ (hW2 w hw)]
      _ = w := by rw [mulVec_mulVec, hGK, one_mulVec]

theorem mem_normalizer_of_conj {G : Type} [Group G] {H : Subgroup G} {g k : G}
    (hk : g * k = 1) (hkg : k * g = 1) (hconj : ∀ u ∈ H, g * u * k ∈ H)
    (hconj' : ∀ u ∈ H, k * u * g ∈ H) : g ∈ normalizer (H : Set G) := by
  have hk' : k = g⁻¹ := (inv_eq_of_mul_eq_one_right hk).symm
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have h1 := hconj u hu
    rwa [hk'] at h1
  · intro hu
    have h1 := hconj' (g * u * g⁻¹) (by simpa only [hk'] using hu)
    have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rwa [hk', e] at h1

theorem mem_normalizer_unip_of (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    {g k : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hk : g * k = 1) (hkg : k * g = 1)
    (hW1 : ∀ w ∈ W, M[g] *ᵥ w ∈ W) (hW2 : ∀ w ∈ W, M[k] *ᵥ w ∈ W) :
    g ∈ normalizer ((unip W : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
      Set (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :=
  mem_normalizer_of_conj hk hkg (fun u hu => normalizes_unip W hk hkg hW1 hW2 hu)
    (fun u hu => normalizes_unip W hkg hk hW2 hW1 hu)

end CFSG.LocalAnalysis.GLTheoremA.Timm.L2
