module

public import CFSG.LieType.SeitzGeneration.RootPairOrthModel
public import CFSG.LieType.SeitzGeneration.RootPairOrthTail
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.LieType.SeitzGeneration.RootPairOrth

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

@[expose] def TailAnisotropic (S : HypCoord Q) : Prop :=
  ∀ v : Fin d → K, (∀ a ∈ S.hyp, v a = 0) → Q v = 0 → v = 0

@[expose] def ratEichlerGroup (Q : QuadraticForm K (Fin d → K)) (k : Subfield K) :
    Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  Subgroup.closure {E | ∃ u w : Fin d → K, IsRat k u ∧ IsRat k w ∧ Q u = 0 ∧ polar Q u w = 0 ∧
    E = eichler Q u w}

variable {k : Subfield K} {Q₀ : QuadraticForm k (Fin d → k)}

theorem eichler_mem_ratEichlerGroup {u w : Fin d → K} (hu : IsRat k u) (hw : IsRat k w)
    (hQu : Q u = 0) (hp : polar Q u w = 0) : eichler Q u w ∈ ratEichlerGroup Q k :=
  Subgroup.subset_closure ⟨u, w, hu, hw, hQu, hp, rfl⟩

private theorem tA1_isRat_smul {c : K} (hc : c ∈ k) {x : Fin d → K} (hx : IsRat k x) :
    IsRat k (c • x) := fun i => by
  rw [Pi.smul_apply, smul_eq_mul]
  exact k.mul_mem hc (hx i)

private theorem tA1_isRat_neg {x : Fin d → K} (hx : IsRat k x) : IsRat k (-x) := fun i => by
  rw [Pi.neg_apply]
  exact k.neg_mem (hx i)

private theorem tA1_isRat_eichler (hext : IsExtension k Q₀ Q) {u w : Fin d → K} (hu : IsRat k u)
    (hw : IsRat k w) (hQu : Q u = 0) (hp : polar Q u w = 0) {v : Fin d → K} (hv : IsRat k v) :
    IsRat k (eichler Q u w v) := by
  rw [eichler_apply hQu hp v]
  exact IsRat.sub
    (IsRat.add hv (tA1_isRat_smul (polar_isRat_mem hext hv hu) hw))
    (tA1_isRat_smul (k.add_mem (polar_isRat_mem hext hv hw)
      (k.mul_mem (Q_isRat_mem hext hw) (polar_isRat_mem hext hv hu))) hu)

private theorem tA1_both (hext : IsExtension k Q₀ Q) {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hg : g ∈ ratEichlerGroup Q k) :
    (∀ v : Fin d → K, IsRat k v → IsRat k (g v)) ∧
      (∀ v : Fin d → K, IsRat k v → IsRat k (g⁻¹ v)) := by
  unfold ratEichlerGroup at hg
  induction hg using Subgroup.closure_induction with
  | mem E hE =>
    obtain ⟨u, w, hu, hw, hQu, hp, rfl⟩ := hE
    refine ⟨fun v hv => tA1_isRat_eichler hext hu hw hQu hp hv, fun v hv => ?_⟩
    rw [eichler_inv hp]
    exact tA1_isRat_eichler hext hu (tA1_isRat_neg hw) hQu
      (by rw [polar_neg_right, hp, neg_zero]) hv
  | one =>
    exact ⟨fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [LinearEquiv.mul_apply]
      exact hx.1 _ (hy.1 v hv)
    · rw [_root_.mul_inv_rev, LinearEquiv.mul_apply]
      exact hy.2 _ (hx.2 v hv)
  | inv x _ hx =>
    refine ⟨hx.2, fun v hv => ?_⟩
    rw [inv_inv]
    exact hx.1 v hv

theorem ratEichlerGroup_le_orthogonalGroup :
    ratEichlerGroup Q k ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  unfold ratEichlerGroup
  rw [Subgroup.closure_le]
  rintro E ⟨u, w, -, -, -, -, rfl⟩
  exact eichler_mem_orthogonalGroup Q u w

theorem ratEichlerGroup_isRat (hext : IsExtension k Q₀ Q) {h : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hh : h ∈ ratEichlerGroup Q k) {v : Fin d → K} (hv : IsRat k v) : IsRat k (h v) :=
  (tA1_both hext hh).1 v hv

variable (S : HypCoord Q)

private theorem tA1_polar_star_single {a : Fin d} (ha : a ∈ S.hyp) {c : Fin d} (hc : c ≠ a)
    (t : K) : polar Q (Pi.single (S.star a) 1 : Fin d → K) (t • (Pi.single c 1 : Fin d → K)) = 0 := by
  rw [polar_smul_right_eq, S.polar_single_single (S.star_mem a ha) c, S.star_star a ha,
    if_neg (Ne.symm hc), mul_zero]

theorem eichler_star_single_apply {a : Fin d} (ha : a ∈ S.hyp) {c : Fin d} (hc : c ≠ a) (t : K)
    (x : Fin d → K) :
    eichler Q (Pi.single (S.star a) 1 : Fin d → K) (t • (Pi.single c 1 : Fin d → K)) x =
      x + (t * x a) • (Pi.single c 1 : Fin d → K) -
        (t * polar Q x (Pi.single c 1) + t ^ 2 * Q (Pi.single c 1) * x a) •
          (Pi.single (S.star a) 1 : Fin d → K) := by
  rw [eichler_apply (S.Q_single _ (S.star_mem a ha)) (tA1_polar_star_single S ha hc t) x,
    S.polar_single_right (S.star_mem a ha) x, S.star_star a ha, polar_smul_right_eq,
    map_smul_eq_sq, smul_smul, mul_comm (x a) t]

theorem eichler_star_single_mem {a : Fin d} (ha : a ∈ S.hyp) {c : Fin d} (hc : c ≠ a) {t : K}
    (ht : t ∈ k) :
    eichler Q (Pi.single (S.star a) 1 : Fin d → K) (t • (Pi.single c 1 : Fin d → K)) ∈
      ratEichlerGroup Q k :=
  eichler_mem_ratEichlerGroup (isRat_single k _) (tA1_isRat_smul ht (isRat_single k c))
    (S.Q_single _ (S.star_mem a ha)) (tA1_polar_star_single S ha hc t)

theorem exists_clear_fix (hext : IsExtension k Q₀ Q) {b : Fin d} (hb : b ∈ S.hyp)
    (T : Finset (Fin d)) (hT : ∀ c ∈ T, c ≠ b ∧ c ≠ S.star b) (u : Fin d → K)
    (hu : polar Q u (Pi.single (S.star b) 1) = 0 ∧ ∀ c ∈ T, polar Q u (Pi.single c 1) = 0) :
    ∀ x : Fin d → K, IsRat k x → x b = 1 → ∃ h ∈ ratEichlerGroup Q k, h u = u ∧
      (∀ c ∈ T, (h x) c = 0) ∧ (h x) b = 1 ∧ ∀ c, c ∉ T → c ≠ S.star b → (h x) c = x c := by
  revert hT hu
  induction T using Finset.induction_on with
  | empty =>
    intro _ _ x _ hxb
    exact ⟨1, Subgroup.one_mem _, rfl, fun c hc => by simp at hc, by simpa using hxb,
      fun c _ _ => rfl⟩
  | insert c T hcT ih =>
    intro hT hu x hx hxb
    have hcb : c ≠ b := (hT c (Finset.mem_insert_self c T)).1
    have hcs : c ≠ S.star b := (hT c (Finset.mem_insert_self c T)).2
    have hT' : ∀ d ∈ T, d ≠ b ∧ d ≠ S.star b := fun d hd => hT d (Finset.mem_insert_of_mem hd)
    have hu' : polar Q u (Pi.single (S.star b) 1 : Fin d → K) = 0 ∧
        ∀ j ∈ T, polar Q u (Pi.single j 1 : Fin d → K) = 0 :=
      ⟨hu.1, fun j hj => hu.2 j (Finset.mem_insert_of_mem hj)⟩
    obtain ⟨t, ht_def⟩ : ∃ t : K, t = -(x c) := ⟨_, rfl⟩
    have ht : t ∈ k := by
      rw [ht_def]
      exact k.neg_mem (hx c)
    have hEmem := eichler_star_single_mem S hb hcb ht
    have hEx := eichler_star_single_apply S hb hcb t x
    have hyrat : IsRat k (eichler Q (Pi.single (S.star b) 1 : Fin d → K)
        (t • (Pi.single c 1 : Fin d → K)) x) :=
      ratEichlerGroup_isRat hext hEmem hx
    have hEc : eichler Q (Pi.single (S.star b) 1 : Fin d → K)
        (t • (Pi.single c 1 : Fin d → K)) x c = 0 := by
      rw [hEx]
      simp [Pi.single_apply, hcs, hxb, ht_def]
    have hEb : eichler Q (Pi.single (S.star b) 1 : Fin d → K)
        (t • (Pi.single c 1 : Fin d → K)) x b = 1 := by
      rw [hEx]
      simp [Pi.single_apply, hcb.symm, (S.star_ne b hb).symm, hxb]
    have hEu : eichler Q (Pi.single (S.star b) 1 : Fin d → K)
        (t • (Pi.single c 1 : Fin d → K)) u = u := by
      apply eichler_apply_of_polar_eq_zero
      · exact hu'.1
      · rw [polar_smul_right_eq, hu.2 c (Finset.mem_insert_self c T), mul_zero]
    have hEout : ∀ j, j ≠ c → j ≠ S.star b →
        eichler Q (Pi.single (S.star b) 1 : Fin d → K)
          (t • (Pi.single c 1 : Fin d → K)) x j = x j := by
      intro j hjc hjs
      rw [hEx]
      simp [Pi.single_apply, hjc, hjs]
    obtain ⟨h', hh'mem, hh'u, hh'T, hh'b, hh'out⟩ := ih hT' hu' _ hyrat hEb
    refine ⟨h' * eichler Q (Pi.single (S.star b) 1 : Fin d → K)
      (t • (Pi.single c 1 : Fin d → K)), mul_mem hh'mem hEmem, ?_, ?_, ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, hEu, hh'u]
    · intro d hd
      rw [LinearEquiv.mul_apply]
      rcases Finset.mem_insert.mp hd with h1 | h1
      · rw [h1, hh'out c hcT hcs, hEc]
      · exact hh'T d h1
    · rw [LinearEquiv.mul_apply]
      exact hh'b
    · intro d hd hds
      rw [LinearEquiv.mul_apply, hh'out d (fun h => hd (Finset.mem_insert_of_mem h)) hds]
      exact hEout d (fun h => hd (by rw [h]; exact Finset.mem_insert_self c T)) hds

theorem eq_single_of_support_pair {a : Fin d} (ha : a ∈ S.hyp) {x : Fin d → K} (hQx : Q x = 0)
    (hsupp : ∀ c, c ≠ a → c ≠ S.star a → x c = 0) (hxa : x a = 1) :
    x = (Pi.single a 1 : Fin d → K) := by
  have has : S.star a ∈ S.hyp := S.star_mem a ha
  have hne : S.star a ≠ a := S.star_ne a ha
  have hdecomp : x = (Pi.single a 1 : Fin d → K) +
      x (S.star a) • (Pi.single (S.star a) 1 : Fin d → K) := by
    funext c
    by_cases hca : c = a
    · rw [hca]
      simp [Pi.single_apply, hne.symm, hxa]
    · by_cases hcs : c = S.star a
      · rw [hcs]
        simp [Pi.single_apply, hne]
      · simp [Pi.single_apply, hca, hcs, hsupp c hca hcs]
  have hs : x (S.star a) = 0 := by
    have h1 := hQx
    rw [hdecomp, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq,
      S.polar_single_single ha (S.star a), S.Q_single a ha, S.Q_single _ has] at h1
    simpa using h1
  rw [hdecomp, hs, zero_smul, add_zero]

end CFSG.LieType.SeitzGeneration.OmegaF2
