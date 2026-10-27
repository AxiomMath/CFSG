module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutLinRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutUniDet
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.U

section UnitaryRank

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem kdY1Ent_mem_mu3 (x : Fin 4 → Kˣ) (hx : ∀ i, x i ∈ kdY1Mu3 K) (k : ℕ) :
    kdY1Ent K x k ∈ kdY1Mu3 K := by
  simp only [kdY1Ent]
  split_ifs
  · exact hx _
  · exact (kdY1Mu3 K).inv_mem (Subgroup.prod_mem _ fun i _ => hx i)
  · exact (kdY1Mu3 K).one_mem

theorem mu3_norm_one (h : UnitaryFieldData ℓ f K) (hdiv : 3 ∣ ℓ ^ f + 1) {y : Kˣ}
    (hy : y ∈ kdY1Mu3 K) : h.norm (y : K) = 1 := by
  rw [norm_eq_one_iff_pow]
  obtain ⟨k, hk⟩ := hdiv
  have h3 : y ^ 3 = 1 := (mem_rootsOfUnity 3 y).mp hy
  rw [hk, show 3 * k = 3 * k from rfl, pow_mul, h3, one_pow]

def kdY1UInv (m : ℕ) (x : Fin 4 → Kˣ) : Matrix (Fin m) (Fin m) K :=
  Matrix.diagonal fun j => ((kdY1Ent K x j)⁻¹ : K)

theorem kdY1Diag_mul_inv (m : ℕ) (x : Fin 4 → Kˣ) :
    kdY1Diag K m x * kdY1UInv m x = 1 := by
  rw [kdY1Diag, kdY1UInv, Matrix.diagonal_mul_diagonal]
  have : (fun j : Fin m => (kdY1Ent K x j : K) * ((kdY1Ent K x j)⁻¹ : K)) = fun _ => 1 := by
    funext j
    exact mul_inv_cancel₀ (Units.ne_zero _)
  simp only [this, Matrix.diagonal_one]

theorem kdY1UInv_mul_diag (m : ℕ) (x : Fin 4 → Kˣ) :
    kdY1UInv m x * kdY1Diag K m x = 1 := by
  rw [kdY1Diag, kdY1UInv, Matrix.diagonal_mul_diagonal]
  have : (fun j : Fin m => ((kdY1Ent K x j)⁻¹ : K) * (kdY1Ent K x j : K)) = fun _ => 1 := by
    funext j
    exact inv_mul_cancel₀ (Units.ne_zero _)
  simp only [this, Matrix.diagonal_one]

def kdY1UGL (m : ℕ) (x : Fin 4 → Kˣ) : GL (Fin m) K :=
  ⟨kdY1Diag K m x, kdY1UInv m x, kdY1Diag_mul_inv m x, kdY1UInv_mul_diag m x⟩

@[expose] def kdY1UHom (m : ℕ) : (Fin 4 → Kˣ) →* GL (Fin m) K where
  toFun x := kdY1UGL m x
  map_one' := by
    apply Units.ext
    simp only [kdY1UGL, kdY1Diag, Units.val_one, Matrix.diagonal_one]
    congr 1
    funext j
    simp [kdY1Ent_one]
  map_mul' x y := by
    apply Units.ext
    show kdY1Diag K m (x * y) = kdY1Diag K m x * kdY1Diag K m y
    rw [kdY1Diag, kdY1Diag, kdY1Diag, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp [kdY1Ent_mul]

theorem bar_mul_kdY1Ent (h : UnitaryFieldData ℓ f K) (hdiv : 3 ∣ ℓ ^ f + 1) (x : Fin 4 → Kˣ)
    (hx : ∀ i, x i ∈ kdY1Mu3 K) (k : ℕ) :
    h.bar ((kdY1Ent K x k : Kˣ) : K) * ((kdY1Ent K x k : Kˣ) : K) = 1 := by
  have h1 := mu3_norm_one h hdiv (kdY1Ent_mem_mu3 x hx k)
  rw [UnitaryFieldData.norm] at h1
  rw [mul_comm]
  exact h1

theorem kdY1UGL_mem_gramSU (h : UnitaryFieldData ℓ f K) (hdiv : 3 ∣ ℓ ^ f + 1) {m : ℕ}
    (hm : 5 ≤ m) (x : Fin 4 → Kˣ) (hx : ∀ i, x i ∈ kdY1Mu3 K) :
    kdY1UGL m x ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU h
      ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
  refine (mem_gramSU_iff_unitary h).mpr ⟨?_, ?_⟩
  · rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    show ((kdY1Diag K m x).map h.bar).transpose * kdY1Diag K m x = 1
    rw [kdY1Diag, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have : (fun j : Fin m => h.bar ((kdY1Ent K x j : Kˣ) : K) * ((kdY1Ent K x j : Kˣ) : K)) =
        fun _ => 1 := by
      funext j
      exact bar_mul_kdY1Ent h hdiv x hx j
    simp only [Function.comp_def, this, Matrix.diagonal_one]
  · show (kdY1Diag K m x).det = 1
    exact kdY1Diag_det K hm x

@[expose] def kdY1UGS (h : UnitaryFieldData ℓ f K) (hdiv : 3 ∣ ℓ ^ f + 1) {m : ℕ} (hm : 5 ≤ m) :
    (Fin 4 → kdY1Mu3 K) →* StatedSU m (ℓ ^ f) K :=
  ((kdY1UHom m).comp (kdY1Coord K)).codRestrict (StatedSU m (ℓ ^ f) K) fun x => by
    rw [statedSU_eq_gramSU h (n := m)]
    exact kdY1UGL_mem_gramSU h hdiv hm _ (fun i => (x i).2)

@[expose] def kdY1UPhi (h : UnitaryFieldData ℓ f K) (hdiv : 3 ∣ ℓ ^ f + 1) {m : ℕ} (hm : 6 ≤ m) :
    (Fin 4 → kdY1Mu3 K) →* StatedProj (StatedSU m (ℓ ^ f) K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin m) K).subgroupOf (StatedSU m (ℓ ^ f) K))).comp
    (kdY1UGS h hdiv (by omega : 5 ≤ m))

theorem kdY1UPhi_injective (h : UnitaryFieldData ℓ f K) (hdiv : 3 ∣ ℓ ^ f + 1) {m : ℕ}
    (hm : 6 ≤ m) : Function.Injective (kdY1UPhi h hdiv hm) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, kdY1UPhi, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hx
  have hentry : ∀ i : Fin m, ((kdY1Ent K (fun k => ((x k : kdY1Mu3 K) : Kˣ)) i : Kˣ) : K) = (c : K) := by
    intro i
    have e1 : ((kdY1UGS h hdiv (by omega : 5 ≤ m) x : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) i i =
        ((kdY1Ent K (fun k => ((x k : kdY1Mu3 K) : Kˣ)) i : Kˣ) : K) := by
      show kdY1Diag K m _ i i = _
      rw [kdY1Diag, Matrix.diagonal_apply_eq]
      rfl
    have e2 : ((Matrix.GeneralLinearGroup.scalar (Fin m) c : GL (Fin m) K) :
        Matrix (Fin m) (Fin m) K) i i = (c : K) := by
      show Matrix.scalar (Fin m) (c : K) i i = _
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    have h1 := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K) i i) hc
    rw [e1, e2] at h1
    exact h1.symm
  have h5 := hentry ⟨5, by omega⟩
  have hc1 : (c : K) = 1 := by
    rw [← h5]
    simp [kdY1Ent]
  have hcoord : ∀ k : ℕ, (hk : k < 4) → ((x ⟨k, hk⟩ : kdY1Mu3 K) : Kˣ) = 1 := by
    intro k hk
    have h' := hentry ⟨k, by omega⟩
    rw [hc1] at h'
    have h'' : kdY1Ent K (fun k => ((x k : kdY1Mu3 K) : Kˣ)) k = 1 := Units.ext (by simpa using h')
    simpa [kdY1Ent, hk] using h''
  rw [Subgroup.mem_bot]
  funext i
  exact Subtype.ext (by simpa using hcoord i.1 i.2)

theorem kdY1UPhi_range_isElemAbelian (h : UnitaryFieldData ℓ f K) (hdiv : 3 ∣ ℓ ^ f + 1)
    {m : ℕ} (hm : 6 ≤ m) : CFSG.Open.IsElemAbelian 3 (kdY1UPhi h hdiv hm).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · intro z hz
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hz
    have hy : y ^ 3 = 1 := by
      funext i
      have h3 : ((y i : kdY1Mu3 K) : Kˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp (y i).2
      apply Subtype.ext
      simpa using h3
    rw [← map_pow, hy, map_one]

theorem three_dvd_sq_sub_one (a : ℕ) (ha : 1 ≤ a) (h3 : 3 ∣ a + 1) : 3 ∣ a * a - 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [show (b + 1) * (b + 1) = b * (b + 2) + 1 by ring, Nat.add_sub_cancel]
  exact Dvd.dvd.mul_left (by simpa [show b + 1 + 1 = b + 2 by ring] using h3) b

theorem kdY1UPhi_card (h : UnitaryFieldData ℓ f K) (hdiv : 3 ∣ ℓ ^ f + 1) {m : ℕ}
    (hm : 6 ≤ m) : Nat.card (kdY1UPhi h hdiv hm).range = 3 ^ 4 := by
  haveI := h.finite
  have hsq : Nat.card K = ℓ ^ f * ℓ ^ f := by rw [h.card, two_mul, pow_add]
  have h3N : 3 ∣ Nat.card K - 1 := by
    rw [hsq]
    exact three_dvd_sq_sub_one _ (pow_pos h.prime.pos f) hdiv
  obtain ⟨ζ, hζ⟩ := kdY1Out_exists_isPrimitiveRoot_three K h3N
  have hmu : Nat.card (kdY1Mu3 K) = 3 := hζ.card_rootsOfUnity
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (kdY1UPhi_injective h hdiv hm),
    Subgroup.card_top, Nat.card_fun, hmu]
  simp

theorem exists_elemAbelian_card_81_unitary (h : UnitaryFieldData ℓ f K) (hdiv : 3 ∣ ℓ ^ f + 1)
    {m : ℕ} (hm : 6 ≤ m) :
    ∃ E : Subgroup (StatedProj (StatedSU m (ℓ ^ f) K)),
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  ⟨(kdY1UPhi h hdiv hm).range, kdY1UPhi_range_isElemAbelian h hdiv hm, kdY1UPhi_card h hdiv hm⟩

end UnitaryRank

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
