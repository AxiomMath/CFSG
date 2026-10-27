module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorOps
public import CFSG.LieType.SeitzGeneration.UnitaryNonCube

public section

namespace CFSG.LieType.SeitzGeneration.HeisTensor

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.BorelTits

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem exists_heisFrame [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    {X Y : Matrix (Fin n) (Fin n) K} {α ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) (hζ1 : ζ ≠ 1)
    (hζN : h.bar ζ * ζ = 1) (hα0 : α ≠ 0)
    (hX3 : X * X * X = α • 1) (hY3 : Y * Y * Y = 1) (hYX : Y * X = ζ • (X * Y))
    (hXu : ∀ u v, herm (unitaryInvolution K ℓ f) (X *ᵥ u) (X *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v)
    (hYu : ∀ u v, herm (unitaryInvolution K ℓ f) (Y *ᵥ u) (Y *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v) :
    ∃ m, Nonempty (HeisFrame (unitaryInvolution K ℓ f) n m X Y α ζ) := by
  classical
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσb : ∀ c, σ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  have hζ3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ
  have hbζ : h.bar ζ = ζ ^ 2 := by linear_combination (ζ ^ 2) * hζN - (h.bar ζ) * hζ3
  set YT : Module.End K (Fin n → K) := Matrix.toLin' Y with hYT
  have hYT3 : YT ^ 3 = algebraMap K (Module.End K (Fin n → K)) (1 ^ 3) := by
    have h1 : Y ^ 3 = 1 := by simpa [pow_succ] using hY3
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_one] at h2
    rw [one_pow, map_one]
    exact h2
  set E : Fin 3 → Submodule K (Fin n → K) :=
    fun j => Module.End.eigenspace YT (1 * ζ ^ (j : ℕ)) with hE
  have hsup : ⨆ j, E j = ⊤ := NonCube.iSup_eigenspace_eq_top hζ hζ1 one_ne_zero hYT3
  have hmem : ∀ j v, v ∈ E j ↔ Y *ᵥ v = ζ ^ (j : ℕ) • v := fun j v => by
    simp [hE, Module.End.mem_eigenspace_iff, hYT, Matrix.toLin'_apply]
  have hshift : ∀ (l : K) (v : Fin n → K), Y *ᵥ v = l • v →
      Y *ᵥ (X *ᵥ v) = (ζ * l) • (X *ᵥ v) := by
    intro l v hv
    rw [mulVec_mulVec, hYX, smul_mulVec, ← mulVec_mulVec, hv, mulVec_smul, smul_smul]
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h2
    apply hζ1
    linear_combination hζ3 - ζ * h2
  have hζk : ∀ k : ℕ, ¬ 3 ∣ k → ζ ^ k ≠ 1 := by
    intro k hk
    have hk' : k % 3 = 1 ∨ k % 3 = 2 := by omega
    have hdec : ζ ^ k = ζ ^ (k % 3) := by
      conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hζ3, one_pow, one_mul]
    rw [hdec]
    rcases hk' with h1 | h1 <;> rw [h1]
    · simpa using hζ1
    · exact hζ2
  have hlam_ne : ∀ i j : Fin 3, i ≠ j → h.bar (ζ ^ (i : ℕ)) * ζ ^ (j : ℕ) ≠ 1 := by
    intro i j hij
    have e : h.bar (ζ ^ (i : ℕ)) * ζ ^ (j : ℕ) = ζ ^ (2 * (i : ℕ) + (j : ℕ)) := by
      rw [map_pow, hbζ, ← pow_mul, ← pow_add]
    rw [e]
    refine hζk _ ?_
    have hij' : (i : ℕ) ≠ (j : ℕ) := fun h' => hij (Fin.ext h')
    have hi := i.2
    have hj := j.2
    omega
  have hYB : ∀ u v, idForm h n (YT u) (YT v) = idForm h n u v := fun u v => by
    rw [Nonsplit.idForm_eq_herm, Nonsplit.idForm_eq_herm]
    simpa [hYT, Matrix.toLin'_apply] using hYu u v
  have hV_orth : ∀ i j, i ≠ j → ∀ u ∈ E i, ∀ v ∈ E j, herm σ u v = 0 := by
    intro i j hij u hu v hv
    have := NonCube.eigen_orthogonal hYB (hlam_ne i j hij)
      (by simpa [hYT, Matrix.toLin'_apply] using (hmem i u).mp hu)
      (by simpa [hYT, Matrix.toLin'_apply] using (hmem j v).mp hv)
    rwa [Nonsplit.idForm_eq_herm] at this
  have hnd : ((idForm h n).domRestrict₁₂ (E 0) (E 0)).SeparatingLeft :=
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) E
      (fun i j hij u hu v hv => by rw [Nonsplit.idForm_eq_herm]; exact hV_orth i j hij u hu v hv)
      hsup 0
  obtain ⟨m, b, hb⟩ : ∃ (m : ℕ) (b : Module.Basis (Fin m) K (E 0)), ∀ i j,
      ((idForm h n).domRestrict₁₂ (E 0) (E 0)) (b i) (b j) = if i = j then 1 else 0 := by
    obtain ⟨b, hb⟩ := h.exists_orthonormal_basis ((idForm_isSymm h n).domRestrict (E 0)) hnd
    exact ⟨_, b, hb⟩
  set ε : Fin m → Fin n → K := fun r => ((b r : E 0) : Fin n → K) with hε
  have hεon : ∀ r s, herm σ (ε r) (ε s) = if r = s then 1 else 0 := by
    intro r s
    have := hb r s
    rw [LinearMap.domRestrict₁₂_apply, Nonsplit.idForm_eq_herm] at this
    exact this
  have hεmem : ∀ r, ε r ∈ E 0 := fun r => (b r).2
  have hYε : ∀ r, Y *ᵥ ε r = ε r := fun r => by simpa using (hmem 0 _).mp (hεmem r)
  have hX3v : ∀ x : Fin n → K, X *ᵥ (X *ᵥ (X *ᵥ x)) = α • x := fun x => by
    rw [mulVec_mulVec, mulVec_mulVec, hX3, smul_mulVec, one_mulVec]
  have hb1 : ∀ x ∈ E 1, ∃ w ∈ E 0, X *ᵥ w = x := by
    intro x hx
    have hxY : Y *ᵥ x = ζ • x := by simpa using (hmem 1 x).mp hx
    refine ⟨α⁻¹ • (X *ᵥ (X *ᵥ x)), ?_, ?_⟩
    · rw [hmem, mulVec_smul, hshift _ _ (hshift _ _ hxY), smul_comm]
      have : ζ * (ζ * ζ) = ζ ^ ((0 : Fin 3) : ℕ) := by simp; linear_combination hζ3
      rw [this]
    · rw [mulVec_smul, hX3v, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  have hb2 : ∀ x ∈ E 2, ∃ w ∈ E 1, X *ᵥ w = x := by
    intro x hx
    have hxY : Y *ᵥ x = ζ ^ 2 • x := by simpa using (hmem 2 x).mp hx
    refine ⟨α⁻¹ • (X *ᵥ (X *ᵥ x)), ?_, ?_⟩
    · rw [hmem, mulVec_smul, hshift _ _ (hshift _ _ hxY), smul_comm]
      have : ζ * (ζ * ζ ^ 2) = ζ ^ ((1 : Fin 3) : ℕ) := by
        simp
        linear_combination (ζ) * hζ3
      rw [this]
    · rw [mulVec_smul, hX3v, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  let fr : Fin 3 → Fin m → Fin n → K := fun k r => (X ^ (k : ℕ)) *ᵥ ε r
  have hf0 : ∀ r, fr 0 r = ε r := fun r => by simp [fr]
  have hf1 : ∀ r, fr 1 r = X *ᵥ ε r := fun r => by simp [fr]
  have hf2 : ∀ r, fr 2 r = X *ᵥ (X *ᵥ ε r) := fun r => by
    simp [fr, pow_two, mulVec_mulVec]
  have hY0 : ∀ r, Y *ᵥ fr 0 r = ζ ^ ((0 : Fin 3) : ℕ) • fr 0 r := fun r => by
    simp [hf0, hYε]
  have hY1' : ∀ r, Y *ᵥ (X *ᵥ ε r) = (ζ * 1) • (X *ᵥ ε r) := fun r =>
    hshift 1 (ε r) (by rw [hYε, one_smul])
  have hY1 : ∀ r, Y *ᵥ fr 1 r = ζ ^ ((1 : Fin 3) : ℕ) • fr 1 r := fun r => by
    rw [hf1, hY1']
    simp
  have hY2 : ∀ r, Y *ᵥ fr 2 r = ζ ^ ((2 : Fin 3) : ℕ) • fr 2 r := fun r => by
    rw [hf2, hshift _ _ (hY1' r)]
    simp [pow_two]
  have hfmem : ∀ k r, fr k r ∈ E k := fun k r => by
    rw [hmem]
    fin_cases k
    · exact hY0 r
    · exact hY1 r
    · exact hY2 r
  have hXiter : ∀ (k : Fin 3) (u v : Fin n → K),
      herm σ ((X ^ (k : ℕ)) *ᵥ u) ((X ^ (k : ℕ)) *ᵥ v) = herm σ u v := fun k u v => by
    fin_cases k
    · simp
    · simp [hXu]
    · simp [pow_two, ← mulVec_mulVec, hXu]
  have hfon : ∀ k r l s, herm σ (fr k r) (fr l s) = if k = l ∧ r = s then 1 else 0 := by
    intro k r l s
    by_cases hkl : k = l
    · subst hkl
      have h1 : herm σ (fr k r) (fr k s) = herm σ (ε r) (ε s) := hXiter k _ _
      rw [h1, hεon]
      simp
    · rw [hV_orth k l hkl _ (hfmem k r) _ (hfmem l s)]
      simp [hkl]
  have hexp : ∀ w ∈ E 0, ∃ c : Fin m → K, w = ∑ r, c r • ε r := fun w hw => by
    refine ⟨fun r => b.repr ⟨w, hw⟩ r, ?_⟩
    have h1 : (∑ r, b.repr ⟨w, hw⟩ r • b r : E 0) = ⟨w, hw⟩ := b.sum_repr ⟨w, hw⟩
    have h2 := congrArg Subtype.val h1
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  have hspan : ∀ v : Fin n → K, ∃ c : Fin 3 → Fin m → K, v = ∑ k, ∑ r, c k r • fr k r := by
    intro v
    have hv : v ∈ ⨆ j, E j := by rw [hsup]; exact Submodule.mem_top
    refine Submodule.iSup_induction E
      (motive := fun v => ∃ c : Fin 3 → Fin m → K, v = ∑ k, ∑ r, c k r • fr k r) hv ?_
      ⟨0, by simp⟩ ?_
    · intro j x hx
      fin_cases j
      · obtain ⟨c, rfl⟩ := hexp x hx
        refine ⟨fun k r => if k = 0 then c r else 0, ?_⟩
        simp [Fin.sum_univ_three, hf0]
      · obtain ⟨w, hw, rfl⟩ := hb1 x hx
        obtain ⟨c, rfl⟩ := hexp w hw
        refine ⟨fun k r => if k = 1 then c r else 0, ?_⟩
        simp [Fin.sum_univ_three, hf1, mulVec_sum, mulVec_smul]
      · obtain ⟨w, hw, rfl⟩ := hb2 x hx
        obtain ⟨w', hw', rfl⟩ := hb1 w hw
        obtain ⟨c, rfl⟩ := hexp w' hw'
        refine ⟨fun k r => if k = 2 then c r else 0, ?_⟩
        simp [Fin.sum_univ_three, hf2, mulVec_sum, mulVec_smul]
    · rintro x y ⟨c, rfl⟩ ⟨c', rfl⟩
      exact ⟨c + c', by simp [add_smul, Finset.sum_add_distrib]⟩
  refine ⟨m, ⟨{ f := fr, on := hfon, span := hspan, hY := ?_, hX0 := ?_, hX1 := ?_, hX2 := ?_ }⟩⟩
  · intro k r
    exact (hmem k _).mp (hfmem k r)
  · intro r
    rw [hf0, hf1]
  · intro r
    rw [hf1, hf2]
  · intro r
    rw [hf2, hX3v, hf0]

end CFSG.LieType.SeitzGeneration.HeisTensor
