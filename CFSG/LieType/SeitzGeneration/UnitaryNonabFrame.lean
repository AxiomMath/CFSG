module

public import CFSG.LieType.SeitzGeneration.UnitaryNonabDefs
public import CFSG.LieType.SeitzGeneration.UnitaryNonabNonPthAlgebra
public import CFSG.LieType.SeitzGeneration.UnitaryNonCubeAlgebra
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit

public section

namespace CFSG.LieType.SeitzGeneration.HeisP

open Matrix CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {p : ℕ}

theorem Zm_apply (ζ : K) (a b : Fin p) : Zm ζ a b = if a = b then ζ ^ (a : ℕ) else 0 := by
  simp [Zm, Matrix.diagonal_apply]

theorem Gj_apply [NeZero p] (ζ α : K) (j : ℕ) (a b : Fin p) :
    Gj ζ α j a b =
      if a = b + 1 then ζ ^ (j * (b : ℕ)) * (if (b : ℕ) + 1 = p then α else 1) else 0 :=
  rfl

theorem mul_Zm_apply (ζ : K) (M : Matrix (Fin p) (Fin p) K) (a b : Fin p) :
    (M * (Zm ζ : Matrix (Fin p) (Fin p) K)) a b = M a b * ζ ^ (b : ℕ) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Zm_apply, if_pos rfl]
  · intro c _ hc
    rw [Zm_apply, if_neg hc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem Gj_one_zero_eq_transpose [NeZero p] (ζ : K) :
    (Gj ζ 1 0 : Matrix (Fin p) (Fin p) K) = (heisShiftMat K p)ᵀ := by
  ext a b
  simp only [Gj_apply, heisShiftMat, Matrix.transpose_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, finRotate_apply, Option.mem_def]
  by_cases hab : a = b + 1
  · subst hab
    simp
  · have hba : ¬ (b + 1 = a) := fun h => hab h.symm
    simp [hab, hba]

theorem herm_sum_smul_right {σ : K ≃+* K} {ι : Type*} [Fintype ι] {n : ℕ}
    (x : Fin n → K) (g : ι → K) (w : ι → Fin n → K) :
    herm σ x (∑ i, g i • w i) = ∑ i, g i * herm σ x (w i) := by
  simp only [herm_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem HeisFrameP.card_eq {σ : K ≃+* K} {m n : ℕ} [NeZero p] {X Y : Matrix (Fin n) (Fin n) K}
    {α ζ : K} (F : HeisFrameP σ p n m X Y α ζ) (hσ : ∀ c, σ (σ c) = c) : n = p * m := by
  classical
  let v : Fin p × Fin m → (Fin n → K) := fun x => F.f x.1 x.2
  have hon : ∀ x i : Fin p × Fin m, herm σ (v x) (v i) = if x = i then 1 else 0 := by
    rintro ⟨k, r⟩ ⟨l, s⟩
    simp only [v, F.on, Prod.mk.injEq]
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg x
    have h1 : herm σ (v x) (∑ i, g i • v i) = g x := by
      rw [herm_sum_smul_right]
      simp [hon]
    rw [hg, herm_zero_right] at h1
    exact h1.symm
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro w _
    obtain ⟨c, rfl⟩ := F.span w
    exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(k, r), rfl⟩)
  have hcard := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  rw [Module.finrank_fin_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  exact hcard

theorem HeisFrameP.exists_matrix {σ : K ≃+* K} [NeZero p] {X Y : Matrix (Fin p) (Fin p) K}
    {α ζ : K} (F : HeisFrameP σ p p 1 X Y α ζ) :
    ∃ P : Matrix (Fin p) (Fin p) K, (∀ a b, ∑ i, σ (P i a) * P i b = if a = b then 1 else 0) ∧
      X * P = P * Gj ζ α 0 ∧ Y * P = P * Zm ζ := by
  refine ⟨Matrix.of fun i a => F.f a 0 i, fun a b => ?_, ?_, ?_⟩
  · have h := F.on a 0 b 0
    simpa [herm_def] using h
  · ext i b
    have h1 := congrFun (F.hX b 0) i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at h1
    simp only [Matrix.mul_apply, Matrix.of_apply, Gj_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_mul, pow_zero, one_mul]
    rw [h1]
    split_ifs <;> ring
  · ext i a
    have h1 := congrFun (F.hY a 0) i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at h1
    rw [Matrix.mul_apply, mul_Zm_apply]
    simp only [Matrix.of_apply]
    rw [h1, mul_comm]

section Existence

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.BorelTits

variable {ℓ f n : ℕ}

theorem exists_heisFrameP [Finite K] [Fact ℓ.Prime] [CharP K ℓ] [NeZero p]
    (h : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) {X Y : Matrix (Fin n) (Fin n) K}
    {α ζ : K} (hζ : IsPrimitiveRoot ζ p) (hα0 : α ≠ 0) (hX : X ^ p = α • 1) (hY : Y ^ p = 1)
    (hYX : Y * X = ζ • (X * Y))
    (hXu : ∀ u v, herm (unitaryInvolution K ℓ f) (X *ᵥ u) (X *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v)
    (hYu : ∀ u v, herm (unitaryInvolution K ℓ f) (Y *ᵥ u) (Y *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v) :
    ∃ m, Nonempty (HeisFrameP (unitaryInvolution K ℓ f) p n m X Y α ζ) := by
  classical
  set σ := unitaryInvolution K ℓ f with hσdef
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hbζ : h.bar ζ * ζ = 1 := by
    rw [UnitaryFieldData.bar_apply, ← pow_succ]
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, hζp, one_pow]
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K ℓ] at h0
    have hℓ : ℓ.Prime := Fact.out
    have hℓp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp h0
    rw [← hℓp] at hpq
    have h2 : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by have := h.one_le; omega)
    exact hℓ.not_dvd_one ((Nat.dvd_add_right h2).mp hpq)
  set YT : Module.End K (Fin n → K) := Matrix.toLin' Y with hYT
  have hYTp : YT ^ p = algebraMap K (Module.End K (Fin n → K)) (1 ^ p) := by
    have h2 := congrArg Matrix.toLinAlgEquiv' hY
    rw [map_pow, map_one] at h2
    rw [one_pow, map_one]
    exact h2
  set E : Fin p → Submodule K (Fin n → K) :=
    fun j => Module.End.eigenspace YT (1 * ζ ^ (j : ℕ)) with hE
  have hsup : ⨆ j, E j = ⊤ := NonPth.iSup_eigenspace_eq_top_p hp hpK hζ one_ne_zero hYTp
  have hmem : ∀ j v, v ∈ E j ↔ Y *ᵥ v = ζ ^ (j : ℕ) • v := fun j v => by
    simp [hE, Module.End.mem_eigenspace_iff, hYT, Matrix.toLin'_apply]
  have hshift : ∀ (l : K) (v : Fin n → K), Y *ᵥ v = l • v →
      Y *ᵥ (X *ᵥ v) = (ζ * l) • (X *ᵥ v) := by
    intro l v hv
    rw [mulVec_mulVec, hYX, smul_mulVec, ← mulVec_mulVec, hv, mulVec_smul, smul_smul]
  have hYpow : ∀ (k : ℕ) (v : Fin n → K) (l : K), Y *ᵥ v = l • v →
      Y *ᵥ (X ^ k *ᵥ v) = (ζ ^ k * l) • (X ^ k *ᵥ v) := by
    intro k
    induction k with
    | zero => intro v l hv; simpa using hv
    | succ k ih =>
      intro v l hv
      rw [pow_succ', ← mulVec_mulVec, hshift _ _ (ih v l hv),
        show ζ * (ζ ^ k * l) = ζ ^ (k + 1) * l by ring]
  have hbζ' : ∀ i : ℕ, h.bar (ζ ^ i) * ζ ^ i = 1 := by
    intro i
    rw [map_pow, ← mul_pow, hbζ, one_pow]
  have hlam_ne : ∀ i j : Fin p, i ≠ j → h.bar (ζ ^ (i : ℕ)) * ζ ^ (j : ℕ) ≠ 1 := by
    intro i j hij heq
    have h2 : ζ ^ (j : ℕ) = ζ ^ (i : ℕ) := by
      calc ζ ^ (j : ℕ) = (h.bar (ζ ^ (i : ℕ)) * ζ ^ (i : ℕ)) * ζ ^ (j : ℕ) := by
            rw [hbζ' i, one_mul]
        _ = ζ ^ (i : ℕ) * (h.bar (ζ ^ (i : ℕ)) * ζ ^ (j : ℕ)) := by ring
        _ = ζ ^ (i : ℕ) := by rw [heq, mul_one]
    exact hij (Fin.ext (hζ.pow_inj i.isLt j.isLt h2.symm))
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
  have hXp : ∀ x : Fin n → K, X ^ p *ᵥ x = α • x := fun x => by
    rw [hX, smul_mulVec, one_mulVec]
  have hXpm : X * X ^ (p - 1) = X ^ p := by
    rw [← pow_succ']
    congr 1
    have := hp.pos
    omega
  have hXinv : ∀ x : Fin n → K, X *ᵥ (α⁻¹ • (X ^ (p - 1) *ᵥ x)) = x := fun x => by
    rw [mulVec_smul, mulVec_mulVec, hXpm, hXp, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  have hEX : ∀ (j : ℕ) (x : Fin n → K), Y *ᵥ x = ζ ^ j • x →
      ∃ w : Fin n → K, Y *ᵥ w = w ∧ x = X ^ j *ᵥ w := by
    intro j
    induction j with
    | zero => intro x hx; exact ⟨x, by simpa using hx, by simp⟩
    | succ j ih =>
      intro x hx
      have hζpow : ζ ^ (p - 1) * ζ ^ (j + 1) = ζ ^ j := by
        rw [← pow_add]
        have : p - 1 + (j + 1) = j + p := by have := hp.pos; omega
        rw [this, pow_add, hζp, mul_one]
      have hYx' : Y *ᵥ (α⁻¹ • (X ^ (p - 1) *ᵥ x)) = ζ ^ j • (α⁻¹ • (X ^ (p - 1) *ᵥ x)) := by
        rw [mulVec_smul, hYpow (p - 1) x (ζ ^ (j + 1)) hx, hζpow, smul_comm]
      obtain ⟨w, hw, hxw⟩ := ih _ hYx'
      refine ⟨w, hw, ?_⟩
      calc x = X *ᵥ (α⁻¹ • (X ^ (p - 1) *ᵥ x)) := (hXinv x).symm
        _ = X ^ (j + 1) *ᵥ w := by rw [hxw, mulVec_mulVec, ← pow_succ']
  let fr : Fin p → Fin m → Fin n → K := fun k r => (X ^ (k : ℕ)) *ᵥ ε r
  have hval : ∀ k : Fin p, ((k + 1 : Fin p) : ℕ) = if (k : ℕ) + 1 = p then 0 else (k : ℕ) + 1 := by
    intro k
    have hp1 : 1 < p := hp.one_lt
    have hk := k.isLt
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hp1]
    split_ifs with hkp
    · rw [hkp, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  have hfr_succ : ∀ (k : Fin p) (r : Fin m),
      X *ᵥ fr k r = (if (k : ℕ) + 1 = p then α else 1) • fr (k + 1) r := by
    intro k r
    simp only [fr]
    rw [hval k]
    split_ifs with hkp
    · rw [mulVec_mulVec, ← pow_succ', hkp, hXp, pow_zero, one_mulVec]
    · rw [one_smul, mulVec_mulVec, ← pow_succ']
  have hYfr : ∀ k r, Y *ᵥ fr k r = ζ ^ (k : ℕ) • fr k r := fun k r => by
    simp only [fr]
    rw [hYpow (k : ℕ) (ε r) 1 (by rw [hYε, one_smul]), mul_one]
  have hfmem : ∀ k r, fr k r ∈ E k := fun k r => (hmem k _).mpr (hYfr k r)
  have hXiter : ∀ (k : ℕ) (u v : Fin n → K),
      herm σ ((X ^ k) *ᵥ u) ((X ^ k) *ᵥ v) = herm σ u v := by
    intro k
    induction k with
    | zero => intro u v; simp
    | succ k ih =>
      intro u v
      rw [pow_succ', ← mulVec_mulVec, ← mulVec_mulVec, hXu, ih]
  have hfon : ∀ k r l s, herm σ (fr k r) (fr l s) = if k = l ∧ r = s then 1 else 0 := by
    intro k r l s
    by_cases hkl : k = l
    · subst hkl
      have h1 : herm σ (fr k r) (fr k s) = herm σ (ε r) (ε s) := hXiter (k : ℕ) _ _
      rw [h1, hεon]
      simp
    · rw [hV_orth k l hkl _ (hfmem k r) _ (hfmem l s)]
      simp [hkl]
  have hexp : ∀ w : Fin n → K, Y *ᵥ w = w → ∃ c : Fin m → K, w = ∑ r, c r • ε r :=
    fun w hw => by
      have hw0 : w ∈ E 0 := (hmem 0 w).mpr (by simpa using hw)
      refine ⟨fun r => b.repr ⟨w, hw0⟩ r, ?_⟩
      have h1 : (∑ r, b.repr ⟨w, hw0⟩ r • b r : E 0) = ⟨w, hw0⟩ := b.sum_repr ⟨w, hw0⟩
      have h2 := congrArg Subtype.val h1
      rw [Submodule.coe_sum] at h2
      simp only [Submodule.coe_smul] at h2
      exact h2.symm
  have hspan : ∀ v : Fin n → K, ∃ c : Fin p → Fin m → K, v = ∑ k, ∑ r, c k r • fr k r := by
    intro v
    have hv : v ∈ ⨆ j, E j := by rw [hsup]; exact Submodule.mem_top
    refine Submodule.iSup_induction E
      (motive := fun v => ∃ c : Fin p → Fin m → K, v = ∑ k, ∑ r, c k r • fr k r) hv ?_
      ⟨0, by simp⟩ ?_
    · intro j x hx
      obtain ⟨w, hw, rfl⟩ := hEX (j : ℕ) x ((hmem j x).mp hx)
      obtain ⟨c, rfl⟩ := hexp w hw
      refine ⟨fun k r => if k = j then c r else 0, ?_⟩
      beta_reduce
      rw [Finset.sum_eq_single j]
      · simp [fr, mulVec_sum, mulVec_smul]
      · intro k _ hk
        simp [hk]
      · intro h'
        exact absurd (Finset.mem_univ j) h'
    · rintro x y ⟨c, rfl⟩ ⟨c', rfl⟩
      exact ⟨c + c', by simp [add_smul, Finset.sum_add_distrib]⟩
  exact ⟨m, ⟨{ f := fr, on := hfon, span := hspan, hY := hYfr, hX := hfr_succ }⟩⟩

end Existence

end CFSG.LieType.SeitzGeneration.HeisP
