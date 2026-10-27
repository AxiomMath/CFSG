module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.QuasithinUnique.B113Lie.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.Open

theorem charTwo_of_core {G : Type*} [Group G] [Finite G] {P R : Subgroup G} (hRP : R ≤ P)
    (hN : P ≤ Subgroup.normalizer (R : Set G)) (h2 : IsPGroup 2 R)
    (hC : P ⊓ Subgroup.centralizer (R : Set G) ≤ R) : CharTwo P := by
  have hR : R ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRP hN h2
  intro x hx
  obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxR : x ∈ P ⊓ Subgroup.centralizer (R : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hxP, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro y hy
    exact hxC y (hR hy)
  exact hR (hC hxR)

section Radical

variable {n : ℕ} {K : Type} [Field K]

@[expose] def radical (n : ℕ) (K : Type) [Field K] (d : ℕ) :
    Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | (∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ flagSpace n K d) ∧
    ∀ v ∈ flagSpace n K d, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  one_mem' := by
    refine ⟨fun v => ?_, fun v _ => ?_⟩
    · simp
    · simp
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      have h1 := hg1 ((h : Matrix (Fin n) (Fin n) K) *ᵥ v)
      have h2 := hh1 v
      have : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ v) - v =
          ((g : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ v) -
            (h : Matrix (Fin n) (Fin n) K) *ᵥ v) + ((h : Matrix (Fin n) (Fin n) K) *ᵥ v - v) := by
        abel
      rw [this]
      exact add_mem h1 h2
    · simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hh2 v hv, hg2 v hv]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hinv : ∀ w, ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec]
    have hinv' : ∀ w, (g : Matrix (Fin n) (Fin n) K) *ᵥ
        (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have := hg1 (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
      rw [hinv'] at this
      have h3 : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v - v =
          -(v - ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
        abel
      rw [h3]
      exact neg_mem this
    · have := hinv v
      rw [hg2 v hv] at this
      exact this

theorem radical_le_stabilizer (d : ℕ) : radical n K d ≤ stabilizer (flagSpace n K d) := by
  rintro g ⟨hg1, hg2⟩
  rw [mem_stabilizer]
  refine le_antisymm ?_ fun v hv => ⟨v, hv, (hg2 v hv)⟩
  rintro _ ⟨v, hv, rfl⟩
  rw [mulVecLin_apply, hg2 v hv]
  exact hv

theorem stabilizer_mulVec_mem {d : ℕ} {q : SpecialLinearGroup (Fin n) K}
    (hq : q ∈ stabilizer (flagSpace n K d)) {v : Fin n → K} (hv : v ∈ flagSpace n K d) :
    (q : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ flagSpace n K d := by
  have : (q : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
      (flagSpace n K d).map (mulVecLin (q : Matrix (Fin n) (Fin n) K)) := ⟨v, hv, rfl⟩
  rwa [mem_stabilizer.mp hq] at this

theorem radical_conj_mem {d : ℕ} {q : SpecialLinearGroup (Fin n) K}
    (hq : q ∈ stabilizer (flagSpace n K d)) {r : SpecialLinearGroup (Fin n) K}
    (hr : r ∈ radical n K d) : q * r * q⁻¹ ∈ radical n K d := by
  obtain ⟨hr1, hr2⟩ := hr
  have hq' : q⁻¹ ∈ stabilizer (flagSpace n K d) := inv_mem hq
  have hqq : ∀ w, (q : Matrix (Fin n) (Fin n) K) *ᵥ
      (((q⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hqq' : ∀ w, ((q⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((q : Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec]
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    set w := ((q⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v with hw
    have h1 := hr1 w
    have h2 : (q : Matrix (Fin n) (Fin n) K) *ᵥ ((r : Matrix (Fin n) (Fin n) K) *ᵥ w) - v =
        (q : Matrix (Fin n) (Fin n) K) *ᵥ ((r : Matrix (Fin n) (Fin n) K) *ᵥ w - w) := by
      rw [Matrix.mulVec_sub, hw, hqq]
    rw [h2]
    exact stabilizer_mulVec_mem hq h1
  · simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    have h1 : ((q⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
        flagSpace n K d := stabilizer_mulVec_mem hq' hv
    rw [hr2 _ h1, hqq]

theorem matrix_eq_of_mulVec {M N : Matrix (Fin n) (Fin n) K}
    (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem radical_sq [CharP K 2] {d : ℕ} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ radical n K d) : g * g = 1 := by
  obtain ⟨hg1, hg2⟩ := hg
  apply Subtype.ext
  change (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1
  apply matrix_eq_of_mulVec
  intro v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have h2 := hg2 _ (hg1 v)
  rw [Matrix.mulVec_sub] at h2
  have h3 : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) - v =
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ v - v) + ((g : Matrix (Fin n) (Fin n) K) *ᵥ v - v) := by
    nth_rewrite 2 [← h2]
    abel
  have h4 : ((g : Matrix (Fin n) (Fin n) K) *ᵥ v - v) + ((g : Matrix (Fin n) (Fin n) K) *ᵥ v - v) =
      0 := by
    ext k
    simp [CharTwo.add_self_eq_zero]
  rw [h4] at h3
  exact sub_eq_zero.1 h3

theorem radical_isPGroup [CharP K 2] (d : ℕ) : IsPGroup 2 (radical n K d) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have := radical_sq g.2
  simpa [pow_two] using this

theorem one_add_single_mulVec (i j : Fin n) (c : K) (v : Fin n → K) :
    (1 + Matrix.single i j c) *ᵥ v = v + Pi.single i (c * v j) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

theorem transvection_mem_radical {d : ℕ} {i j : Fin n} (hi : (i : ℕ) < d) (hj : d ≤ (j : ℕ)) :
    Matrix.SpecialLinearGroup.transvection
      (show i ≠ j from fun h => by rw [h] at hi; omega) (1 : K) ∈ radical n K d := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [Matrix.SpecialLinearGroup.transvection_coe, one_add_single_mulVec, add_sub_cancel_left]
    rw [mem_flagSpace]
    intro k hk
    have hki : k ≠ i := fun h => by rw [h] at hk; omega
    simp [hki]
  · rw [Matrix.SpecialLinearGroup.transvection_coe, one_add_single_mulVec, mem_flagSpace.1 hv j hj]
    simp

theorem entries_of_commute {G : Matrix (Fin n) (Fin n) K} {i j : Fin n}
    (h : G * (1 + Matrix.single i j (1 : K)) = (1 + Matrix.single i j (1 : K)) * G) :
    (∀ k, G k i = if k = i then G j j else 0) ∧ (∀ l, G j l = if l = j then G i i else 0) := by
  rw [mul_add, add_mul, mul_one, one_mul] at h
  have h' := add_left_cancel h
  refine ⟨fun k => ?_, fun l => ?_⟩
  · have h2 := congrFun (congrFun h' k) j
    rw [Matrix.mul_single_apply_same (1 : K) i j k G] at h2
    by_cases hk : k = i
    · rw [hk] at h2 ⊢
      rw [Matrix.single_mul_apply_same (1 : K) i j j G] at h2
      simpa using h2
    · rw [Matrix.single_mul_apply_of_ne (1 : K) i j k j hk G] at h2
      simpa [hk] using h2
  · have h2 := congrFun (congrFun h' i) l
    rw [Matrix.single_mul_apply_same (1 : K) i j l G] at h2
    by_cases hl : l = j
    · rw [hl] at h2 ⊢
      rw [Matrix.mul_single_apply_same (1 : K) i j i G] at h2
      simpa using h2.symm
    · rw [Matrix.mul_single_apply_of_ne (1 : K) i j i l hl G] at h2
      simpa [hl] using h2.symm

theorem vec_facts_of_shape {d : ℕ} {G : Matrix (Fin n) (Fin n) K} {lam : K}
    (hcol : ∀ k l : Fin n, (l : ℕ) < d → G k l = if k = l then lam else 0)
    (hrow : ∀ k l : Fin n, d ≤ (k : ℕ) → G k l = if l = k then lam else 0)
    (hdiag : ∀ k : Fin n, G k k = lam) :
    (∀ v, G *ᵥ v - lam • v ∈ flagSpace n K d) ∧
      ∀ v ∈ flagSpace n K d, G *ᵥ v = lam • v := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [mem_flagSpace]
    intro k hk
    simp only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · rw [hdiag k, sub_self]
    · intro l _ hlk
      rw [hrow k l hk]
      simp [hlk]
    · simp
  · ext k
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · rw [hdiag k]
    · intro l _ hlk
      by_cases hl : (l : ℕ) < d
      · rw [hcol k l hl]
        simp [Ne.symm hlk]
      · rw [mem_flagSpace.1 hv l (not_lt.1 hl), mul_zero]
    · simp

theorem centralizer_radical {d : ℕ} (hd0 : 0 < d) (hdn : d < n)
    {g : SpecialLinearGroup (Fin n) K}
    (hc : ∀ r ∈ radical n K d, g * r = r * g) :
    ∃ (c : Kˣ) (hc : c ^ n = 1) (r : SpecialLinearGroup (Fin n) K), r ∈ radical n K d ∧
      g = scalarElement c hc * r := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let j₀ : Fin n := ⟨d, hdn⟩
  obtain ⟨G, hGg⟩ : ∃ G : Matrix (Fin n) (Fin n) K, (g : Matrix (Fin n) (Fin n) K) = G :=
    ⟨_, rfl⟩
  have hGdet : G.det = 1 := hGg ▸ g.2
  have hE : ∀ i j : Fin n, (i : ℕ) < d → d ≤ (j : ℕ) →
      (∀ k, G k i = if k = i then G j j else 0) ∧
      (∀ l, G j l = if l = j then G i i else 0) := by
    intro i j hi hj
    have h1 := hc _ (transvection_mem_radical (K := K) hi hj)
    have h2 : (g : Matrix (Fin n) (Fin n) K) * (1 + Matrix.single i j (1 : K)) =
        (1 + Matrix.single i j (1 : K)) * (g : Matrix (Fin n) (Fin n) K) :=
      congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h1
    rw [hGg] at h2
    exact entries_of_commute h2
  set lam : K := G j₀ j₀ with hlam
  have hdiag_lo : ∀ i : Fin n, (i : ℕ) < d → G i i = lam := by
    intro i hi
    have := (hE i j₀ hi (le_refl _)).1 i
    simpa using this
  have hi₀ : (i₀ : ℕ) < d := hd0
  have hcol : ∀ k l : Fin n, (l : ℕ) < d → G k l = if k = l then lam else 0 :=
    fun k l hl => (hE l j₀ hl (le_refl _)).1 k
  have hrow : ∀ k l : Fin n, d ≤ (k : ℕ) → G k l = if l = k then lam else 0 := by
    intro k l hk
    have := (hE i₀ k hi₀ hk).2 l
    rw [this, hdiag_lo i₀ hi₀]
  have hdiag : ∀ k : Fin n, G k k = lam := by
    intro k
    by_cases hk : (k : ℕ) < d
    · exact hdiag_lo k hk
    · have := hrow k k (not_lt.1 hk)
      simpa using this
  have hupper : G.IsUpperTriangular := by
    intro k l hlk
    have hlk' : l < k := hlk
    by_cases hl : (l : ℕ) < d
    · rw [hcol k l hl]
      simp [hlk'.ne']
    · have hk : d ≤ (k : ℕ) := le_trans (not_lt.1 hl) (Fin.lt_def.1 hlk').le
      rw [hrow k l hk]
      simp [hlk'.ne]
  have hdet : G.det = lam ^ n := by
    rw [Matrix.det_of_isUpperTriangular hupper]
    simp [hdiag]
  have hlam_pow : lam ^ n = 1 := hdet.symm.trans hGdet
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : n ≠ 0)] at hlam_pow
    exact zero_ne_one hlam_pow
  set c : Kˣ := Units.mk0 lam hlam0 with hcdef
  have hcn : c ^ n = 1 := Units.ext (by simpa [hcdef] using hlam_pow)
  obtain ⟨hGv, hGF⟩ := vec_facts_of_shape hcol hrow hdiag
  set s : SpecialLinearGroup (Fin n) K := scalarElement c hcn with hs
  have hsvec : ∀ w, (s : Matrix (Fin n) (Fin n) K) *ᵥ w = lam • w := by
    intro w
    rw [hs, coe_scalarElement, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec, one_mulVec]
    rfl
  have hsinv : ∀ w, ((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w =
      lam⁻¹ • w := by
    intro w
    have h1 : (s : Matrix (Fin n) (Fin n) K) *ᵥ (lam⁻¹ • w) = w := by
      rw [hsvec, smul_smul, mul_inv_cancel₀ hlam0, one_smul]
    have h2 := coe_inv_mul_coe s
    calc ((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w
        = ((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            ((s : Matrix (Fin n) (Fin n) K) *ᵥ (lam⁻¹ • w)) := by rw [h1]
      _ = lam⁻¹ • w := by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  refine ⟨c, hcn, s⁻¹ * g, ⟨fun v => ?_, fun v hv => ?_⟩, by rw [mul_inv_cancel_left]⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    rw [hGg, hsinv]
    have : lam⁻¹ • (G *ᵥ v) - v = lam⁻¹ • (G *ᵥ v - lam • v) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (hGv v)
  · simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    rw [hGg, hsinv, hGF v hv, smul_smul, inv_mul_cancel₀ hlam0, one_smul]

theorem scalar_mem_radical {d : ℕ} (hdn : d < n) {s : SpecialLinearGroup (Fin n) K}
    (hs : s ∈ scalars n K) (hr : s ∈ radical n K d) : s = 1 := by
  obtain ⟨c, -, hc⟩ := hs
  have h1 := hr.1 (Pi.single ⟨d, hdn⟩ (1 : K))
  have h2 := mem_flagSpace.1 h1 ⟨d, hdn⟩ (le_refl _)
  rw [hc, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec, one_mulVec] at h2
  simp at h2
  have hc1 : (c : K) = 1 := by
    have := h2
    rw [sub_eq_zero] at this
    exact this
  apply Subtype.ext
  rw [hc, scalar_apply, hc1]
  simp

theorem charTwo_projStabilizer [Finite K] [CharP K 2] {d : ℕ} (hd0 : 0 < d) (hdn : d < n) :
    CharTwo (projStabilizer (flagSpace n K d)) := by
  have : Finite (SpecialLinearGroup (Fin n) K) := inferInstance
  have : Finite (projectiveSL n K) := inferInstance
  refine charTwo_of_core (R := (radical n K d).map (proj n K)) ?_ ?_ ?_ ?_
  · exact Subgroup.map_mono (radical_le_stabilizer d)
  · rintro x ⟨q, hq, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨q * r * q⁻¹, radical_conj_mem hq hr, by simp [map_mul, map_inv]⟩
    · rintro ⟨r, hr, hry⟩
      obtain ⟨y', rfl⟩ := proj_surjective n K y
      refine ⟨q⁻¹ * r * q, ?_, ?_⟩
      · have := radical_conj_mem (inv_mem hq) hr
        simpa using this
      · have h1 : proj n K r = proj n K q * proj n K y' * (proj n K q)⁻¹ := hry
        calc proj n K (q⁻¹ * r * q) = (proj n K q)⁻¹ * proj n K r * proj n K q := by
              simp [map_mul, map_inv]
          _ = proj n K y' := by rw [h1]; group
  · exact (radical_isPGroup d).map (proj n K)
  · rintro x ⟨hxP, hxC⟩
    obtain ⟨g, hgQ, rfl⟩ := hxP
    have hxC' := Subgroup.mem_centralizer_iff.1
      (show proj n K g ∈ Subgroup.centralizer
        (((radical n K d).map (proj n K) : Subgroup (projectiveSL n K)) : Set (projectiveSL n K))
        from hxC)
    have hcomm : ∀ r ∈ radical n K d, g * r = r * g := by
      intro r hr
      have h1 : proj n K r * proj n K g = proj n K g * proj n K r :=
        hxC' (proj n K r) ⟨r, hr, rfl⟩
      have hcommR : g * r * g⁻¹ * r⁻¹ ∈ radical n K d :=
        mul_mem (radical_conj_mem hgQ hr) (inv_mem hr)
      have hsc : g * r * g⁻¹ * r⁻¹ ∈ scalars n K := by
        rw [← proj_eq_one_iff]
        simp only [map_mul, map_inv]
        rw [← h1]
        group
      have h2 := scalar_mem_radical hdn hsc hcommR
      calc g * r = g * r * g⁻¹ * r⁻¹ * (r * g) := by group
        _ = r * g := by rw [h2, one_mul]
    obtain ⟨c, hcn, r, hr, hgr⟩ := centralizer_radical hd0 hdn hcomm
    refine ⟨r, hr, ?_⟩
    rw [hgr, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars c hcn), one_mul]

theorem radical_map_ne_bot {d : ℕ} (hd0 : 0 < d) (hdn : d < n) :
    (radical n K d).map (proj n K) ≠ ⊥ := by
  intro hbot
  obtain ⟨i, hi⟩ : ∃ i : Fin n, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin n, (j : ℕ) = d := ⟨⟨d, hdn⟩, rfl⟩
  have hid : (i : ℕ) < d := by omega
  have hjd : d ≤ (j : ℕ) := by omega
  have hij : i ≠ j := fun h => by rw [h] at hid; omega
  have hTr := transvection_mem_radical (K := K) hid hjd
  have h1 : proj n K (Matrix.SpecialLinearGroup.transvection hij (1 : K)) = 1 := by
    have : proj n K (Matrix.SpecialLinearGroup.transvection hij (1 : K)) ∈
        (radical n K d).map (proj n K) := ⟨_, hTr, rfl⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have h2 := scalar_mem_radical hdn (proj_eq_one_iff.1 h1) hTr
  have h3 := congrArg
    (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K) i j) h2
  have h4 : (1 : Matrix (Fin n) (Fin n) K) i j + Matrix.single i j (1 : K) i j =
      (1 : Matrix (Fin n) (Fin n) K) i j := h3
  rw [Matrix.one_apply_ne hij, Matrix.single_apply_same] at h4
  simp at h4

theorem two_dvd_card_projectiveSL [Finite K] [CharP K 2] (hn : 2 ≤ n) :
    2 ∣ Nat.card (projectiveSL n K) := by
  have h2 := radical_isPGroup (n := n) (K := K) 1
  have hR : IsPGroup 2 ((radical n K 1).map (proj n K)) := h2.map (proj n K)
  have hne := radical_map_ne_bot (K := K) (d := 1) (n := n) one_pos (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hR.card_eq_or_dvd with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
  · exact h.trans (Subgroup.card_subgroup_dvd_card _)

end Radical

end CFSG.QuasithinUnique.B113Lie.Lin
