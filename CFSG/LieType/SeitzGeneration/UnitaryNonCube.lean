module

public import CFSG.LieType.SeitzGeneration.UnitaryAbelianGen
public import CFSG.LieType.SeitzGeneration.UnitaryNonCubeMixing
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryToral
public import CFSG.LieType.SeitzGeneration.UnitaryTwoStep
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.LieType.SeitzGeneration

namespace NonCube

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {ℓ f n : ℕ} {K : Type} [Field K]

section Core

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem eq_top_of_noncube_pair (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2)
    {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) (hxy : x * y = y * x) {α ν ζ : K}
    (hx3 : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hcx : ¬ ∃ μ : K, μ ^ 3 = α)
    (hy3 : ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ν ^ 3) • 1)
    (hν0 : ν ≠ 0) (hνN : h.bar ν * ν = 1)
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (hζN : h.bar ζ * ζ = 1)
    (hy1 : ∀ c : K, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (hHx : ∀ g : SUid (unitaryInvolution K ℓ f) n,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
        (x : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → g ∈ H)
    (hHy : ∀ g : SUid (unitaryInvolution K ℓ f) n,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K) =
        (y : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
        g ∈ H) :
    H = ⊤ := by
  classical
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  set B := idForm h n with hBdef
  have hBsymm : B.IsSymm := idForm_isSymm h n
  have hζ : ζ ^ 2 + ζ + 1 = 0 := by
    have : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hζ1)
  set xm : Matrix (Fin n) (Fin n) K := (x : Matrix (Fin n) (Fin n) K) with hxm
  set ym : Matrix (Fin n) (Fin n) K := (y : Matrix (Fin n) (Fin n) K) with hym
  have hxB : ∀ u v, B (Matrix.toLin' xm u) (Matrix.toLin' xm v) = B u v := fun u v =>
    mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff x).mpr hx) u v
  have hyB : ∀ u v, B (Matrix.toLin' ym u) (Matrix.toLin' ym v) = B u v := fun u v =>
    mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff y).mpr hy) u v
  have hyU : ∀ u w, herm σ₀ (ym *ᵥ u) (ym *ᵥ w) = herm σ₀ u w := fun u w => by
    have := hyB u w
    rw [hBdef, Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h] at this
    simpa [Matrix.toLin'_apply] using this
  set xT : Module.End K (Fin n → K) := Matrix.toLin' xm with hxT
  set yT : Module.End K (Fin n → K) := Matrix.toLin' ym with hyT
  have hxT3 : xT ^ 3 = algebraMap K (Module.End K (Fin n → K)) α := by
    have h1 : xm ^ 3 = α • 1 := by rw [hxm, ← Units.val_pow_eq_pow_val]; exact hx3
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_smul, map_one] at h2
    rw [hxT, Algebra.algebraMap_eq_smul_one]
    exact h2
  have hyT3 : yT ^ 3 = algebraMap K (Module.End K (Fin n → K)) (ν ^ 3) := by
    have h1 : ym ^ 3 = (ν ^ 3) • 1 := by rw [hym, ← Units.val_pow_eq_pow_val]; exact hy3
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_smul, map_one] at h2
    rw [hyT, Algebra.algebraMap_eq_smul_one]
    exact h2
  have hcomm : xT * yT = yT * xT := by
    have h1 : Matrix.toLin' (xm * ym) = Matrix.toLin' (ym * xm) := by
      rw [hxm, hym, ← Units.val_mul, ← Units.val_mul, hxy]
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at h1
    exact h1
  let lam : Fin 3 → K := fun j => ν * ζ ^ (j : ℕ)
  let V : Fin 3 → Submodule K (Fin n → K) := fun j => Module.End.eigenspace yT (lam j)
  have hsup : ⨆ j, V j = ⊤ := iSup_eigenspace_eq_top hζ hζ1 hν0 hyT3
  have hmemV : ∀ j v, v ∈ V j ↔ yT v = lam j • v := fun j v => Module.End.mem_eigenspace_iff
  have hstab : ∀ j, ∀ s ∈ V j, xT s ∈ V j := by
    intro j s hs
    rw [hmemV] at hs ⊢
    have h1 := congrArg (fun T : Module.End K (Fin n → K) => T s) hcomm
    simp only [Module.End.mul_apply] at h1
    rw [← h1, hs, map_smul]
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
  have hbζ : h.bar ζ = ζ ^ 2 := by linear_combination (ζ ^ 2) * hζN - (h.bar ζ) * hζ3
  have hlam_ne : ∀ i j : Fin 3, i ≠ j → h.bar (lam i) * lam j ≠ 1 := by
    intro i j hij
    have e : h.bar (lam i) * lam j = ζ ^ (2 * (i : ℕ) + (j : ℕ)) := by
      simp only [lam, map_mul, map_pow]
      rw [hbζ, pow_add, pow_mul]
      linear_combination (ζ ^ (2 * (i : ℕ)) * ζ ^ (j : ℕ)) * hνN
    rw [e]
    refine hζk _ ?_
    have hij' : (i : ℕ) ≠ (j : ℕ) := fun h' => hij (Fin.ext h')
    have hi := i.2
    have hj := j.2
    omega
  have hV_orth : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j, B u v = 0 := by
    intro i j hij u hu v hv
    exact eigen_orthogonal hyB (hlam_ne i j hij) ((hmemV i u).mp hu)
      ((hmemV j v).mp hv)
  have hnd : ∀ j, (B.domRestrict₁₂ (V j) (V j)).SeparatingLeft := fun j =>
    separatingLeft_of_orth_iSup (idForm_separatingLeft h n) V hV_orth hsup j
  have hdim : ∀ j, V j ≠ ⊥ → 3 ≤ Module.finrank K (V j) := fun j hj =>
    three_le_finrank_of_stable hxT3 hcx (hstab j) hj
  have hdimOK : ∀ j, V j ≠ ⊥ → (4 ≤ Module.finrank K (V j) ∨
      (3 ≤ Module.finrank K (V j) ∧ ∃ s : K, s ≠ 0 ∧ σ₀ s * s ≠ 1)) := by
    intro j hj
    right
    refine ⟨hdim j hj, ?_⟩
    obtain ⟨s, hs0, hs⟩ := Nonsplit.exists_norm_ne_one h hq
    exact ⟨s, hs0, by rw [hσb]; exact hs⟩
  have hON : ∀ j, V j ≠ ⊥ → Centers.HasONBasis σ₀ (V j) := fun j hj =>
    Nonsplit.hasONBasis_of_separatingLeft h (V j) (hnd j) (hdimOK j hj)
  have hnorm : ∀ j : Fin 3, h.bar (lam j) * lam j = 1 := by
    intro j
    simp only [lam, map_mul, map_pow]
    have : h.bar ζ ^ (j : ℕ) * ζ ^ (j : ℕ) = 1 := by rw [← mul_pow, hζN, one_pow]
    linear_combination (h.bar ζ ^ (j : ℕ) * ζ ^ (j : ℕ)) * hνN + this
  have hVdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    rw [Submodule.disjoint_def]
    intro v hvi hvj
    have h1 := (hmemV i v).mp hvi
    have h2 := (hmemV j v).mp hvj
    have h3 : (lam i - lam j) • v = 0 := by rw [sub_smul, ← h1, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exfalso
      apply hlam_ne i j hij
      rw [sub_eq_zero.mp h4]
      exact hnorm j
    · exact h4
  have hfour : ∃ i j : Fin 3, i ≠ j ∧ V i ≠ ⊥ ∧ V j ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hj₀ : ∃ j₀ : Fin 3, ∀ j, j ≠ j₀ → V j = ⊥ := by
      by_cases h0 : V 0 = ⊥
      · by_cases h1 : V 1 = ⊥
        · refine ⟨2, fun j hj => ?_⟩
          fin_cases j
          · exact h0
          · exact h1
          · exact absurd rfl hj
        · refine ⟨1, fun j hj => ?_⟩
          fin_cases j
          · exact h0
          · exact absurd rfl hj
          · exact hcon 1 2 (by decide) h1
      · refine ⟨0, fun j hj => ?_⟩
        fin_cases j
        · exact absurd rfl hj
        · exact hcon 0 1 (by decide) h0
        · exact hcon 0 2 (by decide) h0
    obtain ⟨j₀, hj₀⟩ := hj₀
    have hall : ∀ v, yT v = lam j₀ • v := by
      intro v
      have hv : v ∈ ⨆ j, V j := by rw [hsup]; exact Submodule.mem_top
      have hle : (⨆ j, V j) ≤ V j₀ := iSup_le fun j => by
        by_cases hj : j = j₀
        · rw [hj]
        · rw [hj₀ j hj]; exact bot_le
      exact (hmemV j₀ v).mp (hle hv)
    apply hy1 (lam j₀)
    refine Matrix.ext_of_mulVec_single fun i => ?_
    have := hall (Pi.single i 1)
    rw [hyT, Matrix.toLin'_apply] at this
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    exact this
  obtain ⟨i₀, j₀, hij₀, hi₀, hj₀⟩ := hfour
  let W : {j : Fin 3 // V j ≠ ⊥} → Submodule K (Fin n → K) := fun i => V i.1
  have hAll : ∀ j, Centers.AllCenters H (V j) := by
    intro j v hv hvi
    have hyv : ym *ᵥ v = lam j • v := by
      have := (hmemV j v).mp hv
      rwa [hyT, Matrix.toLin'_apply] at this
    have hl : σ₀ (lam j) * lam j = 1 := by rw [hσb]; exact hnorm j
    exact isCenter_of_eigen_matrix hσ.invol hHy hyU hvi hl hyv
  have hWorth : ∀ i j : {j : Fin 3 // V j ≠ ⊥}, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j,
      herm σ₀ u v = 0 := by
    intro i j hij u hu v hv
    have hne : i.1 ≠ j.1 := fun h' => hij (Subtype.ext h')
    rw [← Nonsplit.idForm_eq_herm h]
    exact hV_orth i.1 j.1 hne u hu v hv
  have hWtop : ⨆ i : {j : Fin 3 // V j ≠ ⊥}, W i = ⊤ := by
    rw [eq_top_iff, ← hsup]
    refine iSup_le fun j => ?_
    by_cases hj : V j = ⊥
    · rw [hj]; exact bot_le
    · exact le_iSup_of_le ⟨j, hj⟩ le_rfl
  have hstab' : ∀ j, ∀ s ∈ V j, xm *ᵥ s ∈ V j := fun j s hs => by
    have := hstab j s hs
    rwa [hxT, Matrix.toLin'_apply] at this
  have hmix : ∀ i j : {j : Fin 3 // V j ≠ ⊥}, i ≠ j → ∃ w₁ ∈ W i, ∃ w₂ ∈ W j, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧
      Centers.IsCenter H (w₁ + w₂) := by
    intro i j hij
    have hne : i.1 ≠ j.1 := fun h' => hij (Subtype.ext h')
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot i.2
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot j.2
    have hKI : ∀ w ∈ V j.1, w ≠ 0 → ∃ w₀ ∈ V j.1, herm σ₀ w₀ w₀ = 0 ∧ herm σ₀ w w₀ ≠ 0 :=
      fun w hw hw0 => Nonsplit.exists_isotropic_pairing hσ (hON j.1 j.2) hw hw0
    obtain ⟨g, hgx, w₀, hw₀, hw₀0, hw₀i, u'', hu'', w'', hw'', hu''0, hw''0, hgw⟩ :=
      exists_mixing_of_noncube h hx hx3 hcx (hstab' i.1) (hstab' j.1)
        (hVdisj i.1 j.1 hne) (fun s hs t ht => by
          rw [← Nonsplit.idForm_eq_herm h]; exact hV_orth i.1 j.1 hne s hs t ht)
        (hnd i.1) (hnd j.1) hKI hu hu0 hw hw0
    have hgH : g ∈ H := hHx g hgx
    have hC : Centers.IsCenter H w₀ := hAll j.1 w₀ hw₀ hw₀i
    have hCg := hC.map hgH
    rw [hgw] at hCg
    exact ⟨u'', hu'', w'', hw'', hu''0, hw''0, hCg⟩
  have hn4 : 4 ≤ n := by
    have h1 := hdim i₀ hi₀
    have h2 := hdim j₀ hj₀
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (V i₀) (V j₀)
    rw [(hVdisj i₀ j₀ hij₀).eq_bot, finrank_bot] at h3
    have h4 := Submodule.finrank_le (V i₀ ⊔ V j₀)
    rw [Module.finrank_fin_fun] at h4
    omega
  have : Nonempty {j : Fin 3 // V j ≠ ⊥} := ⟨⟨i₀, hi₀⟩⟩
  exact Centers.eq_top_of_blocks hσ hn4 W (fun i => hON i.1 i.2) hWorth (fun i => hAll i.1) hmix
    hWtop


end Core

theorem bar_mul_eq_one_of_pow_three (h : UnitaryFieldData ℓ f K) {g : GL (Fin n) K} (hn : 1 ≤ n)
    (hg : g ∈ primeFormUnitary h (idGram K n)) {lam : K}
    (hlam : ((g ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = lam • 1) :
    h.bar lam * lam = 1 := by
  have h1 := mem_primeFormUnitary.1 (pow_mem hg 3)
  simp only [idGram, Units.val_one] at h1
  rw [hlam, barTranspose_smul_mul_smul] at h1
  have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  simpa using h2

end NonCube

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits NonCube

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem closure_planeFixUn_abelian_noncube (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) (hn : 3 ≤ n)
    {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) (hxy : x * y = y * x) {α β : K}
    (hβ : β ≠ 0)
    (hx3 : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hy3 : ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1)
    (hy1 : ∀ c : K, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1)
    (hcx : ¬ ∃ μ : K, μ ^ 3 = α) (hcy : ∃ ν : K, ν ^ 3 = β) :
    Subgroup.closure (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K)) = ⊤ := by
  classical
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  obtain ⟨ν, hν⟩ := hcy
  have hν0 : ν ≠ 0 := by rintro rfl; exact hβ (by rw [← hν]; norm_num)
  have hβN : β ^ (ℓ ^ f + 1) = 1 := by
    have := bar_mul_eq_one_of_pow_three h (by omega) hy hy3
    rwa [h.bar_apply, ← pow_succ] at this
  have hνN : h.bar ν * ν = 1 := bar_mul_eq_one_of_cube h hq3 hν0 hν hβN
  obtain ⟨ζ, hζ3, hζ1, hζN⟩ := exists_primitive_cube_root h hq3
  have hy3' : ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ν ^ 3) • 1 := by
    rw [hy3, hν]
  let ε : SUid (unitaryInvolution K ℓ f) n ≃* unitarySU ℓ f K n :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq n)
  let H : Subgroup (SUid (unitaryInvolution K ℓ f) n) :=
    (Subgroup.closure (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K))).comap ε.toMonoidHom
  have hHx : ∀ g : SUid (unitaryInvolution K ℓ f) n,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
        (x : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
        g ∈ H := fun g hg =>
    Subgroup.subset_closure (Or.inl (mem_FixUn_of_mul_comm (g := ε g) hg))
  have hHy : ∀ g : SUid (unitaryInvolution K ℓ f) n,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K) =
        (y : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
        g ∈ H := fun g hg =>
    Subgroup.subset_closure (Or.inr (mem_FixUn_of_mul_comm (g := ε g) hg))
  have hH : H = ⊤ :=
    eq_top_of_noncube_pair h hq hx hy hxy hx3 hcx hy3' hν0 hνN hζ3 hζ1 hζN hy1 hHx hHy
  rw [eq_top_iff]
  intro u _
  have hu : ε.symm u ∈ H := hH ▸ Subgroup.mem_top _
  simpa [H] using hu

end CFSG.LieType.SeitzGeneration
