module

public import CFSG.LieType.SeitzGeneration.UnitaryTwoNonCubeBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryNonCube

public section

namespace CFSG.LieType.SeitzGeneration

namespace TwoNonCube

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.SeitzGeneration.UnitaryTwo CFSG.LieType.SeitzGeneration.NonCube

variable {ℓ f n : ℕ} {K : Type} [Field K]

section Core

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem field4_of_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) {ζ : K} (hζ3 : ζ ^ 3 = 1)
    (hζ1 : ζ ≠ 1) : Field4 (unitaryInvolution K ℓ f) ζ := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K ℓ f) :=
    isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hcard4 : Nat.card K = 4 := by
    rw [h.card_eq_sq, hq]
    norm_num
  have hℓ2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1
    (hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega))
  have h2 : (1 : K) + 1 = 0 := by
    have h := CharP.cast_eq_zero K ℓ
    rw [hℓ2] at h
    rw [one_add_one_eq_two]
    exact_mod_cast h
  have hqn : ∀ c : K, c ≠ 0 → unitaryInvolution K ℓ f c * c = 1 := fun c hc => by
    have hc3 : c ^ 3 = 1 := by
      have := Fintype.ofFinite K
      have h := FiniteField.pow_card_sub_one_eq_one c hc
      rwa [← Nat.card_eq_fintype_card, hcard4] at h
    rw [unitaryInvolution_apply, hq]
    linear_combination hc3
  exact ⟨hσ, hqn, h2, hζ3, hζ1⟩

theorem mulVec_mem_sup {x : Matrix (Fin n) (Fin n) K} {S₁ S₂ : Submodule K (Fin n → K)}
    (h₁ : ∀ s ∈ S₁, x *ᵥ s ∈ S₁) (h₂ : ∀ s ∈ S₂, x *ᵥ s ∈ S₂) :
    ∀ s ∈ S₁ ⊔ S₂, x *ᵥ s ∈ S₁ ⊔ S₂ := by
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hs
  rw [mulVec_add]
  exact Submodule.add_mem_sup (h₁ a ha) (h₂ b hb)

theorem eq_top_of_noncube_pair_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2)
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
  have hK : Field4 σ₀ ζ := field4_of_two h hq hζ3 hζ1
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
  have hgood : ∀ j, V j ≠ ⊥ → GoodBlock σ₀ (V j) := fun j hj =>
    goodBlock_of_sep h (V j) (hnd j) (hdim j hj)
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
  have hstab' : ∀ j, ∀ s ∈ V j, xm *ᵥ s ∈ V j := fun j s hs => by
    have := hstab j s hs
    rwa [hxT, Matrix.toLin'_apply] at this
  have hVeig : ∀ j, ∀ v ∈ V j, ym *ᵥ v = lam j • v := fun j v hv => by
    have := (hmemV j v).mp hv
    rwa [hyT, Matrix.toLin'_apply] at this
  have hVorth : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j, herm σ₀ u v = 0 := by
    intro i j hij u hu v hv
    rw [← Nonsplit.idForm_eq_herm h]
    exact hV_orth i j hij u hu v hv
  have hAll : ∀ j, Centers.AllCenters H (V j) := by
    intro j v hv hvi
    have hl : σ₀ (lam j) * lam j = 1 := by rw [hσb]; exact hnorm j
    exact isCenter_of_eigen_matrix hσ.invol hHy hyU hvi hl (hVeig j v hv)
  have mixing : ∀ (S₁ S₂ : Submodule K (Fin n → K)), (∀ s ∈ S₁, xm *ᵥ s ∈ S₁) →
      (∀ s ∈ S₂, xm *ᵥ s ∈ S₂) → Disjoint S₁ S₂ → (∀ s ∈ S₁, ∀ t ∈ S₂, herm σ₀ s t = 0) →
      (B.domRestrict₁₂ S₁ S₁).SeparatingLeft → (B.domRestrict₁₂ S₂ S₂).SeparatingLeft →
      (∀ w ∈ S₂, w ≠ 0 → ∃ w₀ ∈ S₂, herm σ₀ w₀ w₀ = 0 ∧ herm σ₀ w w₀ ≠ 0) →
      Centers.AllCenters H S₂ →
      S₁ ≠ ⊥ → S₂ ≠ ⊥ → ∃ a ∈ S₁, ∃ b ∈ S₂, a ≠ 0 ∧ b ≠ 0 ∧ Centers.IsCenter H (a + b) := by
    intro S₁ S₂ hS₁ hS₂ hdisj horth hnd₁ hnd₂ hKI hS₂A hne₁ hne₂
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne₁
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne₂
    obtain ⟨g, hgx, w₀, hw₀, hw₀0, hw₀i, u'', hu'', w'', hw'', hu''0, hw''0, hgw⟩ :=
      exists_mixing_of_noncube h hx hx3 hcx hS₁ hS₂ hdisj horth hnd₁ hnd₂ hKI hu hu0 hw hw0
    have hgH : g ∈ H := hHx g hgx
    have hC : Centers.IsCenter H w₀ := hS₂A w₀ hw₀ hw₀i
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
  have hmix₀ := mixing (V i₀) (V j₀) (hstab' i₀) (hstab' j₀) (hVdisj i₀ j₀ hij₀)
    (hVorth i₀ j₀ hij₀) (hnd i₀) (hnd j₀)
    (fun w hw hw0 => exists_isotropic_pairing_of_ON hσ (hgood j₀ hj₀).1 hw hw0) (hAll j₀) hi₀ hj₀
  have hA2 := allCenters_sup_two hK hyU hHy (hVorth i₀ j₀ hij₀)
    (by rw [hσb]; exact hnorm i₀) (by rw [hσb]; exact hnorm j₀) (hVeig i₀) (hVeig j₀)
    (hgood i₀ hi₀) (hgood j₀ hj₀) hmix₀
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i₀ ∧ k ≠ j₀ := by
    have : ∀ a b : Fin 3, a ≠ b → ∃ k : Fin 3, k ≠ a ∧ k ≠ b := by decide
    exact this i₀ j₀ hij₀
  have hcover : ∀ j : Fin 3, j = i₀ ∨ j = j₀ ∨ j = k := by
    have : ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b → ∀ j : Fin 3, j = a ∨ j = b ∨ j = c := by
      decide
    exact this i₀ j₀ k hij₀ hki hkj
  by_cases hk : V k = ⊥
  · have htop : V i₀ ⊔ V j₀ = ⊤ := by
      rw [eq_top_iff, ← hsup]
      refine iSup_le fun j => ?_
      rcases hcover j with rfl | rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
      · rw [hk]
        exact bot_le
    have hA := hA2.1
    rw [htop] at hA
    exact Centers.eq_top_of_forall_isCenter hσ (by omega) (fun h3 => by omega) fun a ha =>
      hA a Submodule.mem_top ha
  · have hWstab : ∀ s ∈ V i₀ ⊔ V j₀, xm *ᵥ s ∈ V i₀ ⊔ V j₀ :=
      mulVec_mem_sup (hstab' i₀) (hstab' j₀)
    have hWorth : ∀ s ∈ V i₀ ⊔ V j₀, ∀ t ∈ V k, herm σ₀ s t = 0 := by
      intro s hs t ht
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hs
      rw [herm_add_left, hVorth i₀ k (Ne.symm hki) a ha t ht,
        hVorth j₀ k (Ne.symm hkj) b hb t ht, add_zero]
    have hWnd : (B.domRestrict₁₂ (V i₀ ⊔ V j₀) (V i₀ ⊔ V j₀)).SeparatingLeft :=
      Nonsplit.separatingLeft_sup hBsymm (hnd i₀) (hnd j₀) (fun u hu v hv =>
        hV_orth i₀ j₀ hij₀ u hu v hv)
    have hWdisj : Disjoint (V i₀ ⊔ V j₀) (V k) := by
      rw [Submodule.disjoint_def]
      intro v hvW hvk
      have h0 := hnd k ⟨v, hvk⟩ (fun t => by
        rw [LinearMap.domRestrict₁₂_apply]
        show B v (t : Fin n → K) = 0
        rw [hBdef, Nonsplit.idForm_eq_herm h]
        exact hWorth v hvW t t.2)
      simpa using congrArg Subtype.val h0
    have hWne : V i₀ ⊔ V j₀ ≠ ⊥ := ne_bot_of_le_ne_bot hi₀ le_sup_left
    have hmix₁ := mixing (V i₀ ⊔ V j₀) (V k) hWstab (hstab' k) hWdisj hWorth hWnd (hnd k)
      (fun w hw hw0 => exists_isotropic_pairing_of_ON hσ (hgood k hk).1 hw hw0) (hAll k) hWne hk
    have hA1 := allCenters_sup_one hK hyU hHy hWorth hA2.2 hA2.1 (lc := lam k)
      (by rw [hσb]; exact hnorm k) (hVeig k) (hgood k hk) hmix₁
    have htop : (V i₀ ⊔ V j₀) ⊔ V k = ⊤ := by
      rw [eq_top_iff, ← hsup]
      refine iSup_le fun j => ?_
      rcases hcover j with rfl | rfl | rfl
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    have hA := hA1.1
    rw [htop] at hA
    exact Centers.eq_top_of_forall_isCenter hσ (by omega) (fun h3 => by omega) fun a ha =>
      hA a Submodule.mem_top ha

end Core

end TwoNonCube

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits NonCube

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem closure_planeFixUn_abelian_noncube_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2)
    {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) (hxy : x * y = y * x) {α β : K}
    (hβ : β ≠ 0)
    (hx3 : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hy3 : ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1)
    (hy1 : ∀ c : K, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1)
    (hcx : ¬ ∃ μ : K, μ ^ 3 = α) (hcy : ∃ ν : K, ν ^ 3 = β) (hn : 1 ≤ n) :
    Subgroup.closure (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K)) = ⊤ := by
  classical
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hq3 : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  obtain ⟨ν, hν⟩ := hcy
  have hν0 : ν ≠ 0 := by rintro rfl; exact hβ (by rw [← hν]; norm_num)
  have hβN : β ^ (ℓ ^ f + 1) = 1 := by
    have := bar_mul_eq_one_of_pow_three h hn hy hy3
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
    TwoNonCube.eq_top_of_noncube_pair_two h hq hx hy hxy hx3 hcx hy3' hν0 hνN hζ3 hζ1 hζN hy1
      hHx hHy
  rw [eq_top_iff]
  intro u _
  have hu : ε.symm u ∈ H := hH ▸ Subgroup.mem_top _
  simpa [H] using hu

end CFSG.LieType.SeitzGeneration
