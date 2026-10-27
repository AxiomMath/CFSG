module

public import CFSG.LieType.SeitzGeneration.UnitaryNonabNonPthMixing
public import CFSG.LieType.SeitzGeneration.UnitaryNonCubeAlgebra
public import CFSG.LieType.SeitzGeneration.UnitaryNonCubeMixing
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.LieType.SeitzGeneration.UnitaryCenters
public import CFSG.LieType.SeitzGeneration.UnitaryHeisTensorCenters
public import CFSG.LieType.SeitzGeneration.HeisTorusIdent
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.UnitaryTwoStep
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.LieType.SeitzGeneration.NonPth

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem exists_primitive_prime_root_bar (h : UnitaryFieldData ℓ f K) (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) : ∃ ζ : K, IsPrimitiveRoot ζ p ∧ h.bar ζ * ζ = 1 := by
  classical
  have hfin := h.finite
  have := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hK : Fintype.card K = ℓ ^ f * ℓ ^ f := by
    rw [← Nat.card_eq_fintype_card, h.card, two_mul, pow_add]
  have hd : p ∣ Nat.card Kˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hK]
    have h1 : ℓ ^ f * ℓ ^ f - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa using this
    rw [h1]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hd
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hgK : (g : K) ^ p = 1 := by
    have := congrArg Units.val hgp
    simpa using this
  refine ⟨(g : K), IsPrimitiveRoot.coe_units_iff.mpr (hg ▸ IsPrimitiveRoot.orderOf g), ?_⟩
  rw [h.bar_apply, ← pow_succ]
  obtain ⟨m, hm⟩ := hpq
  rw [hm, pow_mul, hgK, one_pow]

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem eq_top_of_nonpth_pair (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1) {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) (hxy : x * y = y * x) {α : K}
    (hx3 : ((x ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hcx : ¬ ∃ μ : K, μ ^ p = α)
    (hy3 : ((y ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1)
    (hy1 : ∀ c : K, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) n)}
    (hHx : HeisTensor.Cent H (x : Matrix (Fin n) (Fin n) K))
    (hHy : HeisTensor.Cent H (y : Matrix (Fin n) (Fin n) K)) : H = ⊤ := by
  classical
  obtain ⟨ζ, hζ, hζN⟩ := exists_primitive_prime_root_bar h hp hpq
  have hpK : (p : K) ≠ 0 := heis_natCast_ne_zero hζ hp.two_le
  have hσ : IsUnitaryInvolution σ₀ := Nonsplit.isUnitaryInvolution h
  have hσb : ∀ c, σ₀ c = h.bar c := Nonsplit.unitaryInvolution_eq_bar h
  set B := idForm h n with hBdef
  set xm : Matrix (Fin n) (Fin n) K := (x : Matrix (Fin n) (Fin n) K) with hxm
  set ym : Matrix (Fin n) (Fin n) K := (y : Matrix (Fin n) (Fin n) K) with hym
  have hyB : ∀ u v, B (Matrix.toLin' ym u) (Matrix.toLin' ym v) = B u v := fun u v =>
    mem_sesqUnitaryGroup.mp ((toLin_mem_sesqUnitaryGroup_iff y).mpr hy) u v
  have hyU : ∀ u w, herm σ₀ (ym *ᵥ u) (ym *ᵥ w) = herm σ₀ u w := fun u w => by
    have := hyB u w
    rw [hBdef, Nonsplit.idForm_eq_herm h, Nonsplit.idForm_eq_herm h] at this
    simpa [Matrix.toLin'_apply] using this
  set xT : Module.End K (Fin n → K) := Matrix.toLin' xm with hxT
  set yT : Module.End K (Fin n → K) := Matrix.toLin' ym with hyT
  have hxT3 : xT ^ p = algebraMap K (Module.End K (Fin n → K)) α := by
    have h1 : xm ^ p = α • 1 := by rw [hxm, ← Units.val_pow_eq_pow_val]; exact hx3
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_smul, map_one] at h2
    rw [hxT, Algebra.algebraMap_eq_smul_one]
    exact h2
  have hyT3 : yT ^ p = algebraMap K (Module.End K (Fin n → K)) (1 ^ p) := by
    have h1 : ym ^ p = 1 := by rw [hym, ← Units.val_pow_eq_pow_val]; exact hy3
    have h2 := congrArg Matrix.toLinAlgEquiv' h1
    rw [map_pow, map_one] at h2
    rw [one_pow, map_one]
    exact h2
  have hcomm : xT * yT = yT * xT := by
    have h1 : Matrix.toLin' (xm * ym) = Matrix.toLin' (ym * xm) := by
      rw [hxm, hym, ← Units.val_mul, ← Units.val_mul, hxy]
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at h1
    exact h1
  have hsup0 := iSup_eigenspace_eq_top_p hp hpK hζ one_ne_zero hyT3
  simp only [one_mul] at hsup0
  let V : Fin p → Submodule K (Fin n → K) := fun j => Module.End.eigenspace yT (ζ ^ (j : ℕ))
  have hsup : ⨆ j, V j = ⊤ := hsup0
  have hmemV : ∀ j v, v ∈ V j ↔ yT v = ζ ^ (j : ℕ) • v := fun j v =>
    Module.End.mem_eigenspace_iff
  have hstab : ∀ j, ∀ s ∈ V j, xT s ∈ V j := by
    intro j s hs
    rw [hmemV] at hs ⊢
    have h1 := congrArg (fun T : Module.End K (Fin n → K) => T s) hcomm
    simp only [Module.End.mul_apply] at h1
    rw [← h1, hs, map_smul]
  have hbar_pow : ∀ k : ℕ, h.bar (ζ ^ k) * ζ ^ k = 1 := fun k => by
    rw [map_pow, ← mul_pow, hζN, one_pow]
  have hlam_ne : ∀ i j : Fin p, i ≠ j → h.bar (ζ ^ (i : ℕ)) * ζ ^ (j : ℕ) ≠ 1 := by
    intro i j hij he
    have key : ζ ^ (j : ℕ) = ζ ^ (i : ℕ) := by
      linear_combination (-(ζ ^ (j : ℕ))) * hbar_pow i + (ζ ^ (i : ℕ)) * he
    have hji := hζ.pow_inj j.2 i.2 key
    exact hij (Fin.ext hji.symm)
  have hV_orth : ∀ i j : Fin p, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j, B u v = 0 := by
    intro i j hij u hu v hv
    exact NonCube.eigen_orthogonal hyB (hlam_ne i j hij) ((hmemV i u).mp hu)
      ((hmemV j v).mp hv)
  have hnd : ∀ j : Fin p, (B.domRestrict₁₂ (V j) (V j)).SeparatingLeft := fun j =>
    NonCube.separatingLeft_of_orth_iSup (idForm_separatingLeft h n) V hV_orth hsup j
  have hdim : ∀ j, V j ≠ ⊥ → p ≤ Module.finrank K (V j) := fun j hj =>
    p_le_finrank_of_stable hp hxT3 hcx (hstab j) hj
  have hON : ∀ j, V j ≠ ⊥ → Centers.HasONBasis σ₀ (V j) := fun j hj =>
    Nonsplit.hasONBasis_of_separatingLeft h (V j) (hnd j)
      (Or.inl (by have := hdim j hj; omega))
  have hVdisj : ∀ i j : Fin p, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    rw [Submodule.disjoint_def]
    intro v hvi hvj
    have h1 := (hmemV i v).mp hvi
    have h2 := (hmemV j v).mp hvj
    have h3 : (ζ ^ (i : ℕ) - ζ ^ (j : ℕ)) • v = 0 := by
      rw [sub_smul, ← h1, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exfalso
      apply hlam_ne i j hij
      rw [sub_eq_zero.mp h4]
      exact hbar_pow j
    · exact h4
  have hpair : ∃ i j : Fin p, i ≠ j ∧ V i ≠ ⊥ ∧ V j ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hj₀ : ∃ j₀ : Fin p, ∀ j, j ≠ j₀ → V j = ⊥ := by
      by_cases hex : ∃ j₀, V j₀ ≠ ⊥
      · obtain ⟨j₀, hj₀⟩ := hex
        exact ⟨j₀, fun j hj => hcon j₀ j (Ne.symm hj) hj₀⟩
      · push Not at hex
        exact ⟨⟨0, hp.pos⟩, fun j _ => hex j⟩
    obtain ⟨j₀, hj₀⟩ := hj₀
    have hall : ∀ v, yT v = ζ ^ (j₀ : ℕ) • v := by
      intro v
      have hv : v ∈ ⨆ j, V j := by rw [hsup]; exact Submodule.mem_top
      have hle : (⨆ j, V j) ≤ V j₀ := iSup_le fun j => by
        by_cases hj : j = j₀
        · rw [hj]
        · rw [hj₀ j hj]; exact bot_le
      exact (hmemV j₀ v).mp (hle hv)
    apply hy1 (ζ ^ (j₀ : ℕ))
    refine Matrix.ext_of_mulVec_single fun i => ?_
    have := hall (Pi.single i 1)
    rw [hyT, Matrix.toLin'_apply] at this
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    exact this
  obtain ⟨i₀, j₀, hij₀, hi₀, hj₀⟩ := hpair
  let W : {j : Fin p // V j ≠ ⊥} → Submodule K (Fin n → K) := fun i => V i.1
  have hAll : ∀ j, Centers.AllCenters H (V j) := by
    intro j v hv hvi
    have hyv : ym *ᵥ v = ζ ^ (j : ℕ) • v := by
      have := (hmemV j v).mp hv
      rwa [hyT, Matrix.toLin'_apply] at this
    have hl : σ₀ (ζ ^ (j : ℕ)) * ζ ^ (j : ℕ) = 1 := by rw [hσb]; exact hbar_pow j
    exact NonCube.isCenter_of_eigen_matrix hσ.invol hHy hyU hvi hl hyv
  have hWorth : ∀ i j : {j : Fin p // V j ≠ ⊥}, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j,
      herm σ₀ u v = 0 := by
    intro i j hij u hu v hv
    have hne : i.1 ≠ j.1 := fun h' => hij (Subtype.ext h')
    rw [← Nonsplit.idForm_eq_herm h]
    exact hV_orth i.1 j.1 hne u hu v hv
  have hWtop : ⨆ i : {j : Fin p // V j ≠ ⊥}, W i = ⊤ := by
    rw [eq_top_iff, ← hsup]
    refine iSup_le fun j => ?_
    by_cases hj : V j = ⊥
    · rw [hj]; exact bot_le
    · exact le_iSup_of_le ⟨j, hj⟩ le_rfl
  have hstab' : ∀ j, ∀ s ∈ V j, xm *ᵥ s ∈ V j := fun j s hs => by
    have := hstab j s hs
    rwa [hxT, Matrix.toLin'_apply] at this
  have hmix : ∀ i j : {j : Fin p // V j ≠ ⊥}, i ≠ j → ∃ w₁ ∈ W i, ∃ w₂ ∈ W j,
      w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ Centers.IsCenter H (w₁ + w₂) := by
    intro i j hij
    have hne : i.1 ≠ j.1 := fun h' => hij (Subtype.ext h')
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot i.2
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot j.2
    have hKI : ∀ w ∈ V j.1, w ≠ 0 → ∃ w₀ ∈ V j.1, herm σ₀ w₀ w₀ = 0 ∧ herm σ₀ w w₀ ≠ 0 :=
      fun w hw hw0 => Nonsplit.exists_isotropic_pairing hσ (hON j.1 j.2) hw hw0
    obtain ⟨g, hgx, w₀, hw₀, hw₀0, hw₀i, u'', hu'', w'', hw'', hu''0, hw''0, hgw⟩ :=
      exists_mixing_of_nonpth h hp hx hx3 hcx (hstab' i.1) (hstab' j.1)
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
  have : Nonempty {j : Fin p // V j ≠ ⊥} := ⟨⟨i₀, hi₀⟩⟩
  exact Centers.eq_top_of_blocks hσ hn4 W (fun i => hON i.1 i.2) hWorth (fun i => hAll i.1) hmix
    hWtop

end CFSG.LieType.SeitzGeneration.NonPth
