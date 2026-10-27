module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Roots
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Bruhat
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Gen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Lin
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2RankOne
import CFSG.LieType.Chevalley.Braid
import CFSG.LieType.Chevalley.WeylRootTransport

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

private theorem commute_pinnedX_torusElt_iR {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) (h : 3 ∣ ∑ j, Tag.G2.cartan iR j * γ j)
    (s : K) : Commute (X γ s) (torusElt .G2 K iR ω) := by
  obtain ⟨k, hk⟩ := h
  have hc := commute_torus2_pinnedX (t₁ := 1) (t₂ := ω) hγ
    (by rw [one_zpow, one_mul, hk, zpow_mul, zpow_ofNat, hω3, one_zpow]) s
  rw [torusElt_one, one_mul] at hc
  exact hc.symm


private theorem conj_torusElt_iR_mem_Qg {ω : Kˣ} (hω3 : ω ^ 3 = 1) {g : ModGL .G2 K}
    (hg : g ∈ Qg K) {d : K × K × K × K} (hd : clsT g = vec d) :
    torusElt .G2 K iR ω * g * (torusElt .G2 K iR ω)⁻¹ ∈ Qg K ∧
      clsT (torusElt .G2 K iR ω * g * (torusElt .G2 K iR ω)⁻¹) =
        vec (d.1, (ω : K) ^ 2 * d.2.1, ω * d.2.2.1, d.2.2.2) := by
  have hm3 : ω ^ (-3 : ℤ) = 1 := by rw [zpow_neg, zpow_ofNat, hω3, inv_one]
  have hω3K : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hinv : ((ω⁻¹ : Kˣ) : K) = (ω : K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right (by linear_combination hω3K)
  obtain ⟨e, rfl⟩ := eq_g2QWord_mul_of_clsT hg hd
  have hc := torus_conj_g2QWord 1 ω d e
  simp only [torusElt_one, one_mul, one_pow, inv_one, hm3, hω3, Units.val_one, hinv] at hc
  have hZ := classTwoG2.le (X_mem_Zg (K := K) e)
  rw [hc]
  exact ⟨mul_mem (g2QWord_mem _) hZ, by
    rw [clsT_mul (g2QWord_mem _) hZ, clsT_g2QWord, clsT_Z (X_mem_Zg _), add_zero]⟩

private theorem exists_mem_g2QCoords_of_conj_negA {ω : Kˣ} (hω1 : (ω : K) ≠ 1)
    (hω3 : ω ^ 3 = 1) {H : Subgroup (ModGL .G2 K)} (hXa : ∀ s : K, X gA s ∈ H)
    (hXc : ∀ s : K, X gC s ∈ H) (hda : ∀ ν : Kˣ, torusElt .G2 K iA ν ∈ H) {q : ModGL .G2 K}
    (hq : q ∈ Qg K) {μ : K} (hμ : μ ≠ 0) (h1 : q * X (-gA) μ * q⁻¹ ∈ H)
    (h2 : ¬ Commute (q * X (-gA) μ * q⁻¹) (torusElt .G2 K iR ω)) :
    ∃ w ∈ g2QCoords H, w.2.1 ≠ 0 ∨ w.2.2.1 ≠ 0 := by
  obtain ⟨⟨d₁, d₂, d₃, d₄⟩, hd⟩ := exists_clsT_eq_vec hq
  by_cases hd2 : d₂ = 0
  ·
    refine (h2 ?_).elim
    obtain ⟨e, he⟩ := eq_g2QWord_mul_of_clsT hq hd
    subst hd2
    have hr : X gV d₃ * X gB d₄ ∈ Qg K := mul_mem (X_mem_Qg isQRoot_v _) (X_mem_Qg isQRoot_b _)
    have hc := classTwoG2.central _ hr _ (X_mem_Zg (K := K) e)
    have hq' : q = X gA d₁ * X gC e * (X gV d₃ * X gB d₄) := by
      rw [he]
      simp only [g2QWord, pinnedX_zero .G2 K, mul_one]
      rw [show X gA d₁ * X gV d₃ * X gB d₄ * X gC e = X gA d₁ * (X gV d₃ * X gB d₄ * X gC e) by
        group, hc]
      group
    have hp : Commute (X gA d₁ * X gC e) (torusElt .G2 K iR ω) :=
      (commute_pinnedX_torusElt_iR hω3 isRoot_gA (by decide) d₁).mul_left
        (commute_pinnedX_torusElt_iR hω3 isRoot_gC (by decide) e)
    have hr' : Commute (X (-gA) μ) (X gV d₃ * X gB d₄) :=
      (commute_negA_v μ d₃).mul_right (commute_negA_b μ d₄)
    rw [hq', show X gA d₁ * X gC e * (X gV d₃ * X gB d₄) * X (-gA) μ *
        (X gA d₁ * X gC e * (X gV d₃ * X gB d₄))⁻¹ = X gA d₁ * X gC e *
        (X gV d₃ * X gB d₄ * X (-gA) μ * (X gV d₃ * X gB d₄)⁻¹) * (X gA d₁ * X gC e)⁻¹ by group,
      ← hr'.eq, mul_inv_cancel_right]
    exact (hp.mul_left (commute_pinnedX_torusElt_iR hω3 (IsRoot.neg isRoot_gA) (by decide)
      μ)).mul_left hp.inv_left
  ·
    have h2' : ∀ s : K, q * X gA s * q⁻¹ ∈ H := fun s => by
      obtain ⟨e, he⟩ := exists_conj_eq_mul_pinnedX_gC hq (X_mem_Qg isQRoot_a s)
      rw [he]
      exact H.mul_mem (hXa s) (hXc e)
    have hmem := sub_torus_mem_g2QCoords (t₁ := ω) (t₂ := 1)
      (by rw [torusElt_one, mul_one]; exact hda ω) hq
      (by rw [torusElt_one, mul_one]; exact conj_torusElt_iA_mem hμ h1 h2' ω) hd
    refine ⟨_, hmem, Or.inl ?_⟩
    simp only [Prod.mk_sub_mk, inv_one, mul_one]
    rw [show d₂ - (ω : K) * d₂ = (1 - ω) * d₂ by ring]
    exact mul_ne_zero (sub_ne_zero.2 (Ne.symm hω1)) hd2

theorem adjointGroup_le_of_overgroup_torus (h3 : (3 : K) ≠ 0) {ω : Kˣ}
    (hω : (ω : K) ^ 2 + ω + 1 = 0) {H : Subgroup (ModGL .G2 K)}
    (hC : ∀ g ∈ adjointGroup .G2 K, Commute g (torusElt .G2 K iR ω) → g ∈ H)
    (hn : weylElt .G2 K iR 1 ∈ H) {x : ModGL .G2 K} (hx : x ∈ adjointGroup .G2 K)
    (hxH : x ∈ H) (h1 : ¬ Commute (x * X gC 1 * x⁻¹) (X gC 1))
    (h2 : ¬ Commute (x * X gC 1 * x⁻¹) (torusElt .G2 K iR ω)) : adjointGroup .G2 K ≤ H := by
  have hω3K : (ω : K) ^ 3 = 1 := by linear_combination ((ω : K) - 1) * hω
  have hω3 : ω ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hω3K, Units.val_one])
  have hω1 : (ω : K) ≠ 1 := fun h => h3 (by rw [h] at hω; linear_combination hω)
  have hX : ∀ {γ : Fin Tag.G2.rank → ℤ}, IsRoot .G2 γ → 3 ∣ ∑ j, Tag.G2.cartan iR j * γ j →
      ∀ s : K, X γ s ∈ H := fun hγ h s =>
    hC _ (pinnedX_mem_adjointGroup _ _) (commute_pinnedX_torusElt_iR hω3 hγ h s)
  have hXa : ∀ s : K, X gA s ∈ H := hX isRoot_gA (by decide)
  have hXc : ∀ s : K, X gC s ∈ H := hX isRoot_gC (by decide)
  have hXnc : ∀ s : K, X (-gC) s ∈ H := hX (IsRoot.neg isRoot_gC) (by decide)
  have hz : torusElt .G2 K iR ω ∈ H := hC _ (torusElt_mem_adjointGroup _ _) (Commute.refl _)
  have hda : ∀ ν : Kˣ, torusElt .G2 K iA ν ∈ H := fun ν =>
    hC _ (torusElt_mem_adjointGroup _ _) (torusElt_mul_comm iA iR ν ω)
  have hhc : ∀ ν : Kˣ, torusElt .G2 K iA (ν ^ 2) * torusElt .G2 K iR ν ∈ H := fun ν =>
    H.mul_mem (hda _) (hC _ (torusElt_mem_adjointGroup _ _) (torusElt_mul_comm iR iR ν ω))
  have hzQ : ∀ g ∈ Qg K, torusElt .G2 K iR ω * g * (torusElt .G2 K iR ω)⁻¹ ∈ Qg K :=
    fun g hg => (conj_torusElt_iR_mem_Qg hω3 hg (exists_clsT_eq_vec hg).choose_spec).1
  have hD : ∀ d ∈ g2QCoords H,
      ((d.1, (ω : K) ^ 2 * d.2.1, ω * d.2.2.1, d.2.2.2) : K × K × K × K) ∈ g2QCoords H :=
    fun d hd => map_mem_g2QCoords (M := fun c => (c.1, (ω : K) ^ 2 * c.2.1, ω * c.2.2.1, c.2.2.2))
      hz hzQ (fun g hg c hc => (conj_torusElt_iR_mem_Qg hω3 hg hc).2) hd
  have hN : ∀ d ∈ g2QCoords H, Nmat d ∈ g2QCoords H := fun d hd =>
    map_mem_g2QCoords (M := Nmat) hn nR_normalizes
      (fun g hg c hc => by rw [← cn_clsT hg, hc, cn_vec]) hd
  have ha : ((1, 0, 0, 0) : K × K × K × K) ∈ g2QCoords H :=
    ⟨X gA 1, hXa 1, X_mem_Qg isQRoot_a 1, (vec_E 1).symm⟩
  have hz3 : torusElt .G2 K iR ω ^ 3 = 1 := by
    rw [pow_three, ← torusElt_mul, ← torusElt_mul, ← pow_three, hω3, torusElt_one]
  have hzZ : ∀ c ∈ Zg K, torusElt .G2 K iR ω * c * (torusElt .G2 K iR ω)⁻¹ = c := fun c hc => by
    obtain ⟨e, rfl⟩ := mem_Zg.1 hc
    exact mul_inv_eq_iff_eq_mul.2 (commute_pinnedX_torusElt_iR hω3 isRoot_gC (by decide) e).eq.symm
  have hfix : ∀ q ∈ Qg K, clsT (torusElt .G2 K iR ω * q * (torusElt .G2 K iR ω)⁻¹) = clsT q →
      Commute q (torusElt .G2 K iR ω) := fun q hq h =>
    (mul_inv_eq_iff_eq_mul.1 (conj_eq_self_of_clsT_eq h3 hz3 hzZ hq (hzQ q hq) h)).symm
  obtain ⟨q, hq, κ, hform⟩ := exists_conj_pinnedX_c_forms hx h1
  have hR : ∀ s : K, x * X gC s * x⁻¹ ∈ H := fun s =>
    H.mul_mem (H.mul_mem hxH (hXc s)) (H.inv_mem hxH)
  have hκ : (κ : K) * 1 ≠ 0 := mul_ne_zero κ.ne_zero one_ne_zero
  obtain ⟨w, hwW, hw0⟩ : ∃ w ∈ g2QCoords H, w.2.1 ≠ 0 ∨ w.2.2.1 ≠ 0 := by
    rcases hform with hf | hf | ⟨t, hf⟩
    ·
      obtain ⟨⟨d₁, d₂, d₃, d₄⟩, hd⟩ := exists_clsT_eq_vec hq
      refine ⟨_, mem_g2QCoords_of_conj_negC hω1 hXc hhc hq hκ (by rw [← hf 1]; exact hR 1) hd,
        ?_⟩
      by_contra h0
      push Not at h0
      obtain ⟨rfl, rfl⟩ : d₂ = 0 ∧ d₃ = 0 := h0
      have hqz : Commute q (torusElt .G2 K iR ω) := hfix q hq (by
        rw [(conj_torusElt_iR_mem_Qg hω3 hq hd).2, hd]
        simp only [mul_zero])
      refine h2 ?_
      rw [hf 1]
      exact (hqz.mul_left (commute_pinnedX_torusElt_iR hω3 (IsRoot.neg isRoot_gC) (by decide)
        _)).mul_left hqz.inv_left
    ·
      exact exists_mem_g2QCoords_of_conj_negA hω1 hω3 hXa hXc hda hq hκ
        (by rw [← hf 1]; exact hR 1) (by rw [← hf 1]; exact h2)
    · by_cases ht : t = 0
      ·
        subst ht
        obtain ⟨σ, hσ, hnb⟩ := weylElt_mul_pinnedX_mul_inv K iR (IsRoot.neg isRoot_gB)
        have hrb : reflect .G2 iR (-gB) = -gA := by funext i; fin_cases i <;> rfl
        have e : weylElt .G2 K iR 1 * (x * X gC 1 * x⁻¹) * (weylElt .G2 K iR 1)⁻¹ =
            weylElt .G2 K iR 1 * q * (weylElt .G2 K iR 1)⁻¹ * X (-gA) (σ * ((κ : K) * 1)) *
              (weylElt .G2 K iR 1 * q * (weylElt .G2 K iR 1)⁻¹)⁻¹ := by
          rw [hf 1, pinnedX_zero .G2 K, mul_one, show weylElt .G2 K iR 1 *
              (q * X (-gB) ((κ : K) * 1) * q⁻¹) * (weylElt .G2 K iR 1)⁻¹ =
              weylElt .G2 K iR 1 * q * (weylElt .G2 K iR 1)⁻¹ *
              (weylElt .G2 K iR 1 * X (-gB) ((κ : K) * 1) * (weylElt .G2 K iR 1)⁻¹) *
              (weylElt .G2 K iR 1 * q * (weylElt .G2 K iR 1)⁻¹)⁻¹ by group, hnb, hrb]
        have hnz : weylElt .G2 K iR 1 * torusElt .G2 K iR ω * (weylElt .G2 K iR 1)⁻¹ =
            (torusElt .G2 K iR ω)⁻¹ := by
          rw [weylElt_one_mul_torusElt_mul_inv .G2 K iR iR ω]
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← torusElt_mul, ← torusElt_mul, show Tag.G2.cartan iR iR = 2 by decide,
            show ω * ω ^ (-(2 : ℤ)) * ω = 1 by group, torusElt_one]
        refine exists_mem_g2QCoords_of_conj_negA hω1 hω3 hXa hXc hda (nR_normalizes q hq)
          (mul_ne_zero (left_ne_zero_of_mul_eq_one hσ) hκ)
          (by rw [← e]; exact H.mul_mem (H.mul_mem hn (hR 1)) (H.inv_mem hn))
          (fun hc => h2 ((Commute.conj_iff (weylElt .G2 K iR 1)).1 ?_))
        rw [hnz, e]
        exact hc.inv_right
      ·
        obtain ⟨ε, hε, hmem⟩ := exists_Xmat_mem_g2QCoords_of_conj_negB hq t ((κ : K) * 1)
          (by rw [← hf 1]; exact hR 1) (hXc 1)
        refine ⟨_, hmem, Or.inl ?_⟩
        simp only [Xmat, zero_sub, neg_ne_zero]
        exact mul_ne_zero ht (mul_ne_zero (left_ne_zero_of_mul_eq_one hε) hκ)
  exact adjointGroup_le_of_Qg_le H (Qg_le_of_forall_mem_g2QCoords
    (forall_mem_of_ne_fixedD h3 hω (fun d hd d' hd' => add_mem_g2QCoords hd hd')
      (fun k d hd => smul_mem_g2QCoords hhc k hd) hD hN ha hwW hw0) hXc) hXnc

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max
