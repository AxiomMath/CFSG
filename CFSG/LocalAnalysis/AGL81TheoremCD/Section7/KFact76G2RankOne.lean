module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Coords
import CFSG.LieType.Chevalley.WeylRootTransport
import CFSG.LieType.Chevalley.Braid

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
open scoped commutatorElement

theorem commutatorElement_conj_of_commute {G : Type*} [Group G] {p c : G} (h : Commute p c)
    (g : G) : ⁅p * g * p⁻¹, c⁆ = p * ⁅g, c⁆ * p⁻¹ := by
  rw [conjugate_commutatorElement, h.eq, mul_inv_cancel_right]

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem commute_torus2_pinnedX {t₁ t₂ : Kˣ} {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ)
    (h : t₁ ^ (∑ j, Tag.G2.cartan iA j * γ j) * t₂ ^ (∑ j, Tag.G2.cartan iR j * γ j) = 1)
    (c : K) : Commute (torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂) (X γ c) := by
  have e := torus2_conj_pinnedX t₁ t₂ hγ c
  rw [h, Units.val_one, one_mul] at e
  exact mul_inv_eq_iff_eq_mul.1 e


theorem clsT_conj_of_mem_Qg {q g : ModGL .G2 K} (hq : q ∈ Qg K) (hg : g ∈ Qg K) :
    clsT (q * g * q⁻¹) = clsT g := by
  rw [clsT_mul (mul_mem hq hg) (inv_mem hq), clsT_mul hq hg, clsT_inv hq]
  abel

theorem exists_conj_eq_mul_pinnedX_gC {q g : ModGL .G2 K} (hq : q ∈ Qg K) (hg : g ∈ Qg K) :
    ∃ e : K, q * g * q⁻¹ = g * X gC e := by
  obtain ⟨e, he⟩ := mem_Zg.1 ((clsT_eq_iff hg (mul_mem (mul_mem hq hg) (inv_mem hq))).1
    (clsT_conj_of_mem_Qg hq hg).symm)
  exact ⟨e, by rw [← he]; group⟩

theorem sub_map_mem_g2QCoords {H : Subgroup (ModGL .G2 K)} {y q : ModGL .G2 K} (hy : y ∈ H)
    (hqy : q * y * q⁻¹ ∈ H) (hq : q ∈ Qg K) (hyq : y * q * y⁻¹ ∈ Qg K)
    {d d' : K × K × K × K} (hd : clsT q = vec d) (hd' : clsT (y * q * y⁻¹) = vec d') :
    d - d' ∈ g2QCoords H := by
  refine ⟨q * (y * q * y⁻¹)⁻¹, ?_, mul_mem hq (inv_mem hyq), ?_⟩
  · rw [show q * (y * q * y⁻¹)⁻¹ = q * y * q⁻¹ * y⁻¹ by group]
    exact H.mul_mem hqy (H.inv_mem hy)
  · have hsub : vec (d - d') = vec d - vec d' := map_sub (vecHom K) d d'
    rw [clsT_mul hq (inv_mem hyq), clsT_inv hyq, hd, hd', hsub, sub_eq_add_neg]

theorem sub_torus_mem_g2QCoords {H : Subgroup (ModGL .G2 K)} {t₁ t₂ : Kˣ}
    (hh : torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂ ∈ H) {q : ModGL .G2 K} (hq : q ∈ Qg K)
    (hqh : q * (torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂) * q⁻¹ ∈ H)
    {d : K × K × K × K} (hd : clsT q = vec d) :
    d - (((t₁ ^ 2 * t₂ ^ (-3 : ℤ) : Kˣ) : K) * d.1, ((t₁ * t₂⁻¹ : Kˣ) : K) * d.2.1,
      (t₂ : K) * d.2.2.1, ((t₁⁻¹ * t₂ ^ 3 : Kˣ) : K) * d.2.2.2) ∈ g2QCoords H := by
  obtain ⟨e, he⟩ := eq_g2QWord_mul_of_clsT hq hd
  have hc := torus_conj_g2QWord t₁ t₂ d e
  rw [← he] at hc
  have hZ := classTwoG2.le (X_mem_Zg (K := K) ((t₁ : K) * e))
  refine sub_map_mem_g2QCoords hh hqh hq (by rw [hc]; exact mul_mem (g2QWord_mem _) hZ) hd ?_
  rw [hc, clsT_mul (g2QWord_mem _) hZ, clsT_g2QWord, clsT_Z (X_mem_Zg _), add_zero]

theorem smul_mem_g2QCoords {H : Subgroup (ModGL .G2 K)}
    (hh : ∀ ν : Kˣ, torusElt .G2 K iA (ν ^ 2) * torusElt .G2 K iR ν ∈ H) (k : K)
    {d : K × K × K × K} (hd : d ∈ g2QCoords H) : k • d ∈ g2QCoords H := by
  by_cases hk : k = 0
  · rw [hk, zero_smul]
    exact zero_mem_g2QCoords
  · have := torus_mem_g2QCoords (hh (Units.mk0 k hk)) hd
    rw [show (Units.mk0 k hk ^ 2) ^ 2 * Units.mk0 k hk ^ (-3 : ℤ) = Units.mk0 k hk by group,
      show Units.mk0 k hk ^ 2 * (Units.mk0 k hk)⁻¹ = Units.mk0 k hk by group,
      show (Units.mk0 k hk ^ 2)⁻¹ * Units.mk0 k hk ^ 3 = Units.mk0 k hk by group,
      Units.val_mk0] at this
    exact this

theorem conj_eq_self_of_clsT_eq (h3 : (3 : K) ≠ 0) {y q : ModGL .G2 K} (hy3 : y ^ 3 = 1)
    (hyZ : ∀ c ∈ Zg K, y * c * y⁻¹ = c) (hq : q ∈ Qg K) (hyq : y * q * y⁻¹ ∈ Qg K)
    (h : clsT (y * q * y⁻¹) = clsT q) : y * q * y⁻¹ = q :=
  conj_eq_self_of_inv_mul_conj_mem hy3 hyZ (Z_no_three_torsion h3)
    ((clsT_eq_iff hq hyq).1 h.symm)


theorem conj_pinnedX_negA_mem {H : Subgroup (ModGL .G2 K)} {g : ModGL .G2 K} {μ : K}
    (hμ : μ ≠ 0) (h1 : g * X (-gA) μ * g⁻¹ ∈ H) (h2 : ∀ s : K, g * X gA s * g⁻¹ ∈ H)
    (s : K) : g * X (-gA) s * g⁻¹ ∈ H := by
  have mem : ∀ y : ModGL .G2 K, y ∈ H.comap (MulAut.conj g).toMonoidHom ↔ g * y * g⁻¹ ∈ H :=
    fun y => by rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have ht0 : -μ⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hμ)
  obtain ⟨t, htv⟩ : ∃ t : Kˣ, (t : K) = -μ⁻¹ := ⟨Units.mk0 _ ht0, rfl⟩
  have hn : weylElt .G2 K iA t ∈ H.comap (MulAut.conj g).toMonoidHom := by
    have ht : -((t⁻¹ : Kˣ) : K) = μ := by
      rw [Units.val_inv_eq_inv_val, htv, inv_neg, inv_inv, neg_neg]
    rw [weylElt_eq_xUnit_mul, xUnit_iA, yUnit_iA, ht]
    exact mul_mem (mul_mem ((mem _).2 (h2 _)) ((mem _).2 h1)) ((mem _).2 (h2 _))
  obtain ⟨ε, hε, hconj⟩ := weylElt_mul_pinnedX_mul_inv K iA isRoot_gA
  have hr : reflect .G2 iA gA = -gA := by funext i; fin_cases i <;> rfl
  have e2 : ∑ j, Tag.G2.cartan iA j * (-gA) j = -2 := by decide
  have key : ∀ c : K, weylElt .G2 K iA t * X gA c * (weylElt .G2 K iA t)⁻¹ =
      X (-gA) (((t ^ (-2 : ℤ) : Kˣ) : K) * (ε * c)) := fun c => by
    rw [← torusElt_mul_weylElt_one .G2 K iA t,
      show torusElt .G2 K iA t * weylElt .G2 K iA 1 * X gA c *
          (torusElt .G2 K iA t * weylElt .G2 K iA 1)⁻¹ = torusElt .G2 K iA t *
          (weylElt .G2 K iA 1 * X gA c * (weylElt .G2 K iA 1)⁻¹) * (torusElt .G2 K iA t)⁻¹ by
        group,
      hconj, hr, root_torus_conjugation iA (IsRoot.neg isRoot_gA), e2]
  have hmem := mul_mem (mul_mem hn ((mem _).2 (h2 (ε * (((t ^ (2 : ℤ) : Kˣ) : K) * s)))))
    (inv_mem hn)
  rw [key] at hmem
  have h22 : ((t ^ (-2 : ℤ) : Kˣ) : K) * ((t ^ (2 : ℤ) : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, ← zpow_add]
    simp
  have hs : ((t ^ (-2 : ℤ) : Kˣ) : K) * (ε * (ε * (((t ^ (2 : ℤ) : Kˣ) : K) * s))) = s := by
    linear_combination (((t ^ (2 : ℤ) : Kˣ) : K) * ((t ^ (-2 : ℤ) : Kˣ) : K) * s) * hε +
      s * h22
  rw [hs] at hmem
  exact (mem _).1 hmem

theorem conj_torusElt_iA_mem {H : Subgroup (ModGL .G2 K)} {g : ModGL .G2 K} {μ : K}
    (hμ : μ ≠ 0) (h1 : g * X (-gA) μ * g⁻¹ ∈ H) (h2 : ∀ s : K, g * X gA s * g⁻¹ ∈ H)
    (ν : Kˣ) : g * torusElt .G2 K iA ν * g⁻¹ ∈ H := by
  have hle : Subgroup.closure (Set.range (X gA) ∪ Set.range (X (-gA))) ≤
      H.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;>
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · exact h2 c
    · exact conj_pinnedX_negA_mem hμ h1 h2 c
  have := hle (torusElt_iA_mem ν)
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem conj_torusElt_c_mem {H : Subgroup (ModGL .G2 K)} {g : ModGL .G2 K} {μ : K}
    (hμ : μ ≠ 0) (h1 : g * X (-gC) μ * g⁻¹ ∈ H) (h2 : ∀ s : K, g * X gC s * g⁻¹ ∈ H)
    (ν : Kˣ) : g * (torusElt .G2 K iA (ν ^ 2) * torusElt .G2 K iR ν) * g⁻¹ ∈ H := by
  obtain ⟨σ₁, hσ₁, k₁⟩ := weylElt_mul_pinnedX_mul_inv K iR (IsRoot.neg isRoot_gA)
  obtain ⟨σ₂, hσ₂, k₂⟩ := weylElt_mul_pinnedX_mul_inv K iA (IsRoot.neg isRoot_gB)
  have r₁ : reflect .G2 iR (-gA) = -gB := by funext i; fin_cases i <;> rfl
  have r₂ : reflect .G2 iA (-gB) = -gC := by funext i; fin_cases i <;> rfl
  have conj : ∀ y : ModGL .G2 K, g * (weylElt .G2 K iA 1 * weylElt .G2 K iR 1) * y *
      (g * (weylElt .G2 K iA 1 * weylElt .G2 K iR 1))⁻¹ = g * (weylElt .G2 K iA 1 *
      (weylElt .G2 K iR 1 * y * (weylElt .G2 K iR 1)⁻¹) * (weylElt .G2 K iA 1)⁻¹) * g⁻¹ :=
    fun y => by group
  have e : σ₂ * (σ₁ * (σ₁ * (σ₂ * μ))) = μ := by
    linear_combination (σ₂ * σ₂ * μ) * hσ₁ + μ * hσ₂
  have h1' : g * (weylElt .G2 K iA 1 * weylElt .G2 K iR 1) * X (-gA) (σ₁ * (σ₂ * μ)) *
      (g * (weylElt .G2 K iA 1 * weylElt .G2 K iR 1))⁻¹ ∈ H := by
    rw [conj, k₁, r₁, k₂, r₂, e]
    exact h1
  have h2' : ∀ s : K, g * (weylElt .G2 K iA 1 * weylElt .G2 K iR 1) * X gA s *
      (g * (weylElt .G2 K iA 1 * weylElt .G2 K iR 1))⁻¹ ∈ H := fun s => by
    rw [conj, nR_a, nA_b]
    exact h2 s
  have hμ' : σ₁ * (σ₂ * μ) ≠ 0 := mul_ne_zero (left_ne_zero_of_mul_eq_one hσ₁)
    (mul_ne_zero (left_ne_zero_of_mul_eq_one hσ₂) hμ)
  have := conj_torusElt_iA_mem hμ' h1' h2' ν
  rwa [show g * (weylElt .G2 K iA 1 * weylElt .G2 K iR 1) * torusElt .G2 K iA ν *
      (g * (weylElt .G2 K iA 1 * weylElt .G2 K iR 1))⁻¹ = g * (weylElt .G2 K iA 1 *
      weylElt .G2 K iR 1 * torusElt .G2 K iA ν * (weylElt .G2 K iA 1 * weylElt .G2 K iR 1)⁻¹) *
      g⁻¹ by group, conj_torusElt_iA] at this

theorem mem_g2QCoords_of_conj_negC {H : Subgroup (ModGL .G2 K)} {t : Kˣ} (ht : (t : K) ≠ 1)
    (hXc : ∀ s : K, X gC s ∈ H)
    (hh : ∀ ν : Kˣ, torusElt .G2 K iA (ν ^ 2) * torusElt .G2 K iR ν ∈ H)
    {q : ModGL .G2 K} (hq : q ∈ Qg K) {μ : K} (hμ : μ ≠ 0) (h1 : q * X (-gC) μ * q⁻¹ ∈ H)
    {d : K × K × K × K} (hd : clsT q = vec d) : d ∈ g2QCoords H := by
  have h2 : ∀ s : K, q * X gC s * q⁻¹ ∈ H := fun s => by
    obtain ⟨e, he⟩ := exists_conj_eq_mul_pinnedX_gC hq (X_mem_Qg isQRoot_c s)
    rw [he]
    exact H.mul_mem (hXc s) (hXc e)
  have hmem := sub_torus_mem_g2QCoords (hh t) hq (conj_torusElt_c_mem hμ h1 h2 t) hd
  rw [show (t ^ 2) ^ 2 * t ^ (-3 : ℤ) = t by group, show t ^ 2 * t⁻¹ = t by group,
    show (t ^ 2)⁻¹ * t ^ 3 = t by group] at hmem
  have h1t : (1 : K) - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have hcancel : ∀ a : K, a = (1 - (t : K))⁻¹ * (a - t * a) := fun a => by
    rw [show a - t * a = (1 - (t : K)) * a by ring, ← mul_assoc, inv_mul_cancel₀ h1t, one_mul]
  convert smul_mem_g2QCoords hh (1 - (t : K))⁻¹ hmem using 1
  obtain ⟨d₁, d₂, d₃, d₄⟩ := d
  simp only [Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
  exact ⟨hcancel d₁, hcancel d₂, hcancel d₃, hcancel d₄⟩

theorem exists_Xmat_mem_g2QCoords_of_conj_negB {H : Subgroup (ModGL .G2 K)} {q : ModGL .G2 K}
    (hq : q ∈ Qg K) (t κ : K) (hR : q * X gR t * X (-gB) κ * (q * X gR t)⁻¹ ∈ H)
    (hc1 : X gC 1 ∈ H) : ∃ ε : K, ε * ε = 1 ∧ Xmat t (ε * κ, 0, 0, 0) ∈ g2QCoords H := by
  obtain ⟨ε, hε, hc⟩ := comm_negB_c (K := K)
  have hqc : Commute q (X gC 1) := classTwoG2.central q hq _ (X_mem_Zg 1)
  have hpc : Commute (q * X gR t) (X gC 1) := hqc.mul_left (commute_r_c t 1)
  have ha := X_mem_Qg (K := K) isQRoot_a (ε * κ)
  have hra := Xr_normalizes t _ ha
  have e : ⁅q * X gR t * X (-gB) κ * (q * X gR t)⁻¹, X gC 1⁆ =
      q * (X gR t * X gA (ε * κ) * (X gR t)⁻¹) * q⁻¹ := by
    rw [commutatorElement_conj_of_commute hpc, hc, mul_one]
    group
  refine ⟨ε, hε, ⁅q * X gR t * X (-gB) κ * (q * X gR t)⁻¹, X gC 1⁆, ?_, ?_, ?_⟩
  · rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hR hc1) (H.inv_mem hR)) (H.inv_mem hc1)
  · rw [e]
    exact mul_mem (mul_mem hq hra) (inv_mem hq)
  · rw [e, clsT_conj_of_mem_Qg hq hra, ← cx_clsT t ha, ← vec_E, cx_vec]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max
