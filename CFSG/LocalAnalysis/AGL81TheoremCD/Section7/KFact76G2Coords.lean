module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Roots

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

theorem conj_eq_self_of_inv_mul_conj_mem {G : Type*} [Group G] {Z : Subgroup G} {y g : G}
    (hy3 : y ^ 3 = 1) (hyZ : ∀ c ∈ Z, y * c * y⁻¹ = c) (hZ3 : ∀ c ∈ Z, c ^ 3 = 1 → c = 1)
    (hc : g⁻¹ * (y * g * y⁻¹) ∈ Z) : y * g * y⁻¹ = g := by
  obtain ⟨c, hcZ, h1⟩ : ∃ c ∈ Z, y * g * y⁻¹ = g * c := ⟨_, hc, by group⟩
  have hyc := hyZ c hcZ
  have h2 : y * (g * c) * y⁻¹ = g * c * c := by
    rw [show y * (g * c) * y⁻¹ = (y * g * y⁻¹) * (y * c * y⁻¹) by group, h1, hyc]
  have h3 : y * (g * c * c) * y⁻¹ = g * c * c * c := by
    rw [show y * (g * c * c) * y⁻¹ = (y * (g * c) * y⁻¹) * (y * c * y⁻¹) by group, h2, hyc]
  have hy3' : y * y * y = 1 := by simpa [pow_succ, mul_assoc] using hy3
  have h4 : g * c * c * c = g := by
    rw [← h3, ← h2, ← h1]
    calc y * (y * (y * g * y⁻¹) * y⁻¹) * y⁻¹ = y * y * y * g * (y * y * y)⁻¹ := by group
      _ = g := by rw [hy3', one_mul, inv_one, mul_one]
  have hc3 : c ^ 3 = 1 := by
    rw [pow_succ, pow_two]
    exact mul_left_cancel (a := g) (by rw [mul_one, ← mul_assoc, ← mul_assoc, h4])
  rw [h1, hZ3 c hcZ hc3, mul_one]

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

@[expose] noncomputable def g2QWord (d : K × K × K × K) : ModGL .G2 K :=
  X gA d.1 * X gU d.2.1 * X gV d.2.2.1 * X gB d.2.2.2

theorem torus2_conj_pinnedX (t₁ t₂ : Kˣ) {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) (s : K) :
    torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂ * X γ s *
        (torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂)⁻¹ =
      X γ (((t₁ ^ (∑ j, Tag.G2.cartan iA j * γ j) * t₂ ^ (∑ j, Tag.G2.cartan iR j * γ j) :
        Kˣ) : K) * s) := by
  rw [show torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂ * X γ s *
      (torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂)⁻¹ = torusElt .G2 K iA t₁ *
      (torusElt .G2 K iR t₂ * X γ s * (torusElt .G2 K iR t₂)⁻¹) * (torusElt .G2 K iA t₁)⁻¹ by
    group, root_torus_conjugation iR hγ, root_torus_conjugation iA hγ, ← mul_assoc,
    ← Units.val_mul]

theorem torus_conj_g2QWord (t₁ t₂ : Kˣ) (d : K × K × K × K) (e : K) :
    torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂ * (g2QWord d * X gC e) *
        (torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂)⁻¹ =
      g2QWord (((t₁ ^ 2 * t₂ ^ (-3 : ℤ) : Kˣ) : K) * d.1, ((t₁ * t₂⁻¹ : Kˣ) : K) * d.2.1,
        (t₂ : K) * d.2.2.1, ((t₁⁻¹ * t₂ ^ 3 : Kˣ) : K) * d.2.2.2) * X gC ((t₁ : K) * e) := by
  set h := torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂
  have ea : ∑ j, Tag.G2.cartan iA j * gA j = 2 ∧ ∑ j, Tag.G2.cartan iR j * gA j = -3 := by decide
  have eu : ∑ j, Tag.G2.cartan iA j * gU j = 1 ∧ ∑ j, Tag.G2.cartan iR j * gU j = -1 := by decide
  have ev : ∑ j, Tag.G2.cartan iA j * gV j = 0 ∧ ∑ j, Tag.G2.cartan iR j * gV j = 1 := by decide
  have eb : ∑ j, Tag.G2.cartan iA j * gB j = -1 ∧ ∑ j, Tag.G2.cartan iR j * gB j = 3 := by decide
  have ec : ∑ j, Tag.G2.cartan iA j * gC j = 1 ∧ ∑ j, Tag.G2.cartan iR j * gC j = 0 := by decide
  have ha := torus2_conj_pinnedX t₁ t₂ isRoot_gA d.1
  have hu := torus2_conj_pinnedX t₁ t₂ isRoot_gU d.2.1
  have hv := torus2_conj_pinnedX t₁ t₂ isRoot_gV d.2.2.1
  have hb := torus2_conj_pinnedX t₁ t₂ isRoot_gB d.2.2.2
  have hc := torus2_conj_pinnedX t₁ t₂ isRoot_gC e
  rw [ea.1, ea.2] at ha
  rw [eu.1, eu.2, zpow_one, zpow_neg_one] at hu
  rw [ev.1, ev.2, zpow_zero, one_mul, zpow_one] at hv
  rw [eb.1, eb.2, zpow_neg_one] at hb
  rw [ec.1, ec.2, zpow_zero, mul_one, zpow_one] at hc
  rw [show h * (g2QWord d * X gC e) * h⁻¹ = (h * X gA d.1 * h⁻¹) * (h * X gU d.2.1 * h⁻¹) *
      (h * X gV d.2.2.1 * h⁻¹) * (h * X gB d.2.2.2 * h⁻¹) * (h * X gC e * h⁻¹) by
    simp only [g2QWord]; group, ha, hu, hv, hb, hc, g2QWord]
  norm_cast

theorem g2QWord_mem (d : K × K × K × K) : g2QWord d ∈ Qg K :=
  mul_mem (mul_mem (mul_mem (X_mem_Qg isQRoot_a _) (X_mem_Qg isQRoot_u _))
    (X_mem_Qg isQRoot_v _)) (X_mem_Qg isQRoot_b _)

theorem clsT_g2QWord (d : K × K × K × K) : clsT (g2QWord d) = vec d := by
  have ha := X_mem_Qg (K := K) isQRoot_a d.1
  have hu := X_mem_Qg (K := K) isQRoot_u d.2.1
  have hv := X_mem_Qg (K := K) isQRoot_v d.2.2.1
  have hb := X_mem_Qg (K := K) isQRoot_b d.2.2.2
  rw [g2QWord, clsT_mul (mul_mem (mul_mem ha hu) hv) hb, clsT_mul (mul_mem ha hu) hv,
    clsT_mul ha hu]
  simp only [vec, th_apply]

theorem vec_neg_g2Q (d : K × K × K × K) : vec (-d) = -vec d := by
  rw [← vecHom_apply, map_neg, vecHom_apply]

theorem vec_zero_g2Q : vec (0 : K × K × K × K) = 0 := by
  rw [← vecHom_apply, map_zero]

theorem exists_clsT_eq_vec {g : ModGL .G2 K} (hg : g ∈ Qg K) : ∃ d, clsT g = vec d := by
  have hX : ∀ {γ : Fin Tag.G2.rank → ℤ} (hγ : IsQRoot γ) (c : K), ∃ d, clsT (X γ c) = vec d := by
    intro γ hγ c
    rcases hγ with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(c, 0, 0, 0), by rw [← clsT_g2QWord]; simp [g2QWord, pinnedX_zero .G2 K]⟩
    · exact ⟨(0, c, 0, 0), by rw [← clsT_g2QWord]; simp [g2QWord, pinnedX_zero .G2 K]⟩
    · exact ⟨(0, 0, c, 0), by rw [← clsT_g2QWord]; simp [g2QWord, pinnedX_zero .G2 K]⟩
    · exact ⟨(0, 0, 0, c), by rw [← clsT_g2QWord]; simp [g2QWord, pinnedX_zero .G2 K]⟩
    · exact ⟨0, by rw [clsT_Z (X_mem_Zg c), vec_zero_g2Q]⟩
  unfold Qg at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, c, rfl⟩ := hx
    exact hX hγ c
  | one => exact ⟨0, by rw [clsT_one, vec_zero_g2Q]⟩
  | mul x y hx hy hdx hdy =>
    obtain ⟨d, hd⟩ := hdx
    obtain ⟨d', hd'⟩ := hdy
    exact ⟨d + d', by rw [clsT_mul hx hy, hd, hd', vec_add]⟩
  | inv x hx hdx =>
    obtain ⟨d, hd⟩ := hdx
    exact ⟨-d, by rw [clsT_inv hx, hd, vec_neg_g2Q]⟩

theorem eq_g2QWord_mul_of_clsT {g : ModGL .G2 K} (hg : g ∈ Qg K) {d : K × K × K × K}
    (h : clsT g = vec d) : ∃ e : K, g = g2QWord d * X gC e := by
  obtain ⟨e, he⟩ := mem_Zg.1 ((clsT_eq_iff (g2QWord_mem d) hg).1 ((clsT_g2QWord d).trans h.symm))
  exact ⟨e, by rw [← he]; group⟩

@[expose] def g2QCoords (H : Subgroup (ModGL .G2 K)) : Set (K × K × K × K) :=
  {d | ∃ g ∈ H, g ∈ Qg K ∧ clsT g = vec d}

variable {H : Subgroup (ModGL .G2 K)}

theorem zero_mem_g2QCoords : (0 : K × K × K × K) ∈ g2QCoords H :=
  ⟨1, H.one_mem, (Qg K).one_mem, by rw [clsT_one, vec_zero_g2Q]⟩

theorem add_mem_g2QCoords {d d' : K × K × K × K} (hd : d ∈ g2QCoords H) (hd' : d' ∈ g2QCoords H) :
    d + d' ∈ g2QCoords H := by
  obtain ⟨g, hgH, hgQ, hg⟩ := hd
  obtain ⟨g', hgH', hgQ', hg'⟩ := hd'
  exact ⟨g * g', H.mul_mem hgH hgH', mul_mem hgQ hgQ',
    by rw [clsT_mul hgQ hgQ', hg, hg', vec_add]⟩

theorem Qg_le_of_forall_mem_g2QCoords (hall : ∀ d, d ∈ g2QCoords H) (hZ : ∀ e : K, X gC e ∈ H) :
    Qg K ≤ H := by
  intro g hg
  obtain ⟨d, hd⟩ := exists_clsT_eq_vec hg
  obtain ⟨g', hg'H, hg'Q, hg'⟩ := hall d
  obtain ⟨e, he⟩ := mem_Zg.1 ((clsT_eq_iff hg'Q hg).1 (hg'.trans hd.symm))
  rw [show g = g' * X gC e by rw [← he]; group]
  exact H.mul_mem hg'H (hZ e)

theorem torus_mem_g2QCoords {t₁ t₂ : Kˣ} (hh : torusElt .G2 K iA t₁ * torusElt .G2 K iR t₂ ∈ H)
    {d : K × K × K × K} (hd : d ∈ g2QCoords H) :
    (((t₁ ^ 2 * t₂ ^ (-3 : ℤ) : Kˣ) : K) * d.1, ((t₁ * t₂⁻¹ : Kˣ) : K) * d.2.1,
      (t₂ : K) * d.2.2.1, ((t₁⁻¹ * t₂ ^ 3 : Kˣ) : K) * d.2.2.2) ∈ g2QCoords H := by
  obtain ⟨g, hgH, hgQ, hg⟩ := hd
  obtain ⟨e, rfl⟩ := eq_g2QWord_mul_of_clsT hgQ hg
  have hZQ := classTwoG2.le (X_mem_Zg (K := K) ((t₁ : K) * e))
  refine ⟨_, H.mul_mem (H.mul_mem hh hgH) (H.inv_mem hh), ?_, ?_⟩ <;> rw [torus_conj_g2QWord]
  · exact mul_mem (g2QWord_mem _) hZQ
  · rw [clsT_mul (g2QWord_mem _) hZQ, clsT_g2QWord, clsT_Z (X_mem_Zg _), add_zero]

theorem map_mem_g2QCoords {y : ModGL .G2 K} (hy : y ∈ H) (hyQ : ∀ g ∈ Qg K, y * g * y⁻¹ ∈ Qg K)
    {M : K × K × K × K → K × K × K × K}
    (hM : ∀ g ∈ Qg K, ∀ c, clsT g = vec c → clsT (y * g * y⁻¹) = vec (M c))
    {d : K × K × K × K} (hd : d ∈ g2QCoords H) : M d ∈ g2QCoords H := by
  obtain ⟨g, hgH, hgQ, hg⟩ := hd
  exact ⟨y * g * y⁻¹, H.mul_mem (H.mul_mem hy hgH) (H.inv_mem hy), hyQ g hgQ, hM g hgQ d hg⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max
