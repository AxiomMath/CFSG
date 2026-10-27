module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Chart
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Struct

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Universal
open scoped MatrixGroups

section Prod

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def TK : Subgroup (twistedGroup σ) where
  carrier := {x | ∃ b : Fin d4.rank → Kˣ, twistedIncl σ x = rootDiagUnit d4 b}
  one_mem' := ⟨1, by rw [map_one, rootDiagUnit_one]⟩
  mul_mem' := by
    rintro x y ⟨b, hb⟩ ⟨c, hc⟩
    exact ⟨b * c, by rw [map_mul, hb, hc, rootDiagUnit_mul]⟩
  inv_mem' := by
    rintro x ⟨b, hb⟩
    exact ⟨b⁻¹, by rw [map_inv, hb, rootDiagUnit_inv]⟩

variable {σ}

theorem mem_TK {x : twistedGroup σ} :
    x ∈ TK σ ↔ ∃ b : Fin d4.rank → Kˣ, twistedIncl σ x = rootDiagUnit d4 b := Iff.rfl

variable (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem TK_conj_slLong {t : twistedGroup σ} (ht : t ∈ TK σ) (A : SL(2, fixedField σ)) :
    ∃ A' : SL(2, fixedField σ), t * slLong σ hσ A * t⁻¹ = slLong σ hσ A' := by
  obtain ⟨b, hb⟩ := ht
  obtain ⟨s, -, hs⟩ := torus_conj_slLong hσ hb
  exact ⟨_, hs A⟩

include hσ in
theorem TK_conj_slB {t : twistedGroup σ} (ht : t ∈ TK σ) (B : SL(2, K)) :
    ∃ B' : SL(2, K), t * slB σ hσ B * t⁻¹ = slB σ hσ B' := by
  obtain ⟨b, hb⟩ := ht
  obtain ⟨s, -, hs⟩ := torus_conj_slB hσ hb
  exact ⟨_, hs B⟩

variable (σ) in
@[expose] def SProd : Subgroup (twistedGroup σ) where
  carrier := {x | ∃ t ∈ TK σ, ∃ (A : SL(2, fixedField σ)) (B : SL(2, K)),
    x = t * slLong σ hσ A * slB σ hσ B}
  one_mem' := ⟨1, one_mem _, 1, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨t₁, ht₁, A₁, B₁, rfl⟩ ⟨t₂, ht₂, A₂, B₂, rfl⟩
    obtain ⟨A₁', hA₁⟩ := TK_conj_slLong hσ (inv_mem ht₂) A₁
    obtain ⟨B₁', hB₁⟩ := TK_conj_slB hσ (inv_mem ht₂) B₁
    refine ⟨t₁ * t₂, mul_mem ht₁ ht₂, A₁' * A₂, B₁' * B₂, ?_⟩
    have e1 : slLong σ hσ A₁ * t₂ = t₂ * slLong σ hσ A₁' := by
      have := hA₁
      rw [inv_inv] at this
      calc slLong σ hσ A₁ * t₂ = t₂ * (t₂⁻¹ * slLong σ hσ A₁ * t₂) := by group
        _ = _ := by rw [this]
    have e2 : slB σ hσ B₁ * t₂ = t₂ * slB σ hσ B₁' := by
      have := hB₁
      rw [inv_inv] at this
      calc slB σ hσ B₁ * t₂ = t₂ * (t₂⁻¹ * slB σ hσ B₁ * t₂) := by group
        _ = _ := by rw [this]
    have hc := slLong_comm_slB hσ
    calc t₁ * slLong σ hσ A₁ * slB σ hσ B₁ * (t₂ * slLong σ hσ A₂ * slB σ hσ B₂)
        = t₁ * (slLong σ hσ A₁ * (slB σ hσ B₁ * t₂)) * slLong σ hσ A₂ * slB σ hσ B₂ := by
          group
      _ = t₁ * (slLong σ hσ A₁ * (t₂ * slB σ hσ B₁')) * slLong σ hσ A₂ * slB σ hσ B₂ := by
          rw [e2]
      _ = t₁ * ((slLong σ hσ A₁ * t₂) * slB σ hσ B₁') * slLong σ hσ A₂ * slB σ hσ B₂ := by
          group
      _ = t₁ * ((t₂ * slLong σ hσ A₁') * slB σ hσ B₁') * slLong σ hσ A₂ * slB σ hσ B₂ := by
          rw [e1]
      _ = t₁ * t₂ * slLong σ hσ A₁' * (slB σ hσ B₁' * slLong σ hσ A₂) * slB σ hσ B₂ := by
          group
      _ = t₁ * t₂ * slLong σ hσ A₁' * (slLong σ hσ A₂ * slB σ hσ B₁') * slB σ hσ B₂ := by
          rw [← hc A₂ B₁']
      _ = t₁ * t₂ * slLong σ hσ (A₁' * A₂) * slB σ hσ (B₁' * B₂) := by
          rw [map_mul, map_mul]; group
  inv_mem' := by
    rintro _ ⟨t, ht, A, B, rfl⟩
    obtain ⟨A', hA'⟩ := TK_conj_slLong hσ ht A⁻¹
    obtain ⟨B', hB'⟩ := TK_conj_slB hσ ht B⁻¹
    refine ⟨t⁻¹, inv_mem ht, A', B', ?_⟩
    have hc := slLong_comm_slB hσ
    calc (t * slLong σ hσ A * slB σ hσ B)⁻¹
        = slB σ hσ B⁻¹ * slLong σ hσ A⁻¹ * t⁻¹ := by simp only [map_inv]; group
      _ = slLong σ hσ A⁻¹ * slB σ hσ B⁻¹ * t⁻¹ := by rw [← hc A⁻¹ B⁻¹]
      _ = t⁻¹ * (t * slLong σ hσ A⁻¹ * t⁻¹) * (t * slB σ hσ B⁻¹ * t⁻¹) := by group
      _ = t⁻¹ * slLong σ hσ A' * slB σ hσ B' := by rw [hA', hB']

end Prod

section Factor

variable {K : Type} [Field K]

theorem mem_of_centralizes_aux_gen (σ : K ≃+* K) (a : Fin d4.rank → Kˣ)
    (S : Subgroup (ModGL d4 K))
    (hX : ∀ β ∈ proj '' psiTD4 a,
      (twistedRootSubgroupD4 σ.toRingHom β).map (adjointGroup d4 K).subtype ≤ S)
    (hclosed : ∀ α ∈ psiTD4 a, ∀ β ∈ psiTD4 a, IsRoot d4 (α + β) → α + β ∈ psiTD4 a)
    (hρ : ∀ α ∈ psiTD4 a, rho α ∈ psiTD4 a)
    (hT : ∀ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom, h ∈ S)
    (hW : ∀ w : WeylGroup d4, weylTwist TwistTag.D4 w = w → w ∈ rootCharStabilizer a →
      canonicalRep (coxeterSystem d4) K w ∈ (twistedIncl σ.toRingHom).range →
        canonicalRep (coxeterSystem d4) K w ∈ S)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤ (twistedIncl σ.toRingHom).range)
    {g : ModGL d4 K} (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hga : g ∈ Subgroup.centralizer ({rootDiagUnit d4 a} : Set (ModGL d4 K))) : g ∈ S := by
  set Γ := twistedFixedGroup TwistTag.D4 K σ.toRingHom with hΓ
  obtain ⟨w, hw1, hwa, h, hh, u, hu, v, hv, hgeq⟩ :=
    graphFixed_toral_centralizer_Bruhat_factors TwistTag.D4 K σ a hg hga
  have hwρ : weylTwist TwistTag.D4 w = w := hw1
  have hhC₀ : h ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := (Subgroup.mem_inf.1 hh).2
  have hXmR : ∀ β ∈ proj '' psiTD4 a,
      (twistedRootSubgroupD4 σ.toRingHom β).map (adjointGroup d4 K).subtype ≤
        (twistedIncl σ.toRingHom).range := by
    rintro β ⟨α, hαΨ, rfl⟩
    exact map_twistedRootSubgroupD4_le_range σ.toRingHom (isRoot_proj hαΨ.2.1)
  have hΨ : rootSpan d4 K (psiTD4 a) ⊓ Γ ≤ S ⊓ (twistedIncl σ.toRingHom).range := by
    refine (rootSpan_inf_twistedFixed_le σ.toRingHom (fun α hα => hα.2) hclosed hρ).trans ?_
    exact le_inf (iSup₂_le fun β hβ => hX β hβ) (iSup₂_le fun β hβ => hXmR β hβ)
  have hsub : rootCharKernel a ∩ inversionSet w ⊆ psiTD4 a :=
    fun α hα => ⟨hα.1, hα.2.1, hα.2.2.1⟩
  have huSR := hΨ hu
  have hvSR := hΨ (Subgroup.mem_inf.2 ⟨rootSpan_mono hsub (Subgroup.mem_inf.1 hv).1,
    (Subgroup.mem_inf.1 hv).2⟩)
  have hnR : canonicalRep (coxeterSystem d4) K w ∈ (twistedIncl σ.toRingHom).range := by
    have e : canonicalRep (coxeterSystem d4) K w = (h * u)⁻¹ * g * v⁻¹ := by rw [hgeq]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (mul_mem (hC₀ hhC₀) huSR.2)) (hC₀ hg)) (inv_mem hvSR.2)
  rw [hgeq]
  exact mul_mem (mul_mem (mul_mem (hT h hh) huSR.1) (hW w hwρ hwa hnR)) hvSR.1

theorem mem_of_centralizes_aux_gen' {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
    (a : Fin d4.rank → Kˣ) (S : Subgroup (ModGL d4 K))
    (hX : ∀ β ∈ proj '' psiTD4 a,
      (twistedRootSubgroupD4 σ β).map (adjointGroup d4 K).subtype ≤ S)
    (hclosed : ∀ α ∈ psiTD4 a, ∀ β ∈ psiTD4 a, IsRoot d4 (α + β) → α + β ∈ psiTD4 a)
    (hρ : ∀ α ∈ psiTD4 a, rho α ∈ psiTD4 a)
    (hT : ∀ h ∈ graphFixedRootTorus TwistTag.D4 K σ, h ∈ S)
    (hW : ∀ w : WeylGroup d4, weylTwist TwistTag.D4 w = w → w ∈ rootCharStabilizer a →
      canonicalRep (coxeterSystem d4) K w ∈ (twistedIncl σ).range →
        canonicalRep (coxeterSystem d4) K w ∈ S)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    {g : ModGL d4 K} (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    (hga : g ∈ Subgroup.centralizer ({rootDiagUnit d4 a} : Set (ModGL d4 K))) : g ∈ S := by
  obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, fun y => ⟨σ (σ y), hσ y⟩⟩, RingHom.ext fun _ => rfl⟩
  exact mem_of_centralizes_aux_gen σ' a S hX hclosed hρ hT hW hC₀ hg hga

end Factor

section WeylReps

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem WSL_eq_td4 : (WSL : SL(2, K)) = uSL 1 * vSL (-1) * uSL 1 := by
  apply SL2_ext <;> simp [coe_uSL, coe_vSL, Matrix.SpecialLinearGroup.coe_mul, WSL,
    Matrix.mul_apply, Fin.sum_univ_two]

include hσ in
theorem slShort_WSL : slShort σ hσ WSL = nHat σ (ng 1) := by
  apply Subtype.ext
  rw [WSL_eq_td4]
  simp only [map_mul, Subgroup.coe_mul]
  rw [uSL_eq_sl2Upper, vSL_eq_sl2Lower, slShort_upper, slShort_lower, nHat_val, nHatE_one_eq]
  simp [map_one, map_neg]

include hσ in
theorem twistedIncl_slB_WSL : twistedIncl σ (slB σ hσ WSL) =
    canonicalRep (coxeterSystem d4) K tdNhat * (weylElt d4 K (nd 0) 1 * weylElt d4 K (nd 1) 1 *
      weylElt d4 K (nd 3) 1) * (canonicalRep (coxeterSystem d4) K tdNhat)⁻¹ := by
  rw [twistedIncl_slB, slShort_WSL hσ]
  congr 2

end WeylReps

section RootGroups

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem psi_long_pos : ∀ α ∈ rootFinset d4, (α (nd 0) + α (nd 1) + α (nd 3)) % 2 = 0 →
    0 < height α → α = Pi.single (nd 2) 1 ∨ α = vd4 0 1 1 1 ∨ α = vd4 1 0 1 1 ∨
      α = vd4 1 1 1 0 := by decide +kernel

theorem proj_gamma3_orbit : ∀ α ∈ ([vd4 0 1 1 1, vd4 1 0 1 1, vd4 1 1 1 0] :
    List (Fin d4.rank → ℤ)), proj α = proj (vd4 0 1 1 1) := by decide +kernel

include hσ in
theorem twistedRootSubgroupD4_gamma3_le :
    (twistedRootSubgroupD4 σ (proj (vd4 0 1 1 1))).map (adjointGroup d4 K).subtype ≤
      ((slB σ hσ).range).map (twistedIncl σ) := by
  rw [map_twistedRootSubgroupD4_eq σ isRoot_gamma3]
  rintro y ⟨hy1, hy2⟩
  have hT := (canonical_weyl_root_transport d4 K).1 tdNhat (td4Orb (Pi.single (nd 0) 1))
    (fun α hα => isRoot_of_mem_td4Orb (isRoot_single d4 (nd 0)) hα)
  rw [image_td4Orb weylTwist_tdNhat, tdNhat_smul_zero] at hT
  rw [← hT] at hy1
  obtain ⟨z, hz, rfl⟩ := hy1
  have hnF : canonicalRep (coxeterSystem d4) K tdNhat ∈ twistedFixedGroup TwistTag.D4 K σ := by
    rw [canonicalRep_tdNhat σ]
    exact twistedIncl_mem_twistedFixedGroup _
  have hzF : z ∈ twistedFixedGroup TwistTag.D4 K σ := by
    have h1 : z = (canonicalRep (coxeterSystem d4) K tdNhat)⁻¹ *
        (MulAut.conj (canonicalRep (coxeterSystem d4) K tdNhat)).toMonoidHom z *
        canonicalRep (coxeterSystem d4) K tdNhat := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h1]
    exact mul_mem (mul_mem (inv_mem hnF) hy2) hnF
  have hzN : z ∈ nodeGroupTD4 σ (Pi.single (nd 0) 1) := Subgroup.mem_sup_left ⟨hz, hzF⟩
  rw [← map_rankOne_short, ModelFacts.rankOne_short_eq_range hσ] at hzN
  obtain ⟨c, ⟨B, rfl⟩, rfl⟩ := hzN
  refine ⟨slB σ hσ B, ⟨B, rfl⟩, ?_⟩
  rw [twistedIncl_slB]
  simp [MulAut.conj_apply]

end RootGroups

section WeylCases

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem SProd_mem_of_TK {t : twistedGroup σ} (ht : t ∈ TK σ) : t ∈ SProd σ hσ :=
  ⟨t, ht, 1, 1, by simp⟩

theorem slLong_mem_SProd (A : SL(2, fixedField σ)) : slLong σ hσ A ∈ SProd σ hσ :=
  ⟨1, one_mem _, A, 1, by simp⟩

theorem slB_mem_SProd (B : SL(2, K)) : slB σ hσ B ∈ SProd σ hσ :=
  ⟨1, one_mem _, 1, B, by simp⟩

include hσ in
theorem torusWeylCosets_slB_WSL : twistedIncl σ (slB σ hσ WSL) ∈ torusWeylCosets d4 K := by
  rw [twistedIncl_slB_WSL hσ]
  exact mul_mem (mul_mem (canonicalRep_mem_torusWeylCosets tdNhat)
    (mul_mem (mul_mem (weylElt_mem_torusWeylCosets _) (weylElt_mem_torusWeylCosets _))
      (weylElt_mem_torusWeylCosets _)))
    (inv_mem (canonicalRep_mem_torusWeylCosets tdNhat))

include hσ in
theorem mapsRootLines_slB_WSL : MapsRootLines (twistedIncl σ (slB σ hσ WSL)) tdWB := by
  rw [twistedIncl_slB_WSL hσ]
  exact ((mapsRootLines_canonicalRep tdNhat).mul (((mapsRootLines_weylElt _).mul
    (mapsRootLines_weylElt _)).mul (mapsRootLines_weylElt _))).mul
    (mapsRootLines_canonicalRep tdNhat).inv

include hσ in
theorem canonicalRep_mem_SProd {w : WeylGroup d4}
    (hw : w = 1 ∨ w = tdWA ∨ w = tdWB ∨ w = tdWA * tdWB)
    (hr : canonicalRep (coxeterSystem d4) K w ∈ (twistedIncl σ).range) :
    canonicalRep (coxeterSystem d4) K w ∈ (SProd σ hσ).map (twistedIncl σ) := by
  set S := (SProd σ hσ).map (twistedIncl σ) with hS
  have hSR : ∀ g ∈ S, g ∈ (twistedIncl σ).range := fun g ⟨x, _, hx⟩ => ⟨x, hx⟩
  have key : ∀ g ∈ torusWeylCosets d4 K, g ∈ S → ∀ w' : WeylGroup d4,
      canonicalRep (coxeterSystem d4) K w' ∈ (twistedIncl σ).range → MapsRootLines g w' →
        canonicalRep (coxeterSystem d4) K w' ∈ S := by
    intro g hg hgS w' hw' hmaps
    obtain ⟨k, hk, hgk⟩ := exists_torus_mul_canonicalRep hg hmaps
    have hkr : k ∈ (twistedIncl σ).range := by
      have : k = g * (canonicalRep (coxeterSystem d4) K w')⁻¹ := by
        rw [hgk]; group
      rw [this]
      exact mul_mem (hSR g hgS) (inv_mem hw')
    obtain ⟨y, rfl⟩ := hkr
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hk
    have hy : y ∈ TK σ := ⟨b, hb⟩
    have : canonicalRep (coxeterSystem d4) K w' = (twistedIncl σ y)⁻¹ * g := by rw [hgk]; group
    rw [this]
    refine mul_mem ?_ hgS
    exact ⟨y⁻¹, SProd_mem_of_TK hσ (inv_mem hy), by rw [map_inv]⟩
  have hn0 : twistedIncl σ (nHat σ (ng 0)) = weylElt d4 K (nd 2) 1 := rfl
  obtain ⟨A₀, hA₀⟩ : nHat σ (ng 0) ∈ (slLong σ hσ).range := by
    rw [← ModelFacts.rankOne_long_eq_range hσ]
    exact nHat_mem_rankOne σ (ng 0)
  have hnS : twistedIncl σ (nHat σ (ng 0)) ∈ S :=
    ⟨nHat σ (ng 0), by rw [← hA₀]; exact slLong_mem_SProd hσ A₀, rfl⟩
  have hBS : twistedIncl σ (slB σ hσ WSL) ∈ S := ⟨slB σ hσ WSL, slB_mem_SProd hσ _, rfl⟩
  have hcos : ∀ i : Fin d4.rank, weylElt d4 K i 1 ∈ torusWeylCosets d4 K := fun i =>
    weylElt_mem_torusWeylCosets i
  have hgB := torusWeylCosets_slB_WSL hσ
  have hmB := mapsRootLines_slB_WSL hσ
  rcases hw with rfl | rfl | rfl | rfl
  · rw [canonicalRep_one]
    exact S.one_mem
  · have : canonicalRep (coxeterSystem d4) K tdWA = twistedIncl σ (nHat σ (ng 0)) := by
      rw [tdWA, canonicalRep_simple]
      rfl
    rw [this]
    exact hnS
  · exact key _ hgB hBS _ hr hmB
  · have hn0cos : twistedIncl σ (nHat σ (ng 0)) ∈ torusWeylCosets d4 K := by
      rw [hn0]
      exact hcos _
    have hn0m : MapsRootLines (twistedIncl σ (nHat σ (ng 0))) tdWA := by
      rw [hn0]
      exact mapsRootLines_weylElt (nd 2)
    exact key _ (mul_mem hn0cos hgB) (S.mul_mem hnS hBS) _ hr (hn0m.mul hmB)

end WeylCases

section Main

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem mem_SProd_of_centralizes (hK : (-1 : Kˣ) ≠ 1)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {x : twistedGroup σ} (hx : x * slLong σ hσ (-1) = slLong σ hσ (-1) * x) :
    x ∈ SProd σ hσ := by
  set S := (SProd σ hσ).map (twistedIncl σ) with hS
  have hga : twistedIncl σ x ∈
      Subgroup.centralizer ({rootDiagUnit d4 (aLongTD4 K)} : Set (ModGL d4 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← twistedIncl_slLong_neg_one hσ, ← map_mul,
      ← map_mul, hx]
  have key : twistedIncl σ x ∈ S := by
    refine mem_of_centralizes_aux_gen' hσ (aLongTD4 K) S ?_ (psi_long_closed hK)
      (psi_long_rho hK) ?_ ?_ hC₀ (hgF x) hga
    · rintro β ⟨α, hα, rfl⟩
      have hpar := (rootChar_aLong_eq_one_iff hK α).1 hα.1.2
      rcases psi_long_pos α (mem_rootFinset.2 hα.2.1) hpar hα.2.2 with h | h | h | h
      · subst h
        rw [map_twistedRootSubgroupD4_eq σ (isRoot_single d4 (nd 2))]
        intro y hy
        have hyN : y ∈ nodeGroupTD4 σ (Pi.single (nd 2) 1) := Subgroup.mem_sup_left hy
        rw [← map_rankOne_long, ModelFacts.rankOne_long_eq_range hσ] at hyN
        obtain ⟨c, ⟨A, rfl⟩, rfl⟩ := hyN
        exact ⟨slLong σ hσ A, slLong_mem_SProd hσ A, rfl⟩
      all_goals
        have hp : proj α = proj (vd4 0 1 1 1) := proj_gamma3_orbit α (by simp [h])
        rw [hp]
        intro y hy
        obtain ⟨c, ⟨B, rfl⟩, rfl⟩ := twistedRootSubgroupD4_gamma3_le hσ hy
        exact ⟨slB σ hσ B, slB_mem_SProd hσ B, rfl⟩
    · intro h hh
      obtain ⟨y, rfl⟩ := hC₀ (Subgroup.mem_inf.1 hh).2
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
      exact ⟨y, SProd_mem_of_TK hσ ⟨b, hb⟩, rfl⟩
    · intro w hwρ hwa hn
      exact canonicalRep_mem_SProd hσ (weyl_long_cases hK hwρ hwa) hn
  obtain ⟨y, hy, hyx⟩ := key
  rw [← twistedIncl_injective σ hyx]
  exact hy

end Main

end CFSG.ClassicalInvolution.G2D4Models
