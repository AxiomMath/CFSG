module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux1

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


variable {K L : Type} [Field K] [Field L]

@[expose] def Fv (Fr : L →+* L) (c : Fn L) : Fn L := fun ν => Fr (c ν)

@[expose] def ιFn (ι : K →+* L) (c : Fn K) : Fn L := fun ν => ι (c ν)

@[expose] def Frob (Fr : L →+* L) : ModGL Tag.E8 L →* ModGL Tag.E8 L :=
  Units.map (entrywiseHom Fr)

theorem Frob_pinnedX (Fr : L →+* L) (β : Fin Tag.E8.rank → ℤ) (c : L) :
    Frob Fr (pinnedX Tag.E8 L β c) = pinnedX Tag.E8 L β (Fr c) :=
  Units.ext (entrywise_pinnedX Fr β c)

theorem Fv_add (Fr : L →+* L) (c c' : Fn L) : Fv Fr (c + c') = Fv Fr c + Fv Fr c' := by
  funext ν
  simp [Fv]

theorem Fv_neg (Fr : L →+* L) (c : Fn L) : Fv Fr (-c) = -Fv Fr c := by
  funext ν
  simp [Fv]

theorem Fv_zero (Fr : L →+* L) : Fv Fr (0 : Fn L) = 0 := by
  funext ν
  simp [Fv]

theorem Fv_single (Fr : L →+* L) (μ : Fin Tag.E8.rank → ℤ) (c : L) :
    Fv Fr (Pi.single μ c : Fn L) = Pi.single μ (Fr c) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [Fv]
  · simp [Fv, Pi.single_eq_of_ne h]

theorem ιFn_add (ι : K →+* L) (c c' : Fn K) : ιFn ι (c + c') = ιFn ι c + ιFn ι c' := by
  funext ν
  simp [ιFn]

theorem ιFn_neg (ι : K →+* L) (c : Fn K) : ιFn ι (-c) = -ιFn ι c := by
  funext ν
  simp [ιFn]

theorem ιFn_zero (ι : K →+* L) : ιFn ι (0 : Fn K) = 0 := by
  funext ν
  simp [ιFn]

theorem ιFn_single (ι : K →+* L) (μ : Fin Tag.E8.rank → ℤ) (c : K) :
    ιFn ι (Pi.single μ c : Fn K) = Pi.single μ (ι c) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [ιFn]
  · simp [ιFn, Pi.single_eq_of_ne h]

theorem ιFn_injective (ι : K →+* L) : Function.Injective (ιFn ι) := by
  intro c c' h
  funext ν
  exact ι.injective (congrFun h ν)

@[expose] def frobGood (Fr : L →+* L) : Subgroup (ModGL Tag.E8 L) where
  carrier := {q | q ∈ Qθ Tag.E8 L ∧ Frob Fr q ∈ Qθ Tag.E8 L ∧
    heisCoord Tag.E8 L (Frob Fr q) = Fv Fr (heisCoord Tag.E8 L q)}
  mul_mem' := by
    rintro q q' ⟨hq, hcq, hqe⟩ ⟨hq', hcq', hq'e⟩
    refine ⟨mul_mem hq hq', ?_, ?_⟩
    · rw [map_mul]
      exact mul_mem hcq hcq'
    · rw [map_mul, (heisCoord_spec Tag.E8 L).mul _ hcq _ hcq', hqe, hq'e,
        (heisCoord_spec Tag.E8 L).mul _ hq _ hq', Fv_add]
  one_mem' := ⟨one_mem _, by rw [map_one]; exact one_mem _, by
    rw [map_one, heisCoord_one, Fv_zero]⟩
  inv_mem' := by
    rintro q ⟨hq, hcq, hqe⟩
    refine ⟨inv_mem hq, ?_, ?_⟩
    · rw [map_inv]
      exact inv_mem hcq
    · rw [map_inv, heisCoord_inv hcq, hqe, heisCoord_inv hq, Fv_neg]

theorem pinnedX_highRoot_mem_Qθ (c : L) : pinnedX Tag.E8 L (highRoot Tag.E8) c ∈ Qθ Tag.E8 L :=
  pinnedX_mem_rootSpan
    (by
      rw [mem_parabolicRadicalRoots_iff]
      refine ⟨isRoot_highRoot _, height_highRoot_pos _, iθ _, fun h => h rfl, ?_⟩
      rw [CoordAux.highRoot_degree]
      omega) c

theorem heisCoord_Frob (Fr : L →+* L) {q : ModGL Tag.E8 L} (hq : q ∈ Qθ Tag.E8 L) :
    Frob Fr q ∈ Qθ Tag.E8 L ∧ heisCoord Tag.E8 L (Frob Fr q) = Fv Fr (heisCoord Tag.E8 L q) := by
  have hle : Qθ Tag.E8 L ≤ frobGood Fr := by
    refine Qθ_le_of_gen (fun β hβ c => ?_) (fun c => ?_)
    · refine ⟨pinnedX_mem_Qθ_of_mem_Deg1 hβ c, ?_, ?_⟩
      · rw [Frob_pinnedX]
        exact pinnedX_mem_Qθ_of_mem_Deg1 hβ _
      · rw [Frob_pinnedX, (heisCoord_spec _ L).pinnedX_deg1 β hβ,
          (heisCoord_spec _ L).pinnedX_deg1 β hβ, Fv_single]
    · refine ⟨pinnedX_highRoot_mem_Qθ c, ?_, ?_⟩
      · rw [Frob_pinnedX]
        exact pinnedX_highRoot_mem_Qθ _
      · rw [Frob_pinnedX, (heisCoord_spec _ L).pinnedX_highRoot,
          (heisCoord_spec _ L).pinnedX_highRoot, Fv_zero]
  exact (hle hq).2

@[expose] def bcGood (ι : K →+* L) : Subgroup (ModGL Tag.E8 K) where
  carrier := {q | q ∈ Qθ Tag.E8 K ∧ baseChangeGL ι q ∈ Qθ Tag.E8 L ∧
    heisCoord Tag.E8 L (baseChangeGL ι q) = ιFn ι (heisCoord Tag.E8 K q)}
  mul_mem' := by
    rintro q q' ⟨hq, hcq, hqe⟩ ⟨hq', hcq', hq'e⟩
    refine ⟨mul_mem hq hq', ?_, ?_⟩
    · rw [map_mul]
      exact mul_mem hcq hcq'
    · rw [map_mul, (heisCoord_spec Tag.E8 L).mul _ hcq _ hcq', hqe, hq'e,
        (heisCoord_spec Tag.E8 K).mul _ hq _ hq', ιFn_add]
  one_mem' := ⟨one_mem _, by rw [map_one]; exact one_mem _, by
    rw [map_one, heisCoord_one, heisCoord_one, ιFn_zero]⟩
  inv_mem' := by
    rintro q ⟨hq, hcq, hqe⟩
    refine ⟨inv_mem hq, ?_, ?_⟩
    · rw [map_inv]
      exact inv_mem hcq
    · rw [map_inv, heisCoord_inv hcq, hqe, heisCoord_inv hq, ιFn_neg]

theorem heisCoord_baseChange (ι : K →+* L) {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K) :
    baseChangeGL ι q ∈ Qθ Tag.E8 L ∧
      heisCoord Tag.E8 L (baseChangeGL ι q) = ιFn ι (heisCoord Tag.E8 K q) := by
  have hle : Qθ Tag.E8 K ≤ bcGood ι := by
    refine Qθ_le_of_gen (fun β hβ c => ?_) (fun c => ?_)
    · refine ⟨pinnedX_mem_Qθ_of_mem_Deg1 hβ c, ?_, ?_⟩
      · rw [baseChangeGL_pinnedX]
        exact pinnedX_mem_Qθ_of_mem_Deg1 hβ _
      · rw [baseChangeGL_pinnedX, (heisCoord_spec _ L).pinnedX_deg1 β hβ,
          (heisCoord_spec _ K).pinnedX_deg1 β hβ, ιFn_single]
    · refine ⟨pinnedX_highRoot_mem_Qθ c, ?_, ?_⟩
      · rw [baseChangeGL_pinnedX]
        exact pinnedX_highRoot_mem_Qθ _
      · rw [baseChangeGL_pinnedX, (heisCoord_spec _ L).pinnedX_highRoot,
          (heisCoord_spec _ K).pinnedX_highRoot, ιFn_zero]
  exact (hle hq).2

theorem Frob_baseChangeGL (ι : K →+* L) (Fr : L →+* L) (hfix : ∀ a : K, Fr (ι a) = ι a)
    (g : ModGL Tag.E8 K) : Frob Fr (baseChangeGL ι g) = baseChangeGL ι g := by
  have hcomp : Fr.comp ι = ι := RingHom.ext hfix
  have e : Frob Fr (baseChangeGL ι g) = baseChangeGL Fr (baseChangeGL ι g) := Units.ext rfl
  rw [e, baseChangeGL_baseChangeGL, hcomp]

@[expose] def sgn (w : WeylGroup Tag.E8) (μ : Fin Tag.E8.rank → ℤ) : L :=
  open Classical in
  if h : IsRoot Tag.E8 μ then (exists_canonicalRep_mul_pinnedX_mul_inv L w h).choose else 1

theorem sgn_spec (w : WeylGroup Tag.E8) {μ : Fin Tag.E8.rank → ℤ} (h : IsRoot Tag.E8 μ) :
    sgn (L := L) w μ * sgn (L := L) w μ = 1 ∧ ∀ c : L,
      canonicalRep (coxeterSystem Tag.E8) L w * pinnedX Tag.E8 L μ c *
          (canonicalRep (coxeterSystem Tag.E8) L w)⁻¹ = pinnedX Tag.E8 L (w • μ) (sgn w μ * c) := by
  simp only [sgn, dif_pos h]
  exact (exists_canonicalRep_mul_pinnedX_mul_inv L w h).choose_spec

@[expose] def Mg (w : WeylGroup Tag.E8) (sg : (Fin Tag.E8.rank → ℤ) → L) : Fn L →ₗ[L] Fn L where
  toFun c := fun ν => sg (w⁻¹ • ν) * c (w⁻¹ • ν)
  map_add' c c' := by
    funext ν
    simp only [Pi.add_apply]
    ring
  map_smul' t c := by
    funext ν
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem Mg_apply (w : WeylGroup Tag.E8) (sg : (Fin Tag.E8.rank → ℤ) → L) (c : Fn L)
    (ν : Fin Tag.E8.rank → ℤ) : Mg w sg c ν = sg (w⁻¹ • ν) * c (w⁻¹ • ν) := rfl

theorem Mg_single (w : WeylGroup Tag.E8) (sg : (Fin Tag.E8.rank → ℤ) → L)
    (μ : Fin Tag.E8.rank → ℤ) (c : L) :
    Mg w sg (Pi.single μ c : Fn L) = Pi.single (w • μ) (sg μ * c) := by
  funext ν
  rw [Mg_apply]
  by_cases h : ν = w • μ
  · subst h
    simp
  · have h' : w⁻¹ • ν ≠ μ := fun e => h (by rw [← e, smul_inv_smul])
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
    simp

@[expose] def Mono (n : ModGL Tag.E8 L) (w : WeylGroup Tag.E8)
    (sg : (Fin Tag.E8.rank → ℤ) → L) : Prop :=
  ∀ β, IsRoot Tag.E8 β → sg β * sg β = 1 ∧
    ∀ c : L, n * pinnedX Tag.E8 L β c * n⁻¹ = pinnedX Tag.E8 L (w • β) (sg β * c)

theorem actsBy_mono {n : ModGL Tag.E8 L} {w : WeylGroup Tag.E8}
    {sg : (Fin Tag.E8.rank → ℤ) → L} (hm : Mono n w sg)
    (hθ : w • highRoot Tag.E8 = highRoot Tag.E8)
    (hD : ∀ μ ∈ Deg1 Tag.E8, w • μ ∈ Deg1 Tag.E8) : ActsBy n (Mg w sg) := by
  rw [actsBy_iff_le]
  refine Qθ_le_of_gen (fun β hβ c => ?_) (fun c => ?_)
  · obtain ⟨-, hc⟩ := hm β hβ.1
    refine ⟨pinnedX_mem_Qθ_of_mem_Deg1 hβ c, ?_, ?_⟩
    · rw [hc c]
      exact pinnedX_mem_Qθ_of_mem_Deg1 (hD β hβ) _
    · rw [hc c, (heisCoord_spec _ L).pinnedX_deg1 (w • β) (hD β hβ),
        (heisCoord_spec _ L).pinnedX_deg1 β hβ, Mg_single]
  · obtain ⟨-, hc⟩ := hm _ (isRoot_highRoot Tag.E8)
    rw [hθ] at hc
    refine ⟨pinnedX_highRoot_mem_Qθ c, ?_, ?_⟩
    · rw [hc c]
      exact pinnedX_highRoot_mem_Qθ _
    · rw [hc c, (heisCoord_spec _ L).pinnedX_highRoot, (heisCoord_spec _ L).pinnedX_highRoot,
        map_zero]

theorem mono_canonicalRep (w : WeylGroup Tag.E8) :
    Mono (canonicalRep (coxeterSystem Tag.E8) L w) w (sgn w) := fun β hβ => sgn_spec w hβ

theorem sigma_fixed_coords (ι : K →+* L) (Fr : L →+* L) (hfix : ∀ a : K, Fr (ι a) = ι a)
    {g n : ModGL Tag.E8 L} (hlang : Frob Fr g = g * n) {M : Fn L →ₗ[L] Fn L} (hn : ActsBy n M)
    (q₀ : ModGL Tag.E8 K) (hy : g⁻¹ * baseChangeGL ι q₀ * g ∈ Qθ Tag.E8 L) :
    M (Fv Fr (heisCoord Tag.E8 L (g⁻¹ * baseChangeGL ι q₀ * g))) =
      heisCoord Tag.E8 L (g⁻¹ * baseChangeGL ι q₀ * g) := by
  set y := g⁻¹ * baseChangeGL ι q₀ * g with hydef
  have hF : Frob Fr y = n⁻¹ * y * n := by
    rw [hydef, map_mul, map_mul, map_inv, hlang, Frob_baseChangeGL ι Fr hfix]
    group
  obtain ⟨hFy, hFc⟩ := heisCoord_Frob Fr hy
  rw [← hFc]
  obtain ⟨-, hc⟩ := hn (Frob Fr y) hFy
  rw [← hc, hF]
  congr 1
  group

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
