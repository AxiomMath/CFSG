module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftImages

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization

section Defs

variable {G : Type} [Group G]

structure EvenSL2ImagesOutput (X R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] (r : ℕ)
    (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  model : ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (θ : ↥V ≃* Multiplicative W),
    EvenSL2MaxOutput ((autOn X V).map (binPsi θ).toMonoidHom)
        ((autOn R V).map (binPsi θ).toMonoidHom) ((autOn M V).map (binPsi θ).toMonoidHom) n F r
        (fun i => (Lc i).map (binPsi θ).toMonoidHom) ∧
      EvenSL2ImagesActor ((autOn X V).map (binPsi θ).toMonoidHom)
        ((autOn R V).map (binPsi θ).toMonoidHom)
        ((autOn (thompsonJ R) V).map (binPsi θ).toMonoidHom)
        ((autOn (baum R) V).map (binPsi θ).toMonoidHom) n F r
        (fun i => (Lc i).map (binPsi θ).toMonoidHom)

end Defs

section Tools

variable {G : Type} [Group G] {V : Subgroup G}

theorem autOn_iSup_of_le {ι : Sort*} (Y : ι → Subgroup G)
    (hY : ∀ i, Y i ≤ Subgroup.normalizer (V : Set G)) :
    autOn (⨆ i, Y i) V = ⨆ i, autOn (Y i) V := by
  unfold autOn
  rw [subgroupOf_iSup_of_le _ Y hY, Subgroup.map_iSup]

theorem autOn_eq_bot_of_le_centralizer {A : Subgroup G}
    (hAc : A ≤ Subgroup.centralizer (V : Set G)) : autOn A V = ⊥ :=
  CFSG.Quasithin.AutOn.autOn_eq_bot_of_le_centralizer hAc

theorem autOn_le_normalizer_autOn {X Y : Subgroup G} (_hX : X ≤ Subgroup.normalizer (V : Set G))
    (_hY : Y ≤ Subgroup.normalizer (V : Set G)) (h : X ≤ Subgroup.normalizer (Y : Set G)) :
    autOn X V ≤ Subgroup.normalizer (autOn Y V : Set (MulAut V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn h

theorem map_le_normalizer_map_of_le {A B : Type*} [Group A] [Group B] (f : A ≃* B)
    {X Y : Subgroup A} (h : X ≤ Subgroup.normalizer (Y : Set A)) :
    X.map f.toMonoidHom ≤ Subgroup.normalizer ((Y.map f.toMonoidHom : Subgroup B) : Set B) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.1 (h hx) y).1 hy, by simp⟩
  · rintro ⟨y, hy, hyb⟩
    refine ⟨x⁻¹ * y * x, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (h (X.inv_mem hx)) y).1 hy
      simpa using this
    · have hyb' : f y = f x * b * (f x)⁻¹ := hyb
      show f (x⁻¹ * y * x) = b
      rw [map_mul, map_mul, map_inv, hyb']
      group

theorem thompsonJ_le_baum' (R : Subgroup G) : thompsonJ R ≤ baum R := by
  refine le_inf (B6.thompsonJ_le R) ?_
  rw [Subgroup.le_centralizer_iff]
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  exact hx.1.2

end Tools

section Main

variable {G : Type} [Group G] [Finite G]

theorem even_SL2_original_images
    {X R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    (hS : EvenSL2Setting X R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn X V) r Lc) : EvenSL2ImagesOutput X R M V n F r Lc := by
  classical
  have hred := hS.reduced
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have hX : X ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hRX : R ≤ X := hS.sylow.1
  obtain ⟨hCM, hCR, hXLR, hΛ, hVR⟩ := even_SL2_setting_basic hS
  obtain ⟨A₀, hoff, hFF⟩ := even_SL2_setting_ffcore hS
  obtain ⟨D, hD, ⟨α⟩⟩ := hS.component
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hS.card_eq
  let _ : CommGroup V := commGroupOfElemAbelian hVe
  have hV2 : ∀ v : V, v * v = 1 := fun v => Subtype.ext (by simpa [sq] using hVe.2 v v.2)
  obtain ⟨W, hW1, hW2, hW3, ⟨θ⟩⟩ := exists_binModel_of_binary hV2
  obtain ⟨hmax, hsyl, -⟩ :=
    even_SL2_actor_max_output_of_model θ hFF hS.nonsolvable hS.two_le hF hD α hLc
  have hbridge := even_SL2_original_bridge hS hLc
  refine ⟨⟨W, hW1, hW2, hW3, θ, hmax, ?_⟩⟩
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRX.trans hX
  have hJN : thompsonJ R ≤ Subgroup.normalizer (V : Set G) := (B6.thompsonJ_le R).trans hRN
  have hBN : baum R ≤ Subgroup.normalizer (V : Set G) := (inf_le_left : baum R ≤ R).trans hRN
  let 𝓔 : Set (Subgroup (W ≃ₗ[ZMod 2] W)) :=
    {E | ∃ A : Subgroup G, IsMaxElemAbelian R A ∧ E = (autOn A V).map (binPsi θ).toMonoidHom}
  have hDimg : (⨆ E ∈ 𝓔, E) = (autOn (thompsonJ R) V).map (binPsi θ).toMonoidHom := by
    have hJeq : autOn (thompsonJ R) V =
        ⨆ A : {A : Subgroup G // IsMaxElemAbelian R A}, autOn A.1 V := by
      unfold thompsonJ
      rw [iSup_subtype']
      exact autOn_iSup_of_le _ (fun A => A.2.1.trans hRN)
    rw [hJeq, Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup₂_le fun E hE' => ?_
      obtain ⟨A, hA, rfl⟩ := hE'
      exact le_iSup (fun A : {A : Subgroup G // IsMaxElemAbelian R A} =>
        (autOn A.1 V).map (binPsi θ).toMonoidHom) ⟨A, hA⟩
    · exact iSup_le fun A => le_iSup₂_of_le _ ⟨A.1, A.2, rfl⟩ le_rfl
  have hE : ∀ E ∈ 𝓔, E ≤ (autOn R V).map (binPsi θ).toMonoidHom ∧
      (E = ⊥ ∨ IsOffender ((autOn X V).map (binPsi θ).toMonoidHom) E) := by
    rintro E ⟨A, hA, rfl⟩
    have hAn : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hRN
    refine ⟨Subgroup.map_mono (autOn_le_autOn V hA.1), ?_⟩
    by_cases hAc : A ≤ Subgroup.centralizer (V : Set G)
    · left
      rw [autOn_eq_bot_of_le_centralizer hAc, Subgroup.map_bot]
    · right
      have hne : autOn A V ≠ ⊥ := autOn_ne_bot_of_not_le_centralizer hAn hAc
      refine ⟨Subgroup.map_mono (autOn_le_autOn V (hA.1.trans hRX)), ?_, ?_, ?_⟩
      · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (binPsi θ).injective]
      · exact (isElemAbelian2_iff_map θ _).1 (isElemAbelian2_autOn hVe hA.2.1 hAn)
      · rw [weight_map θ, card_autOn_eq_relIndex hAn, card_fixV_autOn_eq hVe hAn, ← natCard_eq θ]
        exact (hbridge.weight A hA).le
  have hDsubT : (autOn (thompsonJ R) V).map (binPsi θ).toMonoidHom ≤
      (autOn R V).map (binPsi θ).toMonoidHom :=
    Subgroup.map_mono (autOn_le_autOn V (B6.thompsonJ_le R))
  have hDn : (((autOn (thompsonJ R) V).map (binPsi θ).toMonoidHom).subgroupOf
      ((autOn R V).map (binPsi θ).toMonoidHom)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDsubT]
    exact map_le_normalizer_map_of_le (binPsi θ)
      (autOn_le_normalizer_autOn hRN hJN (B6.le_normalizer_thompsonJ R))
  have hJc : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G) := fun hc =>
    hS.thompson_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc)
  have hne : (autOn (thompsonJ R) V).map (binPsi θ).toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (binPsi θ).injective]
    exact autOn_ne_bot_of_not_le_centralizer hJN hJc
  have hDS : (autOn (thompsonJ R) V).map (binPsi θ).toMonoidHom ≤
      (autOn (baum R) V).map (binPsi θ).toMonoidHom :=
    Subgroup.map_mono (autOn_le_autOn V (thompsonJ_le_baum' R))
  have hST : (autOn (baum R) V).map (binPsi θ).toMonoidHom ≤
      (autOn R V).map (binPsi θ).toMonoidHom :=
    Subgroup.map_mono (autOn_le_autOn V (inf_le_left : baum R ≤ R))
  have hSfix : ∀ s ∈ (autOn (baum R) V).map (binPsi θ).toMonoidHom,
      ∀ v ∈ fixGL ((autOn (thompsonJ R) V).map (binPsi θ).toMonoidHom), s v = v := by
    rintro _ ⟨σ, hσ, rfl⟩ v hv
    obtain ⟨g, hgB, rfl⟩ := mem_autOn_iff.1 hσ
    set v0 : V := θ.symm (Multiplicative.ofAdd v) with hv0
    have hv0fix : v0 ∈ fixV (autOn (thompsonJ R) V) :=
      (mem_fixGL_map θ (autOn (thompsonJ R) V) v0).1 (by simpa [hv0] using hv)
    have hvJ : ∀ j ∈ thompsonJ R, (j : G) * v0 = v0 * j := by
      intro j hj
      have hφ : conjAct V ⟨j, hJN hj⟩ ∈ autOn (thompsonJ R) V :=
        mem_autOn_iff.2 ⟨⟨j, hJN hj⟩, hj, rfl⟩
      have h1 := congrArg (fun w : V => (w : G)) (hv0fix _ hφ)
      simp only [coe_conjAct_apply] at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hvA : ∀ A : Subgroup G, IsMaxElemAbelian R A → (v0 : G) ∈ A := by
      intro A hA
      rw [eq_omegaOneOf_centralizer hA]
      refine Subgroup.subset_closure ⟨⟨hVR v0.2, ?_⟩, hVe.2 v0 v0.2⟩
      exact Subgroup.mem_centralizer_iff.2 fun a ha => hvJ a (B6.le_thompsonJ hA ha)
    have hvE : (v0 : G) ∈ omegaOneCenterOf (thompsonJ R) := by
      rw [(omegaOne_centralizer_thompsonJ R).2]
      simp only [Subgroup.mem_iInf]
      exact fun A hA => hvA A hA
    have hgv : (v0 : G) * g = g * v0 := Subgroup.mem_centralizer_iff.1 hgB.2 v0 hvE
    have hfix0 : conjAct V g v0 = v0 := by
      apply Subtype.ext
      rw [coe_conjAct_apply, mul_inv_eq_iff_eq_mul]
      exact hgv.symm
    show (binPsi θ) (conjAct V g) v = v
    rw [binPsi_apply]
    change Multiplicative.toAdd (θ (conjAct V g v0)) = v
    rw [hfix0]
    simp [hv0]
  have ctx := familyCtx_of_layer hS.two_le hF (isCompListIn_map (binPsi θ) hLc)
    hmax.offenders.family.layer
  have key := even_SL2_images_actor ctx hsyl hmax.U_sylow hmax.Q_sylow hmax.D_eq 𝓔 hE
    (hDimg ▸ hDn) (hDimg ▸ hne) ((autOn (baum R) V).map (binPsi θ).toMonoidHom)
    (hDimg ▸ hDS) hST (hDimg ▸ hSfix)
  rwa [hDimg] at key

end Main

end CFSG.QuasithinUnique.Setup.Lift
