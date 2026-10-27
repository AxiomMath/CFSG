module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreGood
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreAssemble

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Main

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Planes
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Assemble
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Link
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Glue
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Good
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable {E : Subgroup (V ≃ₗ[ZMod 2] V)} {k : ℕ} {X : Fin k → Submodule (ZMod 2) V}
  {ρf : Fin k → (V ≃ₗ[ZMod 2] V)}

theorem isElemAbelian_le' {G : Type*} [Group G] {p : ℕ} {E F : Subgroup G} (h : F ≤ E)
    (hE : IsElemAbelian p E) : IsElemAbelian p F :=
  ⟨⟨⟨fun a b => Subtype.ext (show a.1 * b.1 = b.1 * a.1 from congrArg Subtype.val
      (hE.1.is_comm.comm ⟨a.1, h a.2⟩ ⟨b.1, h b.2⟩))⟩⟩, fun x hx => hE.2 x (h hx)⟩

theorem mul_on_p1 {p₁ p₂ : Fin k} (D : PieceData E X ρf) (hne : p₁ ≠ p₂)
    {e₁ e₂ : V ≃ₗ[ZMod 2] V} (h₁ : ∀ x ∈ X p₁, e₁ x = ρf p₁ x)
    (h₂' : ∀ j, j ≠ p₂ → ∀ x ∈ X j, e₂ x = x) (x : V) (hx : x ∈ X p₁) :
    (e₁ * e₂) x = ρf p₁ x := by
  rw [LinearEquiv.mul_apply, h₂' p₁ hne x hx, h₁ x hx]

theorem mul_on_p2 {p₁ p₂ : Fin k} (D : PieceData E X ρf) (hne : p₁ ≠ p₂)
    {e₁ e₂ : V ≃ₗ[ZMod 2] V} (h₂ : ∀ x ∈ X p₂, e₂ x = ρf p₂ x)
    (h₁' : ∀ j, j ≠ p₁ → ∀ x ∈ X j, e₁ x = x) (x : V) (hx : x ∈ X p₂) :
    (e₁ * e₂) x = ρf p₂ x := by
  rw [LinearEquiv.mul_apply, h₂ x hx, h₁' p₂ (Ne.symm hne) _
    (D.inv p₂ (ρf p₂) (D.gen_mem p₂) x hx)]

theorem phi_scalar {ψ₁ ψ₂ : Model.F4 →ₗ[ZMod 2] V} {f : V ≃ₗ[ZMod 2] V} {s : Model.F4}
    (h₁ : ∀ a, f (ψ₁ a) = ψ₁ (s * a)) (h₂ : ∀ a, f (ψ₂ a) = ψ₂ (s * a)) (c : Fin 2 → Model.F4) :
    f (phiOf ψ₁ ψ₂ c) = phiOf ψ₁ ψ₂ (s • c) := by
  rw [phiOf_apply, phiOf_apply, map_add, h₁, h₂]
  rfl

theorem pow_on_plane (D : PieceData E X ρf) {i : Fin k} (hi : Module.finrank (ZMod 2) (X i) = 2) :
    ∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x := by
  intro g hg
  rcases (D.gen i).2 with h' | h'
  · exact absurd h'.1 (by omega)
  · exact h'.2.2.2 g hg

theorem core_good (D : PieceData E X ρf) (hdual : DualData E X ρf)
    {p₁ p₂ : Fin k} (hp₁ : Module.finrank (ZMod 2) (X p₁) = 2)
    (hp₂ : Module.finrank (ZMod 2) (X p₂) = 2) (hne : p₁ ≠ p₂)
    {e₁ e₂ : V ≃ₗ[ZMod 2] V} (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E)
    (he₁a : ∀ x ∈ X p₁, e₁ x = ρf p₁ x) (he₁b : ∀ l, l ≠ p₁ → ∀ x ∈ X l, e₁ x = x)
    (he₂a : ∀ x ∈ X p₂, e₂ x = ρf p₂ x) (he₂b : ∀ l, l ≠ p₂ → ∀ x ∈ X l, e₂ x = x) :
    ∃ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ E ∧ IsElemAbelian 3 F ∧ Nat.card E = 3 * Nat.card F ∧
      ∃ L : Subgroup (V ≃ₗ[ZMod 2] V),
        CFSG.Open.IsSubnormal L (Subgroup.centralizer (F : Set (V ≃ₗ[ZMod 2] V))) ∧
          CFSG.Open.IsQuasisimple L ∧ 3 ∣ Nat.card (L ⧸ Subgroup.center L) := by
  classical
  have hFE : Fset D hp₁ hp₂ ≤ E := fun g hg => ((mem_Fset D hp₁ hp₂).1 hg).1
  refine ⟨Fset D hp₁ hp₂, hFE, isElemAbelian_le' hFE D.ab,
    card_eq_three_mul D hp₁ hp₂ he₁ he₁a (he₁b p₂ (Ne.symm hne)), ?_⟩
  obtain ⟨Uc, hUc⟩ : ∃ Uc : Submodule (ZMod 2) V,
      Uc = ⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i := ⟨_, rfl⟩
  have hcU : IsCompl (X p₁ ⊔ X p₂) Uc := by
    rw [hUc, ← sup_pair_eq X p₁ p₂]
    exact isCompl_pair D hne
  have hf1E : (e₁ * e₂) ∈ E := E.mul_mem he₁ he₂
  have hf1a : ∀ x ∈ X p₁, (e₁ * e₂) x = ρf p₁ x := fun x hx => mul_on_p1 D hne he₁a he₂b x hx
  have hf1b : ∀ x ∈ X p₂, (e₁ * e₂) x = ρf p₂ x := fun x hx => mul_on_p2 D hne he₂a he₁b x hx
  have hrange1 : LinearMap.range (((e₁ * e₂ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id) =
      X p₁ ⊔ X p₂ := range_pair D hp₁ hp₂ hne he₁a he₁b he₂a he₂b
  have hf1F : (e₁ * e₂) ∈ Fset D hp₁ hp₂ := by
    rw [mem_Fset D hp₁ hp₂]
    refine ⟨hf1E, ?_⟩
    have h1 : expo ρf X p₁ e₁ = 1 := expo_eq_one D hp₁ he₁ he₁a
    have h2 : expo ρf X p₁ e₂ = 0 := expo_eq_zero_of_fix D hp₁ he₂ (he₂b p₁ hne)
    have h3 : expo ρf X p₂ e₁ = 0 := expo_eq_zero_of_fix D hp₂ he₁ (he₁b p₂ (Ne.symm hne))
    have h4 : expo ρf X p₂ e₂ = 1 := expo_eq_one D hp₂ he₂ he₂a
    rw [expo_add D hp₁ he₁ he₂, expo_add D hp₂ he₁ he₂, h1, h2, h3, h4]
    rfl
  have hinv1 : ∀ x ∈ X p₁, ρf p₁ x ∈ X p₁ := fun x hx => D.inv p₁ (ρf p₁) (D.gen_mem p₁) x hx
  have hinv2 : ∀ x ∈ X p₂, ρf p₂ x ∈ X p₂ := fun x hx => D.inv p₂ (ρf p₂) (D.gen_mem p₂) x hx
  obtain ⟨w₁, hw₁X, hw₁0⟩ := exists_ne_zero_of_ne_bot (D.irr p₁).1
  obtain ⟨w₂, hw₂X, hw₂0⟩ := exists_ne_zero_of_ne_bot (D.irr p₂).1
  have li₁ := li_plane hw₁X hw₁0 (fun x => cube_apply (pow3_eq_one_of_mem D.ab (D.gen_mem p₁)) x)
    (D.plane_fixed hp₁) (D.plane_quad hp₁) hinv1
  have li₂ := li_plane hw₂X hw₂0 (fun x => cube_apply (pow3_eq_one_of_mem D.ab (D.gen_mem p₂)) x)
    (D.plane_fixed hp₂) (D.plane_quad hp₂) hinv2
  have hr1 : LinearMap.range (psiOf w₁ (ρf p₁)) = X p₁ := psiOf_range hw₁X hinv1 hp₁ li₁
  have hr2 : LinearMap.range (psiOf w₂ (ρf p₂)) = X p₂ := psiOf_range hw₂X hinv2 hp₂ li₂
  have hinj1 := psiOf_injective li₁
  have hinj2 := psiOf_injective li₂
  have hdisjψ : Disjoint (LinearMap.range (psiOf w₁ (ρf p₁))) (LinearMap.range (psiOf w₂ (ρf p₂))) := by
    rw [hr1, hr2]
    exact D.ind.pairwiseDisjoint hne
  have hφinj := phiOf_injective hinj1 hinj2 hdisjψ
  have hφrange : LinearMap.range (phiOf (psiOf w₁ (ρf p₁)) (psiOf w₂ (ρf p₂))) = X p₁ ⊔ X p₂ := by
    rw [phiOf_range, hr1, hr2]
  let phiU : (Fin 2 → Model.F4) ≃ₗ[ZMod 2] ↥(X p₁ ⊔ X p₂) :=
    (LinearEquiv.ofInjective _ hφinj).trans (LinearEquiv.ofEq _ _ hφrange)
  have hphiU : ∀ c, ((phiU c : ↥(X p₁ ⊔ X p₂)) : V) =
      phiOf (psiOf w₁ (ρf p₁)) (psiOf w₂ (ρf p₂)) c := fun c => rfl
  have h₁ : ∀ a, (e₁ * e₂) (psiOf w₁ (ρf p₁) a) = psiOf w₁ (ρf p₁) (Model.omega * a) :=
    fun a => psiOf_compat hw₁X hinv1 (D.plane_quad hp₁) hf1a a
  have h₂ : ∀ a, (e₁ * e₂) (psiOf w₂ (ρf p₂) a) = psiOf w₂ (ρf p₂) (Model.omega * a) :=
    fun a => psiOf_compat hw₂X hinv2 (D.plane_quad hp₂) hf1b a
  have hf1phi : ∀ c, (e₁ * e₂) ((phiU c : ↥(X p₁ ⊔ X p₂)) : V) =
      ((phiU (Model.omega • c) : ↥(X p₁ ⊔ X p₂)) : V) := by
    intro c
    rw [hphiU, hphiU]
    exact phiOf_compat h₁ h₂ c
  have hFinv_U : ∀ f ∈ Fset D hp₁ hp₂, Pres (X p₁ ⊔ X p₂) f := by
    intro f hf
    have hfE := ((mem_Fset D hp₁ hp₂).1 hf).1
    have := pres_range_of_comm E D.ab hf1E hfE
    rw [hrange1] at this
    exact this
  have hFinv_Uc : ∀ f ∈ Fset D hp₁ hp₂, Pres Uc f := by
    intro f hf
    rw [hUc]
    exact pres_Uc_of_dual D hdual f ((mem_Fset D hp₁ hp₂).1 hf).1
  have hC_pres : ∀ g ∈ Subgroup.centralizer ((Fset D hp₁ hp₂ : Subgroup (V ≃ₗ[ZMod 2] V)) :
      Set (V ≃ₗ[ZMod 2] V)), Pres (X p₁ ⊔ X p₂) g ∧ Pres Uc g := by
    intro g hg
    have hcomm1 : g * (e₁ * e₂) = (e₁ * e₂) * g :=
      ((Subgroup.mem_centralizer_iff.1 hg) (e₁ * e₂) hf1F).symm
    have hU : Pres (X p₁ ⊔ X p₂) g := by
      have := map_range_le_of_comm g (e₁ * e₂) hcomm1
      rw [hrange1] at this
      intro x hx
      exact this (Submodule.mem_map_of_mem hx)
    refine ⟨hU, ?_⟩
    rw [hUc]
    apply pres_Uc_of_mem
    intro j hj x hx
    have hj1 : j ≠ p₁ := fun h => hj (Or.inl h)
    have hj2 : j ≠ p₂ := fun h => hj (Or.inr h)
    by_cases hpl : Module.finrank (ZMod 2) (X j) = 2
    · obtain ⟨ej, hej, hejp, hejfix⟩ := hdual j hpl
      have hejF : ej ∈ Fset D hp₁ hp₂ := by
        rw [mem_Fset D hp₁ hp₂]
        refine ⟨hej, ?_⟩
        rw [expo_eq_zero_of_fix D hp₁ hej (fun y hy => hejfix p₁ (Ne.symm hj1) y hy),
          expo_eq_zero_of_fix D hp₂ hej (fun y hy => hejfix p₂ (Ne.symm hj2) y hy)]
      have hcomm := (Subgroup.mem_centralizer_iff.1 hg) ej hejF
      have hr := range_sub_eq_plane D hpl hej hejp hejfix
      have hx' : x ∈ LinearMap.range ((ej : V →ₗ[ZMod 2] V) - LinearMap.id) := by
        rw [hr]
        exact hx
      have hgx := map_range_le_of_comm g ej hcomm.symm (Submodule.mem_map_of_mem hx')
      rw [hr] at hgx
      exact (le_iSup₂ (f := fun i (_ : i ∈ ({p₁, p₂} : Set (Fin k))ᶜ) => X i) j hj) hgx
    · have hv : ∀ f ∈ Fset D hp₁ hp₂, f (g x) = g x := by
        intro f hf
        have hfE := ((mem_Fset D hp₁ hp₂).1 hf).1
        have hcomm' := (Subgroup.mem_centralizer_iff.1 hg) f hf
        show (f * g) x = g x
        rw [hcomm', LinearEquiv.mul_apply, D.line_triv hpl f hfE x hx]
      exact fix_mem_Uc D hp₁ hp₂ hne hf1a hf1b (Fset D hp₁ hp₂ : Set (V ≃ₗ[ZMod 2] V)) hf1F
        (fun f hf => hFinv_U f hf) (fun f hf => by rw [← hUc]; exact hFinv_Uc f hf) (g x) hv
  have hcomm_glue : ∀ f ∈ Fset D hp₁ hp₂, ∀ A : Matrix.SpecialLinearGroup (Fin 2) Model.F4,
      f * glueSL hcU phiU A = glueSL hcU phiU A * f := by
    intro f hf A
    have hfE := ((mem_Fset D hp₁ hp₂).1 hf).1
    have hkk : expo ρf X p₂ f = expo ρf X p₁ f := ((mem_Fset D hp₁ hp₂).1 hf).2.symm
    have hfp1 : ∀ x ∈ X p₁, f x = (ρf p₁ ^ ((expo ρf X p₁ f : Fin 3) : ℕ)) x :=
      fun x hx => expo_spec (pow_on_plane D hp₁ f hfE) x hx
    have hfp2 : ∀ x ∈ X p₂, f x = (ρf p₂ ^ ((expo ρf X p₁ f : Fin 3) : ℕ)) x := by
      intro x hx
      rw [expo_spec (pow_on_plane D hp₂ f hfE) x hx, hkk]
    have hψ1 : ∀ a, f (psiOf w₁ (ρf p₁) a) =
        psiOf w₁ (ρf p₁) (Model.omega ^ ((expo ρf X p₁ f : Fin 3) : ℕ) * a) := by
      intro a
      have hmem : psiOf w₁ (ρf p₁) a ∈ X p₁ := by
        rw [← hr1]
        exact LinearMap.mem_range_self _ a
      rw [hfp1 _ hmem, psiOf_pow hw₁X hinv1 (D.plane_quad hp₁) _ a]
    have hψ2 : ∀ a, f (psiOf w₂ (ρf p₂) a) =
        psiOf w₂ (ρf p₂) (Model.omega ^ ((expo ρf X p₁ f : Fin 3) : ℕ) * a) := by
      intro a
      have hmem : psiOf w₂ (ρf p₂) a ∈ X p₂ := by
        rw [← hr2]
        exact LinearMap.mem_range_self _ a
      rw [hfp2 _ hmem, psiOf_pow hw₂X hinv2 (D.plane_quad hp₂) _ a]
    have hf_scalar : ∀ c, f ((phiU c : ↥(X p₁ ⊔ X p₂)) : V) =
        ((phiU ((Model.omega ^ ((expo ρf X p₁ f : Fin 3) : ℕ)) • c) : ↥(X p₁ ⊔ X p₂)) : V) := by
      intro c
      rw [hphiU, hphiU]
      exact phi_scalar hψ1 hψ2 c
    apply LinearEquiv.ext
    intro x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact glueA_comm_f hcU phiU (Matrix.SpecialLinearGroup.toGL A) f _ hf_scalar
      (hFinv_U f hf) (hFinv_Uc f hf) x
  have hL_le : (glueSL hcU phiU).range ≤
      Subgroup.centralizer ((Fset D hp₁ hp₂ : Subgroup (V ≃ₗ[ZMod 2] V)) :
        Set (V ≃ₗ[ZMod 2] V)) := by
    rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_centralizer_iff.2 (fun f hf => hcomm_glue f hf A)
  have hconj : ∀ g ∈ Subgroup.centralizer ((Fset D hp₁ hp₂ : Subgroup (V ≃ₗ[ZMod 2] V)) :
      Set (V ≃ₗ[ZMod 2] V)), ∀ A : Matrix.SpecialLinearGroup (Fin 2) Model.F4,
      g * glueSL hcU phiU A * g⁻¹ ∈ (glueSL hcU phiU).range := by
    intro g hg A
    obtain ⟨hgU, hgUc⟩ := hC_pres g hg
    have hginv : g⁻¹ ∈ Subgroup.centralizer ((Fset D hp₁ hp₂ : Subgroup (V ≃ₗ[ZMod 2] V)) :
        Set (V ≃ₗ[ZMod 2] V)) := Subgroup.inv_mem _ hg
    obtain ⟨hginvU, hginvUc⟩ := hC_pres g⁻¹ hginv
    have hgcomm : g * (e₁ * e₂) = (e₁ * e₂) * g :=
      ((Subgroup.mem_centralizer_iff.1 hg) (e₁ * e₂) hf1F).symm
    obtain ⟨B, hB⟩ := commutant_on_U phiU hf1phi g hgcomm hgU hginvU
    have hdetconj : ((B : Matrix (Fin 2) (Fin 2) Model.F4) * (A : Matrix (Fin 2) (Fin 2) Model.F4) *
        ((B⁻¹ : GL (Fin 2) Model.F4) : Matrix (Fin 2) (Fin 2) Model.F4)).det = 1 := by
      rw [Matrix.det_units_conj]
      exact A.2
    let A' : Matrix.SpecialLinearGroup (Fin 2) Model.F4 := ⟨_, hdetconj⟩
    have hunit : Matrix.SpecialLinearGroup.toGL A' =
        B * Matrix.SpecialLinearGroup.toGL A * B⁻¹ := Units.ext rfl
    have hA' : glueSL hcU phiU A' = g * glueSL hcU phiU A * g⁻¹ := by
      apply LinearEquiv.ext
      intro x
      show glueA hcU phiU (Matrix.SpecialLinearGroup.toGL A') x = _
      rw [hunit]
      exact (glueA_conj hcU phiU g B (Matrix.SpecialLinearGroup.toGL A) hginvU hginvUc hB x).symm
    rw [← hA']
    exact ⟨A', rfl⟩
  have hnorm : ((glueSL hcU phiU).range.subgroupOf (Subgroup.centralizer
      ((Fset D hp₁ hp₂ : Subgroup (V ≃ₗ[ZMod 2] V)) : Set (V ≃ₗ[ZMod 2] V)))).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 hn
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hA]
    exact hconj _ g.2 A
  have hsub : CFSG.Open.IsSubnormal ((glueSL hcU phiU).range) (Subgroup.centralizer
      ((Fset D hp₁ hp₂ : Subgroup (V ≃ₗ[ZMod 2] V)) : Set (V ≃ₗ[ZMod 2] V))) :=
    CFSG.Open.IsSubnormal.step hL_le hnorm (CFSG.Open.IsSubnormal.refl _)
  have hQ : CFSG.Open.IsQuasisimple ↥(glueSL hcU phiU).range :=
    CFSG.LargeExtraspecial.Bridge.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (glueSL_injective hcU phiU)) isQuasisimple_sl_F4
  have hcenter : Subgroup.center ↥(glueSL hcU phiU).range = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨z, hzL⟩ hz
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hzL
    rw [Subgroup.mem_bot]
    have hcomm : ∀ B : Matrix.SpecialLinearGroup (Fin 2) Model.F4, A * B = B * A := by
      intro B
      apply glueSL_injective hcU phiU
      rw [map_mul, map_mul]
      have h1 := (Subgroup.mem_center_iff.1 hz) ⟨glueSL hcU phiU B, ⟨B, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      exact h2.symm
    have hAc : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) Model.F4) :=
      Subgroup.mem_center_iff.2 (fun B => (hcomm B).symm)
    rw [center_sl_F4, Subgroup.mem_bot] at hAc
    apply Subtype.ext
    simp [hAc]
  let x : ↥(glueSL hcU phiU).range := ⟨glueSL hcU phiU mtilde, ⟨mtilde, rfl⟩⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    show (glueSL hcU phiU mtilde) ^ 3 = 1
    rw [← map_pow, mtilde_cube, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    apply mtilde_ne_one
    apply glueSL_injective hcU phiU
    rw [map_one]
    exact congrArg Subtype.val h
  have hxbar : orderOf (QuotientGroup.mk x : ↥(glueSL hcU phiU).range ⧸
      Subgroup.center ↥(glueSL hcU phiU).range) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, hx3]
      rfl
    · intro h
      rw [QuotientGroup.eq_one_iff, hcenter, Subgroup.mem_bot] at h
      exact hx1 h
  have hdvd : 3 ∣ Nat.card (↥(glueSL hcU phiU).range ⧸
      Subgroup.center ↥(glueSL hcU phiU).range) := by
    rw [← hxbar]
    exact orderOf_dvd_natCard _
  exact ⟨(glueSL hcU phiU).range, hsub, hQ, hdvd⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Main

end
