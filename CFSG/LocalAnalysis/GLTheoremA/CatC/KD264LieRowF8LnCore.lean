module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreFinal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Planes
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Assemble
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Main
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Link
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Glue
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Good
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Model
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Final

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable {E : Subgroup (V ≃ₗ[ZMod 2] V)} {k : ℕ} {X : Fin k → Submodule (ZMod 2) V}
  {ρf : Fin k → (V ≃ₗ[ZMod 2] V)}

theorem core_good_c (D : PieceData E X ρf)
    {p₁ p₂ : Fin k} (hp₁ : Module.finrank (ZMod 2) (X p₁) = 2)
    (hp₂ : Module.finrank (ZMod 2) (X p₂) = 2) (hne : p₁ ≠ p₂)
    {e₁ e₂ : V ≃ₗ[ZMod 2] V} (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E)
    (he₁a : ∀ x ∈ X p₁, e₁ x = ρf p₁ x) (he₁b : ∀ l, l ≠ p₁ → ∀ x ∈ X l, e₁ x = x)
    (he₂a : ∀ x ∈ X p₂, e₂ x = ρf p₂ x) (he₂b : ∀ l, l ≠ p₂ → ∀ x ∈ X l, e₂ x = x) :
    ∃ c ∈ E, c ≠ 1 ∧ ∃ L : Subgroup (V ≃ₗ[ZMod 2] V),
      L ≤ Subgroup.centralizer ({c} : Set (V ≃ₗ[ZMod 2] V)) ∧
      (L.subgroupOf (Subgroup.centralizer ({c} : Set (V ≃ₗ[ZMod 2] V)))).Normal ∧
      CFSG.Open.IsQuasisimple L ∧ 3 ∣ Nat.card (L ⧸ Subgroup.center L) := by
  classical
  obtain ⟨Uc, hUc⟩ : ∃ Uc : Submodule (ZMod 2) V,
      Uc = ⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i := ⟨_, rfl⟩
  have hcU : IsCompl (X p₁ ⊔ X p₂) Uc := by
    rw [hUc, ← sup_pair_eq X p₁ p₂]
    exact isCompl_pair D hne
  have hf1E : (e₁ * e₂) ∈ E := E.mul_mem he₁ he₂
  have hf1a : ∀ x ∈ X p₁, (e₁ * e₂) x = ρf p₁ x := fun x hx => mul_on_p1 D hne he₁a he₂b x hx
  have hf1b : ∀ x ∈ X p₂, (e₁ * e₂) x = ρf p₂ x := fun x hx => mul_on_p2 D hne he₂a he₁b x hx
  have hf1c : ∀ j, j ≠ p₁ → j ≠ p₂ → ∀ x ∈ X j, (e₁ * e₂) x = x := by
    intro j hj1 hj2 x hx
    rw [LinearEquiv.mul_apply, he₂b j hj2 x hx, he₁b j hj1 x hx]
  have hrange1 : LinearMap.range (((e₁ * e₂ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id) =
      X p₁ ⊔ X p₂ := range_pair D hp₁ hp₂ hne he₁a he₁b he₂a he₂b
  have hf1ne : (e₁ * e₂) ≠ 1 := by
    intro h1
    obtain ⟨w₁, hw₁X, hw₁0⟩ := exists_ne_zero_of_ne_bot (D.irr p₁).1
    have h2 : ρf p₁ w₁ = w₁ := by
      have := hf1a w₁ hw₁X
      rw [h1] at this
      exact this.symm
    exact hw₁0 (D.plane_fixed hp₁ w₁ hw₁X h2)
  have hfixUc : ∀ x ∈ Uc, (e₁ * e₂) x = x := by
    intro x hx
    rw [hUc] at hx
    refine Submodule.iSup_induction
      (fun i => ⨆ (_ : i ∈ ({p₁, p₂} : Set (Fin k))ᶜ), X i)
      (motive := fun x => (e₁ * e₂) x = x) hx ?_ ?_ ?_
    · intro i y hy
      by_cases hi : i ∈ ({p₁, p₂} : Set (Fin k))ᶜ
      · rw [iSup_pos hi] at hy
        exact hf1c i (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h)) y hy
      · rw [iSup_neg hi] at hy
        rw [(Submodule.mem_bot _).1 hy, map_zero]
    · exact map_zero _
    · intro x y hx hy
      rw [map_add, hx, hy]
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
  have hdisjψ : Disjoint (LinearMap.range (psiOf w₁ (ρf p₁)))
      (LinearMap.range (psiOf w₂ (ρf p₂))) := by
    rw [hr1, hr2]
    exact D.ind.pairwiseDisjoint hne
  have hφinj := phiOf_injective hinj1 hinj2 hdisjψ
  have hφrange : LinearMap.range (phiOf (psiOf w₁ (ρf p₁)) (psiOf w₂ (ρf p₂))) =
      X p₁ ⊔ X p₂ := by
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
  have hf1U : Pres (X p₁ ⊔ X p₂) (e₁ * e₂) := by
    have := pres_range_of_comm E D.ab hf1E hf1E
    rw [hrange1] at this
    exact this
  have hf1Uc : Pres Uc (e₁ * e₂) := fun x hx => by rw [hfixUc x hx]; exact hx
  have hC_pres : ∀ g ∈ Subgroup.centralizer ({e₁ * e₂} : Set (V ≃ₗ[ZMod 2] V)),
      Pres (X p₁ ⊔ X p₂) g ∧ Pres Uc g := by
    intro g hg
    have hcomm1 : g * (e₁ * e₂) = (e₁ * e₂) * g :=
      ((Subgroup.mem_centralizer_iff.1 hg) (e₁ * e₂) (Set.mem_singleton _)).symm
    have hU : Pres (X p₁ ⊔ X p₂) g := by
      have := map_range_le_of_comm g (e₁ * e₂) hcomm1
      rw [hrange1] at this
      intro x hx
      exact this (Submodule.mem_map_of_mem hx)
    refine ⟨hU, fun x hx => ?_⟩
    have hv : ∀ f ∈ ({e₁ * e₂} : Set (V ≃ₗ[ZMod 2] V)), f (g x) = g x := by
      intro f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      show ((e₁ * e₂) * g) x = g x
      rw [← hcomm1, LinearEquiv.mul_apply, hfixUc x hx]
    have := fix_mem_Uc D hp₁ hp₂ hne hf1a hf1b ({e₁ * e₂} : Set (V ≃ₗ[ZMod 2] V))
      (Set.mem_singleton _) (fun f hf => by rw [Set.mem_singleton_iff] at hf; subst hf; exact hf1U)
      (fun f hf => by
        rw [Set.mem_singleton_iff] at hf; subst hf; rw [← hUc]; exact hf1Uc) (g x) hv
    rw [hUc]
    exact this
  have hcomm_glue : ∀ A : Matrix.SpecialLinearGroup (Fin 2) Model.F4,
      (e₁ * e₂) * glueSL hcU phiU A = glueSL hcU phiU A * (e₁ * e₂) := by
    intro A
    apply LinearEquiv.ext
    intro x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact glueA_comm_f hcU phiU (Matrix.SpecialLinearGroup.toGL A) (e₁ * e₂) Model.omega
      hf1phi hf1U hf1Uc x
  have hL_le : (glueSL hcU phiU).range ≤
      Subgroup.centralizer ({e₁ * e₂} : Set (V ≃ₗ[ZMod 2] V)) := by
    rintro _ ⟨A, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 (fun f hf => ?_)
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact hcomm_glue A
  have hconj : ∀ g ∈ Subgroup.centralizer ({e₁ * e₂} : Set (V ≃ₗ[ZMod 2] V)),
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) Model.F4,
      g * glueSL hcU phiU A * g⁻¹ ∈ (glueSL hcU phiU).range := by
    intro g hg A
    obtain ⟨hgU, hgUc⟩ := hC_pres g hg
    have hginv : g⁻¹ ∈ Subgroup.centralizer ({e₁ * e₂} : Set (V ≃ₗ[ZMod 2] V)) :=
      Subgroup.inv_mem _ hg
    obtain ⟨hginvU, hginvUc⟩ := hC_pres g⁻¹ hginv
    have hgcomm : g * (e₁ * e₂) = (e₁ * e₂) * g :=
      ((Subgroup.mem_centralizer_iff.1 hg) (e₁ * e₂) (Set.mem_singleton _)).symm
    obtain ⟨B, hB⟩ := commutant_on_U phiU hf1phi g hgcomm hgU hginvU
    have hdetconj : ((B : Matrix (Fin 2) (Fin 2) Model.F4) *
        (A : Matrix (Fin 2) (Fin 2) Model.F4) *
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
      ({e₁ * e₂} : Set (V ≃ₗ[ZMod 2] V)))).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 hn
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hA]
    exact hconj _ g.2 A
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
  exact ⟨e₁ * e₂, hf1E, hf1ne, (glueSL hcU phiU).range, hL_le, hnorm, hQ, hdvd⟩

theorem core_c {N : ℕ} (hV : Module.finrank (ZMod 2) V = N) (hN : 4 ≤ N)
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) (hE : IsElemAbelian 3 E)
    (hge : 3 ^ (N / 2) ≤ Nat.card E) :
    ∃ c ∈ E, c ≠ 1 ∧ ∃ L : Subgroup (V ≃ₗ[ZMod 2] V),
      L ≤ Subgroup.centralizer ({c} : Set (V ≃ₗ[ZMod 2] V)) ∧
      (L.subgroupOf (Subgroup.centralizer ({c} : Set (V ≃ₗ[ZMod 2] V)))).Normal ∧
      CFSG.Open.IsQuasisimple L ∧ 3 ∣ Nat.card (L ⧸ Subgroup.center L) := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  have hge' : 3 ^ (Module.finrank (ZMod 2) V / 2) ≤ Fintype.card E := by
    rw [hV, ← Nat.card_eq_fintype_card]
    exact hge
  obtain ⟨k, X, ρf, hXprop, hind, hsup, hρf, hPcard, hpe⟩ := exists_struct E hE hge'
  let D : PieceData E X ρf := ⟨hE, fun i => (hXprop i).1, fun i => (hXprop i).2, hind, hsup, hρf⟩
  have hdual : DualData E X ρf := dual_of_struct D hpe
  have hone : 1 < Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} := by
    rw [hPcard]
    omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hone
  have hne : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  obtain ⟨e₁, he₁, he₁a, he₁b⟩ := hdual a.1 a.2
  obtain ⟨e₂, he₂, he₂a, he₂b⟩ := hdual b.1 b.2
  exact core_good_c D a.2 b.2 hne he₁ he₂ he₁a he₁b he₂a he₂b

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

end
