module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderNat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDelE

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Range

theorem isElementaryAbelian_range {p : ℕ} {G G' : Type*} [Group G] [Group G']
    [hG : CFSG.IsElementaryAbelian p G] (f : G →* G') : CFSG.IsElementaryAbelian p f.range where
  is_comm := ⟨fun x y => by
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    show (x : G') * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, hG.1.1.1 a b]⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
    obtain ⟨a, ha⟩ := x.2
    apply Subtype.ext
    show (x : G') ^ p = 1
    rw [← ha, ← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hG.exponent_dvd_p a,
      map_one]

end Range

section DelSplit

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}
  {ctx : FamilyCtx H T n F r Lc} {i : Fin r}

@[expose] noncomputable def DelModel.actUnit (M : DelModel ctx i) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hIE : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤)) :
    ↥(Lc i ⊔ E) →* (Module.End (ZMod 2) ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))))ˣ :=
  (conjU M.β).comp ((unitsEquiv (ZMod 2) ↥(commGL (Lc i) ⊤)).symm.toMonoidHom.comp
    (resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) hIE))

omit [Finite V] in
theorem DelModel.actUnit_val (M : DelModel ctx i) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hIE : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤))
    (x : ↥(Lc i ⊔ E)) (u : ↥(commGL (Lc i) ⊤)) :
    (M.actUnit hIE x).val (M.β u) =
      M.β (resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) hIE x u) := by
  show (conjU M.β ((unitsEquiv (ZMod 2) ↥(commGL (Lc i) ⊤)).symm
    (resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) hIE x))).val
      (M.β u) = _
  rw [conjU_val_apply, ← unitsEquiv_apply, MulEquiv.apply_symm_apply]

omit [Finite V] in
theorem DelModel.actUnit_eq_permU (M : DelModel ctx i) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hIE : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤))
    (x : ↥(Lc i ⊔ E)) (hxB : (x : V ≃ₗ[ZMod 2] V) ∈ blockB H (Lc i)) :
    M.actUnit hIE x = permU (M.ψ ⟨x, hxB⟩) := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  obtain ⟨u, rfl⟩ := M.β.surjective w
  apply Subtype.ext
  rw [M.actUnit_val hIE x u, permU_apply]
  exact M.compat ⟨x, hxB⟩ u
    (resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) hIE x u)
    (resSub_apply _ _ _ _ x u)

omit [Finite V] in
theorem DelModel.act_eq_of_val_eq (M : DelModel ctx i) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hIE : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤))
    (x₁ x₂ : ↥(Lc i ⊔ E)) (p : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))))
    (h : (M.actUnit hIE x₁).val p = (M.actUnit hIE x₂).val p) :
    (x₁ : V ≃ₗ[ZMod 2] V) ((M.β.symm p : ↥(commGL (Lc i) ⊤)) : V) =
      (x₂ : V ≃ₗ[ZMod 2] V) ((M.β.symm p : ↥(commGL (Lc i) ⊤)) : V) := by
  have h1 := M.actUnit_val hIE x₁ (M.β.symm p)
  have h2 := M.actUnit_val hIE x₂ (M.β.symm p)
  rw [M.β.apply_symm_apply] at h1 h2
  have h3 : resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) hIE x₁
      (M.β.symm p) = resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) hIE x₂
      (M.β.symm p) := M.β.injective (h1.symm.trans (h.trans h2))
  have h4 := congrArg Subtype.val h3
  rwa [resSub_apply, resSub_apply] at h4

omit [Finite V] in
theorem DelModel.act_ne_of_val_ne (M : DelModel ctx i) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hIE : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤))
    (x₁ : ↥(Lc i ⊔ E)) (p : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))))
    (h : (M.actUnit hIE x₁).val p ≠ p) :
    (x₁ : V ≃ₗ[ZMod 2] V) ((M.β.symm p : ↥(commGL (Lc i) ⊤)) : V) ≠
      ((M.β.symm p : ↥(commGL (Lc i) ⊤)) : V) := by
  intro heq
  apply h
  have h1 := M.actUnit_val hIE x₁ (M.β.symm p)
  rw [M.β.apply_symm_apply] at h1
  have h2 : resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) hIE x₁
      (M.β.symm p) = M.β.symm p := Subtype.ext (by rw [resSub_apply]; exact heq)
  rw [h1, h2, M.β.apply_symm_apply]

omit [Finite V] in
theorem DelModel.eq_one_or_gen (M : DelModel ctx i) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hAB : A ≤ blockB H (Lc i)) {x y : ℙ F (Fin 2 → F)}
    (hAxy : (A.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom = Subgroup.closure {Equiv.swap x y})
    {b₁ : ↥(blockB H (Lc i))} (hb₁ : M.ψ b₁ = Equiv.swap x y) :
    ∀ a ∈ A, a = 1 ∨ a = (b₁ : V ≃ₗ[ZMod 2] V) := by
  intro a ha
  have h1 := (M.mem_iff_image hAxy ⟨a, hAB ha⟩).1 ha
  rcases (mem_closure_swap _).1 h1 with h2 | h2
  · left
    have : (⟨a, hAB ha⟩ : ↥(blockB H (Lc i))) = 1 := M.ψ.injective (by rw [h2, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨a, hAB ha⟩ : ↥(blockB H (Lc i))) = b₁ := M.ψ.injective (by rw [h2, hb₁])
    exact congrArg Subtype.val this

omit [Finite V] in
theorem DelModel.actUnit_mk (M : DelModel ctx i) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hIE : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤))
    (b : ↥(blockB H (Lc i))) (hbX : (b : V ≃ₗ[ZMod 2] V) ∈ Lc i ⊔ E) :
    M.actUnit hIE ⟨b, hbX⟩ = permU (M.ψ b) :=
  M.actUnit_eq_permU hIE ⟨b, hbX⟩ b.2

theorem deleted_split_data (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ →
      DelData n (Lc i) A (ctx.α i))
    (M : DelModel ctx i) (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5)
    {A E : Subgroup (V ≃ₗ[ZMod 2] V)} (hA : IsMinOffender H A) (hmove : ⁅Lc i, A⁆ ≠ ⊥)
    (hE : IsOffender H E) (hAE : A ≤ E) :
    ∃ W : Submodule (ZMod 2) V, W ⊔ fixGL A = ⊤ ∧
      (∀ a ∈ A, (∀ w ∈ W, a w = w) → a = 1) ∧ (∀ e ∈ E, ∃ a ∈ A, ∀ w ∈ W, e w = a w) := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  have hEel : CFSG.IsElementaryAbelian 2 E := hE.2.2.1
  obtain ⟨hd, -⟩ := ctx.offd A hA i hmove
  have hEn := offender_le_normalizer ctx hA hmove hE hAE
  have hIE : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ E) (commGL (Lc i) ⊤) :=
    isInvariant_sup_subgroup hd.inv_L (isInvariant_commGL_of_le_normalizer hEn)
  obtain ⟨x, y, hxy, hAxy⟩ := M.single_transposition hdel hA hmove h5
  have hsw : Equiv.swap x y ∈ (A.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
    rw [hAxy]
    exact Subgroup.subset_closure (Set.mem_singleton _)
  obtain ⟨b₁, hb₁A, hb₁⟩ := hsw
  have hb₁' : M.ψ b₁ = Equiv.swap x y := hb₁
  have hb₁A' : (b₁ : V ≃ₗ[ZMod 2] V) ∈ A := hb₁A
  have hAeq : ∀ a ∈ A, a = 1 ∨ a = (b₁ : V ≃ₗ[ZMod 2] V) :=
    M.eq_one_or_gen (le_blockB_gen hA hmove) hAxy hb₁'
  have hkerD : LinearMap.ker (((b₁ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id) =
      fixGL A := ker_sub_id_eq_fixGL hb₁A' hAeq
  have hV : commGL (Lc i) ⊤ ⊔ LinearMap.ker
      (((b₁ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id) = ⊤ := by
    rw [hkerD]
    exact hd.V_split
  let ΨE : ↥E →* (Module.End (ZMod 2) ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))))ˣ :=
    (M.actUnit hIE).comp (Subgroup.inclusion (le_sup_right : E ≤ Lc i ⊔ E))
  let E' : Subgroup (Module.End (ZMod 2) ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))))ˣ :=
    ΨE.range
  have : CFSG.IsElementaryAbelian 2 E' := isElementaryAbelian_range ΨE
  have hEN : ∀ e ∈ E', ∀ σ ∈ alternatingGroup (ℙ F (Fin 2 → F)),
      ∃ σ' ∈ alternatingGroup (ℙ F (Fin 2 → F)), e * permU σ * e⁻¹ = permU σ' := by
    rintro _ ⟨⟨e₀, he₀⟩, rfl⟩ σ hσ
    rw [← M.alt] at hσ
    obtain ⟨b, hb, hbσ⟩ := hσ
    have hσ' : σ = M.ψ b := hbσ.symm
    subst hσ'
    have hbL : (b : V ≃ₗ[ZMod 2] V) ∈ Lc i := hb
    have hconjL : e₀ * (b : V ≃ₗ[ZMod 2] V) * e₀⁻¹ ∈ Lc i :=
      (Subgroup.mem_normalizer_iff.1 (hEn he₀) _).1 hbL
    have hconjB : e₀ * (b : V ≃ₗ[ZMod 2] V) * e₀⁻¹ ∈ blockB H (Lc i) :=
      Lc_le_blockB ctx i hconjL
    refine ⟨M.ψ ⟨_, hconjB⟩, ?_, ?_⟩
    · rw [← M.alt]
      exact ⟨⟨_, hconjB⟩, hconjL, rfl⟩
    · have e1 : ΨE ⟨e₀, he₀⟩ = M.actUnit hIE ⟨e₀, Subgroup.mem_sup_right he₀⟩ := rfl
      have e2 : permU (M.ψ b) = M.actUnit hIE ⟨b, Subgroup.mem_sup_left hbL⟩ :=
        (M.actUnit_eq_permU hIE ⟨b, Subgroup.mem_sup_left hbL⟩ b.2).symm
      have e3 : permU (M.ψ ⟨_, hconjB⟩) = M.actUnit hIE
          ⟨e₀ * (b : V ≃ₗ[ZMod 2] V) * e₀⁻¹, Subgroup.mem_sup_left hconjL⟩ :=
        (M.actUnit_eq_permU hIE ⟨_, Subgroup.mem_sup_left hconjL⟩ hconjB).symm
      rw [e1, e2, e3]
      have e4 : (⟨e₀ * (b : V ≃ₗ[ZMod 2] V) * e₀⁻¹, Subgroup.mem_sup_left hconjL⟩ : ↥(Lc i ⊔ E)) =
          ⟨e₀, Subgroup.mem_sup_right he₀⟩ * ⟨b, Subgroup.mem_sup_left hbL⟩ *
            ⟨e₀, Subgroup.mem_sup_right he₀⟩⁻¹ := Subtype.ext rfl
      rw [e4, map_mul, map_mul, map_inv]
  have ht : permU (Equiv.swap x y) ∈ E' := by
    refine ⟨⟨(b₁ : V ≃ₗ[ZMod 2] V), hAE hb₁A'⟩, ?_⟩
    show M.actUnit hIE ⟨(b₁ : V ≃ₗ[ZMod 2] V), Subgroup.mem_sup_right (hAE hb₁A')⟩ = _
    rw [M.actUnit_mk hIE b₁ _, hb₁']
  obtain ⟨⟨ω, hωx, hωy, hωfix⟩, hplane⟩ := deleted_five_transposition_plane h5 hxy E' hEN ht
  obtain ⟨-, hact2, hnt, -, -⟩ := hplane ω hωx hωy hωfix
  let Wp : Submodule (ZMod 2) ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))) :=
    Submodule.span (ZMod 2) {pairVec x ω, pairVec y ω}
  let W : Submodule (ZMod 2) V :=
    (Wp.map M.β.symm.toLinearMap).map (commGL (Lc i) ⊤).subtype
  have hWmem : ∀ p ∈ Wp, ((M.β.symm p : ↥(commGL (Lc i) ⊤)) : V) ∈ W := fun p hp =>
    ⟨M.β.symm p, ⟨p, hp, rfl⟩, rfl⟩
  have hWmem' : ∀ w ∈ W, ∃ p ∈ Wp, ((M.β.symm p : ↥(commGL (Lc i) ⊤)) : V) = w := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  have hnt' : ∃ w ∈ W, (b₁ : V ≃ₗ[ZMod 2] V) w ≠ w := by
    obtain ⟨p, hp, hpn⟩ := hnt
    refine ⟨_, hWmem p hp, M.act_ne_of_val_ne hIE
      ⟨(b₁ : V ≃ₗ[ZMod 2] V), Subgroup.mem_sup_right (hAE hb₁A')⟩ p ?_⟩
    rw [M.actUnit_mk hIE b₁ _, hb₁']
    exact hpn
  refine ⟨W, ?_, ?_, ?_⟩
  · rw [← hkerD]
    exact M.sup_ker_eq_top h5 hxy b₁.2 hb₁' hV hnt'
  · intro a ha hfix
    rcases hAeq a ha with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨w, hw, hne⟩ := hnt'
      rw [h1] at hfix
      exact hne (hfix w hw)
  · intro e he
    have hmem : ΨE ⟨e, he⟩ ∈ E' := ⟨⟨e, he⟩, rfl⟩
    rcases hact2 _ hmem with h | h
    · refine ⟨1, A.one_mem, fun w hw => ?_⟩
      obtain ⟨p, hp, rfl⟩ := hWmem' w hw
      have h1 : (M.actUnit hIE ⟨e, Subgroup.mem_sup_right he⟩).val p =
          (M.actUnit hIE 1).val p := by
        rw [map_one]
        exact h p hp
      exact M.act_eq_of_val_eq hIE _ _ p h1
    · refine ⟨(b₁ : V ≃ₗ[ZMod 2] V), hb₁A', fun w hw => ?_⟩
      obtain ⟨p, hp, rfl⟩ := hWmem' w hw
      have h1 : (M.actUnit hIE ⟨e, Subgroup.mem_sup_right he⟩).val p =
          (M.actUnit hIE ⟨(b₁ : V ≃ₗ[ZMod 2] V), Subgroup.mem_sup_right (hAE hb₁A')⟩).val p := by
        rw [M.actUnit_mk hIE b₁ _, hb₁']
        exact h p hp
      exact M.act_eq_of_val_eq hIE _ _ p h1

theorem deleted_offenderSplit (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i)) :
    OffenderSplit H := by
  intro A E hA hAE hE
  obtain ⟨-, i, hi, -⟩ := ctx.layer.offender A hA
  obtain ⟨M⟩ := nonempty_delModel ctx hdel i
  have h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5 := by
    rw [card_projectiveLine, ctx.hF, (hdel A hA i hi).1]
    norm_num
  obtain ⟨W, hV, hfaith, hact⟩ := deleted_split_data hdel M h5 hA hi hE hAE
  have hEw : weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E = Nat.card V :=
    le_antisymm (ctx.layer.upper_bound E hE.1 hE.2.1 hE.2.2.1) hE.2.2.2
  obtain ⟨D, hDE, hAD, hED, -, hDw⟩ :=
    split_offender hAE hE.2.2.1 (weight_eq_of_mem ctx hA) hEw hV hfaith hact
  refine ⟨D, hDE, hAD, hED, ?_⟩
  by_cases hD : D = ⊥
  · exact Or.inl hD
  · exact Or.inr ⟨hDE.trans hE.1, hD, isElementaryAbelian_of_le hDE hE.2.2.1, hDw.ge⟩

end DelSplit

end CFSG.QuasithinUnique.Setup.Lift
