module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyB

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Model

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem blockB_le_normalizer (ctx : FamilyCtx H T n F r Lc) (i : Fin r) :
    blockB H (Lc i) ≤ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) :=
  blockB_le_of fun A hA hmove => (ctx.offd A hA i hmove).1.A_norm

omit [Finite V] in
theorem blockB_isInvariant (ctx : FamilyCtx H T n F r Lc) (i : Fin r) :
    Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (blockB H (Lc i)) (commGL (Lc i) ⊤) := by
  intro b hb u hu
  have h1 : b u - u ∈ commGL (Lc i) ⊤ := blockB_le_trivMod ctx hb u
  have h2 : (MonoidHom.id (V ≃ₗ[ZMod 2] V)) b u = (b u - u) + u := by simp
  rw [h2]
  exact Submodule.add_mem _ h1 hu

theorem blockB_faithful (ctx : FamilyCtx H T n F r Lc) (i : Fin r) {b : V ≃ₗ[ZMod 2] V}
    (hb : b ∈ blockB H (Lc i)) (h : ∀ u ∈ commGL (Lc i) ⊤, b u = u) : b = 1 := by
  have hall : ∀ v : V, b v = v := by
    have hle : (⊤ : Submodule (ZMod 2) V) ≤
        LinearMap.ker ((b : V →ₗ[ZMod 2] V) - LinearMap.id) := by
      rw [← V_sum ctx]
      refine sup_le (iSup_le fun k => ?_) ?_
      · intro u hu
        rw [LinearMap.mem_ker]
        by_cases hk : k = i
        · subst hk
          exact sub_eq_zero.2 (h u hu)
        · exact sub_eq_zero.2 (blockB_le_centSub_I ctx hk hb u hu)
      · intro c hc
        rw [LinearMap.mem_ker]
        exact sub_eq_zero.2 (blockB_le_centSub_C ctx hb c hc)
    intro v
    have := hle (Submodule.mem_top : v ∈ ⊤)
    rw [LinearMap.mem_ker] at this
    exact sub_eq_zero.1 this
  exact LinearEquiv.ext hall

theorem exists_deleted_model (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (i : Fin r) :
    ∃ (ψ : ↥(blockB H (Lc i)) ≃* Equiv.Perm (ℙ F (Fin 2 → F)))
      (β : ↥(commGL (Lc i) ⊤) ≃ₗ[ZMod 2] ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))),
      (∀ (b : ↥(blockB H (Lc i))) (u u' : ↥(commGL (Lc i) ⊤)),
        (u' : V) = (b : V ≃ₗ[ZMod 2] V) (u : V) →
          ((β u' : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2) =
            SL2Modules.permAct (ψ b)
              ((β u : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) :
                ℙ F (Fin 2 → F) → ZMod 2)) ∧
      (∀ l : ↥(Lc i), ψ ⟨l, Lc_le_blockB ctx i l.2⟩ =
        MulAction.toPerm (thetaL (Lc i) (ctx.α i) l)) ∧
      ((Lc i).subgroupOf (blockB H (Lc i))).map ψ.toMonoidHom =
        alternatingGroup (ℙ F (Fin 2 → F)) := by
  classical
  obtain ⟨A₀, hA₀, hLA₀⟩ := ctx.layer.moving i
  have hmove₀ : ⁅Lc i, A₀⁆ ≠ ⊥ := by rw [hLA₀]; exact ctx.hLc.ne_bot i
  obtain ⟨hn2, -, hnle₀, β₀, ψ₀, hcomp₀, hψL₀, hAlt₀, -⟩ := hdel A₀ hA₀ i hmove₀
  have h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5 := by
    rw [card_projectiveLine, ctx.hF, hn2]; norm_num
  let θ : ↥(Lc i) →* SL(2, F) := thetaL (Lc i) (ctx.α i)
  have hθinj : Function.Injective θ := thetaL_injective (ctx.α i) (ctx.layer.center_trivial i)
  have hθsurj : Function.Surjective θ := by
    intro g
    obtain ⟨q, hq⟩ := (ctx.α i).surjective g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, hq⟩
  let θe : ↥(Lc i) ≃* SL(2, F) := MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  let π : SL(2, F) →* Equiv.Perm (ℙ F (Fin 2 → F)) :=
    MulAction.toPermHom SL(2, F) (ℙ F (Fin 2 → F))
  have hπ : π.range = alternatingGroup (ℙ F (Fin 2 → F)) := by
    rw [← hAlt₀]
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨l, rfl⟩ := hθsurj g
      exact ⟨⟨l, Subgroup.mem_sup_left l.2⟩, l.2, hψL₀ l⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨θ ⟨y, hy⟩, (hψL₀ ⟨y, hy⟩).symm⟩
  have hIB := blockB_isInvariant ctx i
  let ρB : ↥(blockB H (Lc i)) →* (↥(commGL (Lc i) ⊤) ≃ₗ[ZMod 2] ↥(commGL (Lc i) ⊤)) :=
    resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (blockB H (Lc i)) (commGL (Lc i) ⊤) hIB
  have hρB_apply : ∀ (b : ↥(blockB H (Lc i))) (u : ↥(commGL (Lc i) ⊤)),
      ((ρB b u : ↥(commGL (Lc i) ⊤)) : V) = (b : V ≃ₗ[ZMod 2] V) (u : V) :=
    fun b u => resSub_apply _ _ _ _ b u
  have hρB_inj : Function.Injective ρB := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine blockB_faithful ctx i b.2 fun u hu => ?_
    have := hρB_apply b ⟨u, hu⟩
    rw [hb] at this
    exact this.symm
  let ρU₁ : ↥(blockB H (Lc i)) →* (Module.End (ZMod 2) ↥(commGL (Lc i) ⊤))ˣ :=
    (unitsEquiv (ZMod 2) ↥(commGL (Lc i) ⊤)).symm.toMonoidHom.comp ρB
  have hρU₁_val : ∀ (b : ↥(blockB H (Lc i))) (u : ↥(commGL (Lc i) ⊤)),
      (ρU₁ b).val u = ρB b u := by
    intro b u
    rw [← unitsEquiv_apply]
    show (unitsEquiv (ZMod 2) _ ((unitsEquiv (ZMod 2) _).symm (ρB b))) u = ρB b u
    rw [MulEquiv.apply_symm_apply]
  have hρU₁_inj : Function.Injective ρU₁ := fun b b' h =>
    hρB_inj ((unitsEquiv (ZMod 2) ↥(commGL (Lc i) ⊤)).symm.injective h)
  let G : Subgroup (Module.End (ZMod 2) ↥(commGL (Lc i) ⊤))ˣ := ρU₁.range
  let ρU : SL(2, F) →* (Module.End (ZMod 2) ↥(commGL (Lc i) ⊤))ˣ :=
    ρU₁.comp ((Subgroup.inclusion (Lc_le_blockB ctx i)).comp θe.symm.toMonoidHom)
  have hρU_θ : ∀ l : ↥(Lc i), ρU (θ l) = ρU₁ ⟨l, Lc_le_blockB ctx i l.2⟩ := by
    intro l
    show ρU₁ (Subgroup.inclusion (Lc_le_blockB ctx i) (θe.symm (θe l))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hβ : ∀ (g : SL(2, F)) (w : ↥(commGL (Lc i) ⊤)),
      ((β₀ ((ρU g).val w) : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) :
          ℙ F (Fin 2 → F) → ZMod 2) =
        SL2Modules.permAct (π g)
          ((β₀ w : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2) := by
    intro g w
    obtain ⟨l, rfl⟩ := hθsurj g
    rw [hρU_θ l, hρU₁_val]
    have := hcomp₀ ⟨l, Subgroup.mem_sup_left l.2⟩ w
      (ρB ⟨l, Lc_le_blockB ctx i l.2⟩ w) (hρB_apply _ w)
    rw [hψL₀ l] at this
    exact this
  have hLG : ρU.range ≤ G := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  have hGN : ∀ y ∈ G, y ∈ Subgroup.normalizer
      (ρU.range : Set (Module.End (ZMod 2) ↥(commGL (Lc i) ⊤))ˣ) := by
    rintro _ ⟨b, rfl⟩
    have hbN : (b : V ≃ₗ[ZMod 2] V) ∈ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) :=
      blockB_le_normalizer ctx i b.2
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨l, rfl⟩ := hθsurj g
      have hl' : (b : V ≃ₗ[ZMod 2] V) * (l : V ≃ₗ[ZMod 2] V) * (b : V ≃ₗ[ZMod 2] V)⁻¹ ∈ Lc i :=
        (Subgroup.mem_normalizer_iff.1 hbN _).1 l.2
      refine ⟨θ ⟨_, hl'⟩, ?_⟩
      rw [hρU_θ, hρU_θ l, ← map_inv, ← map_mul, ← map_mul]
      rfl
    · rintro ⟨g, hg⟩
      obtain ⟨l, rfl⟩ := hθsurj g
      have hl' : (b : V ≃ₗ[ZMod 2] V)⁻¹ * (l : V ≃ₗ[ZMod 2] V) * (b : V ≃ₗ[ZMod 2] V) ∈ Lc i := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbN) (l : V ≃ₗ[ZMod 2] V)).1 l.2
        simpa using this
      refine ⟨θ ⟨_, hl'⟩, ?_⟩
      rw [hρU_θ l] at hg
      rw [hρU_θ]
      have hx : x = (ρU₁ b)⁻¹ * ρU₁ ⟨l, Lc_le_blockB ctx i l.2⟩ * ρU₁ b := by
        rw [hg]; group
      rw [hx, ← map_inv, ← map_mul, ← map_mul]
      rfl
  obtain ⟨ψ, hψinj, hψeq, hψext, hψsurj⟩ :=
    exists_sym_extension h5 β₀ π hπ ρU hβ G hLG hGN
  let ψB : ↥(blockB H (Lc i)) →* Equiv.Perm (ℙ F (Fin 2 → F)) := ψ.comp ρU₁.rangeRestrict
  have hrr_inj : Function.Injective ρU₁.rangeRestrict := fun b b' h =>
    hρU₁_inj (congrArg Subtype.val h)
  have hψB_inj : Function.Injective ψB := hψinj.comp hrr_inj
  have hψB_surj : Function.Surjective ψB := by
    have hex : ∃ y ∈ G, y ∉ ρU.range := by
      obtain ⟨a₀, ha₀, hnl⟩ := Set.not_subset.1 hnle₀
      refine ⟨ρU₁ ⟨a₀, le_blockB_gen hA₀ hmove₀ ha₀⟩, ⟨_, rfl⟩, ?_⟩
      rintro ⟨g, hg⟩
      have h1 : (Subgroup.inclusion (Lc_le_blockB ctx i) (θe.symm g) : ↥(blockB H (Lc i))) =
          ⟨a₀, le_blockB_gen hA₀ hmove₀ ha₀⟩ := hρU₁_inj hg
      apply hnl
      have h3 : ((θe.symm g : ↥(Lc i)) : V ≃ₗ[ZMod 2] V) = a₀ := congrArg Subtype.val h1
      exact h3 ▸ (θe.symm g).2
    have hs := hψsurj hex
    intro σ
    obtain ⟨y, rfl⟩ := hs σ
    obtain ⟨b, rfl⟩ := ρU₁.rangeRestrict_surjective y
    exact ⟨b, rfl⟩
  let ψe : ↥(blockB H (Lc i)) ≃* Equiv.Perm (ℙ F (Fin 2 → F)) :=
    MulEquiv.ofBijective ψB ⟨hψB_inj, hψB_surj⟩
  have hψe_L : ∀ l : ↥(Lc i), ψe ⟨l, Lc_le_blockB ctx i l.2⟩ =
      MulAction.toPerm (thetaL (Lc i) (ctx.α i) l) := by
    intro l
    have hmem : ρU (θ l) ∈ G := hLG ⟨θ l, rfl⟩
    have h1 : ρU₁.rangeRestrict ⟨l, Lc_le_blockB ctx i l.2⟩ = ⟨ρU (θ l), hmem⟩ :=
      Subtype.ext (hρU_θ l).symm
    show ψ (ρU₁.rangeRestrict ⟨l, Lc_le_blockB ctx i l.2⟩) = _
    rw [h1]
    exact hψext (θ l) hmem
  refine ⟨ψe, β₀, ?_, hψe_L, ?_⟩
  · intro b u u' hu'
    have h1 := hψeq (ρU₁.rangeRestrict b) u
    have hu'' : u' = ρB b u := Subtype.ext (by rw [hρB_apply]; exact hu')
    rw [hu'', ← hρU₁_val b u]
    exact h1
  · rw [← hπ]
    ext σ
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : V ≃ₗ[ZMod 2] V) ∈ Lc i := hy
      refine ⟨θ ⟨y, hy'⟩, ?_⟩
      have := hψe_L ⟨y, hy'⟩
      exact this.symm
    · rintro ⟨g, rfl⟩
      obtain ⟨l, rfl⟩ := hθsurj g
      exact ⟨⟨_, Lc_le_blockB ctx i l.2⟩, l.2, hψe_L l⟩

end Model

end CFSG.QuasithinUnique.Setup.Lift
