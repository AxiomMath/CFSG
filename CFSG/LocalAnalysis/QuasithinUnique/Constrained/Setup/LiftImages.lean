module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftImageDel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftImageNat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMax

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ABGLocalTools
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Defs

variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

structure EvenSL2ImagesActor (H T D S : Subgroup (W ≃ₗ[ZMod 2] W)) (n : ℕ) (F : Type) [Field F]
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] (r : ℕ)
    (Lc : Fin r → Subgroup (W ≃ₗ[ZMod 2] W)) : Prop where
  V_eq : commGL (oddGen H) ⊤ ⊔ fixGL (oddGen H) = ⊤
  baumann_eq : D = S
  natural : NaturalFamily H F r Lc → D = ⨆ i, T ⊓ Lc i ∧ IsSylowTwoOf D (oddGen H) ∧
    fixGL D = (⨆ i, commGL (Lc i) ⊤ ⊓ fixGL (T ⊓ Lc i)) ⊔ fixGL (oddGen H) ∧
    Nat.card W = 2 ^ (n * r) * Nat.card ↥(fixGL D)
  deleted : DeletedFamily H n r Lc → ¬ D ≤ oddGen H ∧
    Nat.card W = 2 ^ (2 * r) * Nat.card ↥(fixGL D) ∧
    ∃ (ψ : ∀ i, ↥(blockB H (Lc i)) ≃* Equiv.Perm (ℙ F (Fin 2 → F)))
      (β : ∀ i, ↥(commGL (Lc i) ⊤) ≃ₗ[ZMod 2] ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))))
      (A : Fin r → Subgroup (W ≃ₗ[ZMod 2] W)),
      Fintype.card (ℙ F (Fin 2 → F)) = 5 ∧ D = ⨆ i, A i ∧
      ∀ i, (∀ (b : ↥(blockB H (Lc i))) (u u' : ↥(commGL (Lc i) ⊤)),
          (u' : W) = (b : W ≃ₗ[ZMod 2] W) (u : W) →
            ((β i u' : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2) =
              permAct (ψ i b)
                ((β i u : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2)) ∧
        ((Lc i).subgroupOf (blockB H (Lc i))).map (ψ i).toMonoidHom =
          alternatingGroup (ℙ F (Fin 2 → F)) ∧
        A i ≤ T ⊓ blockB H (Lc i) ∧
        ∃ a b c d ω : ℙ F (Fin 2 → F), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
          ω ≠ a ∧ ω ≠ b ∧ ω ≠ c ∧ ω ≠ d ∧
          ((A i).subgroupOf (blockB H (Lc i))).map (ψ i).toMonoidHom =
            Subgroup.closure {Equiv.swap a b, Equiv.swap c d} ∧
          (∀ σ ∈ ((T ⊓ blockB H (Lc i)).subgroupOf (blockB H (Lc i))).map (ψ i).toMonoidHom,
            σ ω = ω) ∧
          ∀ u v : ℙ F (Fin 2 → F), u ≠ v →
            Equiv.swap u v ∈ ((T ⊓ blockB H (Lc i)).subgroupOf (blockB H (Lc i))).map
              (ψ i).toMonoidHom → Equiv.swap u v = Equiv.swap a b ∨ Equiv.swap u v = Equiv.swap c d

end Defs

section Tools

theorem natCard_closure_two_swaps {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {a b c d : Ω}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Nat.card (Subgroup.closure {Equiv.swap a b, Equiv.swap c d}) = 4 := by
  have hcl : Subgroup.closure {Equiv.swap a b, Equiv.swap c d} =
      Subgroup.closure {Equiv.swap a b} ⊔ Subgroup.closure {Equiv.swap c d} := by
    rw [← Subgroup.closure_union, Set.singleton_union]
  have hcomm : ∀ x ∈ Subgroup.closure {Equiv.swap a b}, ∀ y ∈ Subgroup.closure {Equiv.swap c d},
      x * y = y * x := by
    intro x hx y hy
    rw [mem_closure_swap] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp
    · simp
    · simp
    · exact ((swap_disjoint hac had hbc hbd).commute).eq
  have hdisj : Disjoint (Subgroup.closure {Equiv.swap a b}) (Subgroup.closure {Equiv.swap c d}) := by
    rw [Subgroup.disjoint_def]
    intro x hx hy
    rw [mem_closure_swap] at hx hy
    rcases hx with h | h
    · exact h
    · exfalso
      rcases hy with h' | h'
      · exact swap_ne_one hab (h.symm.trans h')
      · have h2 := congrArg (fun π : Equiv.Perm Ω => π a) (h.symm.trans h')
        simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac had] at h2
        exact hab h2.symm
  rw [hcl, natCard_sup_of_commute_of_disjoint hcomm hdisj, natCard_closure_swap hab,
    natCard_closure_swap hcd]

end Tools

section Main

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}
  {ctx : FamilyCtx H T n F r Lc} {i : Fin r}

theorem DelModel.not_le_oddGen (M : DelModel ctx i) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    {a b : ℙ F (Fin 2 → F)} (hab : a ≠ b) (hX : Equiv.swap a b ∈ delImage M X) :
    ¬ X ≤ oddGen H := by
  intro hK
  obtain ⟨x, hxX, hxψ⟩ := (mem_delImage M).1 hX
  have hxK : (x : V ≃ₗ[ZMod 2] V) ∈ oddGen H := hK hxX
  have hKeq : oddGen H = Lc i ⊔ ⨆ j, ⨆ (_ : j ≠ i), Lc j := by
    rw [ctx.layer.K_eq]
    apply le_antisymm
    · refine iSup_le fun k => ?_
      by_cases hk : k = i
      · rw [hk]
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le k hk le_rfl)
    · exact sup_le (le_iSup Lc i) (iSup₂_le fun j _ => le_iSup Lc j)
  rw [hKeq] at hxK
  have hoth : (⨆ j, ⨆ (_ : j ≠ i), Lc j) ≤ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V))
      (commGL (Lc i) ⊤) :=
    iSup₂_le fun j hj z hz => mem_centSub.2 fun v hv => ctx.layer.others_fix i j hj z hz v hv
  have hcomm : ∀ l ∈ Lc i, ∀ d ∈ (⨆ j, ⨆ (_ : j ≠ i), Lc j), l * d = d * l := by
    intro l hl d hd
    have : (⨆ j, ⨆ (_ : j ≠ i), Lc j) ≤ Subgroup.centralizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) :=
      iSup₂_le fun j hj z hz => Subgroup.mem_centralizer_iff.2 fun l' hl' =>
        ctx.hLc.elem_commute (Ne.symm hj) l' hl' z hz
    exact Subgroup.mem_centralizer_iff.1 (this hd) l hl
  obtain ⟨l, hl, m, hm, hxlm⟩ := exists_mul_of_mem_sup_of_commute hcomm hxK
  have hmfix : ∀ u ∈ commGL (Lc i) ⊤, m u = u := fun u hu => mem_centSub.1 (hoth hm) u hu
  have hlB : l ∈ blockB H (Lc i) := Lc_le_blockB ctx i hl
  have hb : l⁻¹ * (x : V ≃ₗ[ZMod 2] V) ∈ blockB H (Lc i) :=
    (blockB H (Lc i)).mul_mem ((blockB H (Lc i)).inv_mem hlB) x.2
  have hfix : ∀ u ∈ commGL (Lc i) ⊤, (l⁻¹ * (x : V ≃ₗ[ZMod 2] V)) u = u := by
    intro u hu
    rw [hxlm, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hmfix u hu]
    exact ρ_inv_apply (MonoidHom.id (V ≃ₗ[ZMod 2] V)) l u
  have h1 : l⁻¹ * (x : V ≃ₗ[ZMod 2] V) = 1 := blockB_faithful ctx i hb hfix
  have hxl : (x : V ≃ₗ[ZMod 2] V) = l := by
    have := congrArg (l * ·) h1
    simpa using this
  have hxL : (x : V ≃ₗ[ZMod 2] V) ∈ Lc i := by rw [hxl]; exact hl
  have hψx : M.ψ x ∈ alternatingGroup (ℙ F (Fin 2 → F)) := by
    rw [← M.alt]
    exact ⟨x, hxL, rfl⟩
  have hψx' : M.ψ x = Equiv.swap a b := hxψ
  rw [hψx', Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hab] at hψx
  exact absurd hψx (by decide)

theorem V_eq_of_ctx (ctx : FamilyCtx H T n F r Lc) :
    commGL (oddGen H) ⊤ ⊔ fixGL (oddGen H) = ⊤ := by
  have hLK : ∀ i, Lc i ≤ oddGen H := fun i => by
    rw [ctx.layer.K_eq]
    exact le_iSup Lc i
  refine top_le_iff.1 ?_
  calc (⊤ : Submodule (ZMod 2) V)
      = (⨆ i, commGL (Lc i) ⊤) ⊔ fixGL (oddGen H) := (V_sum ctx).symm
    _ ≤ commGL (oddGen H) ⊤ ⊔ fixGL (oddGen H) :=
      sup_le_sup_right (iSup_le fun i => commSub_mono_left _ (hLK i)) _

omit [Finite V] in
theorem weight_eq_of_offender (ctx : FamilyCtx H T n F r Lc) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : IsOffender H E) : Offender.weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E = Nat.card V :=
  le_antisymm (ctx.layer.upper_bound E hE.1 hE.2.1 hE.2.2.1) hE.2.2.2

theorem images_actor_natural (ctx : FamilyCtx H T n F r Lc) (hT : IsSylowTwoOf T H)
    (hU : ∀ i, IsSylowTwoOf (T ⊓ Lc i) (Lc i))
    (hDeq : T ⊓ oddGen H = ⨆ i, T ⊓ Lc i)
    (𝓔 : Set (Subgroup (V ≃ₗ[ZMod 2] V)))
    (hE : ∀ E ∈ 𝓔, E ≤ T ∧ (E = ⊥ ∨ IsOffender H E))
    (hDn : ((⨆ E ∈ 𝓔, E).subgroupOf T).Normal) (hne : (⨆ E ∈ 𝓔, E) ≠ ⊥)
    (S : Subgroup (V ≃ₗ[ZMod 2] V)) (hDS : (⨆ E ∈ 𝓔, E) ≤ S) (hST : S ≤ T)
    (hSfix : ∀ s ∈ S, ∀ v ∈ fixGL (⨆ E ∈ 𝓔, E), s v = v)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i) :
    EvenSL2ImagesActor H T (⨆ E ∈ 𝓔, E) S n F r Lc := by
  classical
  have hTp : IsPGroup 2 ↥T := hT.2.1
  have hnat := natural_family ctx hglob
  have hDnat := natural_thompson_image ctx hnat hU 𝓔 hE hDn hne
  have hSD : S ≤ ⨆ E ∈ 𝓔, E := by
    intro s hs
    rw [hDnat]
    rw [hDnat] at hSfix
    exact natural_baumann ctx hnat hTp hU (hST hs) (hSfix s hs)
  refine ⟨V_eq_of_ctx ctx, le_antisymm hDS hSD, fun _ => ⟨hDnat, ?_, ?_, ?_⟩,
    fun hdel => (not_natural_and_deleted ctx hnat hdel).elim⟩
  · rw [hDnat, ← hDeq]
    refine isSylowTwoOf_of_isSylowOf ?_
    exact (isSylowOf_two_of hT).inf_of_le_normalizer (oddGen_le_self H)
      (fun h hh => mem_normalizer_oddGen ctx hh)
  · rw [hDnat]
    exact natural_fixGL ctx
  · have hw := (natural_iSup_weight ctx hglob (fun i => T ⊓ Lc i) Finset.univ
      (fun i _ => hU i)).2.1
    have hunivEq : (⨆ i ∈ (Finset.univ : Finset (Fin r)), T ⊓ Lc i) = ⨆ i, T ⊓ Lc i := by simp
    rw [hunivEq] at hw
    have hc := natCard_natural_D ctx hnat hU
    rw [hDnat]
    rw [ctx.hF, ← pow_mul] at hc
    unfold Offender.weight at hw
    rw [hc] at hw
    exact hw.symm

theorem delA_family_facts (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (a b c d : Fin r → ℙ F (Fin 2 → F))
    (hab : ∀ i, a i ≠ b i) (hac : ∀ i, a i ≠ c i) (had : ∀ i, a i ≠ d i) (hbc : ∀ i, b i ≠ c i)
    (hbd : ∀ i, b i ≠ d i) (hcd : ∀ i, c i ≠ d i)
    (himg : ∀ i, ((delA (delModelOf ctx hdel i)).subgroupOf (blockB H (Lc i))).map
      (delModelOf ctx hdel i).ψ.toMonoidHom = Subgroup.closure {Equiv.swap (a i) (b i),
        Equiv.swap (c i) (d i)}) :
    Nat.card ↥(⨆ i, delA (delModelOf ctx hdel i)) = 2 ^ (2 * r) ∧
      IsOffender H (⨆ i, delA (delModelOf ctx hdel i)) := by
  classical
  have hAB : ∀ i, delA (delModelOf ctx hdel i) ≤ blockB H (Lc i) := fun i =>
    (delA_le _).trans inf_le_right
  have hcardA : ∀ i, Nat.card ↥(delA (delModelOf ctx hdel i)) = 4 := fun i => by
    have h1 : Nat.card ↥(delA (delModelOf ctx hdel i)) =
        Nat.card ↥((delA (delModelOf ctx hdel i)).subgroupOf (blockB H (Lc i))) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAB i)).toEquiv).symm
    rw [h1, ← Subgroup.card_map_of_injective (f := (delModelOf ctx hdel i).ψ.toMonoidHom)
      (delModelOf ctx hdel i).ψ.injective, himg i]
    exact natCard_closure_two_swaps (hab i) (hac i) (had i) (hbc i) (hbd i) (hcd i)
  refine ⟨?_, ?_⟩
  · have := natCard_iSup_of_le (fun i => blockB H (Lc i)) (fun i => delA (delModelOf ctx hdel i))
      hAB (fun i j hij => blockB_comm ctx hij) (blockB_direct ctx) hcardA Finset.univ
    have hunivEq : (⨆ i ∈ (Finset.univ : Finset (Fin r)), delA (delModelOf ctx hdel i)) =
        ⨆ i, delA (delModelOf ctx hdel i) := by simp
    rw [hunivEq, Finset.card_univ, Fintype.card_fin] at this
    rw [this, pow_mul]
    norm_num
  · refine (deleted_offender_iff ctx hdel _).2 ⟨Finset.univ,
      fun i => delA (delModelOf ctx hdel i), ⟨⟨0, ctx.layer.r_pos⟩, Finset.mem_univ _⟩,
      fun i _ => ⟨hAB i, Or.inr ⟨a i, b i, c i, d i, hab i, hac i, had i, hbc i, hbd i, hcd i,
        himg i⟩⟩, ?_⟩
    simp

theorem images_actor_deleted (ctx : FamilyCtx H T n F r Lc)
    (hQ : ∀ i, IsSylowTwoOf (T ⊓ blockB H (Lc i)) (blockB H (Lc i)))
    (𝓔 : Set (Subgroup (V ≃ₗ[ZMod 2] V)))
    (hE : ∀ E ∈ 𝓔, E ≤ T ∧ (E = ⊥ ∨ IsOffender H E))
    (hDn : ((⨆ E ∈ 𝓔, E).subgroupOf T).Normal) (hne : (⨆ E ∈ 𝓔, E) ≠ ⊥)
    (S : Subgroup (V ≃ₗ[ZMod 2] V)) (hDS : (⨆ E ∈ 𝓔, E) ≤ S) (hST : S ≤ T)
    (hSfix : ∀ s ∈ S, ∀ v ∈ fixGL (⨆ E ∈ 𝓔, E), s v = v)
    (hglob : ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → ¬ A ≤ Lc i) :
    EvenSL2ImagesActor H T (⨆ E ∈ 𝓔, E) S n F r Lc := by
  classical
  have hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i) :=
    fun A hA i hmove => (alt_dichotomy ctx hA i hmove).resolve_left fun hN =>
      hglob i A hA hmove hN.1
  have hdelF := deleted_family ctx hdel
  have h5 := card_five_of_deleted ctx hdel
  obtain ⟨hD, hstruct⟩ := deleted_thompson_image ctx hdel hQ 𝓔 hE hDn hne
  have hSD : S ≤ ⨆ E ∈ 𝓔, E := by
    intro s hs
    rw [hD]
    rw [hD] at hSfix
    refine deleted_baumann ctx hdelF.Z_bot h5 (fun i => delModelOf ctx hdel i)
      (fun i => delA (delModelOf ctx hdel i)) (fun i => (delA_le _).trans inf_le_right)
      (fun i => ?_) (hST hs) (hSfix s hs)
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, himg, -⟩ := hstruct i
    exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, himg⟩
  choose a b c d hab hac had hbc hbd hcd himg hall ω hωa hωb hωc hωd hωP using hstruct
  obtain ⟨hcardD, hoffD⟩ := delA_family_facts ctx hdel a b c d hab hac had hbc hbd hcd himg
  have hnotK : ¬ (⨆ E ∈ 𝓔, E) ≤ oddGen H := by
    intro hK
    have hmem : Equiv.swap (a ⟨0, ctx.layer.r_pos⟩) (b ⟨0, ctx.layer.r_pos⟩) ∈
        ((delA (delModelOf ctx hdel ⟨0, ctx.layer.r_pos⟩)).subgroupOf
          (blockB H (Lc ⟨0, ctx.layer.r_pos⟩))).map
          (delModelOf ctx hdel ⟨0, ctx.layer.r_pos⟩).ψ.toMonoidHom := by
      rw [himg ⟨0, ctx.layer.r_pos⟩]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    obtain ⟨x, hx, hxσ⟩ := hmem
    have hxD : (x : V ≃ₗ[ZMod 2] V) ∈ ⨆ i, delA (delModelOf ctx hdel i) :=
      Subgroup.mem_iSup_of_mem (⟨0, ctx.layer.r_pos⟩ : Fin r) (Subgroup.mem_subgroupOf.1 hx)
    rw [← hD] at hxD
    exact (delModelOf ctx hdel ⟨0, ctx.layer.r_pos⟩).not_le_oddGen (hab ⟨0, ctx.layer.r_pos⟩)
      ((mem_delImage _).2 ⟨x, hxD, hxσ⟩) hK
  have hoffD' : IsOffender H (⨆ E ∈ 𝓔, E) := by
    rw [hD]
    exact hoffD
  have hcardD' : Nat.card ↥(⨆ E ∈ 𝓔, E) = 2 ^ (2 * r) := by
    rw [hD]
    exact hcardD
  have hw := weight_eq_of_offender ctx hoffD'
  unfold Offender.weight at hw
  rw [hcardD'] at hw
  refine ⟨V_eq_of_ctx ctx, le_antisymm hDS hSD,
    fun hnat => (not_natural_and_deleted ctx hnat hdelF).elim,
    fun _ => ⟨hnotK, hw.symm, fun i => (delModelOf ctx hdel i).ψ,
      fun i => (delModelOf ctx hdel i).β, fun i => delA (delModelOf ctx hdel i), h5, hD,
      fun i => ⟨(delModelOf ctx hdel i).compat, (delModelOf ctx hdel i).alt, delA_le _, a i, b i,
        c i, d i, ω i, hab i, hac i, had i, hbc i, hbd i, hcd i, hωa i, hωb i, hωc i, hωd i,
        himg i, hωP i, hall i⟩⟩⟩

theorem even_SL2_images_actor (ctx : FamilyCtx H T n F r Lc) (hT : IsSylowTwoOf T H)
    (hU : ∀ i, IsSylowTwoOf (T ⊓ Lc i) (Lc i))
    (hQ : ∀ i, IsSylowTwoOf (T ⊓ blockB H (Lc i)) (blockB H (Lc i)))
    (hDeq : T ⊓ oddGen H = ⨆ i, T ⊓ Lc i)
    (𝓔 : Set (Subgroup (V ≃ₗ[ZMod 2] V)))
    (hE : ∀ E ∈ 𝓔, E ≤ T ∧ (E = ⊥ ∨ IsOffender H E))
    (hDn : ((⨆ E ∈ 𝓔, E).subgroupOf T).Normal) (hne : (⨆ E ∈ 𝓔, E) ≠ ⊥)
    (S : Subgroup (V ≃ₗ[ZMod 2] V)) (hDS : (⨆ E ∈ 𝓔, E) ≤ S) (hST : S ≤ T)
    (hSfix : ∀ s ∈ S, ∀ v ∈ fixGL (⨆ E ∈ 𝓔, E), s v = v) :
    EvenSL2ImagesActor H T (⨆ E ∈ 𝓔, E) S n F r Lc := by
  rcases global_alt ctx with hglob | hglob
  · exact images_actor_natural ctx hT hU hDeq 𝓔 hE hDn hne S hDS hST hSfix hglob
  · exact images_actor_deleted ctx hQ 𝓔 hE hDn hne S hDS hST hSfix hglob

end Main

end CFSG.QuasithinUnique.Setup.Lift
