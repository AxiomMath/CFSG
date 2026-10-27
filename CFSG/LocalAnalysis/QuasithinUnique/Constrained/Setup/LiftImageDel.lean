module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxDel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderDelClass
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSylow5

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ABGLocalTools
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Image

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}
  {ctx : FamilyCtx H T n F r Lc} {i : Fin r}

@[expose] def delImage (M : DelModel ctx i) (X : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Subgroup (Equiv.Perm (ℙ F (Fin 2 → F))) :=
  (X.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom

omit [Finite V] in
theorem mem_delImage (M : DelModel ctx i) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    {σ : Equiv.Perm (ℙ F (Fin 2 → F))} :
    σ ∈ delImage M X ↔ ∃ b : ↥(blockB H (Lc i)), (b : V ≃ₗ[ZMod 2] V) ∈ X ∧ M.ψ b = σ :=
  Subgroup.mem_map

omit [Finite V] in
theorem delImage_mono (M : DelModel ctx i) {X Y : Subgroup (V ≃ₗ[ZMod 2] V)} (h : X ≤ Y) :
    delImage M X ≤ delImage M Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem DelModel.card_image_sylow (M : DelModel ctx i)
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5)
    (hQ : IsSylowTwoOf (T ⊓ blockB H (Lc i)) (blockB H (Lc i))) :
    Nat.card (delImage M (T ⊓ blockB H (Lc i))) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsSylowOf 2 ((T ⊓ blockB H (Lc i)).subgroupOf (blockB H (Lc i))) ⊤ := by
    refine (isSylowOf_map_subtype_iff (p := 2) (blockB H (Lc i))
      (A := (T ⊓ blockB H (Lc i)).subgroupOf (blockB H (Lc i))) (B := ⊤)).1 ?_
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right, map_top_subtype]
    exact isSylowOf_two_of hQ
  have h2 := isSylowOf_map hQ' M.ψ.toMonoidHom
  rw [Subgroup.map_top, MonoidHom.range_eq_top.2 M.ψ.surjective] at h2
  exact card_sylow_sym_five h5 h2

@[expose] def delTr (M : DelModel ctx i) : Set (Equiv.Perm (ℙ F (Fin 2 → F))) :=
  {σ | σ ∈ delImage M (T ⊓ blockB H (Lc i)) ∧ ∃ u v : ℙ F (Fin 2 → F), u ≠ v ∧ σ = Equiv.swap u v}

@[expose] noncomputable def delA (M : DelModel ctx i) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  ((Subgroup.closure (delTr M)).comap M.ψ.toMonoidHom).map (blockB H (Lc i)).subtype

omit [Finite V] in
theorem mem_delA (M : DelModel ctx i) (b : ↥(blockB H (Lc i))) :
    (b : V ≃ₗ[ZMod 2] V) ∈ delA M ↔ M.ψ b ∈ Subgroup.closure (delTr M) := by
  constructor
  · rintro ⟨b', hb', hbb⟩
    have : b' = b := Subtype.ext hbb
    subst this
    exact hb'
  · intro hb
    exact ⟨b, hb, rfl⟩

omit [Finite V] in
theorem delA_image (M : DelModel ctx i) :
    ((delA M).subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom = Subgroup.closure (delTr M) := by
  have h1 : (delA M).subgroupOf (blockB H (Lc i)) =
      (Subgroup.closure (delTr M)).comap M.ψ.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (blockB H (Lc i)).subtype_injective _
  rw [h1]
  exact Subgroup.map_comap_eq_self_of_surjective M.ψ.surjective _

omit [Finite V] in
theorem delA_le (M : DelModel ctx i) : delA M ≤ T ⊓ blockB H (Lc i) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hbP : M.ψ b ∈ delImage M (T ⊓ blockB H (Lc i)) :=
    (Subgroup.closure_le _).2 (fun σ hσ => hσ.1) hb
  refine ⟨?_, b.2⟩
  exact (M.mem_iff_image (X := T ⊓ blockB H (Lc i)) (K := delImage M (T ⊓ blockB H (Lc i)))
    rfl b).2 hbP |>.1

end Image

section Main

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

theorem deleted_thompson_image (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (hQ : ∀ i, IsSylowTwoOf (T ⊓ blockB H (Lc i)) (blockB H (Lc i)))
    (𝓔 : Set (Subgroup (V ≃ₗ[ZMod 2] V)))
    (hE : ∀ E ∈ 𝓔, E ≤ T ∧ (E = ⊥ ∨ IsOffender H E))
    (hDn : ((⨆ E ∈ 𝓔, E).subgroupOf T).Normal) (hne : (⨆ E ∈ 𝓔, E) ≠ ⊥) :
    (⨆ E ∈ 𝓔, E) = ⨆ i, delA (delModelOf ctx hdel i) ∧
      ∀ i, ∃ a b c d : ℙ F (Fin 2 → F), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        ((delA (delModelOf ctx hdel i)).subgroupOf (blockB H (Lc i))).map
          (delModelOf ctx hdel i).ψ.toMonoidHom = Subgroup.closure {Equiv.swap a b, Equiv.swap c d} ∧
        (∀ u v : ℙ F (Fin 2 → F), u ≠ v →
          Equiv.swap u v ∈ delImage (delModelOf ctx hdel i) (T ⊓ blockB H (Lc i)) →
          Equiv.swap u v = Equiv.swap a b ∨ Equiv.swap u v = Equiv.swap c d) ∧
        ∃ ω : ℙ F (Fin 2 → F), ω ≠ a ∧ ω ≠ b ∧ ω ≠ c ∧ ω ≠ d ∧
          ∀ σ ∈ delImage (delModelOf ctx hdel i) (T ⊓ blockB H (Lc i)), σ ω = ω := by
  classical
  have h5 := card_five_of_deleted ctx hdel
  set D : Subgroup (V ≃ₗ[ZMod 2] V) := ⨆ E ∈ 𝓔, E with hDdef
  have hDT : D ≤ T := iSup₂_le fun E hE' => (hE E hE').1
  have hXP : ∀ i, delImage (delModelOf ctx hdel i) D ≤
      delImage (delModelOf ctx hdel i) (T ⊓ blockB H (Lc i)) := fun i =>
    Subgroup.map_mono (fun b hb => ⟨hDT hb, b.2⟩)
  have hP8 : ∀ i, Nat.card (delImage (delModelOf ctx hdel i) (T ⊓ blockB H (Lc i))) = 8 :=
    fun i => (delModelOf ctx hdel i).card_image_sylow h5 (hQ i)
  obtain ⟨E, hE', hE0⟩ : ∃ E ∈ 𝓔, E ≠ ⊥ := by
    by_contra hno
    push Not at hno
    apply hne
    refine le_bot_iff.1 (iSup₂_le fun E hE' => ?_)
    rw [hno E hE']
  have hoff : IsOffender H E := ((hE E hE').2).resolve_left hE0
  obtain ⟨I, U, hI, hUT, hEeq⟩ := (deleted_offender_iff ctx hdel E).1 hoff
  obtain ⟨i0, hi0⟩ := hI
  have hED : E ≤ D := le_iSup₂_of_le E hE' le_rfl
  have hUE : ∀ i ∈ I, U i ≤ E := fun i hi => hEeq ▸ le_iSup₂_of_le i hi le_rfl
  have hswap : ∀ j, ∃ x y : ℙ F (Fin 2 → F), x ≠ y ∧
      Equiv.swap x y ∈ delImage (delModelOf ctx hdel j) D := by
    obtain ⟨hUB, hshape⟩ := hUT i0 hi0
    obtain ⟨x, y, hxy, hsw⟩ : ∃ x y : ℙ F (Fin 2 → F), x ≠ y ∧
        Equiv.swap x y ∈ delImage (delModelOf ctx hdel i0) (U i0) := by
      rcases hshape with ⟨x, y, hxy, h⟩ | ⟨x, y, z, t, hxy, -, -, -, -, -, h⟩
      · refine ⟨x, y, hxy, ?_⟩
        show Equiv.swap x y ∈ ((U i0).subgroupOf (blockB H (Lc i0))).map
          (delModelOf ctx hdel i0).ψ.toMonoidHom
        rw [h]
        exact Subgroup.subset_closure (Set.mem_singleton _)
      · refine ⟨x, y, hxy, ?_⟩
        show Equiv.swap x y ∈ ((U i0).subgroupOf (blockB H (Lc i0))).map
          (delModelOf ctx hdel i0).ψ.toMonoidHom
        rw [h]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
    have hK0le : Subgroup.closure {Equiv.swap x y} ≤ delImage (delModelOf ctx hdel i0) (U i0) := by
      rw [Subgroup.closure_le]
      intro σ hσ
      rw [Set.mem_singleton_iff] at hσ
      rw [hσ]
      exact hsw
    have hA0img := (delModelOf ctx hdel i0).sub_image hK0le
    have hA0U : (U i0 ⊓ ((Subgroup.closure {Equiv.swap x y}).comap
        (delModelOf ctx hdel i0).ψ.toMonoidHom).map (blockB H (Lc i0)).subtype) ≤ U i0 := inf_le_left
    set A0 : Subgroup (V ≃ₗ[ZMod 2] V) := U i0 ⊓ ((Subgroup.closure {Equiv.swap x y}).comap
        (delModelOf ctx hdel i0).ψ.toMonoidHom).map (blockB H (Lc i0)).subtype with hA0
    have hA0B : A0 ≤ blockB H (Lc i0) := hA0U.trans hUB
    have hA0D : A0 ≤ D := hA0U.trans ((hUE i0 hi0).trans hED)
    have hA0P := ((delModelOf ctx hdel i0).pmem_iff hdel h5 A0).2 ⟨x, y, hxy, hA0B, hA0img⟩
    intro j
    obtain ⟨t, ht, hconjL⟩ := ctx.layer.transitive i0 j
    have htH : t ∈ H := T_le_H ctx ht
    have hA0'P : IsMinOffender H (conjSub t A0) ∧ ⁅Lc j, conjSub t A0⁆ ≠ ⊥ := by
      refine ⟨hA0P.1.conj htH, ?_⟩
      have h1 : conjSub t (Lc i0) = Lc j := hconjL
      rw [← h1, conjSub_commutator]
      intro hbot
      apply hA0P.2
      exact (conjSub t).injective (hbot.trans (conjSub t).map_bot.symm)
    obtain ⟨x', y', hxy', hA0'B, hA0'img⟩ :=
      ((delModelOf ctx hdel j).pmem_iff hdel h5 (conjSub t A0)).1 hA0'P
    have hA0'D : conjSub t A0 ≤ D := by
      intro a ha
      rw [mem_conjSub] at ha
      have hzT : t⁻¹ * a * t ∈ T := hDT (hA0D ha)
      have hzD : (⟨t⁻¹ * a * t, hzT⟩ : ↥T) ∈ D.subgroupOf T := hA0D ha
      have h2 := hDn.conj_mem ⟨t⁻¹ * a * t, hzT⟩ hzD ⟨t, ht⟩
      have h3 : t * (t⁻¹ * a * t) * t⁻¹ ∈ D := h2
      have h4 : t * (t⁻¹ * a * t) * t⁻¹ = a := by group
      rwa [h4] at h3
    refine ⟨x', y', hxy', ?_⟩
    have hmem : Equiv.swap x' y' ∈ ((conjSub t A0).subgroupOf (blockB H (Lc j))).map
        (delModelOf ctx hdel j).ψ.toMonoidHom := by
      rw [hA0'img]
      exact Subgroup.subset_closure (Set.mem_singleton _)
    obtain ⟨b, hb, hbσ⟩ := hmem
    exact (mem_delImage _).2 ⟨b, hA0'D hb, hbσ⟩
  have hstruct : ∀ j, ∃ (a b c d ω : ℙ F (Fin 2 → F)) (q : Equiv.Perm (ℙ F (Fin 2 → F))),
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ ω ≠ a ∧ ω ≠ b ∧ ω ≠ c ∧ ω ≠ d ∧
      (∀ σ ∈ delImage (delModelOf ctx hdel j) (T ⊓ blockB H (Lc j)), σ ω = ω) ∧
      Equiv.swap a b ∈ delImage (delModelOf ctx hdel j) (T ⊓ blockB H (Lc j)) ∧
      Equiv.swap c d ∈ delImage (delModelOf ctx hdel j) (T ⊓ blockB H (Lc j)) ∧
      q ∈ delImage (delModelOf ctx hdel j) (T ⊓ blockB H (Lc j)) ∧
      q * Equiv.swap a b * q⁻¹ = Equiv.swap c d ∧
      (∀ u v : ℙ F (Fin 2 → F), u ≠ v →
        Equiv.swap u v ∈ delImage (delModelOf ctx hdel j) (T ⊓ blockB H (Lc j)) →
        Equiv.swap u v = Equiv.swap a b ∨ Equiv.swap u v = Equiv.swap c d) ∧
      Equiv.swap a b ∈ delImage (delModelOf ctx hdel j) D := by
    intro j
    obtain ⟨x, y, hxy, hsw⟩ := hswap j
    obtain ⟨z, w, ω, hzw, hzx, hzy, hwx, hwy, hωx, hωy, hωz, hωw, hωP, hzwP, ⟨q, hqP, hq⟩, hall⟩ :=
      sylow_two_swaps h5 _ (hP8 j) hxy (hXP j hsw)
    exact ⟨x, y, z, w, ω, q, hxy, hzx.symm, hwx.symm, hzy.symm, hwy.symm, hzw, hωx, hωy, hωz, hωw,
      hωP, hXP j hsw, hzwP, hqP, hq, hall, hsw⟩
  have hTr : ∀ j, ∃ a b c d ω : ℙ F (Fin 2 → F), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ω ≠ a ∧ ω ≠ b ∧ ω ≠ c ∧ ω ≠ d ∧
      (∀ σ ∈ delImage (delModelOf ctx hdel j) (T ⊓ blockB H (Lc j)), σ ω = ω) ∧
      Subgroup.closure (delTr (delModelOf ctx hdel j)) =
        Subgroup.closure {Equiv.swap a b, Equiv.swap c d} ∧
      Subgroup.closure {Equiv.swap a b, Equiv.swap c d} ≤ delImage (delModelOf ctx hdel j) D ∧
      (∀ u v : ℙ F (Fin 2 → F), u ≠ v →
        Equiv.swap u v ∈ delImage (delModelOf ctx hdel j) (T ⊓ blockB H (Lc j)) →
        Equiv.swap u v = Equiv.swap a b ∨ Equiv.swap u v = Equiv.swap c d) := by
    intro j
    obtain ⟨a, b, c, d, ω, q, hab, hac, had, hbc, hbd, hcd, hωa, hωb, hωc, hωd, hωP, hsP, hcdP, hqP,
      hq, hall, hsX⟩ := hstruct j
    refine ⟨a, b, c, d, ω, hab, hac, had, hbc, hbd, hcd, hωa, hωb, hωc, hωd, hωP, ?_, ?_, hall⟩
    · apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro σ ⟨hσP, u, v, huv, rfl⟩
        rcases hall u v huv hσP with h | h
        · rw [h]
          exact Subgroup.subset_closure (Set.mem_insert _ _)
        · rw [h]
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · rw [Subgroup.closure_le]
        rintro σ (rfl | rfl)
        · exact Subgroup.subset_closure ⟨hsP, a, b, hab, rfl⟩
        · exact Subgroup.subset_closure ⟨hcdP, c, d, hcd, rfl⟩
    · rw [Subgroup.closure_le]
      rintro σ (rfl | rfl)
      · exact hsX
      · obtain ⟨q0, hq0, hq0q⟩ := (mem_delImage _).1 hqP
        obtain ⟨a0, ha0, ha0σ⟩ := (mem_delImage _).1 hsX
        have hq0T : (q0 : V ≃ₗ[ZMod 2] V) ∈ T := hq0.1
        have ha0T : (a0 : V ≃ₗ[ZMod 2] V) ∈ T := hDT ha0
        refine (mem_delImage _).2 ⟨q0 * a0 * q0⁻¹, ?_, ?_⟩
        · have h2 := hDn.conj_mem ⟨(a0 : V ≃ₗ[ZMod 2] V), ha0T⟩ ha0 ⟨(q0 : V ≃ₗ[ZMod 2] V), hq0T⟩
          exact h2
        · rw [map_mul, map_mul, map_inv, hq0q, ha0σ]
          exact hq
  refine ⟨le_antisymm ?_ (iSup_le fun j => ?_), fun j => ?_⟩
  ·
    refine iSup₂_le fun E' hE'' => ?_
    obtain ⟨hE'T, hE'0⟩ := hE E' hE''
    rcases hE'0 with rfl | hoff'
    · exact bot_le
    obtain ⟨I', U', hI', hUT', rfl⟩ := (deleted_offender_iff ctx hdel E').1 hoff'
    refine iSup₂_le fun i hi => ?_
    obtain ⟨hUB, hshape⟩ := hUT' i hi
    have hUTe : U' i ≤ T := (le_iSup₂_of_le i hi le_rfl).trans hE'T
    intro a ha
    have hbB : a ∈ blockB H (Lc i) := hUB ha
    refine Subgroup.mem_iSup_of_mem i ?_
    refine (mem_delA (delModelOf ctx hdel i) ⟨a, hbB⟩).2 ?_
    have hUP : delImage (delModelOf ctx hdel i) (U' i) ≤
        delImage (delModelOf ctx hdel i) (T ⊓ blockB H (Lc i)) :=
      delImage_mono _ (le_inf hUTe hUB)
    have hψa : (delModelOf ctx hdel i).ψ ⟨a, hbB⟩ ∈ delImage (delModelOf ctx hdel i) (U' i) :=
      (mem_delImage _).2 ⟨⟨a, hbB⟩, ha, rfl⟩
    have hgen : ∀ x y : ℙ F (Fin 2 → F), x ≠ y →
        Equiv.swap x y ∈ delImage (delModelOf ctx hdel i) (U' i) →
        Equiv.swap x y ∈ delTr (delModelOf ctx hdel i) :=
      fun x y hxy h => ⟨hUP h, x, y, hxy, rfl⟩
    have hψa' : (delModelOf ctx hdel i).ψ ⟨a, hbB⟩ ∈
        ((U' i).subgroupOf (blockB H (Lc i))).map (delModelOf ctx hdel i).ψ.toMonoidHom := hψa
    rcases hshape with ⟨x, y, hxy, h⟩ | ⟨x, y, z, t, hxy, hxz, hxt, hyz, hyt, hzt, h⟩
    · rw [h] at hψa'
      refine (Subgroup.closure_le _).2 ?_ hψa'
      intro σ hσ
      rw [Set.mem_singleton_iff] at hσ
      rw [hσ]
      refine Subgroup.subset_closure (hgen x y hxy ?_)
      show Equiv.swap x y ∈ ((U' i).subgroupOf (blockB H (Lc i))).map
        (delModelOf ctx hdel i).ψ.toMonoidHom
      rw [h]
      exact Subgroup.subset_closure (Set.mem_singleton _)
    · rw [h] at hψa'
      refine (Subgroup.closure_le _).2 ?_ hψa'
      intro σ hσ
      rcases hσ with rfl | hσ
      · refine Subgroup.subset_closure (hgen x y hxy ?_)
        show Equiv.swap x y ∈ ((U' i).subgroupOf (blockB H (Lc i))).map
          (delModelOf ctx hdel i).ψ.toMonoidHom
        rw [h]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff] at hσ
        rw [hσ]
        refine Subgroup.subset_closure (hgen z t hzt ?_)
        show Equiv.swap z t ∈ ((U' i).subgroupOf (blockB H (Lc i))).map
          (delModelOf ctx hdel i).ψ.toMonoidHom
        rw [h]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  ·
    intro a ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨a', b', c', d', ω', -, -, -, -, -, -, -, -, -, -, -, hclos, hXj, -⟩ := hTr j
    have hbX : (delModelOf ctx hdel j).ψ b ∈ delImage (delModelOf ctx hdel j) D :=
      hXj (by rw [← hclos]; exact hb)
    obtain ⟨b0, hb0, hb0b⟩ := (mem_delImage _).1 hbX
    have : b0 = b := (delModelOf ctx hdel j).ψ.injective hb0b
    subst this
    exact hb0
  · obtain ⟨a', b', c', d', ω', hab, hac, had, hbc, hbd, hcd, hωa, hωb, hωc, hωd, hωP, hclos, -,
      hall⟩ := hTr j
    exact ⟨a', b', c', d', hab, hac, had, hbc, hbd, hcd, by rw [delA_image, hclos], hall,
      ω', hωa, hωb, hωc, hωd, hωP⟩

end Main

end CFSG.QuasithinUnique.Setup.Lift
