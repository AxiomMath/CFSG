module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

noncomputable abbrev NG (α k : ℕ) : Subgroup (Equiv.Perm (Fin 16)) :=
  modelGroup 16 9 (nGens α k)

noncomputable abbrev wp (α k : ℕ) (w : List (Fin 9 × Bool)) : Equiv.Perm (Fin 16) :=
  FreeGroup.lift (modelGens 16 9 (nGens α k)) (FreeGroup.mk w)

theorem wp_mem (α k : ℕ) (w : List (Fin 9 × Bool)) : wp α k w ∈ NG α k :=
  lift_mem_modelGroup 16 9 (nGens α k) w

section Model

variable {α k : ℕ}

theorem nEnum_spec (hnC : ModelOK 16 16 9 (nGens α k) (relN α α k) 3072) :
    EnumSpec 16 (nGens α k) (nEnum α k) := by
  have h := hnC.1
  simp only [modelCheck, Bool.and_eq_true] at h
  exact (enumOK_spec (by norm_num) h.1.1).1

theorem closure_nGens_eq (hsz : (nGens α k).size = 9) :
    closure (tp 16 '' {x | x ∈ nGens α k}) = NG α k := by
  show _ = closure (Set.range (modelGens 16 9 (nGens α k)))
  rw [range_modelGens hsz]

theorem mem_NG_of_mem_nEnum (hsz : (nGens α k).size = 9)
    (hnC : ModelOK 16 16 9 (nGens α k) (relN α α k) 3072) {T : Table}
    (hT : T ∈ nEnum α k) : tablePerm 16 T ∈ NG α k := by
  have h := ((nEnum_spec hnC).rep_mem hT).2
  rwa [closure_nGens_eq hsz] at h

theorem rep_nT (hsz : (nGens α k).size = 9)
    (hnC : ModelOK 16 16 9 (nGens α k) (relN α α k) 3072)
    (w : List (Fin 9 × Bool)) : Rep 16 (nT α k w) (wp α k w) :=
  rep_modelT (by norm_num) hsz hnC w

theorem conjugatesTo_sound (hsz : (nGens α k).size = 9)
    (hnC : ModelOK 16 16 9 (nGens α k) (relN α α k) 3072)
    {t₁ t₂ : Table} {p₁ p₂ : Equiv.Perm (Fin 16)} (h1 : Rep 16 t₁ p₁) (h2 : Rep 16 t₂ p₂)
    (h : conjugatesTo α k t₁ t₂ = true) : ∃ m ∈ NG α k, m * p₁ * m⁻¹ = p₂ := by
  unfold conjugatesTo at h
  obtain ⟨T, hT, he⟩ := Array.any_eq_true'.1 h
  obtain ⟨hrep, -⟩ := (nEnum_spec hnC).rep_mem hT
  have hc := rep_conjT (by norm_num) hrep h1
  exact ⟨tablePerm 16 T, mem_NG_of_mem_nEnum hsz hnC hT, (tblEq_iff_eq hc h2).1 he⟩

theorem commutator_fst (p q : Multiplicative (ZMod 2) × G12) :
    (⁅p, q⁆ : Multiplicative (ZMod 2) × G12).1 = 1 := by
  have h : (MonoidHom.fst (Multiplicative (ZMod 2)) G12 ⁅p, q⁆ : Multiplicative (ZMod 2)) =
      ⁅p.1, q.1⁆ := map_commutatorElement _ p q
  exact h.trans (commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _))

end Model

section Embedding

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)


set_option linter.unusedSectionVars false

structure NEmb (d : G) (α k : ℕ) where
  Ψ : ↥(NG α k) →* G
  inj : Function.Injective Ψ
  range : Ψ.range = Nn e₀
  gen : ∀ i : Fin 9, Ψ ⟨modelGens 16 9 (nGens α k) i, mem_modelGroup_gen _ _ _ i⟩ =
    gen5 e₀ d α α i
  hrel : ∀ r ∈ rel4 α α, FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) = 1

variable {e₀}
variable {d : G} {α k : ℕ}

@[expose] noncomputable def val (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)
    (d : G) (α : ℕ) (w : List (Fin 9 × Bool)) : G :=
  FreeGroup.lift (gen5 e₀ d α α) (FreeGroup.mk w)

theorem NEmb.apply_wp (E : NEmb e₀ d α k) (w : List (Fin 9 × Bool)) :
    E.Ψ ⟨wp α k w, wp_mem α k w⟩ = val e₀ d α w := by
  let f : FreeGroup (Fin 9) →* ↥(NG α k) :=
    FreeGroup.lift fun i => ⟨modelGens 16 9 (nGens α k) i, mem_modelGroup_gen _ _ _ i⟩
  have h1 : (NG α k).subtype.comp f = FreeGroup.lift (modelGens 16 9 (nGens α k)) := by
    apply FreeGroup.ext_hom
    intro i
    simp [f]
  have h2 : E.Ψ.comp f = FreeGroup.lift (gen5 e₀ d α α) := by
    apply FreeGroup.ext_hom
    intro i
    simp [f, E.gen i]
  have h3 : (⟨wp α k w, wp_mem α k w⟩ : ↥(NG α k)) = f (FreeGroup.mk w) := by
    apply Subtype.ext
    have := congrArg (fun φ => φ (FreeGroup.mk w)) h1
    simpa using this.symm
  rw [h3]
  have := congrArg (fun φ => φ (FreeGroup.mk w)) h2
  simpa [val] using this

theorem NEmb.isConj_of_conj (E : NEmb e₀ d α k) {m p₁ p₂ : Equiv.Perm (Fin 16)} (hm : m ∈ NG α k)
    (h1 : p₁ ∈ NG α k) (h2 : p₂ ∈ NG α k) (h : m * p₁ * m⁻¹ = p₂) :
    IsConj (E.Ψ ⟨p₁, h1⟩) (E.Ψ ⟨p₂, h2⟩) := by
  refine isConj_iff.2 ⟨E.Ψ ⟨m, hm⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

theorem conjugatesTo_isConj (hsz : (nGens α k).size = 9)
    (hnC : ModelOK 16 16 9 (nGens α k) (relN α α k) 3072)
    (E : NEmb e₀ d α k) {w₁ w₂ : List (Fin 9 × Bool)}
    (h : conjugatesTo α k (nT α k w₁) (nT α k w₂) = true) :
    IsConj (val e₀ d α w₁) (val e₀ d α w₂) := by
  obtain ⟨m, hm, hmm⟩ := conjugatesTo_sound hsz hnC (rep_nT hsz hnC w₁) (rep_nT hsz hnC w₂) h
  rw [← E.apply_wp w₁, ← E.apply_wp w₂]
  exact E.isConj_of_conj hm (wp_mem α k w₁) (wp_mem α k w₂) hmm

structure FusionData (α k : ℕ) : Prop where
  hα : α < 2
  hsz : (nGens α k).size = 9
  hnC : ModelOK 16 16 9 (nGens α k) (relN α α k) 3072
  hsig : sigmaQCheck α = true
  hchains : fusionChainsCheck α k = true
  hcover : fusionCoverCheck α k = true

theorem lift_gen4_substW_toQ (hα : α < 2) (w : List (Fin 9 × Bool)) (hw : ∀ l ∈ w, l.1 ≠ 7) :
    FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk (substW (toQ α α) w)) =
      FreeGroup.lift (gen5 e₀ d α α) (FreeGroup.mk w) := by
  have h1 := lift_comp_substW (MonoidHom.id G) (toQ α α) (gen4 e₀ d) w
  simp only [MonoidHom.id_apply] at h1
  rw [← h1]
  symm
  apply lift_mk_congr
  intro l hl
  simp [gen5, hw l hl]

theorem jgenW_ne_seven : ∀ α < 2, ∀ j : Fin 9, (∀ l ∈ jgenW α j, l.1 ≠ 7) ∧
    ∀ l ∈ substW (jgenW α) (sgenW α j), l.1 ≠ 7 := by
  intro α hα j
  interval_cases α <;> revert j <;> decide

theorem sigma_rel (hα : α < 2) (hsig : sigmaQCheck α = true)
    (hrel : ∀ r ∈ rel4 α α, FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) = 1) (j : Fin 9) :
    (gen4 e₀ d 4)⁻¹ * val e₀ d α (jgenW α j) * gen4 e₀ d 4 =
      FreeGroup.lift (fun i => val e₀ d α (jgenW α i)) (FreeGroup.mk (sgenW α j)) := by
  obtain ⟨h7a, h7b⟩ := jgenW_ne_seven α hα j
  have hmem : ([((4 : Fin 8), false)] ++ substW (toQ α α) (jgenW α j) ++ [((4 : Fin 8), true)] ++
      invW (substW (toQ α α) (substW (jgenW α) (sgenW α j)))) ∈ sigmaRelQ α :=
    List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩
  unfold sigmaQCheck wordsTrivial at hsig
  have h1 := qTrivial hα hα (gen4 e₀ d) hrel (List.all_eq_true.1 hsig _ hmem)
  rw [lift_mk_append, lift_mk_append, lift_mk_append, lift_mk_invW, lift_mk_single_inv,
    lift_mk_single, lift_gen4_substW_toQ hα _ h7a, lift_gen4_substW_toQ hα _ h7b] at h1
  have h2 := lift_comp_substW (MonoidHom.id G) (jgenW α) (gen5 e₀ d α α) (sgenW α j)
  simp only [MonoidHom.id_apply] at h2
  have h3 : FreeGroup.lift (gen5 e₀ d α α) (FreeGroup.mk (substW (jgenW α) (sgenW α j))) =
      FreeGroup.lift (fun i => val e₀ d α (jgenW α i)) (FreeGroup.mk (sgenW α j)) := h2.symm
  rw [h3] at h1
  have h4 : (gen4 e₀ d 4)⁻¹ * val e₀ d α (jgenW α j) * gen4 e₀ d 4 *
      (FreeGroup.lift (fun i => val e₀ d α (jgenW α i)) (FreeGroup.mk (sgenW α j)))⁻¹ = 1 := h1
  exact mul_inv_eq_one.1 h4

theorem sigma_conj (hα : α < 2) (hsig : sigmaQCheck α = true)
    (hrel : ∀ r ∈ rel4 α α, FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) = 1)
    (W : List (Fin 9 × Bool)) :
    (gen4 e₀ d 4)⁻¹ * val e₀ d α (jIn α W) * gen4 e₀ d 4 = val e₀ d α (jOut α W) := by
  have hc := conj_lift_substW (gen4 e₀ d 4) (fun i => val e₀ d α (jgenW α i)) (sgenW α)
    (sigma_rel hα hsig hrel) W
  have h1 := lift_comp_substW (MonoidHom.id G) (jgenW α) (gen5 e₀ d α α) W
  have h2 := lift_comp_substW (MonoidHom.id G) (jgenW α) (gen5 e₀ d α α) (substW (sgenW α) W)
  simp only [MonoidHom.id_apply] at h1 h2
  unfold val jIn jOut
  rw [← h1, ← h2]
  exact hc

theorem isConj_conj_s (x : G) : IsConj x ((gen4 e₀ d 4)⁻¹ * x * gen4 e₀ d 4) := by
  refine isConj_iff.2 ⟨(gen4 e₀ d 4)⁻¹, ?_⟩
  simp [mul_assoc]

theorem chainRun_sound (D : FusionData α k) (E : NEmb e₀ d α k) :
    ∀ (steps : List (List Int × Bool)) (w w' : List (Fin 9 × Bool)),
      chainRun α k w steps = some w' → IsConj (val e₀ d α w) (val e₀ d α w') := by
  intro steps
  induction steps with
  | nil =>
    intro w w' h
    simp only [chainRun, Option.some.injEq] at h
    subst h
    exact IsConj.refl _
  | cons st rest ih =>
    intro w w' h
    obtain ⟨W, dir⟩ := st
    have hs := sigma_conj D.hα D.hsig E.hrel (swN W)
    have hsc := isConj_conj_s (e₀ := e₀) (d := d) (val e₀ d α (jIn α (swN W)))
    rw [hs] at hsc
    cases dir
    · simp only [chainRun, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hc : conjugatesTo α k (nT α k w) (nT α k (jIn α (swN W))) = true
      · rw [if_pos hc] at h
        exact ((conjugatesTo_isConj D.hsz D.hnC E hc).trans hsc).trans (ih _ _ h)
      · rw [if_neg hc] at h
        exact absurd h (by simp)
    · simp only [chainRun, ↓reduceIte] at h
      by_cases hc : conjugatesTo α k (nT α k w) (nT α k (jOut α (swN W))) = true
      · rw [if_pos hc] at h
        exact ((conjugatesTo_isConj D.hsz D.hnC E hc).trans hsc.symm).trans (ih _ _ h)
      · rw [if_neg hc] at h
        exact absurd h (by simp)

theorem val_e (he2 : orderOf e = 2) : val e₀ d α [((5 : Fin 9), true)] = e := by
  rw [val, lift_mk_single, gen5_e]
  exact valG_tau e₀ he2

theorem not_isConj_e_of_isSq (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)
    (he2 : orderOf e = 2) {y : G} (hy : ∃ z : G, z * z = y) : ¬ IsConj e y := by
  intro hc
  obtain ⟨c, hcy⟩ := isConj_iff.1 hc
  obtain ⟨z, hz⟩ := hy
  apply not_isSq_e e₀ he2
  refine ⟨c⁻¹ * z * c, ?_⟩
  calc c⁻¹ * z * c * (c⁻¹ * z * c) = c⁻¹ * (z * z) * c := by group
    _ = c⁻¹ * y * c := by rw [hz]
    _ = e := by rw [← hcy]; group

theorem not_isConj_e_of_isComm
    (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12) (he2 : orderOf e = 2)
    {y : G} (hy : ∃ a b : G, a * y = y * a ∧ b * y = y * b ∧ ⁅a, b⁆ = y) : ¬ IsConj e y := by
  intro hc
  obtain ⟨c, hcy⟩ := isConj_iff.1 hc
  obtain ⟨a, b, ha, hb, hab⟩ := hy
  have hce : ∀ x : G, x * y = y * x → (c⁻¹ * x * c) * e = e * (c⁻¹ * x * c) := by
    intro x hx
    have h1 : c * e = y * c := by rw [← hcy]; group
    have h2 : c⁻¹ * y = e * c⁻¹ := by rw [← hcy]; group
    calc c⁻¹ * x * c * e = c⁻¹ * x * (c * e) := by group
      _ = c⁻¹ * x * (y * c) := by rw [h1]
      _ = c⁻¹ * (x * y) * c := by group
      _ = c⁻¹ * (y * x) * c := by rw [hx]
      _ = (c⁻¹ * y) * (x * c) := by group
      _ = e * (c⁻¹ * x * c) := by rw [h2]; group
  have hcent : ∀ x : G, x * y = y * x → c⁻¹ * x * c ∈ centralizer ({e} : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hce x hx).symm
  obtain ⟨p, hp⟩ := (mem_range_jH e₀).2 (hcent a ha)
  obtain ⟨q, hq⟩ := (mem_range_jH e₀).2 (hcent b hb)
  have hcomm : ⁅c⁻¹ * a * c, c⁻¹ * b * c⁆ = e := by
    have : ⁅c⁻¹ * a * c, c⁻¹ * b * c⁆ = c⁻¹ * ⁅a, b⁆ * c := by
      simp only [commutatorElement_def]; group
    rw [this, hab, ← hcy]; group
  have h1 : jH e₀ ⁅p, q⁆ = jH e₀ (Multiplicative.ofAdd 1, 1) := by
    rw [map_commutatorElement, hp, hq, hcomm]
    exact e_eq_jH e₀ he2
  have h2 := congrArg Prod.fst (jH_injective e₀ h1)
  rw [commutator_fst] at h2
  exact ofAdd_one_ne_one h2.symm

theorem isSqN_sound (D : FusionData α k) {w : List (Fin 9 × Bool)}
    (h : isSqN α k (nT α k w) = true) : ∃ z ∈ NG α k, z * z = wp α k w := by
  unfold isSqN at h
  obtain ⟨T, hT, he⟩ := Array.any_eq_true'.1 h
  obtain ⟨hrep, -⟩ := (nEnum_spec D.hnC).rep_mem hT
  have hc := hrep.compT hrep
  exact ⟨tablePerm 16 T, mem_NG_of_mem_nEnum D.hsz D.hnC hT,
    (tblEq_iff_eq hc (rep_nT D.hsz D.hnC w)).1 he⟩

theorem isCommN_sound (D : FusionData α k) {w : List (Fin 9 × Bool)}
    (h : isCommN α k (nT α k w) = true) :
    ∃ a ∈ NG α k, ∃ b ∈ NG α k, a * wp α k w = wp α k w * a ∧ b * wp α k w = wp α k w * b ∧
      ⁅a, b⁆ = wp α k w := by
  unfold isCommN at h
  simp only at h
  obtain ⟨A, hA, h1⟩ := Array.any_eq_true'.1 h
  obtain ⟨B, hB, he⟩ := Array.any_eq_true'.1 h1
  obtain ⟨hAL, hAc⟩ := Array.mem_filter.1 hA
  obtain ⟨hBL, hBc⟩ := Array.mem_filter.1 hB
  obtain ⟨hrepA, -⟩ := (nEnum_spec D.hnC).rep_mem hAL
  obtain ⟨hrepB, -⟩ := (nEnum_spec D.hnC).rep_mem hBL
  have hw := rep_nT D.hsz D.hnC w
  refine ⟨tablePerm 16 A, mem_NG_of_mem_nEnum D.hsz D.hnC hAL, tablePerm 16 B,
    mem_NG_of_mem_nEnum D.hsz D.hnC hBL, ((commTT_iff hw hrepA).1 hAc).symm,
    ((commTT_iff hw hrepB).1 hBc).symm, ?_⟩
  exact (tblEq_iff_eq (rep_commutatorT (by norm_num) hrepA hrepB) hw).1 he

theorem witness_not_isConj (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    {w : List (Fin 9 × Bool)} (h : witnessOK α k (nT α k w) = true) :
    ¬ IsConj e (val e₀ d α w) := by
  unfold witnessOK at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨z, hz, hzz⟩ := isSqN_sound D h
    refine not_isConj_e_of_isSq e₀ he2 ⟨E.Ψ ⟨z, hz⟩, ?_⟩
    rw [← E.apply_wp w, ← map_mul]
    congr 1
    exact Subtype.ext hzz
  · obtain ⟨a, ha, b, hb, hac, hbc, hab⟩ := isCommN_sound D h
    refine not_isConj_e_of_isComm e₀ he2 ⟨E.Ψ ⟨a, ha⟩, E.Ψ ⟨b, hb⟩, ?_, ?_, ?_⟩
    · rw [← E.apply_wp w, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hac
    · rw [← E.apply_wp w, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hbc
    · rw [← E.apply_wp w, ← map_commutatorElement]
      congr 1
      exact Subtype.ext hab

theorem goodReps_isConj (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    {w' : List (Fin 9 × Bool)} (hw' : w' ∈ goodReps α k) : IsConj e (val e₀ d α w') := by
  obtain ⟨c, hc, hrun⟩ := List.mem_filterMap.1 hw'
  have hfus := D.hchains
  unfold fusionChainsCheck at hfus
  rw [Bool.and_eq_true] at hfus
  have hgood := List.all_eq_true.1 hfus.1 c hc
  rw [Bool.and_eq_true] at hgood
  have hc1 : c.1 = [6] := beq_iff_eq.1 hgood.1
  have h2 := chainRun_sound D E c.2 _ _ hrun
  rw [hc1, show swN [6] = [((5 : Fin 9), true)] by decide, val_e he2] at h2
  exact h2

theorem badReps_not_isConj (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    {w' : List (Fin 9 × Bool)} (hw' : w' ∈ badReps α k) : ¬ IsConj e (val e₀ d α w') := by
  intro hconj
  obtain ⟨c, hc, hrun⟩ := List.mem_filterMap.1 hw'
  have hfus := D.hchains
  unfold fusionChainsCheck at hfus
  rw [Bool.and_eq_true] at hfus
  have hbad := List.all_eq_true.1 hfus.2 c hc
  rw [Bool.and_eq_true] at hbad
  have h1 := witness_not_isConj D E he2 hbad.1
  have h2 := chainRun_sound D E c.2 _ _ hrun
  exact h1 (hconj.trans h2.symm)

theorem orderOf_isConj {x y : G} (h : IsConj x y) : orderOf y = orderOf x := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  have := (MulAut.conj c).orderOf_eq x
  simpa [MulAut.conj_apply] using this

theorem mem_classTabs (D : FusionData α k) {w : List (Fin 9 × Bool)} {T : Table}
    (hT : T ∈ classTabs α k (nT α k w)) :
    ∃ m : Equiv.Perm (Fin 16), m ∈ NG α k ∧ Rep 16 T (m * wp α k w * m⁻¹) := by
  unfold classTabs at hT
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hT
  have hM' := Array.mem_toList_iff.1 hM
  obtain ⟨hrep, -⟩ := (nEnum_spec D.hnC).rep_mem hM'
  exact ⟨tablePerm 16 M, mem_NG_of_mem_nEnum D.hsz D.hnC hM',
    rep_conjT (by norm_num) hrep (rep_nT D.hsz D.hnC w)⟩

theorem classTabs_conj (D : FusionData α k) (E : NEmb e₀ d α k) {w : List (Fin 9 × Bool)}
    {T : Table} (hT : T ∈ classTabs α k (nT α k w)) {s : Equiv.Perm (Fin 16)}
    (hs : Rep 16 T s) : ∃ hs' : s ∈ NG α k, IsConj (val e₀ d α w) (E.Ψ ⟨s, hs'⟩) := by
  obtain ⟨m, hm, hrep⟩ := mem_classTabs D hT
  have hmem : m * wp α k w * m⁻¹ ∈ NG α k :=
    (NG α k).mul_mem ((NG α k).mul_mem hm (wp_mem α k w)) ((NG α k).inv_mem hm)
  have hseq : m * wp α k w * m⁻¹ = s := rep_unique hrep hs
  subst hseq
  refine ⟨hmem, ?_⟩
  have h1 := E.isConj_of_conj hm (wp_mem α k w) hmem rfl
  rwa [E.apply_wp] at h1

theorem rep_of_mem_goodTabs (D : FusionData α k) {T : Table} (hT : T ∈ goodTabs α k) :
    ∃ s : Equiv.Perm (Fin 16), Rep 16 T s := by
  unfold goodTabs at hT
  obtain ⟨w, -, hTw⟩ := List.mem_flatMap.1 hT
  obtain ⟨m, -, hrep⟩ := mem_classTabs D hTw
  exact ⟨_, hrep⟩

theorem rep_of_mem_badTabs (D : FusionData α k) {T : Table} (hT : T ∈ badTabs α k) :
    ∃ s : Equiv.Perm (Fin 16), Rep 16 T s := by
  unfold badTabs at hT
  obtain ⟨w, -, hTw⟩ := List.mem_flatMap.1 hT
  obtain ⟨m, -, hrep⟩ := mem_classTabs D hTw
  exact ⟨_, hrep⟩

theorem goodTabs_spec (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    {T : Table} (hT : T ∈ goodTabs α k) {s : Equiv.Perm (Fin 16)} (hs : Rep 16 T s) :
    ∃ hs' : s ∈ NG α k, IsConj e (E.Ψ ⟨s, hs'⟩) := by
  unfold goodTabs at hT
  obtain ⟨w, hw, hTw⟩ := List.mem_flatMap.1 hT
  obtain ⟨hs', hc⟩ := classTabs_conj D E hTw hs
  exact ⟨hs', (goodReps_isConj D E he2 hw).trans hc⟩

theorem badTabs_spec (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    {T : Table} (hT : T ∈ badTabs α k) {s : Equiv.Perm (Fin 16)} (hs : Rep 16 T s) :
    ∃ hs' : s ∈ NG α k, ¬ IsConj e (E.Ψ ⟨s, hs'⟩) := by
  unfold badTabs at hT
  obtain ⟨w, hw, hTw⟩ := List.mem_flatMap.1 hT
  obtain ⟨hs', hc⟩ := classTabs_conj D E hTw hs
  exact ⟨hs', fun h => badReps_not_isConj D E he2 hw (h.trans hc.symm)⟩

theorem cover_parts (h : fusionCoverCheck α k = true) :
    (∀ T ∈ nEnum α k, involOK 16 T = true →
      memTab 16 (goodTabs α k) T = true ∨ memTab 16 (badTabs α k) T = true) ∧
    ((nEnum α k).toList.filter (memTab 16 (goodTabs α k))).length = goodCount α := by
  unfold fusionCoverCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  refine ⟨fun T hT hinv => ?_, h.2⟩
  have := h.1 T (Array.mem_toList_iff.2 hT)
  simpa [hinv] using this

theorem memTab_good_iff (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2)
    {T : Table} {g : Equiv.Perm (Fin 16)} (hT : Rep 16 T g) (hg : g ∈ NG α k) :
    memTab 16 (goodTabs α k) T = true ↔ IsConj e (E.Ψ ⟨g, hg⟩) := by
  constructor
  · intro h
    obtain ⟨S, hS, s, hr, rfl⟩ := (memTab_iff hT (fun S hS => rep_of_mem_goodTabs D hS)).1 h
    obtain ⟨_, hc⟩ := goodTabs_spec D E he2 hS hr
    exact hc
  · intro hconj
    have hord : orderOf g = 2 :=
      calc orderOf g = orderOf (⟨g, hg⟩ : ↥(NG α k)) := Subgroup.orderOf_coe ⟨g, hg⟩
        _ = orderOf (E.Ψ ⟨g, hg⟩) := (orderOf_injective E.Ψ E.inj _).symm
        _ = orderOf e := orderOf_isConj hconj
        _ = 2 := he2
    obtain ⟨T', hT', hrep'⟩ := (nEnum_spec D.hnC).exists_entry (g := g)
      (by rw [closure_nGens_eq D.hsz]; exact hg)
    have hinv := involOK_of_orderOf (by norm_num) hrep' hord
    obtain ⟨hcov, -⟩ := cover_parts D.hcover
    rcases hcov T' hT' hinv with hgood | hbad
    · obtain ⟨S, hS, s, hr, hsg⟩ :=
        (memTab_iff hrep' (fun S hS => rep_of_mem_goodTabs D hS)).1 hgood
      exact (memTab_iff hT (fun S hS => rep_of_mem_goodTabs D hS)).2 ⟨S, hS, s, hr, hsg⟩
    · exfalso
      obtain ⟨S, hS, s, hr, rfl⟩ :=
        (memTab_iff hrep' (fun S hS => rep_of_mem_badTabs D hS)).1 hbad
      obtain ⟨_, hnc⟩ := badTabs_spec D E he2 hS hr
      exact hnc hconj

theorem card_isConj_e (D : FusionData α k) (E : NEmb e₀ d α k) (he2 : orderOf e = 2) :
    Nat.card {y : ↥(Nn e₀) // IsConj e (y : G)} = goodCount α := by
  classical
  let Q : Equiv.Perm (Fin 16) → Prop := fun g => ∃ hg : g ∈ NG α k, IsConj e (E.Ψ ⟨g, hg⟩)
  have h1 : Nat.card {y : ↥(Nn e₀) // IsConj e (y : G)} =
      Nat.card {m : ↥(NG α k) // IsConj e (E.Ψ m)} := by
    refine (Nat.card_congr (Equiv.subtypeEquiv
      ((MonoidHom.ofInjective E.inj).toEquiv.trans (MulEquiv.subgroupCongr E.range).toEquiv)
      ?_)).symm
    intro m
    exact Iff.rfl
  have h2 : Nat.card {m : ↥(NG α k) // IsConj e (E.Ψ m)} =
      Nat.card {g : Equiv.Perm (Fin 16) //
        g ∈ closure (tp 16 '' {x | x ∈ nGens α k}) ∧ Q g} :=
    Nat.card_congr
      { toFun := fun m => ⟨(m.1 : Equiv.Perm (Fin 16)),
          by rw [closure_nGens_eq D.hsz]; exact m.1.2, m.1.2, m.2⟩
        invFun := fun g => ⟨⟨g.1, g.2.2.choose⟩, g.2.2.choose_spec⟩
        left_inv := fun m => Subtype.ext (Subtype.ext rfl)
        right_inv := fun g => Subtype.ext rfl }
  have hP : ∀ T ∈ nEnum α k, memTab 16 (goodTabs α k) T = true ↔ Q (tablePerm 16 T) := by
    intro T hT
    obtain ⟨hrep, -⟩ := (nEnum_spec D.hnC).rep_mem hT
    have hg := mem_NG_of_mem_nEnum D.hsz D.hnC hT
    rw [memTab_good_iff D E he2 hrep hg]
    exact ⟨fun h => ⟨hg, h⟩, fun ⟨_, h⟩ => h⟩
  rw [h1, h2, (nEnum_spec D.hnC).card_filter Q (memTab 16 (goodTabs α k)) hP]
  exact (cover_parts D.hcover).2

end Embedding

end CFSG.EvenSporadicStandard.M12Std.Yosh
