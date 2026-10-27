module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderDel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderNatClass

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Combinatorics

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] in
theorem swap_disjoint {a b c d : Ω} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).Disjoint (Equiv.swap c d) := by
  intro p
  by_cases hp : p = a ∨ p = b
  · right
    rcases hp with rfl | rfl
    · exact Equiv.swap_apply_of_ne_of_ne hac had
    · exact Equiv.swap_apply_of_ne_of_ne hbc hbd
  · left
    push Not at hp
    exact Equiv.swap_apply_of_ne_of_ne hp.1 hp.2

omit [Fintype Ω] in
theorem swap_ne_of_commute {a b c d : Ω} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : Equiv.swap a b ≠ Equiv.swap c d)
    (h : Equiv.swap c d * Equiv.swap a b = Equiv.swap a b * Equiv.swap c d) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  rcases perm_commute_swap hab (Equiv.swap c d) h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro rfl
      rw [Equiv.swap_apply_left] at h1
      exact hcd h1.symm
    · rintro rfl
      rw [Equiv.swap_apply_right] at h1
      exact hcd h1
    · rintro rfl
      rw [Equiv.swap_apply_left] at h2
      exact hcd h2.symm
    · rintro rfl
      rw [Equiv.swap_apply_right] at h2
      exact hcd h2
  · exfalso
    apply hne
    have ha : a = c ∨ a = d := by
      by_contra hcon
      push Not at hcon
      rw [Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2] at h1
      exact hab h1
    have hb : b = c ∨ b = d := by
      by_contra hcon
      push Not at hcon
      rw [Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2] at h2
      exact hab h2.symm
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · exact Equiv.swap_comm _ _
    · exact absurd rfl hab

theorem not_three_disjoint_swaps (h5 : Fintype.card Ω = 5) {a b c d e f : Ω}
    (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hae : a ≠ e) (haf : a ≠ f) (hbe : b ≠ e) (hbf : b ≠ f) (hce : c ≠ e)
    (hcf : c ≠ f) (hde : d ≠ e) (hdf : d ≠ f) : False := by
  have hcard : ({a, b, c, d, e, f} : Finset Ω).card = 6 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae, haf]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe, hbf]),
      Finset.card_insert_of_notMem (by simp [hcd, hce, hcf]),
      Finset.card_insert_of_notMem (by simp [hde, hdf]),
      Finset.card_insert_of_notMem (by simp [hef]), Finset.card_singleton]
  have := Finset.card_le_univ ({a, b, c, d, e, f} : Finset Ω)
  omega

theorem exists_avoiding (h5 : Fintype.card Ω = 5) (x y z t : Ω) :
    ∃ ω : Ω, ω ≠ x ∧ ω ≠ y ∧ ω ≠ z ∧ ω ≠ t := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset Ω) ⊆ {x, y, z, t} := by
    intro ω _
    by_cases h1 : ω = x
    · simp [h1]
    by_cases h2 : ω = y
    · simp [h2]
    by_cases h3 : ω = z
    · simp [h3]
    simp [hcon ω h1 h2 h3]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, h5] at h1
  have h2 : ({x, y, z, t} : Finset Ω).card ≤ 4 := Finset.card_le_four
  omega

end Combinatorics

@[expose] def IsTranspGroup {G : Type*} [Group G] {Ω : Type*} [DecidableEq Ω] (B U : Subgroup G)
    (ψ : ↥B ≃* Equiv.Perm Ω) : Prop :=
  U ≤ B ∧ ((∃ x y : Ω, x ≠ y ∧
      (U.subgroupOf B).map ψ.toMonoidHom = Subgroup.closure {Equiv.swap x y}) ∨
    (∃ x y z t : Ω, x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t ∧ z ≠ t ∧
      (U.subgroupOf B).map ψ.toMonoidHom =
        Subgroup.closure {Equiv.swap x y, Equiv.swap z t}))

section Model

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}
  {ctx : FamilyCtx H T n F r Lc} {i : Fin r}

noncomputable def delModelOf (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (i : Fin r) : DelModel ctx i :=
  (nonempty_delModel ctx hdel i).some

omit [Finite V] in
theorem card_five_of_deleted (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i)) :
    Fintype.card (ℙ F (Fin 2 → F)) = 5 := by
  obtain ⟨A, hA, hLA⟩ := ctx.layer.moving ⟨0, ctx.layer.r_pos⟩
  have hmove : ⁅Lc ⟨0, ctx.layer.r_pos⟩, A⁆ ≠ ⊥ := by
    rw [hLA]
    exact ctx.hLc.ne_bot _
  rw [card_projectiveLine, ctx.hF, (hdel A hA _ hmove).1]
  norm_num

omit [Finite V] in
theorem DelModel.act_vec (M : DelModel ctx i) (b : ↥(blockB H (Lc i))) (u : ↥(commGL (Lc i) ⊤)) :
    M.β ⟨(b : V ≃ₗ[ZMod 2] V) u, blockB_isInvariant ctx i b b.2 u u.2⟩ =
      (permU (M.ψ b)).val (M.β u) := by
  apply Subtype.ext
  rw [permU_apply]
  exact M.compat b u _ rfl

omit [Finite V] in
theorem DelModel.fixed_iff (M : DelModel ctx i) (b : ↥(blockB H (Lc i)))
    (u : ↥(commGL (Lc i) ⊤)) :
    (b : V ≃ₗ[ZMod 2] V) (u : V) = u ↔ (permU (M.ψ b)).val (M.β u) = M.β u := by
  constructor
  · intro h
    rw [← M.act_vec b u]
    congr 1
    exact Subtype.ext h
  · intro h
    rw [← M.act_vec b u] at h
    exact congrArg Subtype.val (M.β.injective h)

omit [Finite V] in
theorem DelModel.sub_image (M : DelModel ctx i) {U : Subgroup (V ≃ₗ[ZMod 2] V)}
    {K : Subgroup (Equiv.Perm (ℙ F (Fin 2 → F)))}
    (hK : K ≤ (U.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom) :
    ((U ⊓ (K.comap M.ψ.toMonoidHom).map (blockB H (Lc i)).subtype).subgroupOf
      (blockB H (Lc i))).map M.ψ.toMonoidHom = K := by
  ext σ
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨-, b', hb', hbb⟩ := hb
    have : b' = b := Subtype.ext hbb
    subst this
    exact hb'
  · intro hσ
    obtain ⟨b, hbU, hbσ⟩ := hK hσ
    refine ⟨b, ⟨hbU, b, ?_, rfl⟩, hbσ⟩
    show M.ψ.toMonoidHom b ∈ K
    rw [hbσ]
    exact hσ

theorem DelModel.pmem_iff (M : DelModel ctx i)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) (A : Subgroup (V ≃ₗ[ZMod 2] V)) :
    (IsMinOffender H A ∧ ⁅Lc i, A⁆ ≠ ⊥) ↔
      ∃ x y : ℙ F (Fin 2 → F), x ≠ y ∧ A ≤ blockB H (Lc i) ∧
        (A.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom = Subgroup.closure {Equiv.swap x y} := by
  constructor
  · rintro ⟨hA, hmv⟩
    obtain ⟨x, y, hxy, h⟩ := M.single_transposition hdel hA hmv h5
    exact ⟨x, y, hxy, le_blockB_gen hA hmv, h⟩
  · rintro ⟨x, y, hxy, hAB, h⟩
    exact M.isMinOffender_of_transposition hdel h5 hxy hAB h

theorem DelModel.transp_pair (M : DelModel ctx i)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) {U : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hUB : U ≤ blockB H (Lc i)) {x y z t : ℙ F (Fin 2 → F)} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxt : x ≠ t) (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (hU : (U.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom =
      Subgroup.closure {Equiv.swap x y, Equiv.swap z t}) :
    CFSG.IsElementaryAbelian 2 U ∧ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) U = Nat.card V := by
  classical
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  have hsub₁ : Subgroup.closure ({Equiv.swap x y} : Set (Equiv.Perm (ℙ F (Fin 2 → F)))) ≤
      (U.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
    rw [hU]
    exact Subgroup.closure_mono (by simp)
  have hsub₂ : Subgroup.closure ({Equiv.swap z t} : Set (Equiv.Perm (ℙ F (Fin 2 → F)))) ≤
      (U.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
    rw [hU]
    exact Subgroup.closure_mono (by simp)
  obtain ⟨A₁, hA₁def⟩ : ∃ A₁ : Subgroup (V ≃ₗ[ZMod 2] V), A₁ = U ⊓
      ((Subgroup.closure ({Equiv.swap x y} : Set (Equiv.Perm (ℙ F (Fin 2 → F))))).comap
        M.ψ.toMonoidHom).map (blockB H (Lc i)).subtype := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂def⟩ : ∃ A₂ : Subgroup (V ≃ₗ[ZMod 2] V), A₂ = U ⊓
      ((Subgroup.closure ({Equiv.swap z t} : Set (Equiv.Perm (ℙ F (Fin 2 → F))))).comap
        M.ψ.toMonoidHom).map (blockB H (Lc i)).subtype := ⟨_, rfl⟩
  have hA₁img : (A₁.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom =
      Subgroup.closure {Equiv.swap x y} := by
    rw [hA₁def]
    exact M.sub_image hsub₁
  have hA₂img : (A₂.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom =
      Subgroup.closure {Equiv.swap z t} := by
    rw [hA₂def]
    exact M.sub_image hsub₂
  have hA₁U : A₁ ≤ U := by rw [hA₁def]; exact inf_le_left
  have hA₂U : A₂ ≤ U := by rw [hA₂def]; exact inf_le_left
  have hA₁B : A₁ ≤ blockB H (Lc i) := hA₁U.trans hUB
  have hA₂B : A₂ ≤ blockB H (Lc i) := hA₂U.trans hUB
  obtain ⟨hA₁ℙ, hA₁m⟩ := M.isMinOffender_of_transposition hdel h5 hxy hA₁B hA₁img
  obtain ⟨hA₂ℙ, hA₂m⟩ := M.isMinOffender_of_transposition hdel h5 hzt hA₂B hA₂img
  have hdisj12 : (Equiv.swap x y).Disjoint (Equiv.swap z t) := swap_disjoint hxz hxt hyz hyt
  have hneq : Equiv.swap x y ≠ Equiv.swap z t := by
    intro h
    have h1 := congrArg (fun π : Equiv.Perm (ℙ F (Fin 2 → F)) => π x) h
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxz hxt] at h1
    exact hxy h1.symm
  have hUeq : U = A₁ ⊔ A₂ := by
    apply le_antisymm
    · have himg : ((A₁ ⊔ A₂).subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom =
          Subgroup.closure {Equiv.swap x y, Equiv.swap z t} := by
        rw [Subgroup.subgroupOf_sup hA₁B hA₂B, Subgroup.map_sup, hA₁img, hA₂img,
          ← Subgroup.closure_union, ← Set.insert_eq]
      have hinj : Function.Injective M.ψ.toMonoidHom := M.ψ.injective
      have hle : U.subgroupOf (blockB H (Lc i)) ≤ (A₁ ⊔ A₂).subgroupOf (blockB H (Lc i)) := by
        rw [← Subgroup.map_le_map_iff_of_injective hinj, hU, himg]
      intro u hu
      exact hle (show (⟨u, hUB hu⟩ : ↥(blockB H (Lc i))) ∈ U.subgroupOf (blockB H (Lc i)) from hu)
    · exact sup_le hA₁U hA₂U
  have hsw₁ : Equiv.swap x y ∈ (A₁.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
    rw [hA₁img]
    exact Subgroup.subset_closure (Set.mem_singleton _)
  have hsw₂ : Equiv.swap z t ∈ (A₂.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
    rw [hA₂img]
    exact Subgroup.subset_closure (Set.mem_singleton _)
  obtain ⟨b₁, hb₁A, hb₁⟩ := hsw₁
  obtain ⟨b₂, hb₂A, hb₂⟩ := hsw₂
  have hb₁' : M.ψ b₁ = Equiv.swap x y := hb₁
  have hb₂' : M.ψ b₂ = Equiv.swap z t := hb₂
  have hb₁A' : (b₁ : V ≃ₗ[ZMod 2] V) ∈ A₁ := hb₁A
  have hb₂A' : (b₂ : V ≃ₗ[ZMod 2] V) ∈ A₂ := hb₂A
  have hAeq₁ := M.eq_one_or_gen hA₁B hA₁img hb₁'
  have hAeq₂ := M.eq_one_or_gen hA₂B hA₂img hb₂'
  have hker₁ := ker_sub_id_eq_fixGL hb₁A' hAeq₁
  have hcomm : ∀ a ∈ A₁, ∀ d ∈ A₂, a * d = d * a := by
    intro a ha d hd
    rcases hAeq₁ a ha with rfl | rfl
    · simp
    rcases hAeq₂ d hd with rfl | rfl
    · simp
    have hc : M.ψ b₁ * M.ψ b₂ = M.ψ b₂ * M.ψ b₁ := by
      rw [hb₁', hb₂']
      exact hdisj12.commute.eq
    have := M.ψ.injective (by rw [map_mul, map_mul]; exact hc :
      M.ψ (b₁ * b₂) = M.ψ (b₂ * b₁))
    exact congrArg Subtype.val this
  have hdisj : Disjoint A₁ A₂ := by
    rw [disjoint_iff, eq_bot_iff]
    intro a ⟨ha1, ha2⟩
    have h1 := (M.mem_iff_image hA₁img ⟨a, hA₁B ha1⟩).1 ha1
    have h2 := (M.mem_iff_image hA₂img ⟨a, hA₁B ha1⟩).1 ha2
    rcases (mem_closure_swap _).1 h1 with h | h
    · have : (⟨a, hA₁B ha1⟩ : ↥(blockB H (Lc i))) = 1 := M.ψ.injective (by rw [h, map_one])
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · rcases (mem_closure_swap _).1 h2 with h' | h'
      · have : (⟨a, hA₁B ha1⟩ : ↥(blockB H (Lc i))) = 1 := M.ψ.injective (by rw [h', map_one])
        exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
      · exact absurd (h.symm.trans h') hneq
  obtain ⟨ω, hωx, hωy, hωz, hωt⟩ := exists_avoiding h5 x y z t
  let u₀ : ↥(commGL (Lc i) ⊤) := M.β.symm (pairVec x ω)
  have hβu₀ : M.β u₀ = pairVec x ω := M.β.apply_symm_apply _
  have hW : ∃ w ∈ commGL (Lc i) ⊤ ⊓ fixGL A₂, (b₁ : V ≃ₗ[ZMod 2] V) w ≠ w := by
    refine ⟨(u₀ : V), ⟨u₀.2, ?_⟩, ?_⟩
    · intro a ha
      rcases hAeq₂ a ha with rfl | rfl
      · rfl
      · show (b₂ : V ≃ₗ[ZMod 2] V) (u₀ : V) = u₀
        rw [M.fixed_iff, hβu₀, hb₂', permU_pairVec,
          Equiv.swap_apply_of_ne_of_ne hxz hxt, Equiv.swap_apply_of_ne_of_ne hωz hωt]
    · intro h
      rw [M.fixed_iff, hβu₀, hb₁', permU_pairVec, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hωx hωy] at h
      have h1 := congrArg (fun v : ↥(SL2Modules.evenWeight (ℙ F (Fin 2 → F))) =>
        (v : ℙ F (Fin 2 → F) → ZMod 2) x) h
      simp [pairVec_apply, hxy, hωx.symm] at h1
  obtain ⟨hd, -⟩ := ctx.offd A₁ hA₁ℙ i hA₁m
  have hVk : commGL (Lc i) ⊤ ⊔ LinearMap.ker
      (((b₁ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id) = ⊤ := by
    rw [hker₁]
    exact hd.V_split
  have hV := M.sup_ker_eq_top h5 hxy b₁.2 hb₁' hVk hW
  rw [hker₁] at hV
  obtain ⟨-, -, h3⟩ := fixed_codimensions_add (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A₁ A₂ hcomm
    (commGL (Lc i) ⊤ ⊓ fixGL A₂) inf_le_right hV
  obtain ⟨h4, -⟩ := h3 hdisj
  rw [hUeq]
  refine ⟨isElementaryAbelian_sup_of_commute hA₁ℙ.2.2.1 hA₂ℙ.2.2.1 hcomm, ?_⟩
  rw [weight_eq_of_mem ctx hA₁ℙ, weight_eq_of_mem ctx hA₂ℙ] at h4
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card V) h4

theorem DelModel.transp_group (M : DelModel ctx i)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) {U : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hU : IsTranspGroup (blockB H (Lc i)) U M.ψ) :
    CFSG.IsElementaryAbelian 2 U ∧ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) U = Nat.card V := by
  obtain ⟨hUB, ⟨x, y, hxy, h⟩ | ⟨x, y, z, t, hxy, hxz, hxt, hyz, hyt, hzt, h⟩⟩ := hU
  · obtain ⟨hA, -⟩ := M.isMinOffender_of_transposition hdel h5 hxy hUB h
    exact ⟨hA.2.2.1, weight_eq_of_mem ctx hA⟩
  · exact M.transp_pair hdel h5 hUB hxy hxz hxt hyz hyt hzt h

end Model

section Classify

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

theorem sup_fixGL_eq_top_of_le_blockB (ctx : FamilyCtx H T n F r Lc) {j : Fin r}
    {X : Subgroup (V ≃ₗ[ZMod 2] V)} (hX : X ≤ blockB H (Lc j)) :
    commGL (Lc j) ⊤ ⊔ fixGL X = ⊤ := by
  rw [eq_top_iff]
  calc (⊤ : Submodule (ZMod 2) V) = (⨆ i, commGL (Lc i) ⊤) ⊔ fixGL (oddGen H) := (V_sum ctx).symm
    _ ≤ commGL (Lc j) ⊤ ⊔ fixGL X := by
      refine sup_le (iSup_le fun k => ?_) ?_
      · by_cases hkj : k = j
        · subst hkj
          exact le_sup_left
        · refine le_sup_of_le_right ?_
          intro w hw x hx
          exact mem_centSub.1 (blockB_le_centSub_I ctx hkj (hX hx)) w hw
      · refine le_sup_of_le_right ?_
        intro w hw x hx
        exact mem_centSub.1 (blockB_le_centSub_C ctx (hX hx)) w hw

theorem deleted_iSup_weight (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (U : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) (I : Finset (Fin r))
    (hU : ∀ i ∈ I, IsTranspGroup (blockB H (Lc i)) (U i) (delModelOf ctx hdel i).ψ) :
    CFSG.IsElementaryAbelian 2 ↥(⨆ i ∈ I, U i) ∧
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (⨆ i ∈ I, U i) = Nat.card V ∧
      (⨆ i ∈ I, U i) ≤ H := by
  classical
  have h5 := card_five_of_deleted ctx hdel
  induction I using Finset.induction_on with
  | empty =>
    have hbot : (⨆ i ∈ (∅ : Finset (Fin r)), U i) = ⊥ := by simp
    rw [hbot]
    exact ⟨isElementaryAbelian_bot 2, weight_bot _, bot_le⟩
  | insert j I' hj ih =>
    have hU' : ∀ i ∈ I', IsTranspGroup (blockB H (Lc i)) (U i) (delModelOf ctx hdel i).ψ :=
      fun i hi => hU i (Finset.mem_insert_of_mem hi)
    obtain ⟨ihel, ihw, ihH⟩ := ih hU'
    have hUj := hU j (Finset.mem_insert_self _ _)
    obtain ⟨hAel, hAw⟩ := (delModelOf ctx hdel j).transp_group hdel h5 hUj
    rw [Finset.iSup_insert]
    have hDB : (⨆ i ∈ I', U i) ≤ ⨆ i, ⨆ (_ : i ≠ j), blockB H (Lc i) :=
      iSup₂_le fun i hi => (hU' i hi).1.trans
        (le_iSup₂_of_le i (fun h => hj (h ▸ hi)) le_rfl)
    have hcomm : ∀ a ∈ U j, ∀ d ∈ (⨆ i ∈ I', U i), a * d = d * a := by
      intro a ha d hd
      have : (⨆ i ∈ I', U i) ≤ Subgroup.centralizer (blockB H (Lc j) : Set (V ≃ₗ[ZMod 2] V)) := by
        refine hDB.trans (iSup₂_le fun i hij z hz => ?_)
        exact Subgroup.mem_centralizer_iff.2 fun l hl => (blockB_comm ctx hij z hz l hl).symm
      exact Subgroup.mem_centralizer_iff.1 (this hd) a (hUj.1 ha)
    have hdisj : Disjoint (U j) (⨆ i ∈ I', U i) := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have h1 : x ∈ blockB H (Lc j) ⊓ ⨆ i, ⨆ (_ : i ≠ j), blockB H (Lc i) := ⟨hUj.1 hx.1, hDB hx.2⟩
      rw [blockB_direct ctx j] at h1
      exact h1
    have hDW : commGL (Lc j) ⊤ ≤ fixSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (⨆ i ∈ I', U i) := by
      intro w hw d hd
      have hle : (⨆ i ∈ I', U i) ≤ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (commGL (Lc j) ⊤) :=
        hDB.trans (iSup₂_le fun i hij => blockB_le_centSub_I ctx (Ne.symm hij))
      exact mem_centSub.1 (hle hd) w hw
    obtain ⟨-, -, h3⟩ := fixed_codimensions_add (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (U j)
      (⨆ i ∈ I', U i) hcomm (commGL (Lc j) ⊤) hDW
      (sup_fixGL_eq_top_of_le_blockB ctx hUj.1)
    obtain ⟨h4, -⟩ := h3 hdisj
    refine ⟨isElementaryAbelian_sup_of_commute hAel ihel hcomm, ?_, ?_⟩
    · rw [hAw, ihw] at h4
      exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card V) h4
    · refine sup_le ?_ ihH
      exact (hUj.1.trans (blockB_le_J j)).trans offenderJ_le

theorem IsTranspGroup.ne_bot {G : Type*} [Group G] {Ω : Type*} [DecidableEq Ω] {B U : Subgroup G}
    {ψ : ↥B ≃* Equiv.Perm Ω} (h : IsTranspGroup B U ψ) : U ≠ ⊥ := by
  intro hU
  have hbot : (U.subgroupOf B).map ψ.toMonoidHom = ⊥ := by rw [hU]; simp
  obtain ⟨-, ⟨x, y, hxy, himg⟩ | ⟨x, y, z, t, hxy, -, -, -, -, -, himg⟩⟩ := h
  · rw [hbot] at himg
    have : Equiv.swap x y ∈ Subgroup.closure ({Equiv.swap x y} : Set (Equiv.Perm Ω)) :=
      Subgroup.subset_closure (Set.mem_singleton _)
    rw [← himg, Subgroup.mem_bot] at this
    exact swap_ne_one hxy this
  · rw [hbot] at himg
    have : Equiv.swap x y ∈ Subgroup.closure
        ({Equiv.swap x y, Equiv.swap z t} : Set (Equiv.Perm Ω)) :=
      Subgroup.subset_closure (by simp)
    rw [← himg, Subgroup.mem_bot] at this
    exact swap_ne_one hxy this

theorem DelModel.kc_step {ctx : FamilyCtx H T n F r Lc} {i : Fin r} (M : DelModel ctx i)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (h5 : Fintype.card (ℙ F (Fin 2 → F)) = 5) {A Ui : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) (hmove : ⁅Lc i, A⁆ ≠ ⊥)
    (hUi : IsTranspGroup (blockB H (Lc i)) Ui M.ψ) (hAU : A ⊓ Ui = ⊥)
    (hcomm : ∀ a ∈ A, ∀ u ∈ Ui, a * u = u * a) :
    IsTranspGroup (blockB H (Lc i)) (A ⊔ Ui) M.ψ := by
  classical
  have hAB : A ≤ blockB H (Lc i) := le_blockB_gen hA hmove
  obtain ⟨hUiB, hUi'⟩ := hUi
  obtain ⟨x, y, hxy, hAxy⟩ := M.single_transposition hdel hA hmove h5
  have hsw : Equiv.swap x y ∈ (A.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
    rw [hAxy]
    exact Subgroup.subset_closure (Set.mem_singleton _)
  obtain ⟨b₁, hb₁A, hb₁⟩ := hsw
  have hb₁' : M.ψ b₁ = Equiv.swap x y := hb₁
  have hb₁A' : (b₁ : V ≃ₗ[ZMod 2] V) ∈ A := hb₁A
  have hgen : ∀ σ ∈ (Ui.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom,
      σ ≠ Equiv.swap x y ∧ σ * Equiv.swap x y = Equiv.swap x y * σ := by
    intro σ hσ
    obtain ⟨b₂, hb₂U, hb₂⟩ := hσ
    have hb₂' : M.ψ b₂ = σ := hb₂
    have hb₂U' : (b₂ : V ≃ₗ[ZMod 2] V) ∈ Ui := hb₂U
    refine ⟨?_, ?_⟩
    · intro h
      have himg : M.ψ b₁ ∈ (Ui.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
        rw [hb₁', ← h]
        exact ⟨b₂, hb₂U, hb₂⟩
      have hmem : (b₁ : V ≃ₗ[ZMod 2] V) ∈ Ui := (M.mem_iff_image rfl b₁).2 himg
      have h1 : (b₁ : V ≃ₗ[ZMod 2] V) ∈ A ⊓ Ui := ⟨hb₁A', hmem⟩
      rw [hAU, Subgroup.mem_bot] at h1
      have h2 : b₁ = 1 := Subtype.ext h1
      rw [h2, map_one] at hb₁'
      exact swap_ne_one hxy hb₁'.symm
    · rw [← hb₂', ← hb₁', ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm _ hb₁A' _ hb₂U').symm
  have hsup : ∀ K : Subgroup (Equiv.Perm (ℙ F (Fin 2 → F))),
      (Ui.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom = K →
      ((A ⊔ Ui).subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom =
        Subgroup.closure {Equiv.swap x y} ⊔ K := by
    intro K hK
    rw [Subgroup.subgroupOf_sup hAB hUiB, Subgroup.map_sup, hAxy, hK]
  refine ⟨sup_le hAB hUiB, ?_⟩
  rcases hUi' with ⟨z, w, hzw, himg⟩ | ⟨z, w, z', w', hzw, hzz', hzw', hwz', hww', hz'w', himg⟩
  · have hσ : Equiv.swap z w ∈ (Ui.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
      rw [himg]
      exact Subgroup.subset_closure (Set.mem_singleton _)
    obtain ⟨hne, hc⟩ := hgen _ hσ
    obtain ⟨hxz, hxw, hyz, hyw⟩ := swap_ne_of_commute hxy hzw hne.symm hc
    refine Or.inr ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, ?_⟩
    rw [hsup _ himg, ← Subgroup.closure_union, ← Set.insert_eq]
  · exfalso
    have hσ₁ : Equiv.swap z w ∈ (Ui.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
      rw [himg]
      exact Subgroup.subset_closure (by simp)
    have hσ₂ : Equiv.swap z' w' ∈ (Ui.subgroupOf (blockB H (Lc i))).map M.ψ.toMonoidHom := by
      rw [himg]
      exact Subgroup.subset_closure (by simp)
    obtain ⟨hne₁, hc₁⟩ := hgen _ hσ₁
    obtain ⟨hne₂, hc₂⟩ := hgen _ hσ₂
    obtain ⟨hxz, hxw, hyz, hyw⟩ := swap_ne_of_commute hxy hzw hne₁.symm hc₁
    obtain ⟨hxz', hxw', hyz', hyw'⟩ := swap_ne_of_commute hxy hz'w' hne₂.symm hc₂
    exact not_three_disjoint_swaps h5 hxy hzw hz'w' hxz hxw hyz hyw hxz' hxw' hyz' hyw' hzz' hzw'
      hwz' hww'

theorem kc (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (I' : Finset (Fin r)) (U' : Fin r → Subgroup (V ≃ₗ[ZMod 2] V))
    (hU' : ∀ j ∈ I', IsTranspGroup (blockB H (Lc j)) (U' j) (delModelOf ctx hdel j).ψ)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hA : IsMinOffender H A) {i : Fin r}
    (hmove : ⁅Lc i, A⁆ ≠ ⊥) (hAD : A ⊓ (⨆ j ∈ I', U' j) = ⊥)
    (hcomm : ∀ a ∈ A, ∀ d ∈ (⨆ j ∈ I', U' j), a * d = d * a) :
    ∃ (I'' : Finset (Fin r)) (U'' : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)),
      (∀ j ∈ I'', IsTranspGroup (blockB H (Lc j)) (U'' j) (delModelOf ctx hdel j).ψ) ∧
      A ⊔ (⨆ j ∈ I', U' j) = ⨆ j ∈ I'', U'' j := by
  classical
  have h5 := card_five_of_deleted ctx hdel
  obtain ⟨x, y, hxy, hAxy⟩ := (delModelOf ctx hdel i).single_transposition hdel hA hmove h5
  have hAgood : IsTranspGroup (blockB H (Lc i)) A (delModelOf ctx hdel i).ψ :=
    ⟨le_blockB_gen hA hmove, Or.inl ⟨x, y, hxy, hAxy⟩⟩
  by_cases hi : i ∈ I'
  · have hUiD : U' i ≤ ⨆ j ∈ I', U' j := le_iSup₂_of_le i hi le_rfl
    have hAU : A ⊓ U' i = ⊥ := by
      rw [eq_bot_iff, ← hAD]
      exact inf_le_inf_left A hUiD
    have hgood := (delModelOf ctx hdel i).kc_step hdel h5 hA hmove (hU' i hi) hAU
      (fun a ha u hu => hcomm a ha u (hUiD hu))
    refine ⟨I', Function.update U' i (A ⊔ U' i), ?_, ?_⟩
    · intro j hj
      by_cases hji : j = i
      · subst hji
        simpa using hgood
      · rw [Function.update_of_ne hji]
        exact hU' j hj
    · apply le_antisymm
      · refine sup_le ?_ (iSup₂_le fun j hj => ?_)
        · exact le_iSup₂_of_le i hi (by simp)
        · by_cases hji : j = i
          · subst hji
            exact le_iSup₂_of_le j hj (by simp)
          · exact le_iSup₂_of_le j hj (by rw [Function.update_of_ne hji])
      · refine iSup₂_le fun j hj => ?_
        by_cases hji : j = i
        · subst hji
          simp only [Function.update_self]
          exact sup_le_sup_left hUiD _
        · rw [Function.update_of_ne hji]
          exact le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)
  · refine ⟨insert i I', Function.update U' i A, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · simpa using hAgood
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
        exact hU' j hj
    · rw [Finset.iSup_insert, Function.update_self]
      congr 1
      exact (iSup_congr fun j => iSup_congr fun hj => by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]).symm

theorem deleted_offender_iff (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) :
    IsOffender H E ↔ ∃ (I : Finset (Fin r)) (U : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)), I.Nonempty ∧
      (∀ i ∈ I, IsTranspGroup (blockB H (Lc i)) (U i) (delModelOf ctx hdel i).ψ) ∧
      E = ⨆ i ∈ I, U i := by
  classical
  have h5 := card_five_of_deleted ctx hdel
  constructor
  · intro hE
    suffices h : ∀ m : ℕ, ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), Nat.card E = m → IsOffender H E →
        ∃ (I : Finset (Fin r)) (U : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)),
          (∀ i ∈ I, IsTranspGroup (blockB H (Lc i)) (U i) (delModelOf ctx hdel i).ψ) ∧
          E = ⨆ i ∈ I, U i by
      obtain ⟨I, U, hU, hEeq⟩ := h _ E rfl hE
      refine ⟨I, U, ?_, hU, hEeq⟩
      by_contra hI
      rw [Finset.not_nonempty_iff_eq_empty] at hI
      subst hI
      apply hE.2.1
      rw [hEeq]
      simp
    have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro E hm hE
      obtain ⟨A, hAE, hA⟩ := exists_minOffender_le hE
      obtain ⟨-, i, hi, -⟩ := ctx.layer.offender A hA
      obtain ⟨D, hDE, hAD, hED, hD⟩ := deleted_offenderSplit ctx hdel A E hA hAE hE
      have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
        congrArg Subtype.val (hE.2.2.1.1.1.1 ⟨x, hx⟩ ⟨y, hy⟩)
      obtain ⟨x, y, hxy, hAxy⟩ := (delModelOf ctx hdel i).single_transposition hdel hA hi h5
      have hAgood : IsTranspGroup (blockB H (Lc i)) A (delModelOf ctx hdel i).ψ :=
        ⟨le_blockB_gen hA hi, Or.inl ⟨x, y, hxy, hAxy⟩⟩
      rcases hD with rfl | hDoff
      · refine ⟨{i}, fun _ => A, ?_, ?_⟩
        · intro j hj
          rw [Finset.mem_singleton] at hj
          subst hj
          exact hAgood
        · rw [hED, sup_bot_eq]
          simp
      · have hDne : D ≠ E := by
          intro hDE'
          apply hA.2.1
          rw [← hAD, eq_comm, inf_eq_left, hDE']
          exact hAE
        have hlt : Nat.card D < m := by
          rw [← hm]
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hDE) fun hcard => hDne ?_
          exact Subgroup.eq_of_le_of_card_ge hDE hcard.symm.le
        obtain ⟨I', U', hU', hDeq⟩ := ih (Nat.card D) hlt D rfl hDoff
        obtain ⟨I'', U'', hU'', hsup⟩ := kc ctx hdel I' U' hU' hA hi (hDeq ▸ hAD)
          (fun a ha d hd => hcommE a (hAE ha) d (hDE (hDeq ▸ hd)))
        exact ⟨I'', U'', hU'', hED.trans (by rw [hDeq]; exact hsup)⟩
  · rintro ⟨I, U, hne, hU, rfl⟩
    obtain ⟨hel, hw, hH⟩ := deleted_iSup_weight ctx hdel U I hU
    obtain ⟨j, hj⟩ := hne
    refine ⟨hH, ?_, hel, hw.ge⟩
    intro hbot
    apply (hU j hj).ne_bot
    rw [eq_bot_iff, ← hbot]
    exact le_iSup₂_of_le j hj le_rfl

theorem deleted_internal_product_iff (ctx : FamilyCtx H T n F r Lc)
    (hdel : ∀ A, IsMinOffender H A → ∀ i, ⁅Lc i, A⁆ ≠ ⊥ → DelData n (Lc i) A (ctx.α i))
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) :
    IsOffender H E ↔ ∃ s : Finset (Subgroup (V ≃ₗ[ZMod 2] V)), s.Nonempty ∧
      (∀ A ∈ s, IsMinOffender H A) ∧ IsInternalProduct E s := by
  classical
  constructor
  · intro hE
    exact offender_internal_product (deleted_offenderSplit ctx hdel) hE
  · rintro ⟨s, hne, hs, hind, rfl, hcomm⟩
    have key : ∀ s : Finset (Subgroup (V ≃ₗ[ZMod 2] V)), (∀ A ∈ s, IsMinOffender H A) →
        s.SupIndep id → (∀ A ∈ s, ∀ A' ∈ s, ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a) →
        ∃ (I : Finset (Fin r)) (U : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)),
          (∀ i ∈ I, IsTranspGroup (blockB H (Lc i)) (U i) (delModelOf ctx hdel i).ψ) ∧
          s.sup id = ⨆ i ∈ I, U i := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _ _ _
        exact ⟨∅, fun _ => ⊥, by simp, by simp⟩
      | insert A s' hAs' ih =>
        intro hs hind hcomm
        have hs' : ∀ A'' ∈ s', IsMinOffender H A'' := fun A'' h =>
          hs A'' (Finset.mem_insert_of_mem h)
        have hind' : s'.SupIndep id := hind.subset (Finset.subset_insert _ _)
        have hcomm' : ∀ A₁ ∈ s', ∀ A₂ ∈ s', ∀ a ∈ A₁, ∀ a' ∈ A₂, a * a' = a' * a :=
          fun A₁ h₁ A₂ h₂ => hcomm A₁ (Finset.mem_insert_of_mem h₁) A₂
            (Finset.mem_insert_of_mem h₂)
        obtain ⟨I', U', hU', hsup'⟩ := ih hs' hind' hcomm'
        have hA : IsMinOffender H A := hs A (Finset.mem_insert_self _ _)
        obtain ⟨-, i, hmove, -⟩ := ctx.layer.offender A hA
        have hdisj : Disjoint A (s'.sup id) :=
          hind (Finset.subset_insert A s') (Finset.mem_insert_self A s') hAs'
        have hAD : A ⊓ (⨆ j ∈ I', U' j) = ⊥ := by
          rw [← hsup']
          exact disjoint_iff.1 hdisj
        have hcommA : ∀ a ∈ A, ∀ d ∈ (⨆ j ∈ I', U' j), a * d = d * a := by
          rw [← hsup']
          have : s'.sup id ≤ Subgroup.centralizer (A : Set (V ≃ₗ[ZMod 2] V)) :=
            Finset.sup_le fun A'' hA''s z hz => Subgroup.mem_centralizer_iff.2 fun a ha =>
              hcomm A (Finset.mem_insert_self _ _) A'' (Finset.mem_insert_of_mem hA''s) a ha z hz
          intro a ha d hd
          exact Subgroup.mem_centralizer_iff.1 (this hd) a ha
        obtain ⟨I'', U'', hU'', hsup''⟩ := kc ctx hdel I' U' hU' hA hmove hAD hcommA
        refine ⟨I'', U'', hU'', ?_⟩
        rw [Finset.sup_insert]
        rw [← hsup'] at hsup''
        exact hsup''
    obtain ⟨I, U, hU, hsup⟩ := key s hs hind hcomm
    obtain ⟨hel, hw, hH⟩ := deleted_iSup_weight ctx hdel U I hU
    rw [hsup]
    obtain ⟨A, hAs⟩ := hne
    refine ⟨hH, ?_, hel, hw.ge⟩
    intro hbot
    apply (hs A hAs).2.1
    rw [eq_bot_iff, ← hbot, ← hsup]
    exact Finset.le_sup (f := id) hAs

end Classify

end CFSG.QuasithinUnique.Setup.Lift
