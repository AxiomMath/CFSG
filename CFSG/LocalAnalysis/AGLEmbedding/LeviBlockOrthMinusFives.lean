module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusVoid
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenFive
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinTorus

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail LeviBlock Matrix

namespace LeviBlock

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

omit [CharP K 2] in
theorem orthLeviBlock_inl_of_sixty {f : ℕ} (hK : Nat.card K = 2 ^ f) (l : Fin s)
    (hq : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c (.inl l)))
    (h60 : Nat.card (↥(orthLeviBlock K r d b c (.inl l)) ⧸
      Subgroup.center ↥(orthLeviBlock K r d b c (.inl l))) = 60) :
    d l.succ - d l.castSucc = 2 ∧ Nat.card K = 4 := by
  change CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range at hq
  change Nat.card (↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range ⧸
    Subgroup.center ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range) = 60 at h60
  have h2 := two_le_of_isQuasisimple_specialLinear
    (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) _).symm hq)
  rw [card_range_toGL_quotient_center (by omega)] at h60
  obtain ⟨h1, h4⟩ := (ordA_eq_sixty_iff hK).1 h60
  exact ⟨by omega, h4⟩

theorem orthLeviBlock_inr_of_sixty {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (u : Unit)
    (hq : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c (.inr u)))
    (h60 : Nat.card (↥(orthLeviBlock K r d b c (.inr u)) ⧸
      Subgroup.center ↥(orthLeviBlock K r d b c (.inr u))) = 60) : Nat.card K = 2 := by
  obtain ⟨-, -, h⟩ := card_orthResDer_quotient_center hK hirr hq
  change Nat.card (↥(orthResDer K b c (r - d (Fin.last s))) ⧸
    Subgroup.center ↥(orthResDer K b c (r - d (Fin.last s)))) = 60 at h60
  rw [h] at h60
  rw [hK]
  exact ((ordTwistedD_eq_sixty_iff rfl).1 h60).2

theorem card_eq_four_and_six_le (hd : OrthCuts r d) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h3 : 3 ≤ Nat.card {j // CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j) ∧
      Nat.card (↥(orthLeviBlock K r d b c j) ⧸ Subgroup.center ↥(orthLeviBlock K r d b c j)) =
        60}) : Nat.card K = 4 ∧ 6 ≤ r := by
  classical
  obtain ⟨f, hK⟩ := orthMinus_card_eq_two_pow (K := K)
  set p : Fin s ⊕ Unit → Prop := fun j => CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j) ∧
    Nat.card (↥(orthLeviBlock K r d b c j) ⧸ Subgroup.center ↥(orthLeviBlock K r d b c j)) = 60
  have hcard : Nat.card (Subtype p) = (Finset.univ.filter p).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change 3 ≤ Nat.card (Subtype p) at h3
  have h4 : Nat.card K = 4 := by
    by_contra h4
    have hsub : Finset.univ.filter p ⊆ {.inr ()} := by
      intro j hj
      rcases j with l | u
      · exact absurd (orthLeviBlock_inl_of_sixty hK l (Finset.mem_filter.1 hj).2.1
          (Finset.mem_filter.1 hj).2.2).2 h4
      · simp
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton, ← hcard] at this
    omega
  refine ⟨h4, ?_⟩
  set B : Finset (Fin s) := Finset.univ.filter fun l => d l.succ - d l.castSucc = 2
  have hsub : Finset.univ.filter p ⊆ B.map Function.Embedding.inl := by
    intro j hj
    rcases j with l | u
    · exact Finset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _,
        (orthLeviBlock_inl_of_sixty hK l (Finset.mem_filter.1 hj).2.1
          (Finset.mem_filter.1 hj).2.2).1⟩)
    · exact absurd (orthLeviBlock_inr_of_sixty hK hirr u (Finset.mem_filter.1 hj).2.1
        (Finset.mem_filter.1 hj).2.2) (by omega)
  have hB : 3 ≤ B.card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_map, ← hcard] at this
    omega
  let φ : {l // l ∈ B} × Fin 2 → Fin r := fun x =>
    orthBlockIdx hd x.1.1 (Fin.cast (Finset.mem_filter.1 x.1.2).2.symm x.2)
  have hφ : Function.Injective φ := by
    rintro ⟨⟨l, hl⟩, i⟩ ⟨⟨l', hl'⟩, i'⟩ h
    by_cases hll : l = l'
    · subst hll
      have := orthBlockIdx_injective hd l h
      exact Prod.ext rfl (Fin.ext (by simpa using congrArg Fin.val this))
    · exact absurd h (orthBlockIdx_ne hd hll _ _)
  have := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := {l // l ∈ B}), Fintype.card_coe,
    Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, Nat.card_fin] at this
  omega

variable (K r) in
@[expose] noncomputable def orthDMapOneHom :
    GL (Fin r) K →* ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))
    where
  toFun D := dMap D (1 : (Fin 2 → K) ≃ₗ[K] _)
  map_one' := dMap_one_one
  map_mul' D D' := by rw [dMap_mul_dMap, mul_one]

variable (b c) in
@[expose] noncomputable def orthTorus (hr : 6 ≤ r) :
    (Fin 4 → Kˣ) →* ↥(orthParab r (minusTailForm K b c) d) :=
  (((orthDMapOneHom K r).comp ((SpecialLinearGroup.toGL).comp
    (torusFour K (n := r) (by omega)))).codRestrict
      (orthElementaryGroup (quadTail r (minusTailForm K b c))) fun t =>
        NonsplitOrthogonalCover.dMap_one_mem_orthElementaryGroup (by omega)
          (torusFour K (n := r) (by omega) t).2).codRestrict _ fun t =>
    mem_orthParab.2 fun i => map_tailFlag_dMap (blockTriangular_diagonal _) _ _

omit [Finite K] in
theorem orthTorus_injective (hr : 6 ≤ r) :
    Function.Injective (orthTorus b c hr (K := K) (d := d)) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have h1 : dMap (SpecialLinearGroup.toGL (torusFour K (n := r) (by omega) t))
      (1 : (Fin 2 → K) ≃ₗ[K] _) = 1 := congrArg (fun x : ↥(orthParab r (minusTailForm K b c) d) =>
        ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
          ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))) ht
  have h2 := congrArg orthCoefMat h1
  rw [orthCoefMat_dMap, orthCoefMat_one] at h2
  have h3 : torusFour K (n := r) (by omega) t = 1 := Subtype.ext h2
  exact eq_one_of_torusFour_mem_center hr (h3 ▸ Subgroup.one_mem _)

end LeviBlock

theorem kFactCompParabThreeFivesOn_twistedD (hZ : OddCenterRest) :
    KFactCompParabThreeFivesOn (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP ⟨dI, hdI, ⟨e⟩⟩
  obtain ⟨K, _, _, _, b, c, r, s, d, ρ, hr, hirr, hcuts, hρ, -⟩ :=
    exists_orthCover_of_twistedD hZ hCP dI hdI e
  intro O J _ hPO _ hsec hJ hJc
  set f : ↥(orthParab r (minusTailForm K b c) d) →* Y :=
    L.subtype.comp (ρ.toMonoidHom.comp (orthParab r (minusTailForm K b c) d).subtype) with hfdef
  have hf : f.range = P := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have hx : (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) ∈
          (P.subgroupOf L).comap ρ.toMonoidHom := by
        rw [hρ]
        exact x.2
      exact Subgroup.mem_subgroupOf.1 hx
    · intro p hp
      obtain ⟨x, hx⟩ := ρ.surjective ⟨p, hCP.parab.1 hp⟩
      have hxP : x ∈ orthParab r (minusTailForm K b c) d := by
        rw [← hρ, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hx]
        exact Subgroup.mem_subgroupOf.2 hp
      exact ⟨⟨x, hxP⟩, by simp [hfdef, hx]⟩
  have h3 := three_le_card_fiveBlocks f hf (orthLeviHom b c hcuts) (isPGroup_ker_orthLeviHom hcuts)
    (pi_orthLeviBlock_le_range hcuts hr (commutator_orthogonalGroup_quadTail_minus hr hirr))
    (commutator_range_orthLeviHom_le hcuts) (isQuasisimple_or_isSolvable_orthLeviBlock hirr)
    (orthLeviBlock_card_of_sixty hirr) hPO hsec hJ hJc
  obtain ⟨h4, hr6⟩ := card_eq_four_and_six_le hcuts hirr h3
  have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, h4]
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b)
    (fun a => ?_) ?_ (f.comp (orthTorus b c hr6)) ?_ ?_
  · funext j
    rw [Pi.pow_apply, Pi.one_apply, ← hunits]
    exact pow_card_eq_one'
  · rw [Nat.card_fun, hunits, Nat.card_fin]
  · refine (L.subtype_injective.comp (ρ.injective.comp Subtype.val_injective)).comp
      (orthTorus_injective hr6)
  · rintro _ ⟨t, rfl⟩
    rw [← hf]
    exact ⟨_, rfl⟩

end CFSG.AGLEmbedding
