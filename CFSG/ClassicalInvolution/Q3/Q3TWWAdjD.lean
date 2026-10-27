module

public import CFSG.ClassicalInvolution.Q3.Q3TWWLayer
public import CFSG.ClassicalInvolution.Q3.Q3TWWEvalD
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjChain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open scoped MatrixGroups

local notation "bA0" => (blockSL (ZMod 3) 3 2 0 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "bA1" => (blockSL (ZMod 3) 3 2 1 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))

section Absorb

variable {H : Type} [Group H]

@[expose] def AbsorbsT (L : TwistedLayer H) (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) : Prop :=
  ∃ (t : SL(3, ZMod 3)) (B : H),
    (∀ A, t * bA0 A * t⁻¹ = bA0 A) ∧
    (∀ A, ∃ A', t * bA1 A * t⁻¹ = bA1 A') ∧
    (∀ A', ∃ A, t * bA1 A * t⁻¹ = bA1 A') ∧
    (∀ A A', t * bA1 A * t⁻¹ = bA1 A' → B⁻¹ * L.lbZ A * B = L.lbZ (α.symm A')) ∧
    (∀ s ∈ L.S, B * s * B⁻¹ ∈ L.S) ∧ (∀ s ∈ L.S, B⁻¹ * s * B ∈ L.S)

theorem absorbsT_id (L : TwistedLayer H) (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3))
    (hp : α autXp = autXp) (hm : α autXm = autXm) : AbsorbsT L α := by
  have hα : α = MulEquiv.refl _ := alpha_eq_of_gens hp hm
  refine ⟨1, 1, fun A => by simp, fun A => ⟨A, by simp⟩, fun A' => ⟨A', by simp⟩, ?_,
    fun s hs => by simpa using hs, fun s hs => by simpa using hs⟩
  intro A A' h
  have h1 : A' = A := blockSL_one_injective (by simpa using h.symm)
  subst h1
  subst hα
  simp

theorem absorbsT_flip (L : TwistedLayer H) (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3))
    (hp : α autXp = autXp⁻¹) (hm : α autXm = autXm⁻¹) : AbsorbsT L α := by
  have hα : ∀ A, α A = flipSLg A := fun A => DFunLike.congr_fun
    (hom_ext_of_gens (f := α.toMonoidHom) (g := flipHom) (by simpa [flipHom, flip_autXp] using hp)
      (by simpa [flipHom, flip_autXm] using hm)) A
  refine ⟨twAg (ZMod 3), 1, twAg_conj_bA0, fun A => ⟨flipSLg A, twAg_conj_bA1 A⟩,
    fun A' => ⟨flipSLg A', by rw [twAg_conj_bA1, flipSLg_flipSLg]⟩, ?_,
    fun s hs => by simpa using hs, fun s hs => by simpa using hs⟩
  intro A A' h
  rw [twAg_conj_bA1] at h
  have h1 : A' = flipSLg A := (blockSL_one_injective h).symm
  subst h1
  have h2 : α.symm (flipSLg A) = A := by
    rw [MulEquiv.symm_apply_eq, hα]
  rw [h2]
  simp

theorem absorbsT_swapInv (L : TwistedLayer H) (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3))
    (hp : α autXp = autXm⁻¹) (hm : α autXm = autXp⁻¹) : AbsorbsT L α := by
  have hα : ∀ A, α ((absD 0)⁻¹ * A * absD 0) = A := fun A => by
    have := DFunLike.congr_fun
      (hom_ext_of_gens
        (f := α.toMonoidHom.comp (MulAut.conj (absD 0)⁻¹).toMonoidHom) (g := MonoidHom.id _)
        (by simp [absD0_inv_conj_xp, hm]) (by simp [absD0_inv_conj_xm, hp])) A
    simpa using this
  refine ⟨1, L.B, fun A => by simp, fun A => ⟨A, by simp⟩, fun A' => ⟨A', by simp⟩, ?_,
    L.B_S, L.B_S'⟩
  intro A A' h
  have h1 : A' = A := blockSL_one_injective (by simpa using h.symm)
  rw [h1, L.B_lb, (MulEquiv.symm_apply_eq α).2 (hα A).symm]

theorem absorbsT_swap (L : TwistedLayer H) (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3))
    (hp : α autXp = autXm) (hm : α autXm = autXp) : AbsorbsT L α := by
  have hα : ∀ A, α ((absD 0)⁻¹ * A * absD 0) = flipSLg A := fun A => by
    have := DFunLike.congr_fun
      (hom_ext_of_gens
        (f := α.toMonoidHom.comp (MulAut.conj (absD 0)⁻¹).toMonoidHom) (g := flipHom)
        (by simp [absD0_inv_conj_xp, hm, flipHom, flip_autXp])
        (by simp [absD0_inv_conj_xm, hp, flipHom, flip_autXm])) A
    simpa [show flipHom A = flipSLg A from rfl] using this
  refine ⟨twAg (ZMod 3), L.B, twAg_conj_bA0, fun A => ⟨flipSLg A, twAg_conj_bA1 A⟩,
    fun A' => ⟨flipSLg A', by rw [twAg_conj_bA1, flipSLg_flipSLg]⟩, ?_, L.B_S, L.B_S'⟩
  intro A A' h
  rw [twAg_conj_bA1] at h
  have h1 : A' = flipSLg A := (blockSL_one_injective h).symm
  rw [h1, L.B_lb, (MulEquiv.symm_apply_eq α).2 (hα A).symm]

theorem absorbT (L : TwistedLayer H) (k : Fin 4) (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3))
    (hp : α autXp = absImgP k) (hm : α autXm = absImgM k) : AbsorbsT L α := by
  fin_cases k
  · exact absorbsT_swapInv L α (by simpa [absImgP] using hp) (by simpa [absImgM] using hm)
  · exact absorbsT_flip L α (by simpa [absImgP] using hp) (by simpa [absImgM] using hm)
  · exact absorbsT_id L α (by simpa [absImgP] using hp) (by simpa [absImgM] using hm)
  · exact absorbsT_swap L α (by simpa [absImgP] using hp) (by simpa [absImgM] using hm)

end Absorb

section Adjust

variable {H G : Type} [Group H] [Group G]

theorem exists_adjust_td4 (L : TwistedLayer H) (V0 V1 V2 : Subgroup G)
    (hcomm : ∀ a ∈ V0, ∀ b ∈ V2, a * b = b * a) (hC : TD4Collapse)
    (θA : SL(3, ZMod 3) →* G) (hιA : Function.Injective (θA.comp bA1))
    (hA0 : (bA0).range.map θA = V0) (hA1 : (bA1).range.map θA = V1)
    (θ : H →* G) (hιL : Function.Injective (θ.comp L.lbZ))
    (hB1 : L.lbZ.range.map θ = V1) (hB2 : L.S.map θ = V2) :
    ∃ (θA' : SL(3, ZMod 3) →* G) (θ' : H →* G),
      θA'.comp bA0 = θA.comp bA0 ∧ (∀ A, θ' (L.lbZ A) = θA' (bA1 A)) ∧
      Function.Injective (θA'.comp bA1) ∧ (bA1).range.map θA' = V1 ∧
      L.S.map θ' = V2 := by
  have hrA : (θA.comp bA1).range = V1 := by rw [MonoidHom.range_comp]; exact hA1
  have hrB : (θ.comp L.lbZ).range = V1 := by rw [MonoidHom.range_comp]; exact hB1
  obtain ⟨α, hα⟩ := exists_mulEquiv_of_range_eq hιA hιL (hrA.trans hrB.symm)
  have hα' : ∀ a, θA (bA1 (α a)) = θ (L.lbZ a) := hα
  have hrelA : RelsHold (fun j => θA (a2Mat j)) a2Words := relsHold_hom θA a2_relsHold
  have m0p : θA (a2Mat 0) ∈ V0 := by
    rw [a2Mat_zero, ← hA0]
    exact mem_map_range θA _ xpS
  have m0m : θA (a2Mat 1) ∈ V0 := by
    rw [a2Mat_one, ← hA0]
    exact mem_map_range θA _ xmS
  obtain ⟨k, hp, hm⟩ := aut_pair_cases α
  by_cases hk : k.val < 4
  ·
    obtain ⟨j, rfl⟩ : ∃ j : Fin 4, Fin.castLE (by norm_num) j = k :=
      ⟨⟨k.val, hk⟩, Fin.ext rfl⟩
    rw [evalW_gluingA_castLE] at hp
    rw [evalW_gluingB_castLE] at hm
    obtain ⟨t, B, ht0, htA, htA', htL, hBS, hBS'⟩ := absorbT L j α hp hm
    let θA' : SL(3, ZMod 3) →* G := θA.comp (MulAut.conj t).toMonoidHom
    let θ' : H →* G := θ.comp (MulAut.conj B⁻¹).toMonoidHom
    have hθA' : ∀ x, θA' x = θA (t * x * t⁻¹) := fun x => rfl
    have hθ' : ∀ x, θ' x = θ (B⁻¹ * x * B) := by
      intro x
      simp [θ']
    have hLA : ∀ A A', t * bA1 A * t⁻¹ = bA1 A' → θA' (bA1 A) = θA (bA1 A') := by
      intro A A' h
      rw [hθA', h]
    refine ⟨θA', θ', ?_, ?_, ?_, ?_, ?_⟩
    · refine MonoidHom.ext fun A => ?_
      show θA (t * bA0 A * t⁻¹) = θA (bA0 A)
      rw [ht0]
    · intro A
      obtain ⟨A', hA'⟩ := htA A
      rw [hLA A A' hA', hθ', htL A A' hA', ← hα' (α.symm A'), α.apply_symm_apply]
    · intro A₁ A₂ h
      obtain ⟨A₁', h₁⟩ := htA A₁
      obtain ⟨A₂', h₂⟩ := htA A₂
      have h' : (θA.comp bA1) A₁' = (θA.comp bA1) A₂' := by
        have := h
        simp only [MonoidHom.comp_apply] at this ⊢
        rw [hLA A₁ A₁' h₁, hLA A₂ A₂' h₂] at this
        exact this
      have hA' : A₁' = A₂' := hιA h'
      subst hA'
      have : bA1 A₁ = bA1 A₂ := by
        have e : t * bA1 A₁ * t⁻¹ = t * bA1 A₂ * t⁻¹ := by rw [h₁, h₂]
        simpa using e
      exact blockSL_one_injective this
    · rw [← hA1]
      ext x
      constructor
      · rintro ⟨y, ⟨A, rfl⟩, rfl⟩
        obtain ⟨A', hA'⟩ := htA A
        rw [hLA A A' hA']
        exact mem_map_range θA _ A'
      · rintro ⟨y, ⟨A', rfl⟩, rfl⟩
        obtain ⟨A, hA⟩ := htA' A'
        exact ⟨bA1 A, ⟨A, rfl⟩, hLA A A' hA⟩
    · rw [← hB2]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [hθ']
        exact ⟨B⁻¹ * y * B, hBS' y hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨B * y * B⁻¹, hBS y hy, ?_⟩
        rw [hθ']
        congr 1
        group
  ·
    exfalso
    have hk' : gluingComplete k = false := decide_eq_false hk
    have hrelC : RelsHold (fun j => θ (L.e j)) su4Words := relsHold_hom θ L.rels
    have mS : ∀ j, L.e j ∈ L.S → θ (L.e j) ∈ V2 := fun j hj => by
      rw [← hB2]
      exact Subgroup.mem_map_of_mem θ hj
    have m6 := mS 6 L.eS6
    have m7 := mS 7 L.eS7
    have m8 := mS 8 L.eS8
    have m9 := mS 9 L.eS9
    set fA : Fin 6 → G := fun j => θA (a2Mat j) with hfA
    set fC : Fin 12 → G := fun j => θ (L.e j) with hfC
    have hp' : (gOfD fA fC ∘ ext12) xPlus = (θA.comp bA1) autXp := by
      show θA (a2Mat 4) = θA (bA1 autXp)
      rw [a2Mat_four, adj_autXp_eq]
    have hm' : (gOfD fA fC ∘ ext12) xMinus = (θA.comp bA1) autXm := by
      show θA (a2Mat 5) = θA (bA1 autXm)
      rw [a2Mat_five, adj_autXm_eq]
    have ha : evalW (gOfD fA fC) (mapWord ext12 (gluingA k)) = fC 2 := by
      rw [evalW_mapWord, evalW_gluingA_map (θA.comp bA1) _ hp' hm' k, ← hp]
      show θA (bA1 (α autXp)) = θ (L.e 2)
      rw [hα' autXp, L.e2]
    have hb : evalW (gOfD fA fC) (mapWord ext12 (gluingB k)) = fC 3 := by
      rw [evalW_mapWord, evalW_gluingB_map (θA.comp bA1) _ hp' hm' k, ← hm]
      show θA (bA1 (α autXm)) = θ (L.e 3)
      rw [hα' autXm, L.e3]
    have hrels : RelsHold (gOfD fA fC) (td4aWords k) :=
      relsHold_td4Glued fA fC hrelA hrelC _ _ ha hb (hcomm _ m0p _ m6) (hcomm _ m0p _ m7)
        (hcomm _ m0p _ m8) (hcomm _ m0p _ m9) (hcomm _ m0m _ m6) (hcomm _ m0m _ m7)
        (hcomm _ m0m _ m8) (hcomm _ m0m _ m9)
    have h9 := hC k hk' _ hrels 9
    have h9' : θA (bA1 xpS) = θA (bA1 1) := by
      have e : gOfD fA fC 9 = θA (bA1 xpS) := by
        show θA (a2Mat 4) = _
        rw [a2Mat_four]
      rw [e] at h9
      rw [h9, map_one, map_one]
    exact adj_xpS_ne_one (hιA (a₁ := xpS) (a₂ := 1) h9')

end Adjust

end CFSG.ClassicalInvolution.Q3.Q3TW
