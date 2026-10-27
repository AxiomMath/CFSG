module

public import CFSG.LieType.Steinberg.CentralExt.GriessGTwoThree
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5Cover
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5Central
public import Certificates.Certificate271037
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Sporadic.He.Native CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.G23 CFSG.Open CFSG.RankThree.PerfectCover
  CFSG.LieType.Steinberg.CentralExt

@[expose] noncomputable def rootC (j : Fin 4) : Cov :=
  PresentedGroup.mk _ (FreeGroup.mk (genWord j))

noncomputable def eltC : List (Fin 4) → Cov
  | [] => 1
  | j :: w => rootC j * eltC w

section Facts


@[expose] noncomputable def rhoC : Cov →* GL (Fin 54) (ZMod 2) :=
  PresentedGroup.toGroup lift_coverGL_coverRelators

theorem rhoC_mk (w : List (Fin 2 × Bool)) :
    rhoC (PresentedGroup.mk _ (FreeGroup.mk w) : Cov) = FreeGroup.lift coverGL (FreeGroup.mk w) :=
  rfl

theorem mat_eltC (w : List (Fin 4)) :
    ((rhoC (eltC w) : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) =
      toMat 2 54 (prodArr 2 54 coverRoot w) := by
  induction w with
  | nil => rw [eltC, map_one, Units.val_one, prodArr, List.foldr_nil, toMat_idM]
  | cons j w ih =>
    have hj : ((rhoC (rootC j) : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) =
        toMat 2 54 (coverRoot j) := by
      rw [rootC, rhoC_mk]
      exact val_lift_coverGL (genWord j)
    have hcons : prodArr 2 54 coverRoot (j :: w) =
        mulM 2 54 (coverRoot j) (prodArr 2 54 coverRoot w) := rfl
    rw [eltC, map_mul, Units.val_mul, ih, hj, hcons, toMat_mulM]

theorem mat_one_C : ((rhoC (1 : Cov) : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) =
    toMat 2 54 (idM 54) := by
  rw [map_one, Units.val_one, toMat_idM]

theorem mat_mul_C {x y : Cov} {X Y : Array (Array ℕ)}
    (hx : ((rhoC x : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) = toMat 2 54 X)
    (hy : ((rhoC y : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) = toMat 2 54 Y) :
    ((rhoC (x * y) : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) =
      toMat 2 54 (mulM 2 54 X Y) := by
  rw [map_mul, Units.val_mul, hx, hy, toMat_mulM]

theorem eq_of_beq_C (hρ : Function.Injective (rhoC : Cov →* GL (Fin 54) (ZMod 2))) {x y : Cov}
    {X Y : Array (Array ℕ)}
    (hx : ((rhoC x : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) = toMat 2 54 X)
    (hy : ((rhoC y : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) = toMat 2 54 Y)
    (h : (X == Y) = true) : x = y :=
  hρ (Units.ext (by rw [hx, hy]; exact toMat_eq_of_beq h))

theorem ne_one_of_entry_C {x : Cov} {X : Array (Array ℕ)} {i j : Fin 54} (hij : i ≠ j)
    (hx : ((rhoC x : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) = toMat 2 54 X)
    (h : (entryOf X i.val j.val == 1) = true) : x ≠ 1 := by
  intro hx1
  rw [hx1, map_one, Units.val_one] at hx
  have h1 := congrFun (congrFun hx i) j
  rw [Matrix.one_apply_ne hij, toMat_apply] at h1
  rw [beq_iff_eq] at h
  have h2 : ((X[i.val]!)[j.val]! : ZMod 2) = 1 := by
    change ((entryOf X i.val j.val : ℕ) : ZMod 2) = 1
    rw [h]
    rfl
  rw [h2] at h1
  exact absurd h1.symm (by decide)

noncomputable def c0C : Cov :=
  eltC uW * (eltC a2W * ((eltC uW * eltC uW) * (eltC a2W * eltC a2W)))


theorem cover_facts_emb (hρ : Function.Injective (rhoC : Cov →* GL (Fin 54) (ZMod 2))) :
    CoverCfg (eltC uW) (eltC vW) (eltC a1W) (eltC a2W) c0C := by
  have h := Certificates.certificate271037
  simp only [coverEmbCheck, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have hU : _ = toMat 2 54 covU := mat_eltC uW
  have hV : _ = toMat 2 54 covV := mat_eltC vW
  have hA1 : _ = toMat 2 54 covA1 := mat_eltC a1W
  have hA2 : _ = toMat 2 54 covA2 := mat_eltC a2W
  have hC0 : ((rhoC c0C : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) =
      toMat 2 54 covC0 :=
    mat_mul_C hU (mat_mul_C hA2 (mat_mul_C (mat_mul_C hU hU) (mat_mul_C hA2 hA2)))
  have hone := mat_one_C
  have cube : ∀ {x : Cov} {X : Array (Array ℕ)},
      ((rhoC x : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) = toMat 2 54 X →
      (mulM 2 54 X (mulM 2 54 X X) == idM 54) = true → x ^ 3 = 1 := by
    intro x X hx hb
    rw [pow_three]
    exact eq_of_beq_C hρ (mat_mul_C hx (mat_mul_C hx hx)) hone hb
  have comm : ∀ {x y : Cov} {X Y : Array (Array ℕ)},
      ((rhoC x : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) = toMat 2 54 X →
      ((rhoC y : GL (Fin 54) (ZMod 2)) : Matrix (Fin 54) (Fin 54) (ZMod 2)) = toMat 2 54 Y →
      (mulM 2 54 X Y == mulM 2 54 Y X) = true → x * y = y * x := by
    intro x y X Y hx hy hb
    exact eq_of_beq_C hρ (mat_mul_C hx hy) (mat_mul_C hy hx) hb
  refine ⟨cube hA1 h1, cube hA2 h2, cube hC0 h4, comm hC0 hU h5, comm hC0 hV h6, comm hC0 hA1 h7,
    comm hC0 hA2 h8, comm hA1 hA2 h9, comm hV hA2 h10, ?_, ?_, ?_⟩
  · rw [mul_assoc]
    exact eq_of_beq_C hρ (mat_mul_C hU hA2) (mat_mul_C hC0 (mat_mul_C hA2 hU)) h11
  · rw [mul_assoc, mul_assoc]
    exact eq_of_beq_C hρ (mat_mul_C hV hA1)
      (mat_mul_C hC0 (mat_mul_C hC0 (mat_mul_C hA1 hV))) h12
  · exact ne_one_of_entry_C (i := 0) (j := 1) (by decide) hC0 h13

end Facts

section Inj

variable
  {K : Type} [Field K] (σ : K ≃+* ZMod 3)

theorem card_ker_coverMap (hK : Nat.card K = 3) :
    Nat.card (coverMap (isPresentation σ hK) (lift_gens_commWords σ)).ker = 3 := by
  have hw : ∀ i, FreeGroup.mk (commWords (pairs i)) ∈ commutator (FreeGroup (Fin 2)) :=
    fun i => mk_commWords_mem_commutator _
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have eX : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  rw [← Nat.card_congr (griessHopfMultiplierEquivKer (isPresentation σ hK) hw
    (lift_gens_commWords σ)).toEquiv, ← Nat.card_congr (griessHopfMultiplierCongr eX).toEquiv]
  exact (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.g2_three_card_griessHopfMultiplier
    hK).2

include σ in
theorem rhoC_injective (hK : Nat.card K = 3) (hX : IsSimpleGroup (adjointGroup .G2 K)) :
    Function.Injective (rhoC : Cov →* GL (Fin 54) (ZMod 2)) := by
  have hw : ∀ i, FreeGroup.mk (commWords (pairs i)) ∈ commutator (FreeGroup (Fin 2)) :=
    fun i => mk_commWords_mem_commutator _
  have hP := isPresentation σ hK
  have hwg := lift_gens_commWords σ
  have hr6 : (PresentedGroup.mk _ (FreeGroup.mk relSix) : Cov) ∈ (coverMap hP hwg).ker := by
    rw [MonoidHom.mem_ker, coverMap_mk]
    exact hP.lift_eq_one (List.mem_map_of_mem relSix_mem)
  have hne : rhoC (PresentedGroup.mk _ (FreeGroup.mk relSix) : Cov) ≠ 1 := by
    intro h
    apply cover_facts.2.2.2.2
    rw [← val_lift_coverGL relSix, ← rhoC_mk, h, Units.val_one]
  have := hX
  exact injective_of_perfect_central (coverMap hP hwg) (coverMap_surjective hP hwg)
    (coverMap_ker_le_center hP hwg) (presentedCover_isPerfect hw).commutator_eq_top
    (card_ker_coverMap σ hK) rhoC hr6 hne


include σ in
theorem cover_bound_cov (hK : Nat.card K = 3) (hX : IsSimpleGroup (adjointGroup .G2 K))
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ρ : Cov →* MulAut V)
    (hρ : Function.Injective ρ) : 2 ^ 18 ≤ Nat.card V :=
  cover_bound hV (cover_facts_emb (rhoC_injective σ hK hX)) ρ hρ

end Inj

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
