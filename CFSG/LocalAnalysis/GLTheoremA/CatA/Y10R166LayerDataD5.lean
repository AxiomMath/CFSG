module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataD3
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusFour
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Glue
public import CFSG.ClassicalGroups.F2Fixed.SL2Fixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaPair

open Subgroup CFSG.Open
open CFSG.SeitzReduction.OmegaPilot
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv
  regular_coordinateQuadPlus)
open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private noncomputable def planeParamFun (m : ℕ) [NeZero m] (q : ℕ)
    (x : rootsOfUnity q F × rootsOfUnity q F) (i : Fin m) : rootsOfUnity q F :=
  if i = 0 then x.1 else if i = 1 then x.1 else if i = 2 then x.2 else 1

private noncomputable def planeParamHom (m : ℕ) [NeZero m] (q : ℕ) :
    (rootsOfUnity q F × rootsOfUnity q F) →* (Fin m → rootsOfUnity q F) where
  toFun := planeParamFun (F := F) m q
  map_one' := by
    funext i
    simp only [planeParamFun]
    split_ifs <;> simp
  map_mul' x y := by
    funext i
    simp only [planeParamFun, Pi.mul_apply, Prod.fst_mul, Prod.snd_mul]
    split_ifs <;> simp

private theorem planeParamHom_apply {m : ℕ} [NeZero m] (q : ℕ)
    (x : rootsOfUnity q F × rootsOfUnity q F) (i : Fin m) :
    planeParamHom (F := F) m q x i = planeParamFun (F := F) m q x i := rfl

private theorem planeParamHom_injective {m : ℕ} [NeZero m] {q : ℕ} (hm : 4 ≤ m) :
    Function.Injective (planeParamHom (F := F) m q) := by
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  have h0 := congrFun h (0 : Fin m)
  have h2 := congrFun h (2 : Fin m)
  have h0' : a₁ = b₁ := by simpa [planeParamHom_apply, planeParamFun] using h0
  have h2' : a₂ = b₂ := by
    simpa [planeParamHom_apply, planeParamFun, two_ne_zero_fin hm, two_ne_one_fin hm] using h2
  exact Prod.ext h0' h2'

private theorem planeParamHom_apply_zero_eq_one {m : ℕ} [NeZero m] {q : ℕ} (hm : 4 ≤ m)
    (x : rootsOfUnity q F × rootsOfUnity q F) :
    ((planeParamHom (F := F) m q x (0 : Fin m) : rootsOfUnity q F) : Fˣ) =
      ((planeParamHom (F := F) m q x (1 : Fin m) : rootsOfUnity q F) : Fˣ) := by
  simp [planeParamHom_apply, planeParamFun, one_ne_zero_fin hm]

private theorem planeParamHom_pair_one {m : ℕ} [NeZero m] {q : ℕ} (hm : 4 ≤ m) {ζ : Fˣ}
    (hζq : ζ ^ q = 1) :
    (fun i => (((planeParamHom (F := F) m q
        (⟨ζ, (mem_rootsOfUnity q ζ).2 hζq⟩, 1)) i : rootsOfUnity q F) : Fˣ)) =
      torusParam m ζ := by
  funext i
  rw [torusParam_apply hm, planeParamHom_apply, planeParamFun]
  by_cases h0 : i = 0
  · rw [if_pos h0, if_pos (Or.inl h0)]
  by_cases h1 : i = 1
  · rw [if_neg h0, if_pos h1, if_pos (Or.inr h1)]
  rw [if_neg h0, if_neg h1]
  by_cases h2 : i = 2
  · rw [if_pos h2, if_neg (by tauto : ¬ (i = 0 ∨ i = 1))]; simp
  · rw [if_neg h2, if_neg (by tauto : ¬ (i = 0 ∨ i = 1))]; simp

private noncomputable def twoPlaneTorus (m q : ℕ) [NeZero m] :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus m F)) :=
  ((qTorusHom (K := F) m q).comp (planeParamHom (F := F) m q)).range

private theorem twoPlaneTorus_le_qTorus {m q : ℕ} [NeZero m] :
    twoPlaneTorus (F := F) m q ≤ qTorus (K := F) m q := by
  intro x hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hx
  rw [qTorus_eq_range]
  exact MonoidHom.mem_range.2 ⟨planeParamHom (F := F) m q y, rfl⟩

private theorem card_twoPlaneTorus {m n q : ℕ} [NeZero m] (hm : 4 ≤ m)
    (hF : Nat.card F = 2 ^ n) (hq : q.Prime) (hqF : q ∣ Nat.card F - 1) :
    Nat.card (twoPlaneTorus (F := F) m q) = q ^ 2 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hinj : Function.Injective
      ((qTorusHom (K := F) m q).comp (planeParamHom (F := F) m q)) :=
    (qTorusHom_injective (K := F) m q).comp (planeParamHom_injective (F := F) hm)
  change Nat.card ↥(((qTorusHom (K := F) m q).comp
    (planeParamHom (F := F) m q)).range) = q ^ 2
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj,
    show Nat.card ↥(⊤ : Subgroup (rootsOfUnity q F × rootsOfUnity q F)) =
      Nat.card (rootsOfUnity q F × rootsOfUnity q F) from
      Nat.card_congr Subgroup.topEquiv.toEquiv,
    Nat.card_prod, CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := F) (d := q) hqF, pow_two]

private noncomputable def rootSL2 (m : ℕ) [NeZero m] :
    Subgroup ((Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) :=
  leviFix (orthDerived (coordinateQuadPlus m F)) (framePair (F := F) 0) (framePair (F := F) 1)

private noncomputable def torusElt (m : ℕ) [NeZero m] (ζ : Fˣ) :
    orthDerived (coordinateQuadPlus m F) :=
  ⟨frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ),
    (isHypFrame_plus (K := F) m).frameLin_mem_orthDerived _⟩

private theorem coe_torusElt (m : ℕ) [NeZero m] (ζ : Fˣ) :
    (torusElt (F := F) m ζ : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) =
      frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) := rfl

private theorem qTorusHom_eq_projHom_frameLin {m q : ℕ} [NeZero m]
    (p : Fin m → rootsOfUnity q F) :
    qTorusHom (K := F) m q p =
      projHom (coordinateQuadPlus m F) ⟨frameLin (plusFrameLeft m) (plusFrameRight m)
        (fun i => ((p i : rootsOfUnity q F) : Fˣ)),
        (isHypFrame_plus (K := F) m).frameLin_mem_orthDerived _⟩ := by
  rw [qTorusHom, MonoidHom.comp_apply, IsHypFrame.frameHom_apply]
  refine congrArg (projHom (coordinateQuadPlus m F)) (Subtype.ext ?_)
  congr 1

private theorem qTorusHom_pair_one_mem {m q : ℕ} [NeZero m] (hm : 4 ≤ m) {ζ : Fˣ}
    (hζq : ζ ^ q = 1) : projHom (coordinateQuadPlus m F) (torusElt (F := F) m ζ) ∈
      twoPlaneTorus (F := F) m q := by
  change _ ∈ ((qTorusHom (K := F) m q).comp (planeParamHom (F := F) m q)).range
  refine MonoidHom.mem_range.2 ⟨(⟨ζ, (mem_rootsOfUnity q ζ).2 hζq⟩, 1), ?_⟩
  rw [MonoidHom.comp_apply, qTorusHom_eq_projHom_frameLin]
  exact congrArg (projHom (coordinateQuadPlus m F))
    (Subtype.ext (congrArg (frameLin (plusFrameLeft m) (plusFrameRight m))
      (planeParamHom_pair_one (F := F) hm hζq)))

private theorem leviFixBar_le_centralizer {m q : ℕ} [NeZero m] (hm : 4 ≤ m) :
    leviFixBar (framePair (F := F) (m := m) 0) (framePair (F := F) (m := m) 1) ≤ Subgroup.centralizer
      (twoPlaneTorus (F := F) m q :
        Set (matrixProjectiveDerived (coordinateQuadPlus m F))) := by
  intro f hf
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hf
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  obtain ⟨y, heq⟩ := MonoidHom.mem_range.1 he
  rw [← heq, MonoidHom.comp_apply, qTorusHom_eq_projHom_frameLin]
  have hfl : frameLin (plusFrameLeft m) (plusFrameRight m)
      (fun i => (((planeParamHom (F := F) m q y) i : rootsOfUnity q F) : Fˣ)) ∈
      Subgroup.centralizer
        ((rootSL2 (F := F) m : Subgroup ((Fin (2 * m) → F) ≃ₗ[F]
          (Fin (2 * m) → F))) : Set ((Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F))) :=
    frameLin_mem_centralizer_leviFix (F := F) hm
      (planeParamHom_apply_zero_eq_one (F := F) hm y)
  have hcomm : (s : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) *
      frameLin (plusFrameLeft m) (plusFrameRight m)
        (fun i => (((planeParamHom (F := F) m q y) i : rootsOfUnity q F) : Fˣ)) =
      frameLin (plusFrameLeft m) (plusFrameRight m)
        (fun i => (((planeParamHom (F := F) m q y) i : rootsOfUnity q F) : Fˣ)) * (s : _) :=
    Subgroup.mem_centralizer_iff.1 hfl (s : _) (Subgroup.mem_subgroupOf.1 hs)
  rw [← map_mul, ← map_mul]
  refine congrArg (projHom (coordinateQuadPlus m F)) (Subtype.ext ?_)
  simpa using hcomm.symm

private theorem leviFixBar_isQuasisimple {m : ℕ} [NeZero m] (hm : 4 ≤ m)
    (hF4 : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple
      ↥(leviFixBar (framePair (F := F) (m := m) 0) (framePair (F := F) (m := m) 1)) := by
  have horth : (framePair (F := F) 0).Orth (framePair (F := F) 1) := framePair_orth (F := F) hm
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (K := F) (n := m) (by omega)
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (leviFixBarEquiv horth hQ hT ?_).symm
    (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le (K := F) hF4)
  exact (isHypCoord_coordinateQuadPlus (K := F) (zeroIdx m hm)).exists_ne_zero

private theorem q_dvd_card_leviFixBar {m n q : ℕ} [NeZero m] (hm : 4 ≤ m)
    (hF : Nat.card F = 2 ^ n) (hq : q.Prime) (hqF : q ∣ Nat.card F - 1) :
    q ∣ Nat.card ↥(leviFixBar (framePair (F := F) (m := m) 0) (framePair (F := F) (m := m) 1)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have horth : (framePair (F := F) 0).Orth (framePair (F := F) 1) := framePair_orth (F := F) hm
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (K := F) (n := m) (by omega)
  have hQne : ∃ v, (coordinateQuadPlus m F) v ≠ 0 :=
    (isHypCoord_coordinateQuadPlus (K := F) (zeroIdx m hm)).exists_ne_zero
  rw [card_leviFixBar horth hQ hT hQne, CFSG.ClassicalGroups.F2Fixed.card_sl2]
  have hsq : q ∣ Nat.card F ^ 2 - 1 := by
    have h1 : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      simpa using Nat.sq_sub_sq (Nat.card F) 1
    rw [h1]
    exact Dvd.dvd.mul_left hqF (Nat.card F + 1)
  exact Dvd.dvd.mul_left hsq (Nat.card F)

private theorem conj_mem_leviFixBar {m q : ℕ} [NeZero m] (hm : 4 ≤ m) {ζ : Fˣ}
    (hζ1 : ζ ≠ 1) (hζinv : ζ⁻¹ ≠ ζ) (hζq : ζ ^ q = 1)
    {g f : matrixProjectiveDerived (coordinateQuadPlus m F)}
    (hg : g ∈ Subgroup.centralizer (twoPlaneTorus (F := F) m q : Set _))
    (hf : f ∈ leviFixBar (framePair (F := F) (m := m) 0) (framePair (F := F) (m := m) 1)) :
    g * f * g⁻¹ ∈ leviFixBar (framePair (F := F) (m := m) 0) (framePair (F := F) (m := m) 1) := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hf
  obtain ⟨g', hg'⟩ := projHom_surjective (coordinateQuadPlus m F) g
  have hproj_inj : Function.Injective (projHom (coordinateQuadPlus m F)) :=
    projHom_injective (Q := coordinateQuadPlus m F)
      (isHypCoord_coordinateQuadPlus (K := F) (zeroIdx m hm)).exists_ne_zero
  have hfl_mem : projHom (coordinateQuadPlus m F) (torusElt (F := F) m ζ) ∈
      twoPlaneTorus (F := F) m q :=
    qTorusHom_pair_one_mem (F := F) hm hζq
  have hgc : g * projHom (coordinateQuadPlus m F) (torusElt (F := F) m ζ) =
      projHom (coordinateQuadPlus m F) (torusElt (F := F) m ζ) * g :=
    (Subgroup.mem_centralizer_iff.1 hg _ hfl_mem).symm
  have hconj : g' * torusElt (F := F) m ζ * g'⁻¹ = torusElt (F := F) m ζ := by
    refine hproj_inj ?_
    rw [map_mul, map_mul, map_inv, hg', hgc, mul_assoc, mul_inv_cancel, mul_one]
  have hfl_comm : (g' : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) *
      frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) =
      frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) * (g' : _) := by
    have h := congrArg Subtype.val hconj
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at h
    have h2 : (g' : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) *
        (torusElt (F := F) m ζ : _) * (g' : _)⁻¹ = (torusElt (F := F) m ζ : _) := by
      simpa using h
    have h2' : (g' : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) *
        frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) * (g' : _)⁻¹ =
        frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) := by
      simpa [coe_torusElt] using h2
    have h3 : (((g' : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F))) *
        frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) * (g' : _)⁻¹) *
        (g' : _) = frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) * (g' : _) := by
      rw [h2']
    simpa [mul_assoc] using h3
  have hconj_L : (g' : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) *
      (s : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) *
      (g' : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F))⁻¹ ∈ rootSL2 (F := F) m :=
    conj_mem_leviFix (F := F) hm hζ1 hζinv g'.2 hfl_comm (Subgroup.mem_subgroupOf.1 hs)
  have hmem : g' * s * g'⁻¹ ∈
      (rootSL2 (F := F) m).subgroupOf (orthDerived (coordinateQuadPlus m F)) := by
    change (g' : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) * (s : _) * (g' : _)⁻¹ ∈
      rootSL2 (F := F) m
    exact hconj_L
  have hgoal : g * projHom (coordinateQuadPlus m F) s * g⁻¹ =
      projHom (coordinateQuadPlus m F) (g' * s * g'⁻¹) := by
    rw [map_mul, map_mul, map_inv, hg']
  rw [hgoal]
  exact Subgroup.mem_map.2 ⟨_, hmem, rfl⟩

theorem exists_qLayer_le_qTorus {m n q : ℕ} (hm : 4 ≤ m) (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hq : q.Prime) (hq2 : q ≠ 2) (hqF : q ∣ Nat.card F - 1) :
    ∃ E : Subgroup (matrixProjectiveDerived (coordinateQuadPlus m F)),
      E ≤ qTorus (K := F) m q ∧ Nat.card E = q ^ 2 ∧
        GLAPLayer q (Subgroup.centralizer
          (E : Set (matrixProjectiveDerived (coordinateQuadPlus m F)))) ≠ ⊥ := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqdvd : q ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) q hqdvd
  have hζq : ζ ^ q = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ
    exact hq.ne_one hζ.symm
  have hζinv : ζ⁻¹ ≠ ζ := by
    intro h
    have h2 : ζ ^ 2 = 1 := by
      rw [pow_two]
      simpa [h] using mul_inv_cancel ζ
    have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hζ] at hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hdvd)
  refine ⟨twoPlaneTorus (F := F) m q, twoPlaneTorus_le_qTorus (F := F) (m := m) (q := q),
    card_twoPlaneTorus (F := F) (m := m) (n := n) (q := q) hm hF hq hqF, ?_⟩
  exact CFSG.LocalAnalysis.GLTheoremA.glaPLayer_ne_bot_of_block hq
    (leviFixBar_le_centralizer (F := F) (q := q) hm)
    (leviFixBar_isQuasisimple (F := F) hm hF4)
    (fun g hg f hf => conj_mem_leviFixBar (F := F) (q := q) hm hζ1 hζinv hζq hg hf)
    (q_dvd_card_leviFixBar (F := F) (n := n) (q := q) hm hF hq hqF)

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaPair
