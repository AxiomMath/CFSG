module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrth
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEight
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapEnd

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadMinus minusIndexEquiv regular_coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SymplecticPilot (planeTorusParam)

section Symm

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem stabSub_comm (a b : Fin d) : stabSub (K := K) a b = stabSub b a := by
  ext g
  simp only [mem_stabSub]
  exact and_comm

theorem stabPairsBar_swap_right (a a' b b' : Fin d) :
    stabPairsBar Q a a' b b' = stabPairsBar Q a a' b' b := by
  rw [stabPairsBar, stabPairsBar, stabSub_comm b b']

end Symm

section Commute

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

theorem commute_of_fixW_of_mem_span (h₁₂ : P₁.Orth P₂) {g h : V ≃ₗ[K] V}
    (hgW : ∀ x, InW P₁ P₂ x → g x = x) (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hh : h P₁.e = P₁.e ∧ h P₁.f = P₁.f ∧ h P₂.e = P₂.e ∧ h P₂.f = P₂.f)
    (hgU : ∀ v ∈ ({P₁.e, P₁.f, P₂.e, P₂.f} : Set V),
      g v ∈ Submodule.span K ({P₁.e, P₁.f, P₂.e, P₂.f} : Set V)) :
    g * h = h * g := by
  have hspan : Submodule.span K ({P₁.e, P₁.f, P₂.e, P₂.f} : Set V) ≤
      LinearMap.eqLocus h.toLinearMap LinearMap.id := by
    rw [Submodule.span_le]
    obtain ⟨h1, h2, h3, h4⟩ := hh
    rintro v (rfl | rfl | rfl | rfl) <;> simp [LinearMap.eqLocus, *]
  have hfix : ∀ v ∈ ({P₁.e, P₁.f, P₂.e, P₂.f} : Set V), h (g v) = g v := fun v hv =>
    hspan (hgU v hv)
  exact commute_of_fixW_of_fix h₁₂ hgW hhO hh
    ⟨hfix _ (by simp), hfix _ (by simp), hfix _ (by simp), hfix _ (by simp)⟩

end Commute

section Frame

variable {K : Type} [Field K] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)} {a b : Fin m → Fin d}

theorem IsHypFrame.inW_iff (h : IsHypFrame Q a b) (p q : Fin m) (x : Fin d → K) :
    InW (h.hyp p).hypPair (h.hyp q).symm.hypPair x ↔
      x (b p) = 0 ∧ x (a p) = 0 ∧ x (a q) = 0 ∧ x (b q) = 0 := by
  simp only [InW, IsHypCoord.hypPair_e, IsHypCoord.hypPair_f, (h.hyp p).polar_left,
    (h.hyp p).polar_right, (h.hyp q).symm.polar_left, (h.hyp q).symm.polar_right]

theorem IsHypFrame.pairs_set_eq (h : IsHypFrame Q a b) (p q : Fin m) :
    ({(h.hyp p).hypPair.e, (h.hyp p).hypPair.f, (h.hyp q).symm.hypPair.e,
      (h.hyp q).symm.hypPair.f} : Set (Fin d → K)) =
      {Pi.single (a p) 1, Pi.single (b p) 1, Pi.single (b q) 1, Pi.single (a q) 1} := by
  simp only [IsHypCoord.hypPair_e, IsHypCoord.hypPair_f]

theorem IsHypFrame.frameRootElt_commute (h : IsHypFrame Q a b) {p q p' q' : Fin m} (hpq : p ≠ q)
    (hpq' : p' ≠ q') (hp' : p' = p ∨ p' = q) (hq' : q' = p ∨ q' = q) (c : K)
    {Y : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hYO : Y ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hY : Y ∈ stabSub (a p) (b p) ⊓ stabSub (b q) (a q)) :
    frameRootElt Q a b p' q' c * Y = Y * frameRootElt Q a b p' q' c := by
  obtain ⟨⟨y1, y2⟩, y3, y4⟩ := hY
  have h₁₂ : (h.hyp p).hypPair.Orth (h.hyp q).symm.hypPair :=
    (h.hyp p).orth (h.hyp q).symm ((h.pairDisjoint hpq).swap_right)
  refine commute_of_fixW_of_mem_span h₁₂ (fun x hx => ?_) hYO
    ⟨by simpa using y1, by simpa using y2, by simpa using y3, by simpa using y4⟩ ?_
  · rw [h.inW_iff p q] at hx
    obtain ⟨x1, x2, x3, x4⟩ := hx
    have hbp : x (b p') = 0 := by rcases hp' with rfl | rfl <;> assumption
    have haq : x (a q') = 0 := by rcases hq' with rfl | rfl <;> assumption
    rw [h.frameRootElt_apply hpq' c x, hbp, haq]
    simp
  · rw [h.pairs_set_eq p q]
    have hS : ∀ v ∈ ({Pi.single (a p) 1, Pi.single (b p) 1, Pi.single (b q) 1,
        Pi.single (a q) 1} : Set (Fin d → K)), v ∈ Submodule.span K ({Pi.single (a p) 1,
          Pi.single (b p) 1, Pi.single (b q) 1, Pi.single (a q) 1} : Set (Fin d → K)) :=
      fun v hv => Submodule.subset_span hv
    have hbq : Pi.single (b q') (1 : K) ∈ ({Pi.single (a p) 1, Pi.single (b p) 1,
        Pi.single (b q) 1, Pi.single (a q) 1} : Set (Fin d → K)) := by
      rcases hq' with rfl | rfl <;> simp
    have hap : Pi.single (a p') (1 : K) ∈ ({Pi.single (a p) 1, Pi.single (b p) 1,
        Pi.single (b q) 1, Pi.single (a q) 1} : Set (Fin d → K)) := by
      rcases hp' with rfl | rfl <;> simp
    intro v hv
    rw [h.frameRootElt_apply hpq' c v]
    exact sub_mem (add_mem (hS v hv) (Submodule.smul_mem _ _ (hS _ hbq)))
      (Submodule.smul_mem _ _ (hS _ hap))

theorem frameEntry_eq_one_of_planes {p q : Fin m} {t : Fin m → Kˣ}
    (ht : ∀ k, k ≠ p → k ≠ q → t k = 1) {i : Fin d} (h1 : i ≠ a p) (h2 : i ≠ b p) (h3 : i ≠ a q)
    (h4 : i ≠ b q) : frameEntry a b t i = 1 := by
  refine Finset.prod_eq_one fun k _ => ?_
  by_cases hkp : k = p
  · subst hkp
    unfold torusEntry
    rw [ite_eq_right h1, ite_eq_right h2]
  by_cases hkq : k = q
  · subst hkq
    unfold torusEntry
    rw [ite_eq_right h3, ite_eq_right h4]
  rw [ht k hkp hkq, torusEntry_one]

theorem IsHypFrame.frameLin_commute (h : IsHypFrame Q a b) {p q : Fin m} (hpq : p ≠ q)
    {t : Fin m → Kˣ} (ht : ∀ k, k ≠ p → k ≠ q → t k = 1)
    {Y : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hYO : Y ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hY : Y ∈ stabSub (a p) (b p) ⊓ stabSub (b q) (a q)) :
    frameLin a b t * Y = Y * frameLin a b t := by
  obtain ⟨⟨y1, y2⟩, y3, y4⟩ := hY
  have h₁₂ : (h.hyp p).hypPair.Orth (h.hyp q).symm.hypPair :=
    (h.hyp p).orth (h.hyp q).symm ((h.pairDisjoint hpq).swap_right)
  refine commute_of_fixW_of_mem_span h₁₂ (fun x hx => ?_) hYO
    ⟨by simpa using y1, by simpa using y2, by simpa using y3, by simpa using y4⟩ ?_
  · rw [h.inW_iff p q] at hx
    obtain ⟨x1, x2, x3, x4⟩ := hx
    funext i
    rw [frameLin_apply]
    by_cases i1 : i = a p
    · rw [i1, x2, mul_zero]
    by_cases i2 : i = b p
    · rw [i2, x1, mul_zero]
    by_cases i3 : i = a q
    · rw [i3, x3, mul_zero]
    by_cases i4 : i = b q
    · rw [i4, x4, mul_zero]
    rw [frameEntry_eq_one_of_planes ht i1 i2 i3 i4, Units.val_one, one_mul]
  · rw [h.pairs_set_eq p q]
    intro v hv
    have hS : v ∈ Submodule.span K ({Pi.single (a p) 1, Pi.single (b p) 1, Pi.single (b q) 1,
        Pi.single (a q) 1} : Set (Fin d → K)) := Submodule.subset_span hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [h.frameLin_single_left]; exact Submodule.smul_mem _ _ hS
    · rw [h.frameLin_single_right]; exact Submodule.smul_mem _ _ hS
    · rw [h.frameLin_single_right]; exact Submodule.smul_mem _ _ hS
    · rw [h.frameLin_single_left]; exact Submodule.smul_mem _ _ hS

theorem IsHypFrame.frameLeviSL_le_centralizer_stab (h : IsHypFrame Q a b) {p q : Fin m}
    (hpq : p ≠ q) :
    frameLeviSL Q a b p q ≤ centralizer ((stabSub (a p) (b p) ⊓ stabSub (b q) (a q) ⊓
      TauCeti.QuadraticMap.orthogonalGroup Q : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))) :
        Set ((Fin d → K) ≃ₗ[K] (Fin d → K))) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨μ, rfl⟩) <;> rw [SetLike.mem_coe, mem_centralizer_iff] <;>
    rintro Y ⟨hY, hYO⟩
  · exact (h.frameRootElt_commute hpq hpq.symm (Or.inr rfl) (Or.inl rfl) c hYO hY).symm
  · exact (h.frameRootElt_commute hpq hpq (Or.inl rfl) (Or.inr rfl) c hYO hY).symm
  · refine (h.frameLin_commute hpq (fun k hkp hkq => ?_) hYO hY).symm
    simp [Pi.mulSingle_eq_of_ne hkp, Pi.mulSingle_eq_of_ne hkq]

theorem IsHypFrame.frameLeviProj_le_centralizer_stabPairsBar (h : IsHypFrame Q a b)
    {p q : Fin m} (hpq : p ≠ q) :
    frameLeviProj Q a b p q ≤
      centralizer (stabPairsBar Q (a p) (b p) (b q) (a q) : Set (matrixProjectiveDerived Q)) := by
  rintro _ ⟨X, hX, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨Y, hY, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hYO : (Y : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _ Y.2
  exact mem_centralizer_iff.1 (h.frameLeviSL_le_centralizer_stab hpq (mem_subgroupOf.1 hX)) _
    ⟨mem_subgroupOf.1 hY, hYO⟩

theorem IsHypFrame.frameTorusOf_le_centralizer_stabPairsBar (h : IsHypFrame Q a b) {p q : Fin m}
    (hpq : p ≠ q) {P : Subgroup (Fin m → Kˣ)} (hP : ∀ t ∈ P, ∀ k, k ≠ p → k ≠ q → t k = 1) :
    frameTorusOf Q a b P ≤
      centralizer (stabPairsBar Q (a p) (b p) (b q) (a q) : Set (matrixProjectiveDerived Q)) := by
  rintro _ ⟨X, hX, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨Y, hY, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hYO : (Y : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _ Y.2
  obtain ⟨t, ht, htX⟩ := mem_subgroupOf.1 hX
  change (Y : (Fin d → K) ≃ₗ[K] (Fin d → K)) * X = X * Y
  rw [← htX]
  exact (h.frameLin_commute hpq (hP t ht) hYO (mem_subgroupOf.1 hY)).symm

end Frame

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def minusRootElt (hn : 4 ≤ n) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0) (i j : Fin (n - 1)) (c : K) :
    matrixProjectiveDerived (coordinateQuadMinus n K (by omega) β γ) :=
  projHom _ ⟨frameRootElt (coordinateQuadMinus n K (by omega) β γ) (minusFrameLeft (by omega))
    (minusFrameRight (by omega)) i j c,
    eichler_mem_orthDerived (regular_coordinateQuadMinus n K β γ hn hirr).1
      (regular_coordinateQuadMinus n K β γ hn hirr).2 _ _⟩

omit [CharP K 2] in
theorem minusRootElt_mem_frameLeviProj (hn : 4 ≤ n) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0) (i j : Fin (n - 1)) (c : K) :
    minusRootElt hn hirr i j c ∈ frameLeviProj (coordinateQuadMinus n K (by omega) β γ)
      (minusFrameLeft (by omega)) (minusFrameRight (by omega)) i j :=
  ⟨_, mem_subgroupOf.mpr (Subgroup.subset_closure (Or.inl (Or.inr ⟨c, rfl⟩))), rfl⟩

omit [CharP K 2] in
theorem minusRootElt_swap_mem_frameLeviProj (hn : 4 ≤ n) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0) (i j : Fin (n - 1)) (c : K) :
    minusRootElt hn hirr j i c ∈ frameLeviProj (coordinateQuadMinus n K (by omega) β γ)
      (minusFrameLeft (by omega)) (minusFrameRight (by omega)) i j :=
  ⟨_, mem_subgroupOf.mpr (Subgroup.subset_closure (Or.inl (Or.inl ⟨c, rfl⟩))), rfl⟩

omit [Finite K] [CharP K 2] in
theorem torusLin_inv_swap {d : ℕ} {a b : Fin d} (hab : a ≠ b) (l : Kˣ) :
    torusLin (K := K) b a l⁻¹ = torusLin a b l := by
  ext v x
  rw [torusLin_apply, torusLin_apply]
  unfold torusEntry
  by_cases hxb : x = b
  · subst hxb
    simp [hab.symm]
  · by_cases hxa : x = a
    · subst hxa
      simp [hxb]
    · simp [hxa, hxb]

theorem orthTorusElt_mem_minusLevelTorus (hn : 1 ≤ n) {β γ : K} {i j : Fin (n - 1)} (hij : i ≠ j)
    (l : Kˣ) :
    orthTorusElt (isHypCoord_coordinateQuadMinus hn β γ i)
        (isHypCoord_coordinateQuadMinus hn β γ j).symm l ∈
      minusLevelTorus hn β γ {i, j} := by
  have hfr := isHypFrame_minus K hn β γ
  set t : Fin (n - 1) → Kˣ := Pi.mulSingle i l * Pi.mulSingle j l with htdef
  have hlin : orthTorusLin (minusIndexEquiv n hn (.inl i)) (minusIndexEquiv n hn (.inr (.inl i)))
      (minusIndexEquiv n hn (.inr (.inl j))) (minusIndexEquiv n hn (.inl j)) l =
      frameLin (minusFrameLeft hn) (minusFrameRight hn) t := by
    rw [orthTorusLin, torusLin_inv_swap (isHypCoord_coordinateQuadMinus hn β γ j).ne, htdef, map_mul,
      frameLin_mulSingle,
      frameLin_mulSingle]
    rfl
  have ht : t ∈ levelParam (K := K) ({i, j} : Finset (Fin (n - 1))) := by
    have hti : t i = l := by simp [htdef, Pi.mulSingle_eq_of_ne hij]
    have htj : t j = l := by simp [htdef, Pi.mulSingle_eq_of_ne hij.symm]
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [hti, htj]
  refine ⟨⟨frameLin (minusFrameLeft hn) (minusFrameRight hn) t,
    hfr.frameLin_mem_orthDerived t⟩, mem_subgroupOf.mpr ⟨t, ht, rfl⟩, ?_⟩
  rw [orthTorusElt]
  congr 1
  exact Subtype.ext hlin.symm

omit [Finite K] [CharP K 2] in
theorem modelToG_stabPairsBar_le_minusPieceCore {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hn : 1 ≤ n) {β γ : K}
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K hn β γ)) {i j : Fin (n - 1)}
    (hij : i ≠ j)
    (hperf : ⁅stabPairsBar (coordinateQuadMinus n K hn β γ) (minusIndexEquiv n hn (.inl i))
        (minusIndexEquiv n hn (.inr (.inl i))) (minusIndexEquiv n hn (.inl j))
        (minusIndexEquiv n hn (.inr (.inl j))),
      stabPairsBar (coordinateQuadMinus n K hn β γ) (minusIndexEquiv n hn (.inl i))
        (minusIndexEquiv n hn (.inr (.inl i))) (minusIndexEquiv n hn (.inl j))
        (minusIndexEquiv n hn (.inr (.inl j)))⁆ =
      stabPairsBar (coordinateQuadMinus n K hn β γ) (minusIndexEquiv n hn (.inl i))
        (minusIndexEquiv n hn (.inr (.inl i))) (minusIndexEquiv n hn (.inl j))
        (minusIndexEquiv n hn (.inr (.inl j)))) :
    modelToG e (stabPairsBar (coordinateQuadMinus n K hn β γ) (minusIndexEquiv n hn (.inl i))
        (minusIndexEquiv n hn (.inr (.inl i))) (minusIndexEquiv n hn (.inl j))
        (minusIndexEquiv n hn (.inr (.inl j)))) ≤
      minusPieceCore e ({i, j}ᶜ : Finset (Fin (n - 1))) := by
  have hfr := isHypFrame_minus K hn β γ
  have hc := hfr.frameTorusOf_le_centralizer_stabPairsBar hij (P := planeTorusParam K {i, j}ᶜ)
    (fun t ht k hki hkj => ht k (by simp [hki, hkj]))
  rw [← stabPairsBar_swap_right] at hc
  refine UnitaryPilot.modelToG_le_centralizerPerfectCore e ?_ hperf
  rw [le_centralizer_iff]
  exact hc

omit [CharP K 2] in
theorem rootPairElt_eq_minusRootElt (hn : 4 ≤ n) {β γ : K} (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    {i j : Fin (n - 1)} (hQ : (polarBilin (coordinateQuadMinus n K (by omega) β γ)).Nondegenerate)
    {P₃ : HypPair (coordinateQuadMinus n K (by omega) β γ)}
    (h₁₂ : (isHypCoord_coordinateQuadMinus (by omega) β γ i).hypPair.Orth
      (isHypCoord_coordinateQuadMinus (by omega) β γ j).symm.hypPair)
    (h₁₃ : (isHypCoord_coordinateQuadMinus (by omega) β γ i).hypPair.Orth P₃)
    (h₂₃ : (isHypCoord_coordinateQuadMinus (by omega) β γ j).symm.hypPair.Orth P₃) :
    rootPairElt hQ h₁₂ h₁₃ h₂₃ = minusRootElt hn hirr i j 1 := by
  rw [rootPairElt, minusRootElt]
  congr 1
  apply Subtype.ext
  simp only [IsHypCoord.hypPair_e, frameRootElt, one_smul]
  rfl

theorem exists_conj_eq_mul_forall_le_centralizer_minusPlanes {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : SeitzSetting G L) {f : ℕ} (hn : 4 ≤ n) (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {β γ : K} (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) β γ)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {i j : Fin (n - 1)} (hij : i ≠ j) {l : Kˣ} (hl : l ≠ 1) :
    ∃ g : G, g⁻¹ * t * g = t * (e.symm (minusRootElt hn hirr i j 1) : G) ∧
      ∀ S : Subgroup G, ⁅S, S⁆ = S → (∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) →
        S ≤ centralizer ({g⁻¹ * t * g} : Set G) →
        S ≤ centralizer ({(e.symm (orthTorusElt (isHypCoord_coordinateQuadMinus (by omega) β γ i)
          (isHypCoord_coordinateQuadMinus (by omega) β γ j).symm l) : G)} : Set G) →
        (e.symm (minusRootElt hn hirr i j 1) : G) ∈ S →
        S ≤ centralizer (modelToG e (stabPairsBar (coordinateQuadMinus n K (by omega) β γ)
          (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
          (minusIndexEquiv n (by omega) (.inl j))
          (minusIndexEquiv n (by omega) (.inr (.inl j)))) : Set G) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, -⟩ := regular_coordinateQuadMinus n K β γ hn hirr
  obtain ⟨k, hki, hkj⟩ := exists_ne_ne_fin (by omega : 3 ≤ n - 1) i j
  have hfr := isHypFrame_minus K hn1 β γ
  set ha := isHypCoord_coordinateQuadMinus hn1 β γ i with hadef
  set hb := (isHypCoord_coordinateQuadMinus hn1 β γ j).symm with hbdef
  set hc := isHypCoord_coordinateQuadMinus hn1 β γ k with hcdef
  have hd : PairDisjoint (minusIndexEquiv n hn1 (.inl i)) (minusIndexEquiv n hn1 (.inr (.inl i)))
      (minusIndexEquiv n hn1 (.inr (.inl j))) (minusIndexEquiv n hn1 (.inl j)) :=
    (hfr.pairDisjoint hij).swap_right
  have h₁₃ : ha.hypPair.Orth hc.hypPair := ha.orth hc (hfr.pairDisjoint hki.symm)
  have h₂₃ : hb.hypPair.Orth hc.hypPair := hb.orth hc (hfr.pairDisjoint hkj.symm).swap_left
  have hBq := isQuasisimple_minusStabPairsBar_of_four_le hn hirr hij
  have hBcard := card_le_minusStabPairsBar_of_four_le hn hirr hij
  rw [stabPairsBar_swap_right] at hBq hBcard
  obtain ⟨hy1, hy2, hy3, hy4⟩ := orthTorusElt_spec ha hb hd hl
  obtain ⟨g, hg, hS⟩ := exists_conj_eq_mul_forall_le_centralizer_minus hset hn hK hq hirr rfl e ht
    hKt ha hb hd hQ h₁₃ h₂₃ hBq hBcard hy1 hy2 hy3 hy4
  rw [rootPairElt_eq_minusRootElt hn hirr hQ] at hg hS
  refine ⟨g, hg, fun S hSp hSs hSt hSy hzS => ?_⟩
  have h := hS S hSp hSs hSt hSy hzS
  rw [stabPairsBar_swap_right] at h
  exact h

end Minus

end CFSG.SeitzReduction.OmegaPilot
