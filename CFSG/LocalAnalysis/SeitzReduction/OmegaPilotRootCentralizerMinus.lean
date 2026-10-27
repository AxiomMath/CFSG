module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerOTwo
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRootQTwo

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem minusPairPerpEquiv_apply (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (x : minusPairPerp (K := K) (by omega) b c i)
    (G : orthDerived (coordinateQuadMinus n K (by omega) b c))
    (hG : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i))))
    (hxG : (x : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) = projHom _ G)
    (w : Fin (2 * (n - 1)) → K) (y : Fin (2 * (n - 1))) :
    ((minusPairPerpEquiv hn hirr i x :
        orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) w y =
      (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K))
        (Function.extend (minusPerpCoord (by omega) i) w 0) (minusPerpCoord (by omega) i y) := by
  have hsymm : ((stabDerived (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))).equivMapOfInjective
      (projHom _) (projHom_injective
        (isHypCoord_coordinateQuadMinus (K := K) (by omega) b c i).exists_ne_zero)).symm x =
      ⟨G, hG⟩ :=
    (MulEquiv.symm_apply_eq _).mpr (Subtype.ext hxG)
  have e1 : minusPairPerpEquiv hn hirr i x = orthDerivedCongr (minusPerpIsometry (by omega) b c i)
      ((isHypCoord_coordinateQuadMinus (K := K) (by omega) b c i).stabDerivedEquiv
        (regular_coordinateQuadMinus n K b c (by omega) hirr).1 (regular_minusPerp hn hirr i).1
        (regular_minusPerp hn hirr i).2 ⟨G, hG⟩) := by
    unfold minusPairPerpEquiv IsHypCoord.pairPerpOfEquiv
    change orthDerivedCongr (minusPerpIsometry (by omega) b c i)
      ((isHypCoord_coordinateQuadMinus (K := K) (by omega) b c i).stabDerivedEquiv
        (regular_coordinateQuadMinus n K b c (by omega) hirr).1 (regular_minusPerp hn hirr i).1
        (regular_minusPerp hn hirr i).2
        (((stabDerived (coordinateQuadMinus n K (by omega) b c)
          (minusIndexEquiv n (by omega) (.inl i))
          (minusIndexEquiv n (by omega) (.inr (.inl i)))).equivMapOfInjective (projHom _)
          (projHom_injective
            (isHypCoord_coordinateQuadMinus (K := K) (by omega) b c i).exists_ne_zero)).symm x)) = _
    rw [hsymm]
  rw [e1, orthDerivedCongr_apply]
  rfl

omit [Finite K] [CharP K 2] in
theorem minusPerpCoord_inl {i j : Fin (n - 1)} (hn2 : 2 ≤ n) {j' : Fin (n - 1 - 1)}
    (hj' : avoid (by omega) i j' = j) :
    minusPerpCoord hn2 i (minusIndexEquiv (n - 1) (by omega) (.inl j')) =
      minusIndexEquiv n (by omega) (.inl j) := by
  simp [minusPerpCoord, hj']

omit [Finite K] [CharP K 2] in
theorem minusPerpCoord_inr {i j : Fin (n - 1)} (hn2 : 2 ≤ n) {j' : Fin (n - 1 - 1)}
    (hj' : avoid (by omega) i j' = j) :
    minusPerpCoord hn2 i (minusIndexEquiv (n - 1) (by omega) (.inr (.inl j'))) =
      minusIndexEquiv n (by omega) (.inr (.inl j)) := by
  simp [minusPerpCoord, hj']

theorem minusPairPerpEquiv_fix_iff (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (x : minusPairPerp (K := K) (by omega) b c i)
    (G : orthDerived (coordinateQuadMinus n K (by omega) b c))
    (hG : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i))))
    (hxG : (x : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) = projHom _ G)
    (c' : Fin (2 * (n - 1))) :
    ((minusPairPerpEquiv hn hirr i x :
        orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) (Pi.single c' 1) =
        Pi.single c' 1 ↔
      (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K))
        (Pi.single (minusPerpCoord (by omega) i c') 1) =
        Pi.single (minusPerpCoord (by omega) i c') 1 := by
  have hn2 : 2 ≤ n := by omega
  have hinj := minusPerpCoord_injective hn2 i
  have hext := extend_single (K := K) hinj c'
  have hcomp := single_comp (K := K) hinj c'
  have hi := isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n) b c i
  have hGO : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadMinus n K (by omega) b c) :=
    Subgroup.commutator_le_self _ G.2
  have hU : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K))
      (Pi.single (minusPerpCoord hn2 i c') 1) ∈
      perpSub K (minusIndexEquiv n (by omega) (.inl i))
        (minusIndexEquiv n (by omega) (.inr (.inl i))) :=
    hi.apply_mem_perpSub hGO hG (single_mem_perpSub (minusPerpCoord_ne_left hn2 i c')
      (minusPerpCoord_ne_right hn2 i c'))
  constructor
  · intro h
    funext v
    by_cases hva : v = minusIndexEquiv n (by omega) (.inl i)
    · subst hva
      rw [hU.1, Pi.single_eq_of_ne (minusPerpCoord_ne_left hn2 i c').symm]
    by_cases hvb : v = minusIndexEquiv n (by omega) (.inr (.inl i))
    · subst hvb
      rw [hU.2, Pi.single_eq_of_ne (minusPerpCoord_ne_right hn2 i c').symm]
    obtain ⟨y, rfl⟩ := exists_minusPerpCoord_eq hn2 i hva hvb
    have h1 := congrFun h y
    rw [minusPairPerpEquiv_apply hn hirr i x G hG hxG, hext] at h1
    rw [h1, ← hcomp]
  · intro h
    funext y
    rw [minusPairPerpEquiv_apply hn hirr i x G hG hxG, hext, h, ← hcomp]

theorem map_minusStabPairsBar (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (n - 1)} {j' : Fin (n - 1 - 1)} (hj' : avoid (by omega) i j' = j) :
    ((stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j)) (minusIndexEquiv n (by omega) (.inr (.inl j)))).subgroupOf
        (minusPairPerp (by omega) b c i)).map (minusPairPerpEquiv hn hirr i).toMonoidHom =
      stabDerived (coordinateQuadMinus (n - 1) K (by omega) b c)
        (minusIndexEquiv (n - 1) (by omega) (.inl j'))
        (minusIndexEquiv (n - 1) (by omega) (.inr (.inl j'))) := by
  have hn2 : 2 ≤ n := by omega
  have hlift : ∀ x : minusPairPerp (K := K) (by omega) b c i,
      ∃ G : orthDerived (coordinateQuadMinus n K (by omega) b c),
      (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
        stabSub (minusIndexEquiv n (by omega) (.inl i))
          (minusIndexEquiv n (by omega) (.inr (.inl i))) ∧
      (x : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) = projHom _ G := by
    rintro ⟨_, ⟨G, hG, rfl⟩⟩
    exact ⟨G, mem_subgroupOf.mp hG, rfl⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨G, hG, hxG⟩ := mem_map.mp (mem_subgroupOf.mp hx)
    have hG' := mem_subgroupOf.mp hG
    refine mem_subgroupOf.mpr ⟨?_, ?_⟩
    · refine (minusPairPerpEquiv_fix_iff hn hirr i x G hG'.1 hxG.symm _).mpr ?_
      rw [minusPerpCoord_inl hn2 hj']
      exact hG'.2.1
    · refine (minusPairPerpEquiv_fix_iff hn hirr i x G hG'.1 hxG.symm _).mpr ?_
      rw [minusPerpCoord_inr hn2 hj']
      exact hG'.2.2
  · intro hz
    refine ⟨(minusPairPerpEquiv hn hirr i).symm z, ?_, by simp⟩
    obtain ⟨G, hG, hxG⟩ := hlift ((minusPairPerpEquiv hn hirr i).symm z)
    have hz' : ((minusPairPerpEquiv hn hirr i ((minusPairPerpEquiv hn hirr i).symm z) :
        orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) ∈
        stabSub (minusIndexEquiv (n - 1) (by omega) (.inl j'))
          (minusIndexEquiv (n - 1) (by omega) (.inr (.inl j'))) := by
      rw [MulEquiv.apply_symm_apply]
      exact mem_subgroupOf.mp hz
    have h1 := (minusPairPerpEquiv_fix_iff hn hirr i _ G hG hxG _).mp hz'.1
    have h2 := (minusPairPerpEquiv_fix_iff hn hirr i _ G hG hxG _).mp hz'.2
    rw [minusPerpCoord_inl hn2 hj'] at h1
    rw [minusPerpCoord_inr hn2 hj'] at h2
    refine mem_subgroupOf.mpr ?_
    rw [hxG]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr ⟨hG, h1, h2⟩)

theorem isQuasisimple_minusStabPairsBar (hn : 6 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)} (hij : i ≠ j) :
    CFSG.IsQuasisimple (stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j)) (minusIndexEquiv n (by omega) (.inr (.inl j)))) ∧
    center (stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j))
      (minusIndexEquiv n (by omega) (.inr (.inl j)))) = ⊥ := by
  obtain ⟨j', hj'⟩ := exists_avoid_eq (M := n - 1 - 1) (by omega : n - 1 - 1 + 1 = n - 1) hij.symm
  have hk := isHypCoord_coordinateQuadMinus (K := K) (n := n - 1) (by omega) b c j'
  obtain ⟨hR, hT⟩ := regular_minusPerp (K := K) (n := n - 1) (by omega) hirr j'
  have hle : stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j)) (minusIndexEquiv n (by omega) (.inr (.inl j))) ≤
      minusPairPerp (by omega) b c i :=
    map_mono fun _ hx => (mem_subgroupOf.mp hx).1
  set φ := (((Subgroup.subgroupOfEquivOfLe hle).symm.trans
    (((stabPairsBar (coordinateQuadMinus n K _ b c)
      (minusIndexEquiv n _ (.inl i)) (minusIndexEquiv n _ (.inr (.inl i)))
      (minusIndexEquiv n _ (.inl j))
      (minusIndexEquiv n _ (.inr (.inl j)))).subgroupOf
        (minusPairPerp _ b c i)).equivMapOfInjective
      (minusPairPerpEquiv (K := K) (by omega) hirr i).toMonoidHom
      (minusPairPerpEquiv (K := K) (by omega) hirr i).injective)).trans
    (MulEquiv.subgroupCongr (map_minusStabPairsBar (by omega) hirr hj'))).trans
    (hk.stabDerivedEquiv (regular_coordinateQuadMinus (n - 1) K b c (by omega) hirr).1 hR hT)
    with hφ
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT), ?_⟩
  have hne : ∃ v : perpSub K (minusIndexEquiv (n - 1) (by omega) (.inl j'))
      (minusIndexEquiv (n - 1) (by omega) (.inr (.inl j'))),
      (coordinateQuadMinus (n - 1) K (by omega) b c).comp
      (perpSub K (minusIndexEquiv (n - 1) (by omega) (.inl j'))
      (minusIndexEquiv (n - 1) (by omega) (.inr (.inl j')))).subtype v ≠ 0 := by
    obtain ⟨T, hT3, -⟩ := hT
    have : Nontrivial T := Module.nontrivial_of_finrank_eq_succ hT3
    obtain ⟨t, ht⟩ := exists_ne (0 : T)
    have : Nontrivial (perpSub K (minusIndexEquiv (n - 1) (by omega) (.inl j'))
        (minusIndexEquiv (n - 1) (by omega) (.inr (.inl j')))) :=
      nontrivial_of_ne (t : perpSub K (minusIndexEquiv (n - 1) (by omega) (.inl j'))
        (minusIndexEquiv (n - 1) (by omega) (.inr (.inl j')))) 0 (fun h => ht (Subtype.ext h))
    exact CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hR
  have hc := center_orthDerived_eq_bot' hR hT hne
  have hmap := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ.symm
  rw [← hmap, hc, Subgroup.map_bot]

omit [Finite K] [CharP K 2] in
theorem single_minus_apply_eq_zero (hn1 : 1 ≤ n) {i k : Fin (n - 1)} (hik : i ≠ k)
    (s t : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (hs : s = .inl i ∨ s = .inr (.inl i))
    (ht : t = .inl k ∨ t = .inr (.inl k)) :
    (Pi.single (minusIndexEquiv n hn1 s) (1 : K) : Fin (2 * n) → K) (minusIndexEquiv n hn1 t) =
      0 := by
  refine Pi.single_eq_of_ne (fun h => ?_) _
  have h' := (minusIndexEquiv n hn1).injective h
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp_all

theorem centralizer_longRoot_decomp_minus (hq : 4 ≤ Nat.card K) (hn : 6 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    ∃ (z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
      (Qz Mz : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))),
      z ∈ minusPairPerp (by omega) b c k ∧ IsLongRoot _ z ∧
        CFSG.Quasithin.perfectCore (centralizer ({z} : Set _)) = centralizer {z} ∧
        centralizer {z} = Qz ⊔ Mz ∧ IsPGroup 2 Qz ∧
        Mz ≤ normalizer (Qz : Set (matrixProjectiveDerived
          (coordinateQuadMinus n K (by omega) b c))) ∧
        Disjoint Qz Mz ∧ (∀ N : Subgroup Mz, N.Normal → IsPGroup 2 N → N = ⊥) ∧
        minusPairTorus (by omega) b c k ≤ Mz := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨i, j, hij, hik, hjk⟩ := exists_pair_ne_fin (by omega : 3 ≤ n - 1) k
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn1 b c i
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn1 b c j
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hd := pairDisjoint_minus hn1 hij
  have h₁₂ := hi.orth hj hd
  have h₁₃ := hi.orth hk (pairDisjoint_minus hn1 hik)
  have h₂₃ := hj.orth hk (pairDisjoint_minus hn1 hjk)
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  have hS := isQuasisimple_minusStabPairsBar (K := K) hn hirr hij
  refine ⟨rootPairElt hQ h₁₂ h₁₃ h₂₃, rootRadicalBar _ hi.hypPair hj.hypPair,
    rootLeviBar _ hi.hypPair hj.hypPair, ?_, isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_centralizer_rootPairElt_of hi hj hd hQ h₁₃ h₂₃ hl0 hl1
        (Subgroup.isPerfect_iff.mp hS.1.1)),
    centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃, isPGroup_rootRadicalBar _ _,
    rootLeviBar_le_normalizer h₁₂, disjoint_rootRadicalBar_rootLeviBar h₁₂,
    fun N hN h2 => rootLeviBar_normal_isPGroup_eq_bot_of hi hj hd hQ hT hS N hN h2, ?_⟩
  · exact rootPairElt_mem_pairPerpOf hQ h₁₂ h₁₃ h₂₃ hk
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inr rfl)⟩
  · exact pairTorusOf_le_rootLeviBar hk
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inr rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inr rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inr rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inr rfl) (.inr rfl)⟩

theorem exists_perfect_le_centralizer_of_isLongRoot_minus (hn : 6 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)} (hz : IsLongRoot _ z) :
    ∃ H : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)),
      ⁅H, H⁆ = H ∧ z ∈ H ∧ H ≤ centralizer {z} := by
  have hn1 : 1 ≤ n := by omega
  set i : Fin (n - 1) := ⟨0, by omega⟩
  set j : Fin (n - 1) := ⟨1, by omega⟩
  set k : Fin (n - 1) := ⟨2, by omega⟩
  set l : Fin (n - 1) := ⟨3, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hik : i ≠ k := by simp [i, k, Fin.ext_iff]
  have hjk : j ≠ k := by simp [j, k, Fin.ext_iff]
  have hil : i ≠ l := by simp [i, l, Fin.ext_iff]
  have hjl : j ≠ l := by simp [j, l, Fin.ext_iff]
  have hkl : k ≠ l := by simp [k, l, Fin.ext_iff]
  obtain ⟨hQ, -⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn1 b c i
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn1 b c j
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hl := isHypCoord_coordinateQuadMinus (K := K) hn1 b c l
  obtain ⟨z₀, hz₀def⟩ : ∃ z₀, z₀ = rootPairElt hQ (hi.orth hj (pairDisjoint_minus hn1 hij))
      (hi.orth hk (pairDisjoint_minus hn1 hik)) (hj.orth hk (pairDisjoint_minus hn1 hjk)) :=
    ⟨_, rfl⟩
  have hz₀ : IsLongRoot _ z₀ := hz₀def ▸ isLongRoot_rootPairElt hQ
    (hi.orth hj (pairDisjoint_minus hn1 hij)) (hi.orth hk (pairDisjoint_minus hn1 hik))
    (hj.orth hk (pairDisjoint_minus hn1 hjk))
  have hmem := rootPairElt_mem_perfectCore_of hi hj hk hl (pairDisjoint_minus hn1 hij)
    (pairDisjoint_minus hn1 hik) (pairDisjoint_minus hn1 hjk) (pairDisjoint_minus hn1 hil)
    (pairDisjoint_minus hn1 hjl) (pairDisjoint_minus hn1 hkl) hQ
    (Subgroup.isPerfect_iff.mp (isQuasisimple_minusStabPairsBar (K := K) hn hirr hij).1.1)
    hz₀def
  obtain ⟨c', hc⟩ := isConj_iff.mp (isConj_of_isLongRoot_minus (by omega) hirr hz₀ hz)
  refine ⟨(CFSG.Quasithin.perfectCore (centralizer {z₀})).map (MulAut.conj c').toMonoidHom,
    ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, CFSG.Quasithin.perfectCore_perfect]
  · rw [← hc]
    exact ⟨_, hmem, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := mem_centralizer_singleton_iff.mp (CFSG.Quasithin.perfectCore_le _ hy)
    rw [mem_centralizer_singleton_iff, ← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c' * y * c'⁻¹ * (c' * z₀ * c'⁻¹) = c' * (y * z₀) * c'⁻¹ := by group
      _ = c' * (z₀ * y) * c'⁻¹ := by rw [h]
      _ = c' * z₀ * c'⁻¹ * (c' * y * c'⁻¹) := by group

end Minus

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_isLongRoot_conj_minus_of_six_le (hset : SeitzSetting G L) {n f : ℕ} (hn : 6 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G) (hgL : g⁻¹ * t * g ∈ L) :
    ¬ IsLongRoot _ (e ⟨g⁻¹ * t * g, hgL⟩) :=
  not_isLongRoot_conj_of_perfect hset e
    (isSolvable_outer_of_mulEquiv_minus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hK) hK
      hirr e)
    (fun _ hz => exists_perfect_le_centralizer_of_isLongRoot_minus hn hirr hz) htC ht g hgL

theorem not_forall_commute_sylow_conj_minus_of_six_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 6 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hgL hcomm
  exact not_isLongRoot_conj_minus_of_six_le hset hn hK hirr e htC ht g hgL
    (isLongRoot_of_commute_sylow_minus_of_mulEquiv (by omega) hirr e U
      (conj_ne_one_of_orderOf ht g hgL) fun u hu => Subtype.ext (hcomm u hu))

theorem exists_conj_eq_mul_longRoot_twoSided_minus_of_six_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 6 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htC := mem_centralizer_of_inf_eq hKt
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hLt : L ≤ centralizer ({t} : Set G) :=
    SeitzQ2.le_centralizer_singleton_of_mem_centralizer htC
  obtain ⟨x, z, hz, hxz, hz1, ⟨U, hU⟩, ⟨U', hU'⟩, hact⟩ :=
    exists_conj_eq_mul_twoSided_of_commutator_eq_top_of_autU2
      (SeitzQ2.commutator_eq_top_of_standardSetting hset.standardSetting) ht hLt hCN hKt
      (not_forall_commute_sylow_conj_minus_of_six_le hset hn hK hirr e htC ht)
      (autU2_minus_of_mulEquiv (by omega) hirr e)
      (habel_minus hset (by omega) hK hirr e ht hKt)
  refine ⟨x, z, hz, hxz, ⟨hz.1, ?_⟩, ⟨hz.2, ?_⟩, hact⟩
  · exact isLongRoot_of_commute_sylow_minus_of_mulEquiv (by omega) hirr e U
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU u hu)
  · exact isLongRoot_of_commute_sylow_minus_of_mulEquiv (by omega) hirr
      ((conjugateMulEquiv L x).symm.trans e) U'
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext (hU' u hu)

theorem exists_conj_eq_mul_longRoot_minus_of_six_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 6 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ (g : G) (z : L), IsLongRoot _ (e z) ∧ g⁻¹ * t * g = t * (z : G) := by
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, -, -⟩ :=
    exists_conj_eq_mul_longRoot_twoSided_minus_of_six_le hset hn hK hirr e ht hKt
  exact ⟨x, ⟨z, hzL⟩, hzl, hxz⟩

end Setting

end CFSG.SeitzReduction.OmegaPilot
