module

public import CFSG.CGT.Hall82.Fusion

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

theorem conj_inf_pCoreOf_eq_bot (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {g : G}
    (hgW : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ⊓
      CFSG.Open.pCoreOf 2 M = ⊥ := by
  set W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) with hW
  set Y : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g W with hY
  apply le_bot_iff.mp
  intro y hy
  obtain ⟨hyY, hyJ⟩ := Subgroup.mem_inf.mp hy
  have hyW : g⁻¹ * y * g ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
    have h : g⁻¹ * y * g ∈ W := by
      rw [hY, CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hyY
      exact hyY
    simpa [hW] using h
  by_cases hw1 : g⁻¹ * y * g = 1
  · have hy1 : y = 1 := by
      calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [hw1]
        _ = 1 := by group
    simpa [hy1]
  · have hgM : g ∈ M := by
      refine S.mem_of_conj_mem hF hc hW2 hWab hyW hw1 ?_
      rw [show g * (g⁻¹ * y * g) * g⁻¹ = y from by group]
      exact hyJ
    have hYeq : Y = W := by
      apply le_antisymm
      · intro x hx
        change x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g W at hx
        rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx
        have hx' : g * (g⁻¹ * x * g) * g⁻¹ ∈ W :=
          S.conj_mem_pCoreOf_centralizer hgM (by simpa [hW] using hx)
        rw [show x = g * (g⁻¹ * x * g) * g⁻¹ from by group]
        exact hx'
      · intro x hx
        change x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g W
        rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
        have hx' : (g⁻¹) * x * (g⁻¹)⁻¹ ∈ W :=
          S.conj_mem_pCoreOf_centralizer (M.inv_mem hgM) (by simpa [hW] using hx)
        simpa using hx'
    exfalso
    exact hgW (by simpa [hY, hW] using hYeq)

theorem centralizer_le_normalizer_conj (S : Setting G M L) {g y : G}
    (hy : y ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))))
    (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.normalizer (CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) : Set G) := by
  set W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) with hW
  set Y : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g W with hY
  have hyW : g⁻¹ * y * g ∈ W := by
    have h : g⁻¹ * y * g ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
      rw [hY, CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hy
      exact hy
    simpa [hW] using h
  have hw1 : g⁻¹ * y * g ≠ 1 := by
    intro h
    apply hy1
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  have hzcomm : y * z = z * y :=
    Subgroup.mem_centralizer_iff.mp hz y (by simp)
  have hzh : (g⁻¹ * y * g) * (g⁻¹ * z * g) = (g⁻¹ * z * g) * (g⁻¹ * y * g) := by
    calc (g⁻¹ * y * g) * (g⁻¹ * z * g) = g⁻¹ * (y * z) * g := by group
      _ = g⁻¹ * (z * y) * g := by rw [hzcomm]
      _ = (g⁻¹ * z * g) * (g⁻¹ * y * g) := by group
  have hzM : g⁻¹ * z * g ∈ M :=
    centralizer_le_of_mem_pCoreOf S.uniq hyW hw1 (by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      exact hzh)
  have hzN : g⁻¹ * z * g ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact S.conj_mem_pCoreOf_centralizer hzM (by simpa [hW] using hx)
    · intro hx
      have hx' : g⁻¹ * z * g * x * (g⁻¹ * z * g)⁻¹ ∈
          CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
        simpa [hW] using hx
      have h := S.conj_mem_pCoreOf_centralizer (M.inv_mem hzM) hx'
      simpa [hW, mul_assoc] using h
  intro x
  constructor
  · intro hx
    change x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g W at hx
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx
    change z * x * z⁻¹ ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g W
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    have hxW : g⁻¹ * x * g ∈ W := by simpa [hW] using hx
    have hconj : (g⁻¹ * z * g) * (g⁻¹ * x * g) * (g⁻¹ * z * g)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp hzN (g⁻¹ * x * g)).mp hxW
    rw [show g⁻¹ * (z * x * z⁻¹) * g =
      (g⁻¹ * z * g) * (g⁻¹ * x * g) * (g⁻¹ * z * g)⁻¹ from by group]
    exact hconj
  · intro hx
    change z * x * z⁻¹ ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g W at hx
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx
    change x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g W
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    have hxW : g⁻¹ * (z * x * z⁻¹) * g ∈ W := by simpa [hW] using hx
    have hxW' : (g⁻¹ * z * g) * (g⁻¹ * x * g) * (g⁻¹ * z * g)⁻¹ ∈ W := by
      rwa [show (g⁻¹ * z * g) * (g⁻¹ * x * g) * (g⁻¹ * z * g)⁻¹ =
        g⁻¹ * (z * x * z⁻¹) * g from by group]
    exact (Subgroup.mem_normalizer_iff.mp hzN (g⁻¹ * x * g)).mpr hxW'

theorem commute_of_commute_conj (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {g : G}
    (hgM : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ M)
    (hgW : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    {y : G} (hy : y ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))) (hy1 : y ≠ 1)
    {j : G} (hj : j ∈ CFSG.Open.pCoreOf 2 M) (hjy : j * y = y * j)
    {y' : G} (hy' : y' ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))) :
    j * y' = y' * j := by
  set W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) with hW
  set Y : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g W with hY
  have hyY : y ∈ Y := by simpa [hY] using hy
  have hy'Y : y' ∈ Y := by simpa [hY] using hy'
  have hgMY : Y ≤ M := by simpa [hY] using hgM
  have hjN : j ∈ Subgroup.normalizer (Y : Set G) := by
    have h := centralizer_le_normalizer_conj S (g := g) hy hy1
    refine h ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hjy.symm
  have hconjY : j * y' * j⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp hjN y').mp hy'Y
  have hcommY : j * y' * j⁻¹ * y'⁻¹ ∈ Y :=
    Y.mul_mem hconjY (Y.inv_mem hy'Y)
  have hcommJ : j * y' * j⁻¹ * y'⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
    have hy'M : y' ∈ M := hgMY hy'Y
    have hy'N : y' ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hy'M
    have h1 : y' * j * y'⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp hy'N j).mp hj
    have h2 : y' * j * y'⁻¹ * j⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (CFSG.Open.pCoreOf 2 M).mul_mem h1 ((CFSG.Open.pCoreOf 2 M).inv_mem hj)
    rw [show j * y' * j⁻¹ * y'⁻¹ = (y' * j * y'⁻¹ * j⁻¹)⁻¹ from by group]
    exact (CFSG.Open.pCoreOf 2 M).inv_mem h2
  have hYJ : Y ⊓ CFSG.Open.pCoreOf 2 M = ⊥ := by
    simpa [hY, hW] using conj_inf_pCoreOf_eq_bot S hF hc hW2 hWab (g := g)
      (by simpa [hY, hW] using hgW)
  have hbot : j * y' * j⁻¹ * y'⁻¹ = 1 := by
    have hmem : j * y' * j⁻¹ * y'⁻¹ ∈ Y ⊓ CFSG.Open.pCoreOf 2 M :=
      Subgroup.mem_inf.mpr ⟨hcommY, hcommJ⟩
    simpa [hYJ] using hmem
  have hconj : j * y' * j⁻¹ = y' := by
    calc j * y' * j⁻¹ = (j * y' * j⁻¹ * y'⁻¹) * y' := by group
      _ = 1 * y' := by rw [hbot]
      _ = y' := by group
  calc j * y' = (j * y' * j⁻¹) * j := by group
    _ = y' * j := by rw [hconj]

theorem conj_inf_centralizer_eq_bot (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {g : G}
    (hgM : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ M)
    (hgW : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ⊓
      Subgroup.centralizer (blockU L : Set G) = ⊥ := by
  set W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) with hW
  set Y : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g W with hY
  have hY2 : IsPGroup 2 Y := by
    rw [hY, CFSG.CGT.Timmesfeld75.conjSubgroup]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer (L : Set G))).map (MulAut.conj g).toMonoidHom
  have hYJ : Y ⊓ CFSG.Open.pCoreOf 2 M = ⊥ := by
    simpa [hY, hW] using conj_inf_pCoreOf_eq_bot S hF hc hW2 hWab (g := g)
      (by simpa [hY, hW] using hgW)
  have hgMY : Y ≤ M := by simpa [hY] using hgM
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨hxY, hxC⟩ := Subgroup.mem_inf.mp hx
  let X : Subgroup G := Y ⊓ Subgroup.centralizer (blockU L : Set G)
  have hxX : x ∈ X := Subgroup.mem_inf.mpr ⟨hxY, hxC⟩
  have hX2 : IsPGroup 2 X := hY2.to_inf_left
  have hXM : X ≤ M := (inf_le_left : X ≤ Y).trans hgMY
  have hXC : X ≤ Subgroup.centralizer (blockU L : Set G) := inf_le_right
  have hXJ : X ≤ CFSG.Open.pCoreOf 2 M :=
    S.le_pCoreOf_of_le_centralizer hF hc hW2 hX2 hXM hXC
  have hxYJ : x ∈ Y ⊓ CFSG.Open.pCoreOf 2 M :=
    Subgroup.mem_inf.mpr ⟨hxY, hXJ hxX⟩
  simpa [hYJ] using hxYJ

theorem card_psiSub_conj (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {g : G}
    (hgM : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ M)
    (hgW : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    Nat.card ↥(S.psiSub hc (CFSG.CGT.Timmesfeld75.conjSubgroup g
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))))) =
      Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) := by
  set W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) with hW
  set Y : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g W with hY
  have hgMY : Y ≤ M := by simpa [hY] using hgM
  have hYV : Y ⊓ Subgroup.centralizer (blockU L : Set G) = ⊥ := by
    simpa [hY, hW] using conj_inf_centralizer_eq_bot S hF hc hW2 hWab (g := g)
      (by simpa [hY, hW] using hgM) (by simpa [hY, hW] using hgW)
  have hcard := S.card_psiSub hc (A := Y) hgMY
  rw [hYV, Subgroup.card_bot, one_mul] at hcard
  have hYcard : Nat.card Y = Nat.card W := by
    rw [hY, CFSG.CGT.Timmesfeld75.conjSubgroup]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (K := W)
      (MulAut.conj g).injective
  rw [hYcard] at hcard
  exact hcard.symm

theorem fixPts_singleton_eq (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {g : G}
    (hgM : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ M)
    (hgW : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    ∀ b ∈ S.psiSub hc (CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))), b ≠ 1 →
      fixPts {b} = fixPts (S.psiSub hc (CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))) : Set _) := by
  intro b hb hb1
  set W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) with hW
  set Y : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g W with hY
  have hgMY : Y ≤ M := by simpa [hY] using hgM
  change b ∈ S.psiSub hc Y at hb
  rw [mem_psiSub S hc hgMY] at hb
  obtain ⟨y, hy, hyM, hb_eq⟩ := hb
  have hy1 : y ≠ 1 := by
    intro hy0
    apply hb1
    rw [← hb_eq]
    have hsub : (⟨y, hyM⟩ : ↥M) = 1 := Subtype.ext hy0
    rw [hsub, map_one]
  rw [← hb_eq]
  have hb_mem : S.psiM hc ⟨y, hyM⟩ ∈ S.psiSub hc Y := by
    rw [mem_psiSub S hc hgMY]
    exact ⟨y, hy, hyM, rfl⟩
  have hsub : fixPts (S.psiSub hc Y : Set (Equiv.Perm (Fin 64))) ⊆
      fixPts {S.psiM hc ⟨y, hyM⟩} := by
    intro v hv
    simp only [fixPts, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
    exact hv _ hb_mem
  have hcent : blockU L ⊓ Subgroup.centralizer (Y : Set G) =
      blockU L ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
      refine Subgroup.mem_inf.mpr ⟨hvV, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      exact Subgroup.mem_centralizer_iff.mp hvC y hy
    · intro v hv
      obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
      refine Subgroup.mem_inf.mpr ⟨hvV, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hvJ : v ∈ CFSG.Open.pCoreOf 2 M := S.blockU_le_pCoreOf hvV
      have hcomm : v * y = y * v :=
        (Subgroup.mem_centralizer_iff.mp hvC y (by simp)).symm
      exact (commute_of_commute_conj S hF hc hW2 hWab hgM hgW hy hy1 hvJ hcomm ha).symm
  have hcardY := S.card_inf_centralizer hc (A := Y) hgMY
  have hcardy := S.card_inf_centralizer_singleton hc (m := ⟨y, hyM⟩)
  have hcard_eq : Nat.card (fixPts {S.psiM hc ⟨y, hyM⟩}) =
      Nat.card (fixPts (S.psiSub hc Y : Set (Equiv.Perm (Fin 64)))) := by
    calc Nat.card (fixPts {S.psiM hc ⟨y, hyM⟩})
        = Nat.card ↥(blockU L ⊓ Subgroup.centralizer
            ({((⟨y, hyM⟩ : ↥M) : G)} : Set G)) := hcardy.symm
      _ = Nat.card ↥(blockU L ⊓ Subgroup.centralizer (Y : Set G)) := by rw [hcent]
      _ = Nat.card (fixPts (S.psiSub hc Y : Set (Equiv.Perm (Fin 64)))) := hcardY
  have hncard : (fixPts {S.psiM hc ⟨y, hyM⟩}).ncard =
      (fixPts (S.psiSub hc Y : Set (Equiv.Perm (Fin 64)))).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard_eq]
  exact (Set.eq_of_subset_of_ncard_le hsub (le_of_eq hncard) (Set.toFinite _)).symm

theorem of_four_le_card (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {g : G}
    (hgM : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ M)
    (hgW : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (h4 : 4 ≤ Nat.card (CFSG.Open.pCoreOf 2
      (Subgroup.centralizer (L : Set G)))) :
    S.psiSub hc (CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))) ≤ hexaL ∧
      Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 4 ∧
      (∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1) ∧
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer
        (CFSG.CGT.Timmesfeld75.conjSubgroup g
          (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) : Set G)) = 16 ∧
      CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ S.M1 hc := by
  set W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) with hW
  set Y : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g W with hY
  have hgMY : Y ≤ M := by simpa [hY] using hgM
  have hY2 : IsPGroup 2 Y := by
    rw [hY, CFSG.CGT.Timmesfeld75.conjSubgroup]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer (L : Set G))).map (MulAut.conj g).toMonoidHom
  have h4W : 4 ≤ Nat.card W := by simpa [hW] using h4
  have hcardYW : Nat.card (S.psiSub hc Y) = Nat.card W := by
    simpa [hY, hW] using card_psiSub_conj S hF hc hW2 hWab (g := g) hgM hgW
  have h4psi : 4 ≤ Nat.card (S.psiSub hc Y) := by
    rw [hcardYW]
    exact h4W
  have hfixeq : ∀ b ∈ S.psiSub hc Y, b ≠ 1 →
      fixPts {b} = fixPts (S.psiSub hc Y : Set _) := by
    intro b hb hb1
    have hb' : b ∈ S.psiSub hc (CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))) := by
      simpa [hY, hW] using hb
    simpa [hY, hW] using fixPts_singleton_eq S hF hc hW2 hWab hgM hgW b hb' hb1
  obtain ⟨hle, hcardpsi, hpsiSq, hfix⟩ :=
    hF.of_fixPts_eq (S.psiSub hc Y) (S.psiSub_le_hexaM hc Y)
      (S.isPGroup_psiSub hc hY2) h4psi hfixeq
  have hYsq : ∀ y ∈ Y, y * y = 1 := by
    intro y hy
    have hyM : y ∈ M := hgMY hy
    have hmem : S.psiM hc ⟨y, hyM⟩ ∈ S.psiSub hc Y := by
      rw [mem_psiSub S hc hgMY]
      exact ⟨y, hy, hyM, rfl⟩
    have hpsi : S.psiM hc ⟨y * y, hgMY (Y.mul_mem hy hy)⟩ = 1 := by
      have harg : (⟨y * y, hgMY (Y.mul_mem hy hy)⟩ : ↥M) =
          ⟨y, hyM⟩ * ⟨y, hyM⟩ := Subtype.ext rfl
      rw [harg, map_mul]
      exact hpsiSq _ hmem
    have hmemC : y * y ∈ Subgroup.centralizer (blockU L : Set G) :=
      (S.psiM_eq_one_iff hc ⟨y * y, hgMY (Y.mul_mem hy hy)⟩).mp hpsi
    have hmemV : y * y ∈ Y ⊓ Subgroup.centralizer (blockU L : Set G) :=
      Subgroup.mem_inf.mpr ⟨Y.mul_mem hy hy, hmemC⟩
    have hYV : Y ⊓ Subgroup.centralizer (blockU L : Set G) = ⊥ := by
      simpa [hY, hW] using conj_inf_centralizer_eq_bot S hF hc hW2 hWab (g := g) hgM hgW
    simpa [hYV] using hmemV
  have hWsq : ∀ w ∈ W, w * w = 1 := by
    intro w hw
    have hy : g * w * g⁻¹ ∈ Y := by
      rw [hY, CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      rw [show g⁻¹ * (g * w * g⁻¹) * g = w from by group]
      exact hw
    have h := hYsq (g * w * g⁻¹) hy
    calc w * w = g⁻¹ * ((g * w * g⁻¹) * (g * w * g⁻¹)) * g := by group
      _ = 1 := by rw [h]; group
  have hVY : Nat.card ↥(blockU L ⊓ Subgroup.centralizer (Y : Set G)) = 16 := by
    rw [S.card_inf_centralizer hc (A := Y) hgMY]
    exact hfix
  have hM1 : Y ≤ S.M1 hc := by
    intro y hy
    rw [mem_M1 S hc]
    refine ⟨hgMY hy, ?_⟩
    have hmem : S.psiM hc ⟨y, hgMY hy⟩ ∈ S.psiSub hc Y := by
      rw [mem_psiSub S hc hgMY]
      exact ⟨y, hy, hgMY hy, rfl⟩
    exact hle hmem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hY, hW] using hle
  · rw [← hcardYW]
    exact hcardpsi
  · exact hWsq
  · simpa [hY] using hVY
  · simpa [hY] using hM1

theorem card_eq_two_or_four (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    {g : G}
    (hgM : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ M)
    (hgW : CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 2 ∨
      (Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 4 ∧
        ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1) := by
  set W : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) with hW
  set Y : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g W with hY
  have hWne : W ≠ ⊥ := by
    intro hbot
    apply hgW
    rw [hY, hbot, CFSG.CGT.Timmesfeld75.conjSubgroup, Subgroup.map_bot]
  have hcardne1 : Nat.card W ≠ 1 := by
    intro h
    exact hWne (Subgroup.card_eq_one.mp h)
  have h2le : 2 ≤ Nat.card W := by
    have hpos : 0 < Nat.card W := Nat.card_pos
    omega
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
    (Subgroup.centralizer (L : Set G))).exists_card_eq
  have hn' : Nat.card W = 2 ^ n := by simpa [hW] using hn
  by_cases h2 : Nat.card W = 2
  · left
    exact h2
  · right
    have hn0 : n ≠ 0 := by
      intro h
      apply hcardne1
      have hh : Nat.card W = 2 ^ 0 := by rw [h] at hn'; exact hn'
      rw [pow_zero] at hh
      exact hh
    have hn1 : n ≠ 1 := by
      intro h
      apply h2
      rw [hn', h]
      norm_num
    have h2n : 2 ≤ n := by omega
    have h4 : 4 ≤ Nat.card W := by
      rw [hn']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2n
    obtain ⟨-, hcard, hsq, -, -⟩ := of_four_le_card S hF hc hW2 hWab hgM hgW
      (by simpa [hW] using h4)
    exact ⟨hcard, hsq⟩

end CFSG.CGT.Hall82.Setting
