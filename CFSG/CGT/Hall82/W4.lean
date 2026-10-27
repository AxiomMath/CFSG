module

public import CFSG.CGT.Hall82.Centralize
public import CFSG.CGT.Hall82.WStruct
public import CFSG.RankThree.PartTwo.Sec15.Item1424Proof

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

theorem isElemAbelian_pCoreOf (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hWel : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1) :
    CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 M) := by
  have hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a :=
    fun a ha b hb => mul_comm_of_mul_self_eq_one hWel ha hb
  have hWea : CFSG.Open.IsElemAbelian 2
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :=
    ⟨⟨⟨fun a b => Subtype.ext (hWab a.1 a.2 b.1 b.2)⟩⟩, fun x hx => by
      rw [pow_two]
      exact hWel x hx⟩
  have hJe : CFSG.Open.pCoreOf 2 M =
      blockU L ⊔ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) :=
    S.pCoreOf_eq hF hc
  rw [hJe]
  exact CFSG.Open.IsElemAbelian.sup_of_commute S.elemU hWea
    (fun v hv w hw => S.commute_blockU_pCoreOf_centralizer hv hw)

theorem exists_abelian_of_conj_ne (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 4)
    (hWel : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1)
    {h : G}
    (hYM : CFSG.CGT.Timmesfeld75.conjSubgroup h
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ M)
    (hYW : CFSG.CGT.Timmesfeld75.conjSubgroup h
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≠
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    ∃ A : Subgroup G,
      CFSG.CGT.Timmesfeld75.conjSubgroup h
          (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ≤ A ∧
      A ≤ (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer
            (CFSG.CGT.Timmesfeld75.conjSubgroup h
              (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) : Set G)) ⊔
          CFSG.CGT.Timmesfeld75.conjSubgroup h
            (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      Nat.card (CFSG.Open.pCoreOf 2 M) ≤ Nat.card A ∧
      A ≠ CFSG.Open.pCoreOf 2 M := by
  classical
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 C
  let J : Subgroup G := CFSG.Open.pCoreOf 2 M
  let Y : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup h W
  have hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a :=
    fun a ha b hb => mul_comm_of_mul_self_eq_one hWel ha hb
  have hWcard : Nat.card W = 4 := by simpa [W, C] using hcard
  have hJab : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a :=
    fun a ha b hb => S.commute_of_mem_pCoreOf hF hc hWab (by simpa [J] using ha)
      (by simpa [J] using hb)
  have hY2 : IsPGroup 2 Y := by
    rw [show Y = CFSG.CGT.Timmesfeld75.conjSubgroup h W from rfl,
      CFSG.CGT.Timmesfeld75.conjSubgroup]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C).map (MulAut.conj h).toMonoidHom
  have hYcard : Nat.card Y = 4 := by
    rw [show Y = CFSG.CGT.Timmesfeld75.conjSubgroup h W from rfl,
      CFSG.CGT.Timmesfeld75.conjSubgroup,
      Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom) (K := W)
        (MulAut.conj h).injective, hWcard]
  have hYM' : Y ≤ M := by simpa [Y, W] using hYM
  have hYW' : Y ≠ W := by simpa [Y] using hYW
  have hYV : Nat.card ↥(blockU L ⊓ Subgroup.centralizer (Y : Set G)) = 16 := by
    obtain ⟨-, -, -, hV, -⟩ :=
      of_four_le_card S hF hc hW2 hWab (g := h) hYM' hYW' (by rw [hWcard])
    simpa [Y] using hV
  have hWleCY : W ≤ Subgroup.centralizer (Y : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact commute_of_isPGroup S hF hc hW2 hWcard hWel hYM' hY2 hy
      (by simpa [W, C] using hw)
  have hYJ : Y ⊓ J = ⊥ := by
    have h := conj_inf_pCoreOf_eq_bot S hF hc hW2 hWab (g := h) hYW'
    simpa [Y, W, J] using h
  let P : Subgroup G := J ⊓ Subgroup.centralizer (Y : Set G)
  let A : Subgroup G := P ⊔ Y
  have hPcard : Nat.card P = 64 := by
    have h1 := S.card_pCoreOf_inf_centralizer hF hc (A := Y) hYM'
    have hWY : (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ⊓
        Subgroup.centralizer (Y : Set G)) = W := by
      rw [show CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) = W from rfl,
        inf_eq_left.mpr hWleCY]
    rw [hWY, hWcard, hYV] at h1
    have h1' : Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓
        Subgroup.centralizer (Y : Set G)) = 64 := by
      rwa [show (16 : ℕ) * 4 = 64 from by norm_num] at h1
    simpa [P, J] using h1'
  have hPYbot : P ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxJ : x ∈ J := (Subgroup.mem_inf.mp hx.1).1
    have hxY : x ∈ Y := hx.2
    have hmem : x ∈ Y ⊓ J := Subgroup.mem_inf.mpr ⟨hxY, hxJ⟩
    rwa [hYJ] at hmem
  have hPYcomm : ∀ a ∈ P, ∀ b ∈ Y, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 b hb).symm
  have hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    intro a ha b hb
    rw [show Y = CFSG.CGT.Timmesfeld75.conjSubgroup h W from rfl,
      CFSG.CGT.Timmesfeld75.conjSubgroup, Subgroup.mem_map] at ha hb
    obtain ⟨a0, ha0, rfl⟩ := ha
    obtain ⟨b0, hb0, rfl⟩ := hb
    rw [← map_mul, ← map_mul, hWab a0 ha0 b0 hb0]
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    exact hJab a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨p1, hp1, y1, hy1, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hPYcomm ha
    obtain ⟨p2, hp2, y2, hy2, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hPYcomm hb
    calc (p1 * y1) * (p2 * y2)
        = p1 * (y1 * p2) * y2 := by group
      _ = p1 * (p2 * y1) * y2 := by rw [← hPYcomm p2 hp2 y1 hy1]
      _ = (p1 * p2) * (y1 * y2) := by group
      _ = (p2 * p1) * (y2 * y1) := by rw [hPab p1 hp1 p2 hp2, hYab y1 hy1 y2 hy2]
      _ = p2 * (p1 * y2) * y1 := by group
      _ = p2 * (y2 * p1) * y1 := by rw [← hPYcomm p1 hp1 y2 hy2]
      _ = (p2 * y2) * (p1 * y1) := by group
  have hAcard : Nat.card A = 256 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P Y hPYcomm).1
    rw [hPYbot, Subgroup.card_bot, hPcard, hYcard] at h
    simp only [mul_one] at h
    rw [show A = P ⊔ Y from rfl, h]
  have hJcard : Nat.card J = 64 * Nat.card W := by simpa [J, W, C] using S.card_pCoreOf hF hc
  refine ⟨A, ?_, ?_, hAab, ?_, ?_⟩
  · rw [show A = P ⊔ Y from rfl]
    exact le_sup_right
  · rw [show A = P ⊔ Y from rfl]
  · rw [hJcard, hWcard, hAcard]
  · intro hAJ
    have hYleJ : Y ≤ J := by
      change Y ≤ CFSG.Open.pCoreOf 2 M
      rw [← hAJ]
      exact le_sup_right
    have hYbot : Y = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hmem : y ∈ Y ⊓ J := Subgroup.mem_inf.mpr ⟨hy, hYleJ hy⟩
      rwa [hYJ] at hmem
    have hY1 : Nat.card Y = 1 := by rw [hYbot, Subgroup.card_bot]
    omega

theorem centralizer_singleton_le (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 4)
    (hWel : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1)
    {t : G} (ht : t ∈ CFSG.Open.pCoreOf 2 M) (ht1 : t ≠ 1) :
    Subgroup.centralizer ({t} : Set G) ≤ M := by
  classical
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let W : Subgroup G := CFSG.Open.pCoreOf 2 C
  let J : Subgroup G := CFSG.Open.pCoreOf 2 M
  have hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a :=
    fun a ha b hb => mul_comm_of_mul_self_eq_one hWel ha hb
  have hWcard : Nat.card W = 4 := by simpa [W, C] using hcard
  by_cases htW : t ∈ W
  · exact centralizer_le_of_mem_pCoreOf S.uniq (by simpa [W, C] using htW) ht1
  · intro h hh
    let R₀ : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({t} : Set G))
    let Q : Subgroup G :=
      CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer ({t} : Set G))
    have hR0M : R₀ ≤ M :=
      S.pCoreOf_centralizer_singleton_le hF hc hW2 hWab (by simpa [J] using ht)
    have hJleCt : J ≤ Subgroup.centralizer ({t} : Set G) := by
      intro j hj
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact (S.commute_of_mem_pCoreOf hF hc hWab (by simpa [J] using hj) ht).symm
    have hWleJ : W ≤ J := by simpa [W, J, C] using S.pCoreOf_centralizer_le
    have hWleCt : W ≤ Subgroup.centralizer ({t} : Set G) := hWleJ.trans hJleCt
    have hWcentR0 : W ≤ Subgroup.centralizer (R₀ : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact commute_of_isPGroup S hF hc hW2 hWcard hWel hR0M
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hr (by simpa [W, C] using hw)
    have hWleR0 : W ≤ R₀ := by
      have hfit : CFSG.generalizedFitting ↥(Subgroup.centralizer ({t} : Set G)) =
          CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G)) :=
        S.cent t (by simpa [J] using ht) ht1
      have h := CFSG.RankThree.PartTwo.Sec15.inf_centralizer_le_pCoreOf_of_fitting
        (G := G) (Y := Subgroup.centralizer ({t} : Set G)) hfit
      intro w hw
      exact h (Subgroup.mem_inf.mpr ⟨hWleCt hw, hWcentR0 hw⟩)
    have hhnorm : h ∈ Subgroup.normalizer (R₀ : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
        (Subgroup.centralizer ({t} : Set G)) hh
    have hYleR0 : CFSG.CGT.Timmesfeld75.conjSubgroup h W ≤ R₀ := by
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup]
      calc W.map (MulAut.conj h).toMonoidHom ≤ R₀.map (MulAut.conj h).toMonoidHom :=
            Subgroup.map_mono hWleR0
        _ = R₀ := by
            simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hhnorm)
    have hYleM : CFSG.CGT.Timmesfeld75.conjSubgroup h W ≤ M := hYleR0.trans hR0M
    by_cases hYW : CFSG.CGT.Timmesfeld75.conjSubgroup h W = W
    · have hhN : h ∈ Subgroup.normalizer (W : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        show W.map (MulAut.conj h).toMonoidHom = W
        simpa [CFSG.CGT.Timmesfeld75.conjSubgroup] using hYW
      have hWne : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≠ ⊥ := by
        intro hbot
        have h1 : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 1 := by
          rw [hbot, Subgroup.card_bot]
        omega
      have hNW : Subgroup.normalizer (W : Set G) = M := by
        simpa [W, C] using
          normalizer_pCoreOf_centralizer_eq S.normalizer_eq S.uniq hWne
      rwa [hNW] at hhN
    · exfalso
      obtain ⟨A, -, hAle, hAab, hcardJA, hAJ⟩ :=
        exists_abelian_of_conj_ne S hF hc hW2 hcard hWel hYleM hYW
      have hR0Q : R₀ ≤ Q := by
        simpa [R₀, Q] using S.le_pCoreOf_inf_of_le hF hc hW2 hWab ht
      have hYQ : CFSG.CGT.Timmesfeld75.conjSubgroup h W ≤ Q := hYleR0.trans hR0Q
      have hJQ : J ≤ Q := by
        refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
        · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 M) hJleCt
        · intro m hm
          exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm.1
      have hAQ : A ≤ Q := hAle.trans (sup_le (inf_le_left.trans hJQ) hYQ)
      have hAeqJ : A = J := by
        have h := S.eq_of_le_pCoreOf_centralizer hF hc hW2 hWab ht hAQ hAab hcardJA
        simpa [J] using h
      exact hAJ hAeqJ

theorem isTI (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 4)
    (hWel : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1) :
    CFSG.CGT.Timmesfeld75.IsTI (CFSG.Open.pCoreOf 2 M) := by
  classical
  have hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a :=
    fun a ha b hb => mul_comm_of_mul_self_eq_one hWel ha hb
  have hW1 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 1 := by
      rw [hbot, Subgroup.card_bot]
    omega
  have hJab : ∀ a ∈ CFSG.Open.pCoreOf 2 M, ∀ b ∈ CFSG.Open.pCoreOf 2 M,
      a * b = b * a :=
    fun a ha b hb => S.commute_of_mem_pCoreOf hF hc hWab ha hb
  intro g
  by_cases hbot : CFSG.Open.pCoreOf 2 M ⊓
      CFSG.CGT.Timmesfeld75.conjSubgroup g (CFSG.Open.pCoreOf 2 M) = ⊥
  · exact Or.inl hbot
  · right
    have hnt : Nontrivial ↥(CFSG.Open.pCoreOf 2 M ⊓
        CFSG.CGT.Timmesfeld75.conjSubgroup g (CFSG.Open.pCoreOf 2 M)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hbot
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(CFSG.Open.pCoreOf 2 M ⊓
      CFSG.CGT.Timmesfeld75.conjSubgroup g (CFSG.Open.pCoreOf 2 M)))
    have hx1 : (z : G) ≠ 1 := by
      intro h0
      exact hz1 (Subtype.ext h0)
    have hxJ : (z : G) ∈ CFSG.Open.pCoreOf 2 M := z.2.1
    have hxY : (z : G) ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 M) := z.2.2
    have hYab : ∀ a ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g
        (CFSG.Open.pCoreOf 2 M),
        ∀ b ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (CFSG.Open.pCoreOf 2 M),
        a * b = b * a := by
      intro a ha b hb
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup, Subgroup.mem_map] at ha hb
      obtain ⟨a0, ha0, rfl⟩ := ha
      obtain ⟨b0, hb0, rfl⟩ := hb
      rw [← map_mul, ← map_mul, hJab a0 ha0 b0 hb0]
    have hYleCx : CFSG.CGT.Timmesfeld75.conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≤
        Subgroup.centralizer ({(z : G)} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst u
      exact (hYab y hy (z : G) hxY).symm
    have hYM : CFSG.CGT.Timmesfeld75.conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≤ M :=
      hYleCx.trans
        (S.centralizer_singleton_le hF hc hW2 hcard hWel hxJ hx1)
    have hYeq : CFSG.CGT.Timmesfeld75.conjSubgroup g (CFSG.Open.pCoreOf 2 M) =
        CFSG.Open.pCoreOf 2 M :=
      (weaklyClosedIn_pCoreOf S hF hc hW2 hWab hW1).2 g hYM
    rw [hYeq, inf_idem]

theorem weaklyClosedIn_normalizer (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 4)
    (hWel : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1) :
    CFSG.CGT.Timmesfeld75.WeaklyClosedIn (CFSG.Open.pCoreOf 2 M)
      (Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G)) := by
  have hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a :=
    fun a ha b hb => mul_comm_of_mul_self_eq_one hWel ha hb
  have hW1 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 1 := by
      rw [hbot, Subgroup.card_bot]
    omega
  have hNM : Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) = M :=
    S.normalizer_pCoreOf
  refine ⟨Subgroup.le_normalizer, ?_⟩
  intro g hg
  rw [hNM] at hg
  exact (weaklyClosedIn_pCoreOf S hF hc hW2 hWab hW1).2 g hg

theorem inCatalog_of_card_eq_four
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    (S : Setting G M L)
    (hF : ModelFacts) (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) = 4)
    (hWel : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w * w = 1) :
    CFSG.Assembly.InCatalog G := by
  have hJ1 : CFSG.Open.pCoreOf 2 M ≠ ⊥ := by
    intro hbot
    have hJcard : Nat.card (CFSG.Open.pCoreOf 2 M) =
        64 * Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :=
      S.card_pCoreOf hF hc
    rw [hbot, Subgroup.card_bot, hcard] at hJcard
    norm_num at hJcard
  exact inCatalog_of_isTI_of_weaklyClosedIn hNode S.simple S.nonab
    (isElemAbelian_pCoreOf S hF hc hWel) hJ1
    (isTI S hF hc hW2 hcard hWel)
    (weaklyClosedIn_normalizer S hF hc hW2 hcard hWel)

end CFSG.CGT.Hall82.Setting
