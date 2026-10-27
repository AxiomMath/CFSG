module

public import CFSG.LieType.Chevalley.E6GraphInnerCosetGeneric
public import CFSG.LieType.Chevalley.E6GraphRootPairDichotomy

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphInnerCoset

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphRootSL2
  CFSG.LieType.Chevalley.E6GraphRootPair

variable {E : Type} [Field E] {F₀ : Type} [Field F₀]

structure ExhaustionData (ι : F₀ →+* E) (G L Q U : Subgroup (ModGL TwistTag.E6.tag E)) :
    Prop where
  two_eq_zero : (2 : E) = 0
  P_mul_self : diagramMap TwistTag.E6 E * diagramMap TwistTag.E6 E = 1
  P_conj_G : ∀ g ∈ G, diagramMap TwistTag.E6 E * g * (diagramMap TwistTag.E6 E)⁻¹ ∈ G
  P_not_mem : diagramMap TwistTag.E6 E ∉ G
  U_le : U ≤ G
  U_sylow : ∃ S : Sylow 2 ↥G, (S : Subgroup ↥G) = U.subgroupOf G
  P_conj_U : ∀ u ∈ U, diagramMap TwistTag.E6 E * u * (diagramMap TwistTag.E6 E)⁻¹ ∈ U
  U_le_centralizer :
    U ≤ Subgroup.centralizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag E))
  centralizer_factor : ∀ g ∈ Subgroup.centralizer (thetaRootGroup ι :
      Set (ModGL TwistTag.E6.tag E)) ⊓ G, ∃ q ∈ Q, ∃ l ∈ L, g = q * l
  Q_le : Q ≤ G
  L_le : L ≤ G
  Q_inf_L : Q ⊓ L = ⊥
  L_le_normalizer : L ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag E))
  P_conj_Q : ∀ q ∈ Q, diagramMap TwistTag.E6 E * q * (diagramMap TwistTag.E6 E)⁻¹ ∈ Q
  P_conj_L : ∀ l ∈ L, diagramMap TwistTag.E6 E * l * (diagramMap TwistTag.E6 E)⁻¹ ∈ L
  X_le : thetaRankOneGroup ι ≤ G
  P_conj_X : ∀ x ∈ thetaRankOneGroup ι,
    diagramMap TwistTag.E6 E * x * (diagramMap TwistTag.E6 E)⁻¹ = x
  L_commute_X : ∀ x ∈ thetaRankOneGroup ι, ∀ l ∈ L, x * l = l * x
  X_inf_L : thetaRankOneGroup ι ⊓ L = ⊥
  normalizer_factor : ∀ g ∈ Subgroup.normalizer (thetaRankOneGroup ι :
      Set (ModGL TwistTag.E6.tag E)) ⊓ G, ∃ x ∈ thetaRankOneGroup ι, ∃ l ∈ L, g = x * l
  levi_form : ∀ l ∈ L, (l * diagramMap TwistTag.E6 E) ^ 2 = 1 →
    (∃ x ∈ L, x * (l * diagramMap TwistTag.E6 E) * x⁻¹ = diagramMap TwistTag.E6 E) ∨
      ∃ x ∈ L, x * (l * diagramMap TwistTag.E6 E) * x⁻¹ =
        pinnedX TwistTag.E6.tag E sRoot 1 * diagramMap TwistTag.E6 E
  levi_detector : ∀ l ∈ L, (l * diagramMap TwistTag.E6 E) ^ 2 = 1 →
    (∃ x ∈ L, x * (l * diagramMap TwistTag.E6 E) * x⁻¹ =
      pinnedX TwistTag.E6.tag E sRoot 1 * diagramMap TwistTag.E6 E) →
    ∃ g ∈ G, (thetaRootGroup ι).map (MulAut.conj g).toMonoidHom ≤ L ∧
      ¬ IsPGroup 2 ↥((thetaRootGroup ι).map (MulAut.conj g).toMonoidHom ⊔
        ((thetaRootGroup ι).map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj (l * diagramMap TwistTag.E6 E)).toMonoidHom)
  radical : ∀ a ∈ Q, (a * diagramMap TwistTag.E6 E) ^ 2 = 1 →
    (∃ g ∈ G, g * (a * diagramMap TwistTag.E6 E) * g⁻¹ = diagramMap TwistTag.E6 E) ∨
      (∃ g ∈ G, g * (a * diagramMap TwistTag.E6 E) * g⁻¹ =
        pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E) ∨
      ∃ g ∈ G, ¬ IsPGroup 2 ↥((thetaRootGroup ι).map (MulAut.conj g).toMonoidHom ⊔
        ((thetaRootGroup ι).map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj (a * diagramMap TwistTag.E6 E)).toMonoidHom)
  pair : ∀ g₁ ∈ G, ∀ j ∈ G ⊔ Subgroup.zpowers (diagramMap TwistTag.E6 E), j * j = 1 →
    ¬ IsPGroup 2 ↥((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
      ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj j).toMonoidHom) →
    (∃ g ∈ G, (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
        ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj j).toMonoidHom =
      (thetaRankOneGroup ι).map (MulAut.conj g).toMonoidHom) ∧
    ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
        ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map
          (MulAut.conj j).toMonoidHom).map (MulAut.conj j).toMonoidHom =
      (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
        ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj j).toMonoidHom ∧
    ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj j).toMonoidHom ≠
      (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom
  fusion_mem : wordElt E fusionWord ∈ G
  fusion_P : diagramMap TwistTag.E6 E * wordElt E fusionWord * (diagramMap TwistTag.E6 E)⁻¹ =
    wordElt E fusionWord
  fusion_L : wordElt E fusionWord * (pinnedX TwistTag.E6.tag E e6HighestRoot 1 *
    pinnedX TwistTag.E6.tag E sRoot 1) * (wordElt E fusionWord)⁻¹ ∈ L
  up_mem : wordElt E upWord.reverse ∈ G
  up_P : diagramMap TwistTag.E6 E * wordElt E upWord.reverse * (diagramMap TwistTag.E6 E)⁻¹ =
    wordElt E upWord.reverse
  up_conj : wordElt E upWord.reverse * pinnedX TwistTag.E6.tag E sRoot 1 *
    (wordElt E upWord.reverse)⁻¹ = pinnedX TwistTag.E6.tag E e6HighestRoot 1

namespace ExhaustionData

variable {ι : F₀ →+* E} {G L Q U : Subgroup (ModGL TwistTag.E6.tag E)}

theorem P_inv
    (D : ExhaustionData ι G L Q U) :
    (diagramMap TwistTag.E6 E)⁻¹ = diagramMap TwistTag.E6 E :=
  (eq_inv_of_mul_eq_one_left D.P_mul_self).symm

theorem mul_diagramMap_mem_sup {b : ModGL TwistTag.E6.tag E} (hb : b ∈ G) :
    b * diagramMap TwistTag.E6 E ∈ G ⊔ Subgroup.zpowers (diagramMap TwistTag.E6 E) :=
  mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem conj_mul_P
    (D : ExhaustionData ι G L Q U) {g b : ModGL TwistTag.E6.tag E} (hg : g ∈ G)
    (hb : b ∈ G) : ∃ b' ∈ G, g * (b * diagramMap TwistTag.E6 E) * g⁻¹ =
      b' * diagramMap TwistTag.E6 E :=
  ⟨g * b * (diagramMap TwistTag.E6 E * g⁻¹ * (diagramMap TwistTag.E6 E)⁻¹),
    mul_mem (mul_mem hg hb) (D.P_conj_G _ (inv_mem hg)), by group⟩

theorem mem_normalizer_of_map_eq {H : Subgroup (ModGL TwistTag.E6.tag E)}
    {g : ModGL TwistTag.E6.tag E} (h : H.map (MulAut.conj g).toMonoidHom = H) :
    g ∈ Subgroup.normalizer (H : Set (ModGL TwistTag.E6.tag E)) := by
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← h]
    exact ⟨x, hx, rfl⟩
  · rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [mul_assoc] using this
    rwa [← this]

theorem final_of_not_isPGroup
    (D : ExhaustionData ι G L Q U) [Finite E] [Finite F₀]
    {b : ModGL TwistTag.E6.tag E} (hb : b ∈ G)
    (hjj : (b * diagramMap TwistTag.E6 E) * (b * diagramMap TwistTag.E6 E) = 1)
    {g₁ : ModGL TwistTag.E6.tag E} (hg₁ : g₁ ∈ G)
    (hnot : ¬ IsPGroup 2 ↥((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
      ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map
        (MulAut.conj (b * diagramMap TwistTag.E6 E)).toMonoidHom)) :
    (∃ g ∈ G, g * (b * diagramMap TwistTag.E6 E) * g⁻¹ = diagramMap TwistTag.E6 E) ∨
      ∃ g ∈ G, g * (b * diagramMap TwistTag.E6 E) * g⁻¹ =
        pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E := by
  obtain ⟨⟨g', hg', hH⟩, hnorm, hne⟩ := D.pair g₁ hg₁ _ (mul_diagramMap_mem_sup hb) hjj hnot
  obtain ⟨b'', hb'', hj''⟩ := D.conj_mul_P (inv_mem hg') hb
  have hXj : (thetaRankOneGroup ι).map
      (MulAut.conj (b'' * diagramMap TwistTag.E6 E)).toMonoidHom = thetaRankOneGroup ι := by
    rw [← hj'', inv_inv, map_conj_mul, map_conj_mul, ← hH, hnorm, hH, ← map_conj_mul,
      inv_mul_cancel, map_conj_one]
  have hPN : (diagramMap TwistTag.E6 E)⁻¹ ∈
      Subgroup.normalizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E)) := by
    refine mem_normalizer_of_map_eq (map_conj_of_forall fun x hx => ?_)
    rw [D.P_inv]
    exact D.P_conj_X x hx
  have hb''N : b'' ∈ Subgroup.normalizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E)) := by
    have := mul_mem (mem_normalizer_of_map_eq hXj) hPN
    rwa [mul_inv_cancel_right] at this
  obtain ⟨x, hx, l, hl, rfl⟩ := D.normalizer_factor b'' (Subgroup.mem_inf.2 ⟨hb''N, hb''⟩)
  have hPx := D.P_conj_X x hx
  have hxl : x * l = l * x := D.L_commute_X x hx l hl
  have hjj'' : (x * l * diagramMap TwistTag.E6 E) * (x * l * diagramMap TwistTag.E6 E) = 1 := by
    rw [← hj'']
    calc g'⁻¹ * (b * diagramMap TwistTag.E6 E) * g'⁻¹⁻¹ *
          (g'⁻¹ * (b * diagramMap TwistTag.E6 E) * g'⁻¹⁻¹) =
          g'⁻¹ * ((b * diagramMap TwistTag.E6 E) * (b * diagramMap TwistTag.E6 E)) * g'⁻¹⁻¹ := by
          group
      _ = 1 := by rw [hjj]; group
  have e1 : (x * l * diagramMap TwistTag.E6 E) * (x * l * diagramMap TwistTag.E6 E) =
      (x * x) * (l * (diagramMap TwistTag.E6 E * l * (diagramMap TwistTag.E6 E)⁻¹)) := by
    calc (x * l * diagramMap TwistTag.E6 E) * (x * l * diagramMap TwistTag.E6 E) =
          x * l * (diagramMap TwistTag.E6 E * x * (diagramMap TwistTag.E6 E)⁻¹) *
            (diagramMap TwistTag.E6 E * l * (diagramMap TwistTag.E6 E)⁻¹) *
            (diagramMap TwistTag.E6 E * diagramMap TwistTag.E6 E) := by
          group
      _ = x * (l * x) * (diagramMap TwistTag.E6 E * l * (diagramMap TwistTag.E6 E)⁻¹) := by
          rw [hPx, D.P_mul_self, mul_one]
          group
      _ = _ := by rw [← hxl]; group
  have hm := mul_mem hl (D.P_conj_L l hl)
  rw [e1] at hjj''
  have hxx : x * x ∈ thetaRankOneGroup ι ⊓ L := by
    refine Subgroup.mem_inf.2 ⟨mul_mem hx hx, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hjj'']
    exact inv_mem hm
  rw [D.X_inf_L, Subgroup.mem_bot] at hxx
  have hlP : (l * diagramMap TwistTag.E6 E) ^ 2 = 1 := by
    rw [hxx, one_mul] at hjj''
    calc (l * diagramMap TwistTag.E6 E) ^ 2 =
          l * (diagramMap TwistTag.E6 E * l * (diagramMap TwistTag.E6 E)⁻¹) *
            (diagramMap TwistTag.E6 E * diagramMap TwistTag.E6 E) := by rw [sq]; group
      _ = 1 := by rw [hjj'', D.P_mul_self, mul_one]
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hne
    have hR₁X : ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map
        (MulAut.conj g'⁻¹).toMonoidHom ≤ thetaRankOneGroup ι := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' := (le_sup_left : (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ≤
        (thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom ⊔
          ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map
            (MulAut.conj (b * diagramMap TwistTag.E6 E)).toMonoidHom) hw
      rw [hH] at hw'
      obtain ⟨v, hv, rfl⟩ := hw'
      simpa [mul_assoc] using hv
    have hfix := map_conj_of_forall (H := ((thetaRootGroup ι).map
      (MulAut.conj g₁).toMonoidHom).map (MulAut.conj g'⁻¹).toMonoidHom)
      (g := 1 * l * diagramMap TwistTag.E6 E) fun z hz => by
        have hzX := hR₁X hz
        calc 1 * l * diagramMap TwistTag.E6 E * z * (1 * l * diagramMap TwistTag.E6 E)⁻¹ =
              l * (diagramMap TwistTag.E6 E * z * (diagramMap TwistTag.E6 E)⁻¹) * l⁻¹ := by
              group
          _ = z := by rw [D.P_conj_X z hzX, ← D.L_commute_X z hzX l hl, mul_inv_cancel_right]
    rw [← hj'', ← map_conj_mul, show g'⁻¹ * (b * diagramMap TwistTag.E6 E) * g'⁻¹⁻¹ * g'⁻¹ =
      g'⁻¹ * (b * diagramMap TwistTag.E6 E) by group, map_conj_mul] at hfix
    exact Subgroup.map_injective (MulAut.conj g'⁻¹).injective hfix
  obtain ⟨y, hy, hyx⟩ := exists_conj_eq_theta D.two_eq_zero ι hx hxx hx1
  have htX : pinnedX TwistTag.E6.tag E e6HighestRoot 1 ∈ thetaRankOneGroup ι :=
    (le_sup_left : thetaRootGroup ι ≤ thetaRankOneGroup ι)
      ((mem_thetaRootGroup ι).2 ⟨1, by rw [map_one]⟩)
  have hyl := D.L_commute_X y hy l hl
  have hyP := D.P_conj_X y hy
  have e2 : y * g'⁻¹ * (b * diagramMap TwistTag.E6 E) * (y * g'⁻¹)⁻¹ =
      pinnedX TwistTag.E6.tag E e6HighestRoot 1 * (l * diagramMap TwistTag.E6 E) := by
    calc y * g'⁻¹ * (b * diagramMap TwistTag.E6 E) * (y * g'⁻¹)⁻¹ =
          y * (g'⁻¹ * (b * diagramMap TwistTag.E6 E) * g'⁻¹⁻¹) * y⁻¹ := by group
      _ = (y * x * y⁻¹) * (y * l * y⁻¹) *
            (y * (diagramMap TwistTag.E6 E * y⁻¹ * (diagramMap TwistTag.E6 E)⁻¹)) *
            diagramMap TwistTag.E6 E := by rw [hj'']; group
      _ = _ := by
          have hyP' : diagramMap TwistTag.E6 E * y⁻¹ * (diagramMap TwistTag.E6 E)⁻¹ = y⁻¹ := by
            rw [← inv_inj]
            simpa [mul_assoc] using hyP
          rw [hyx, hyP', mul_inv_cancel, mul_one, hyl, mul_inv_cancel_right]
          group
  have hsq : ∀ c : ModGL TwistTag.E6.tag E,
      (c * (b * diagramMap TwistTag.E6 E) * c⁻¹) ^ 2 = 1 := fun c => by
    calc (c * (b * diagramMap TwistTag.E6 E) * c⁻¹) ^ 2 =
          c * ((b * diagramMap TwistTag.E6 E) * (b * diagramMap TwistTag.E6 E)) * c⁻¹ := by
          rw [sq]; group
      _ = 1 := by rw [hjj]; group
  have hyG : y * g'⁻¹ ∈ G := mul_mem (D.X_le hy) (inv_mem hg')
  rcases D.levi_form l hl hlP with ⟨z, hz, hzl⟩ | ⟨z, hz, hzl⟩
  ·
    refine Or.inr ⟨z * (y * g'⁻¹), mul_mem (D.L_le hz) hyG, ?_⟩
    calc z * (y * g'⁻¹) * (b * diagramMap TwistTag.E6 E) * (z * (y * g'⁻¹))⁻¹ =
          z * (y * g'⁻¹ * (b * diagramMap TwistTag.E6 E) * (y * g'⁻¹)⁻¹) * z⁻¹ := by group
      _ = (z * pinnedX TwistTag.E6.tag E e6HighestRoot 1 * z⁻¹) *
            (z * (l * diagramMap TwistTag.E6 E) * z⁻¹) := by rw [e2]; group
      _ = _ := by
          rw [hzl, ← D.L_commute_X _ htX z hz, mul_inv_cancel_right]
  ·
    set n := wordElt E fusionWord with hn
    have hnP : n * diagramMap TwistTag.E6 E * n⁻¹ = diagramMap TwistTag.E6 E := by
      calc n * diagramMap TwistTag.E6 E * n⁻¹ =
            n * (diagramMap TwistTag.E6 E * n * (diagramMap TwistTag.E6 E)⁻¹)⁻¹ *
              diagramMap TwistTag.E6 E := by group
        _ = _ := by rw [D.fusion_P, mul_inv_cancel, one_mul]
    set c := n * z * (y * g'⁻¹) with hc
    have hcG : c ∈ G := mul_mem (mul_mem D.fusion_mem (D.L_le hz)) hyG
    have e3 : c * (b * diagramMap TwistTag.E6 E) * c⁻¹ =
        (n * (pinnedX TwistTag.E6.tag E e6HighestRoot 1 * pinnedX TwistTag.E6.tag E sRoot 1) *
          n⁻¹) * diagramMap TwistTag.E6 E := by
      calc c * (b * diagramMap TwistTag.E6 E) * c⁻¹ =
            n * (z * (y * g'⁻¹ * (b * diagramMap TwistTag.E6 E) * (y * g'⁻¹)⁻¹) * z⁻¹) * n⁻¹ := by
            rw [hc]; group
        _ = n * ((z * pinnedX TwistTag.E6.tag E e6HighestRoot 1 * z⁻¹) *
              (z * (l * diagramMap TwistTag.E6 E) * z⁻¹)) * n⁻¹ := by rw [e2]; group
        _ = n * (pinnedX TwistTag.E6.tag E e6HighestRoot 1 * pinnedX TwistTag.E6.tag E sRoot 1) *
              n⁻¹ * (n * diagramMap TwistTag.E6 E * n⁻¹) := by
            rw [hzl, ← D.L_commute_X _ htX z hz, mul_inv_cancel_right]
            group
        _ = _ := by rw [hnP]
    have hl₂ := D.fusion_L
    rw [← hn] at hl₂
    have hsq₂ := hsq c
    rw [e3] at hsq₂
    rcases D.levi_form _ hl₂ hsq₂ with ⟨v, hv, hvl⟩ | ⟨v, hv, hvl⟩
    · refine Or.inl ⟨v * c, mul_mem (D.L_le hv) hcG, ?_⟩
      calc v * c * (b * diagramMap TwistTag.E6 E) * (v * c)⁻¹ =
            v * (c * (b * diagramMap TwistTag.E6 E) * c⁻¹) * v⁻¹ := by group
        _ = _ := by rw [e3, hvl]
    · set u := wordElt E upWord.reverse with hu
      have huP : u * diagramMap TwistTag.E6 E * u⁻¹ = diagramMap TwistTag.E6 E := by
        calc u * diagramMap TwistTag.E6 E * u⁻¹ =
              u * (diagramMap TwistTag.E6 E * u * (diagramMap TwistTag.E6 E)⁻¹)⁻¹ *
                diagramMap TwistTag.E6 E := by group
          _ = _ := by rw [D.up_P, mul_inv_cancel, one_mul]
      refine Or.inr ⟨u * (v * c), mul_mem D.up_mem (mul_mem (D.L_le hv) hcG), ?_⟩
      calc u * (v * c) * (b * diagramMap TwistTag.E6 E) * (u * (v * c))⁻¹ =
            u * (v * (c * (b * diagramMap TwistTag.E6 E) * c⁻¹) * v⁻¹) * u⁻¹ := by group
        _ = (u * pinnedX TwistTag.E6.tag E sRoot 1 * u⁻¹) *
              (u * diagramMap TwistTag.E6 E * u⁻¹) := by rw [e3, hvl]; group
        _ = _ := by rw [D.up_conj, huP]

theorem exhaust_levi
    (D : ExhaustionData ι G L Q U) [Finite E] [Finite F₀]
    {q l : ModGL TwistTag.E6.tag E} (hq : q ∈ Q) (hl : l ∈ L)
    (hsq : (q * l * diagramMap TwistTag.E6 E) ^ 2 = 1) :
    (∃ g ∈ G, g * (q * l * diagramMap TwistTag.E6 E) * g⁻¹ = diagramMap TwistTag.E6 E) ∨
      ∃ g ∈ G, g * (q * l * diagramMap TwistTag.E6 E) * g⁻¹ =
        pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E := by
  have hqG := D.Q_le hq
  have hlG := D.L_le hl
  have hjj : (q * l * diagramMap TwistTag.E6 E) * (q * l * diagramMap TwistTag.E6 E) = 1 := by
    rw [← sq]; exact hsq
  have hlP := levi_sq_eq_one D.Q_inf_L D.L_le_normalizer D.P_mul_self D.P_conj_Q D.P_conj_L hq hl
    hsq
  have hfinal : ∀ c ∈ G, ∀ g₁ ∈ G, ¬ IsPGroup 2 ↥((thetaRootGroup ι).map
      (MulAut.conj g₁).toMonoidHom ⊔ ((thetaRootGroup ι).map (MulAut.conj g₁).toMonoidHom).map
        (MulAut.conj (c * (q * l * diagramMap TwistTag.E6 E) * c⁻¹)).toMonoidHom) →
      (∃ g ∈ G, g * (q * l * diagramMap TwistTag.E6 E) * g⁻¹ = diagramMap TwistTag.E6 E) ∨
        ∃ g ∈ G, g * (q * l * diagramMap TwistTag.E6 E) * g⁻¹ =
          pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E := by
    intro c hc g₁ hg₁ hnot
    obtain ⟨b, hb, hcb⟩ := D.conj_mul_P hc (mul_mem hqG hlG)
    rw [hcb] at hnot
    have hbb : (b * diagramMap TwistTag.E6 E) * (b * diagramMap TwistTag.E6 E) = 1 := by
      rw [← hcb]
      calc c * (q * l * diagramMap TwistTag.E6 E) * c⁻¹ * (c * (q * l * diagramMap TwistTag.E6 E) *
            c⁻¹) = c * ((q * l * diagramMap TwistTag.E6 E) * (q * l * diagramMap TwistTag.E6 E)) *
            c⁻¹ := by group
        _ = 1 := by rw [hjj]; group
    have e : ∀ g : ModGL TwistTag.E6.tag E, g * c * (q * l * diagramMap TwistTag.E6 E) *
        (g * c)⁻¹ = g * (b * diagramMap TwistTag.E6 E) * g⁻¹ := fun g => by
      rw [← hcb]
      group
    rcases D.final_of_not_isPGroup hb hbb hg₁ hnot with ⟨g, hg, he⟩ | ⟨g, hg, he⟩
    · exact Or.inl ⟨g * c, mul_mem hg hc, by rw [e, he]⟩
    · exact Or.inr ⟨g * c, mul_mem hg hc, by rw [e, he]⟩
  rcases D.levi_form l hl hlP with ⟨x, hx, hxl⟩ | ⟨x, hx, hxl⟩
  ·
    have hxq : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (D.L_le_normalizer hx) q).1 hq
    have e : x * (q * l * diagramMap TwistTag.E6 E) * x⁻¹ =
        (x * q * x⁻¹) * diagramMap TwistTag.E6 E := by
      calc x * (q * l * diagramMap TwistTag.E6 E) * x⁻¹ =
            (x * q * x⁻¹) * (x * (l * diagramMap TwistTag.E6 E) * x⁻¹) := by group
        _ = _ := by rw [hxl]
    have hsq' : ((x * q * x⁻¹) * diagramMap TwistTag.E6 E) ^ 2 = 1 := by
      rw [← e, sq]
      calc x * (q * l * diagramMap TwistTag.E6 E) * x⁻¹ * (x * (q * l * diagramMap TwistTag.E6 E) *
            x⁻¹) = x * ((q * l * diagramMap TwistTag.E6 E) * (q * l * diagramMap TwistTag.E6 E)) *
            x⁻¹ := by group
        _ = 1 := by rw [hjj]; group
    have e' : ∀ g : ModGL TwistTag.E6.tag E, g * x * (q * l * diagramMap TwistTag.E6 E) *
        (g * x)⁻¹ = g * ((x * q * x⁻¹) * diagramMap TwistTag.E6 E) * g⁻¹ := fun g => by
      rw [← e]
      group
    rcases D.radical _ hxq hsq' with ⟨g, hg, he⟩ | ⟨g, hg, he⟩ | ⟨g₁, hg₁, hnot⟩
    · exact Or.inl ⟨g * x, mul_mem hg (D.L_le hx), by rw [e', he]⟩
    · exact Or.inr ⟨g * x, mul_mem hg (D.L_le hx), by rw [e', he]⟩
    · rw [← e] at hnot
      exact hfinal x (D.L_le hx) g₁ hg₁ hnot
  ·
    obtain ⟨g₁, hg₁, hR₁L, hnot⟩ := D.levi_detector l hl hlP ⟨x, hx, hxl⟩
    refine hfinal 1 (one_mem _) g₁ hg₁ fun hp => hnot ?_
    rw [one_mul, inv_one, mul_one, mul_assoc, map_conj_mul] at hp
    refine isPGroup_sup_of_isPGroup_sup_conj D.Q_inf_L D.L_le_normalizer hR₁L ?_ hq hp
    rintro _ ⟨r, hr, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hrL := hR₁L hr
    have h1 : diagramMap TwistTag.E6 E * r * (diagramMap TwistTag.E6 E)⁻¹ ∈ L :=
      D.P_conj_L r hrL
    have e : l * diagramMap TwistTag.E6 E * r * (l * diagramMap TwistTag.E6 E)⁻¹ =
        l * (diagramMap TwistTag.E6 E * r * (diagramMap TwistTag.E6 E)⁻¹) * l⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hl h1) (inv_mem hl)

theorem exhaust
    (D : ExhaustionData ι G L Q U) [Finite E] [Finite F₀]
    {a : ModGL TwistTag.E6.tag E} (ha : a ∈ G) (hsq : (a * diagramMap TwistTag.E6 E) ^ 2 = 1) :
    (∃ g ∈ G, g * (a * diagramMap TwistTag.E6 E) * g⁻¹ = diagramMap TwistTag.E6 E) ∨
      ∃ g ∈ G, g * (a * diagramMap TwistTag.E6 E) * g⁻¹ =
        pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E := by
  have : Finite (ModGL TwistTag.E6.tag E) := finite_modGL
  obtain ⟨g, hg, u, hu, hgu⟩ := exists_conj_eq_mul_of_sylow D.U_le D.U_sylow D.P_conj_G
    D.P_conj_U D.P_mul_self D.P_not_mem ha hsq
  obtain ⟨q, hq, l, hl, rfl⟩ := D.centralizer_factor u
    (Subgroup.mem_inf.2 ⟨D.U_le_centralizer hu, D.U_le hu⟩)
  have hsq' : (q * l * diagramMap TwistTag.E6 E) ^ 2 = 1 := by
    rw [← hgu, sq]
    calc g * (a * diagramMap TwistTag.E6 E) * g⁻¹ * (g * (a * diagramMap TwistTag.E6 E) * g⁻¹) =
          g * ((a * diagramMap TwistTag.E6 E) ^ 2) * g⁻¹ := by rw [sq]; group
      _ = 1 := by rw [hsq]; group
  have e : ∀ c : ModGL TwistTag.E6.tag E, c * g * (a * diagramMap TwistTag.E6 E) * (c * g)⁻¹ =
      c * (q * l * diagramMap TwistTag.E6 E) * c⁻¹ := fun c => by
    rw [← hgu]
    group
  rcases D.exhaust_levi hq hl hsq' with ⟨c, hc, he⟩ | ⟨c, hc, he⟩
  · exact Or.inl ⟨c * g, mul_mem hc hg, by rw [e, he]⟩
  · exact Or.inr ⟨c * g, mul_mem hc hg, by rw [e, he]⟩

end ExhaustionData

end CFSG.LieType.Chevalley.E6GraphInnerCoset
