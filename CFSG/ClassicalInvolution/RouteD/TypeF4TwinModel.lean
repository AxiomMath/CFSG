module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6TwinModel
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBModel

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

section HypFrame

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {m : ℕ} (H : HypFrame Q m)

theorem _root_.CFSG.LieType.Universal.Spin.HypFrame.longWeyl_conj_longRoot'
    {i j k l k' l' : Fin m} (hij : i ≠ j) (s t : Bool) (hkl : k ≠ l) (hk'l' : k' ≠ l')
    (hk : Equiv.swap i j k = k') (hl : Equiv.swap i j l = l') {u v u' v' : Bool}
    (hu : longWeylBool i j s t k u = u') (hv : longWeylBool i j s t l v = v') {c c' : K}
    (hc : (longWeylSign i k : K) * longWeylSign i l * c = c') :
    H.longWeyl hij s t * H.longRoot hkl u v (.ofAdd c) * (H.longWeyl hij s t)⁻¹ =
      H.longRoot hk'l' u' v' (.ofAdd c') := by
  subst hk hl hu hv hc
  exact H.longWeyl_conj_longRoot hij s t hkl u v c

@[expose] noncomputable def twinWeyl {b c : Fin m} (hbc : b ≠ c) : spinGroup Q :=
  H.longWeyl hbc true false * H.longWeyl hbc true true

theorem twinWeyl_conj_zero_upper {a b c : Fin m} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (x : K) :
    twinWeyl H hbc * H.longRoot hab true false (.ofAdd x) * (twinWeyl H hbc)⁻¹ =
      H.longRoot hab true true (.ofAdd (-x)) := by
  have e : twinWeyl H hbc * H.longRoot hab true false (.ofAdd x) * (twinWeyl H hbc)⁻¹ =
      H.longWeyl hbc true false * (H.longWeyl hbc true true * H.longRoot hab true false (.ofAdd x) *
        (H.longWeyl hbc true true)⁻¹) * (H.longWeyl hbc true false)⁻¹ := by
    simp only [twinWeyl]
    group
  have h1 : H.longWeyl hbc true true * H.longRoot hab true false (.ofAdd x) *
      (H.longWeyl hbc true true)⁻¹ = H.longRoot hac true true (.ofAdd (-x)) :=
    H.longWeyl_conj_longRoot' hbc true true hab hac (Equiv.swap_apply_of_ne_of_ne hab hac)
      (Equiv.swap_apply_left b c) (longWeylBool_of_ne true true hab hac true)
      (by simp [longWeylBool]) (by rw [longWeylSign_of_ne hab, longWeylSign_self]; ring)
  have h2 : H.longWeyl hbc true false * H.longRoot hac true true (.ofAdd (-x)) *
      (H.longWeyl hbc true false)⁻¹ = H.longRoot hab true true (.ofAdd (-x)) :=
    H.longWeyl_conj_longRoot' hbc true false hac hab (Equiv.swap_apply_of_ne_of_ne hab hac)
      (Equiv.swap_apply_right b c) (longWeylBool_of_ne true false hab hac true)
      (by simp [longWeylBool]) (by rw [longWeylSign_of_ne hab, longWeylSign_of_ne hbc.symm]; ring)
  rw [e, h1, h2]

theorem twinWeyl_conj_zero_lower {a b c : Fin m} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (x : K) :
    twinWeyl H hbc * H.longRoot hab.symm true false (.ofAdd x) * (twinWeyl H hbc)⁻¹ =
      H.longRoot hab.symm false false (.ofAdd (-x)) := by
  have e : twinWeyl H hbc * H.longRoot hab.symm true false (.ofAdd x) * (twinWeyl H hbc)⁻¹ =
      H.longWeyl hbc true false * (H.longWeyl hbc true true *
        H.longRoot hab.symm true false (.ofAdd x) * (H.longWeyl hbc true true)⁻¹) *
          (H.longWeyl hbc true false)⁻¹ := by
    simp only [twinWeyl]
    group
  have h1 : H.longWeyl hbc true true * H.longRoot hab.symm true false (.ofAdd x) *
      (H.longWeyl hbc true true)⁻¹ = H.longRoot hac.symm false false (.ofAdd (-x)) :=
    H.longWeyl_conj_longRoot' hbc true true hab.symm hac.symm (Equiv.swap_apply_left b c)
      (Equiv.swap_apply_of_ne_of_ne hab hac) (by simp [longWeylBool])
      (longWeylBool_of_ne true true hab hac false)
      (by rw [longWeylSign_self, longWeylSign_of_ne hab]; ring)
  have h2 : H.longWeyl hbc true false * H.longRoot hac.symm false false (.ofAdd (-x)) *
      (H.longWeyl hbc true false)⁻¹ = H.longRoot hab.symm false false (.ofAdd (-x)) :=
    H.longWeyl_conj_longRoot' hbc true false hac.symm hab.symm (Equiv.swap_apply_right b c)
      (Equiv.swap_apply_of_ne_of_ne hab hac) (by simp [longWeylBool])
      (longWeylBool_of_ne true false hab hac false)
      (by rw [longWeylSign_of_ne hbc.symm, longWeylSign_of_ne hab]; ring)
  rw [e, h1, h2]

theorem twinWeyl_conj_one_upper {b c : Fin m} (hbc : b ≠ c) (x : K) :
    twinWeyl H hbc * H.longRoot hbc true false (.ofAdd x) * (twinWeyl H hbc)⁻¹ =
      H.longRoot hbc.symm true false (.ofAdd (-x)) := by
  have e : twinWeyl H hbc * H.longRoot hbc true false (.ofAdd x) * (twinWeyl H hbc)⁻¹ =
      H.longWeyl hbc true false * (H.longWeyl hbc true true * H.longRoot hbc true false (.ofAdd x) *
        (H.longWeyl hbc true true)⁻¹) * (H.longWeyl hbc true false)⁻¹ := by
    simp only [twinWeyl]
    group
  have h1 : H.longWeyl hbc true true * H.longRoot hbc true false (.ofAdd x) *
      (H.longWeyl hbc true true)⁻¹ = H.longRoot hbc.symm false true (.ofAdd (-x)) :=
    H.longWeyl_conj_longRoot' hbc true true hbc hbc.symm (Equiv.swap_apply_left b c)
      (Equiv.swap_apply_right b c) (by simp [longWeylBool]) (by simp [longWeylBool])
      (by rw [longWeylSign_self, longWeylSign_of_ne hbc.symm]; ring)
  have h2 : H.longWeyl hbc true false * H.longRoot hbc.symm false true (.ofAdd (-x)) *
      (H.longWeyl hbc true false)⁻¹ = H.longRoot hbc false true (.ofAdd x) :=
    H.longWeyl_conj_longRoot' hbc true false hbc.symm hbc (Equiv.swap_apply_right b c)
      (Equiv.swap_apply_left b c) (by simp [longWeylBool]) (by simp [longWeylBool])
      (by rw [longWeylSign_of_ne hbc.symm, longWeylSign_self]; ring)
  rw [e, h1, h2, H.longRoot_swap hbc false true x]

theorem twinWeyl_conj_one_lower {b c : Fin m} (hbc : b ≠ c) (x : K) :
    twinWeyl H hbc * H.longRoot hbc.symm true false (.ofAdd x) * (twinWeyl H hbc)⁻¹ =
      H.longRoot hbc true false (.ofAdd (-x)) := by
  have e : twinWeyl H hbc * H.longRoot hbc.symm true false (.ofAdd x) * (twinWeyl H hbc)⁻¹ =
      H.longWeyl hbc true false * (H.longWeyl hbc true true *
        H.longRoot hbc.symm true false (.ofAdd x) * (H.longWeyl hbc true true)⁻¹) *
          (H.longWeyl hbc true false)⁻¹ := by
    simp only [twinWeyl]
    group
  have h1 : H.longWeyl hbc true true * H.longRoot hbc.symm true false (.ofAdd x) *
      (H.longWeyl hbc true true)⁻¹ = H.longRoot hbc false true (.ofAdd (-x)) :=
    H.longWeyl_conj_longRoot' hbc true true hbc.symm hbc (Equiv.swap_apply_right b c)
      (Equiv.swap_apply_left b c) (by simp [longWeylBool]) (by simp [longWeylBool])
      (by rw [longWeylSign_of_ne hbc.symm, longWeylSign_self]; ring)
  have h2 : H.longWeyl hbc true false * H.longRoot hbc false true (.ofAdd (-x)) *
      (H.longWeyl hbc true false)⁻¹ = H.longRoot hbc.symm false true (.ofAdd x) :=
    H.longWeyl_conj_longRoot' hbc true false hbc hbc.symm (Equiv.swap_apply_left b c)
      (Equiv.swap_apply_right b c) (by simp [longWeylBool]) (by simp [longWeylBool])
      (by rw [longWeylSign_self, longWeylSign_of_ne hbc.symm]; ring)
  rw [e, h1, h2, H.longRoot_swap hbc.symm false true x]

end HypFrame

section Odd

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem finite_spinGroup_quadOdd (n : ℕ) : Finite (spinGroup (quadOdd n F)) := by
  have : FiniteDimensional F (CliffordAlgebra (quadOdd n F)) :=
    finiteDimensional_cliffordAlgebra' _
  have : Finite (CliffordAlgebra (quadOdd n F)) := Module.finite_of_finite F
  infer_instance

omit [Finite F] in
@[expose] def oddTwIdx0 (hn : 3 ≤ n) : Fin n := ⟨0, by omega⟩

@[expose] def oddTwIdx1 (hn : 3 ≤ n) : Fin n := ⟨1, by omega⟩

@[expose] def oddTwIdx2 (hn : 3 ≤ n) : Fin n := ⟨2, by omega⟩

theorem oddTwIdx0_ne_oddTwIdx1 (hn : 3 ≤ n) : oddTwIdx0 hn ≠ oddTwIdx1 hn := fun h => by
  have := congrArg Fin.val h
  simp [oddTwIdx0, oddTwIdx1] at this

theorem oddTwIdx1_ne_oddTwIdx2 (hn : 3 ≤ n) : oddTwIdx1 hn ≠ oddTwIdx2 hn := fun h => by
  have := congrArg Fin.val h
  simp [oddTwIdx1, oddTwIdx2] at this

theorem oddTwIdx0_ne_oddTwIdx2 (hn : 3 ≤ n) : oddTwIdx0 hn ≠ oddTwIdx2 hn := fun h => by
  have := congrArg Fin.val h
  simp [oddTwIdx0, oddTwIdx2] at this

omit [Finite F] in
theorem oddTw_rankOne_eq_range {k j : Fin n} (hk : k.val + 1 < n) (hj : j.val = k.val + 1)
    (hkj : k ≠ j) :
    rankOne (oddDatum n F).rootGroup k =
      ((oddFrame n F).toHypFrame.longSL2 hkj true false).range := by
  have hR : rankOne (oddRootGroup n F) k = (rankOneB F k).range :=
    le_antisymm (OddCT.rankOne_le_range k) (by
      rintro _ ⟨M, rfl⟩
      exact OddCT.rankOneB_mem_rankOne k M)
  rw [rankOneB_of_lt F hk hj hkj] at hR
  exact hR

noncomputable abbrev oddTwFrame (hn : 3 ≤ n) : Frame (quadOdd n F) :=
  (oddFrame n F).toHypFrame.toFrame (oddTwIdx0_ne_oddTwIdx1 hn) true false

omit [Finite F] in
theorem oddTw_toFrame_true_true_eq_swap (hn : 3 ≤ n) :
    (oddFrame n F).toHypFrame.toFrame (oddTwIdx0_ne_oddTwIdx1 hn) true true =
      (oddTwFrame (F := F) hn).swap := rfl

noncomputable abbrev oddTwR0 (hn : 3 ≤ n) : Subgroup (spinGroup (quadOdd n F)) :=
  rankOne (oddDatum n F).rootGroup (oddTwIdx0 hn : Fin n)

noncomputable abbrev oddTwR1 (hn : 3 ≤ n) : Subgroup (spinGroup (quadOdd n F)) :=
  rankOne (oddDatum n F).rootGroup (oddTwIdx1 hn : Fin n)

noncomputable abbrev oddTwG (hn : 3 ≤ n) : spinGroup (quadOdd n F) :=
  twinWeyl (oddFrame n F).toHypFrame (oddTwIdx1_ne_oddTwIdx2 hn)

noncomputable abbrev oddTwR0' (hn : 3 ≤ n) : Subgroup (spinGroup (quadOdd n F)) :=
  conjSub (oddTwG hn) (oddTwR0 hn)

noncomputable abbrev oddTwInv (hn : 3 ≤ n) : (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F]
    (Fin n ⊕ Fin n ⊕ Unit → F) :=
  (oddTwFrame (F := F) hn).La (-1)

omit [Finite F] in
theorem oddTw_map_rankOne_zero (hn : 3 ≤ n) :
    (oddTwR0 (F := F) hn).map (spinAction (quadOdd n F)) = (oddTwFrame (F := F) hn).La.range := by
  rw [oddTwR0, oddTw_rankOne_eq_range (by simp only [oddTwIdx0]; omega) rfl
    (oddTwIdx0_ne_oddTwIdx1 hn), ← MonoidHom.range_comp,
    CFSG.ClassicalInvolution.ModelFacts.spinAction_comp_longSL2]

omit [Finite F] in
theorem oddTw_spinAction_longSL2_tt_mem (hn : 3 ≤ n) (A : SL(2, F)) :
    spinAction (quadOdd n F)
      ((oddFrame n F).toHypFrame.longSL2 (oddTwIdx0_ne_oddTwIdx1 hn) true true A) ∈
        (oddTwFrame (F := F) hn).swap.La.range := by
  have h := DFunLike.congr_fun (CFSG.ClassicalInvolution.ModelFacts.spinAction_comp_longSL2
    (oddFrame n F).toHypFrame (oddTwIdx0_ne_oddTwIdx1 hn) true true) A
  rw [MonoidHom.comp_apply] at h
  rw [h, oddTw_toFrame_true_true_eq_swap]
  exact ⟨A, rfl⟩

omit [Finite F] in
theorem oddTw_map_conj_le (hn : 3 ≤ n) :
    (oddTwR0' (F := F) hn).map (spinAction (quadOdd n F)) ≤
      (oddTwFrame (F := F) hn).swap.La.range := by
  rw [oddTwR0', oddTwR0, oddTw_rankOne_eq_range (by simp only [oddTwIdx0]; omega) rfl
    (oddTwIdx0_ne_oddTwIdx1 hn)]
  rintro _ ⟨x, ⟨y, ⟨A, rfl⟩, rfl⟩, rfl⟩
  have hφ := Frame.sl2_apply_mem
    ((spinAction (quadOdd n F)).comp ((MulAut.conj (oddTwG hn)).toMonoidHom.comp
      ((oddFrame n F).toHypFrame.longSL2 (oddTwIdx0_ne_oddTwIdx1 hn) true false)))
    (oddTwFrame (F := F) hn).swap.La.range ?_ ?_ A
  · exact hφ
  · intro c'
    rw [← CFSG.ClassicalInvolution.ModelFacts.coe_upperSL2_eq_transvection]
    show spinAction (quadOdd n F) (oddTwG hn *
      (oddFrame n F).toHypFrame.longSL2 (oddTwIdx0_ne_oddTwIdx1 hn) true false (upperSL2 c') *
        (oddTwG hn)⁻¹) ∈ _
    rw [HypFrame.longSL2_upperSL2, oddTwG, twinWeyl_conj_zero_upper _
      (oddTwIdx0_ne_oddTwIdx1 hn) (oddTwIdx1_ne_oddTwIdx2 hn) (oddTwIdx0_ne_oddTwIdx2 hn) c',
      ← HypFrame.longSL2_upperSL2 (oddFrame n F).toHypFrame (oddTwIdx0_ne_oddTwIdx1 hn) true true
        (-c')]
    exact oddTw_spinAction_longSL2_tt_mem hn _
  · intro c'
    rw [← CFSG.ClassicalInvolution.ModelFacts.coe_lowerSL2_eq_transvection]
    show spinAction (quadOdd n F) (oddTwG hn *
      (oddFrame n F).toHypFrame.longSL2 (oddTwIdx0_ne_oddTwIdx1 hn) true false (lowerSL2 c') *
        (oddTwG hn)⁻¹) ∈ _
    rw [HypFrame.longSL2_lowerSL2, oddTwG]
    simp only [Bool.not_false, Bool.not_true]
    rw [twinWeyl_conj_zero_lower _ (oddTwIdx0_ne_oddTwIdx1 hn) (oddTwIdx1_ne_oddTwIdx2 hn)
      (oddTwIdx0_ne_oddTwIdx2 hn) c']
    have := oddTw_spinAction_longSL2_tt_mem (F := F) hn (lowerSL2 (-c'))
    rw [HypFrame.longSL2_lowerSL2] at this
    simpa only [Bool.not_true] using this

omit [Finite F] in
theorem oddTw_conj_R1_le (hn : 3 ≤ n) :
    conjSub (oddTwG hn) (oddTwR1 (F := F) hn) ≤ oddTwR1 hn := by
  have hR1 : oddTwR1 (F := F) hn =
      ((oddFrame n F).toHypFrame.longSL2 (oddTwIdx1_ne_oddTwIdx2 hn) true false).range :=
    oddTw_rankOne_eq_range (by simp only [oddTwIdx1]; omega) rfl (oddTwIdx1_ne_oddTwIdx2 hn)
  rw [hR1]
  rintro _ ⟨y, ⟨A, rfl⟩, rfl⟩
  have hφ := Frame.sl2_apply_mem
    ((MulAut.conj (oddTwG hn)).toMonoidHom.comp
      ((oddFrame n F).toHypFrame.longSL2 (oddTwIdx1_ne_oddTwIdx2 hn) true false))
    ((oddFrame n F).toHypFrame.longSL2 (oddTwIdx1_ne_oddTwIdx2 hn) true false).range ?_ ?_ A
  · exact hφ
  · intro c'
    rw [← CFSG.ClassicalInvolution.ModelFacts.coe_upperSL2_eq_transvection]
    show oddTwG hn *
      (oddFrame n F).toHypFrame.longSL2 (oddTwIdx1_ne_oddTwIdx2 hn) true false (upperSL2 c') *
        (oddTwG hn)⁻¹ ∈ _
    rw [HypFrame.longSL2_upperSL2, oddTwG, twinWeyl_conj_one_upper _ (oddTwIdx1_ne_oddTwIdx2 hn) c']
    refine ⟨lowerSL2 (-c'), ?_⟩
    rw [HypFrame.longSL2_lowerSL2]
    simp only [Bool.not_false, Bool.not_true]
  · intro c'
    rw [← CFSG.ClassicalInvolution.ModelFacts.coe_lowerSL2_eq_transvection]
    show oddTwG hn *
      (oddFrame n F).toHypFrame.longSL2 (oddTwIdx1_ne_oddTwIdx2 hn) true false (lowerSL2 c') *
        (oddTwG hn)⁻¹ ∈ _
    rw [HypFrame.longSL2_lowerSL2, oddTwG]
    simp only [Bool.not_false, Bool.not_true]
    rw [twinWeyl_conj_one_lower _ (oddTwIdx1_ne_oddTwIdx2 hn) c']
    refine ⟨upperSL2 (-c'), ?_⟩
    rw [HypFrame.longSL2_upperSL2]

theorem oddTw_conj_R1_eq (hn : 3 ≤ n) :
    conjSub (oddTwG hn) (oddTwR1 (F := F) hn) = oddTwR1 hn := by
  have hfin : Finite (spinGroup (quadOdd n F)) := finite_spinGroup_quadOdd n
  refine Subgroup.eq_of_le_of_card_ge (oddTw_conj_R1_le hn) ?_
  rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem exists_standardPair_oddTw_R0_R1 (hn : 3 ≤ n) :
    ∃ W, LinearBlockStandardPair F W (oddTwR0 (F := F) hn) (oddTwR1 hn) :=
  (CFSG.ClassicalInvolution.ModelFacts.standardPair_oddDatum hn).2

theorem exists_standardPair_oddTw_R1_twin (hn : 3 ≤ n) :
    ∃ W, LinearBlockStandardPair F W (oddTwR1 (F := F) hn) (oddTwR0' hn) := by
  obtain ⟨W, hW⟩ := exists_standardPair_oddTw_R0_R1 (F := F) hn
  have h := CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW (oddTwG hn)
  have e1 := oddTw_conj_R1_eq (F := F) hn
  rw [conjSub] at e1
  have e0 : (oddTwR0 (F := F) hn).map (MulAut.conj (oddTwG hn)).toMonoidHom = oddTwR0' hn := rfl
  rw [e0, e1] at h
  exact ⟨_, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm h⟩

omit [Finite F] in
theorem isFundamental_oddTwR0 (hn : 3 ≤ n) :
    IsFundamental (quadOdd n F) ((oddTwR0 (F := F) hn).map (spinAction (quadOdd n F)))
      (oddTwInv hn) := by
  rw [oddTw_map_rankOne_zero hn]
  exact IsFundamental.of_frame _

omit [Finite F] in
theorem isFundamental_map_conj_odd {R₀ : Subgroup (spinGroup (quadOdd n F))}
    {i₀ : (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F] (Fin n ⊕ Fin n ⊕ Unit → F)}
    (h : IsFundamental (quadOdd n F) (R₀.map (spinAction (quadOdd n F))) i₀)
    (g : spinGroup (quadOdd n F)) :
    IsFundamental (quadOdd n F) ((conjSub g R₀).map (spinAction (quadOdd n F)))
      (spinAction (quadOdd n F) g * i₀ * (spinAction (quadOdd n F) g)⁻¹) := by
  rw [← conjSub_map]
  have hg : ((spinToOrthogonalGroup (quadOdd n F) g :
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd n F)) :
        (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F] (Fin n ⊕ Fin n ⊕ Unit → F)) =
        spinAction (quadOdd n F) g :=
    LinearEquiv.ext (coe_spinToOrthogonalGroup_apply _ g)
  have := IsFundamental.conj (spinToOrthogonalGroup (quadOdd n F) g).2 h
  rw [hg] at this
  exact this

theorem isFundamental_oddTwR0' (hodd : Odd (Nat.card F)) (hn : 3 ≤ n) :
    IsFundamental (quadOdd n F) ((oddTwR0' (F := F) hn).map (spinAction (quadOdd n F)))
      (oddTwInv hn) := by
  have h := isFundamental_map_conj_odd (isFundamental_oddTwR0 (F := F) hn) (oddTwG hn)
  have hle := oddTw_map_conj_le (F := F) hn
  have hL' : IsFundamental (quadOdd n F) (oddTwFrame (F := F) hn).swap.La.range (oddTwInv hn) :=
    IsFundamental.of_frame_swap _
  have h1 := hL'.eq_of_orderOf_eq_two hodd (hle h.mem) (h.orderOf_eq_two hodd)
  rw [h1] at h
  exact h

theorem oddTwR0'_ne (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) (hn : 3 ≤ n) :
    oddTwR0' (F := F) hn ≠ oddTwR0 hn := by
  intro h
  have hle : (oddTwR0' (F := F) hn).map (spinAction (quadOdd n F)) ≤
      (oddTwFrame (F := F) hn).swap.La.range := oddTw_map_conj_le hn
  rw [h, oddTw_map_rankOne_zero] at hle
  have hL₀ := isFundamental_oddTwR0 (F := F) hn
  rw [oddTw_map_rankOne_zero] at hL₀
  have hab : ∀ x ∈ (oddTwFrame (F := F) hn).La.range,
      ∀ y ∈ (oddTwFrame (F := F) hn).La.range, x * y = y * x := by
    rintro _ ⟨A, rfl⟩ y hy
    obtain ⟨B, hB⟩ := hle hy
    rw [← hB]
    exact Frame.La_comm_La_swap _ A B
  have hcomm := hL₀.commutator_eq h4
  have hbot : ⁅(oddTwFrame (F := F) hn).La.range, (oddTwFrame (F := F) hn).La.range⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx y hy
    exact (hab y hy x hx)
  rw [hbot] at hcomm
  have hi : oddTwInv (F := F) hn ∈ (oddTwFrame (F := F) hn).La.range := hL₀.mem
  rw [← hcomm] at hi
  exact hL₀.ne_one hodd ((Subgroup.mem_bot).mp hi)

theorem same_involution_of_twin_odd (hodd : Odd (Nat.card F)) (hn : 4 ≤ n)
    {R R' : Subgroup (spinGroup (quadOdd n F))}
    {i i' : (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F] (Fin n ⊕ Fin n ⊕ Unit → F)}
    (hR : IsFundamental (quadOdd n F) (R.map (spinAction (quadOdd n F))) i)
    (hR' : IsFundamental (quadOdd n F) (R'.map (spinAction (quadOdd n F))) i')
    (hcomm : ∀ a ∈ R, ∀ a' ∈ R', a * a' = a' * a)
    (hncR : ∀ x ∈ R,
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) → x = 1)
    (hncR' : ∀ x ∈ R',
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) → x = 1)
    {r r' : spinGroup (quadOdd n F)} (hr : r ∈ R) (hr1 : r ≠ 1) (hr' : r' ∈ R')
    (hr'1 : r' ≠ 1)
    (hcen : ∀ y, r * r' * y * (r * r')⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) :
    i = i' := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hn3 : 3 ≤ n := by omega
  have hdim : 8 < Module.finrank F (Fin n ⊕ Fin n ⊕ Unit → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    omega
  obtain ⟨hcR, hcR'⟩ := central_of_twin hcomm hncR hncR' hr hr' hcen
  have hθr : spinAction (quadOdd n F) r = i := spinAction_eq_of_central rfl hR hncR hr hr1 hcR
  have hθr' : spinAction (quadOdd n F) r' = i' :=
    spinAction_eq_of_central rfl hR' hncR' hr' hr'1 hcR'
  have hperfK : Group.IsPerfect (spinGroup (quadOdd n F)) := isPerfect_spinGroup_quadOdd h2 hn3
  have hc : r * r' ∈ Subgroup.center (spinGroup (quadOdd n F)) :=
    CFSG.ClassicalInvolution.RouteD.mem_center_of_comm_mem_center (fun s => hcen s)
  have hrange := range_spinAction_quadOdd h2 hn3
  have hmem : spinAction (quadOdd n F) (r * r') ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadOdd n F) :=
    hrange ▸ ⟨_, rfl⟩
  let z : ↥(CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadOdd n F)) := ⟨_, hmem⟩
  have hzc : z ∈ Subgroup.center
      ↥(CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadOdd n F)) := by
    rw [Subgroup.mem_center_iff]
    intro u
    have hu : (u : (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F] (Fin n ⊕ Fin n ⊕ Unit → F)) ∈
        (spinAction (quadOdd n F)).range := by
      rw [hrange]
      exact u.2
    obtain ⟨y, hy⟩ := hu
    apply Subtype.ext
    show (u : (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F] (Fin n ⊕ Fin n ⊕ Unit → F)) *
      spinAction (quadOdd n F) (r * r') =
        spinAction (quadOdd n F) (r * r') *
          (u : (Fin n ⊕ Fin n ⊕ Unit → F) ≃ₗ[F] (Fin n ⊕ Fin n ⊕ Unit → F))
    rw [← hy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc y)]
  have hcommi : i * i' = i' * i := by
    rw [← hθr, ← hθr', ← map_mul, ← map_mul, hcomm r hr r' hr']
  have hz2 : z * z = 1 := by
    apply Subtype.ext
    show (spinAction (quadOdd n F) (r * r')) * spinAction (quadOdd n F) (r * r') = 1
    rw [map_mul, hθr, hθr']
    calc i * i' * (i * i') = i * (i' * i) * i' := by group
      _ = i * (i * i') * i' := by rw [hcommi]
      _ = (i * i) * (i' * i') := by group
      _ = 1 := by rw [hR.mul_self, hR'.mul_self, mul_one]
  have : Nontrivial (Fin n ⊕ Fin n ⊕ Unit → F) :=
    Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hZ := CFSG.ClassicalInvolution.Models.Transfer.centerScalar_quadOdd h2 hn3
  rcases CFSG.ClassicalInvolution.Models.Transfer.eq_one_or_eq_neg_of_mem_center hZ hzc hz2 with
    h | h
  · exact eq_of_mul_eq_one_or_neg h2 hdim hR hR'
      (Or.inl (by rw [← hθr, ← hθr', ← map_mul]; exact congrArg Subtype.val h))
  · exact eq_of_mul_eq_one_or_neg h2 hdim hR hR'
      (Or.inr (by rw [← hθr, ← hθr', ← map_mul]; exact h))

theorem eq_oddTwR0'_of_twin (hn : 4 ≤ n) (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (hsc : FundamentalSingleClass .POmegaOdd (oddDatum n F))
    (hperf : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F), R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F), ∀ x ∈ R,
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) → x = 1)
    {R' : Subgroup (spinGroup (quadOdd n F))}
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F))
    (hne : R' ≠ oddTwR0 (F := F) (by omega : 3 ≤ n))
    (hcomm : Commutes (oddTwR0 (F := F) (by omega : 3 ≤ n)) R')
    {r r' : spinGroup (quadOdd n F)} (hr : r ∈ oddTwR0 (F := F) (by omega : 3 ≤ n))
    (hr1 : r ≠ 1) (hr' : r' ∈ R') (hr'1 : r' ≠ 1)
    (hcen : ∀ y, r * r' * y * (r * r')⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) :
    R' = oddTwR0' (F := F) (by omega : 3 ≤ n) := by
  have hn3 : 3 ≤ n := by omega
  have hR₀mem : oddTwR0 (F := F) hn3 ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    rankOne_mem_fundamentalSubgroups_oddDatum hn3 (i := oddTwIdx0 hn3)
      (by simp only [oddTwIdx0]; omega)
  have hR₀'mem : oddTwR0' (F := F) hn3 ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    conjSub_mem_fundamentalSubgroups hR₀mem _
  obtain ⟨g, hg⟩ := hsc _ hR₀mem R' hR'
  have hF' := isFundamental_map_conj_odd (isFundamental_oddTwR0 (F := F) hn3) g
  rw [← hg] at hF'
  have hinv := same_involution_of_twin_odd hodd hn (isFundamental_oddTwR0 (F := F) hn3) hF' hcomm
    (hnc _ hR₀mem) (hnc _ hR') hr hr1 hr' hr'1 hcen
  rw [← hinv] at hF'
  obtain ⟨L'', hL'', hneL, -, huniq⟩ :=
    IsFundamental.exists_twin hodd (isFundamental_oddTwR0 (F := F) hn3)
  have h1 := huniq _ hF'
  have h2 := huniq _ (isFundamental_oddTwR0' (F := F) hodd hn3)
  have hθ : ∀ X ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F),
      X.map (spinAction (quadOdd n F)) = (oddTwR0 (F := F) hn3).map (spinAction (quadOdd n F)) →
        X = oddTwR0 hn3 :=
    fun X hX h => Gaps.eq_of_map_eq_of_central _ (ker_spinAction_le_center _) (hperf X hX)
      (hperf _ hR₀mem) h
  rcases h1 with h1 | h1
  · exact absurd (hθ R' hR' h1) hne
  rcases h2 with h2 | h2
  · exact absurd (hθ _ hR₀'mem h2) (oddTwR0'_ne hodd h4 hn3)
  exact Gaps.eq_of_map_eq_of_central _ (ker_spinAction_le_center _) (hperf R' hR')
    (hperf _ hR₀'mem) (h1.trans h2.symm)

theorem twin_partner_spin_odd (hn : 4 ≤ n) (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (hsc : FundamentalSingleClass .POmegaOdd (oddDatum n F))
    (hperf : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F), R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F), ∀ x ∈ R,
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) → x = 1)
    {R R' : Subgroup (spinGroup (quadOdd n F))}
    (hR : R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F))
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F)) (hne : R ≠ R')
    (hcomm : Commutes R R')
    (hant : ∃ r ∈ R, r ≠ 1 ∧ ∃ r' ∈ R', r' ≠ 1 ∧ ∀ y,
      r * r' * y * (r * r')⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F))) :
    ∃ R'' ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F),
      (∃ W, LinearBlockStandardPair F W R R'') ∧ ∃ W, LinearBlockStandardPair F W R'' R' := by
  have hn3 : 3 ≤ n := by omega
  have hR₀mem : oddTwR0 (F := F) hn3 ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    rankOne_mem_fundamentalSubgroups_oddDatum hn3 (i := oddTwIdx0 hn3)
      (by simp only [oddTwIdx0]; omega)
  have hR₁mem : oddTwR1 (F := F) hn3 ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    rankOne_mem_fundamentalSubgroups_oddDatum hn3 (i := oddTwIdx1 hn3)
      (by simp only [oddTwIdx1]; omega)
  obtain ⟨g, hg⟩ := hsc _ hR₀mem R hR
  obtain ⟨r, hr, hr1, r', hr', hr'1, hcen⟩ := hant
  have hR₁' : conjSub g⁻¹ R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum n F) :=
    conjSub_mem_fundamentalSubgroups hR' g⁻¹
  have hRg : conjSub g⁻¹ R = oddTwR0 (F := F) hn3 := by
    rw [hg, conjSub_inv_conjSub]
  have hne₁ : conjSub g⁻¹ R' ≠ oddTwR0 (F := F) hn3 := by
    intro h
    apply hne
    rw [← hRg] at h
    have := congrArg (conjSub g) h
    rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
    exact this.symm
  have hcomm₁ : Commutes (oddTwR0 (F := F) hn3) (conjSub g⁻¹ R') := by
    rw [← hRg]
    exact (commutes_conjSub_iff g⁻¹).mpr hcomm
  have hr₁ : g⁻¹ * r * g ∈ oddTwR0 (F := F) hn3 := by
    rw [← hRg]
    exact mem_conjSub_iff.mpr (by simpa [mul_assoc] using hr)
  have hr₁' : g⁻¹ * r' * g ∈ conjSub g⁻¹ R' := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hr'
  have hcen₁ : ∀ y, (g⁻¹ * r * g) * (g⁻¹ * r' * g) * y * ((g⁻¹ * r * g) * (g⁻¹ * r' * g))⁻¹ *
      y⁻¹ ∈ Subgroup.center (spinGroup (quadOdd n F)) := by
    intro y
    have h := hcen (g * y * g⁻¹)
    set w := r * r' * (g * y * g⁻¹) * (r * r')⁻¹ * (g * y * g⁻¹)⁻¹ with hw
    have hc : g⁻¹ * w = w * g⁻¹ := Subgroup.mem_center_iff.mp h g⁻¹
    have e : (g⁻¹ * r * g) * (g⁻¹ * r' * g) * y * ((g⁻¹ * r * g) * (g⁻¹ * r' * g))⁻¹ * y⁻¹ =
        g⁻¹ * w * g := by
      rw [hw]
      group
    rw [e, hc, mul_assoc, inv_mul_cancel, mul_one]
    exact h
  have hone : ∀ x : spinGroup (quadOdd n F), x ≠ 1 → g⁻¹ * x * g ≠ 1 := by
    intro x hx h
    apply hx
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]
    group
  have key := eq_oddTwR0'_of_twin hn hodd h4 hsc hperf hnc hR₁' hne₁ hcomm₁ hr₁
    (hone r hr1) hr₁' (hone r' hr'1) hcen₁
  have hR'eq : R' = conjSub g (oddTwR0' (F := F) hn3) := by
    rw [← key, conjSub_conjSub_inv]
  refine ⟨conjSub g (oddTwR1 (F := F) hn3), conjSub_mem_fundamentalSubgroups hR₁mem g, ?_, ?_⟩
  · obtain ⟨W, hW⟩ := exists_standardPair_oddTw_R0_R1 (F := F) hn3
    rw [hg]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW g⟩
  · obtain ⟨W, hW⟩ := exists_standardPair_oddTw_R1_twin (F := F) hn3
    rw [hR'eq]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW g⟩

end Odd

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem twinPartnerFactTwin_pOmegaOdd_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    TwinPartnerFactTwin p f .POmegaOdd 4 f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaOdd 4 p f :=
    ⟨Fact.out, hf, by norm_num, hp2⟩
  obtain ⟨hodd, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  intro R hR R' hR' hne hcomm hant
  have hsc := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd 4 p f
    Fact.out trivial hadm (by decide) (by decide)
  have hperf := CFSG.ClassicalInvolution.RouteD.Gaps.fundPerfect_modelUniv hp2
    (t := .POmegaOdd) (n := 4) (e := f) trivial hadm (by omega)
  have hnc := CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p .POmegaOdd 4 f trivial hadm
    (by decide)
  exact twin_partner_spin_odd (by norm_num) hodd h4 hsc hperf hnc hR hR' hne hcomm hant

end Main

end CFSG.ClassicalInvolution.RouteD.NonClassical
