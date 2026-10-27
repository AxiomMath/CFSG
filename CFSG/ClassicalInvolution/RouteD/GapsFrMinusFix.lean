module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusEigen
public import CFSG.ClassicalInvolution.RouteD.TypeF4Lift
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDModel

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.CurtisTits (rankOne)
open scoped MatrixGroups commutatorElement

section Group

variable {Kc X : Type} [Group Kc] [Group X]

private theorem eq_of_central_perfect (α : Kc ≃* Kc) {R : Subgroup Kc} (hR : ⁅R, R⁆ = R)
    (hc : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center Kc) : ∀ r ∈ R, α r = r := by
  have hle : ⁅R, R⁆ ≤ MonoidHom.eqLocus (α : Kc →* Kc) (MonoidHom.id Kc) := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    show α ⁅x, y⁆ = ⁅x, y⁆
    rw [map_commutatorElement]
    have e1 : α x = x * (x⁻¹ * α x) := by group
    have e2 : α y = y * (y⁻¹ * α y) := by group
    rw [e1, e2, CFSG.ClassicalInvolution.ModelFacts.commutatorElement_mul_central (hc x hx)
      (hc y hy)]
  intro r hr
  have hr' : r ∈ ⁅R, R⁆ := by rw [hR]; exact hr
  exact hle hr'

theorem alpha_mem_of_perfect (α : Kc ≃* Kc) {R : Subgroup Kc} (hR : ⁅R, R⁆ = R)
    (h : ∀ r ∈ R, ∃ r' ∈ R, ∃ c ∈ Subgroup.center Kc, α r = r' * c) : ∀ r ∈ R, α r ∈ R := by
  intro r hr
  have hr' : r ∈ ⁅R, R⁆ := by rw [hR]; exact hr
  clear hr
  rw [Subgroup.commutator_def] at hr'
  induction hr' using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    obtain ⟨y₁, hy₁, c₁, hc₁, e₁⟩ := h a ha
    obtain ⟨y₂, hy₂, c₂, hc₂, e₂⟩ := h b hb
    rw [map_commutatorElement, e₁, e₂,
      CFSG.ClassicalInvolution.RouteD.Gaps.commutator_mul_central _ _ _ _ hc₁ hc₂]
    simp only [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hy₁ hy₂) (R.inv_mem hy₁)) (R.inv_mem hy₂)
  | one => simp
  | mul a b _ _ ha hb =>
    rw [map_mul]
    exact R.mul_mem ha hb
  | inv a _ ha =>
    rw [map_inv]
    exact R.inv_mem ha

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem commute_of_fixed (θ : Kc →* X) (hker : θ.ker ≤ Subgroup.center Kc) (α : Kc ≃* Kc)
    (σ : X ≃* X) (hαθ : ∀ y, θ (α y) = σ (θ y)) (ρ : Kc →* (V ≃ₗ[K] V)) {g : V ≃ₗ[K] V}
    (hconj : ∀ y, ρ (α y) * g = g * ρ y) {R : Subgroup Kc} (hR : ⁅R, R⁆ = R)
    (hfix : ∀ r ∈ R, σ (θ r) = θ r) : ∀ r ∈ R, g * ρ r = ρ r * g := by
  have hc : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center Kc := fun r hr => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, hfix r hr, inv_mul_cancel])
  intro r hr
  have := hconj r
  rw [eq_of_central_perfect α hR hc r hr] at this
  exact this.symm

theorem fixed_of_commute (θ : Kc →* X) (α : Kc ≃* Kc) (σ : X ≃* X)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (ρ : Kc →* (V ≃ₗ[K] V))
    (hρ : ρ.ker ≤ Subgroup.center Kc) {g : V ≃ₗ[K] V} (hconj : ∀ y, ρ (α y) * g = g * ρ y)
    {R : Subgroup Kc} (hR : ⁅R, R⁆ = R) (hcomm : ∀ r ∈ R, g * ρ r = ρ r * g) :
    ∀ r ∈ R, σ (θ r) = θ r := by
  have hc : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center Kc := fun r hr => hρ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have h1 : ρ (α r) * g = ρ r * g := by rw [hconj r, hcomm r hr]
    have h2 : ρ (α r) = ρ r := mul_right_cancel h1
    rw [h2, inv_mul_cancel])
  intro r hr
  rw [← hαθ, eq_of_central_perfect α hR hc r hr]

end Group

section Nodes

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

theorem spinAction_rankOne_vec0 (h0 : 0 < n - 1) {k : Fin (n - 1)} (hk : 1 ≤ k.val)
    {r : spinGroup (quadMinus n F b c)} (hr : r ∈ rankOne (minusDatum n hirr).rootGroup k)
    (u : Bool) :
    spinAction (quadMinus n F b c) r (minusVec n ⟨0, h0⟩ u) = minusVec n ⟨0, h0⟩ u := by
  let Fix0 : Subgroup (spinGroup (quadMinus n F b c)) :=
    { carrier := {y | ∀ u, spinAction (quadMinus n F b c) y (minusVec n ⟨0, h0⟩ u) =
        minusVec n ⟨0, h0⟩ u}
      mul_mem' := fun {x y} hx hy u => by
        rw [map_mul, LinearEquiv.mul_apply, hy u, hx u]
      one_mem' := fun u => by simp
      inv_mem' := fun {x} hx u => by
        have h1 := hx u
        calc spinAction (quadMinus n F b c) x⁻¹ (minusVec n ⟨0, h0⟩ u)
            = spinAction (quadMinus n F b c) x⁻¹
                (spinAction (quadMinus n F b c) x (minusVec n ⟨0, h0⟩ u)) := by rw [h1]
          _ = minusVec n ⟨0, h0⟩ u := by
            rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
            rfl }
  have hle : rankOne (minusDatum n hirr).rootGroup k ≤ Fix0 := by
    unfold rankOne
    by_cases hlong : k.val + 1 < n - 1
    · have hij : k ≠ ⟨k.val + 1, hlong⟩ := fun h => by
        have := congrArg Fin.val h
        simp at this
      have hk0 : (⟨0, h0⟩ : Fin (n - 1)) ≠ k := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      have hk1 : (⟨0, h0⟩ : Fin (n - 1)) ≠ ⟨k.val + 1, hlong⟩ := fun h => by
        have := congrArg Fin.val h
        simp at this
      refine sup_le ?_ ?_
      · show minusRootGroup n hirr (Pi.single k 1) ≤ Fix0
        rw [minusRootGroup_eq_long n hirr hij true false (toStdB_single_of_lt' n hlong)]
        rintro _ ⟨x, rfl⟩ u
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
        exact (minusFrame n b c).toHypFrame.spinAction_longRoot_vec_of_ne hij true false a hk0 hk1 u
      · show minusRootGroup n hirr (-Pi.single k 1) ≤ Fix0
        rw [minusRootGroup_eq_long n hirr hij.symm true false (toStdB_neg_single_of_lt' n hlong)]
        rintro _ ⟨x, rfl⟩ u
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
        exact (minusFrame n b c).toHypFrame.spinAction_longRoot_vec_of_ne hij.symm true false a hk1
          hk0 u
    · have hk0 : (⟨0, h0⟩ : Fin (n - 1)) ≠ k := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      refine sup_le ?_ ?_
      · show minusRootGroup n hirr (Pi.single k 1) ≤ Fix0
        rw [minusRootGroup_eq_short n hirr k true (toStdB_single_of_not_lt' n hlong)]
        rintro _ ⟨x, rfl⟩ u
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
        exact spinAction_twShortRoot_vec_of_ne n hirr hk0 true a u
      · show minusRootGroup n hirr (-Pi.single k 1) ≤ Fix0
        rw [minusRootGroup_eq_short n hirr k false (toStdB_neg_single_of_not_lt' n hlong)]
        rintro _ ⟨x, rfl⟩ u
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
        exact spinAction_twShortRoot_vec_of_ne n hirr hk0 false a u
  exact hle hr u

end Nodes

section Perfect

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {m : ℕ}

private theorem rootSL2_conj_perfect (h4 : 4 ≤ Nat.card K) (F₀ : HypFrame Q m) (a b : ℕ)
    (ha : a < m) (hb : b < m) (hab : a ≠ b) (s t : Bool) (x : spinGroup Q) :
    ⁅(rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom,
      (rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom⁆ =
      (rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom := by
  have : Group.IsPerfect SL(2, K) := CFSG.ClassicalInvolution.sl2_isPerfect h4
  have h1 : ⁅rootSL2 F₀ a b ha hb hab s t, rootSL2 F₀ a b ha hb hab s t⁆ =
      rootSL2 F₀ a b ha hb hab s t :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (f := F₀.longSL2 (i := ⟨a, ha⟩) (j := ⟨b, hb⟩)
      (fun h => hab (congrArg Fin.val h)) s t))
  rw [← Subgroup.map_commutator, h1]

end Perfect

section RankOnePerfect

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

omit [Finite F] in
private theorem comm_le_self (R : Subgroup (spinGroup (quadMinus n F b c))) : ⁅R, R⁆ ≤ R :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)

theorem rankOne_minusDatum_perfect' (h4 : 4 ≤ Nat.card F) (k : Fin (n - 1)) :
    ⁅rankOne (minusDatum n hirr).rootGroup k, rankOne (minusDatum n hirr).rootGroup k⁆ =
      rankOne (minusDatum n hirr).rootGroup k := by
  by_cases hk : k.val + 1 < n - 1
  · exact le_antisymm (comm_le_self _)
      (CFSG.ClassicalInvolution.RouteD.rankOne_minusDatum_perfect hirr h4 hk)
  · have := fact_shortField hirr
    have := finite_shortField (b := b) (c := c)
    refine le_antisymm (comm_le_self _) ?_
    rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_short hirr hk]
    exact range_perfect_of_sl2
      (CFSG.ClassicalInvolution.Models.TwistedPairs.four_le_card_shortField' (b := b) (c := c)) _

end RankOnePerfect

section Main

noncomputable abbrev minusHyp {F : Type} [Field F] (n : ℕ) (b c : F) :
    HypFrame (quadMinus n F b c) (n - 1) :=
  (minusFrame n b c).toHypFrame

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  {s : ℕ}

theorem minus_nodes_fixed (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (hs : 1 ≤ s)
    (hker2 : (spinAction (quadMinus (s + 5) F b c)).ker ≤
      Subgroup.center (spinGroup (quadMinus (s + 5) F b c)))
    {X : Type} [Group X] (θ : spinGroup (quadMinus (s + 5) F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus (s + 5) F b c)))
    (σ : X ≃* X) (α : spinGroup (quadMinus (s + 5) F b c) ≃* spinGroup (quadMinus (s + 5) F b c))
    (hαθ : ∀ y, θ (α y) = σ (θ y)) {g₀ : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F}
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (s + 5) F b c))
    (hg₀2 : g₀ * g₀ = 1)
    (hconj : ∀ y, spinAction (quadMinus (s + 5) F b c) (α y) * g₀ =
      g₀ * spinAction (quadMinus (s + 5) F b c) y)
    (x : spinGroup (quadMinus (s + 5) F b c)) (tM : Bool)
    (hfix : ∀ a (_ : 1 ≤ a) (ha : a ≤ s), ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) a (a + 1)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom,
      σ (θ y) = θ y)
    (hfixN : ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) (s + 1) (s + 2) (by omega) (by omega)
      (by omega) true false).map (MulAut.conj x).toMonoidHom, σ (θ y) = θ y)
    (hfixM : ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) (s + 2) (s + 3) (by omega) (by omega)
      (by omega) true tM).map (MulAut.conj x).toMonoidHom, σ (θ y) = θ y)
    (hfixW : ∀ t : Fin 2, ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) 3 4 (by omega) (by omega)
      (by omega) true false).map (MulAut.conj (x * twShortRoot (s + 5) hirr ⟨4, by omega⟩ true
        (.ofAdd (Pi.single t 1)))).toMonoidHom, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) 0 1 (by omega) (by omega) (by omega) true
      false).map (MulAut.conj x).toMonoidHom, σ (θ y) ∈
        ((rootSL2 (minusHyp (s + 5) b c) 0 1 (by omega) (by omega) (by omega) true false).map
          (MulAut.conj x).toMonoidHom).map θ)
    (hmov0 : ∃ y ∈ (rootSL2 (minusHyp (s + 5) b c) 0 1 (by omega) (by omega) (by omega) true
      false).map (MulAut.conj x).toMonoidHom, σ (θ y) ≠ θ y) :
    ∀ k : Fin (s + 5 - 1), 1 ≤ k.val → ∀ r ∈ (rankOne (minusDatum (s + 5) hirr).rootGroup k).map
      (MulAut.conj x).toMonoidHom, σ (θ r) = θ r := by
  classical
  have hQ : (polarBilin (quadMinus (s + 5) F b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite _ F hirr
  set Xl : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F := spinAction (quadMinus (s + 5) F b c) x with hXl
  have hXO : Xl ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (s + 5) F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  set gt : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F := Xl⁻¹ * g₀ * Xl with hgt
  have hgtO : gt ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (s + 5) F b c) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hXO) hg₀O) hXO
  have hgt2 : gt * gt = 1 := by
    calc gt * gt = Xl⁻¹ * (g₀ * g₀) * Xl := by simp only [hgt]; group
      _ = 1 := by rw [hg₀2]; group
  have conv : ∀ {ε : F} {v : Vm (s + 5) F}, g₀ (Xl v) = ε • Xl v → gt v = ε • v := by
    intro ε v h
    show Xl.symm (g₀ (Xl v)) = ε • v
    rw [h, map_smul, LinearEquiv.symm_apply_apply]
  have T1 : ∀ {S : Subgroup (spinGroup (quadMinus (s + 5) F b c))}, ⁅S, S⁆ = S →
      (∀ r ∈ S, σ (θ r) = θ r) → ∀ r ∈ S, g₀ * spinAction (quadMinus (s + 5) F b c) r =
        spinAction (quadMinus (s + 5) F b c) r * g₀ :=
    fun hS hf => commute_of_fixed θ hker α σ hαθ (spinAction (quadMinus (s + 5) F b c)) hconj hS hf
  have T2 : ∀ {S : Subgroup (spinGroup (quadMinus (s + 5) F b c))}, ⁅S, S⁆ = S →
      (∀ r ∈ S, g₀ * spinAction (quadMinus (s + 5) F b c) r =
        spinAction (quadMinus (s + 5) F b c) r * g₀) → ∀ r ∈ S, σ (θ r) = θ r :=
    fun hS hc => fixed_of_commute θ α σ hαθ (spinAction (quadMinus (s + 5) F b c)) hker2 hconj
      hS hc
  have hmapx : ∀ {y : spinGroup (quadMinus (s + 5) F b c)},
      spinAction (quadMinus (s + 5) F b c) (x * y * x⁻¹) = Xl * spinAction _ y * Xl⁻¹ := by
    intro y
    simp [hXl]
  have comm_conj : ∀ {Y : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F}, gt * Y = Y * gt →
      g₀ * (Xl * Y * Xl⁻¹) = (Xl * Y * Xl⁻¹) * g₀ := by
    intro Y h
    calc g₀ * (Xl * Y * Xl⁻¹) = Xl * (Xl⁻¹ * g₀ * Xl * Y) * Xl⁻¹ := by group
      _ = Xl * (Y * (Xl⁻¹ * g₀ * Xl)) * Xl⁻¹ := by rw [← hgt, h]
      _ = (Xl * Y * Xl⁻¹) * g₀ := by group
  have comm_conj' : ∀ {Y : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F},
      g₀ * (Xl * Y * Xl⁻¹) = (Xl * Y * Xl⁻¹) * g₀ → gt * Y = Y * gt := by
    intro Y h
    calc gt * Y = Xl⁻¹ * (g₀ * (Xl * Y * Xl⁻¹)) * Xl := by simp only [hgt]; group
      _ = Xl⁻¹ * ((Xl * Y * Xl⁻¹) * g₀) * Xl := by rw [h]
      _ = Y * gt := by simp only [hgt]; group
  have eigen : ∀ (a b' : ℕ) (ha : a < s + 5 - 1) (hb' : b' < s + 5 - 1) (hab : a ≠ b')
      (sg tg : Bool) (x' : spinGroup (quadMinus (s + 5) F b c)),
      (∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) a b' ha hb' hab sg tg).map
        (MulAut.conj x').toMonoidHom, σ (θ y) = θ y) →
      ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ ∀ u : Bool,
        g₀ (spinAction (quadMinus (s + 5) F b c) x' (minusVec (s + 5) ⟨a, ha⟩ u)) =
          ε • spinAction (quadMinus (s + 5) F b c) x' (minusVec (s + 5) ⟨a, ha⟩ u) ∧
        g₀ (spinAction (quadMinus (s + 5) F b c) x' (minusVec (s + 5) ⟨b', hb'⟩ u)) =
          ε • spinAction (quadMinus (s + 5) F b c) x' (minusVec (s + 5) ⟨b', hb'⟩ u) := by
    intro a b' ha hb' hab sg tg x' hfx
    exact eigen_of_commute_conj_rootSL2 h2 (minusHyp (s + 5) b c) ha hb' hab sg tg x' hg₀O hg₀2
      (T1 (rootSL2_conj_perfect h4 (minusHyp (s + 5) b c) a b' ha hb' hab sg tg x') hfx)
  have toEig : ∀ {a b' : ℕ} {ha : a < s + 5 - 1} {hb' : b' < s + 5 - 1},
      (∃ ε : F, (ε = 1 ∨ ε = -1) ∧ ∀ u : Bool,
        g₀ (Xl (minusVec (s + 5) ⟨a, ha⟩ u)) = ε • Xl (minusVec (s + 5) ⟨a, ha⟩ u) ∧
        g₀ (Xl (minusVec (s + 5) ⟨b', hb'⟩ u)) = ε • Xl (minusVec (s + 5) ⟨b', hb'⟩ u)) →
      ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε a ∧ EigAt gt ε b' := by
    rintro a b' ha hb' ⟨ε, hε, hv⟩
    exact ⟨ε, hε, ⟨ha, fun u => conv (hv u).1⟩, ⟨hb', fun u => conv (hv u).2⟩⟩
  have hchain' : ∀ a, 1 ≤ a → a ≤ s → ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε a ∧
      EigAt gt ε (a + 1) := fun a h1 ha =>
    toEig (eigen a (a + 1) (by omega) (by omega) (by omega) true false x (hfix a h1 ha))
  have hN' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε (s + 1) ∧ EigAt gt ε (s + 2) :=
    toEig (eigen (s + 1) (s + 2) (by omega) (by omega) (by omega) true false x hfixN)
  have hM' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε (s + 2) ∧ EigAt gt ε (s + 3) :=
    toEig (eigen (s + 2) (s + 3) (by omega) (by omega) (by omega) true tM x hfixM)
  have hW' : ∀ t : Fin 2, ∃ ε' : F,
      gt (minusVec (s + 5) ⟨3, by omega⟩ true) = ε' • minusVec (s + 5) ⟨3, by omega⟩ true ∧
      gt (minusVec (s + 5) ⟨4, by omega⟩ true) = ε' • minusVec (s + 5) ⟨4, by omega⟩ true ∧
      gt (minusVec (s + 5) ⟨4, by omega⟩ false + planeVec (s + 5) (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec (s + 5) ⟨4, by omega⟩ true) =
        ε' • (minusVec (s + 5) ⟨4, by omega⟩ false + planeVec (s + 5) (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec (s + 5) ⟨4, by omega⟩ true) := by
    intro t
    obtain ⟨ε, -, hv⟩ := eigen 3 4 (by omega) (by omega) (by omega) true false
      (x * twShortRoot (s + 5) hirr ⟨4, by omega⟩ true (.ofAdd (Pi.single t 1))) (hfixW t)
    have hX : ∀ v, spinAction (quadMinus (s + 5) F b c)
        (x * twShortRoot (s + 5) hirr ⟨4, by omega⟩ true (.ofAdd (Pi.single t 1))) v =
        Xl (spinAction (quadMinus (s + 5) F b c)
          (twShortRoot (s + 5) hirr ⟨4, by omega⟩ true (.ofAdd (Pi.single t 1))) v) :=
      fun v => by rw [map_mul]; rfl
    have h3 : ∀ u, spinAction (quadMinus (s + 5) F b c)
        (twShortRoot (s + 5) hirr ⟨4, by omega⟩ true (.ofAdd (Pi.single t 1)))
        (minusVec (s + 5) ⟨3, by omega⟩ u) = minusVec (s + 5) ⟨3, by omega⟩ u :=
      fun u => spinAction_twShortRoot_vec_of_ne (s + 5) hirr (k := ⟨3, by omega⟩)
        (i := ⟨4, by omega⟩) (by simp) true _ u
    refine ⟨ε, ?_, ?_, ?_⟩
    · have := (hv true).1
      rw [hX, h3] at this
      exact conv this
    · have := (hv true).2
      rw [hX, spinAction_twShortRoot_vec_self] at this
      exact conv this
    · have := (hv false).2
      have h4' : spinAction (quadMinus (s + 5) F b c)
          (twShortRoot (s + 5) hirr ⟨4, by omega⟩ true (.ofAdd (Pi.single t 1)))
          (minusVec (s + 5) ⟨4, by omega⟩ false) =
          minusVec (s + 5) ⟨4, by omega⟩ false + planeVec (s + 5) (Pi.single t 1) -
            planeNorm b c (Pi.single t 1) • minusVec (s + 5) ⟨4, by omega⟩ true :=
        spinAction_twShortRoot_vec_not (s + 5) hirr ⟨4, by omega⟩ true (Pi.single t 1)
      rw [hX, h4'] at this
      exact conv this
  have hperf0 := rootSL2_conj_perfect h4 (minusHyp (s + 5) b c) 0 1 (by omega) (by omega)
    (by omega) true false x
  have hnorm' : ∀ y ∈ rootSL2 (minusHyp (s + 5) b c) 0 1 (by omega) (by omega) (by omega) true
      false,
      ∃ y' ∈ rootSL2 (minusHyp (s + 5) b c) 0 1 (by omega) (by omega) (by omega) true false,
        gt * spinAction (quadMinus (s + 5) F b c) y =
          spinAction (quadMinus (s + 5) F b c) y' * gt := by
    intro y hy
    have hyx : x * y * x⁻¹ ∈ (rootSL2 (minusHyp (s + 5) b c) 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
    have hmem := alpha_mem_of_perfect α hperf0 (fun r hr => by
      obtain ⟨r', hr', hr'e⟩ := hnorm0 r hr
      refine ⟨r', hr', r'⁻¹ * α r, hker ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hr'e, hαθ, inv_mul_cancel]) (x * y * x⁻¹) hyx
    obtain ⟨y', hy', hy'e⟩ := hmem
    have hy'e' : x * y' * x⁻¹ = α (x * y * x⁻¹) := hy'e
    refine ⟨y', hy', ?_⟩
    have h := hconj (x * y * x⁻¹)
    rw [← hy'e', hmapx, hmapx] at h
    calc gt * spinAction (quadMinus (s + 5) F b c) y
        = Xl⁻¹ * (g₀ * (Xl * spinAction _ y * Xl⁻¹)) * Xl := by simp only [hgt]; group
      _ = Xl⁻¹ * ((Xl * spinAction _ y' * Xl⁻¹) * g₀) * Xl := by rw [h]
      _ = spinAction (quadMinus (s + 5) F b c) y' * gt := by simp only [hgt]; group
  have hmov' : ∃ y ∈ rootSL2 (minusHyp (s + 5) b c) 0 1 (by omega) (by omega) (by omega) true false,
      gt * spinAction (quadMinus (s + 5) F b c) y ≠
        spinAction (quadMinus (s + 5) F b c) y * gt := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y0, hy0, hne⟩ := hmov0
    apply hne
    have hall := T2 hperf0 (fun r hr => by
      obtain ⟨y, hy, rfl⟩ := hr
      have := comm_conj (hcon y hy)
      show g₀ * spinAction (quadMinus (s + 5) F b c) (x * y * x⁻¹) =
        spinAction (quadMinus (s + 5) F b c) (x * y * x⁻¹) * g₀
      rw [hmapx]
      exact this)
    exact hall y0 hy0
  have hcl := minus_classify h2 hs hQ hgtO hgt2 hchain' hN' hM' hW' hnorm' hmov'
  intro k hk r hr
  have hperfk : ⁅(rankOne (minusDatum (s + 5) hirr).rootGroup k).map (MulAut.conj x).toMonoidHom,
      (rankOne (minusDatum (s + 5) hirr).rootGroup k).map (MulAut.conj x).toMonoidHom⁆ =
      (rankOne (minusDatum (s + 5) hirr).rootGroup k).map (MulAut.conj x).toMonoidHom := by
    rw [← Subgroup.map_commutator, rankOne_minusDatum_perfect' hirr h4 k]
  refine T2 hperfk (fun r' hr' => ?_) r hr
  obtain ⟨r0, hr0, rfl⟩ := hr'
  have hY0O : spinAction (quadMinus (s + 5) F b c) r0 ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (s + 5) F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ r0 v
  have h0 : 0 < s + 5 - 1 := by omega
  have hc := hcl _ hY0O (spinAction_rankOne_vec0 hirr h0 hk hr0 true)
    (spinAction_rankOne_vec0 hirr h0 hk hr0 false)
  have := comm_conj hc
  show g₀ * spinAction (quadMinus (s + 5) F b c) (x * r0 * x⁻¹) =
    spinAction (quadMinus (s + 5) F b c) (x * r0 * x⁻¹) * g₀
  rw [hmapx]
  exact this

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
