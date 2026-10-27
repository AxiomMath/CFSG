module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusFix
public import CFSG.ClassicalInvolution.RouteD.TwinSmallSixGeo
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.LieType.CurtisTits (rankOne)
open scoped MatrixGroups commutatorElement

section Nodes

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

private theorem spinAction_rankOne_vec0 (h0 : 0 < n - 1) {k : Fin (n - 1)} (hk : 1 ≤ k.val)
    {r : spinGroup (quadMinus n F b c)} (hr : r ∈ rankOne (minusDatum n hirr).rootGroup k)
    (u : Bool) :
    spinAction (quadMinus n F b c) r (minusVec n ⟨0, h0⟩ u) = minusVec n ⟨0, h0⟩ u :=
  CFSG.ClassicalInvolution.RouteD.Gaps.spinAction_rankOne_vec0 hirr h0 hk hr u

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

private theorem rankOne_minusDatum_perfect' (h4 : 4 ≤ Nat.card F) (k : Fin (n - 1)) :
    ⁅rankOne (minusDatum n hirr).rootGroup k, rankOne (minusDatum n hirr).rootGroup k⁆ =
      rankOne (minusDatum n hirr).rootGroup k :=
  CFSG.ClassicalInvolution.RouteD.Gaps.rankOne_minusDatum_perfect' hirr h4 k

end RankOnePerfect

section Main

variable {F : Type} [Field F] [Finite F] {b c : F}

theorem minus_nodes_fixed_six (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hodd : Odd (Nat.card F))
    (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (hker2 : (spinAction (quadMinus 6 F b c)).ker ≤
      Subgroup.center (spinGroup (quadMinus 6 F b c)))
    {X : Type} [Group X] (θ : spinGroup (quadMinus 6 F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus 6 F b c)))
    (σ : X ≃* X) (α : spinGroup (quadMinus 6 F b c) ≃* spinGroup (quadMinus 6 F b c))
    (hαθ : ∀ y, θ (α y) = σ (θ y)) {g₀ : Vm 6 F ≃ₗ[F] Vm 6 F}
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 6 F b c))
    (hg₀2 : g₀ * g₀ = 1)
    (hconj : ∀ y, spinAction (quadMinus 6 F b c) (α y) * g₀ =
      g₀ * spinAction (quadMinus 6 F b c) y)
    (x : spinGroup (quadMinus 6 F b c)) (tM : Bool)
    (hfix : ∀ y ∈ (rootSL2 (minusHyp 6 b c) 1 2 (by omega) (by omega) (by omega) true
      false).map (MulAut.conj x).toMonoidHom, σ (θ y) = θ y)
    (hfixM : ∀ y ∈ (rootSL2 (minusHyp 6 b c) 3 4 (by omega) (by omega) (by omega) true
      tM).map (MulAut.conj x).toMonoidHom, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ (rootSL2 (minusHyp 6 b c) 0 1 (by omega) (by omega) (by omega) true
      false).map (MulAut.conj x).toMonoidHom, σ (θ y) ∈
        ((rootSL2 (minusHyp 6 b c) 0 1 (by omega) (by omega) (by omega) true false).map
          (MulAut.conj x).toMonoidHom).map θ)
    (hmov0 : ∃ y ∈ (rootSL2 (minusHyp 6 b c) 0 1 (by omega) (by omega) (by omega) true
      false).map (MulAut.conj x).toMonoidHom, σ (θ y) ≠ θ y)
    (hN0 : (∀ y ∈ (rootSL2 (minusHyp 6 b c) 0 3 (by omega) (by omega) (by omega) true
      false).map (MulAut.conj x).toMonoidHom, σ (θ y) = θ y) → False)
    (hpair : ∃ (T₀ : Submodule F (Vm 6 F)) (s : F), 6 ≤ Module.finrank F T₀ ∧
      (∀ v ∈ T₀, g₀ v = s • v) ∧ (∀ v ∈ T₀, ∀ k : Fin (6 - 1), (k.val = 1 ∨ k.val = 2) → ∀ u,
        polar (quadMinus 6 F b c) v (spinAction (quadMinus 6 F b c) x (minusVec 6 k u)) = 0)) :
    ∀ k : Fin (6 - 1), 1 ≤ k.val → ∀ r ∈ (rankOne (minusDatum 6 hirr).rootGroup k).map
      (MulAut.conj x).toMonoidHom, σ (θ r) = θ r := by
  classical
  have hQ : (polarBilin (quadMinus 6 F b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite _ F hirr
  set Xl : Vm 6 F ≃ₗ[F] Vm 6 F := spinAction (quadMinus 6 F b c) x with hXl
  have hXO : Xl ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 6 F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  set gt : Vm 6 F ≃ₗ[F] Vm 6 F := Xl⁻¹ * g₀ * Xl with hgt
  have hgtO : gt ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 6 F b c) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hXO) hg₀O) hXO
  have hgt2 : gt * gt = 1 := by
    calc gt * gt = Xl⁻¹ * (g₀ * g₀) * Xl := by simp only [hgt]; group
      _ = 1 := by rw [hg₀2]; group
  have conv : ∀ {ε : F} {v : Vm 6 F}, g₀ (Xl v) = ε • Xl v → gt v = ε • v := by
    intro ε v h
    show Xl.symm (g₀ (Xl v)) = ε • v
    rw [h, map_smul, LinearEquiv.symm_apply_apply]
  have T1 : ∀ {S : Subgroup (spinGroup (quadMinus 6 F b c))}, ⁅S, S⁆ = S →
      (∀ r ∈ S, σ (θ r) = θ r) → ∀ r ∈ S, g₀ * spinAction (quadMinus 6 F b c) r =
        spinAction (quadMinus 6 F b c) r * g₀ :=
    fun hS hf => commute_of_fixed θ hker α σ hαθ (spinAction (quadMinus 6 F b c)) hconj hS hf
  have T2 : ∀ {S : Subgroup (spinGroup (quadMinus 6 F b c))}, ⁅S, S⁆ = S →
      (∀ r ∈ S, g₀ * spinAction (quadMinus 6 F b c) r =
        spinAction (quadMinus 6 F b c) r * g₀) → ∀ r ∈ S, σ (θ r) = θ r :=
    fun hS hc => fixed_of_commute θ α σ hαθ (spinAction (quadMinus 6 F b c)) hker2 hconj
      hS hc
  have hmapx : ∀ {y : spinGroup (quadMinus 6 F b c)},
      spinAction (quadMinus 6 F b c) (x * y * x⁻¹) = Xl * spinAction _ y * Xl⁻¹ := by
    intro y
    simp [hXl]
  have comm_conj : ∀ {Y : Vm 6 F ≃ₗ[F] Vm 6 F}, gt * Y = Y * gt →
      g₀ * (Xl * Y * Xl⁻¹) = (Xl * Y * Xl⁻¹) * g₀ := by
    intro Y h
    calc g₀ * (Xl * Y * Xl⁻¹) = Xl * (Xl⁻¹ * g₀ * Xl * Y) * Xl⁻¹ := by group
      _ = Xl * (Y * (Xl⁻¹ * g₀ * Xl)) * Xl⁻¹ := by rw [← hgt, h]
      _ = (Xl * Y * Xl⁻¹) * g₀ := by group
  have comm_conj' : ∀ {Y : Vm 6 F ≃ₗ[F] Vm 6 F},
      g₀ * (Xl * Y * Xl⁻¹) = (Xl * Y * Xl⁻¹) * g₀ → gt * Y = Y * gt := by
    intro Y h
    calc gt * Y = Xl⁻¹ * (g₀ * (Xl * Y * Xl⁻¹)) * Xl := by simp only [hgt]; group
      _ = Xl⁻¹ * ((Xl * Y * Xl⁻¹) * g₀) * Xl := by rw [h]
      _ = Y * gt := by simp only [hgt]; group
  have eigen : ∀ (a b' : ℕ) (ha : a < 6 - 1) (hb' : b' < 6 - 1) (hab : a ≠ b')
      (sg tg : Bool) (x' : spinGroup (quadMinus 6 F b c)),
      (∀ y ∈ (rootSL2 (minusHyp 6 b c) a b' ha hb' hab sg tg).map
        (MulAut.conj x').toMonoidHom, σ (θ y) = θ y) →
      ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ ∀ u : Bool,
        g₀ (spinAction (quadMinus 6 F b c) x' (minusVec 6 ⟨a, ha⟩ u)) =
          ε • spinAction (quadMinus 6 F b c) x' (minusVec 6 ⟨a, ha⟩ u) ∧
        g₀ (spinAction (quadMinus 6 F b c) x' (minusVec 6 ⟨b', hb'⟩ u)) =
          ε • spinAction (quadMinus 6 F b c) x' (minusVec 6 ⟨b', hb'⟩ u) := by
    intro a b' ha hb' hab sg tg x' hfx
    exact eigen_of_commute_conj_rootSL2 h2 (minusHyp 6 b c) ha hb' hab sg tg x' hg₀O hg₀2
      (T1 (rootSL2_conj_perfect h4 (minusHyp 6 b c) a b' ha hb' hab sg tg x') hfx)
  have toEig : ∀ {a b' : ℕ} {ha : a < 6 - 1} {hb' : b' < 6 - 1},
      (∃ ε : F, (ε = 1 ∨ ε = -1) ∧ ∀ u : Bool,
        g₀ (Xl (minusVec 6 ⟨a, ha⟩ u)) = ε • Xl (minusVec 6 ⟨a, ha⟩ u) ∧
        g₀ (Xl (minusVec 6 ⟨b', hb'⟩ u)) = ε • Xl (minusVec 6 ⟨b', hb'⟩ u)) →
      ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε a ∧ EigAt gt ε b' := by
    rintro a b' ha hb' ⟨ε, hε, hv⟩
    exact ⟨ε, hε, ⟨ha, fun u => conv (hv u).1⟩, ⟨hb', fun u => conv (hv u).2⟩⟩
  have hC1 : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε 1 ∧ EigAt gt ε 2 :=
    toEig (eigen 1 2 (by omega) (by omega) (by omega) true false x hfix)
  have hchain'' : ∀ a, 1 ≤ a → a ≤ 1 → ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε a ∧
      EigAt gt ε (a + 1) := fun a h1 ha => by
    obtain rfl : a = 1 := by omega
    exact hC1
  have hM' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε 3 ∧ EigAt gt ε 4 :=
    toEig (eigen 3 4 (by omega) (by omega) (by omega) true tM x hfixM)
  have hperf0 := rootSL2_conj_perfect h4 (minusHyp 6 b c) 0 1 (by omega) (by omega)
    (by omega) true false x
  have hnorm' : ∀ y ∈ rootSL2 (minusHyp 6 b c) 0 1 (by omega) (by omega) (by omega) true
      false,
      ∃ y' ∈ rootSL2 (minusHyp 6 b c) 0 1 (by omega) (by omega) (by omega) true false,
        gt * spinAction (quadMinus 6 F b c) y =
          spinAction (quadMinus 6 F b c) y' * gt := by
    intro y hy
    have hyx : x * y * x⁻¹ ∈ (rootSL2 (minusHyp 6 b c) 0 1 (by omega) (by omega)
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
    calc gt * spinAction (quadMinus 6 F b c) y
        = Xl⁻¹ * (g₀ * (Xl * spinAction _ y * Xl⁻¹)) * Xl := by simp only [hgt]; group
      _ = Xl⁻¹ * ((Xl * spinAction _ y' * Xl⁻¹) * g₀) * Xl := by rw [h]
      _ = spinAction (quadMinus 6 F b c) y' * gt := by simp only [hgt]; group
  have hmov' : ∃ y ∈ rootSL2 (minusHyp 6 b c) 0 1 (by omega) (by omega) (by omega) true false,
      gt * spinAction (quadMinus 6 F b c) y ≠
        spinAction (quadMinus 6 F b c) y * gt := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y0, hy0, hne⟩ := hmov0
    apply hne
    have hall := T2 hperf0 (fun r hr => by
      obtain ⟨y, hy, rfl⟩ := hr
      have := comm_conj (hcon y hy)
      show g₀ * spinAction (quadMinus 6 F b c) (x * y * x⁻¹) =
        spinAction (quadMinus 6 F b c) (x * y * x⁻¹) * g₀
      rw [hmapx]
      exact this)
    exact hall y0 hy0
  obtain ⟨ε₁, hε₁, hE1a, hE1b⟩ := hC1
  obtain ⟨εM, hεM, hE3, hE4⟩ := hM'
  have hsq₁ : ε₁ * ε₁ = 1 := by rcases hε₁ with rfl | rfl <;> ring
  have hsqM : εM * εM = 1 := by rcases hεM with rfl | rfl <;> ring
  obtain ⟨h1lt, hv1⟩ := hE1a
  obtain ⟨h2lt, hv2⟩ := hE1b
  obtain ⟨h3lt, hv3⟩ := hE3
  obtain ⟨h4lt, hv4⟩ := hE4
  have hS : SixSigns b c gt ε₁ εM :=
    { gO := hgtO
      g2 := hgt2
      sq₁ := hsq₁
      sqM := hsqM
      p1 := fun k hk u => by
        rcases hk with hk | hk
        · have : k = ⟨1, h1lt⟩ := Fin.ext hk
          rw [this]
          exact hv1 u
        · have : k = ⟨2, h2lt⟩ := Fin.ext hk
          rw [this]
          exact hv2 u
      p3 := fun k hk u => by
        rcases hk with hk | hk
        · have : k = ⟨3, h3lt⟩ := Fin.ext hk
          rw [this]
          exact hv3 u
        · have : k = ⟨4, h4lt⟩ := Fin.ext hk
          rw [this]
          exact hv4 u }
  obtain ⟨a, ha1, haε, hg0⟩ := geo_H0 hodd hS hnorm' hmov'
  have haa : a * a = 1 := by rcases ha1 with rfl | rfl <;> ring
  have haM : a ≠ εM := by
    intro haεM
    apply hN0
    let σs : Fin (6 - 1) → F := fun i => if i.val = 0 then a else if i.val ≤ 2 then ε₁ else εM
    have hσ : ∀ i, σs i * σs i = 1 := by
      intro i
      simp only [σs]
      split_ifs <;> assumption
    have hTσ : ∀ i r, gt ((minusHyp 6 b c).vec i r) = σs i • (minusHyp 6 b c).vec i r := by
      intro i r
      change gt (minusVec 6 i r) = σs i • minusVec 6 i r
      by_cases hi0 : i.val = 0
      · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
        have hs0 : σs i = a := by
          show (if i.val = 0 then a else if i.val ≤ 2 then ε₁ else εM) = a
          rw [ite_eq_left hi0]
        rw [hs0, hi]
        exact hg0 r
      · by_cases hi12 : i.val ≤ 2
        · have hs1 : σs i = ε₁ := by
            show (if i.val = 0 then a else if i.val ≤ 2 then ε₁ else εM) = ε₁
            rw [ite_eq_right hi0, ite_eq_left hi12]
          rw [hs1]
          exact hS.p1 i (by omega) r
        · have hs3 : σs i = εM := by
            show (if i.val = 0 then a else if i.val ≤ 2 then ε₁ else εM) = εM
            rw [ite_eq_right hi0, ite_eq_right hi12]
          rw [hs3]
          exact hS.p3 i (by omega) r
    have hkl : (⟨0, by omega⟩ : Fin (6 - 1)) ≠ ⟨3, by omega⟩ := by simp
    have hσkl : σs ⟨0, by omega⟩ = σs ⟨3, by omega⟩ := by simp [σs, haεM]
    have hperf03 := rootSL2_conj_perfect h4 (minusHyp 6 b c) 0 3 (by omega) (by omega)
      (by omega) true false x
    have hc03 : ∀ y ∈ rootSL2 (minusHyp 6 b c) 0 3 (by omega) (by omega) (by omega) true false,
        gt * spinAction (quadMinus 6 F b c) y = spinAction (quadMinus 6 F b c) y * gt := by
      intro y hy
      obtain ⟨A, rfl⟩ := hy
      have hA : spinAction (quadMinus 6 F b c) ((minusHyp 6 b c).longSL2 hkl true false A) =
          ((minusHyp 6 b c).toFrame hkl true false).La A :=
        DFunLike.congr_fun (spinAction_comp_longSL2 (minusHyp 6 b c) hkl true false) A
      rw [hA]
      exact comm_La_toFrame_of_sign (minusHyp 6 b c) hgtO hσ hTσ hkl true false hσkl A
    exact T2 hperf03 (fun r hr => by
      obtain ⟨y, hy, rfl⟩ := hr
      have := comm_conj (hc03 y hy)
      show g₀ * spinAction (quadMinus 6 F b c) (x * y * x⁻¹) =
        spinAction (quadMinus 6 F b c) (x * y * x⁻¹) * g₀
      rw [hmapx]
      exact this)
  obtain ⟨T₀, s, hT0, hT0g, hT0p⟩ := hpair
  let T : Submodule F (Vm 6 F) := T₀.map (Xl.symm : Vm 6 F ≃ₗ[F] Vm 6 F).toLinearMap
  have hTdim : 6 ≤ Module.finrank F T := by
    have : Module.finrank F T = Module.finrank F T₀ := LinearEquiv.finrank_map_eq Xl.symm T₀
    omega
  have hTg : ∀ v ∈ T, gt v = s • v := by
    rintro _ ⟨y, hy, rfl⟩
    show Xl.symm (g₀ (Xl (Xl.symm y))) = s • Xl.symm y
    rw [LinearEquiv.apply_symm_apply, hT0g y hy, map_smul]
  have hTp : ∀ v ∈ T, ∀ k : Fin (6 - 1), (k.val = 1 ∨ k.val = 2) → ∀ u,
      polar (quadMinus 6 F b c) v (minusVec 6 k u) = 0 := by
    rintro _ ⟨y, hy, rfl⟩ k hk u
    have h := hT0p y hy k hk u
    change polar (quadMinus 6 F b c) (Xl.symm y) (minusVec 6 k u) = 0
    rw [← polar_map_of_mem hXO (Xl.symm y) (minusVec 6 k u)]
    simpa using h
  obtain ⟨hεMε₁, hA⟩ := geo_ties hodd hS ha1 haε haM hg0 T hTdim hTg hTp
  have hN' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε 2 ∧ EigAt gt ε 3 :=
    ⟨ε₁, hε₁, ⟨h2lt, hv2⟩, ⟨h3lt, fun u => by rw [hv3 u, hεMε₁]⟩⟩
  have hM'' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε 3 ∧ EigAt gt ε 4 :=
    ⟨εM, hεM, ⟨h3lt, hv3⟩, ⟨h4lt, hv4⟩⟩
  have hW' : ∀ t : Fin 2, ∃ ε' : F,
      gt (minusVec 6 ⟨3, by omega⟩ true) = ε' • minusVec 6 ⟨3, by omega⟩ true ∧
      gt (minusVec 6 ⟨4, by omega⟩ true) = ε' • minusVec 6 ⟨4, by omega⟩ true ∧
      gt (minusVec 6 ⟨4, by omega⟩ false + planeVec 6 (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec 6 ⟨4, by omega⟩ true) =
        ε' • (minusVec 6 ⟨4, by omega⟩ false + planeVec 6 (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec 6 ⟨4, by omega⟩ true) := by
    intro t
    refine ⟨εM, hv3 true, hv4 true, ?_⟩
    rw [map_sub, map_add, map_smul, hv4 false, hv4 true, hA, ← hεMε₁]
    module
  have hcl := minus_classify h2 (s := 1) (le_refl 1) hQ hgtO hgt2 hchain'' hN' hM'' hW' hnorm' hmov'
  intro k hk r hr
  have hperfk : ⁅(rankOne (minusDatum 6 hirr).rootGroup k).map (MulAut.conj x).toMonoidHom,
      (rankOne (minusDatum 6 hirr).rootGroup k).map (MulAut.conj x).toMonoidHom⁆ =
      (rankOne (minusDatum 6 hirr).rootGroup k).map (MulAut.conj x).toMonoidHom := by
    rw [← Subgroup.map_commutator, rankOne_minusDatum_perfect' hirr h4 k]
  refine T2 hperfk (fun r' hr' => ?_) r hr
  obtain ⟨r0, hr0, rfl⟩ := hr'
  have hY0O : spinAction (quadMinus 6 F b c) r0 ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 6 F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ r0 v
  have h0 : 0 < 6 - 1 := by omega
  have hc := hcl _ hY0O (spinAction_rankOne_vec0 hirr h0 hk hr0 true)
    (spinAction_rankOne_vec0 hirr h0 hk hr0 false)
  have := comm_conj hc
  show g₀ * spinAction (quadMinus 6 F b c) (x * r0 * x⁻¹) =
    spinAction (quadMinus 6 F b c) (x * r0 * x⁻¹) * g₀
  rw [hmapx]
  exact this


end Main

end CFSG.ClassicalInvolution.RouteD.TwinSmall
