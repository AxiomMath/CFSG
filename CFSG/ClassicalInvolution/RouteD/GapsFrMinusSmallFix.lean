module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusFix

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.CurtisTits (rankOne)
open scoped MatrixGroups commutatorElement

section Nodes

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}


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


end RankOnePerfect

section EigChain

variable {F : Type} [Field F] {n : ℕ}

private theorem minusVec_ne_zero' (b c : F) (i : Fin (n - 1)) (u : Bool) :
    minusVec n (K := F) i u ≠ 0 := by
  intro h
  have h1 := polar_minusVec_minusVec n b c i i u (!u)
  rw [h] at h1
  simp at h1

private theorem EigAt.unique' (b c : F) {g : Vm n F ≃ₗ[F] Vm n F} {ε ε' : F} {a : ℕ}
    (h : EigAt g ε a) (h' : EigAt g ε' a) : ε = ε' := by
  obtain ⟨ha, hv⟩ := h
  obtain ⟨_, hv'⟩ := h'
  exact smul_left_injective F (minusVec_ne_zero' b c ⟨a, ha⟩ true)
    ((hv true).symm.trans (hv' true))

theorem eigAt_chain (b c : F) {s : ℕ} (hs : 1 ≤ s) {g : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F}
    (hchain : ∀ a, 1 ≤ a → a ≤ s → ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt g ε a ∧ EigAt g ε (a + 1)) :
    ∃ ε : F, ∀ a, 1 ≤ a → a ≤ s + 1 → EigAt g ε a := by
  obtain ⟨ε₀, -, h1, h2⟩ := hchain 1 le_rfl hs
  have key : ∀ k, 1 ≤ k → k ≤ s → EigAt g ε₀ k ∧ EigAt g ε₀ (k + 1) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact fun _ => ⟨h1, h2⟩
    | succ k hk ih =>
      intro hks
      obtain ⟨ε', -, h1', h2'⟩ := hchain (k + 1) (by omega) hks
      obtain ⟨-, hk1⟩ := ih (by omega)
      have := EigAt.unique' b c hk1 h1'
      subst this
      exact ⟨h1', h2'⟩
  refine ⟨ε₀, fun a ha1 ha2 => ?_⟩
  by_cases has : a ≤ s
  · exact (key a ha1 has).1
  · have : a = s + 1 := by omega
    subst this
    exact (key s hs le_rfl).2

end EigChain

section Main

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  {s : ℕ}

theorem minus_nodes_fixed_bridge (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (hs : 1 ≤ s)
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
    (hfixB : ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) 2 (s + 2) (by omega) (by omega)
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
  have hB' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε 2 ∧ EigAt gt ε (s + 2) :=
    toEig (eigen 2 (s + 2) (by omega) (by omega) (by omega) true false x hfixB)
  have hN' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε (s + 1) ∧ EigAt gt ε (s + 2) := by
    obtain ⟨ε, hε, hε2, hεs⟩ := hB'
    obtain ⟨ε₀, hε₀⟩ := eigAt_chain b c hs hchain'
    have h2' : ε₀ = ε := EigAt.unique' b c (hε₀ 2 (by omega) (by omega)) hε2
    subst h2'
    exact ⟨ε₀, hε, hε₀ (s + 1) (by omega) (by omega), hεs⟩
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
