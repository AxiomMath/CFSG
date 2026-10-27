module

public import CFSG.ClassicalInvolution.Q3.Q3TY17

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.CurtisTits (rankOne)
open scoped MatrixGroups commutatorElement

section Group

variable {Kc X : Type} [Group Kc] [Group X]

theorem eq_of_central_pow3 (α : Kc ≃* Kc) {R : Subgroup Kc} (hR : Pow3 R)
    (hcop : ∀ w ∈ Subgroup.center Kc, ¬ 3 ∣ orderOf w)
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
  set k := r⁻¹ * α r with hkdef
  have hαr : α r = r * k := by rw [hkdef]; group
  have h3 : α (r ^ 3) = r ^ 3 := hle (hR r hr)
  have hkc : Commute r k := (Subgroup.mem_center_iff.mp (hc r hr)) r
  have hk3 : k ^ 3 = 1 := by
    have : r ^ 3 * k ^ 3 = r ^ 3 := by
      rw [← hkc.mul_pow, ← hαr, ← map_pow, h3]
    exact mul_eq_left.mp this
  have hk1 : k = 1 := by
    by_contra hne
    have h3' : orderOf k = 3 := orderOf_eq_prime hk3 hne
    exact hcop k (hc r hr) (by rw [h3'])
  rw [hαr, hk1, mul_one]

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem commute_of_fixed3 (θ : Kc →* X) (hker : θ.ker ≤ Subgroup.center Kc)
    (hcop : ∀ w ∈ Subgroup.center Kc, ¬ 3 ∣ orderOf w) (α : Kc ≃* Kc)
    (σ : X ≃* X) (hαθ : ∀ y, θ (α y) = σ (θ y)) (ρ : Kc →* (V ≃ₗ[K] V)) {g : V ≃ₗ[K] V}
    (hconj : ∀ y, ρ (α y) * g = g * ρ y) {R : Subgroup Kc} (hR : Pow3 R)
    (hfix : ∀ r ∈ R, σ (θ r) = θ r) : ∀ r ∈ R, g * ρ r = ρ r * g := by
  have hc : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center Kc := fun r hr => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, hfix r hr, inv_mul_cancel])
  intro r hr
  have := hconj r
  rw [eq_of_central_pow3 α hR hcop hc r hr] at this
  exact this.symm

theorem fixed_of_commute3 (θ : Kc →* X) (α : Kc ≃* Kc) (σ : X ≃* X)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (ρ : Kc →* (V ≃ₗ[K] V))
    (hρ : ρ.ker ≤ Subgroup.center Kc) (hcop : ∀ w ∈ Subgroup.center Kc, ¬ 3 ∣ orderOf w)
    {g : V ≃ₗ[K] V} (hconj : ∀ y, ρ (α y) * g = g * ρ y)
    {R : Subgroup Kc} (hR : Pow3 R) (hcomm : ∀ r ∈ R, g * ρ r = ρ r * g) :
    ∀ r ∈ R, σ (θ r) = θ r := by
  have hc : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center Kc := fun r hr => hρ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have h1 : ρ (α r) * g = ρ r * g := by rw [hconj r, hcomm r hr]
    have h2 : ρ (α r) = ρ r := mul_right_cancel h1
    rw [h2, inv_mul_cancel])
  intro r hr
  rw [← hαθ, eq_of_central_pow3 α hR hcop hc r hr]

end Group

section Nodes

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}

private theorem spinAction_rankOne_vec0 (h0 : 0 < n - 1) {k : Fin (n - 1)} (hk : 1 ≤ k.val)
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

private theorem eigAt_chain (b c : F) {s : ℕ} (hs : 1 ≤ s) {g : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F}
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

private theorem idx_facts3 (s : ℕ) (hs : 1 ≤ s) :
    0 < s + 5 - 1 ∧ 1 < s + 5 - 1 ∧ 2 < s + 5 - 1 ∧ 3 < s + 5 - 1 ∧ 4 < s + 5 - 1 ∧
      s + 1 < s + 5 - 1 ∧ s + 2 < s + 5 - 1 ∧ s + 3 < s + 5 - 1 ∧ (0 : ℕ) ≠ 1 ∧
      (2 : ℕ) ≠ s + 2 ∧ (3 : ℕ) ≠ 4 ∧ s + 2 ≠ s + 3 := by
  omega

private theorem idx_chain3 (s a : ℕ) (ha : a ≤ s) :
    a < s + 5 - 1 ∧ a + 1 < s + 5 - 1 ∧ a ≠ a + 1 := by
  omega

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  {s : ℕ}

theorem minus_nodes_fixed_bridge3 (h2 : (2 : F) ≠ 0) (hs : 1 ≤ s)
    (hcopZ : ∀ w ∈ Subgroup.center (spinGroup (quadMinus (s + 5) F b c)), ¬ 3 ∣ orderOf w)
    (hpowR : ∀ (a b' : ℕ) (ha : a < s + 5 - 1) (hb' : b' < s + 5 - 1) (hab : a ≠ b') (sg tg : Bool)
      (x' : spinGroup (quadMinus (s + 5) F b c)),
      Pow3 ((rootSL2 (minusHyp (s + 5) b c) a b' ha hb' hab sg tg).map
        (MulAut.conj x').toMonoidHom))
    (hpowk : ∀ (k : Fin (s + 5 - 1)) (x' : spinGroup (quadMinus (s + 5) F b c)),
      Pow3 ((rankOne (minusDatum (s + 5) hirr).rootGroup k).map (MulAut.conj x').toMonoidHom))
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
    (hfix : ∀ a (_ : 1 ≤ a) (_ : a ≤ s) (h1 : a < s + 5 - 1) (h2 : a + 1 < s + 5 - 1)
      (h3 : a ≠ a + 1), ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) a (a + 1) h1 h2 h3 true false).map
        (MulAut.conj x).toMonoidHom, σ (θ y) = θ y)
    (hfixB : ∀ (h1 : 2 < s + 5 - 1) (h2 : s + 2 < s + 5 - 1) (h3 : (2 : ℕ) ≠ s + 2),
      ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) 2 (s + 2) h1 h2 h3 true false).map
        (MulAut.conj x).toMonoidHom, σ (θ y) = θ y)
    (hfixM : ∀ (h1 : s + 2 < s + 5 - 1) (h2 : s + 3 < s + 5 - 1) (h3 : s + 2 ≠ s + 3),
      ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) (s + 2) (s + 3) h1 h2 h3 true tM).map
        (MulAut.conj x).toMonoidHom, σ (θ y) = θ y)
    (hfixW : ∀ (h1 : 3 < s + 5 - 1) (h2 : 4 < s + 5 - 1) (h3 : (3 : ℕ) ≠ 4) (t : Fin 2),
      ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) 3 4 h1 h2 h3 true false).map
        (MulAut.conj (x * twShortRoot (s + 5) hirr ⟨4, h2⟩ true
          (.ofAdd (Pi.single t 1)))).toMonoidHom, σ (θ y) = θ y)
    (hnorm0 : ∀ (h1 : 0 < s + 5 - 1) (h2 : 1 < s + 5 - 1) (h3 : (0 : ℕ) ≠ 1),
      ∀ y ∈ (rootSL2 (minusHyp (s + 5) b c) 0 1 h1 h2 h3 true false).map
        (MulAut.conj x).toMonoidHom, σ (θ y) ∈
          ((rootSL2 (minusHyp (s + 5) b c) 0 1 h1 h2 h3 true false).map
            (MulAut.conj x).toMonoidHom).map θ)
    (hmov0 : ∀ (h1 : 0 < s + 5 - 1) (h2 : 1 < s + 5 - 1) (h3 : (0 : ℕ) ≠ 1),
      ∃ y ∈ (rootSL2 (minusHyp (s + 5) b c) 0 1 h1 h2 h3 true false).map
        (MulAut.conj x).toMonoidHom, σ (θ y) ≠ θ y) :
    ∀ k : Fin (s + 5 - 1), 1 ≤ k.val → ∀ r ∈ (rankOne (minusDatum (s + 5) hirr).rootGroup k).map
      (MulAut.conj x).toMonoidHom, σ (θ r) = θ r := by
  classical
  obtain ⟨i0, i1, i2, i3, i4, is1, is2, is3, n01, n2s, n34, nss⟩ := idx_facts3 s hs
  have hQ : (polarBilin (quadMinus (s + 5) F b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite _ F hirr
  obtain ⟨Xl, hXl⟩ : ∃ Xl : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F,
      Xl = spinAction (quadMinus (s + 5) F b c) x := ⟨_, rfl⟩
  have hXO : Xl ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (s + 5) F b c) := by
    rw [hXl]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  obtain ⟨gt, hgt⟩ : ∃ gt : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F, gt = Xl⁻¹ * g₀ * Xl := ⟨_, rfl⟩
  have hgtO : gt ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (s + 5) F b c) := by
    rw [hgt]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hXO) hg₀O) hXO
  have hgt2 : gt * gt = 1 := by
    calc gt * gt = Xl⁻¹ * (g₀ * g₀) * Xl := by rw [hgt]; group
      _ = 1 := by rw [hg₀2]; group
  have conv : ∀ {ε : F} {v : Vm (s + 5) F}, g₀ (Xl v) = ε • Xl v → gt v = ε • v := by
    intro ε v h
    rw [hgt]
    show Xl.symm (g₀ (Xl v)) = ε • v
    rw [h, map_smul, LinearEquiv.symm_apply_apply]
  have T1 : ∀ {S : Subgroup (spinGroup (quadMinus (s + 5) F b c))}, Pow3 S →
      (∀ r ∈ S, σ (θ r) = θ r) → ∀ r ∈ S, g₀ * spinAction (quadMinus (s + 5) F b c) r =
        spinAction (quadMinus (s + 5) F b c) r * g₀ :=
    fun hS hf => commute_of_fixed3 θ hker hcopZ α σ hαθ (spinAction (quadMinus (s + 5) F b c))
      hconj hS hf
  have T2 : ∀ {S : Subgroup (spinGroup (quadMinus (s + 5) F b c))}, Pow3 S →
      (∀ r ∈ S, g₀ * spinAction (quadMinus (s + 5) F b c) r =
        spinAction (quadMinus (s + 5) F b c) r * g₀) → ∀ r ∈ S, σ (θ r) = θ r :=
    fun hS hc => fixed_of_commute3 θ α σ hαθ (spinAction (quadMinus (s + 5) F b c)) hker2 hcopZ
      hconj hS hc
  have hmapx : ∀ {y : spinGroup (quadMinus (s + 5) F b c)},
      spinAction (quadMinus (s + 5) F b c) (x * y * x⁻¹) = Xl * spinAction _ y * Xl⁻¹ := by
    intro y
    rw [hXl, map_mul, map_mul, map_inv]
  have comm_conj : ∀ {Y : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F}, gt * Y = Y * gt →
      g₀ * (Xl * Y * Xl⁻¹) = (Xl * Y * Xl⁻¹) * g₀ := by
    intro Y h
    rw [hgt] at h
    calc g₀ * (Xl * Y * Xl⁻¹) = Xl * (Xl⁻¹ * g₀ * Xl * Y) * Xl⁻¹ := by group
      _ = Xl * (Y * (Xl⁻¹ * g₀ * Xl)) * Xl⁻¹ := by rw [h]
      _ = (Xl * Y * Xl⁻¹) * g₀ := by group
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
      (T1 (hpowR a b' ha hb' hab sg tg x') hfx)
  have toEig : ∀ {a b' : ℕ} {ha : a < s + 5 - 1} {hb' : b' < s + 5 - 1},
      (∃ ε : F, (ε = 1 ∨ ε = -1) ∧ ∀ u : Bool,
        g₀ (spinAction (quadMinus (s + 5) F b c) x (minusVec (s + 5) ⟨a, ha⟩ u)) =
          ε • spinAction (quadMinus (s + 5) F b c) x (minusVec (s + 5) ⟨a, ha⟩ u) ∧
        g₀ (spinAction (quadMinus (s + 5) F b c) x (minusVec (s + 5) ⟨b', hb'⟩ u)) =
          ε • spinAction (quadMinus (s + 5) F b c) x (minusVec (s + 5) ⟨b', hb'⟩ u)) →
      ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε a ∧ EigAt gt ε b' := by
    rintro a b' ha hb' ⟨ε, hε, hv⟩
    rw [← hXl] at hv
    exact ⟨ε, hε, ⟨ha, fun u => conv (hv u).1⟩, ⟨hb', fun u => conv (hv u).2⟩⟩
  have hchain' : ∀ a, 1 ≤ a → a ≤ s → ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε a ∧
      EigAt gt ε (a + 1) := fun a h1 ha => by
    obtain ⟨j1, j2, j3⟩ := idx_chain3 s a ha
    exact toEig (eigen a (a + 1) j1 j2 j3 true false x (hfix a h1 ha j1 j2 j3))
  have hB' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε 2 ∧ EigAt gt ε (s + 2) :=
    toEig (eigen 2 (s + 2) i2 is2 n2s true false x (hfixB i2 is2 n2s))
  have hN' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε (s + 1) ∧ EigAt gt ε (s + 2) := by
    obtain ⟨ε, hε, hε2, hεs⟩ := hB'
    obtain ⟨ε₀, hε₀⟩ := eigAt_chain b c hs hchain'
    have h2' : ε₀ = ε := EigAt.unique' b c (hε₀ 2 (by omega) (by omega)) hε2
    subst h2'
    exact ⟨ε₀, hε, hε₀ (s + 1) (by omega) (by omega), hεs⟩
  have hM' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε (s + 2) ∧ EigAt gt ε (s + 3) :=
    toEig (eigen (s + 2) (s + 3) is2 is3 nss true tM x (hfixM is2 is3 nss))
  have hW' : ∀ t : Fin 2, ∃ ε' : F,
      gt (minusVec (s + 5) ⟨3, i3⟩ true) = ε' • minusVec (s + 5) ⟨3, i3⟩ true ∧
      gt (minusVec (s + 5) ⟨4, i4⟩ true) = ε' • minusVec (s + 5) ⟨4, i4⟩ true ∧
      gt (minusVec (s + 5) ⟨4, i4⟩ false + planeVec (s + 5) (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec (s + 5) ⟨4, i4⟩ true) =
        ε' • (minusVec (s + 5) ⟨4, i4⟩ false + planeVec (s + 5) (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec (s + 5) ⟨4, i4⟩ true) := by
    intro t
    obtain ⟨ε, -, hv⟩ := eigen 3 4 i3 i4 n34 true false
      (x * twShortRoot (s + 5) hirr ⟨4, i4⟩ true (.ofAdd (Pi.single t 1))) (hfixW i3 i4 n34 t)
    have hX : ∀ v, spinAction (quadMinus (s + 5) F b c)
        (x * twShortRoot (s + 5) hirr ⟨4, i4⟩ true (.ofAdd (Pi.single t 1))) v =
        Xl (spinAction (quadMinus (s + 5) F b c)
          (twShortRoot (s + 5) hirr ⟨4, i4⟩ true (.ofAdd (Pi.single t 1))) v) :=
      fun v => by rw [map_mul, hXl]; rfl
    have h3 : ∀ u, spinAction (quadMinus (s + 5) F b c)
        (twShortRoot (s + 5) hirr ⟨4, i4⟩ true (.ofAdd (Pi.single t 1)))
        (minusVec (s + 5) ⟨3, i3⟩ u) = minusVec (s + 5) ⟨3, i3⟩ u :=
      fun u => spinAction_twShortRoot_vec_of_ne (s + 5) hirr (k := ⟨3, i3⟩)
        (i := ⟨4, i4⟩) (by simp) true _ u
    refine ⟨ε, ?_, ?_, ?_⟩
    · have := (hv true).1
      rw [hX, h3] at this
      exact conv this
    · have := (hv true).2
      rw [hX, spinAction_twShortRoot_vec_self] at this
      exact conv this
    · have := (hv false).2
      have h4' : spinAction (quadMinus (s + 5) F b c)
          (twShortRoot (s + 5) hirr ⟨4, i4⟩ true (.ofAdd (Pi.single t 1)))
          (minusVec (s + 5) ⟨4, i4⟩ false) =
          minusVec (s + 5) ⟨4, i4⟩ false + planeVec (s + 5) (Pi.single t 1) -
            planeNorm b c (Pi.single t 1) • minusVec (s + 5) ⟨4, i4⟩ true :=
        spinAction_twShortRoot_vec_not (s + 5) hirr ⟨4, i4⟩ true (Pi.single t 1)
      rw [hX, h4'] at this
      exact conv this
  have hperf0 := hpowR 0 1 i0 i1 n01 true false x
  have hnorm' : ∀ y ∈ rootSL2 (minusHyp (s + 5) b c) 0 1 i0 i1 n01 true false,
      ∃ y' ∈ rootSL2 (minusHyp (s + 5) b c) 0 1 i0 i1 n01 true false,
        gt * spinAction (quadMinus (s + 5) F b c) y =
          spinAction (quadMinus (s + 5) F b c) y' * gt := by
    intro y hy
    have hyx : x * y * x⁻¹ ∈ (rootSL2 (minusHyp (s + 5) b c) 0 1 i0 i1 n01 true false).map
        (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
    have hmem := mem_of_stable3 θ hker (fun w hw => hcopZ w (hker hw)) α σ hαθ hperf0
      (fun r hr => hnorm0 i0 i1 n01 r hr) (x * y * x⁻¹) hyx
    obtain ⟨y', hy', hy'e⟩ := hmem
    have hy'e' : x * y' * x⁻¹ = α (x * y * x⁻¹) := hy'e
    refine ⟨y', hy', ?_⟩
    have h := hconj (x * y * x⁻¹)
    rw [← hy'e', hmapx, hmapx] at h
    rw [hgt]
    calc Xl⁻¹ * g₀ * Xl * spinAction (quadMinus (s + 5) F b c) y
        = Xl⁻¹ * (g₀ * (Xl * spinAction _ y * Xl⁻¹)) * Xl := by group
      _ = Xl⁻¹ * ((Xl * spinAction _ y' * Xl⁻¹) * g₀) * Xl := by rw [h]
      _ = spinAction (quadMinus (s + 5) F b c) y' * (Xl⁻¹ * g₀ * Xl) := by group
  have hmov' : ∃ y ∈ rootSL2 (minusHyp (s + 5) b c) 0 1 i0 i1 n01 true false,
      gt * spinAction (quadMinus (s + 5) F b c) y ≠
        spinAction (quadMinus (s + 5) F b c) y * gt := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y0, hy0, hne⟩ := hmov0 i0 i1 n01
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
  refine T2 (hpowk k x) (fun r' hr' => ?_) r hr
  obtain ⟨r0, hr0, rfl⟩ := hr'
  have hY0O : spinAction (quadMinus (s + 5) F b c) r0 ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (s + 5) F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ r0 v
  have hc := hcl _ hY0O (spinAction_rankOne_vec0 hirr i0 hk hr0 true)
    (spinAction_rankOne_vec0 hirr i0 hk hr0 false)
  have := comm_conj hc
  show g₀ * spinAction (quadMinus (s + 5) F b c) (x * r0 * x⁻¹) =
    spinAction (quadMinus (s + 5) F b c) (x * r0 * x⁻¹) * g₀
  rw [hmapx]
  exact this


end Main

end CFSG.ClassicalInvolution.Q3.Q3TY
