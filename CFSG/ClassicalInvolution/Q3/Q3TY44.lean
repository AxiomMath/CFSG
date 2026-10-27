module

public import CFSG.ClassicalInvolution.Q3.Q3TY35
public import CFSG.ClassicalInvolution.RouteD.TwinSmallFix
public import CFSG.ClassicalInvolution.Q3.Q3TY34

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.ClassicalInvolution.RouteD.TwinSmall (leafV₀)
open scoped MatrixGroups commutatorElement

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame


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

section Main

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

omit [Finite F] in
private theorem leaf_sign {V : Type} [AddCommGroup V] [Module F V] {g : V ≃ₗ[F] V}
    {S : Submodule F V} (hS : (∀ v ∈ S, g v = v) ∨ (∀ v ∈ S, g v = -v)) {v : V} (hv : v ∈ S)
    (hv0 : v ≠ 0) {ε : F} (hε : g v = ε • v) : ∀ u ∈ S, g u = ε • u := by
  rcases hS with h | h
  · have h1 : ε • v = v := by rw [← hε]; exact h v hv
    have h2 : ε = 1 := by
      have : (ε - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hv0)
    intro u hu
    rw [h u hu, h2, one_smul]
  · have h1 : ε • v = -v := by rw [← hε]; exact h v hv
    have h2 : ε = -1 := by
      have : (ε + 1) • v = 0 := by rw [add_smul, h1, one_smul, neg_add_cancel]
      exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp this).resolve_right hv0)
    intro u hu
    rw [h u hu, h2, neg_one_smul]

theorem minus_nodes_fixed_seven3 (h2 : (2 : F) ≠ 0)
    (hcopZ : ∀ w ∈ Subgroup.center (spinGroup (quadMinus 7 F b c)), ¬ 3 ∣ orderOf w)
    (hpowR : ∀ (a b' : ℕ) (ha : a < 7 - 1) (hb' : b' < 7 - 1) (hab : a ≠ b') (sg tg : Bool)
      (x' : spinGroup (quadMinus 7 F b c)),
      Pow3 ((rootSL2 (minusHyp 7 b c) a b' ha hb' hab sg tg).map (MulAut.conj x').toMonoidHom))
    (hpowk : ∀ (k : Fin (7 - 1)) (x' : spinGroup (quadMinus 7 F b c)),
      Pow3 ((rankOne (minusDatum 7 hirr).rootGroup k).map (MulAut.conj x').toMonoidHom))
    (hker2 : (spinAction (quadMinus 7 F b c)).ker ≤
      Subgroup.center (spinGroup (quadMinus 7 F b c)))
    {X : Type} [Group X] (θ : spinGroup (quadMinus 7 F b c) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus 7 F b c)))
    (σ : X ≃* X) (α : spinGroup (quadMinus 7 F b c) ≃* spinGroup (quadMinus 7 F b c))
    (hαθ : ∀ y, θ (α y) = σ (θ y)) {g₀ : Vm 7 F ≃ₗ[F] Vm 7 F}
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 7 F b c)) (hg₀2 : g₀ * g₀ = 1)
    (hconj : ∀ y, spinAction (quadMinus 7 F b c) (α y) * g₀ =
      g₀ * spinAction (quadMinus 7 F b c) y)
    (x : spinGroup (quadMinus 7 F b c)) (tM : Bool)
    (hfix : ∀ a (_ : 1 ≤ a) (ha : a ≤ 2), ∀ y ∈ (rootSL2 (minusHyp 7 b c) a (a + 1)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom,
      σ (θ y) = θ y)
    (hfixM : ∀ y ∈ (rootSL2 (minusHyp 7 b c) 4 5 (by omega) (by omega) (by omega) true tM).map
      (MulAut.conj x).toMonoidHom, σ (θ y) = θ y)
    (hleaf₁ : ∃ (R : Subgroup (spinGroup (quadMinus 7 F b c))) (F_N : OPFrame (quadMinus 7 F b c)),
      Pow3 R ∧ R.map (spinAction (quadMinus 7 F b c)) = F_N.La.range ∧
        leafV₀ 7 (⟨2, by omega⟩ : Fin (7 - 1)) ∈ F_N.span ∧ (∀ w, planeVec 7 w ∈ F_N.span) ∧
        ∀ y ∈ R.map (MulAut.conj x).toMonoidHom, σ (θ y) = θ y)
    (hleaf₂ : ∃ (R : Subgroup (spinGroup (quadMinus 7 F b c))) (F_N : OPFrame (quadMinus 7 F b c)),
      Pow3 R ∧ R.map (spinAction (quadMinus 7 F b c)) = F_N.La.range ∧
        leafV₀ 7 (⟨4, by omega⟩ : Fin (7 - 1)) ∈ F_N.span ∧ (∀ w, planeVec 7 w ∈ F_N.span) ∧
        ∀ y ∈ R.map (MulAut.conj x).toMonoidHom, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ (rootSL2 (minusHyp 7 b c) 0 1 (by omega) (by omega) (by omega) true
      false).map (MulAut.conj x).toMonoidHom, σ (θ y) ∈
        ((rootSL2 (minusHyp 7 b c) 0 1 (by omega) (by omega) (by omega) true false).map
          (MulAut.conj x).toMonoidHom).map θ)
    (hmov0 : ∃ y ∈ (rootSL2 (minusHyp 7 b c) 0 1 (by omega) (by omega) (by omega) true
      false).map (MulAut.conj x).toMonoidHom, σ (θ y) ≠ θ y) :
    ∀ k : Fin (7 - 1), 1 ≤ k.val → ∀ r ∈ (rankOne (minusDatum 7 hirr).rootGroup k).map
      (MulAut.conj x).toMonoidHom, σ (θ r) = θ r := by
  classical
  have hQ : (polarBilin (quadMinus 7 F b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite _ F hirr
  set Xl : Vm 7 F ≃ₗ[F] Vm 7 F := spinAction (quadMinus 7 F b c) x with hXl
  have hXO : Xl ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 7 F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  set gt : Vm 7 F ≃ₗ[F] Vm 7 F := Xl⁻¹ * g₀ * Xl with hgt
  have hgtO : gt ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 7 F b c) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hXO) hg₀O) hXO
  have hgt2 : gt * gt = 1 := by
    calc gt * gt = Xl⁻¹ * (g₀ * g₀) * Xl := by simp only [hgt]; group
      _ = 1 := by rw [hg₀2]; group
  have conv : ∀ {ε : F} {v : Vm 7 F}, g₀ (Xl v) = ε • Xl v → gt v = ε • v := by
    intro ε v h
    show Xl.symm (g₀ (Xl v)) = ε • v
    rw [h, map_smul, LinearEquiv.symm_apply_apply]
  have T1 : ∀ {S : Subgroup (spinGroup (quadMinus 7 F b c))}, Pow3 S →
      (∀ r ∈ S, σ (θ r) = θ r) → ∀ r ∈ S, g₀ * spinAction (quadMinus 7 F b c) r =
        spinAction (quadMinus 7 F b c) r * g₀ :=
    fun hS hf => commute_of_fixed3 θ hker hcopZ α σ hαθ (spinAction (quadMinus 7 F b c)) hconj
      hS hf
  have T2 : ∀ {S : Subgroup (spinGroup (quadMinus 7 F b c))}, Pow3 S →
      (∀ r ∈ S, g₀ * spinAction (quadMinus 7 F b c) r =
        spinAction (quadMinus 7 F b c) r * g₀) → ∀ r ∈ S, σ (θ r) = θ r :=
    fun hS hc => fixed_of_commute3 θ α σ hαθ (spinAction (quadMinus 7 F b c)) hker2 hcopZ hconj
      hS hc
  have hmapx : ∀ {y : spinGroup (quadMinus 7 F b c)},
      spinAction (quadMinus 7 F b c) (x * y * x⁻¹) = Xl * spinAction _ y * Xl⁻¹ := by
    intro y
    simp [hXl]
  have comm_conj : ∀ {Y : Vm 7 F ≃ₗ[F] Vm 7 F}, gt * Y = Y * gt →
      g₀ * (Xl * Y * Xl⁻¹) = (Xl * Y * Xl⁻¹) * g₀ := by
    intro Y h
    calc g₀ * (Xl * Y * Xl⁻¹) = Xl * (Xl⁻¹ * g₀ * Xl * Y) * Xl⁻¹ := by group
      _ = Xl * (Y * (Xl⁻¹ * g₀ * Xl)) * Xl⁻¹ := by rw [← hgt, h]
      _ = (Xl * Y * Xl⁻¹) * g₀ := by group
  have comm_conj' : ∀ {Y : Vm 7 F ≃ₗ[F] Vm 7 F},
      g₀ * (Xl * Y * Xl⁻¹) = (Xl * Y * Xl⁻¹) * g₀ → gt * Y = Y * gt := by
    intro Y h
    calc gt * Y = Xl⁻¹ * (g₀ * (Xl * Y * Xl⁻¹)) * Xl := by simp only [hgt]; group
      _ = Xl⁻¹ * ((Xl * Y * Xl⁻¹) * g₀) * Xl := by rw [h]
      _ = Y * gt := by simp only [hgt]; group
  have eigen : ∀ (a b' : ℕ) (ha : a < 7 - 1) (hb' : b' < 7 - 1) (hab : a ≠ b')
      (sg tg : Bool) (x' : spinGroup (quadMinus 7 F b c)),
      (∀ y ∈ (rootSL2 (minusHyp 7 b c) a b' ha hb' hab sg tg).map
        (MulAut.conj x').toMonoidHom, σ (θ y) = θ y) →
      ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ ∀ u : Bool,
        g₀ (spinAction (quadMinus 7 F b c) x' (minusVec 7 ⟨a, ha⟩ u)) =
          ε • spinAction (quadMinus 7 F b c) x' (minusVec 7 ⟨a, ha⟩ u) ∧
        g₀ (spinAction (quadMinus 7 F b c) x' (minusVec 7 ⟨b', hb'⟩ u)) =
          ε • spinAction (quadMinus 7 F b c) x' (minusVec 7 ⟨b', hb'⟩ u) := by
    intro a b' ha hb' hab sg tg x' hfx
    exact eigen_of_commute_conj_rootSL2 h2 (minusHyp 7 b c) ha hb' hab sg tg x' hg₀O hg₀2
      (T1 (hpowR a b' ha hb' hab sg tg x') hfx)
  have toEig : ∀ {a b' : ℕ} {ha : a < 7 - 1} {hb' : b' < 7 - 1},
      (∃ ε : F, (ε = 1 ∨ ε = -1) ∧ ∀ u : Bool,
        g₀ (Xl (minusVec 7 ⟨a, ha⟩ u)) = ε • Xl (minusVec 7 ⟨a, ha⟩ u) ∧
        g₀ (Xl (minusVec 7 ⟨b', hb'⟩ u)) = ε • Xl (minusVec 7 ⟨b', hb'⟩ u)) →
      ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε a ∧ EigAt gt ε b' := by
    rintro a b' ha hb' ⟨ε, hε, hv⟩
    exact ⟨ε, hε, ⟨ha, fun u => conv (hv u).1⟩, ⟨hb', fun u => conv (hv u).2⟩⟩
  have hchain' : ∀ a, 1 ≤ a → a ≤ 2 → ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε a ∧
      EigAt gt ε (a + 1) := fun a h1 ha =>
    toEig (eigen a (a + 1) (by omega) (by omega) (by omega) true false x (hfix a h1 ha))
  have hM' : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε 4 ∧ EigAt gt ε 5 :=
    toEig (eigen 4 5 (by omega) (by omega) (by omega) true tM x hfixM)
  have hleafcomm : ∀ (R : Subgroup (spinGroup (quadMinus 7 F b c)))
      (F_N : OPFrame (quadMinus 7 F b c)), Pow3 R →
      R.map (spinAction (quadMinus 7 F b c)) = F_N.La.range →
      (∀ y ∈ R.map (MulAut.conj x).toMonoidHom, σ (θ y) = θ y) →
      ∀ A : SL(2, F), gt * F_N.La A = F_N.La A * gt := by
    intro R F_N hRp hRm hRf A
    have hA : F_N.La A ∈ R.map (spinAction (quadMinus 7 F b c)) := by
      rw [hRm]
      exact ⟨A, rfl⟩
    obtain ⟨y, hy, hyA⟩ := hA
    have hc := T1 (hRp.map (MulAut.conj x).toMonoidHom) hRf (x * y * x⁻¹) ⟨y, hy, rfl⟩
    rw [hmapx] at hc
    rw [← hyA]
    exact comm_conj' hc
  have leafV₀_ne : ∀ i : Fin (7 - 1), leafV₀ (K := F) 7 i ≠ 0 := fun i h => by
    have : polar (quadMinus 7 F b c) (leafV₀ 7 i) (minusVec 7 i false) = 1 := by
      unfold leafV₀
      simp only [polar_sub_left, polar_minusVec_minusVec 7 b c]
      simp
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  have hpl0 : planeVec 7 (planeOne : Fin 2 → F) ≠ 0 := fun h => by
    have := quadMinus_planeOne 7 b c
    rw [h, QuadraticMap.map_zero] at this
    exact zero_ne_one this
  obtain ⟨ε₂, hε₂, hc2a, hc2b⟩ := hchain' 2 (by omega) le_rfl
  obtain ⟨εM, hεM, hM4, hM5⟩ := hM'
  obtain ⟨R₁, F₁, hR₁p, hR₁m, hv₁, hα₁, hR₁f⟩ := hleaf₁
  obtain ⟨R₂, F₂, hR₂p, hR₂m, hv₂, hα₂, hR₂f⟩ := hleaf₂
  have hlf1 := frame_eigen_of_commute_La h2 F₁ hgtO hgt2 (hleafcomm R₁ F₁ hR₁p hR₁m hR₁f)
  have hlf2 := frame_eigen_of_commute_La h2 F₂ hgtO hgt2 (hleafcomm R₂ F₂ hR₂p hR₂m hR₂f)
  have hv₁eig : gt (leafV₀ 7 (⟨2, by omega⟩ : Fin (7 - 1))) =
      ε₂ • leafV₀ 7 (⟨2, by omega⟩ : Fin (7 - 1)) := by
    obtain ⟨h2a, hv2⟩ := hc2a
    unfold leafV₀
    rw [map_sub, hv2 true, hv2 false, smul_sub]
  have hv₂eig : gt (leafV₀ 7 (⟨4, by omega⟩ : Fin (7 - 1))) =
      εM • leafV₀ 7 (⟨4, by omega⟩ : Fin (7 - 1)) := by
    obtain ⟨h4a, hv4⟩ := hM4
    unfold leafV₀
    rw [map_sub, hv4 true, hv4 false, smul_sub]
  have hA1 : ∀ w, gt (planeVec 7 w) = ε₂ • planeVec 7 w := fun w =>
    leaf_sign hlf1 hv₁ (leafV₀_ne _) hv₁eig _ (hα₁ w)
  have hA2 : ∀ w, gt (planeVec 7 w) = εM • planeVec 7 w := fun w =>
    leaf_sign hlf2 hv₂ (leafV₀_ne _) hv₂eig _ (hα₂ w)
  have hεeq : ε₂ = εM := by
    have h1 := (hA1 planeOne).symm.trans (hA2 planeOne)
    have h' : (ε₂ - εM) • planeVec 7 (planeOne : Fin 2 → F) = 0 := by
      rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hpl0)
  have hNd : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε 3 ∧ EigAt gt ε 4 :=
    ⟨εM, hεM, hεeq ▸ hc2b, hM4⟩
  have hMd : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt gt ε 4 ∧ EigAt gt ε 5 :=
    ⟨εM, hεM, hM4, hM5⟩
  have hW' : ∀ t : Fin 2, ∃ ε' : F,
      gt (minusVec 7 ⟨3, by omega⟩ true) = ε' • minusVec 7 ⟨3, by omega⟩ true ∧
      gt (minusVec 7 ⟨4, by omega⟩ true) = ε' • minusVec 7 ⟨4, by omega⟩ true ∧
      gt (minusVec 7 ⟨4, by omega⟩ false + planeVec 7 (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec 7 ⟨4, by omega⟩ true) =
        ε' • (minusVec 7 ⟨4, by omega⟩ false + planeVec 7 (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec 7 ⟨4, by omega⟩ true) := by
    intro t
    obtain ⟨h3, hv3⟩ := hc2b
    obtain ⟨h4', hv4⟩ := hM4
    refine ⟨εM, ?_, hv4 true, ?_⟩
    · have := hv3 true
      rwa [hεeq] at this
    · rw [map_sub, map_add, map_smul, hv4 true, hv4 false, hA2]
      module
  have hperf0 := hpowR 0 1 (by omega) (by omega) (by omega) true false x
  have hnorm' : ∀ y ∈ rootSL2 (minusHyp 7 b c) 0 1 (by omega) (by omega) (by omega) true
      false,
      ∃ y' ∈ rootSL2 (minusHyp 7 b c) 0 1 (by omega) (by omega) (by omega) true false,
        gt * spinAction (quadMinus 7 F b c) y =
          spinAction (quadMinus 7 F b c) y' * gt := by
    intro y hy
    have hyx : x * y * x⁻¹ ∈ (rootSL2 (minusHyp 7 b c) 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
    have hmem := mem_of_stable3 θ hker (fun w hw => hcopZ w (hker hw)) α σ hαθ hperf0
      (fun r hr => hnorm0 r hr) (x * y * x⁻¹) hyx
    obtain ⟨y', hy', hy'e⟩ := hmem
    have hy'e' : x * y' * x⁻¹ = α (x * y * x⁻¹) := hy'e
    refine ⟨y', hy', ?_⟩
    have h := hconj (x * y * x⁻¹)
    rw [← hy'e', hmapx, hmapx] at h
    calc gt * spinAction (quadMinus 7 F b c) y
        = Xl⁻¹ * (g₀ * (Xl * spinAction _ y * Xl⁻¹)) * Xl := by simp only [hgt]; group
      _ = Xl⁻¹ * ((Xl * spinAction _ y' * Xl⁻¹) * g₀) * Xl := by rw [h]
      _ = spinAction (quadMinus 7 F b c) y' * gt := by simp only [hgt]; group
  have hmov' : ∃ y ∈ rootSL2 (minusHyp 7 b c) 0 1 (by omega) (by omega) (by omega) true false,
      gt * spinAction (quadMinus 7 F b c) y ≠
        spinAction (quadMinus 7 F b c) y * gt := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y0, hy0, hne⟩ := hmov0
    apply hne
    have hall := T2 hperf0 (fun r hr => by
      obtain ⟨y, hy, rfl⟩ := hr
      have := comm_conj (hcon y hy)
      show g₀ * spinAction (quadMinus 7 F b c) (x * y * x⁻¹) =
        spinAction (quadMinus 7 F b c) (x * y * x⁻¹) * g₀
      rw [hmapx]
      exact this)
    exact hall y0 hy0
  have hcl := minus_classify (s := 2) h2 (by omega) hQ hgtO hgt2 hchain' hNd hMd hW' hnorm' hmov'
  intro k hk r hr
  refine T2 (hpowk k x) (fun r' hr' => ?_) r hr
  obtain ⟨r0, hr0, rfl⟩ := hr'
  have hY0O : spinAction (quadMinus 7 F b c) r0 ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 7 F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ r0 v
  have h0 : 0 < 7 - 1 := by omega
  have hc := hcl _ hY0O (spinAction_rankOne_vec0 hirr h0 hk hr0 true)
    (spinAction_rankOne_vec0 hirr h0 hk hr0 false)
  have := comm_conj hc
  show g₀ * spinAction (quadMinus 7 F b c) (x * r0 * x⁻¹) =
    spinAction (quadMinus 7 F b c) (x * r0 * x⁻¹) * g₀
  rw [hmapx]
  exact this

end Main

end CFSG.ClassicalInvolution.Q3.Q3TY
