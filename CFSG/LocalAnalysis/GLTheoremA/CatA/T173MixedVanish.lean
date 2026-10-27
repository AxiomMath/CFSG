module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedStd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniVanish
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedShape

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173M

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.LocalAnalysis.GLTheoremA.T173X
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {l : ℕ} {U : Fin l → Submodule F V}
  {ρ : Fin l → ↥(orthDerived Q)} {i j : Fin l} {A : Subgroup ↥(orthDerived Q)} {d : ↥(orthDerived Q)}

theorem exists_fin_ne_three (hl : 4 ≤ l) (i j k : Fin l) : ∃ m : Fin l, m ≠ i ∧ m ≠ j ∧ m ≠ k := by
  by_contra hno
  push Not at hno
  have hsub : (Finset.univ : Finset (Fin l)) ⊆ {i, j, k} := fun m _ => by
    by_contra hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact hm.2.2 (hno m hm.1 hm.2.1)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h3 : ({i, j, k} : Finset (Fin l)).card ≤ 3 := Finset.card_le_three
  omega

private theorem eq_bot_of_rootSet_aux1 (hM : IsMixedFrame Q p U ρ i j A) {a m : Fin l} (ham : a ≠ m)
    {y : V} (hy : y ∈ U a) : ∃ z ∈ U m, Q y = Q z := by
  obtain ⟨φ⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff
    (n := 1) (hM.frame.nondeg a) (hM.frame.nondeg m)
    (by rw [hM.frame.finrank_eq a]) (by rw [hM.frame.finrank_eq m])
    ⟨fun h => absurd h (hM.frame.not_isPlusType a),
      fun h => absurd h (hM.frame.not_isPlusType m)⟩
  exact ⟨φ ⟨y, hy⟩, (φ ⟨y, hy⟩).2, (φ.map_app ⟨y, hy⟩).symm⟩

private theorem eq_bot_of_rootSet_aux2 (hM : IsMixedFrame Q p U ρ i j A) {a m : Fin l}
    (ham : a ≠ m) (hmi : m ≠ i) (hmj : m ≠ j) {K : Subgroup (V ≃ₗ[F] V)}
    {W : Submodule F V} (hTS : ∀ x ∈ W, Q x = 0) (hWij : W ≤ U i ⊔ U j)
    (hKW : ∀ g ∈ K, ∀ x ∈ W, g x ∈ W) {x y z w : V}
    (hx : x ∈ W) (hy : y ∈ U a) (hz : z ∈ U m) (hQyz : Q y = Q z)
    (hwroot : w ∈ rootSet Q K (y + z)) (hwmem : w ∈ U a ⊔ U m) :
    eichler Q (y + z) w x = x := by
  have hpol : polar Q (y + z) w = 0 := (mem_rootSet.1 hwroot).1
  have hE : eichler Q (y + z) w ∈ K := (mem_rootSet.1 hwroot).2
  have hyz : polar Q y z = 0 := hM.frame.perp a m ham y hy z hz
  have hQu : Q (y + z) = 0 := by
    rw [QuadraticMap.map_add Q y z, hyz, add_zero, hQyz]
    exact CharTwo.add_self_eq_zero _
  have hvW : eichler Q (y + z) w x - x ∈ W := Submodule.sub_mem _ (hKW _ hE x hx) hx
  have hWperp : ∀ v ∈ W, v ∈ polarPerp Q (U m) := by
    intro v hv
    refine mem_polarPerp_iff.2 fun s hs => ?_
    obtain ⟨vi, hvi, vj, hvj, rfl⟩ := Submodule.mem_sup.1 (hWij hv)
    rw [polar_add_right, polar_comm Q s vi, polar_comm Q s vj,
      hM.frame.perp i m (Ne.symm hmi) vi hvi s hs, hM.frame.perp j m (Ne.symm hmj) vj hvj s hs, add_zero]
  have hvperp : eichler Q (y + z) w x - x ∈ polarPerp Q (U m) := hWperp _ hvW
  have hu_mem : y + z ∈ U a ⊔ U m :=
    Submodule.add_mem _ (Submodule.mem_sup_left hy) (Submodule.mem_sup_right hz)
  have hvsup : eichler Q (y + z) w x - x ∈ U a ⊔ U m := by
    have h' : eichler Q (y + z) w x - x =
        polar Q x (y + z) • w - (polar Q x w + Q w * polar Q x (y + z)) • (y + z) := by
      rw [eichler_apply hQu hpol]; abel
    rw [h']
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hwmem) (Submodule.smul_mem _ _ hu_mem)
  obtain ⟨va, hva, vm, hvm, hv_eq⟩ := Submodule.mem_sup.1 hvsup
  have hvm0 : vm = 0 := by
    have h0 : (⟨vm, hvm⟩ : U m) = 0 := (hM.frame.nondeg m).1 ⟨vm, hvm⟩ fun s => by
      rw [polarBilin_apply_apply, polar_comp_subtype_cent]
      have h1 : polar Q s (eichler Q (y + z) w x - x) = 0 := (mem_polarPerp_iff.1 hvperp) s s.2
      rw [← hv_eq, polar_add_right, polar_comm Q s va,
        hM.frame.perp a m ham va hva s s.2, zero_add] at h1
      rw [polar_comm Q vm s]
      exact h1
    exact congrArg Subtype.val h0
  have hva' : eichler Q (y + z) w x - x ∈ U a := by rw [← hv_eq, hvm0, add_zero]; exact hva
  have hzero : eichler Q (y + z) w x - x = 0 :=
    eq_zero_of_map_eq_zero_of_mem_plane hM.frame.toIsPlaneSystem a hva' (hTS _ hvW)
  exact sub_eq_zero.mp hzero

private theorem eq_bot_of_rootSet_aux3 (hM : IsMixedFrame Q p U ρ i j A) {a m : Fin l}
    (ham : a ≠ m) (hmi : m ≠ i) (hmj : m ≠ j) {K : Subgroup (V ≃ₗ[F] V)}
    (hK : ∀ y ∈ U a, ∀ z ∈ U m, y ≠ 0 → Q y = Q z →
      ∃ w ∈ rootSet Q K (y + z), w ∈ U a ⊔ U m ∧ ∀ c : F, w ≠ c • (y + z))
    {W : Submodule F V} (hTS : ∀ x ∈ W, Q x = 0) (hWij : W ≤ U i ⊔ U j)
    (hKW : ∀ g ∈ K, ∀ x ∈ W, g x ∈ W) :
    ∀ x ∈ W, ∀ y ∈ U a, polar Q x y = 0 := by
  intro x hx y hy
  by_cases hy0 : y = 0
  · rw [hy0, polar_zero_right]
  · obtain ⟨z, hz, hQyz⟩ := eq_bot_of_rootSet_aux1 hM ham hy
    obtain ⟨w, hwroot, hwmem, hwne⟩ := hK y hy z hz hy0 hQyz
    have hEx : eichler Q (y + z) w x = x :=
      eq_bot_of_rootSet_aux2 hM ham hmi hmj hTS hWij hKW hx hy hz hQyz hwroot hwmem
    have hpol : polar Q (y + z) w = 0 := (mem_rootSet.1 hwroot).1
    have hyz : polar Q y z = 0 := hM.frame.perp a m ham y hy z hz
    have hQu : Q (y + z) = 0 := by
      rw [QuadraticMap.map_add Q y z, hyz, add_zero, hQyz]
      exact CharTwo.add_self_eq_zero _
    have hxu : polar Q x (y + z) = 0 := by
      by_contra hxu0
      have hEq : polar Q x (y + z) • w =
          (polar Q x w + Q w * polar Q x (y + z)) • (y + z) := by
        have h := eichler_apply hQu hpol x
        rw [hEx, eq_sub_iff_add_eq] at h
        exact (add_left_cancel h).symm
      have hw : w = ((polar Q x (y + z))⁻¹ *
          (polar Q x w + Q w * polar Q x (y + z))) • (y + z) := by
        calc w = (polar Q x (y + z))⁻¹ • (polar Q x (y + z) • w) := by
              rw [smul_smul, inv_mul_cancel₀ hxu0, one_smul]
          _ = (polar Q x (y + z))⁻¹ •
                ((polar Q x w + Q w * polar Q x (y + z)) • (y + z)) := by rw [hEq]
          _ = ((polar Q x (y + z))⁻¹ *
                (polar Q x w + Q w * polar Q x (y + z))) • (y + z) := by rw [smul_smul]
      exact hwne _ hw
    have hxz : polar Q x z = 0 := by
      have h1 : x ∈ polarPerp Q (U m) := by
        refine mem_polarPerp_iff.2 fun s hs => ?_
        obtain ⟨xi, hxi, xj, hxj, rfl⟩ := Submodule.mem_sup.1 (hWij hx)
        rw [polar_add_right, polar_comm Q s xi, polar_comm Q s xj,
          hM.frame.perp i m (Ne.symm hmi) xi hxi s hs, hM.frame.perp j m (Ne.symm hmj) xj hxj s hs, add_zero]
      have h2 := (mem_polarPerp_iff.1 h1) z hz
      rwa [polar_comm] at h2
    have h := hxu
    rw [polar_add_right, hxz, add_zero] at h
    exact h

private theorem eq_bot_of_rootSet_aux4 (hM : IsMixedFrame Q p U ρ i j A) {a : Fin l}
    (ha : a = i ∨ a = j) {W : Submodule F V} (hTS : ∀ x ∈ W, Q x = 0) (hWij : W ≤ U i ⊔ U j)
    (hperp : ∀ x ∈ W, ∀ y ∈ U a, polar Q x y = 0) : W = ⊥ := by
  refine (Submodule.eq_bot_iff W).2 fun x hx => ?_
  rcases ha with h | h
  · rw [h] at hperp
    obtain ⟨xi, hxi, xj, hxj, rfl⟩ := Submodule.mem_sup.1 (hWij hx)
    have hxi0 : xi = 0 := by
      have h0 : (⟨xi, hxi⟩ : U i) = 0 := (hM.frame.nondeg i).1 ⟨xi, hxi⟩ fun s => by
        rw [polarBilin_apply_apply, polar_comp_subtype_cent]
        have h2 : polar Q (xi + xj) s = 0 := hperp (xi + xj) hx s s.2
        rw [polar_add_left, hM.frame.perp j i (Ne.symm hM.ne) xj hxj s s.2, add_zero] at h2
        exact h2
      exact congrArg Subtype.val h0
    have hQxj : Q xj = 0 := by
      have h3 := hTS (xi + xj) hx
      rw [hxi0, zero_add] at h3
      exact h3
    have hxj0 : xj = 0 :=
      eq_zero_of_map_eq_zero_of_mem_plane hM.frame.toIsPlaneSystem j hxj hQxj
    rw [hxi0, hxj0, zero_add]
  · rw [h] at hperp
    obtain ⟨xi, hxi, xj, hxj, rfl⟩ := Submodule.mem_sup.1 (hWij hx)
    have hxj0 : xj = 0 := by
      have h0 : (⟨xj, hxj⟩ : U j) = 0 := (hM.frame.nondeg j).1 ⟨xj, hxj⟩ fun s => by
        rw [polarBilin_apply_apply, polar_comp_subtype_cent]
        have h2 : polar Q (xi + xj) s = 0 := hperp (xi + xj) hx s s.2
        rw [polar_add_left, hM.frame.perp i j hM.ne xi hxi s s.2, zero_add] at h2
        exact h2
      exact congrArg Subtype.val h0
    have hQxi : Q xi = 0 := by
      have h3 := hTS (xi + xj) hx
      rw [hxj0, add_zero] at h3
      exact h3
    have hxi0 : xi = 0 :=
      eq_zero_of_map_eq_zero_of_mem_plane hM.frame.toIsPlaneSystem i hxi hQxi
    rw [hxi0, hxj0, zero_add]

theorem eq_bot_of_rootSet (hM : IsMixedFrame Q p U ρ i j A) {a m : Fin l} (ha : a = i ∨ a = j) (hmi : m ≠ i)
    (hmj : m ≠ j) {K : Subgroup (V ≃ₗ[F] V)}
    (hK : ∀ y ∈ U a, ∀ z ∈ U m, y ≠ 0 → Q y = Q z →
      ∃ w ∈ rootSet Q K (y + z), w ∈ U a ⊔ U m ∧ ∀ c : F, w ≠ c • (y + z))
    {W : Submodule F V} (hTS : ∀ x ∈ W, Q x = 0) (hWij : W ≤ U i ⊔ U j)
    (hKW : ∀ g ∈ K, ∀ x ∈ W, g x ∈ W) : W = ⊥ := by
  have ham : a ≠ m := by
    intro h
    rcases ha with h' | h'
    · exact hmi (h.symm.trans h')
    · exact hmj (h.symm.trans h')
  exact eq_bot_of_rootSet_aux4 hM ha hTS hWij
    (eq_bot_of_rootSet_aux3 hM ham hmi hmj hK hTS hWij hKW)

private theorem exists_rootSet_specialBlock_aux1 (hM : IsMixedFrame Q p U ρ i j A)
    {d : ↥(orthDerived Q)} (hd : d ∈ A) (k : Fin l) :
    ∀ x ∈ U k, (d : V ≃ₗ[F] V) x ∈ U k := by
  obtain ⟨n, hn⟩ := hM.frame.exists_pow_apply_eq (hM.le_torus hd) k
  have hpow : ∀ n : ℕ, ∀ x ∈ U k, ((ρ k : V ≃ₗ[F] V) ^ n) x ∈ U k := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ, LinearEquiv.mul_apply]
      exact ih _ (hM.frame.maps_to k x hx)
  intro x hx
  rw [hn x hx]
  exact hpow n x hx

private theorem exists_rootSet_specialBlock_aux2 (hM : IsMixedFrame Q p U ρ i j A) {a m : Fin l}
    (ham : a ≠ m) {d : V ≃ₗ[F] V} {y z : V} (hy : y ∈ U a) (hz : z ∈ U m)
    (hdya : d y ∈ U a) (hdzm : d z ∈ U m) {c : F} (hcu : d (y + z) = c • (y + z)) :
    d y = c • y := by
  have hdisj : Disjoint (U a) (U m) := by
    have h := hM.frame.disjoint_biSup (a := a) (s := {m}) (by simp [ham])
    simpa using h
  have hXY : (d y - c • y) + (d z - c • z) = 0 := by
    have h := hcu
    rw [map_add, smul_add] at h
    rw [show (d y - c • y) + (d z - c • z) = (d y + d z) - (c • y + c • z) by abel,
      h, sub_self]
  have hXa : d y - c • y ∈ U a := Submodule.sub_mem _ hdya (Submodule.smul_mem _ _ hy)
  have hYm : d z - c • z ∈ U m := Submodule.sub_mem _ hdzm (Submodule.smul_mem _ _ hz)
  have hXm : d y - c • y ∈ U m := by
    have h2 : d y - c • y = -(d z - c • z) := eq_neg_iff_add_eq_zero.2 hXY
    rw [h2]
    exact neg_mem hYm
  have hX0 : d y - c • y = 0 := by
    have h2 : d y - c • y ∈ U a ⊓ U m := Submodule.mem_inf.2 ⟨hXa, hXm⟩
    rw [disjoint_iff.mp hdisj] at h2
    exact (Submodule.mem_bot F).1 h2
  exact sub_eq_zero.mp hX0

private theorem exists_rootSet_specialBlock_aux3 {d : V ≃ₗ[F] V} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {h : Polynomial F} (hh : h ∈ primaryFactors d.toLinearMap)
    (hh1 : h ≠ X - 1) {y : V} (hy0 : y ≠ 0) (hyV : y ∈ primaryComponent d.toLinearMap h)
    (hdp : d ^ p = 1) {c : F} (hdcy : d y = c • y) : False := by
  have hiter : ∀ k : ℕ, (d ^ k) y = (c ^ k) • y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, LinearEquiv.mul_apply, hdcy, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hycp : y = c ^ p • y := by
    have h := hiter p
    rw [hdp] at h
    simpa using h
  have hzero : (c ^ p - 1) • y = 0 := by
    rw [sub_smul, one_smul, ← hycp, sub_self]
  have hcp : c ^ p = 1 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hy0
  have hc1 : c = 1 := eq_one_of_pow_eq_one_of_dvd_card_add_one hp hp2 hpq hcp
  have hdy : d y = y := by rw [hdcy, hc1, one_smul]
  exact hy0 (eq_zero_of_mem_primaryComponent_of_apply_eq hh hh1 hyV hdy)

theorem exists_rootSet_specialBlock (hM : IsMixedFrame Q p U ρ i j A) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d) {h : Polynomial F}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ k, U k ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) {a m : Fin l} (ham : a ≠ m) {y z : V}
    (hy : y ∈ U a) (hz : z ∈ U m) (hy0 : y ≠ 0) (hQyz : Q y = Q z) :
    ∃ w ∈ rootSet Q (specialBlock Q (d : V ≃ₗ[F] V) h) (y + z), w ∈ U a ⊔ U m ∧ ∀ c : F, w ≠ c • (y + z) := by
  have hPn : PolarNondegOn Q ⊤ := by
    have h := CFSG.LocalAnalysis.GLTheoremA.T173U.polarNondegOn_iSup_of_isPlaneSystem
      hM.frame.toIsPlaneSystem
    rwa [hM.iSup_eq_top] at h
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    ⟨fun v hv => hPn v trivial fun w _ => by simpa using hv w,
      fun v hv => hPn v trivial fun w _ => by
        have h : polar Q w v = 0 := by simpa using hv w
        rwa [polar_comm] at h⟩
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) := oddOrderIsometry_of_std hQ hp hp2 hd
  have hu : y + z ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h :=
    Submodule.add_mem _ (hU a hy) (hU m hz)
  have hyz : polar Q y z = 0 := hM.frame.perp a m ham y hy z hz
  have hQu : Q (y + z) = 0 := by
    rw [QuadraticMap.map_add Q y z, hyz, add_zero, hQyz]
    exact CharTwo.add_self_eq_zero _
  have hdya : (d : V ≃ₗ[F] V) y ∈ U a := exists_rootSet_specialBlock_aux1 hM hd.1 a y hy
  have hdzm : (d : V ≃ₗ[F] V) z ∈ U m := exists_rootSet_specialBlock_aux1 hM hd.1 m z hz
  refine ⟨(d : V ≃ₗ[F] V) (y + z), ?_, ?_, ?_⟩
  · have hroot := CFSG.LocalAnalysis.GLTheoremA.T173U.aeval_mem_rootSet_specialBlock
      hp hp2 hpq hx hh hh1 hu hQu Polynomial.X
    simpa using hroot
  · rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hdya) (Submodule.mem_sup_right hdzm)
  · intro c hcu
    have hdp : (d : V ≃ₗ[F] V) ^ p = 1 := by
      have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hd.2.2.1
      simpa using h
    exact exists_rootSet_specialBlock_aux3 hp hp2 hpq hh hh1 hy0 (hU a hy) hdp
      (exists_rootSet_specialBlock_aux2 hM ham hy hz hdya hdzm hcu)

private theorem exists_rootSet_supportedFixed_aux1 (hM : IsMixedFrame Q p U ρ i j A)
    {a m : Fin l} (ham : a ≠ m) {y z y' z' : V} (hy : y ∈ U a) (hz : z ∈ U m)
    (hy' : y' ∈ U a) (hz' : z' ∈ U m) (hpy' : polar Q y y' ≠ 0) :
    ∀ c : F, y' + z' ≠ c • (y + z) := by
  intro c hc
  have hyy : polar Q y y = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  have hyz0 : polar Q y z = 0 := hM.frame.perp a m ham y hy z hz
  have hw0 : polar Q y (y' + z') = 0 := by
    rw [hc, polar_smul_right_eq, polar_add_right, hyy, hyz0, add_zero, mul_zero]
  have hw1 : polar Q y (y' + z') = polar Q y y' := by
    rw [polar_add_right, hM.frame.perp a m ham y hy z' hz', add_zero]
  exact hpy' (hw1 ▸ hw0)

theorem exists_rootSet_supportedFixed (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) (hd : IsStdElt p A d) {k : Fin l} (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U k))
    {a m : Fin l} (hak : a ≠ k) (hmk : m ≠ k) (ham : a ≠ m) {y z : V} (hy : y ∈ U a) (hz : z ∈ U m) (hy0 : y ≠ 0)
    (hQyz : Q y = Q z) :
    ∃ w ∈ rootSet Q (supportedFixedDerived Q (d : V ≃ₗ[F] V)) (y + z), w ∈ U a ⊔ U m ∧
      ∀ c : F, w ≠ c • (y + z) := by
  have hQy0 : Q y ≠ 0 := fun h0 =>
    hy0 (eq_zero_of_map_eq_zero_of_mem_plane hM.frame.toIsPlaneSystem a hy h0)
  have hz0 : z ≠ 0 := fun h0 => hQy0 (by rw [hQyz, h0, map_zero])
  obtain ⟨y', hy', hpy'⟩ :=
    (T173U.polarNondegOn_of_nondegenerate (hM.frame.nondeg a)).exists_polar_ne_zero hy hy0
  obtain ⟨z₁, hz₁, hpz₁⟩ :=
    (T173U.polarNondegOn_of_nondegenerate (hM.frame.nondeg m)).exists_polar_ne_zero hz hz0
  obtain ⟨z', hz', hpzz'⟩ : ∃ z' ∈ U m, polar Q z z' = polar Q y y' := by
    refine ⟨(polar Q y y' / polar Q z z₁) • z₁, Submodule.smul_mem _ _ hz₁, ?_⟩
    rw [polar_smul_right_eq, div_mul_cancel₀ _ hpz₁]
  refine ⟨y' + z', mem_rootSet.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · have h1 : polar Q y z' = 0 := hM.frame.perp a m ham y hy z' hz'
    have h2 : polar Q z y' = 0 := hM.frame.perp m a (Ne.symm ham) z hz y' hy'
    rw [polar_add_left, polar_add_right, polar_add_right, h1, h2, hpzz']
    simp only [add_zero, zero_add]
    exact CharTwo.add_self_eq_zero _
  · have hufix : y + z ∈ fixedSpace (d : V ≃ₗ[F] V) := by
      rw [hfs, mem_polarPerp_iff]
      intro s hs
      rw [polar_add_right, hM.frame.perp k a (Ne.symm hak) s hs y hy,
        hM.frame.perp k m (Ne.symm hmk) s hs z hz, add_zero]
    have hwfix : y' + z' ∈ fixedSpace (d : V ≃ₗ[F] V) := by
      rw [hfs, mem_polarPerp_iff]
      intro s hs
      rw [polar_add_right, hM.frame.perp k a (Ne.symm hak) s hs y' hy',
        hM.frame.perp k m (Ne.symm hmk) s hs z' hz', add_zero]
    have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) := oddOrderIsometry_of_std hQ hp hp2 hd
    have hm : 3 ≤ l - 1 := by omega
    have hdimfs : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) = 2 * (l - 1) := by
      rw [hfs, finrank_polarPerp hQ (U k), hM.frame.finrank_eq k, hdim]
      omega
    have hmem : eichler Q (y + z) (y' + z') ∈
        eichlerGroupOn Q (fixedSpace (d : V ≃ₗ[F] V)) :=
      eichler_mem_eichlerGroupOn hufix hwfix
    exact T173U.eichlerGroupOn_fixedSpace_le_supportedFixedDerived hx hm hdimfs hmem
  · exact Submodule.add_mem _ (Submodule.mem_sup_left hy') (Submodule.mem_sup_right hz')
  · exact exists_rootSet_supportedFixed_aux1 hM ham hy hz hy' hz' hpy'

theorem stdVanishes_of_rootSet (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) {a m : Fin l} (ha : a = i ∨ a = j) (hmi : m ≠ i) (hmj : m ≠ j) {K : Subgroup (V ≃ₗ[F] V)}
    (hKl : ∀ g ∈ K, ∃ g' ∈ stdLayer d, (g' : V ≃ₗ[F] V) = g)
    (hK : ∀ y ∈ U a, ∀ z ∈ U m, y ≠ 0 → Q y = Q z →
      ∃ w ∈ rootSet Q K (y + z), w ∈ U a ⊔ U m ∧ ∀ c : F, w ≠ c • (y + z)) :
    StdVanishes A d := by
  rintro ⟨T, hT0, hT2, hle⟩
  obtain ⟨W, hW0, hWTS, hWinv⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T173S.exists_invariant_totallySingular_of_normalizes hQ hdim hl hT2 hT0 hle
  have hWA : ∀ a ∈ A, ∀ x ∈ W, (a : V ≃ₗ[F] V) x ∈ W := fun a ha => hWinv a (Subgroup.mem_sup_right ha)
  have hWK : ∀ g ∈ K, ∀ x ∈ W, g x ∈ W := by
    intro g hg x hx
    obtain ⟨g', hg', rfl⟩ := hKl g hg
    exact hWinv g' (Subgroup.mem_sup_left (le_closureIn_self _ _ hg')) x hx
  have hWij := le_sup_of_invariant_totallySingular hp hp2 hM.frame hM.iSup_eq_top
    (fun k hki hkj => hM.rho_mem hki hkj) hWTS hWA
  exact hW0 (eq_bot_of_rootSet hM ha hmi hmj hK hWTS hWij hWK)

theorem stdVanishes_of_fullSupport (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d) {h : Polynomial F}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ k, U k ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    (hL : stdLayer d = (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hquasi : CFSG.IsQuasisimple ↥(specialBlock Q (d : V ≃ₗ[F] V) h)) : StdVanishes A d := by
  obtain ⟨m, hmi, hmj, -⟩ := exists_fin_ne_three hl i j j
  have hle := CFSG.LocalAnalysis.GLTheoremA.T173U.specialBlock_le_orthDerived hquasi.1
  refine stdVanishes_of_rootSet hM hQ hdim hl hp hp2 (Or.inl rfl) hmi hmj (K := specialBlock Q (d : V ≃ₗ[F] V) h)
    (fun g hg => ⟨⟨g, hle hg⟩, by rw [hL]; exact Subgroup.mem_subgroupOf.2 hg, rfl⟩) ?_
  intro y hy z hz hy0 hQyz
  exact exists_rootSet_specialBlock hM hp hp2 hpq hd hh hh1 hU (Ne.symm hmi) hy hz hy0 hQyz

theorem stdVanishes_of_weightOne (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime)
    (hp2 : p ≠ 2) (hd : IsStdElt p A d) {k : Fin l} (hki : k ≠ i) (hkj : k ≠ j)
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U k))
    (hL : stdLayer d = (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) : StdVanishes A d := by
  obtain ⟨m, hmi, hmj, hmk⟩ := exists_fin_ne_three hl i j k
  have hx := oddOrderIsometry_of_std hQ hp hp2 hd
  have hle := hx.supportedFixedDerived_le_orthDerived
  refine stdVanishes_of_rootSet hM hQ hdim hl hp hp2 (Or.inl rfl) hmi hmj
    (K := supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (fun g hg => ⟨⟨g, hle hg⟩, by rw [hL]; exact Subgroup.mem_subgroupOf.2 hg, rfl⟩) ?_
  intro y hy z hz hy0 hQyz
  exact exists_rootSet_supportedFixed hM hQ hdim hl hp hp2 hd hfs (Ne.symm hki) hmk (Ne.symm hmi) hy hz hy0 hQyz

end CFSG.LocalAnalysis.GLTheoremA.T173M

end
