module

public import CFSG.LieType.SeitzGeneration.OrthCenter
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityMixing
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts

public section

namespace CFSG.LieType.SeitzGeneration

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitaryMixing
open CFSG.RankThree.Classical2 (orthDerived)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}
  {E : Subgroup (orthDerived Q)}

section Stable

theorem orthDerived_mem_orthogonalGroup {g : orthDerived Q} :
    (g : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  orthDerived_le_orthogonalGroup g.2

theorem apply_eq_of_mem_planeFixSpace (y : E) {u : V} (hu : u ∈ planeFixSpace E) :
    ((y : orthDerived Q) : V ≃ₗ[K] V) u = u :=
  hu _ ⟨(y : orthDerived Q), y.2, rfl⟩

theorem apply_eq_of_mem_lineFixSpace {M : Subgroup E} (m : M) {u : V} (hu : u ∈ lineFixSpace M) :
    (((m : E) : orthDerived Q) : V ≃ₗ[K] V) u = u :=
  hu _ ⟨((m : E) : orthDerived Q), ⟨(m : E), m.2, rfl⟩, rfl⟩

theorem lineSpace_stable (hE : ∀ x y : E, x * y = y * x) (M : Subgroup E) (y : E) {s : V}
    (hs : s ∈ lineSpace M) : ((y : orthDerived Q) : V ≃ₗ[K] V) s ∈ lineSpace M := by
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨g', ⟨m, hm, rfl⟩, rfl⟩ := hg
    have hcomm : ((m : E) : orthDerived Q) * (y : orthDerived Q) =
        (y : orthDerived Q) * ((m : E) : orthDerived Q) :=
      congrArg Subtype.val (hE (m : E) y)
    have h1 : (((m : E) : orthDerived Q) : V ≃ₗ[K] V) s = s :=
      apply_eq_of_mem_lineFixSpace (E := E) ⟨m, hm⟩ hs.1
    change (((m : E) : orthDerived Q) : V ≃ₗ[K] V)
      (((y : orthDerived Q) : V ≃ₗ[K] V) s) = ((y : orthDerived Q) : V ≃ₗ[K] V) s
    rw [← LinearEquiv.mul_apply]
    have : (((m : E) : orthDerived Q) : V ≃ₗ[K] V) * ((y : orthDerived Q) : V ≃ₗ[K] V) =
        ((y : orthDerived Q) : V ≃ₗ[K] V) * (((m : E) : orthDerived Q) : V ≃ₗ[K] V) :=
      congrArg (fun z : orthDerived Q => (z : V ≃ₗ[K] V)) hcomm
    rw [this, LinearEquiv.mul_apply, h1]
  · rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hyu : ((y : orthDerived Q) : V ≃ₗ[K] V) u = u := apply_eq_of_mem_planeFixSpace y hu
    have h3 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
      (orthDerived_mem_orthogonalGroup (Q := Q) (g := (y : orthDerived Q))) u s
    rw [hyu] at h3
    have h4 : (polarBilin Q) u s = 0 := hs.2 u hu
    change (polarBilin Q) u (((y : orthDerived Q) : V ≃ₗ[K] V) s) = 0
    rw [polarBilin_apply_apply] at h4 ⊢
    rw [h3]
    exact h4

end Stable

section Decomp

variable [FiniteDimensional K V]

theorem isCompl_planeFixSpace (hK : KernelLineData Q p E) :
    IsCompl (planeFixSpace E) (LinearMap.BilinForm.orthogonal (polarBilin Q) (planeFixSpace E)) :=
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (QuadraticMap.isSymm_polarBilin Q).isRefl (hK.regular none)

theorem lineFixSpace_le_sup (hK : KernelLineData Q p E) (M : Subgroup E) :
    lineFixSpace M ≤ planeFixSpace E ⊔ lineSpace M := by
  intro v hv
  obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Submodule.mem_sup.1
    ((isCompl_planeFixSpace hK).sup_eq_top ▸ Submodule.mem_top (x := v))
  refine Submodule.add_mem_sup hv₀ ⟨?_, hv₁⟩
  have : v₁ = (v₀ + v₁) - v₀ := by abel
  rw [this]
  exact (lineFixSpace M).sub_mem hv (planeFixSpace_le_lineFixSpace M hv₀)

omit [FiniteDimensional K V] in
theorem disjoint_lineSpace_sup (hK : KernelLineData Q p E) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N) :
    Disjoint (lineSpace L) (planeFixSpace E ⊔ lineSpace N) := by
  classical
  have hind := hK.internal.submodule_iSupIndep
  have h1 := hind (some ⟨L, hL⟩)
  refine h1.mono_right (sup_le ?_ ?_)
  · exact le_iSup₂_of_le none (by simp) le_rfl
  · have hne : (some ⟨N, hN⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ some ⟨L, hL⟩ :=
      fun h' => hLN (congrArg Subtype.val (Option.some.inj h')).symm
    exact le_iSup₂_of_le (some ⟨N, hN⟩) hne le_rfl

theorem eq_zero_of_fixed_lineSpace (hK : KernelLineData Q p E) (hp : p.Prime) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N) {t : N} (ht : t ≠ 1) {v : V}
    (hv : v ∈ lineSpace L) (hfix : (((t : E) : orthDerived Q) : V ≃ₗ[K] V) v = v) : v = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  let S : Subgroup N :=
    { carrier := {n | (((n : E) : orthDerived Q) : V ≃ₗ[K] V) v = v}
      mul_mem' := fun {a b} ha hb => by
        change (((a : E) * (b : E) : E) : orthDerived Q).1 v = v
        have : ((((a : E) * (b : E) : E) : orthDerived Q) : V ≃ₗ[K] V) =
            (((a : E) : orthDerived Q) : V ≃ₗ[K] V) * (((b : E) : orthDerived Q) : V ≃ₗ[K] V) :=
          rfl
        rw [this, LinearEquiv.mul_apply, hb, ha]
      one_mem' := rfl
      inv_mem' := fun {a} ha => by
        change ((((a : E)⁻¹ : E) : orthDerived Q) : V ≃ₗ[K] V) v = v
        have : (((a : E)⁻¹ : E) : orthDerived Q) = ((a : E) : orthDerived Q)⁻¹ := rfl
        rw [this]
        exact (LinearEquiv.symm_apply_eq _).mpr ha.symm }
  have hSN : ∀ n : N, n ∈ S := fun n => by
    have := mem_zpowers_of_prime_card hN ht (g' := n)
    exact (Subgroup.zpowers_le.mpr (show t ∈ S from hfix)) this
  have hvN : v ∈ lineFixSpace N := fun g hg => by
    obtain ⟨g', ⟨m, hm, rfl⟩, rfl⟩ := hg
    exact hSN ⟨m, hm⟩
  exact Submodule.disjoint_def.mp (disjoint_lineSpace_sup hK hL hN hLN) v hv
    (lineFixSpace_le_sup hK N hvN)

end Decomp

section Factors

variable [Finite K] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem oddOrderIsometry_of_mem (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hpl : p ≠ ringChar K) (hK : KernelLineData Q p E) {x : E} (hx : x ≠ 1) :
    OddOrderIsometry Q p (((x : E) : orthDerived Q) : V ≃ₗ[K] V) := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf ((x : E) : orthDerived Q) = p := by
    refine orderOf_eq_prime ?_ ?_
    · have := congrArg (fun z : E => (z : orthDerived Q)) (hK.exp x)
      simpa using this
    · intro h
      exact hx (Subtype.ext h)
  exact oddOrderIsometry_of_orthDerived hp hpl hQ _ hord

theorem exists_factor_of_line (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hpl : p ≠ ringChar K) (hK : KernelLineData Q p E) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N) {t : N} (ht : t ≠ 1)
    (hVL : lineSpace L ≠ ⊥) :
    ∃ g ∈ primaryFactors (((t : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap, g ≠ X - 1 ∧
      ∃ v ∈ lineSpace L, v ∈ primaryComponent
        (((t : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap g ∧ v ≠ 0 := by
  have ht' : (t : E) ≠ 1 := fun h => ht (Subtype.ext h)
  have hx := oddOrderIsometry_of_mem hQ hp hpl hK ht'
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVL
  obtain ⟨g, hg, v, hvL, hvg, hv0⟩ := exists_primaryFactor_mem hx.squarefree_minpoly
    (S := lineSpace L) (fun s hs => lineSpace_stable hK.comm L (t : E) hs) hv₀ hv₀0
  refine ⟨g, hg, ?_, v, hvL, hvg, hv0⟩
  rintro rfl
  have hfix : (((t : E) : orthDerived Q) : V ≃ₗ[K] V) v = v := by
    have := mem_primaryComponent.mp hvg
    simpa [sub_eq_zero] using this
  exact hv0 (eq_zero_of_fixed_lineSpace hK hp hL hN hLN ht hvL hfix)

theorem inf_eq_bot_of_card_prime' {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {L N : Subgroup G} (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N) :
    L ⊓ N = ⊥ := by
  have hd : Nat.card ↥(L ⊓ N) ∣ p := hL ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hd with h1 | h1
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have e1 : L ⊓ N = L := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hL])
    have e2 : L ⊓ N = N := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hN])
    exact hLN (e1.symm.trans e2)

theorem exists_mixing_factor_orth (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hpl : p ≠ ringChar K) (hK : KernelLineData Q p E) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N) (hVL : lineSpace L ≠ ⊥)
    (hVN : lineSpace N ≠ ⊥) :
    ∃ a : E, a ≠ 1 ∧
      ∃ h ∈ primaryFactors (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 ∧
        2 ≤ primaryMultiplicity (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap h ∧
        (∃ v ∈ lineSpace L, v ∈ primaryComponent
          (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap h ∧ v ≠ 0) ∧
        (∃ w ∈ lineSpace N, w ∈ primaryComponent
          (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap h ∧ w ≠ 0) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hK.card]; exact pow_ne_zero 2 hp.ne_zero)
  have hLne : L ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hL
    exact hp.one_lt.ne' hL.symm
  have hNne : N ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hN
    exact hp.one_lt.ne' hN.symm
  obtain ⟨tL, htL1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hLne
  obtain ⟨tN, htN1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hNne
  have htL1' : (tL : E) ≠ 1 := fun h => htL1 (Subtype.ext h)
  have htN1' : (tN : E) ≠ 1 := fun h => htN1 (Subtype.ext h)
  obtain ⟨f₁, hf₁, hf₁1, v, hvL, hvf, hv0⟩ :=
    exists_factor_of_line hQ hp hpl hK hL hN hLN htN1 hVL
  obtain ⟨g₁, hg₁, hg₁1, w, hwN, hwg, hw0⟩ :=
    exists_factor_of_line hQ hp hpl hK hN hL hLN.symm htL1 hVN
  have hxN := oddOrderIsometry_of_mem hQ hp hpl hK htN1'
  have hxL := oddOrderIsometry_of_mem hQ hp hpl hK htL1'
  have hfd := hxN.dvd_X_pow_sub_one hf₁
  have hgd := hxL.dvd_X_pow_sub_one hg₁
  have hfmon := monic_of_mem_primaryFactors hf₁
  have hfirr := irreducible_of_mem_primaryFactors hf₁
  have hX : (X - 1 : K[X]) = X - C 1 := by rw [map_one]
  obtain ⟨j, hj0, hjp, hdvd⟩ := exists_pow_dvd_comp hp hfmon hfirr hfd (by rwa [← hX])
    (monic_of_mem_primaryFactors hg₁) (irreducible_of_mem_primaryFactors hg₁) hgd
    (by rwa [← hX])
  obtain ⟨a, ha⟩ : ∃ a : E, a = (tL : E) ^ j * (tN : E) := ⟨_, rfl⟩
  have hLj : (tL : E) ^ j ∈ L := L.pow_mem tL.2 j
  have hcoe : ∀ s : V, (((a : E) : orthDerived Q) : V ≃ₗ[K] V) s =
      ((((tL : E) ^ j : E) : orthDerived Q) : V ≃ₗ[K] V)
        ((((tN : E) : orthDerived Q) : V ≃ₗ[K] V) s) := fun s => by
    rw [ha]
    rfl
  have hLfix : ∀ s' ∈ lineFixSpace L,
      ((((tL : E) ^ j : E) : orthDerived Q) : V ≃ₗ[K] V) s' = s' := fun s' hs' =>
    apply_eq_of_mem_lineFixSpace (E := E) (⟨(tL : E) ^ j, hLj⟩ : L) hs'
  have hNfix : ∀ s' ∈ lineFixSpace N, (((tN : E) : orthDerived Q) : V ≃ₗ[K] V) s' = s' :=
    fun s' hs' => apply_eq_of_mem_lineFixSpace (E := E) tN hs'
  have hpowL : ((((tL : E) ^ j : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap =
      ((((tL : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap) ^ j := by
    have := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V))
      (((tL : E) : orthDerived Q) : V ≃ₗ[K] V) j
    exact this
  have hTL : ∀ s ∈ lineSpace L, (((a : E) : orthDerived Q) : V ≃ₗ[K] V) s =
      (((tN : E) : orthDerived Q) : V ≃ₗ[K] V) s := fun s hs => by
    rw [hcoe]
    exact hLfix _ (lineSpace_le_lineFixSpace L (lineSpace_stable hK.comm L (tN : E) hs))
  have hTN : ∀ s ∈ lineSpace N, (((a : E) : orthDerived Q) : V ≃ₗ[K] V) s =
      ((((tL : E) ^ j : E) : orthDerived Q) : V ≃ₗ[K] V) s := fun s hs => by
    rw [hcoe, hNfix s (lineSpace_le_lineFixSpace N hs)]
  have hfv : aeval (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap f₁ v = 0 := by
    rw [aeval_apply_eq_of_agree (T₂ := (((tN : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap)
      (S := lineSpace L) (fun s hs => lineSpace_stable hK.comm L (tN : E) hs) hTL f₁ hvL]
    exact mem_primaryComponent.mp hvf
  have hfw : aeval (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap f₁ w = 0 := by
    rw [aeval_apply_eq_of_agree
      (T₂ := ((((tL : E) ^ j : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap)
      (S := lineSpace N)
      (fun s hs => lineSpace_stable hK.comm N ((tL : E) ^ j) hs) hTN f₁ hwN, hpowL]
    have hcomp : aeval ((((tL : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap) (f₁.comp (X ^ j)) =
        aeval ((((tL : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap ^ j) f₁ := by
      rw [Polynomial.aeval_comp, aeval_X_pow]
    obtain ⟨q, hq⟩ := hdvd
    rw [← hcomp, hq, mul_comm, map_mul, Module.End.mul_apply, mem_primaryComponent.mp hwg,
      map_zero]
  have hmem : f₁ ∈ primaryFactors
      (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap :=
    mem_primaryFactors_of_apply_eq_zero hfirr hfmon hfv hv0
  have : Fact (Irreducible f₁) := ⟨hfirr⟩
  have hdisj : Disjoint (lineSpace L) (lineSpace N) :=
    (disjoint_lineSpace_sup hK hL hN hLN).mono_right le_sup_right
  have hm2 : 2 ≤ primaryMultiplicity (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap f₁ :=
    two_le_primaryMultiplicity (a := f₁) (S₁ := lineSpace L) (S₂ := lineSpace N)
      (fun s hs => lineSpace_stable hK.comm L a hs) (fun s hs => lineSpace_stable hK.comm N a hs)
      hdisj hvL hwN (mem_primaryComponent.mpr hfv) (mem_primaryComponent.mpr hfw) hv0 hw0
  have ha1 : a ≠ 1 := by
    intro h1
    apply htN1'
    have h2 : (tN : E) = ((tL : E) ^ j)⁻¹ := by
      rw [ha] at h1
      exact eq_inv_of_mul_eq_one_right h1
    have h3 : (tN : E) ∈ L ⊓ N := ⟨h2 ▸ L.inv_mem hLj, tN.2⟩
    rw [inf_eq_bot_of_card_prime' hp hL hN hLN] at h3
    exact Subgroup.mem_bot.mp h3
  exact ⟨a, ha1, f₁, hmem, hf₁1, hm2, ⟨v, hvL, mem_primaryComponent.mpr hfv, hv0⟩,
    ⟨w, hwN, mem_primaryComponent.mpr hfw, hw0⟩⟩

end Factors

end CFSG.LieType.SeitzGeneration
