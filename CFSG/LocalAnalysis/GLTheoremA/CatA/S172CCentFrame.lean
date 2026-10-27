module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal CFSG.Open
  CFSG.GroupTheory.WeirSylow

section Perp

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def polarPerp (Q : QuadraticForm F V) (W : Submodule F V) : Submodule F V :=
  LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W

variable {Q : QuadraticForm F V} {W : Submodule F V}

theorem mem_polarPerp_iff {x : V} : x ∈ polarPerp Q W ↔ ∀ y ∈ W, QuadraticMap.polar Q y x = 0 := by
  simp only [polarPerp, LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.IsOrtho,
    QuadraticMap.polarBilin_apply_apply]

theorem isRefl_polarBilin (Q : QuadraticForm F V) : (QuadraticMap.polarBilin Q).IsRefl := by
  intro x y h
  rw [QuadraticMap.polarBilin_apply_apply] at h ⊢
  rw [QuadraticMap.polar_comm]
  exact h

theorem polar_comp_subtype_cent (Q : QuadraticForm F V) (W : Submodule F V) (x y : W) :
    QuadraticMap.polar (Q.comp W.subtype) x y = QuadraticMap.polar Q (x : V) (y : V) := by
  simp [QuadraticMap.polar, QuadraticMap.comp_apply]

theorem polarBilin_comp_subtype_cent (Q : QuadraticForm F V) (W : Submodule F V) :
    QuadraticMap.polarBilin (Q.comp W.subtype) =
      LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) W := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  simp [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent]

theorem isCompl_polarPerp [FiniteDimensional F V] {W : Submodule F V}
    (hW : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate) :
    IsCompl W (polarPerp Q W) := by
  rw [polarBilin_comp_subtype_cent] at hW
  exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate (isRefl_polarBilin Q) hW

theorem finrank_polarPerp [FiniteDimensional F V] (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (W : Submodule F V) : Module.finrank F (polarPerp Q W) = Module.finrank F V - Module.finrank F W :=
  LinearMap.BilinForm.finrank_orthogonal hQ W

theorem exists_ne_zero_mem_of_finrank_eq_two [FiniteDimensional F V] (W : Submodule F V)
    (h : Module.finrank F W = 2) : ∃ v ∈ W, v ≠ 0 := by
  have hpos : 0 < Module.finrank F W := by omega
  obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  exact ⟨v, hv, fun h0 => hv0 (Subtype.ext h0)⟩

end Perp

section Frame

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]

structure IsPlaneSystem (Q : QuadraticForm F V) {m : ℕ} (U : Fin m → Submodule F V) : Prop where
  finrank_eq : ∀ j, Module.finrank F (U j) = 2
  nondeg : ∀ j, (QuadraticMap.polarBilin (Q.comp (U j).subtype)).Nondegenerate
  not_isPlusType : ∀ j, ¬ IsPlusType (Q.comp (U j).subtype)
  perp : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, QuadraticMap.polar Q x y = 0

structure IsPlaneFrame (Q : QuadraticForm F V) (p : ℕ) {m : ℕ} (U : Fin m → Submodule F V)
    (e : Fin m → ↥(orthDerived Q)) (Bb : Subgroup ↥(orthDerived Q)) : Prop
    extends IsPlaneSystem Q U where
  orderOf_eq : ∀ j, orderOf (e j) = p
  apply_of_perp : ∀ j, ∀ x ∈ polarPerp Q (U j), (e j : V ≃ₗ[F] V) x = x
  maps_to : ∀ j, ∀ x ∈ U j, (e j : V ≃ₗ[F] V) x ∈ U j
  eq_zero_of_apply_eq : ∀ j, ∀ x ∈ U j, (e j : V ≃ₗ[F] V) x = x → x = 0
  isElemAbelian : IsElemAbelian p Bb
  closure_eq : Subgroup.closure (Set.range e) = Bb

end Frame

section Calculus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {m : ℕ} {U : Fin m → Submodule F V}
  {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}

theorem IsPlaneFrame.exists_pow_apply_eq (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (j : Fin m) :
    ∃ k : ℕ, ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = ((e j : V ≃ₗ[F] V) ^ k) x := by
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hp0 : 0 < p := hF.orderOf_eq j ▸ orderOf_pos (e j)
  have hpow : ∀ (k : ℕ), ∀ x ∈ U j, ((e j : V ≃ₗ[F] V) ^ k) x ∈ U j := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ, LinearEquiv.mul_apply]
      exact ih _ (hF.maps_to j x hx)
  have hep : (e j : V ≃ₗ[F] V) ^ p = 1 := by
    have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hF.orderOf_eq j ▸ pow_orderOf_eq_one (e j))
    simpa using this
  rw [← hF.closure_eq] at hd
  induction hd using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    by_cases hij : i = j
    · subst hij
      exact ⟨1, fun x _ => by simp⟩
    · refine ⟨0, fun x hx => ?_⟩
      have hx' : x ∈ polarPerp Q (U i) := mem_polarPerp_iff.2 fun y hy => by
        rw [QuadraticMap.polar_comm]
        exact hF.perp j i (fun h => hij h.symm) x hx y hy
      simpa using hF.apply_of_perp i x hx'
  | one => exact ⟨0, fun x _ => rfl⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k₁, h₁⟩ := ha
    obtain ⟨k₂, h₂⟩ := hb
    refine ⟨k₁ + k₂, fun x hx => ?_⟩
    show (a : V ≃ₗ[F] V) ((b : V ≃ₗ[F] V) x) = _
    rw [h₂ x hx, h₁ _ (hpow k₂ x hx), pow_add, LinearEquiv.mul_apply]
  | inv a _ ha =>
    obtain ⟨k, hk⟩ := ha
    refine ⟨(p - 1) * k, fun y hy => ?_⟩
    show ((a : V ≃ₗ[F] V)⁻¹) y = _
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    rw [hk _ (hpow _ y hy), ← LinearEquiv.mul_apply, ← pow_add]
    have : k + (p - 1) * k = p * k := by
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      simp [Nat.add_mul]
      ring
    rw [this, pow_mul, hep, one_pow]
    rfl

theorem IsPlaneFrame.apply_eq_or_eq_zero (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (j : Fin m) :
    (∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x) ∨
      ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x → x = 0 := by
  obtain ⟨k, hk⟩ := hF.exists_pow_apply_eq hd j
  set ρ : V ≃ₗ[F] V := (e j : V ≃ₗ[F] V) with hρ
  have hep : ρ ^ p = 1 := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hF.orderOf_eq j ▸ pow_orderOf_eq_one (e j))
    simpa [hρ] using h
  have hk' : ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = (ρ ^ k) x := by
    intro x hx
    rw [hk x hx, hρ]
  by_cases hpk : p ∣ k
  · left
    intro x hx
    rw [hk' x hx]
    obtain ⟨t, rfl⟩ := hpk
    rw [pow_mul, hep, one_pow]
    rfl
  · right
    intro x hx hdx
    have hkx : (ρ ^ k) x = x := (hk' x hx).symm.trans hdx
    have hcop : Nat.Coprime k p := ((hp.coprime_iff_not_dvd).2 hpk).symm
    obtain ⟨n, -, hn⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hkm : ρ ^ (k * n) = ρ := by
      rw [pow_eq_pow_mod (k * n) hep, hn, pow_one]
    have hfixpow : ∀ t : ℕ, ((ρ ^ k) ^ t) x = x := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hkx]
    have hfix : (ρ ^ (k * n)) x = x := by
      rw [pow_mul]
      exact hfixpow n
    rw [hkm, hρ] at hfix
    exact hF.eq_zero_of_apply_eq j x hx hfix

theorem IsPlaneSystem.biSup_le_polarPerp (hF : IsPlaneSystem Q U) {a : Fin m} {s : Finset (Fin m)}
    (ha : a ∉ s) : (⨆ j ∈ s, U j) ≤ polarPerp Q (U a) :=
  iSup₂_le fun j hj _ hx => mem_polarPerp_iff.2 fun _ hy => hF.perp a j (fun h => ha (h ▸ hj)) _ hy _ hx

private theorem IsPlaneSystem.nondeg_biSup_aux1 {A B : Submodule F V}
    (hA : (QuadraticMap.polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (QuadraticMap.polarBilin (Q.comp B.subtype)).Nondegenerate)
    (hAB : B ≤ polarPerp Q A) :
    (QuadraticMap.polarBilin (Q.comp (A ⊔ B).subtype)).Nondegenerate := by
  refine ((isRefl_polarBilin (Q.comp (A ⊔ B).subtype)).nondegenerate_iff_separatingLeft).2 ?_
  intro x hx
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 x.2
  have hu0 : u = 0 := by
    have h0 : (⟨u, hu⟩ : ↥A) = 0 := hA.1 ⟨u, hu⟩ (fun y => by
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent]
      have hxy := hx ⟨(y : V), Submodule.mem_sup_left y.2⟩
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent, ← huv,
        polar_add_left] at hxy
      have hvy : QuadraticMap.polar Q v (y : V) = 0 := by
        rw [QuadraticMap.polar_comm]
        exact mem_polarPerp_iff.1 (hAB hv) (y : V) y.2
      rw [hvy, add_zero] at hxy
      exact hxy)
    exact Subtype.ext_iff.mp h0
  have hv0 : v = 0 := by
    have h0 : (⟨v, hv⟩ : ↥B) = 0 := hB.1 ⟨v, hv⟩ (fun y => by
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent]
      have hxy := hx ⟨(y : V), Submodule.mem_sup_right y.2⟩
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent, ← huv,
        polar_add_left] at hxy
      have huy : QuadraticMap.polar Q u (y : V) = 0 :=
        mem_polarPerp_iff.1 (hAB y.2) u hu
      rw [huy, zero_add] at hxy
      exact hxy)
    exact Subtype.ext_iff.mp h0
  apply Subtype.ext
  rw [← huv, hu0, hv0, add_zero]
  rfl

theorem IsPlaneSystem.nondeg_biSup (hF : IsPlaneSystem Q U) (s : Finset (Fin m)) :
    (QuadraticMap.polarBilin (Q.comp (⨆ j ∈ s, U j).subtype)).Nondegenerate := by
  induction s using Finset.induction_on with
  | empty =>
    have hbot : (⨆ j ∈ (∅ : Finset (Fin m)), U j) = ⊥ := by simp
    rw [hbot]
    exact ⟨fun x _ => Submodule.eq_zero_of_bot_submodule x,
      fun x _ => Submodule.eq_zero_of_bot_submodule x⟩
  | insert a s ha ih =>
    rw [Finset.iSup_insert]
    exact IsPlaneSystem.nondeg_biSup_aux1 (Q := Q) (hF.nondeg a) ih (hF.biSup_le_polarPerp ha)

theorem IsPlaneSystem.disjoint_biSup (hF : IsPlaneSystem Q U) {a : Fin m} {s : Finset (Fin m)}
    (ha : a ∉ s) : Disjoint (U a) (⨆ j ∈ s, U j) :=
  (isCompl_polarPerp (hF.nondeg a)).disjoint.mono_right (hF.biSup_le_polarPerp ha)

theorem IsPlaneSystem.finrank_biSup (hF : IsPlaneSystem Q U) (s : Finset (Fin m)) :
    Module.finrank F (⨆ j ∈ s, U j : Submodule F V) = 2 * s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.card_insert_of_notMem ha]
    have h := Submodule.finrank_sup_add_finrank_inf_eq (U a) (⨆ j ∈ s, U j)
    rw [disjoint_iff.1 (hF.disjoint_biSup ha), finrank_bot, add_zero, ih, hF.finrank_eq a] at h
    omega

theorem IsPlaneSystem.isCompl_iSup (hF : IsPlaneSystem Q U) :
    IsCompl (⨆ j, U j) (polarPerp Q (⨆ j, U j)) := by
  have h := isCompl_polarPerp (hF.nondeg_biSup Finset.univ)
  simpa using h

theorem IsPlaneSystem.eq_one_of_apply_eq (hF : IsPlaneSystem Q U) {d : V ≃ₗ[F] V}
    (h : ∀ j, ∀ x ∈ U j, d x = x) (hperp : ∀ x ∈ polarPerp Q (⨆ j, U j), d x = x) : d = 1 := by
  have hall : ∀ x ∈ (⨆ j, U j), d x = x := by
    intro x hx
    refine Submodule.iSup_induction U (motive := fun x => d x = x) hx (fun j y hy => h j y hy)
      (map_zero _) ?_
    intro x y hx hy
    rw [map_add, hx, hy]
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ (⨆ j, U j) ⊔ polarPerp Q (⨆ j, U j) := by
    rw [hF.isCompl_iSup.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, hall a ha, hperp z hz]
  rfl

theorem IsPlaneFrame.apply_eq_of_mem_polarPerp_iSup (hF : IsPlaneFrame Q p U e Bb)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) {x : V} (hx : x ∈ polarPerp Q (⨆ j, U j)) :
    (d : V ≃ₗ[F] V) x = x := by
  rw [← hF.closure_eq] at hd
  induction hd using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, rfl⟩ := hg
    exact hF.apply_of_perp j x
      (mem_polarPerp_iff.2 fun y hy => mem_polarPerp_iff.1 hx y (le_iSup U j hy))
  | one => rfl
  | mul a b _ _ ha hb =>
    show (a : V ≃ₗ[F] V) ((b : V ≃ₗ[F] V) x) = x
    rw [hb, ha]
  | inv a _ ha =>
    show ((a : V ≃ₗ[F] V)⁻¹) x = x
    exact (LinearEquiv.symm_apply_eq _).2 ha.symm

theorem IsPlaneFrame.eq_one_of_forall_apply_eq (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (h : ∀ j, ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x) : d = 1 :=
  Subtype.ext (hF.toIsPlaneSystem.eq_one_of_apply_eq h fun _ hx =>
    hF.apply_eq_of_mem_polarPerp_iSup hd hx)

theorem IsPlaneFrame.apply_eq_of_mem_zpowers (hF : IsPlaneFrame Q p U e Bb) (hp : p.Prime)
    {d : ↥(orthDerived Q)} (hd : d ∈ Bb) {j : Fin m} (hj : e j ∈ Subgroup.zpowers d) :
    ∀ i, i ≠ j → ∀ x ∈ U i, (d : V ≃ₗ[F] V) x = x := by
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun f : V ≃ₗ[F] V => (f : V → V))
    fun f g h => LinearEquiv.ext (congrFun h)
  have hdp : d ^ p = 1 := hF.isElemAbelian.2 d hd
  have hd_ne : d ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hj
    have he1 : e j = 1 := by rw [← hk, h1, one_zpow]
    have h1p : (1 : ℕ) = p := by rw [← hF.orderOf_eq j, he1, orderOf_one]
    exact hp.ne_one h1p.symm
  have hord_d : orderOf d = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf d) (orderOf_dvd_iff_pow_eq_one.2 hdp) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hd_ne
    · exact h
  have hle : Subgroup.zpowers (e j) ≤ Subgroup.zpowers d := (Subgroup.zpowers_le).2 hj
  have hcard : Nat.card (Subgroup.zpowers d) ≤ Nat.card (Subgroup.zpowers (e j)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord_d, hF.orderOf_eq j]
  have heq : Subgroup.zpowers (e j) = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hd_mem : d ∈ Subgroup.zpowers (e j) := by rw [heq]; exact Subgroup.mem_zpowers d
  obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.1 hd_mem
  have hcoeeq : ((e j : V ≃ₗ[F] V)) ^ k' = (d : V ≃ₗ[F] V) := by
    simpa using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hk'
  intro i hij x hx
  have hxperp : x ∈ polarPerp Q (U j) := mem_polarPerp_iff.2 fun y hy => by
    rw [QuadraticMap.polar_comm]
    exact hF.perp i j hij x hx y hy
  have hρx : (e j : V ≃ₗ[F] V) x = x := hF.apply_of_perp j x hxperp
  have hstab : (e j : V ≃ₗ[F] V) ∈ MulAction.stabilizer (V ≃ₗ[F] V) x :=
    (MulAction.mem_stabilizer_iff).2 hρx
  have hmem : (d : V ≃ₗ[F] V) ∈ Subgroup.zpowers (e j : V ≃ₗ[F] V) := by
    rw [← hcoeeq]
    exact Subgroup.mem_zpowers_iff.2 ⟨k', rfl⟩
  exact (MulAction.mem_stabilizer_iff).1
    ((Subgroup.zpowers_le (H := MulAction.stabilizer (V ≃ₗ[F] V) x)).2 hstab hmem)

theorem IsPlaneFrame.fixedSpace_eq_polarPerp (hF : IsPlaneFrame Q p U e Bb) (j : Fin m) :
    fixedSpace (e j : V ≃ₗ[F] V) = polarPerp Q (U j) := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_fixedSpace.2 (hF.apply_of_perp j x hx))
  have hx' := mem_fixedSpace.1 hx
  have hx2 : x ∈ U j ⊔ polarPerp Q (U j) := by
    rw [(isCompl_polarPerp (hF.nondeg j)).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx2
  rw [map_add, hF.apply_of_perp j w hw] at hx'
  have hu' : (e j : V ≃ₗ[F] V) u = u := add_right_cancel hx'
  rw [hF.eq_zero_of_apply_eq j u hu hu', zero_add]
  exact hw

private theorem fixedSpace_eq_of_mem_zpowers_aux1 {x y : V ≃ₗ[F] V}
    (hy : y ∈ Subgroup.zpowers x) : fixedSpace x ≤ fixedSpace y := by
  intro v hv
  rw [mem_fixedSpace] at hv ⊢
  have hst : x ∈ MulAction.stabilizer (V ≃ₗ[F] V) v :=
    (MulAction.mem_stabilizer_iff).2 (by rwa [LinearEquiv.smul_def])
  have hy' : y ∈ MulAction.stabilizer (V ≃ₗ[F] V) v :=
    (Subgroup.zpowers_le (H := MulAction.stabilizer (V ≃ₗ[F] V) v)).2 hst hy
  rwa [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] at hy'

theorem fixedSpace_eq_of_mem_zpowers {x y : V ≃ₗ[F] V} (hp : p.Prime) (hxp : orderOf x = p)
    (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) : fixedSpace y = fixedSpace x := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine le_antisymm ?_ (fixedSpace_eq_of_mem_zpowers_aux1 hy)
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hyp : y ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← hk]
    have hxpf : x ^ (p : ℤ) = 1 := by
      rw [zpow_natCast]
      exact hxp ▸ pow_orderOf_eq_one x
    rw [← zpow_natCast (x ^ k) p, ← zpow_mul x k (p : ℤ), mul_comm k (p : ℤ),
      zpow_mul x (p : ℤ) k, hxpf, one_zpow]
  have hyorder : orderOf y = p := orderOf_eq_prime hyp hy1
  have hxmem : x ∈ Subgroup.zpowers y := by
    have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hy
    have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hyorder, hxp])
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact fixedSpace_eq_of_mem_zpowers_aux1 hxmem

theorem IsPlaneFrame.mem (hF : IsPlaneFrame Q p U e Bb) (j : Fin m) : e j ∈ Bb := by
  rw [← hF.closure_eq]
  exact Subgroup.subset_closure ⟨j, rfl⟩

private theorem IsPlaneFrame.mem_zpowers_of_apply_eq_aux1 (hF : IsPlaneFrame Q p U e Bb)
    (j : Fin m) : ∀ n : ℕ, ∀ x ∈ U j, ((e j : V ≃ₗ[F] V) ^ n) x ∈ U j := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, LinearEquiv.mul_apply]
    exact ih _ (hF.maps_to j x hx)

private theorem IsPlaneFrame.mem_zpowers_of_apply_eq_aux2 (hF : IsPlaneFrame Q p U e Bb)
    (j : Fin m) : (e j : V ≃ₗ[F] V) ^ p = 1 := by
  have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
    (hF.orderOf_eq j ▸ pow_orderOf_eq_one (e j))
  simpa using this

private theorem mem_zpowers_of_apply_eq_aux3 (hp : 0 < p) (k : ℕ) :
    k + (p - 1) * k = p * k := by
  have hp1 : 1 ≤ p := by omega
  calc k + (p - 1) * k = (p - 1) * k + k := Nat.add_comm _ _
    _ = (p - 1) * k + 1 * k := by rw [one_mul]
    _ = (p - 1 + 1) * k := (Nat.add_mul (p - 1) 1 k).symm
    _ = p * k := by rw [Nat.sub_add_cancel hp1]

theorem IsPlaneFrame.mem_zpowers_of_apply_eq (hF : IsPlaneFrame Q p U e Bb) {b : ↥(orthDerived Q)}
    (hb : b ∈ Bb) (j : Fin m)
    (h : ∀ i, i ≠ j → ∀ x ∈ U i, (b : V ≃ₗ[F] V) x = x) : b ∈ Subgroup.zpowers (e j) := by
  obtain ⟨k, hk⟩ := hF.exists_pow_apply_eq hb j
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hp0 : 0 < p := hF.orderOf_eq j ▸ orderOf_pos (e j)
  have hep : (e j : V ≃ₗ[F] V) ^ p = 1 := hF.mem_zpowers_of_apply_eq_aux2 j
  have hpow := hF.mem_zpowers_of_apply_eq_aux1 j
  let K : ℕ := (p - 1) * k
  have hkadd : k + K = p * k := by
    show k + (p - 1) * k = p * k
    exact mem_zpowers_of_apply_eq_aux3 hp0 k
  have hcoe : ((b * e j ^ K : ↥(orthDerived Q)) : V ≃ₗ[F] V)
      = (b : V ≃ₗ[F] V) * ((e j : V ≃ₗ[F] V) ^ K) := by
    simp [Subgroup.coe_mul, Subgroup.coe_pow]
  have hb'one : b * e j ^ K = 1 := by
    refine hF.eq_one_of_forall_apply_eq (Bb.mul_mem hb (pow_mem (hF.mem j) K)) ?_
    intro i x hx
    by_cases hij : i = j
    · subst hij
      rw [hcoe, LinearEquiv.mul_apply, hk _ (hpow K x hx), ← LinearEquiv.mul_apply,
        ← pow_add, hkadd, pow_mul, hep, one_pow]
      simp
    · have hxperp : x ∈ polarPerp Q (U j) := mem_polarPerp_iff.2 fun y hy =>
        hF.perp j i (fun hji => hij hji.symm) y hy x hx
      have hxfix : ((e j : V ≃ₗ[F] V) ^ K) x = x :=
        mem_fixedSpace.1 (fixedSpace_eq_of_mem_zpowers_aux1
          (Subgroup.npow_mem_zpowers (e j : V ≃ₗ[F] V) K)
          (mem_fixedSpace.2 (hF.apply_of_perp j x hxperp)))
      rw [hcoe, LinearEquiv.mul_apply, hxfix]
      exact h i hij x hx
  have hb_eq : b = (e j) ^ (-(K : ℤ)) := by
    have h1 : b = (e j ^ K)⁻¹ := by
      have hthis := congrArg (fun z : ↥(orthDerived Q) => z * (e j ^ K)⁻¹) hb'one
      simpa [mul_assoc] using hthis
    rw [h1, show (e j ^ K : ↥(orthDerived Q)) = (e j) ^ (K : ℤ) by rw [zpow_natCast]]
    exact (zpow_neg (e j) (K : ℤ)).symm
  exact Subgroup.mem_zpowers_iff.2 ⟨-(K : ℤ), hb_eq.symm⟩

theorem IsPlaneFrame.exists_mul_zpow_apply (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (j : Fin m) :
    ∃ k : ℤ, (∀ v ∈ U j, ((d * e j ^ k : ↥(orthDerived Q)) : V ≃ₗ[F] V) v = v) ∧
      ∀ i, i ≠ j → ∀ v ∈ U i,
        ((d * e j ^ k : ↥(orthDerived Q)) : V ≃ₗ[F] V) v = (d : V ≃ₗ[F] V) v := by
  obtain ⟨k₀, hk₀⟩ := hF.exists_pow_apply_eq hd j
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hp0 : 0 < p := hF.orderOf_eq j ▸ orderOf_pos (e j)
  have hep : (e j : V ≃ₗ[F] V) ^ p = 1 := hF.mem_zpowers_of_apply_eq_aux2 j
  have hpow := hF.mem_zpowers_of_apply_eq_aux1 j
  let K : ℕ := (p - 1) * k₀
  have hkadd : k₀ + K = p * k₀ := by
    show k₀ + (p - 1) * k₀ = p * k₀
    exact mem_zpowers_of_apply_eq_aux3 hp0 k₀
  have hcoe : ((d * e j ^ (K : ℤ) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
      = (d : V ≃ₗ[F] V) * ((e j : V ≃ₗ[F] V) ^ K) := by
    simp [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_pow, zpow_natCast]
  refine ⟨(K : ℤ), ?_, ?_⟩
  · intro v hv
    rw [hcoe, LinearEquiv.mul_apply, hk₀ _ (hpow K v hv), ← LinearEquiv.mul_apply,
      ← pow_add, hkadd, pow_mul, hep, one_pow]
    simp
  · intro i hij v hv
    have hvperp : v ∈ polarPerp Q (U j) := mem_polarPerp_iff.2 fun y hy =>
      hF.perp j i (fun hji => hij hji.symm) y hy v hv
    have hvfix : ((e j : V ≃ₗ[F] V) ^ K) v = v :=
      mem_fixedSpace.1 (fixedSpace_eq_of_mem_zpowers_aux1
        (Subgroup.npow_mem_zpowers (e j : V ≃ₗ[F] V) K)
        (mem_fixedSpace.2 (hF.apply_of_perp j v hvperp)))
    rw [hcoe, LinearEquiv.mul_apply, hvfix]

end Calculus

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
