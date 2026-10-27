module

public import CFSG.FeitThompson.Representations.ExtraspecialEndomorphismBasis
public import CFSG.FeitThompson.Representations.CyclicConjugationEigenspaceDimensions
public import CFSG.FeitThompson.Representations.ExtraspecialAbelianNormalSqrtIndex
public import CFSG.FeitThompson.Local.InvariantCyclicComplementPrimeLine
public import CFSG.FeitThompson.Local.InvariantCyclicComplementCommutatorPlane

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module MulAction SemidirectProduct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v w

section CycleBasis

variable {k W O : Type*} [Field k] [AddCommGroup W] [Module k W] {r : ℕ} [NeZero r] {ε : k}

theorem pow_val_add_of_pow_eq_one {M : Type*} [Monoid M] {x : M} (hx : x ^ r = 1) (i j : ZMod r) :
    x ^ (i + j).val = x ^ i.val * x ^ j.val := by
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hx]

theorem card_le_finrank_of_linearIndependent [FiniteDimensional k W] {ι : Type*} [Fintype ι]
    {v : ι → W} (hv : LinearIndependent k v) {S : Submodule k W} (hmem : ∀ i, v i ∈ S) :
    Fintype.card ι ≤ finrank k S := by
  rw [← finrank_span_eq_card hv]
  exact Submodule.finrank_mono (Submodule.span_le.2 (Set.range_subset_iff.2 hmem))

noncomputable def cycleEigenvector (b : Module.Basis (Option (O × ZMod r)) k W) (ε : k)
    (o : O) (m : ZMod r) : W :=
  ∑ j : ZMod r, ε ^ (-(m * j)).val • b (some (o, j))

variable {b : Module.Basis (Option (O × ZMod r)) k W} {C : W ≃ₗ[k] W}

@[simp]
theorem repr_cycleEigenvector_none (o : O) (m : ZMod r) :
    b.repr (cycleEigenvector b ε o m) none = 0 := by
  classical
  rw [← Basis.coord_apply, cycleEigenvector, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, Basis.coord_apply, Basis.repr_self_apply, if_neg (by simp), smul_zero]

@[simp]
theorem repr_cycleEigenvector_some_self (o : O) (m j : ZMod r) :
    b.repr (cycleEigenvector b ε o m) (some (o, j)) = ε ^ (-(m * j)).val := by
  classical
  rw [← Basis.coord_apply, cycleEigenvector, map_sum, Finset.sum_eq_single j]
  · rw [map_smul, Basis.coord_apply, Basis.repr_self_apply, if_pos rfl, smul_eq_mul, mul_one]
  · intro c _ hc
    rw [map_smul, Basis.coord_apply, Basis.repr_self_apply, if_neg (by simp [hc]), smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem repr_cycleEigenvector_some_of_ne {o o' : O} (hoo : o ≠ o') (m j : ZMod r) :
    b.repr (cycleEigenvector b ε o m) (some (o', j)) = 0 := by
  classical
  rw [← Basis.coord_apply, cycleEigenvector, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [map_smul, Basis.coord_apply, Basis.repr_self_apply, if_neg (by simp [hoo]), smul_zero]

theorem apply_cycleEigenvector (hεr : ε ^ r = 1)
    (hb : ∀ o j, C (b (some (o, j))) = b (some (o, j + 1))) (o : O) (m : ZMod r) :
    C (cycleEigenvector b ε o m) = ε ^ m.val • cycleEigenvector b ε o m := by
  rw [cycleEigenvector, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod r)) _ _ fun j => ?_
  simp only [Equiv.coe_addRight, map_smul, hb o j, smul_smul]
  congr 1
  have hmj : -(m * j) = -(m * (j + 1)) + m := by ring
  rw [hmj, pow_val_add_of_pow_eq_one hεr, mul_comm]

theorem linearIndependent_optionCycleEigenvector (hε0 : ε ≠ 0) :
    LinearIndependent k fun x : Option O =>
      x.elim (b none) fun o => cycleEigenvector b ε o (0 : ZMod r) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg x hx
  match x with
  | none =>
    have h := congrArg (b.coord none) hg
    rw [map_sum, map_zero, Finset.sum_eq_single_of_mem none hx] at h
    · simpa using h
    · intro c _ hc
      match c with
      | none => exact absurd rfl hc
      | some o => simp [Basis.coord_apply]
  | some o =>
    have h := congrArg (b.coord (some (o, (0 : ZMod r)))) hg
    rw [map_sum, map_zero, Finset.sum_eq_single_of_mem (some o) hx] at h
    · rw [map_smul, Basis.coord_apply, Option.elim, repr_cycleEigenvector_some_self,
        smul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_right (pow_ne_zero _ hε0)
    · intro c _ hc
      match c with
      | none => simp [Basis.coord_apply]
      | some o' =>
        rw [map_smul, Basis.coord_apply, Option.elim,
          repr_cycleEigenvector_some_of_ne (by simpa using hc), smul_zero]

theorem linearIndependent_cycleEigenvector (hε0 : ε ≠ 0) (m : ZMod r) :
    LinearIndependent k fun o : O => cycleEigenvector b ε o m := by
  classical
  rw [linearIndependent_iff']
  intro s g hg o ho
  have h := congrArg (b.coord (some (o, (0 : ZMod r)))) hg
  rw [map_sum, map_zero, Finset.sum_eq_single_of_mem o ho] at h
  · rw [map_smul, Basis.coord_apply, repr_cycleEigenvector_some_self, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_right (pow_ne_zero _ hε0)
  · intro c _ hc
    rw [map_smul, Basis.coord_apply, repr_cycleEigenvector_some_of_ne hc, smul_zero]

omit [NeZero r] in
theorem pow_apply_basis_some (hb : ∀ o j, C (b (some (o, j))) = b (some (o, j + 1)))
    (m : ℕ) (o : O) (j : ZMod r) : (C ^ m) (b (some (o, j))) = b (some (o, j + (m : ZMod r))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : (C ^ (m + 1)) (b (some (o, j))) = C ((C ^ m) (b (some (o, j)))) := by
      rw [pow_succ']; rfl
    rw [hs, ih, hb]
    push_cast
    rw [add_assoc]

omit [NeZero r] in
theorem pow_apply_basis_none (hb0 : C (b none) = b none) (m : ℕ) : (C ^ m) (b none) = b none := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : (C ^ (m + 1)) (b none) = C ((C ^ m) (b none)) := by rw [pow_succ']; rfl
    rw [hs, ih, hb0]

theorem pow_eq_one_of_basis_cycle (hb0 : C (b none) = b none)
    (hb : ∀ o j, C (b (some (o, j))) = b (some (o, j + 1))) : C ^ r = 1 := by
  refine LinearEquiv.toLinearMap_injective (b.ext fun i => ?_)
  match i with
  | none => simpa using pow_apply_basis_none hb0 r
  | some (o, j) => simpa using pow_apply_basis_some hb r o j

theorem cyclicEigenspace_conj_eq_conjEigenspace {V : Type*} [AddCommGroup V] [Module k V]
    (T : V ≃ₗ[k] V) (m : ZMod r) :
    cyclicEigenspace ε T.conj m = conjEigenspace ε T m :=
  Submodule.ext fun f => by rw [mem_cyclicEigenspace_iff, mem_conjEigenspace_iff]

theorem finrank_cyclicEigenspace_of_basis_cycle [Fintype O] [IsAlgClosed k] (hrk : (r : k) ≠ 0)
    (hε : IsPrimitiveRoot ε r) (hb0 : C (b none) = b none)
    (hb : ∀ o j, C (b (some (o, j))) = b (some (o, j + 1))) (m : ZMod r) :
    finrank k (cyclicEigenspace ε C m) = Fintype.card O + (if m = 0 then 1 else 0) := by
  classical
  have hfd : FiniteDimensional k W := Module.Finite.of_basis b
  have hε0 : ε ≠ 0 := hε.ne_zero (NeZero.ne r)
  have hCr : C ^ r = 1 := pow_eq_one_of_basis_cycle hb0 hb
  have hlow : ∀ m : ZMod r, Fintype.card O + (if m = 0 then 1 else 0) ≤
      finrank k (cyclicEigenspace ε C m) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      rw [if_pos rfl]
      have hmem : ∀ x : Option O, (x.elim (b none) fun o => cycleEigenvector b ε o (0 : ZMod r)) ∈
          cyclicEigenspace ε C (0 : ZMod r) := by
        intro x
        match x with
        | none => rw [mem_cyclicEigenspace_iff]; simp [hb0]
        | some o =>
          rw [mem_cyclicEigenspace_iff]
          exact apply_cycleEigenvector hε.pow_eq_one hb o 0
      have hcard := card_le_finrank_of_linearIndependent
        (linearIndependent_optionCycleEigenvector (b := b) hε0) hmem
      simpa [Fintype.card_option] using hcard
    · rw [if_neg hm]
      have hmem : ∀ o : O, cycleEigenvector b ε o m ∈ cyclicEigenspace ε C m := fun o => by
        rw [mem_cyclicEigenspace_iff]; exact apply_cycleEigenvector hε.pow_eq_one hb o m
      have hcard := card_le_finrank_of_linearIndependent
        (linearIndependent_cycleEigenvector (b := b) hε0 m) hmem
      simpa using hcard
  have hsum : ∑ m : ZMod r, finrank k (cyclicEigenspace ε C m) = finrank k W :=
    (finrank_eq_sum_finrank_cyclicEigenspace hrk hε hCr).symm
  have htot : ∑ m : ZMod r, (Fintype.card O + (if m = 0 then 1 else 0)) = finrank k W := by
    rw [Finset.sum_add_distrib, Module.finrank_eq_card_basis b]
    simp [Fintype.card_option, mul_comm]
  exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => hlow i)).1 (by rw [htot, hsum]) m
    (Finset.mem_univ m)).symm

end CycleBasis

section PermCycles

variable {X : Type u} {σ : Equiv.Perm X} {r : ℕ}

abbrev permCycleQuot (σ : Equiv.Perm X) : Type u :=
  MulAction.orbitRel.Quotient (Subgroup.zpowers σ) X

noncomputable def permCycleIndex (σ : Equiv.Perm X) (r : ℕ) (x : permCycleQuot σ × ZMod r) : X :=
  (σ ^ (x.2).val) (Quotient.out x.1)

theorem permCycleIndex_apply (σ : Equiv.Perm X) (r : ℕ) (o : permCycleQuot σ) (j : ZMod r) :
    permCycleIndex σ r (o, j) = (σ ^ j.val) (Quotient.out o) := (rfl)

theorem dvd_of_pow_apply_eq_self (hr : r.Prime) (hσr : σ ^ r = 1) (hfree : ∀ x : X, σ x ≠ x)
    {m : ℕ} {x : X} (hm : (σ ^ m) x = x) : r ∣ m := by
  have := Fact.mk hr
  have hper : Function.IsPeriodicPt σ r x := by
    have h1 : (σ ^ r) x = x := by rw [hσr]; rfl
    rwa [Equiv.Perm.coe_pow] at h1
  have hmin : Function.minimalPeriod σ x = r := Function.minimalPeriod_eq_prime hper (hfree x)
  have hpm : Function.IsPeriodicPt σ m x := by rwa [Equiv.Perm.coe_pow] at hm
  rw [← hmin]
  exact hpm.minimalPeriod_dvd

theorem mk_pow_apply (m : ℕ) (x : X) :
    (Quotient.mk'' ((σ ^ m) x) : permCycleQuot σ) = Quotient.mk'' x := by
  have h : (Quotient.mk'' ((σ ^ (m : ℤ)) x) : permCycleQuot σ) = Quotient.mk'' x :=
    Quotient.eq''.2 ⟨⟨σ ^ (m : ℤ), Subgroup.zpow_mem _ (Subgroup.mem_zpowers σ) _⟩, rfl⟩
  simpa using h

theorem permCycleIndex_injective [NeZero r] (hr : r.Prime) (hσr : σ ^ r = 1)
    (hfree : ∀ x : X, σ x ≠ x) : Function.Injective (permCycleIndex σ r) := by
  rintro ⟨o, i⟩ ⟨o', j⟩ hij
  rw [permCycleIndex, permCycleIndex] at hij
  simp only at hij
  have hoo : o = o' := by
    have h1 : (Quotient.mk'' ((σ ^ i.val) (Quotient.out o)) : permCycleQuot σ) =
        Quotient.mk'' ((σ ^ j.val) (Quotient.out o')) := by rw [hij]
    rwa [mk_pow_apply, mk_pow_apply, Quotient.out_eq', Quotient.out_eq'] at h1
  subst hoo
  suffices hij' : i = j by rw [hij']
  set x := Quotient.out o with hx
  have key : ∀ a b : ℕ, b ≤ a → (σ ^ a) x = (σ ^ b) x → r ∣ a - b := by
    intro a b hba hab
    refine dvd_of_pow_apply_eq_self hr hσr hfree (x := (σ ^ b) x) ?_
    have hab2 : (σ ^ (a - b)) ((σ ^ b) x) = (σ ^ a) x := by
      rw [← Equiv.Perm.mul_apply, ← pow_add]
      congr 2
      omega
    rw [hab2, hab]
  refine ZMod.val_injective r ?_
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  rcases le_total j.val i.val with hle | hle
  · have hd := key i.val j.val hle hij
    rcases Nat.eq_zero_or_pos (i.val - j.val) with h0 | h0
    · omega
    · have := Nat.le_of_dvd h0 hd; omega
  · have hd := key j.val i.val hle hij.symm
    rcases Nat.eq_zero_or_pos (j.val - i.val) with h0 | h0
    · omega
    · have := Nat.le_of_dvd h0 hd; omega

theorem permCycleIndex_surjective [NeZero r] (hσr : σ ^ r = 1) :
    Function.Surjective (permCycleIndex σ r) := by
  intro x
  set o : permCycleQuot σ := Quotient.mk'' x with ho
  have hmem : x ∈ o.orbit := MulAction.orbitRel.Quotient.mem_orbit.2 ho.symm
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out o (fun q => Quotient.out_eq' q)] at hmem
  obtain ⟨⟨g, hg⟩, hgx⟩ := hmem
  obtain ⟨m, rfl⟩ := hg
  refine ⟨(o, (m : ZMod r)), ?_⟩
  have hval : ((m : ZMod r)).val = (m % (r : ℤ)).toNat := by
    have := ZMod.val_intCast (n := r) m
    omega
  rw [permCycleIndex, hval]
  have hpow : (σ ^ ((m % (r : ℤ)).toNat : ℕ)) = σ ^ m := by
    have hnn : (0 : ℤ) ≤ m % (r : ℤ) := Int.emod_nonneg m (by exact_mod_cast (NeZero.ne r))
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn,
      ← zpow_eq_zpow_emod m (by rw [zpow_natCast]; exact hσr)]
  rw [hpow]
  exact hgx

noncomputable def permCycleEquiv [NeZero r] (hr : r.Prime) (hσr : σ ^ r = 1)
    (hfree : ∀ x : X, σ x ≠ x) : permCycleQuot σ × ZMod r ≃ X :=
  Equiv.ofBijective _ ⟨permCycleIndex_injective hr hσr hfree, permCycleIndex_surjective hσr⟩

theorem permCycleEquiv_apply [NeZero r] (hr : r.Prime) (hσr : σ ^ r = 1)
    (hfree : ∀ x : X, σ x ≠ x) (x : permCycleQuot σ × ZMod r) :
    permCycleEquiv hr hσr hfree x = permCycleIndex σ r x := (rfl)

end PermCycles

section Quot

variable {P H : Type*} [Group P] [Group H] (α : H →* MulAut P)

noncomputable def centerQuotAut : H →* MulAut (P ⧸ Subgroup.center P) :=
  quotientMulAut α (Subgroup.center P) fun a _ hx =>
    apply_mem_of_characteristic α (Subgroup.center P) a hx

theorem centerQuotAut_mk (a : H) (x : P) :
    centerQuotAut α a (QuotientGroup.mk x) = (QuotientGroup.mk (α a x)) :=
  quotientMulAut_mk α (Subgroup.center P) _ a x

noncomputable def centerQuotPerm (a : H) : Equiv.Perm (P ⧸ Subgroup.center P) :=
  MulAut.toPerm _ (centerQuotAut α a)

theorem centerQuotPerm_apply (a : H) (q : P ⧸ Subgroup.center P) :
    centerQuotPerm α a q = centerQuotAut α a q := (rfl)

theorem centerQuotPerm_mk (a : H) (x : P) :
    centerQuotPerm α a (QuotientGroup.mk x) = (QuotientGroup.mk (α a x)) := by
  rw [centerQuotPerm_apply, centerQuotAut_mk]

theorem centerQuotPerm_one (q : P ⧸ Subgroup.center P) : centerQuotPerm α 1 q = q := by
  rw [centerQuotPerm, map_one]; rfl

theorem centerQuotPerm_mul_apply (a b : H) (q : P ⧸ Subgroup.center P) :
    centerQuotPerm α (a * b) q = centerQuotPerm α a (centerQuotPerm α b q) := by
  rw [centerQuotPerm, centerQuotPerm, centerQuotPerm, map_mul]; rfl

theorem centerQuotPerm_eq_one_iff (a : H) {q : P ⧸ Subgroup.center P} :
    centerQuotPerm α a q = 1 ↔ q = 1 := by
  rw [centerQuotPerm_apply]
  refine ⟨fun hq => (centerQuotAut α a).injective ?_, fun hq => by rw [hq, map_one]⟩
  rw [hq, map_one]

abbrev NontrivialCoset (P : Type*) [Group P] : Type _ :=
  {q : P ⧸ Subgroup.center P // q ≠ 1}

theorem centerQuotPerm_ne_one_iff (a : H) (q : P ⧸ Subgroup.center P) :
    centerQuotPerm α a q ≠ 1 ↔ q ≠ 1 := not_congr (centerQuotPerm_eq_one_iff α a)

noncomputable def nontrivialCosetPerm (a : H) : Equiv.Perm (NontrivialCoset P) :=
  (centerQuotPerm α a).subtypePerm (centerQuotPerm_ne_one_iff α a)

@[simp]
theorem coe_nontrivialCosetPerm_apply (a : H) (q : NontrivialCoset P) :
    (nontrivialCosetPerm α a q : P ⧸ Subgroup.center P) = centerQuotPerm α a q := (rfl)

theorem coe_nontrivialCosetPerm_pow_apply (a : H) (m : ℕ) (q : NontrivialCoset P) :
    ((nontrivialCosetPerm α a ^ m) q : P ⧸ Subgroup.center P) = centerQuotPerm α (a ^ m) q := by
  induction m with
  | zero => rw [pow_zero, pow_zero, centerQuotPerm_one]; rfl
  | succ m ih =>
    have h1 : ((nontrivialCosetPerm α a ^ (m + 1)) q : P ⧸ Subgroup.center P) =
        nontrivialCosetPerm α a ((nontrivialCosetPerm α a ^ m) q) := by
      rw [pow_succ']; rfl
    rw [h1, coe_nontrivialCosetPerm_apply, ih, ← centerQuotPerm_mul_apply, ← pow_succ']

theorem nontrivialCosetPerm_pow_eq_one {a : H} {m : ℕ} (ha : a ^ m = 1) :
    nontrivialCosetPerm α a ^ m = 1 := by
  refine Equiv.ext fun q => Subtype.ext ?_
  rw [coe_nontrivialCosetPerm_pow_apply, ha, centerQuotPerm_one]
  rfl

variable {α}

theorem centerQuotAut_zpow_fixed {a : H} {q : P ⧸ Subgroup.center P}
    (hq : centerQuotAut α a q = q) (m : ℤ) : centerQuotAut α (a ^ m) q = q := by
  rw [map_zpow]
  have hfp := Function.IsFixedPt.perm_zpow
    (e := MulAut.toPerm (P ⧸ Subgroup.center P) (centerQuotAut α a)) hq m
  rw [← map_zpow] at hfp
  exact hfp

theorem nontrivialCosetPerm_apply_ne {h : H} (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1)
    (q : NontrivialCoset P) : nontrivialCosetPerm α h q ≠ q := by
  intro hq
  have hq' : centerQuotAut α h (q : P ⧸ Subgroup.center P) = q := by
    have hcoe := congrArg (fun x : NontrivialCoset P => (x : P ⧸ Subgroup.center P)) hq
    rwa [coe_nontrivialCosetPerm_apply, centerQuotPerm_apply] at hcoe
  refine q.2 (hfix _ fun a => ?_)
  obtain ⟨m, rfl⟩ := (show a ∈ Subgroup.zpowers h from hgen ▸ Subgroup.mem_top a)
  exact centerQuotAut_zpow_fixed hq' m

end Quot

section Semidirect

variable {P H : Type u} [Group P] [Group H] {α : H →* MulAut P}
  {k : Type v} [Field k] {V : Type w} [AddCommGroup V] [Module k V]

def resInl (ρ : Representation k (P ⋊[α] H) V) : Representation k P V :=
  ρ.comp (SemidirectProduct.inl : P →* P ⋊[α] H)

theorem resInl_apply (ρ : Representation k (P ⋊[α] H) V) (x : P) :
    resInl ρ x = ρ (SemidirectProduct.inl x) := (rfl)

noncomputable def repEquiv (ρ : Representation k (P ⋊[α] H) V) (a : H) : V ≃ₗ[k] V :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv k V (ρ.asGroupHom (SemidirectProduct.inr a))

theorem repEquiv_apply (ρ : Representation k (P ⋊[α] H) V) (a : H) (v : V) :
    repEquiv ρ a v = ρ (SemidirectProduct.inr a) v := (rfl)

theorem coe_repEquiv (ρ : Representation k (P ⋊[α] H) V) (a : H) :
    (repEquiv ρ a : Module.End k V) = ρ (SemidirectProduct.inr a) :=
  LinearMap.ext fun v => repEquiv_apply ρ a v

theorem repEquiv_symm_apply (ρ : Representation k (P ⋊[α] H) V) (a : H) (v : V) :
    (repEquiv ρ a).symm v = ρ (SemidirectProduct.inr a⁻¹) v := by
  rw [LinearEquiv.symm_apply_eq, repEquiv_apply, ← Module.End.mul_apply, ← map_mul,
    show (SemidirectProduct.inr a : P ⋊[α] H) * SemidirectProduct.inr a⁻¹ = 1 from by
      rw [← map_mul, mul_inv_cancel, map_one],
    map_one, Module.End.one_apply]

theorem repEquiv_pow_eq_one (ρ : Representation k (P ⋊[α] H) V) {a : H} {m : ℕ}
    (ha : a ^ m = 1) : repEquiv ρ a ^ m = 1 := by
  refine LinearEquiv.toLinearMap_injective ?_
  rw [coe_pow_toLinearMap, coe_repEquiv, ← map_pow, ← map_pow, ha, map_one, map_one]
  rfl

theorem conj_repEquiv_resInl (ρ : Representation k (P ⋊[α] H) V) (a : H) (x : P) :
    (repEquiv ρ a).conj (resInl ρ x) = resInl ρ (α a x) := by
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [repEquiv_symm_apply, resInl_apply, repEquiv_apply, resInl_apply,
    SemidirectProduct.inl_aut a x, map_mul, map_mul]
  simp [Module.End.mul_apply]

end Semidirect

section Main

variable {p n r : ℕ} {P H : Type u} [Group P] [Group H] {α : H →* MulAut P} {h : H}
  {k : Type v} [Field k] {V : Type w} [AddCommGroup V] [Module k V]
  {ρ : Representation k (P ⋊[α] H) V} {zeta : ↥(Subgroup.center P) →* kˣ} {B : Subgroup P} {ε : k}

abbrev cosetCycles (α : H →* MulAut P) (h : H) : Type u :=
  permCycleQuot (nontrivialCosetPerm α h)

noncomputable def cycleRepr (α : H →* MulAut P) (h : H) (o : cosetCycles α h) : P :=
  Quotient.out ((Quotient.out o : NontrivialCoset P) : P ⧸ Subgroup.center P)

theorem mk_cycleRepr (α : H →* MulAut P) (h : H) (o : cosetCycles α h) :
    (QuotientGroup.mk (cycleRepr α h o) : P ⧸ Subgroup.center P) =
      ((Quotient.out o : NontrivialCoset P) : P ⧸ Subgroup.center P) :=
  QuotientGroup.out_eq' _

noncomputable def cycleTransversal (α : H →* MulAut P) (h : H) (r : ℕ) :
    Option (cosetCycles α h × ZMod r) → P
  | none => 1
  | some (o, j) => α (h ^ j.val) (cycleRepr α h o)

@[simp]
theorem cycleTransversal_none : cycleTransversal α h r none = 1 := (rfl)

theorem cycleTransversal_some (o : cosetCycles α h) (j : ZMod r) :
    cycleTransversal α h r (some (o, j)) = α (h ^ j.val) (cycleRepr α h o) := (rfl)

theorem mk_cycleTransversal_some (o : cosetCycles α h) (j : ZMod r) :
    (QuotientGroup.mk (cycleTransversal α h r (some (o, j))) : P ⧸ Subgroup.center P) =
      ((permCycleIndex (nontrivialCosetPerm α h) r (o, j) : NontrivialCoset P) :
        P ⧸ Subgroup.center P) := by
  rw [cycleTransversal_some, ← centerQuotPerm_mk, mk_cycleRepr, permCycleIndex_apply,
    coe_nontrivialCosetPerm_pow_apply]

theorem aut_pow_val_succ [NeZero r] (hr1 : 1 < r) (hhr : h ^ r = 1) (j : ZMod r) (x : P) :
    α h (α (h ^ j.val) x) = α (h ^ (j + 1).val) x := by
  have : Fact (1 < r) := ⟨hr1⟩
  rw [pow_val_add_of_pow_eq_one hhr, ZMod.val_one r, pow_one, ← pow_succ, pow_succ', map_mul]
  rfl

theorem bijective_mk_cycleTransversal [NeZero r] (hr : r.Prime) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1) :
    Function.Bijective fun i : Option (cosetCycles α h × ZMod r) =>
      (QuotientGroup.mk (cycleTransversal α h r i) : P ⧸ Subgroup.center P) := by
  classical
  have hσr : nontrivialCosetPerm α h ^ r = 1 :=
    nontrivialCosetPerm_pow_eq_one α (hho ▸ pow_orderOf_eq_one h)
  have hfree := nontrivialCosetPerm_apply_ne hgen hfix
  set e : Option (cosetCycles α h × ZMod r) ≃ P ⧸ Subgroup.center P :=
    (Equiv.optionCongr (permCycleEquiv hr hσr hfree)).trans
      (Equiv.optionSubtypeNe (1 : P ⧸ Subgroup.center P)) with he
  have hfun : (fun i : Option (cosetCycles α h × ZMod r) =>
      (QuotientGroup.mk (cycleTransversal α h r i) : P ⧸ Subgroup.center P)) = e := by
    funext i
    match i with
    | none => rw [cycleTransversal_none, he]; simp
    | some (o, j) =>
      rw [mk_cycleTransversal_some, he]
      simp [permCycleEquiv_apply]
  rw [hfun]
  exact e.bijective

variable (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
  (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
  (hBZ : (Subgroup.center P).relIndex B = p ^ n) [IsAlgClosed k] (hp : (p : k) ≠ 0)
  (hirr : (resInl ρ).IsIrreducible) (hzeta : zeta ≠ 1)
  (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), resInl ρ (z : P) w = (zeta z : k) • w)

noncomputable def endCycleBasis [NeZero r] (hr : r.Prime) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1) :
    Module.Basis (Option (cosetCycles α h × ZMod r)) k (Module.End k V) :=
  ExtraspecialWeight.endBasis hP hZB hCB hPB hBZ hp hirr hzeta hz (cycleTransversal α h r)
    (bijective_mk_cycleTransversal hr hho hgen hfix)

theorem endCycleBasis_apply [NeZero r] (hr : r.Prime) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1)
    (i : Option (cosetCycles α h × ZMod r)) :
    endCycleBasis hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix i =
      (resInl ρ (cycleTransversal α h r i) : Module.End k V) :=
  ExtraspecialWeight.endBasis_apply hP hZB hCB hPB hBZ hp hirr hzeta hz _ _ i

theorem endCycleBasis_none [NeZero r] (hr : r.Prime) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1) :
    endCycleBasis hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix none = 1 := by
  rw [endCycleBasis_apply, cycleTransversal_none, map_one]

theorem conj_endCycleBasis_some [NeZero r] (hr : r.Prime) (hho : orderOf h = r)
    (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1)
    (o : cosetCycles α h) (j : ZMod r) :
    (repEquiv ρ h).conj
        (endCycleBasis hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix (some (o, j))) =
      endCycleBasis hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix (some (o, j + 1)) := by
  have hhr : h ^ r = 1 := hho ▸ pow_orderOf_eq_one h
  rw [endCycleBasis_apply, endCycleBasis_apply, cycleTransversal_some, cycleTransversal_some,
    conj_repEquiv_resInl, aut_pow_val_succ hr.one_lt hhr]

theorem exists_basis_conj_cycle (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    (hBZ : (Subgroup.center P).relIndex B = p ^ n) (hp : (p : k) ≠ 0)
    (hirr : (resInl ρ).IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), resInl ρ (z : P) w = (zeta z : k) • w)
    [NeZero r] (hr : r.Prime) (hho : orderOf h = r) (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1) :
    ∃ b : Module.Basis (Option (cosetCycles α h × ZMod r)) k (Module.End k V),
      b none = 1 ∧ ∀ (o : cosetCycles α h) (j : ZMod r),
        (repEquiv ρ h).conj (b (some (o, j))) = b (some (o, j + 1)) :=
  ⟨endCycleBasis hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix,
    endCycleBasis_none hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix,
    conj_endCycleBasis_some hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix⟩

theorem finrank_conjEigenspace_eq (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    (hBZ : (Subgroup.center P).relIndex B = p ^ n) (hp : (p : k) ≠ 0)
    (hirr : (resInl ρ).IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), resInl ρ (z : P) w = (zeta z : k) • w)
    [NeZero r] (hr : r.Prime) (hrk : (r : k) ≠ 0)
    (hε : IsPrimitiveRoot ε r) (hho : orderOf h = r) (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1)
    (m : ZMod r) :
    finrank k (conjEigenspace ε (repEquiv ρ h) m) =
      Nat.card (cosetCycles α h) + (if m = 0 then 1 else 0) := by
  classical
  have := hP.finite
  have : Finite (cosetCycles α h) := Quotient.finite _
  have : Fintype (cosetCycles α h) := Fintype.ofFinite _
  have hb0 : (repEquiv ρ h).conj
      (endCycleBasis hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix none) =
      endCycleBasis hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix none := by
    rw [endCycleBasis_none]
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.conj_apply]
    simp
  have hkey := finrank_cyclicEigenspace_of_basis_cycle (k := k) (W := Module.End k V)
    (O := cosetCycles α h) (b := endCycleBasis hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix)
    (C := (repEquiv ρ h).conj) hrk hε hb0
    (conj_endCycleBasis_some hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix) m
  rw [← cyclicEigenspace_conj_eq_conjEigenspace, hkey,
    ← Nat.card_eq_fintype_card (α := cosetCycles α h)]

theorem finrank_conjEigenspace_zero_eq_succ (hP : IsExtraspecial p P)
    (hZB : Subgroup.center P ≤ B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    (hBZ : (Subgroup.center P).relIndex B = p ^ n) (hp : (p : k) ≠ 0)
    (hirr : (resInl ρ).IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), resInl ρ (z : P) w = (zeta z : k) • w)
    [NeZero r] (hr : r.Prime) (hrk : (r : k) ≠ 0)
    (hε : IsPrimitiveRoot ε r) (hho : orderOf h = r) (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1)
    {m : ZMod r} (hm : m ≠ 0) :
    finrank k (conjEigenspace ε (repEquiv ρ h) (0 : ZMod r)) =
      finrank k (conjEigenspace ε (repEquiv ρ h) m) + 1 := by
  rw [finrank_conjEigenspace_eq hP hZB hCB hPB hBZ hp hirr hzeta hz hr hrk hε hho hgen hfix,
    finrank_conjEigenspace_eq hP hZB hCB hPB hBZ hp hirr hzeta hz hr hrk hε hho hgen hfix,
    if_pos rfl, if_neg hm]

theorem exists_basis_conj_cycle' (hP : IsExtraspecial p P) (hp : (p : k) ≠ 0)
    (hirr : (resInl ρ).IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), resInl ρ (z : P) w = (zeta z : k) • w)
    [NeZero r] (hr : r.Prime) (hho : orderOf h = r) (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1) :
    ∃ b : Module.Basis (Option (cosetCycles α h × ZMod r)) k (Module.End k V),
      b none = 1 ∧ ∀ (o : cosetCycles α h) (j : ZMod r),
        (repEquiv ρ h).conj (b (some (o, j))) = b (some (o, j + 1)) := by
  obtain ⟨N, B, -, -, -, hZB, -, hPB, hBZ, hCB⟩ := hP.exists_abelian_normal_polarization
  exact exists_basis_conj_cycle hP hZB hCB hPB hBZ hp hirr hzeta hz hr hho hgen hfix

theorem finrank_conjEigenspace_zero_eq_succ' (hP : IsExtraspecial p P) (hp : (p : k) ≠ 0)
    (hirr : (resInl ρ).IsIrreducible) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V), resInl ρ (z : P) w = (zeta z : k) • w)
    [NeZero r] (hr : r.Prime) (hrk : (r : k) ≠ 0)
    (hε : IsPrimitiveRoot ε r) (hho : orderOf h = r) (hgen : Subgroup.zpowers h = ⊤)
    (hfix : ∀ q : P ⧸ Subgroup.center P, (∀ a : H, centerQuotAut α a q = q) → q = 1)
    {m : ZMod r} (hm : m ≠ 0) :
    finrank k (conjEigenspace ε (repEquiv ρ h) (0 : ZMod r)) =
      finrank k (conjEigenspace ε (repEquiv ρ h) m) + 1 := by
  obtain ⟨N, B, -, -, -, hZB, -, hPB, hBZ, hCB⟩ := hP.exists_abelian_normal_polarization
  exact finrank_conjEigenspace_zero_eq_succ hP hZB hCB hPB hBZ hp hirr hzeta hz hr hrk hε hho
    hgen hfix hm

end Main

end

end CFSG.FeitThompson
