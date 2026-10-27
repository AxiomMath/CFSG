module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Lift
public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagGlue

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2


section Weyl

variable {b : Fin Tag.E6.rank → ZMod 3}

theorem triPairing_zsmul (c : ℤ) (v : Fin Tag.E6.rank → ℤ) :
    triPairing b (c • v) = (c : ZMod 3) * triPairing b v := by
  simp only [triPairing, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem q_eq_one_of_commutator {w w' : WeylGroup Tag.E6} {q : ZMod 3}
    (hw : w ∈ charStabilizer (triChar b)) (hsh : triPairing b (e6Shift w) ≠ 0)
    (hrel : ∀ v, triPairing b (w' • v) = q * triPairing b v)
    (hcomm : w' * w * w'⁻¹ * w⁻¹ ∈ kernelWeylGroup (triChar b)) : q = 1 := by
  have h1 : q * triPairing b (e6Shift w'⁻¹) + triPairing b (e6Shift w') = 0 := by
    have := e6Shift_mul w' w'⁻¹
    rw [mul_inv_cancel, e6Shift_one] at this
    have h := congrArg (triPairing b) this
    rw [triPairing_zero, triPairing_add, hrel] at h
    exact h.symm
  have e2 : triPairing b (e6Shift (w' * w * w'⁻¹)) = q * triPairing b (e6Shift w) := by
    rw [mul_assoc, e6Shift_mul, triPairing_add, hrel, e6Shift_mul, triPairing_add,
      triPairing_smul_of_mem hw]
    linear_combination h1
  have e3 : triPairing b (e6Shift (w' * w * w'⁻¹)) = triPairing b (e6Shift w) := by
    have hxw : w' * w * w'⁻¹ = (w' * w * w'⁻¹ * w⁻¹) * w := by group
    rw [hxw, e6Shift_mul, triPairing_add, triPairing_smul_of_mem (kernelWeylGroup_le hcomm),
      triPairing_e6Shift_of_mem_kernelWeylGroup hcomm, add_zero]
  have h4 : q * triPairing b (e6Shift w) = 1 * triPairing b (e6Shift w) := by
    rw [← e2, e3, one_mul]
  exact mul_right_cancel₀ hsh h4

theorem pow_charStab_shift {w : WeylGroup Tag.E6} (hw : w ∈ charStabilizer (triChar b)) (n : ℕ) :
    triPairing b (e6Shift (w ^ n)) = n * triPairing b (e6Shift w) := by
  induction n with
  | zero => simp [e6Shift_one, triPairing_zero]
  | succ n ih =>
    rw [pow_succ, triPairing_e6Shift_mul (pow_mem hw n), ih]
    push_cast
    ring

theorem exists_pow_mul_mem_kernelWeylGroup {w w' : WeylGroup Tag.E6}
    (hw : w ∈ charStabilizer (triChar b)) (hw' : w' ∈ charStabilizer (triChar b))
    (hsh : triPairing b (e6Shift w) ≠ 0) :
    ∃ j : ℕ, w ^ j * w' ∈ kernelWeylGroup (triChar b) := by
  refine ⟨(-(triPairing b (e6Shift w') / triPairing b (e6Shift w))).val,
    e6Shift_mem_kernelWeylGroup b (mul_mem (pow_mem hw _) hw') ?_⟩
  rw [triPairing_e6Shift_mul (pow_mem hw _), pow_charStab_shift hw, ZMod.natCast_zmod_val,
    neg_mul, div_mul_cancel₀ _ hsh]
  ring

end Weyl

section Group

variable {L : Type} [Field L] [IsAlgClosed L]

abbrev heisM (a : Fin Tag.E6.rank → Lˣ) : Subgroup (ModGL Tag.E6 L) :=
  familyGroup (K := L) (fun _ : Unit => a)

theorem familyKernel_unit (a : Fin Tag.E6.rank → Lˣ) :
    familyKernel (fun _ : Unit => a) = rootCharKernel a := by
  ext α
  simp [familyKernel, rootCharKernel]

theorem toralRootGroup_eq_heisM (a : Fin Tag.E6.rank → Lˣ) :
    toralRootGroup Tag.E6 L a = heisM a := by
  show torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (rootCharKernel a) =
    torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (familyKernel (fun _ : Unit => a))
  rw [familyKernel_unit]

theorem torus_le_heisM (a : Fin Tag.E6.rank → Lˣ) : torusGroup Tag.E6 L ≤ heisM a :=
  torus_le_familyGroup _

theorem rootSpan_le_heisM (a : Fin Tag.E6.rank → Lˣ) :
    rootSpan Tag.E6 L (rootCharKernel a) ≤ heisM a := by
  rw [← familyKernel_unit]
  exact rootSpan_le_familyGroup _

theorem heisM_comm (a : Fin Tag.E6.rank → Lˣ) {m : ModGL Tag.E6 L} (hm : m ∈ heisM a) :
    m * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * m :=
  familyGroup_comm (fun _ : Unit => a) () hm

theorem heisM_le_adjoint (a : Fin Tag.E6.rank → Lˣ) : heisM a ≤ adjointGroup Tag.E6 L :=
  familyGroup_le_adjoint _

theorem kernelReflectionGroup_le_closure (a : Fin Tag.E6.rank → Lˣ) :
    kernelReflectionGroup a ≤ Subgroup.closure (rootReflection '' rootCharKernel a) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, i, hk, rfl⟩
  exact Subgroup.subset_closure ⟨_, hk, (conj_simple_eq_rootReflection w i).symm⟩

theorem mem_heisM_of_mapsRootLines {a : Fin Tag.E6.rank → Lˣ} {g : ModGL Tag.E6 L}
    {x : WeylGroup Tag.E6} (hg : g ∈ monomialSubgroup Tag.E6 L) (hgx : MapsRootLines g x)
    (hx : x ∈ kernelReflectionGroup a) : g ∈ heisM a := by
  obtain ⟨x', t, ht, rfl⟩ := exists_torus_mul_canonicalRep_of_mem_monomial hg
  have h1 : MapsRootLines (t * canonicalRep (coxeterSystem Tag.E6) L x') (1 * x') :=
    (mapsRootLines_of_mem_torusGroup ht).mul (mapsRootLines_canonicalRep x')
  rw [one_mul] at h1
  have e := hgx.unique h1
  subst e
  have hx' := kernelReflectionGroup_le_closure a hx
  rw [← familyKernel_unit] at hx'
  exact mul_mem (torus_le_heisM a ht) (canonicalRep_closure_mem_familyGroup _ hx')

theorem mem_kernelReflectionGroup_of_mapsRootLines {a : Fin Tag.E6.rank → Lˣ}
    {g : ModGL Tag.E6 L} {x : WeylGroup Tag.E6} (hg : g ∈ monomialSubgroup Tag.E6 L)
    (hgx : MapsRootLines g x) (hgM : g ∈ heisM a) : x ∈ kernelReflectionGroup a := by
  obtain ⟨x', t, ht, rfl⟩ := exists_torus_mul_canonicalRep_of_mem_monomial hg
  have h1 : MapsRootLines (t * canonicalRep (coxeterSystem Tag.E6) L x') (1 * x') :=
    (mapsRootLines_of_mem_torusGroup ht).mul (mapsRootLines_canonicalRep x')
  rw [one_mul] at h1
  have e := hgx.unique h1
  subst e
  have hn : canonicalRep (coxeterSystem Tag.E6) L x ∈ heisM a := by
    have e2 : canonicalRep (coxeterSystem Tag.E6) L x =
        t⁻¹ * (t * canonicalRep (coxeterSystem Tag.E6) L x) := by group
    rw [e2]
    exact mul_mem (inv_mem (torus_le_heisM a ht)) hgM
  exact mem_kernelReflectionGroup_of_canonicalRep_mem_gen (by rwa [toralRootGroup_eq_heisM])

end Group

section Core

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_triData_lattice {a : Fin Tag.E6.rank → Lˣ} (ha3 : ∀ i, a i ^ 3 = 1) :
    ∃ b3 : Fin Tag.E6.rank → ZMod 3, ∀ x, rootCharHom3 a x = 1 ↔ triChar b3 x = 1 := by
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a ha3)
  refine ⟨fun j => Z3.toAdd (χ' (Multiplicative.ofAdd (Pi.single j 1))), fun x => ?_⟩
  rw [← eq_triChar χ']
  exact hker x

theorem triPairing_frob_rel {a : Fin Tag.E6.rank → Lˣ} {b3 : Fin Tag.E6.rank → ZMod 3}
    (hker : ∀ x, rootCharHom3 a x = 1 ↔ triChar b3 x = 1) {w' : WeylGroup Tag.E6} {q : ℕ}
    (hrel : ∀ v, rootChar a (w' • v) = rootChar a v ^ q) (v : Fin Tag.E6.rank → ℤ) :
    triPairing b3 (w' • v) = (q : ZMod 3) * triPairing b3 v := by
  have hz : rootCharHom3 a (Multiplicative.ofAdd (w' • v - (q : ℤ) • v)) = 1 := by
    show rootChar a (w' • v - (q : ℤ) • v) = 1
    rw [rootChar_sub, rootChar_zsmul, hrel v, zpow_natCast]
    simp
  have h := (hker _).1 hz
  rw [triChar_apply, Z3.ofAdd_eq_one] at h
  have h2 := triPairing_add b3 (w' • v - (q : ℤ) • v) ((q : ℤ) • v)
  rw [sub_add_cancel, h, zero_add, triPairing_zsmul] at h2
  simpa using h2

theorem commutator_mem_kernel {f : ℕ} {a b : Fin Tag.E6.rank → Lˣ} {w w' : WeylGroup Tag.E6}
    {u : ModGL Tag.E6 L}
    (hnw : canonicalRep (coxeterSystem Tag.E6) L w ∈ Subgroup.normalizer (heisM a : Set (ModGL Tag.E6 L)))
    (hnw' : canonicalRep (coxeterSystem Tag.E6) L w' ∈
      Subgroup.normalizer (heisM a : Set (ModGL Tag.E6 L)))
    (hu : u ∈ heisM a)
    (hy : canonicalRep (coxeterSystem Tag.E6) L w' *
        entrywiseFrobGL Tag.E6 L ℓ f (u⁻¹ * (rootDiagUnit Tag.E6 b *
          canonicalRep (coxeterSystem Tag.E6) L w) * u) *
        (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ =
      u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u) :
    w' * w * w'⁻¹ * w⁻¹ ∈ kernelReflectionGroup a := by
  set F := entrywiseFrobGL Tag.E6 L ℓ f with hF
  set y₀ := rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w with hy₀
  set nw' := canonicalRep (coxeterSystem Tag.E6) L w' with hnw'def
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnwdef
  have hΦM : ∀ g ∈ heisM a, nw' * F g * nw'⁻¹ ∈ heisM a := fun g hg =>
    (Subgroup.mem_normalizer_iff.1 hnw' _).1 (entrywiseFrobGL_mem_familyGroup ℓ _ f hg)
  have hdb : rootDiagUnit Tag.E6 b ∈ heisM a := torus_le_heisM a (rootDiagUnit_mem_torusGroup b)
  have hy₀N : y₀ ∈ Subgroup.normalizer (heisM a : Set (ModGL Tag.E6 L)) :=
    mul_mem (Subgroup.le_normalizer hdb) hnw
  set m' := (nw' * F u * nw'⁻¹) * u⁻¹ with hm'
  have hm'M : m' ∈ heisM a := mul_mem (hΦM u hu) (inv_mem hu)
  have hΦy₀ : nw' * F y₀ * nw'⁻¹ = m' * y₀ * m'⁻¹ := by
    have h := hy
    simp only [map_mul, map_inv] at h
    rw [hm']
    calc nw' * F y₀ * nw'⁻¹ = (nw' * F u * nw'⁻¹) * (nw' * (F u)⁻¹ * (F y₀) * F u * nw'⁻¹) *
          (nw' * F u * nw'⁻¹)⁻¹ := by group
      _ = _ := by
        have e : nw' * (F u)⁻¹ * F y₀ * F u * nw'⁻¹ = u⁻¹ * y₀ * u := by
          rw [← h]; group
        rw [e]; group
  have hg₀M : (nw' * F y₀ * nw'⁻¹) * y₀⁻¹ ∈ heisM a := by
    rw [hΦy₀]
    have : m' * y₀ * m'⁻¹ * y₀⁻¹ = m' * (y₀ * m'⁻¹ * y₀⁻¹) := by group
    rw [this]
    exact mul_mem hm'M ((Subgroup.mem_normalizer_iff.1 hy₀N _).1 (inv_mem hm'M))
  have hFn : F nw = nw := E8Lift.units_map_entrywiseHom_canonicalRep _ w
  have hFd : F (rootDiagUnit Tag.E6 b) ∈ torusGroup Tag.E6 L := by
    rw [hF, entrywiseFrobGL_rootDiagUnit_eq_pow]
    exact rootDiagUnit_mem_torusGroup _
  have hmono : (nw' * F y₀ * nw'⁻¹) * y₀⁻¹ ∈ monomialSubgroup Tag.E6 L := by
    have hd : ∀ t ∈ torusGroup Tag.E6 L, t ∈ monomialSubgroup Tag.E6 L := fun t ht =>
      Subgroup.mem_sup_left ht
    have h1 : nw' ∈ monomialSubgroup Tag.E6 L := canonicalRep_mem_monomialSubgroup' w'
    have h2 : nw ∈ monomialSubgroup Tag.E6 L := canonicalRep_mem_monomialSubgroup' w
    have hFy₀ : F y₀ = F (rootDiagUnit Tag.E6 b) * nw := by rw [hy₀, map_mul, hFn]
    rw [hFy₀]
    have h3 : y₀ ∈ monomialSubgroup Tag.E6 L := mul_mem (hd _ (rootDiagUnit_mem_torusGroup b)) h2
    exact mul_mem (mul_mem h1 (mul_mem (mul_mem (hd _ hFd) h2) (inv_mem h1))) (inv_mem h3) |> fun h => by
      simpa [mul_assoc] using h
  have hmaps : MapsRootLines ((nw' * F y₀ * nw'⁻¹) * y₀⁻¹) (w' * (1 * w) * w'⁻¹ * (1 * w)⁻¹) := by
    have h1 : MapsRootLines nw' w' := mapsRootLines_canonicalRep w'
    have hFy₀ : F y₀ = F (rootDiagUnit Tag.E6 b) * nw := by rw [hy₀, map_mul, hFn]
    have h2 : MapsRootLines (F (rootDiagUnit Tag.E6 b) * nw) (1 * w) :=
      (mapsRootLines_of_mem_torusGroup hFd).mul (mapsRootLines_canonicalRep w)
    have h4 : MapsRootLines y₀ (1 * w) :=
      (mapsRootLines_of_mem_torusGroup (rootDiagUnit_mem_torusGroup b)).mul
        (mapsRootLines_canonicalRep w)
    rw [hFy₀]
    exact ((h1.mul h2).mul h1.inv).mul h4.inv
  have := mem_kernelReflectionGroup_of_mapsRootLines hmono hmaps hg₀M
  simpa using this

theorem kernel_facts {a : Fin Tag.E6.rank → Lˣ} {b3 : Fin Tag.E6.rank → ZMod 3}
    (hker : ∀ x, rootCharHom3 a x = 1 ↔ triChar b3 x = 1) :
    (∀ x : WeylGroup Tag.E6, x ∈ rootCharStabilizer a ↔ x ∈ charStabilizer (triChar b3)) ∧
    kernelReflectionGroup a = kernelWeylGroup (triChar b3) ∧
    ∀ x : Fin Tag.E6.rank → ℤ, rootChar a x = 1 ↔ triPairing b3 x = 0 := by
  refine ⟨fun x => ?_, ?_, fun x => ?_⟩
  · rw [← charStabilizer_congr_ker hker]
    exact Iff.rfl
  · exact (show kernelReflectionGroup a = kernelWeylGroup (rootCharHom3 a) from rfl).trans
      (kernelWeylGroup_congr_ker hker)
  · have h := hker (Multiplicative.ofAdd x)
    rw [triChar_apply, Z3.ofAdd_eq_one] at h
    exact h

theorem rootDiag_mul_canonicalRep_facts (b : Fin Tag.E6.rank → Lˣ) (w : WeylGroup Tag.E6) :
    rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w ∈ monomialSubgroup Tag.E6 L ∧
    MapsRootLines (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) w := by
  refine ⟨mul_mem (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup b))
    (canonicalRep_mem_monomialSubgroup' w), ?_⟩
  have := (mapsRootLines_of_mem_torusGroup (rootDiagUnit_mem_torusGroup b)).mul
    (mapsRootLines_canonicalRep (R := L) w)
  rwa [one_mul] at this

theorem heis_straighten_core {f : ℕ} (hf : 1 ≤ f)
    {a b : Fin Tag.E6.rank → Lˣ} (ha3 : ∀ i, a i ^ 3 = 1)
    {w w' : WeylGroup Tag.E6} (hw : w ∈ rootCharStabilizer a)
    (hsh : rootChar a (e6Shift w) ≠ 1) {u y : ModGL Tag.E6 L} (hu : u ∈ heisM a)
    (hyd : y = u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u)
    (hT : canonicalRep (coxeterSystem Tag.E6) L w' *
        entrywiseFrobGL Tag.E6 L ℓ f (rootDiagUnit Tag.E6 a) *
        (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ = rootDiagUnit Tag.E6 a)
    (hy : canonicalRep (coxeterSystem Tag.E6) L w' * entrywiseFrobGL Tag.E6 L ℓ f y *
        (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ = y) :
    ((ℓ ^ f : ℕ) : ZMod 3) = 1 ∧ ∃ (j : ℕ) (z : ModGL Tag.E6 L), z ∈ heisM a ∧
      entrywiseFrobGL Tag.E6 L ℓ f z = z * (y ^ j * canonicalRep (coxeterSystem Tag.E6) L w') ∧
      entrywiseFrobGL Tag.E6 L ℓ f (z * y * z⁻¹) = z * y * z⁻¹ ∧
      z * y * z⁻¹ ∈ Subgroup.normalizer (heisM a : Set (ModGL Tag.E6 L)) ∧
      ∃ m ∈ heisM a, z * y * z⁻¹ = m * canonicalRep (coxeterSystem Tag.E6) L w := by
  obtain ⟨b3, hker⟩ := exists_triData_lattice ha3
  obtain ⟨hS, hKW, hχ⟩ := kernel_facts hker
  have hrelF : ∀ v, rootChar a (w' • v) = rootChar a v ^ (ℓ ^ f) :=
    rootChar_frob_of_conj a w' hT.symm
  have hrel3 := triPairing_frob_rel hker hrelF
  have hnw : canonicalRep (coxeterSystem Tag.E6) L w ∈
      Subgroup.normalizer (heisM a : Set (ModGL Tag.E6 L)) :=
    canonicalRep_mem_normalizer_familyGroup (a := fun _ : Unit => a) (fun _ => hw)
  have hnw' : canonicalRep (coxeterSystem Tag.E6) L w' ∈
      Subgroup.normalizer (heisM a : Set (ModGL Tag.E6 L)) := by
    refine canonicalRep_mem_normalizer_of_image (a := fun _ : Unit => a) ?_
    refine image_eq_of_mem_stab _ w' (fun β hβ => ?_) (fun β hβ => ?_)
    · exact (family_w_stab (a := fun _ : Unit => a) (p := ℓ) (e := f) (fun _ v => hrelF v) hβ).1
    · exact (family_w_stab (a := fun _ : Unit => a) (p := ℓ) (e := f) (fun _ v => hrelF v) hβ).2
  have hcomm := commutator_mem_kernel (f := f) (b := b) hnw hnw' hu (hyd ▸ hy)
  rw [hKW] at hcomm
  have hsh3 : triPairing b3 (e6Shift w) ≠ 0 := (not_congr (hχ _)).1 hsh
  have hq : ((ℓ ^ f : ℕ) : ZMod 3) = 1 :=
    q_eq_one_of_commutator ((hS w).1 hw) hsh3 hrel3 hcomm
  refine ⟨hq, ?_⟩
  have hw'S : w' ∈ charStabilizer (triChar b3) := fun v => by
    rw [triChar_apply, triChar_apply, hrel3 v, hq, one_mul]
  obtain ⟨j, hj⟩ := exists_pow_mul_mem_kernelWeylGroup ((hS w).1 hw) hw'S hsh3
  rw [← hKW] at hj
  obtain ⟨hy₀mono, hy₀maps⟩ := rootDiag_mul_canonicalRep_facts (L := L) b w
  have hdb : rootDiagUnit Tag.E6 b ∈ heisM a := torus_le_heisM a (rootDiagUnit_mem_torusGroup b)
  have hyN : y ∈ Subgroup.normalizer (heisM a : Set (ModGL Tag.E6 L)) := by
    rw [hyd]
    exact mul_mem (mul_mem (inv_mem (Subgroup.le_normalizer hu))
      (mul_mem (Subgroup.le_normalizer hdb) hnw)) (Subgroup.le_normalizer hu)
  have e1 : y ^ j = u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) ^ j * u := by
    have := conj_pow (a := u⁻¹) (b := rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) (i := j)
    rw [inv_inv] at this
    rw [hyd]
    exact this
  have hcM : y ^ j * canonicalRep (coxeterSystem Tag.E6) L w' ∈ heisM a := by
    have e2 : y ^ j * canonicalRep (coxeterSystem Tag.E6) L w' =
        u⁻¹ * ((rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) ^ j *
          canonicalRep (coxeterSystem Tag.E6) L w') *
          ((canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ * u *
            canonicalRep (coxeterSystem Tag.E6) L w') := by
      rw [e1]; group
    rw [e2]
    refine mul_mem (mul_mem (inv_mem hu) ?_) ?_
    · exact mem_heisM_of_mapsRootLines
        (mul_mem (pow_mem hy₀mono j) (canonicalRep_mem_monomialSubgroup' w'))
        ((E8Lift.mapsRootLines_pow hy₀maps j).mul (mapsRootLines_canonicalRep w')) hj
    · have := (Subgroup.mem_normalizer_iff.1 (inv_mem hnw') u).1 hu
      simpa using this
  obtain ⟨z, hz, hzc⟩ := lang_familyGroup ℓ (fun _ : Unit => a) f hf 1 (one_mem _) _ hcM
  have hFz : entrywiseFrobGL Tag.E6 L ℓ f z =
      z * (y ^ j * canonicalRep (coxeterSystem Tag.E6) L w') := by
    simp only [one_mul, inv_one, mul_one] at hzc
    rw [← hzc]
    group
  have hcy : (y ^ j * canonicalRep (coxeterSystem Tag.E6) L w') * entrywiseFrobGL Tag.E6 L ℓ f y *
      (y ^ j * canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ = y := by
    calc (y ^ j * canonicalRep (coxeterSystem Tag.E6) L w') * entrywiseFrobGL Tag.E6 L ℓ f y *
        (y ^ j * canonicalRep (coxeterSystem Tag.E6) L w')⁻¹
        = y ^ j * (canonicalRep (coxeterSystem Tag.E6) L w' * entrywiseFrobGL Tag.E6 L ℓ f y *
          (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹) * (y ^ j)⁻¹ := by group
      _ = y ^ j * y * (y ^ j)⁻¹ := by rw [hy]
      _ = y := by group
  refine ⟨j, z, hz, hFz, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, hFz]
    calc z * (y ^ j * canonicalRep (coxeterSystem Tag.E6) L w') * entrywiseFrobGL Tag.E6 L ℓ f y *
        (z * (y ^ j * canonicalRep (coxeterSystem Tag.E6) L w'))⁻¹
        = z * ((y ^ j * canonicalRep (coxeterSystem Tag.E6) L w') * entrywiseFrobGL Tag.E6 L ℓ f y *
          (y ^ j * canonicalRep (coxeterSystem Tag.E6) L w')⁻¹) * z⁻¹ := by group
      _ = z * y * z⁻¹ := by rw [hcy]
  · exact mul_mem (mul_mem (Subgroup.le_normalizer hz) hyN) (inv_mem (Subgroup.le_normalizer hz))
  · refine ⟨z * u⁻¹ * rootDiagUnit Tag.E6 b *
      (canonicalRep (coxeterSystem Tag.E6) L w * (u * z⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹), ?_, ?_⟩
    · refine mul_mem (mul_mem (mul_mem hz (inv_mem hu)) hdb) ?_
      exact (Subgroup.mem_normalizer_iff.1 hnw (u * z⁻¹)).1 (mul_mem hu (inv_mem hz))
    · rw [hyd]
      group

end Core

section Frame

variable {K : Type} [Field K] [Finite K]

theorem frame_straighten (hK4 : 4 ≤ Nat.card K)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : CFSG.IsElementaryAbelian 3 E)
    (F : E6HeisenbergFrame K E) :
    ∃ y' : ModGL Tag.E6 (AlgebraicClosure K),
      y' ∈ Subgroup.normalizer (heisM F.a : Set (ModGL Tag.E6 (AlgebraicClosure K))) ∧
      (∃ m ∈ heisM F.a, y' = m * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w) ∧
      y' ^ 3 = 1 ∧ Units.map (entrywiseHom F.Fr) y' = y' ∧
      ∀ x ∈ heisM F.a, x ≠ 1 → x ^ ringChar K = 1 → Units.map (entrywiseHom F.Fr) x = x →
        Commute x y' →
        ∃ v : ModGL Tag.E6 (AlgebraicClosure K),
          v ∈ adjointGroup Tag.E6 (AlgebraicClosure K) ∧ v ≠ 1 ∧ v ^ ringChar K = 1 ∧
          Units.map (entrywiseHom F.Fr) v = v ∧
          Commute v (baseChangeGL (algebraMap K (AlgebraicClosure K)) (F.g₁ : ModGL Tag.E6 K)) ∧
          Commute v (baseChangeGL (algebraMap K (AlgebraicClosure K)) (F.g₂ : ModGL Tag.E6 K)) := by
  classical
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hFrEq : F.Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) e :=
    RingHom.ext fun c => by rw [F.hFr c, iterateFrobenius_def, hcard]
  have hFrob : ∀ g : ModGL Tag.E6 (AlgebraicClosure K),
      Units.map (entrywiseHom F.Fr) g =
        entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e g := by
    intro g
    rw [hFrEq]
  have hg0F : entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e F.g0 =
      F.g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w' := by
    rw [← hFrob]
    exact F.hg0
  have hBF : ∀ z : ModGL Tag.E6 K, entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) z) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) z := by
    intro z
    rw [← hFrob]
    exact CFSG.RankThree.PartOne.KE.baseChangeGL_frobenius_fixed F.Fr F.hFr z
  have hT : canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w' *
      entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e (rootDiagUnit Tag.E6 F.a) *
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w')⁻¹ =
      rootDiagUnit Tag.E6 F.a := by
    have := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 F.hT).2
    rwa [hFrob] at this
  set y : ModGL Tag.E6 (AlgebraicClosure K) := F.u⁻¹ * (rootDiagUnit Tag.E6 F.b *
    canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w) * F.u with hyd
  have hyg : y = F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (F.g₂ : ModGL Tag.E6 K) * F.g0 := F.hg₂.symm
  have hy : canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w' *
      entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e y *
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w')⁻¹ = y := by
    have hFy : entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e y =
        (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w')⁻¹ * y *
          canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w' := by
      rw [hyg, map_mul, map_mul, map_inv, hg0F, hBF]
      group
    rw [hFy]
    group
  have hy3 : y ^ 3 = 1 := by
    have hinj := e6InndiagConj_injective K hK4
    have hg₂3 : F.g₂ ^ 3 = 1 := hinj (by
      rw [map_pow, map_one]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ F.hE₂)
    have hd₂3 : (F.g₂ : ModGL Tag.E6 K) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hg₂3
    have h1 := conj_pow (a := F.g0⁻¹) (b := baseChangeGL (algebraMap K (AlgebraicClosure K))
      (F.g₂ : ModGL Tag.E6 K)) (i := 3)
    rw [inv_inv, ← map_pow, hd₂3, map_one] at h1
    rw [hyg, h1]
    group
  have hu : F.u ∈ heisM F.a := rootSpan_le_heisM F.a F.hu
  obtain ⟨-, j, z, hz, hFz, hFy, hyN, m, hm, hym⟩ := heis_straighten_core (ℓ := ringChar K) he
    F.ha3 F.hw F.hsh hu hyd hT hy
  have hzadj : z ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := heisM_le_adjoint F.a hz
  refine ⟨z * y * z⁻¹, hyN, ⟨m, hm, hym⟩, ?_, ?_, ?_⟩
  · have h1 := conj_pow (a := z) (b := y) (i := 3)
    rw [h1, hy3]
    group
  · rw [hFrob]
    exact hFy
  · intro x hxM hx1 hxp hxF hxc
    rw [hFrob] at hxF
    have hXM : z⁻¹ * x * z ∈ heisM F.a := mul_mem (mul_mem (inv_mem hz) hxM) hz
    have hXy : (z⁻¹ * x * z) * y = y * (z⁻¹ * x * z) := by
      have h := hxc.eq
      calc (z⁻¹ * x * z) * y = z⁻¹ * (x * (z * y * z⁻¹)) * z := by group
        _ = z⁻¹ * ((z * y * z⁻¹) * x) * z := by rw [h]
        _ = y * (z⁻¹ * x * z) := by group
    have hXyj : (z⁻¹ * x * z) * y ^ j = y ^ j * (z⁻¹ * x * z) :=
      (Commute.pow_right (show Commute (z⁻¹ * x * z) y from hXy) j).eq
    refine ⟨F.g0 * (z⁻¹ * x * z) * F.g0⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_mem (mul_mem F.hg0C (heisM_le_adjoint F.a hXM)) (inv_mem F.hg0C)
    · intro h
      apply hx1
      calc x = z * (F.g0⁻¹ * (F.g0 * (z⁻¹ * x * z) * F.g0⁻¹) * F.g0) * z⁻¹ := by group
        _ = 1 := by rw [h]; group
    · have h1 := conj_pow (a := F.g0) (b := z⁻¹ * x * z) (i := ringChar K)
      have h2 := conj_pow (a := z⁻¹) (b := x) (i := ringChar K)
      rw [inv_inv] at h2
      rw [h1, h2, hxp]
      group
    · rw [hFrob, map_mul, map_mul, map_inv, hg0F, map_mul, map_mul, map_inv, hFz, hxF]
      calc F.g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w' *
          ((z * (y ^ j * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w'))⁻¹ * x *
            (z * (y ^ j * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w'))) *
          (F.g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w')⁻¹
          = F.g0 * ((y ^ j)⁻¹ * (z⁻¹ * x * z) * y ^ j) * F.g0⁻¹ := by group
        _ = F.g0 * (z⁻¹ * x * z) * F.g0⁻¹ := by
          rw [show (y ^ j)⁻¹ * (z⁻¹ * x * z) * y ^ j = z⁻¹ * x * z by
            rw [mul_assoc, hXyj, ← mul_assoc, inv_mul_cancel, one_mul]]
    · have hg₁ : baseChangeGL (algebraMap K (AlgebraicClosure K)) (F.g₁ : ModGL Tag.E6 K) =
          F.g0 * rootDiagUnit Tag.E6 F.a * F.g0⁻¹ := by
        rw [← F.hg₁]
        group
      rw [hg₁]
      have hc := heisM_comm F.a hXM
      show _ * _ = _ * _
      calc F.g0 * (z⁻¹ * x * z) * F.g0⁻¹ * (F.g0 * rootDiagUnit Tag.E6 F.a * F.g0⁻¹)
          = F.g0 * ((z⁻¹ * x * z) * rootDiagUnit Tag.E6 F.a) * F.g0⁻¹ := by group
        _ = F.g0 * (rootDiagUnit Tag.E6 F.a * (z⁻¹ * x * z)) * F.g0⁻¹ := by rw [hc]
        _ = _ := by group
    · have hg₂ : baseChangeGL (algebraMap K (AlgebraicClosure K)) (F.g₂ : ModGL Tag.E6 K) =
          F.g0 * y * F.g0⁻¹ := by
        rw [hyg]
        group
      rw [hg₂]
      show _ * _ = _ * _
      calc F.g0 * (z⁻¹ * x * z) * F.g0⁻¹ * (F.g0 * y * F.g0⁻¹)
          = F.g0 * ((z⁻¹ * x * z) * y) * F.g0⁻¹ := by group
        _ = F.g0 * (y * (z⁻¹ * x * z)) * F.g0⁻¹ := by rw [hXy]
        _ = _ := by group

end Frame


end CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4
