module

public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.RankThree.PartOne.SLB4A.ClassTwistedE6
import CFSG.GroupTheory.ElementaryAbelianTransport

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open TauCeti CFSG.Open

@[expose] def twE6W0Word : List (Fin 6) :=
  [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5,
    4, 3, 2, 0]

@[expose] def twE6W0 : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word twE6W0Word)

section Torus


theorem weylMatrix_twE6W0 : weylMatrix twE6W0 = -rhoMatrix :=
  weylMatrix_wordProd_e6 (by decide +kernel)

theorem twE6W0_smul (x : Fin Tag.E6.rank → ℤ) : twE6W0 • x = -(permLattice e6Rho x) := by
  rw [← weylMatrix_mulVec, weylMatrix_twE6W0, permLattice_eq_mulVec, Matrix.neg_mulVec]

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem conj_twistE6_rootDiagUnit_of_cube {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1)
    (b : Fin Tag.E6.rank → Ωˣ) (hb : ∀ i, b i ^ 3 = 1) :
    canonicalRep (coxeterSystem Tag.E6) Ω twE6W0 * twistE6 Ω Fr (rootDiagUnit Tag.E6 b) *
      (canonicalRep (coxeterSystem Tag.E6) Ω twE6W0)⁻¹ = rootDiagUnit Tag.E6 b := by
  have hb' : (fun i => Units.map Fr.toMonoidHom (b (e6Rho.symm i))) =
      (fun i => b (e6Rho.symm i)) ^ q := by
    funext i
    refine Units.ext ?_
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, hFr]
    rfl
  rw [twistE6_rootDiagUnit, hb', eq_comm, rootDiagUnit_eq_conj_canonicalRep_iff]
  intro v
  have hchar : rootChar ((fun i => b (e6Rho.symm i)) ^ q) v =
      rootChar b (permLattice e6Rho v) ^ q := by
    rw [CFSG.RankThree.Chevalley.rootChar_pow_tuple, ← rootChar_permLattice,
      CFSG.RankThree.Classical2.e6Rho_symm]
  rw [twE6W0_smul, rootChar_neg', hchar]
  have hz3 : rootChar b (permLattice e6Rho v) ^ 3 = 1 := by
    have h1 : b ^ 3 = 1 := funext fun i => hb i
    rw [← CFSG.RankThree.Chevalley.rootChar_pow_tuple, h1]
    simp [rootChar]
  obtain ⟨k, hk⟩ := h3
  have : rootChar b (permLattice e6Rho v) * rootChar b (permLattice e6Rho v) ^ q = 1 := by
    rw [← pow_succ', hk, pow_mul, hz3, one_pow]
  exact inv_eq_of_mul_eq_one_right this

@[expose] def cubeRootTuples (Ω : Type) [Field Ω] : Subgroup (Fin Tag.E6.rank → Ωˣ) :=
  Subgroup.pi Set.univ fun _ => rootsOfUnity 3 Ω

theorem mem_cubeRootTuples {b : Fin Tag.E6.rank → Ωˣ} :
    b ∈ cubeRootTuples Ω ↔ ∀ i, b i ^ 3 = 1 := by
  simp [cubeRootTuples, Subgroup.mem_pi, mem_rootsOfUnity]

theorem natCard_cubeRootTuples [IsAlgClosed Ω] (h3 : (3 : Ω) ≠ 0) :
    Nat.card (cubeRootTuples Ω) = 3 ^ 6 := by
  have : NeZero ((3 : ℕ) : Ω) := ⟨by exact_mod_cast h3⟩
  have := IsSepClosed.hasEnoughRootsOfUnity Ω 3
  have hr : Nat.card (rootsOfUnity 3 Ω) = 3 := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω 3
  let e : cubeRootTuples Ω ≃ (Fin Tag.E6.rank → rootsOfUnity 3 Ω) :=
    { toFun := fun b i => ⟨b.1 i, (Subgroup.mem_pi _).1 b.2 i (Set.mem_univ i)⟩
      invFun := fun c => ⟨fun i => (c i).1, (Subgroup.mem_pi _).2 fun i _ => (c i).2⟩
      left_inv := fun b => rfl
      right_inv := fun c => rfl }
  rw [Nat.card_congr e, Nat.card_fun, hr]
  simp
  rfl


end Torus

theorem isElemAbelian_map {A B : Type*} [CommGroup A] [Group B] (f : A →* B) (S : Subgroup A)
    (hS : ∀ a ∈ S, a ^ 3 = 1) : IsElemAbelian 3 (S.map f) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    exact Subtype.ext (by simp [← map_mul, mul_comm])
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hS a ha, map_one]

section Lang


variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem three_ne_zero_of_dvd_card_add_one {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (h3 : 3 ∣ ℓ ^ f + 1) : (3 : Ω) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : Ω) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff Ω ℓ] at h'
  have hl : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 h'
  subst hl
  have := (Nat.dvd_add_right (dvd_pow_self 3 (by omega : f ≠ 0))).1 h3
  omega

theorem exists_elemAbelian_three_pow_six_twistedFixed [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP Ω ℓ] (hf : 1 ≤ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (h3 : 3 ∣ ℓ ^ f + 1) :
    ∃ E : Subgroup (ModGL Tag.E6 Ω), E ≤ twistedFixedGroup TwistTag.E6 Ω Fr ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 := by
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one hf h3
  obtain ⟨g, hg, hgn⟩ := exists_inv_mul_twistE6_eq hf hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω twE6W0)
  let n0 := canonicalRep (coxeterSystem Tag.E6) Ω twE6W0
  let Ψ : (Fin Tag.E6.rank → Ωˣ) →* ModGL Tag.E6 Ω :=
    (MulAut.conj g).toMonoidHom.comp (rootDiagUnitHom Tag.E6 Ω)
  have hΨ : Function.Injective Ψ := fun a b h =>
    rootDiagUnit_injective ((MulAut.conj g).injective h)
  have hFg : twistE6 Ω Fr g = g * n0 := inv_mul_eq_iff_eq_mul.1 hgn
  refine ⟨(cubeRootTuples Ω).map Ψ, ?_, isElemAbelian_map Ψ _ (fun a ha => ?_), ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    have hb' := mem_cubeRootTuples.1 hb
    have hd : rootDiagUnit Tag.E6 b ∈ adjointGroup Tag.E6 Ω :=
      torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup b)
    have hFd : twistE6 Ω Fr (rootDiagUnit Tag.E6 b) = n0⁻¹ * rootDiagUnit Tag.E6 b * n0 := by
      have h := conj_twistE6_rootDiagUnit_of_cube hFr h3 b hb'
      calc twistE6 Ω Fr (rootDiagUnit Tag.E6 b)
          = n0⁻¹ * (n0 * twistE6 Ω Fr (rootDiagUnit Tag.E6 b) * n0⁻¹) * n0 := by group
        _ = n0⁻¹ * rootDiagUnit Tag.E6 b * n0 := by rw [h]
    refine (mem_phi3Rzero_iff).2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hg hd) (inv_mem hg)
    · show twistE6 Ω Fr (g * rootDiagUnit Tag.E6 b * g⁻¹) = g * rootDiagUnit Tag.E6 b * g⁻¹
      rw [map_mul, map_mul, map_inv, hFg, hFd]
      group
  · have hb' := mem_cubeRootTuples.1 ha
    exact funext fun i => hb' i
  · rw [Subgroup.card_map_of_injective hΨ, natCard_cubeRootTuples h30]

end Lang


theorem isElemAbelian_mono {M : Type*} [Group M] {X E : Subgroup M} (hXE : X ≤ E)
    (hE : IsElemAbelian 3 E) : IsElemAbelian 3 X := CFSG.Open.IsElemAbelian.mono hE hXE

theorem exists_elemAbelian_of_injective_hom {A M : Type*} [Group A] [Group M] (f : A →* M)
    (hf : Function.Injective f) {X : Subgroup M} (hXf : X ≤ f.range) (hX : IsElemAbelian 3 X) :
    ∃ E : Subgroup A, IsElemAbelian 3 E ∧ Nat.card E = Nat.card X := by
  refine ⟨X.comap f, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply hf
    have := hX.1.is_comm.comm ⟨f a.1, a.2⟩ ⟨f b.1, b.2⟩
    simpa using congrArg Subtype.val this
  · apply hf
    rw [map_pow, map_one]
    exact hX.2 _ hx
  · have h : (X.comap f).map f = X := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 hXf
    calc Nat.card (X.comap f) = Nat.card ((X.comap f).map f) :=
          (Subgroup.card_map_of_injective hf).symm
      _ = Nat.card X := by rw [h]

theorem three_pow_six_dvd_numerator {Q : ℕ} (h3 : 3 ∣ Q + 1) :
    3 ^ 6 ∣ Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 + 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 5 + 1) *
      (Q ^ 2 - 1) := by
  have hQ : Q % 3 = 2 := by omega
  have hpow : ∀ k, Q ^ k % 3 = 2 ^ k % 3 := fun k => by rw [Nat.pow_mod, hQ]
  have d12 : 3 ∣ Q ^ 12 - 1 := by have := hpow 12; norm_num at this; omega
  have d9 : 3 ∣ Q ^ 9 + 1 := by have := hpow 9; norm_num at this; omega
  have d8 : 3 ∣ Q ^ 8 - 1 := by have := hpow 8; norm_num at this; omega
  have d6 : 3 ∣ Q ^ 6 - 1 := by have := hpow 6; norm_num at this; omega
  have d5 : 3 ∣ Q ^ 5 + 1 := by have := hpow 5; norm_num at this; omega
  have d2 : 3 ∣ Q ^ 2 - 1 := by have := hpow 2; norm_num at this; omega
  have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
    (one_dvd (Q ^ 36)) d12) d9) d8) d6) d5) d2
  simpa using this

theorem three_pow_five_dvd_ordTwistedE6 {Q : ℕ} (h3 : 3 ∣ Q + 1) : 3 ^ 5 ∣ ordTwistedE6 Q := by
  unfold ordTwistedE6
  rw [Nat.gcd_eq_left h3]
  refine Nat.dvd_div_of_mul_dvd ?_
  have := three_pow_six_dvd_numerator h3
  rwa [show (3 : ℕ) * 3 ^ 5 = 3 ^ 6 by norm_num]

section Bridge


open CFSG.RankThree.PartOne.SLB4A in
theorem exists_equiv_graphFixedRootGroup_twistedE6 (q : PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K),
      Nat.card K = q.card ^ 2 ∧ (∀ x, σ x = x ^ q.card) ∧
        Nonempty ((TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group ≃*
          graphFixedRootGroup TwistTag.E6 K σ) :=
  exists_equiv_graphFixedRootGroup (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).twistedE6 q hv

theorem three_pow_four_dvd_card_twistedE6 (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) (h3 : 3 ∣ q.card + 1) :
    3 ^ 4 ∣ Nat.card (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_equiv_graphFixedRootGroup_twistedE6 q hv
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ 2 := by rw [hK, PrimePower.card_def]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by rw [hσ, PrimePower.card_def]
  have h3' : 3 ∣ q.p ^ q.exponent + 1 := by rwa [PrimePower.card_def] at h3
  rw [Nat.card_congr e.toEquiv,
    CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 q.prime_p q.exponent_pos hK' σ hσ']
  exact (pow_dvd_pow 3 (by norm_num)).trans (three_pow_five_dvd_ordTwistedE6 h3')

theorem exists_elemAbelian_27_twistedE6 (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) (h3 : 3 ∣ q.card + 1) :
    ∃ E : Subgroup (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group, IsElemAbelian 3 E ∧
      27 ≤ Nat.card E := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_equiv_graphFixedRootGroup_twistedE6 q hv
  have hℓ : q.p.Prime := q.prime_p
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hQ : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have : Fact q.p.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, hQ, ← pow_mul])
  let Ω := AlgebraicClosure K
  have : CharP Ω q.p := charP_of_injective_algebraMap (algebraMap K Ω).injective q.p
  let Fr : Ω →+* Ω := iterateFrobenius Ω q.p q.exponent
  have hFr : ∀ c, Fr c = c ^ (q.p ^ q.exponent) := fun c => iterateFrobenius_def ..
  have h3' : 3 ∣ q.p ^ q.exponent + 1 := by rwa [hQ] at h3
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ 2 := by rw [hK, hQ]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by rw [hσ, hQ]
  obtain ⟨E, hER, hEab, hEcard⟩ := exists_elemAbelian_three_pow_six_twistedFixed (Fr := Fr) hf hFr h3'
  obtain ⟨-, hle, hnormal, -⟩ :=
    exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6 hℓ hf K hK' σ hσ' Ω Fr hFr
  obtain ⟨hfin, -, -, -, -, hRcard, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK' σ hσ' Ω Fr hFr
  set R := twistedFixedGroup TwistTag.E6 Ω Fr with hRdef
  set G0 := graphFixedRootGroup TwistTag.E6 K σ with hG0
  set C := G0.map (baseChangeGL (algebraMap K Ω)) with hCdef
  have hCcard : Nat.card C = ordTwistedE6 (q.p ^ q.exponent) := by
    rw [hCdef, Subgroup.card_map_of_injective (baseChangeGL_injective _)]
    exact CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 hℓ hf hK' σ hσ'
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have h3N : 3 ∣ Nat.card R := by
    rw [hRcard]
    exact (dvd_pow_self 3 (by norm_num : (6 : ℕ) ≠ 0)).trans (three_pow_six_dvd_numerator h3')
  have hC3 : Nat.card C * 3 = Nat.card R := by
    rw [hCcard]
    unfold ordTwistedE6
    rw [Nat.gcd_eq_left h3', ← hRcard]
    exact Nat.div_mul_cancel h3N
  have hidx : (C.subgroupOf R).index = 3 := by
    have h := Subgroup.card_mul_index (C.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
    have hC0 : Nat.card C ≠ 0 := by
      intro h0
      rw [h0] at hC3
      omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hC0) (h.trans hC3.symm)
  have hrel : C.relIndex E ∣ 3 := by
    have h1 : (C.subgroupOf R).relIndex (E.subgroupOf R) = C.relIndex E := by
      have h2 : (E.subgroupOf R).map R.subtype = E := Subgroup.map_subgroupOf_eq_of_le hER
      have := Subgroup.relIndex_comap (H := C) R.subtype (E.subgroupOf R)
      exact this.trans (congrArg C.relIndex h2)
    have := hnormal
    rw [← h1, ← hidx]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  have hmul : C.relIndex E * Nat.card ↥(C ⊓ E) = 3 ^ 6 :=
    (Subgroup.relIndex_mul_card (H := C) (K := E)).trans hEcard
  have hr3 : C.relIndex E ≤ 3 := Nat.le_of_dvd (by norm_num) hrel
  have hXcard : 27 ≤ Nat.card ↥(C ⊓ E) := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith [hmul]
  have hX : IsElemAbelian 3 (C ⊓ E) := isElemAbelian_mono inf_le_right hEab
  have hinj : Function.Injective ((baseChangeGL (algebraMap K Ω)).comp G0.subtype) :=
    (baseChangeGL_injective _).comp Subtype.val_injective
  obtain ⟨E0, hE0, hE0card⟩ := exists_elemAbelian_of_injective_hom _ hinj
    (X := C ⊓ E) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := (Subgroup.mem_inf.1 hx).1
      exact ⟨⟨y, hy⟩, rfl⟩) hX
  obtain ⟨E1, hE1, hE1card⟩ := exists_elemAbelian_of_injective_hom e.toMonoidHom e.injective
    (X := E0) (fun x _ => ⟨e.symm x, by simp⟩) hE0
  exact ⟨E1, hE1, by rw [hE1card, hE0card]; exact hXcard⟩

end Bridge

end CFSG.HardMathSupport.Lang.E6Descent
