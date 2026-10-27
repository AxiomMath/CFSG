module

public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.Chevalley.LangPrimeFieldInvolutionTorus
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem card_le_sq_card_inf_centralizer {T : Subgroup G} [Finite T]
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hsq : ∀ y ∈ T, y * y = 1) {v : G}
    (hvT : ∀ y ∈ T, v * y * v⁻¹ ∈ T) (hv2 : ∀ y ∈ T, v * (v * y * v⁻¹) * v⁻¹ = y) :
    Nat.card T ≤ Nat.card (T ⊓ Subgroup.centralizer {v} : Subgroup G) ^ 2 := by
  let φ : T →* T :=
    { toFun := fun y => ⟨y * (v * y * v⁻¹), mul_mem y.2 (hvT y y.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y₁ y₂ => Subtype.ext (by
        change (y₁ : G) * y₂ * (v * (y₁ * y₂) * v⁻¹) =
          (y₁ * (v * y₁ * v⁻¹)) * (y₂ * (v * y₂ * v⁻¹))
        have e : v * ((y₁ : G) * y₂) * v⁻¹ = (v * y₁ * v⁻¹) * (v * y₂ * v⁻¹) := by group
        rw [e]
        have h := hcomm _ y₂.2 _ (hvT y₁ y₁.2)
        calc (y₁ : G) * y₂ * ((v * y₁ * v⁻¹) * (v * y₂ * v⁻¹))
            = y₁ * (y₂ * (v * y₁ * v⁻¹)) * (v * y₂ * v⁻¹) := by group
          _ = y₁ * ((v * y₁ * v⁻¹) * y₂) * (v * y₂ * v⁻¹) := by rw [h]
          _ = _ := by group) }
  set C := T ⊓ Subgroup.centralizer {v} with hC
  have hmemC : ∀ y : G, y ∈ C ↔ y ∈ T ∧ v * y * v⁻¹ = y := fun y => by
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨hy, by rw [← h, mul_inv_cancel_right]⟩
    · rintro ⟨hy, h⟩
      refine ⟨hy, ?_⟩
      calc y * v = (v * y * v⁻¹) * v := by rw [h]
        _ = v * y := by group
  have hker : φ.ker = C.subgroupOf T := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hmemC]
    constructor
    · intro h
      have h' : (y : G) * (v * y * v⁻¹) = 1 := congrArg Subtype.val h
      refine ⟨y.2, ?_⟩
      have := eq_inv_of_mul_eq_one_right h'
      rw [this, inv_eq_of_mul_eq_one_right (hsq y y.2)]
    · rintro ⟨-, h⟩
      exact Subtype.ext (by
        change (y : G) * (v * y * v⁻¹) = 1
        rw [h, hsq y y.2])
  have hrange : φ.range ≤ C.subgroupOf T := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_subgroupOf, hmemC]
    refine ⟨(φ y).2, ?_⟩
    change v * ((y : G) * (v * y * v⁻¹)) * v⁻¹ = y * (v * y * v⁻¹)
    have e : v * ((y : G) * (v * y * v⁻¹)) * v⁻¹ =
        (v * y * v⁻¹) * (v * (v * y * v⁻¹) * v⁻¹) := by group
    rw [e, hv2 y y.2]
    exact hcomm _ (hvT y y.2) _ y.2
  have hCT : C ≤ T := inf_le_left
  have hcardC : Nat.card (C.subgroupOf T) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCT).toEquiv
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hker, hcardC] at h1
  have h2 : Nat.card φ.range ≤ Nat.card C := by
    rw [← hcardC]
    exact Subgroup.card_le_of_le hrange
  rw [← h1, sq]
  exact Nat.mul_le_mul_left _ h2

end Group

section Weyl

variable {τ : Tag} {K : Type} [Field K]

@[expose] def weylTuple
    (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) : Fin τ.rank → Kˣ :=
  fun i => rootChar b (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))

theorem rootChar_weylTuple
    (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) (u : Fin τ.rank → ℤ) :
    rootChar (weylTuple w b) u = rootChar b (w⁻¹ • u) := by
  conv_rhs => rw [pi_eq_sum_univ u]
  rw [Finset.smul_sum, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (fun j => if i = j then (1 : ℤ) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [e, smul_comm, rootChar_zsmul]
  rfl

theorem canonicalRep_conj_rootDiagUnit
    (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) :
    canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ = rootDiagUnit τ (weylTuple w b) :=
  ((rootDiagUnit_eq_conj_canonicalRep_iff (weylTuple w b) b w).2 fun v => by
    rw [rootChar_weylTuple, inv_smul_smul]).symm

theorem weylTuple_weylTuple
    (w w' : WeylGroup τ) (b : Fin τ.rank → Kˣ) :
    weylTuple w (weylTuple w' b) = weylTuple (w * w') b := by
  funext i
  simp only [weylTuple]
  rw [rootChar_weylTuple, mul_inv_rev, mul_smul]

theorem weylTuple_one
    (b : Fin τ.rank → Kˣ) : weylTuple (1 : WeylGroup τ) b = b := by
  funext i
  simp only [weylTuple, inv_one, one_smul]
  simpa using rootChar_nsmul_single b i 1

theorem rootChar_sq_eq_one {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i ^ 2 = 1) (u : Fin τ.rank → ℤ) :
    rootChar b u ^ 2 = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem weylTuple_sq_eq_one
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i ^ 2 = 1) (w : WeylGroup τ)
    (i : Fin τ.rank) : weylTuple w b i ^ 2 = 1 :=
  rootChar_sq_eq_one hb _

end Weyl

section Aux

theorem commutator_subgroupOf_normal {G : Type*} [Group G] (R : Subgroup G) :
    (⁅R, R⁆.subgroupOf R).Normal := by
  have hcomm : ⁅R, R⁆.subgroupOf R = commutator R := by
    rw [← Subgroup.map_subtype_commutator, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
  rw [hcomm]
  infer_instance

theorem isSolvable_quotient_commutator_subgroupOf {G : Type*} [Group G] (R : Subgroup G)
    [(⁅R, R⁆.subgroupOf R).Normal] : Group.IsSolvable (R ⧸ ⁅R, R⁆.subgroupOf R) := by
  refine Group.isSolvable_of_comm fun a b => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : (((x * y)⁻¹ * (y * x) : R) : G) = ⁅(y : G)⁻¹, (x : G)⁻¹⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv, mul_inv_rev]
    group
  rw [e]
  exact Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2)

theorem exists_intUnit_eq_of_sq_eq_one {L : Type*} [Field L] {u : Lˣ} (hu : u ^ 2 = 1) :
    ∃ s : ℤˣ, Units.map (Int.castRingHom L).toMonoidHom s = u := by
  have h : (u : L) * u = 1 := by
    rw [← Units.val_mul, ← sq, hu, Units.val_one]
  rcases mul_self_eq_one_iff.1 h with h1 | h1
  · exact ⟨1, Units.ext (by simp [h1])⟩
  · exact ⟨-1, Units.ext (by simp [h1])⟩

end Aux

section Select

variable {G : Type*} [Group G]

theorem sixteen_le_of_dvd_of_le_sq {N : ℕ} (hdvd : N ∣ 2 ^ 7) (hle : 2 ^ 7 ≤ N ^ 2) :
    16 ≤ N := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  revert hle
  interval_cases k <;> norm_num

theorem exists_elemAbelian_eight_le_inf {R H B : Subgroup G} [Finite R] (hBR : B ≤ R)
    (hidx : (H.subgroupOf R).index ≤ 2) (hcomm : ∀ y ∈ B, ∀ y' ∈ B, y * y' = y' * y)
    (hsq : ∀ y ∈ B, y ^ 2 = 1) (hcard : 16 ≤ Nat.card B) :
    ∃ E : Subgroup G, E ≤ H ⊓ B ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  have hR0 : (H.subgroupOf R).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : H.relIndex B ≤ 2 := (Subgroup.relIndex_le_of_le_right hBR hR0).trans hidx
  have hmul := Subgroup.relIndex_mul_card H B
  have hfin : Finite ↥(H ⊓ B) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right.trans hBR : H ⊓ B ≤ R))
  have h8 : 8 ≤ Nat.card ↥(H ⊓ B) := by
    have := Nat.mul_le_mul_right (Nat.card ↥(H ⊓ B)) hrel
    omega
  have hP : IsPGroup 2 ↥(H ⊓ B) := fun y => ⟨1, Subtype.ext (by simpa using hsq y y.2.2)⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have h3 : 2 ^ 3 ∣ Nat.card ↥(H ⊓ B) := by
    rw [hn]
    refine pow_dvd_pow 2 ?_
    by_contra h
    have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 h3
  refine ⟨K.map (H ⊓ B).subtype, Subgroup.map_subtype_le K, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, y, -, rfl⟩ ⟨_, y', -, rfl⟩
    exact Subtype.ext (hcomm _ y.2.2 _ y'.2.2)
  · rintro _ ⟨y, -, rfl⟩
    exact hsq _ y.2.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
    norm_num

end Select

section SignDiag

variable {τ : Tag} {L : Type} [Field L]

theorem rootDiagUnit_conj_rootDiagUnit (a b : Fin τ.rank → Lˣ) :
    rootDiagUnit τ a * rootDiagUnit τ b * (rootDiagUnit τ a)⁻¹ = rootDiagUnit τ b := by
  rw [← rootDiagUnit_mul, mul_comm a b, rootDiagUnit_mul, mul_inv_cancel_right]

variable (τ L) in
@[expose] def signDiagGroup : Subgroup (ModGL τ L) :=
  ((rootDiagUnitHom τ L).comp (MonoidHom.compLeft (intUnitsMap L) (Fin τ.rank))).range

theorem mem_signDiagGroup {y : ModGL τ L} :
    y ∈ signDiagGroup τ L ↔ ∃ b : Fin τ.rank → Lˣ, (∀ i, b i ^ 2 = 1) ∧ rootDiagUnit τ b = y := by
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨fun i => intUnitsMap L (s i), fun i => ?_, rfl⟩
    rw [← map_pow, Int.units_sq, map_one]
  · rintro ⟨b, hb, rfl⟩
    choose s hs using fun i => exists_intUnit_eq_of_sq_eq_one (hb i)
    exact ⟨s, congrArg (rootDiagUnit τ) (funext hs)⟩

theorem card_signDiagGroup
    (hL : ringChar L ≠ 2) :
    Nat.card (signDiagGroup τ L) = 2 ^ τ.rank := by
  have hinj : Function.Injective
      ((rootDiagUnitHom τ L).comp (MonoidHom.compLeft (intUnitsMap L) (Fin τ.rank))) := by
    intro s s' h
    change rootDiagUnit τ (fun i => intUnitsMap L (s i)) =
      rootDiagUnit τ (fun i => intUnitsMap L (s' i)) at h
    funext i
    exact intUnitsMap_injective hL (congrFun (rootDiagUnit_injective h) i)
  rw [signDiagGroup, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int, Nat.card_fin]

theorem signDiagGroup_comm {y y' : ModGL τ L} (hy : y ∈ signDiagGroup τ L)
    (hy' : y' ∈ signDiagGroup τ L) : y * y' = y' * y := by
  obtain ⟨b, -, rfl⟩ := mem_signDiagGroup.1 hy
  obtain ⟨b', -, rfl⟩ := mem_signDiagGroup.1 hy'
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem signDiagGroup_mul_self {y : ModGL τ L} (hy : y ∈ signDiagGroup τ L) : y * y = 1 := by
  obtain ⟨b, hb, rfl⟩ := mem_signDiagGroup.1 hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_one]
  congr 1
  funext i
  rw [Pi.mul_apply, ← pow_two, hb, Pi.one_apply]

theorem canonicalRep_conj_mem_signDiagGroup
    (w : WeylGroup τ) {y : ModGL τ L}
    (hy : y ∈ signDiagGroup τ L) :
    canonicalRep (coxeterSystem τ) L w * y * (canonicalRep (coxeterSystem τ) L w)⁻¹ ∈
      signDiagGroup τ L := by
  obtain ⟨b, hb, rfl⟩ := mem_signDiagGroup.1 hy
  rw [canonicalRep_conj_rootDiagUnit]
  exact mem_signDiagGroup.2 ⟨_, weylTuple_sq_eq_one hb w, rfl⟩

theorem canonicalRep_conj_conj_of_mul_self
    {w : WeylGroup τ} (hw : w * w = 1)
    (b : Fin τ.rank → Lˣ) :
    canonicalRep (coxeterSystem τ) L w *
        (canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
          (canonicalRep (coxeterSystem τ) L w)⁻¹) *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootDiagUnit τ b := by
  rw [canonicalRep_conj_rootDiagUnit, canonicalRep_conj_rootDiagUnit, weylTuple_weylTuple, hw,
    weylTuple_one]

theorem signDiagGroup_le_toralCentralizer
    [IsAlgClosed L] (a : Fin τ.rank → Lˣ) :
    signDiagGroup τ L ≤ toralCentralizer τ L a := by
  intro y hy
  obtain ⟨b, -, rfl⟩ := mem_signDiagGroup.1 hy
  exact mem_toralCentralizer.2
    ⟨(exceptional_Lang_adjoint_diagonal_lift τ L b).1, rootDiagUnit_conj_rootDiagUnit a b⟩

end SignDiag

theorem odd_E7_rational_involution_fixed_eight_group
    (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (x : ModGL Tag.E7 L)
    (hxR : x ∈ adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _))
    (hx2 : x ^ 2 = 1) :
    ∃ E : Subgroup (ModGL Tag.E7 L),
      E ≤ ⁅adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _),
          adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)⁆ ⊓
        Subgroup.centralizer {x} ∧
      CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set p := ringChar K with hpdef
  have : CharP K p := ringChar.charP K
  obtain ⟨e', hpp, hcardK⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hpp⟩
  set e := (e' : ℕ) with hedef
  have he1 : 1 ≤ e := e'.pos
  have hcardK' : Nat.card K = p ^ e := by rw [Nat.card_eq_fintype_card, hcardK]
  have hp2 : p ≠ 2 := by
    intro h2
    rw [hcardK', h2] at hK
    exact (Nat.not_even_iff_odd.2 hK) ((Nat.even_pow' (by omega)).2 even_two)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hL2 : ringChar L ≠ 2 := by rw [ringChar.eq L p]; exact hp2
  have hFrIt : iterateFrobenius L p e = Fr := RingHom.ext fun c => by
    rw [iterateFrobenius_def, hFr, hcardK']
  set F := frobTwistGL Tag.E7 L p e 1 with hFdef
  have hF : ∀ g, F g = Units.map (entrywiseHom Fr) g := fun g => by
    rw [hFdef, frobTwistGL_apply, one_mul, inv_one, mul_one, ← hFrIt]
  have hRF : adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      fixedPointsIn (adjointGroup Tag.E7 L) F := by
    ext g
    refine and_congr_right fun _ => ?_
    change Units.map (entrywiseHom Fr) g = g ↔ F g = g
    rw [hF]
  obtain ⟨hRfin, hder, hidx⟩ := odd_E7_rational_derived_index_at_most_two K hK L Fr hFr
  rw [← hder] at hidx
  rw [hRF] at hRfin hidx hxR ⊢
  set R := fixedPointsIn (adjointGroup Tag.E7 L) F with hRdef
  set H := ⁅R, R⁆ with hHdef
  have hHR : H ≤ R := Subgroup.commutator_le_self R
  have hnorm := commutator_subgroupOf_normal R
  have hsolv := isSolvable_quotient_commutator_subgroupOf R
  have halg : letI := ZMod.algebra L p; Algebra.IsAlgebraic (ZMod p) L := by
    let _ : Algebra (ZMod p) L := ZMod.algebra L p
    refine ⟨fun y => ?_⟩
    obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := K) ({y} : Finset L)
    have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
    have : Fintype E := Fintype.ofFinite E
    have hpow : y ^ Fintype.card E = y := by
      have := FiniteField.pow_card (⟨y, hy⟩ : E)
      exact congrArg Subtype.val this
    have hcard : 1 < Fintype.card E := Fintype.one_lt_card
    refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) hcard, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]
  have hxG : x ∈ adjointGroup Tag.E7 L := hxR.1
  have hxF : F x = x := hxR.2
  obtain ⟨g, hg, a, ha, hgx⟩ :=
    exceptional_Lang_algebraic_prime_field_involution_torus hp2 L halg Tag.E7 hxG hx2
  have hFsign : ∀ b : Fin Tag.E7.rank → Lˣ, (∀ i, b i ^ 2 = 1) →
      F (rootDiagUnit Tag.E7 b) = rootDiagUnit Tag.E7 b := by
    intro b hb
    rw [hF]
    refine Units.ext ?_
    rw [Units.coe_map]
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    obtain ⟨s, hs⟩ := exists_intUnit_eq_of_sq_eq_one (hb i)
    rw [← hs, ← MonoidHom.comp_apply, ← Units.map_comp]
    exact congrArg (fun φ : ℤ →* L => Units.map φ s)
      (congrArg RingHom.toMonoidHom (RingHom.ext_int (Fr.comp (Int.castRingHom L))
        (Int.castRingHom L)))
  have hasq : ∀ i, a i ^ 2 = 1 := fun i => by
    rcases ha i with h | h <;> rw [h] <;> simp
  have ht : F (rootDiagUnit Tag.E7 a) = rootDiagUnit Tag.E7 a := hFsign a hasq
  have hFG : ∀ y ∈ adjointGroup Tag.E7 L, F y ∈ adjointGroup Tag.E7 L := fun y hy => by
    rw [hFdef, frobTwistGL_apply, one_mul, inv_one, mul_one]
    exact entrywiseFrobGL_mem p e hy
  set Z := toralCentralizer Tag.E7 L a with hZdef
  set M := toralRootGroup Tag.E7 L a with hMdef
  have hcZ : g * (F g)⁻¹ ∈ Z := by
    refine mem_toralCentralizer.2 ⟨mul_mem hg (inv_mem (hFG g hg)), ?_⟩
    have hFgx : F g * x * (F g)⁻¹ = rootDiagUnit Tag.E7 a := by
      rw [← ht, ← hgx, map_mul, map_mul, map_inv, hxF]
    calc rootDiagUnit Tag.E7 a * (g * (F g)⁻¹) * (rootDiagUnit Tag.E7 a)⁻¹
        = (g * x * g⁻¹) * (g * (F g)⁻¹) * (F g * x * (F g)⁻¹)⁻¹ := by rw [hgx, hFgx]
      _ = g * (F g)⁻¹ := by group
  obtain ⟨-, -, ⟨-, -, -, -, eW, heW⟩, -⟩ :=
    exceptional_toral_centralizer_identity_component Tag.E7 L hL2 a ha
  obtain ⟨w', hw'⟩ := QuotientGroup.mk_surjective (eW.symm (QuotientGroup.mk ⟨_, hcZ⟩))
  set χ := maskChar (signTupleBits a) with hχ
  obtain ⟨-, hΩle, hKWle, -, huniq, -, -, hΩ2, -⟩ :=
    sign_kernel_positive_Weyl_component_representatives Tag.E7 χ
  obtain ⟨⟨u, ω⟩, ⟨hu, hω, hwuω⟩, -⟩ :=
    huniq _ ((mem_rootCharStabilizer_iff hL2 ha).1 (mem_rootCharStabilizerSubgroup.1 w'.2))
  have hωW : ω ∈ rootCharStabilizerSubgroup a := (mem_rootCharStabilizer_iff hL2 ha).2 (hΩle hω)
  have huW : u ∈ rootCharStabilizerSubgroup a := (mem_rootCharStabilizer_iff hL2 ha).2 (hKWle hu)
  have huK : u ∈ kernelReflectionGroup a := by
    rw [kernelReflectionGroup_eq_kernelWeylGroup hL2 ha]
    exact hu
  have hω2 : ω * ω = 1 := by
    have hcard := hΩ2 rfl
    have hx : (⟨ω, hω⟩ : kernelPosStabilizer χ) ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := hcard
      rw [hk, pow_mul, pow_card_eq_one', one_pow]
    have := congrArg Subtype.val hx
    simpa [pow_two] using this
  have hmk : (QuotientGroup.mk w' : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) =
        QuotientGroup.mk ⟨ω, hωW⟩ := by
    have e : w' = ⟨u, huW⟩ * ⟨ω, hωW⟩ := Subtype.ext hwuω
    rw [e, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 huK), one_mul]
  have hnω := heW ⟨ω, hωW⟩
  rw [← hmk, hw', MulEquiv.apply_symm_apply] at hnω
  have hvZ : canonicalRep (coxeterSystem Tag.E7) L ω ∈ Z := canonicalRep_mem_toralCentralizer hωW
  have hdiv := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq_iff_div_mem.1 hnω)
  have hcv : ∃ m ∈ M, g * (F g)⁻¹ = m * canonicalRep (coxeterSystem Tag.E7) L ω :=
    ⟨g * (F g)⁻¹ / canonicalRep (coxeterSystem Tag.E7) L ω, hdiv, (div_mul_cancel _ _).symm⟩
  obtain ⟨z, -, -, hconj, -⟩ := rational_centralizer_cocycle_reduction_of_map_conj p hp2 he1
    (D := 1) (IsDiagramTwistMatrix.map_conj_eq (Or.inl rfl)) hRfin hHR ha hg hgx ht hvZ hcv
  set v := canonicalRep (coxeterSystem Tag.E7) L ω with hvdef
  set T := signDiagGroup Tag.E7 L with hTdef
  have hTcard : Nat.card T = 2 ^ 7 := card_signDiagGroup hL2
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hTcard]; norm_num)
  have hTv2 : ∀ y ∈ T, v * (v * y * v⁻¹) * v⁻¹ = y := by
    intro y hy
    obtain ⟨b, -, rfl⟩ := mem_signDiagGroup.1 hy
    exact canonicalRep_conj_conj_of_mul_self hω2 b
  have hA := card_le_sq_card_inf_centralizer (T := T) (fun _ hy _ hy' => signDiagGroup_comm hy hy')
    (fun _ hy => signDiagGroup_mul_self hy) (fun _ hy => canonicalRep_conj_mem_signDiagGroup ω hy)
    hTv2
  have hA16 : 16 ≤ Nat.card (T ⊓ Subgroup.centralizer {v} : Subgroup (ModGL Tag.E7 L)) :=
    sixteen_le_of_dvd_of_le_sq (hTcard ▸ Subgroup.card_dvd_of_le inf_le_left) (hTcard ▸ hA)
  have hAS : T ⊓ Subgroup.centralizer {v} ≤
      fixedPointsIn Z ((MulAut.conj v).toMonoidHom.comp F) := by
    rintro y ⟨hyT, hyv⟩
    refine ⟨signDiagGroup_le_toralCentralizer a hyT, ?_⟩
    obtain ⟨b, hb, rfl⟩ := mem_signDiagGroup.1 hyT
    change v * F (rootDiagUnit Tag.E7 b) * v⁻¹ = rootDiagUnit Tag.E7 b
    rw [hFsign b hb, mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hyv).symm
  set B := (T ⊓ Subgroup.centralizer {v}).comap (MulAut.conj (z * g)).toMonoidHom with hBdef
  have hBR : B ≤ R ⊓ Subgroup.centralizer {x} := by
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := (SetLike.ext_iff.1 hconj _).2 (hAS hy)
    rwa [← (MulAut.conj (z * g)).injective hyy']
  have hBcard :
      Nat.card B = Nat.card (T ⊓ Subgroup.centralizer {v} : Subgroup (ModGL Tag.E7 L)) := by
    rw [hBdef, Subgroup.comap_equiv_eq_map_symm',
      Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hBcomm : ∀ y ∈ B, ∀ y' ∈ B, y * y' = y' * y := by
    intro y hy y' hy'
    have h := signDiagGroup_comm hy.1 hy'.1
    rw [← map_mul, ← map_mul] at h
    exact (MulAut.conj (z * g)).injective h
  have hBsq : ∀ y ∈ B, y ^ 2 = 1 := by
    intro y hy
    have h := signDiagGroup_mul_self hy.1
    rw [← map_mul, ← map_one (MulAut.conj (z * g)).toMonoidHom] at h
    rw [pow_two]
    exact (MulAut.conj (z * g)).injective h
  obtain ⟨E, hEle, hEab, hEcard⟩ := exists_elemAbelian_eight_le_inf (hBR.trans inf_le_left) hidx
    hBcomm hBsq (hBcard ▸ hA16)
  exact ⟨E, fun y hy => ⟨(hEle hy).1, (hBR (hEle hy).2).2⟩, hEab, hEcard⟩

end CFSG.LieType.Chevalley
