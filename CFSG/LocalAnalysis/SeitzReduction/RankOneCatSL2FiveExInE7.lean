module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExInTorus
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExTwoPartE
public import CFSG.LocalAnalysis.SteinbergBMOddResidualE7Lift

public noncomputable section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

namespace FiveExIn

theorem two_pow_six_dvd_card_inf {G : Type*} [Group G] {R H B : Subgroup G} [Finite R]
    (hBR : B ≤ R) (hidx : (H.subgroupOf R).index ≤ 2) (hB : IsPGroup 2 B)
    (hcard : 2 ^ 7 ≤ Nat.card B) : 2 ^ 6 ∣ Nat.card ↥(H ⊓ B) := by
  have hR0 : (H.subgroupOf R).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : H.relIndex B ≤ 2 := (Subgroup.relIndex_le_of_le_right hBR hR0).trans hidx
  have hmul := Subgroup.relIndex_mul_card H B
  have hfin : Finite ↥(H ⊓ B) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right.trans hBR : H ⊓ B ≤ R))
  have h6 : 2 ^ 6 ≤ Nat.card ↥(H ⊓ B) := by
    have := Nat.mul_le_mul_right (Nat.card ↥(H ⊓ B)) hrel
    omega
  have hP : IsPGroup 2 ↥(H ⊓ B) := fun y => by
    obtain ⟨n, hn⟩ := hB ⟨y, y.2.2⟩
    exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn] at h6 ⊢
  exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).1 h6)

end FiveExIn

open FiveExIn in
theorem two_pow_six_dvd_card_E7_rational_centralizer
    (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (x : ModGL Tag.E7 L)
    (hxR : x ∈ adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _))
    (hx2 : x ^ 2 = 1) :
    2 ^ 6 ∣ Nat.card ↥(⁅adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus
        (MonoidHom.id _), adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus
        (MonoidHom.id _)⁆ ⊓ Subgroup.centralizer {x}) := by
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
  set S := (MulAut.conj v).toMonoidHom.comp F with hSdef
  set A := fourDiagGroup Tag.E7 L with hAdef
  have : Finite A := finite_fourDiagGroup
  have hq : Odd (p ^ e) := hcardK' ▸ hK
  have hSy : ∀ y ∈ A, S y = v * y ^ (p ^ e) * v⁻¹ := fun y hy => by
    change v * F y * v⁻¹ = _
    rw [hFdef, frobTwistGL_apply, one_mul, inv_one, mul_one,
      entrywiseFrobGL_of_mem_fourDiagGroup p e hy]
  have hSA : ∀ y ∈ A, S y ∈ A := fun y hy => by
    rw [hSy y hy]
    exact canonicalRep_conj_mem_fourDiagGroup ω (pow_mem hy _)
  have hS2 : ∀ y ∈ A, S (S y) = y := fun y hy => by
    rw [hSy _ (hSA y hy), hSy y hy, conj_pow, ← pow_mul, ← sq,
      pow_eq_self_of_mem_fourDiagGroup hy (sq_mod_four_of_odd hq)]
    obtain ⟨b, -, rfl⟩ := mem_fourDiagGroup.1 hy
    exact canonicalRep_conj_conj_of_mul_self hω2 b
  have hcard := card_le_card_fixedPoints_of_sq S (fun _ hy _ hy' => fourDiagGroup_comm hy hy')
    hSA hS2 signDiagGroup_le_fourDiagGroup (fun _ hy => signDiagGroup_mul_self hy)
    (fun _ hy => exists_mul_self_eq_of_mem_signDiagGroup hy)
  rw [card_signDiagGroup hL2] at hcard
  have hAS : A ⊓ S.eqLocus (MonoidHom.id _) ≤ fixedPointsIn Z S := fun y hy =>
    ⟨fourDiagGroup_le_toralCentralizer a hy.1, hy.2⟩
  set B := (A ⊓ S.eqLocus (MonoidHom.id _)).comap (MulAut.conj (z * g)).toMonoidHom with hBdef
  have hBR : B ≤ R ⊓ Subgroup.centralizer {x} := by
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := (SetLike.ext_iff.1 hconj _).2 (hAS hy)
    rwa [← (MulAut.conj (z * g)).injective hyy']
  have hBcard : Nat.card B =
      Nat.card (A ⊓ S.eqLocus (MonoidHom.id _) : Subgroup (ModGL Tag.E7 L)) := by
    rw [hBdef, Subgroup.comap_equiv_eq_map_symm',
      Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hBp : IsPGroup 2 B := fun y => by
    refine ⟨2, Subtype.ext ?_⟩
    have h4 := pow_four_of_mem_fourDiagGroup y.2.1
    rw [← map_pow, ← map_one (MulAut.conj (z * g)).toMonoidHom] at h4
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact (MulAut.conj (z * g)).injective h4
  have := hRfin
  have hdvd := two_pow_six_dvd_card_inf (hBR.trans inf_le_left) hidx hBp (hBcard ▸ hcard)
  have hfin : Finite ↥(H ⊓ Subgroup.centralizer {x}) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      ((inf_le_left.trans hHR) : H ⊓ Subgroup.centralizer {x} ≤ R))
  exact hdvd.trans (Subgroup.card_dvd_of_le fun y hy => ⟨hy.1, (hBR hy.2).2⟩)

theorem e7InnerTwoPartInput
    {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≤ 6) : E7InnerTwoPartInput p f k := by
  intro K _ _ hK α g a hαg hα
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := FiveExIn.one_le_of_card hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    LocalAnalysis.SteinbergBM.exists_mulEquiv_E7_inner_diagonal_fixed hp2 hf hK hαg hα2
  have hKodd : Odd (Nat.card K) := FiveExIn.odd_card hp hp2 hK
  set Lk := AlgebraicClosure K
  set Fr := iterateFrobenius Lk p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hFrdef, iterateFrobenius_def, hK]
  have hRF : fixedPointsIn (adjointGroup .E7 Lk) (frobTwistGL .E7 Lk p f 1) =
      adjointGroup Tag.E7 Lk ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    ext y
    refine and_congr_right fun _ => ?_
    change frobTwistGL .E7 Lk p f 1 y = y ↔ Units.map (entrywiseHom Fr) y = y
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  have hcard : Nat.card (fixedSubgroup α) = Nat.card ↥(⁅fixedPointsIn (adjointGroup .E7 Lk)
      (frobTwistGL .E7 Lk p f 1), fixedPointsIn (adjointGroup .E7 Lk)
      (frobTwistGL .E7 Lk p f 1)⁆ ⊓ Subgroup.centralizer {x}) := Nat.card_congr eA.toEquiv
  rw [hRF] at hcard hxR
  rw [hcard]
  exact (pow_dvd_pow 2 hk).trans
    (two_pow_six_dvd_card_E7_rational_centralizer K hKodd Lk Fr hFr x hxR hx2)

end CFSG.SeitzReduction.RankOne
