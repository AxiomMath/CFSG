module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExInTorus
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExTwoPartE
public import CFSG.LocalAnalysis.SteinbergCEOddResidualTwistedE6Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6TwistedOuter

public noncomputable section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.Chevalley.ToralSign
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

namespace FiveExIn

@[expose] def e6Cube : Matrix (Fin (Tag.rank .E6)) (Fin (Tag.rank .E6)) ℤ :=
  !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6;
    4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

theorem e6Cube_mul_cartan : e6Cube * Tag.cartan .E6 = ((3 : ℕ) : ℤ) • 1 := by
  decide +kernel

theorem e6Cube_perm (i j : Fin TwistTag.E6.tag.rank) :
    e6Cube (TwistTag.E6.perm i) (TwistTag.E6.perm j) = e6Cube i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem cartanChar_prod_zpow_eq_pow' {τ : Tag} {K : Type} [Field K]
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {d : ℕ} (hB : B * τ.cartan = (d : ℤ) • 1)
    (c : Fin τ.rank → Kˣ) : cartanChar (fun i => ∏ j, c j ^ B j i) = c ^ d := by
  funext l
  calc ∏ i, (∏ j, c j ^ B j i) ^ τ.cartan i l
      = ∏ i, ∏ j, c j ^ (B j i * τ.cartan i l) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm
    _ = ∏ j, ∏ i, c j ^ (B j i * τ.cartan i l) := Finset.prod_comm
    _ = ∏ j, c j ^ ((B * τ.cartan) j l) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Matrix.mul_apply, Finset.prod_zpow_eq_zpow_sum]
    _ = (c ^ d) l := by
        rw [hB]
        simp [Matrix.one_apply]

theorem rootDiagUnit_pow_three_mem_graphFixedRootGroup_E6
    {K : Type} [Field K] {σ : K →+* K} {c : Fin TwistTag.E6.tag.rank → Kˣ}
    (hc : ∀ i, c (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (c i)) :
    rootDiagUnit TwistTag.E6.tag (c ^ 3) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  set b : Fin TwistTag.E6.tag.rank → Kˣ := fun i => ∏ j, c j ^ e6Cube j i with hbdef
  have hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i) := fun i => by
    calc ∏ j, c j ^ e6Cube j (TwistTag.E6.perm i)
        = ∏ j, c (TwistTag.E6.perm j) ^ e6Cube (TwistTag.E6.perm j) (TwistTag.E6.perm i) :=
          (Fintype.prod_equiv TwistTag.E6.perm _ _ fun _ => rfl).symm
      _ = ∏ j, c (TwistTag.E6.perm j) ^ e6Cube j i :=
          Finset.prod_congr rfl fun j _ => by rw [e6Cube_perm]
      _ = ∏ j, Units.map σ.toMonoidHom (c j) ^ e6Cube j i := by simp only [hc]
      _ = Units.map σ.toMonoidHom (∏ j, c j ^ e6Cube j i) := by
          rw [map_prod]
          simp only [map_zpow]
  obtain ⟨w, hw⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ) hb
  have key : cartanChar (compatDiag TwistTag.E6 σ w) = c ^ 3 := by
    rw [hw]
    exact cartanChar_prod_zpow_eq_pow' e6Cube_mul_cartan c
  rw [← key, ← list_prod_orbitH_eq_rootDiagUnit]
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact orbitH_mem_graphFixedRootGroup _ _ _ _

theorem e6_omegaWords_eq_nil : ∀ r ∈ e6SignDiagramReps, ∀ l ∈ r.omegaWords, l = [] := by
  intro r hr l hl
  simp only [e6SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    simpa [e6OmegaWords0, e6OmegaWords20, e6OmegaWords2] using hl

end FiveExIn

open FiveExIn in
theorem two_pow_six_dvd_card_twistedE6_rational_centralizer
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] {x : ModGL TwistTag.E6.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)))
    (hx2 : x ^ 2 = 1) :
    2 ^ 6 ∣ Nat.card ↥(⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
      fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
      Subgroup.centralizer {x}) := by
  classical
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  set D := diagramMap TwistTag.E6 k with hDdef
  have hD : (adjointGroup TwistTag.E6.tag k).map (MulAut.conj D).toMonoidHom =
      adjointGroup TwistTag.E6.tag k := map_conj_diagramMap TwistTag.E6 k (Or.inl rfl)
  set F := frobTwistGL TwistTag.E6.tag k p e D with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p he (by decide)
    (units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (iterateFrobenius k p e))
    (diagramMap_pow_order TwistTag.E6 k)
  have hFG : ∀ g ∈ adjointGroup TwistTag.E6.tag k, F g ∈ adjointGroup TwistTag.E6.tag k :=
    fun g hg => conj_mem_adjointGroup_of_map_eq hD _ (entrywiseFrobGL_mem p e hg)
  obtain ⟨hxG, hxF⟩ := mem_fixedPointsIn.1 hx
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨g, hg, r, hr, hgx, hFt⟩ := exists_conj_eq_rootDiagUnit_of_reps hp TwistTag.E6.perm F
    hFG (fun b hb => frobTwistGL_diagramMap_rootDiagUnit_of_sign p TwistTag.E6 e hb)
    e6SignDiagramReps h6.permChar_eq h6.exists_rep hxG hxF hx2
  set χ := signMaskChar TwistTag.E6.tag r.mask with hχ
  set a := signCharTuple (k := k) χ with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
  have hFgx : F g * x * (F g)⁻¹ = rootDiagUnit TwistTag.E6.tag a := by
    rw [← hFt, ← hgx, map_mul, map_mul, map_inv, hxF]
  have hcZ : g * (F g)⁻¹ ∈ toralCentralizer TwistTag.E6.tag k a := by
    refine mem_toralCentralizer.2 ⟨mul_mem hg (inv_mem (hFG g hg)), ?_⟩
    calc rootDiagUnit TwistTag.E6.tag a * (g * (F g)⁻¹) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ =
        (g * x * g⁻¹) * (g * (F g)⁻¹) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ := by rw [hgx]
      _ = g * (F g)⁻¹ * (F g * x * (F g)⁻¹) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ := by group
      _ = g * (F g)⁻¹ := by rw [hFgx]; group
  obtain ⟨-, -, ⟨hMZ, hMn, -, -, eW, heW⟩, -⟩ :=
    exceptional_toral_centralizer_identity_component TwistTag.E6.tag k hk a ha
  obtain ⟨q, hq⟩ := eW.surjective (QuotientGroup.mk ⟨_, hcZ⟩)
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hwχ : w ∈ charStabilizer χ := (mem_rootCharStabilizer_signCharTuple hk χ).1 hw
  obtain ⟨u, hu, hωΩ⟩ := exists_mul_mem_kernelPosStabilizer hwχ
  set ω := w * u with hω_def
  have huW : u ∈ kernelReflectionGroup a := by
    rw [kernelReflectionGroup_signCharTuple hk]
    exact hu
  have hωa : ω ∈ rootCharStabilizer a :=
    (mem_rootCharStabilizer_signCharTuple hk χ).2 (kernelPosStabilizer_le hωΩ)
  have hmk : (QuotientGroup.mk ⟨w, hw⟩ : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) =
        QuotientGroup.mk ⟨ω, hωa⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change w⁻¹ * (w * u) ∈ kernelReflectionGroup a
    rw [inv_mul_cancel_left]
    exact huW
  rw [hmk, heW, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
  change (canonicalRep (coxeterSystem TwistTag.E6.tag) k ω)⁻¹ * (g * (F g)⁻¹) ∈
    toralRootGroup TwistTag.E6.tag k a at hq
  obtain ⟨l, hl, hlω⟩ : ∃ l ∈ r.omegaWords, ToralSign.wordElt TwistTag.E6.tag l = ω := by
    exact (Set.ext_iff.1 (h6.coe_kernelPosStabilizer r hr) ω).1 hωΩ
  have hl0 : l = [] := e6_omegaWords_eq_nil r hr l hl
  have hω1 : ω = 1 := by rw [← hlω, hl0, ToralSign.wordElt_nil]
  rw [hω1, canonicalRep_one, inv_one, one_mul] at hq
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have := commutator_subgroupOf_normal R
  have := isSolvable_quotient_commutator_subgroupOf R
  obtain ⟨z, hzM, hzF, hconj, -⟩ := rational_centralizer_cocycle_reduction_of_map_conj p
    hp he hD hRfin hRsub ha hg hgx hFt (one_mem _) ⟨_, hq, (mul_one _).symm⟩
  have hg₁G : z * g ∈ adjointGroup TwistTag.E6.tag k :=
    mul_mem (mem_toralCentralizer.1 (hMZ hzM)).1 hg
  have hg₁R : z * g ∈ R := ⟨hg₁G, (mul_inv_eq_one.1 hzF).symm⟩
  set Fr := iterateFrobenius k p e with hFrdef
  have hFtw : ∀ y, F y = twistHom TwistTag.E6 k Fr y := fun y => by
    rw [twistHom_apply]
    rfl
  have hRtw : R = twistedFixedGroup TwistTag.E6 k Fr := by
    ext y
    rw [mem_twistedFixedGroup_iff_twistHom, ← hFtw]
    exact Iff.rfl
  have hFrsurj : Function.Surjective Fr := fun y => by
    obtain ⟨c, hc⟩ :=
      IsAlgClosed.exists_pow_nat_eq y (n := p ^ e) (pow_pos (Fact.out : p.Prime).pos e)
    exact ⟨c, by rw [hFrdef, iterateFrobenius_def, hc]⟩
  set σL : k ≃+* k := RingEquiv.ofBijective Fr ⟨Fr.injective, hFrsurj⟩ with hσLdef
  have hσL : σL.toRingHom = Fr := RingHom.ext fun _ => rfl
  obtain ⟨-, -, hder⟩ := odd_diagram_fixed_root_group_perfect TwistTag.E6 k hk σL
  rw [hσL, ← hRtw] at hder
  set A := fourDiagGroup TwistTag.E6.tag k with hAdef
  have : Finite A := finite_fourDiagGroup
  have hq2 : Odd (p ^ e) := ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp).pow
  have hDb : ∀ b : Fin TwistTag.E6.tag.rank → kˣ, D * rootDiagUnit TwistTag.E6.tag b * D⁻¹ =
      rootDiagUnit TwistTag.E6.tag fun i => b (TwistTag.E6.perm.symm i) := fun b => by
    have h := congrArg (fun f : ModGL TwistTag.E6.tag k →* ModGL TwistTag.E6.tag k =>
      f (rootDiagUnit TwistTag.E6.tag b)) (conj_diagramMap_eq_twistHom TwistTag.E6 k)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [h, twistHom_rootDiagUnit_eq]
    rfl
  have hperm2 : ∀ i, TwistTag.E6.perm.symm (TwistTag.E6.perm.symm i) = i := fun i => by
    fin_cases i <;> rfl
  have hDA : ∀ y ∈ A, D * y * D⁻¹ ∈ A := fun y hy => by
    obtain ⟨b, hb, rfl⟩ := mem_fourDiagGroup.1 hy
    rw [hDb]
    exact mem_fourDiagGroup.2 ⟨_, fun i => hb _, rfl⟩
  have hDD : ∀ y ∈ A, D * (D * y * D⁻¹) * D⁻¹ = y := fun y hy => by
    obtain ⟨b, -, rfl⟩ := mem_fourDiagGroup.1 hy
    rw [hDb, hDb]
    congr 1
    funext i
    rw [hperm2]
  set S := (MulAut.conj (1 : ModGL TwistTag.E6.tag k)).toMonoidHom.comp F with hSdef
  have hSy : ∀ y ∈ A, S y = D * y ^ (p ^ e) * D⁻¹ := fun y hy => by
    change 1 * F y * 1⁻¹ = _
    rw [one_mul, inv_one, mul_one, hF, frobTwistGL_apply,
      entrywiseFrobGL_of_mem_fourDiagGroup p e hy]
  have hSA : ∀ y ∈ A, S y ∈ A := fun y hy => by
    rw [hSy y hy]
    exact hDA _ (pow_mem hy _)
  have hS2 : ∀ y ∈ A, S (S y) = y := fun y hy => by
    rw [hSy _ (hSA y hy), hSy y hy, conj_pow, ← pow_mul, ← sq,
      pow_eq_self_of_mem_fourDiagGroup hy (sq_mod_four_of_odd hq2)]
    exact hDD y hy
  have hcard := card_le_card_fixedPoints_of_sq S (fun _ hy _ hy' => fourDiagGroup_comm hy hy')
    hSA hS2 signDiagGroup_le_fourDiagGroup (fun _ hy => signDiagGroup_mul_self hy)
    (fun _ hy => exists_mul_self_eq_of_mem_signDiagGroup hy)
  rw [card_signDiagGroup hk] at hcard
  have hAH : ∀ y ∈ A, S y = y → y ∈ ⁅R, R⁆ := fun y hy hSy' => by
    obtain ⟨b, hb4, rfl⟩ := mem_fourDiagGroup.1 hy
    have hFb : twistHom TwistTag.E6 k Fr (rootDiagUnit TwistTag.E6.tag b) =
        rootDiagUnit TwistTag.E6.tag b := by
      rw [← hFtw]
      have h1 : S (rootDiagUnit TwistTag.E6.tag b) = F (rootDiagUnit TwistTag.E6.tag b) := by
        change 1 * F (rootDiagUnit TwistTag.E6.tag b) * 1⁻¹ = _
        rw [one_mul, inv_one, mul_one]
      rw [← h1, hSy']
    have hcomp := compat_of_twistHom_rootDiagUnit hFb
    have hc : ∀ i, (b ^ 3) (TwistTag.E6.perm i) = Units.map Fr.toMonoidHom ((b ^ 3) i) :=
      fun i => by rw [Pi.pow_apply, Pi.pow_apply, hcomp, map_pow]
    have hb9 : (b ^ 3) ^ 3 = b := by
      funext i
      rw [Pi.pow_apply, Pi.pow_apply, ← pow_mul,
        show 3 * 3 = 4 * 2 + 1 by rfl, pow_succ, pow_mul, hb4 i, one_pow, one_mul]
    rw [hder, ← hb9]
    exact rootDiagUnit_pow_three_mem_graphFixedRootGroup_E6 hc
  have hAS : A ⊓ S.eqLocus (MonoidHom.id _) ≤
      fixedPointsIn (toralCentralizer TwistTag.E6.tag k a) S := fun y hy =>
    ⟨fourDiagGroup_le_toralCentralizer a hy.1, hy.2⟩
  set B := (A ⊓ S.eqLocus (MonoidHom.id _)).comap (MulAut.conj (z * g)).toMonoidHom with hBdef
  have hBR : B ≤ R ⊓ Subgroup.centralizer {x} := by
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := (SetLike.ext_iff.1 hconj _).2 (hAS hy)
    rwa [← (MulAut.conj (z * g)).injective hyy']
  have hnorm := commutator_subgroupOf_normal R
  have hBH : B ≤ ⁅R, R⁆ := by
    intro y hy
    have hyH : (MulAut.conj (z * g)) y ∈ ⁅R, R⁆ := hAH _ hy.1 hy.2
    have hyR : (MulAut.conj (z * g)) y ∈ R := Subgroup.commutator_le_self R hyH
    have h1 := hnorm.conj_mem ⟨_, hyR⟩ (Subgroup.mem_subgroupOf.2 hyH) ⟨_, inv_mem hg₁R⟩
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((⟨(z * g)⁻¹, inv_mem hg₁R⟩ : R) * ⟨_, hyR⟩ * (⟨(z * g)⁻¹, inv_mem hg₁R⟩ : R)⁻¹ :
        R) = (y : ModGL TwistTag.E6.tag k) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conj_apply, inv_inv]
      group
    rwa [h2] at h1
  have hBcard : Nat.card B =
      Nat.card (A ⊓ S.eqLocus (MonoidHom.id _) : Subgroup (ModGL TwistTag.E6.tag k)) := by
    rw [hBdef, Subgroup.comap_equiv_eq_map_symm',
      Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hBp : IsPGroup 2 B := fun y => by
    refine ⟨2, Subtype.ext ?_⟩
    have h4 := pow_four_of_mem_fourDiagGroup y.2.1
    rw [← map_pow, ← map_one (MulAut.conj (z * g)).toMonoidHom] at h4
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact (MulAut.conj (z * g)).injective h4
  have hB6 : 2 ^ 6 ∣ Nat.card B := by
    have : Finite B := Finite.of_injective _ (Subgroup.inclusion_injective
      ((hBR.trans inf_le_left) : B ≤ R))
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    have h6 : 2 ^ 6 ≤ 2 ^ n := hn ▸ hBcard ▸ hcard
    rw [hn]
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).1 h6)
  have hfin : Finite ↥(⁅R, R⁆ ⊓ Subgroup.centralizer {x}) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      ((inf_le_left.trans hRsub) : ⁅R, R⁆ ⊓ Subgroup.centralizer {x} ≤ R))
  exact hB6.trans (Subgroup.card_dvd_of_le fun y hy => ⟨hBH hy, (hBR hy).2⟩)

theorem twistedE6InnerTwoPartInput
    {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≤ 6) :
    TwistedE6InnerTwoPartInput p f k := by
  intro J _ hm α hα hαi
  have hadm := SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hm
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  have hF2 : Nat.card F = (p ^ f) ^ 2 := hF
  have : CharP F p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (show 1 ≤ f * 2 by omega) (by rw [hF2, ← pow_mul])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hα' : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hα'2 : MulAut.congr e α ^ 2 = 1 := by
    rw [← hα']
    exact pow_orderOf_eq_one _
  have hα'i : MulAut.congr e α ∈ twistedE6Inn F σ := by
    obtain ⟨g, hg⟩ := hαi
    exact ⟨e g, by rw [← hg, ComponentClassification.CatLeafProof.mulAut_congr_conj_twistedE6]⟩
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    LocalAnalysis.SteinbergCE.exists_mulEquiv_twisted_E6_inner_fixed hp2 hf hF2 σ hσ hα'2 hα'i
  have hcard : Nat.card (fixedSubgroup α) = Nat.card ↥(⁅fixedPointsIn
      (adjointGroup TwistTag.E6.tag (AlgebraicClosure F)) (frobTwistGL TwistTag.E6.tag
        (AlgebraicClosure F) p f (diagramMap TwistTag.E6 (AlgebraicClosure F))),
      fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure F))
        (frobTwistGL TwistTag.E6.tag (AlgebraicClosure F) p f
          (diagramMap TwistTag.E6 (AlgebraicClosure F)))⁆ ⊓ Subgroup.centralizer {x}) :=
    Nat.card_congr ((ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv e α).trans
      eA).toEquiv
  rw [hcard]
  exact (pow_dvd_pow 2 hk).trans
    (two_pow_six_dvd_card_twistedE6_rational_centralizer p hp2 hf (AlgebraicClosure F) hxR hx2)

end CFSG.SeitzReduction.RankOne
