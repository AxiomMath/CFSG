module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM6TwoG2
import CFSG.RankThree.PartTwo.Sec4.HeringK419G2
import CFSG.RankThree.PartTwo.Sec4.HeringK419U33
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311g
public import CFSG.Quasithin.Recognition.CertU33DcPG

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open (IsElemAbelian ordG2)
open CFSG.Blueprint.Chevalley (TwistTag Tag adjointGroup)
open CFSG.LieType.Chevalley (fieldActor fixSubfield ringEquiv_cube_apply_eq)
open CFSG.RankThree.PartTwo.Sec4 (autFix)
open CFSG.RankThree.PartTwo.Sec4.HeringK419 (HasTwoWitness hasTwoWitness_of_mulEquiv)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3 (fixSubgroupFieldActorEquiv)

section Elementary

private theorem t2021TD4G2_four_le {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf : 2 ^ 2 ≤ 2 ^ f)

private theorem t2021TD4G2_ordG2_pos {f : ℕ} (hf : 1 ≤ f) : 0 < ordG2 (2 ^ f) := by
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have h6 : 1 < (2 ^ f) ^ 6 := Nat.one_lt_pow (by norm_num) hq
  have h2 : 1 < (2 ^ f) ^ 2 := Nat.one_lt_pow (by norm_num) hq
  unfold ordG2
  exact Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) (by omega)

private theorem t2021TD4G2_two_dvd_ordG2 {f : ℕ} (hf : 1 ≤ f) : 2 ∣ ordG2 (2 ^ f) := by
  unfold ordG2
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _) _

private theorem t2021TD4G2_three_dvd_ordG2 (f : ℕ) : 3 ∣ ordG2 (2 ^ f) := by
  have h : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    rw [show (2 ^ f) ^ 2 = 4 ^ f by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    exact Nat.sub_one_dvd_pow_sub_one 4 f
  unfold ordG2
  exact Dvd.dvd.mul_left h _

private theorem t2021TD4G2_three_dvd_sub_one {f : ℕ} (hf : Even f) : 3 ∣ 2 ^ f - 1 := by
  obtain ⟨r, rfl⟩ := hf
  rw [show 2 ^ (r + r) = 4 ^ r by rw [← two_mul, pow_mul]; norm_num]
  exact Nat.sub_one_dvd_pow_sub_one 4 r

private theorem t2021TD4G2_two_eq_zero {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) : (2 : k) = 0 := by
  have : Fintype k := Fintype.ofFinite k
  have h := card_nsmul_eq_zero (G := k) (x := 1)
  rw [← Nat.card_eq_fintype_card, hk, nsmul_eq_mul, mul_one] at h
  push_cast at h
  exact (pow_eq_zero_iff (by omega)).1 h

variable {X : Type*} [Group X]

private theorem t2021TD4G2_pow_conj_mem (U : Subgroup X) {x : X} (hx : ∀ u ∈ U, x * u * x⁻¹ ∈ U) :
    ∀ m : ℕ, ∀ u ∈ U, x ^ m * u * (x ^ m)⁻¹ ∈ U
  | 0, u, hu => by simpa using hu
  | m + 1, u, hu => by
    have e : x ^ (m + 1) * u * (x ^ (m + 1))⁻¹ = x ^ m * (x * u * x⁻¹) * (x ^ m)⁻¹ := by
      rw [pow_succ, mul_inv_rev]
      simp only [mul_assoc]
    rw [e]
    exact t2021TD4G2_pow_conj_mem U hx m _ (hx u hu)

private theorem t2021TD4G2_exists_ne_one {E : Subgroup X} (hE : Nat.card E = 3) : ∃ x ∈ E, x ≠ 1 := by
  rcases E.bot_or_exists_ne_one with h | h
  · rw [h, Subgroup.card_bot] at hE
    omega
  · exact h

private theorem t2021TD4G2_conj_mem_of_three {E U : Subgroup X} (hE : Nat.card E = 3)
    (h3 : ∀ e ∈ E, e ^ 3 = 1) {x : X} (hxE : x ∈ E) (hx1 : x ≠ 1) (hx : ∀ u ∈ U, x * u * x⁻¹ ∈ U) :
    ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x = 3 := orderOf_eq_prime (h3 x hxE) hx1
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have hzE : Subgroup.zpowers x = E :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxE) (by rw [Nat.card_zpowers, hord, hE])
  have hfin : IsOfFinOrder x := orderOf_pos_iff.1 (by rw [hord]; norm_num)
  intro e he u hu
  rw [← hzE] at he
  obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2 he)
  exact t2021TD4G2_pow_conj_mem U hx m u hu

end Elementary

private theorem t2021TD4G2_setup {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    Nat.card (fixSubfield σ) = 2 ^ f ∧
      Nat.card ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) = ordG2 (2 ^ f) ∧
      Nonempty (↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ))) := by
  have hF := CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_of_cube hf hK hσ
  have hfix : autFix (fieldActor (t := TwistTag.D4) σ σ) = fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) :=
    Subgroup.ext fun _ => Iff.rfl
  let Φ : ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
    (MulEquiv.subgroupCongr hfix).trans ((fixSubgroupFieldActorEquiv K σ (ringEquiv_cube_apply_eq hK hσ)).trans
      (sfm6TrialityFieldImageEquivG2 σ (t2021TD4G2_two_eq_zero hf hF)))
  refine ⟨hF, ?_, ⟨Φ⟩⟩
  rw [Nat.card_congr Φ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]

private theorem t2021TD4G2_commutator_eq_top {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) = ⊤ := by
  obtain ⟨hF, -, ⟨Φ⟩⟩ := t2021TD4G2_setup (by omega) σ hK hσ
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard, hF]
    exact_mod_cast (le_trans (by norm_num) (t2021TD4G2_four_le hf) : 3 ≤ 2 ^ f)
  have htop := CFSG.LieType.Chevalley.generated_group_perfect_away_from_two Tag.G2 (fixSubfield σ) hk3
  have hmap : (commutator ↥(adjointGroup Tag.G2 (fixSubfield σ))).map Φ.symm.toMonoidHom =
      commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.2 Φ.symm.surjective, ← commutator_def]
  rw [← hmap, htop, Subgroup.map_top_of_surjective _ Φ.symm.surjective]

section Core


theorem t2021TD4_g2Core {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsSimpleGroup ↥(commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) ∧
      3 ∣ Nat.card ↥(commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) := by
  obtain ⟨hF, -, ⟨Φ⟩⟩ := t2021TD4G2_setup hf σ hK hσ
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
  · obtain ⟨hs, hc⟩ := CFSG.QuasithinUnique.Id2519.g2Two_derived (k := fixSubfield σ) (by simpa using hF)
    haveI := hs
    refine ⟨(MulEquiv.commutatorCongr Φ).isSimpleGroup, ?_⟩
    rw [Nat.card_congr (MulEquiv.commutatorCongr Φ).toEquiv, hc]
    norm_num
  · have h3 : 3 ≤ Nat.card (fixSubfield σ) := hF ▸ le_trans (by norm_num) (t2021TD4G2_four_le hf2)
    haveI := CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 h3
    let e : ↥(commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) ≃*
        ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
      ((MulEquiv.subgroupCongr (t2021TD4G2_commutator_eq_top hf2 σ hK hσ)).trans Subgroup.topEquiv).trans Φ
    refine ⟨e.isSimpleGroup, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]
    exact t2021TD4G2_three_dvd_ordG2 f

end Core

private theorem t2021TD4G2_two_dvd {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    2 ∣ Nat.card ↥(commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) := by
  obtain ⟨hF, hA, ⟨Φ⟩⟩ := t2021TD4G2_setup hf σ hK hσ
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
  · obtain ⟨-, hc⟩ := CFSG.QuasithinUnique.Id2519.g2Two_derived (k := fixSubfield σ) (by simpa using hF)
    rw [Nat.card_congr (MulEquiv.commutatorCongr Φ).toEquiv, hc]
    norm_num
  · rw [t2021TD4G2_commutator_eq_top hf2 σ hK hσ, Subgroup.card_top, hA]
    exact t2021TD4G2_two_dvd_ordG2 hf

private theorem t2021TD4G2_witness_one
    {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    {x : ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ U : Subgroup ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)),
      U ≤ commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
        ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
  obtain ⟨hF, hA, ⟨Φ⟩⟩ := t2021TD4G2_setup le_rfl σ hK hσ
  have hF2 : Nat.card (fixSubfield σ) = 2 := by simpa using hF
  obtain ⟨-, hc⟩ := CFSG.QuasithinUnique.Id2519.g2Two_derived hF2
  have hidx : (commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))).index = 2 := by
    have h := (commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))).card_mul_index
    rw [Nat.card_congr (MulEquiv.commutatorCongr Φ).toEquiv, hc, hA] at h
    norm_num [ordG2] at h
    omega
  have hxC : x ∈ commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
    have h2 := (commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))).pow_index_mem x
    rw [hidx] at h2
    have hx : x = (x ^ 2)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ']
      exact hx3
    rw [hx]
    exact inv_mem h2
  set G := adjointGroup Tag.G2 (fixSubfield σ)
  have hLie := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds (fixSubfield σ) hF2
  obtain ⟨eU⟩ := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.nonempty_mulEquiv_u33G_of_statedClassicalModel
    (hLie.statedClassicalModel (by decide))
  let eC : ↥(commutator ↥G) ≃* ↥⁅G, G⁆ :=
    ((commutator ↥G).equivMapOfInjective G.subtype G.subtype_injective).trans
      (MulEquiv.subgroupCongr G.map_subtype_commutator)
  let Ψ : ↥(commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) ≃* CFSG.Quasithin.U33G :=
    ((MulEquiv.commutatorCongr Φ).trans eC).trans eU
  have hx3' : (⟨x, hxC⟩ : ↥(commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)))) ^ 3 = 1 :=
    Subtype.ext hx3
  have hw : HasTwoWitness (⟨x, hxC⟩ : ↥(commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)))) := by
    refine hasTwoWitness_of_mulEquiv Ψ
      (CFSG.RankThree.PartTwo.Sec4.HeringK419U33.hasTwoWitness_u33G ?_ ?_)
    · rw [← map_pow, hx3', map_one]
    · rw [Ne, MulEquiv.map_eq_one_iff]
      exact fun h => hx1 (congrArg Subtype.val h)
  obtain ⟨T, hT2, hTn, t, htT, ht⟩ := hw
  refine ⟨T.map (commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))).subtype, Subgroup.map_subtype_le T,
    hT2.map _, ?_, ?_⟩
  · intro hbot
    apply ht
    have hmem : (t : ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) ∈
        T.map (commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))).subtype := ⟨t, htT, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [OneMemClass.coe_eq_one.1 hmem, mul_one, mul_inv_cancel]
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨_, hTn u hu, rfl⟩

private theorem t2021TD4G2_witness_big {f : ℕ}
    (hf : 2 ≤ f) {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) :
    ∃ U : Subgroup ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)),
      U ≤ commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
        ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
  obtain ⟨hF, -, ⟨Φ⟩⟩ := t2021TD4G2_setup (by omega) σ hK hσ
  haveI : CharP (fixSubfield σ) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (t2021TD4G2_two_eq_zero (by omega) hF)
  obtain ⟨s, hs2, hsx⟩ := CFSG.RankThree.PartTwo.Sec4.HeringK419G2.exists_involution_commute
    (hF ▸ t2021TD4G2_four_le hf) (z := Φ x) (by rw [← map_pow, hx3, map_one])
    (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hx1)
  have hts : orderOf (Φ.symm s) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hs2
  have htx : Commute (Φ.symm s) x := by
    apply Φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hsx
  refine ⟨Subgroup.zpowers (Φ.symm s), ?_,
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hts, pow_one]), ?_, ?_⟩
  · rw [t2021TD4G2_commutator_eq_top hf σ hK hσ]
    exact le_top
  · rw [Ne, Subgroup.zpowers_eq_bot]
    intro h1
    rw [h1, orderOf_one] at hts
    omega
  · intro u hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [((htx.zpow_left n).symm).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ n

private theorem t2021TD4G2_nine
    {f : ℕ} (hf : 1 ≤ f) (hfe : Even f) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (E₀ : Subgroup ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) (hE3 : ∀ e ∈ E₀, e ^ 3 = 1)
    (hcard : Nat.card E₀ = 9) :
    ∃ U : Subgroup ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)),
      U ≤ commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
        ∀ e ∈ E₀, ∀ u ∈ U, e * u * e⁻¹ ∈ U := by
  have hf2 : 2 ≤ f := by
    obtain ⟨r, rfl⟩ := hfe
    omega
  obtain ⟨hF, -, ⟨Φ⟩⟩ := t2021TD4G2_setup hf σ hK hσ
  have h3 : 3 ∣ Nat.card (fixSubfield σ) - 1 := by
    rw [hF]
    exact t2021TD4G2_three_dvd_sub_one hfe
  obtain ⟨R, hR1, hRp, hRn⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311g.g2ThreeNormalizesR_minus h3
      (E₀.map Φ.toMonoidHom) (by
        rintro _ ⟨e, he, rfl⟩
        rw [← map_pow, hE3 e he, map_one])
      (by rw [Subgroup.card_map_of_injective Φ.injective, hcard]; norm_num)
  have hchar : ringChar (fixSubfield σ) = 2 := by
    haveI : CharP (fixSubfield σ) 2 :=
      CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (t2021TD4G2_two_eq_zero hf hF)
    exact ringChar.eq (fixSubfield σ) 2
  rw [hchar] at hRp
  refine ⟨R.comap Φ.toMonoidHom, ?_, hRp.comap_of_injective _ Φ.injective, ?_, ?_⟩
  · rw [t2021TD4G2_commutator_eq_top hf2 σ hK hσ]
    exact le_top
  · intro hbot
    apply hR1
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := Φ.toMonoidHom) Φ.surjective R, hbot,
      Subgroup.map_bot]
  · intro e he u hu
    have hΦe : Φ e ∈ E₀.map Φ.toMonoidHom := ⟨e, he, rfl⟩
    show Φ (e * u * e⁻¹) ∈ R
    rw [← hRn (Φ e) hΦe]
    exact ⟨Φ u, hu, by rw [map_mul, map_mul, map_inv]; rfl⟩

section Two


theorem t2021TD4_g2Two {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (E₀ : Subgroup ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) (hE : IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ ≤ 3 ∨ (Nat.card E₀ = 9 ∧ Even f)) :
    ∃ U : Subgroup ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)),
      U ≤ commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
        ∀ e ∈ E₀, ∀ u ∈ U, e * u * e⁻¹ ∈ U := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hA, -⟩ := t2021TD4G2_setup hf σ hK hσ
  haveI : Finite ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) :=
    Nat.finite_of_card_ne_zero (by rw [hA]; exact (t2021TD4G2_ordG2_pos hf).ne')
  rcases hcard with hle | ⟨h9, hfe⟩
  · have hp : IsPGroup 3 E₀ := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 _ g.2)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
    have hn1 : n ≤ 1 := by
      by_contra h
      have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n
    ·
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 (t2021TD4G2_two_dvd hf σ hK hσ)
      have hg' : orderOf (g : ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))) = 2 := by
        rw [Subgroup.orderOf_coe, hg]
      refine ⟨Subgroup.zpowers (g : ↥(autFix (fieldActor (t := TwistTag.D4) σ σ))),
        Subgroup.zpowers_le.2 g.2, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg', pow_one]), ?_, ?_⟩
      · rw [Ne, Subgroup.zpowers_eq_bot]
        intro h1
        rw [h1, orderOf_one] at hg'
        omega
      · intro e he u hu
        rw [Subgroup.eq_bot_of_card_eq E₀ (by simpa using hn), Subgroup.mem_bot] at he
        rw [he, one_mul, inv_one, mul_one]
        exact hu
    ·
      have hE₀ : Nat.card E₀ = 3 := by simpa using hn
      obtain ⟨x, hxE, hx1⟩ := t2021TD4G2_exists_ne_one hE₀
      obtain ⟨U, hU, hU2, hU1, hUx⟩ : ∃ U : Subgroup ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)),
          U ≤ commutator ↥(autFix (fieldActor (t := TwistTag.D4) σ σ)) ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
            ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
        rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
        · exact t2021TD4G2_witness_one σ hK hσ (hE.2 x hxE) hx1
        · exact t2021TD4G2_witness_big hf2 σ hK hσ (hE.2 x hxE) hx1
      exact ⟨U, hU, hU2, hU1, t2021TD4G2_conj_mem_of_three hE₀ hE.2 hxE hx1 hUx⟩
  · exact t2021TD4G2_nine hf hfe σ hK hσ E₀ hE.2 h9

end Two

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
