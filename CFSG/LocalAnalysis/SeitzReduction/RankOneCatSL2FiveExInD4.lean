module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExTwoPartE
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Untwist

public noncomputable section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley.ToralSign
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped commutatorElement

namespace FiveExIn

section Group

variable {G : Type*} [Group G]

theorem two_pow_dvd_of_card_fixedSubgroup_conj_eq [Finite G] {N n : ℕ}
    (hconst : ∀ c : G, c ≠ 1 → c ^ 2 = 1 → Nat.card (fixedSubgroup (MulAut.conj c)) = N)
    (h2 : 2 ^ n ∣ Nat.card G) : 2 ^ n ∣ N := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero]
    exact one_dvd N
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
  have hP : 2 ^ n ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card h2
  have hPnt : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have h1 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    have h3 : 0 < Nat.card P := Nat.card_pos
    exact lt_of_lt_of_le (by omega) (h1.trans (Nat.le_of_dvd h3 hP))
  have hZnt : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  obtain ⟨m, hm⟩ := (P.isPGroup'.to_subgroup (center P)).exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' hm
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2
    (by rw [hm]; exact dvd_pow_self 2 hm0)
  set c : G := ((z : P) : G) with hcdef
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hc2 : c ^ 2 = 1 := by
    have h := congrArg (fun w : center P => ((w : P) : G)) hz2
    simpa [hcdef] using h
  have hc1 : c ≠ 1 := by
    intro h
    have hz1 : z = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hPle : (P : Subgroup G) ≤ fixedSubgroup (MulAut.conj c) := fun y hy => by
    change c * y * c⁻¹ = y
    have h := Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩
    have h' : y * c = c * y := congrArg Subtype.val h
    rw [← h', mul_inv_cancel_right]
  have hdvd := Subgroup.card_dvd_of_le hPle
  rw [hconst c hc1 hc2] at hdvd
  exact hP.trans hdvd

theorem conj_mem_commutator_self {R : Subgroup G} {r h : G} (hr : r ∈ R) (hh : h ∈ ⁅R, R⁆) :
    r * h * r⁻¹ ∈ ⁅R, R⁆ := by
  have hn := commutator_subgroupOf_normal R
  have hhR : h ∈ R := Subgroup.commutator_le_self R hh
  have h1 := hn.conj_mem ⟨h, hhR⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨r, hr⟩
  rwa [Subgroup.mem_subgroupOf] at h1

theorem card_inf_centralizer_conj_eq {R : Subgroup G} {g : G} (hg : g ∈ R) (y : G) :
    Nat.card ↥(⁅R, R⁆ ⊓ Subgroup.centralizer {g * y * g⁻¹}) =
      Nat.card ↥(⁅R, R⁆ ⊓ Subgroup.centralizer {y}) := by
  have hmap : (⁅R, R⁆ ⊓ Subgroup.centralizer {y}).map (MulAut.conj g).toMonoidHom =
      ⁅R, R⁆ ⊓ Subgroup.centralizer {g * y * g⁻¹} := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨v, ⟨hvH, hvy⟩, rfl⟩
      refine ⟨conj_mem_commutator_self hg hvH, ?_⟩
      calc g * v * g⁻¹ * (g * y * g⁻¹) = g * (v * y) * g⁻¹ := by group
        _ = g * (y * v) * g⁻¹ := by rw [hvy]
        _ = g * y * g⁻¹ * (g * v * g⁻¹) := by group
    · rintro ⟨hwH, hwy⟩
      refine ⟨g⁻¹ * w * g, ⟨?_, ?_⟩, by group⟩
      · have h := conj_mem_commutator_self (inv_mem hg) hwH
        rwa [inv_inv] at h
      · calc g⁻¹ * w * g * y = g⁻¹ * (w * (g * y * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * y * g⁻¹) * w) * g := by rw [hwy]
          _ = y * (g⁻¹ * w * g) := by group
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]

end Group

end FiveExIn

open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.ClassicalInvolution.ModelFacts FiveExIn in
theorem trialityInnerTwoPartInput
    {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≤ 6) : TrialityInnerTwoPartInput p f k := by
  classical
  intro J _ hm α hα hαi
  have hadm := SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hm
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have htw : TwistedChevalleyModel J .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hCdef
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK3 σ hσ
  set k' := AlgebraicClosure K
  set ι := algebraMap K k' with hι
  have hK3' : Nat.card K = p ^ (3 * f) := by rw [hK3, ← pow_mul, mul_comm]
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3'
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap K k').injective p
  set Fr := iterateFrobenius k' p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  obtain ⟨-, -, hHR, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.D4
    hp hf hodd K hK3 σ.toRingHom hσ k' Fr hFr
  have hRF : fixedPointsIn (adjointGroup TwistTag.D4.tag k')
      (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k')) =
        twistedFixedGroup TwistTag.D4 k' Fr := rfl
  have hder' : ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k')
      (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k')),
      fixedPointsIn (adjointGroup TwistTag.D4.tag k')
        (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k'))⁆ =
      C.map (baseChangeGL ι) := hder
  set t₄ := rootDiagUnit TwistTag.D4.tag (signCharTuple (k := k') (signMaskChar TwistTag.D4.tag 4))
    with ht₄
  have key : ∀ c : C, c ≠ 1 → c ^ 2 = 1 → Nat.card (fixedSubgroup (MulAut.conj c)) =
      Nat.card ↥(⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k')
        (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k')),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k')
          (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k'))⁆ ⊓
        Subgroup.centralizer {t₄}) := by
    intro c hc1 hc2
    set y := baseChangeGL ι (c : ModGL TwistTag.D4.tag K) with hydef
    have hyR : y ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k')
        (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k')) := by
      rw [hRF]
      exact hHR ⟨c, c.2, rfl⟩
    have hy2 : y ^ 2 = 1 := by
      rw [hydef, ← map_pow, ← Subgroup.coe_pow, hc2, Subgroup.coe_one, map_one]
    have hy1 : y ≠ 1 := by
      intro h1
      refine hc1 (Subtype.ext (baseChangeGL_injective ι ?_))
      rw [Subgroup.coe_one, map_one]
      exact h1
    let φ : C →* ModGL TwistTag.D4.tag k' := (baseChangeGL ι).comp C.subtype
    have hφ : Function.Injective φ := (baseChangeGL_injective ι).comp Subtype.val_injective
    have hmap : (fixedSubgroup (MulAut.conj c)).map φ =
        ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k')
          (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k')),
          fixedPointsIn (adjointGroup TwistTag.D4.tag k')
            (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k'))⁆ ⊓
          Subgroup.centralizer {y} := by
      rw [hder']
      ext z
      simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨a, a.2, rfl⟩, ?_⟩
        have ha' : c * a * c⁻¹ = a := ha
        have hac : a * c = c * a := by
          calc a * c = c * a * c⁻¹ * c := by rw [ha']
            _ = c * a := by group
        change baseChangeGL ι (a : ModGL TwistTag.D4.tag K) * y =
          y * baseChangeGL ι (a : ModGL TwistTag.D4.tag K)
        rw [hydef, ← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hac]
      · rintro ⟨⟨a, ha, rfl⟩, hay⟩
        refine ⟨⟨a, ha⟩, ?_, rfl⟩
        change c * ⟨a, ha⟩ * c⁻¹ = ⟨a, ha⟩
        have hac : (⟨a, ha⟩ : C) * c = c * ⟨a, ha⟩ := by
          refine Subtype.ext (baseChangeGL_injective ι ?_)
          rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
          exact hay
        rw [← hac]
        group
    have hcard1 : Nat.card (fixedSubgroup (MulAut.conj c)) =
        Nat.card ↥(⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k')
          (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k')),
          fixedPointsIn (adjointGroup TwistTag.D4.tag k')
            (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k'))⁆ ⊓
          Subgroup.centralizer {y}) := by
      rw [← hmap, Subgroup.card_map_of_injective hφ]
    obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
    obtain ⟨r, hr, g₁, hg₁G, hg₁F, hg₁y, -⟩ := exists_twisted_toral_reduction p TwistTag.D4 hp2
      hf d4SignDiagramReps h4.permChar_eq h4.exists_rep (untwistAt_d4 p hp2 f) hyR hy2
    have hrm : r.mask = 4 := by
      rcases List.mem_cons.1 (hr : r ∈ ⟨0, 1, 1, d4OmegaWords0⟩ :: [⟨4, 3, 4, d4OmegaWords4⟩])
        with rfl | hr'
      · exfalso
        apply hy1
        have h0 : signMaskTuple TwistTag.D4.tag k' 0 = 1 := by
          funext j
          simp [signMaskTuple]
        have e0 : g₁ * y * g₁⁻¹ = 1 := by
          rw [hg₁y]
          change rootDiagUnit TwistTag.D4.tag
            (signCharTuple (signMaskChar TwistTag.D4.tag 0)) = 1
          rw [signCharTuple_signMaskChar, h0, rootDiagUnit_one]
        exact mul_left_cancel ((mul_inv_eq_one.1 e0).trans (mul_one g₁).symm)
      · obtain rfl := List.mem_singleton.1 hr'
        rfl
    have hg₁R : g₁ ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k')
        (frobTwistGL TwistTag.D4.tag k' p f (diagramMap TwistTag.D4 k')) := ⟨hg₁G, hg₁F⟩
    rw [hcard1, ← card_inf_centralizer_conj_eq hg₁R y, hg₁y, hrm]
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have h64 : 2 ^ 6 ∣ Nat.card C :=
    (Nat.card_congr e.toEquiv) ▸ two_pow_six_dvd_card_of_lieModel (by decide) hp2 hm
  have hN := two_pow_dvd_of_card_fixedSubgroup_conj_eq key h64
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by
    rw [hβdef, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hβi : β ∈ (MulAut.conj : C →* MulAut C).range := by
    change MulAut.congr e α ∈ OuterAutomorphisms.inner C
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαi
  obtain ⟨c, hc⟩ := hβi
  have hc2 : c ^ 2 = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hc, hβ2, map_one])
  have hc1 : c ≠ 1 := by
    rintro rfl
    have hα1 : α = 1 := (MulAut.congr e).injective (by rw [map_one, ← hβdef, ← hc, map_one])
    rw [hα1, orderOf_one] at hα
    exact absurd hα (by norm_num)
  have hcard : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup (MulAut.conj c)) :=
    Nat.card_congr ((fixedSubgroupCongrEquiv e α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc.symm))).toEquiv
  rw [hcard, key c hc1 hc2]
  exact (pow_dvd_pow 2 hk).trans hN

end CFSG.SeitzReduction.RankOne
