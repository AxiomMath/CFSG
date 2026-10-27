module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowGlue
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Rank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

private theorem conj_injective_of_center_eq_bot {S : Type*} [Group S]
    (hZ : Subgroup.center S = ⊥) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff.mpr fun g hg => ?_)
  rw [← hZ, Subgroup.mem_center_iff]
  intro z
  have h := congrArg (fun f : MulAut S => f z) (MonoidHom.mem_ker.mp hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc z * g = g * z * g⁻¹ * g := by rw [h]
    _ = g * z := by group

private theorem centralizer_inner_eq_bot {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥) :
    Subgroup.centralizer ((inner S : Subgroup (MulAut S)) : Set (MulAut S)) = ⊥ := by
  refine eq_bot_iff.mpr fun α hα => ?_
  rw [Subgroup.mem_bot]
  have key : ∀ g z : S, g * z * g⁻¹ = α g * z * (α g)⁻¹ := by
    intro g z
    have h := congrArg (fun f : MulAut S => f (α.symm z))
      (Subgroup.mem_centralizer_iff.mp hα (MulAut.conj g) ⟨g, rfl⟩)
    simpa only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] using h
  ext x
  have hc : (α x)⁻¹ * x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro z
    calc z * ((α x)⁻¹ * x) = (α x)⁻¹ * (α x * z * (α x)⁻¹) * x := by group
      _ = (α x)⁻¹ * (x * z * x⁻¹) * x := by rw [← key x z]
      _ = (α x)⁻¹ * x * z := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  rw [MulAut.one_apply]
  exact hc

theorem sylow_normal_outer_of_outTowerAt {S : Type} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]
    (hZ : Subgroup.center S = ⊥) (hT : OutTowerAt S p) :
    ∀ P : Sylow p (Outer S), (P : Subgroup (Outer S)).Normal :=
  pClosed_of_outTower (X := MulAut S) (L := inner S) (centralizer_inner_eq_bot hZ)
    (OutTowerAt.of_mulEquiv (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)).symm hT)

theorem not_rankLE2_linear_residual_three {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) [Finite (Cat ⟨.A m q, hv⟩)]
    (hφ : 3 ∣ Nat.totient (Nat.gcd (m + 1) (q.card - 1))) (hq1 : ¬ 3 ∣ q.card - 1) :
    ¬ RankLE2 3 (Cat ⟨.A m q, hv⟩) := by
  intro hrk
  have hd0 : 0 < Nat.gcd (m + 1) (q.card - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hd : 6 ≤ Nat.gcd (m + 1) (q.card - 1) := by
    by_contra h
    exact not_dvd_totient_of_lt Nat.prime_three (by norm_num) hd0 (by omega) hφ
  have hm : 5 ≤ m := by
    have := hd.trans (Nat.gcd_le_left _ (by omega : 0 < m + 1))
    omega
  by_cases hq3 : q.p = 3
  ·
    have h2 : Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group) ≤ 2 :=
      CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => hrk E hE
    rcases KFactProofs.T29.Chev3.rank_dichotomy_classical ⟨.A m q, hv⟩ (by simpa using hq3)
        (Or.inl ⟨m, q, rfl⟩) (MulEquiv.refl _) with h4 | ⟨q', hq', -⟩ | ⟨q', hq', -⟩ | ⟨q', hq', -⟩
    · omega
    · obtain ⟨h1, -⟩ := TauCeti.LieTypeIndex.A.inj hq'
      omega
    · obtain ⟨h1, -⟩ := TauCeti.LieTypeIndex.A.inj hq'
      omega
    · cases hq'
  ·
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
    have hq0 : ¬ 3 ∣ q.card := fun h => hq3
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
        (Nat.prime_three.dvd_of_dvd_pow (by rwa [TauCeti.PrimePower.card_def] at h))).symm
    have hmod : q.card % 3 = 2 := by omega
    have hsq : q.card ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hmod]
    have hpos : 1 ≤ q.card ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h32 : 3 ∣ q.card ^ 2 - 1 := (Nat.modEq_iff_dvd' hpos).mp (by
      change 1 % 3 = q.card ^ 2 % 3
      rw [hsq])
    let σ : (Fin 2 × Fin 3) ⊕ Fin (m + 1 - 6) ≃ Fin (m + 1) :=
      (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
        (finSumFinEquiv.trans (finCongr (by omega)))
    exact not_rankLE2_of_hasThreeIndep Nat.prime_three
      ((hasThreeIndep_psl_blocks σ (by norm_num) Nat.prime_three (by rwa [hcardF])
        (by rwa [hcardF])).of_mulEquiv
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).symm) hrk

theorem not_rankLE2_unitary_residual_three {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) [Finite (Cat ⟨.twistedA m q, hv⟩)]
    (hφ : 3 ∣ Nat.totient (Nat.gcd (m + 1) (q.card + 1))) (hq1 : ¬ 3 ∣ q.card + 1) :
    ¬ RankLE2 3 (Cat ⟨.twistedA m q, hv⟩) := by
  intro hrk
  have hd0 : 0 < Nat.gcd (m + 1) (q.card + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hd : 6 ≤ Nat.gcd (m + 1) (q.card + 1) := by
    by_contra h
    exact not_dvd_totient_of_lt Nat.prime_three (by norm_num) hd0 (by omega) hφ
  have hm : 5 ≤ m := by
    have := hd.trans (Nat.gcd_le_left _ (by omega : 0 < m + 1))
    omega
  by_cases hq3 : q.p = 3
  ·
    have h2 : Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group) ≤ 2 :=
      CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => hrk E hE
    rcases KFactProofs.T29.Chev3.rank_dichotomy_classical ⟨.twistedA m q, hv⟩
        (by simpa using hq3) (Or.inr (Or.inl ⟨m, q, rfl⟩)) (MulEquiv.refl _) with
      h4 | ⟨q', hq', -⟩ | ⟨q', hq', -⟩ | ⟨q', hq', -⟩
    · omega
    · cases hq'
    · cases hq'
    · obtain ⟨h1, -⟩ := TauCeti.LieTypeIndex.twistedA.inj hq'
      omega
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hmodel :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv (MulEquiv.refl _)
    obtain ⟨K, _, hU, ⟨e₀⟩, -⟩ :=
      CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.exists_primeFormP_mulEquiv_of_statedModel
        hmodel
    have : Finite K := hU.finite
    have hq1' : ¬ 3 ∣ q.p ^ q.exponent + 1 := by rwa [TauCeti.PrimePower.card_def] at hq1
    have hz : (-((q.p : ZMod 3) ^ q.exponent)) ≠ 0 :=
      neg_ne_zero.mpr (CFSG.RankThree.PartOne.KCUnitaryPlane.natCast_pow_ne_zero Nat.prime_three
        (Ne.symm hq3) q.prime_p)
    have h3 : (-((q.p : ZMod 3) ^ q.exponent)) ^ 2 = 1 := ZMod.pow_card_sub_one_eq_one hz
    let σ : (Fin 2 × Fin 3) ⊕ Fin (m + 1 - 6) ≃ Fin (m + 1) :=
      (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
        (finSumFinEquiv.trans (finCongr (by omega)))
    exact not_rankLE2_of_hasThreeIndep Nat.prime_three
      ((CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.hasThreeIndep_psu_blocks hU σ
        (by norm_num) Nat.prime_three h3 hq1').of_mulEquiv e₀.symm) hrk

theorem outTowerAt_three_of_rankLE2 (hT : ExceptionalTowers) (d : TauCeti.ValidLieTypeIndex)
    [Finite (Cat d)] (hrk : RankLE2 3 (Cat d)) :
    OutTowerAt (TauCeti.CFSGIndex.lie d).Group 3 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A m q =>
    have hm1 : 1 ≤ m := hrange.1
    rcases Nat.lt_or_ge m 2 with h1 | hm2
    · obtain rfl : m = 1 := by omega
      exact outTowerAt_catA_one hv
    · rcases outTowerAt_catA_or hm2 hv hp hp2 hrk with h | ⟨hφ, hq1⟩
      · exact h
      · exact absurd hrk (not_rankLE2_linear_residual_three hv hφ hq1)
  | twistedA m q =>
    rcases outTowerAt_cat_twistedA_or hv hp hp2 hrk with h | ⟨hφ, hq1⟩
    · exact h
    · exact absurd hrk (not_rankLE2_unitary_residual_three hv hφ hq1)
  | B r q =>
    have hr2 : 2 ≤ r := hrange.1
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · obtain rfl : r = 2 := by omega
      exact outTowerAt_catB_two hv
    · by_cases hq2 : q.p = 2
      · exact outTowerAt_catB_even hr3 hq2 hv
      · exact outTowerAt_catOrth (d := ⟨.B r q, hv⟩) (Or.inl ⟨r, q, rfl, hr3, hq2⟩) hp hp2 hrk
  | C r q => exact outTowerAt_catC hv
  | D r q =>
    exact outTowerAt_catOrth (d := ⟨.D r q, hv⟩) (Or.inr (Or.inl ⟨r, q, rfl⟩)) hp hp2 hrk
  | twistedD r q =>
    exact outTowerAt_catOrth (d := ⟨.twistedD r q, hv⟩) (Or.inr (Or.inr ⟨r, q, rfl⟩)) hp hp2 hrk
  | E6 q => exact hT.lie ⟨.E6 q, hv⟩ trivial 3 hp hp2
  | E7 q => exact hT.lie ⟨.E7 q, hv⟩ trivial 3 hp hp2
  | E8 q => exact hT.lie ⟨.E8 q, hv⟩ trivial 3 hp hp2
  | F4 q => exact hT.lie ⟨.F4 q, hv⟩ trivial 3 hp hp2
  | G2 q => exact hT.lie ⟨.G2 q, hv⟩ trivial 3 hp hp2
  | twistedE6 q => exact hT.lie ⟨.twistedE6 q, hv⟩ trivial 3 hp hp2
  | trialityD4 q => exact hT.lie ⟨.trialityD4 q, hv⟩ trivial 3 hp hp2
  | suzuki m => exact hT.lie ⟨.suzuki m, hv⟩ trivial 3 hp hp2
  | reeG2 m => exact hT.lie ⟨.reeG2 m, hv⟩ trivial 3 hp hp2
  | reeF4 m => exact hT.lie ⟨.reeF4 m, hv⟩ trivial 3 hp hp2
  | tits => exact hT.lie ⟨.tits, hv⟩ trivial 3 hp hp2

theorem sylow_normal_outer_three_of_simple (hT : ExceptionalTowers) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : IsCatalogGroup S)
    (hrk : RankLE2 3 S) : ∀ P : Sylow 3 (Outer S), (P : Subgroup (Outer S)).Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, hab⟩ := hnab
  have hZ : Subgroup.center S = ⊥ :=
    CFSG.Sporadic.Schreier.center_eq_bot_of_simple inferInstance hab
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    exact (hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))).elim
  | alternating n hn =>
    haveI := Hyp111.finite_outer (alternatingGroup (Fin n))
    exact Hyp111.sylow_normal_outer_of_mulEquiv e (Hyp111.sylow_normal_of_not_dvd
      (not_dvd_card_outer_alternatingGroup n hn 3 Nat.prime_three (by norm_num)))
  | sporadic s =>
    exact sylow_normal_outer_of_outTowerAt hZ
      (OutTowerAt.of_mulEquiv e (hT.sporadic s 3 Nat.prime_three (by norm_num)))
  | lie d =>
    haveI : Finite (Cat d) := Finite.of_equiv S e.toEquiv
    exact sylow_normal_outer_of_outTowerAt hZ
      (OutTowerAt.of_mulEquiv e (outTowerAt_three_of_rankLE2 hT d (RankLE2.of_mulEquiv e hrk)))

end CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo
