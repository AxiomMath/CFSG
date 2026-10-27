module

public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoRat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqKac
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerCover
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmall
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltFin
import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerLastChoice

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017Cls

open CFSG.Open CFSG.Open.StatedAPI CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.LocalAnalysis.GLTheoremA.RationalModel CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
  CFSG.StandardType CFSG.StandardType.ExcThreeAtTwo
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

set_option linter.unusedSectionVars false

section Def


@[expose] def ExcRatNoA8 (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀), S.D.q = 2 →
    ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ j, a j ^ 3 = 1) →
      rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          IsEmpty (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
              alternatingGroup (Fin 8))

end Def

private theorem card_alt_eight_exc : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
  rw [Nat.card_perm, Nat.card_fin] at h
  have h8 : (8 : ℕ).factorial = 40320 := by decide
  omega

private theorem card_eq_of_alt8 {G : Type} [Group G] {H : Subgroup G}
    (e : ↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 8)) :
    Nat.card (↥H ⧸ Subgroup.center ↥H) = 20160 :=
  (Nat.card_congr e.toEquiv).trans card_alt_eight_exc

private theorem false_of_two_pow_dvd_alt8 {k n : ℕ} (hk : 7 ≤ k) (h : 2 ^ k ∣ n)
    (hn : n = 20160) : False := by
  subst hn
  have h7 : 2 ^ 7 ∣ 20160 := (Nat.pow_dvd_pow 2 hk).trans h
  revert h7
  decide

private theorem ordPSL_ne_alt8 {d a : ℕ} (hd : 2 ≤ d) (ha : 1 ≤ a) (h32 : ¬ (d = 3 ∧ a = 2))
    (h41 : ¬ (d = 4 ∧ a = 1)) :
    (2 ^ a) ^ (d * (d - 1) / 2) * (∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1)) /
      Nat.gcd d (2 ^ a - 1) ≠ 20160 := by
  intro h
  have hb := ggAKFL_bound_of_ordSL (k := 6) (r := 315) hd (by norm_num) (h.trans (by norm_num))
  have hd4 : d ≤ 4 := by
    by_contra h5
    have h10 := ggAKFL_choose_two_le (s := 10) (by omega : 5 ≤ d) (by norm_num)
    have := Nat.mul_le_mul ha h10
    omega
  interval_cases d
  · have ha6 : a ≤ 6 := by norm_num at hb; omega
    interval_cases a <;> revert h <;> decide
  · have ha2 : a ≤ 2 := by norm_num at hb; omega
    interval_cases a
    · revert h
      decide
    · exact h32 ⟨rfl, rfl⟩
  · have ha1 : a ≤ 1 := by norm_num at hb; omega
    interval_cases a
    exact h41 ⟨rfl, rfl⟩

private theorem ordSU_ne_alt8 {a d z : ℕ} (ha : 1 ≤ a) (hd : 3 ≤ d) (hz : Odd z) :
    ((2 ^ a : ℕ) : ℤ) ^ (d * (d - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) ≠ ((20160 * z : ℕ) : ℤ) := by
  intro h
  have h2 : 2 ^ (a * (d * (d - 1) / 2)) ∣ 2 ^ 6 * (315 * z) := by
    have h3 : ((2 ^ (a * (d * (d - 1) / 2)) : ℕ) : ℤ) ∣ ((20160 * z : ℕ) : ℤ) := by
      rw [← h]
      push_cast
      rw [pow_mul]
      exact dvd_mul_right _ _
    have h4 := Int.natCast_dvd_natCast.mp h3
    rwa [show 20160 * z = 2 ^ 6 * (315 * z) by ring] at h4
  have h5 : ((20160 : ℕ) : ℤ) ∣ ((2 ^ a : ℕ) : ℤ) ^ (d * (d - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [h, Nat.cast_mul]
    exact dvd_mul_right _ _
  have hb := ggAKFG_le_of_two_pow_dvd (Odd.mul ⟨157, by norm_num⟩ hz) h2
  have hd4 : d ≤ 4 := by
    by_contra h5'
    have h10 := ggAKFL_choose_two_le (s := 10) (by omega : 5 ≤ d) (by norm_num)
    have := Nat.mul_le_mul ha h10
    omega
  clear h h2
  interval_cases d
  · have : a ≤ 2 := by norm_num at hb; omega
    interval_cases a <;> revert h5 <;> decide +kernel
  · have : a ≤ 1 := by norm_num at hb; omega
    interval_cases a
    revert h5
    decide +kernel

private theorem ordPSU_ne_alt8 {d a : ℕ} (hd : 3 ≤ d) (ha : 1 ≤ a) :
    (2 ^ a) ^ (d * (d - 1) / 2) *
      (∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
        Nat.gcd d (2 ^ a + 1) ≠ 20160 := by
  have hQ1 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hodd : Odd (Nat.gcd d (2 ^ a + 1)) := by
    refine Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right d (2 ^ a + 1))
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hPcast : ((∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i).toNat : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => Int.toNat_of_nonneg ?_
    have h1 : (1 : ℤ) ≤ ((2 ^ a : ℕ) : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast (by omega))
    have h2 : ((-1 : ℤ)) ^ i ≤ 1 := by
      rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> norm_num
    linarith
  have hgdvd : Nat.gcd d (2 ^ a + 1) ∣ (2 ^ a) ^ (d * (d - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 d, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i).toNat := by
    rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hPcast]
    refine Dvd.dvd.mul_left ?_ _
    have hmem : d ∈ Finset.Icc 2 d := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
    refine (?_ : ((Nat.gcd d (2 ^ a + 1) : ℕ) : ℤ) ∣ ((2 ^ a : ℕ) : ℤ) ^ d - (-1) ^ d).trans
      (Finset.dvd_prod_of_mem (fun i => ((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) hmem)
    have h1 : ((Nat.gcd d (2 ^ a + 1) : ℕ) : ℤ) ∣ ((2 ^ a : ℕ) : ℤ) - (-1) := by
      rw [sub_neg_eq_add]
      exact_mod_cast Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right d (2 ^ a + 1))
    exact h1.trans (sub_dvd_pow_sub_pow _ _ d)
  intro heq
  have hmul := Nat.div_mul_cancel hgdvd
  rw [heq] at hmul
  refine ordSU_ne_alt8 ha hd hodd ?_
  rw [← hPcast, ← Nat.cast_pow, ← Nat.cast_mul, hmul]

section Kac

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

private theorem kc_single24_exc : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, szF (zlC m0 m1 m2 m3 m4 m5) x = 24 →
      cntB m0.val m1.val m2.val m3.val m4.val m5.val = 24 := by
  decide +kernel


private theorem kernelRoots_subset_of_ncard24_exc {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i := by
  obtain ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs.kac_class_data h3 hap
  obtain ⟨x, hx, -, hncard, -, -⟩ := hcl i
  have hcnt :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn.ncard_kernelRoots_eq_cntB
      hζ w hchar
  have h24 := kc_single24_exc m0 m1 m2 m3 m4 m5 hsum x hx (hncard.symm.trans hc)
  have hk : (kernelRoots (rootCharHom a)).ncard = 24 := hcnt.trans h24
  have hle : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) := fun γ hγ => hγ.1
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  exact (Set.eq_of_subset_of_ncard_le hle (by rw [hk, hc]) hfin).ge

end Kac

section Classes


private theorem typeA_not_alt8 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hq2 : S.D.q = 2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hr3 : compRank (componentRoots (rootCharHom a) i) ≠ 3)
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (e : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        alternatingGroup (Fin 8)) : False := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  obtain ⟨f, hf1, hmodel⟩ :=
    rationalComponent_typeA_model_dim S Nat.prime_three hT hap h1 i hA hqs
  rw [ringChar.eq L 2] at hmodel
  have hcard := card_eq_of_alt8 e
  rcases hmodel with hPSL | hPSU
  · by_cases h32 : compRank (componentRoots (rootCharHom a) i) + 1 = 3 ∧ f = 2
    · obtain ⟨h3, rfl⟩ := h32
      rw [h3] at hPSL
      obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hPSL
      exact CFSG.HardMathSupport.Solomon.Coordinator.false_of_projectiveSL_alt_eight (F := K)
        (by rw [hK]; norm_num)
        (((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          3 K).symm.trans
            (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K)).trans
          (eT.symm.trans e))
    · have h := card_of_statedClassicalModel_psl (by omega) hPSL
      rw [hcard] at h
      exact ordPSL_ne_alt8 (by omega) hf1 h32 (fun h' => hr3 (by omega)) h.symm
  · have hν3 : 3 ≤ compRank (componentRoots (rootCharHom a) i) + 1 := hPSU.1.2.2.1
    have h := card_of_statedClassicalModel_psu (by omega) hPSU
    rw [hcard] at h
    exact ordPSU_ne_alt8 hν3 hf1 h.symm

private theorem two_pow_twelve_dvd_of_inner_exc {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} [CharP L 2] {S : LangSetup τ L p₀} {a : Fin τ.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hc : 24 ≤ (componentRoots (rootCharHom a) i).ncard) :
    2 ^ 12 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hk : twistKind S.ρ (rootCharHom a) i = .inner := by
    unfold twistKind
    rw [if_pos hinner]
  obtain ⟨D⟩ := nonempty_innerData S hT i hk
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf := isPerfect_componentRootSpan_of_big hτ D (by omega)
  obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have h2N := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.ncard_eq_two_mul_ncard_posRoots hΨ hfin
  have hN : 12 ≤ (posRoots (componentRoots (rootCharHom a) i)).ncard := by omega
  have hdvd := pow_card_dvd_centerQuotient_of_uniEmbed uniEmbed_holds (rootCharHom a) i
    (fixSubfield D.σ) g hg hgk hperf
  obtain ⟨k, hk1, hkcard⟩ :=
    CFSG.StandardType.LayerExcThree.exists_card_eq_two_pow (fixSubfield D.σ)
  rw [hkcard, ← pow_mul] at hdvd
  have h12 : 12 ≤ k * (posRoots (componentRoots (rootCharHom a) i)).ncard := by nlinarith
  exact (Nat.pow_dvd_pow 2 h12).trans hdvd

private theorem outerD_not_alt8 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hq2 : S.D.q = 2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hcq : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 20160) : False := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  obtain ⟨m, e, -, hlie⟩ :=
    lieModel_rationalComponent_of_twoD_highG Nat.prime_three S hT hap h1 i h5 hn hout
      (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega))
      trivial
  rw [ringChar.eq L 2] at hlie
  have hm4 : 4 ≤ m := hlie.admissible.2.2
  have he : 1 ≤ e := hlie.admissible.2.1
  have hdvd : 2 ^ (e * (m * (m - 1))) ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
    rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical
      (hlie.statedClassicalModel (by decide)), pow_mul]
    exact CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedD m (2 ^ e)
  have h12 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm4 (by omega)
  exact false_of_two_pow_dvd_alt8 (by nlinarith) hdvd hcq

private theorem outerE_not_alt8 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hq2 : S.D.q = 2) (hτ : τ = .E7 ∨ τ = .E8)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hcq : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 20160) : False := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hτ with rfl | rfl
  · obtain ⟨f, -, -, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E7 S Nat.prime_three h3L hT hTp i h6 hn hout
    rw [ringChar.eq L 2] at hlie
    have hf : 1 ≤ f := hlie.admissible.2.1
    have hdvd : 2 ^ (f * 36) ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
      rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
        (hlie.chevalleyExceptionalModel (by decide)), pow_mul]
      exact CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedE6 (2 ^ f)
    exact false_of_two_pow_dvd_alt8 (by omega) hdvd hcq
  · obtain ⟨f, -, -, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E8 S Nat.prime_three h3L hT hTp i h6 hn hout
    rw [ringChar.eq L 2] at hlie
    have hf : 1 ≤ f := hlie.admissible.2.1
    have hdvd : 2 ^ (f * 36) ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
      rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional
        (hlie.chevalleyExceptionalModel (by decide)), pow_mul]
      exact CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedE6 (2 ^ f)
    exact false_of_two_pow_dvd_alt8 (by omega) hdvd hcq

private theorem d4Class_E6_not_alt8 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq2 : S.D.q = 2) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 4)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 24)
    (hcq : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 20160) : False := by
  classical
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact false_of_two_pow_dvd_alt8 (by norm_num)
      (two_pow_twelve_dvd_of_inner_exc (Or.inr (Or.inl rfl)) hT hinner (by omega)) hcq
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, ht, rfl⟩
  ·
    have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext1 g
      rw [hΦ, one_mul, inv_one, mul_one]
    have hfine := omegaMinus8Fine_d4Class_E6_two S ⟨Fr, hFr, hΦ'⟩ hq2 hT hap h1 i hrank hcard
    have hadm := LieModel.admissible hfine
    obtain ⟨-, -, hfac⟩ :=
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput _ _ 4 2 1 hadm hfine
    have hdvd : 2 ^ 12 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
      have := Nat.ordProj_dvd (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) 2
      rwa [hfac] at this
    exact false_of_two_pow_dvd_alt8 (by norm_num) hdvd hcq
  ·
    obtain ⟨v, hv, hρ'⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3L facts_E6
      kacCount_E6_four (by decide) (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT
      (rootDiagUnit_pow_eq_one_of_forall hap) i hrank hcard
    have hs := componentOrbitLength_eq_one hfin hρ'
    rw [hs, Function.iterate_one] at hinner
    have hsub := kernelRoots_subset_of_ncard24_exc h3L hap i hcard
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq21 : S.D.q = 2 ^ 1 := by rw [hq2, pow_one]
    obtain ⟨⟨e⟩, hZ⟩ := d4t2out_rationalComponent_equiv (ℓ := 2) (f := 1) S
      ⟨t, ht, Fr, hFr, hΦ⟩ (by norm_num) hq21 (by norm_num) hT hap i v hv hsub hρ' hinner
    haveI := finite_rationalComponent S a i
    have hcardR : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) =
        CFSG.Open.orderTrialityD4 (2 ^ 1) := by
      have h := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds _ _ ⟨e⟩
      change _ = CFSG.Open.orderTrialityD4 (TauCeti.PrimePower.card _) at h
      rw [h, TauCeti.PrimePower.card_def]
    have hquot : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) =
        Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      Nat.card_congr
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
    have hdvd : 2 ^ 12 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
      rw [hquot, hcardR]
      unfold CFSG.Open.orderTrialityD4
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _) _
    exact false_of_two_pow_dvd_alt8 (by norm_num) hdvd hcq

private theorem bc3Class_F4_not_alt8 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) (hq2 : S.D.q = 2) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 3)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 18)
    (hcq : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 20160) : False := by
  classical
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
    by_cases hin : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · exact hin
    · have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
        unfold twistKind
        rw [if_neg hin, if_neg (by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega),
          if_neg (fun h => by omega),
          if_neg (fun h => by have := h.2; rw [hrank, hcard] at this; omega)]
      exact twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨σ, hfin, hcardσ, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  haveI := hfin
  rw [hq2] at hcardσ
  have hperf :=
    isPerfect_componentRootSpan_f4_card_eighteen i hcard (Nat.succ_le_of_lt hs0) hcardσ
  have hN : (posRoots (componentRoots (rootCharHom a) i)).ncard = 9 := by
    have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
    have hfinΨ : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot Tag.F4).subset fun β hβ => hΨ.isRoot β hβ
    have := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.ncard_eq_two_mul_ncard_posRoots hΨ hfinΨ
    omega
  obtain ⟨u, hu, hCQ⟩ := exists_odd_ggCQ_componentRootSpan i (Nat.succ_le_of_lt hs0) hcardσ
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperf)) hf1
  have h := ggCQ_map_of_perfect f hker (Group.IsPerfect.top_iff.mpr hperf)
  rw [← MonoidHom.range_eq_map, hRf, ggCQ_top_subgroup] at h
  have hcq' : ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i) = 20160 := hcq
  rw [h, hCQ, hN] at hcq'
  have hle := ggAKFG_le_of_two_pow_dvd (k := componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i) * 9) (e := 6) (n := 315) ⟨157, by norm_num⟩
    (Dvd.intro u (hcq'.trans (by norm_num)))
  omega

theorem excRatNoA8_E8 : ExcRatNoA8 .E8 := by
  intro L _ _ p₀ S hq2 a hT hap h1 i hqs
  classical
  refine ⟨fun e => ?_⟩
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  have hcq := card_eq_of_alt8 e
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E8 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact not_a3Shape_of_three_E8 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩
    · exact typeA_not_alt8 S hq2 hT hap h1 i hA hr3 hqs e
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S
        Nat.prime_three h3L hTp i
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact hA hA'
    · have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
        by_contra hlt
        have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
        exact not_d4Shape_of_three_E8 S h3L hTp i ⟨hr4, by rw [hD.2, hr4]⟩
      have h24 : 24 ≤ (componentRoots (rootCharHom a) i).ncard := by
        rw [hD.2, Nat.mul_assoc]
        have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
        have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) :=
          le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
        omega
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact false_of_two_pow_dvd_alt8 (by norm_num)
          (two_pow_twelve_dvd_of_inner_exc (Or.inr (Or.inr (Or.inr rfl))) hT hinner h24) hcq
      · exact outerD_not_alt8 S hq2 hT hap h1 i hr5 hD.2 hinner hcq
    · have hr8 : compRank (componentRoots (rootCharHom a) i) ≤ 8 := by
        have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
        rwa [show Tag.E8.rank = 8 from rfl] at hle
      have h24 : 24 ≤ (componentRoots (rootCharHom a) i).ncard := by
        rw [hE.2]
        have hc : compRank (componentRoots (rootCharHom a) i) = 6 ∨
            compRank (componentRoots (rootCharHom a) i) = 7 ∨
            compRank (componentRoots (rootCharHom a) i) = 8 := by omega
        rcases hc with h6 | h7 | h8
        · rw [h6]
          norm_num [eRootCount]
        · rw [h7]
          norm_num [eRootCount]
        · rw [h8]
          norm_num [eRootCount]
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact false_of_two_pow_dvd_alt8 (by norm_num)
          (two_pow_twelve_dvd_of_inner_exc (Or.inr (Or.inr (Or.inr rfl))) hT hinner h24) hcq
      · exact outerE_not_alt8 S hq2 (Or.inr rfl) hT hap h1 i hE.1 hE.2 hinner hcq

theorem excRatNoA8_E7 : ExcRatNoA8 .E7 := by
  intro L _ _ p₀ S hq2 a hT hap h1 i hqs
  classical
  refine ⟨fun e => ?_⟩
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  have hcq := card_eq_of_alt8 e
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E7 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact not_a3Shape_of_three_E7 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩
    · exact typeA_not_alt8 S hq2 hT hap h1 i hA hr3 hqs e
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S
        Nat.prime_three h3L hTp i
    have hshape := e7_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact hA hA'
    · have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
        by_contra hlt
        have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
        exact not_d4Shape_of_three_E7 S h3L hTp i ⟨hr4, by rw [hD.2, hr4]⟩
      have h24 : 24 ≤ (componentRoots (rootCharHom a) i).ncard := by
        rw [hD.2, Nat.mul_assoc]
        have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
        have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) :=
          le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
        omega
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact false_of_two_pow_dvd_alt8 (by norm_num)
          (two_pow_twelve_dvd_of_inner_exc (Or.inr (Or.inr (Or.inl rfl))) hT hinner h24) hcq
      · exact outerD_not_alt8 S hq2 hT hap h1 i hr5 hD.2 hinner hcq
    · have hr7 : compRank (componentRoots (rootCharHom a) i) ≤ 7 := by
        have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
        rwa [show Tag.E7.rank = 7 from rfl] at hle
      have h24 : 24 ≤ (componentRoots (rootCharHom a) i).ncard := by
        rw [hE.2]
        have hc : compRank (componentRoots (rootCharHom a) i) = 6 ∨
            compRank (componentRoots (rootCharHom a) i) = 7 := by omega
        rcases hc with h6 | h7
        · rw [h6]
          norm_num [eRootCount]
        · rw [h7]
          norm_num [eRootCount]
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact false_of_two_pow_dvd_alt8 (by norm_num)
          (two_pow_twelve_dvd_of_inner_exc (Or.inr (Or.inr (Or.inl rfl))) hT hinner h24) hcq
      · exact outerE_not_alt8 S hq2 (Or.inl rfl) hT hap h1 i hE.1 hE.2 hinner hcq

theorem excRatNoA8_E6 : ExcRatNoA8 .E6 := by
  intro L _ _ p₀ S hq2 a hT hap h1 i hqs
  classical
  refine ⟨fun e => ?_⟩
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two S hq2
  have hcq := card_eq_of_alt8 e
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact not_a3Shape_of_three_E6 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩
    · exact typeA_not_alt8 S hq2 hT hap h1 i hA hr3 hqs e
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S
        Nat.prime_three h3L hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact hA hA'
    · by_cases hr4 : compRank (componentRoots (rootCharHom a) i) = 4
      · exact d4Class_E6_not_alt8 S hq2 hT hap h1 i hr4 (by rw [hD.2, hr4]) hcq
      · have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
        have h24 : 24 ≤ (componentRoots (rootCharHom a) i).ncard := by
          rw [hD.2, Nat.mul_assoc]
          have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
          have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1) :=
            le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
          omega
        by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)])
        · exact false_of_two_pow_dvd_alt8 (by norm_num)
            (two_pow_twelve_dvd_of_inner_exc (Or.inr (Or.inl rfl)) hT hinner h24) hcq
        · exact outerD_not_alt8 S hq2 hT hap h1 i hr5 hD.2 hinner hcq
    · exact false_of_e6Class_E S Nat.prime_three h3L hTp h1 i hE.1 hE.2

theorem excRatNoA8_F4 : ExcRatNoA8 .F4 := by
  intro L _ _ p₀ S hq2 a hT hap h1 i hqs
  classical
  refine ⟨fun e => ?_⟩
  have hcq := card_eq_of_alt8 e
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.F4 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact not_a3Shape_of_three_F4 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩
    · exact typeA_not_alt8 S hq2 hT hap h1 i hA hr3 hqs e
  · rcases f4_nonA_casesP Nat.prime_three (by norm_num) S h3L hTp h1 i hA with
      hB2 | ⟨-, -, -, -, hr, hn⟩
    · exact not_b2Shape_of_three_F4 S h3L hTp i hB2
    · exact bc3Class_F4_not_alt8 S hq2 hT i hr hn hcq

end Classes

end CFSG.LocalAnalysis.GLTheoremA.I2017Cls

end
