module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Alpha
public import CFSG.RankThree.PartTwo.Census.LinearRank
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1

section SL2

open Module CFSG.RankThree.PartOne.LIT

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem card_le_of_det_eq_one_of_finrank_eq_two [FiniteDimensional K V] {r : ℕ} (hr : r.Prime)
    (hrK : (r : K) ≠ 0) (hV : finrank K V = 2) (E : Subgroup (V ≃ₗ[K] V)) [Finite E]
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ r = 1)
    (hdet : ∀ g ∈ E, LinearMap.det (g : V →ₗ[K] V) = 1) : Nat.card E ≤ r := by
  by_contra hlt
  rw [not_le] at hlt
  have hr2 : 2 ≤ r := hr.two_le
  have hexpE : ∀ a : E, a ^ r = 1 := fun a => Subtype.ext (hexp a a.2)
  have hsq : r ^ 2 ≤ Nat.card E := by
    obtain ⟨k, hk⟩ := CFSG.RankThree.PartTwo.Census.exists_card_eq_pow_of_exponent hr hexpE
    rw [hk] at hlt ⊢
    have hk2 : 2 ≤ k := by
      by_contra h
      rw [not_le] at h
      interval_cases k <;> simp at hlt <;> omega
    exact Nat.pow_le_pow_right hr.pos hk2
  obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hr hrK E hcomm hexp hsq
  have hc := isCompl_fixedSpace_commSpace hrK (hexp x hxE)
  have hxcomm : ∀ g ∈ E, g * x = x * g := fun g hg => hcomm g hg x hxE
  have hUinv : ∀ g : E, ∀ u ∈ fixedSpace x, (E.subtype g) u ∈ fixedSpace x :=
    fun g u hu => map_mem_fixedSpace (hxcomm g g.2) hu
  have hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x :=
    fun g w hw => map_mem_commSpace (hxcomm g g.2) hw
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hUpos : 0 < finrank K (fixedSpace x) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨v, mem_fixedSpace.mpr hxv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have hWpos : 0 < finrank K (commSpace x) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    by_contra hcon
    have hcon' : ∀ w : commSpace x, w = 0 := fun w => by_contra fun hw => hcon ⟨w, hw⟩
    apply hx1
    apply LinearEquiv.ext
    intro y
    have hy : x y - y ∈ commSpace x := mem_commSpace.mpr ⟨y, rfl⟩
    have h2 : x y - y = 0 := congrArg Subtype.val (hcon' ⟨x y - y, hy⟩)
    simpa [sub_eq_zero] using h2
  have hU1 : finrank K (fixedSpace x) = 1 := by omega
  have hW1 : finrank K (commSpace x) = 1 := by omega
  let ρ : E →* (V ≃ₗ[K] V) := E.subtype
  let ρU := restrictAction ρ (fixedSpace x) hUinv
  let ρW := restrictAction ρ (commSpace x) hWinv
  have hdet2 : ∀ g : E, LinearMap.det (ρU g : fixedSpace x →ₗ[K] fixedSpace x) *
      LinearMap.det (ρW g : commSpace x →ₗ[K] commSpace x) = 1 := by
    intro g
    have h := det_eq_mul_of_isCompl hc (g : V ≃ₗ[K] V).toLinearMap (hUinv g) (hWinv g)
    rw [hdet g g.2] at h
    exact h.symm
  have hext : ∀ g : E, ρU g = 1 → ρW g = 1 → g = 1 := by
    intro g h1 h2
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    have hfun : (g : V ≃ₗ[K] V).toLinearMap = LinearMap.id := by
      apply ext_of_isCompl hc
      · intro u hu
        exact (restrictAction_apply ρ (fixedSpace x) hUinv g ⟨u, hu⟩).symm.trans
          (congrArg Subtype.val (LinearEquiv.congr_fun h1 ⟨u, hu⟩))
      · intro w hw
        exact (restrictAction_apply ρ (commSpace x) hWinv g ⟨w, hw⟩).symm.trans
          (congrArg Subtype.val (LinearEquiv.congr_fun h2 ⟨w, hw⟩))
    exact LinearMap.congr_fun hfun y
  let _ := commGroupOfCommSubgroup E hcomm
  have hinj : Function.Injective ρW := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hd : LinearMap.det (ρU g : fixedSpace x →ₗ[K] fixedSpace x) = 1 := by
      have := hdet2 g
      rw [hg] at this
      simpa using this
    have h1 : ρU g = 1 :=
      LinearEquiv.ext fun a => LinearMap.congr_fun
        (eq_id_of_det_eq_one_of_finrank_eq_one hU1 _ hd) a
    exact Subgroup.mem_bot.2 (hext g h1 hg)
  have hbound :=
    CFSG.RankThree.PartTwo.Census.card_le_pow_finrank_of_faithful hr hrK hexpE ρW hinj
  rw [hW1, pow_one] at hbound
  omega

end SL2

section GL3

theorem card_le_five_of_exponent_five_gl {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (hV : Module.finrank (ZMod 3) V ≤ 4)
    (E : Subgroup (V ≃ₗ[ZMod 3] V)) (hexp : ∀ g ∈ E, g ^ 5 = 1) : Nat.card E ≤ 5 := by
  haveI : Finite V := Module.finite_of_finite (R := ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 3] V => (f : V → V)) LinearEquiv.coe_injective
  set d := Module.finrank (ZMod 3) V
  let e : V ≃ₗ[ZMod 3] (Fin d → ZMod 3) := (Module.finBasis (ZMod 3) V).equivFun
  let c : (V ≃ₗ[ZMod 3] V) ≃ ((Fin d → ZMod 3) ≃ₗ[ZMod 3] (Fin d → ZMod 3)) :=
    { toFun := fun g => e.symm.trans (g.trans e)
      invFun := fun h => e.trans (h.trans e.symm)
      left_inv := fun g => by ext v; simp
      right_inv := fun h => by ext v; simp }
  have hGL : Nat.card (V ≃ₗ[ZMod 3] V) = ∏ i : Fin d, ((3 : ℕ) ^ d - 3 ^ (i : ℕ)) := by
    have h2 : Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 3)) =
        Nat.card ((Fin d → ZMod 3) ≃ₗ[ZMod 3] (Fin d → ZMod 3)) :=
      Nat.card_congr
        (Matrix.GeneralLinearGroup.toLin.trans
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Fin d → ZMod 3))).toEquiv
    have h3 := Matrix.card_GL_field (𝔽 := ZMod 3) d
    rw [ZMod.card] at h3
    rw [Nat.card_congr c, ← h2, h3]
  have key : ∀ m : ℕ, m ≤ 4 → ¬ (25 : ℕ) ∣ ∏ i : Fin m, ((3 : ℕ) ^ m - 3 ^ (i : ℕ)) := by
    intro m hm
    interval_cases m <;> norm_num [Fin.prod_univ_succ]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 E := by
    intro g
    refine ⟨1, ?_⟩
    have h5 : (g : V ≃ₗ[ZMod 3] V) ^ 5 = 1 := hexp _ g.2
    rw [pow_one]
    exact Subtype.ext (by simpa using h5)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : Nat.card E ∣ ∏ i : Fin d, ((3 : ℕ) ^ d - 3 ^ (i : ℕ)) := by
    rw [← hGL]
    exact Subgroup.card_subgroup_dvd_card E
  rcases k with _ | _ | k
  · rw [hk]; norm_num
  · rw [hk]; norm_num
  · exfalso
    have h25 : (25 : ℕ) ∣ Nat.card E := by
      rw [hk]
      exact dvd_trans (by norm_num : (25 : ℕ) ∣ 5 ^ 2) (pow_dvd_pow 5 (by omega))
    exact key d hV (dvd_trans h25 hdvd)

end GL3

section Pow3

open Subgroup

variable {K : Type*} [Group K] [Finite K]

theorem card_le_pow_three {f : ℕ} (hf : f.Prime) {Ω : Subgroup K}
    (hexp : ∀ x ∈ Ω, x ^ f = 1)
    (hrank : ∀ E : Subgroup K, E ≤ Ω → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E ≤ f ^ 2) : Nat.card Ω ≤ f ^ 3 := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hexp' : ∀ x : ↥Ω, x ^ f = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hP : IsPGroup f ↥Ω := fun x => ⟨1, by rw [pow_one]; exact hexp' x⟩
  rcases le_or_gt (Nat.card Ω) f with hsmall | hgt
  · exact hsmall.trans (Nat.le_self_pow (by norm_num) f)
  have h2 : 2 ≤ CFSG.pRank f ↥Ω := CFSG.RankThree.PartTwo.two_le_pRank hP hexp' hgt
  have hle2 : CFSG.pRank f ↥Ω ≤ 2 := by
    refine CFSG.RankThree.PartTwo.pRank_le_of_forall_isMulCommutative hf (k := 2) fun E hE => ?_
    have hE' : ∀ a ∈ E.map Ω.subtype, ∀ b ∈ E.map Ω.subtype, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      have h := congrArg (fun x : E => ((x : ↥Ω) : K)) (hE.is_comm.comm (⟨a', ha'⟩ : E) ⟨b', hb'⟩)
      simpa using h
    have := hrank (E.map Ω.subtype) (Subgroup.map_subtype_le E) hE'
    rwa [Subgroup.card_subtype] at this
  obtain ⟨-, -, hcard, -⟩ :=
    CFSG.RankThree.PartTwo.card_le_pow_three_of_pRank_two hP hexp' (le_antisymm hle2 h2)
  exact hcard

end Pow3

section Sigma

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_two_of_five_mem (hrank : evenRank G = 3) (h5 : 5 ∈ rankThreeSigmaA G) {q : ℕ}
    (hq : q.Prime) (hq5 : 5 < q) {H : Subgroup G} (hH : IsTwoLocal H) :
    Open.pRank q H ≤ 2 := by
  classical
  by_contra h3
  push Not at h3
  haveI : Fact q.Prime := ⟨hq⟩
  have hle : Open.pRank q H ≤ 3 :=
    (local_pRank_le_evenRank q hq (by omega) H hH).trans hrank.le
  have hbdd : BddAbove {k | ∃ K : Subgroup G, IsTwoLocal K ∧ CFSG.Open.pRank q K = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨K, -, rfl⟩
    refine CFSG.SectionRank.pRank_le hq.one_lt (k := Nat.card G) (fun E _ hE => ?_)
    exact (Subgroup.card_le_card_group E).trans (Nat.lt_pow_self hq.one_lt).le
  have hloc3 : rankThreeLocalRank q G = 3 := by
    have h1 : Open.pRank q H ≤ rankThreeLocalRank q G := le_csSup hbdd ⟨H, hH, rfl⟩
    have h2 := rankThreeLocalRank_le_evenRank (G := G) q hq (by omega)
    omega
  have hdvd : q ∣ Nat.card G :=
    (CFSG.LocalAnalysis.RankFourTheoremC.dvd_card_of_one_le_pRank hq (by omega : 1 ≤ Open.pRank q H)).trans
      (Subgroup.card_subgroup_dvd_card H)
  dsimp only [rankThreeSigmaA] at h5
  split_ifs at h5 with h1 h2 h3'
  · exfalso
    have hlt := h5.2.2.2
    have hle5 := rankThreeLocalRank_le_evenRank (G := G) 5 Nat.prime_five (by norm_num)
    omega
  · exact absurd h5.2.1 (lt_irrefl 5)
  · exact h2 ⟨q, hq, hq5, hdvd, hloc3⟩
  · exact h2 ⟨q, hq, hq5, hdvd, hloc3⟩

end Sigma

section Bound

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem exists_rank_bound_e3 {f p : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) (hp : p.Prime) (hp5 : p = 5)
    (hpf : p ≠ f) {Fs N : Subgroup K} (hFs : IsPGroup f Fs) (hN : N ≤ normalizer (Fs : Set K))
    (hrank : ∀ E : Subgroup K, E ≤ Fs → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ f = 1) → Nat.card E ≤ f ^ 3)
    (hrank7 : 7 ≤ f → ∀ E : Subgroup K, E ≤ Fs → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ f = 1) → Nat.card E ≤ f ^ 2) :
    ∃ χ : ↥N →* (ZMod f)ˣ, ∀ (E : Subgroup K) (hEN : E ≤ N),
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ p = 1) →
      (∀ (a : K) (ha : a ∈ E), χ ⟨a, hEN ha⟩ = 1) →
      Nat.card E ≤ p * Nat.card (E ⊓ centralizer (Fs : Set K) : Subgroup K) := by
  have hf : f.Prime := Fact.out
  obtain ⟨Ω, hΩ⟩ := exists_omega hf2 hp hpf hFs hN
  have hΩ5 : Nat.card Ω ≤ f ^ 5 := card_le_pow_five hf hΩ.exp hΩ.central
    (fun E hEΩ hEc => hrank E (hEΩ.trans hΩ.le) hEc (fun a ha => hΩ.exp a (hEΩ ha)))
  have hle : (⁅Ω, Ω⁆ : Subgroup K) ≤ Ω := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2.commutator_le_self Ω
  obtain ⟨W, _, _, _, π, ρ, hs⟩ := exists_elemSec (f := f) (Y := Ω) (M := ⁅Ω, Ω⁆) (G := N) hle
    (fun x hx m hm => (mem_normalizer_iff.mp
      (normalizer_le_normalizer_commutator Ω (le_normalizer hx)) m).mp hm)
    (fun x hx y hy => Subgroup.commutator_mem_commutator hx hy)
    (fun x hx => by rw [hΩ.exp x hx]; exact one_mem _)
    hΩ.norm (fun g hg => normalizer_le_normalizer_commutator Ω (hΩ.norm hg))
  haveI : Finite W := Module.finite_of_finite (ZMod f)
  set d := Module.finrank (ZMod f) W with hd
  have hrK : ((p : ℕ) : ZMod f) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff p f).mp h
    exact hpf ((Nat.prime_dvd_prime_iff_eq hf hp).mp this).symm
  have hfaith : ∀ (a : K) (haN : a ∈ N), a ^ p = 1 → actEquiv ρ ⟨a, haN⟩ = 1 →
      a ∈ centralizer (Fs : Set K) := by
    intro a haN hap h1
    rw [mem_centralizer_iff]
    intro x hx
    refine (hΩ.faithful a haN 1 (by simpa using hap) (fun y hy => ?_) x hx).symm
    have hay : a * y * a⁻¹ ∈ Ω := (mem_normalizer_iff.mp (hΩ.norm haN) y).mp hy
    refine (hs.eq_iff hy hay).mp ?_
    have h2 := hs.act ⟨a, haN⟩ y hy
    have h3 : ρ ⟨a, haN⟩ (π y) = π y := by
      have := LinearEquiv.congr_fun h1 (π y)
      exact this
    rw [h3] at h2
    exact h2
  have hcardW : Nat.card Ω = Nat.card (⁅Ω, Ω⁆ : Subgroup K) * f ^ d := by
    rw [hs.card_eq hle, Module.natCard_eq_pow_finrank (K := ZMod f) (V := W), Nat.card_zmod]
  obtain ⟨k, hk⟩ := (hFs.to_le (hle.trans hΩ.le)).exists_card_eq
  have hdcase : d ≤ 3 ∨ (d = 4 ∧ Nat.card (⁅Ω, Ω⁆ : Subgroup K) = f) := by
    by_cases hk0 : k = 0
    · left
      have hbot : (⁅Ω, Ω⁆ : Subgroup K) = ⊥ :=
        Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
      have hcomm : ∀ a ∈ Ω, ∀ b ∈ Ω, a * b = b * a := by
        intro a ha b hb
        have : ⁅a, b⁆ ∈ (⁅Ω, Ω⁆ : Subgroup K) := Subgroup.commutator_mem_commutator ha hb
        rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      have h1 := hrank Ω hΩ.le hcomm hΩ.exp
      rw [hcardW, hk, hk0, pow_zero, one_mul] at h1
      exact (Nat.pow_le_pow_iff_right hf.one_lt).mp h1
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      have h5 : f ^ (k + d) ≤ f ^ 5 := by rw [pow_add, ← hk, ← hcardW]; exact hΩ5
      have h6 : k + d ≤ 5 := (Nat.pow_le_pow_iff_right hf.one_lt).mp h5
      by_cases hd4 : d ≤ 3
      · exact Or.inl hd4
      · right
        have hd : d = 4 := by omega
        refine ⟨hd, ?_⟩
        have hk' : k = 1 := by omega
        rw [hk, hk', pow_one]
  have himg : ∀ (E : Subgroup K) (hEN : E ≤ N), (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ p = 1) →
      Finite (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range ∧
      (∀ g ∈ (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range,
        ∀ h ∈ (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range, g * h = h * g) ∧
      (∀ g ∈ (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range, g ^ p = 1) := by
    intro E hEN hEc hEp
    refine ⟨Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _), ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEc a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hEp a a.2)
      rw [this, map_one]
  have hker : ∀ (E : Subgroup K) (hEN : E ≤ N), (∀ a ∈ E, a ^ p = 1) → ∀ a : ↥E,
      actEquiv ρ (Subgroup.inclusion hEN a) = 1 → (a : K) ∈ centralizer (Fs : Set K) :=
    fun E hEN hEp a h => hfaith (a : K) (hEN a.2) (hEp a a.2) h
  have hf37 : f = 3 ∨ 7 ≤ f := by
    have h2 := hf.two_le
    have h4 : f ≠ 4 := by
      rintro rfl
      norm_num at hf
    have h6 : f ≠ 6 := by
      rintro rfl
      norm_num at hf
    have h5 : f ≠ 5 := fun h => hpf (hp5.trans h.symm)
    omega
  rcases hf37 with hf3 | h7
  ·
    have hd4 : d ≤ 4 := by
      rcases hdcase with h | ⟨h, -⟩ <;> omega
    refine ⟨1, fun E hEN hEc hEp _ => ?_⟩
    obtain ⟨hfin, hcomm, hexp⟩ := himg E hEN hEc hEp
    haveI := hfin
    refine card_le_of_range (actEquiv ρ) hEN (hker E hEN hEp) ?_
    subst hp5
    subst hf3
    exact card_le_five_of_exponent_five_gl hd4 _ hexp
  ·
    have hΩ3 : Nat.card Ω ≤ f ^ 3 := card_le_pow_three hf hΩ.exp
      (fun E hEΩ hEc => hrank7 h7 E (hEΩ.trans hΩ.le) hEc (fun a ha => hΩ.exp a (hEΩ ha)))
    have hd2 : d ≤ 2 := by
      by_cases hk0 : k = 0
      · have hbot : (⁅Ω, Ω⁆ : Subgroup K) = ⊥ :=
          Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
        have hcomm : ∀ a ∈ Ω, ∀ b ∈ Ω, a * b = b * a := by
          intro a ha b hb
          have : ⁅a, b⁆ ∈ (⁅Ω, Ω⁆ : Subgroup K) := Subgroup.commutator_mem_commutator ha hb
          rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
          exact this
        have h1 := hrank7 h7 Ω hΩ.le hcomm hΩ.exp
        rw [hcardW, hk, hk0, pow_zero, one_mul] at h1
        exact (Nat.pow_le_pow_iff_right hf.one_lt).mp h1
      · have h3 : f ^ (k + d) ≤ f ^ 3 := by
          rw [pow_add, ← hk, ← hcardW]
          exact hΩ3
        have h4 := (Nat.pow_le_pow_iff_right hf.one_lt).mp h3
        omega
    refine ⟨LinearEquiv.det.comp (actEquiv ρ), fun E hEN hEc hEp hχ => ?_⟩
    obtain ⟨hfin, hcomm, hexp⟩ := himg E hEN hEc hEp
    haveI := hfin
    refine card_le_of_range (actEquiv ρ) hEN (hker E hEN hEp) ?_
    by_cases hd1 : d ≤ 1
    · have h1 := CFSG.RankThree.PartOne.LIT.card_le_pow_finrank_sub hp hrK
        (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range hcomm hexp
      calc _ ≤ p ^ d := h1
        _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hd1
        _ = p := pow_one p
    · have hd2' : d = 2 := by omega
      refine card_le_of_det_eq_one_of_finrank_eq_two hp hrK hd2'
        (actEquiv ρ |>.comp (Subgroup.inclusion hEN)).range hcomm hexp ?_
      rintro _ ⟨a, rfl⟩
      have h2 : LinearMap.det (((actEquiv ρ) ⟨(a : K), hEN a.2⟩ : W ≃ₗ[ZMod f] W) :
          W →ₗ[ZMod f] W) = 1 := by
        have h3 := congrArg (fun z : (ZMod f)ˣ => (z : ZMod f)) (hχ (a : K) a.2)
        simpa [LinearEquiv.coe_det] using h3
      exact h2

theorem card_le_pow_of_pRank_le {A : Type} [Group A] [Finite A] {f r : ℕ} (hf : f.Prime)
    {X Fs : Subgroup A} (hFX : Fs ≤ X) (hX : CFSG.Open.pRank f X ≤ r) :
    ∀ E : Subgroup A, E ≤ Fs → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ f = 1) →
      Nat.card E ≤ f ^ r := by
  intro E hEF hEc hEp
  haveI : Fact f.Prime := ⟨hf⟩
  have hEf : IsPGroup f E := fun g => ⟨1, Subtype.ext (by simpa using hEp g g.2)⟩
  obtain ⟨k, hk⟩ := hEf.exists_card_eq
  have hEab : IsElemAbelian f E := ⟨⟨⟨fun a b => Subtype.ext (hEc a a.2 b b.2)⟩⟩, hEp⟩
  have := CFSG.SectionRank.le_pRank hf.one_lt (hEF.trans hFX) hEab hk
  rw [hk]
  exact Nat.pow_le_pow_right hf.pos (this.trans hX)

theorem lemma69_e3 {A : Type} [Group A] [Finite A] {p f : ℕ} (hp5 : p = 5) (hf : f.Prime)
    (hf2 : f ≠ 2) (hfp : f ≠ p) {X D Fs R : Subgroup A}
    (hperf : ∀ (M : Subgroup ↥X) [M.Normal], IsPGroup p (↥X ⧸ M) → M = ⊤)
    (hDX : D ≤ X) (hDn : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (hD : ¬ p ∣ Nat.card D)
    (hFsp : IsPGroup f Fs) (hFsX : Fs ≤ X)
    (hXDN : ∀ x ∈ X, ∃ d ∈ D, ∃ n ∈ X ⊓ normalizer (Fs : Set A), x = d * n)
    (hRN : R ≤ X ⊓ normalizer (Fs : Set A)) (hR3 : 3 ≤ Open.pRank p R)
    (hcyc : IsCyclic (R ⊓ centralizer (Fs : Set A) : Subgroup A))
    (hX3 : Open.pRank f X ≤ 3) (hX7 : 7 ≤ f → Open.pRank f X ≤ 2) : False := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hprime : p.Prime := hp5 ▸ Nat.prime_five
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : NeZero f := ⟨hf.ne_zero⟩
  obtain ⟨χ, hχ⟩ := exists_rank_bound_e3 hf2 hprime hp5 hfp.symm hFsp
    (N := X ⊓ normalizer (Fs : Set A)) inf_le_right (card_le_pow_of_pRank_le hf hFsX hX3)
    (fun h7 => card_le_pow_of_pRank_le hf hFsX (hX7 h7))
  obtain ⟨E, hER, hEab, hEcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank hprime hR3
  have hEN : E ≤ X ⊓ normalizer (Fs : Set A) := hER.trans hRN
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hχE : ∀ (a : A) (ha : a ∈ E), χ ⟨a, hEN ha⟩ = 1 := fun a ha =>
    trivial_of_perfect hprime hperf hDX hDn hD inf_le_left hXDN χ a (hEN ha) 1
      (by simpa using hEab.2 a ha)
  have h1 := hχ E hEN hEc hEab.2 hχE
  have h2 : Nat.card (E ⊓ centralizer (Fs : Set A) : Subgroup A) ≤ p :=
    card_le_of_cyclic hprime.pos hcyc (inf_le_inf_right _ hER) (fun t ht => hEab.2 t ht.1)
  rw [hEcard] at h1
  have h3 : p ^ 3 ≤ p * p := h1.trans (Nat.mul_le_mul_left _ h2)
  have h4 : p * p < p ^ 3 := by
    have := hprime.one_lt
    calc p * p = p ^ 2 := by ring
      _ < p ^ 3 := Nat.pow_lt_pow_right this (by norm_num)
  omega

end Bound

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1
