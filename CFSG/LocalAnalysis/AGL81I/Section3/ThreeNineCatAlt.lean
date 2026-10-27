module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatCross
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.IndexGen
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListDefs
import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
import CFSG.LocalAnalysis.GL83PartI.I_23_3Gen

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)

theorem center_eq_bot_of_pCoverList (hPC : GL83.I243.PCoverList) {K : Type} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : CFSG.IsQuasisimple K)
    (hOp : CFSG.pPrimeCore p K = ⊥) {n : ℕ} (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) : Subgroup.center K = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hZp : IsPGroup p (Subgroup.center K) :=
    CFSG.isPGroup_of_nilpotent_normal (Subgroup.center K) inferInstance inferInstance hOp
  by_contra hne
  have hdvd : p ∣ Nat.card (Subgroup.center K) :=
    hZp.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.mp h)
  rcases hPC K (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hq) p hp (by omega) hdvd
    (.alternating n hn) ⟨e⟩ with ⟨d, hd, -⟩ | ⟨hp3, -⟩
  · cases hd
  · omega

theorem two_le_pRank_mulAut_of_faithful {X : Type} [Group X] [Finite X] {K E : Subgroup X}
    {p : ℕ} (hp : p.Prime) (hKn : K.Normal) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hfaith : ∀ x ∈ E, (∀ c ∈ K, x * c = c * x) → x = 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) := by
  have hEN : E ≤ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
    exact le_top
  let ψ : E →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine Subtype.ext (hfaith a a.2 fun c hcK => ?_)
    have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨c, hcK⟩ : ↥K) : X)) ha
    simp only [ψ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      MulAut.one_apply] at h1
    have h2 : (a : X) * c * (a : X)⁻¹ = c := h1
    calc (a : X) * c = (a : X) * c * (a : X)⁻¹ * a := by group
      _ = c * a := by rw [h2]
  have hcard : Nat.card ψ.range = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top (GL83.PiGen.isElemAbelian_range hE ψ) hcard

theorem card_orbit_le_of_lt_sq {p n : ℕ} (hp : p.Prime) (hn : n < p ^ 2)
    {R : Subgroup (Equiv.Perm (Fin n))} (hR : Nat.card R ∣ p ^ 2) (ω : Fin n) :
    Nat.card (MulAction.orbit R ω) ≤ p := by
  have hdvd : Nat.card (MulAction.orbit R ω) ∣ p ^ 2 :=
    (Dvd.intro _ (GL83.PiGen.card_mul_card_stabIn R ω).symm).trans hR
  obtain ⟨i, hi, hiq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hle : Nat.card (MulAction.orbit R ω) ≤ n := by
    simpa using Nat.card_le_card_of_injective (Subtype.val : MulAction.orbit R ω → Fin n)
      Subtype.val_injective
  rw [hiq] at hle ⊢
  interval_cases i
  · simpa using hp.one_lt.le
  · simp
  · omega

theorem centGenI_le_gammaOver {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {E K : Subgroup X} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    GL83.CompFam.centGenI p E K ≤ gammaOver 1 p E K := by
  refine iSup_le fun ⟨F, hFE, hFc⟩ => ?_
  rintro c ⟨hcK, hcF⟩
  have hFne : F ≠ ⊥ := by
    rintro rfl
    rw [hEc, Subgroup.card_bot] at hFc
    nlinarith [hp.two_le]
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
  exact mem_gammaOver_of_commute hp (hFE x.2) (fun h => hx1 (Subtype.ext h))
    (hE.2 x (hFE x.2)) hcK (Subgroup.mem_centralizer_iff.mp hcF x x.2)

theorem alt_of_catalogue24_12_five (hPC : GL83.I243.PCoverList) {X : Type} [Group X] [Finite X]
    {K E : Subgroup X} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hKq : CFSG.IsQuasisimple ↥K)
    (hOp : CFSG.pPrimeCore p ↥K = ⊥) (hKn : K.Normal) (hE : CFSG.Open.IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hrk : CFSG.Open.pRank p (K ⊔ E) ≤ 3)
    (hΓ : ¬ K ≤ CFSG.LocalAnalysis.AGL81TheoremCD.Section12.gammaOver 1 p E K)
    {n : ℕ} (hn : 5 ≤ n) (e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin n)) :
    Nonempty (↥K ≃* alternatingGroup (Fin (2 * p))) ∨
      Nonempty (↥K ≃* alternatingGroup (Fin (3 * p))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Group.IsPerfect ↥K := hKq.1
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_pCoverList hPC hp hp5 hKq hOp hn e
  have hfaith : ∀ x ∈ E, (∀ c ∈ K, x * c = c * x) → x = 1 := by
    intro x hxE hxc
    by_contra hx1
    exact hΓ fun c hcK => mem_gammaOver_of_commute hp hxE hx1 (hE.2 x hxE) hcK (hxc c hcK)
  have h2le : 2 ≤ n / p :=
    (two_le_pRank_mulAut_of_faithful hp hKn hE hEc hfaith).trans
      (CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_aut_le hn e hp hp2)
  have h3ge : n / p ≤ 3 := by
    have h1 := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.le_pRank_top hn e hp hp2
    have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥K) = CFSG.Open.pRank p K :=
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) K).symm
    have h3 : CFSG.Open.pRank p K ≤ CFSG.Open.pRank p (K ⊔ E) :=
      CFSG.SectionRank.pRank_mono hp.one_lt le_sup_left
    omega
  have h2p : 2 * p ≤ n := (Nat.le_div_iff_mul_le hp.pos).1 h2le
  have h4p : n < 4 * p := by
    have := (Nat.div_lt_iff_lt_mul hp.pos).1 (Nat.lt_succ_of_le h3ge)
    omega
  by_cases hpn : p ∣ n
  ·
    obtain ⟨m, hm⟩ := hpn
    have hm2 : 2 ≤ m := by nlinarith
    have hm3 : m ≤ 3 := by nlinarith
    have hKe : Nonempty (↥K ≃* alternatingGroup (Fin n)) :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩
    interval_cases m
    · obtain rfl : n = 2 * p := by omega
      exact Or.inl hKe
    · obtain rfl : n = 3 * p := by omega
      exact Or.inr hKe
  ·
    exfalso
    have hn6 : n ≠ 6 := by omega
    have hnlt : n < p ^ 2 := by nlinarith
    have hnp : n % p ≠ 0 := fun h => hpn (Nat.dvd_of_mod_eq_zero h)
    have hEN : E ≤ Subgroup.normalizer (K : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
      exact le_top
    have hodd : Odd (Nat.card (Subgroup.center ↥K)) := by
      rw [hZ, Subgroup.card_bot]
      exact odd_one
    have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
    have horb : ∀ ω : Fin n,
        Nat.card (MulAction.orbit (GL83.PiGen.permHom hEN hn hn6 e).range ω) ≤ p := fun ω =>
      card_orbit_le_of_lt_sq hp hnlt (hEc ▸ Subgroup.card_range_dvd _) ω
    exact hΓ ((GL83.PiGen.le_centGenI_of_orbits_of_ne_zero hp5 hEN hEp hodd hn hn6 e hnp
      horb).trans (centGenI_le_gammaOver hp hE hEc))

end CFSG.LocalAnalysis.AGL81I.Section3
