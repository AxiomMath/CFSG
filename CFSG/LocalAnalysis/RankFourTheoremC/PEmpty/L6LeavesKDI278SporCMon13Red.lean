module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporC
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13Bal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13Mon
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.HardMathSupport.Dickson.BMRows.M13Normal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open Subgroup CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal

theorem balance_mulAut_of_inner {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (hInner : ∀ α : MulAut X, ∃ g : X, α = MulAut.conj g)
    (hbal : ∀ R Y : Subgroup X, CFSG.Open.IsElemAbelian 13 R → Nat.card R = 13 ^ 2 →
      ¬ 13 ∣ Nat.card Y → R ≤ normalizer (Y : Set X) → Y = ⊥) :
    ∀ R Y : Subgroup (MulAut X), CFSG.Open.IsElemAbelian 13 R → Nat.card R = 13 ^ 2 →
      ¬ 13 ∣ Nat.card Y → R ≤ normalizer (Y : Set (MulAut X)) → Y = ⊥ := by
  intro R Y hR hR2 hY hRY
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h2 : g * h * g⁻¹ = h := DFunLike.congr_fun hg h
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hsurj : Function.Surjective (MulAut.conj : X →* MulAut X) := fun α => by
    obtain ⟨g, hg⟩ := hInner α
    exact ⟨g, hg.symm⟩
  let e : X ≃* MulAut X := MulEquiv.ofBijective (MulAut.conj : X →* MulAut X) ⟨hinj, hsurj⟩
  let f : MulAut X →* X := e.symm.toMonoidHom
  have hfinj : Function.Injective f := e.symm.injective
  have hR' : CFSG.Open.IsElemAbelian 13 (R.map f) := hR.map f
  have hR'2 : Nat.card (R.map f) = 13 ^ 2 := by rw [card_map_of_injective hfinj, hR2]
  have hY' : ¬ 13 ∣ Nat.card (Y.map f) := by
    rw [card_map_of_injective hfinj]
    exact hY
  have hfwd : ∀ g ∈ R.map f, ∀ h ∈ Y.map f, g * h * g⁻¹ ∈ Y.map f := by
    rintro g ⟨r, hr, rfl⟩ h ⟨y, hy, rfl⟩
    have e1 : f r * f y * (f r)⁻¹ = f (r * y * r⁻¹) := by rw [map_mul, map_mul, map_inv]
    rw [e1]
    exact Subgroup.mem_map_of_mem f ((mem_normalizer_iff.1 (hRY hr) y).1 hy)
  have hRN : R.map f ≤ normalizer ((Y.map f : Subgroup X) : Set X) := by
    intro g hg
    refine mem_normalizer_iff.2 fun h => ⟨hfwd g hg h, fun hh => ?_⟩
    have h3 := hfwd g⁻¹ (inv_mem hg) _ hh
    have e2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e2] at h3
  have hbot := hbal (R.map f) (Y.map f) hR' hR'2 hY' hRN
  rw [eq_bot_iff]
  intro y hy
  have hmem : f y ∈ Y.map f := Subgroup.mem_map_of_mem f hy
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact hfinj (hmem.trans (map_one f).symm)

theorem gmat_center_eq_bot :
    Subgroup.center CFSG.Monster.Generated.Gmat = ⊥ := by
  haveI : IsSimpleGroup ↥CFSG.Monster.Generated.Gmat :=
    generated_rational_group_finite_simple.2.1
  haveI : Finite ↥CFSG.Monster.Generated.Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, -, hdg, -, -⟩ := d13_gw_facts
  apply CFSG.HardMathSupport.Dickson.BMRows.M13Normal.center_eq_bot_of_simple_nonab
  refine ⟨gw genD13W2, gw genD13W0, fun h => ?_⟩
  have h1 := h.symm.trans hdg
  have h2 : gw genD13W1 ^ 4 = 1 := by simpa using (mul_left_cancel h1).symm
  have h3 : orderOf (gw genD13W1) ∣ 4 := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_c13] at h3
  norm_num at h3

theorem kdI278SporCMonster_of_xE
    (hD : ∀ R Y : Subgroup CFSG.Monster.Generated.Gmat, CFSG.Open.IsElemAbelian 13 R →
      Nat.card R = 13 ^ 2 → gw thirteenX ∈ R →
      Y ≤ Subgroup.centralizer ({gw thirteenX} : Set CFSG.Monster.Generated.Gmat) →
      ¬ 13 ∣ Nat.card Y → R ≤ Subgroup.normalizer (Y : Set CFSG.Monster.Generated.Gmat) → Y = ⊥) :
    KDI278SporCMonster := by
  haveI : Finite ↥CFSG.Monster.Generated.Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hx : orderOf (gw thirteenX) = 13 := orderOf_xE
  have hc : orderOf (gw genD13W1) = 13 := orderOf_c13
  have hbal := balance_of_census_local hc hx census_thirteen balance_gmat_c13 hD
  have hZ : Subgroup.center ↥CFSG.Monster.Generated.Gmat = ⊥ := gmat_center_eq_bot
  have hiso : Nonempty (CFSG.Monster.Generated.Gmat ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  intro Z _ _ K hKn hsK hC B hB hBc _ W hBW hW
  haveI : K.Normal := hKn
  obtain ⟨eK⟩ := hsK
  obtain ⟨b⟩ := hiso
  have f : ↥K ≃* ↥CFSG.Monster.Generated.Gmat := eK.trans b.symm
  exact kdSporC_eq_bot_of_model (by norm_num : Nat.Prime 13) hC f
    (balance_mulAut_of_inner hZ CFSG.RankThree.PartOne.SPOR.allInner_Gmat hbal) hB hBc hBW hW

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
