module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenHat
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagAssembly
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Rank1

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm)
open CFSG.LieType.SeitzGeneration.ExcWideThree (E6NormalizesR)
open CFSG.LieType.SeitzGeneration.ExcHighThree (pinnedX_pow_char)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (e6Inndiag e6InndiagGL e6InndiagConj
  e6InndiagConj_apply e6InndiagConj_injective range_e6InndiagConj rootDiagUnit_mem_e6InndiagGL)
open CFSG.HardMathSupport.Timmesfeld.Torality (familyCentralizer familyKernel
  mem_familyCentralizer familyCentralizer_factors)
open CFSG.ClassicalInvolution.ModelFacts.Levi (abs_iform_le_two_E6
  pinnedX_commute_of_iform_eq_zero_E6)

theorem cen_iform_single {τ : Tag} (x : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    iform x (Pi.single j 1) = ∑ i, x i * τ.symmetrizedCartan i j := by
  unfold iform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Pi.single_apply, hk]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem cen_iform_eq_sum {τ : Tag} (β γ : Fin τ.rank → ℤ) :
    ∑ j, iform β (Pi.single j 1) * γ j = iform β γ := by
  simp only [cen_iform_single, Finset.sum_mul]
  unfold iform
  exact Finset.sum_comm

theorem cen_rootChar_coroot {K : Type} [Field K] (u : Kˣ) (β γ : Fin Tag.E6.rank → ℤ) :
    rootChar (fun j => u ^ iform β (Pi.single j 1)) γ = u ^ iform β γ := by
  rw [← cen_iform_eq_sum β γ]
  unfold rootChar
  simp only [← zpow_mul]
  exact CFSG.LieType.Chevalley.prod_zpow_eq_zpow_sum _ _ _

theorem cen_three_dvd_of_zpow_eq_one {G : Type*} [Group G] {ω : G} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) {m : ℤ} (h : ω ^ m = 1) : (3 : ℤ) ∣ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h
  rw [orderOf_eq_prime hω3 hω1] at h2
  exact_mod_cast h2

theorem cen_four_le_card {K : Type} [Field K] [Finite K] {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) : 4 ≤ Nat.card K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by
    have h := orderOf_dvd_natCard ω
    rwa [orderOf_eq_prime hω3 hω1] at h
  have hle : 3 ≤ Nat.card Kˣ := Nat.le_of_dvd Nat.card_pos hdvd
  rw [Nat.card_eq_card_units_add_one K]
  omega

theorem cen_root_eq_of_modEq : ∀ β ∈ rootFinset Tag.E6, ∀ γ ∈ rootFinset Tag.E6,
    (∀ j : Fin Tag.E6.rank, (∑ i, (β i - γ i) * Tag.E6.symmetrizedCartan i j) % 3 = 0) →
      β = γ := by
  decide +kernel

section Stab


theorem cen_smul_eq_of_mem_rootCharStabilizer {K : Type} [Field K] {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) {ρ : Fin Tag.E6.rank → ℤ} (hρ : IsRoot Tag.E6 ρ) {a : Fin Tag.E6.rank → Kˣ}
    (ha : ∀ v, rootChar a v = ω ^ iform ρ v) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizer a) : w • ρ = ρ := by
  have key : ∀ j : Fin Tag.E6.rank,
      (∑ i, ((w⁻¹ • ρ) i - ρ i) * Tag.E6.symmetrizedCartan i j) % 3 = 0 := by
    intro j
    have h1 : rootChar a (w • Pi.single j 1) = rootChar a (Pi.single j 1) := hw (Pi.single j 1)
    rw [ha, ha, ← iform_smul w⁻¹ ρ, inv_smul_smul] at h1
    have h2 := cen_three_dvd_of_zpow_eq_one hω3 hω1
      (show ω ^ (iform (w⁻¹ • ρ) (Pi.single j 1) - iform ρ (Pi.single j 1)) = 1 by
        rw [zpow_sub, h1, mul_inv_cancel])
    rw [cen_iform_single, cen_iform_single, ← Finset.sum_sub_distrib] at h2
    simp only [← sub_mul] at h2
    exact Int.emod_eq_zero_of_dvd h2
  have h5 := cen_root_eq_of_modEq _ (mem_rootFinset.2 (IsRoot.smul hρ w⁻¹)) _
    (mem_rootFinset.2 hρ) key
  calc w • ρ = w • (w⁻¹ • ρ) := by rw [h5]
    _ = ρ := smul_inv_smul w ρ

theorem cen_iform_eq_zero_of_rootChar {K : Type} [Field K] {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) {ρ α : Fin Tag.E6.rank → ℤ} (hρ : IsRoot Tag.E6 ρ) {a : Fin Tag.E6.rank → Kˣ}
    (ha : ∀ v, rootChar a v = ω ^ iform ρ v) (hα : IsRoot Tag.E6 α) (h : rootChar a α = 1) :
    iform α ρ = 0 := by
  rw [ha] at h
  obtain ⟨k, hk⟩ := cen_three_dvd_of_zpow_eq_one hω3 hω1 h
  have h2 := abs_le.1 (abs_iform_le_two_E6 hρ hα)
  rw [iform_comm, hk]
  rw [hk] at h2
  omega

end Stab

section Normalizes


theorem cen_rootSpan_commute {K : Type} [Field K] {ρ : Fin Tag.E6.rank → ℤ}
    (hρ : IsRoot Tag.E6 ρ) {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α ∧ iform α ρ = 0) {x : ModGL Tag.E6 K}
    (hx : x ∈ rootSpan Tag.E6 K S) (t : K) :
    x * pinnedX Tag.E6 K ρ t = pinnedX Tag.E6 K ρ t * x := by
  have hle : rootSpan Tag.E6 K S ≤ Subgroup.centralizer {pinnedX Tag.E6 K ρ t} := by
    refine iSup₂_le fun α hα => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact pinnedX_commute_of_iform_eq_zero_E6 (hS α hα).1 hρ (hS α hα).2 c t
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem cen_conj_pinnedX_of_commute {K : Type} [Field K] [Finite K] {ω : Kˣ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {ρ : Fin Tag.E6.rank → ℤ} (hρ : IsRoot Tag.E6 ρ)
    {a : Fin Tag.E6.rank → Kˣ} (ha : ∀ v, rootChar a v = ω ^ iform ρ v)
    {x : e6InndiagGL K} (hx : e6InndiagConj K x * rootDiagAutHom Tag.E6 K a =
      rootDiagAutHom Tag.E6 K a * e6InndiagConj K x) (t : K) :
    ∃ t' : K, (x : ModGL Tag.E6 K) * pinnedX Tag.E6 K ρ t * (x : ModGL Tag.E6 K)⁻¹ =
      pinnedX Tag.E6 K ρ t' := by
  have hD : e6InndiagConj K (⟨rootDiagUnit Tag.E6 a, rootDiagUnit_mem_e6InndiagGL a⟩ :
      e6InndiagGL K) = rootDiagAutHom Tag.E6 K a :=
    MulEquiv.ext fun y => Subtype.ext (e6InndiagConj_apply _ y)
  have hxD : x * (⟨rootDiagUnit Tag.E6 a, rootDiagUnit_mem_e6InndiagGL a⟩ : e6InndiagGL K) =
      (⟨rootDiagUnit Tag.E6 a, rootDiagUnit_mem_e6InndiagGL a⟩ : e6InndiagGL K) * x := by
    apply e6InndiagConj_injective K (cen_four_le_card hω3 hω1)
    rw [map_mul, map_mul, hD]
    exact hx
  have hxD' : (x : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * x :=
    congrArg Subtype.val hxD
  obtain ⟨g, hgC, b, hxgb⟩ := cen_exists_mul_of_mem_e6InndiagGL x.2
  have hab : rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 a =
      rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 b := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm b a]
  have hgab : g * rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 b =
      rootDiagUnit Tag.E6 a * g * rootDiagUnit Tag.E6 b :=
    calc g * rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 b
        = g * (rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 a) := by rw [mul_assoc, hab]
      _ = (x : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a := by rw [hxgb, mul_assoc]
      _ = rootDiagUnit Tag.E6 a * x := hxD'
      _ = rootDiagUnit Tag.E6 a * g * rootDiagUnit Tag.E6 b := by rw [hxgb, mul_assoc]
  have hga : g * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * g := mul_right_cancel hgab
  have hgF : g ∈ familyCentralizer Tag.E6 K (fun _ : Unit => a) :=
    mem_familyCentralizer.2 ⟨hgC, fun _ => mul_inv_eq_of_eq_mul hga.symm⟩
  obtain ⟨w, hw, h₀, hh₀, u, hu, v, hv, hguv⟩ := familyCentralizer_factors Tag.E6 K _ g hgF
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh₀
  have hwρ : w • ρ = ρ := cen_smul_eq_of_mem_rootCharStabilizer hω3 hω1 hρ ha (hw ())
  obtain ⟨e, -, he⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hρ
  rw [hwρ] at he
  have hS : ∀ X : Set (Fin Tag.E6.rank → ℤ), ∀ α ∈ familyKernel (fun _ : Unit => a) ∩ X,
      IsRoot Tag.E6 α ∧ iform α ρ = 0 := fun X α hα =>
    ⟨hα.1.1, cen_iform_eq_zero_of_rootChar hω3 hω1 hρ ha hα.1.1 (hα.1.2 ())⟩
  refine ⟨(rootChar l ρ : K) * (e * ((rootChar b ρ : K) * t)), ?_⟩
  calc (x : ModGL Tag.E6 K) * pinnedX Tag.E6 K ρ t * (x : ModGL Tag.E6 K)⁻¹
      = g * (rootDiagUnit Tag.E6 b * pinnedX Tag.E6 K ρ t * (rootDiagUnit Tag.E6 b)⁻¹) *
          g⁻¹ := by
        rw [hxgb]
        group
    _ = g * pinnedX Tag.E6 K ρ ((rootChar b ρ : K) * t) * g⁻¹ := by
        rw [rootDiagUnit_conj_pinnedX b hρ]
    _ = rootDiagUnit Tag.E6 l * u * (canonicalRep (coxeterSystem Tag.E6) K w *
          (v * pinnedX Tag.E6 K ρ ((rootChar b ρ : K) * t) * v⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) K w)⁻¹) * u⁻¹ * (rootDiagUnit Tag.E6 l)⁻¹ := by
        rw [hguv]
        group
    _ = rootDiagUnit Tag.E6 l * (u * pinnedX Tag.E6 K ρ (e * ((rootChar b ρ : K) * t)) * u⁻¹) *
          (rootDiagUnit Tag.E6 l)⁻¹ := by
        rw [mul_inv_eq_of_eq_mul (cen_rootSpan_commute hρ (hS _) hv ((rootChar b ρ : K) * t)),
          he]
        group
    _ = pinnedX Tag.E6 K ρ ((rootChar l ρ : K) * (e * ((rootChar b ρ : K) * t))) := by
        rw [mul_inv_eq_of_eq_mul (cen_rootSpan_commute hρ (hS _) hu (e * ((rootChar b ρ : K) * t))),
          rootDiagUnit_conj_pinnedX l hρ]

theorem e6NormalizesR_of_commute_coroot {K : Type} [Field K] [Finite K] {ω : Kˣ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {ρ : Fin Tag.E6.rank → ℤ} (hρ : IsRoot Tag.E6 ρ)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : E ≤ e6Inndiag K)
    (hc : ∀ ε ∈ E, ε * rootDiagAutHom Tag.E6 K (fun j => ω ^ iform ρ (Pi.single j 1)) =
      rootDiagAutHom Tag.E6 K (fun j => ω ^ iform ρ (Pi.single j 1)) * ε) :
    E6NormalizesR K E := by
  have : Finite (adjointGroup Tag.E6 K) := generated_group_finite Tag.E6 K
  set R : Subgroup (adjointGroup Tag.E6 K) :=
    (rootSubgroup Tag.E6 K ρ).subgroupOf (adjointGroup Tag.E6 K) with hR
  have hmemR : ∀ g : adjointGroup Tag.E6 K,
      g ∈ R ↔ ∃ t : K, pinnedX Tag.E6 K ρ t = (g : ModGL Tag.E6 K) := fun g =>
    Subgroup.mem_subgroupOf.trans mem_rootSubgroup
  refine ⟨R, ?_, ?_, fun ε hε => ?_⟩
  · intro h
    have h1 : (⟨pinnedX Tag.E6 K ρ 1, pinnedX_mem_adjointGroup ρ 1⟩ :
        adjointGroup Tag.E6 K) ∈ R := (hmemR _).2 ⟨1, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : pinnedX Tag.E6 K ρ 1 = pinnedX Tag.E6 K ρ 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h1
    exact one_ne_zero (pinnedX_injective Tag.E6 K ρ h2)
  · intro g
    obtain ⟨t, ht⟩ := (hmemR _).1 g.2
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← ht]
    exact pinnedX_pow_char (ringChar K) ρ t
  · obtain ⟨x, rfl⟩ : ε ∈ (e6InndiagConj K).range := by
      rw [range_e6InndiagConj]
      exact hE hε
    have hle : R.map (e6InndiagConj K x).toMonoidHom ≤ R := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨t, ht⟩ := (hmemR y).1 hy
      obtain ⟨t', ht'⟩ := cen_conj_pinnedX_of_commute hω3 hω1 hρ (cen_rootChar_coroot ω ρ)
        (hc _ hε) t
      refine (hmemR _).2 ⟨t', ?_⟩
      change pinnedX Tag.E6 K ρ t' = (x : ModGL Tag.E6 K) * y * (x : ModGL Tag.E6 K)⁻¹
      rw [← ht, ht']
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (e6InndiagConj K x).injective])

end Normalizes

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
