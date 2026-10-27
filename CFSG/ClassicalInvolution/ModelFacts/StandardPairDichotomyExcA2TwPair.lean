module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwRational
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Pair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Data
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthTw
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAdj
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain
public import CFSG.ClassicalInvolution.Balance.BootstrapExoticE6
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Balance.QNineModels
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main
public import CFSG.ClassicalInvolution.Models.SymplecticPairs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional

section Hull

variable {p e : ℕ} [Fact p.Prime]

local notation "kE6" => LeviE6.E6Closure p e

theorem rho_neg_of_fixed {β : Fin (Tag.rank .E6) → ℤ} (hβ : rho β = β) : rho (-β) = -β := by
  have h : rho (-β) = -rho β := permLattice_neg _ _
  rw [h, hβ]

theorem phi_map_stdRank_le (hp2 : p ≠ 2) (he : 1 ≤ e) {β : Fin (Tag.rank .E6) → ℤ}
    (hβ : IsRoot .E6 β) (hfix : rho β = β) :
    (stdRankOne (twistedE6Datum p e) (proj β)).map (LeviE6.phiE6 p e) ≤
      rootRankOneGroup .E6 kE6 β := by
  rw [rootRankOneGroup_eq_sup hβ]
  have h1 : ∀ x ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj β),
      LeviE6.phiE6 p e x ∈ rootSubgroup .E6 kE6 β := fun x hx =>
    ((map_twistedRootGroup_fixed p e hp2 he hβ hfix).le (Subgroup.mem_map_of_mem _ hx)).1
  have h2 : ∀ x ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-proj β),
      LeviE6.phiE6 p e x ∈ rootSubgroup .E6 kE6 (-β) := fun x hx => by
    have hx' : x ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj (-β)) := by
      rw [map_neg]
      exact hx
    exact ((map_twistedRootGroup_fixed p e hp2 he (IsRoot.neg hβ) (rho_neg_of_fixed hfix)).le
      (Subgroup.mem_map_of_mem _ hx')).1
  show ((twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj β) ⊔
    twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-proj β)).map (LeviE6.phiE6 p e)) ≤ _
  rw [Subgroup.map_sup]
  exact sup_le_sup (by rintro _ ⟨x, hx, rfl⟩; exact h1 x hx)
    (by rintro _ ⟨x, hx, rfl⟩; exact h2 x hx)

theorem mem_phi_of_fixed_pinnedX (hp2 : p ≠ 2) (he : 1 ≤ e) {β : Fin (Tag.rank .E6) → ℤ}
    (hβ : IsRoot .E6 β) (hfix : rho β = β) {x : kE6}
    (hx : LeviE6.frobE6 p e (pinnedX .E6 kE6 β x) = pinnedX .E6 kE6 β x) :
    pinnedX .E6 kE6 β x ∈
      (twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj β)).map (LeviE6.phiE6 p e) :=
  (map_twistedRootGroup_fixed p e hp2 he hβ hfix).ge
    (mem_fixedPointsIn.2 ⟨mem_rootSubgroup.2 ⟨x, rfl⟩, hx⟩)

theorem phi_sat_thetaE6 (hp2 : p ≠ 2) (he : 1 ≤ e) :
    rootRankOneGroup .E6 kE6 thetaE6 ⊓ (LeviE6.phiE6 p e).range ≤
      (stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (LeviE6.phiE6 p e) := by
  rw [thetaE6_eq_leviE6]
  rintro y ⟨⟨A, hA⟩, x, hx⟩
  have hk : ringChar kE6 ≠ 2 := by
    rw [ringChar.eq kE6 p]
    exact hp2
  have hρinj : Function.Injective (rootSL2 .E6 kE6 LeviE6.thetaE6) :=
    ((exceptional_Lang_root_rank_one_data .E6 kE6 LeviE6.thetaE6).2.2.2.2.2.2.2.1 hk).1
  have hFρ : ∀ B : SL2 kE6, LeviE6.frobE6 p e (rootSL2 .E6 kE6 LeviE6.thetaE6 B) =
      rootSL2 .E6 kE6 LeviE6.thetaE6
        (Matrix.SpecialLinearGroup.map (iterateFrobenius kE6 p e) B) := fun B => by
    have := frobE6_rootSL2_thetaE6 p e hp2 he B
    rwa [thetaE6_eq_leviE6] at this
  have hFy : LeviE6.frobE6 p e y = y := by
    rw [← hx]
    exact (mem_fixedPointsIn.1 (twistedE6Phi_mem_fixedPointsIn p e hp2 he x)).2
  have hAfix : Matrix.SpecialLinearGroup.map (iterateFrobenius kE6 p e) A = A := by
    apply hρinj
    rw [← hFρ, hA, hFy]
  have hcl := mem_closure_fixed_of_mem_slFixed (iterateFrobenius kE6 p e)
    (hAfix : A ∈ slFixed kE6 (iterateFrobenius kE6 p e))
  have hsubU : (twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj LeviE6.thetaE6)).map
      (LeviE6.phiE6 p e) ≤
      (stdRankOne (twistedE6Datum p e) (proj LeviE6.thetaE6)).map (LeviE6.phiE6 p e) :=
    Subgroup.map_mono le_sup_left
  have hsubV : (twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-proj LeviE6.thetaE6)).map
      (LeviE6.phiE6 p e) ≤
      (stdRankOne (twistedE6Datum p e) (proj LeviE6.thetaE6)).map (LeviE6.phiE6 p e) :=
    Subgroup.map_mono le_sup_right
  have hle : Subgroup.closure {g : SL2 kE6 | ∃ c, iterateFrobenius kE6 p e c = c ∧
      (g = uSL c ∨ g = vSL c)} ≤
      ((stdRankOne (twistedE6Datum p e) (proj LeviE6.thetaE6)).map (LeviE6.phiE6 p e)).comap
        (rootSL2 .E6 kE6 LeviE6.thetaE6) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, rootSL2_uSL_eq]
      have hF : LeviE6.frobE6 p e (pinnedX .E6 kE6 LeviE6.thetaE6
          ((pinnedData .E6 LeviE6.thetaE6).2.2 • c)) =
          pinnedX .E6 kE6 LeviE6.thetaE6 ((pinnedData .E6 LeviE6.thetaE6).2.2 • c) := by
        rw [frobE6_pinnedX_thetaE6 p e hp2 he, map_zsmul, hc]
      exact hsubU (mem_phi_of_fixed_pinnedX hp2 he LeviE6.isRoot_thetaE6 LeviE6.rho_thetaE6 hF)
    · obtain ⟨η, hη, hv⟩ := exists_rootSL2_vSL_eq (K := kE6) LeviE6.isRoot_thetaE6
      rw [SetLike.mem_coe, Subgroup.mem_comap, hv]
      have hηF : iterateFrobenius kE6 p e η = η := by
        rcases mul_self_eq_one_iff.1 hη with rfl | rfl
        · exact map_one _
        · rw [map_neg, map_one]
      have hF : LeviE6.frobE6 p e (pinnedX .E6 kE6 (-LeviE6.thetaE6) (η * c)) =
          pinnedX .E6 kE6 (-LeviE6.thetaE6) (η * c) := by
        rw [frobE6_pinnedX_neg_thetaE6 p e hp2 he, map_mul, hc, hηF]
      have hmem := mem_phi_of_fixed_pinnedX hp2 he (IsRoot.neg LeviE6.isRoot_thetaE6)
        (LeviE6.rho_neg_thetaE6) hF
      rw [map_neg] at hmem
      exact hsubV hmem
  have := hle hcl
  rw [← hA]
  exact this

theorem rho_thetaE6' : rho thetaE6 = thetaE6 := by
  rw [thetaE6_eq_leviE6]
  exact LeviE6.rho_thetaE6

theorem phi_stdRankE6_eq (hp2 : p ≠ 2) (he : 1 ≤ e) :
    (stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (LeviE6.phiE6 p e) =
      rootRankOneGroup .E6 kE6 thetaE6 ⊓ (LeviE6.phiE6 p e).range :=
  le_antisymm (le_inf (phi_map_stdRank_le hp2 he isRoot_thetaE6 rho_thetaE6')
    (Subgroup.map_le_range _ _)) (phi_sat_thetaE6 hp2 he)

theorem stdRank_mem_longestFundamental_TwE6 {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β)
    (hfix : rho β = β) :
    stdRankOne (twistedE6Datum p e) (proj β) ∈ longestFundamental (twistedE6Datum p e) := by
  refine ⟨1, proj β, isLongestRoot_twistedDatum_proj (frobQ p e) hβ hfix, ?_⟩
  have : (MulAut.conj (1 : twistedE6Group p e)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  rw [this, Subgroup.map_id]
  rfl

theorem phi_injOn_fundamental (hadm : StatedLieAdmissible .twistedE6 0 p e)
    {R : Subgroup (twistedE6Group p e)}
    (hR : R ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e)) :
    ∀ x ∈ R, LeviE6.phiE6 p e x = 1 → x = 1 := fun x hx h1 => by
  have hxc : x ∈ Subgroup.center (twistedE6Group p e) :=
    ker_twistedE6Phi_le_center p e kE6 (by rw [MonoidHom.mem_ker]; exact h1)
  have key : ∀ y : twistedE6Group p e,
      x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (twistedE6Group p e) := fun y => by
    rw [Subgroup.mem_center_iff] at hxc
    have h2 : x * y * x⁻¹ * y⁻¹ = 1 := by
      calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [hxc y]
        _ = 1 := by group
    rw [h2]
    exact Subgroup.one_mem _
  exact fundNoncentral_generic p .twistedE6 0 e trivial hadm (by simp) R hR x hx key

theorem phi_involution (hp2 : p ≠ 2) (he : 1 ≤ e) (hadm : StatedLieAdmissible .twistedE6 0 p e)
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) (hfix : rho β = β) {c : twistedE6Group p e}
    (hc : c ∈ stdRankOne (twistedE6Datum p e) (proj β)) (ho : orderOf c = 2) :
    LeviE6.phiE6 p e c = signDiagE6 kE6 β := by
  have hk : ringChar kE6 ≠ 2 := by
    rw [ringChar.eq kE6 p]
    exact hp2
  have hρinj : Function.Injective (rootSL2 .E6 kE6 β) :=
    ((exceptional_Lang_root_rank_one_data .E6 kE6 β).2.2.2.2.2.2.2.1 hk).1
  obtain ⟨A, hA⟩ := phi_map_stdRank_le hp2 he hβ hfix (Subgroup.mem_map_of_mem _ hc)
  obtain ⟨h1, h2⟩ := (orderOf_eq_prime_iff (p := 2)).1 ho
  have hΦ1 : LeviE6.phiE6 p e c ≠ 1 := fun h => h2 (phi_injOn_fundamental hadm
    (longestFundamental_subset .twistedE6 _ (stdRank_mem_longestFundamental_TwE6 hβ hfix)) c hc h)
  have hAA : A * A = 1 := by
    apply hρinj
    rw [map_mul, hA, map_one, ← map_mul, ← sq, h1, map_one]
  have hA1 : A ≠ 1 := fun h => hΦ1 (by rw [← hA, h, map_one])
  have hneg : A = HSL (-1) := by
    rw [HSL_neg_one_eq_neg_one_A2]
    exact SL2_eq_neg_one_of_mul_self hk hAA hA1
  rw [← hA, hneg]
  exact rootSL2_HSL_eq_thetaDiag_E6 hβ (-1)

end Hull

theorem map_conj_map_of_hom {K X : Type*} [Group K] [Group X] (ψ : K →* X) (g : K)
    (S : Subgroup K) :
    (S.map (MulAut.conj g).toMonoidHom).map ψ =
      (S.map ψ).map (MulAut.conj (ψ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

section Normalizer

theorem exists_conj_rootSL2_of_mem_h1E6 {k : Type} [Field k] {g : ModGL .E6 k}
    (hg : g ∈ h1E6 k) (A : SL2 k) :
    ∃ A' : SL2 k, g * rootSL2 .E6 k thetaE6 A * g⁻¹ = rootSL2 .E6 k thetaE6 A' := by
  obtain ⟨n, hn, B, rfl⟩ := hg
  obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E6 hn (B * A * B⁻¹)
  refine ⟨A', ?_⟩
  rw [← hA']
  simp only [map_mul, map_inv]
  group

theorem map_conj_rootRankOne_of_mem_h1E6 {k : Type} [Field k] {g : ModGL .E6 k}
    (hg : g ∈ h1E6 k) :
    (rootRankOneGroup .E6 k thetaE6).map (MulAut.conj g).toMonoidHom =
      rootRankOneGroup .E6 k thetaE6 := by
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    obtain ⟨A', hA'⟩ := exists_conj_rootSL2_of_mem_h1E6 hg A
    exact ⟨A', hA'.symm⟩
  · rintro ⟨A, rfl⟩
    obtain ⟨A', hA'⟩ := exists_conj_rootSL2_of_mem_h1E6 (inv_mem hg) A
    refine ⟨rootSL2 .E6 k thetaE6 A', ⟨A', rfl⟩, ?_⟩
    rw [← hA']
    simp [MulAut.conj_apply]
    group

variable {p e : ℕ} [Fact p.Prime]

local notation "kE6" => LeviE6.E6Closure p e

theorem phi_mem_h1E6_of_commute (hp2 : p ≠ 2) (he : 1 ≤ e) {u : twistedE6Group p e}
    (hu : LeviE6.phiE6 p e u * signDiagE6 kE6 thetaE6 =
      signDiagE6 kE6 thetaE6 * LeviE6.phiE6 p e u) : LeviE6.phiE6 p e u ∈ h1E6 kE6 := by
  have hk : ringChar kE6 ≠ 2 := by
    rw [ringChar.eq kE6 p]
    exact hp2
  have hG : LeviE6.phiE6 p e u ∈ adjointGroup .E6 kE6 :=
    (mem_fixedPointsIn.1 (twistedE6Phi_mem_fixedPointsIn p e hp2 he u)).1
  exact mem_h1E6_of_commute_signDiagE6 hk (u := ⟨LeviE6.phiE6 p e u, hG⟩) hu

theorem conj_stdRankE6_of_commute (hp2 : p ≠ 2) (he : 1 ≤ e) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .twistedE6 0 p e) {u : twistedE6Group p e}
    (hu : LeviE6.phiE6 p e u * signDiagE6 kE6 thetaE6 =
      signDiagE6 kE6 thetaE6 * LeviE6.phiE6 p e u) :
    (stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (MulAut.conj u).toMonoidHom =
      stdRankOne (twistedE6Datum p e) (proj thetaE6) := by
  have hθ := stdRank_mem_longestFundamental_TwE6 (p := p) (e := e) isRoot_thetaE6 rho_thetaE6'
  have hH := phi_mem_h1E6_of_commute hp2 he hu
  refine eq_of_map_eq_of_isPerfect (LeviE6.phiE6 p e) (ker_twistedE6Phi_le_center p e kE6)
    (commutator_eq_of_mem_longestFundamental (t := .twistedE6) hp2 hq trivial hadm
      (map_conj_mem_longestFundamental u hθ))
    (commutator_eq_of_mem_longestFundamental (t := .twistedE6) hp2 hq trivial hadm hθ) ?_
  rw [map_conj_map_of_hom, phi_stdRankE6_eq hp2 he,
    Subgroup.map_inf _ _ _ (MulAut.conj (LeviE6.phiE6 p e u)).injective,
    map_conj_rootRankOne_of_mem_h1E6 hH, map_conj_range_eq _ ⟨u, rfl⟩]

theorem eq_of_mem_longestFundamental_TwE6 (hp2 : p ≠ 2) (he : 1 ≤ e) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .twistedE6 0 p e) {R R' : Subgroup (twistedE6Group p e)}
    (hR : R ∈ longestFundamental (twistedE6Datum p e))
    (hR' : R' ∈ longestFundamental (twistedE6Datum p e)) {c c' : twistedE6Group p e}
    (hc : c ∈ R) (hc' : c' ∈ R') (ho : orderOf c = 2) (ho' : orderOf c' = 2)
    (h : LeviE6.phiE6 p e c = LeviE6.phiE6 p e c') : R = R' := by
  have hsingle : Generic.FundamentalSingleClass .twistedE6 (twistedE6Datum p e) :=
    fundamentalSingleClass .twistedE6 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (twistedE6Datum p e) (proj thetaE6) ∈
      Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e) :=
    ⟨1, proj thetaE6, Or.inl (isLongestRoot_twistedDatum_proj (frobQ p e) isRoot_thetaE6
      rho_thetaE6'), (Generic.conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hθmem R (longestFundamental_subset .twistedE6 _ hR)
  obtain ⟨g', hg'⟩ := hsingle _ hθmem R' (longestFundamental_subset .twistedE6 _ hR')
  have hd : g⁻¹ * c * g ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6) :=
    Generic.mem_conjSub_iff.1 (hg ▸ hc)
  have hd' : g'⁻¹ * c' * g' ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6) :=
    Generic.mem_conjSub_iff.1 (hg' ▸ hc')
  have ord : ∀ (y x : twistedE6Group p e), orderOf x = 2 → orderOf (y⁻¹ * x * y) = 2 :=
    fun y x hx => by
      have := a2_orderOf_conj_eq_two hx y⁻¹
      simpa using this
  have z1 := phi_involution hp2 he hadm isRoot_thetaE6 rho_thetaE6' hd (ord g c ho)
  have z1' := phi_involution hp2 he hadm isRoot_thetaE6 rho_thetaE6' hd' (ord g' c' ho')
  simp only [map_mul, map_inv] at z1 z1'
  have hcg : LeviE6.phiE6 p e c = LeviE6.phiE6 p e g * signDiagE6 kE6 thetaE6 *
      (LeviE6.phiE6 p e g)⁻¹ := by
    rw [← z1]
    group
  have hcg' : LeviE6.phiE6 p e c' = LeviE6.phiE6 p e g' * signDiagE6 kE6 thetaE6 *
      (LeviE6.phiE6 p e g')⁻¹ := by
    rw [← z1']
    group
  have hu : LeviE6.phiE6 p e (g'⁻¹ * g) * signDiagE6 kE6 thetaE6 =
      signDiagE6 kE6 thetaE6 * LeviE6.phiE6 p e (g'⁻¹ * g) := by
    rw [map_mul, map_inv]
    have h2 := hcg.symm.trans (h.trans hcg')
    calc (LeviE6.phiE6 p e g')⁻¹ * LeviE6.phiE6 p e g * signDiagE6 kE6 thetaE6 =
        (LeviE6.phiE6 p e g')⁻¹ * (LeviE6.phiE6 p e g * signDiagE6 kE6 thetaE6 *
          (LeviE6.phiE6 p e g)⁻¹) * LeviE6.phiE6 p e g := by group
      _ = (LeviE6.phiE6 p e g')⁻¹ * (LeviE6.phiE6 p e g' * signDiagE6 kE6 thetaE6 *
          (LeviE6.phiE6 p e g')⁻¹) * LeviE6.phiE6 p e g := by rw [h2]
      _ = signDiagE6 kE6 thetaE6 * ((LeviE6.phiE6 p e g')⁻¹ * LeviE6.phiE6 p e g) := by group
  have hconj := conj_stdRankE6_of_commute hp2 he hq hadm hu
  calc R = Generic.conjSub g (stdRankOne (twistedE6Datum p e) (proj thetaE6)) := hg
    _ = Generic.conjSub (g' * (g'⁻¹ * g)) (stdRankOne (twistedE6Datum p e) (proj thetaE6)) := by
      rw [mul_inv_cancel_left]
    _ = Generic.conjSub g' (Generic.conjSub (g'⁻¹ * g)
          (stdRankOne (twistedE6Datum p e) (proj thetaE6))) := Generic.conjSub_mul _ _ _
    _ = Generic.conjSub g' (stdRankOne (twistedE6Datum p e) (proj thetaE6)) := by
      rw [show Generic.conjSub (g'⁻¹ * g) (stdRankOne (twistedE6Datum p e) (proj thetaE6)) =
        stdRankOne (twistedE6Datum p e) (proj thetaE6) from hconj]
    _ = R' := hg'.symm

theorem exists_involution_stdRank_TwE6 (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hadm : StatedLieAdmissible .twistedE6 0 p e) {c₁ : twistedE6Group p e}
    (hc₁ : c₁ ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6)) (ho₁ : orderOf c₁ = 2)
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) (hfix : rho β = β) :
    ∃ c ∈ stdRankOne (twistedE6Datum p e) (proj β), orderOf c = 2 ∧
      LeviE6.phiE6 p e c = signDiagE6 kE6 β := by
  have hsingle : Generic.FundamentalSingleClass .twistedE6 (twistedE6Datum p e) :=
    fundamentalSingleClass .twistedE6 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (twistedE6Datum p e) (proj thetaE6) ∈
      Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e) :=
    ⟨1, proj thetaE6, Or.inl (isLongestRoot_twistedDatum_proj (frobQ p e) isRoot_thetaE6
      rho_thetaE6'), (Generic.conjSub_one _).symm⟩
  have hβl := stdRank_mem_longestFundamental_TwE6 (p := p) (e := e) hβ hfix
  obtain ⟨k, hk⟩ := hsingle _ hθmem _ (longestFundamental_subset .twistedE6 _ hβl)
  have hmem : k * c₁ * k⁻¹ ∈ stdRankOne (twistedE6Datum p e) (proj β) := by
    rw [hk]
    exact ⟨c₁, hc₁, rfl⟩
  have hord := a2_orderOf_conj_eq_two ho₁ k
  exact ⟨k * c₁ * k⁻¹, hmem, hord, phi_involution hp2 he hadm hβ hfix hmem hord⟩

end Normalizer

section StdPair

variable {p e : ℕ} [Fact p.Prime]

theorem reflect_thetaF4_of_mem {j : Fin (Tag.rank .F4)} (hj : j ∈ JF4) :
    reflect .F4 j thetaF4 = thetaF4 := by
  set X : Fin (Tag.rank .F4) → ℤ := reflect .F4 j thetaF4 - thetaF4 with hX
  have hXl : ∀ l, iform X (Pi.single l 1) = 0 := by
    intro l
    rw [hX, iform_sub_left, iform_reflect_single, iform_thetaF4_single_of_mem hj]
    ring
  have hX0 : X = 0 := by
    by_contra hne
    have hpos := iform_self_pos hne
    rw [iform_eq_sum_single X X] at hpos
    simp only [hXl, mul_zero, Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  exact sub_eq_zero.1 hX0

theorem wordActF4_thetaF4 {l : List (Fin (Tag.rank .F4))} (hl : ∀ j ∈ l, j ∈ JF4) :
    wordActF4 l thetaF4 = thetaF4 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have h2 : wordActF4 (j :: l) thetaF4 = reflect .F4 j (wordActF4 l thetaF4) := rfl
    rw [h2, ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))]
    exact reflect_thetaF4_of_mem (hl j List.mem_cons_self)

theorem weylAction_word_F4 (hA : TauCeti.IsFiniteType (Tag.cartan .F4))
    (l : List (Fin (Tag.rank .F4))) (v : Fin (Tag.rank .F4) → ℤ) :
    CFSG.LieType.RootSystem.weylAction hA
        ((l.map (CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem.simple).prod) v =
      wordActF4 l v := by
  induction l with
  | nil => simp [wordActF4]
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, CFSG.LieType.RootSystem.weylAction_mul_apply, ih]
    exact weylAction_simple_eq_reflect (τ := .F4) hA j _

theorem proj_thetaE6_eq : proj thetaE6 = thetaF4 := by
  rw [thetaF4_eq, thetaE6_eq_leviE6]
  exact (by decide : proj LeviE6.thetaE6 = thetaF4')

theorem proj_deltaE6_eq : proj deltaE6 = deltaF4 := by decide

theorem isPartnerF4_of_isPartner_tw {δ : Fin (Tag.rank .F4) → ℤ}
    (hlong : Generic.IsLongestRoot (twistedE6Datum p e) δ)
    (hp : IsPartner (twistedE6Datum p e).isFiniteType (proj thetaE6) δ) : IsPartnerF4 δ := by
  rw [proj_thetaE6_eq] at hp
  obtain ⟨hmem, hmax⟩ := (isLongestRoot_iff _ _).1 hlong
  have hδ : IsRoot .F4 δ := isRoot_iff_mem_roots.2 hmem
  obtain ⟨c, hc, hform0⟩ := form_eq_iform_tag .F4 (twistedE6Datum p e).isFiniteType
  have hform : ∀ x y : Fin (Tag.rank .F4) → ℤ,
      CFSG.LieType.RootSystem.form (twistedE6Datum p e).isFiniteType
        (CFSG.LieType.RootSystem.toRat x) (CFSG.LieType.RootSystem.toRat y) =
        c * (iform x y : ℚ) := hform0
  have hθ : thetaF4 ∈ (twistedE6Datum p e).roots := isRoot_iff_mem_roots.1 isRoot_thetaF4
  have h1 := hmax thetaF4 hθ
  rw [hform, hform] at h1
  have h2 : iform thetaF4 thetaF4 ≤ iform δ δ := by
    have := le_of_mul_le_mul_left h1 hc
    exact_mod_cast this
  rw [iform_thetaF4_self] at h2
  have hl : iform δ δ = 4 := by
    rcases iform_self_isRoot_F4 hδ with h | h <;> omega
  refine ⟨hδ, hl, ?_⟩
  have hp' : 2 * CFSG.LieType.RootSystem.form (twistedE6Datum p e).isFiniteType
      (CFSG.LieType.RootSystem.toRat thetaF4) (CFSG.LieType.RootSystem.toRat δ) =
      -CFSG.LieType.RootSystem.form (twistedE6Datum p e).isFiniteType
        (CFSG.LieType.RootSystem.toRat δ) (CFSG.LieType.RootSystem.toRat δ) := hp
  rw [hform, hform] at hp'
  have h3 : c * (2 * (iform thetaF4 δ : ℚ)) = c * (-4) := by
    have : (iform δ δ : ℚ) = 4 := by exact_mod_cast hl
    rw [this] at hp'
    linear_combination hp'
  have h4 := mul_left_cancel₀ hc.ne' h3
  have : (iform thetaF4 δ : ℚ) = -2 := by linarith
  exact_mod_cast this

theorem linearBlockStandardPair_theta_deltaTwE6 (hadm : StatedLieAdmissible .twistedE6 0 p e) :
    ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (twistedE6Datum p e) (proj thetaE6))
      (stdRankOne (twistedE6Datum p e) (proj deltaE6)) := by
  have hθl : Generic.IsLongestRoot (twistedE6Datum p e) (proj thetaE6) :=
    isLongestRoot_twistedDatum_proj (frobQ p e) isRoot_thetaE6 rho_thetaE6'
  obtain ⟨δ', hδ'l, hδ'p, W, hW⟩ :=
    CFSG.ClassicalInvolution.Balance.exists_standardPair_partner_twistedE6 hadm hθl
  obtain ⟨W', hW'⟩ : ∃ W' : Subgroup (twistedE6Group p e),
      WeakCT.LinearBlockStandardPair (GaloisField p e) W'
        (stdRankOne (twistedE6Datum p e) (proj thetaE6))
        (stdRankOne (twistedE6Datum p e) δ') := ⟨W, hW⟩
  have hδ'PF : IsPartnerF4 δ' := isPartnerF4_of_isPartner_tw hδ'l hδ'p
  obtain ⟨l, hlJ, hlδ⟩ := exists_word_partnerF4 hδ'PF
  obtain ⟨n, H, hct0, -⟩ := hasBruhatDatum .twistedE6 0 p e Fact.out trivial hadm
  have hct : CFSG.LieType.CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (twistedE6Datum p e).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (twistedE6Datum p e).isFiniteType)
      (twistedE6Datum p e).roots (twistedE6Datum p e).rootGroup n H := hct0
  set w := (l.map (CFSG.LieType.RootSystem.coxeterMatrix
    (twistedE6Datum p e).isFiniteType).toCoxeterSystem.simple).prod with hwdef
  obtain ⟨g, hg⟩ := exists_map_conj_rankOne hct w
  have hw : ∀ v, CFSG.LieType.RootSystem.weylAction (twistedE6Datum p e).isFiniteType w v =
      wordActF4 l v := fun v => weylAction_word_F4 (twistedE6Datum p e).isFiniteType l v
  have hθroot : proj thetaE6 ∈ (twistedE6Datum p e).roots :=
    isRoot_iff_mem_roots.1 (isRoot_proj isRoot_thetaE6)
  have hδroot : proj deltaE6 ∈ (twistedE6Datum p e).roots :=
    isRoot_iff_mem_roots.1 (isRoot_proj isPartnerE6_deltaE6.1)
  have hθw : CFSG.LieType.RootSystem.weylAction (twistedE6Datum p e).isFiniteType w
      (proj thetaE6) = proj thetaE6 := by
    refine (hw (proj thetaE6)).trans ?_
    rw [proj_thetaE6_eq]
    exact wordActF4_thetaF4 hlJ
  have hδw : CFSG.LieType.RootSystem.weylAction (twistedE6Datum p e).isFiniteType w
      (proj deltaE6) = δ' := by
    refine (hw (proj deltaE6)).trans ?_
    rw [proj_deltaE6_eq]
    exact hlδ
  have h1 : (stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (MulAut.conj g).toMonoidHom =
      stdRankOne (twistedE6Datum p e) (proj thetaE6) := by
    have := hg _ hθroot
    rw [hθw] at this
    exact this
  have h2 : (stdRankOne (twistedE6Datum p e) (proj deltaE6)).map (MulAut.conj g).toMonoidHom =
      stdRankOne (twistedE6Datum p e) δ' := by
    have := hg _ hδroot
    rw [hδw] at this
    exact this
  have hpair := linearBlockStandardPair_map_conj hW' g⁻¹
  have e1 : (stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (MulAut.conj g⁻¹).toMonoidHom =
      stdRankOne (twistedE6Datum p e) (proj thetaE6) := by
    have := a2_map_conj_inv_map_conj g (stdRankOne (twistedE6Datum p e) (proj thetaE6))
    rwa [h1] at this
  have e2 : (stdRankOne (twistedE6Datum p e) δ').map (MulAut.conj g⁻¹).toMonoidHom =
      stdRankOne (twistedE6Datum p e) (proj deltaE6) := by
    have := a2_map_conj_inv_map_conj g (stdRankOne (twistedE6Datum p e) (proj deltaE6))
    rwa [h2] at this
  rw [e1, e2] at hpair
  exact ⟨_, hpair⟩

end StdPair

end CFSG.ClassicalInvolution.ModelFacts.Levi
