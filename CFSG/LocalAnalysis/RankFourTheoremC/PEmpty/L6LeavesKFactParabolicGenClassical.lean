module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenDatum

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.ASVolI.ChIJK Subgroup

theorem hasParGen_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [Finite F] (H : Subgroup (GL ι F)) (h2 : 2 ∣ Nat.card F) (h : HasParGen ↥H) :
    HasParGen (StatedProj H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hasParGen_of_surjective (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H))
    (QuotientGroup.mk'_surjective _) ?_ ?_ h
  · rw [QuotientGroup.ker_mk']
    intro x hx
    have hx' : (x : GL ι F) ∈ StatedScalars ι F := hx
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hx' (y : GL ι F))
  · intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    have hx' : (x : GL ι F) ∈ StatedScalars ι F := hx
    obtain ⟨c, hc⟩ := hx'
    have h1 : orderOf (x : GL ι F) ∣ Nat.card F - 1 := by
      rw [← hc]
      refine (orderOf_map_dvd _ c).trans (orderOf_dvd_of_pow_eq_one ?_)
      exact burnsideI2BN_units_pow_card_sub_one c
    rw [Subgroup.orderOf_coe] at h1
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    exact burnsideI2BN_not_dvd_card_sub_one Nat.prime_two h2 ((even_iff_two_dvd.mp hne).trans h1)


section Sp

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.RootSystem

theorem parGen_sp {d f : ℕ} (hd : 2 ≤ d) (hf : 0 < f) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f) :
    HasParGen ↥(StatedSp d F) ∧ ∀ x ∈ center ↥(StatedSp d F), Odd (orderOf x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := burnsideI2BN_charP_of_card Nat.prime_two hf hF
  refine parGen_of_datum_pkg (D := Symplectic.rootDatum d F) (n := Symplectic.weylRep d F)
    (H := Symplectic.torus d F) (Symplectic.isCTGroupDatum d F) (Symplectic.steinbergExtras d F)
    CFSG.StandardType.GGRootSp.bruhatExtras ?_ ?_ hd
  · rintro ⟨x, hx⟩
    have hidb := idBelow_of_mem_iSup (F := F) 1
      {γ | γ ∈ roots (isFiniteType_cartanC d) ∅ ∧ 0 < ht γ}
      (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hx
    obtain ⟨k, hk⟩ := burnsideI2BN_pow_eq_one_of_triangular (p := 2)
      (fun a => (1 : ℤ) * lvl a) (M := mat d F x) hidb
    refine ⟨k, Subtype.ext (mat_injective (n := d) (F := F) ?_)⟩
    simpa [map_pow] using hk
  · have hT : ∀ x ∈ (⨆ i, Symplectic.torus d F i : Subgroup (StatedSp d F)),
        x ^ (Nat.card F - 1) = 1 := by
      intro x hx
      obtain ⟨t, rfl⟩ := exists_diagonal_of_mem_iSup_torus hx
      have ht : t ^ (Nat.card F - 1) = 1 := by
        funext i
        rw [Pi.pow_apply, Pi.one_apply]
        exact burnsideI2BN_units_pow_card_sub_one (t i)
      rw [← map_pow, ← map_pow, ht, map_one, map_one]
    exact burnsideI2BN_not_dvd_card_of_pow_eq_one hT
      (burnsideI2BN_not_dvd_card_sub_one Nat.prime_two (hF ▸ dvd_pow_self 2 hf.ne'))

end Sp

section SL

open Matrix

theorem parGen_sl {m f : ℕ} (hm : 2 ≤ m) (hf : 0 < f) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f) :
    HasParGen (SpecialLinearGroup (Fin (m + 1)) F) ∧
      ∀ x ∈ center (SpecialLinearGroup (Fin (m + 1)) F), Odd (orderOf x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := burnsideI2BN_charP_of_card Nat.prime_two hf hF
  exact parGen_of_datum_pkg (D := SpecialLinear.rootDatum m F) (n := SpecialLinear.weylRep m F)
    (H := SpecialLinear.torus m F) (SpecialLinear.isCTGroupDatum m F)
    (SpecialLinear.steinbergExtras m F) CFSG.StandardType.GGRootSL.bruhatExtras
    burnsideI2BN_SL_isPGroup
    (burnsideI2BN_SL_torus Nat.prime_two (hF ▸ dvd_pow_self 2 hf.ne')) hm

end SL


section SU

open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg.CentralExt.SUBruhat CFSG.LieType.RootSystem

theorem parGen_su {d f : ℕ} (hd : 4 ≤ d) (hf : 0 < f) (F : Type) [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2) :
    HasParGen ↥(SU (unitaryInvolution F 2 f) d) ∧
      ∀ x ∈ center ↥(SU (unitaryInvolution F 2 f) d), Odd (orderOf x) := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hd2 : 2 ≤ d := by omega
  have hσ := unitaryInvolution_involutive hF
  refine parGen_of_datum_pkg (D := rootDatum hF d) (n := levelWeyl hσ ζ)
    (H := levelTorus (unitaryInvolution F 2 f)) (isCTGroupDatum hF d hd2 ζ hζ)
    (steinbergExtras hF d hd2 ζ hζ) (bruhatExtras hF hd2 ζ hζ) ?_ ?_ (by
      show 2 ≤ d / 2
      omega)
  · rintro ⟨x, hx⟩
    have hidb := idBelow_of_mem_iSup hσ 1
      {γ | γ ∈ roots (isFiniteType_cartan d) (divisible d) ∧ 0 < ht γ}
      (fun γ hγ => by have := hγ.2; omega) hx
    obtain ⟨k, hk⟩ := burnsideI2BN_pow_eq_one_of_triangular (p := 2) (lvl 1)
      (M := mat (unitaryInvolution F 2 f) d x) hidb
    refine ⟨k, Subtype.ext (mat_injective (σ := unitaryInvolution F 2 f) (n := d) ?_)⟩
    simpa [map_pow] using hk
  · have hT : ∀ y ∈ (⨆ i, levelTorus (unitaryInvolution F 2 f) i :
        Subgroup (SU (unitaryInvolution F 2 f) d)), y ^ (Nat.card F - 1) = 1 := by
      intro y hy
      obtain ⟨t, ht⟩ : ∃ t : Fin d → F, mat (unitaryInvolution F 2 f) d y = Matrix.diagonal t :=
        Subgroup.iSup_induction _ hy
          (C := fun y => ∃ t : Fin d → F,
            mat (unitaryInvolution F 2 f) d y = Matrix.diagonal t)
          (fun k y hy => exists_diagonal_of_mem_levelTorus hy)
          ⟨1, by rw [map_one]; exact Matrix.diagonal_one.symm⟩
          (fun y z ⟨d₁, h₁⟩ ⟨d₂, h₂⟩ =>
            ⟨d₁ * d₂, by rw [map_mul, h₁, h₂, Matrix.diagonal_mul_diagonal]; rfl⟩)
      have hdet : ∏ a, t a = 1 := by
        have := y.2.1
        rwa [← mat_apply (σ := unitaryInvolution F 2 f) (n := d), ht, Matrix.det_diagonal] at this
      have hne : ∀ a, t a ≠ 0 := fun a h0 => by
        have := Finset.prod_eq_zero (Finset.mem_univ a) h0
        rw [hdet] at this
        exact one_ne_zero this
      have : Fintype F := Fintype.ofFinite F
      refine mat_injective (σ := unitaryInvolution F 2 f) (n := d) ?_
      rw [map_pow, ht, Matrix.diagonal_pow, map_one]
      have hd1 : t ^ (Nat.card F - 1) = 1 := by
        funext a
        rw [Pi.pow_apply, Pi.one_apply, Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_sub_one_eq_one _ (hne a)
      rw [hd1]
      simp
    exact burnsideI2BN_not_dvd_card_of_pow_eq_one hT
      (burnsideI2BN_not_dvd_card_sub_one Nat.prime_two
        (hF ▸ dvd_pow (dvd_pow_self 2 hf.ne') two_ne_zero))

end SU

section Spin

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem

theorem parGen_spinPlus {n f : ℕ} (hn : 4 ≤ n) (hf : 0 < f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) :
    HasParGen ↥(spinGroup (quadPlus n K)) ∧
      ∀ x ∈ center ↥(spinGroup (quadPlus n K)), Odd (orderOf x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := burnsideI2BN_charP_of_card Nat.prime_two hf hK
  have hn3 : 3 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  haveI : Finite (spinGroup (quadPlus n K)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := K))
  have hext := plusDatum_steinbergExtras (K := K) hn3
  refine parGen_of_datum_pkg (D := plusDatum n K hn3) (n := weylD K hn3)
    (H := fun k => (torusD K hn3 k).range)
    (plusDatum_isCTGroupDatum hn3 (plusDatum_iSup_eq_top n K hn3)) hext
    (CFSG.StandardType.GGRootSpinPlus.bruhatExtras hn3)
    (isPGroup_iSup_pos hext fun γ hγ =>
      isPGroup_of_isParametrization (SpinPlus.isParametrization hn3) hγ) ?_ (by
      show 2 ≤ n
      omega)
  exact burnsideI2BN_not_dvd_card_iSup_range_units (hK ▸ dvd_pow_self 2 hf.ne')
    (fun i => torusD K hn3 i) fun i j h hh h' hh' => hext.torus_commute i j h hh h' hh'

open CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Universal.Spin.Twisted in
theorem parGen_spinMinus {n f : ℕ} (hn : 4 ≤ n) (hf : 0 < f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    HasParGen ↥(spinGroup (quadMinus n K b c)) ∧
      ∀ x ∈ center ↥(spinGroup (quadMinus n K b c)), Odd (orderOf x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := burnsideI2BN_charP_of_card Nat.prime_two hf hK
  haveI : Finite (spinGroup (quadMinus n K b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hext := minusDatum_steinbergExtras n hirr
  refine parGen_of_datum_pkg (D := minusDatum n hirr) (n := minusWeyl n hirr)
    (H := minusTorus n hirr) (minusDatum_isCTGroupDatum n hirr hn) hext
    (SpinMinusClosed.bruhatExtras hirr hn)
    (isPGroup_iSup_pos hext fun γ hγ => isPGroup_minusRootGroup hirr hγ) ?_ (by
      show 2 ≤ n - 1
      omega)
  refine burnsideI2BN_not_dvd_card_of_pow_eq_one (m := Nat.card K ^ 2 - 1) (fun x hx => ?_)
    (burnsideI2BN_not_dvd_sub_one Nat.prime_two (Nat.one_le_pow _ _ Nat.card_pos)
      (dvd_pow (hK ▸ dvd_pow_self 2 hf.ne') two_ne_zero))
  exact SpinMinusClosed.pow_eq_one_of_mem_iSup
    (fun i h hh => by
      have := SpinMinusClosed.pow_eq_one_of_mem_minusTorus hirr i hh
      rwa [SpinMinusClosed.card_shortField] at this)
    (fun i j h hh h' hh' => hext.torus_commute i j h hh h' hh') hx

end Spin

section Models

open Matrix CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.Universal.Spin.Twisted

noncomputable def slEquivStated (m : ℕ) (F : Type) [Field F] :
    SpecialLinearGroup (Fin (m + 1)) F ≃* ↥(StatedSL (m + 1) F) :=
  (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL (m + 1) F).symm)

theorem hasParGen_PSL {G : Type} [Group G] [Finite G] {n f : ℕ} (hn : 3 ≤ n)
    (h : StatedClassicalModel G .PSL n 2 f) : HasParGen G := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hpg, -⟩ := parGen_sl (m := m) (by omega) hf K hK
  have h2 : 2 ∣ Nat.card K := hK ▸ dvd_pow_self 2 (by omega)
  exact hasParGen_of_mulEquiv e.symm
    (hasParGen_statedProj _ h2 (hasParGen_of_mulEquiv (slEquivStated m K) hpg))

theorem hasParGen_PSU {G : Type} [Group G] [Finite G] {n f : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel G .PSU n 2 f) : HasParGen G := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : CharP K 2 := burnsideI2BN_charP_of_card Nat.prime_two (f := f * 2) (by omega)
    (by rw [hK, pow_mul])
  obtain ⟨hpg, -⟩ := parGen_su (d := n) hn hf K hK
  have h2 : 2 ∣ Nat.card K := hK ▸ dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
  exact hasParGen_of_mulEquiv e.symm
    (hasParGen_statedProj _ h2
      (hasParGen_of_mulEquiv (CFSG.LieType.Universal.Unitary.equivStatedSU hK n) hpg))

theorem hasParGen_PSp {G : Type} [Group G] [Finite G] {n f : ℕ} (hn : 2 ≤ n)
    (h : StatedClassicalModel G .PSp n 2 f) : HasParGen G := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨hpg, -⟩ := parGen_sp hn hf K hK
  have h2 : 2 ∣ Nat.card K := hK ▸ dvd_pow_self 2 (by omega)
  exact hasParGen_of_mulEquiv e.symm (hasParGen_statedProj _ h2 hpg)

theorem hasParGen_POmegaPlus {G : Type} [Group G] [Finite G] {n f : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel G .POmegaPlus n 2 f) : HasParGen G := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hn3 : 3 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  haveI : CharP K 2 := burnsideI2BN_charP_of_card Nat.prime_two hf hK
  haveI : Finite (spinGroup (quadPlus n K)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := K))
  obtain ⟨hpg, hodd⟩ := parGen_spinPlus hn hf K hK
  have hq := hasParGen_of_surjective (QuotientGroup.mk' (center (spinGroup (quadPlus n K))))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (fun x hx => hodd x (by rwa [QuotientGroup.ker_mk'] at hx)) hpg
  exact hasParGen_of_mulEquiv ((spinQuotientCenterEquivQuadPlus hn3).trans e.symm) hq

theorem hasParGen_POmegaMinus {G : Type} [Group G] [Finite G] {n f : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel G .POmegaMinus n 2 f) : HasParGen G := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  haveI : CharP K 2 := burnsideI2BN_charP_of_card Nat.prime_two hf hK
  haveI : Finite (spinGroup (quadMinus n K b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  obtain ⟨hpg, hodd⟩ := parGen_spinMinus hn hf K hK hirr
  have hq := hasParGen_of_surjective
    (QuotientGroup.mk' (center (spinGroup (quadMinus n K b c))))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (fun x hx => hodd x (by rwa [QuotientGroup.ker_mk'] at hx)) hpg
  exact hasParGen_of_mulEquiv ((spinQuotientCenterEquivQuadMinus hn hirr).trans e.symm) hq

theorem hasParGen_of_statedClassicalModel {G : Type} [Group G] [Finite G] {t : StatedLieTag}
    {n f : ℕ} (h : StatedClassicalModel G t n 2 f) (h1 : ¬ (t = .PSL ∧ n = 2))
    (h2 : ¬ (t = .PSU ∧ n = 3)) : HasParGen G := by
  have hadm := h.1
  obtain ⟨-, -, hadm'⟩ := hadm
  cases t with
  | PSL => exact hasParGen_PSL (by simp at h1 hadm'; omega) h
  | PSU => exact hasParGen_PSU (by simp at h2 hadm'; omega) h
  | PSp => exact hasParGen_PSp (by simpa using hadm'.1) h
  | POmegaOdd => exact absurd rfl hadm'.2
  | POmegaPlus => exact hasParGen_POmegaPlus hadm' h
  | POmegaMinus => exact hasParGen_POmegaMinus hadm' h
  | _ => exact h.2.elim

end Models

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
