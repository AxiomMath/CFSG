module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeModelDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeLinBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeLinTorus
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.Open.StatedAPI

namespace LinThree

section FieldFacts

variable {K : Type} [Field K] [Finite K]

theorem three_ne_zero_of_not_dvd_card (h : ¬ 3 ∣ Nat.card K) : (3 : K) ≠ 0 := by
  intro h0
  apply h
  have hfin := Fintype.ofFinite K
  have hchar : ringChar K ∣ 3 := by
    have : ((3 : ℕ) : K) = 0 := by exact_mod_cast h0
    exact (CharP.cast_eq_zero_iff K (ringChar K) 3).1 this
  have hprime : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have h33 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_three).1 hchar
  have hdvd : ringChar K ∣ Fintype.card K :=
    (CharP.cast_eq_zero_iff K (ringChar K) (Fintype.card K)).1 (Nat.cast_card_eq_zero K)
  rw [h33] at hdvd
  rwa [Nat.card_eq_fintype_card]

theorem no_root_of_not_dvd_card_sub_one (h3 : (3 : K) ≠ 0) (h : ¬ 3 ∣ Nat.card K - 1) (x : K) :
    x ^ 2 + x + 1 ≠ 0 := by
  intro hx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hx
  let u : Kˣ := Units.mk0 x hx0
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa [u] using hx3)
  have hu1 : u ≠ 1 := fun h' => hx1 (by simpa [u] using congrArg Units.val h')
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have := orderOf_dvd_natCard u
  rw [hord, Nat.card_units] at this
  exact h this

theorem unit_eq_one_of_pow_three (hN : Nat.Coprime 3 (Nat.card K - 1)) (d : Kˣ) (hd : d ^ 3 = 1) :
    d = 1 := by
  have h1 : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd
  have h2 : orderOf d ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard d
  have h3 : orderOf d ∣ Nat.gcd 3 (Nat.card K - 1) := Nat.dvd_gcd h1 h2
  rw [hN] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

end FieldFacts

end LinThree

open LinThree

theorem i294CrossModelPSL67_holds : I294CrossModelPSL67 := by
  intro K _ _ h3q h3q1 n hn x hx
  have h6 : 6 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hN : Nat.Coprime 3 (Nat.card K - 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3q1
  have hZ : ∀ z ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K),
      z ^ (Nat.card K - 1) = 1 :=
    pow_eq_one_of_mem_statedScalars_subgroupOf fun c _ => by
      rw [← Nat.card_units]
      exact pow_card_eq_one' (G := Kˣ)
  obtain ⟨g, hg3, rfl⟩ := exists_lift_pow_three hN hZ hx3
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_not_dvd_card h3q
  have hroot := no_root_of_not_dvd_card_sub_one h3 h3q1
  let gL : Module.End K (Fin n → K) :=
    Matrix.toLinAlgEquiv' ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hgL3 : gL ^ 3 = 1 := by
    have hA : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
      have := congrArg (fun z : StatedSL n K => ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        hg3
      simpa using this
    rw [← map_pow, hA, map_one]
  obtain ⟨E, hEinj, hEcomm⟩ := exists_torus_hom gL hgL3 h3 hroot
    (by rw [Module.finrank_fin_fun]; exact h6)
  let φ : Multiplicative (Fin 3 → ZMod 3) →* GL (Fin n) K :=
    (Matrix.GeneralLinearGroup.toLin.symm :
      LinearMap.GeneralLinearGroup K (Fin n → K) ≃* GL (Fin n) K).toMonoidHom.comp E.toHomUnits
  have hφtoLin : ∀ a, Matrix.GeneralLinearGroup.toLin (φ a) = E.toHomUnits a := fun a =>
    MulEquiv.apply_symm_apply _ _
  have hφinj : Function.Injective φ := by
    intro a a' h
    apply hEinj
    have h1 := congrArg Matrix.GeneralLinearGroup.toLin h
    rw [hφtoLin, hφtoLin] at h1
    exact congrArg Units.val h1
  have hpow : ∀ a : Multiplicative (Fin 3 → ZMod 3), a ^ 3 = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_one]
    funext j
    simp only [Pi.smul_apply, Pi.zero_apply]
    generalize Multiplicative.toAdd a j = y
    revert y
    decide
  have hcard : Nat.card (Multiplicative (Fin 3 → ZMod 3)) = 3 ^ 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 3 → ZMod 3) ≃ _)]
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  have hH : ∀ a, φ a ∈ StatedSL n K := by
    intro a
    have h3a : (φ a) ^ 3 = 1 := by rw [← map_pow, hpow a, map_one]
    have hd : (Matrix.GeneralLinearGroup.det (φ a)) ^ 3 = 1 := by
      rw [← map_pow, h3a, map_one]
    have hd1 := unit_eq_one_of_pow_three hN _ hd
    rw [mem_statedSL_iff]
    have := congrArg Units.val hd1
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  have hcomm : ∀ a, (g : GL (Fin n) K) * φ a = φ a * (g : GL (Fin n) K) := by
    intro a
    apply Matrix.GeneralLinearGroup.toLin.injective
    rw [map_mul, map_mul, hφtoLin]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact (hEcomm a).symm
  exact le_pRank_centralizer_statedProj_of_coprime (H := StatedSL n K)
    (A := Multiplicative (Fin 3 → ZMod 3)) (k := 3) (N := Nat.card K - 1) hN hZ
    (fun a b => mul_comm a b) hpow hcard φ hφinj hH g hcomm

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
