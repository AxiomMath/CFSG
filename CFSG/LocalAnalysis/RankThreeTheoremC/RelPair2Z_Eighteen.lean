module

import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Lift
import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.ABGLocalTools
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem zjn_mulAut_eq_one {X : Type} [Group X] [Finite X] (hX : Group.IsSolvable X) {q m : ℕ}
    [Fact q.Prime] (hcop : Nat.Coprime m (Nat.card X)) (hcore : CFSG.pPrimeCore q X = ⊥)
    (S : Sylow q X) (φ : MulAut X) (hm : φ ^ m = 1) (hfix : ∀ x ∈ (S : Subgroup X), φ x = x) :
    φ = 1 := by
  have hF : CFSG.fittingSubgroup X = CFSG.pCore q X := CFSG.Fitting_eq_pcore X q hcore
  have hFS : CFSG.fittingSubgroup X ≤ (S : Subgroup X) := by
    rw [hF]
    exact (CFSG.pCore_isPGroup (p := q) (G := X)).le_sylow_of_normal S
  refine CFSG.mulAut_eq_one_of_fixes_fittingSubgroup X hX φ m hm ?_ (fun x hx => hfix x (hFS hx))
  exact hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _)

theorem zjn_le_of_sup {p : ℕ} {Y : Type} [Group Y] {J R N : Subgroup Y} (hRJ : R ≤ J)
    (hNJ : N ≤ J) (hRn : R.Normal) (hRp : p.Coprime (Nat.card R))
    (hJp : pElementSubgroup p J = J) (hnorm : ∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N)
    (hJN : J ≤ N ⊔ R) : J ≤ N := by
  have hNn : (N.subgroupOf J).Normal := ⟨fun n hn g => by
    have := hnorm g g.2 n (Subgroup.mem_subgroupOf.mp hn)
    exact Subgroup.mem_subgroupOf.mpr this⟩
  rw [← hJp]
  refine (Subgroup.closure_le N).mpr ?_
  rintro x ⟨hxJ, k, hk⟩
  obtain ⟨n, hn, r, hr, hnr⟩ := Subgroup.mem_sup_of_normal_right.mp (hJN hxJ)
  set π := QuotientGroup.mk' (N.subgroupOf J) with hπ
  have hx' : (⟨x, hxJ⟩ : J) = ⟨n, hNJ hn⟩ * ⟨r, hRJ hr⟩ := Subtype.ext hnr.symm
  have hn1 : π ⟨n, hNJ hn⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (by
    exact Subgroup.mem_subgroupOf.mpr hn)
  have h1 : orderOf (π ⟨x, hxJ⟩) ∣ p ^ k := by
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_mk, hk]
  have h2 : orderOf (π ⟨x, hxJ⟩) ∣ Nat.card R := by
    rw [hx', map_mul, hn1, one_mul]
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard R hr
  have h3 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hRp) h1 h2
  have : π ⟨x, hxJ⟩ = 1 := orderOf_eq_one_iff.mp h3
  have := (QuotientGroup.eq_one_iff _).mp this
  exact Subgroup.mem_subgroupOf.mp this

theorem zjn_core {p q : ℕ} (hp : p.Prime) (hqp : q.Prime) {Y : Type} [Group Y] [Finite Y]
    {J R Q : Subgroup Y} (hRJ : R ≤ J) (hJn : J.Normal) (hRn : R.Normal)
    (hRp : p.Coprime (Nat.card R)) (hRs : Group.IsSolvable R)
    (hJp : pElementSubgroup p J = J) (hJR : ⁅J, J⁆ ⊔ R = J)
    (hQ : IsSylowOf q Q ⁅J, R⁆) (hq : q ∣ Nat.card (⁅J, R⁆ : Subgroup Y))
    (hcore : CFSG.pPrimeCore q ↥(⁅J, R⁆ : Subgroup Y) = ⊥) :
    ¬ J ≤ (centralizer (Q : Set Y) ⊓ J) ⊔ R := by
  intro hcov
  have : Fact q.Prime := ⟨hqp⟩
  set X : Subgroup Y := ⁅J, R⁆ with hX
  have hXn : X.Normal := inferInstance
  have hXR : X ≤ R := Subgroup.commutator_le_right J R
  have hXJ : X ≤ J := hXR.trans hRJ
  have hXs : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXR)
  obtain ⟨S, hS⟩ := hQ
  set C : Subgroup Y := centralizer (Q : Set Y) ⊓ J with hC
  have hS2 : ∀ y ∈ C, (∃ k : ℕ, orderOf y = p ^ k) → ∀ x ∈ X, y * x = x * y := by
    rintro y hyC ⟨k, hk⟩ x hx
    have hφ1 : (MulAut.conjNormal y : MulAut ↥X) ^ (p ^ k) = 1 := by
      rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
    have hcop : Nat.Coprime (p ^ k) (Nat.card ↥X) :=
      Nat.Coprime.pow_left k (hRp.coprime_dvd_right (Subgroup.card_dvd_of_le hXR))
    have hfix : ∀ z ∈ (S : Subgroup ↥X), (MulAut.conjNormal y : MulAut ↥X) z = z := by
      intro z hz
      have hzQ : (z : Y) ∈ Q := by
        rw [← hS]
        exact ⟨z, hz, rfl⟩
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have h := mem_centralizer_iff.mp hyC.1 (z : Y) hzQ
      rw [mul_inv_eq_iff_eq_mul]
      exact h.symm
    have h1 := zjn_mulAut_eq_one hXs hcop hcore S _ hφ1 hfix
    have h2 := congrArg (fun φ : MulAut ↥X => (φ ⟨x, hx⟩ : Y)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hlift : ∀ x ∈ J, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ pElementSubgroup p C ⊔ R := by
    rintro x hxJ ⟨k, hk⟩
    obtain ⟨c, hcC, r, hrR, hcr⟩ := Subgroup.mem_sup_of_normal_right.mp (hcov hxJ)
    have hn0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
    have hcop2 : Nat.Coprime (p ^ a) m :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop2
    have hc1 : c ^ (v * (m : ℤ)) * c ^ (u * ((p ^ a : ℕ) : ℤ)) = c := by
      rw [← zpow_add]
      have : v * (m : ℤ) + u * ((p ^ a : ℕ) : ℤ) = 1 := by linarith
      rw [this, zpow_one]
    have hcn : c ^ orderOf c = 1 := pow_orderOf_eq_one c
    have hc1mem : c ^ (v * (m : ℤ)) ∈ C := zpow_mem hcC _
    have hc2mem : c ^ (u * ((p ^ a : ℕ) : ℤ)) ∈ C := zpow_mem hcC _
    have hord1 : ∃ j : ℕ, orderOf (c ^ (v * (m : ℤ))) = p ^ j := by
      have h1 : (c ^ (v * (m : ℤ))) ^ (p ^ a) = 1 := by
        rw [← zpow_natCast, ← zpow_mul]
        have : v * (m : ℤ) * ((p ^ a : ℕ) : ℤ) = (orderOf c : ℤ) * v := by
          rw [hn]; push_cast; ring
        rw [this, zpow_mul, zpow_natCast, hcn, one_zpow]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h1)
      exact ⟨j, hj⟩
    have hc2R : c ^ (u * ((p ^ a : ℕ) : ℤ)) ∈ R := by
      rw [← QuotientGroup.eq_one_iff]
      set ρ := QuotientGroup.mk' R with hρ
      have hρr : ρ r = 1 := (QuotientGroup.eq_one_iff r).mpr hrR
      have hρc : ρ c = ρ x := by rw [← hcr, map_mul, hρr, mul_one]
      have h1 : (ρ c) ^ (p ^ k) = 1 := by
        rw [hρc, ← map_pow, ← hk, pow_orderOf_eq_one, map_one]
      have h2 : (ρ (c ^ (u * ((p ^ a : ℕ) : ℤ)))) ^ (p ^ k) = 1 := by
        rw [map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
      have h3 : (ρ (c ^ (u * ((p ^ a : ℕ) : ℤ)))) ^ m = 1 := by
        rw [← map_pow, ← zpow_natCast, ← zpow_mul]
        have : u * ((p ^ a : ℕ) : ℤ) * (m : ℤ) = (orderOf c : ℤ) * u := by
          rw [hn]; push_cast; ring
        rw [this, zpow_mul, zpow_natCast, hcn, one_zpow, map_one]
      have hcop3 : Nat.Coprime (p ^ k) m :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes hcop3 (orderOf_dvd_of_pow_eq_one h2)
          (orderOf_dvd_of_pow_eq_one h3))
    have hx : x = c ^ (v * (m : ℤ)) * (c ^ (u * ((p ^ a : ℕ) : ℤ)) * r) := by
      rw [← mul_assoc, hc1, hcr]
    rw [hx]
    refine Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨hc1mem, hord1⟩) ?_
    exact R.mul_mem hc2R hrR
  have hJER : J ≤ pElementSubgroup p C ⊔ R := by
    conv_lhs => rw [← hJp]
    exact (Subgroup.closure_le _).mpr fun x hx => hlift x hx.1 hx.2
  let Φ : ↥J →* MulAut ↥X := (MulAut.conjNormal : Y →* MulAut ↥X).comp J.subtype
  obtain ⟨N, hN⟩ : ∃ N : Subgroup Y, N = Φ.ker.map J.subtype := ⟨_, rfl⟩
  have hmemN : ∀ y : Y, y ∈ N ↔ ∃ y' : ↥J, y' ∈ Φ.ker ∧ (y' : Y) = y := by
    intro y
    rw [hN]
    exact Subgroup.mem_map
  have hNJ : N ≤ J := by
    intro y hy
    obtain ⟨y', -, rfl⟩ := (hmemN y).mp hy
    exact y'.2
  have hker_norm : ∀ a ∈ Φ.ker, ∀ g : ↥J, g * a * g⁻¹ ∈ Φ.ker := by
    intro a ha g
    rw [MonoidHom.mem_ker] at ha ⊢
    rw [map_mul, map_mul, ha, mul_one, map_inv, mul_inv_cancel]
  have hnorm : ∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N := by
    intro j hj n hn
    obtain ⟨n', hn', rfl⟩ := (hmemN n).mp hn
    have hmem : ((⟨j, hj⟩ * n' * ⟨j, hj⟩⁻¹ : ↥J) : Y) = j * (n' : Y) * j⁻¹ := rfl
    rw [← hmem]
    exact (hmemN _).mpr ⟨_, hker_norm n' hn' ⟨j, hj⟩, rfl⟩
  have hEN : pElementSubgroup p C ≤ N := by
    refine (Subgroup.closure_le N).mpr ?_
    rintro y ⟨hyC, hy⟩
    refine (hmemN y).mpr ⟨⟨y, hyC.2⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    ext x
    have := hS2 y hyC hy x x.2
    simp only [Φ, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply]
    show y * (x : Y) * y⁻¹ = x
    rw [this, mul_inv_cancel_right]
  have hJN : J ≤ N ⊔ R := hJER.trans (sup_le_sup_right hEN R)
  have hJNle : J ≤ N := zjn_le_of_sup hRJ hNJ hRn hRp hJp hnorm hJN
  have hcentral : ∀ j ∈ J, ∀ x ∈ X, j * x = x * j := by
    intro j hj x hx
    obtain ⟨j', hj', hjj⟩ := (hmemN j).mp (hJNle hj)
    have h1 : Φ j' = 1 := hj'
    have h2 := congrArg (fun φ : MulAut ↥X => (φ ⟨x, hx⟩ : Y)) h1
    simp only [Φ, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    have h3 : (j' : Y) * x * (j' : Y)⁻¹ = x := h2
    rw [hjj] at h3
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  have hJJ : ⁅J, J⁆ = J := by
    refine le_antisymm (Subgroup.commutator_le_left J J) ?_
    refine zjn_le_of_sup (R := R) hRJ (Subgroup.commutator_le_left J J) hRn hRp hJp ?_ hJR.ge
    intro j _ n hn
    exact (inferInstance : (⁅J, J⁆ : Subgroup Y).Normal).conj_mem n hn j
  have h1 : ⁅⁅J, R⁆, J⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro j hj
    exact hcentral j hj x hx
  have h2 : ⁅⁅R, J⁆, J⁆ = ⊥ := by
    rw [Subgroup.commutator_comm R J]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := J) (H₂ := J) (H₃ := R) h1 h2
  rw [hJJ] at h3
  have hXbot : X = ⊥ := h3
  rw [hXbot, Subgroup.card_bot] at hq
  exact hqp.one_lt.ne' (Nat.dvd_one.mp hq)

theorem eighteen_ten_solvable {p q : ℕ} (hp : p.Prime) (hqp : q.Prime) {Y : Type} [Group Y]
    [Finite Y] {J R Q : Subgroup Y} (hRJ : R ≤ J) (hJn : J.Normal) (hRn : R.Normal)
    (hRp : p.Coprime (Nat.card R)) (hRs : Group.IsSolvable R)
    (hJp : pElementSubgroup p J = J) (hJR : ⁅J, J⁆ ⊔ R = J)
    (hQ : IsSylowOf q Q ⁅J, R⁆) (hq : q ∣ Nat.card (⁅J, R⁆ : Subgroup Y)) :
    ¬ J ≤ (centralizer (Q : Set Y) ⊓ J) ⊔ R := by
  intro hcov
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨X, hX⟩ : ∃ X : Subgroup Y, X = ⁅J, R⁆ := ⟨_, rfl⟩
  have hXn : X.Normal := by rw [hX]; infer_instance
  have hXR : X ≤ R := by rw [hX]; exact Subgroup.commutator_le_right J R
  obtain ⟨N0, hN0⟩ : ∃ N0 : Subgroup ↥X, N0 = CFSG.pPrimeCore q ↥X := ⟨_, rfl⟩
  have hN0n : N0.Normal := by rw [hN0]; infer_instance
  obtain ⟨N, hN⟩ : ∃ N : Subgroup Y, N = N0.map X.subtype := ⟨_, rfl⟩
  have hNn : N.Normal := by
    have : N0.Characteristic := by rw [hN0]; infer_instance
    rw [hN]
    infer_instance
  have hNX : N ≤ X := by rw [hN]; exact Subgroup.map_subtype_le _
  have hNcop : q.Coprime (Nat.card N) := by
    rw [hN, Subgroup.card_map_of_injective X.subtype_injective, hN0]
    exact CFSG.pPrimeCore_coprime_card
  set ρ : Y →* Y ⧸ N := QuotientGroup.mk' N with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective N
  have hker : ρ.ker = N := QuotientGroup.ker_mk' N
  rw [← hX] at hQ hq
  have hXh : ⁅J.map ρ, R.map ρ⁆ = X.map ρ := by rw [hX, Subgroup.map_commutator]
  have hcore' : CFSG.pPrimeCore q ↥(⁅J.map ρ, R.map ρ⁆ : Subgroup (Y ⧸ N)) = ⊥ := by
    rw [hXh]
    set f' : ↥X →* ↥(X.map ρ) := ρ.subgroupMap X with hf'
    have hf's : Function.Surjective f' := ρ.subgroupMap_surjective X
    have hk : f'.ker = N0 := by
      ext x
      rw [MonoidHom.mem_ker]
      have h1 : f' x = 1 ↔ ρ (x : Y) = 1 := by
        constructor
        · intro h
          exact congrArg Subtype.val h
        · intro h
          exact Subtype.ext h
      rw [h1, ← MonoidHom.mem_ker, hker, hN]
      exact (Subgroup.mem_map_iff_mem X.subtype_injective)
    let e : ↥X ⧸ N0 ≃* ↥(X.map ρ) :=
      (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f' hf's)
    have h2 := CFSG.pPrimeCore_map_iso q e
    have h3 : CFSG.pPrimeCore q (↥X ⧸ N0) = ⊥ := by
      subst hN0
      exact CFSG.pPrimeCore_quotient_eq_bot hqp
    rw [h3, Subgroup.map_bot] at h2
    exact h2.symm
  have hρN : ∀ y : Y, y ∈ N → ρ y = 1 := fun y hy => (QuotientGroup.eq_one_iff y).mpr hy
  have hRp' : p.Coprime (Nat.card (R.map ρ)) :=
    hRp.coprime_dvd_right (Subgroup.card_map_dvd R ρ)
  have hRs' : Group.IsSolvable (R.map ρ) :=
    Group.isSolvable_of_surjective (ρ.subgroupMap_surjective R)
  have hJp' : pElementSubgroup p (J.map ρ) = J.map ρ := by
    refine le_antisymm (pElementSubgroup_le _) ?_
    conv_lhs => rw [← hJp]
    rw [pElementSubgroup, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, ⟨hxJ, k, hk⟩, rfl⟩
    refine Subgroup.subset_closure ⟨⟨x, hxJ, rfl⟩, ?_⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp
      ((orderOf_map_dvd ρ x).trans (dvd_of_eq hk))
    exact ⟨j, hj⟩
  have hJR' : ⁅J.map ρ, J.map ρ⁆ ⊔ R.map ρ = J.map ρ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_sup, hJR]
  have hQ' : IsSylowOf q (Q.map ρ) ⁅J.map ρ, R.map ρ⁆ := by
    rw [hXh]
    exact isSylowOf_map_hom ρ hQ
  have hq' : q ∣ Nat.card (⁅J.map ρ, R.map ρ⁆ : Subgroup (Y ⧸ N)) := by
    rw [hXh]
    have h1 := card_eq_card_map_mul_card_inf_ker ρ X
    rw [hker, inf_eq_right.mpr hNX] at h1
    rw [h1] at hq
    exact (Nat.Coprime.dvd_of_dvd_mul_right hNcop hq)
  refine zjn_core hp hqp (Subgroup.map_mono hRJ) (hJn.map ρ hρs) (hRn.map ρ hρs) hRp' hRs' hJp'
    hJR' hQ' hq' hcore' ?_
  have h1 := Subgroup.map_mono (f := ρ) hcov
  rw [Subgroup.map_sup] at h1
  refine h1.trans (sup_le_sup_right ?_ _)
  rintro _ ⟨c, ⟨hcC, hcJ⟩, rfl⟩
  refine ⟨?_, ⟨c, hcJ, rfl⟩⟩
  show ρ c ∈ centralizer ((Q.map ρ : Subgroup (Y ⧸ N)) : Set (Y ⧸ N))
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have h : y * c = c * y := mem_centralizer_iff.mp (show c ∈ centralizer (Q : Set Y) from hcC) y hy
  rw [← map_mul, ← map_mul, h]


end CFSG.LocalAnalysis.RankThreeTheoremC
