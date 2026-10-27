module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115dA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115cC

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec11dRho (t z : G) (K1 K2 R : Subgroup G) (ρ : ↥R →* MulAut ↥(K1 ⊔ K2)) : Prop where
  lift : ∀ κ : ↥(K1 ⊔ K2), ∃ k ∈ secKD (secD K1 K2 R), ∃ n ∈ oddCoreIn (secK0 t z),
    k = n * (κ : G)
  act : ∀ (y : ↥R) (k n : G) (κ : ↥(K1 ⊔ K2)), k ∈ secKD (secD K1 K2 R) →
    n ∈ oddCoreIn (secK0 t z) → k = n * (κ : G) →
      ∃ n' ∈ oddCoreIn (secK0 t z), (y : G) * k * (y : G)⁻¹ = n' * ((ρ y κ : ↥(K1 ⊔ K2)) : G)

theorem sec11d_cent_mem_KD [Finite G] {t z : G} {D : Subgroup G}
    (hK0 : secK0 t z = secKD D ⊔ oddCoreIn (secK0 t z)) (hKD : secKD D ≤ secK0 t z) {x : G}
    (hx : x ∈ secK0 t z) (hxD : ∀ d ∈ D, d * x = x * d) : x ∈ secKD D := by
  have hKN : ∀ a ∈ secKD D, ∀ n ∈ oddCoreIn (secK0 t z),
      a * n * a⁻¹ ∈ oddCoreIn (secK0 t z) := fun a ha n hn =>
    sec11_conj_mem_oddCoreIn (Subgroup.le_normalizer (hKD ha)) hn
  have hx' : x ∈ secKD D ⊔ oddCoreIn (secK0 t z) := hK0 ▸ hx
  obtain ⟨a, ha, n, hn, rfl⟩ := sec11d_mem_sup hKN x hx'
  have haD : ∀ d ∈ D, d * a = a * d := fun d hd =>
    Subgroup.mem_centralizer_iff.mp (sec11c_oTwoRes_le _ ha) d hd
  have hnD : n ∈ centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 := haD d hd
    have h2 := hxD d hd
    refine mul_left_cancel (a := a) ?_
    calc a * (d * n) = (a * d) * n := by group
      _ = (d * a) * n := by rw [h1]
      _ = d * (a * n) := by group
      _ = (a * n) * d := h2
      _ = a * (n * d) := by group
  have hnK : n ∈ secKD D := sec11c_mem_oTwoRes hnD (odd_orderOf_of_mem_oddCoreIn hn)
  exact Subgroup.mul_mem _ ha hnK

theorem sec11d_exists_rho [Finite G] {t z : G} {K1 K2 R : Subgroup G}
    (hS : Sec11cSplit t z K1 K2) (hWD : zpowers t ⊔ zpowers z ≤ secD K1 K2 R)
    (hRN : R ≤ normalizer (secKD (secD K1 K2 R) : Set G))
    (hK0 : secK0 t z = secKD (secD K1 K2 R) ⊔ oddCoreIn (secK0 t z)) :
    ∃ ρ : ↥R →* MulAut ↥(K1 ⊔ K2), Sec11dRho t z K1 K2 R ρ := by
  set D := secD K1 K2 R with hD
  set KD := secKD D with hKD
  set N0 := oddCoreIn (secK0 t z) with hN0
  have hKD0 : KD ≤ secK0 t z := sec11c_KD_le_K0 hWD
  have hDQ : ∀ e ∈ D, ∀ q ∈ secQ K1 K2, e * q = q * e := fun e he q hq =>
    (Subgroup.mem_centralizer_iff.mp he.1 q hq).symm
  have hKN : ∀ a ∈ KD, ∀ n ∈ N0, a * n * a⁻¹ ∈ N0 := fun a ha n hn =>
    sec11_conj_mem_oddCoreIn (Subgroup.le_normalizer (hKD0 ha)) hn
  obtain ⟨Pr, hPr1, hPr2⟩ := hS.split.exists_proj
  let Pi : ↥KD →* ↥(K1 ⊔ K2) := Pr.comp (Subgroup.inclusion hKD0)
  have hPi : ∀ (a : ↥KD) (n : G) (κ : ↥(K1 ⊔ K2)), n ∈ N0 → (a : G) = n * (κ : G) →
      Pi a = κ := fun a n κ hn h => hPr2 (Subgroup.inclusion hKD0 a) n κ hn h
  have hPi1 : ∀ a : ↥KD, ∃ n ∈ N0, (a : G) = n * (Pi a : G) := fun a =>
    hPr1 (Subgroup.inclusion hKD0 a)
  have hlift : ∀ κ : ↥(K1 ⊔ K2), ∃ a : ↥KD, ∃ n ∈ N0, (a : G) = n * (κ : G) := by
    intro κ
    have hκ : (κ : G) ∈ KD ⊔ N0 := hK0 ▸ hS.split.right_le κ.2
    obtain ⟨a, ha, n, hn, hκan⟩ := sec11d_mem_sup hKN _ hκ
    have h1 : (a : G) = n⁻¹ * (κ : G) := by
      calc a = (κ : G) * n⁻¹ := by rw [hκan]; group
        _ = n⁻¹ * (κ : G) := hS.comm' (N0.inv_mem hn) κ.2
    exact ⟨⟨a, ha⟩, n⁻¹, N0.inv_mem hn, h1⟩
  have hsurj : Function.Surjective Pi := by
    intro κ
    obtain ⟨a, n, hn, h⟩ := hlift κ
    exact ⟨a, hPi a n κ hn h⟩
  have hPi_one : ∀ a : ↥KD, Pi a = 1 ↔ (a : G) ∈ N0 := by
    intro a
    constructor
    · intro h1
      obtain ⟨n, hn, hn'⟩ := hPi1 a
      rw [h1] at hn'
      have : (a : G) = n := by simpa using hn'
      rw [this]
      exact hn
    · intro h1
      exact hPi a a 1 h1 (by simp)
  let c : ↥R →* MulAut ↥KD := KD.normalizerMonoidHom.comp (Subgroup.inclusion hRN)
  have hc : ∀ (y : ↥R) (a : ↥KD), ((c y a : ↥KD) : G) = (y : G) * (a : G) * (y : G)⁻¹ :=
    fun y a => rfl
  have hker : ∀ (y : ↥R) (a : ↥KD), Pi a = 1 → Pi (c y a) = 1 := by
    intro y a ha
    rw [hPi_one] at ha ⊢
    rw [hc]
    have h1 : (y : G) * (a : G) * (y : G)⁻¹ ∈ oddCoreIn KD :=
      sec11_conj_mem_oddCoreIn (hRN y.2) (hS.inf_le_oddCore hKD0 ⟨a.2, ha⟩)
    exact hS.oddCore_le hKD0 hDQ h1
  obtain ⟨ρ, hρ⟩ := sec11d_descent Pi hsurj c hker
  refine ⟨ρ, ⟨fun κ => ?_, fun y k n κ hk hn hkn => ?_⟩⟩
  · obtain ⟨a, n, hn, h⟩ := hlift κ
    exact ⟨a, a.2, n, hn, h⟩
  · have hPik : Pi ⟨k, hk⟩ = κ := hPi ⟨k, hk⟩ n κ hn hkn
    have h1 : ρ y κ = Pi (c y ⟨k, hk⟩) := by
      rw [← hPik]
      exact hρ y ⟨k, hk⟩
    obtain ⟨n', hn', h2⟩ := hPi1 (c y ⟨k, hk⟩)
    refine ⟨n', hn', ?_⟩
    rw [h1]
    exact (hc y ⟨k, hk⟩).symm.trans h2

namespace Sec11dRho

variable {t z : G} {K1 K2 R : Subgroup G} {ρ : ↥R →* MulAut ↥(K1 ⊔ K2)}

theorem apply_conj [Finite G] (hρ : Sec11dRho t z K1 K2 R ρ) (hS : Sec11cSplit t z K1 K2)
    {y : ↥R}
    (hyN : ∀ n ∈ oddCoreIn (secK0 t z), (y : G) * n * (y : G)⁻¹ ∈ oddCoreIn (secK0 t z))
    {κ : ↥(K1 ⊔ K2)} (hκ : (y : G) * (κ : G) * (y : G)⁻¹ ∈ K1 ⊔ K2) :
    ((ρ y κ : ↥(K1 ⊔ K2)) : G) = (y : G) * (κ : G) * (y : G)⁻¹ := by
  obtain ⟨k, hk, n0, hn0, hkn⟩ := hρ.lift κ
  obtain ⟨n', hn', h⟩ := hρ.act y k n0 κ hk hn0 hkn
  have e : (y : G) * k * (y : G)⁻¹ =
      ((y : G) * n0 * (y : G)⁻¹) * ((y : G) * (κ : G) * (y : G)⁻¹) := by
    rw [hkn]
    group
  rw [e] at h
  exact (hS.split.unique (hyN n0 hn0) hn' hκ (ρ y κ).2 h).2.symm

theorem ker_of_mem [Finite G] (hρ : Sec11dRho t z K1 K2 R ρ) (hS : Sec11cSplit t z K1 K2)
    {y : ↥R} (hy : (y : G) ∈ secD K1 K2 R) : ρ y = 1 := by
  refine MulEquiv.ext fun κ => ?_
  obtain ⟨k, hk, n0, hn0, hkn⟩ := hρ.lift κ
  obtain ⟨n', hn', h⟩ := hρ.act y k n0 κ hk hn0 hkn
  have hcomm : (y : G) * k * (y : G)⁻¹ = k := by
    have h1 : (y : G) * k = k * (y : G) :=
      Subgroup.mem_centralizer_iff.mp (sec11c_oTwoRes_le _ hk) (y : G) hy
    rw [h1]
    group
  rw [hcomm, hkn] at h
  exact Subtype.ext (hS.split.unique hn0 hn' κ.2 (ρ y κ).2 h).2.symm

theorem mem_of_ker [Finite G] (hρ : Sec11dRho t z K1 K2 R ρ) (hS : Sec11cSplit t z K1 K2)
    (hQKD : secQ K1 K2 ≤ secKD (secD K1 K2 R))
    (hRQ : R ≤ normalizer (secQ K1 K2 : Set G)) {y : ↥R} (hy : ρ y = 1) :
    (y : G) ∈ secD K1 K2 R := by
  suffices hyc : (y : G) ∈ centralizer (secQ K1 K2 : Set G) from ⟨hyc, y.2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqK : q ∈ K1 ⊔ K2 := hS.Q_le hq
  obtain ⟨n', hn', h⟩ := hρ.act y q 1 ⟨q, hqK⟩ (hQKD hq) (oddCoreIn _).one_mem (by simp)
  rw [hy] at h
  have hyq : (y : G) * q * (y : G)⁻¹ ∈ secQ K1 K2 :=
    (Subgroup.mem_normalizer_iff.mp (hRQ y.2) q).mp hq
  have h' : (1 : G) * ((y : G) * q * (y : G)⁻¹) = n' * q := by
    rw [one_mul]
    exact h
  have hu := (hS.split.unique (oddCoreIn _).one_mem hn' (hS.Q_le hyq) hqK h').2
  exact (mul_inv_eq_iff_eq_mul.mp hu).symm

theorem conj_of_mem [Finite G] (hρ : Sec11dRho t z K1 K2 R ρ) (hS : Sec11cSplit t z K1 K2)
    {y : ↥R} (hyK : (y : G) ∈ K1 ⊔ K2) : ρ y = MulAut.conj (⟨(y : G), hyK⟩ : ↥(K1 ⊔ K2)) := by
  refine MulEquiv.ext fun κ => Subtype.ext ?_
  have hyN : ∀ n ∈ oddCoreIn (secK0 t z), (y : G) * n * (y : G)⁻¹ ∈ oddCoreIn (secK0 t z) :=
    fun n hn => sec11_conj_mem_oddCoreIn
      (Subgroup.le_normalizer (hS.split.right_le hyK)) hn
  have hκ : (y : G) * (κ : G) * (y : G)⁻¹ ∈ K1 ⊔ K2 :=
    (K1 ⊔ K2).mul_mem ((K1 ⊔ K2).mul_mem hyK κ.2) ((K1 ⊔ K2).inv_mem hyK)
  exact hρ.apply_conj hS hyN hκ

end Sec11dRho

end CFSG.OddStandard.SmallF3.Omega
