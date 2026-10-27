module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115dC

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec11dSet (t z : G) (K1 K2 R : Subgroup G) : Prop where
  split : Sec11cSplit t z K1 K2
  KD_le : secKD (secD K1 K2 R) ≤ secK0 t z
  RN : R ≤ normalizer (secKD (secD K1 K2 R) : Set G)
  K0_eq : secK0 t z = secKD (secD K1 K2 R) ⊔ oddCoreIn (secK0 t z)

namespace Sec11dSet

variable {t z : G} {K1 K2 R Ki : Subgroup G}

theorem Xi_le_KD [Finite G] (hs : Sec11dSet t z K1 K2 R) (hKi : Ki ≤ K1 ⊔ K2) :
    secKiD t z Ki (secD K1 K2 R) ≤ secKD (secD K1 K2 R) := by
  intro x hx
  have hN0 : oddCoreIn (secK0 t z) ≤ secK0 t z := (oddCoreIn_normal _).1
  have hle : Ki ⊔ oddCoreIn (secK0 t z) ≤ secK0 t z :=
    sup_le (hKi.trans hs.split.split.right_le) hN0
  refine sec11d_cent_mem_KD hs.K0_eq hs.KD_le (hle hx.1) fun d hd => ?_
  exact Subgroup.mem_centralizer_iff.mp hx.2 d hd

theorem Xi_decomp [Finite G] (hs : Sec11dSet t z K1 K2 R) (hKi : Ki ≤ K1 ⊔ K2) {x : G}
    (hx : x ∈ secKiD t z Ki (secD K1 K2 R)) :
    ∃ a ∈ Ki, ∃ n ∈ oddCoreIn (secK0 t z), x = n * a := by
  obtain ⟨a, ha, n, hn, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun a ha b hb => hs.split.comm' hb (hKi ha)) hx.1
  exact ⟨a, ha, n, hn, hs.split.comm' hn (hKi ha)⟩

theorem oddCore_le [Finite G] (hs : Sec11dSet t z K1 K2 R) :
    oddCoreIn (secKD (secD K1 K2 R)) ≤ oddCoreIn (secK0 t z) :=
  hs.split.oddCore_le hs.KD_le fun e he q hq =>
    (Subgroup.mem_centralizer_iff.mp he.1 q hq).symm

end Sec11dSet

namespace Sec11dRho

variable {t z : G} {K1 K2 R Ki : Subgroup G} {ρ : ↥R →* MulAut ↥(K1 ⊔ K2)}

theorem Xi_lift [Finite G] (hρ : Sec11dRho t z K1 K2 R ρ) (hKi : Ki ≤ K1 ⊔ K2) {a : G}
    (ha : a ∈ Ki) :
    ∃ x ∈ secKiD t z Ki (secD K1 K2 R), ∃ n ∈ oddCoreIn (secK0 t z), x = n * a := by
  obtain ⟨k, hk, n, hn, hkn⟩ := hρ.lift ⟨a, hKi ha⟩
  refine ⟨k, ⟨?_, sec11c_oTwoRes_le _ hk⟩, n, hn, hkn⟩
  rw [hkn]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hn) (Subgroup.mem_sup_left ha)

def fixK2 (K1 K2 : Subgroup G) : Subgroup (MulAut ↥(K1 ⊔ K2)) where
  carrier := {φ | ∀ k : ↥(K1 ⊔ K2), (k : G) ∈ K2 → φ k = k}
  mul_mem' := by
    intro φ ψ hφ hψ k hk
    show φ (ψ k) = k
    rw [hψ k hk, hφ k hk]
  one_mem' := fun _ _ => rfl
  inv_mem' := by
    intro φ hφ k hk
    show φ.symm k = k
    calc φ.symm k = φ.symm (φ k) := by rw [hφ k hk]
      _ = k := φ.symm_apply_apply k

theorem commutator_le [Finite G] (hρ : Sec11dRho t z K1 K2 R ρ) (hs : Sec11dSet t z K1 K2 R)
    {x1 : ↥R} (hx1 : ∀ k : ↥(K1 ⊔ K2), (k : G) ∈ K2 → ρ x1 k = k) :
    ⁅zpowers (x1 : G), secKiD t z K2 (secD K1 K2 R)⁆ ≤ oddCoreIn (secKD (secD K1 K2 R)) := by
  rw [Subgroup.commutator_le]
  intro g1 hg1 g2 hg2
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg1
  set y : ↥R := x1 ^ m with hy
  have hyG : (y : G) = (x1 : G) ^ m := by simp [hy]
  have hρy : ρ y ∈ fixK2 K1 K2 := by
    rw [hy, map_zpow]
    exact Subgroup.zpow_mem _ (show ρ x1 ∈ fixK2 K1 K2 from hx1) m
  obtain ⟨a, ha, n, hn, hg2e⟩ := hs.Xi_decomp le_sup_right hg2
  have hg2K : g2 ∈ secKD (secD K1 K2 R) := hs.Xi_le_KD le_sup_right hg2
  obtain ⟨n', hn', hact⟩ := hρ.act y g2 n ⟨a, Subgroup.mem_sup_right ha⟩ hg2K hn hg2e
  have hfix : ((ρ y ⟨a, Subgroup.mem_sup_right ha⟩ : ↥(K1 ⊔ K2)) : G) = a :=
    congrArg Subtype.val (hρy ⟨a, Subgroup.mem_sup_right ha⟩ ha)
  rw [hfix] at hact
  have hcomm : (y : G) * g2 * (y : G)⁻¹ * g2⁻¹ = n' * n⁻¹ := by
    rw [hact, hg2e]
    group
  have h1 : (y : G) * g2 * (y : G)⁻¹ ∈ secKD (secD K1 K2 R) :=
    (Subgroup.mem_normalizer_iff.mp (hs.RN y.2) g2).mp hg2K
  have h2 : (y : G) * g2 * (y : G)⁻¹ * g2⁻¹ ∈ secKD (secD K1 K2 R) :=
    Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hg2K)
  rw [commutatorElement_def, ← hyG]
  refine hs.split.inf_le_oddCore hs.KD_le ⟨h2, ?_⟩
  rw [hcomm]
  exact Subgroup.mul_mem _ hn' (Subgroup.inv_mem _ hn)

theorem sq_comm_mem [Finite G] (hρ : Sec11dRho t z K1 K2 R ρ) (hs : Sec11dSet t z K1 K2 R)
    {x1 : ↥R} (hsq : ρ x1 * ρ x1 = 1) :
    ∀ y ∈ secKiD t z K1 (secD K1 K2 R),
      (x1 : G) * x1 * y * ((x1 : G) * x1)⁻¹ * y⁻¹ ∈ oddCoreIn (secKD (secD K1 K2 R)) := by
  intro y hy
  obtain ⟨a, ha, n, hn, hye⟩ := hs.Xi_decomp le_sup_left hy
  have hyK : y ∈ secKD (secD K1 K2 R) := hs.Xi_le_KD le_sup_left hy
  obtain ⟨n', hn', hact⟩ := hρ.act (x1 * x1) y n ⟨a, Subgroup.mem_sup_left ha⟩ hyK hn hye
  have h1 : ρ (x1 * x1) = 1 := by rw [map_mul]; exact hsq
  rw [h1] at hact
  have hcomm : ((x1 * x1 : ↥R) : G) * y * ((x1 * x1 : ↥R) : G)⁻¹ * y⁻¹ = n' * n⁻¹ := by
    rw [hact, hye]
    show n' * a * (n * a)⁻¹ = n' * n⁻¹
    group
  have h2 : ((x1 * x1 : ↥R) : G) * y * ((x1 * x1 : ↥R) : G)⁻¹ ∈ secKD (secD K1 K2 R) :=
    (Subgroup.mem_normalizer_iff.mp (hs.RN (x1 * x1).2) y).mp hyK
  have h3 : ((x1 * x1 : ↥R) : G) * y * ((x1 * x1 : ↥R) : G)⁻¹ * y⁻¹ ∈
      secKD (secD K1 K2 R) := Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hyK)
  show ((x1 * x1 : ↥R) : G) * y * ((x1 * x1 : ↥R) : G)⁻¹ * y⁻¹ ∈ _
  refine hs.split.inf_le_oddCore hs.KD_le ⟨h3, ?_⟩
  rw [hcomm]
  exact Subgroup.mul_mem _ hn' (Subgroup.inv_mem _ hn)

theorem isOuterOn [Finite G] (hρ : Sec11dRho t z K1 K2 R ρ) (hs : Sec11dSet t z K1 K2 R)
    {x1 : ↥R} (hψ1 : ∀ k : ↥(K1 ⊔ K2), (k : G) ∈ K1 → ((ρ x1 k : ↥(K1 ⊔ K2)) : G) ∈ K1)
    (hout : ¬ ∃ k : ↥(K1 ⊔ K2), (k : G) ∈ K1 ∧
      ∀ y : ↥(K1 ⊔ K2), (y : G) ∈ K1 → ((ρ x1 y : ↥(K1 ⊔ K2)) : G) = k * y * k⁻¹) :
    IsOuterOn (x1 : G) (secKiD t z K1 (secD K1 K2 R)) (oddCoreIn (secKD (secD K1 K2 R))) := by
  refine ⟨?_, ?_⟩
  · refine sec10A2_mem_normalizer_of_map_le fun x hx => ?_
    obtain ⟨a, ha, n, hn, hxe⟩ := hs.Xi_decomp le_sup_left hx
    have hxK : x ∈ secKD (secD K1 K2 R) := hs.Xi_le_KD le_sup_left hx
    obtain ⟨n', hn', hact⟩ := hρ.act x1 x n ⟨a, Subgroup.mem_sup_left ha⟩ hxK hn hxe
    have h1 : (x1 : G) * x * (x1 : G)⁻¹ ∈ secKD (secD K1 K2 R) :=
      (Subgroup.mem_normalizer_iff.mp (hs.RN x1.2) x).mp hxK
    refine ⟨?_, sec11c_oTwoRes_le _ h1⟩
    rw [hact]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hn')
      (Subgroup.mem_sup_left (hψ1 ⟨a, Subgroup.mem_sup_left ha⟩ ha))
  · rintro ⟨k, hk, hkprop⟩
    obtain ⟨κ, hκ, n0, hn0, hke⟩ := hs.Xi_decomp le_sup_left hk
    apply hout
    refine ⟨⟨κ, Subgroup.mem_sup_left hκ⟩, hκ, fun w hw => ?_⟩
    obtain ⟨y, hy, m, hm, hye⟩ := hρ.Xi_lift le_sup_left (a := (w : G)) hw
    have hyK : y ∈ secKD (secD K1 K2 R) := hs.Xi_le_KD le_sup_left hy
    obtain ⟨n', hn', hact⟩ := hρ.act x1 y m w hyK hm hye
    have hνN : (x1 : G) * y * (x1 : G)⁻¹ * (k * y * k⁻¹)⁻¹ ∈ oddCoreIn (secK0 t z) :=
      hs.oddCore_le (hkprop y hy)
    have hκK : κ ∈ K1 ⊔ K2 := Subgroup.mem_sup_left hκ
    have hκw : κ * (w : G) * κ⁻¹ ∈ K1 ⊔ K2 :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hκK w.2) (Subgroup.inv_mem _ hκK)
    have hkyk : k * y * k⁻¹ = (n0 * m * n0⁻¹) * (κ * (w : G) * κ⁻¹) := by
      have c1 : κ * m = m * κ := hs.split.comm' hm hκK
      have c2 : (κ * (w : G) * κ⁻¹) * n0⁻¹ = n0⁻¹ * (κ * (w : G) * κ⁻¹) :=
        hs.split.comm' (Subgroup.inv_mem _ hn0) hκw
      rw [hke, hye]
      calc n0 * κ * (m * (w : G)) * (n0 * κ)⁻¹ = n0 * (κ * m) * (w : G) * κ⁻¹ * n0⁻¹ := by
            group
        _ = n0 * (m * κ) * (w : G) * κ⁻¹ * n0⁻¹ := by rw [c1]
        _ = n0 * m * ((κ * (w : G) * κ⁻¹) * n0⁻¹) := by group
        _ = n0 * m * (n0⁻¹ * (κ * (w : G) * κ⁻¹)) := by rw [c2]
        _ = (n0 * m * n0⁻¹) * (κ * (w : G) * κ⁻¹) := by group
    have hkey : n' * ((ρ x1 w : ↥(K1 ⊔ K2)) : G) =
        ((x1 : G) * y * (x1 : G)⁻¹ * (k * y * k⁻¹)⁻¹ * (n0 * m * n0⁻¹)) * (κ * (w : G) * κ⁻¹) := by
      rw [← hact]
      calc (x1 : G) * y * (x1 : G)⁻¹
          = ((x1 : G) * y * (x1 : G)⁻¹ * (k * y * k⁻¹)⁻¹) * (k * y * k⁻¹) := by group
        _ = _ := by rw [hkyk]; group
    have hnm : (x1 : G) * y * (x1 : G)⁻¹ * (k * y * k⁻¹)⁻¹ * (n0 * m * n0⁻¹) ∈
        oddCoreIn (secK0 t z) :=
      Subgroup.mul_mem _ hνN
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hn0 hm) (Subgroup.inv_mem _ hn0))
    exact (hs.split.split.unique hn' hnm (ρ x1 w).2 hκw hkey).2

end Sec11dRho

end CFSG.OddStandard.SmallF3.Omega
