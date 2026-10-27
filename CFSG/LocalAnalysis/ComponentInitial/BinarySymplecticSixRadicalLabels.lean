module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullCosetMiddleSubgroup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits
open LinearMap (BilinForm)

variable {G : Type*} [Group G]

@[expose] def zPow (z : G) (ε : ZMod 2) : G :=
  z ^ ε.val

theorem zPow_zero (z : G) : zPow z 0 = 1 :=
  pow_zero z

theorem zPow_one (z : G) : zPow z 1 = z :=
  pow_one z

theorem zPow_add {z : G} (hz : orderOf z = 2) (ε ε' : ZMod 2) :
    zPow z (ε + ε') = zPow z ε * zPow z ε' := by
  rw [zPow, zPow, zPow, ← pow_add, ← pow_mod_orderOf z (ε.val + ε'.val), hz, ← ZMod.val_add]

theorem zPow_mem (z : G) (ε : ZMod 2) : zPow z ε ∈ zpowers z :=
  pow_mem (mem_zpowers z) _

theorem zPow_eq_one_iff {z : G} (hz : orderOf z = 2) {ε : ZMod 2} : zPow z ε = 1 ↔ ε = 0 := by
  constructor
  · intro h
    have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases key ε with rfl | rfl
    · rfl
    · rw [zPow_one] at h
      rw [h, orderOf_one] at hz
      exact absurd hz (by norm_num)
  · rintro rfl
    exact zPow_zero z

theorem mem_conjClass_iff_right {M : Subgroup G} {z x : G} :
    x ∈ conjClass M z ↔ ∃ m ∈ M, m⁻¹ * z * m = x := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m⁻¹, M.inv_mem hm, by rw [inv_inv]⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m⁻¹, M.inv_mem hm, by rw [inv_inv]⟩

theorem conj_mem_conjClass_right {M : Subgroup G} {z x m : G} (hm : m ∈ M)
    (hx : x ∈ conjClass M z) : m⁻¹ * x * m ∈ conjClass M z := by
  have h := conj_mem_conjClass (M.inv_mem hm) hx
  rwa [inv_inv] at h

variable {L : Subgroup G}
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
variable (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) {z : G} (hzC : z ∈ centralizer (L : Set G))
  (hz : orderOf z = 2)

include hzC in
theorem mul_comm_z {a : G} (ha : a ∈ L) : a * z = z * a :=
  mem_centralizer_iff.1 hzC a ha

include hzC in
theorem mul_comm_zPow {a : G} (ha : a ∈ L) (ε : ZMod 2) : a * zPow z ε = zPow z ε * a :=
  ((Commute.pow_right (mul_comm_z hzC ha) ε.val))

@[expose] def radHom : Multiplicative (↥(binarySymMatrices 3) × ZMod 2) →* G where
  toFun x := tauHom φ he (Multiplicative.ofAdd (Multiplicative.toAdd x).1) *
    zPow z (Multiplicative.toAdd x).2
  map_one' := by
    rw [toAdd_one, Prod.fst_zero, Prod.snd_zero, ofAdd_zero, map_one, zPow_zero, mul_one]
  map_mul' x y := by
    rw [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul, zPow_add hz]
    have h := mul_comm_zPow hzC (tauHom_mem φ he (Multiplicative.ofAdd
      (Multiplicative.toAdd y).1)) (Multiplicative.toAdd x).2
    calc tauHom φ he (Multiplicative.ofAdd (Multiplicative.toAdd x).1) *
          tauHom φ he (Multiplicative.ofAdd (Multiplicative.toAdd y).1) *
          (zPow z (Multiplicative.toAdd x).2 * zPow z (Multiplicative.toAdd y).2) =
        tauHom φ he (Multiplicative.ofAdd (Multiplicative.toAdd x).1) *
          (tauHom φ he (Multiplicative.ofAdd (Multiplicative.toAdd y).1) *
            zPow z (Multiplicative.toAdd x).2) * zPow z (Multiplicative.toAdd y).2 := by group
      _ = _ := by rw [h]; group

theorem radHom_apply (B : ↥(binarySymMatrices 3)) (ε : ZMod 2) :
    radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) =
      tauHom φ he (Multiplicative.ofAdd B) * zPow z ε :=
  rfl

theorem radHom_tau (B : ↥(binarySymMatrices 3)) :
    radHom φ he hzC hz (Multiplicative.ofAdd (B, 0)) = tauHom φ he (Multiplicative.ofAdd B) := by
  rw [radHom_apply, zPow_zero, mul_one]

theorem radHom_z : radHom φ he hzC hz (Multiplicative.ofAdd (0, 1)) = z := by
  rw [radHom_apply, ofAdd_zero, map_one, zPow_one, one_mul]

variable (z) in
abbrev radSub (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) : Subgroup G :=
  pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔ zpowers z

include hzC hz in
theorem mem_radSub_iff {x : G} :
    x ∈ radSub φ z e ↔ ∃ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      tauHom φ he (Multiplicative.ofAdd B) * zPow z ε = x := by
  constructor
  · intro hx
    obtain ⟨a, ha, s, hs, rfl⟩ := (mem_sup_of_le_centralizer
      (zpowers_le_centralizer_pullSub φ hzC _)).1 hx
    obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    rcases eq_one_or_eq_of_mem_zpowers hz hs with rfl | rfl
    · exact ⟨Multiplicative.toAdd B, 0, by rw [ofAdd_toAdd, zPow_zero]⟩
    · exact ⟨Multiplicative.toAdd B, 1, by rw [ofAdd_toAdd, zPow_one]⟩
  · rintro ⟨B, ε, rfl⟩
    exact mul_mem (mem_sup_left ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩))
      (mem_sup_right (zPow_mem z ε))

theorem range_radHom : (radHom φ he hzC hz).range = radSub φ z e := by
  ext x
  rw [MonoidHom.mem_range, mem_radSub_iff φ he hzC hz]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, _, rfl⟩
  · rintro ⟨B, ε, rfl⟩
    exact ⟨Multiplicative.ofAdd (B, ε), rfl⟩

theorem radHom_injective (hinf : L ⊓ zpowers z = ⊥) : Function.Injective (radHom φ he hzC hz) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨⟨B, ε⟩, rfl⟩ : ∃ y, Multiplicative.ofAdd y = x := ⟨Multiplicative.toAdd x, rfl⟩
  rw [radHom_apply] at hx
  have hzε : zPow z ε ∈ L ⊓ zpowers z := by
    refine mem_inf.2 ⟨?_, zPow_mem z ε⟩
    have h1 : zPow z ε = (tauHom φ he (Multiplicative.ofAdd B))⁻¹ := eq_inv_of_mul_eq_one_right hx
    rw [h1]
    exact L.inv_mem (tauHom_mem φ he _)
  rw [hinf, mem_bot] at hzε
  rw [hzε, mul_one, ← map_one (tauHom φ he)] at hx
  have hB := tauHom_injective φ he hx
  rw [(zPow_eq_one_iff hz).1 hzε]
  rw [← ofAdd_zero] at hB
  rw [Multiplicative.ofAdd.injective hB]
  rfl

@[expose] def radLabel (hinf : L ⊓ zpowers z = ⊥) :
    radSub φ z e ≃* Multiplicative (↥(binarySymMatrices 3) × ZMod 2) :=
  ((MonoidHom.ofInjective (radHom_injective φ he hzC hz hinf)).trans
    (MulEquiv.subgroupCongr (range_radHom φ he hzC hz))).symm

theorem coe_radLabel_symm (hinf : L ⊓ zpowers z = ⊥)
    (x : Multiplicative (↥(binarySymMatrices 3) × ZMod 2)) :
    ((radLabel φ he hzC hz hinf).symm x : G) = radHom φ he hzC hz x :=
  rfl

@[expose] def radLabelOf (hinf : L ⊓ zpowers z = ⊥) {M : Subgroup G} (hRM : radSub φ z e ≤ M) :
    (radSub φ z e).subgroupOf M ≃* Multiplicative (↥(binarySymMatrices 3) × ZMod 2) :=
  (subgroupOfEquivOfLe hRM).trans (radLabel φ he hzC hz hinf)

include hzC in
theorem conj_radHom_of_congr {n : G} (hnz : n * z = z * n) (D : GL (Fin 3) (ZMod 2))
    (hn : ∀ B : ↥(binarySymMatrices 3), n * tauHom φ he (Multiplicative.ofAdd B) * n⁻¹ =
      tauHom φ he (Multiplicative.ofAdd (symThreeCongr D B)))
    (B : ↥(binarySymMatrices 3)) (ε : ZMod 2) :
    n * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * n⁻¹ =
      radHom φ he hzC hz (Multiplicative.ofAdd (symThreeCongr D B, ε)) := by
  have hzε : n * zPow z ε * n⁻¹ = zPow z ε := by
    rw [zPow, mul_inv_eq_iff_eq_mul, (Commute.pow_right hnz ε.val).eq]
  rw [radHom_apply, radHom_apply, ← hn B]
  calc n * (tauHom φ he (Multiplicative.ofAdd B) * zPow z ε) * n⁻¹ =
      (n * tauHom φ he (Multiplicative.ofAdd B) * n⁻¹) * (n * zPow z ε * n⁻¹) := by group
    _ = _ := by rw [hzε]

include he in
theorem eq_tauHom_of_toMatrix {a : G} (ha : a ∈ L) (B : ↥(binarySymMatrices 3))
    (hB : LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) =
      fromBlocks 1 (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1) :
    a = tauHom φ he (Multiplicative.ofAdd B) := by
  have hmem : a ∈ tauSet φ e (fun B' => B' = (B : Matrix (Fin 3) (Fin 3) (ZMod 2))) :=
    ⟨ha, B, B.2, rfl, hB⟩
  obtain ⟨B', hB', hB'a⟩ := (mem_tauSet_iff φ he).1 hmem
  rw [← hB'a]
  congr 1
  exact Multiplicative.toAdd.injective (Subtype.ext hB')

include he in
theorem conj_tauHom_of_sigma {N₀ : Subgroup G} (σ : N₀ →* GL (Fin 3) (ZMod 2))
    (hσ : ∀ (n : N₀) (a : G) (ha : a ∈ L) (B : Matrix (Fin 3) (Fin 3) (ZMod 2)), Bᵀ = B →
      LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
      ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
        LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
          fromBlocks 1 ((σ n : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B *
            (σ n : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) 0 1)
    (n : N₀) (B : ↥(binarySymMatrices 3)) :
    (n : G) * tauHom φ he (Multiplicative.ofAdd B) * (n : G)⁻¹ =
      tauHom φ he (Multiplicative.ofAdd (symThreeCongr (σ n) B)) := by
  obtain ⟨h, hmat⟩ := hσ n _ (tauHom_mem φ he (Multiplicative.ofAdd B)) B B.2
    (toMatrix_tauHom φ he _)
  exact eq_tauHom_of_toMatrix φ he h _ hmat

include he in
theorem conj_radHom_of_sigma {N₀ : Subgroup G} (hN₀ : N₀ ≤ centralizer ({z} : Set G))
    (σ : N₀ →* GL (Fin 3) (ZMod 2))
    (hσ : ∀ (n : N₀) (a : G) (ha : a ∈ L) (B : Matrix (Fin 3) (Fin 3) (ZMod 2)), Bᵀ = B →
      LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
      ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
        LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
          fromBlocks 1 ((σ n : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B *
            (σ n : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) 0 1)
    (n : N₀) (B : ↥(binarySymMatrices 3)) (ε : ZMod 2) :
    (n : G) * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * (n : G)⁻¹ =
      radHom φ he hzC hz (Multiplicative.ofAdd (symThreeCongr (σ n) B, ε)) :=
  conj_radHom_of_congr φ he hzC hz (mem_centralizer_singleton_iff.1 (hN₀ n.2)) (σ n)
    (conj_tauHom_of_sigma φ he σ hσ n) B ε

theorem leviHom_conj_tauHom' (D : GL (Fin 3) (ZMod 2)) (B : ↥(binarySymMatrices 3)) :
    leviHom φ he D * tauHom φ he (Multiplicative.ofAdd B) * (leviHom φ he D)⁻¹ =
      tauHom φ he (Multiplicative.ofAdd (symThreeCongr D B)) := by
  rw [leviHom_conj_tauHom]
  rfl

include hzC in
theorem leviHom_mul_z (D : GL (Fin 3) (ZMod 2)) : leviHom φ he D * z = z * leviHom φ he D :=
  mul_comm_z hzC (leviHom_mem φ he D)

theorem leviHom_conj_radHom (D : GL (Fin 3) (ZMod 2)) (B : ↥(binarySymMatrices 3))
    (ε : ZMod 2) :
    leviHom φ he D * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * (leviHom φ he D)⁻¹ =
      radHom φ he hzC hz (Multiplicative.ofAdd (symThreeCongr D B, ε)) :=
  conj_radHom_of_congr φ he hzC hz (leviHom_mul_z φ he hzC D) D (leviHom_conj_tauHom' φ he D) B ε

theorem leviHom_inv_conj_radHom (D : GL (Fin 3) (ZMod 2)) (B : ↥(binarySymMatrices 3))
    (ε : ZMod 2) :
    (leviHom φ he D)⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * leviHom φ he D =
      radHom φ he hzC hz (Multiplicative.ofAdd (symThreeCongr D⁻¹ B, ε)) := by
  have h := leviHom_conj_radHom φ he hzC hz D⁻¹ B ε
  rwa [map_inv, inv_inv] at h

include hzC hz in
theorem leviHom_mem_normalizer_radSub (D : GL (Fin 3) (ZMod 2)) :
    leviHom φ he D ∈ normalizer (radSub φ z e : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨B, ε, rfl⟩ := (mem_radSub_iff φ he hzC hz).1 hx
    rw [← radHom_apply φ he hzC hz, leviHom_conj_radHom, radHom_apply]
    exact (mem_radSub_iff φ he hzC hz).2 ⟨_, _, rfl⟩
  · intro hx
    obtain ⟨B, ε, hBε⟩ := (mem_radSub_iff φ he hzC hz).1 hx
    have h1 : x = (leviHom φ he D)⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) *
        leviHom φ he D := by
      rw [radHom_apply, hBε]
      group
    rw [h1, leviHom_inv_conj_radHom, radHom_apply]
    exact (mem_radSub_iff φ he hzC hz).2 ⟨_, _, rfl⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels
