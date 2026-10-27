module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOMod
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYGrp
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam
open CFSG.ClassicalInvolution.Q3.AE

theorem triple_comm_aux {G : Type*} [Group G] {u e a b : G} (hu : u * u = 1) (hue : u * e = e * u)
    (hua : u * a = a * u) (hub : u * b = b * u) : u * e * (u * a) * (u * b) = u * (e * a * b) := by
  calc u * e * (u * a) * (u * b) = u * (e * u) * a * (u * b) := by group
    _ = u * (u * e) * a * (u * b) := by rw [← hue]
    _ = (u * u) * e * a * (u * b) := by group
    _ = e * a * (u * b) := by rw [hu, one_mul]
    _ = e * (a * u) * b := by group
    _ = e * (u * a) * b := by rw [← hua]
    _ = (e * u) * a * b := by group
    _ = (u * e) * a * b := by rw [← hue]
    _ = u * (e * a * b) := by group

section Cert


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem exists_y_rel (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5) :
    ∃ y : Y, y * u = u * y ∧ y * t = t * y ∧ (∃ a : ℕ, y ^ 3 ^ a = 1) ∧
      (∀ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), y * e * y⁻¹ ≠ o * e * o⁻¹) ∧
      ∃ m : Y, (∃ N : ℕ, Odd N ∧ m ^ N = 1) ∧ m * u = u * m ∧
        (e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) = t * m ∨
          e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) = u * t * m) := by
  classical
  obtain ⟨x, vH, v', ψ, p, ι, hvx, hxx, hvH, hzv, hvH2, hψinj, hrange, hψx, hιr, hψv⟩ :=
    AY.frame_psi hc hA5
  obtain ⟨w, hwA, hw3, hwv, hwx, hwxc, hwprod⟩ := exists_three_elt_prod hιr
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) u) with hN
  have hNodd : Odd (Nat.card N) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull (Om R) u)
  obtain ⟨q, hq⟩ := hrange (mkQ 5 w) (Subgroup.mem_map_of_mem _ hwA)
  have hq3 : q ^ 3 = 1 := hψinj (by rw [map_pow, hq, hw3, map_one])
  have hqv : q * (QuotientGroup.mk vH : ↥(coreHull (Om R) u) ⧸ N) =
      QuotientGroup.mk vH * q :=
    hψinj (by rw [map_mul, map_mul, hq, hψv]; exact hwv)
  have hqx : q * (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) ≠ QuotientGroup.mk x * q := by
    intro h
    apply hwx
    have := congrArg ψ h
    rwa [map_mul, map_mul, hq, hψx] at this
  have hqxc : (q * (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) * q⁻¹) * QuotientGroup.mk x =
      QuotientGroup.mk x * (q * QuotientGroup.mk x * q⁻¹) := by
    apply hψinj
    simp only [map_mul, map_inv, hq]
    rw [hψx]
    exact hwxc
  have hxq : (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) * QuotientGroup.mk x = 1 := by
    rw [← QuotientGroup.mk_mul, hxx, QuotientGroup.mk_one]
  have hprodq : (QuotientGroup.mk x : ↥(coreHull (Om R) u) ⧸ N) * (q * QuotientGroup.mk x * q⁻¹) *
      (q ^ 2 * QuotientGroup.mk x * (q ^ 2)⁻¹) = QuotientGroup.mk vH := by
    apply hψinj
    simp only [map_mul, map_inv, map_pow, hq]
    rw [hψx, hψv]
    exact hwprod
  obtain ⟨y₁, hy₁q, hy₁v, a, hy₁a⟩ := AY.exists_pow_three_lift hNodd hvH2 hq3 hqv
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  obtain ⟨y, hy⟩ : ∃ y : Y, y = hcoeHom (Om R) u y₁ := ⟨_, rfl⟩
  have hyu : y * u = u * y := by
    rw [hy]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcoeHom_mem_centralizer (Om R) u y₁)
  have hyv : y * v' = v' * y := by
    rw [← hvH, hy, ← map_mul, ← map_mul, hy₁v]
  have hyt : y * t = t * y := by
    rcases hzv with ht | ht
    · rw [ht]; exact hyv
    · rw [ht]
      calc y * (u * v') = (y * u) * v' := by group
        _ = (u * y) * v' := by rw [hyu]
        _ = u * (y * v') := by group
        _ = u * (v' * y) := by rw [hyv]
        _ = (u * v') * y := by group
  have hy3 : y ^ 3 ^ a = 1 := by rw [hy, ← map_pow, hy₁a, map_one]
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hue : u * e = e * u := hWab _ hd.huW _ heW
  have het : e * t = t * e := hWab _ heW _ hd.hzW
  have heC : e ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr het
  have heO : ∀ g ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)),
      e * g * e⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp (Sec7.le_normalizer_oddCoreOf _ heC) g).mp hg
  have hPH : (QuotientGroup.mk (x * (y₁ * x * y₁⁻¹) * (y₁ ^ 2 * x * (y₁ ^ 2)⁻¹)) :
      ↥(coreHull (Om R) u) ⧸ N) = QuotientGroup.mk vH := by
    rw [← hprodq, ← hy₁q]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
    rfl
  obtain ⟨nH, hnH⟩ : ∃ nH : ↥(coreHull (Om R) u),
      nH = vH⁻¹ * (x * (y₁ * x * y₁⁻¹) * (y₁ ^ 2 * x * (y₁ ^ 2)⁻¹)) := ⟨_, rfl⟩
  have hnN : nH ∈ N := by
    rw [hnH]
    exact QuotientGroup.eq.mp hPH.symm
  obtain ⟨m, hm⟩ : ∃ m : Y, m = hcoeHom (Om R) u nH := ⟨_, rfl⟩
  have hmu : m * u = u * m := by
    rw [hm]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcoeHom_mem_centralizer (Om R) u nH)
  have hmN : m ^ Nat.card N = 1 := by
    have h1 : nH ^ Nat.card N = 1 := by
      have := pow_card_eq_one' (G := ↥N) (x := ⟨nH, hnN⟩)
      exact congrArg Subtype.val this
    rw [hm, ← map_pow, h1, map_one]
  have hP : (u * e) * (y * (u * e) * y⁻¹) * (y ^ 2 * (u * e) * (y ^ 2)⁻¹) = v' * m := by
    have h1 : vH * nH = x * (y₁ * x * y₁⁻¹) * (y₁ ^ 2 * x * (y₁ ^ 2)⁻¹) := by rw [hnH]; group
    have h2 := congrArg (hcoeHom (Om R) u) h1
    simp only [map_mul, map_inv, map_pow, hvx, hvH] at h2
    rw [hm, hy]
    exact h2.symm
  have hyu' : y * u * y⁻¹ = u := by rw [hyu]; group
  have hy2u : y ^ 2 * u * (y ^ 2)⁻¹ = u := by
    have h : y ^ 2 * u = u * y ^ 2 := (Commute.pow_left (show Commute y u from hyu) 2).eq
    rw [h]; group
  have hue1 : u * (y * e * y⁻¹) = (y * e * y⁻¹) * u := by
    calc u * (y * e * y⁻¹) = (y * u * y⁻¹) * (y * e * y⁻¹) := by rw [hyu']
      _ = y * (u * e) * y⁻¹ := by group
      _ = y * (e * u) * y⁻¹ := by rw [hue]
      _ = (y * e * y⁻¹) * (y * u * y⁻¹) := by group
      _ = (y * e * y⁻¹) * u := by rw [hyu']
  have hue2 : u * (y ^ 2 * e * (y ^ 2)⁻¹) = (y ^ 2 * e * (y ^ 2)⁻¹) * u := by
    calc u * (y ^ 2 * e * (y ^ 2)⁻¹) = (y ^ 2 * u * (y ^ 2)⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) := by rw [hy2u]
      _ = y ^ 2 * (u * e) * (y ^ 2)⁻¹ := by group
      _ = y ^ 2 * (e * u) * (y ^ 2)⁻¹ := by rw [hue]
      _ = (y ^ 2 * e * (y ^ 2)⁻¹) * (y ^ 2 * u * (y ^ 2)⁻¹) := by group
      _ = (y ^ 2 * e * (y ^ 2)⁻¹) * u := by rw [hy2u]
  have hP' : (u * e) * (y * (u * e) * y⁻¹) * (y ^ 2 * (u * e) * (y ^ 2)⁻¹) =
      u * (e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹)) := by
    have h1 : y * (u * e) * y⁻¹ = u * (y * e * y⁻¹) := by
      calc y * (u * e) * y⁻¹ = (y * u * y⁻¹) * (y * e * y⁻¹) := by group
        _ = u * (y * e * y⁻¹) := by rw [hyu']
    have h2 : y ^ 2 * (u * e) * (y ^ 2)⁻¹ = u * (y ^ 2 * e * (y ^ 2)⁻¹) := by
      calc y ^ 2 * (u * e) * (y ^ 2)⁻¹ = (y ^ 2 * u * (y ^ 2)⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) := by group
        _ = u * (y ^ 2 * e * (y ^ 2)⁻¹) := by rw [hy2u]
    rw [h1, h2]
    exact triple_comm_aux hd.hu2 hue hue1 hue2
  obtain ⟨X, hX⟩ : ∃ X : Y, X = e * (y * e * y⁻¹) * (y ^ 2 * e * (y ^ 2)⁻¹) := ⟨_, rfl⟩
  have hX1 : u * X = v' * m := by rw [hX, ← hP', hP]
  have hX2 : X = u * (v' * m) := by
    calc X = (u * u) * X := by rw [hd.hu2, one_mul]
      _ = u * (u * X) := mul_assoc _ _ _
      _ = u * (v' * m) := by rw [hX1]
  refine ⟨y, hyu, hyt, ⟨a, hy3⟩, ?_, m, ⟨Nat.card N, hNodd, hmN⟩, hmu, ?_⟩
  · intro o ho hyo
    have hpow := AY.commutator_pow_card hyu heO ho hyo
    rw [hy] at hpow
    have hpow' : (y₁ * x * y₁⁻¹ * x⁻¹) ^ Nat.card ↥(oddCoreOf (Subgroup.centralizer ({t} : Set Y))) =
        1 := by
      apply hcoeHom_injective (Om R) u
      rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_inv, hvx, map_one]
      exact hpow
    have hq' := congrArg (QuotientGroup.mk' N) hpow'
    simp only [map_pow, map_mul, map_inv, QuotientGroup.mk'_apply, hy₁q] at hq'
    exact AY.commutator_pow_ne_one hxq hqx hqxc (oddCoreOf_odd_natCard _) hq'
  · rcases hzv with ht | ht
    · right
      rw [← hX, hX2, ht]
      group
    · left
      rw [← hX, hX2, ht]
      group

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
