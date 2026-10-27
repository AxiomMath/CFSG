module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLemmaP
public import CFSG.GroupTheory.SteinbergBSFixedPointFree
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (thin_four_twentySix_commutator_eq_bot)

variable {W : Type} [CommGroup W] [Finite W]

theorem normalizer_zpowers_of_center {X Y : Subgroup (MulAut W)} {ω : MulAut W}
    (hcenter : ∀ z ∈ Subgroup.centralizer (X : Set (MulAut W)),
      (∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * z = z * c) →
        z ∈ Subgroup.zpowers ω)
    (hωC : ω ∈ Subgroup.centralizer (X : Set (MulAut W)))
    (hωcentral : ∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * ω = ω * c)
    (hY : Y ≤ Subgroup.normalizer (X : Set (MulAut W))) :
    Y ≤ Subgroup.normalizer (Subgroup.zpowers ω : Set (MulAut W)) := by
  have hconjC : ∀ a ∈ Y, a * ω * a⁻¹ ∈ Subgroup.zpowers ω := by
    intro a ha
    have hainv : a⁻¹ ∈ Y := Y.inv_mem ha
    have haXω : a * ω * a⁻¹ ∈ Subgroup.centralizer (X : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : a⁻¹ * x * a ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hY hainv) x).mp hx
      have hωx : (a⁻¹ * x * a) * ω = ω * (a⁻¹ * x * a) :=
        (Subgroup.mem_centralizer_iff.mp hωC) _ hx'
      calc x * (a * ω * a⁻¹) = a * ((a⁻¹ * x * a) * ω) * a⁻¹ := by group
        _ = a * (ω * (a⁻¹ * x * a)) * a⁻¹ := by rw [hωx]
        _ = (a * ω * a⁻¹) * x := by group
    have hacentral : ∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)),
        c * (a * ω * a⁻¹) = (a * ω * a⁻¹) * c := by
      intro c hc
      have hc' : a⁻¹ * c * a ∈ Subgroup.centralizer (X : Set (MulAut W)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hx' : a * x * a⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp (hY ha) x).mp hx
        calc x * (a⁻¹ * c * a) = a⁻¹ * ((a * x * a⁻¹) * c) * a := by group
          _ = a⁻¹ * (c * (a * x * a⁻¹)) * a := by
                rw [Subgroup.mem_centralizer_iff.mp hc _ hx']
          _ = (a⁻¹ * c * a) * x := by group
      have hcω : (a⁻¹ * c * a) * ω = ω * (a⁻¹ * c * a) := hωcentral _ hc'
      calc c * (a * ω * a⁻¹) = a * ((a⁻¹ * c * a) * ω) * a⁻¹ := by group
        _ = a * (ω * (a⁻¹ * c * a)) * a⁻¹ := by rw [hcω]
        _ = (a * ω * a⁻¹) * c := by group
    exact hcenter _ haXω hacentral
  have key : ∀ a ∈ Y, ∀ z ∈ Subgroup.zpowers ω, a * z * a⁻¹ ∈ Subgroup.zpowers ω := by
    intro a ha z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hconjC a ha) n
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  exact ⟨key y hy z, fun hz => by
      have h := key y⁻¹ (Y.inv_mem hy) (y * z * y⁻¹) hz
      rwa [show y⁻¹ * (y * z * y⁻¹) * (y⁻¹)⁻¹ = z by group] at h⟩

theorem gf4Linear_of_mem_aSet_two_of_omega (hW : ∀ w : W, w ^ 2 = 1)
    {X Y A : Subgroup (MulAut W)} {ω : MulAut W}
    (hcenter : ∀ z ∈ Subgroup.centralizer (X : Set (MulAut W)),
      (∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * z = z * c) →
        z ∈ Subgroup.zpowers ω)
    (hωC : ω ∈ Subgroup.centralizer (X : Set (MulAut W)))
    (hωcentral : ∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * ω = ω * c)
    (hω3 : orderOf ω = 3)
    (hY : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hA : A ∈ E3.aSet 2 Y) :
    A ≤ Subgroup.centralizer ({ω} : Set (MulAut W)) := by
  have hnorm := normalizer_zpowers_of_center hcenter hωC hωcentral hY
  have hodd : Odd (Nat.card ↥(Subgroup.zpowers ω)) := by
    rw [Nat.card_zpowers, hω3]
    norm_num
  have hAnorm : A ≤ Subgroup.normalizer (Subgroup.zpowers ω : Set (MulAut W)) :=
    hA.1.trans hnorm
  have hcomm := thin_four_twentySix_commutator_eq_bot hW hA hodd hAnorm
  rw [Subgroup.commutator_comm] at hcomm
  have hle : A ≤ Subgroup.centralizer (Subgroup.zpowers ω : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact hle.trans (Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers ω)))

theorem even_mQuot_of_gf4 {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {ω : MulAut V} (hω3 : ω ^ 3 = 1) (hfree : ∀ v : V, ω v = v → v = 1)
    (W U : Subgroup V) (hUW : U ≤ W)
    (hWω : W.map ω.toMonoidHom = W) (hUω : U.map ω.toMonoidHom = U) :
    Even (E3.mQuot W U) := by
  have hW2 : ∀ w : W, w * w = 1 := fun w => Subtype.ext (by simpa [pow_two] using hV (w : V))
  have hU2 : ∀ u : U, u * u = 1 := fun u => Subtype.ext (by simpa [pow_two] using hV (u : V))
  let zW : MulAut W := CFSG.GroupTheory.SteinbergBS.invariantRestrict ω W hWω
  let zU : MulAut U := CFSG.GroupTheory.SteinbergBS.invariantRestrict ω U hUω
  have hzW3 : zW ^ 3 = 1 := by
    ext w
    change (((CFSG.GroupTheory.SteinbergBS.invariantRestrict ω W hWω) ^ 3) w : V) =
      ((1 : MulAut W) w : V)
    rw [CFSG.GroupTheory.SteinbergBS.coe_invariantRestrict_pow]
    simpa using congrArg (fun f : MulAut V => f (w : V)) hω3
  have hzU3 : zU ^ 3 = 1 := by
    ext u
    change (((CFSG.GroupTheory.SteinbergBS.invariantRestrict ω U hUω) ^ 3) u : V) =
      ((1 : MulAut U) u : V)
    rw [CFSG.GroupTheory.SteinbergBS.coe_invariantRestrict_pow]
    simpa using congrArg (fun f : MulAut V => f (u : V)) hω3
  have hzWfpf : ∀ w : W, zW w = w → w = 1 := by
    intro w hw
    apply Subtype.ext
    have h1 : (zW w : V) = (w : V) := congrArg Subtype.val hw
    rw [show ((zW : MulAut W) w : V) = ω (w : V) from by
      change ((CFSG.GroupTheory.SteinbergBS.invariantRestrict ω W hWω) w : V) = ω (w : V)
      rw [show CFSG.GroupTheory.SteinbergBS.invariantRestrict ω W hWω =
        CFSG.GroupTheory.SteinbergBS.invariantRestrict ω W hWω ^ 1 from (pow_one _).symm,
        CFSG.GroupTheory.SteinbergBS.coe_invariantRestrict_pow]
      rfl] at h1
    exact hfree _ h1
  have hzUfpf : ∀ u : U, zU u = u → u = 1 := by
    intro u hu
    apply Subtype.ext
    have h1 : (zU u : V) = (u : V) := congrArg Subtype.val hu
    rw [show ((zU : MulAut U) u : V) = ω (u : V) from by
      change ((CFSG.GroupTheory.SteinbergBS.invariantRestrict ω U hUω) u : V) = ω (u : V)
      rw [show CFSG.GroupTheory.SteinbergBS.invariantRestrict ω U hUω =
        CFSG.GroupTheory.SteinbergBS.invariantRestrict ω U hUω ^ 1 from (pow_one _).symm,
        CFSG.GroupTheory.SteinbergBS.coe_invariantRestrict_pow]
      rfl] at h1
    exact hfree _ h1
  obtain ⟨aW, hWcard⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.exists_card_eq_four_pow hW2 hzW3 hzWfpf
  obtain ⟨aU, hUcard⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.exists_card_eq_four_pow hU2 hzU3 hzUfpf
  have hcardle : Nat.card U ≤ Nat.card W := Nat.card_mono (Set.toFinite _) hUW
  have hle : aU ≤ aW := by
    by_contra h
    have hlt : aW < aU := by omega
    have hpow : 4 ^ aW < 4 ^ aU := Nat.pow_lt_pow_right (by norm_num) hlt
    omega
  have hrel : U.relIndex W = 4 ^ (aW - aU) := by
    have hmul := Subgroup.relIndex_mul_card (H := U) (K := W)
    rw [inf_eq_left.mpr hUW, hWcard, hUcard] at hmul
    have h4eq : (4 : ℕ) ^ aW = 4 ^ aU * 4 ^ (aW - aU) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    rw [h4eq, mul_comm (U.relIndex W) (4 ^ aU)] at hmul
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : (0 : ℕ) < 4) aU) hmul
  unfold E3.mQuot
  rw [hrel]
  have h4 : 4 ^ (aW - aU) = 2 ^ (2 * (aW - aU)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [h4, padicValNat.prime_pow]
  exact even_two_mul _

theorem even_mQuot_fixV_of_gf4 (hW : ∀ w : W, w ^ 2 = 1) {ω : MulAut W}
    (hω3 : ω ^ 3 = 1) (hfree : ∀ v : W, ω v = v → v = 1)
    (M : Subgroup W) (hMω : M.map ω.toMonoidHom = M) (A : Subgroup (MulAut W))
    (hAω : ∀ a ∈ A, a * ω = ω * a) :
    Even (E3.mQuot M (M ⊓ fixV A)) := by
  have hstab : (M ⊓ fixV A).map ω.toMonoidHom ≤ M ⊓ fixV A := by
    rintro x ⟨u, hu, rfl⟩
    obtain ⟨huM, huA⟩ := Subgroup.mem_inf.1 hu
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have : ω u ∈ M.map ω.toMonoidHom := Subgroup.mem_map_of_mem _ huM
      rwa [hMω] at this
    · change u ∈ fixV A at huA
      change ω u ∈ fixV A
      rw [mem_fixV] at huA ⊢
      intro a ha
      have hcomm : a (ω u) = ω (a u) := by
        have h1 := congrArg (fun f : MulAut W => f u) (hAω a ha)
        simpa only [MulAut.mul_apply] using h1
      change a (ω u) = ω u
      rw [hcomm, huA a ha]
  have hfixω : (M ⊓ fixV A).map ω.toMonoidHom = M ⊓ fixV A :=
    Subgroup.eq_of_le_of_card_ge hstab (le_of_eq
      (Subgroup.card_map_of_injective (MulEquiv.injective ω)).symm)
  exact even_mQuot_of_gf4 (hV := hW) (ω := ω) hω3 hfree M (M ⊓ fixV A)
    inf_le_left hMω hfixω

end CFSG.GroupTheory
