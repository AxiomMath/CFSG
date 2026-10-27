module

public import CFSG.HardMathSupport.Timmesfeld.DFour.OddRank4
public import CFSG.RankThree.Classical.OrthogonalOrderThree
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSULift
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem

open Matrix CFSG.Open CFSG.SectionRank.ClassicalEven

section Swap

variable {n : ℕ} {K : Type} [Field K]

theorem permGL_swap_apply_self (i j : Fin n) :
    ((CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i j = 1 := by
  rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Equiv.swap_inv]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem permGL_swap_mem_statedSU (h2 : (2 : K) = 0) {q : ℕ} (hq : q ≠ 0) (i j : Fin n) :
    CFSG.RankThree.Classical.permGL (Equiv.swap i j) ∈ StatedSU n q K := by
  set τ : Equiv.Perm (Fin n) := (Equiv.swap i j)⁻¹ with hτ
  have hP : ((CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = τ.permMatrix K := by
    rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply]
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [hP, Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
    · rw [h]
      simp
    · rw [h]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      linear_combination (-1 : K) * h2
  · have hmap : (τ.permMatrix K).map (· ^ q) = τ.permMatrix K := by
      ext a b
      simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      split_ifs <;> simp [zero_pow hq]
    rw [hP, hmap, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one]

theorem eq_of_commute_permGL_swap {d : Fin n → Kˣ} {i j : Fin n}
    (h : CFSG.RankThree.Classical.permGL (Equiv.swap i j) * torusDiag d =
      torusDiag d * CFSG.RankThree.Classical.permGL (Equiv.swap i j)) : d i = d j := by
  have h1 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j) h
  simp only [Units.val_mul, coe_torusDiag, Matrix.mul_diagonal, Matrix.diagonal_mul,
    permGL_swap_apply_self, one_mul, mul_one] at h1
  exact Units.ext h1.symm

theorem eq_of_mem_center_statedSU (h2 : (2 : K) = 0) {q : ℕ} (hq : q ≠ 0)
    {g : StatedSU n q K} (hg : g ∈ Subgroup.center (StatedSU n q K)) {d : Fin n → Kˣ}
    (hgd : (g : GL (Fin n) K) = torusDiag d) (i j : Fin n) : d i = d j := by
  have hc := Subgroup.mem_center_iff.1 hg ⟨_, permGL_swap_mem_statedSU h2 hq i j⟩
  have hc' := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul] at hc'
  rw [hgd] at hc'
  exact eq_of_commute_permGL_swap hc'

end Swap

section Four

variable {K : Type} [Field K] [Finite K]

theorem four_le_pRank_of_statedSU_hom (hK : Nat.card K = 4) {n : ℕ} (hn : 5 ≤ n) {W : Type*}
    [Group W] [Finite W] (β : StatedSU n (2 ^ 1) K →* W)
    (hβ : β.ker ≤ Subgroup.center (StatedSU n (2 ^ 1) K)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup W) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hcard])
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    norm_num at hζ
  have hq : (2 ^ 1 : ℕ) ≠ 0 := by norm_num
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, by omega⟩
  set i₃ : Fin n := ⟨3, by omega⟩
  set i₄ : Fin n := ⟨4, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂]
  have h03 : i₀ ≠ i₃ := by simp [i₀, i₃]
  have h04 : i₀ ≠ i₄ := by simp [i₀, i₄]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂]
  have h13 : i₁ ≠ i₃ := by simp [i₁, i₃]
  have h14 : i₁ ≠ i₄ := by simp [i₁, i₄]
  have h23 : i₂ ≠ i₃ := by simp [i₂, i₃]
  have h24 : i₂ ≠ i₄ := by simp [i₂, i₄]
  have h34 : i₃ ≠ i₄ := by simp [i₃, i₄]
  have hmem : ∀ j : Fin n, torusDiag (torusVec ζ j i₄) ∈ StatedSU n (2 ^ 1) K := fun j =>
    torusDiag_mem_SU hq (prod_torusVec ζ j i₄)
      (by rw [torusVec_pow, show (2 ^ 1 + 1 : ℕ) = 3 by norm_num, hζ3, torusVec_one])
  set t : Fin n → StatedSU n (2 ^ 1) K := fun j => ⟨torusDiag (torusVec ζ j i₄), hmem j⟩
  have ht : ∀ j, ((t j : StatedSU n (2 ^ 1) K) : GL (Fin n) K) = torusDiag (torusVec ζ j i₄) :=
    fun j => rfl
  have hpow3 : ∀ j, β (t j) ^ 3 = 1 := fun j => by
    rw [← map_pow]
    have : t j ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, ht, ← map_pow, torusVec_pow, hζ3, torusVec_one, map_one,
        OneMemClass.coe_one])
    rw [this, map_one]
  have hcomm : ∀ j k, Commute (β (t j)) (β (t k)) := fun j k =>
    Commute.map (show Commute (t j) (t k) from Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ht, ht, ← map_mul, ← map_mul, mul_comm])) β
  have key : ∀ (a b : StatedSU n (2 ^ 1) K) (d : Fin n → Kˣ), β a = β b →
      ((a⁻¹ * b : StatedSU n (2 ^ 1) K) : GL (Fin n) K) = torusDiag d → ∀ i j, d i = d j := by
    intro a b d hab hd i j
    have hk : a⁻¹ * b ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    exact eq_of_mem_center_statedSU h2 hq (hβ hk) hd i j
  have hcoe : ∀ j m, ((t j ^ m : StatedSU n (2 ^ 1) K) : GL (Fin n) K) =
      torusDiag (torusVec ζ j i₄ ^ m) := fun j m => by
    rw [SubgroupClass.coe_pow, ht, map_pow]
  refine CFSG.HardMathSupport.Timmesfeld.DFour.four_le_pRank_of_gens (p := 3)
    (hpow3 i₀) (hpow3 i₁) (hpow3 i₂) (hpow3 i₃) (hcomm _ _) (hcomm _ _) (hcomm _ _)
    (hcomm _ _) (hcomm _ _) (hcomm _ _) ?_ ?_ ?_ ?_
  · intro h
    have e := key 1 (t i₀) (torusVec ζ i₀ i₄) (by rw [h, map_one])
      (by rw [inv_one, one_mul, ht]) i₀ i₁
    rw [torusVec_apply_left ζ h04, torusVec_apply_of_ne ζ h01.symm h14] at e
    exact hζ1 e
  · intro m h
    have e := key (t i₀ ^ m) (t i₁) ((torusVec ζ i₀ i₄ ^ m)⁻¹ * torusVec ζ i₁ i₄)
      (by rw [map_pow, h]) (by rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe, ht, map_mul,
        map_inv]) i₁ i₂
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, torusVec_apply_left ζ h14,
      torusVec_apply_of_ne ζ h01.symm h14, torusVec_apply_of_ne ζ h02.symm h24,
      torusVec_apply_of_ne ζ h12.symm h24, one_pow, inv_one, one_mul] at e
    exact hζ1 e
  · intro m l h
    have e := key (t i₀ ^ m * t i₁ ^ l) (t i₂)
      ((torusVec ζ i₀ i₄ ^ m * torusVec ζ i₁ i₄ ^ l)⁻¹ * torusVec ζ i₂ i₄)
      (by rw [map_mul, map_pow, map_pow, h])
      (by rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hcoe, hcoe, ht, map_mul,
        map_inv, map_mul]) i₂ i₃
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, torusVec_apply_left ζ h24,
      torusVec_apply_of_ne ζ h02.symm h24, torusVec_apply_of_ne ζ h12.symm h24,
      torusVec_apply_of_ne ζ h03.symm h34, torusVec_apply_of_ne ζ h13.symm h34,
      torusVec_apply_of_ne ζ h23.symm h34, one_pow, mul_one, inv_one, one_mul] at e
    exact hζ1 e
  · intro m l r h
    set d : Fin n → Kˣ :=
      (torusVec ζ i₀ i₄ ^ m * torusVec ζ i₁ i₄ ^ l * torusVec ζ i₂ i₄ ^ r)⁻¹ *
        torusVec ζ i₃ i₄ with hd
    have e := key (t i₀ ^ m * t i₁ ^ l * t i₂ ^ r) (t i₃) d
      (by rw [map_mul, map_mul, map_pow, map_pow, map_pow, h])
      (by rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul, hcoe,
        hcoe, hcoe, ht, hd, map_mul, map_inv, map_mul, map_mul])
    have e0 := e i₀ i₃
    have e1 := e i₁ i₃
    have e2 := e i₂ i₃
    have e4 := e i₄ i₃
    simp only [hd, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, torusVec_apply_left ζ h04,
      torusVec_apply_left ζ h14, torusVec_apply_left ζ h24, torusVec_apply_left ζ h34,
      torusVec_apply_right ζ h04, torusVec_apply_right ζ h14, torusVec_apply_right ζ h24,
      torusVec_apply_right ζ h34,
      torusVec_apply_of_ne ζ h01 h04, torusVec_apply_of_ne ζ h02 h04,
      torusVec_apply_of_ne ζ h03 h04,
      torusVec_apply_of_ne ζ h01.symm h14, torusVec_apply_of_ne ζ h12 h14,
      torusVec_apply_of_ne ζ h13 h14,
      torusVec_apply_of_ne ζ h02.symm h24, torusVec_apply_of_ne ζ h12.symm h24,
      torusVec_apply_of_ne ζ h23 h24,
      torusVec_apply_of_ne ζ h03.symm h34, torusVec_apply_of_ne ζ h13.symm h34,
      torusVec_apply_of_ne ζ h23.symm h34, one_pow, mul_one, one_mul, inv_one] at e0 e1 e2 e4
    rw [inv_pow, inv_pow, inv_pow, e0, e1, e2] at e4
    have h3 : ζ * ζ * ζ = 1 := (pow_three' ζ).symm.trans hζ3
    rw [h3, inv_one, one_mul] at e4
    have h' : ζ * ζ = 1 := by
      calc ζ * ζ = ζ * ζ⁻¹ := by rw [e4]
        _ = 1 := mul_inv_cancel ζ
    exact hζ1 (by
      calc ζ = ζ * ζ * ζ * (ζ * ζ)⁻¹ := by group
        _ = 1 := by rw [h3, h', inv_one, one_mul])

end Four

section Unitary

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem four_le_pRank_of_su_hom {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn : 5 ≤ n) {W : Type*} [Group W] [Finite W]
    (α : SU (unitaryInvolution F 2 1) n →* W)
    (hα : α.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup W) := by
  set e := equivStatedSU hF n
  refine four_le_pRank_of_statedSU_hom (by rw [hF]; norm_num) hn (α.comp e.symm.toMonoidHom) ?_
  intro y hy
  have hc : e.symm y ∈ Subgroup.center (SU (unitaryInvolution F 2 1) n) := hα hy
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro z
  have h1 := congrArg e (hc (e.symm z))
  simpa using h1

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.RankThreeCoreUniqueness.Helpers in
theorem four_le_pRank_of_quasisimple_psu (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) {n : ℕ} (hn : 5 ≤ n)
    (hc : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU n 2 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := id hc
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have hB := borelQuotient_su hcard (by omega) ζ hζ e
  have : Group.IsPerfect Y := ⟨hY.1⟩
  have hX := center_centerQuotient_eq_bot hY
  set O : Subgroup Y := primeComplementCore (G := Y) 3 with hOdef
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (primeComplementCore_coprime 3)
  rcases le_center_or_eq_top_of_normal_quasisimple hY O with hO | hO
  · rw [← CFSG.SectionRank.pRank_quotient_eq O hO3]
    have hY₁ : Group.IsPerfect (Y ⧸ O) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective O)
    obtain ⟨α, -, hαker⟩ := exists_lift_su hGA hcard (by omega) hc hX _ hB.surj
      (fun z hz => hB.ker_central z hz) hY₁ (quotCenterOfLeCenter hO)
      (quotCenterOfLeCenter_surjective hO) (ker_quotCenterOfLeCenter_le_center hO)
      (isPGroup_ker_quotCenterOfLeCenter hO)
    exact four_le_pRank_of_su_hom hcard hn α hαker
  ·
    have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center Y) := fun h =>
      hO3 (h.trans (Subgroup.card_dvd_of_le ((le_top : Subgroup.center Y ≤ ⊤).trans hO.ge)))
    rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center Y) hZ3]
    exact four_le_pRank_of_su_hom hcard hn _ fun z hz => hB.ker_central z hz

end Unitary

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem
