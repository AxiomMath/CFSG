module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviDiag

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Transfer

theorem eq_bot_of_isPGroup_two_of_commutator_eq_self {G : Type*} [Group G] [Finite G]
    {L : Subgroup G} (hL2 : IsPGroup 2 ↥L) (hL : ⁅L, L⁆ = L) : L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥L := hL2.isNilpotent
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  by_contra hne
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable (G := ↥L) inferInstance

variable {P : Type} [Group P]

theorem centralizer_map_mulAut (φ : MulAut P) (S : Subgroup P) :
    (centralizer (S : Set P)).map φ.toMonoidHom =
      centralizer ((S.map φ.toMonoidHom) : Set P) := by
  refine le_antisymm (map_centralizer_le_centralizer_image _ _) ?_
  intro x hx
  refine ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro s hs
  have h := mem_centralizer_iff.mp hx (φ s) ⟨s, hs, rfl⟩
  apply φ.injective
  rw [map_mul, map_mul, φ.apply_symm_apply]
  exact h

theorem noNormalTwo_map_mulAut {H : Subgroup P} (h : NoNormalTwo H) (φ : MulAut P) :
    NoNormalTwo (H.map φ.toMonoidHom) := by
  intro Q hQ hQ2 hN
  set Q' := Q.map φ.symm.toMonoidHom
  have hQ' : Q' ≤ H := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hQ hq
    change φ.symm (φ y) ∈ H
    rwa [φ.symm_apply_apply]
  have hN' : H ≤ normalizer (Q' : Set P) := by
    intro y hy
    have h1 : φ y ∈ normalizer (Q : Set P) := hN ⟨y, hy, rfl⟩
    have h2 : φ.symm (φ y) ∈ (normalizer (Q : Set P)).map φ.symm.toMonoidHom := ⟨φ y, h1, rfl⟩
    rw [φ.symm_apply_apply, map_equiv_normalizer_eq] at h2
    exact h2
  have h3 := h Q' hQ' (hQ2.map _) hN'
  rw [eq_bot_iff]
  intro q hq
  have h4 : φ.symm q ∈ Q' := ⟨q, hq, rfl⟩
  rw [h3, mem_bot] at h4
  rw [mem_bot]
  simpa using congrArg φ h4

theorem mem_centralizer_of_theta_commute {G : Type} [Group G] {A : Subgroup G} {θ : ↥A →* P}
    (hker : θ.ker = center ↥A) {Y : Subgroup G} (hYA : Y ≤ A) (hY : ⁅Y, Y⁆ = Y) {a : ↥A}
    (ha : ∀ y (hy : y ∈ Y), θ a * θ ⟨y, hYA hy⟩ = θ ⟨y, hYA hy⟩ * θ a) :
    (a : G) ∈ centralizer (Y : Set G) := by
  have key : ∀ y ∈ Y, ∃ z : G, (a : G) * y * (a : G)⁻¹ = y * z ∧ ∃ hz : z ∈ A,
      (⟨z, hz⟩ : ↥A) ∈ center ↥A := by
    intro y hy
    have hz : y⁻¹ * ((a : G) * y * (a : G)⁻¹) ∈ A :=
      mul_mem (inv_mem (hYA hy)) (mul_mem (mul_mem a.2 (hYA hy)) (inv_mem a.2))
    refine ⟨y⁻¹ * ((a : G) * y * (a : G)⁻¹), by group, hz, ?_⟩
    rw [← hker, MonoidHom.mem_ker]
    have h1 : (⟨y⁻¹ * ((a : G) * y * (a : G)⁻¹), hz⟩ : ↥A) =
        (⟨y, hYA hy⟩ : ↥A)⁻¹ * (a * ⟨y, hYA hy⟩ * a⁻¹) := rfl
    rw [h1, map_mul, map_inv, map_mul, map_mul, map_inv, ha y hy]
    group
  have hcomm : ∀ {z : G} (hzA : z ∈ A), (⟨z, hzA⟩ : ↥A) ∈ center ↥A → ∀ y ∈ A, z * y = y * z :=
    fun hzA hz y hy => congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩).symm
  have hle : Y ≤ centralizer ({(a : G)} : Set G) := by
    rw [← hY, commutator_le]
    intro b hb c hc
    rw [mem_centralizer_singleton_iff]
    obtain ⟨z₁, hz₁, hz₁A, hz₁Z⟩ := key b hb
    obtain ⟨z₂, hz₂, hz₂A, hz₂Z⟩ := key c hc
    have hconj : (a : G) * ⁅b, c⁆ * (a : G)⁻¹ = ⁅b, c⁆ := by
      rw [show (a : G) * ⁅b, c⁆ * (a : G)⁻¹ =
          ⁅(a : G) * b * (a : G)⁻¹, (a : G) * c * (a : G)⁻¹⁆ by
        simp only [commutatorElement_def]; group, hz₁, hz₂]
      exact commutatorElement_mul_mul_of_commute' (hcomm hz₁A hz₁Z c (hYA hc))
        (hcomm hz₂A hz₂Z b (hYA hb)) (hcomm hz₁A hz₁Z z₂ hz₂A)
    calc ⁅b, c⁆ * (a : G) = (a : G) * ⁅b, c⁆ * (a : G)⁻¹ * (a : G) := by rw [hconj]
      _ = (a : G) * ⁅b, c⁆ := by group
  rw [mem_centralizer_iff]
  intro y hy
  exact mem_centralizer_singleton_iff.mp (hle hy)

theorem noNormalTwo_inf_centralizer_of_quot {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {θ : ↥A →* P} (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {Y : Subgroup G} (hYA : Y ≤ A) (hY : ⁅Y, Y⁆ = Y)
    (h : NoNormalTwo (centralizer (((Y.subgroupOf A).map θ : Subgroup P) : Set P))) :
    NoNormalTwo (A ⊓ centralizer (Y : Set G)) := by
  intro Q hQ hQ2 hN
  have hQA : Q ≤ A := hQ.trans inf_le_left
  set Qθ : Subgroup P := (Q.subgroupOf A).map θ
  have h1 : Qθ ≤ centralizer (((Y.subgroupOf A).map θ : Subgroup P) : Set P) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hab : (b : G) * a = a * b := mem_centralizer_iff.mp (hQ ha).2 b hb
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext hab)
  have hQ2' : IsPGroup 2 ↥(Q.subgroupOf A) := hQ2.of_equiv (subgroupOfEquivOfLe hQA).symm
  have h3 : centralizer (((Y.subgroupOf A).map θ : Subgroup P) : Set P) ≤
      normalizer (Qθ : Set P) := by
    intro x hx
    obtain ⟨a, rfl⟩ := hθ x
    have haY : (a : G) ∈ centralizer (Y : Set G) := by
      refine mem_centralizer_of_theta_commute hker hYA hY fun y hy => ?_
      exact (mem_centralizer_iff.mp hx (θ ⟨y, hYA hy⟩) ⟨⟨y, hYA hy⟩, hy, rfl⟩).symm
    have haN := hN ⟨a.2, haY⟩
    rw [mem_normalizer_iff] at haN ⊢
    intro q
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨a * b * a⁻¹, (haN b).mp hb, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨b, hb, hbq⟩
      have hb0 : (b : G) ∈ Q := hb
      have hb' : ((a⁻¹ * b * a : ↥A) : G) ∈ Q := by
        rw [haN]
        have e : (a : G) * ((a⁻¹ * b * a : ↥A) : G) * (a : G)⁻¹ = b := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        exact hb0
      refine ⟨a⁻¹ * b * a, hb', ?_⟩
      rw [map_mul, map_mul, map_inv, hbq]
      group
  have hbot := h Qθ h1 (hQ2'.map θ) h3
  have hZ : Q.subgroupOf A ≤ center ↥A := by
    intro b hb
    rw [← hker, MonoidHom.mem_ker]
    have : θ b ∈ Qθ := ⟨b, hb, rfl⟩
    rwa [hbot, mem_bot] at this
  have hodd' : Odd (Nat.card ↥(Q.subgroupOf A)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hZ)
  have hbot' := eq_bot_of_isPGroup_two_of_odd hQ2' hodd'
  rw [eq_bot_iff]
  intro q hq
  have : (⟨q, hQA hq⟩ : ↥A) ∈ Q.subgroupOf A := hq
  rw [hbot', mem_bot] at this
  exact (mem_bot).mpr (congrArg Subtype.val this)

end Transfer

section BarW

theorem eq_bot_of_normal_isPGroup_two_of_quasisimple {L : Type*} [Group L] [Finite L]
    (hL : CFSG.IsQuasisimple L) (hodd : Odd (Nat.card (center L))) (M : Subgroup L) [M.Normal]
    (hM : IsPGroup 2 ↥M) : M = ⊥ := by
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hL M with hc | htop
  · exact eq_bot_of_isPGroup_two_of_odd hM (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hc))
  · have hperf : ⁅(⊤ : Subgroup L), ⊤⁆ = ⊤ := hL.1.commutator_eq_top
    rw [htop] at hM ⊢
    exact eq_bot_of_isPGroup_two_of_commutator_eq_self hM hperf

variable {K : Type} [Field K] {k : ℕ}

theorem pow_eq_one_of_commute_barW_barL [Finite K] [CharP K 2] (hk : 1 ≤ k)
    {x : projectiveSL (2 + k) K} (hW : ∀ w ∈ barW K k, x * w = w * x)
    (hL : ∀ l ∈ barL K k, x * l = l * x) : x ^ (Nat.card K - 1) = 1 := by
  have := Fintype.ofFinite K
  obtain ⟨g, rfl, c, D, hg⟩ := exists_blk_of_commute_barW hW
  have hD : ∀ i j : Fin k, i ≠ j → D * (1 + single i j 1) = (1 + single i j 1) * D := by
    intro i j hij
    have h1 := commute_of_proj_commute (blkSL₂_trn_sq i j hij) (hL _ ⟨trn i j hij 1, rfl⟩)
    have h2 := congrArg Subtype.val h1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, coe_blkSL₂,
      coe_trn, blk_mul, blk_mul] at h2
    exact (blk_injective h2).2
  obtain ⟨ν, hν⟩ := exists_scalar_of_commute_trn hD
  have hdet : c ^ 2 * ν ^ k = 1 := by
    have h := g.2
    rw [hg, hν, det_blk, det_smul, det_one, mul_one, det_scalar_fin, Fintype.card_fin] at h
    exact h
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_mul] at hdet
    exact zero_ne_one hdet
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), mul_zero] at hdet
    exact zero_ne_one hdet
  have hg1 : g ^ (Nat.card K - 1) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hg, hν, blk_pow, smul_pow, one_pow, ← map_pow,
      Nat.card_eq_fintype_card, FiniteField.pow_card_sub_one_eq_one c hc,
      FiniteField.pow_card_sub_one_eq_one ν hν0, one_smul, map_one, blk_one]
    rfl
  rw [← map_pow, hg1, map_one]

theorem eq_bot_of_le_centralizer_barW [Finite K] [CharP K 2] (hk : 2 ≤ k)
    (hq4 : ∃ s : Finset K, s.card = 4) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {Q : Subgroup (projectiveSL (2 + k) K)}
    (hQ : Q ≤ centralizer (barW K k : Set (projectiveSL (2 + k) K))) (hQ2 : IsPGroup 2 ↥Q)
    (hLN : barL K k ≤ normalizer (Q : Set (projectiveSL (2 + k) K))) : Q = ⊥ := by
  set M : Subgroup ↥(barL K k) := Q.subgroupOf (barL K k)
  have hMn : M.Normal :=
    ⟨fun n hn l => (mem_normalizer_iff.mp (hLN l.2) n.1).mp hn⟩
  have hM2 : IsPGroup 2 ↥M := fun g => by
    obtain ⟨n, hn⟩ := hQ2 ⟨g.1.1, g.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have h := congrArg (Subtype.val : ↥Q → projectiveSL (2 + k) K) hn
    simpa using h
  have hMbot := eq_bot_of_normal_isPGroup_two_of_quasisimple (isQuasisimple_barL hk hq4)
    (odd_card_center_barL hm hK) M hM2
  have hQW : ∀ x ∈ Q, ∀ w ∈ barW K k, x * w = w * x := fun x hx w hw =>
    (mem_centralizer_iff.mp (hQ hx) w hw).symm
  have hQL : ∀ x ∈ Q, ∀ l ∈ barL K k, x * l = l * x := by
    intro x hx l hl
    have h1 : ⁅x, l⁆ ∈ Q := by
      have hl' : l * x⁻¹ * l⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp (hLN hl) x⁻¹).mp (inv_mem hx)
      rw [commutatorElement_def, mul_assoc x, mul_assoc x]
      exact mul_mem hx hl'
    have h2 : ⁅x, l⁆ ∈ barL K k := commutatorElement_mem_barL (hQW x hx)
      fun w hw => (barW_commute_barL hw hl).symm
    have h3 : (⟨⁅x, l⁆, h2⟩ : ↥(barL K k)) ∈ M := h1
    rw [hMbot, mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h3)
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  have hpow := pow_eq_one_of_commute_barW_barL (by omega) (hQW x hx) (hQL x hx)
  obtain ⟨n, hn⟩ := hQ2 ⟨x, hx⟩
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  have h2 : orderOf x ∣ Nat.card K - 1 := orderOf_dvd_of_pow_eq_one hpow
  have hodd : Odd (Nat.card K - 1) := by
    rw [hK]
    obtain ⟨j, hj⟩ : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    exact ⟨j - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ n) (Nat.card K - 1) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)

theorem noNormalTwo_centralizer_barW [Finite K] [CharP K 2] (hk : 2 ≤ k)
    (hq4 : ∃ s : Finset K, s.card = 4) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    NoNormalTwo (centralizer (barW K k : Set (projectiveSL (2 + k) K))) := by
  intro Q hQ hQ2 hN
  have hLC : barL K k ≤ centralizer (barW K k : Set (projectiveSL (2 + k) K)) := fun l hl =>
    mem_centralizer_iff.mpr fun w hw => barW_commute_barL hw hl
  exact eq_bot_of_le_centralizer_barW hk hq4 hm hK hQ hQ2 (hLC.trans hN)

end BarW

end CFSG.ComponentClassification.RankTwoClassical
