module

public import CFSG.CGT.PushingUpLit.SixThreeV
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.CGT6.SixFiveSylow
public import CFSG.CGT.PushingUpLit.NineChoiceJ
public import CFSG.CGT.PushingUpLit.SixThreeC
public import CFSG.CGT.PushingUpLit.ThreeFromEightOneCore

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] def centralizerQuot (V Q : Subgroup G) [V.Normal] : Subgroup G where
  carrier := {x | ∀ q ∈ Q, ⁅x, q⁆ ∈ V}
  one_mem' := fun q _ => by simp
  mul_mem' := by
    intro x y hx hy q hq
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact V.mul_mem
      (by simpa [mul_assoc] using (inferInstance : V.Normal).conj_mem _ (hy q hq) x) (hx q hq)
  inv_mem' := by
    intro x hx q hq
    have := (inferInstance : V.Normal).conj_mem _ (V.inv_mem (hx q hq)) x⁻¹
    rw [commutatorElement_inv_left, ← commutatorElement_inv]
    simpa using this

instance omegaOneCenterIn_normal (R : Subgroup G) [R.Normal] : (omegaOneCenterIn R).Normal :=
  normal_omegaOneCenterIn R

instance centralizerQuot_normal (V Q : Subgroup G) [V.Normal] [Q.Normal] :
    (centralizerQuot V Q).Normal where
  conj_mem x hx g := by
    intro q hq
    have h1 := hx (g⁻¹ * q * g) (by simpa using (inferInstance : Q.Normal).conj_mem q hq g⁻¹)
    have h2 := (inferInstance : V.Normal).conj_mem _ h1 g
    have e : g * ⁅x, g⁻¹ * q * g⁆ * g⁻¹ = ⁅g * x * g⁻¹, q⁆ := by
      rw [conjugate_commutatorElement]
      have e1 : g * (g⁻¹ * q * g) * g⁻¹ = q := by group
      rw [e1]
    rw [← e]
    exact h2

theorem le_centralizerQuot_of_commutator_le {V Q Y : Subgroup G} [V.Normal] (h : ⁅Q, Y⁆ ≤ V) :
    Y ≤ centralizerQuot V Q := by
  intro y hy q hq
  rw [← commutatorElement_inv]
  exact V.inv_mem (h (Subgroup.commutator_mem_commutator hq hy))

theorem le_of_le_sup_of_isPGroup {X H T : Subgroup G} [H.Normal] (hNo : SubTwo.NoTwoQuotient X)
    (hT : IsPGroup 2 T) (hX : X ≤ H ⊔ T) : X ≤ H := by
  have hTH : T ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.normalizer_eq_top H]
    exact le_top
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left H T hTH
  have hXH : X ⊓ H = X := by
    refine hNo (X ⊓ H) inf_le_left ?_ fun x hx => ?_
    · refine le_trans (le_inf Subgroup.le_normalizer ?_) Subgroup.inf_normalizer_le_normalizer_inf
      rw [Subgroup.normalizer_eq_top H]
      exact le_top
    · have hx' : x ∈ H ⊔ T := hX hx
      rw [← SetLike.mem_coe, hmul] at hx'
      obtain ⟨h, hh, t, ht, rfl⟩ := hx'
      obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
      obtain ⟨h', hh', hpow⟩ := SubTwo.exists_pow_mul_eq hTH hh ht (2 ^ k)
      have ht1 : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine ⟨k, X.pow_mem hx _, ?_⟩
      rw [hpow, ht1, mul_one]
      exact hh'
  exact fun x hx => (hXH.ge hx).2

theorem mem_centralizerModCore_of_commutator_mem [Finite G] {Y R : Subgroup G} [R.Normal]
    (hNo : SubTwo.NoTwoQuotient Y) (hR2 : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) {g : G} (hcomm : ∀ y ∈ Y, ⁅g, y⁆ ∈ R) :
    g ∈ centralizerModCore Y := by
  have hgR : g ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.normalizer_eq_top R]
    exact Subgroup.mem_top g
  have hgY : g ∈ Subgroup.normalizer (Y : Set G) :=
    mem_normalizer_of_commutator_mem hNo hR2 hRY hgR hcomm
  refine ⟨hgY, fun y hy => ?_⟩
  have h1 : ⁅g, y⁆ ∈ Y := by
    have h2 : g * y * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hgY y).mp hy
    exact Y.mul_mem h2 (Y.inv_mem hy)
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.normalizer_eq_top R]
    exact le_top
  have hYR' : Y ⊓ R ≤ oTwoIn Y :=
    le_oTwoIn_of_isPGroup inf_le_left (hR2.to_le inf_le_right)
      (le_trans (le_inf Subgroup.le_normalizer hYR) Subgroup.inf_normalizer_le_normalizer_inf)
  exact hYR' ⟨h1, hcomm y hy⟩

theorem oTwoIn_eq_of_normal_le [Finite G] {Y R H K : Subgroup G} [R.Normal] [H.Normal]
    (hNo : SubTwo.NoTwoQuotient Y) (hR : IsSylowOf 2 R (centralizerModCore Y))
    (hmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ R) (hYH : Y ≤ H) (hHK : H ≤ K)
    (hRK : R ≤ K) : oTwoIn K = R := by
  have hR2 : IsPGroup 2 R := hR.2.1
  have hRY : R ≤ Subgroup.normalizer (Y : Set G) := fun r hr => (hR.1 hr).1
  have hRn : ∀ S : Subgroup G, S ≤ Subgroup.normalizer (R : Set G) := fun S => by
    rw [Subgroup.normalizer_eq_top R]
    exact le_top
  have hRZ : R ≤ oTwoIn K := le_oTwoIn_of_isPGroup hRK hR2 (hRn K)
  refine le_antisymm (fun z hz => ?_) hRZ
  have hOH : oTwoIn H ≤ R := by
    have hn : (oTwoIn H).Normal :=
      ⟨fun z hz g => conj_mem_oTwoIn (by rw [Subgroup.normalizer_eq_top H]; exact Subgroup.mem_top g) hz⟩
    exact hmax _ hn (ThreeFromEight.isPGroup_oTwoIn H)
  have hNH : oTwoIn K ⊓ H ≤ oTwoIn H := by
    refine le_oTwoIn_of_isPGroup inf_le_right
      ((ThreeFromEight.isPGroup_oTwoIn K).to_le inf_le_left) ?_
    refine le_trans (le_inf (hHK.trans (le_normalizer_oTwoIn K)) Subgroup.le_normalizer)
      Subgroup.inf_normalizer_le_normalizer_inf
  have hcomm : ∀ y ∈ Y, ⁅z, y⁆ ∈ R := by
    intro y hy
    have hyK : y ∈ K := hHK (hYH hy)
    have h1 : ⁅z, y⁆ ∈ oTwoIn K := by
      have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (oTwoIn K).mul_mem hz (conj_mem_oTwoIn (Subgroup.le_normalizer hyK)
        ((oTwoIn K).inv_mem hz))
    have h2 : ⁅z, y⁆ ∈ H := by
      have e : ⁅z, y⁆ = (z * y * z⁻¹) * y⁻¹ := rfl
      rw [e]
      exact H.mul_mem ((inferInstance : H.Normal).conj_mem y (hYH hy) z) (H.inv_mem (hYH hy))
    exact hOH (hNH ⟨h1, h2⟩)
  have hzC : z ∈ centralizerModCore Y :=
    mem_centralizerModCore_of_commutator_mem hNo hR2 hRY hcomm
  have hgp : IsPGroup 2 (Subgroup.zpowers z) :=
    (ThreeFromEight.isPGroup_oTwoIn K).to_le (Subgroup.zpowers_le.mpr hz)
  have hP2 : IsPGroup 2 (R ⊔ Subgroup.zpowers z : Subgroup G) := hR2.to_sup_of_normal_left hgp
  have hPC : R ⊔ Subgroup.zpowers z ≤ centralizerModCore Y :=
    sup_le hR.1 (Subgroup.zpowers_le.mpr hzC)
  exact Nine.le_of_isSylowOf_of_le hR hP2 le_sup_left hPC
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))

theorem centralizer_le_of_sup_eq_top [Finite G] {V R T : Subgroup G} [V.Normal] [R.Normal]
    (hR2 : IsPGroup 2 R) (hchar : Subgroup.centralizer (R : Set G) ≤ R)
    (hmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ R) (hT : IsPGroup 2 T)
    (hHT : centralizerQuot V R ⊔ T = ⊤) : Subgroup.centralizer (V : Set G) ≤ R := by
  have hS : stabSeries V R ≤ R := stabSeries_le hR2 hchar hmax
  have hTH : T ≤ Subgroup.normalizer (centralizerQuot V R : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (centralizerQuot V R) T hTH
  have hC2 : IsPGroup 2 (Subgroup.centralizer (V : Set G)) := by
    intro c
    obtain ⟨c, hc⟩ := c
    have hc' : c ∈ centralizerQuot V R ⊔ T := hHT ▸ Subgroup.mem_top c
    rw [← SetLike.mem_coe, hmul] at hc'
    obtain ⟨h, hh, t, ht, rfl⟩ := hc'
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    obtain ⟨h', hh', hpow⟩ := SubTwo.exists_pow_mul_eq hTH hh ht (2 ^ k)
    have ht1 : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hc1 : (h * t) ^ 2 ^ k = h' := by rw [hpow, ht1, mul_one]
    have hcC : (h * t) ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) := Subgroup.pow_mem _ hc _
    have hmem : (h * t) ^ 2 ^ k ∈ R := by
      refine hS ⟨hcC, ?_⟩
      rw [hc1]
      exact hh'
    obtain ⟨j, hj⟩ := hR2 ⟨(h * t) ^ 2 ^ k, hmem⟩
    have h1 : ((h * t) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    refine ⟨k + j, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul]
    exact h1
  exact hmax _ inferInstance hC2

theorem mem_of_pow_mem_of_commutator_mem [Finite G] {Y R : Subgroup G} [R.Normal]
    (hNo : SubTwo.NoTwoQuotient Y) (hR : IsSylowOf 2 R (centralizerModCore Y)) {g : G}
    (hg : ∀ y ∈ Y, ⁅g, y⁆ ∈ R) {k : ℕ} (hk : g ^ 2 ^ k ∈ R) : g ∈ R := by
  have hR2 : IsPGroup 2 R := hR.2.1
  have hRY : R ≤ Subgroup.normalizer (Y : Set G) := fun r hr => (hR.1 hr).1
  have hgC : g ∈ centralizerModCore Y :=
    mem_centralizerModCore_of_commutator_mem hNo hR2 hRY hg
  obtain ⟨j, hj⟩ := hR2 ⟨g ^ 2 ^ k, hk⟩
  have h1 : (g ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hg2 : g ^ 2 ^ (k + j) = 1 := by
    rw [pow_add, pow_mul]
    exact h1
  have hgp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hg2)
  have hP2 : IsPGroup 2 (R ⊔ Subgroup.zpowers g : Subgroup G) := hR2.to_sup_of_normal_left hgp
  have hPC : R ⊔ Subgroup.zpowers g ≤ centralizerModCore Y :=
    sup_le hR.1 (Subgroup.zpowers_le.mpr hgC)
  exact Nine.le_of_isSylowOf_of_le hR hP2 le_sup_left hPC
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

end CFSG.CGT.PushingUpLit.CGT6
