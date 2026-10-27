module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAAut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA Subgroup

theorem eq_one_of_two_elt_p_elt {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {z : G} (h2 : ∃ k : ℕ, z ^ (2 ^ k) = 1) (hp' : ∃ k : ℕ, z ^ (p ^ k) = 1) : z = 1 := by
  obtain ⟨i, hi⟩ := h2
  obtain ⟨j, hj⟩ := hp'
  have hcop : Nat.Coprime (2 ^ i) (p ^ j) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h3 : orderOf z ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hi
  have h4 : orderOf z ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj
  have h5 := Nat.dvd_gcd h3 h4
  rw [hcop.gcd_eq_one] at h5
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h5)

theorem two_elt_mul {G : Type*} [Group G] {a b : G} (hab : Commute a b)
    (ha : ∃ k : ℕ, a ^ (2 ^ k) = 1) (hb : ∃ k : ℕ, b ^ (2 ^ k) = 1) :
    ∃ k : ℕ, (a * b) ^ (2 ^ k) = 1 := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  refine ⟨i + j, ?_⟩
  rw [hab.mul_pow]
  have h1 : a ^ (2 ^ (i + j)) = 1 := by
    rw [pow_add, pow_mul, hi, one_pow]
  have h2 : b ^ (2 ^ (i + j)) = 1 := by
    rw [add_comm, pow_add, pow_mul, hj, one_pow]
  rw [h1, h2, one_mul]

section Embedding

variable {Y : Type} [Group Y] (L : Subgroup Y) [L.Normal] {P' : Type} [Group P']
  (eP : (↥L ⧸ center ↥L) ≃* P')

@[expose] noncomputable def eL : ↥L →* P' :=
  (eP : (↥L ⧸ center ↥L) →* P').comp (QuotientGroup.mk' (center ↥L))

theorem eL_apply (l : ↥L) : eL L eP l = eP (QuotientGroup.mk l) := rfl

theorem eL_eq_one_iff (l : ↥L) : eL L eP l = 1 ↔ l ∈ center ↥L := by
  rw [eL_apply, ← eP.map_one, eP.injective.eq_iff, QuotientGroup.eq_one_iff]

theorem thetaP_eL (y : Y) (l : ↥L) :
    thetaP L eP y (eL L eP l) = eL L eP (MulAut.conjNormal y l) := by
  rw [thetaP_apply, eL_apply, MulEquiv.symm_apply_apply, theta_mk, eL_apply]

@[expose] def stabSub (T : Subgroup P') : Subgroup (MulAut P') where
  carrier := {φ | ∀ t : P', t ∈ T ↔ φ t ∈ T}
  one_mem' := fun t => Iff.rfl
  mul_mem' := by
    intro φ ψ hφ hψ t
    rw [MulAut.mul_apply, hψ t, hφ (ψ t)]
  inv_mem' := by
    intro φ hφ t
    have := hφ (φ⁻¹ t)
    rw [MulAut.apply_inv_self] at this
    exact this.symm

theorem mem_stabSub {T : Subgroup P'} {φ : MulAut P'} :
    φ ∈ stabSub T ↔ ∀ t : P', t ∈ T ↔ φ t ∈ T := Iff.rfl

variable {L}

theorem mem_stabSub_of_mem_normalizer {T₀ : Subgroup Y} (hT₀L : T₀ ≤ L) {y : Y}
    (hy : y ∈ normalizer (T₀ : Set Y)) :
    thetaP L eP y ∈ stabSub ((T₀.subgroupOf L).map (eL L eP)) := by
  have fwd : ∀ y ∈ normalizer (T₀ : Set Y), ∀ t ∈ (T₀.subgroupOf L).map (eL L eP),
      thetaP L eP y t ∈ (T₀.subgroupOf L).map (eL L eP) := by
    intro y hy t ht
    obtain ⟨a, ha, rfl⟩ := ht
    rw [thetaP_eL]
    have ha' : (a : Y) ∈ T₀ := Subgroup.mem_subgroupOf.1 ha
    refine ⟨MulAut.conjNormal y a, ?_, rfl⟩
    show MulAut.conjNormal y a ∈ T₀.subgroupOf L
    rw [Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.1 hy a).1 ha'
  intro t
  refine ⟨fwd y hy t, fun h => ?_⟩
  have := fwd y⁻¹ (Subgroup.inv_mem _ hy) _ h
  rwa [map_inv, MulAut.inv_apply_self] at this

variable (L)

theorem mem_normalizer_of_mem_stabSub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ∀ z ∈ center ↥L, ∃ k : ℕ, z ^ (p ^ k) = 1) {T₀ : Subgroup Y} (hT₀L : T₀ ≤ L)
    (hT₀2 : IsPGroup 2 T₀) {y : Y}
    (hy : thetaP L eP y ∈ stabSub ((T₀.subgroupOf L).map (eL L eP))) :
    y ∈ normalizer (T₀ : Set Y) := by
  have key : ∀ y : Y, thetaP L eP y ∈ stabSub ((T₀.subgroupOf L).map (eL L eP)) →
      ∀ a ∈ T₀, y * a * y⁻¹ ∈ T₀ := by
    intro y hy a ha
    set la : ↥L := ⟨a, hT₀L ha⟩ with hla
    have hmem : eL L eP la ∈ (T₀.subgroupOf L).map (eL L eP) :=
      ⟨la, Subgroup.mem_subgroupOf.2 ha, rfl⟩
    have h1 := (mem_stabSub.1 hy _).1 hmem
    rw [thetaP_eL] at h1
    obtain ⟨b, hb, hbe⟩ := h1
    have hbT : (b : Y) ∈ T₀ := Subgroup.mem_subgroupOf.1 hb
    set w : ↥L := MulAut.conjNormal y la with hw
    have hz : b⁻¹ * w ∈ center ↥L := by
      rw [← eL_eq_one_iff L eP, map_mul, map_inv, hbe, inv_mul_cancel]
    have hbz : Commute b (b⁻¹ * w) := Subgroup.mem_center_iff.1 hz b
    have hwz : w = b * (b⁻¹ * w) := by group
    have hbw : Commute b w := by
      rw [hwz]
      exact (Commute.refl b).mul_right hbz
    obtain ⟨i, hi⟩ := hT₀2 ⟨a, ha⟩
    obtain ⟨j, hj⟩ := hT₀2 ⟨(b : Y), hbT⟩
    have hi' : a ^ (2 ^ i) = 1 := by simpa using congrArg Subtype.val hi
    have hj' : (b : Y) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have hwi : ∃ k : ℕ, w ^ (2 ^ k) = 1 := by
      refine ⟨i, ?_⟩
      rw [hw, ← map_pow]
      have : la ^ (2 ^ i) = 1 := Subtype.ext (by simpa [hla] using hi')
      rw [this, map_one]
    have hbj : ∃ k : ℕ, (b⁻¹) ^ (2 ^ k) = 1 := by
      refine ⟨j, ?_⟩
      have : b ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj')
      rw [inv_pow, this, inv_one]
    have hz2 := two_elt_mul hbw.inv_left hbj hwi
    have hz1 : b⁻¹ * w = 1 := eq_one_of_two_elt_p_elt hp hp2 hz2 (hZ _ hz)
    have hbw' : b = w := inv_mul_eq_one.1 hz1
    have : y * a * y⁻¹ = (b : Y) := by
      rw [hbw', hw, MulAut.conjNormal_apply]
    rw [this]
    exact hbT
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key y hy h, fun hh => ?_⟩
  have hy' : thetaP L eP y⁻¹ ∈ stabSub ((T₀.subgroupOf L).map (eL L eP)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hy
  have := key y⁻¹ hy' _ hh
  simpa [mul_assoc] using this

theorem mem_normalizer_iff_mem_stab {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ∀ z ∈ center ↥L, ∃ k : ℕ, z ^ (p ^ k) = 1) {T₀ : Subgroup Y} (hT₀L : T₀ ≤ L)
    (hT₀2 : IsPGroup 2 T₀) (y : Y) :
    y ∈ normalizer (T₀ : Set Y) ↔
      thetaP L eP y ∈ stabSub ((T₀.subgroupOf L).map (eL L eP)) :=
  ⟨mem_stabSub_of_mem_normalizer eP hT₀L, mem_normalizer_of_mem_stabSub L eP hp hp2 hZ hT₀L hT₀2⟩

theorem isTwoElt_map {T₀ : Subgroup Y} (hT₀L : T₀ ≤ L) (hT₀2 : IsPGroup 2 T₀)
    (t : P') (ht : t ∈ (T₀.subgroupOf L).map (eL L eP)) : ∃ k : ℕ, t ^ (2 ^ k) = 1 := by
  obtain ⟨a, ha, rfl⟩ := ht
  obtain ⟨k, hk⟩ := hT₀2 ⟨(a : Y), Subgroup.mem_subgroupOf.1 ha⟩
  refine ⟨k, ?_⟩
  rw [← map_pow]
  have : a ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  rw [this, map_one]

theorem map_ne_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ∀ z ∈ center ↥L, ∃ k : ℕ, z ^ (p ^ k) = 1) {T₀ : Subgroup Y} (hT₀L : T₀ ≤ L)
    (hT₀2 : IsPGroup 2 T₀) (hT₀ : T₀ ≠ ⊥) : (T₀.subgroupOf L).map (eL L eP) ≠ ⊥ := by
  intro hbot
  apply hT₀
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  have h1 : eL L eP ⟨t, hT₀L ht⟩ ∈ (T₀.subgroupOf L).map (eL L eP) :=
    ⟨⟨t, hT₀L ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  rw [hbot, Subgroup.mem_bot, eL_eq_one_iff] at h1
  obtain ⟨k, hk⟩ := hT₀2 ⟨t, ht⟩
  have h2 : (⟨t, hT₀L ht⟩ : ↥L) = 1 := by
    refine eq_one_of_two_elt_p_elt hp hp2 ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
      (hZ _ h1)
  exact congrArg Subtype.val h2

end Embedding


end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
