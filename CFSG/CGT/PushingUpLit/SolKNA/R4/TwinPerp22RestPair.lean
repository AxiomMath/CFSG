module

public import CFSG.ClassicalInvolution.SmallCases.A7T22Hyp
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.Asc77.AscE184Cent
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open _root_.QuaternionGroup

section Quat

theorem exists_inverting_order_four {k : ℕ} (hk : 1 ≤ k) {u : QuaternionGroup (2 ^ k)}
    (hu : orderOf u = 4) :
    ∃ b : QuaternionGroup (2 ^ k), orderOf b = 4 ∧ b * u * b⁻¹ = u⁻¹ := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 ^ k = 2 * m := ⟨2 ^ (k - 1), by
    rw [← pow_succ' 2 (k - 1), Nat.sub_add_cancel hk]⟩
  have hn0 : (2 ^ k : ℕ) ≠ 0 := pow_ne_zero k two_ne_zero
  have h2n : ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) + ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) = 0 := by
    have := ZMod.natCast_self (2 * 2 ^ k)
    push_cast at this ⊢
    linear_combination this
  rcases u with i | i
  · refine ⟨xa 0, orderOf_xa 0, ?_⟩
    show xa 0 * a i * (xa 0)⁻¹ = (a i)⁻¹
    have e1 : (xa (0 : ZMod (2 * 2 ^ k)))⁻¹ = xa (((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) + 0) := rfl
    have e2 : (a i)⁻¹ = a (-i) := rfl
    rw [e1, e2, xa_mul_a, xa_mul_xa]
    congr 1
    linear_combination h2n
  · have hmn : ((2 * m : ℕ) : ZMod (2 * 2 ^ k)) = ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) := by
      rw [← hm]
    have hj : ((m : ℕ) : ZMod (2 * 2 ^ k)) + (m : ZMod (2 * 2 ^ k)) =
        ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) := by
      rw [← hmn]; push_cast; ring
    refine ⟨a (m : ZMod (2 * 2 ^ k)), ?_, ?_⟩
    · have hsq : (a (m : ZMod (2 * 2 ^ k)) : QuaternionGroup (2 ^ k)) ^ 2 =
          a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) := by
        rw [pow_two, a_mul_a, hj]
      have hne : (a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) : QuaternionGroup (2 ^ k)) ≠ 1 := by
        intro h
        rw [← a_zero] at h
        have h' : ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) = 0 := by injection h
        rw [ZMod.natCast_eq_zero_iff] at h'
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h'
        have h3 : 2 ^ k < 2 * 2 ^ k := by omega
        have := Nat.le_of_dvd (by omega) h'
        omega
      have h4 : (a (m : ZMod (2 * 2 ^ k)) : QuaternionGroup (2 ^ k)) ^ 4 = 1 := by
        have : (4 : ℕ) = 2 * 2 := by norm_num
        rw [this, pow_mul, hsq, pow_two, a_mul_a, h2n, a_zero]
      have := orderOf_eq_prime_pow (p := 2) (n := 1)
        (x := (a (m : ZMod (2 * 2 ^ k)) : QuaternionGroup (2 ^ k)))
        (by rw [pow_one, hsq]; exact hne) (by simpa using h4)
      simpa using this
    · show a (m : ZMod (2 * 2 ^ k)) * xa i * (a (m : ZMod (2 * 2 ^ k)))⁻¹ = (xa i)⁻¹
      have e1 : (a (m : ZMod (2 * 2 ^ k)))⁻¹ = a (-(m : ZMod (2 * 2 ^ k))) := rfl
      have e2 : (xa i)⁻¹ = xa (((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) + i) := rfl
      rw [e1, e2, a_mul_xa, xa_mul_a]
      congr 1
      linear_combination (-1 : ZMod (2 * 2 ^ k)) * hj - h2n

end Quat

section Pair

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_inverting_of_isSylow2In (hΩ : HypOmegaGen Ω) {K R : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylow2In R K) {u : G} (huR : u ∈ R) (hu4 : orderOf u = 4) :
    ∃ b ∈ R, orderOf b = 4 ∧ b * u * b⁻¹ = u⁻¹ := by
  obtain ⟨k, hk, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  have hu : orderOf (e ⟨u, huR⟩) = 4 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hu4
  obtain ⟨q, hq4, hq⟩ := exists_inverting_order_four hk hu
  refine ⟨((e.symm q : ↥R) : G), (e.symm q).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hq4]
  · have h1 : e.symm q * ⟨u, huR⟩ * (e.symm q)⁻¹ = (⟨u, huR⟩ : ↥R)⁻¹ := by
      apply e.injective
      simp [hq]
    exact congrArg Subtype.val h1

theorem exists_pair_b (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} {z u₁ u₂ : G} (hK : K ∈ Ω)
    (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hu₁ : u₁ ∈ K ∧ orderOf u₁ = 4) (hu₂ : u₂ ∈ K' ∧ orderOf u₂ = 4) (hc : u₁ * u₂ = u₂ * u₁) :
    ∃ b₁ ∈ K, ∃ b₂ ∈ K', b₁ * b₁ = z ∧ b₂ * b₂ = z ∧ b₁ * b₂ = b₂ * b₁ ∧
      b₁ * u₁ * b₁⁻¹ = u₁⁻¹ ∧ b₂ * u₂ * b₂⁻¹ = u₂⁻¹ ∧ b₁ * u₂ = u₂ * b₁ ∧ b₂ * u₁ = u₁ * b₂ := by
  classical
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK' hne.symm hz hz'
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK' hK hne hz' hz
  set X : Subgroup G := K ⊔ K' with hX
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hK'N
  have hXK' : X ≤ Subgroup.normalizer (K' : Set G) := sup_le hKN Subgroup.le_normalizer
  have h2₁ : IsPGroup 2 ↥(Subgroup.zpowers u₁) := T7A.isPGroup_zpowers_of_orderOf_four hu₁.2
  have h2₂ : IsPGroup 2 ↥(Subgroup.zpowers u₂) := T7A.isPGroup_zpowers_of_orderOf_four hu₂.2
  have hcN : Subgroup.zpowers u₁ ≤ Subgroup.normalizer (Subgroup.zpowers u₂ : Set G) := by
    have : u₁ ∈ Subgroup.centralizer (Subgroup.zpowers u₂ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (show Commute u₂ u₁ from hc.symm) k).eq
    exact (Subgroup.zpowers_le.mpr this).trans (Subgroup.centralizer_le_normalizer _)
  have hB2 : IsPGroup 2 ↥(Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) :=
    h2₁.to_sup_of_normal_right' h2₂ hcN
  have hBX : Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ ≤ X :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hu₁.1))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right hu₂.1))
  obtain ⟨T, hT, hBT⟩ := IsSylow2In.exists_ge hB2 hBX
  have hR₁ : IsSylow2In (T ⊓ K) K := isSylow2In_inf_of_le_normalizer hT le_sup_left hXK
  have hR₂ : IsSylow2In (T ⊓ K') K' := isSylow2In_inf_of_le_normalizer hT le_sup_right hXK'
  have hu₁T : u₁ ∈ T := hBT (Subgroup.mem_sup_left (Subgroup.mem_zpowers u₁))
  have hu₂T : u₂ ∈ T := hBT (Subgroup.mem_sup_right (Subgroup.mem_zpowers u₂))
  have hu₁R : u₁ ∈ T ⊓ K := ⟨hu₁T, hu₁.1⟩
  have hu₂R : u₂ ∈ T ⊓ K' := ⟨hu₂T, hu₂.1⟩
  have hcomm : Commutes (T ⊓ K) (T ⊓ K') :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK' hne.symm hz hz' inf_le_right inf_le_right
      (hT.2.1.to_le (sup_le inf_le_left inf_le_left))
  obtain ⟨b₁, hb₁R, hb₁4, hb₁⟩ := exists_inverting_of_isSylow2In hΩ hK hR₁ hu₁R hu₁.2
  obtain ⟨b₂, hb₂R, hb₂4, hb₂⟩ := exists_inverting_of_isSylow2In hΩ hK' hR₂ hu₂R hu₂.2
  exact ⟨b₁, hb₁R.2, b₂, hb₂R.2, T7A.sq_eq_of_orderOf_four hz hb₁R.2 hb₁4,
    T7A.sq_eq_of_orderOf_four hz' hb₂R.2 hb₂4, hcomm b₁ hb₁R b₂ hb₂R, hb₁, hb₂,
    hcomm b₁ hb₁R u₂ hu₂R, (hcomm u₁ hu₁R b₂ hb₂R).symm⟩

theorem exists_involution_of_datum {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
    (d : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ v : G, v ∈ K ⊔ K' ∧ v * v = 1 ∧ v * (u₁ * u₂) = (u₁ * u₂) * v ∧
      v * u₁ * v⁻¹ * u₁⁻¹ = z := by
  obtain ⟨b₁, hb₁, b₂, hb₂, hq₁, hq₂, hbb, h1, h2, h3, h4⟩ :=
    exists_pair_b d.hyp d.mem d.hK'.1 d.hne d.hz d.hzK' d.hu₁ d.hu₂ d.comm₁₂
  have e1 : b₁ * u₁ = u₁⁻¹ * b₁ := by
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have e2 : b₂ * u₂ = u₂⁻¹ * b₂ := by
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have e3 : b₁ * u₂⁻¹ = u₂⁻¹ * b₁ := by
    have : Commute b₁ u₂ := h3
    exact this.inv_right.eq
  have hinv : u₁⁻¹ * u₂⁻¹ = u₁ * u₂ := by
    have h5 : (u₁ * u₂)⁻¹ = u₁ * u₂ := inv_eq_of_mul_eq_one_right d.sq_12
    rw [mul_inv_rev] at h5
    rw [← h5]
    exact (show Commute u₁ u₂ from d.comm₁₂).inv_inv.eq
  refine ⟨b₁ * b₂, Subgroup.mul_mem _ (Subgroup.mem_sup_left hb₁) (Subgroup.mem_sup_right hb₂), ?_,
    ?_, ?_⟩
  · calc b₁ * b₂ * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ := by group
      _ = b₁ * (b₁ * b₂) * b₂ := by rw [← hbb]
      _ = (b₁ * b₁) * (b₂ * b₂) := by group
      _ = 1 := by rw [hq₁, hq₂, d.hz.sq]
  · calc b₁ * b₂ * (u₁ * u₂) = b₁ * (b₂ * u₁) * u₂ := by group
      _ = b₁ * (u₁ * b₂) * u₂ := by rw [h4]
      _ = (b₁ * u₁) * (b₂ * u₂) := by group
      _ = (u₁⁻¹ * b₁) * (u₂⁻¹ * b₂) := by rw [e1, e2]
      _ = u₁⁻¹ * (b₁ * u₂⁻¹) * b₂ := by group
      _ = u₁⁻¹ * (u₂⁻¹ * b₁) * b₂ := by rw [e3]
      _ = (u₁⁻¹ * u₂⁻¹) * (b₁ * b₂) := by group
      _ = (u₁ * u₂) * (b₁ * b₂) := by rw [hinv]
  · have h5 : b₁ * b₂ * u₁ * (b₁ * b₂)⁻¹ = u₁⁻¹ := by
      calc b₁ * b₂ * u₁ * (b₁ * b₂)⁻¹ = b₁ * (b₂ * u₁) * b₂⁻¹ * b₁⁻¹ := by group
        _ = b₁ * (u₁ * b₂) * b₂⁻¹ * b₁⁻¹ := by rw [h4]
        _ = b₁ * u₁ * b₁⁻¹ := by group
        _ = u₁⁻¹ := h1
    rw [h5]
    have : u₁⁻¹ * u₁⁻¹ = (u₁ * u₁)⁻¹ := by group
    rw [this, d.sq₁]
    exact inv_eq_of_mul_eq_one_right d.hz.sq

end Pair

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest
