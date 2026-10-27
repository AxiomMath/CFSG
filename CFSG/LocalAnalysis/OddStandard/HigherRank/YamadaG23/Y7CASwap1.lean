module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAJ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement Pointwise

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 K : Subgroup Γ}

private lemma y7c_conj_mul_conj {G : Type*} [Group G] {t x y : G} (ht : t * t = 1) :
    (t * x * t⁻¹) * (t * y * t⁻¹) = t * (x * y) * t⁻¹ := by
  rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_left ht]
  simp only [mul_assoc]
  rw [← mul_assoc t t (y * t), ht, one_mul]

private lemma y7c_conj_conj_self {G : Type*} [Group G] {t x : G} (ht : t * t = 1) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_left ht]
  simp only [mul_assoc]
  rw [← mul_assoc t t (x * (t * t)), ht, one_mul, mul_one]

private lemma y7c_conj_phi {G : Type*} [Group G] {t x : G} (ht : t * t = 1) :
    t * (x * (t * x * t⁻¹)) * t⁻¹ = (t * x * t⁻¹) * x := by
  rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_left ht]
  simp only [mul_assoc, ht, mul_one]

private lemma y7c_commutator_mul_left_of_central {G : Type*} [Group G] {z x c : G}
    (hzx : Commute z x) (hzc : Commute z c) : ⁅z * x, c⁆ = ⁅x, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, hzc.commutator_eq, mul_one]
  calc z * ⁅x, c⁆ * z⁻¹ = ⁅z * x * z⁻¹, z * c * z⁻¹⁆ := conjugate_commutatorElement x c z
    _ = ⁅x, c⁆ := by rw [hzx.eq, hzc.eq]; simp [mul_assoc]

private lemma y7c_commutator_mul_right_of_central {G : Type*} [Group G] {x w y : G}
    (hwx : Commute w x) (hwy : Commute w y) : ⁅x, w * y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, hwx.symm.commutator_eq, one_mul]
  calc w * ⁅x, y⁆ * w⁻¹ = ⁅w * x * w⁻¹, w * y * w⁻¹⁆ := conjugate_commutatorElement x y w
    _ = ⁅x, y⁆ := by rw [hwx.eq, hwy.eq]; simp [mul_assoc]

private lemma y7c_commutator_mul_of_central {G : Type*} [Group G] {z x w y : G}
    (hzx : Commute z x) (hzw : Commute z w) (hzy : Commute z y)
    (hwx : Commute w x) (hwy : Commute w y) : ⁅z * x, w * y⁆ = ⁅x, y⁆ := by
  rw [y7c_commutator_mul_left_of_central hzx (hzw.mul_right hzy),
    y7c_commutator_mul_right_of_central hwx hwy]

@[expose] def y7cPhi (t : Γ) (K : Subgroup Γ)
    (hcomm : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a) : ↥K →* Γ where
  toFun k := (k : Γ) * (t * (k : Γ) * t⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have hb : (b : Γ) * (t * (a : Γ) * t⁻¹) = (t * (a : Γ) * t⁻¹) * (b : Γ) :=
      hcomm b b.2 _ (by simpa using y7c_mul_mem_conjSub (g := t) a.2)
    calc ((a * b : ↥K) : Γ) * (t * ((a * b : ↥K) : Γ) * t⁻¹)
        = (a : Γ) * ((b : Γ) * (t * (a : Γ) * t⁻¹)) * (t * (b : Γ) * t⁻¹) := by
          simp [mul_assoc]
      _ = (a : Γ) * ((t * (a : Γ) * t⁻¹) * (b : Γ)) * (t * (b : Γ) * t⁻¹) := by rw [hb]
      _ = ((a : Γ) * (t * (a : Γ) * t⁻¹)) * ((b : Γ) * (t * (b : Γ) * t⁻¹)) := by
          simp [mul_assoc]

theorem y7cPhi_apply (hcomm : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a) (k : ↥K) :
    y7cPhi t K hcomm k = (k : Γ) * (t * (k : Γ) * t⁻¹) := rfl

theorem y7c_phi_mem_J (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a) (k : ↥K) :
    y7cPhi t K hcomm k ∈ J := by
  haveI : Group.IsPerfect ↥K := hK.1.1
  have hX : ⁅(y7cPhi t K hcomm).range, (y7cPhi t K hcomm).range⁆
      = (y7cPhi t K hcomm).range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (y7cPhi t K hcomm))
  refine y7c_perfect_le_J c hX ?_ (MonoidHom.mem_range.mpr ⟨k, rfl⟩)
  rintro x ⟨k', rfl⟩
  have htt : t * t = 1 := by rw [← pow_two]; exact c.t_sq
  have hconj : t * y7cPhi t K hcomm k' * t⁻¹ = y7cPhi t K hcomm k' := by
    rw [y7cPhi_apply, y7c_conj_phi htt]
    exact (hcomm k' k'.2 (t * (k' : Γ) * t⁻¹) (y7c_mul_mem_conjSub k'.2)).symm
  have htx : t * y7cPhi t K hcomm k' = y7cPhi t K hcomm k' * t := by
    have := congrArg (· * t) hconj
    simpa [mul_assoc] using this
  exact htx.symm

theorem y7c_J_le_phi (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hne : conjSub t K ≠ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a) {j : Γ} (hj : j ∈ J) :
    ∃ k : ↥K, y7cPhi t K hcomm k = j := by
  have htt : t * t = 1 := by rw [← pow_two]; exact c.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have hjt_of : ∀ ⦃x : Γ⦄, x ∈ J → t * x * t⁻¹ = x := by
    intro x hx
    rw [← c.J_cent x hx, mul_assoc, mul_inv_cancel, mul_one]
  have hKnorm : K ≤ Subgroup.normalizer (conjSub t K : Set Γ) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer (conjSub t K : Set Γ) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).symm
  have hsup_mul : ∀ x : Γ, x ∈ K ⊔ conjSub t K ↔
      ∃ a ∈ K, ∃ b ∈ conjSub t K, a * b = x := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ (K : Set Γ) * (conjSub t K : Set Γ) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right K (conjSub t K) hKnorm]
        exact hx
      exact Set.mem_mul.mp hx'
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mul_mem_sup ha hb
  have decomp : ∀ ⦃j : Γ⦄, j ∈ J → ∃ z ∈ K ⊓ conjSub t K, ∃ k : ↥K,
      j = z * y7cPhi t K hcomm k := by
    intro j hj
    obtain ⟨k, hk, k', hk', hjk⟩ := (hsup_mul j).mp (hJK hj)
    have hk0 : t * k' * t⁻¹ ∈ K := by
      have h := (y7c_mem_conjSub (g := t) (x := k') (Y := K)).mp hk'
      simpa [htinv] using h
    have haKt : t * k * t⁻¹ ∈ conjSub t K := y7c_mul_mem_conjSub hk
    have h_ak0 : (t * k * t⁻¹) * (t * k' * t⁻¹) = j := by
      rw [y7c_conj_mul_conj htt, hjk, hjt_of hj]
    have hcomm_k0a :
        (t * k' * t⁻¹) * (t * k * t⁻¹) = (t * k * t⁻¹) * (t * k' * t⁻¹) :=
      hcomm (t * k' * t⁻¹) hk0 (t * k * t⁻¹) haKt
    have h1 : (k⁻¹ * (t * k' * t⁻¹)) * (t * k * t⁻¹) = k' := by
      rw [mul_assoc, hcomm_k0a, h_ak0, ← hjk, ← mul_assoc, inv_mul_cancel, one_mul]
    have hz_eq : k⁻¹ * (t * k' * t⁻¹) = k' * (t * k * t⁻¹)⁻¹ := by
      have := congrArg (· * (t * k * t⁻¹)⁻¹) h1
      simpa [mul_assoc] using this
    have hzK : k⁻¹ * (t * k' * t⁻¹) ∈ K := K.mul_mem (K.inv_mem hk) hk0
    have hzKt : k⁻¹ * (t * k' * t⁻¹) ∈ conjSub t K := by
      rw [hz_eq]
      exact (conjSub t K).mul_mem hk' ((conjSub t K).inv_mem haKt)
    have hf : y7cPhi t K hcomm ⟨t * k' * t⁻¹, hk0⟩ = (t * k' * t⁻¹) * k' := by
      rw [y7cPhi_apply]
      congr 1
      exact y7c_conj_conj_self htt
    have hkz : k * (k⁻¹ * (t * k' * t⁻¹)) = t * k' * t⁻¹ := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hk_eq : k = (k⁻¹ * (t * k' * t⁻¹))⁻¹ * (t * k' * t⁻¹) := by
      have hcz : Commute (t * k' * t⁻¹) (k⁻¹ * (t * k' * t⁻¹)) :=
        hcomm (t * k' * t⁻¹) hk0 (k⁻¹ * (t * k' * t⁻¹)) hzKt
      have hz0 : (t * k' * t⁻¹) * (k⁻¹ * (t * k' * t⁻¹))⁻¹
          = (k⁻¹ * (t * k' * t⁻¹))⁻¹ * (t * k' * t⁻¹) := hcz.inv_right.eq
      calc k = k * ((k⁻¹ * (t * k' * t⁻¹)) * (k⁻¹ * (t * k' * t⁻¹))⁻¹) := by
              rw [mul_inv_cancel, mul_one]
        _ = (k * (k⁻¹ * (t * k' * t⁻¹))) * (k⁻¹ * (t * k' * t⁻¹))⁻¹ :=
              (mul_assoc k (k⁻¹ * (t * k' * t⁻¹)) (k⁻¹ * (t * k' * t⁻¹))⁻¹).symm
        _ = (t * k' * t⁻¹) * (k⁻¹ * (t * k' * t⁻¹))⁻¹ := by rw [hkz]
        _ = (k⁻¹ * (t * k' * t⁻¹))⁻¹ * (t * k' * t⁻¹) := hz0
    refine ⟨(k⁻¹ * (t * k' * t⁻¹))⁻¹,
      Subgroup.mem_inf.mpr ⟨K.inv_mem hzK, (conjSub t K).inv_mem hzKt⟩,
      ⟨t * k' * t⁻¹, hk0⟩, ?_⟩
    calc j = k * k' := hjk.symm
      _ = ((k⁻¹ * (t * k' * t⁻¹))⁻¹ * (t * k' * t⁻¹)) * k' := by
            conv_lhs => rw [hk_eq]
      _ = (k⁻¹ * (t * k' * t⁻¹))⁻¹ * ((t * k' * t⁻¹) * k') := mul_assoc _ _ _
      _ = (k⁻¹ * (t * k' * t⁻¹))⁻¹ * y7cPhi t K hcomm ⟨t * k' * t⁻¹, hk0⟩ := by
            rw [hf]
  have hDcomm : ∀ d ∈ K ⊓ conjSub t K, ∀ x ∈ K ⊔ conjSub t K, d * x = x * d := by
    intro d hd x hx
    obtain ⟨hdK, hdKt⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := (hsup_mul x).mp hx
    calc d * (x₁ * x₂) = (d * x₁) * x₂ := (mul_assoc d x₁ x₂).symm
      _ = (x₁ * d) * x₂ := by rw [(hcomm x₁ hx₁ d hdKt).symm]
      _ = x₁ * (d * x₂) := mul_assoc x₁ d x₂
      _ = x₁ * (x₂ * d) := by rw [hcomm d hdK x₂ hx₂]
      _ = (x₁ * x₂) * d := (mul_assoc x₁ x₂ d).symm
  have hphi_sup : ∀ k : ↥K, y7cPhi t K hcomm k ∈ K ⊔ conjSub t K := by
    intro k
    rw [y7cPhi_apply]
    exact Subgroup.mul_mem_sup k.2 (y7c_mul_mem_conjSub (g := t) k.2)
  have hcommut : ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ ∈ (y7cPhi t K hcomm).range := by
    intro a ha b hb
    obtain ⟨za, hzaD, ka, rfl⟩ := decomp ha
    obtain ⟨zb, hzbD, kb, rfl⟩ := decomp hb
    have hzbK : zb ∈ K := (Subgroup.mem_inf.mp hzbD).1
    have hzaka : Commute za (y7cPhi t K hcomm ka) := hDcomm za hzaD _ (hphi_sup ka)
    have hzazb : Commute za zb := hDcomm za hzaD zb (Subgroup.mem_sup_left hzbK)
    have hzakb : Commute za (y7cPhi t K hcomm kb) := hDcomm za hzaD _ (hphi_sup kb)
    have hzbka : Commute zb (y7cPhi t K hcomm ka) := hDcomm zb hzbD _ (hphi_sup ka)
    have hzbkb : Commute zb (y7cPhi t K hcomm kb) := hDcomm zb hzbD _ (hphi_sup kb)
    rw [y7c_commutator_mul_of_central hzaka hzazb hzakb hzbka hzbkb]
    rw [← map_commutatorElement (y7cPhi t K hcomm)]
    exact MonoidHom.mem_range.mpr ⟨⁅ka, kb⁆, rfl⟩
  have hJle : J ≤ (y7cPhi t K hcomm).range := by
    rw [← y7c_J_perfect c]
    exact Subgroup.commutator_le.mpr hcommut
  exact MonoidHom.mem_range.mp (hJle hj)

end CFSG.OddStandard.HigherRank.YamadaG23
