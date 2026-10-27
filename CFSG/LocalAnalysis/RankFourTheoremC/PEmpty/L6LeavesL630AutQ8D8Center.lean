module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.AutQ8D8

theorem quaternion_central_eq :
    ∀ q : QuaternionGroup 2, (∀ p : QuaternionGroup 2, p * q = q * p) →
      q = 1 ∨ q = QuaternionGroup.a 2 := by
  decide

theorem dihedral_central_eq :
    ∀ q : DihedralGroup 4, (∀ p : DihedralGroup 4, p * q = q * p) →
      q = 1 ∨ q = DihedralGroup.r 2 := by
  decide

theorem exists_ne_one_of_natCard_eq_two {H : Type} [Group H] (h2 : Nat.card H = 2) :
    ∃ c : H, c ≠ 1 := by
  obtain ⟨y, hy, _⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
  exact ⟨y, hy⟩

theorem eq_one_or_eq_of_natCard_eq_two {H : Type} [Group H] (h2 : Nat.card H = 2) {c : H}
    (hc : c ≠ 1) (d : H) : d = 1 ∨ d = c := by
  obtain ⟨y, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
  by_cases hd : d = 1
  · exact Or.inl hd
  · exact Or.inr ((huniq d hd).trans (huniq c hc).symm)

theorem central_transfer {H K : Type} [Group H] [Group K] (e : H ≃* K) (x : H)
    (hx : ∀ y : H, y * x = x * y) : ∀ p : K, p * e x = e x * p := by
  intro p
  obtain ⟨y, rfl⟩ := e.surjective p
  rw [← map_mul, ← map_mul, hx y]

theorem mem_of_mul_eq_one {R : Type} [Group R] {B : Subgroup R} {a b : R} (hb : b ∈ B)
    (h : a * b = 1) : a ∈ B := by
  rw [eq_inv_of_mul_eq_one_left h]
  exact B.inv_mem hb

theorem exists_mul_of_comm {R : Type} [Group R] {A B : Subgroup R}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hsup : A ⊔ B = ⊤) (r : R) :
    ∃ a ∈ A, ∃ b ∈ B, r = a * b := by
  let S : Subgroup R :=
    { carrier := {r | ∃ a ∈ A, ∃ b ∈ B, r = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by simp only [mul_assoc]
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [hcomm a₂ ha₂ b₁ hb₁]
          _ = a₁ * a₂ * (b₁ * b₂) := by simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm }
  have hS : A ⊔ B ≤ S := by
    refine sup_le ?_ ?_
    · intro a ha
      exact ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩
    · intro b hb
      exact ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩
  have hr : r ∈ A ⊔ B := by
    rw [hsup]
    exact Subgroup.mem_top r
  obtain ⟨a, ha, b, hb, h⟩ := hS hr
  exact ⟨a, ha, b, hb, h⟩

theorem natCard_eq_thirtyTwo {R : Type} [Group R] {A B : Subgroup R}
    (eA : A ≃* QuaternionGroup 2) (eB : B ≃* DihedralGroup 4)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hsup : A ⊔ B = ⊤)
    (hAB : Nat.card (A ⊓ B : Subgroup R) = 2) : Nat.card R = 32 := by
  let φ : (↥A × ↥B) →* R :=
    { toFun := fun p => (p.1 : R) * (p.2 : R)
      map_one' := by simp
      map_mul' := by
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
        simp only [Prod.mk_mul_mk, Subgroup.coe_mul, mul_assoc]
        rw [← mul_assoc (a₂ : R) (b₁ : R) (b₂ : R), hcomm (a₂ : R) a₂.2 (b₁ : R) b₁.2]
        simp only [mul_assoc] }
  have hsurj : Function.Surjective φ := by
    intro r
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_comm hcomm hsup r
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hker : Nat.card φ.ker = 2 := by
    let e : φ.ker ≃ (A ⊓ B : Subgroup R) :=
      { toFun := fun p => ⟨(p.1.1 : R), Subgroup.mem_inf.mpr
          ⟨p.1.1.2, mem_of_mul_eq_one p.1.2.2 (MonoidHom.mem_ker.mp p.2)⟩⟩
        invFun := fun a => ⟨(⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩,
          ⟨a.1⁻¹, B.inv_mem (Subgroup.mem_inf.mp a.2).2⟩),
          MonoidHom.mem_ker.mpr (mul_inv_cancel a.1)⟩
        left_inv := by
          rintro ⟨⟨a, b⟩, h⟩
          have h' : (a : R) * (b : R) = 1 := MonoidHom.mem_ker.mp h
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            exact (eq_inv_of_mul_eq_one_right h').symm
        right_inv := fun a => rfl }
    exact (Nat.card_congr e).trans hAB
  have hA8 : Nat.card ↥A = 8 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    all_goals norm_num
  have hB8 : Nat.card ↥B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    all_goals norm_num
  have hprod : Nat.card (↥A × ↥B) = 64 := by
    rw [Nat.card_prod, hA8, hB8]
    all_goals norm_num
  have hquot : Nat.card ((↥A × ↥B) ⧸ φ.ker) = Nat.card R :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [hprod, hquot, hker] at hsplit
  omega

theorem mem_inf_of_central_left {R : Type} [Group R] {A B : Subgroup R}
    (eA : A ≃* QuaternionGroup 2) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAB : Nat.card (A ⊓ B : Subgroup R) = 2) {a : R} (ha : a ∈ A)
    (hac : ∀ a' ∈ A, a' * a = a * a') : a ∈ A ⊓ B := by
  obtain ⟨c, hc1⟩ := exists_ne_one_of_natCard_eq_two hAB
  have hcA : (c : R) ∈ A := (Subgroup.mem_inf.mp c.2).1
  have hcB : (c : R) ∈ B := (Subgroup.mem_inf.mp c.2).2
  have hc1' : (c : R) ≠ 1 := fun h => hc1 (Subtype.ext h)
  let c' : A := ⟨c, hcA⟩
  let a' : A := ⟨a, ha⟩
  have hc'ne : c' ≠ 1 := fun h => hc1' (congrArg Subtype.val h)
  have hcent : ∀ y : A, y * c' = c' * y := fun y =>
    Subtype.ext (hcomm (y : R) y.2 (c : R) hcB)
  have hacent : ∀ y : A, y * a' = a' * y := fun y => Subtype.ext (hac (y : R) y.2)
  have hc8 : eA c' = QuaternionGroup.a 2 := by
    rcases quaternion_central_eq (eA c') (central_transfer eA c' hcent) with h | h
    · have h1 : c' = 1 := eA.injective (by rw [h, map_one])
      exact absurd h1 hc'ne
    · exact h
  rcases quaternion_central_eq (eA a') (central_transfer eA a' hacent) with h | h
  · have h1 : a' = 1 := eA.injective (by rw [h, map_one])
    have h2 : a = 1 := congrArg Subtype.val h1
    rw [h2]
    exact Subgroup.one_mem _
  · have h1 : a' = c' := eA.injective (by rw [h, hc8])
    have h2 : a = (c : R) := congrArg Subtype.val h1
    rw [h2]
    exact c.2

theorem mem_inf_of_central_right {R : Type} [Group R] {A B : Subgroup R}
    (eB : B ≃* DihedralGroup 4) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAB : Nat.card (A ⊓ B : Subgroup R) = 2) {b : R} (hb : b ∈ B)
    (hbc : ∀ b' ∈ B, b' * b = b * b') : b ∈ A ⊓ B := by
  obtain ⟨c, hc1⟩ := exists_ne_one_of_natCard_eq_two hAB
  have hcA : (c : R) ∈ A := (Subgroup.mem_inf.mp c.2).1
  have hcB : (c : R) ∈ B := (Subgroup.mem_inf.mp c.2).2
  have hc1' : (c : R) ≠ 1 := fun h => hc1 (Subtype.ext h)
  let c' : B := ⟨c, hcB⟩
  let b' : B := ⟨b, hb⟩
  have hc'ne : c' ≠ 1 := fun h => hc1' (congrArg Subtype.val h)
  have hcent : ∀ y : B, y * c' = c' * y := fun y =>
    Subtype.ext (hcomm (c : R) hcA (y : R) y.2).symm
  have hbcent : ∀ y : B, y * b' = b' * y := fun y => Subtype.ext (hbc (y : R) y.2)
  have hc8 : eB c' = DihedralGroup.r 2 := by
    rcases dihedral_central_eq (eB c') (central_transfer eB c' hcent) with h | h
    · have h1 : c' = 1 := eB.injective (by rw [h, map_one])
      exact absurd h1 hc'ne
    · exact h
  rcases dihedral_central_eq (eB b') (central_transfer eB b' hbcent) with h | h
  · have h1 : b' = 1 := eB.injective (by rw [h, map_one])
    have h2 : b = 1 := congrArg Subtype.val h1
    rw [h2]
    exact Subgroup.one_mem _
  · have h1 : b' = c' := eB.injective (by rw [h, hc8])
    have h2 : b = (c : R) := congrArg Subtype.val h1
    rw [h2]
    exact c.2

theorem center_eq_inf {R : Type} [Group R] {A B : Subgroup R}
    (eA : A ≃* QuaternionGroup 2) (eB : B ≃* DihedralGroup 4)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hsup : A ⊔ B = ⊤)
    (hAB : Nat.card (A ⊓ B : Subgroup R) = 2) : Subgroup.center R = A ⊓ B := by
  ext z
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_comm hcomm hsup z
    have hac : ∀ a' ∈ A, a' * a = a * a' := by
      intro a' ha'
      have h1 : a' * (a * b) = a * b * a' := hz a'
      have h2 : b * a' = a' * b := (hcomm a' ha' b hb).symm
      have h3 : a' * a * b = a * a' * b := by
        calc a' * a * b = a' * (a * b) := by rw [mul_assoc]
          _ = a * b * a' := h1
          _ = a * (b * a') := by rw [mul_assoc]
          _ = a * (a' * b) := by rw [h2]
          _ = a * a' * b := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hbc : ∀ b' ∈ B, b' * b = b * b' := by
      intro b' hb'
      have h1 : b' * (a * b) = a * b * b' := hz b'
      have h3 : a * (b' * b) = a * (b * b') := by
        calc a * (b' * b) = a * b' * b := by rw [mul_assoc]
          _ = b' * a * b := by rw [hcomm a ha b' hb']
          _ = b' * (a * b) := by rw [mul_assoc]
          _ = a * b * b' := h1
          _ = a * (b * b') := by rw [mul_assoc]
      exact mul_left_cancel h3
    have haAB : a ∈ A ⊓ B := mem_inf_of_central_left eA hcomm hAB ha hac
    have hbAB : b ∈ A ⊓ B := mem_inf_of_central_right eB hcomm hAB hb hbc
    exact Subgroup.mem_inf.mpr ⟨A.mul_mem ha hbAB.1, B.mul_mem haAB.2 hb⟩
  · intro hz
    obtain ⟨hzA, hzB⟩ := Subgroup.mem_inf.mp hz
    intro g
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_comm hcomm hsup g
    calc a' * b' * z = a' * (b' * z) := by rw [mul_assoc]
      _ = a' * (z * b') := by rw [← hcomm z hzA b' hb']
      _ = a' * z * b' := by rw [mul_assoc]
      _ = z * a' * b' := by rw [hcomm a' ha' z hzB]
      _ = z * (a' * b') := by rw [mul_assoc]

theorem natCard_center {R : Type} [Group R] {A B : Subgroup R}
    (eA : A ≃* QuaternionGroup 2) (eB : B ≃* DihedralGroup 4)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hsup : A ⊔ B = ⊤)
    (hAB : Nat.card (A ⊓ B : Subgroup R) = 2) : Nat.card (Subgroup.center R) = 2 := by
  rw [center_eq_inf eA eB hcomm hsup hAB]
  exact hAB

theorem apply_eq_of_mem_center {R : Type} [Group R] (hcen : Nat.card (Subgroup.center R) = 2)
    (q : MulAut R) {z : R} (hz : z ∈ Subgroup.center R) : q z = z := by
  by_cases h1 : z = 1
  · rw [h1, map_one]
  · have hqz : q z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨s, rfl⟩ := q.surjective g
      rw [← map_mul, ← map_mul, hz s]
    have hc1 : (⟨z, hz⟩ : Subgroup.center R) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    rcases eq_one_or_eq_of_natCard_eq_two hcen hc1 ⟨q z, hqz⟩ with hd | hd
    · exfalso
      apply h1
      apply q.injective
      rw [map_one]
      exact congrArg Subtype.val hd
    · exact congrArg Subtype.val hd

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.AutQ8D8
