module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW

open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

structure U3QTriple (z a b : G) : Prop where
  sq_a : a * a = z
  sq_b : b * b = z
  sq_ab : a * b * (a * b) = z
  ne : a * b ≠ b * a

theorem U3QTriple.ne_left {z a b : G} (h : U3QTriple z a b) : a * (a * b) ≠ a * b * a := by
  intro h1
  apply h.ne
  exact mul_left_cancel (a := a) (by rw [h1, mul_assoc])

theorem U3QTriple.ne_right {z a b : G} (h : U3QTriple z a b) : b * (a * b) ≠ a * b * b := by
  intro h1
  apply h.ne
  have : b * a * b = a * b * b := by rw [← h1, mul_assoc]
  exact (mul_right_cancel this).symm

theorem exists_u3QTriple {K R : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) (hRK : R ≤ K)
    (e : ↥R ≃* QuaternionGroup 2) : ∃ a ∈ R, ∃ b ∈ R, U3QTriple z a b := by
  have sq4 : ∀ u : G, u ∈ K → orderOf u = 4 → u * u = z := by
    intro u hu h4
    have h1 : (u * u) * (u * u) = 1 := by
      have := pow_orderOf_eq_one u
      rw [h4] at this
      calc (u * u) * (u * u) = u ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    rcases hz.unique (u * u) (K.mul_mem hu hu) h1 with h | h
    · exfalso
      have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [h4] at this
      omega
    · exact h
  let a₀ : ↥R := e.symm (QuaternionGroup.a 1)
  let b₀ : ↥R := e.symm (QuaternionGroup.xa 0)
  have hord : ∀ q : QuaternionGroup 2, orderOf q = 4 → orderOf ((e.symm q : ↥R) : G) = 4 := by
    intro q hq
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hq]
  have ha4 : orderOf (a₀ : G) = 4 := hord _ (by simp [QuaternionGroup.orderOf_a_one])
  have hb4 : orderOf (b₀ : G) = 4 := hord _ (QuaternionGroup.orderOf_xa _)
  have hab4 : orderOf ((a₀ * b₀ : ↥R) : G) = 4 := by
    have : a₀ * b₀ = e.symm (QuaternionGroup.xa (0 - 1)) := by
      simp only [a₀, b₀, ← map_mul, QuaternionGroup.a_mul_xa]
    rw [this]
    exact hord _ (QuaternionGroup.orderOf_xa _)
  have hne : a₀ * b₀ ≠ b₀ * a₀ := by
    intro h
    have h' : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
      apply e.symm.injective
      simpa only [a₀, b₀, map_mul] using h
    revert h'
    decide
  refine ⟨(a₀ : G), a₀.2, (b₀ : G), b₀.2, ⟨?_, ?_, ?_, fun h => hne (Subtype.ext h)⟩⟩
  · exact sq4 _ (hRK a₀.2) ha4
  · exact sq4 _ (hRK b₀.2) hb4
  · exact sq4 _ (hRK (R.mul_mem a₀.2 b₀.2)) hab4

theorem u3_caseA {N S T T' : Subgroup G} {z α α' β : G} (hz2 : z * z = 1)
    (hTS : T ≤ S) (hT'S : T' ≤ S) (hTT' : ∀ p ∈ T, ∀ q ∈ T', p * q = q * p)
    (hα : α ∈ T) (hα' : α' ∈ T) (hβ : β ∈ T')
    (hsqα : α * α = z) (hsqα' : α' * α' = z) (hsqβ : β * β = z) (hne : α * α' ≠ α' * α)
    (hxN : α * β ∈ N) (hyN : α' * β ∈ N) :
    ∃ x ∈ N, ∃ y ∈ N, x ∈ S ∧ y ∈ S ∧ x * x = 1 ∧ y * y = 1 ∧ x * y ≠ y * x := by
  have hcα : β * α = α * β := (hTT' α hα β hβ).symm
  have hcα' : β * α' = α' * β := (hTT' α' hα' β hβ).symm
  refine ⟨α * β, hxN, α' * β, hyN, S.mul_mem (hTS hα) (hT'S hβ), S.mul_mem (hTS hα') (hT'S hβ),
    ?_, ?_, ?_⟩
  · calc α * β * (α * β) = α * (β * α) * β := by group
      _ = α * (α * β) * β := by rw [hcα]
      _ = (α * α) * (β * β) := by group
      _ = z * z := by rw [hsqα, hsqβ]
      _ = 1 := hz2
  · calc α' * β * (α' * β) = α' * (β * α') * β := by group
      _ = α' * (α' * β) * β := by rw [hcα']
      _ = (α' * α') * (β * β) := by group
      _ = z * z := by rw [hsqα', hsqβ]
      _ = 1 := hz2
  · have hxy : α * β * (α' * β) = α * α' * z := by
      calc α * β * (α' * β) = α * (β * α') * β := by group
        _ = α * (α' * β) * β := by rw [hcα']
        _ = α * α' * (β * β) := by group
        _ = α * α' * z := by rw [hsqβ]
    have hyx : α' * β * (α * β) = α' * α * z := by
      calc α' * β * (α * β) = α' * (β * α) * β := by group
        _ = α' * (α * β) * β := by rw [hcα]
        _ = α' * α * (β * β) := by group
        _ = α' * α * z := by rw [hsqβ]
    intro h
    rw [hxy, hyx] at h
    exact hne (mul_right_cancel h)

theorem u3_pair_noncomm {N S T T' : Subgroup G} {z a b a' b' : G}
    (hzN : z ∈ N) (hz2 : z * z = 1)
    (hc2 : ∀ x ∈ S, ∀ y ∈ S, x * x ∈ N → y * y ∈ N → x ∈ N ∨ y ∈ N ∨ x * y ∈ N)
    (hTS : T ≤ S) (hT'S : T' ≤ S) (hTT' : ∀ p ∈ T, ∀ q ∈ T', p * q = q * p)
    (ha : a ∈ T) (hb : b ∈ T) (ha' : a' ∈ T') (hb' : b' ∈ T')
    (hQ : U3QTriple z a b) (hQ' : U3QTriple z a' b') :
    ∃ x ∈ N, ∃ y ∈ N, x ∈ S ∧ y ∈ S ∧ x * x = 1 ∧ y * y = 1 ∧ x * y ≠ y * x := by
  have hTT'' : ∀ p ∈ T', ∀ q ∈ T, p * q = q * p := fun p hp q hq => (hTT' q hq p hp).symm
  have hab' : a' * b' ∈ T' := T'.mul_mem ha' hb'
  have hab : a * b ∈ T := T.mul_mem ha hb
  have hsqa : a * a ∈ N := by rw [hQ.sq_a]; exact hzN
  have hsqb : b * b ∈ N := by rw [hQ.sq_b]; exact hzN
  have hsqa' : a' * a' ∈ N := by rw [hQ'.sq_a]; exact hzN
  have hsqb' : b' * b' ∈ N := by rw [hQ'.sq_b]; exact hzN
  by_cases hI : a ∈ N ∧ b ∈ N
  ·
    obtain ⟨haN, hbN⟩ := hI
    rcases hc2 a' (hT'S ha') b' (hT'S hb') hsqa' hsqb' with h | h | h
    · exact u3_caseA hz2 hTS hT'S hTT' ha hb ha' hQ.sq_a hQ.sq_b hQ'.sq_a hQ.ne
        (N.mul_mem haN h) (N.mul_mem hbN h)
    · exact u3_caseA hz2 hTS hT'S hTT' ha hb hb' hQ.sq_a hQ.sq_b hQ'.sq_b hQ.ne
        (N.mul_mem haN h) (N.mul_mem hbN h)
    · exact u3_caseA hz2 hTS hT'S hTT' ha hb hab' hQ.sq_a hQ.sq_b hQ'.sq_ab hQ.ne
        (N.mul_mem haN h) (N.mul_mem hbN h)
  · by_cases hII : a' ∈ N ∧ b' ∈ N
    ·
      obtain ⟨ha'N, hb'N⟩ := hII
      rcases hc2 a (hTS ha) b (hTS hb) hsqa hsqb with h | h | h
      · exact u3_caseA (T := T') (T' := T) hz2 hT'S hTS hTT'' ha' hb' ha hQ'.sq_a hQ'.sq_b hQ.sq_a
          hQ'.ne (N.mul_mem ha'N h) (N.mul_mem hb'N h)
      · exact u3_caseA (T := T') (T' := T) hz2 hT'S hTS hTT'' ha' hb' hb hQ'.sq_a hQ'.sq_b hQ.sq_b
          hQ'.ne (N.mul_mem ha'N h) (N.mul_mem hb'N h)
      · exact u3_caseA (T := T') (T' := T) hz2 hT'S hTS hTT'' ha' hb' hab hQ'.sq_a hQ'.sq_b hQ.sq_ab
          hQ'.ne (N.mul_mem ha'N h) (N.mul_mem hb'N h)
    ·
      obtain ⟨β, hβT, hsqβ, hβN⟩ : ∃ β ∈ T', β * β = z ∧ β ∉ N := by
        by_cases h : a' ∈ N
        · exact ⟨b', hb', hQ'.sq_b, fun hb'N => hII ⟨h, hb'N⟩⟩
        · exact ⟨a', ha', hQ'.sq_a, h⟩
      obtain ⟨α, α', hαT, hα'T, hsqα, hsqα', hne, hαN, hα'N⟩ :
          ∃ α α' : G, α ∈ T ∧ α' ∈ T ∧ α * α = z ∧ α' * α' = z ∧ α * α' ≠ α' * α ∧ α ∉ N ∧
            α' ∉ N := by
        by_cases h1 : a ∈ N
        · have hbN : b ∉ N := fun hb'' => hI ⟨h1, hb''⟩
          have habN : a * b ∉ N := fun h2 => hbN (by
            have := N.mul_mem (N.inv_mem h1) h2
            simpa using this)
          exact ⟨b, a * b, hb, hab, hQ.sq_b, hQ.sq_ab, hQ.ne_right, hbN, habN⟩
        · by_cases h2 : b ∈ N
          · have habN : a * b ∉ N := fun h3 => h1 (by
              have := N.mul_mem h3 (N.inv_mem h2)
              simpa using this)
            exact ⟨a, a * b, ha, hab, hQ.sq_a, hQ.sq_ab, hQ.ne_left, h1, habN⟩
          · exact ⟨a, b, ha, hb, hQ.sq_a, hQ.sq_b, hQ.ne, h1, h2⟩
      have hsqα'' : α * α ∈ N := by rw [hsqα]; exact hzN
      have hsqα''' : α' * α' ∈ N := by rw [hsqα']; exact hzN
      have hsqβ' : β * β ∈ N := by rw [hsqβ]; exact hzN
      have hxN : α * β ∈ N := by
        rcases hc2 α (hTS hαT) β (hT'S hβT) hsqα'' hsqβ' with h | h | h
        · exact absurd h hαN
        · exact absurd h hβN
        · exact h
      have hyN : α' * β ∈ N := by
        rcases hc2 α' (hTS hα'T) β (hT'S hβT) hsqα''' hsqβ' with h | h | h
        · exact absurd h hα'N
        · exact absurd h hβN
        · exact h
      exact u3_caseA hz2 hTS hT'S hTT' hαT hα'T hβT hsqα hsqα' hsqβ hne hxN hyN

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW
