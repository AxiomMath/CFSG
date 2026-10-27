module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.A6Leaf
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbAlt

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

section CommCalc

variable {G : Type*} [Group G]

theorem pow_mul_pow_comm {x y ω : G} (hω : ω ∈ Subgroup.center G) (hxy : x * y = ω * (y * x))
    (a b : ℕ) : x ^ a * y ^ b = ω ^ (a * b) * (y ^ b * x ^ a) := by
  have hc : ∀ (n : ℕ) (g : G), g * ω ^ n = ω ^ n * g := fun n g =>
    Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hω n) g
  have hcω : ∀ g : G, g * ω = ω * g := fun g => by simpa using hc 1 g
  have step1 : ∀ b : ℕ, x * y ^ b = ω ^ b * (y ^ b * x) := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      have e1 : y ^ b * (ω * (y * x)) = ω * (y ^ b * (y * x)) := by
        rw [← mul_assoc, hcω, mul_assoc]
      calc x * y ^ (b + 1) = (x * y ^ b) * y := by rw [pow_succ, mul_assoc]
        _ = (ω ^ b * (y ^ b * x)) * y := by rw [ih]
        _ = ω ^ b * (y ^ b * (x * y)) := by simp only [mul_assoc]
        _ = ω ^ b * (y ^ b * (ω * (y * x))) := by rw [hxy]
        _ = ω ^ b * (ω * (y ^ b * (y * x))) := by rw [e1]
        _ = ω ^ (b + 1) * (y ^ (b + 1) * x) := by
              rw [← mul_assoc, ← pow_succ, pow_succ y b]; simp only [mul_assoc]
  induction a with
  | zero => simp
  | succ a ih =>
    have e2 : x * (ω ^ (a * b) * (y ^ b * x ^ a)) = ω ^ (a * b) * (x * (y ^ b * x ^ a)) := by
      rw [← mul_assoc, hc, mul_assoc]
    calc x ^ (a + 1) * y ^ b = x * (x ^ a * y ^ b) := by rw [pow_succ', mul_assoc]
      _ = x * (ω ^ (a * b) * (y ^ b * x ^ a)) := by rw [ih]
      _ = ω ^ (a * b) * (x * (y ^ b * x ^ a)) := e2
      _ = ω ^ (a * b) * ((x * y ^ b) * x ^ a) := by simp only [mul_assoc]
      _ = ω ^ (a * b) * ((ω ^ b * (y ^ b * x)) * x ^ a) := by rw [step1 b]
      _ = ω ^ (a * b) * (ω ^ b * (y ^ b * (x * x ^ a))) := by simp only [mul_assoc]
      _ = ω ^ ((a + 1) * b) * (y ^ b * x ^ (a + 1)) := by
            rw [← mul_assoc, ← pow_add, add_mul, one_mul, pow_succ' x a]

theorem comm_relation {x y ω : G} (hω : ω ∈ Subgroup.center G) (hxy : x * y = ω * (y * x))
    (a b c d : ℕ) :
    ω ^ (b * c) * ((x ^ a * y ^ b) * (x ^ c * y ^ d)) =
      ω ^ (a * d) * ((x ^ c * y ^ d) * (x ^ a * y ^ b)) := by
  have hc : ∀ (n : ℕ) (g : G), g * ω ^ n = ω ^ n * g := fun n g =>
    Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hω n) g
  have h1 : ω ^ (b * c) * (y ^ b * x ^ c) = x ^ c * y ^ b := by
    rw [pow_mul_pow_comm hω hxy c b, mul_comm c b]
  have h2 : ω ^ (a * d) * (y ^ d * x ^ a) = x ^ a * y ^ d := by
    rw [pow_mul_pow_comm hω hxy a d]
  have e3 : ω ^ (b * c) * ((x ^ a * y ^ b) * (x ^ c * y ^ d)) =
      x ^ a * (ω ^ (b * c) * (y ^ b * x ^ c)) * y ^ d := by
    calc ω ^ (b * c) * ((x ^ a * y ^ b) * (x ^ c * y ^ d))
        = (ω ^ (b * c) * x ^ a) * (y ^ b * x ^ c) * y ^ d := by simp only [mul_assoc]
      _ = (x ^ a * ω ^ (b * c)) * (y ^ b * x ^ c) * y ^ d := by rw [← hc (b * c) (x ^ a)]
      _ = x ^ a * (ω ^ (b * c) * (y ^ b * x ^ c)) * y ^ d := by simp only [mul_assoc]
  have e4 : x ^ c * (ω ^ (a * d) * (y ^ d * x ^ a)) * y ^ b =
      ω ^ (a * d) * ((x ^ c * y ^ d) * (x ^ a * y ^ b)) := by
    calc x ^ c * (ω ^ (a * d) * (y ^ d * x ^ a)) * y ^ b
        = (x ^ c * ω ^ (a * d)) * (y ^ d * x ^ a) * y ^ b := by simp only [mul_assoc]
      _ = (ω ^ (a * d) * x ^ c) * (y ^ d * x ^ a) * y ^ b := by rw [hc (a * d) (x ^ c)]
      _ = ω ^ (a * d) * ((x ^ c * y ^ d) * (x ^ a * y ^ b)) := by simp only [mul_assoc]
  rw [e3, h1, ← e4, h2]
  calc x ^ a * (x ^ c * y ^ b) * y ^ d = x ^ (a + c) * y ^ (b + d) := by
        rw [pow_add, pow_add]; simp only [mul_assoc]
    _ = x ^ (c + a) * y ^ (d + b) := by rw [add_comm a c, add_comm b d]
    _ = x ^ c * (x ^ a * y ^ d) * y ^ b := by rw [pow_add, pow_add]; simp only [mul_assoc]

end CommCalc

section Split

theorem center_eq_bot_of_det
    {J Lg : Type} [Group J] [Finite J] [Group Lg] [Group.IsPerfect J]
    (hZ : IsPGroup 3 (Subgroup.center J)) (q : J →* Lg) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center J) (eL : Lg ≃* alternatingGroup (Fin 6))
    (τ : MulAut J) (hτZ : ∀ z ∈ Subgroup.center J, τ z = z)
    (E : Subgroup Lg) (hEcard : Nat.card E = 9) (x y : J)
    (hgen : ∀ g ∈ E, ∃ i j : ℕ, g = q x ^ i * q y ^ j) (hxy : q x * q y = q y * q x)
    (a b c d : ℕ) (hτx : q (τ x) = q x ^ a * q y ^ b) (hτy : q (τ y) = q x ^ c * q y ^ d)
    (hdet : a * d ≡ b * c + 2 [MOD 3]) : Subgroup.center J = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcenLg : Subgroup.center Lg = ⊥ := center_eq_bot_of_equiv_alt6 eL
  have hZker : Subgroup.center J ≤ q.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have : q z ∈ Subgroup.center Lg := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨u, rfl⟩ := hq g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz u]
    rw [hcenLg] at this
    exact Subgroup.mem_bot.1 this
  have hkerEq : q.ker = Subgroup.center J := le_antisymm hker hZker
  let e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)).trans eL
  rcases Amb.alt6_center_cases hZ e with hbot | hZ3
  · exact hbot
  exfalso
  have hHat : IsHatSix J := ⟨Group.IsPerfect.commutator_eq_top (G := J), hZ3, ⟨e⟩⟩
  obtain ⟨ω, hωdef⟩ : ∃ ω : J, ω = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hωker : ω ∈ q.ker := by
    rw [MonoidHom.mem_ker, hωdef]
    simp only [map_mul, map_inv]
    rw [hxy]
    group
  have hωZ : ω ∈ Subgroup.center J := hker hωker
  have hω3 : ω ^ 3 = 1 := by
    have h1 : (⟨ω, hωZ⟩ : Subgroup.center J) ^ Nat.card (Subgroup.center J) = 1 :=
      pow_card_eq_one'
    rw [hZ3] at h1
    exact congrArg Subtype.val h1
  have hcen : ∀ (z : J), z ∈ Subgroup.center J → ∀ g : J, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.1 hz g
  obtain ⟨P, hP⟩ : ∃ P : J, P = x ^ a * y ^ b := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : J, Q = x ^ c * y ^ d := ⟨_, rfl⟩
  obtain ⟨z₁, hz₁def⟩ : ∃ z : J, z = P⁻¹ * τ x := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂def⟩ : ∃ z : J, z = Q⁻¹ * τ y := ⟨_, rfl⟩
  have hz₁ : z₁ ∈ Subgroup.center J := by
    apply hker
    rw [MonoidHom.mem_ker, hz₁def, map_mul, map_inv, hτx, hP]
    simp
  have hz₂ : z₂ ∈ Subgroup.center J := by
    apply hker
    rw [MonoidHom.mem_ker, hz₂def, map_mul, map_inv, hτy, hQ]
    simp
  have hτx' : τ x = P * z₁ := by rw [hz₁def]; group
  have hτy' : τ y = Q * z₂ := by rw [hz₂def]; group
  have hxyω : x * y = ω * (y * x) := by rw [hωdef]; group
  have hτrel : τ x * τ y = ω * (τ y * τ x) := by
    have := congrArg τ hxyω
    rw [map_mul, map_mul, map_mul, hτZ ω hωZ] at this
    exact this
  have hrel : ω ^ (b * c) * (P * Q) = ω ^ (a * d) * (Q * P) := by
    rw [hP, hQ]
    exact comm_relation hωZ hxyω a b c d
  have hexp : ω ^ (a * d) = ω ^ (b * c + 2) := by
    rw [pow_eq_pow_mod (a * d) hω3, pow_eq_pow_mod (b * c + 2) hω3]
    exact congrArg (fun n => ω ^ n) hdet
  have hPQ : P * Q = ω ^ 2 * (Q * P) := by
    rw [hexp, pow_add, mul_assoc] at hrel
    exact mul_left_cancel hrel
  have h1 : τ x * τ y = ω ^ 2 * (τ y * τ x) := by
    rw [hτx', hτy']
    calc P * z₁ * (Q * z₂) = P * (z₁ * Q) * z₂ := by simp only [mul_assoc]
      _ = P * (Q * z₁) * z₂ := by rw [← hcen z₁ hz₁ Q]
      _ = (P * Q) * (z₁ * z₂) := by simp only [mul_assoc]
      _ = (ω ^ 2 * (Q * P)) * (z₁ * z₂) := by rw [hPQ]
      _ = ω ^ 2 * (Q * P * (z₁ * z₂)) := by simp only [mul_assoc]
      _ = ω ^ 2 * (Q * P * (z₂ * z₁)) := by rw [hcen z₁ hz₁ z₂]
      _ = ω ^ 2 * (Q * (P * z₂) * z₁) := by simp only [mul_assoc]
      _ = ω ^ 2 * (Q * (z₂ * P) * z₁) := by rw [hcen z₂ hz₂ P]
      _ = ω ^ 2 * (Q * z₂ * (P * z₁)) := by simp only [mul_assoc]
  have h2 : ω ^ 2 * (τ y * τ x) = ω * (τ y * τ x) := by rw [← h1, hτrel]
  have hω1 : ω = 1 := by
    have h3 : ω ^ 2 = ω := mul_right_cancel h2
    have h4 : ω * ω = ω * 1 := by rw [mul_one, ← pow_two]; exact h3
    exact mul_left_cancel h4
  have hxyc : x * y = y * x := by
    rw [hω1, one_mul] at hxyω
    exact hxyω
  have hLg : Nat.card Lg = 360 := by
    rw [Nat.card_congr eL.toEquiv]
    exact Amb.card_alt6
  have hJcard : Nat.card J = 1080 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)
    rw [Nat.card_congr e.toEquiv, Amb.card_alt6, hZ3] at h
    omega
  have hEidx : E.index = 40 := by
    have h := Subgroup.card_mul_index E
    rw [hEcard, hLg] at h
    omega
  set W : Subgroup J := E.comap q with hW
  have hWidx : W.index = 40 := by
    rw [hW, Subgroup.index_comap_of_surjective E hq]
    exact hEidx
  have hWcard : Nat.card W = 27 := by
    have h := Subgroup.card_mul_index W
    rw [hWidx, hJcard] at h
    omega
  have hfac : (1080 : ℕ).factorization 3 = 3 := by decide +kernel
  have hsyl : Nat.card W = 3 ^ (Nat.card J).factorization 3 := by
    rw [hWcard, hJcard, hfac]
    norm_num
  obtain ⟨-, ⟨r, hr, s, hs, hrs⟩, -⟩ := t112m_sylow_hatSix hHat (Sylow.ofCard W hsyl)
  rw [Sylow.coe_ofCard W hsyl] at hr hs
  apply hrs
  have hdec : ∀ g ∈ W, ∃ (g₀ z : J), (∃ i j : ℕ, g₀ = x ^ i * y ^ j) ∧ z ∈ Subgroup.center J ∧
      g = g₀ * z := by
    intro g hg
    obtain ⟨i, j, hij⟩ := hgen (q g) hg
    refine ⟨x ^ i * y ^ j, (x ^ i * y ^ j)⁻¹ * g, ⟨i, j, rfl⟩, ?_, by group⟩
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hij]
    simp
  obtain ⟨r₀, zr, ⟨i, j, hr₀⟩, hzr, hrr⟩ := hdec r hr
  obtain ⟨s₀, zs, ⟨i', j', hs₀⟩, hzs, hss⟩ := hdec s hs
  have hcx : Commute x y := hxyc
  have hcc : ∀ z ∈ Subgroup.center J, ∀ g : J, Commute z g := fun z hz g => (hcen z hz g).symm
  have h0 : Commute r₀ s₀ := by
    rw [hr₀, hs₀]
    exact ((((Commute.refl x).pow_pow i i').mul_right (hcx.pow_pow i j')).mul_left
      (((hcx.symm.pow_pow j i').mul_right ((Commute.refl y).pow_pow j j'))))
  have h1' : Commute r s := by
    rw [hrr, hss]
    exact (h0.mul_right (hcc zs hzs r₀).symm).mul_left (hcc zr hzr (s₀ * zs))
  exact h1'.eq

end Split

end CFSG.HardMathSupport.Dickson.I271
