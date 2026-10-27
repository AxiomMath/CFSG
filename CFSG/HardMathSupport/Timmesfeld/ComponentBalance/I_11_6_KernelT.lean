module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def KernelT : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J → CFSG.Open.IsKGroup J →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ U : Subgroup J, U ≤ Subgroup.center J ∧ CFSG.Open.IsElemAbelian p U ∧
        Nat.card U = p ^ 2) →
      ∀ φ : MulAut J, IsPGroup p (Subgroup.zpowers φ) → ∃ g : J, ∀ t, φ t = g * t * g⁻¹

section Alt

variable {X : Type*} [Group X] {p : ℕ}

theorem i116t_inv {L : Subgroup X} {a b : X} (haL : a ∈ L)
    (hab : ∀ l ∈ L, a * l * a⁻¹ = b * l * b⁻¹) : ∀ l ∈ L, a⁻¹ * l * a = b⁻¹ * l * b := by
  intro l hl
  have h1 : a⁻¹ * l * a ∈ L := L.mul_mem (L.mul_mem (L.inv_mem haL) hl) haL
  have h2 := hab _ h1
  calc a⁻¹ * l * a = b⁻¹ * (b * (a⁻¹ * l * a) * b⁻¹) * b := by group
    _ = b⁻¹ * (a * (a⁻¹ * l * a) * a⁻¹) * b := by rw [h2]
    _ = b⁻¹ * l * b := by group

theorem i116t_pow {L : Subgroup X} {a b : X}
    (hbN : b ∈ Subgroup.normalizer (L : Set X))
    (hab : ∀ l ∈ L, a * l * a⁻¹ = b * l * b⁻¹) (n : ℕ) :
    ∀ l ∈ L, a ^ n * l * (a ^ n)⁻¹ = b ^ n * l * (b ^ n)⁻¹ := by
  induction n with
  | zero => intro l _; simp
  | succ n ih =>
    intro l hl
    have h1 : b ^ n * l * (b ^ n)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hbN n) l).1 hl
    calc a ^ (n + 1) * l * (a ^ (n + 1))⁻¹
        = a * (a ^ n * l * (a ^ n)⁻¹) * a⁻¹ := by rw [pow_succ']; group
      _ = a * (b ^ n * l * (b ^ n)⁻¹) * a⁻¹ := by rw [ih l hl]
      _ = b * (b ^ n * l * (b ^ n)⁻¹) * b⁻¹ := hab _ h1
      _ = b ^ (n + 1) * l * (b ^ (n + 1))⁻¹ := by rw [pow_succ']; group

theorem i116t_core [hp : Fact p.Prime] {B L : Subgroup X} (hB : IsSCp p ⊤ B)
    (hBL : B ≤ Subgroup.normalizer (L : Set X))
    (hact : ∀ b ∈ B, ∃ j ∈ L, ∀ l ∈ L, b * l * b⁻¹ = j * l * j⁻¹)
    {a b : X} (haL : a ∈ L) (hbB : b ∈ B) (hab : ∀ l ∈ L, a * l * a⁻¹ = b * l * b⁻¹) :
    ∀ b' ∈ B, a * b' * a⁻¹ ∈ B := by
  intro b' hb'
  have hmem : ∀ g ∈ Subgroup.normalizer (L : Set X), ∀ l ∈ L, g * l * g⁻¹ ∈ L :=
    fun g hg l hl => (Subgroup.mem_normalizer_iff.1 hg l).1 hl
  have hmem' : ∀ g ∈ Subgroup.normalizer (L : Set X), ∀ l ∈ L, g⁻¹ * l * g ∈ L :=
    fun g hg l hl => by simpa using hmem g⁻¹ (inv_mem hg) l hl
  have hab' := i116t_inv haL hab
  have hcomm : b * b' = b' * b :=
    congrArg Subtype.val (hB.2.1.1.is_comm.comm (⟨b, hbB⟩ : B) ⟨b', hb'⟩)
  set z : X := a * b' * a⁻¹ * b'⁻¹ with hz
  have hzL : z ∈ L := by
    have : z = a * (b' * a⁻¹ * b'⁻¹) := by simp only [hz]; group
    rw [this]
    exact L.mul_mem haL (hmem b' (hBL hb') a⁻¹ (L.inv_mem haL))
  have hzc : ∀ l ∈ L, z * l = l * z := by
    intro l hl
    have hl1 : b'⁻¹ * l * b' ∈ L := hmem' b' (hBL hb') l hl
    have hl3 : b' * (b⁻¹ * (b'⁻¹ * l * b') * b) * b'⁻¹ ∈ L :=
      hmem b' (hBL hb') _ (hmem' b (hBL hbB) _ hl1)
    have e1 : z * l * z⁻¹ =
        a * (b' * (a⁻¹ * (b'⁻¹ * l * b') * a) * b'⁻¹) * a⁻¹ := by simp only [hz]; group
    rw [hab' _ hl1, hab _ hl3] at e1
    have hc : b * b' * b⁻¹ * b'⁻¹ = 1 := by rw [hcomm]; group
    have e2 : b * (b' * (b⁻¹ * (b'⁻¹ * l * b') * b) * b'⁻¹) * b⁻¹ =
        (b * b' * b⁻¹ * b'⁻¹) * l * (b * b' * b⁻¹ * b'⁻¹)⁻¹ := by group
    rw [e2, hc] at e1
    simp only [inv_one, one_mul, mul_one] at e1
    exact mul_inv_eq_iff_eq_mul.1 e1
  have hzB : ∀ c ∈ B, c * z * c⁻¹ = z := by
    intro c hc
    obtain ⟨j, hjL, hj⟩ := hact c hc
    rw [hj z hzL]
    exact mul_inv_eq_iff_eq_mul.2 (hzc j hjL).symm
  have hzp : z ^ p = 1 := by
    have h1 : a * b' * a⁻¹ = z * b' := by simp only [hz]; group
    have h2 : (a * b' * a⁻¹) ^ p = 1 := by
      rw [conj_pow, hB.2.1.2 b' hb']; simp
    have hc : Commute z b' := by
      have := hzB b' hb'
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [h1, hc.mul_pow, hB.2.1.2 b' hb', mul_one] at h2
    exact h2
  have hzmem : z ∈ B := by
    by_cases hz1 : z = 1
    · rw [hz1]; exact B.one_mem
    · refine mem_of_mem_centralizer_orderOf_eq_prime hB ?_ (orderOf_eq_prime hzp hz1)
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact mul_inv_eq_iff_eq_mul.1 (hzB c hc)
  have : a * b' * a⁻¹ = z * b' := by simp only [hz]; group
  rw [this]
  exact B.mul_mem hzmem hb'

theorem i116t_alt [hp : Fact p.Prime] {B L : Subgroup X} (hB : IsSCp p ⊤ B)
    (hBL : B ≤ Subgroup.normalizer (L : Set X))
    (hact : ∀ b ∈ B, ∃ j ∈ L, ∀ l ∈ L, b * l * b⁻¹ = j * l * j⁻¹)
    (hZp : IsPGroup p ↥(Subgroup.center ↥L)) :
    (∃ a ∈ L, a ∈ Subgroup.normalizer (B : Set X) ∧ (∃ n : ℕ, a ^ (p ^ n) = 1) ∧
      ∃ l ∈ L, a * l ≠ l * a) ∨ ∀ b ∈ B, ∀ l ∈ L, b * l = l * b := by
  classical
  by_cases h : ∃ a ∈ L, (∃ b ∈ B, ∀ l ∈ L, a * l * a⁻¹ = b * l * b⁻¹) ∧
      ∃ l ∈ L, a * l ≠ l * a
  · left
    obtain ⟨a, haL, ⟨b, hbB, hab⟩, hnc⟩ := h
    refine ⟨a, haL, ?_, ?_, hnc⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h'
      refine ⟨fun hh => i116t_core hB hBL hact haL hbB hab h' hh, fun hh => ?_⟩
      have := i116t_core hB hBL hact (a := a⁻¹) (b := b⁻¹) (L.inv_mem haL) (B.inv_mem hbB)
        (fun l hl => by rw [inv_inv, inv_inv]; exact i116t_inv haL hab l hl) _ hh
      simpa [mul_assoc] using this
    · have hpow := i116t_pow (hBL hbB) hab p
      have hbp : b ^ p = 1 := hB.2.1.2 b hbB
      have hzc : (⟨a ^ p, L.pow_mem haL p⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        have := hpow y y.2
        rw [hbp] at this
        simp only [inv_one, mul_one, one_mul] at this
        exact (mul_inv_eq_iff_eq_mul.1 this).symm
      obtain ⟨k, hk⟩ := hZp ⟨_, hzc⟩
      refine ⟨k + 1, ?_⟩
      have := congrArg (fun y : ↥(Subgroup.center ↥L) => ((y : ↥L) : X)) hk
      simp only [OneMemClass.coe_one] at this
      rw [pow_succ', pow_mul]
      exact this
  · right
    intro b hb l hl
    obtain ⟨j, hjL, hj⟩ := hact b hb
    have hjc : j * l = l * j := by
      by_contra hne
      exact h ⟨j, hjL, ⟨b, hb, fun l hl => (hj l hl).symm⟩, l, hl, hne⟩
    have h1 : j * l * j⁻¹ = l := by rw [hjc]; group
    have := hj l hl
    rw [h1] at this
    exact mul_inv_eq_iff_eq_mul.1 this

end Alt

theorem i116t_exists_noncentral_pElt {J : Type*} [Group J] [Finite J]
    (hJ : CFSG.Open.IsQuasisimple J) {p : ℕ} (hp : p.Prime) (Q : Sylow p J)
    (hdvd : p ∣ Nat.card J) : ∃ x ∈ (Q : Subgroup J), x ∉ Subgroup.center J := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  have hQc : ∀ q ∈ (Q : Subgroup J), ∀ g : J, g * q = q * g := fun q hq g =>
    (Subgroup.mem_center_iff.1 (hcon q hq) g)
  have hN : Subgroup.normalizer (Q : Set J) ≤ Subgroup.centralizer (Q : Set J) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hQc h hh g).symm
  have hcomm : IsMulCommutative (Q : Subgroup J) :=
    ⟨⟨fun a b => Subtype.ext (hQc b b.2 a)⟩⟩
  set f := MonoidHom.transferSylow Q hN with hf
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← hJ.1, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact (commutatorElement_eq_one_iff_mul_comm.2 (hcomm.is_comm.comm (f g₁) (f g₂)))
  have hcard : ¬ p ∣ Nat.card f.ker := MonoidHom.not_dvd_card_ker_transferSylow Q hN
  rw [hker, Nat.card_congr (Subgroup.topEquiv (G := J)).toEquiv] at hcard
  exact hcard hdvd

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
