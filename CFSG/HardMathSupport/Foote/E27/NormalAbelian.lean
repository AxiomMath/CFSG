module

public import CFSG.HardMathSupport.Foote.E27.SporKill

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

theorem card_le_card_ker_pow_three {M : Type*} [CommGroup M] [Finite M] (φ : M →* M)
    (h3 : ∀ x, φ (φ (φ x)) = 1) : Nat.card M ≤ Nat.card φ.ker ^ 3 := by
  have h1 := Subgroup.card_ker_mul_card_range φ
  set M1 : Subgroup M := φ.range with hM1
  let φ1 : M1 →* M := φ.comp M1.subtype
  have h2 := Subgroup.card_ker_mul_card_range φ1
  have hk1 : Nat.card φ1.ker ≤ Nat.card φ.ker := by
    refine Nat.card_le_card_of_injective (fun x => ⟨(x : M1).1, x.2⟩) ?_
    intro x y hxy
    have h : ((x : M1) : M) = ((y : M1) : M) := by simpa using congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hr1 : Nat.card φ1.range ≤ Nat.card φ.ker := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := x.2
    rw [MonoidHom.mem_ker]
    change φ (φ x.1) = 1
    rw [← hy]
    exact h3 y
  have hM1card : Nat.card M1 ≤ Nat.card φ.ker ^ 2 := by
    rw [← h2, pow_two]
    exact Nat.mul_le_mul hk1 hr1
  rw [← h1, pow_succ, pow_two]
  have := Nat.mul_le_mul_left (Nat.card φ.ker) hM1card
  nlinarith [this]

theorem cube_aux {M : Type*} [CommGroup M] (a b c : M) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) :
    a * c⁻¹ * (c * b⁻¹)⁻¹ * (c * b⁻¹ * (b * a⁻¹)⁻¹)⁻¹ = 1 := by
  have h : a * c⁻¹ * (c * b⁻¹)⁻¹ * (c * b⁻¹ * (b * a⁻¹)⁻¹)⁻¹ =
      (a * a⁻¹) * (b ^ 3) * (c ^ 3)⁻¹ := by
    simp only [mul_inv_rev, inv_inv, pow_succ, pow_zero, one_mul]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [h, hb, hc]; simp

theorem card_le_card_inf_centralizer_pow {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1)
    {s : G} (hs3 : s ^ 3 = 1) (hnorm : ∀ a ∈ A, s * a * s⁻¹ ∈ A) :
    Nat.card A ≤ Nat.card ↥(A ⊓ centralizer ({s} : Set G)) ^ 3 := by
  let _ : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hρ : ∀ a b : A, (⟨s * (a * b : A) * s⁻¹, hnorm _ (a * b : A).2⟩ : A) =
      ⟨s * a * s⁻¹, hnorm a a.2⟩ * ⟨s * b * s⁻¹, hnorm b b.2⟩ := fun a b =>
    Subtype.ext (by
      change s * (a * b : G) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹)
      group)
  let ρ : A →* A := MonoidHom.mk' (fun a => ⟨s * a * s⁻¹, hnorm a a.2⟩) hρ
  have hρ3 : ∀ a : A, ρ (ρ (ρ a)) = a := fun a => Subtype.ext (by
    change s * (s * (s * a * s⁻¹) * s⁻¹) * s⁻¹ = a
    have h3 : s * s * s = 1 := by
      rw [pow_succ, pow_two] at hs3; exact hs3
    have : s * (s * (s * (a : G) * s⁻¹) * s⁻¹) * s⁻¹ = (s * s * s) * a * (s * s * s)⁻¹ := by
      group
    rw [this, h3]; group)
  have hcube : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by
    change (a : G) ^ 3 = 1
    exact hexp a a.2)
  let φ : A →* A := MonoidHom.mk' (fun a => ρ a * a⁻¹) fun a b => by
    rw [map_mul, mul_inv_rev]; simp only [mul_comm, mul_left_comm, mul_assoc]
  have hφ3 : ∀ x, φ (φ (φ x)) = 1 := by
    intro x
    simp only [φ, MonoidHom.mk'_apply, map_mul, map_inv, hρ3]
    exact cube_aux x (ρ x) (ρ (ρ x)) (hcube _) (hcube _)
  have h := card_le_card_ker_pow_three φ hφ3
  have hker : Nat.card φ.ker = Nat.card ↥(A ⊓ centralizer ({s} : Set G)) := by
    refine Nat.card_congr ⟨fun x => ⟨(x.1 : G), x.1.2, ?_⟩, fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩, ?_, ?_⟩
    · have := x.2
      rw [MonoidHom.mem_ker] at this
      show (x.1 : G) ∈ centralizer ({s} : Set G)
      rw [mem_centralizer_singleton_iff]
      have h' : ρ x.1 * (x.1)⁻¹ = 1 := this
      have h'' := congrArg Subtype.val h'
      change s * (x.1 : G) * s⁻¹ * ((x.1 : G))⁻¹ = 1 at h''
      have : s * (x.1 : G) = (x.1 : G) * s := by
        have := mul_inv_eq_one.mp h''
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      exact this.symm
    · rw [MonoidHom.mem_ker]
      have hy : (y : G) ∈ centralizer ({s} : Set G) := y.2.2
      rw [mem_centralizer_singleton_iff] at hy
      apply Subtype.ext
      change s * (y : G) * s⁻¹ * (y : G)⁻¹ = 1
      rw [mul_inv_eq_one, ← hy]
      group
    · intro x; rfl
    · intro y; rfl
  rw [hker] at h
  exact h

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_normal_abelian (h : E27Config X K R T z) (hz : z ∈ K)
    (S₀ : Sylow 3 ↥K) (A : Subgroup ↥K) (hAS : A ≤ (S₀ : Subgroup ↥K))
    (hnorm : ∀ s ∈ (S₀ : Subgroup ↥K), ∀ a ∈ A, s * a * s⁻¹ ∈ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1)
    (hcard : 3 ^ 7 ≤ Nat.card A) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine h.false_of_sylow_kill hz S₀ fun s hs hord => Or.inl ?_
  have hs3 : s ^ 3 = 1 := hord ▸ pow_orderOf_eq_one s
  have hQp : IsPGroup 3 ↥((S₀ : Subgroup ↥K) ⊓ Subgroup.centralizer ({s} : Set ↥K)) :=
    S₀.isPGroup'.to_le inf_le_left
  obtain ⟨q, hq⟩ := hQp.exists_card_eq
  rw [hq]
  have hAp : IsPGroup 3 A := S₀.isPGroup'.to_le hAS
  obtain ⟨a, ha⟩ := hAp.exists_card_eq
  rw [ha] at hcard
  have ha7 : 7 ≤ a := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  have h81 : (81 : ℕ) = 3 ^ 4 := by norm_num
  rw [h81]
  by_cases hsA : s ∈ A
  · have hAQ : A ≤ (S₀ : Subgroup ↥K) ⊓ Subgroup.centralizer ({s} : Set ↥K) := fun x hx =>
      ⟨hAS hx, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx s hsA)⟩
    have hd := Subgroup.card_dvd_of_le hAQ
    rw [ha, hq] at hd
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd
    exact pow_dvd_pow 3 (by omega)
  · set B : Subgroup ↥K := A ⊓ Subgroup.centralizer ({s} : Set ↥K) with hB
    have hBS : B ≤ (S₀ : Subgroup ↥K) := inf_le_left.trans hAS
    have hBQ : B < (S₀ : Subgroup ↥K) ⊓ Subgroup.centralizer ({s} : Set ↥K) := by
      refine lt_of_le_of_ne (inf_le_inf_right _ hAS) fun e => ?_
      have : s ∈ B := by
        rw [e]
        exact ⟨hs, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      exact hsA this.1
    have hlt := Subgroup.card_lt_of_lt hBQ
    obtain ⟨b, hb⟩ := (S₀.isPGroup'.to_le hBS).exists_card_eq
    have hpow := card_le_card_inf_centralizer_pow A hcomm hexp hs3 (hnorm s hs)
    rw [ha, ← hB, hb, ← pow_mul] at hpow
    have hb3 : a ≤ b * 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
    rw [hb, hq] at hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
    exact pow_dvd_pow 3 (by omega)

end CFSG.HardMathSupport.Foote.E27

end
