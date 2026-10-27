module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverCore

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Subgroup CFSG.Assembly.LowTwoRank

section Powers

variable {P : Type*} [Group P] {K : Subgroup P} (hK : K ≤ center P)
include hK

@[expose] def powers (n : ℕ) : Subgroup P where
  carrier := {z | ∃ x ∈ K, z = x ^ n}
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, K.mul_mem hx hy,
      ((show Commute x y from (mem_center_iff.mp (hK hy) x)).mul_pow n).symm⟩
  one_mem' := ⟨1, K.one_mem, (one_pow n).symm⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, K.inv_mem hx, (inv_pow x n).symm⟩

theorem mem_powers {n : ℕ} {z : P} : z ∈ powers hK n ↔ ∃ x ∈ K, z = x ^ n :=
  Iff.rfl

theorem powers_le (n : ℕ) : powers hK n ≤ K := by
  rintro _ ⟨x, hx, rfl⟩
  exact K.pow_mem hx n

theorem sq_eq_one_of_forall_sq_eq_pow_four [Finite P] (h2 : IsPGroup 2 K)
    (h : ∀ x ∈ K, ∃ y ∈ K, x ^ 2 = y ^ 4) : ∀ x ∈ K, x ^ 2 = 1 := by
  set S := powers hK 2
  have hSK : S ≤ K := powers_le hK 2
  set f : S → S := fun s => ⟨(s : P) ^ 2, S.pow_mem s.2 2⟩ with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h x hx
    refine ⟨⟨y ^ 2, y, hy, rfl⟩, Subtype.ext ?_⟩
    change (y ^ 2) ^ 2 = x ^ 2
    rw [← pow_mul, hxy]
  have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hsurj
  have key : ∀ n : ℕ, ∀ t ∈ S, t ^ 2 ^ n = 1 → t = 1 := by
    intro n
    induction n with
    | zero => intro t _ ht; rwa [pow_zero, pow_one] at ht
    | succ n ih =>
      intro t ht htn
      have ht2 : t ^ 2 = 1 :=
        ih (t ^ 2) (S.pow_mem ht 2) (by rw [← pow_mul, ← pow_succ']; exact htn)
      have := hinj (a₁ := ⟨t, ht⟩) (a₂ := 1) (Subtype.ext (by
        change t ^ 2 = (1 : P) ^ 2
        rw [ht2, one_pow]))
      exact congrArg Subtype.val this
  intro x hx
  obtain ⟨n, hn⟩ := h2 ⟨x ^ 2, K.pow_mem hx 2⟩
  exact key n (x ^ 2) ⟨x, hx, rfl⟩ (congrArg Subtype.val hn)

end Powers


theorem forall_sq_eq_pow_four {P : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    (η : P →* StatedSp 3 (ZMod 2)) (hη : Function.Surjective η) (hK : η.ker ≤ center P) :
    ∀ x ∈ η.ker, ∃ y ∈ η.ker, x ^ 2 = y ^ 4 := by
  set D := powers hK 4 with hD
  have : D.Normal := Subgroup.normal_of_le_center ((powers_le hK 4).trans hK)
  have hDle : D ≤ η.ker := powers_le hK 4
  set θ := QuotientGroup.lift D η hDle with hθ
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨y, rfl⟩ := hη x
    exact ⟨y, QuotientGroup.lift_mk _ _ _⟩
  have hθmk : ∀ y : P, θ (y : P ⧸ D) = η y := fun y => QuotientGroup.lift_mk _ _ _
  have hθC : θ.ker ≤ center (P ⧸ D) := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [MonoidHom.mem_ker, hθmk] at hc
      refine mem_center_iff.mpr fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp (hK hc) g]
  have h4 : ∀ c, θ c = 1 → c ^ 4 = 1 := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [hθmk] at hc
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨y, hc, rfl⟩
  intro x hx
  have hsq := kernel_sq_eq_one hθsurj hθC h4 (c := (x : P ⧸ D)) (by rw [hθmk]; exact hx)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hsq
  exact hsq

theorem binary_symplectic_six_perfect_central_two_kernel_elementary {P : Type*} {Q : Type}
    [Group P] [Group Q] [Finite P] [Group.IsPerfect P] (η : P →* Q)
    (hη : Function.Surjective η) (hK : η.ker ≤ center P) (h2 : IsPGroup 2 η.ker)
    (hQ : CFSG.Blueprint.LieModel Q .PSp 3 2 1) : CFSG.IsElementaryAbelian 2 η.ker := by
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSp_of_lieModel hQ
  set η' : P →* StatedSp 3 (ZMod 2) := e.toMonoidHom.comp η with hη'
  have hker : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hsq := sq_eq_one_of_forall_sq_eq_pow_four hK h2 (by
    have := forall_sq_eq_pow_four η' (e.surjective.comp hη) (hker ▸ hK)
    rwa [hker] at this)
  refine { is_comm := ⟨fun u v => Subtype.ext (mem_center_iff.mp (hK v.2) u)⟩
           exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
             Subtype.ext (by simpa using hsq x x.2) }

theorem binary_symplectic_six_kernel_sq_eq_one {P : Type*} {Q : Type}
    [Group P] [Group Q] [Finite P] [Group.IsPerfect P] (η : P →* Q)
    (hη : Function.Surjective η) (hK : η.ker ≤ center P) (h2 : IsPGroup 2 η.ker)
    (hQ : CFSG.Blueprint.LieModel Q .PSp 3 2 1) : ∀ x ∈ η.ker, x ^ 2 = 1 := by
  have := binary_symplectic_six_perfect_central_two_kernel_elementary η hη hK h2 hQ
  exact fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
