module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalEightCoverCore
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCover

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace OrthogonalEightCover

open Matrix OrthogonalSplit CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem kernel_sq_eq_one (hK : Nat.card K = 2) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] {θ : E →* orthElementaryGroup (quadPlus 4 K)}
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
    (h4 : ∀ c, θ c = 1 → c ^ 4 = 1) {c : E} (hc : θ c = 1) : c ^ 2 = 1 := by
  have hr : 3 ≤ 4 := by norm_num
  have hcomp : (leviTwo 4 K hr).comp SpecialLinearGroup.toGL = leviSLTwo 4 K hr :=
    MonoidHom.ext (leviTwo_toGL hr)
  obtain ⟨S, hS, hVUR⟩ := exists_sylow_leviSLTwo_radicalTwo hr hK
  rw [← hcomp] at hS hVUR
  exact kernel_sq_eq_one_of_model (leviTwo 4 K hr) (leviTwo_injective hr) (radicalTwo 4 K)
    radicalTwo_injective altCongr coe_altCongr (leviTwo_mul_radicalTwo_mul_inv hr) S hS hVUR
    hθ hC h4 hc

theorem forall_sq_eq_pow_four (hK : Nat.card K = 2) {P : Type*} [Group P] [Finite P]
    [Group.IsPerfect P] (η : P →* orthElementaryGroup (quadPlus 4 K))
    (hη : Function.Surjective η) (hK' : η.ker ≤ Subgroup.center P) :
    ∀ x ∈ η.ker, ∃ y ∈ η.ker, x ^ 2 = y ^ 4 := by
  set D := BinarySymplecticSix.powers hK' 4 with hD
  have : D.Normal :=
    Subgroup.normal_of_le_center ((BinarySymplecticSix.powers_le hK' 4).trans hK')
  have hDle : D ≤ η.ker := BinarySymplecticSix.powers_le hK' 4
  set θ := QuotientGroup.lift D η hDle with hθ
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨y, rfl⟩ := hη x
    exact ⟨y, QuotientGroup.lift_mk _ _ _⟩
  have hθmk : ∀ y : P, θ (y : P ⧸ D) = η y := fun y => QuotientGroup.lift_mk _ _ _
  have hθC : θ.ker ≤ Subgroup.center (P ⧸ D) := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [MonoidHom.mem_ker, hθmk] at hc
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hK' hc) g]
  have h4 : ∀ c, θ c = 1 → c ^ 4 = 1 := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [hθmk] at hc
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨y, hc, rfl⟩
  intro x hx
  have hsq := kernel_sq_eq_one hK hθsurj hθC h4 (c := (x : P ⧸ D)) (by rw [hθmk]; exact hx)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hsq
  exact hsq

theorem kernel_sq_eq_one_of_isPGroup (hK : Nat.card K = 2) {P : Type*} [Group P] [Finite P]
    [Group.IsPerfect P] (η : P →* orthElementaryGroup (quadPlus 4 K))
    (hη : Function.Surjective η) (hK' : η.ker ≤ Subgroup.center P) (h2 : IsPGroup 2 η.ker) :
    ∀ x ∈ η.ker, x ^ 2 = 1 :=
  BinarySymplecticSix.sq_eq_one_of_forall_sq_eq_pow_four hK' h2
    (forall_sq_eq_pow_four hK η hη hK')

end OrthogonalEightCover

open OrthogonalEightCover OrthogonalSplit

theorem binary_split_orthogonal_eight_perfect_central_two_kernel_elementary {P : Type*} {Q : Type}
    [Group P] [Group Q] [Finite P] [Group.IsPerfect P] (η : P →* Q)
    (hη : Function.Surjective η) (hK : η.ker ≤ Subgroup.center P) (h2 : IsPGroup 2 η.ker)
    (hQ : CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1) : CFSG.IsElementaryAbelian 2 η.ker := by
  obtain ⟨F, _, _, _, hcard, -, ⟨e⟩⟩ := exists_mulEquiv_elementaryGroup_of_lieModel hQ
  have hF : Nat.card F = 2 := by rw [hcard, pow_one]
  set η' := e.toMonoidHom.comp η with hη'
  have hker : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hsq : ∀ x ∈ η.ker, x ^ 2 = 1 := by
    have := kernel_sq_eq_one_of_isPGroup hF η' (e.surjective.comp hη) (hker ▸ hK) (hker ▸ h2)
    rwa [hker] at this
  exact { is_comm := ⟨fun u v => Subtype.ext (Subgroup.mem_center_iff.mp (hK v.2) u)⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
            Subtype.ext (by simpa using hsq x x.2) }

end CFSG.LocalAnalysis.ComponentInitial
