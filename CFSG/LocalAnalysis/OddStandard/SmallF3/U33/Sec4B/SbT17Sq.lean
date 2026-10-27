module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G]

private lemma mul_comm_of_mem {A : Subgroup G} (hA : IsMulCommutative A) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x := by
  have h := hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  simpa using congrArg Subtype.val h

private lemma conj_conj_eq_self {t x : G} (ht2 : t * t = 1) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_right ht2).symm
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
    _ = (t * t) * x * (t * t) := by rw [htinv]
    _ = x := by rw [ht2]; group

private def psi (A : Subgroup G) (t : G) (hA : IsMulCommutative A)
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) : ↥A →* ↥A :=
  MonoidHom.mk'
    (fun a => ⟨(a : G) * (t * (a : G) * t⁻¹), A.mul_mem a.2 (htA (a : G) a.2)⟩)
    (fun a b => by
      apply Subtype.ext
      show ((a : G) * (b : G)) * (t * ((a : G) * (b : G)) * t⁻¹)
          = ((a : G) * (t * (a : G) * t⁻¹)) * ((b : G) * (t * (b : G) * t⁻¹))
      rw [show t * ((a : G) * (b : G)) * t⁻¹
            = (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹) by group]
      have hcomm : (b : G) * (t * (a : G) * t⁻¹) = (t * (a : G) * t⁻¹) * (b : G) :=
        mul_comm_of_mem hA b.2 (htA (a : G) a.2)
      calc ((a : G) * (b : G)) * ((t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹))
          = (a : G) * ((b : G) * (t * (a : G) * t⁻¹)) * (t * (b : G) * t⁻¹) := by group
        _ = (a : G) * ((t * (a : G) * t⁻¹) * (b : G)) * (t * (b : G) * t⁻¹) := by rw [hcomm]
        _ = ((a : G) * (t * (a : G) * t⁻¹)) * ((b : G) * (t * (b : G) * t⁻¹)) := by group)

private lemma psi_comm_t {A : Subgroup G} {t x : G} (ht2 : t * t = 1)
    (hA : IsMulCommutative A) (hx : x ∈ A) (hu : t * x * t⁻¹ ∈ A) :
    (x * (t * x * t⁻¹)) * t = t * (x * (t * x * t⁻¹)) := by
  have hcomm : (t * x * t⁻¹) * x = x * (t * x * t⁻¹) := mul_comm_of_mem hA hu hx
  have hfix : t * (x * (t * x * t⁻¹)) * t⁻¹ = x * (t * x * t⁻¹) := by
    calc t * (x * (t * x * t⁻¹)) * t⁻¹
        = (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by group
      _ = (t * x * t⁻¹) * x := by rw [conj_conj_eq_self ht2]
      _ = x * (t * x * t⁻¹) := hcomm
  have hgoal : t * (x * (t * x * t⁻¹)) = (x * (t * x * t⁻¹)) * t := by
    calc t * (x * (t * x * t⁻¹)) = t * (x * (t * x * t⁻¹)) * t⁻¹ * t := by group
      _ = (x * (t * x * t⁻¹)) * t := by rw [hfix]
  exact hgoal.symm

theorem card_le_sq_card_centralizer {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) {t : G}
    (ht2 : t * t = 1) (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) :
    Nat.card A ≤ Nat.card ↥(A ⊓ centralizer ({t} : Set G)) ^ 2 := by
  classical
  by_cases hAfin : Finite A
  · haveI : Finite A := hAfin
    let ψ : ↥A →* ↥A := psi A t hA.1 htA
    have hmul := Subgroup.card_ker_mul_card_range ψ
    have hker : ψ.ker ≤ (A ⊓ centralizer ({t} : Set G)).subgroupOf A := by
      intro x hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx1 : (x : G) * (t * (x : G) * t⁻¹) = 1 := by
        have h := MonoidHom.mem_ker.mp hx
        have h2 : ((ψ x : ↥A) : G) = 1 := by rw [h]; simp
        exact h2
      have hx2 : (x : G)⁻¹ = (x : G) := by
        have hp : (x : G) * (x : G) = 1 := by simpa [pow_two] using hA.2 (x : G) x.2
        exact (eq_inv_of_mul_eq_one_right hp).symm
      have hconj : t * (x : G) * t⁻¹ = (x : G) := by
        have h := eq_inv_of_mul_eq_one_right hx1
        rwa [hx2] at h
      calc (x : G) * t = (t * (x : G) * t⁻¹) * t := by rw [hconj]
        _ = t * (x : G) := by group
    have hrange : ψ.range ≤ (A ⊓ centralizer ({t} : Set G)).subgroupOf A := by
      rintro y ⟨x, rfl⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨(ψ x).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      show (x : G) * (t * (x : G) * t⁻¹) * t = t * ((x : G) * (t * (x : G) * t⁻¹))
      exact psi_comm_t ht2 hA.1 x.2 (htA (x : G) x.2)
    have hcardC : Nat.card ↥((A ⊓ centralizer ({t} : Set G)).subgroupOf A)
        = Nat.card ↥(A ⊓ centralizer ({t} : Set G)) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ centralizer ({t} : Set G) ≤ A)).toEquiv
    have h1 : Nat.card ψ.ker ≤ Nat.card ↥(A ⊓ centralizer ({t} : Set G)) :=
      hcardC ▸ Subgroup.card_le_of_le hker
    have h2 : Nat.card ψ.range ≤ Nat.card ↥(A ⊓ centralizer ({t} : Set G)) :=
      hcardC ▸ Subgroup.card_le_of_le hrange
    calc Nat.card A = Nat.card ψ.ker * Nat.card ψ.range := hmul.symm
      _ ≤ Nat.card ↥(A ⊓ centralizer ({t} : Set G))
            * Nat.card ↥(A ⊓ centralizer ({t} : Set G)) := Nat.mul_le_mul h1 h2
      _ = Nat.card ↥(A ⊓ centralizer ({t} : Set G)) ^ 2 := (pow_two _).symm
  · haveI : Infinite A := not_finite_iff_infinite.mp hAfin
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
