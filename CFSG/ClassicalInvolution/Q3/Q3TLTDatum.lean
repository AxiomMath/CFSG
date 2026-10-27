module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RThmI
public import CFSG.ClassicalInvolution.SmallCases.NobqTransfer

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution

structure TightDatum {G : Type*} [Group G] (R : Subgroup G) (S : Sylow 2 R) (t : G) : Prop where
  quat : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))
  mem : t ∈ (S : Subgroup R).map R.subtype
  order : orderOf t = 2
  cent : R ≤ Subgroup.centralizer ({t} : Set G)
  normal : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal
  twoGroup : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R)

namespace TightDatum

variable {G : Type*} [Group G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem mem_right (h : TightDatum R S t) : t ∈ R :=
  Subgroup.map_subtype_le _ h.mem

theorem le_normalizer (h : TightDatum R S t) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (R : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.cent).mp h.normal

theorem eq_of_orderOf_eq_two [Finite G] (h : TightDatum R S t) {u : G} (hu : u ∈ R)
    (hu2 : orderOf u = 2) : u = t := by
  obtain ⟨r, hr, ⟨e⟩⟩ := h.quat
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact Nobq.eq_of_orderOf_eq_two_of_datum S e h.mem h.order h.cent hu hu2

theorem sylow_nonabelian [Finite G] (h : TightDatum R S t) (Q : Sylow 2 R) :
    ∃ x ∈ (Q : Subgroup R), ∃ y ∈ (Q : Subgroup R), x * y ≠ y * x := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq R S Q
  obtain ⟨r, hr, ⟨e⟩⟩ := h.quat
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h2 : 2 ≤ 2 ^ (r - 2) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨a, b, hab⟩ := Nobq.exists_not_commute_of_mulEquiv_quaternionGroup h2 e
  refine ⟨g * a * g⁻¹, ?_, g * b * g⁻¹, ?_, fun hc => hab ?_⟩
  · exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr (by simp [mul_assoc])
  · exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr (by simp [mul_assoc])
  · have := congrArg (fun x => g⁻¹ * x * g) hc
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at this
    exact Subtype.ext this

theorem thmIHyp [Finite G] (h : TightDatum R S t) : Hat2A7R.ThmIHyp R t := by
  have hCR := h.le_normalizer
  refine ⟨h.order, h.mem_right, isSubnormal_of_normal_subgroupOf h.cent h.normal, ?_, ?_, ?_, ?_⟩
  · intro w hw hw2
    exact h.eq_of_orderOf_eq_two hw hw2
  · exact h.sylow_nonabelian
  · intro k hk _ _ g hg
    exact hCR hg
  · intro g hg hgn
    exact absurd (hCR hg) hgn

end TightDatum

theorem isSubnormal_of_inf_centralizer {G : Type*} [Group G] {C E J : Subgroup G}
    (hEC : E ≤ C) (hEn : (E.subgroupOf C).Normal)
    (hJ : IsSubnormal J (C ⊓ Subgroup.centralizer (E : Set G))) : IsSubnormal J C := by
  have hle : C ⊓ Subgroup.centralizer (E : Set G) ≤ C := inf_le_left
  have heq : (C ⊓ Subgroup.centralizer (E : Set G)).subgroupOf C =
      Subgroup.centralizer ((E.subgroupOf C : Subgroup C) : Set C) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe]
    constructor
    · rintro ⟨-, hx⟩ ⟨e, he⟩ he'
      have := hx e (by simpa using he')
      exact Subtype.ext (by simpa using this)
    · intro hx
      refine ⟨x.2, fun e he => ?_⟩
      have := hx ⟨e, hEC he⟩ (by simpa [Subgroup.mem_subgroupOf] using he)
      simpa using congrArg Subtype.val this
  have hn : ((C ⊓ Subgroup.centralizer (E : Set G)).subgroupOf C).Normal := by
    rw [heq]
    have := hEn
    infer_instance
  exact isSubnormal_trans hJ (IsSubnormal.step hle hn (IsSubnormal.refl C))

end CFSG.ClassicalInvolution.Q3
