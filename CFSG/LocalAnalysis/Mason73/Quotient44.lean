module

public import CFSG.CharacterTheory.Semidihedral.QuaternionAutomorphismLifting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCentralQuotient

public section

namespace CFSG.LocalAnalysis.Mason73

open Subgroup CFSG.Semidihedral.QuaternionAutomorphismLifting

variable {X : Type*} [Group X]

theorem zpowers_normal_of_mem_center {z : X} (hz : z ∈ center X) : (zpowers z).Normal :=
  ⟨fun a ha g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    have hk : z ^ k ∈ center X := zpow_mem hz k
    rw [mem_center_iff.1 hk g, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers z) k⟩

theorem mem_zpowers_iff_of_orderOf_eq_two {z x : X} (hz : orderOf z = 2) :
    x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have h2 : z ^ (2 : ℕ) = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    rw [zpow_eq_zpow_emod' k h2]
    have hk : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
    rcases hk with hk | hk <;> rw [hk]
    · exact Or.inl (zpow_zero z)
    · exact Or.inr (zpow_one z)
  · rintro (h | h) <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers z

theorem card_zpowers_of_orderOf_eq_two {z : X} (hz : orderOf z = 2) :
    Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers, hz]

variable {Q₁ Q₂ : Subgroup X} {z : X}

theorem mem_zpowers_of_mul_mem (hinf : Q₁ ⊓ Q₂ = zpowers z) {a b : X} (ha : a ∈ Q₁)
    (hb : b ∈ Q₂) (hab : a * b ∈ zpowers z) : a ∈ zpowers z ∧ b ∈ zpowers z := by
  have hZ2 : zpowers z ≤ Q₂ := hinf ▸ inf_le_right
  have ha2 : a ∈ Q₂ := by
    have := mul_mem (hZ2 hab) (inv_mem hb)
    rwa [mul_inv_cancel_right] at this
  have haZ : a ∈ zpowers z := hinf ▸ ⟨ha, ha2⟩
  refine ⟨haZ, ?_⟩
  have := mul_mem (inv_mem haZ) hab
  rwa [inv_mul_cancel_left] at this

theorem ker_dihedralProjection_comp {Q : Subgroup X} {k : ℕ} (hk : 1 ≤ k)
    (e : Q ≃* QuaternionGroup (2 ^ k)) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    ((dihedralProjection (2 ^ k)).comp e.toMonoidHom).ker = (zpowers z).subgroupOf Q := by
  have hm : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hez : e ⟨z, hzQ⟩ = QuaternionGroup.a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) := by
    refine (unique_involution (2 ^ k) (by positivity) _).1 ?_
    rw [MulEquiv.orderOf_eq, orderOf_mk, hz]
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, dihedralProjection_ker _ hm,
    center_iff _ hm, mem_subgroupOf, mem_zpowers_iff_of_orderOf_eq_two hz]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← hez, ← map_one e, e.injective.eq_iff, e.injective.eq_iff, Subtype.ext_iff,
    Subtype.ext_iff]
  rfl

theorem dihedralProjection_comp_surjective {Q : Subgroup X} {k : ℕ}
    (e : Q ≃* QuaternionGroup (2 ^ k)) :
    Function.Surjective ((dihedralProjection (2 ^ k)).comp e.toMonoidHom) :=
  (dihedralProjection_surjective _).comp e.surjective

theorem nonempty_map_sup_mulEquiv_dihedral [hN : (zpowers z).Normal]
    (hcomm : Q₂ ≤ centralizer (Q₁ : Set X)) (hinf : Q₁ ⊓ Q₂ = zpowers z) (hz : orderOf z = 2)
    {k : ℕ} (hk : 1 ≤ k) (e₁ : Q₁ ≃* QuaternionGroup (2 ^ k))
    (e₂ : Q₂ ≃* QuaternionGroup (2 ^ k)) :
    Nonempty ((Q₁ ⊔ Q₂).map (QuotientGroup.mk' (zpowers z)) ≃*
      DihedralGroup (2 ^ k) × DihedralGroup (2 ^ k)) := by
  set N := zpowers z with hNdef
  have hz1 : z ∈ Q₁ := (hinf.symm ▸ mem_zpowers z : z ∈ Q₁ ⊓ Q₂).1
  have hz2 : z ∈ Q₂ := (hinf.symm ▸ mem_zpowers z : z ∈ Q₁ ⊓ Q₂).2
  let f₁ : Q₁ →* X ⧸ N := (QuotientGroup.mk' N).comp Q₁.subtype
  let f₂ : Q₂ →* X ⧸ N := (QuotientGroup.mk' N).comp Q₂.subtype
  have hc : ∀ (a : Q₁) (b : Q₂), Commute (f₁ a) (f₂ b) := fun a b => by
    change (QuotientGroup.mk' N) (a : X) * (QuotientGroup.mk' N) (b : X) =
      (QuotientGroup.mk' N) (b : X) * (QuotientGroup.mk' N) (a : X)
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (hcomm b.2) a a.2]
  let F : Q₁ × Q₂ →* X ⧸ N := f₁.noncommCoprod f₂ hc
  have hrange : F.range = (Q₁ ⊔ Q₂).map (QuotientGroup.mk' N) := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.map_sup, MonoidHom.range_comp, MonoidHom.range_comp,
      range_subtype, range_subtype]
  let φ₁ : Q₁ →* DihedralGroup (2 ^ k) := (dihedralProjection (2 ^ k)).comp e₁.toMonoidHom
  let φ₂ : Q₂ →* DihedralGroup (2 ^ k) := (dihedralProjection (2 ^ k)).comp e₂.toMonoidHom
  let Φ : Q₁ × Q₂ →* DihedralGroup (2 ^ k) × DihedralGroup (2 ^ k) := φ₁.prodMap φ₂
  have hΦ : Function.Surjective Φ := fun ⟨d₁, d₂⟩ => by
    obtain ⟨a, ha⟩ := dihedralProjection_comp_surjective e₁ d₁
    obtain ⟨b, hb⟩ := dihedralProjection_comp_surjective e₂ d₂
    exact ⟨(a, b), Prod.ext ha hb⟩
  have hker : F.ker = Φ.ker := by
    ext ⟨a, b⟩
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply, Prod.ext_iff]
    change (QuotientGroup.mk' N) (a : X) * (QuotientGroup.mk' N) (b : X) = 1 ↔
      φ₁ a = 1 ∧ φ₂ b = 1
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← MonoidHom.mem_ker,
      ← MonoidHom.mem_ker, ker_dihedralProjection_comp hk e₁ hz1 hz,
      ker_dihedralProjection_comp hk e₂ hz2 hz, mem_subgroupOf, mem_subgroupOf]
    constructor
    · exact mem_zpowers_of_mul_mem hinf a.2 b.2
    · rintro ⟨ha, hb⟩
      exact mul_mem ha hb
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange F).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective Φ hΦ)))⟩

theorem commutator_quotient_eq_top {N : Subgroup X} [N.Normal] (hperf : commutator X = ⊤) :
    commutator (X ⧸ N) = ⊤ := by
  have hs : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  rw [eq_top_iff, ← map_top_of_surjective _ hs, ← hperf, _root_.commutator_def,
    _root_.commutator_def, map_commutator, map_top_of_surjective _ hs]

theorem oddCore_quotient_zpowers_eq_bot [Finite X] [(zpowers z).Normal]
    (hO : CFSG.Open.classicalInvolutionOddCore X = ⊥) (hz : z ∈ center X) (hz2 : orderOf z = 2) :
    CFSG.Open.classicalInvolutionOddCore (X ⧸ zpowers z) = ⊥ :=
  CFSG.ComponentClassification.AschbacherStrongEmbedding.oddCore_central_quotient_eq_bot hO _
    ((zpowers_le (H := center X)).2 hz) (card_zpowers_of_orderOf_eq_two hz2)

end CFSG.LocalAnalysis.Mason73
