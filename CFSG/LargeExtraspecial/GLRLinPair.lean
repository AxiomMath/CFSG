module

public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

structure Pair (S : Setting G) (X : Subgroup S.O) (A B : Submodule (ZMod 2) S.Qt) : Prop where
  q_A : ∀ v ∈ A, S.q v = 0
  q_B : ∀ v ∈ B, S.q v = 0
  inf_eq : A ⊓ B = ⊥
  sup_eq : A ⊔ B = ⊤
  finrank_A : finrank (ZMod 2) A = S.width
  finrank_B : finrank (ZMod 2) B = S.width
  apply_A : ∀ x ∈ X, ∀ v ∈ A, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ A
  apply_B : ∀ x ∈ X, ∀ v ∈ B, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ B
  card : Nat.card X = Nat.card (GL (Fin S.width) (ZMod 2))

omit [Finite G] in
theorem two_vec (v : S.Qt) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 :=
  (zmod2_eq_zero_or_one c).resolve_left h

namespace Pair

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}

theorem symm (h : Pair S X A B) : Pair S X B A :=
  ⟨h.q_B, h.q_A, by rw [inf_comm]; exact h.inf_eq, by rw [sup_comm]; exact h.sup_eq,
    h.finrank_B, h.finrank_A, h.apply_B, h.apply_A, h.card⟩

theorem polar_A (h : Pair S X A B) {u v : S.Qt} (hu : u ∈ A) (hv : v ∈ A) :
    polar S.q u v = 0 := by
  have h1 : polar S.q u v = S.q (u + v) - S.q u - S.q v := rfl
  rw [h1, h.q_A _ (A.add_mem hu hv), h.q_A u hu, h.q_A v hv, sub_zero, sub_zero]

theorem mem_A_of_polar (h : Pair S X A B) {v : S.Qt} (hv : ∀ a ∈ A, polar S.q a v = 0) :
    v ∈ A := by
  set P := LinearMap.BilinForm.orthogonal S.q.polarBilin A
  have hAP : A ≤ P := fun u hu => (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun w hw => by
    change S.q.polarBilin w u = 0
    exact h.polar_A hw hu
  have hdim := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate A
  have hQ := S.finrank_Qt_eq_two_mul_width
  have hPA : A = P := Submodule.eq_of_le_of_finrank_eq hAP (by
    change finrank (ZMod 2) A = finrank (ZMod 2) P
    rw [hdim, h.finrank_A, hQ]; omega)
  rw [hPA]
  exact (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun w hw => hv w hw

theorem eq_zero_of_polar (h : Pair S X A B) {b : S.Qt} (hb : b ∈ B)
    (hA : ∀ a ∈ A, polar S.q a b = 0) : b = 0 := by
  have hb' : b ∈ A ⊓ B := ⟨h.mem_A_of_polar hA, hb⟩
  rw [h.inf_eq] at hb'
  exact (Submodule.mem_bot _).mp hb'

theorem exists_polar_eq_one (h : Pair S X A B) {b : S.Qt} (hb : b ∈ B) (hb0 : b ≠ 0) :
    ∃ a ∈ A, polar S.q a b = 1 := by
  by_contra hc
  push Not at hc
  exact hb0 (h.eq_zero_of_polar hb fun a ha => by
    rcases zmod2_eq_zero_or_one (polar S.q a b) with e | e
    · exact e
    · exact absurd e (hc a ha))

theorem exists_polar_eq (h : Pair S X A B) (f : A →ₗ[ZMod 2] ZMod 2) :
    ∃ b ∈ B, ∀ a : A, polar S.q a b = f a := by
  let Φ : B →ₗ[ZMod 2] Module.Dual (ZMod 2) A :=
    A.subtype.dualMap ∘ₗ (S.q.polarBilin.flip ∘ₗ B.subtype)
  have hΦ : ∀ (b : B) (a : A), Φ b a = polar S.q a b := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have := h.eq_zero_of_polar b.2 fun a ha => by
      rw [← hΦ b ⟨a, ha⟩, hb]
      rfl
    exact Subtype.ext this
  have hdim : finrank (ZMod 2) B = finrank (ZMod 2) (Module.Dual (ZMod 2) A) := by
    rw [Subspace.dual_finrank_eq, h.finrank_A, h.finrank_B]
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj f
  exact ⟨b, b.2, fun a => by rw [← hΦ, hb]⟩

theorem exists_polar_sep (h : Pair S X A B) {U : Submodule (ZMod 2) S.Qt} (hU : U ≤ A)
    {a : S.Qt} (ha : a ∈ A) (haU : a ∉ U) :
    ∃ b ∈ B, (∀ u ∈ U, polar S.q u b = 0) ∧ polar S.q a b = 1 := by
  obtain ⟨f, hfa, hUf⟩ := Submodule.exists_le_ker_of_notMem haU
  obtain ⟨b, hb, hfb⟩ := h.exists_polar_eq (f ∘ₗ A.subtype)
  refine ⟨b, hb, fun u hu => ?_, ?_⟩
  · rw [show u = ((⟨u, hU hu⟩ : A) : S.Qt) from rfl, hfb]
    exact hUf hu
  · rw [show a = ((⟨a, ha⟩ : A) : S.Qt) from rfl, hfb]
    exact zmod2_eq_one_of_ne_zero hfa

theorem map_A_eq (h : Pair S X A B) {x : S.O} (hx : x ∈ X) :
    A.map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = A := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
  rintro _ ⟨v, hv, rfl⟩
  exact h.apply_A x hx v hv

theorem exists_apply_eq (h : Pair S X A B) {x : S.O} (hx : x ∈ X) {a : S.Qt} (ha : a ∈ A) :
    ∃ a' ∈ A, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a' = a := by
  have ha' : a ∈ A.map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    rw [h.map_A_eq hx]; exact ha
  obtain ⟨a', ha', e⟩ := ha'
  exact ⟨a', ha', e⟩

theorem apply_eq_iff (h : Pair S X A B) {x : S.O} (hx : x ∈ X) {b b' : S.Qt} (hb : b ∈ B)
    (hb' : b' ∈ B) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b = b' ↔
      ∀ a ∈ A, polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) a) b' = polar S.q a b := by
  constructor
  · rintro rfl a _
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2 a b
  · intro hpol
    have hd : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b' = 0 := by
      refine h.eq_zero_of_polar (B.sub_mem (h.apply_B x hx b hb) hb') fun a ha => ?_
      obtain ⟨a', ha', rfl⟩ := h.exists_apply_eq hx ha
      rw [polar_sub_right, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2,
        hpol a' ha', sub_self]
    exact sub_eq_zero.mp hd

theorem apply_eq_self_iff (h : Pair S X A B) {x : S.O} (hx : x ∈ X) {b : S.Qt} (hb : b ∈ B) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b = b ↔
      ∀ a ∈ A, polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) a) b = polar S.q a b :=
  h.apply_eq_iff hx hb hb

theorem ext_of_eqOn (h : Pair S X A B) {x y : S.O} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : ∀ a ∈ A, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = (y : S.Qt ≃ₗ[ZMod 2] S.Qt) a) : x = y := by
  have hB : ∀ b ∈ B, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b = (y : S.Qt ≃ₗ[ZMod 2] S.Qt) b := by
    intro b hb
    have hyb := h.apply_B y hy b hb
    refine (h.apply_eq_iff hx hb hyb).mpr fun a ha => ?_
    rw [hxy a ha]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup y.2 a b
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  have hv : v ∈ A ⊔ B := by rw [h.sup_eq]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, map_add, hxy a ha, hB b hb]

end Pair

end CFSG.LargeExtraspecial.GLR
