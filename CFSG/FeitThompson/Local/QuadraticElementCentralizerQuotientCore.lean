module

public import CFSG.FeitThompson.Local.SolvableBaerSuzuki
public import CFSG.FeitThompson.Local.TwoQuadraticElementsPrimePowerAutomorphisms
import CFSG.FeitThompson.Representations.QuadraticPrimeElementsPrimePowerImage
import CFSG.FeitThompson.Local.ExponentPrimeRankTwoOrderCube

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup SemidirectProduct

variable {G : Type*} [Group G] {p : ℕ}

section Quadratic

variable {A B P : Type*} [Group A] [Group B] [Group P]

theorem ActsQuadratically.apply_eq {ρ : A →* MulAut P} {a : A} (h : ActsQuadratically ρ a) {w : P}
    (hw : w ∈ displacementSubgroup ρ a) : ρ a w = w := by
  have h1 := actsQuadratically_iff_commutator_eq_bot.1 h
  rw [commutator_range_inl_zpowers_inr, commutator_map_inl_zpowers_inr_eq_bot_iff] at h1
  exact h1 w hw

theorem ActsQuadratically.conj {ρ : A →* MulAut P} {a : A} (h : ActsQuadratically ρ a) (b : A) :
    ActsQuadratically ρ (b⁻¹ * a * b) := by
  rw [actsQuadratically_iff_forall] at h ⊢
  intro v
  have hb : ρ b⁻¹ = (ρ b).symm := by rw [map_inv]; rfl
  have key : ∀ u : P, ρ (b⁻¹ * a * b) u = (ρ b).symm (ρ a (ρ b u)) := fun u => by
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hb]
  rw [key, key]
  have hσ : ρ b (v⁻¹ * (ρ b).symm (ρ a (ρ b v))) = (ρ b v)⁻¹ * ρ a (ρ b v) := by
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [hσ, h (ρ b v), map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem ActsQuadratically.comp {ρ : A →* MulAut P} (f : B →* A) {b : B}
    (h : ActsQuadratically ρ (f b)) : ActsQuadratically (ρ.comp f) b := by
  rw [actsQuadratically_iff_forall] at h ⊢
  exact fun v => h v

end Quadratic

theorem displacementSubgroup_conjNormal_map_subtype (P : Subgroup G) [P.Normal] (x : G) :
    (displacementSubgroup (MulAut.conjNormal (H := P)) x).map P.subtype
      = closure {y : G | ∃ v ∈ P, y = v⁻¹ * x * v * x⁻¹} := by
  refine le_antisymm ?_ ((closure_le _).2 ?_)
  · rw [Subgroup.map_le_iff_le_comap, displacementSubgroup_le_iff]
    intro v
    refine Subgroup.mem_comap.2 (subset_closure ⟨(v : G), v.2, ?_⟩)
    simp [MulAut.conjNormal_apply, mul_assoc]
  · rintro y ⟨v, hv, rfl⟩
    exact ⟨(⟨v, hv⟩ : P)⁻¹ * MulAut.conjNormal x ⟨v, hv⟩,
      mem_displacementSubgroup _ _ _, by simp [MulAut.conjNormal_apply, mul_assoc]⟩

theorem actsQuadratically_conjNormal_iff {P : Subgroup G} [P.Normal] {x : G} :
    ActsQuadratically (MulAut.conjNormal (H := P)) x ↔
      x ∈ centralizer (closure {y : G | ∃ v ∈ P, y = v⁻¹ * x * v * x⁻¹} : Set G) := by
  rw [← displacementSubgroup_conjNormal_map_subtype]
  constructor
  · intro h
    rw [mem_centralizer_iff]
    rintro y ⟨w, hw, rfl⟩
    have hcw : x * (w : G) * x⁻¹ = (w : G) := congrArg Subtype.val (h.apply_eq hw)
    simp only [Subgroup.coe_subtype]
    calc (w : G) * x = x * (w : G) * x⁻¹ * x := by rw [hcw]
      _ = x * (w : G) := by group
  · intro hx
    rw [actsQuadratically_iff_forall]
    intro v
    have hmem : P.subtype (v⁻¹ * MulAut.conjNormal x v)
        ∈ (displacementSubgroup (MulAut.conjNormal (H := P)) x).map P.subtype :=
      ⟨_, mem_displacementSubgroup _ _ _, rfl⟩
    have hcomm := (mem_centralizer_iff.1 hx) _ hmem
    refine Subtype.ext ?_
    have hv : P.subtype (v⁻¹ * MulAut.conjNormal x v) = (v : G)⁻¹ * (x * (v : G) * x⁻¹) := by
      simp [MulAut.conjNormal_apply]
    rw [hv] at hcomm
    push_cast [MulAut.conjNormal_apply]
    calc x * ((v : G)⁻¹ * (x * (v : G) * x⁻¹)) * x⁻¹
        = ((v : G)⁻¹ * (x * (v : G) * x⁻¹) * x) * x⁻¹ := by rw [hcomm]
      _ = (v : G)⁻¹ * (x * (v : G) * x⁻¹) := by group

theorem mk_mem_pCore_quotient_centralizer_of_quadratic [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hGodd : Odd (Nat.card G)) {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    {x : G} (hx : ∃ k, orderOf x = p ^ k)
    (hquad : ActsQuadratically (MulAut.conjNormal (H := P)) x) :
    QuotientGroup.mk' (centralizer (P : Set G)) x ∈ pCore p (G ⧸ centralizer (P : Set G)) := by
  set C := centralizer (P : Set G) with hC
  set ρ : G →* MulAut P := MulAut.conjNormal with hρ
  have hkerρ : ρ.ker = C := ker_conjNormal P
  set f := QuotientGroup.mk' C with hf
  refine mem_pCore_of_forall_isPGroup_closure_conj hp ?_ ?_
  · obtain ⟨k, hk⟩ := hx
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 (hk ▸ orderOf_map_dvd f x)
    exact ⟨m, hm⟩
  · intro gq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C gq
    set A := closure ({x, g⁻¹ * x * g} : Set G) with hA
    have hxA : x ∈ A := subset_closure (by simp)
    have hyA : g⁻¹ * x * g ∈ A := subset_closure (by simp)
    have hgen : closure ({⟨x, hxA⟩, ⟨g⁻¹ * x * g, hyA⟩} : Set A) = ⊤ := by
      have hset : ({(⟨x, hxA⟩ : A), ⟨g⁻¹ * x * g, hyA⟩} : Set A)
          = Subtype.val ⁻¹' ({x, g⁻¹ * x * g} : Set G) := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
        constructor
        · rintro (rfl | rfl) <;> simp
        · rintro (h | h)
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
      rw [hset]
      exact Subgroup.closure_closure_coe_preimage
    have hAodd : Odd (Nat.card A) := hGodd.of_dvd_nat (card_subgroup_dvd_card A)
    have hsc : SemiconjBy g⁻¹ x (g⁻¹ * x * g) := by
      change g⁻¹ * x = g⁻¹ * x * g * g⁻¹
      group
    have hpg : IsPGroup p (ρ.comp A.subtype).range := by
      refine isPGroup_range_of_quadratic_pElement_generators_of_isPGroup hp hP hAodd _ hgen
        ?_ ?_ ?_ ?_
      · obtain ⟨k, hk⟩ := hx
        exact ⟨k, (Subgroup.orderOf_mk x hxA).trans hk ▸ dvd_rfl⟩
      · obtain ⟨k, hk⟩ := hx
        refine ⟨k, ?_⟩
        rw [Subgroup.orderOf_mk, ← SemiconjBy.orderOf_eq g⁻¹ hsc, hk]
      · exact hquad.comp A.subtype (b := ⟨x, hxA⟩)
      · exact (hquad.conj g).comp A.subtype (b := ⟨g⁻¹ * x * g, hyA⟩)
    have hker : (f.comp A.subtype).ker = (ρ.comp A.subtype).ker := by
      rw [← MonoidHom.comap_ker, ← MonoidHom.comap_ker, hf, QuotientGroup.ker_mk', hkerρ]
    have hrange : IsPGroup p (f.comp A.subtype).range := isPGroup_range_of_ker_eq _ _ hker hpg
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at hrange
    have himg : closure ({f x, (f g)⁻¹ * f x * f g} : Set (G ⧸ C)) = A.map f := by
      rw [hA, MonoidHom.map_closure]
      congr 1
      simp [Set.image_insert_eq]
    rw [himg]
    exact hrange

theorem mk_mem_pCore_quotient_centralizer_of_quadratic_of_odd [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (_hpodd : Odd p) (hGodd : Odd (Nat.card G)) {P : Subgroup G} [P.Normal]
    (hP : IsPGroup p P) {x : G} (hx : x ∈ pElements p G)
    (hquad : x ∈ centralizer (closure {y : G | ∃ v ∈ P, y = v⁻¹ * x * v * x⁻¹} : Set G)) :
    QuotientGroup.mk' (centralizer (P : Set G)) x ∈ pCore p (G ⧸ centralizer (P : Set G)) :=
  mk_mem_pCore_quotient_centralizer_of_quadratic hp hGodd hP (mem_pElements.1 hx)
    (actsQuadratically_conjNormal_iff.2 hquad)

end

end CFSG.FeitThompson
