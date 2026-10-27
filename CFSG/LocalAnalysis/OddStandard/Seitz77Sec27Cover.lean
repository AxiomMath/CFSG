module

public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag CFSG.LieType.Chevalley

section LeviHom

theorem eq_one_of_sq_eq_one_of_odd {Z : Type*} [Group Z] [Finite Z] (hZ : Odd (Nat.card Z))
    {z : Z} (hz : z ^ 2 = 1) : z = 1 := by
  obtain ⟨m, hm⟩ := hZ
  have h := pow_card_eq_one' (G := Z) (x := z)
  rwa [hm, pow_succ, pow_mul, hz, one_pow, one_mul] at h

theorem centralizes_of_div_mem {P : Type*} [Group P] {S : Subgroup P}
    (hS : ∀ r ∈ S, ∀ s ∈ S, r * s = s * r) {c d : P} (hr : c / d ∈ S)
    (hc : ∀ x ∈ S, c * x = x * c) : ∀ x ∈ S, d * x = x * d := by
  intro x hx
  have h1 := hS _ (inv_mem hr) x hx
  calc d * x = (c / d)⁻¹ * c * x := by rw [inv_div, div_mul_cancel]
    _ = (c / d)⁻¹ * (c * x) := mul_assoc _ _ _
    _ = (c / d)⁻¹ * (x * c) := by rw [hc x hx]
    _ = (c / d)⁻¹ * x * c := (mul_assoc _ _ _).symm
    _ = x * (c / d)⁻¹ * c := by rw [h1]
    _ = x * ((c / d)⁻¹ * c) := mul_assoc _ _ _
    _ = x * d := by rw [inv_div, div_mul_cancel]

section Matrices

variable {k : Type} [Field k]

theorem eq_one_of_commute_projRad (i : Fin 2) {B : SL2 k}
    (h : ∀ x ∈ projRad k i, leviProj k i B * x = x * leviProj k i B) : B = 1 := by
  fin_cases i
  · have key : ∀ a c : k, proj 3 k (unipU k a 0 c) ∈ projRad k 0 →
        leviProj k 0 B * proj 3 k (unipU k a 0 c) = proj 3 k (unipU k a 0 c) * leviProj k 0 B →
        a * (B : Matrix (Fin 2) (Fin 2) k) 1 1 - c * (B : Matrix (Fin 2) (Fin 2) k) 1 0 = a ∧
          c * (B : Matrix (Fin 2) (Fin 2) k) 0 0 - a * (B : Matrix (Fin 2) (Fin 2) k) 0 1 = c := by
      intro a c _ hac
      change proj 3 k (leviOne k B) * proj 3 k (unipU k a 0 c) =
        proj 3 k (unipU k a 0 c) * proj 3 k (leviOne k B) at hac
      rw [← map_mul, ← map_mul, leviOne_mul_unipU, map_mul] at hac
      obtain ⟨h1, -, h3⟩ := unipU_eq_of_proj_eq (mul_right_cancel hac)
      exact ⟨h1, h3⟩
    obtain ⟨e1, e2⟩ := key 1 0 (mem_projRad_zero.2 ⟨1, 0, rfl⟩)
      (h _ (mem_projRad_zero.2 ⟨1, 0, rfl⟩))
    obtain ⟨e3, e4⟩ := key 0 1 (mem_projRad_zero.2 ⟨0, 1, rfl⟩)
      (h _ (mem_projRad_zero.2 ⟨0, 1, rfl⟩))
    refine SL2_ext ?_ ?_ ?_ ?_
    · simpa using e4
    · simpa using e2
    · simpa using e3
    · simpa using e1
  · have key : ∀ b c : k, proj 3 k (unipU k 0 b c) ∈ projRad k 1 →
        leviProj k 1 B * proj 3 k (unipU k 0 b c) = proj 3 k (unipU k 0 b c) * leviProj k 1 B →
        (B : Matrix (Fin 2) (Fin 2) k) 1 0 * c + (B : Matrix (Fin 2) (Fin 2) k) 1 1 * b = b ∧
          (B : Matrix (Fin 2) (Fin 2) k) 0 0 * c + (B : Matrix (Fin 2) (Fin 2) k) 0 1 * b = c := by
      intro b c _ hbc
      change proj 3 k (leviTwo k B) * proj 3 k (unipU k 0 b c) =
        proj 3 k (unipU k 0 b c) * proj 3 k (leviTwo k B) at hbc
      rw [← map_mul, ← map_mul, leviTwo_mul_unipU, map_mul] at hbc
      obtain ⟨-, h2, h3⟩ := unipU_eq_of_proj_eq (mul_right_cancel hbc)
      exact ⟨h2, h3⟩
    obtain ⟨e1, e2⟩ := key 1 0 (mem_projRad_one.2 ⟨1, 0, rfl⟩)
      (h _ (mem_projRad_one.2 ⟨1, 0, rfl⟩))
    obtain ⟨e3, e4⟩ := key 0 1 (mem_projRad_one.2 ⟨0, 1, rfl⟩)
      (h _ (mem_projRad_one.2 ⟨0, 1, rfl⟩))
    refine SL2_ext ?_ ?_ ?_ ?_
    · simpa using e4
    · simpa using e2
    · simpa using e3
    · simpa using e1

end Matrices

section Projection

variable {k : Type} [Field k] [Finite k]

theorem leviProj_mem_normalizer (hk : Nat.card k = 4) (i : Fin 2) (B : SL2 k) :
    leviProj k i B ∈ normalizer (projRad k i : Set (projectiveSL 3 k)) := by
  rw [normalizer_projRad hk i]
  exact Subgroup.mem_sup_right ⟨B, rfl⟩

theorem exists_projection_to_sl2 (hk : Nat.card k = 4) (i : Fin 2) :
    ∃ π : ↥(normalizer (projRad k i : Set (projectiveSL 3 k))) →* SL2 k,
      (∀ B : SL2 k, π ⟨leviProj k i B, leviProj_mem_normalizer hk i B⟩ = B) ∧
      ∀ q, π q = 1 ↔ (q : projectiveSL 3 k) ∈ projRad k i := by
  have : ((projRad k i).subgroupOf (normalizer (projRad k i : Set (projectiveSL 3 k)))).Normal :=
    Subgroup.normal_in_normalizer
  let σ : SL2 k →* ↥(normalizer (projRad k i : Set (projectiveSL 3 k))) :=
    { toFun := fun B => ⟨leviProj k i B, leviProj_mem_normalizer hk i B⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun B B' => Subtype.ext (map_mul _ B B') }
  have hinj : Function.Injective
      ((QuotientGroup.mk' ((projRad k i).subgroupOf
        (normalizer (projRad k i : Set (projectiveSL 3 k))))).comp σ) := by
    rw [injective_iff_map_eq_one]
    intro B hB
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hB
    have h1 : leviProj k i B ∈ projRad k i ⊓ (leviProj k i).range := ⟨hB, B, rfl⟩
    rw [projRad_inf_range, Subgroup.mem_bot] at h1
    exact leviProj_injective i (h1.trans (map_one _).symm)
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' ((projRad k i).subgroupOf
        (normalizer (projRad k i : Set (projectiveSL 3 k))))).comp σ) := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hLN : (leviProj k i).range ≤ normalizer (projRad k i : Set (projectiveSL 3 k)) := by
      rw [normalizer_projRad hk i]
      exact le_sup_right
    have hq : (q : projectiveSL 3 k) ∈ ((projRad k i ⊔ (leviProj k i).range : Subgroup _) :
        Set (projectiveSL 3 k)) := by
      rw [← normalizer_projRad hk i]
      exact q.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLN] at hq
    obtain ⟨r, hr, δ, ⟨B, rfl⟩, hrδ⟩ := hq
    refine ⟨B, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    rw [Subgroup.mem_subgroupOf]
    change leviProj k i B / (q : projectiveSL 3 k) ∈ projRad k i
    rw [← hrδ, div_eq_mul_inv, mul_inv_rev, mul_inv_cancel_left]
    exact inv_mem hr
  let e := MulEquiv.ofBijective _ (⟨hinj, hsurj⟩ : Function.Bijective _)
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_⟩
  · intro B
    exact e.symm_apply_apply B
  · intro q
    change e.symm (QuotientGroup.mk' _ q) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]

end Projection

theorem exists_levi_hom {G : Type} [Group G] [Finite G] {A R : Subgroup G} (hRA : R ≤ A)
    (hR : IsElemAbelian 2 R) {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4) (i : Fin 2)
    (φ : ↥A →* projectiveSL 3 k) (hφ : Function.Surjective φ) (hker : φ.ker ≤ center ↥A)
    (hkodd : Odd (Nat.card φ.ker)) (hmap : (R.subgroupOf A).map φ = projRad k i) :
    ∃ Λ : ↥(A ⊓ normalizer (R : Set G)) →* SL2 k, Function.Surjective Λ ∧
      ∀ a : ↥(A ⊓ normalizer (R : Set G)), Λ a = 1 ↔ (a : G) ∈ centralizer (R : Set G) := by
  classical
  obtain ⟨π, hπσ, hπker⟩ := exists_projection_to_sl2 hk i
  have := hR.1
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy => setLike_mul_comm hx hy
  have F1 : ∀ x : ↥A, φ x ∈ projRad k i → ∃ h ∈ R.subgroupOf A, ∃ z ∈ φ.ker, x = h * z := by
    intro x hx
    rw [← hmap] at hx
    obtain ⟨h, hh, hhx⟩ := hx
    refine ⟨h, hh, h⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hhx, inv_mul_cancel]
  have hnorm : ∀ a : ↥(A ⊓ normalizer (R : Set G)),
      φ ⟨a.1, a.2.1⟩ ∈ normalizer (projRad k i : Set (projectiveSL 3 k)) := by
    intro a
    have ha₀H : (⟨a.1, a.2.1⟩ : ↥A) ∈ normalizer ((R.subgroupOf A : Subgroup ↥A) : Set ↥A) := by
      rw [← subgroupOf_normalizer_eq hRA]
      exact mem_subgroupOf.mpr a.2.2
    have := le_normalizer_map φ (Subgroup.mem_map_of_mem φ ha₀H)
    rwa [hmap] at this
  let Φ : ↥(A ⊓ normalizer (R : Set G)) →*
      ↥(normalizer (projRad k i : Set (projectiveSL 3 k))) :=
    (φ.comp (Subgroup.inclusion inf_le_left)).codRestrict _ hnorm
  have hΦ : ∀ a, ((Φ a : ↥(normalizer (projRad k i : Set (projectiveSL 3 k)))) :
      projectiveSL 3 k) = φ ⟨a.1, a.2.1⟩ := fun a => rfl
  refine ⟨π.comp Φ, ?_, ?_⟩
  ·
    intro B
    obtain ⟨a₀, ha₀⟩ := hφ (leviProj k i B)
    have hnormR : (a₀ : G) ∈ normalizer (R : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      have hn' : n ∈ R := hn
      have hnH : (⟨n, hRA hn'⟩ : ↥A) ∈ R.subgroupOf A := hn'
      have hx : φ (a₀ * ⟨n, hRA hn'⟩ * a₀⁻¹) ∈ projRad k i := by
        rw [map_mul, map_mul, map_inv, ha₀]
        have hnR : φ ⟨n, hRA hn'⟩ ∈ projRad k i := hmap ▸ Subgroup.mem_map_of_mem φ hnH
        exact (mem_normalizer_iff.1 (ha₀ ▸ leviProj_mem_normalizer hk i B) _).1 hnR
      obtain ⟨h, hh, z, hz, hxz⟩ := F1 _ hx
      have hcomm : Commute h z := mem_center_iff.1 (hker hz) h
      have hn2 : (⟨n, hRA hn'⟩ : ↥A) ^ 2 = 1 := Subtype.ext (hR.2 n hn')
      have hh2 : h ^ 2 = 1 := Subtype.ext (hR.2 h.1 hh)
      have hsq : (h * z) ^ 2 = 1 := by
        rw [← hxz, conj_pow, hn2]
        group
      have hz2 : (⟨z, hz⟩ : φ.ker) ^ 2 = 1 := by
        apply Subtype.ext
        change z ^ 2 = 1
        rwa [hcomm.mul_pow, hh2, one_mul] at hsq
      have hz1 : z = 1 := congrArg Subtype.val (eq_one_of_sq_eq_one_of_odd hkodd hz2)
      have hmem : (a₀ * ⟨n, hRA hn'⟩ * a₀⁻¹ : ↥A) ∈ R.subgroupOf A := by
        rw [hxz, hz1, mul_one]
        exact hh
      exact hmem
    refine ⟨⟨a₀.1, a₀.2, hnormR⟩, ?_⟩
    have : Φ ⟨a₀.1, a₀.2, hnormR⟩ = ⟨leviProj k i B, leviProj_mem_normalizer hk i B⟩ :=
      Subtype.ext ha₀
    rw [MonoidHom.comp_apply, this]
    exact hπσ B
  ·
    intro a
    rw [MonoidHom.comp_apply]
    constructor
    · intro h1
      have hx : φ ⟨a.1, a.2.1⟩ ∈ projRad k i := by
        rw [← hΦ]
        exact (hπker _).1 h1
      obtain ⟨h, hh, z, hz, hxz⟩ := F1 _ hx
      rw [mem_centralizer_iff]
      intro r hr
      have e1 : (a : G) = (h : G) * (z : G) := congrArg Subtype.val hxz
      have e2 : r * (z : G) = (z : G) * r :=
        congrArg Subtype.val (mem_center_iff.1 (hker hz) ⟨r, hRA hr⟩)
      have e3 : r * (h : G) = (h : G) * r := hRcomm r hr h hh
      rw [e1, ← mul_assoc, e3, mul_assoc, e2, ← mul_assoc]
    · intro hc
      have hcomm : ∀ x ∈ projRad k i, φ ⟨a.1, a.2.1⟩ * x = x * φ ⟨a.1, a.2.1⟩ := by
        intro x hx
        rw [← hmap] at hx
        obtain ⟨h, hh, rfl⟩ := hx
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_iff.1 hc h.1 hh).symm
      have hr : φ ⟨a.1, a.2.1⟩ / leviProj k i (π (Φ a)) ∈ projRad k i := by
        rw [← hΦ]
        refine (hπker (Φ a / ⟨leviProj k i (π (Φ a)), leviProj_mem_normalizer hk i _⟩)).1 ?_
        rw [map_div, hπσ, div_self']
      have hB := centralizes_of_div_mem
        (fun r hr s hs => commute_of_mem_projRad i hr hs) hr hcomm
      exact eq_one_of_commute_projRad i hB

end LeviHom


theorem center_sl2_eq_bot_of_card_four (k : Type) [Field k] [Finite k]
    (hk : Nat.card k = 4) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) = ⊥ := by
  let _ := Fintype.ofFinite k
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hk]
    norm_num)
  exact Subgroup.card_eq_one.mp
    (CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (K := k) (CharTwo.neg_eq 1))

theorem sl2_mulEquiv_alt5 (k : Type) [Field k] [Finite k]
    (hk : Nat.card k = 4) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) k ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five k
    (Or.inl hk)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq (center_sl2_eq_bot_of_card_four k hk)).trans
    QuotientGroup.quotientBot).symm.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 k).trans e)⟩

end CFSG.OddStandard.Seitz77
