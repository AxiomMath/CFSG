module

public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralAutomizers

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.FocalFusion CFSG.QuasiDihedralFusion

theorem sd32_of_gens {G : Type*} [Group G] (S : Subgroup G) (h t : G) (hhS : h ∈ S) (htS : t ∈ S)
    (hord : orderOf h = 16) (ht : t * t = 1) (hconj : t * h * t⁻¹ = h ^ 7)
    (hgen : S = Subgroup.zpowers h ⊔ Subgroup.zpowers t) (hcard : Nat.card S = 32) :
    ∃ f : SemidihedralGroup 5 ≃* S,
      ((f (CFSG.Semidihedral.r 5) : S) : G) = h ∧ ((f (CFSG.Semidihedral.s 5) : S) : G) = t ∧
      qdFour S f = Subgroup.closure ({h ^ 8, t} : Set G) := by
  set h' : S := ⟨h, hhS⟩ with hh'
  set t' : S := ⟨t, htS⟩ with ht'
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by omega)
  have hh'ord : orderOf h' = 16 := by
    rw [hh', Subgroup.orderOf_mk, hord]
  have ht'sq : t' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using ht)
  have hconj' : t' * h' * t'⁻¹ = h' ^ 7 := Subtype.ext (by simpa using hconj)
  have hgen' : (⊤ : Subgroup S) = Subgroup.zpowers h' ⊔ Subgroup.zpowers t' := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, Subgroup.map_top,
      Subgroup.range_subtype]
    exact hgen
  let φ : SemidihedralGroup 5 →* S := PresentedGroup.toGroup (f := ![h', t']) (by
    intro w hw
    simp only [semidihedralRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero]
      rw [show 5 - 1 = 4 by omega, show 2 ^ 4 = 16 by norm_num, ← hh'ord, pow_orderOf_eq_one]
    · simpa only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
        Matrix.cons_val_zero] using ht'sq
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      rw [show 5 - 2 = 3 by omega, show 2 ^ 3 - 1 = 7 by norm_num, hconj', mul_inv_cancel])
  have hφr : φ (CFSG.Semidihedral.r 5) = h' := by simp [φ]
  have hφs : φ (CFSG.Semidihedral.s 5) = t' := by simp [φ]
  have hh'r : h' ∈ φ.range := ⟨CFSG.Semidihedral.r 5, hφr⟩
  have ht'r : t' ∈ φ.range := ⟨CFSG.Semidihedral.s 5, hφs⟩
  have hsurj : Function.Surjective φ := by
    intro g
    have hg : g ∈ (⊤ : Subgroup S) := Subgroup.mem_top g
    rw [hgen'] at hg
    exact (sup_le (Subgroup.zpowers_le.mpr hh'r) (Subgroup.zpowers_le.mpr ht'r)) hg
  have : Finite (SemidihedralGroup 5) := CFSG.Semidihedral.presentation_finite 5 (by omega)
  have hbij : Function.Bijective φ :=
    hsurj.bijective_of_nat_card_le (by rw [hcard, CFSG.Semidihedral.card 5 (by omega)]; norm_num)
  refine ⟨MulEquiv.ofBijective φ hbij, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hφr
  · exact congrArg Subtype.val hφs
  · unfold qdFour sdFourSubgroup
    rw [MonoidHom.map_closure, Set.image_pair]
    have e1 : ambientHom 5 S (MulEquiv.ofBijective φ hbij) (CFSG.Semidihedral.z 5) = h ^ 8 := by
      show ((φ (CFSG.Semidihedral.z 5) : S) : G) = h ^ 8
      have hz : CFSG.Semidihedral.z 5 = CFSG.Semidihedral.r 5 ^ 8 := rfl
      rw [hz, map_pow, hφr]
      rfl
    have e2 : ambientHom 5 S (MulEquiv.ofBijective φ hbij) (CFSG.Semidihedral.s 5) = t :=
      congrArg Subtype.val hφs
    rw [e1, e2]

theorem sd_center_isolated_of_normalizer_fixes {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 4 ≤ n)
    (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfix : ∀ x ∈ Subgroup.normalizer (qdFour (S : Subgroup H) f : Set H),
      x * ambientHom n (S : Subgroup H) f (z n) * x⁻¹ = ambientHom n (S : Subgroup H) f (z n))
    (g : H) (hg : g * ambientHom n (S : Subgroup H) f (z n) * g⁻¹ ∈ (S : Subgroup H)) :
    g * ambientHom n (S : Subgroup H) f (z n) * g⁻¹ = ambientHom n (S : Subgroup H) f (z n) := by
  set ι := ambientHom n (S : Subgroup H) f with hι
  obtain ⟨y₀, hy₀⟩ := exists_ambientHom_eq (S : Subgroup H) f _ hg
  have hy₀o : orderOf y₀ = 2 := by
    rw [← orderOf_ambientHom (S : Subgroup H) f y₀, hy₀,
      ← conjugate_orderOf_eq (isConj_iff.mpr ⟨g, rfl⟩ : IsConj (ι (z n)) (g * ι (z n) * g⁻¹)),
      orderOf_ambientHom, orderOf_z n (by omega)]
  rcases sd_involution_cases hn y₀ hy₀o with hy | hy
  · rw [← hy₀, hy]
  · exfalso
    have hsz : IsConj (ι (s n)) (ι (z n)) := by
      have h1 : IsConj (ι (s n)) (g * ι (z n) * g⁻¹) := by
        rw [← hy₀]
        exact ι.map_isConj hy
      exact h1.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    obtain ⟨x, hxN, hxs⟩ := exists_mem_normalizer_qdFour hn S f hsz
    have hxz := hfix x hxN
    refine s_ne_z hn (ambientHom_injective n (S : Subgroup H) f ?_)
    have h2 : x * ι (s n) * x⁻¹ = x * ι (z n) * x⁻¹ := by rw [hxs, hxz]
    exact mul_left_cancel (mul_right_cancel h2)

theorem isolated_of_normalizer_fixes {G : Type*} [Group G] [Finite G] (A S : Subgroup G)
    (hSA : S ≤ A) (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex A) (h t : G) (hhS : h ∈ S)
    (htS : t ∈ S) (hord : orderOf h = 16) (ht : t * t = 1) (hconj : t * h * t⁻¹ = h ^ 7)
    (hgen : S = Subgroup.zpowers h ⊔ Subgroup.zpowers t) (hcard : Nat.card S = 32)
    (hfix : ∀ n ∈ A, (∀ g ∈ (Subgroup.closure ({h ^ 8, t} : Set G)),
        n * g * n⁻¹ ∈ Subgroup.closure ({h ^ 8, t} : Set G)) → n * h ^ 8 * n⁻¹ = h ^ 8) :
    ∀ g ∈ A, g * h ^ 8 * g⁻¹ ∈ S → g * h ^ 8 * g⁻¹ = h ^ 8 := by
  obtain ⟨f, hfr, hfs, hfT⟩ := sd32_of_gens S h t hhS htS hord ht hconj hgen hcard
  have hS'p : IsPGroup 2 (S.subgroupOf A) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSA).symm
  let T : Sylow 2 A := hS'p.toSylow hSidx
  have hTmem : ∀ x : A, x ∈ (T : Subgroup A) ↔ (x : G) ∈ S := fun x => Iff.rfl
  let f' : SemidihedralGroup 5 ≃* (T : Subgroup A) :=
    f.trans (Subgroup.subgroupOfEquivOfLe hSA).symm
  let ι : SemidihedralGroup 5 →* A := ambientHom 5 (T : Subgroup A) f'
  have hιG : ∀ x, ((ι x : A) : G) = ((f x : S) : G) := fun x => rfl
  have hιz : ((ι (z 5) : A) : G) = h ^ 8 := by
    rw [hιG]
    have hz : z 5 = r 5 ^ 8 := rfl
    rw [hz, map_pow, Subgroup.coe_pow, hfr]
  have hmapT : (qdFour (T : Subgroup A) f').map A.subtype =
      Subgroup.closure ({h ^ 8, t} : Set G) := by
    rw [← hfT]
    unfold qdFour
    rw [Subgroup.map_map]
    rfl
  intro g hgA hgS
  have hz1 : ((⟨g, hgA⟩ : A) * ι (z 5) * (⟨g, hgA⟩ : A)⁻¹ : A) = ι (z 5) := by
    refine sd_center_isolated_of_normalizer_fixes (n := 5) (by norm_num) T f' (fun x hx => ?_)
      ⟨g, hgA⟩ ?_
    · apply Subtype.ext
      change (x : G) * ((ι (z 5) : A) : G) * (x : G)⁻¹ = ((ι (z 5) : A) : G)
      rw [hιz]
      apply hfix x x.2
      intro y hy
      rw [← hmapT] at hy ⊢
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x * y' * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx y').mp hy', rfl⟩
    · rw [hTmem]
      change g * ((ι (z 5) : A) : G) * g⁻¹ ∈ S
      rw [hιz]
      exact hgS
  have h2 := congrArg (fun a : A => (a : G)) hz1
  change g * ((ι (z 5) : A) : G) * g⁻¹ = ((ι (z 5) : A) : G) at h2
  rwa [hιz] at h2

end CFSG.GH74.GLS.Stage4.Q9
