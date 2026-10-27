module

public import CFSG.LieType.Ree.BorelOvergroupClassification
public import CFSG.LieType.Ree.LocalBlockSylowAction

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

theorem minimal_apply_orderIso {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β)
    {P : β → Prop} {x : α} : Minimal P (f x) ↔ Minimal (fun y => P (f y)) x := by
  constructor
  · rintro ⟨hx, hmin⟩
    exact ⟨hx, fun ⦃y⦄ hy hyx => f.le_iff_le.1 (hmin hy (f.le_iff_le.2 hyx))⟩
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, fun ⦃y⦄ hy hyx => ?_⟩
    have h := hmin (y := f.symm y) (by show P (f (f.symm y)); rwa [f.apply_symm_apply])
      (by rwa [← f.le_iff_le, f.apply_symm_apply])
    rwa [← f.le_iff_le, f.apply_symm_apply] at h

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem canonicalRep_mem_reeFixedBruhatCell
    (w : WeylGroup t.tag) :
    canonicalRep (coxeterSystem t.tag) K w ∈ t.reeFixedBruhatCell K a w :=
  mem_reeFixedBruhatCell.2 ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]⟩

theorem canonicalRep_fixedOrbitElement_not_mem_reeFixedBorel
    (j : Fin t.fixedOrbitCount) :
    canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∉ t.reeFixedBorel K a :=
  fun h => Set.disjoint_left.1 (disjoint_reeFixedBorel_reeFixedBruhatCell j) h
    (canonicalRep_mem_reeFixedBruhatCell _)

theorem reeParabolic_singleton
    (j : Fin t.fixedOrbitCount) :
    t.reeParabolic K a {j} = t.reeLocalParabolic K a j := by
  refine le_antisymm (reeParabolic_le_reeGamma_inf subset_rfl) fun g hg => ?_
  have hg' : g ∈ ((t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) :
      Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) := hg
  rw [coe_reeGamma_inf_parabolicSubgroup] at hg'
  rcases hg' with hB | hD
  · exact t.reeFixedBorel_le_reeParabolic K a _ hB
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hD
    exact mul_mem (mul_mem (t.reeFixedBorel_le_reeParabolic K a _ hb)
      (t.canonicalRep_mem_reeParabolic K a (Set.mem_singleton j)))
      (t.reeFixedBorel_le_reeParabolic K a _ hb')

theorem reeFixedBorel_lt_reeLocalParabolic
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedBorel K a < t.reeLocalParabolic K a j := by
  refine lt_of_le_of_ne (reeFixedBorel_le_reeGamma_inf_parabolicSubgroup j) fun h => ?_
  refine canonicalRep_fixedOrbitElement_not_mem_reeFixedBorel (K := K) (a := a) j ?_
  rw [h]
  exact canonicalRep_fixedOrbitElement_mem_reeGamma_inf j

theorem reeLocalParabolic_le_of_mem
    {A : Subgroup (ModGL t.tag K)}
    (hBA : t.reeFixedBorel K a ≤ A) {j : Fin t.fixedOrbitCount}
    (hn : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ A) :
    t.reeLocalParabolic K a j ≤ A := by
  rw [← reeParabolic_singleton]
  refine sup_le hBA ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨i, hi, rfl⟩
  obtain rfl := Set.mem_singleton_iff.1 hi
  exact hn

theorem exists_canonicalRep_mem_of_lt
    {A : Subgroup (ModGL t.tag K)}
    (hlt : t.reeFixedBorel K a < A) (hAΓ : A ≤ t.reeGamma K a) :
    ∃ j, canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ A := by
  by_contra hno'
  have hno : ∀ j, canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∉ A :=
    fun j hj => hno' ⟨j, hj⟩
  have hA := (ree_Borel_overgroup_classification t a K A hlt.le hAΓ).1
  have hJ : {j | canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ A} = ∅ :=
    Set.ext fun j => ⟨fun h => (hno j h).elim, fun h => h.elim⟩
  rw [hJ, t.reeParabolic_empty K a] at hA
  exact hlt.ne hA.symm

theorem minimal_reeFixedBorel_iff
    (A : Subgroup (ModGL t.tag K)) :
    Minimal (fun A => t.reeFixedBorel K a < A ∧ A ≤ t.reeGamma K a) A ↔
      ∃ j, A = t.reeLocalParabolic K a j := by
  constructor
  · rintro ⟨⟨hlt, hAΓ⟩, hmin⟩
    obtain ⟨j, hj⟩ := exists_canonicalRep_mem_of_lt hlt hAΓ
    have hle := reeLocalParabolic_le_of_mem hlt.le hj
    exact ⟨j, le_antisymm (hmin ⟨reeFixedBorel_lt_reeLocalParabolic j, inf_le_left⟩ hle) hle⟩
  · rintro ⟨j, rfl⟩
    refine ⟨⟨reeFixedBorel_lt_reeLocalParabolic j, inf_le_left⟩, fun ⦃A'⦄ hA' hA'P => ?_⟩
    obtain ⟨hlt', hA'Γ⟩ := hA'
    obtain ⟨i, hi⟩ := exists_canonicalRep_mem_of_lt hlt' hA'Γ
    have hij : i ∈ ({j} : Set (Fin t.fixedOrbitCount)) := by
      rw [← canonicalRep_mem_reeParabolic_iff (K := K) (a := a), reeParabolic_singleton]
      exact hA'P hi
    obtain rfl := Set.mem_singleton_iff.1 hij
    exact reeLocalParabolic_le_of_mem hlt'.le hi

theorem reeLocalParabolic_injective :
    Function.Injective (t.reeLocalParabolic K a) := fun i j h => by
  have hi := canonicalRep_fixedOrbitElement_mem_reeGamma_inf (K := K) (a := a) i
  change _ ∈ t.reeLocalParabolic K a i at hi
  rw [h, ← reeParabolic_singleton, canonicalRep_mem_reeParabolic_iff] at hi
  exact hi

theorem reeLocalParabolic_inf_reeFixedNegUnipotent
    (j : Fin t.fixedOrbitCount) :
    t.reeLocalParabolic K a j ⊓ t.reeFixedNegUnipotent K a =
      t.reeFixedOrbitNegUnipotent K a j := by
  have : Fact t.prime.Prime := ⟨by cases t <;> decide⟩
  have hBV := reeFixedBorel_inf_reeFixedNegUnipotent (t := t) (K := K) (a := a)
  have hV1 : ∀ v ∈ t.reeFixedNegUnipotent K a, v ∈ t.reeFixedBorel K a → v = 1 :=
    fun v hv hvB => by
      have h := Subgroup.mem_inf.2 ⟨hvB, hv⟩
      rw [hBV, Subgroup.mem_bot] at h
      exact h
  refine le_antisymm (fun g hg => ?_) (le_inf ((reeFixedOrbitNegUnipotent_le_reeLocalBlock j).trans
    (reeLocalBlock_le j)) (reeFixedOrbitNegUnipotent_le_reeFixedNegUnipotent j))
  obtain ⟨hgP, hgV⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨m, hm, hmn⟩ := exists_mem_reeLocalBlock_mk_eq (K := K) (a := a) j
  obtain ⟨hYeq, -⟩ := reeFixedOrbitNegUnipotent_eq_map_conj hm hmn
  by_cases hgn : (g : ModGL t.tag K ⧸ t.reeFixedBorel K a) =
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : _)
  ·
    exfalso
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (K := K) (a := a) j
    have hy := conj_mem_reeFixedOrbitNegUnipotent (K := K) (a := a) hu
    have hyg := smul_mk_canonicalRep_of_mem hy
    rw [← hgn, smul_mk, QuotientGroup.eq] at hyg
    have hmem : g⁻¹ * (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
        (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹) * g ∈
          t.reeFixedBorel K a := by
      have h := inv_mem hyg
      rwa [mul_inv_rev, inv_inv, ← mul_assoc] at h
    have hyV := reeFixedOrbitNegUnipotent_le_reeFixedNegUnipotent j hy
    have h1 := hV1 _ (mul_mem (mul_mem (inv_mem hgV) hyV) hgV) hmem
    have hy1 : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
        (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ = 1 := by
      have e : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
          (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ =
            g * (g⁻¹ * (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
              (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹) * g) * g⁻¹ := by
        group
      rw [e, h1, mul_one, mul_inv_cancel]
    rw [mul_inv_eq_one, mul_eq_left] at hy1
    exact hu1 hy1
  ·
    have hmB : m ∉ t.reeFixedBorel K a := fun hmB =>
      canonicalRep_fixedOrbitElement_not_mem_reeFixedBorel (K := K) (a := a) j (by
        have h := mul_mem hmB (QuotientGroup.eq.1 hmn)
        rwa [mul_inv_cancel_left] at h)
    have hω₁ : m⁻¹ • ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) ∈
        t.reeLocalCosets K a j := smul_mem_reeLocalCosets (inv_mem hm) (one_mem_reeLocalCosets j)
    have hω₂ : m⁻¹ • (g : ModGL t.tag K ⧸ t.reeFixedBorel K a) ∈ t.reeLocalCosets K a j :=
      smul_mem_reeLocalCosets (inv_mem hm) ⟨g, hgP, rfl⟩
    have hω₁ξ : m⁻¹ • ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) ≠
        ((1 : ModGL t.tag K) : _) := fun h => hmB (by
      have h' := inv_mem (smul_one_eq_one_iff.1 h)
      rwa [inv_inv] at h')
    have hω₂ξ : m⁻¹ • (g : ModGL t.tag K ⧸ t.reeFixedBorel K a) ≠ ((1 : ModGL t.tag K) : _) :=
      fun h => hgn (by
        rw [smul_mk, mk_eq_one_iff] at h
        rw [← hmn, QuotientGroup.eq]
        have h' := inv_mem h
        rwa [mul_inv_rev, inv_inv] at h')
    obtain ⟨x, hx, -⟩ := existsUnique_smul_eq hω₁ hω₁ξ hω₂ hω₂ξ
    have hyY : m * x * m⁻¹ ∈ t.reeFixedOrbitNegUnipotent K a j := by
      rw [hYeq]
      exact ⟨x, x.2, rfl⟩
    have hyg : (m * x * m⁻¹) • ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) =
        (g : ModGL t.tag K ⧸ t.reeFixedBorel K a) := by
      rw [mul_smul, mul_smul, hx, smul_inv_smul]
    rw [smul_mk, mul_one, QuotientGroup.eq] at hyg
    have hyV := reeFixedOrbitNegUnipotent_le_reeFixedNegUnipotent j hyY
    have h1 := hV1 _ (mul_mem (inv_mem hyV) hgV) hyg
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact hyY

section Opposite

variable {w₀ : WeylGroup t.tag}
  (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
include hw₀

theorem map_conj_reeFixedNegUnipotent :
    (t.reeFixedNegUnipotent K a).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      t.reeFixedPosUnipotent K a := by
  have hn := (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2
  have hU := (canonical_weyl_root_transport t.tag K).1 w₀ {α | IsRoot t.tag α ∧ height α < 0}
    fun α hα => hα.1
  have himg : (fun α => w₀ • α) '' {α | IsRoot t.tag α ∧ height α < 0} =
      {α | IsRoot t.tag α ∧ 0 < height α} := by
    ext β
    constructor
    · rintro ⟨γ, ⟨hγ, hγn⟩, rfl⟩
      refine ⟨IsRoot.smul hγ w₀, ?_⟩
      change 0 < height (w₀ • γ)
      rw [smul_longest hw₀, height_neg]
      omega
    · rintro ⟨hβ, hβp⟩
      refine ⟨-β, ⟨IsRoot.neg hβ, by rw [height_neg]; omega⟩, ?_⟩
      change w₀ • -β = β
      rw [smul_longest hw₀, neg_neg]
  rw [himg] at hU
  rw [reeFixedNegUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective]
  change (negUnipotent t.tag K).map _ ⊓ _ = posUnipotent t.tag K ⊓ _
  rw [negUnipotent, hU, map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
  rfl

theorem map_conj_reeFixedOrbitNegUnipotent_longest
    (j : Fin t.fixedOrbitCount) :
    (t.reeFixedOrbitNegUnipotent K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      t.reeFixedOrbitUnipotent K a j := by
  have hn := (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2
  have hU := (canonical_weyl_root_transport t.tag K).1 w₀ (Neg.neg '' t.fixedOrbitRoots j)
    fun α hα => isRoot_of_mem_neg_fixedOrbitRoots hα
  have himg : (fun α => w₀ • α) '' (Neg.neg '' t.fixedOrbitRoots j) = t.fixedOrbitRoots j := by
    rw [Set.image_image]
    simp only [smul_longest hw₀, neg_neg, Set.image_id']
  rw [himg] at hU
  rw [reeFixedOrbitNegUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, hU,
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
  rfl

theorem minimal_reeFixedTorus_sup_iff
    (A : Subgroup (ModGL t.tag K)) :
    Minimal (fun A => t.reeFixedTorus K a ⊔ t.reeFixedNegUnipotent K a < A ∧
      A ≤ t.reeGamma K a) A ↔
      ∃ j, A = (t.reeLocalParabolic K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
  have hn := (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2
  set f := (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).mapSubgroup with hfdef
  have hf : ∀ S : Subgroup (ModGL t.tag K), f S =
      S.map (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := fun _ => rfl
  have hfB : f (t.reeFixedBorel K a) = t.reeFixedTorus K a ⊔ t.reeFixedNegUnipotent K a := by
    rw [hf]
    exact map_conj_reeFixedBorel hw₀
  have hfΓ : f (t.reeGamma K a) = t.reeGamma K a := by
    rw [hf]
    exact map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)
  have key : ∀ S, (t.reeFixedTorus K a ⊔ t.reeFixedNegUnipotent K a < f S ∧
      f S ≤ t.reeGamma K a) ↔ (t.reeFixedBorel K a < S ∧ S ≤ t.reeGamma K a) := fun S => by
    rw [← hfB]
    conv_lhs => rw [← hfΓ]
    rw [f.lt_iff_lt, f.le_iff_le]
  rw [← f.apply_symm_apply A, minimal_apply_orderIso]
  simp only [key]
  rw [minimal_reeFixedBorel_iff]
  refine exists_congr fun j => ⟨fun h => by rw [h, hf], fun h => f.injective ?_⟩
  rw [h, hf]

end Opposite

theorem large_Ree_minimal_Borel_intersections
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (w₀ : WeylGroup F4.tag)
    (hw₀ : ∀ w, (coxeterSystem F4.tag).length w ≤ (coxeterSystem F4.tag).length w₀) :
    (∀ A : Subgroup (ModGL F4.tag K),
      Minimal (fun A => F4.reeFixedBorel K a < A ∧ A ≤ F4.reeGamma K a) A ↔
        A = F4.reeLocalParabolic K a ⟨0, by decide⟩ ∨
          A = F4.reeLocalParabolic K a ⟨1, by decide⟩) ∧
    F4.reeLocalParabolic K a ⟨0, by decide⟩ ≠ F4.reeLocalParabolic K a ⟨1, by decide⟩ ∧
    (∀ j, F4.reeLocalParabolic K a j ⊓ F4.reeFixedNegUnipotent K a =
      F4.reeFixedOrbitNegUnipotent K a j) ∧
    (∀ A : Subgroup (ModGL F4.tag K),
      Minimal (fun A => F4.reeFixedTorus K a ⊔ F4.reeFixedNegUnipotent K a < A ∧
        A ≤ F4.reeGamma K a) A ↔
        A = (F4.reeLocalParabolic K a ⟨0, by decide⟩).map
            (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom ∨
          A = (F4.reeLocalParabolic K a ⟨1, by decide⟩).map
            (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom) ∧
    (F4.reeLocalParabolic K a ⟨0, by decide⟩).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom ≠
      (F4.reeLocalParabolic K a ⟨1, by decide⟩).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom ∧
    (∀ j, (F4.reeLocalParabolic K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom ⊓
          F4.reeFixedPosUnipotent K a = F4.reeFixedOrbitUnipotent K a j) := by
  have hfin : ∀ (p : Fin F4.fixedOrbitCount → Prop),
      (∃ j, p j) ↔ p ⟨0, by decide⟩ ∨ p ⟨1, by decide⟩ := fun p => by
    constructor
    · rintro ⟨⟨j, hj⟩, hp⟩
      change j < 2 at hj
      interval_cases j
      · exact Or.inl hp
      · exact Or.inr hp
    · rintro (hp | hp)
      · exact ⟨_, hp⟩
      · exact ⟨_, hp⟩
  have hne : F4.reeLocalParabolic K a ⟨0, by decide⟩ ≠ F4.reeLocalParabolic K a ⟨1, by decide⟩ :=
    fun h => absurd (reeLocalParabolic_injective h) (by decide)
  refine ⟨fun A => (minimal_reeFixedBorel_iff A).trans (hfin _), hne,
    reeLocalParabolic_inf_reeFixedNegUnipotent, fun A =>
      (minimal_reeFixedTorus_sup_iff hw₀ A).trans (hfin _),
    fun h => hne (Subgroup.map_injective (MulAut.conj _).injective h), fun j => ?_⟩
  rw [← map_conj_reeFixedNegUnipotent hw₀, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    reeLocalParabolic_inf_reeFixedNegUnipotent, map_conj_reeFixedOrbitNegUnipotent_longest hw₀]

end ReeTag

end CFSG.LieType.Ree
