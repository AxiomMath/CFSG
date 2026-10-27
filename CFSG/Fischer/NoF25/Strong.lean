module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Fi22.LH.Facts
public import CFSG.Sporadic.Fi23.Tr.Facts
public import CFSG.Sporadic.Fi24.Complete

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

structure StrongPoints (hF : Pair Y F) (E : Set X) (b : X) where
  L : LocalPoints (pairModel hF) E b
  lift : ∀ r : Y, ∃ x : X, x * b * x⁻¹ = b ∧
    ∀ f g : LocalClass E b, (g : X) = x * f * x⁻¹ → (L.χ g : Y) = r * L.χ f * r⁻¹

@[expose] noncomputable def localPointsOfMulEquiv (hP : Pair X E) (hF : Pair Y F) {e : X}
    (hQ : Pair (LocalQuotient E e) (LocalImages E e)) (iso : LocalQuotient E e ≃* Y)
    (hiso : iso '' LocalImages E e = F) : LocalPoints (pairModel hF) E e where
  χ := Equiv.ofBijective (fun f => ⟨iso (starImage E e f), by
      rw [← hiso]
      refine ⟨starImage E e f, ?_, rfl⟩
      rw [← range_starImage]
      exact ⟨f, rfl⟩⟩)
    ⟨fun f g h => by
      have hone : (1 : LocalQuotient E e) ∉ LocalImages E e := by
        intro h1
        have := hQ.2.2.1 1 h1
        rw [orderOf_one] at this
        exact absurd this (by norm_num)
      exact Pair.starImage_injective_of_one_notMem hP hone
        (iso.injective (congrArg Subtype.val h)), fun y => by
      have hy : (y : Y) ∈ iso '' LocalImages E e := by rw [hiso]; exact y.2
      obtain ⟨q, hq, hqy⟩ := hy
      rw [← range_starImage] at hq
      obtain ⟨f, rfl⟩ := hq
      exact ⟨f, Subtype.ext hqy⟩⟩
  comm f g := by
    show (f : X) * g = g * f ↔ iso (starImage E e f) * iso (starImage E e g) =
      iso (starImage E e g) * iso (starImage E e f)
    rw [← map_mul, ← map_mul, iso.injective.eq_iff, ← commute_iff_eq, ← commute_iff_eq,
      Pair.starImage_commute_iff hP]
  tau f g h := by
    apply Subtype.ext
    show iso (starImage E e ⟨_, h⟩) =
      iso (starImage E e f) * iso (starImage E e g) * iso (starImage E e f)
    rw [starImage_conj f g h, map_mul, map_mul]

theorem localPointsOfMulEquiv_val (hP : Pair X E) (hF : Pair Y F) {e : X}
    (hQ : Pair (LocalQuotient E e) (LocalImages E e)) (iso : LocalQuotient E e ≃* Y)
    (hiso : iso '' LocalImages E e = F) (f : LocalClass E e) :
    ((localPointsOfMulEquiv hP hF hQ iso hiso).χ f : Y) = iso (starImage E e f) := rfl

@[expose] noncomputable def strongPointsOfMulEquiv (hP : Pair X E) (hF : Pair Y F) {e : X}
    (hQ : Pair (LocalQuotient E e) (LocalImages E e)) (iso : LocalQuotient E e ≃* Y)
    (hiso : iso '' LocalImages E e = F) : StrongPoints hF E e where
  L := localPointsOfMulEquiv hP hF hQ iso hiso
  lift r := by
    obtain ⟨x0, hx0⟩ := QuotientGroup.mk_surjective (iso.symm r)
    refine ⟨(x0 : X), ?_, fun f g hg => ?_⟩
    · have h := commute_of_mem_localGroup (E := E) (e := e) (x := e)
        (fun g hg => hg.2.2) x0.2
      rw [h, mul_inv_cancel_right]
    · rw [localPointsOfMulEquiv_val, localPointsOfMulEquiv_val]
      have e1 : starImage E e g = (QuotientGroup.mk x0 : LocalQuotient E e) * starImage E e f *
          (QuotientGroup.mk x0)⁻¹ := by
        have e2 : (⟨g, mem_localGroup g.2⟩ : LocalGroup E e) =
            x0 * ⟨f, mem_localGroup f.2⟩ * x0⁻¹ := Subtype.ext hg
        show (QuotientGroup.mk ⟨g, mem_localGroup g.2⟩ : LocalQuotient E e) = _
        rw [e2]
        rfl
      rw [e1, map_mul, map_mul, map_inv, hx0, MulEquiv.apply_symm_apply]

@[expose] noncomputable def StrongPoints.conj {hF : Pair Y F} (hE : Pair X E) {b : X}
    (S : StrongPoints hF E b) (g : X) : StrongPoints hF E (g * b * g⁻¹) where
  L := S.L.conj hE g
  lift r := by
    obtain ⟨x, hxb, hx⟩ := S.lift r
    refine ⟨g * x * g⁻¹, ?_, fun f f' hf' => ?_⟩
    · calc g * x * g⁻¹ * (g * b * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * b * x⁻¹) * g⁻¹ := by group
        _ = g * b * g⁻¹ := by rw [hxb]
    · show (S.L.χ ((conjStar hE g b).symm f') : Y) = r * S.L.χ ((conjStar hE g b).symm f) * r⁻¹
      refine hx _ _ ?_
      rw [conjStar_symm_val, conjStar_symm_val, hf']
      group

theorem nonempty_strongPoints_of_mem {hF : Pair Y F} (hE : Pair X E) {d : X} (hd : d ∈ E)
    (S : StrongPoints hF E d) : ∀ x ∈ E, Nonempty (StrongPoints hF E x) := by
  intro x hx
  obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hE hd hx)
  exact ⟨S.conj hE g⟩

theorem nonempty_strongPoints_D24
    {X : Type} [Group X] {E : Set X} (hP : Pair X E) {e : X}
    (he : e ∈ E) (hT : F24 (LocalQuotient E e) (LocalImages E e))
    (hZe : Subgroup.center (LocalQuotient E e) = ⊥)
    (hSe : IsSimpleGroup (commutator (LocalQuotient E e))) :
    ∀ b ∈ E, Nonempty (StrongPoints Sporadic.Fi24.pair_R E b) := by
  have hFF := Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts
  obtain ⟨iso, hiso⟩ := F24.exists_mulEquiv polarFacts hyperovalFacts hFF
    (Sporadic.Fi23.fi23Facts hFF) hT Sporadic.Fi24.f24_R hZe Sporadic.Fi24.center_R hSe
    Sporadic.Fi24.isSimpleGroup_commutator_R
  exact nonempty_strongPoints_of_mem hP he
    (strongPointsOfMulEquiv hP Sporadic.Fi24.pair_R hT.1 iso hiso)

end CFSG.Fischer
