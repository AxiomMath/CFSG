module

public import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.RankThree.PerfectCover (hopfMultiplier)

theorem exists_hom_of_cover {H L X : Type} [Group H] [Finite H] [Group L] [Finite L] [Group X]
    (hH : Group.IsPerfect H) (hL : Group.IsPerfect L)
    (α : H →* X) (hα : Function.Surjective α) (hαc : α.ker ≤ Subgroup.center H)
    (β : L →* X) (hβ : Function.Surjective β) (hβc : β.ker ≤ Subgroup.center L)
    [Finite (hopfMultiplier X)] {p : ℕ} (hp : p.Prime) (hβp : IsPGroup p β.ker)
    (hM : (Nat.card (hopfMultiplier X)).factorization p ≤ (Nat.card α.ker).factorization p) :
    ∃ φ : H →* L, Function.Surjective φ ∧ β.comp φ = α := by
  have : Fact p.Prime := ⟨hp⟩
  have hXfin : Finite X := Finite.of_surjective α hα
  set F : Subgroup (H × L) :=
    MonoidHom.eqLocus (α.comp (MonoidHom.fst H L)) (β.comp (MonoidHom.snd H L)) with hFdef
  have hmemF : ∀ x : H × L, x ∈ F ↔ α x.1 = β x.2 := fun x => Iff.rfl
  set π₁ : F →* H := (MonoidHom.fst H L).comp F.subtype with hπ₁def
  have hπ₁ : Function.Surjective π₁ := by
    intro h
    obtain ⟨l, hl⟩ := hβ (α h)
    exact ⟨⟨(h, l), by rw [hmemF]; exact hl.symm⟩, rfl⟩
  have hker₁ : ∀ x : F, x ∈ π₁.ker → (x : H × L).1 = 1 ∧ (x : H × L).2 ∈ β.ker := by
    intro x hx
    have hx1 : (x : H × L).1 = 1 := hx
    refine ⟨hx1, ?_⟩
    have h1 := (hmemF x).1 x.2
    rw [hx1, map_one] at h1
    exact h1.symm
  have hC₁ : π₁.ker ≤ Subgroup.center F := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hker₁ x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · change (y : H × L).1 * (x : H × L).1 = (x : H × L).1 * (y : H × L).1
      rw [hx1, mul_one, one_mul]
    · exact Subgroup.mem_center_iff.1 (hβc hx2) (y : H × L).2
  obtain ⟨-, hE'perf, hE'surj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective π₁ hπ₁ hC₁ hH
  set E' : Subgroup F := commutator F with hE'def
  set π' : E' →* H := π₁.comp E'.subtype with hπ'def
  have hcentral : ∀ g : E', (∀ y : F, (g : F) * y = y * (g : F)) → g ∈ Subgroup.center E' := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    exact Subtype.ext (hg g').symm
  set γ : E' →* X := α.comp π' with hγdef
  have hγ : Function.Surjective γ := hα.comp hE'surj
  have hγc : γ.ker ≤ Subgroup.center E' := by
    intro g hg
    apply hcentral
    intro y
    have h1 : α ((g : F) : H × L).1 = 1 := hg
    have h2 : β ((g : F) : H × L).2 = 1 := by
      rw [← (hmemF _).1 (g : F).2]
      exact h1
    apply Subtype.ext
    apply Prod.ext
    · exact (Subgroup.mem_center_iff.1 (hαc h1) (y : H × L).1).symm
    · exact (Subgroup.mem_center_iff.1 (hβc h2) (y : H × L).2).symm
  have hdvd : Nat.card γ.ker ∣ Nat.card (hopfMultiplier X) :=
    CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hE'perf γ hγ hγc
  have hcard : Nat.card γ.ker = Nat.card α.ker * Nat.card π'.ker := by
    have h1 := CFSG.GH74.Generic.card_eq_card_mul_card_ker π' hE'surj
    have h2 := CFSG.GH74.Generic.card_eq_card_mul_card_ker γ hγ
    have h3 := CFSG.GH74.Generic.card_eq_card_mul_card_ker α hα
    have h4 : 0 < Nat.card X := Nat.card_pos
    rw [h3, mul_assoc] at h1
    exact Nat.eq_of_mul_eq_mul_left h4 (h2.symm.trans h1)
  have hK'p : IsPGroup p π'.ker := by
    let ι : π'.ker →* β.ker :=
      { toFun := fun k => ⟨((k : E') : F).1.2, by
          have h1 := hker₁ (k : E') (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp k.2))
          exact h1.2⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    have hι : Function.Injective ι := by
      intro a b hab
      have hb : ((a : E') : F).1.2 = ((b : E') : F).1.2 := congrArg Subtype.val hab
      have ha1 := (hker₁ (a : E') (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp a.2))).1
      have hb1 := (hker₁ (b : E') (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp b.2))).1
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (ha1.trans hb1.symm) hb
    exact hβp.of_injective ι hι
  have hK'1 : Nat.card π'.ker = 1 := by
    obtain ⟨j, hj⟩ := hK'p.exists_card_eq
    have hpos1 : Nat.card α.ker ≠ 0 := Nat.card_pos.ne'
    have hpos2 : Nat.card π'.ker ≠ 0 := Nat.card_pos.ne'
    have hle : (Nat.card γ.ker).factorization p ≤ (Nat.card (hopfMultiplier X)).factorization p :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd p
    rw [hcard, Nat.factorization_mul hpos1 hpos2, Finsupp.add_apply, hj,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at hle
    have : j = 0 := by omega
    rw [hj, this, pow_zero]
  have hker' : π'.ker = ⊥ := Subgroup.card_eq_one.1 hK'1
  have hbij : Function.Bijective π' := ⟨(MonoidHom.ker_eq_bot_iff π').1 hker', hE'surj⟩
  set e : E' ≃* H := MulEquiv.ofBijective π' hbij with he
  have hπe : ∀ h : H, π' (e.symm h) = h := fun h => e.apply_symm_apply h
  set φ : H →* L := (MonoidHom.snd H L).comp (F.subtype.comp (E'.subtype.comp e.symm.toMonoidHom))
    with hφ
  have hβφ : β.comp φ = α := by
    refine MonoidHom.ext fun h => ?_
    have h1 := (hmemF ((((e.symm h : E') : F)) : H × L)).1 (e.symm h : E').1.2
    have h2 : ((((e.symm h : E') : F)) : H × L).1 = h := hπe h
    rw [h2] at h1
    exact h1.symm
  refine ⟨φ, ?_, hβφ⟩
  have hsup : φ.range ⊔ Subgroup.center L = ⊤ := by
    rw [eq_top_iff]
    intro l _
    obtain ⟨h, hh⟩ := hα (β l)
    have hz : (φ h)⁻¹ * l ∈ Subgroup.center L := by
      apply hβc
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply β φ h, hβφ, hh,
        inv_mul_cancel]
    rw [show l = φ h * ((φ h)⁻¹ * l) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨h, rfl⟩) (Subgroup.mem_sup_right hz)
  exact MonoidHom.range_eq_top.1 ((CFSG.SectionRank.perfect_central_supplement hL).1 _ hsup)

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
