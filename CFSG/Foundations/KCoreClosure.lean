module

public import CFSG.Foundations.KCore
public import Mathlib.GroupTheory.Solvable

public section

universe u

namespace CFSG.KCore

variable {C : Catalogue.{u}} {X Q : Type u} [Group X] [Group Q]

theorem KGroupAllSimple.of_isSolvable (hab : ContainsAbelianSimple C) [Finite X]
    (hX : Group.IsSolvable X) : KGroupAllSimple C X := by
  intro H N _ _
  have hsolv : Group.IsSolvable (H ⧸ N) := inferInstance
  have : Finite (H ⧸ N) := Finite.of_surjective _ (QuotientGroup.mk'_surjective N)
  exact hab _ (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv)

theorem KGroupAllSimple.of_commutative (hab : ContainsAbelianSimple C) [Finite X]
    (h : ∀ a b : X, a * b = b * a) : KGroupAllSimple C X :=
  of_isSolvable hab (Group.isSolvable_of_comm h)

theorem KGroupAllSimple.of_ker (hC : IsoInvariant C) (f : X →* Q)
    (hk : KGroupAllSimple C f.ker) (hq : KGroupAllSimple C Q) : KGroupAllSimple C X := by
  intro H N _ hs
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  let ρ : H →* Q := f.comp H.subtype
  have hMn : ρ.ker.Normal := MonoidHom.normal_ker ρ
  have hmapn : (ρ.ker.map π).Normal := hMn.map π (QuotientGroup.mk'_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map π) with hbot | htop
  ·
    have hle : ρ.ker ≤ π.ker := by
      intro m hm
      have : π m ∈ ρ.ker.map π := Subgroup.mem_map_of_mem π hm
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
    have hker : ρ.rangeRestrict.ker ≤ π.ker := by
      rwa [MonoidHom.ker_rangeRestrict]
    let φ : ρ.range →* H ⧸ N := MonoidHom.liftOfSurjective ρ.rangeRestrict hsurj ⟨π, hker⟩
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N y
      exact ⟨ρ.rangeRestrict h, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
    exact hq.catalogue_of_surjective hC ρ.range φ hφ
  ·
    let K : Subgroup f.ker := H.comap f.ker.subtype
    let ι : K →* H :=
      { toFun := fun k => ⟨k.1.1, k.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Surjective (π.comp ι) := by
      intro y
      have hy : y ∈ ρ.ker.map π := by rw [htop]; trivial
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
      have hmk : (m : X) ∈ f.ker := hm
      exact ⟨⟨⟨m, hmk⟩, m.2⟩, rfl⟩
    exact hk.catalogue_of_surjective hC K (π.comp ι) hφ

theorem KGroupAllSimple.of_isSimpleGroup (hC : IsoInvariant C) (hab : ContainsAbelianSimple C)
    [Finite X] [IsSimpleGroup X] (hX : C X)
    (hprop : ∀ H : Subgroup X, H ≠ ⊤ → ∀ (N : Subgroup H) [N.Normal], IsSimpleGroup (H ⧸ N) →
      (∃ a b : H ⧸ N, a * b ≠ b * a) → C (H ⧸ N)) :
    KGroupAllSimple C X := by
  intro H N _ hs
  by_cases hH : H = ⊤
  · have hmem : ∀ y : X, y ∈ H := fun y => hH ▸ Subgroup.mem_top y
    have hinj : Function.Injective H.subtype := Subtype.val_injective
    have hsurj : Function.Surjective H.subtype := fun y => ⟨⟨y, hmem y⟩, rfl⟩
    have hNn : (N.map H.subtype).Normal := ‹N.Normal›.map H.subtype hsurj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map H.subtype) with hb | ht
    · have hNb : N = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 hb
      exact hC ((QuotientGroup.quotientMulEquivOfEq hNb).trans
        (QuotientGroup.quotientBot.trans (MulEquiv.ofBijective H.subtype ⟨hinj, hsurj⟩))) hX
    · exfalso
      have hNt : ∀ h : H, h ∈ N := by
        intro h
        have : H.subtype h ∈ N.map H.subtype := by rw [ht]; trivial
        obtain ⟨n, hn, hnh⟩ := Subgroup.mem_map.1 this
        rwa [← hinj hnh]
      have hsub : Subsingleton (H ⧸ N) := by
        refine ⟨fun x y => ?_⟩
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        exact QuotientGroup.eq.2 (hNt _)
      exact not_subsingleton _ hsub
  · by_cases hcomm : ∀ a b : H ⧸ N, a * b = b * a
    · have : Finite (H ⧸ N) := Finite.of_surjective _ (QuotientGroup.mk'_surjective N)
      exact hab _ hcomm
    · push Not at hcomm
      exact hprop H hH N hs hcomm

theorem KProperNonab.kGroupAllSimple_of_isSimpleGroup (hC : IsoInvariant C)
    (hab : ContainsAbelianSimple C) [Finite X] [IsSimpleGroup X] (hX : C X)
    (hK : KProperNonab C X) : KGroupAllSimple C X :=
  KGroupAllSimple.of_isSimpleGroup hC hab hX fun H hH N _ _ hn =>
    hK.catalogue_of_surjective hC H hH hn (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end CFSG.KCore
