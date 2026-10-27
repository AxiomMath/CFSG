module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem exists_proj_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∃ (ρA : ↥(A ⊔ B) →* (↥A ⧸ center ↥A)) (ρB : ↥(A ⊔ B) →* (↥B ⧸ center ↥B)),
      (∀ x : ↥(A ⊔ B), ∃ (a : ↥A) (b : ↥B), (x : G) = a * b) ∧
      ∀ (a : ↥A) (b : ↥B) (hab : (a : G) * b ∈ A ⊔ B),
        ρA ⟨a * b, hab⟩ = QuotientGroup.mk a ∧ ρB ⟨a * b, hab⟩ = QuotientGroup.mk b := by
  let f : ↥A × ↥B →* ↥(A ⊔ B) :=
    { toFun := fun x => ⟨(x.1 : G) * (x.2 : G), mul_mem_sup x.1.2 x.2.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
          ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
        calc ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G))
            = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by group
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by
                rw [h y.1 y.1.2 x.2 x.2.2]
          _ = ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) := by group) }
  have hf : Function.Surjective f := by
    have htop : A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    apply MonoidHom.range_eq_top.mp
    rw [eq_top_iff, ← htop]
    apply sup_le
    · rintro a ha
      exact ⟨(⟨(a : G), ha⟩, 1), Subtype.ext (by simp [f])⟩
    · rintro b hb
      exact ⟨(1, ⟨(b : G), hb⟩), Subtype.ext (by simp [f])⟩
  let gA : ↥A × ↥B →* (↥A ⧸ center ↥A) :=
    (QuotientGroup.mk' (center ↥A)).comp (MonoidHom.fst ↥A ↥B)
  let gB : ↥A × ↥B →* (↥B ⧸ center ↥B) :=
    (QuotientGroup.mk' (center ↥B)).comp (MonoidHom.snd ↥A ↥B)
  have hkerA : f.ker ≤ gA.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxval : (x.1 : G) * (x.2 : G) = 1 := by
      simpa [f] using congrArg Subtype.val hx
    have haB : (x.1 : G) ∈ B := by
      have h1 : (x.1 : G) = (x.2 : G)⁻¹ := mul_eq_one_iff_eq_inv.mp hxval
      rw [h1]
      exact B.inv_mem x.2.2
    have hcenter : x.1 ∈ center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro a'
      apply Subtype.ext
      change (a' : G) * (x.1 : G) = (x.1 : G) * (a' : G)
      exact h a' a'.2 (x.1 : G) haB
    exact (QuotientGroup.eq_one_iff x.1).mpr hcenter
  have hkerB : f.ker ≤ gB.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxval : (x.1 : G) * (x.2 : G) = 1 := by
      simpa [f] using congrArg Subtype.val hx
    have hbA : (x.2 : G) ∈ A := by
      have h1 : (x.2 : G) = (x.1 : G)⁻¹ := mul_eq_one_iff_eq_inv'.mp hxval
      rw [h1]
      exact A.inv_mem x.1.2
    have hcenter : x.2 ∈ center ↥B := by
      rw [Subgroup.mem_center_iff]
      intro b'
      apply Subtype.ext
      change (b' : G) * (x.2 : G) = (x.2 : G) * (b' : G)
      exact (h (x.2 : G) hbA b' b'.2).symm
    exact (QuotientGroup.eq_one_iff x.2).mpr hcenter
  let ρA : ↥(A ⊔ B) →* (↥A ⧸ center ↥A) := f.liftOfSurjective hf ⟨gA, hkerA⟩
  let ρB : ↥(A ⊔ B) →* (↥B ⧸ center ↥B) := f.liftOfSurjective hf ⟨gB, hkerB⟩
  have hprojA : ∀ x : ↥A × ↥B, ρA (f x) = gA x := by
    intro x
    dsimp only [ρA]
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  have hprojB : ∀ x : ↥A × ↥B, ρB (f x) = gB x := by
    intro x
    dsimp only [ρB]
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  refine ⟨ρA, ρB, ?_, ?_⟩
  · intro x
    obtain ⟨⟨a, b⟩, hab⟩ := hf x
    exact ⟨a, b, by simpa [f] using (congrArg Subtype.val hab).symm⟩
  · intro a b hab
    have hfab : (⟨(a : G) * b, hab⟩ : ↥(A ⊔ B)) = f (a, b) := Subtype.ext rfl
    rw [hfab]
    exact ⟨by rw [hprojA (a, b)]; rfl, by rw [hprojB (a, b)]; rfl⟩

theorem card_quotient_center_dvd_of_ker_le_center {X C : Type*} [Group X] [Group C] [Finite X]
    [Finite C] (φ : X →* C) (hK : φ.ker ≤ center X) :
    Nat.card (X ⧸ center X) ∣ Nat.card C := by
  have h1 : Nat.card (X ⧸ center X) ∣ Nat.card (X ⧸ φ.ker) := by
    have h := Subgroup.card_quotient_dvd_card ((center X).map (QuotientGroup.mk' φ.ker))
    rw [← Nat.card_congr
      (QuotientGroup.quotientQuotientEquivQuotient φ.ker (center X) hK).toEquiv]
    exact h
  have h2 : Nat.card (X ⧸ φ.ker) ∣ Nat.card C := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card φ.range
  exact h1.trans h2

theorem card_quotient_center_dvd_of_le_sup [Finite G] {A B X : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hX : X ≤ A ⊔ B) (hq : CFSG.IsQuasisimple X) :
    Nat.card (↥X ⧸ center ↥X) ∣ Nat.card (↥A ⧸ center ↥A) ∨
      Nat.card (↥X ⧸ center ↥X) ∣ Nat.card (↥B ⧸ center ↥B) := by
  obtain ⟨ρA, ρB, hdec, hρ⟩ := exists_proj_of_commute hAB
  let ι : ↥X →* ↥(A ⊔ B) := Subgroup.inclusion hX
  let φA : ↥X →* (↥A ⧸ center ↥A) := ρA.comp ι
  let φB : ↥X →* (↥B ⧸ center ↥B) := ρB.comp ι
  have hkey : φA.ker ≤ center ↥X ∨ φB.ker ≤ center ↥X := by
    by_contra h
    have hA : ¬ φA.ker ≤ center ↥X := fun hle => h (Or.inl hle)
    have hB : ¬ φB.ker ≤ center ↥X := fun hle => h (Or.inr hle)
    have hAtop : φA.ker = ⊤ := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker φA) with
        h' | h'
      · exact h'
      · exact absurd h' hA
    have hBtop : φB.ker = ⊤ := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker φB) with
        h' | h'
      · exact h'
      · exact absurd h' hB
    have hcent : ∀ x : ↥X, x ∈ center ↥X := by
      intro x
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨a, b, hab⟩ := hdec (ι x)
      obtain ⟨a', b', hab'⟩ := hdec (ι y)
      have ha : a ∈ center ↥A := by
        have hx1 : φA x = 1 := MonoidHom.mem_ker.mp (by rw [hAtop]; trivial)
        have heq : φA x = QuotientGroup.mk a := by
          change ρA (ι x) = QuotientGroup.mk a
          have hsub : (ι x) = (⟨(a : G) * b, mul_mem_sup a.2 b.2⟩ : ↥(A ⊔ B)) :=
            Subtype.ext hab
          rw [hsub]
          exact (hρ a b (mul_mem_sup a.2 b.2)).1
        rw [heq] at hx1
        exact (QuotientGroup.eq_one_iff a).mp hx1
      have hb : b ∈ center ↥B := by
        have hx1 : φB x = 1 := MonoidHom.mem_ker.mp (by rw [hBtop]; trivial)
        have heq : φB x = QuotientGroup.mk b := by
          change ρB (ι x) = QuotientGroup.mk b
          have hsub : (ι x) = (⟨(a : G) * b, mul_mem_sup a.2 b.2⟩ : ↥(A ⊔ B)) :=
            Subtype.ext hab
          rw [hsub]
          exact (hρ a b (mul_mem_sup a.2 b.2)).2
        rw [heq] at hx1
        exact (QuotientGroup.eq_one_iff b).mp hx1
      apply Subtype.ext
      change ((ι y : ↥(A ⊔ B)) : G) * ((ι x : ↥(A ⊔ B)) : G) =
        ((ι x : ↥(A ⊔ B)) : G) * ((ι y : ↥(A ⊔ B)) : G)
      have haa' : (a : G) * a' = a' * a := by
        have hh := congrArg Subtype.val (Subgroup.mem_center_iff.mp ha a')
        simpa using hh.symm
      have hbb' : (b : G) * b' = b' * b := by
        have hh := congrArg Subtype.val (Subgroup.mem_center_iff.mp hb b')
        simpa using hh.symm
      have hab'' : (a : G) * b' = b' * a := hAB a a.2 b' b'.2
      have ha'b : (a' : G) * b = b * a' := hAB a' a'.2 b b.2
      rw [hab, hab']
      calc ((a' : G) * b') * ((a : G) * b)
          = (a' : G) * (b' * a) * b := by group
        _ = (a' : G) * (a * b') * b := by rw [hab''.symm]
        _ = ((a' : G) * a) * (b' * b) := by group
        _ = ((a : G) * a') * (b * b') := by rw [haa'.symm, hbb'.symm]
        _ = (a : G) * (a' * b) * b' := by group
        _ = (a : G) * (b * a') * b' := by rw [ha'b]
        _ = ((a : G) * b) * ((a' : G) * b') := by group
    have htop : center ↥X = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact hcent x
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by
      have hv : v ∈ center ↥X := by rw [htop]; trivial
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hv u])
  rcases hkey with hk | hk
  · exact Or.inl (card_quotient_center_dvd_of_ker_le_center φA hk)
  · exact Or.inr (card_quotient_center_dvd_of_ker_le_center φB hk)

end CFSG.OddStandard.SmallF3.Omega
